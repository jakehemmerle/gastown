package cmd

import (
	"fmt"
	"os"
	"os/exec"
	"strings"

	"github.com/spf13/cobra"
	"github.com/steveyegge/gastown/internal/style"
	"github.com/steveyegge/gastown/internal/tmux"
)

var handoffCmd = &cobra.Command{
	Use:   "handoff [role]",
	Short: "Hand off to a fresh session, work continues from hook",
	Long: `End watch. Hand off to a fresh agent session.

This command uses tmux respawn-pane to end the current session and restart it
with a fresh Claude instance, running the full startup/priming sequence.

When run without arguments, hands off the current session.
When given a role name, hands off that role's session (and switches to it).

Examples:
  gt handoff           # Hand off current session
  gt handoff crew      # Hand off crew session (auto-detect name)
  gt handoff mayor     # Hand off mayor session
  gt handoff witness   # Hand off witness session for current rig

Any molecule on the hook will be auto-continued by the new session.`,
	RunE: runHandoff,
}

var (
	handoffWatch   bool
	handoffDryRun  bool
	handoffSubject string
	handoffMessage string
)

func init() {
	handoffCmd.Flags().BoolVarP(&handoffWatch, "watch", "w", true, "Switch to new session (for remote handoff)")
	handoffCmd.Flags().BoolVarP(&handoffDryRun, "dry-run", "n", false, "Show what would be done without executing")
	handoffCmd.Flags().StringVarP(&handoffSubject, "subject", "s", "", "Subject for handoff mail (optional)")
	handoffCmd.Flags().StringVarP(&handoffMessage, "message", "m", "", "Message body for handoff mail (optional)")
	rootCmd.AddCommand(handoffCmd)
}

func runHandoff(cmd *cobra.Command, args []string) error {
	t := tmux.NewTmux()

	// Verify we're in tmux
	if !tmux.IsInsideTmux() {
		return fmt.Errorf("not running in tmux - cannot hand off")
	}

	pane := os.Getenv("TMUX_PANE")
	if pane == "" {
		return fmt.Errorf("TMUX_PANE not set - cannot hand off")
	}

	// Get current session name
	currentSession, err := getCurrentTmuxSession()
	if err != nil {
		return fmt.Errorf("getting session name: %w", err)
	}

	// Determine target session
	targetSession := currentSession
	if len(args) > 0 {
		// User specified a role to hand off
		targetSession, err = resolveRoleToSession(args[0])
		if err != nil {
			return fmt.Errorf("resolving role: %w", err)
		}
	}

	// Build the restart command
	restartCmd, err := buildRestartCommand(targetSession)
	if err != nil {
		return err
	}

	// If handing off a different session, we need to find its pane and respawn there
	if targetSession != currentSession {
		return handoffRemoteSession(t, targetSession, restartCmd)
	}

	// If subject/message provided, send handoff mail to self first
	if handoffSubject != "" || handoffMessage != "" {
		if err := sendHandoffMail(handoffSubject, handoffMessage); err != nil {
			fmt.Printf("%s Warning: could not send handoff mail: %v\n", style.Dim.Render("⚠"), err)
			// Continue anyway - the respawn is more important
		} else {
			fmt.Printf("%s Sent handoff mail\n", style.Bold.Render("📬"))
		}
	}

	// Handing off ourselves - print feedback then respawn
	fmt.Printf("%s Handing off %s...\n", style.Bold.Render("🤝"), currentSession)

	// Dry run mode - show what would happen
	if handoffDryRun {
		fmt.Printf("Would execute: tmux respawn-pane -k -t %s %s\n", pane, restartCmd)
		return nil
	}

	// Use exec to respawn the pane - this kills us and restarts
	return t.RespawnPane(pane, restartCmd)
}

// getCurrentTmuxSession returns the current tmux session name.
func getCurrentTmuxSession() (string, error) {
	out, err := exec.Command("tmux", "display-message", "-p", "#{session_name}").Output()
	if err != nil {
		return "", err
	}
	return strings.TrimSpace(string(out)), nil
}

// resolveRoleToSession converts a role name to a tmux session name.
// For roles that need context (crew, witness, refinery), it auto-detects from environment.
func resolveRoleToSession(role string) (string, error) {
	switch strings.ToLower(role) {
	case "mayor", "may":
		return "gt-mayor", nil

	case "deacon", "dea":
		return "gt-deacon", nil

	case "crew":
		// Try to get rig and crew name from environment or cwd
		rig := os.Getenv("GT_RIG")
		crewName := os.Getenv("GT_CREW")
		if rig == "" || crewName == "" {
			// Try to detect from cwd
			detected, err := detectCrewFromCwd()
			if err == nil {
				rig = detected.rigName
				crewName = detected.crewName
			}
		}
		if rig == "" || crewName == "" {
			return "", fmt.Errorf("cannot determine crew identity - run from crew directory or specify GT_RIG/GT_CREW")
		}
		return fmt.Sprintf("gt-%s-crew-%s", rig, crewName), nil

	case "witness", "wit":
		rig := os.Getenv("GT_RIG")
		if rig == "" {
			return "", fmt.Errorf("cannot determine rig - set GT_RIG or run from rig context")
		}
		return fmt.Sprintf("gt-%s-witness", rig), nil

	case "refinery", "ref":
		rig := os.Getenv("GT_RIG")
		if rig == "" {
			return "", fmt.Errorf("cannot determine rig - set GT_RIG or run from rig context")
		}
		return fmt.Sprintf("gt-%s-refinery", rig), nil

	default:
		// Assume it's a direct session name
		return role, nil
	}
}

// buildRestartCommand creates the command to run when respawning a session's pane.
// This needs to be the actual command to execute (e.g., claude), not a session attach command.
func buildRestartCommand(sessionName string) (string, error) {
	// For respawn-pane, we run claude directly. The SessionStart hook will run gt prime.
	// Use exec to ensure clean process replacement.
	claudeCmd := "exec claude --dangerously-skip-permissions"

	switch {
	case sessionName == "gt-mayor":
		return claudeCmd, nil

	case sessionName == "gt-deacon":
		return claudeCmd, nil

	case strings.Contains(sessionName, "-crew-"):
		return claudeCmd, nil

	case strings.HasSuffix(sessionName, "-witness"):
		return claudeCmd, nil

	case strings.HasSuffix(sessionName, "-refinery"):
		return claudeCmd, nil

	default:
		return "", fmt.Errorf("unknown session type: %s (try specifying role explicitly)", sessionName)
	}
}

// handoffRemoteSession respawns a different session and optionally switches to it.
func handoffRemoteSession(t *tmux.Tmux, targetSession, restartCmd string) error {
	// Check if target session exists
	exists, err := t.HasSession(targetSession)
	if err != nil {
		return fmt.Errorf("checking session: %w", err)
	}
	if !exists {
		return fmt.Errorf("session '%s' not found - is the agent running?", targetSession)
	}

	// Get the pane ID for the target session
	targetPane, err := getSessionPane(targetSession)
	if err != nil {
		return fmt.Errorf("getting target pane: %w", err)
	}

	fmt.Printf("%s Handing off %s...\n", style.Bold.Render("🤝"), targetSession)

	// Dry run mode
	if handoffDryRun {
		fmt.Printf("Would execute: tmux respawn-pane -k -t %s %s\n", targetPane, restartCmd)
		if handoffWatch {
			fmt.Printf("Would execute: tmux switch-client -t %s\n", targetSession)
		}
		return nil
	}

	// Respawn the remote session's pane
	if err := t.RespawnPane(targetPane, restartCmd); err != nil {
		return fmt.Errorf("respawning pane: %w", err)
	}

	// If --watch, switch to that session
	if handoffWatch {
		fmt.Printf("Switching to %s...\n", targetSession)
		// Use tmux switch-client to move our view to the target session
		if err := exec.Command("tmux", "switch-client", "-t", targetSession).Run(); err != nil {
			// Non-fatal - they can manually switch
			fmt.Printf("Note: Could not auto-switch (use: tmux switch-client -t %s)\n", targetSession)
		}
	}

	return nil
}

// getSessionPane returns the pane identifier for a session's main pane.
func getSessionPane(sessionName string) (string, error) {
	// Get the pane ID for the first pane in the session
	out, err := exec.Command("tmux", "list-panes", "-t", sessionName, "-F", "#{pane_id}").Output()
	if err != nil {
		return "", err
	}
	lines := strings.Split(strings.TrimSpace(string(out)), "\n")
	if len(lines) == 0 || lines[0] == "" {
		return "", fmt.Errorf("no panes found in session")
	}
	return lines[0], nil
}

// sendHandoffMail sends a handoff mail to self using gt mail send.
func sendHandoffMail(subject, message string) error {
	// Build subject with handoff prefix if not already present
	if subject == "" {
		subject = "🤝 HANDOFF: Session cycling"
	} else if !strings.Contains(subject, "HANDOFF") {
		subject = "🤝 HANDOFF: " + subject
	}

	// Default message if not provided
	if message == "" {
		message = "Context cycling. Check bd ready for pending work."
	}

	// Use gt mail send to self (--self flag sends to current agent identity)
	cmd := exec.Command("gt", "mail", "send", "--self", "-s", subject, "-m", message)
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	return cmd.Run()
}
