package cmd

import (
	"fmt"
	"strings"

	"github.com/spf13/cobra"
	"github.com/steveyegge/gastown/internal/events"
	"github.com/steveyegge/gastown/internal/style"
	"github.com/steveyegge/gastown/internal/tmux"
	"github.com/steveyegge/gastown/internal/workspace"
)

var nudgeMessageFlag string

func init() {
	rootCmd.AddCommand(nudgeCmd)
	nudgeCmd.Flags().StringVarP(&nudgeMessageFlag, "message", "m", "", "Message to send")
}

var nudgeCmd = &cobra.Command{
	Use:     "nudge <target> [message]",
	GroupID: GroupComm,
	Short:   "Send a message to a polecat or deacon session reliably",
	Long: `Sends a message to a polecat's or deacon's Claude Code session.

Uses a reliable delivery pattern:
1. Sends text in literal mode (-l flag)
2. Waits 500ms for paste to complete
3. Sends Enter as a separate command

This is the ONLY way to send messages to Claude sessions.
Do not use raw tmux send-keys elsewhere.

Special targets:
  deacon    Maps to the Deacon session (gt-deacon)

Examples:
  gt nudge greenplace/furiosa "Check your mail and start working"
  gt nudge greenplace/alpha -m "What's your status?"
  gt nudge deacon session-started`,
	Args: cobra.RangeArgs(1, 2),
	RunE: runNudge,
}

func runNudge(cmd *cobra.Command, args []string) error {
	target := args[0]

	// Get message from -m flag or positional arg
	var message string
	if nudgeMessageFlag != "" {
		message = nudgeMessageFlag
	} else if len(args) >= 2 {
		message = args[1]
	} else {
		return fmt.Errorf("message required: use -m flag or provide as second argument")
	}

	// Identify sender for message prefix
	sender := "unknown"
	if roleInfo, err := GetRole(); err == nil {
		switch roleInfo.Role {
		case RoleMayor:
			sender = "mayor"
		case RoleCrew:
			sender = fmt.Sprintf("%s/crew/%s", roleInfo.Rig, roleInfo.Polecat)
		case RolePolecat:
			sender = fmt.Sprintf("%s/%s", roleInfo.Rig, roleInfo.Polecat)
		case RoleWitness:
			sender = fmt.Sprintf("%s/witness", roleInfo.Rig)
		case RoleRefinery:
			sender = fmt.Sprintf("%s/refinery", roleInfo.Rig)
		case RoleDeacon:
			sender = "deacon"
		default:
			sender = string(roleInfo.Role)
		}
	}

	// Prefix message with sender
	message = fmt.Sprintf("[from %s] %s", sender, message)

	t := tmux.NewTmux()

	// Special case: "deacon" target maps to the Deacon session
	if target == "deacon" {
		// Check if Deacon session exists
		exists, err := t.HasSession(DeaconSessionName)
		if err != nil {
			return fmt.Errorf("checking deacon session: %w", err)
		}
		if !exists {
			// Deacon not running - this is not an error, just log and return
			fmt.Printf("%s Deacon not running, nudge skipped\n", style.Dim.Render("○"))
			return nil
		}

		if err := t.NudgeSession(DeaconSessionName, message); err != nil {
			return fmt.Errorf("nudging deacon: %w", err)
		}

		fmt.Printf("%s Nudged deacon\n", style.Bold.Render("✓"))

		// Log nudge event
		if townRoot, err := workspace.FindFromCwd(); err == nil && townRoot != "" {
			LogNudge(townRoot, "deacon", message)
		}
		_ = events.LogFeed(events.TypeNudge, sender, events.NudgePayload("", "deacon", message))
		return nil
	}

	// Check if target is rig/polecat format or raw session name
	if strings.Contains(target, "/") {
		// Parse rig/polecat format
		rigName, polecatName, err := parseAddress(target)
		if err != nil {
			return err
		}

		var sessionName string

		// Check if this is a crew address (polecatName starts with "crew/")
		if strings.HasPrefix(polecatName, "crew/") {
			// Extract crew name and use crew session naming
			crewName := strings.TrimPrefix(polecatName, "crew/")
			sessionName = crewSessionName(rigName, crewName)
		} else {
			// Regular polecat - use session manager
			mgr, _, err := getSessionManager(rigName)
			if err != nil {
				return err
			}
			sessionName = mgr.SessionName(polecatName)
		}

		// Send nudge using the reliable NudgeSession
		if err := t.NudgeSession(sessionName, message); err != nil {
			return fmt.Errorf("nudging session: %w", err)
		}

		fmt.Printf("%s Nudged %s/%s\n", style.Bold.Render("✓"), rigName, polecatName)

		// Log nudge event
		if townRoot, err := workspace.FindFromCwd(); err == nil && townRoot != "" {
			LogNudge(townRoot, target, message)
		}
		_ = events.LogFeed(events.TypeNudge, sender, events.NudgePayload(rigName, target, message))
	} else {
		// Raw session name (legacy)
		exists, err := t.HasSession(target)
		if err != nil {
			return fmt.Errorf("checking session: %w", err)
		}
		if !exists {
			return fmt.Errorf("session %q not found", target)
		}

		if err := t.NudgeSession(target, message); err != nil {
			return fmt.Errorf("nudging session: %w", err)
		}

		fmt.Printf("✓ Nudged %s\n", target)

		// Log nudge event
		if townRoot, err := workspace.FindFromCwd(); err == nil && townRoot != "" {
			LogNudge(townRoot, target, message)
		}
		_ = events.LogFeed(events.TypeNudge, sender, events.NudgePayload("", target, message))
	}

	return nil
}
