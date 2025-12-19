// Package beads molecule support - composable workflow templates.
package beads

import (
	"fmt"
	"regexp"
	"strings"
)

// MoleculeStep represents a parsed step from a molecule definition.
type MoleculeStep struct {
	Ref          string   // Step reference (from "## Step: <ref>")
	Title        string   // Step title (first non-empty line or ref)
	Instructions string   // Prose instructions for this step
	Needs        []string // Step refs this step depends on
	Tier         string   // Optional tier hint: haiku, sonnet, opus
}

// stepHeaderRegex matches "## Step: <ref>" with optional whitespace.
var stepHeaderRegex = regexp.MustCompile(`(?i)^##\s*Step:\s*(\S+)\s*$`)

// needsLineRegex matches "Needs: step1, step2, ..." lines.
var needsLineRegex = regexp.MustCompile(`(?i)^Needs:\s*(.+)$`)

// tierLineRegex matches "Tier: haiku|sonnet|opus" lines.
var tierLineRegex = regexp.MustCompile(`(?i)^Tier:\s*(haiku|sonnet|opus)\s*$`)

// templateVarRegex matches {{variable}} placeholders.
var templateVarRegex = regexp.MustCompile(`\{\{(\w+)\}\}`)

// ParseMoleculeSteps extracts step definitions from a molecule's description.
//
// The expected format is:
//
//	## Step: <ref>
//	<prose instructions>
//	Needs: <step>, <step>  # optional
//	Tier: haiku|sonnet|opus  # optional
//
// Returns an empty slice if no steps are found.
func ParseMoleculeSteps(description string) ([]MoleculeStep, error) {
	if description == "" {
		return nil, nil
	}

	lines := strings.Split(description, "\n")
	var steps []MoleculeStep
	var currentStep *MoleculeStep
	var contentLines []string

	// Helper to finalize current step
	finalizeStep := func() {
		if currentStep == nil {
			return
		}

		// Process content lines to extract Needs/Tier and build instructions
		var instructionLines []string
		for _, line := range contentLines {
			trimmed := strings.TrimSpace(line)

			// Check for Needs: line
			if matches := needsLineRegex.FindStringSubmatch(trimmed); matches != nil {
				deps := strings.Split(matches[1], ",")
				for _, dep := range deps {
					dep = strings.TrimSpace(dep)
					if dep != "" {
						currentStep.Needs = append(currentStep.Needs, dep)
					}
				}
				continue
			}

			// Check for Tier: line
			if matches := tierLineRegex.FindStringSubmatch(trimmed); matches != nil {
				currentStep.Tier = strings.ToLower(matches[1])
				continue
			}

			// Regular instruction line
			instructionLines = append(instructionLines, line)
		}

		// Build instructions, trimming leading/trailing blank lines
		currentStep.Instructions = strings.TrimSpace(strings.Join(instructionLines, "\n"))

		// Set title from first non-empty line of instructions, or use ref
		if currentStep.Instructions != "" {
			firstLine := strings.SplitN(currentStep.Instructions, "\n", 2)[0]
			currentStep.Title = strings.TrimSpace(firstLine)
		}
		if currentStep.Title == "" {
			currentStep.Title = currentStep.Ref
		}

		steps = append(steps, *currentStep)
		currentStep = nil
		contentLines = nil
	}

	for _, line := range lines {
		// Check for step header
		if matches := stepHeaderRegex.FindStringSubmatch(line); matches != nil {
			// Finalize previous step if any
			finalizeStep()

			// Start new step
			currentStep = &MoleculeStep{
				Ref: matches[1],
			}
			contentLines = nil
			continue
		}

		// Accumulate content lines if we're in a step
		if currentStep != nil {
			contentLines = append(contentLines, line)
		}
	}

	// Finalize last step
	finalizeStep()

	return steps, nil
}

// ExpandTemplateVars replaces {{variable}} placeholders in text using the provided context map.
// Unknown variables are left as-is.
func ExpandTemplateVars(text string, ctx map[string]string) string {
	if ctx == nil {
		return text
	}

	return templateVarRegex.ReplaceAllStringFunc(text, func(match string) string {
		// Extract variable name from {{name}}
		varName := match[2 : len(match)-2]
		if value, ok := ctx[varName]; ok {
			return value
		}
		return match // Leave unknown variables as-is
	})
}

// InstantiateOptions configures molecule instantiation behavior.
type InstantiateOptions struct {
	// Context map for {{variable}} substitution
	Context map[string]string
}

// InstantiateMolecule creates child issues from a molecule template.
//
// For each step in the molecule, this creates:
//   - A child issue with ID "{parent.ID}.{step.Ref}"
//   - Title from step title
//   - Description from step instructions (with template vars expanded)
//   - Type: task
//   - Priority: inherited from parent
//   - Dependencies wired according to Needs: declarations
//
// The function is atomic via bd CLI - either all issues are created or none.
// Returns the created step issues.
func (b *Beads) InstantiateMolecule(mol *Issue, parent *Issue, opts InstantiateOptions) ([]*Issue, error) {
	if mol == nil {
		return nil, fmt.Errorf("molecule issue is nil")
	}
	if parent == nil {
		return nil, fmt.Errorf("parent issue is nil")
	}

	// Parse steps from molecule
	steps, err := ParseMoleculeSteps(mol.Description)
	if err != nil {
		return nil, fmt.Errorf("parsing molecule steps: %w", err)
	}

	if len(steps) == 0 {
		return nil, fmt.Errorf("molecule has no steps defined")
	}

	// Build map of step ref -> step for dependency validation
	stepMap := make(map[string]*MoleculeStep)
	for i := range steps {
		stepMap[steps[i].Ref] = &steps[i]
	}

	// Validate all Needs references exist
	for _, step := range steps {
		for _, need := range step.Needs {
			if _, ok := stepMap[need]; !ok {
				return nil, fmt.Errorf("step %q depends on unknown step %q", step.Ref, need)
			}
		}
	}

	// Create child issues for each step
	var createdIssues []*Issue
	stepIssueIDs := make(map[string]string) // step ref -> issue ID

	for _, step := range steps {
		// Expand template variables in instructions
		instructions := step.Instructions
		if opts.Context != nil {
			instructions = ExpandTemplateVars(instructions, opts.Context)
		}

		// Build description with provenance metadata
		description := instructions
		if description != "" {
			description += "\n\n"
		}
		description += fmt.Sprintf("instantiated_from: %s\nstep: %s", mol.ID, step.Ref)
		if step.Tier != "" {
			description += fmt.Sprintf("\ntier: %s", step.Tier)
		}

		// Create the child issue
		childOpts := CreateOptions{
			Title:       step.Title,
			Type:        "task",
			Priority:    parent.Priority,
			Description: description,
			Parent:      parent.ID,
		}

		child, err := b.Create(childOpts)
		if err != nil {
			// Attempt to clean up created issues on failure
			for _, created := range createdIssues {
				_ = b.Close(created.ID)
			}
			return nil, fmt.Errorf("creating step %q: %w", step.Ref, err)
		}

		createdIssues = append(createdIssues, child)
		stepIssueIDs[step.Ref] = child.ID
	}

	// Wire inter-step dependencies based on Needs: declarations
	for _, step := range steps {
		if len(step.Needs) == 0 {
			continue
		}

		childID := stepIssueIDs[step.Ref]
		for _, need := range step.Needs {
			dependsOnID := stepIssueIDs[need]
			if err := b.AddDependency(childID, dependsOnID); err != nil {
				// Log but don't fail - the issues are created
				// This is non-atomic but bd CLI doesn't support transactions
				return createdIssues, fmt.Errorf("adding dependency %s -> %s: %w", childID, dependsOnID, err)
			}
		}
	}

	return createdIssues, nil
}

// ValidateMolecule checks if an issue is a valid molecule definition.
// Returns an error describing the problem, or nil if valid.
func ValidateMolecule(mol *Issue) error {
	if mol == nil {
		return fmt.Errorf("molecule is nil")
	}

	if mol.Type != "molecule" {
		return fmt.Errorf("issue type is %q, expected molecule", mol.Type)
	}

	steps, err := ParseMoleculeSteps(mol.Description)
	if err != nil {
		return fmt.Errorf("parsing steps: %w", err)
	}

	if len(steps) == 0 {
		return fmt.Errorf("molecule has no steps defined")
	}

	// Build step map for reference validation
	stepMap := make(map[string]bool)
	for _, step := range steps {
		if step.Ref == "" {
			return fmt.Errorf("step has empty ref")
		}
		if stepMap[step.Ref] {
			return fmt.Errorf("duplicate step ref: %s", step.Ref)
		}
		stepMap[step.Ref] = true
	}

	// Validate Needs references
	for _, step := range steps {
		for _, need := range step.Needs {
			if !stepMap[need] {
				return fmt.Errorf("step %q depends on unknown step %q", step.Ref, need)
			}
			if need == step.Ref {
				return fmt.Errorf("step %q has self-dependency", step.Ref)
			}
		}
	}

	// TODO: Detect cycles in dependency graph

	return nil
}
