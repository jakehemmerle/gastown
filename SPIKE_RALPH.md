# Spike: Ralph as Rig Config Default

## Executive Summary

**Feasible. Small effort (~50-80 lines of Go).**

Adding a `mode` (or `ralph`) field to `RigSettings` follows the exact same pattern
as the existing `Agent` field. The resolution chain would be:
CLI flag (`--ralph`) → rig config (`mode`) → town config (`default_mode`) → default (`""` / normal).
Mountain requires **zero changes** — it dispatches via `gt sling`, which handles all config
resolution. The main risk is the interaction between rig-level ralph and per-sling overrides;
a `--no-ralph` CLI flag would be needed for opt-out. Estimated effort: 1-2 hours implementation,
including tests.

---

## Current `--agent` Resolution Flow

The `--agent` flag has the most mature multi-level resolution chain in the codebase
and serves as the direct template for ralph config.

### Resolution order (with CLI override):

1. **CLI flag** (`--agent codex`) — `sling.go:125,151`
2. Stored in `ScheduleOptions.Agent` — `sling_schedule.go:47-62`
3. Passed through `SlingParams.Agent` → `SlingSpawnOptions.Agent` — `sling_dispatch.go:19-46`, `polecat_spawn.go:51-59`
4. At spawn time, `ResolveAgentConfigWithOverride()` called — `polecat_spawn.go:385-395`

### Resolution order (without CLI override):

Via `resolveAgentConfigInternal()` in `config/loader.go:1110-1151`:

| Priority | Source | Code |
|----------|--------|------|
| 1 | Rig `Runtime` (deprecated) | `loader.go:1118-1123` |
| 2 | Rig `Agent` field | `loader.go:1140-1141` |
| 3 | Town `DefaultAgent` | `loader.go:1142-1143` |
| 4 | Hardcoded `"claude"` | `loader.go:1145` |

### Role-based resolution adds two more layers:

Via `resolveRoleAgentConfigCore()` in `loader.go:1533-1629`:

| Priority | Source |
|----------|--------|
| 1 | Rig `RoleAgents[role]` |
| 2 | Town `RoleAgents[role]` |
| 3 | Falls through to agent resolution above |

### Key types:

- `RigSettings.Agent` — `config/types.go:635`
- `TownSettings.DefaultAgent` — `config/types.go:55`
- `RigSettings.RoleAgents` — `config/types.go:647`

---

## Current `--ralph` Flow

### CLI flag definition:

- **Variable:** `slingRalph bool` — `sling.go:133`
- **Flag:** `--ralph` (bool, default false) — `sling.go:160`

### Storage path:

1. `slingRalph` bool → `ScheduleOptions.Ralph` — `sling_schedule.go` (opts struct)
2. Converted to mode string: `if opts.Ralph { fields.Mode = "ralph" }` — `sling_schedule.go:161-163`
3. Stored in `SlingContextFields.Mode` — `scheduler/capacity/pipeline.go:34`
4. Persisted to bead attachment fields — `beads/fields.go:23`
5. Written to agent bead via `updateAgentMode()` — `sling_helpers.go:1180-1204`

### Reconstruction during dispatch:

- `ReconstructFromContext()` reads `ctx.Mode` — `pipeline.go:185`
- Mode flows through `SlingParams.Mode` → spawn chain

### Execution behavior:

- **Prime-time output:** `prime.go:802-805` — if `attachment.Mode == "ralph"`, calls `outputRalphLoopDirective()` instead of step-by-step formula display
- **Ralph loop directive:** `prime.go:824-858` — emits iterative workflow instructions (commit frequently, loop until acceptance criteria met)
- **Stuck detector thresholds:** `tui/feed/stuck.go:235-242` — ralph mode gets 120min stalled / 240min GUPP (vs. 15min / 30min normal)
- **Task-only restriction:** `sling_schedule.go:386-389` — ralph rejected for convoy and epic modes

---

## Proposed Changes

### 1. Add `Mode` field to `RigSettings` (`config/types.go`)

```go
// types.go — add to RigSettings struct (after Agent fields, ~line 653)

// Mode sets the default execution mode for polecats in this rig.
// Valid values: "" (normal step-by-step), "ralph" (iterative loop mode).
// CLI --ralph flag overrides this. CLI --no-ralph explicitly disables.
// If empty, falls through to town config, then to normal mode.
Mode string `json:"mode,omitempty"`
```

### 2. Add `DefaultMode` to `TownSettings` (`config/types.go`)

```go
// types.go — add to TownSettings struct (after DefaultAgent, ~line 56)

// DefaultMode sets the default execution mode for all rigs.
// Valid values: "" (normal), "ralph" (iterative loop mode).
// Individual rigs can override via RigSettings.Mode.
DefaultMode string `json:"default_mode,omitempty"`
```

### 3. Add resolution function (`config/loader.go`)

New function, parallel to `resolveAgentConfigInternal()`:

```go
// ResolveModeConfig resolves the execution mode for a rig.
// Resolution order: rig Mode → town DefaultMode → "" (normal).
func ResolveModeConfig(townRoot, rigPath string) string {
    rigSettings, err := LoadRigSettings(RigSettingsPath(rigPath))
    if err == nil && rigSettings != nil && rigSettings.Mode != "" {
        return rigSettings.Mode
    }

    townSettings, err := LoadOrCreateTownSettings(TownSettingsPath(townRoot))
    if err == nil && townSettings.DefaultMode != "" {
        return townSettings.DefaultMode
    }

    return "" // normal mode
}
```

### 4. Wire into schedule path (`sling_schedule.go`)

Modify the mode assignment logic (~line 161):

```go
// Current:
if opts.Ralph {
    fields.Mode = "ralph"
}

// Proposed:
if opts.Ralph {
    fields.Mode = "ralph"
} else if opts.NoRalph {
    fields.Mode = "" // explicit override of rig/town default
} else {
    // Resolve from rig/town config
    resolved := config.ResolveModeConfig(townRoot, rigPath)
    if resolved != "" {
        fields.Mode = resolved
    }
}
```

### 5. Add `--no-ralph` CLI flag (`sling.go`)

```go
// sling.go — new variable (~line 133)
slingNoRalph bool // --no-ralph: explicitly disable ralph mode (override rig config)

// sling.go — flag registration (~line 160)
slingCmd.Flags().BoolVar(&slingNoRalph, "no-ralph", false,
    "Disable Ralph Wiggum loop mode (override rig-level default)")
```

### 6. Pass through schedule options

Add `NoRalph bool` to `ScheduleOptions` struct, wire it through like `Ralph`.

---

## Mountain Integration Analysis

**Mountain requires ZERO changes.**

Mountain's dispatch chain:

```
gt mountain <epic-id>
  → dispatchWave1()
    → dispatchTaskDirect(townRoot, beadID, rig)
      → exec.Command("gt", "sling", beadID, rig)
```

Source: `convoy_launch.go:25-37`

Key insight: Mountain calls `gt sling` as a subprocess. The sling command handles
all config resolution internally via `loadRigCommandVars()` (`sling_helpers.go:1080-1139`).
The proposed `ResolveModeConfig()` would be called during sling's schedule phase,
meaning mountain inherits rig-level ralph config automatically.

The ConvoyManager daemon (auto-feeder for subsequent waves) also dispatches via
`gt sling` (`convoy_manager.go:460`), so it inherits the same behavior.

**However:** Ralph is currently a task-only flag (`sling_schedule.go:386-389`) —
it's rejected for convoy and epic modes. Mountain creates convoys. This means:

- Mountain-dispatched **individual tasks within the convoy** would pick up ralph
  mode from rig config (since each task is slung individually).
- The convoy itself doesn't use ralph mode — only the individual task slings do.
- This is correct behavior: ralph mode applies to the polecat's execution style,
  not the convoy's orchestration.

---

## Edge Cases and Open Questions

### 1. Rig-level ralph + specific sling wants non-ralph

**Solution:** `--no-ralph` CLI flag (proposed above). This follows the same pattern as
how other flags work — explicit CLI flags always win.

### 2. Ralph interaction with formula/molecule step system

**No conflict.** Ralph mode already works with formulas — it shows the same formula
steps but wraps them in iterative loop instructions (`prime.go:840-843`). The formula
steps are guidance, not hard gates, in ralph mode. Rig-level config wouldn't change
this interaction.

### 3. Crew workers vs polecats

**Consider adding role-level mode config.** Similar to `RoleAgents`, a `RoleModes`
map could allow different defaults per role:

```go
// Optional enhancement (not required for MVP):
RoleModes map[string]string `json:"role_modes,omitempty"`
// Example: {"polecat": "ralph", "crew": ""}
```

For MVP, a single `Mode` field on `RigSettings` is sufficient. Role-level granularity
can be added later if needed.

### 4. Validation

The `Mode` field should be validated to only accept `""` or `"ralph"`. Add to
`validateRigSettings()` in `loader.go`:

```go
if settings.Mode != "" && settings.Mode != "ralph" {
    return fmt.Errorf("invalid mode %q: must be empty or \"ralph\"", settings.Mode)
}
```

### 5. Stuck detector awareness

The stuck detector (`tui/feed/stuck.go:235-242`) already checks `isRalphMode(issue)`
by reading the mode from the bead. Since rig-level config flows through the same
`fields.Mode = "ralph"` path, the stuck detector picks it up automatically. No changes needed.

### 6. Batch sling (`sling_batch.go`)

Batch sling also converts `slingRalph` → mode string (`sling_batch.go:119-122`).
The same resolution logic needs to be added here, or extracted to a shared helper.

---

## Recommendation

**Go.** Implement as described above.

### Approach:

1. Add `Mode` to `RigSettings` and `DefaultMode` to `TownSettings` (~10 lines)
2. Add `ResolveModeConfig()` to `loader.go` (~15 lines)
3. Add `--no-ralph` flag to sling (~5 lines)
4. Wire resolution into `sling_schedule.go` and `sling_batch.go` (~20 lines)
5. Add validation (~5 lines)
6. Tests (~30-50 lines)

**Total: ~50-80 lines of implementation + ~30-50 lines of tests.**

The pattern is well-established (Agent field is the direct precedent), the mountain
integration is free, and the risk is low. The main thing to get right is the
`--no-ralph` override flag so individual slings can opt out of a rig default.
