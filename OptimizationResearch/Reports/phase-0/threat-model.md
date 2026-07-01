# Phase 0 Threat Model

## Protected assets

- Read-only source projects.
- Secrets and credential files.
- Fixed corpus, benchmark, and experiment records.
- Canonical Core decisions.

## Threats and controls

| Threat | Control | Status |
|---|---|---|
| Direct source-project write | Resolved-path policy + read-only bubblewrap mount | Enforced and tested |
| Parent traversal | Resolved-path policy + read-only bubblewrap mount | Enforced and tested |
| Symlink escape | Resolved-path policy + resolved writable bind | Enforced and tested |
| Secret-like files entering snapshots | Snapshot exclusion | Enforced and tested |
| Lean placeholder introduced | Placeholder scanner | Enforced in explicit verification; automatic lifecycle invocation pending |
| Source changed during task | Read-only bubblewrap mount + before/after digest hook | Enforced in sandbox; digest integration available |
| Invalid structured record | Record validator | Implemented for core record kinds |
| Dangerous arbitrary shell command | Sandbox and command review | Partly external; no project-local general shell interceptor |
| Network/high-cost action | Explicit approval | Soft project rule plus environment policy |

## Residual risks

An unrelated process launched outside the Harness is outside project-local
policy control. Formal experiment runs must use the bubblewrap command wrapper;
the repository is mounted read-only and only `OptimizationResearch/` is rebound
writable. The environment sandbox remains a second control.

## Integration probe

- A sandboxed write to `OptimizationResearch/Runs/` succeeded.
- A sandboxed write to `Nesterov/` failed with a read-only-filesystem error.
- Network is unshared by default.
