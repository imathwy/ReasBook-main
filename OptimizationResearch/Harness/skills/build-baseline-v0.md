# Build Baseline Skill v0

## Inputs

Project path, corpus version, toolchain, and approved build command.

## Outputs

Exit status, duration, bounded error summary, and source-tree before/after
digests.

## Checks

- The source digest is unchanged.
- Existing failures are not attributed to the Harness.
- No dependency update command is run.

