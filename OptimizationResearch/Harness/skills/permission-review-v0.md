# Permission Review Skill v0

## Inputs

Permissions config, policy tests, and Hook results.

## Outputs

Allow/deny findings, bypass findings, hard/soft constraint classification, and
blocking status.

## Checks

- Source writes are denied.
- Parent traversal and symlink escape are denied.
- Failures become structured findings.

