# Corpus Audit Skill v0

## When to use

Use for a read-only audit of one candidate Lean optimization project.

## Inputs

Project path, fixed revision/content identifier, build command, and audit rubric.

## Outputs

Structured project facts, build boundary, topic evidence, declaration samples,
risks, and uncertainty.

## Method

1. Confirm read-only scope and project configuration.
2. Record toolchain, libraries, file count, source and license status.
3. Run the approved build check.
4. Search optimization topics and sample candidate declarations.
5. Record evidence without deciding whether the project is selected.

## Checks

- No source file changed.
- Required fields are present.
- Claims cite files or command results.

## Failure handling

Record bounded failure and uncertainty; do not repair the source project.

