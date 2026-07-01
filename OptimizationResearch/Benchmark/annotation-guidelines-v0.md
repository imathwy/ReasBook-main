# Benchmark Annotation Guidelines v0

## Scope

The v0 file contains candidates, not gold labels. Reviewers classify each pair
as syntactic equivalence, provable equivalence, implication, specialization,
generalization, compatible adapter, related but not reusable, conflict, or
unknown.

## Required evidence

- Exact declaration names and source files.
- Differences in types, assumptions, domains, codomains, and typeclasses.
- A Lean obligation when the proposed relation is formally checkable.
- A reason for `unknown`; uncertainty is not a failed annotation.

## Review

One reviewer proposes a label and evidence. A second review or human decision
is required for gold status. Disagreement remains `unknown` until resolved.

## Leakage and versioning

Test gold labels are not provided to the Agent. Any task, split, or label change
creates a new benchmark version or an explicit immutable change record.

