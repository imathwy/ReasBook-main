# Metrics Dictionary v0

| Metric | Definition |
|---|---|
| top-k recall | Fraction of tasks whose reviewed target appears in the first k retrieved candidates |
| relation precision | Reviewed correct relation claims divided by all accepted relation claims |
| hard-negative false-positive rate | Hard negatives accepted as reusable relations divided by reviewed hard negatives |
| statement fidelity | Human rubric result for preservation of assumptions, quantifiers, domain, and conclusion |
| human review time | Active review minutes recorded per task |
| human modification | Changed Lean lines or structured correction actions after Agent output |
| coordination time | Time spent preparing, invoking, and integrating a Subagent result |
| net review value | Validated blocking findings weighted by severity minus declared review/coordination cost |
| invalid run | A run violating frozen configuration, leakage, artifact, or stopping rules |

All metrics are reported per task as well as in aggregate. Failed, unknown, and
negative runs remain in the dataset.

