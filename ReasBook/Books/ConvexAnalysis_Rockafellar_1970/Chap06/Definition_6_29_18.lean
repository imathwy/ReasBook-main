import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.18 gives the perturbation function of the generalized convex
  program `(P)` the source notation `inf F`, surfaced canonically in Lean as `infᵇ(F)`, with
  value at `u` equal to the infimum of the slice `F u`.
- `core/canonical`: the owner abstraction is already the Chapter 6 definition
  `Bifunction.perturbationFunction` from Definition 6.29.1.
- `bridge/view`: the displayed source equation `((inf F)(u) = inf_x F u x)` is already the
  companion owner theorem `Bifunction.perturbationFunction_apply`; the owner-literal
  `sInf (Set.range (F u))` form is `Bifunction.perturbationFunction_apply_eq_sInf_range`.

Domain-style sampling used here:
- `Bifunction.perturbationFunction`;
- `Bifunction.perturbationFunction_apply_eq_sInf_range`;
- `Bifunction.perturbationFunction_apply`.

Primitive data vs derived API:
- primitive data: the bifunction `F`;
- primitive owner: `Bifunction.perturbationFunction F`;
- derived API: the value formula at `u`.

Layer target: `core/canonical`, recall-shaped. This item adds no new mathematical owner beyond the
existing Chapter 6 perturbation-function construction.

Notation decision: the stable source-facing Lean notation is the scoped form `infᵇ(F)` from
Definition 6.29.1, which avoids conflict with Lean's global `inf` identifier while tracking the
textbook `inf F` surface.
-/

/- Definition 6.29.18: Rockafellar's perturbation function `inf F`, surfaced as `infᵇ(F)`, is the
existing Chapter 6 owner `Bifunction.perturbationFunction`. The source's concrete
parameter-space and extended-codomain presentation is a specialization of this codomain-general
owner layer. -/
recall perturbationFunction

/- The owner-literal value formula for `infᵇ(F)` at `u` is the infimum of the corresponding slice
range. -/
recall perturbationFunction_apply_eq_sInf_range

/- The displayed source formula `((inf F)(u) = inf_x F u x)` (Lean: `infᵇ(F) u = inf_x F u x`) is
the existing owner-side
evaluation theorem `Bifunction.perturbationFunction_apply`. -/
recall perturbationFunction_apply

end Bifunction
