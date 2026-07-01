import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1

universe u v w r

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.12 attaches to a bifunction `F : U → X → Y` the
  zero-slice objective `x ↦ F 0 x`; in Chapter 6 this is then used on the canonical
  extended-value layer `WithTopBot α` (with `EReal` as a specialization).
- `core/canonical`: the Chapter 6 owner for those perturbation values is already
  `Bifunction.perturbationFunction` from Definition 6.29.1.
- `bridge/view`: the owner file `Definition_6_29_1` already records both the
  `sInf (Set.range (F u))` evaluation formula and the Chapter 1 first-projection
  linear-image identification.

Domain-style sampling used here:
- `Bifunction.perturbationFunction`;
- `Bifunction.perturbationFunction_apply`;
- `Bifunction.perturbationFunction_apply_eq_sInf_range`;
- `Bifunction.perturbationFunction_eq_linearImage_fst`.

Primitive data vs derived API:
- primitive data: the bifunction `F : U → X → Y`;
- primitive source-facing owners: the zero-slice objective `objective F` and the already existing
  perturbation owner `perturbationFunction F`;
- derived API: both perturbation-function companion theorems are reused from the owner file
  `Definition_6_29_1`.

Layer target:
- `source-facing` for `objective`;
- `core/canonical recall/use` for the perturbation-value owner.

Notation decision: Rockafellar uses the recurring zero-slice objective notation `F₀`, so the
owner file exposes the scoped postfix surface `₀`. In `open scoped Rockafellar`, Lean writes this
as `(F)₀` for a general term and also accepts `F ₀` for a named bifunction.
-/

section Objective

variable {U : Type u} {X : Type v} {Y : Type w} [Zero U]

/-- Definition 6.29.12: the objective function of the generalized convex program associated with a
bifunction `F` is its zero slice. -/
def objective (F : U → X → Y) : X → Y :=
  F 0

end Objective

end Bifunction

namespace Rockafellar

/- Rockafellar's zero-slice objective notation. In `open scoped Rockafellar`, a bifunction term
`F` is written as `(F)₀`; for a named bifunction, Lean also accepts `F ₀`. -/
scoped[Rockafellar] postfix:max "₀" => Bifunction.objective

end Rockafellar

namespace Bifunction

open scoped Rockafellar

section Objective

variable {U : Type u} {X : Type v} {Y : Type w} [Zero U]

@[simp] theorem objective_eq (F : U → X → Y) :
    (F)₀ = F 0 :=
  rfl

@[simp] theorem objective_apply (F : U → X → Y) (x : X) :
    (F)₀ x = F 0 x :=
  rfl

end Objective

section ObjectivePerturbation

variable {U : Type u} {X : Type v} {α : Type r}
variable [Zero U]

/-- The unperturbed perturbation value is the infimum of the objective range. -/
@[simp] theorem perturbationFunction_zero_eq_sInf_range
    [InfSet α]
    (F : U → X → α) :
    infᵇ(F) 0 = sInf (Set.range ((F)₀)) := by
  simpa [objective] using
    (perturbationFunction_apply_eq_sInf_range F (0 : U))

/-- The unperturbed perturbation value is the indexed infimum of the objective. -/
@[simp] theorem perturbationFunction_zero_eq_iInf
    [InfSet α]
    (F : U → X → α) :
    infᵇ(F) 0 = ⨅ x, (F)₀ x := by
  simpa [objective] using (perturbationFunction_apply F (0 : U))

end ObjectivePerturbation

/- Definition 6.29.12 uses the existing Chapter 6 owner
`Bifunction.perturbationFunction` for the perturbation-value function `u ↦ inf_x F u x`. -/
recall perturbationFunction

end Bifunction
