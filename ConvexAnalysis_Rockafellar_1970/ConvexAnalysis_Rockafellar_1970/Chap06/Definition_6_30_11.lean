import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_12

noncomputable section

open Function
open scoped Rockafellar

universe u v w

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.11 introduces the perturbation function of the concave
  program associated with a bifunction `G`, namely the slice-wise supremum `u ↦ sup_x G(u, x)`.
- `core/canonical`: the neighboring Chapter 6 owner pattern is the infimum-side
  `Bifunction.perturbationFunction` from Definition 6.29.1, which itself is the curried
  specialization of the Chapter 1 owner `Function.partialInfimum`. The supremum-side dual should
  therefore reuse the matching Chapter 1 owner `Function.partialSupremum`.
- `bridge/view`: the source formulas are exactly the range-supremum expression
  `sSup (Set.range (G u))` and its indexed form `⨆ x, G u x`; no wrapper around the same
  bifunction data is needed.

Domain-style sampling used here:
- `Function.partialSupremum` from `Chap01.Text_5_7_2` as the intrinsic owner for slice-wise
  supremum on product functions;
- `Bifunction.perturbationFunction` from Definition 6.29.1 as the infimum-side owner pattern;
- `Bifunction.objective` from Definition 6.29.12 as the zero-slice owner pattern;
- `Bifunction.maximinValueOn` / `Bifunction.minimaxValueOn` from Definition 36.0.1 as the
  chapter's canonical complete-lattice supremum/infimum surface for bifunction aggregates.

Primitive data vs derived API:
- primitive source data: a bifunction `G : U → X → α`;
- source-facing owner introduced here: `upperPerturbationFunction G`;
- core owner reused upstream: `partialSupremum (Function.uncurry G)`;
- derived API: the pointwise formulas `sSup (Set.range (G u))` and `⨆ x, G u x`.

Ambient minimization:
- the slice-supremum construction itself only uses the supremum-of-sets structure on
  the codomain, so the owner lives over general `α`;
- the Chapter 6 extended-value specialization `WithBotTop α` is recovered by instantiation in
  later duality statements.

Redundant-source-assumption elimination:
- although the source phrases the item for a concave bifunction, the slice-supremum construction
  depends only on the values of `G`; concavity belongs to later theorems, not to this definition.

Layer target: `source-facing`, dual to the infimum-side owner
`Bifunction.perturbationFunction`.
-/

section

variable {U : Type u} {X : Type v} {α : Type w}
variable [SupSet α]

/-- Definition 6.30.11: the perturbation function of the concave program associated with a
bifunction `G` is the pointwise supremum of its slices, i.e. the source object `sup G`. -/
abbrev upperPerturbationFunction (G : U → X → α) : U → α :=
  partialSupremum (Function.uncurry G)

/-- Rockafellar's source-facing notation for the upper perturbation function `sup G`. -/
scoped[Rockafellar] notation "supᵇ(" G ")" => Bifunction.upperPerturbationFunction G

-- Proof sketch: unfold `upperPerturbationFunction`; the right-hand side is exactly the defining
-- slice supremum.
/-- Evaluating `upperPerturbationFunction G` at `u` gives the supremum of the slice `G u` over the
`X`-variable, written as the supremum of its range. -/
@[simp] theorem upperPerturbationFunction_apply_eq_sSup_range
    (G : U → X → α) (u : U) :
    supᵇ(G) u = sSup (Set.range (G u)) := by
  simp [upperPerturbationFunction]

-- Proof sketch: start from `upperPerturbationFunction_apply_eq_sSup_range` and rewrite the range
-- supremum as the indexed supremum with `sSup_range`.
/-- Evaluating `upperPerturbationFunction G` at `u` is the indexed supremum `sup_x G(u, x)`. -/
@[simp] theorem upperPerturbationFunction_apply
    (G : U → X → α) (u : U) :
    supᵇ(G) u = ⨆ x, G u x := by
  rw [upperPerturbationFunction_apply_eq_sSup_range, ← sSup_range]

end

section

variable [Zero U] [SupSet α]

/-- The unperturbed upper perturbation value is the supremum of the objective range. -/
@[simp] theorem upperPerturbationFunction_zero_eq_sSup_range_objective
    (G : U → X → α) :
    supᵇ(G) 0 = sSup (Set.range ((G)₀)) := by
  change supᵇ(G) 0 = sSup (Set.range (G 0))
  rw [upperPerturbationFunction_apply_eq_sSup_range G 0]

/-- The unperturbed upper perturbation value is the indexed supremum of the objective. -/
@[simp] theorem upperPerturbationFunction_zero_eq_iSup_objective
    (G : U → X → α) :
    supᵇ(G) 0 = ⨆ x, (G)₀ x := by
  change supᵇ(G) 0 = ⨆ x, G 0 x
  rw [upperPerturbationFunction_apply G 0]

end

end Bifunction
