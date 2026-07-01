import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_11
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14

noncomputable section

open scoped Rockafellar

universe u v u' v' w

namespace Bifunction

section

variable {U : Type u} {X : Type v} {α : Type w}
variable (UStar : Type u') (XStar : Type v')
variable [AddGroup α] [ConditionallyCompleteLattice α]
variable [Neg UStar] [Zero XStar]
variable [HasPairing U UStar α] [HasPairing X XStar α]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.17 introduces the notion of a Kuhn--Tucker vector for the dual
  program `(P*)` associated with a bifunction `F`.
- `core/canonical`: the Chapter 6 owner layer already present is the adjoint notation `F⋆`
  together with `upperPerturbationFunction` for the dual value function
  `x⋆ ↦ sup_u F⋆(x⋆, u⋆)`, and the Chapter 12 Fenchel owner `convexConjugate` applied to
  `- upperPerturbationFunction (F⋆ : XStar → UStar → WithBotTop α)` once the pairing is read in
  the reversed orientation `HasPairing XStar X α`.
- `bridge/view`: the source's displayed two-variable supremum is kept as the source-facing slice
  expansion of that canonical conjugate owner; there is no separate public `dualUpper`,
  `dualOptimalValue`, or finiteness wrapper.

Domain-style sampling used here:
- `Bifunction.IsKuhnTuckerVector` from Definition 6.29.19 as the primal-side owner pattern;
- `Bifunction.upperPerturbationFunction` from Definition 6.30.11;
- `Bifunction.adjoint` and the notation `F⋆` from Definition 6.30.14;
- `convexConjugate` and `convexConjugate_eq_iSup_pairing_sub` from `Chap03.Defn_12_2`;
- the zero-slice owner recall from Definition 6.30.16.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → WithBotTop α` and a primal vector `x : X`;
- primitive owner introduced here: `IsDualKuhnTuckerVector UStar XStar F x`;
- primitive fields: interval-membership finiteness of the defining supremum and its equality
  with the dual value `upperPerturbationFunction (F⋆ : XStar → UStar → WithBotTop α) 0`;
- derived API: bundled finiteness, finiteness of that dual value, and the bridge from the source
  supremum to the canonical Fenchel conjugate owner.

Layer target: `source-facing`. The source genuinely defines a Kuhn--Tucker property of primal
vectors, so the class remains primitive on the source formula, while the companion conjugate layer
is read directly through `f⋆` under the swapped pairing `HasPairing.swap`.
-/

local notation "dualUpper(" F ")" =>
  (supᵇ((adjoint XStar UStar F : XStar → UStar → WithBotTop α)))

local notation "shiftedSup(" F ", " x ")" =>
  (⨆ xStar : XStar,
    ⟪x, xStar⟫ₚ + dualUpper(F) xStar)

local instance : HasPairing XStar X (WithBotTop α) :=
  HasPairing.swap (X := X) (Y := XStar) (L := WithBotTop α)

/-- Definition 6.30.17: a vector `x` is a Kuhn--Tucker vector for the dual program associated
with `F` when the supremum of the source dual expression
`x⋆ ↦ ⟪x, x⋆⟫ₚ + upperPerturbationFunction (F⋆ : XStar → UStar → WithBotTop α) x⋆` is finite and
equals the dual value `upperPerturbationFunction (F⋆ : XStar → UStar → WithBotTop α) 0`. -/
class IsDualKuhnTuckerVector (F : U → X → WithBotTop α) (x : X) : Prop where
  supremum_mem_Ioo : shiftedSup(F, x) ∈ Set.Ioo (⊥ : WithBotTop α) ⊤
  supremum_eq_upperPerturbationFunction_adjoint_zero :
    shiftedSup(F, x) = dualUpper(F) 0

omit [Zero XStar] in
/-- The source supremum from Definition 6.30.17 is exactly the Fenchel conjugate of the negated
dual upper-perturbation function, read directly through `f⋆` with the swapped pairing
`HasPairing.swap`. -/
theorem shiftedSup_eq_convexConjugate_neg_upperPerturbationFunction_adjoint
    (F : U → X → WithBotTop α) (x : X) :
    shiftedSup(F, x) = ((- dualUpper(F))⋆ : X → WithBotTop α) x := by
  rw [convexConjugate_eq_iSup_pairing_sub
      (X := XStar) (Y := X) (L := WithBotTop α) (f := - dualUpper(F)) (y := x)]
  refine iSup_congr ?_
  intro xStar
  change ⟪x, xStar⟫ₚ + dualUpper(F) xStar =
      ((⟪xStar, x⟫ₚ : WithBotTop α) - (-dualUpper(F) xStar))
  change ⟪x, xStar⟫ₚ + dualUpper(F) xStar =
      (⟪x, xStar⟫ₚ - (-dualUpper(F) xStar))
  rw [WithBotTop.sub_eq_add_neg, neg_neg]

namespace IsDualKuhnTuckerVector

variable {F : U → X → WithBotTop α} {x : X}

/-- Lower finiteness bound from the defining interval-membership field. -/
theorem supremum_bot_lt (h : IsDualKuhnTuckerVector UStar XStar F x) :
    ⊥ < shiftedSup(F, x) :=
  h.supremum_mem_Ioo.1

/-- Upper finiteness bound from the defining interval-membership field. -/
theorem supremum_lt_top (h : IsDualKuhnTuckerVector UStar XStar F x) :
    shiftedSup(F, x) < ⊤ :=
  h.supremum_mem_Ioo.2

/-- A dual Kuhn--Tucker vector makes the defining dual supremum finite. -/
theorem supremum_finite (h : IsDualKuhnTuckerVector UStar XStar F x) :
    ⊥ < shiftedSup(F, x) ∧ shiftedSup(F, x) < ⊤ :=
  ⟨h.supremum_bot_lt, h.supremum_lt_top⟩

/-- A dual Kuhn--Tucker vector identifies the dual value
`upperPerturbationFunction (F⋆ : XStar → UStar → WithBotTop α) 0` with the defining supremum. -/
theorem upperPerturbationFunction_adjoint_zero_eq_supremum
    (h : IsDualKuhnTuckerVector UStar XStar F x) :
    dualUpper(F) 0 = shiftedSup(F, x) :=
  h.supremum_eq_upperPerturbationFunction_adjoint_zero.symm

/-- A dual Kuhn--Tucker vector identifies the swapped-pairing Fenchel conjugate
`((- upperPerturbationFunction (adjoint XStar UStar F))⋆ : X → WithBotTop α)` at `x`
with the dual value `upperPerturbationFunction (adjoint XStar UStar F) 0`. -/
theorem
    convexConjugate_neg_upperPerturbationFunction_adjoint_eq_upperPerturbationFunction_adjoint_zero
    (h : IsDualKuhnTuckerVector UStar XStar F x) :
    ((- dualUpper(F))⋆ : X → WithBotTop α) x = dualUpper(F) 0 := by
  rw [← shiftedSup_eq_convexConjugate_neg_upperPerturbationFunction_adjoint UStar XStar F x,
    h.supremum_eq_upperPerturbationFunction_adjoint_zero]

/-- A dual Kuhn--Tucker vector forces the dual value
`upperPerturbationFunction (F⋆ : XStar → UStar → WithBotTop α) 0` to lie in the finite interval
`Set.Ioo (⊥ : WithBotTop α) ⊤`. -/
theorem upperPerturbationFunction_adjoint_zero_mem_Ioo
    (h : IsDualKuhnTuckerVector UStar XStar F x) :
    dualUpper(F) 0 ∈ Set.Ioo (⊥ : WithBotTop α) ⊤ := by
  rw [h.upperPerturbationFunction_adjoint_zero_eq_supremum]
  exact h.supremum_mem_Ioo

/-- A dual Kuhn--Tucker vector forces the dual value
`upperPerturbationFunction (F⋆ : XStar → UStar → WithBotTop α) 0` to be finite. -/
theorem upperPerturbationFunction_adjoint_zero_finite
    (h : IsDualKuhnTuckerVector UStar XStar F x) :
    ⊥ < dualUpper(F) 0 ∧ dualUpper(F) 0 < ⊤ := by
  exact h.upperPerturbationFunction_adjoint_zero_mem_Ioo

end IsDualKuhnTuckerVector

end

end Bifunction
