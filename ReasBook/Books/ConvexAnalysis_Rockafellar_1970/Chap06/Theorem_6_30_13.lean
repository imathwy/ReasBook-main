import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Operations
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_18
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14

noncomputable section

open scoped Rockafellar

universe u v u' v'

namespace Bifunction

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]
variable [AddCommGroup U] [Preorder U] [Module 𝕜 U]
variable [AddCommGroup X] [PartialOrder X] [IsOrderedAddMonoid X] [Module 𝕜 X]
variable [PosSMulMono 𝕜 X]
variable [AddCommGroup UStar] [PartialOrder UStar] [IsOrderedAddMonoid UStar] [Module 𝕜 UStar]
variable [PosSMulMono 𝕜 UStar]
variable [AddCommGroup XStar] [Preorder XStar] [Module 𝕜 XStar]
variable [HasPairing U UStar 𝕜]
variable [HasPairing XStar X 𝕜]

local instance : HasPairing X XStar 𝕜 :=
  HasPairing.swap (X := XStar) (Y := X) (L := 𝕜)

attribute [local instance] Classical.propDecidable

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.13 computes the adjoint of the polyhedral bifunction attached to
  the linear program data `(aStar, a, A)`, together with a dual-side linear map `AT`.
- `core/canonical`: Chapter 6 already owns the LP perturbation bifunction as
  `linearProgram`, the duality transform as `adjoint`, and the LP feasible-region owner as
  `linearProgramFeasibleSet`. The dual feasible region in the theorem is exactly the same owner,
  written intrinsically with `AT : UStar →ₗ[𝕜] XStar` as
  `linearProgramFeasibleSet xStar (-AT) aStar`, so the theorem surface should reuse that owner
  instead of a duplicate raw set comprehension.
- `bridge/view`: the source's displayed inequalities
  `0 ≤ uStar ∧ aStar - AT uStar ≥ xStar` are the explicit membership condition obtained by
  expanding that same owner, so they remain only in explanatory prose rather than as a second
  public set definition. The compatibility between `A` and `AT` is recorded explicitly by
  `hAT : ∀ x y, ⟪A x, y⟫ₚ = ⟪x, AT y⟫ₚ`.

Domain-style sampling used here:
- `linearProgram` and `linearProgram_apply` from `Definition_6_30_18`;
- `linearProgramFeasibleSet` and `mem_linearProgramFeasibleSet_iff` from `Definition_6_30_18`;
- `adjoint` from `Definition_6_30_14`;
- the indicator owner `δ[𝕜](· | C)` from `Defintion_4_8_1`;
- the canonical pairing owner `⟪·, ·⟫ₚ`;
- linear-map expressions `A x` and `AT uStar`.

Layer target: `source-facing`, keeping the source formula but reusing the canonical owners
`linearProgram aStar a A`, `adjoint`, and the dual feasible-set owner
`linearProgramFeasibleSet xStar (-AT) aStar` instead of preserving coordinate-level wrappers.
-/

-- Proof sketch: start from the defining formula
-- `adjoint F xStar uStar = -((Function.uncurry F)⋆ (-uStar, xStar))`, substitute
-- `F = linearProgram aStar a A`, and compute the conjugate by separating the
-- nonnegativity constraint on `x` from the slack-variable description of `a - A x ≤ u`. The
-- pairing-compatibility identity `hAT` converts `⟪A x, uStar⟫` into `⟪x, AT uStar⟫`.
/-- Theorem 6.30.13: the adjoint of the canonical LP owner
`linearProgram aStar a A`,
equivalently `(u, x) ↦ ⟪aStar, x⟫ + δ[𝕜](x | 0 ≤ x, a ≤ A x + u)`, is
`(xStar, uStar) ↦ ⟪a, uStar⟫ - δ[𝕜](uStar | linearProgramFeasibleSet xStar (-AT) aStar)`,
where membership in that owner is exactly the source condition
`0 ≤ uStar ∧ aStar - AT uStar ≥ xStar`, under the pairing compatibility
`∀ x y, ⟪A x, y⟫ₚ = ⟪x, AT y⟫ₚ`. -/
theorem adjointFunction_linearProgram_apply
    (aStar xStar : XStar) (a : U) (uStar : UStar)
    (A : X →ₗ[𝕜] U) (AT : UStar →ₗ[𝕜] XStar)
    (hAT : ∀ x : X, ∀ y : UStar, (⟪A x, y⟫ₚ : 𝕜) = ⟪x, AT y⟫ₚ) :
    (linearProgram aStar a A)⋆ xStar uStar =
      (⟪a, uStar⟫ₚ : WithBotTop 𝕜) -
        δ[𝕜](uStar | linearProgramFeasibleSet xStar (-AT) aStar) := by
  sorry

-- Proof sketch: rewrite the indicator form in
-- `adjointFunction_linearProgram_apply`. On the feasible set the indicator is `0`, so the value
-- is `⟪a, uStar⟫`; outside the feasible set the indicator is `⊤`, and subtracting `⊤` in
-- `WithBotTop 𝕜` yields `⊥`, i.e. `-∞`.
/-- Equivalent case-split form of the adjoint value for the canonical LP bifunction, phrased using
the reused dual feasible-set owner. This owner membership is equivalent to the source inequalities
`0 ≤ uStar ∧ aStar - AT uStar ≥ xStar`, under the pairing compatibility
`∀ x y, ⟪A x, y⟫ₚ = ⟪x, AT y⟫ₚ`. -/
theorem adjointFunction_linearProgram_apply_eq_ite
    (aStar xStar : XStar) (a : U) (uStar : UStar)
    (A : X →ₗ[𝕜] U) (AT : UStar →ₗ[𝕜] XStar)
    (hAT : ∀ x : X, ∀ y : UStar, (⟪A x, y⟫ₚ : 𝕜) = ⟪x, AT y⟫ₚ) :
    (linearProgram aStar a A)⋆ xStar uStar =
      if uStar ∈ linearProgramFeasibleSet xStar (-AT) aStar then
        (⟪a, uStar⟫ₚ : WithBotTop 𝕜)
      else
        ⊥ := by
  rw [adjointFunction_linearProgram_apply (aStar := aStar) (xStar := xStar) (a := a)
    (uStar := uStar) (A := A) (AT := AT) hAT]
  by_cases hmem : uStar ∈ linearProgramFeasibleSet xStar (-AT) aStar
  · have hnot : uStar ∉ (linearProgramFeasibleSet xStar (-AT) aStar)ᶜ := by
      simpa using hmem
    rw [if_pos hmem, Set.indicator_of_notMem hnot]
    calc
      (⟪a, uStar⟫ₚ : WithBotTop 𝕜) - 0
          = (⟪a, uStar⟫ₚ : WithBotTop 𝕜) + (-0) := by
            rw [WithBotTop.sub_eq_add_neg]
      _ = (⟪a, uStar⟫ₚ : WithBotTop 𝕜) + 0 := by
            rw [WithBotTop.neg_zero]
      _ = (⟪a, uStar⟫ₚ : WithBotTop 𝕜) := by
            rw [add_zero]
  · have hcompl : uStar ∈ (linearProgramFeasibleSet xStar (-AT) aStar)ᶜ := by
      simpa using hmem
    rw [if_neg hmem, Set.indicator_of_mem hcompl]
    exact (WithBotTop.sub_top (x := (⟪a, uStar⟫ₚ : WithBotTop 𝕜)))

end

end Bifunction
