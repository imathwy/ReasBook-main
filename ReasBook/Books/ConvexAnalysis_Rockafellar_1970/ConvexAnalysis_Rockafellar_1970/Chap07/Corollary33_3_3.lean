import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Operations
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_42
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2

noncomputable section

universe u v u' v'

open scoped Rockafellar

namespace Bifunction

section

/-!
Source/core/bridge triage:

- `source-facing`: Corollary33.3.3 reconstructs a closed convex generator from a finite
  concave-convex kernel on `C × D`, then identifies the corresponding primal and adjoint slice
  formulas and the two effective domains.
- `core/canonical`: the owner layer already present upstream is `saddleExtension`,
  `upperBoundaryExtension`, `SaddleFunction.IsLowerClosed`, `SaddleFunction.IsUpperClosed`,
  `Bifunction.IsClosedConvex`, `lowerPairing XStar`, `upperAdjointPairing XStar UStar`, and
  `Bifunction.adjoint XStar UStar`, at the same finite-dimensional continuous-linear-pairing
  ambient layer already used by `Corollary33_2_1`, `Theorem33_0_39`, `Corollary33_3_1`,
  `Theorem_34_2`, and `Corollary33_1_3`.
- `bridge/view`: the upper representative is owned by `upperAdjointPairing XStar UStar`, the
  general-dual bridge behind Chapter 34's self-dual `upperPairing`, instead of being repeated as
  a raw lambda or collapsed to the self-dual specialization `U = U⋆`, `X = X⋆`.

Domain-style sampling used here:
- `Bifunction.lowerPairing` from `Chap07.Defn_34_2`;
- `Bifunction.upperAdjointPairing` from `Chap07.Defn_34_2`;
- `Bifunction.adjoint` from `Chap06.Definition_6_30_14`;
- `Bifunction.existsUnique_closedConvex_generator` from `Chap07.Theorem_34_2`;
- `Bifunction.eq_convexConjugate_slice_of_mem_omega` and
  `Bifunction.adjoint_eq_concaveConjugate_slice_of_mem_omega` from
  `Chap07.Theorem_34_2`;
- `Bifunction.slice_eq_iSup_pairing_sub_sliceConjugate_of_graphPolyhedral_of_proper_of_mem_dom`
  from `Chap07.Corollary33_1_3`;
- `SaddleFunction.IsLowerClosed` and `SaddleFunction.IsUpperClosed` from
  `Chap07.Definition33_0_42`.

Primitive data vs derived API:
- primitive source data: a finite kernel `K : U → XStar → ℝ` on `C × D`;
- primitive reconstructed owner: a closed convex bifunction `F : U → X → EReal`;
- derived API here: the lower representative identity, the upper adjoint-side representative
  identity, and the resulting pointwise/domain formulas.

Layer target: `source-facing`, with explicit primal/dual spaces rather than the old self-dual
model.
-/

open SaddleFunction

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [TopologicalSpace U] [AddCommGroup U] [Module ℝ U]
variable [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [FiniteDimensional ℝ U] [T2Space U]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module ℝ UStar]
variable [IsTopologicalAddGroup UStar] [ContinuousSMul ℝ UStar]
variable [FiniteDimensional ℝ UStar] [T2Space UStar]
variable [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
variable [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [FiniteDimensional ℝ X] [T2Space X]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module ℝ XStar]
variable [IsTopologicalAddGroup XStar] [ContinuousSMul ℝ XStar]
variable [FiniteDimensional ℝ XStar] [T2Space XStar]
variable [HasLinearPairing U UStar ℝ] [HasContinuousPairing U UStar ℝ]
variable [HasLinearPairing X XStar ℝ] [HasContinuousPairing X XStar ℝ]
variable [HasLinearPairing XStar X ℝ] [HasContinuousPairing XStar X ℝ]

variable {C : Set U} {D : Set XStar} {K : U → XStar → ℝ}

attribute [local instance] Classical.propDecidable

section ContinuousConcaveConvexKernel

variable (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
variable (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
variable (hK_cont : ContinuousOn (Function.uncurry K) (C ×ˢ D))
variable (hK_shape : IsConcaveConvexOn ℝ C D K)

section Existence

variable (hC_nonempty : C.Nonempty) (hD_nonempty : D.Nonempty)

-- Proof sketch: use continuity of `K` on the closed sets `C` and `D` to identify the lower
-- boundary extension with the closed concave-convex representative required by the Chapter 34
-- reconstruction theorem, then recover the unique closed convex generator from that lower
-- representative.
/-- Corollary33.3.3 (1): if `C` and `D` are nonempty closed convex sets and `K` is a finite
continuous concave-convex kernel on `C × D`, then the canonical lower boundary extension `K₁`
is the lower representative of a unique closed convex bifunction on `U × X`. -/
theorem existsUnique_closedConvex_generator_of_continuousOn_isConcaveConvexOn
    :
    ∃! F : U → X → EReal,
      IsClosedConvex F ∧ saddleExtension K C D = lowerPairing XStar F := sorry

end Existence

-- Proof sketch: once clause (1) reconstructs the unique closed convex generator from the lower
-- representative, the upper closedness computation for the same boundary-extension pair
-- identifies its upper adjoint-side representative with the upper boundary extension.
/-- Corollary33.3.3 (2): the unique generator furnished by clause (1) has upper adjoint-side
representative equal to the upper boundary extension `K₂`. -/
theorem upperBoundaryExtension_eq_upperAdjointPairing_of_closedConvex_generator
    {F : U → X → EReal}
    (hF : IsClosedConvex F)
    (hLower : saddleExtension K C D = lowerPairing XStar F) :
    upperBoundaryExtension K C D = upperAdjointPairing XStar UStar F := sorry

-- Proof sketch: continuity of the finite branch on the closed product `C × D` identifies the
-- lower boundary extension with the second-variable closure fixed point required by lower
-- closedness.
/-- Corollary33.3.3 (3): the canonical lower boundary extension `K₁` of a finite continuous
concave-convex kernel is lower closed. -/
theorem isLowerClosed_saddleExtension_of_continuousOn_isConcaveConvexOn
    :
    IsLowerClosed (saddleExtension K C D) := sorry

-- Proof sketch: once the lower extension is identified with the first partial closure of the
-- finite branch, applying the second partial closure yields the upper boundary extension, so the
-- upper fixed-point equation follows.
/-- Corollary33.3.3 (4): the canonical upper boundary extension `K₂` of the same kernel is upper
closed. -/
theorem isUpperClosed_upperBoundaryExtension_of_continuousOn_isConcaveConvexOn
    :
    IsUpperClosed (upperBoundaryExtension K C D) := sorry

end ContinuousConcaveConvexKernel

section LowerGenerator

variable {F : U → X → EReal}
variable (hF : IsClosedConvex F)
variable (hLower : saddleExtension K C D = lowerPairing XStar F)

-- Proof sketch: recover each slice `F u` from the lower representative identity `K₁ =
-- lowerPairing XStar F` by the Chapter 34 reconstruction formula; on `u ∈ C` this becomes the
-- Fenchel supremum over the finite branch `xStar ∈ D`, while off `C` the lower boundary
-- extension forces the value `⊤`.
/-- Corollary33.3.3 (5): the closed convex generator determined by the lower boundary extension
has the source Fenchel-supremum formula for its primal slices. -/
theorem closedConvex_generator_apply_eq_iSup_sub_of_saddleExtension_eq_lowerPairing
    (u : U) (x : X) :
    F u x =
      if u ∈ C then
        ⨆ xStar : D, ((⟪x, (xStar : XStar)⟫ₚ : ℝ) : EReal) - (K u xStar : EReal)
      else ⊤ := sorry

-- Proof sketch: the previous pointwise formula shows that for `u ∈ C` the slice `F u` is finite
-- somewhere on `D`, while off `C` the slice is identically `⊤`; this is exactly the
-- nonemptiness criterion defining `dom F`.
/-- Corollary33.3.3 (7): the closed convex generator determined by the boundary extensions has
primal domain exactly `C`. -/
theorem sliceDomain_eq_of_saddleExtension_eq_lowerPairing :
    dom F = C := sorry

end LowerGenerator

section UpperGenerator

variable {F : U → X → EReal}
variable (hF : IsClosedConvex F)
variable (hUpper : upperBoundaryExtension K C D = upperAdjointPairing XStar UStar F)

local notation "F⋆" => adjoint XStar UStar F

-- Proof sketch: apply the adjoint-side Chapter 34 reconstruction formula to the upper
-- representative identity; on `xStar ∈ D` this yields the displayed infimum over `u ∈ C`, while
-- off `D` the upper boundary extension forces the adjoint slice value `⊥`.
/-- Corollary33.3.3 (6): the same closed convex generator has the source infimum formula for its
adjoint slices. -/
theorem adjointFunction_apply_eq_iInf_sub_of_upperBoundaryExtension_eq_upperAdjointPairing
    (xStar : XStar) (uStar : UStar) :
    F⋆ xStar uStar =
      if xStar ∈ D then
        ⨅ u : C, ((⟪(u : U), uStar⟫ₚ : ℝ) : EReal) - (K u xStar : EReal)
      else ⊥ := sorry

-- Proof sketch: the adjoint pointwise formula shows that for `xStar ∈ D` the negated adjoint
-- slice has a finite point on `C`, whereas off `D` it is identically `⊤`; the defining criterion
-- of `dom (-F⋆)` then gives the desired equality.
/-- Corollary33.3.3 (8): the same closed convex generator has adjoint domain exactly `D`. -/
theorem adjointSliceDomain_eq_of_upperBoundaryExtension_eq_upperAdjointPairing
    : dom (-F⋆) = D :=
      sorry

end UpperGenerator

end

end Bifunction
