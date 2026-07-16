import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_3
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_37_3_1

noncomputable section

open scoped Rockafellar

universe u u'

namespace Bifunction

section Pairing

variable {U : Type u} {V : Type}
variable {YU : Type u'} {YV : Type}
variable [Sub U]
variable [SeminormedAddCommGroup V] [NormedSpace ℝ V]
variable [HasPairing U YU ℝ] [HasPairing V YV ℝ]

/-- The saddle kernel obtained by subtracting the two pairing terms determined by `(uStar, vStar)`
from `K`. -/
def subPairingTranslate
    (K : U → V → WithBotTop ℝ) (uStar : YU) (vStar : YV) : U → V → WithBotTop ℝ :=
  fun u v ↦ K u v - ⟪u, uStar⟫ₚ - ⟪v, vStar⟫ₚ

-- Proof sketch: unfold `subPairingTranslate`.
/-- Evaluating `subPairingTranslate K uStar vStar` gives the defining affine-translation formula.
-/
@[simp] theorem subPairingTranslate_apply
    (K : U → V → WithBotTop ℝ) (uStar : YU) (vStar : YV) (u : U) (v : V) :
    subPairingTranslate K uStar vStar u v = K u v - ⟪u, uStar⟫ₚ - ⟪v, vStar⟫ₚ := sorry

-- Proof sketch: subtract the affine form determined by `(uStar, vStar)` from `K`. Membership
-- `(uStar, vStar) ∈ d(K ; u, v)` becomes the zero-subgradient condition for the translated
-- kernel, and Proposition 36.5.2 rewrites that zero-subgradient condition as the ambient
-- saddle-point predicate for the translated kernel.
/-- Theorem 37.4 (1): a pair `(uStar, vStar)` belongs to the saddle subdifferential `∂K(u, v)`
exactly when the translated kernel `K - ⟪·, uStar⟫ - ⟪·, vStar⟫`, rendered as
`subPairingTranslate K uStar vStar`, has `(u, v)` as a saddle-point. -/
theorem mem_subdifferentialAt_iff_isSaddlePointOn_univ_swap_subPairingTranslate
    {K : U → V → WithBotTop ℝ} {u : U} {v : V} {uStar : YU} {vStar : YV} :
    (uStar, vStar) ∈ d(K ; u, v | YU, YV) ↔
      IsSaddlePointOn (Set.univ : Set V) (Set.univ : Set U)
        (Function.swap (subPairingTranslate K uStar vStar)) v u := sorry

end Pairing

section Domain

variable {U : Type u} {V : Type}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

-- Proof sketch: write the relative interior of the product domain through
-- `ri[ℝ](dom K)`, then use the Chapter 35 partial-subdifferential nonemptiness
-- criteria on the two slices to obtain a witness in `d(K ; u, v)`.
/-- Theorem 37.4 (2): for a closed proper concave-convex saddle-function, every point of
`ri (dom K)` admits a saddle subgradient; rendered here as inclusion of
`ri[ℝ](dom K)` into the intrinsic strong-dual domain owner `dom∂ₛ K`. -/
theorem ri_dom_subset_subdifferentialDomDual_of_isClosedProperConcaveConvex
    {K : U → V → WithBotTop ℝ}
    (hK_closed : SaddleFunction.IsClosed K)
    (hK_proper : SaddleFunction.IsProper K)
    (hK_concaveConvex : SaddleFunction.IsConcaveConvex ℝ K) :
    ri[ℝ](SaddleFunction.dom K) ⊆ (dom∂ₛ K) := sorry

-- Proof sketch: if `(u, v)` admits a saddle subgradient, choose
-- `(uStar, vStar) ∈ d(K ; u, v)`. Clause (1) converts this to a saddle-point statement for the
-- corresponding translated kernel, and the Chapter 36 domain bridge places `(u, v)` in
-- `dom K`.
/-- Theorem 37.4 (3): for a closed proper concave-convex saddle-function, the domain of the
saddle subdifferential is contained in the product domain. -/
theorem subdifferentialDomDual_subset_dom_of_isClosedProperConcaveConvex
    {K : U → V → WithBotTop ℝ}
    (hK_closed : SaddleFunction.IsClosed K)
    (hK_proper : SaddleFunction.IsProper K)
    (hK_concaveConvex : SaddleFunction.IsConcaveConvex ℝ K) :
    (dom∂ₛ K) ⊆ SaddleFunction.dom K := sorry

end Domain

end Bifunction
