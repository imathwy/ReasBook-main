import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_5_1

noncomputable section

universe u v

open scoped RealInnerProductSpace Rockafellar

namespace Bifunction

section

variable {𝕜 : Type*} [RCLike 𝕜] [Preorder 𝕜]
variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [InnerProductSpace 𝕜 U]

/-- Downstream inner-product Fréchet-Riesz bridge for Text 35.5.1:
vector-valued first partial subdifferential. -/
abbrev subdifferential1AtVec (K : U → V → WithBotTop 𝕜) (u : U) (v : V) : Set U :=
  Function.concaveSubdifferentialAt (fun u' ↦ K u' v) u

/-- Pointwise inner-product characterization of the vector-valued first partial subdifferential. -/
@[simp] theorem mem_subdifferential1AtVec
    {K : U → V → WithBotTop 𝕜} {u uStar : U} {v : V} :
    uStar ∈ subdifferential1AtVec K u v ↔
      ∀ u', K u' v ≤ K u v + ((inner 𝕜 uStar (u' - u) : 𝕜) : WithBotTop 𝕜) := by
  change uStar ∈ Function.concaveSubdifferentialAt (fun u' ↦ K u' v) u ↔
      ∀ u', K u' v ≤ K u v + ((inner 𝕜 uStar (u' - u) : 𝕜) : WithBotTop 𝕜)
  exact Function.mem_concaveSubdifferentialAt

end

section

variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- Euclidean downstream bridge: the pairing-valued first partial subdifferential over the ambient
space itself agrees with the vector-valued Fréchet-Riesz bridge `subdifferential1AtVec`. -/
theorem subdifferential1At_eq_subdifferential1AtVec
    (K : U → V → WithBotTop ℝ) (u : U) (v : V) :
    subdifferential1At K u v U = subdifferential1AtVec K u v := by
  ext uStar
  rw [mem_subdifferential1At_pairing, mem_subdifferential1AtVec]
  constructor
  · intro h u'
    have hInner :
        ((HasLinearPairing.pairingLinear u') uStar - (HasLinearPairing.pairingLinear u) uStar :
            ℝ) =
          inner ℝ uStar (u' - u) := by
      simp [HasLinearPairing.pairingLinear, innerₗ_apply_apply, inner_sub_right,
        real_inner_comm]
    simpa [hInner] using h u'
  · intro h u'
    have hInner :
        ((HasLinearPairing.pairingLinear u') uStar - (HasLinearPairing.pairingLinear u) uStar :
            ℝ) =
          inner ℝ uStar (u' - u) := by
      simp [HasLinearPairing.pairingLinear, innerₗ_apply_apply, inner_sub_right,
        real_inner_comm]
    simpa [hInner] using h u'

end

end Bifunction
