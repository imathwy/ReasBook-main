import Mathlib
import SmoothManifolds_Lee_2012.Chap07.Sec07_47.Definition_7_47_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

section SemidirectProductOnProd

universe u𝕜 uEN uEH uHN uHH uN uH

variable {N : Type uN} [Group N]
variable {H : Type uH} [Group H]

/-- Exercise 7.31 (1): transport mathlib's canonical semidirect product `N ⋊[θ] H` across
`SemidirectProduct.equivProd` to realize it on the product type `N × H`. -/
abbrev semidirectProductGroup (θ : H →* MulAut N) : Group (N × H) :=
  ((SemidirectProduct.equivProd : N ⋊[θ] H ≃ N × H).symm).group

/-- Multiplication in `semidirectProductGroup θ` is the textbook semidirect-product formula. -/
theorem semidirectProductGroup_mul_eq (θ : H →* MulAut N) (a b : N × H) :
    let _ : Group (N × H) := semidirectProductGroup θ
    a * b = (a.1 * θ a.2 b.1, a.2 * b.2) := sorry

/-- Exercise 7.31 (2): the identity element of `semidirectProductGroup θ` is `(e, e)`. -/
theorem semidirectProductGroup_one_eq (θ : H →* MulAut N) :
    let _ : Group (N × H) := semidirectProductGroup θ
    (1 : N × H) = (1, 1) := by
  rfl

/-- Exercise 7.31 (3): the inverse in `semidirectProductGroup θ` is
`(n, h)⁻¹ = (θ_{h⁻¹}(n⁻¹), h⁻¹)`. -/
theorem semidirectProductGroup_inv_eq (θ : H →* MulAut N) (a : N × H) :
    let _ : Group (N × H) := semidirectProductGroup θ
    a⁻¹ = (θ a.2⁻¹ a.1⁻¹, a.2⁻¹) := sorry

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {I : ModelWithCorners 𝕜 EN HN} {J : ModelWithCorners 𝕜 EH HH}
variable [TopologicalSpace N] [ChartedSpace HN N]
variable [TopologicalSpace H] [ChartedSpace HH H]
variable [LieGroup I ∞ N] [LieGroup J ∞ H]

/-- Exercise 7.31 (4): if the action map `(h, n) ↦ θ h n` is smooth, then the transported
semidirect-product group structure on `N × H` is a Lie group structure on the product manifold. -/
theorem semidirectProductLieGroup (θ : H →* MulAut N)
    (hθ : ContMDiff (J.prod I) I ∞ fun p : H × N ↦ θ p.1 p.2) :
    let _ : Group (N × H) := semidirectProductGroup θ
    LieGroup (I.prod J) ∞ (N × H) := sorry

end SemidirectProductOnProd

section SemidirectProductIsomorphism

universe u𝕜 uEN uHN uN uEH uHH uH uEG uHG uG

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {N : Type uN} [Group N] [TopologicalSpace N] [ChartedSpace HN N]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {H : Type uH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable (I_N : ModelWithCorners 𝕜 EN HN)
variable (I_H : ModelWithCorners 𝕜 EH HH)
variable (I_G : ModelWithCorners 𝕜 EG HG)
variable [LieGroup I_N ∞ N] [LieGroup I_H ∞ H] [LieGroup I_G ∞ G]

/-- Source-facing owner: `G` is Lie-group-isomorphic to a semidirect product `N ⋊ H`. -/
def LieGroupIsomorphicToSemidirectProduct : Prop :=
  ∃ θ : H →* MulAut N,
    ∃ hθ : ContMDiff (I_H.prod I_N) I_N ∞ (fun p : H × N ↦ θ p.1 p.2),
      let _ : Group (N × H) := semidirectProductGroup θ
      let _ : LieGroup (I_N.prod I_H) ∞ (N × H) := semidirectProductLieGroup θ hθ
      Nonempty (LieGroupIsomorphism (I_N.prod I_H) I_G (N × H) G)

end SemidirectProductIsomorphism
