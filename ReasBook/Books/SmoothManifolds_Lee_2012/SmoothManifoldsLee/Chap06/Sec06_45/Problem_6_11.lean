import SmoothManifolds_Lee_2012.Chap06.Sec06_45.Problem_6_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open Manifold Set

section TransversePreimageComposition

universe u𝕜 uEM uEN uEP uEX uEGX uHM uHN uHP uHX uHGX uM uN uP

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
variable {EP : Type uEP} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
variable {EX : Type uEX} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
variable {EGX : Type uEGX} [NormedAddCommGroup EGX] [NormedSpace 𝕜 EGX]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {HP : Type uHP} [TopologicalSpace HP]
variable {HX : Type uHX} [TopologicalSpace HX]
variable {HGX : Type uHGX} [TopologicalSpace HGX]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
variable {P : Type uP} [TopologicalSpace P] [ChartedSpace HP P]
variable {I : ModelWithCorners 𝕜 EM HM} [IsManifold I ∞ M]
variable {J : ModelWithCorners 𝕜 EN HN} [IsManifold J ∞ N]
variable {K : ModelWithCorners 𝕜 EP HP} [IsManifold K ∞ P]
variable {JX : ModelWithCorners 𝕜 EX HX} {X : Set P}
variable [ChartedSpace HX X] [IsManifold JX ∞ X] [IsEmbeddedSubmanifold K JX X]

/-- Problem 6-11: if `F : M → N` is smooth and `X ⊆ P` together with `G ⁻¹' X` carry chosen
embedded submanifold structures, then `F` is transverse to `G ⁻¹' X` if and only if `G ∘ F` is
transverse to `X`. -/
theorem transverse_preimage_iff_comp_transverse
    {F : M → N} {G : N → P} {JGX : ModelWithCorners 𝕜 EGX HGX}
    [ChartedSpace HGX (G ⁻¹' X)] [IsManifold JGX ∞ (G ⁻¹' X)]
    (hF : ContMDiff I J ∞ F)
    [IsEmbeddedSubmanifold J JGX (G ⁻¹' X)]
    (hGtrans : IsTransverseToSubmanifold K J JX X G) :
    IsTransverseToSubmanifold J I JGX (G ⁻¹' X) F ↔
      IsTransverseToSubmanifold K I JX X (G ∘ F) := sorry

end TransversePreimageComposition
