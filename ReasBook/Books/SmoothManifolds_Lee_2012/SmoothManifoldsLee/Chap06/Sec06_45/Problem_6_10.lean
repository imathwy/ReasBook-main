import SmoothManifolds_Lee_2012.Chap06.Sec06_44.Definition_6_44_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open Manifold Set

-- Domain sampling:
-- * owner predicates: `IsTransverseToSubmanifold`, `SubmanifoldsIntersectTransversely`
-- * source-facing owner data: `IsEmbeddedSubmanifold`
-- * tangent-space API: `T[J; p]`

section TransversePreimageTangentSpace

universe u𝕜 uE uF uE' uE'' uH uG uH' uH'' uM uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
variable {H : Type uH} [TopologicalSpace H]
variable {G : Type uG} [TopologicalSpace G]
variable {H' : Type uH'} [TopologicalSpace H']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace G N]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ∞ M]
variable {K : ModelWithCorners 𝕜 F G} [IsManifold K ∞ N]
variable {JX : ModelWithCorners 𝕜 E' H'} {X : Set M}
variable [ChartedSpace H' X] [IsManifold JX ∞ X] [IsEmbeddedSubmanifold I JX X]

omit [IsManifold I ∞ M] [IsManifold K ∞ N] in
/-- Problem 6-10 (1): if `F : N → M` is transverse to the chosen embedded submanifold structure on
`X`, then the tangent space of `F ⁻¹' X` is the inverse image of the tangent space of `X` under
`dFₚ`, written in Lean as a `Submodule.comap`. -/
theorem tangentSpace_preimage_eq_comap_of_transverse
    {f : N → M} {JW : ModelWithCorners 𝕜 E'' H''}
    [ChartedSpace H'' (f ⁻¹' X)] [IsManifold JW ∞ (f ⁻¹' X)]
    (htrans : IsTransverseToSubmanifold I K JX X f)
    (p : f ⁻¹' X) :
    let x : X := ⟨f p, p.2⟩
    T[JW; p] = (T[JX; x]).comap (mfderiv K I f p).toLinearMap := by
  sorry

end TransversePreimageTangentSpace

section TransverseIntersectionTangentSpace

universe u𝕜 uE uE' uE'' uE''' uH uH' uH'' uH''' uM

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
variable {E''' : Type uE'''} [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {H''' : Type uH'''} [TopologicalSpace H''']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ∞ M]
variable {JX : ModelWithCorners 𝕜 E' H'} {X : Set M}
variable {JX' : ModelWithCorners 𝕜 E'' H''} {X' : Set M}
variable [ChartedSpace H' X] [IsManifold JX ∞ X] [IsEmbeddedSubmanifold I JX X]
variable [ChartedSpace H'' X'] [IsManifold JX' ∞ X'] [IsEmbeddedSubmanifold I JX' X']

omit [IsManifold I ∞ M] in
/-- Problem 6-10 (2): if the chosen embedded submanifold structures on `X` and `X'` intersect
transversely, then the tangent space of `X ∩ X'` is the intersection of the tangent spaces of `X`
and `X'`. -/
theorem tangentSpace_inter_eq_inf_of_transverse
    {JXX' : ModelWithCorners 𝕜 E''' H'''}
    [ChartedSpace H''' (X ∩ X' : Set M)] [IsManifold JXX' ∞ (X ∩ X' : Set M)]
    (htrans : SubmanifoldsIntersectTransversely I JX X JX' X')
    (p : (X ∩ X' : Set M)) :
    let px : X := ⟨p, p.2.1⟩
    let px' : X' := ⟨p, p.2.2⟩
    (T[JXX'; p] : Submodule 𝕜 (TangentSpace I (p : M))) = T[JX; px] ⊓ T[JX'; px'] := by
  sorry

end TransverseIntersectionTangentSpace
