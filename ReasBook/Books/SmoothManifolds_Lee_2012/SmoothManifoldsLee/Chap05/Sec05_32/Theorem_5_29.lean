import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_32.Definition_5_32_extra_2

open scoped ContDiff Manifold

universe u𝕜 uE uH uM uE' uH' uE'' uH'' uN

section RestrictingCodomainOfSmoothMaps

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ⊤ M] [BoundarylessManifold I M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners 𝕜 E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J ⊤ S] [BoundarylessManifold J S]
variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H'' N]
variable {K : ModelWithCorners 𝕜 E'' H''} [IsManifold K ⊤ N]

-- Semantic recall note: `lean_leansearch` was unavailable in this session, so the statement
-- surface was checked against the local `IsImmersedSubmanifold` and `contMDiff_toSubtype` APIs.
/-- Theorem 5.29 (Restricting the Codomain of a Smooth Map): if `S ⊆ M` is an immersed
submanifold, `F : N → M` is smooth with image contained in `S`, and the codomain-restricted map
`N → S` is continuous, then `F` is smooth as a map to `S`. -/
theorem contMDiff_toSubtype_of_isImmersedSubmanifold
    (hS : IsImmersedSubmanifold I J S)
    {F : N → M} (hF : ContMDiff K I ⊤ F) (hFS : ∀ x, F x ∈ S)
    (hcont : Continuous (Set.codRestrict F S hFS)) :
    ContMDiff K J ⊤ (Set.codRestrict F S hFS) := sorry

end RestrictingCodomainOfSmoothMaps
