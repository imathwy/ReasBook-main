import Mathlib.Geometry.Manifold.ContMDiff.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace
open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uH' uN uE'' uH'' uP

variable
  {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type uH} [TopologicalSpace H]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type uH'} [TopologicalSpace H']
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type uH''} [TopologicalSpace H'']
  {P : Type uP} [TopologicalSpace P] [ChartedSpace H'' P]
  {I : ModelWithCorners 𝕜 E H}
  {I' : ModelWithCorners 𝕜 E' H'}
  {I'' : ModelWithCorners 𝕜 E'' H''}
  [IsManifold I (∞ : ℕ∞ω) M] [IsManifold I' (∞ : ℕ∞ω) N] [IsManifold I'' (∞ : ℕ∞ω) P]
  {c : N} {U : Opens M} {F : M → N} {G : N → P}

/- Proposition 2.10 (1): every constant map between smooth manifolds is smooth. The canonical
owner theorem is `contMDiff_const`, specialized here to `C^∞`. -/
#check (contMDiff_const : ContMDiff I I' (∞ : ℕ∞ω) (fun _ : M ↦ c))

/- Proposition 2.10 (2): the identity map of a smooth manifold is smooth. The canonical owner
theorem is `contMDiff_id`, specialized here to `C^∞`. -/
#check (contMDiff_id : ContMDiff I I (∞ : ℕ∞ω) (id : M → M))

/- Proposition 2.10 (3): the inclusion of an open submanifold into the ambient manifold is
smooth. The canonical owner theorem is `contMDiff_subtype_val`, specialized here to `C^∞`. -/
#check (contMDiff_subtype_val : ContMDiff I I (∞ : ℕ∞ω) (Subtype.val : U → M))

/- Proposition 2.10 (4): the composite of two smooth maps is smooth. The canonical owner theorem
is `ContMDiff.comp`, specialized here to `C^∞`. -/
#check
  (ContMDiff.comp :
    ContMDiff I' I'' (∞ : ℕ∞ω) G →
      ContMDiff I I' (∞ : ℕ∞ω) F →
        ContMDiff I I'' (∞ : ℕ∞ω) (G ∘ F))
