import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

-- Semantic recall unavailable: `lean_leansearch` was rate-limited (HTTP 429), so the statement
-- was verified directly against mathlib's cover API, in particular `QuasiCompactCover.exists_hom`.

/-- Lemma 34.4.4: an étale cover of an affine scheme admits a finite refinement by affine schemes,
and the refining affine schemes may be chosen as open affines of the original covering schemes. -/
theorem exists_finite_affineRefinement_of_etaleCover_of_isAffine
    {T : Scheme} [IsAffine T] (𝒰 : T.Cover (Scheme.precoverage (@Etale))) :
    ∃ (𝒱 : T.AffineCover (@Etale)) (f : 𝒱.cover ⟶ 𝒰),
      Finite 𝒱.I₀ ∧ ∀ j, IsOpenImmersion (f.h₀ j) := by
  let _ : CompactSpace T := by infer_instance
  let _ : QuasiCompactCover 𝒰.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap fun i ↦ by
      let _ : Etale (𝒰.f i) := Scheme.Cover.map_prop 𝒰 i
      exact Scheme.Hom.isOpenMap (𝒰.f i)
  simpa using (QuasiCompactCover.exists_hom 𝒰)

end AlgebraicGeometry
