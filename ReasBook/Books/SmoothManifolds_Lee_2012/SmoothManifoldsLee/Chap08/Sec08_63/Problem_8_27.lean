import Mathlib.Geometry.Manifold.LocalDiffeomorph
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_61.Definition_8_61_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold ContDiff ContMDiffMonoidMorphism

-- Domain sampling pass:
-- * source-facing layer here: a local diffeomorphism of Lie groups induces a Lie algebra
--   isomorphism;
-- * core/canonical owner for invertibility: `IsLocalDiffeomorph.mfderivToContinuousLinearEquiv`;
-- * bridge/view for the source-facing induced map: the chapter owner
--   `ContMDiffMonoidMorphism.inducedLieAlgebraHomomorphism`, written on the theorem surface as
--   `F_*`;
-- * derived API here: bijectivity and the resulting `LieEquiv`.
-- The local file therefore derives the source-facing isomorphism statement from the canonical
-- differential equivalence at the identity.

section LieGroupLocalDiffeomorphisms

universe u𝕜 uEG uHG uG uEH uHH uH

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [CompleteSpace EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [CompleteSpace EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {H : Type uH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
variable [LieGroup I (minSmoothness 𝕜 3) G] [LieGroup J (minSmoothness 𝕜 3) H]

/-- Problem 8-27: if a Lie group homomorphism `F : G → H` is a local diffeomorphism, then the
induced Lie algebra homomorphism `F_* : Lie(G) → Lie(H)` is bijective, hence an isomorphism of Lie
algebras. -/
theorem local_diffeomorph_induced_group_lie_algebra_hom_bijective
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hF : IsLocalDiffeomorph I J ∞ F) :
    Function.Bijective (ContMDiffMonoidMorphism.inducedLieAlgebraHomomorphism F) := by
  sorry

/-- The Lie algebra equivalence induced by a local diffeomorphism of Lie groups. -/
noncomputable def local_diffeomorph_induced_group_lie_algebra_equiv
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hF : IsLocalDiffeomorph I J ∞ F) :
    GroupLieAlgebra I G ≃ₗ⁅𝕜⁆ GroupLieAlgebra J H :=
  LieEquiv.ofBijective (ContMDiffMonoidMorphism.inducedLieAlgebraHomomorphism F)
    (local_diffeomorph_induced_group_lie_algebra_hom_bijective F hF)

end LieGroupLocalDiffeomorphisms
