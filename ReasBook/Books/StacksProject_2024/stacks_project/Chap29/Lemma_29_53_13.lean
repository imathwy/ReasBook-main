import Mathlib
import StacksProject_2024.Chap28.Definition_28_7_1
import StacksProject_2024.Chap29.Definition_29_50_1
import StacksProject_2024.Chap29.Remark_29_49_13

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical relative-normalization owners
-- `Scheme.Hom.normalization`, `Scheme.Hom.toNormalization`, and
-- `Scheme.Hom.normalizationOpenCover`; local Chapter 29 precedent supplies
-- `genericPointsOfIrreducibleComponents`.

/-- Lemma 29.53.13 (1): let `f : Y ⟶ X` be a quasi-compact and quasi-separated morphism of
schemes. Assume `Y` is normal and every quasi-compact open of `Y` has finitely many irreducible
components. Then the normalization of `X` in `Y` admits a pairwise disjoint open cover by
integral open subschemes. -/
@[stacks 035L]
theorem Scheme.Hom.normalization_exists_pairwiseDisjoint_openCover_integral_of_isNormal
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens Y] (hY : Y.isNormal) :
    ∃ (ι : Type u) (U : ι → f.normalization.Opens),
      ∃ (hpair : Pairwise (fun i j ↦
            Disjoint (U i : Set f.normalization) (U j : Set f.normalization))),
        ∃ (hcover : (⋃ i, (U i : Set f.normalization)) = Set.univ),
          ∀ i, IsIntegral (U i).toScheme := sorry

/-- Lemma 29.53.13 (2): under the same hypotheses, the normalization of `X` in `Y` is normal. -/
@[stacks 035L]
theorem Scheme.Hom.normalization_isNormal_of_isNormal
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens Y] (hY : Y.isNormal) :
    f.normalization.isNormal := sorry

/-- Lemma 29.53.13 (3): under the same hypotheses, the canonical map from `Y` to the normalization
of `X` in `Y` is dominant. -/
@[stacks 035L]
theorem Scheme.Hom.isDominant_toNormalization_of_isNormal
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens Y] (hY : Y.isNormal) :
    IsDominant f.toNormalization := sorry

/-- Lemma 29.53.13 (4): under the same hypotheses, the canonical map from `Y` to the normalization
of `X` in `Y` induces a bijection on the generic points of irreducible components. -/
@[stacks 035L]
theorem Scheme.Hom.bijOn_genericPointsOfIrreducibleComponents_toNormalization_of_isNormal
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens Y] (hY : Y.isNormal) :
    Set.BijOn f.toNormalization
      (genericPointsOfIrreducibleComponents Y)
      (genericPointsOfIrreducibleComponents f.normalization) := sorry

end AlgebraicGeometry
