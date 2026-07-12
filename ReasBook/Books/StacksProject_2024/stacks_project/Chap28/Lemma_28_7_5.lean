import StacksProject_2024.Chap28.Definition_28_7_1
import StacksProject_2024.Chap29.HasFiniteIrreducibleComponentsOnCompactOpens

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- A scheme admits a pairwise disjoint open cover by normal integral open subschemes when it has
an open covering whose members are pairwise disjoint and whose associated open subschemes are
integral and normal. -/
abbrev HasPairwiseDisjointOpenCoverByNormalIntegral : Prop :=
  ∃ (ι : Type u) (U : ι → X.Opens),
    TopologicalSpace.IsOpenCover U ∧
      Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j : Set X)) ∧
        ∀ i, IsIntegral (U i).toScheme ∧ (U i).toScheme.isNormal

/-- Unfold the source-facing cover condition by its indexed open-cover data. -/
@[simp]
theorem hasPairwiseDisjointOpenCoverByNormalIntegral_iff :
    X.HasPairwiseDisjointOpenCoverByNormalIntegral ↔
      ∃ (ι : Type u) (U : ι → X.Opens),
        TopologicalSpace.IsOpenCover U ∧
          Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j : Set X)) ∧
            ∀ i, IsIntegral (U i).toScheme ∧ (U i).toScheme.isNormal :=
  Iff.rfl

end AlgebraicGeometry.Scheme

section

variable {X : Scheme.{u}}

-- Semantic recall / repository-owner check:
-- - the source-facing owner remains `Scheme.isNormal`;
-- - the Chapter 29 repository owner for the finiteness hypothesis on quasi-compact opens is
--   `Scheme.HasFiniteIrreducibleComponentsOnCompactOpens`;
-- - the cover side is repeated in adjacent Chapter 28 items, so this file publicizes the
--   source-facing owner `Scheme.HasPairwiseDisjointOpenCoverByNormalIntegral`.

/-- Lemma 28.7.5: if every quasi-compact open subscheme of `X` has only finitely many irreducible
components, expressed by the canonical repository owner
`Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X`, then `X` is normal if and only if `X`
admits a pairwise disjoint open cover by normal integral open subschemes. -/
@[stacks 033L]
theorem isNormal_iff_exists_pairwiseDisjoint_openCover_normal_integral
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] :
    X.isNormal ↔ X.HasPairwiseDisjointOpenCoverByNormalIntegral := sorry

end
