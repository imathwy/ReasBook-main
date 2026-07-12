import Mathlib
import StacksProject_2024.Chap28.Lemma_28_7_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

section

variable (X : Scheme.{u}) [IsNoetherian X]

-- Semantic recall: `lean_leansearch` surfaced the canonical Noetherian-scheme finiteness theorem
-- `AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian`, and local Chapter 28
-- precedent already packages the general normal-scheme decomposition as
-- `isNormal_iff_exists_pairwiseDisjoint_openCover_normal_integral`. This item is the Noetherian
-- finite-index specialization of that existing open-cover statement.

/-- Lemma 28.7.6: a Noetherian scheme `X` is normal if and only if `X` is a finite disjoint union
of normal integral schemes, expressed as a finite pairwise disjoint open cover by open subschemes
that are both integral and normal. -/
@[stacks 033M]
theorem isNormal_iff_exists_finite_pairwiseDisjoint_openCover_normal_integral :
    X.isNormal ↔
      ∃ n : ℕ, ∃ U : Fin n → X.Opens,
        TopologicalSpace.IsOpenCover U ∧
          Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j : Set X)) ∧
            ∀ i, IsIntegral (U i).toScheme ∧ (U i).toScheme.isNormal := sorry

end
