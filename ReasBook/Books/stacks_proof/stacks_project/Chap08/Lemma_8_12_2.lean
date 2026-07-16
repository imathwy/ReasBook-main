import Mathlib
import stacks_proof.stacks_project.Chap08.Definition_8_4_1
import stacks_proof.stacks_project.Chap08.Lemma_8_4_2
import stacks_proof.stacks_project.Chap08.Lemma_8_2_3.PullbackComparisonNaturality
import stacks_proof.stacks_project.Chap08.Lemma_8_12_1
import stacks_proof.stacks_project.Chap08.Lemma_8_12_2.Index

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology.Cover

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

/-- Chap08 Lemma 8 12 2: if `u : C ⥤ D` is a continuous functor of sites preserving pullbacks, and
`X` is a stack over `(D, K)` with projection `p : S ⥤ D`, then the pullback category `u^p S`,
modeled by the categorical pullback `CategoricalPullback u p`, is a stack over `(C, J)`.

The extra pullback-preservation hypothesis records the source proof's use of the identifications
`u (U_i ×_U U_j) = u(U_i) ×_{u(U)} u(U_j)` and the analogous triple-overlap statement. -/
@[stacks 04WC]
theorem continuous_pullback_isStackOnSite
    [Functor.IsContinuous u J K]
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    (p : S ⥤ D) [IsStackOnSite K p] :
    IsStackOnSite J (CategoricalPullback.π₁ u p) := by
  -- Reduce the site-level statement to the coverwise canonical descent criterion.
  exact
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J
      (CategoricalPullback.π₁ u p)).2
      (fun U S ↦
        pullbackProjection_coverwiseCanonicalDescentFunctor_isEquivalence (J := J) (K := K) u p S)

end

end CategoryTheory
