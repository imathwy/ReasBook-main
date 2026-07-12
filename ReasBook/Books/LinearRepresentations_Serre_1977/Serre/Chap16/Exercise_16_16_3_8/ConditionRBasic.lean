import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1.FiniteRepScalarExtension
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_2.CommonOwner
import LinearRepresentations_Serre_1977.Chap16.Lemma_16_16_3_1
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_3_3.PositiveBasics

/-!
This theorem-local module owns the stable source-facing API from Proposition 16-16.3-3 that is
needed by Exercise 16-16.3-8, without importing the proposition proof itself.
-/

noncomputable section

universe u

open CategoryTheory
open scoped Representation MonoidAlgebra

namespace Representation

section

variable {K : Type u} [Field K]
variable {G : Type u} [Group G]

-- `finiteRepPositiveSubset`, the scoped notation `R⁺[K](G)`, `mem_finiteRepPositiveSubset_iff` and
-- `finiteRepPositiveSubset_subset_simpleBasis_positiveCone` are reused from the owner module
-- `Serre.Chap16.Proposition_16_16_3_3.PositiveBasics` (imported above) to avoid duplicate
-- declarations under co-import.

variable [Finite G]

/-- Helper for Exercise 16-16.3-8: the theorem-local condition `(R)` surface used by the exercise
is the source-facing positive image/range equality for the fixed base-change map. -/
def SatisfiesConditionR_e16338
    (RKplus : Set (R₀[K](G))) (A : Type u) [CommRing A] [IsLocalRing A]
    [Algebra A K] [IsFractionRing A K] : Prop :=
  (projectiveGrothendieckBaseChangeHom K :
      finiteProjectiveGroupAlgebraGrothendieckGroup A G →+
        finiteRepGrothendieckGroup K G) '' P⁺[A](G) =
    (((projectiveGrothendieckBaseChangeHom K :
          finiteProjectiveGroupAlgebraGrothendieckGroup A G →+
            finiteRepGrothendieckGroup K G).range :
        Set (finiteRepGrothendieckGroup K G)) ∩ RKplus)

end

end Representation
