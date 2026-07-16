import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_3_8.ProjectiveBaseChangeScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_3_8.DecompositionImageBridge
import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_3_8.ProjectivePositiveReflection

noncomputable section

universe u

open CategoryTheory
open scoped Representation ZeroObject

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "e" =>
  (projectiveGrothendieckBaseChangeHom K :
    finiteProjectiveGroupAlgebraGrothendieckGroup A G →+
      finiteRepGrothendieckGroup K G)

/-- Helper for Exercise 16-16.3-8: condition `(R)` implies the source-facing base-change
positive-image equality under the Henselian/DVR hypotheses of the target theorem. -/
theorem baseChange_image_eq_range_inter_positive_of_conditionR_henselian
    [IsNoetherianRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (hR : SatisfiesConditionR_e16338 (R⁺[K](G)) A) :
    e '' P⁺[A](G) =
      (((e).range : Set (finiteRepGrothendieckGroup K G)) ∩ R⁺[K](G)) := by
  exact hR

/-- Helper for Exercise 16-16.3-8: the source-facing base-change positive-image equality implies
condition `(R)` under the Henselian/DVR hypotheses of the target theorem. -/
theorem satisfiesConditionR_of_baseChange_image_eq_range_inter_positive_henselian
    [IsNoetherianRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (hbase :
      e '' P⁺[A](G) =
        (((e).range : Set (finiteRepGrothendieckGroup K G)) ∩ R⁺[K](G))) :
    SatisfiesConditionR_e16338 (R⁺[K](G)) A := by
  exact hbase

end

end Representation
