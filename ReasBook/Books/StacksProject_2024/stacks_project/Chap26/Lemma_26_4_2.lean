import StacksProject_2024.Chap26.Definition_26_4_1
import StacksProject_2024.Chap26.Lemma_26_3_5

open AlgebraicGeometry
open CategoryTheory TopologicalSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.LocallyRingedSpace

-- Semantic recall: mathlib provides the scheme-level target-local criterion
-- `AlgebraicGeometry.IsLocalAtTarget.of_openCover` for `AlgebraicGeometry.IsClosedImmersion`.
-- This file records the locally-ringed-space analogue using the Chapter 26 owner
-- `LocallyRingedSpace.IsClosedImmersion` together with the restricted-morphism owner
-- `LocallyRingedSpace.pullbackToPreimageOpenMorphism`.

namespace IsClosedImmersion

section

variable {X Z : LocallyRingedSpace.{u}} (f : Z ⟶ X)

/-- For a chosen open covering of the target, closed immersion can be checked on each restricted
morphism over a member of the cover. -/
theorem of_openCover
    {ι : Type v} (U : ι → Opens X) (hU : TopologicalSpace.IsOpenCover U)
    (hclosed : ∀ i, IsClosedImmersion (pullbackToPreimageOpenMorphism f (U i))) :
    IsClosedImmersion f := sorry

/-- Companion API: for an open cover of the target, closed immersion can be checked after
restricting to each member of the cover. -/
theorem iff_of_openCover
    {ι : Type v} (U : ι → Opens X) (hU : TopologicalSpace.IsOpenCover U) :
    IsClosedImmersion f ↔ ∀ i, IsClosedImmersion (pullbackToPreimageOpenMorphism f (U i)) := by
  constructor
  · intro hf
    sorry
  · intro hclosed
    exact of_openCover f U hU hclosed

/-- Lemma 26.4.2: a morphism of locally ringed spaces is a closed immersion if and only if there
exists an open covering of the target on which every restricted morphism is a closed immersion. -/
@[stacks 01HL]
theorem iff_exists_openCover :
    IsClosedImmersion f ↔
      ∃ (ι : Type v) (U : ι → Opens X), TopologicalSpace.IsOpenCover U ∧
        ∀ i, IsClosedImmersion (pullbackToPreimageOpenMorphism f (U i)) := by
  constructor
  · intro hf
    refine ⟨PUnit, fun _ ↦ (⊤ : Opens X), ?_, ?_⟩
    · simpa [TopologicalSpace.IsOpenCover]
    · intro i
      simpa using
        ((iff_of_openCover f (fun _ : PUnit ↦ (⊤ : Opens X))
          (by simpa [TopologicalSpace.IsOpenCover])).mp hf) i
  · rintro ⟨ι, U, hU, hclosed⟩
    exact (iff_of_openCover f U hU).mpr hclosed

end

end IsClosedImmersion

end AlgebraicGeometry.LocallyRingedSpace
