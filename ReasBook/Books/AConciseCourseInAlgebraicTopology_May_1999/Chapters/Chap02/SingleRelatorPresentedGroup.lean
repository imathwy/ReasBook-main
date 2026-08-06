import Mathlib.GroupTheory.PresentedGroup

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace FreeGroup

/-- Any word in the free group on one generator, after sending that generator to `r`, lies in the
subgroup closure of the singleton `{r}`. -/
theorem lift_unit_mem_closure_singleton {α : Type*} (r : FreeGroup α) (w : FreeGroup Unit) :
    FreeGroup.lift (fun _ : Unit ↦ r) w ∈ Subgroup.closure ({r} : Set (FreeGroup α)) := by
  refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
  · exact Subgroup.one_mem _
  · intro _
    rw [FreeGroup.lift_apply_of]
    exact Subgroup.mem_closure_singleton_self r
  · intro _ h
    simpa [map_inv] using Subgroup.inv_mem _ h
  · intro _ _ hx hy
    simpa using Subgroup.mul_mem _ hx hy

/-- The normal closure of the image of the canonical map `FreeGroup Unit →* FreeGroup α` sending
the generator to `r` is exactly the normal closure of the singleton `{r}`. -/
theorem normalClosure_range_lift_unit_eq {α : Type*} (r : FreeGroup α) :
    Subgroup.normalClosure
        (Set.range (FreeGroup.lift (fun _ : Unit ↦ r) : FreeGroup Unit →* FreeGroup α)) =
      Subgroup.normalClosure ({r} : Set (FreeGroup α)) := by
  refine le_antisymm ?_ ?_
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨w, rfl⟩
    exact Subgroup.closure_le_normalClosure (lift_unit_mem_closure_singleton r w)
  · apply Subgroup.normalClosure_mono
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact ⟨FreeGroup.of (), by simp⟩

end FreeGroup
