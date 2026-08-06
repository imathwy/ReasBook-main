import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.SingleRelatorPresentedGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Proposition_2_8_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

variable {X : Type u} [TopologicalSpace X]

section

variable {α : Type*}
variable (U V : TopologicalSpace.Opens X) (hcover : U ⊔ V = ⊤)
variable (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
variable [PathConnectedSpace U]
variable [PathConnectedSpace (U ⊓ V : TopologicalSpace.Opens X)]
variable [SimplyConnectedSpace V]
variable
  (pi1_U_equiv : FundamentalGroup U ⟨x, hxU⟩ ≃* FreeGroup α)
  (pi1_inter_equiv :
    FundamentalGroup (U ⊓ V : TopologicalSpace.Opens X) ⟨x, ⟨hxU, hxV⟩⟩ ≃*
      FreeGroup Unit)
variable (relator : FreeGroup α)
variable
  (attaching_map_eq :
    (pi1_U_equiv.toMonoidHom.comp
        (fundamental_group_inf_to_left U V x hxU hxV)).comp
      pi1_inter_equiv.symm.toMonoidHom =
      FreeGroup.lift fun _ : Unit ↦ relator)

/-- If the van Kampen attaching map for `U ∩ V` is identified with the single relator `r`, then
`π₁(X, x)` is the presented group `⟨generators | r = 1⟩`. -/
def fundamental_group_left_to_union_single_relator_presented_group_equiv :
    FundamentalGroup X x ≃* PresentedGroup ({relator} : Set (FreeGroup α)) :=
  let φ := pi1_U_equiv.toMonoidHom
  let ψ := pi1_inter_equiv.symm.toMonoidHom
  let ι :
      FundamentalGroup (U ⊓ V : TopologicalSpace.Opens X) ⟨x, ⟨hxU, hxV⟩⟩ →*
        FundamentalGroup U ⟨x, hxU⟩ :=
    fundamental_group_inf_to_left U V x hxU hxV
  let hrange :
      Set.range (φ.comp ι) = Set.range (FreeGroup.lift fun _ : Unit ↦ relator) := by
    calc
      Set.range (φ.comp ι) = Set.range ((φ.comp ι).comp ψ) := by
        ext y
        constructor
        · rintro ⟨z, rfl⟩
          exact ⟨pi1_inter_equiv z, by simp [φ, ψ]⟩
        · rintro ⟨z, rfl⟩
          exact ⟨pi1_inter_equiv.symm z, by simp [φ, ψ]⟩
      _ = Set.range (FreeGroup.lift fun _ : Unit ↦ relator) := by
        simpa only [φ, ι, ψ] using
          congrArg (fun f : FreeGroup Unit →* FreeGroup α ↦ Set.range f) attaching_map_eq
  let hmap_overlap :
      (Subgroup.normalClosure (Set.range ι)).map φ =
        Subgroup.normalClosure ({relator} : Set (FreeGroup α)) := by
    calc
      (Subgroup.normalClosure (Set.range ι)).map φ =
          Subgroup.normalClosure (φ '' Set.range ι) := by
        rw [Subgroup.map_normalClosure _ _ pi1_U_equiv.surjective]
      _ = Subgroup.normalClosure (Set.range (φ.comp ι)) := by
        congr 1
        ext y
        constructor
        · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
          exact ⟨w, rfl⟩
        · rintro ⟨w, rfl⟩
          exact ⟨_, ⟨w, rfl⟩, rfl⟩
      _ = Subgroup.normalClosure (Set.range (FreeGroup.lift fun _ : Unit ↦ relator)) := by
        rw [hrange]
      _ = Subgroup.normalClosure ({relator} : Set (FreeGroup α)) := by
        exact FreeGroup.normalClosure_range_lift_unit_eq relator
  (fundamental_group_left_to_union_quotient_normal_closure_range_equiv
    U V hcover x hxU hxV).trans <|
    by
      simpa using
        QuotientGroup.congr (Subgroup.normalClosure (Set.range ι))
          (Subgroup.normalClosure ({relator} : Set (FreeGroup α)))
          pi1_U_equiv hmap_overlap

end
