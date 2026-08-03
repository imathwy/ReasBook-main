module

public import Topology_Munkres_2000.Book.Exercise_36_5.Charts
public import Mathlib.Topology.Separation.Basic

public section

namespace LineWithTwoOrigins

/-- The line with two origins satisfies the `T₁` separation axiom. -/
instance instT1Space : T1Space LineWithTwoOrigins := by
  rw [t1Space_iff_exists_open]
  intro x y hxy
  cases x with
  | point x hx =>
      refine ⟨{z | z ≠ y}, ?_, hxy, by simp⟩
      cases y with
      | point y hy =>
          have hxyReal : x ≠ y := by
            intro h
            subst y
            exact hxy rfl
          have hpreimage : toReal ⁻¹' ({y} : Set ℝ) = {point y hy} := by
            ext z
            cases z with
            | point z hz =>
                simp only [Set.mem_preimage, Set.mem_singleton_iff, toReal_point]
                constructor
                · intro h
                  subst z
                  rfl
                · intro h
                  exact LineWithTwoOrigins.point.inj h
            | origin o =>
                simp only [Set.mem_preimage, Set.mem_singleton_iff, toReal_origin]
                constructor
                · exact fun h ↦ (hy h.symm).elim
                · intro h
                  cases h
          have hclosed : IsClosed {point y hy} := by
            rw [← hpreimage]
            exact isClosed_singleton.preimage continuous_toReal
          exact hclosed.isOpen_compl
      | origin o => simpa only [Set.mem_setOf_eq] using isOpen_ne_origin o
  | origin o =>
      refine ⟨{z | z ≠ y}, ?_, hxy, by simp⟩
      cases y with
      | point y hy =>
          have hpreimage : toReal ⁻¹' ({y} : Set ℝ) = {point y hy} := by
            ext z
            cases z with
            | point z hz =>
                simp only [Set.mem_preimage, Set.mem_singleton_iff, toReal_point]
                constructor
                · intro h
                  subst z
                  rfl
                · intro h
                  exact LineWithTwoOrigins.point.inj h
            | origin o =>
                simp only [Set.mem_preimage, Set.mem_singleton_iff, toReal_origin]
                constructor
                · exact fun h ↦ (hy h.symm).elim
                · intro h
                  cases h
          have hclosed : IsClosed {point y hy} := by
            rw [← hpreimage]
            exact isClosed_singleton.preimage continuous_toReal
          exact hclosed.isOpen_compl
      | origin o' => simpa only [Set.mem_setOf_eq] using isOpen_ne_origin o'

/-- The line with two origins has a countable basis for its topology. -/
instance instSecondCountableTopology : SecondCountableTopology LineWithTwoOrigins := by
  let U : Origin → Set LineWithTwoOrigins := fun o ↦ {z | z ≠ origin o}
  have hopen : ∀ o, IsOpen (U o) := fun o ↦ isOpen_ne_origin o
  have hcover : ⋃ o, U o = Set.univ := by
    ext z
    constructor
    · intro _
      exact Set.mem_univ z
    · intro _
      cases z with
      | point x hx => exact Set.mem_iUnion.mpr ⟨.p, point_ne_origin x hx .p⟩
      | origin o =>
          cases o with
          | p => exact Set.mem_iUnion.mpr ⟨.q, by simp [U]⟩
          | q => exact Set.mem_iUnion.mpr ⟨.p, by simp [U]⟩
  letI : ∀ o, SecondCountableTopology (U o) := fun o ↦
    (removeOriginHomeomorphReal o).isInducing.secondCountableTopology
  exact TopologicalSpace.secondCountableTopology_of_countable_cover hopen hcover

end LineWithTwoOrigins
