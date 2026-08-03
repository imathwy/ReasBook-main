module

public import Topology_Munkres_2000.Book.Definition_3_6

universe u

public section

variable {α : Type u} {A : Set α}

/-- Remark 3.2: Every partition of `A` is the collection of equivalence classes
of exactly one equivalence relation on `A`. -/
theorem Setoid.IsPartition.existsUnique_setoid {D : Set (Set A)}
    (hD : Setoid.IsPartition D) : ∃! r : Setoid A, r.classes = D := by
  refine ⟨Setoid.mkClasses D hD.2, Setoid.classes_mkClasses D hD, ?_⟩
  intro r hr
  exact Setoid.classes_inj.2 (hr.trans (Setoid.classes_mkClasses D hD).symm)

end
