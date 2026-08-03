module

public import Topology_Munkres_2000.Book.Definition_19_1.BoxTopology
public import Mathlib.Topology.Constructions

universe u v

public section

namespace Pi

/-- On a finite dependent product, the box topology equals the product topology. -/
theorem box_eq_product_of_finite {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] [Finite ι] :
    boxTopologicalSpace X =
      (Pi.topologicalSpace : TopologicalSpace ((i : ι) → X i)) := by
  classical
  apply le_antisymm
  · -- Extend each finite-coordinate product generator to a full open box.
    rw [pi_eq_generateFrom]
    refine le_generateFrom ?_
    rintro _ ⟨U, F, hU, rfl⟩
    let V : (i : ι) → Set (X i) := fun i ↦ if i ∈ F then U i else Set.univ
    have hV : ∀ i, IsOpen (V i) := by
      intro i
      by_cases hi : i ∈ F
      · simpa only [V, if_pos hi] using hU i hi
      · simpa only [V, if_neg hi] using (isOpen_univ : IsOpen (Set.univ : Set (X i)))
    apply TopologicalSpace.GenerateOpen.basic
    refine (mem_boxBasis _).mpr ⟨V, hV, ?_⟩
    ext x
    simp [Set.mem_pi, V]
  · -- Finiteness makes every full open box open in the product topology.
    refine le_generateFrom ?_
    intro s hs
    obtain ⟨U, hU, rfl⟩ := (mem_boxBasis s).mp hs
    exact isOpen_set_pi Set.finite_univ fun i _ ↦ hU i

end Pi
