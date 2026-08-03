module

public import Topology_Munkres_2000.Book.Proposition_19_1.Comparison
public import Topology_Munkres_2000.Book.Definition_19_1.BoxTopology
public import Mathlib.Topology.Constructions

universe u v

public section

namespace Pi

/- Proposition 19.3 (1): On a finite product, the box topology and product topology
are equal. -/
#check Pi.box_eq_product_of_finite

/-- Helper for Proposition 19.3: a product restricted to finitely many open coordinates is a
generator for the box topology. -/
private lemma finiteSupportPi_mem_boxBasis {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] (U : (i : ι) → Set (X i))
    (F : Finset ι) (hU : ∀ i ∈ F, IsOpen (U i)) :
    Set.pi (↑F : Set ι) U ∈ boxBasis X := by
  classical
  -- Extend the finite family by the whole space at every unrestricted coordinate.
  let V : (i : ι) → Set (X i) := fun i ↦ if i ∈ F then U i else Set.univ
  have hV : ∀ i, IsOpen (V i) := by
    intro i
    by_cases hi : i ∈ F
    · simpa [V, hi] using hU i hi
    · simp [V, hi]
  -- The extended full product imposes exactly the original finite restrictions.
  have hpi : Set.pi (↑F : Set ι) U = Set.pi Set.univ V := by
    ext x
    simp [Set.mem_pi, V]
  exact (mem_boxBasis _).mpr ⟨V, hV, hpi⟩

/-- Proposition 19.3 (2): The box topology is finer than the product topology. -/
theorem box_le_product {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] :
    boxTopologicalSpace X ≤
      (Pi.topologicalSpace : TopologicalSpace ((i : ι) → X i)) := by
  -- Present the product topology by its finite-coordinate generating sets.
  rw [pi_eq_generateFrom]
  refine le_generateFrom ?_
  intro g hg
  obtain ⟨U, F, hU, rfl⟩ := hg
  -- Each product generator is already a generator for the box topology.
  exact TopologicalSpace.GenerateOpen.basic _ (finiteSupportPi_mem_boxBasis U F hU)

end Pi
