module

public import Topology_Munkres_2000.Book.Proposition_19_1.Comparison
public import Mathlib.Topology.Instances.Real.Lemmas

public section

/- Proposition 19.1 (1): The box and product topologies agree on finite products. -/
#check Pi.box_eq_product_of_finite

namespace Pi

/-- Helper for Proposition 19.1: the full product of the real open unit interval. -/
private def unitIntervalBox : Set (ℕ → ℝ) :=
  Set.pi Set.univ (fun _ ↦ Set.Ioo (-1) 1)

/-- Helper for Proposition 19.1: a cylinder restricted to finitely many open coordinates is an
open-box generator. -/
private lemma finiteSupportPi_mem_boxBasis {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] (U : (i : ι) → Set (X i))
    (F : Finset ι) (hU : ∀ i ∈ F, IsOpen (U i)) :
    Set.pi (↑F : Set ι) U ∈ boxBasis X := by
  classical
  -- Extend the cylinder by the whole coordinate space outside its finite support.
  let V : (i : ι) → Set (X i) := fun i ↦ if i ∈ F then U i else Set.univ
  have hV : ∀ i, IsOpen (V i) := by
    intro i
    by_cases hi : i ∈ F
    · simpa only [V, if_pos hi] using hU i hi
    · simpa only [V, if_neg hi] using (isOpen_univ : IsOpen (Set.univ : Set (X i)))
  -- The resulting full box imposes exactly the original finite restrictions.
  have hpi : Set.pi (↑F : Set ι) U = Set.pi Set.univ V := by
    ext x
    simp [Set.mem_pi, V]
  exact (mem_boxBasis _).mpr ⟨V, hV, hpi⟩

/-- Helper for Proposition 19.1: the box topology on a dependent product is finer than its
product topology. -/
private lemma box_le_product {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] :
    boxTopologicalSpace X ≤
      (Pi.topologicalSpace : TopologicalSpace ((i : ι) → X i)) := by
  -- Present the product topology by finite-coordinate cylinders.
  rw [pi_eq_generateFrom]
  refine le_generateFrom ?_
  intro g hg
  obtain ⟨U, F, hU, rfl⟩ := hg
  -- Each product generator is already an open-box generator.
  exact TopologicalSpace.GenerateOpen.basic _ (finiteSupportPi_mem_boxBasis U F hU)

/-- Helper for Proposition 19.1: the full open unit-interval box is box-open. -/
private lemma isOpen_unitIntervalBox_box :
    (boxTopologicalSpace (fun _ : ℕ ↦ ℝ)).IsOpen unitIntervalBox := by
  -- Apply the box-openness computation rule coordinatewise.
  simpa only [unitIntervalBox] using
    (isOpen_box (fun _ : ℕ ↦ Set.Ioo (-1 : ℝ) 1) (fun _ ↦ isOpen_Ioo))

/-- Helper for Proposition 19.1: the full open unit-interval box is not product-open. -/
private lemma unitIntervalBox_not_productOpen :
    ¬ (Pi.topologicalSpace : TopologicalSpace (ℕ → ℝ)).IsOpen unitIntervalBox := by
  classical
  intro hopen
  -- At zero, a product-open neighborhood can restrict only finitely many coordinates.
  have hzero : (0 : ℕ → ℝ) ∈ unitIntervalBox := by
    rw [unitIntervalBox, Set.mem_pi]
    intro i hi
    norm_num
  obtain ⟨I, U, hU, hsub⟩ := isOpen_pi_iff.mp hopen 0 hzero
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset I
  let y : ℕ → ℝ := Function.update 0 j 2
  -- Alter an unrestricted coordinate while preserving every cylinder condition.
  have hybasis : y ∈ (I : Set ℕ).pi U := by
    rw [Set.mem_pi]
    intro i hi
    have hij : i ≠ j := by
      intro hij
      apply hj
      exact Finset.mem_coe.mp (hij ▸ hi)
    dsimp only [y]
    rw [Function.update_of_ne hij]
    exact (hU i hi).2
  have hybox : y ∈ unitIntervalBox := hsub hybasis
  -- The changed coordinate equals `2`, contradicting membership in `(-1, 1)`.
  rw [unitIntervalBox, Set.mem_pi] at hybox
  have hycoord := hybox j (Set.mem_univ j)
  simp only [y, Function.update_self] at hycoord
  norm_num at hycoord

/-- Proposition 19.1 (2): On the countably infinite product `ℕ → ℝ`, the box topology is
strictly finer than the product topology. -/
theorem box_lt_product_nat_real :
    boxTopologicalSpace (fun _ : ℕ ↦ ℝ) <
      (Pi.topologicalSpace : TopologicalSpace (ℕ → ℝ)) := by
  -- Combine the general comparison with the open box separating the two topologies.
  refine lt_of_le_of_ne box_le_product ?_
  intro heq
  apply unitIntervalBox_not_productOpen
  rw [← heq]
  exact isOpen_unitIntervalBox_box

end Pi
