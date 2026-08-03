module

public import Topology_Munkres_2000.Book.Proposition_19_1.Comparison
public import Mathlib.Topology.Instances.Real.Lemmas
import Topology_Munkres_2000.Book.Remark_14_2
import Topology_Munkres_2000.Book.Theorem_19_2.Basis
import Topology_Munkres_2000.Book.Definition_5_3.CartesianProduct

public section

open scoped CartesianProduct

/-- Example 19.1 (1): products of open real intervals form a basis for the canonical
topology on finite-dimensional real Cartesian space. -/
theorem isTopologicalBasis_realOpenBoxes (n : ℕ) :
    TopologicalSpace.IsTopologicalBasis
      {S : Set (Fin n → ℝ) |
        ∃ a b : Fin n → ℝ, (∀ i, a i < b i) ∧
          S = ∏ i, Set.Ioo (a i) (b i)} := by
  rw [← Pi.box_eq_product_of_finite]
  have hIntervals :
      TopologicalSpace.IsTopologicalBasis (OrderTopology.openIntervals ℝ) := by
    rw [← OrderTopology.basis_eq_openIntervals ℝ]
    exact OrderTopology.isTopologicalBasis_basis
  rw [show
    {S : Set (Fin n → ℝ) |
      ∃ a b : Fin n → ℝ, (∀ i, a i < b i) ∧ S = ∏ i, Set.Ioo (a i) (b i)} =
      {S | ∃ U : Fin n → Set ℝ,
        (∀ i, U i ∈ OrderTopology.openIntervals ℝ) ∧ S = Set.pi Set.univ U} by
    ext S
    constructor
    · rintro ⟨a, b, hab, rfl⟩
      exact ⟨fun i ↦ Set.Ioo (a i) (b i),
        fun i ↦ OrderTopology.mem_openIntervals.mpr ⟨a i, b i, hab i, rfl⟩, rfl⟩
    · rintro ⟨U, hU, rfl⟩
      choose a b hab hU_eq using fun i ↦ OrderTopology.mem_openIntervals.mp (hU i)
      exact ⟨a, b, hab, congrArg (Set.pi Set.univ) (funext hU_eq)⟩]
  exact Pi.isTopologicalBasis_box (fun _ : Fin n ↦ hIntervals)

/-- Example 19.1 (2): on finite-dimensional real Cartesian space, the box topology
equals the canonical product topology. -/
theorem realBoxTopology_eq_productTopology (n : ℕ) :
    Pi.boxTopologicalSpace (fun _ : Fin n ↦ ℝ) =
      Pi.topologicalSpace :=
  Pi.box_eq_product_of_finite

/- Example 19.1 (3): the canonical topology on `Fin n → ℝ` is the product topology. -/
#check Pi.topologicalSpace
