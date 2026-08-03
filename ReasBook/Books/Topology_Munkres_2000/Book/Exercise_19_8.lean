module

public import Topology_Munkres_2000.Book.Exercise_19_8.Coordinatewise

public section

/-- Exercise 19.8 (1): the coordinatewise affine map with positive scale factors is a
homeomorphism of real sequence space with the product topology. -/
theorem isHomeomorph_realSequenceAffineMap_product
    (a b : ℕ → ℝ) (ha : ∀ i, 0 < a i) :
    IsHomeomorph (realSequenceAffineMap a b) := by
  let h := realSequenceAffineHomeomorph a b fun i ↦ (ha i).ne'
  have h_apply : (h : (ℕ → ℝ) → ℕ → ℝ) = realSequenceAffineMap a b := by
    funext x
    exact realSequenceAffineHomeomorph_apply a b (fun i ↦ (ha i).ne') x
  rw [← h_apply]
  exact h.isHomeomorph

/-- Exercise 19.8 (2): the coordinatewise affine map with positive scale factors is also a
homeomorphism of real sequence space with the box topology. -/
theorem isHomeomorph_realSequenceAffineMap_box
    (a b : ℕ → ℝ) (ha : ∀ i, 0 < a i) :
    IsHomeomorph (Pi.boxMap fun i x ↦ a i * x + b i) := by
  exact isHomeomorph_realSequenceAffineMap_box_of_ne_zero a b fun i ↦ (ha i).ne'
