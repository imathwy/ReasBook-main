module

public import Topology_Munkres_2000.Book.Exercise_48_7.CountableDense
public import Mathlib.Topology.GDelta.MetrizableSpace

public section

/- Exercise 48.7 (a). The continuity set of a real-valued function on `ℝ` is a `Gδ` set. -/
#check (IsGδ.setOf_continuousAt : ∀ f : ℝ → ℝ, IsGδ {x | ContinuousAt f x})

/-- Exercise 48.7. If `D` is a countable dense subset of `ℝ`, no function
`f : ℝ → ℝ` is continuous precisely at the points of `D`. -/
theorem not_exists_continuousAt_set_eq_of_countable_dense
    (D : Set ℝ) (hD_countable : D.Countable) (hD_dense : Dense D) :
    ¬ ∃ f : ℝ → ℝ, {x | ContinuousAt f x} = D := by
  -- An alleged witness identifies `D` with a continuity set.
  rintro ⟨f, hf⟩
  -- Continuity sets are `Gδ`, contradicting the countable dense-set obstruction.
  apply hD_countable.not_isGδ_of_dense hD_dense
  rw [← hf]
  exact IsGδ.setOf_continuousAt f
