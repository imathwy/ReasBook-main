module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.IntermediateValue

public section

/-- Theorem 3.0.1. Intermediate value theorem: a continuous real-valued function on
`Set.Icc a b` attains every value between its endpoint values. -/
theorem intermediateValueOnIcc {a b : ℝ} (hab : a ≤ b) (f : Set.Icc a b → ℝ)
    (hf : Continuous f) (r : ℝ)
    (hr : r ∈ Set.uIcc (f ⟨a, Set.left_mem_Icc.mpr hab⟩)
      (f ⟨b, Set.right_mem_Icc.mpr hab⟩)) :
    ∃ c : Set.Icc a b, f c = r := by
  have hIccSpace : PreconnectedSpace (Set.Icc a b) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  have hIcc : IsPreconnected (Set.univ : Set (Set.Icc a b)) :=
    hIccSpace.isPreconnected_univ
  rcases Set.mem_uIcc.mp hr with hr | hr
  · simpa only [Set.image_univ, Set.mem_range] using hIcc.intermediate_value
      (Set.mem_univ ⟨a, Set.left_mem_Icc.mpr hab⟩)
      (Set.mem_univ ⟨b, Set.right_mem_Icc.mpr hab⟩) hf.continuousOn hr
  · simpa only [Set.image_univ, Set.mem_range] using hIcc.intermediate_value
      (Set.mem_univ ⟨b, Set.right_mem_Icc.mpr hab⟩)
      (Set.mem_univ ⟨a, Set.left_mem_Icc.mpr hab⟩) hf.continuousOn hr
