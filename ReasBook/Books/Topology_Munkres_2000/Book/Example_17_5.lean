module

public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Instances.Real.Lemmas

public section

/-- The separated union `[0, 1] ∪ (2, 3)` as a subset of the real line. -/
abbrev separatedIntervals : Set ℝ :=
  Set.Icc (0 : ℝ) 1 ∪ Set.Ioo 2 3

/-- The copy of `[0, 1]` inside the subspace `separatedIntervals`. -/
abbrev leftSeparatedInterval : Set separatedIntervals :=
  Subtype.val ⁻¹' Set.Icc (0 : ℝ) 1

/-- The copy of `(2, 3)` inside the subspace `separatedIntervals`. -/
abbrev rightSeparatedInterval : Set separatedIntervals :=
  Subtype.val ⁻¹' Set.Ioo (2 : ℝ) 3

/-- In `separatedIntervals`, the two component intervals are complements. -/
theorem leftSeparatedInterval_compl :
    leftSeparatedIntervalᶜ = rightSeparatedInterval := by
  -- Split according to the component containing the subtype point.
  ext x
  rcases x.property with hx | hx
  · simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_Icc, Set.mem_Ioo]
    constructor
    · intro h
      exact False.elim (h hx)
    · intro h
      rcases hx with ⟨_, hx_upper⟩
      rcases h with ⟨h_lower, _⟩
      linarith
  · simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_Icc, Set.mem_Ioo]
    constructor
    · intro _
      exact hx
    · intro _ h
      linarith

/-- Helper for Example 17.5: the left component is cut out by an ambient open interval. -/
lemma leftSeparatedInterval_eq_preimage_Ioo :
    leftSeparatedInterval = Subtype.val ⁻¹' Set.Ioo (-(1 : ℝ) / 2) (3 / 2) := by
  -- On the left component both descriptions hold, while on the right both fail.
  ext x
  rcases x.property with hx | hx
  · simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ioo]
    constructor
    · intro _
      constructor <;> linarith
    · intro _
      exact hx
  · simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ioo]
    constructor
    · intro h
      rcases hx with ⟨hx_lower, _⟩
      rcases h with ⟨_, h_upper⟩
      linarith
    · intro h
      rcases hx with ⟨hx_lower, _⟩
      rcases h with ⟨_, h_upper⟩
      linarith

/-- Helper for Example 17.5: the left interval is open in the separated subspace. -/
lemma isOpen_leftSeparatedInterval : IsOpen leftSeparatedInterval := by
  -- Transport openness of the ambient interval through the subtype inclusion.
  rw [leftSeparatedInterval_eq_preimage_Ioo]
  exact isOpen_Ioo.preimage continuous_subtype_val

/-- Helper for Example 17.5: the right interval is open in the separated subspace. -/
lemma isOpen_rightSeparatedInterval : IsOpen rightSeparatedInterval := by
  -- The right component is already the preimage of an ambient open interval.
  exact isOpen_Ioo.preimage continuous_subtype_val

/-- Example 17.5 (1): The interval `[0, 1]` is clopen in the subspace
`[0, 1] ∪ (2, 3)`. -/
theorem isClopen_leftSeparatedInterval : IsClopen leftSeparatedInterval := by
  -- Openness of the complementary component supplies closedness of the left one.
  constructor
  · rw [← isOpen_compl_iff, leftSeparatedInterval_compl]
    exact isOpen_rightSeparatedInterval
  · exact isOpen_leftSeparatedInterval

/-- Example 17.5 (2): The interval `(2, 3)` is clopen in the subspace
`[0, 1] ∪ (2, 3)`. -/
theorem isClopen_rightSeparatedInterval : IsClopen rightSeparatedInterval := by
  -- Complement the left clopen component and use the component decomposition.
  rw [← leftSeparatedInterval_compl]
  exact isClopen_leftSeparatedInterval.compl
