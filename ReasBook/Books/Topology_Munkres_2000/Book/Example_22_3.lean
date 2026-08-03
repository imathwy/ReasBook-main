module

public import Mathlib.Topology.Instances.Real.Lemmas

public section

noncomputable section

namespace ThreePointQuotient

/-- The three-point set `A = {a, b, c}` from Example 22.3. -/
inductive Point
  | positive
  | negative
  | zero
  deriving DecidableEq

/-- The point `a` in Example 22.3, representing the positive real numbers. -/
abbrev a : Point := .positive

/-- The point `b` in Example 22.3, representing the negative real numbers. -/
abbrev b : Point := .negative

/-- The point `c` in Example 22.3, representing zero. -/
abbrev c : Point := .zero

/-- The map from `ℝ` onto the three-point set in Example 22.3. -/
noncomputable def map (x : ℝ) : Point :=
  if 0 < x then a else if x < 0 then b else c

/-- The canonical quotient topology induced by `map`. -/
instance instTopologicalSpace : TopologicalSpace Point :=
  TopologicalSpace.coinduced map inferInstance

/-- The map `map : ℝ → Point` is surjective. -/
theorem map_surjective : Function.Surjective map := by
  -- Each point is represented by a real number with the corresponding sign.
  intro y
  cases y with
  | positive =>
      refine ⟨1, ?_⟩
      norm_num [map]
  | negative =>
      refine ⟨-1, ?_⟩
      norm_num [map]
  | zero =>
      refine ⟨0, ?_⟩
      norm_num [map]

/-- Helper for Example 22.3: away from `c`, the preimage under `map` is the union of
the selected positive and negative rays. -/
private lemma preimage_eq_signedRays_of_zero_not_mem {s : Set Point} (hc : c ∉ s) :
    map ⁻¹' s = {x : ℝ | (0 < x ∧ a ∈ s) ∨ (x < 0 ∧ b ∈ s)} := by
  -- Split by sign so that the piecewise definition of `map` reduces in every branch.
  ext x
  by_cases hpos : 0 < x
  · have hneg : ¬ x < 0 := not_lt_of_ge hpos.le
    simp [map, hpos, hneg]
  · by_cases hneg : x < 0
    · simp [map, hpos, hneg]
    · simp [map, hpos, hneg, hc]

/-- Helper for Example 22.3: every subset omitting `c` has open preimage under `map`. -/
private lemma isOpen_preimage_of_zero_not_mem {s : Set Point} (hc : c ∉ s) :
    IsOpen (map ⁻¹' s) := by
  -- Normalize the preimage, then select the appropriate union of the two open rays.
  rw [preimage_eq_signedRays_of_zero_not_mem hc]
  have hposOpen : IsOpen {x : ℝ | 0 < x} := isOpen_lt continuous_const continuous_id
  have hnegOpen : IsOpen {x : ℝ | x < 0} := isOpen_lt continuous_id continuous_const
  by_cases ha : a ∈ s
  · by_cases hb : b ∈ s
    · simpa only [ha, hb, and_true, Set.setOf_or] using hposOpen.union hnegOpen
    · simpa only [ha, hb, and_true, and_false, or_false] using hposOpen
  · by_cases hb : b ∈ s
    · simpa only [ha, hb, and_false, and_true, false_or] using hnegOpen
    · simpa only [ha, hb, and_false, or_self, Set.setOf_false] using
        (isOpen_empty : IsOpen (∅ : Set ℝ))

/-- Helper for Example 22.3: an open preimage whose image subset contains `c` forces
that subset to contain all three points. -/
private lemma eq_univ_of_isOpen_preimage_of_zero_mem {s : Set Point}
    (hopen : IsOpen (map ⁻¹' s)) (hc : c ∈ s) : s = Set.univ := by
  -- Openness at the real number zero supplies a ball contained in the preimage.
  have hzero : (0 : ℝ) ∈ map ⁻¹' s := by
    simpa [map] using hc
  obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp hopen) 0 hzero
  have hhalf : 0 < ε / 2 := by
    linarith
  -- The positive and negative half-radius points lie in that ball.
  have hposBall : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    simp only [sub_zero, abs_of_pos hhalf]
    linarith
  have hnegBall : -(ε / 2) ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    simp only [sub_zero, abs_neg, abs_of_pos hhalf]
    linarith
  have hposPreimage : ε / 2 ∈ map ⁻¹' s := hball hposBall
  have hnegPreimage : -(ε / 2) ∈ map ⁻¹' s := hball hnegBall
  have ha : a ∈ s := by
    simpa [map, hhalf] using hposPreimage
  have hneg : -(ε / 2) < 0 := by
    linarith
  have hhalfNotNeg : ¬ ε / 2 < 0 := not_lt_of_ge hhalf.le
  have hb : b ∈ s := by
    simpa [map, hhalfNotNeg, hneg] using hnegPreimage
  -- Exhausting `Point` now shows that the subset is universal.
  apply Set.eq_univ_of_forall
  intro y
  cases y with
  | positive => exact ha
  | negative => exact hb
  | zero => exact hc

/-- Example 22.3: A subset of the three-point quotient is open exactly when it
omits `c`, unless it is the whole space. -/
theorem isOpen_iff (s : Set Point) : IsOpen s ↔ c ∉ s ∨ s = Set.univ := by
  -- The coinduced topology turns openness into openness of the real preimage.
  rw [isOpen_coinduced]
  constructor
  · intro hopen
    by_cases hc : c ∈ s
    · exact Or.inr (eq_univ_of_isOpen_preimage_of_zero_mem hopen hc)
    · exact Or.inl hc
  · rintro (hc | rfl)
    · exact isOpen_preimage_of_zero_not_mem hc
    · exact isOpen_univ

/-- The sign map from `ℝ` is a quotient map. -/
theorem map_isQuotientMap : Topology.IsQuotientMap map := by
  -- The codomain topology is definitionally coinduced, and surjectivity was established above.
  constructor
  · constructor
    rfl
  · exact map_surjective


end ThreePointQuotient

end
