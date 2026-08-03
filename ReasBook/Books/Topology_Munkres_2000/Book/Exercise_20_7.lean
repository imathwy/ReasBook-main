module

public import Topology_Munkres_2000.Book.Exercise_19_8.Coordinatewise
public import Mathlib.Topology.MetricSpace.UniformConvergence

public section

open scoped ENNReal NNReal UniformConvergence

/-- Helper for Exercise 20.7: evaluating the coordinatewise affine map gives the expected
scalar affine formula. -/
lemma realSequenceAffineMap_apply_of_pos
    (a b x : ℕ → ℝ) (_ha : ∀ i, 0 < a i) (i : ℕ) :
    realSequenceAffineMap a b x i = a i * x i + b i := by
  -- Route correction: use the construction owner's coordinate API instead of unfolding opacity.
  exact realSequenceAffineMap_apply a b x i

/-- Helper for Exercise 20.7: a common upper bound for positive coordinate scales gives a
Lipschitz bound for the associated affine map in the uniform topology. -/
lemma lipschitzWith_realSequenceAffineMap_uniform_of_bddAbove
    (a b : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hupper : ∀ i, a i ≤ M) (ha : ∀ i, 0 < a i) :
    LipschitzWith (Real.toNNReal M) (fun x : ℕ →ᵤ ℝ ↦
      UniformFun.ofFun (realSequenceAffineMap a b (UniformFun.toFun x))) := by
  -- Reduce the global estimate to the same scalar estimate at every coordinate.
  rw [UniformFun.lipschitzWith_iff]
  intro i x y
  rw [edist_dist]
  simp only [UniformFun.toFun_ofFun]
  rw [realSequenceAffineMap_apply_of_pos a b (UniformFun.toFun x) ha i,
    realSequenceAffineMap_apply_of_pos a b (UniformFun.toFun y) ha i]
  -- Translation cancels, and positivity removes the absolute value on the scale factor.
  simp only [Real.dist_eq]
  rw [add_sub_add_right_eq_sub, ← mul_sub, abs_mul, abs_of_pos (ha i)]
  rw [ENNReal.ofReal_mul (ha i).le]
  rw [← Real.dist_eq, ← edist_dist]
  rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal M hM]
  exact mul_le_mul (ENNReal.ofReal_le_ofReal (hupper i)) UniformFun.edist_eval_le
    (by positivity) (by positivity)

/-- Helper for Exercise 20.7: continuity of the coordinatewise affine map forces its positive
coordinate scales to be bounded above. -/
lemma bddAbove_range_of_continuous_realSequenceAffineMap_uniform
    (a b : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (hc : Continuous (fun x : ℕ →ᵤ ℝ ↦
      UniformFun.ofFun (realSequenceAffineMap a b (UniformFun.toFun x)))) :
    BddAbove (Set.range a) := by
  -- If the scales were unbounded, a one-coordinate spike would be arbitrarily small at zero.
  by_contra hbounded
  rw [not_bddAbove_iff] at hbounded
  let f := fun x : ℕ →ᵤ ℝ ↦
    UniformFun.ofFun (realSequenceAffineMap a b (UniformFun.toFun x))
  have hc0 := EMetric.continuousAt_iff.mp
    (hc.continuousAt : ContinuousAt f (UniformFun.ofFun 0))
  obtain ⟨δ, hδ, hcontrol⟩ := hc0 (1 / 2 : ℝ≥0∞) (by norm_num)
  let C : ℝ := if δ = ∞ then 0 else δ.toReal⁻¹
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hbounded C
  let x : ℕ →ᵤ ℝ := UniformFun.ofFun (Function.update 0 i (a i)⁻¹)
  have hspike : ENNReal.ofReal (a i)⁻¹ < δ := by
    by_cases hδtop : δ = ∞
    · simp [hδtop]
    · have hδreal : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδtop
      have hai : δ.toReal⁻¹ < a i := by
        simpa [C, hδtop] using hi
      have hinv : (a i)⁻¹ < δ.toReal := (inv_lt_comm₀ (ha i) hδreal).2 hai
      exact (ENNReal.ofReal_lt_iff_lt_toReal (inv_nonneg.mpr (ha i).le) hδtop).2 hinv
  have hinput : edist x (UniformFun.ofFun 0) < δ := by
    apply lt_of_le_of_lt (UniformFun.edist_le.mpr fun j ↦ ?_) hspike
    rw [edist_dist]
    simp only [x, UniformFun.toFun_ofFun, Pi.zero_apply, dist_zero_right]
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (ha i))]
    · simp only [Function.update_of_ne hji]
      simp
  -- Its image still moves by exactly one in the selected coordinate, contradicting continuity.
  have himage := hcontrol hinput
  have heval := lt_of_le_of_lt (UniformFun.edist_eval_le (x := i)) himage
  rw [edist_dist] at heval
  simp only [UniformFun.toFun_ofFun] at heval
  rw [realSequenceAffineMap_apply_of_pos a b (UniformFun.toFun x) ha i,
    realSequenceAffineMap_apply_of_pos a b 0 ha i] at heval
  simp only [x, UniformFun.toFun_ofFun, Function.update_self, Pi.zero_apply] at heval
  norm_num [ne_of_gt (ha i), Real.dist_eq] at heval

/-- Helper for Exercise 20.7: reciprocal coordinate scales and adjusted translations define a
 two-sided inverse to a coordinatewise affine map with positive scales. -/
lemma realSequenceAffineMap_uniform_inverse
    (a b : ℕ → ℝ) (ha : ∀ i, 0 < a i) :
    let f := fun x : ℕ →ᵤ ℝ ↦
      UniformFun.ofFun (realSequenceAffineMap a b (UniformFun.toFun x))
    let g := fun y : ℕ →ᵤ ℝ ↦ UniformFun.ofFun
      (realSequenceAffineMap (fun i ↦ (a i)⁻¹) (fun i ↦ -(a i)⁻¹ * b i)
        (UniformFun.toFun y))
    Function.LeftInverse g f ∧ Function.RightInverse g f := by
  -- Both inverse identities are coordinatewise field calculations.
  dsimp only
  constructor
  · intro x
    apply UniformFun.toFun.injective
    funext i
    simp only [UniformFun.toFun_ofFun]
    rw [realSequenceAffineMap_apply_of_pos (fun i ↦ (a i)⁻¹)
      (fun i ↦ -(a i)⁻¹ * b i) (realSequenceAffineMap a b (UniformFun.toFun x))
      (fun j ↦ inv_pos.mpr (ha j)) i]
    rw [realSequenceAffineMap_apply_of_pos a b (UniformFun.toFun x) ha i]
    field_simp [ne_of_gt (ha i)]
    ring
  · intro y
    apply UniformFun.toFun.injective
    funext i
    simp only [UniformFun.toFun_ofFun]
    rw [realSequenceAffineMap_apply_of_pos a b
      (realSequenceAffineMap (fun i ↦ (a i)⁻¹) (fun i ↦ -(a i)⁻¹ * b i)
        (UniformFun.toFun y)) ha i]
    rw [realSequenceAffineMap_apply_of_pos (fun i ↦ (a i)⁻¹)
      (fun i ↦ -(a i)⁻¹ * b i) (UniformFun.toFun y) (fun j ↦ inv_pos.mpr (ha j)) i]
    field_simp [ne_of_gt (ha i)]
    ring

/-- Exercise 20.7 (1): The coordinatewise affine map on real sequence space with the
uniform topology is continuous exactly when its positive scale factors are bounded above. -/
theorem continuous_realSequenceAffineMap_uniform_iff
    (a b : ℕ → ℝ) (ha : ∀ i, 0 < a i) :
    Continuous (fun x : ℕ →ᵤ ℝ ↦
      UniformFun.ofFun (realSequenceAffineMap a b (UniformFun.toFun x))) ↔
      BddAbove (Set.range a) := by
  -- Necessity is the spike contradiction; sufficiency follows from a global Lipschitz bound.
  constructor
  · exact bddAbove_range_of_continuous_realSequenceAffineMap_uniform a b ha
  · intro hb
    rw [bddAbove_def] at hb
    obtain ⟨M, hM⟩ := hb
    have hupper : ∀ i, a i ≤ M := fun i ↦ hM (a i) ⟨i, rfl⟩
    have hM0 : 0 ≤ M := (ha 0).le.trans (hupper 0)
    exact (lipschitzWith_realSequenceAffineMap_uniform_of_bddAbove
      a b M hM0 hupper ha).continuous

/-- Exercise 20.7 (2): The coordinatewise affine map on real sequence space with the
uniform topology is a homeomorphism exactly when its positive scale factors and their
reciprocals are bounded above. -/
theorem isHomeomorph_realSequenceAffineMap_uniform_iff
    (a b : ℕ → ℝ) (ha : ∀ i, 0 < a i) :
    IsHomeomorph (fun x : ℕ →ᵤ ℝ ↦
      UniformFun.ofFun (realSequenceAffineMap a b (UniformFun.toFun x))) ↔
      BddAbove (Set.range a) ∧ BddAbove (Set.range fun i ↦ (a i)⁻¹) := by
  let f := fun x : ℕ →ᵤ ℝ ↦
    UniformFun.ofFun (realSequenceAffineMap a b (UniformFun.toFun x))
  let g := fun y : ℕ →ᵤ ℝ ↦ UniformFun.ofFun
    (realSequenceAffineMap (fun i ↦ (a i)⁻¹) (fun i ↦ -(a i)⁻¹ * b i)
      (UniformFun.toFun y))
  have hinv := realSequenceAffineMap_uniform_inverse a b ha
  constructor
  · intro hf
    -- A homeomorphism makes both the affine map and its explicit inverse continuous.
    have hfa : BddAbove (Set.range a) :=
      (continuous_realSequenceAffineMap_uniform_iff a b ha).mp hf.continuous
    obtain ⟨_, q, hqleft, hqright, hqcont⟩ := isHomeomorph_iff_exists_inverse.mp hf
    have hqg : q = g := by
      funext y
      exact hf.injective ((hqright y).trans (hinv.2 y).symm)
    have hgcont : Continuous g := by
      simpa [hqg] using hqcont
    have hga : BddAbove (Set.range fun i ↦ (a i)⁻¹) :=
      (continuous_realSequenceAffineMap_uniform_iff (fun i ↦ (a i)⁻¹)
        (fun i ↦ -(a i)⁻¹ * b i) (fun i ↦ inv_pos.mpr (ha i))).mp hgcont
    exact ⟨hfa, hga⟩
  · rintro ⟨hfa, hga⟩
    -- The two boundedness hypotheses make the affine map and reciprocal-affine inverse continuous.
    have hfcont : Continuous f :=
      (continuous_realSequenceAffineMap_uniform_iff a b ha).mpr hfa
    have hgcont : Continuous g :=
      (continuous_realSequenceAffineMap_uniform_iff (fun i ↦ (a i)⁻¹)
        (fun i ↦ -(a i)⁻¹ * b i) (fun i ↦ inv_pos.mpr (ha i))).mpr hga
    exact isHomeomorph_iff_exists_inverse.mpr ⟨hfcont, g, hinv.1, hinv.2, hgcont⟩
