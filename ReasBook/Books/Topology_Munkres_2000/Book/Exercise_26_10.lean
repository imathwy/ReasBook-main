module

public import Mathlib.Topology.«UniformSpace».Dini
public import Topology_Munkres_2000.Book.Exercise_21_9.MovingSpike

public section

/- Exercise 26.10 (1): Dini's theorem for an increasing sequence of continuous
real-valued functions on a compact space. -/
#check Monotone.tendstoUniformly_of_forall_tendsto

/-- Helper for Exercise 26.10: a fixed positive error at every index prevents uniform
convergence. -/
private lemma notTendstoUniformly_of_forall_exists_dist_ge
    {α β : Type*} [PseudoMetricSpace β] (F : ℕ → α → β) (f : α → β) (ε : ℝ)
    (hε : 0 < ε) (hF : ∀ n, ∃ x, ε ≤ dist (f x) (F n x)) :
    ¬ TendstoUniformly F f Filter.atTop := by
  intro hUniform
  -- Uniform convergence eventually makes every pointwise error smaller than `ε`.
  have hEventually := (Metric.tendstoUniformly_iff.mp hUniform) ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hEventually
  obtain ⟨x, hx⟩ := hF N
  -- The witness at index `N` contradicts the eventual strict estimate.
  exact (not_lt_of_ge hx) (hN N le_rfl x)

namespace HalfOpenPower

/-- The increasing power sequence on the noncompact half-open unit interval. -/
def sequence (n : ℕ) (x : Set.Ico (0 : ℝ) 1) : ℝ :=
  -((x : ℝ) ^ (n + 1))

/-- Every term of `HalfOpenPower.sequence` is continuous. -/
theorem continuous (n : ℕ) : Continuous (sequence n) := by
  -- Compose the continuous subtype coercion with powers and negation.
  unfold sequence
  fun_prop

/-- `HalfOpenPower.sequence` is monotone increasing in the pointwise function order. -/
theorem monotone : Monotone sequence := by
  intro n m hnm x
  -- Powers decrease with the exponent on `[0,1]`, so their negatives increase.
  exact neg_le_neg (pow_le_pow_of_le_one x.property.1 x.property.2.le
    (Nat.add_le_add_right hnm 1))

/-- `HalfOpenPower.sequence` converges pointwise to zero. -/
theorem tendstoAt (x : Set.Ico (0 : ℝ) 1) :
    Filter.Tendsto (fun n ↦ sequence n x) Filter.atTop (nhds 0) := by
  -- Shift the standard geometric-power limit from exponent `n` to exponent `n + 1`.
  have hPower :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one x.property.1 x.property.2).comp
      (Filter.tendsto_add_atTop_nat 1)
  -- Negation preserves convergence to zero.
  simpa only [sequence, Function.comp_apply, neg_zero] using hPower.neg

/-- The half-open unit interval is not a compact space. -/
theorem notCompactSpace : ¬ CompactSpace (Set.Ico (0 : ℝ) 1) := by
  intro hCompactSpace
  -- Compactness of the subtype would make the half-open interval compact as a set.
  have hCompact : IsCompact (Set.Ico (0 : ℝ) 1) :=
    isCompact_iff_compactSpace.mpr hCompactSpace
  have hImpossible : (1 : ℝ) ≤ 0 := isCompact_Ico_iff.mp hCompact
  norm_num at hImpossible

/-- Helper for Exercise 26.10: every half-open power term has error at least `1 / 2`
at a suitable point. -/
private lemma exists_dist_zero_sequence_ge_half (n : ℕ) :
    ∃ x : Set.Ico (0 : ℝ) 1, (1 / 2 : ℝ) ≤ dist 0 (sequence n x) := by
  let point : ℝ := 1 - 1 / (2 * (n + 1 : ℝ))
  have hPoint : point ∈ Set.Ico (0 : ℝ) 1 := by
    constructor
    · -- The removed fraction is at most `1 / 2`.
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hden : (2 : ℝ) ≤ 2 * (n + 1 : ℝ) := by
        nlinarith
      have htwo : (0 : ℝ) < 2 := by
        norm_num
      have hfrac : 1 / (2 * (n + 1 : ℝ)) ≤ (1 : ℝ) / 2 := by
        exact one_div_le_one_div_of_le htwo hden
      dsimp only [point]
      nlinarith
    · -- The removed fraction is positive, so the point lies strictly below `1`.
      have hden : 0 < (2 : ℝ) * (n + 1 : ℝ) := by
        positivity
      have hfrac : 0 < 1 / ((2 : ℝ) * (n + 1 : ℝ)) := one_div_pos.mpr hden
      dsimp only [point]
      linarith
  refine ⟨⟨point, hPoint⟩, ?_⟩
  -- Bernoulli's inequality gives the uniform lower bound for the matching power.
  have hMinusOne : (-1 : ℝ) ≤ point := by
    linarith [hPoint.1]
  have hBernoulli :
      1 + ((n + 1 : ℕ) : ℝ) * (point - 1) ≤ point ^ (n + 1) :=
    one_add_mul_sub_le_pow hMinusOne (n + 1)
  have hden : 0 < (n + 1 : ℝ) := by
    positivity
  have hLower : (1 / 2 : ℝ) ≤ 1 + ((n + 1 : ℕ) : ℝ) * (point - 1) := by
    dsimp only [point]
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
    ring_nf
    norm_num
  have hPower : (1 / 2 : ℝ) ≤ point ^ (n + 1) := hLower.trans hBernoulli
  simpa only [sequence, Real.dist_eq, sub_neg_eq_add, zero_add, abs_neg,
    abs_of_nonneg (pow_nonneg hPoint.1 (n + 1))] using hPower

/-- Exercise 26.10 (2): Without compactness, a monotone increasing sequence of
continuous functions can converge pointwise but not uniformly to a continuous limit. -/
theorem notTendstoUniformly :
    ¬ TendstoUniformly sequence (fun _ ↦ 0) Filter.atTop := by
  -- The fixed half-unit error witnesses contradict uniform convergence.
  have hHalf : (0 : ℝ) < 1 / 2 := by
    norm_num
  exact notTendstoUniformly_of_forall_exists_dist_ge sequence (fun _ ↦ 0) (1 / 2)
    hHalf exists_dist_zero_sequence_ge_half

end HalfOpenPower

namespace CompactMovingSpike

/-- The moving-spike sequence restricted to the compact closed unit interval. -/
noncomputable def sequence (n : ℕ) (x : Set.Icc (0 : ℝ) 1) : ℝ :=
  MovingSpike.sequence n (x : ℝ)

/-- Every term of `CompactMovingSpike.sequence` is continuous. -/
theorem continuous (n : ℕ) : Continuous (sequence n) :=
  (MovingSpike.continuous n).comp continuous_subtype_val

/-- `CompactMovingSpike.sequence` converges pointwise to zero. -/
theorem tendstoAt (x : Set.Icc (0 : ℝ) 1) :
    Filter.Tendsto (fun n ↦ sequence n x) Filter.atTop (nhds 0) :=
  MovingSpike.tendsto_at x

/-- `CompactMovingSpike.sequence` is not monotone increasing. -/
theorem notMonotone : ¬ Monotone sequence := by
  intro hMonotone
  have hOne : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    norm_num
  let x : Set.Icc (0 : ℝ) 1 := ⟨1, hOne⟩
  -- At `x = 1`, the first moving spike is larger than the second.
  have hStep := hMonotone (Nat.zero_le 1) x
  norm_num [sequence, MovingSpike.sequence, x] at hStep

/-- Helper for Exercise 26.10: each restricted moving spike equals `1` at its center. -/
private lemma exists_sequence_eq_one (n : ℕ) :
    ∃ x : Set.Icc (0 : ℝ) 1, sequence n x = 1 := by
  have hCenter : 1 / ((n + 1 : ℕ) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · have hden : (0 : ℝ) < (n + 1 : ℕ) := by
        positivity
      rw [div_le_one hden]
      norm_num
  refine ⟨⟨1 / ((n + 1 : ℕ) : ℝ), hCenter⟩, ?_⟩
  -- Restriction to the subtype preserves the imported center computation.
  simpa only [sequence] using MovingSpike.sequence_center n

/-- Exercise 26.10 (3): On a compact space, a nonmonotone sequence of continuous
functions can converge pointwise but not uniformly to a continuous limit. -/
theorem notTendstoUniformly :
    ¬ TendstoUniformly sequence (fun _ ↦ 0) Filter.atTop := by
  -- Every index has a center where the error from zero is exactly one.
  apply notTendstoUniformly_of_forall_exists_dist_ge sequence (fun _ ↦ 0) 1
  · norm_num
  · intro n
    obtain ⟨x, hx⟩ := exists_sequence_eq_one n
    refine ⟨x, ?_⟩
    rw [hx]
    norm_num

end CompactMovingSpike
