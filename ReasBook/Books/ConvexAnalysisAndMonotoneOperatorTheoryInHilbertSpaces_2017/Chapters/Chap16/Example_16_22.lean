import Mathlib
import BauschkeLean.Chap08.Corollary_8_39
import BauschkeLean.Chap09.Example_9_13
import BauschkeLean.Chap11.Definition_11_11
import BauschkeLean.Chap12.Proposition_12_15
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_17

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace ERealFunction

local notation "L2pos" => ℓ²(ℕ+, ℝ)

/-- The one-variable coordinate function `t ↦ n * t^(2n)` from Example 16.22. -/
def positiveNatWeightedEvenPowerCoordinate (n : ℕ+) : ℝ → ℝ :=
  fun t ↦ (n : ℝ) * t ^ (2 * (n : ℕ))

-- Proof sketch: unfold `positiveNatWeightedEvenPowerCoordinate`.
/-- Evaluating the `n`th coordinate function recovers the explicit formula `n * t^(2n)`. -/
@[simp] theorem positiveNatWeightedEvenPowerCoordinate_apply (n : ℕ+) (t : ℝ) :
    positiveNatWeightedEvenPowerCoordinate n t = (n : ℝ) * t ^ (2 * (n : ℕ)) :=
  rfl

/-- The coordinate function from Example 16.22 vanishes at `0`. -/
@[simp] theorem positiveNatWeightedEvenPowerCoordinate_zero (n : ℕ+) :
    positiveNatWeightedEvenPowerCoordinate n 0 = 0 := by
  simp [positiveNatWeightedEvenPowerCoordinate]

-- Proof sketch: `n : ℝ` is nonnegative and `t^(2n)` is nonnegative because the exponent is even.
/-- The coordinate function `t ↦ n * t^(2n)` is pointwise nonnegative. -/
theorem positiveNatWeightedEvenPowerCoordinate_nonneg (n : ℕ+) (t : ℝ) :
    0 ≤ positiveNatWeightedEvenPowerCoordinate n t := by
  rw [positiveNatWeightedEvenPowerCoordinate]
  have hpow : 0 ≤ t ^ (2 * (n : ℕ)) := by
    simpa [pow_mul] using pow_nonneg (sq_nonneg t) (n : ℕ)
  exact mul_nonneg (by positivity) hpow

/-- Viewing the coordinate function through `toEReal` preserves the value at `0`. -/
@[simp] theorem positiveNatWeightedEvenPowerCoordinate_toEReal_zero (n : ℕ+) :
    (((positiveNatWeightedEvenPowerCoordinate n).toEReal) 0 : EReal) = 0 := by
  simp [positiveNatWeightedEvenPowerCoordinate]

-- Proof sketch: rewrite through `Function.toEReal_apply` and use real-valued nonnegativity.
/-- The `toEReal` lift of the coordinate function attains its minimum at `0`. -/
theorem positiveNatWeightedEvenPowerCoordinate_toEReal_nonneg (n : ℕ+) (t : ℝ) :
    (((positiveNatWeightedEvenPowerCoordinate n).toEReal) 0 : EReal) ≤
      (positiveNatWeightedEvenPowerCoordinate n).toEReal t := by
  rw [positiveNatWeightedEvenPowerCoordinate_toEReal_zero]
  simp only [Function.toEReal_apply]
  exact_mod_cast positiveNatWeightedEvenPowerCoordinate_nonneg n t

-- Proof sketch: the exponent `2n` is even, so `t ↦ n * t^(2n)` is convex, lower semicontinuous,
-- finite everywhere, and minimized at `0`.
/-- Each coordinate function from Example 16.22 belongs to `Γ₀(ℝ)`. -/
theorem positiveNatWeightedEvenPowerCoordinate_mem_gammaZero (n : ℕ+) :
    (positiveNatWeightedEvenPowerCoordinate n).toEReal ∈ Γ₀(ℝ) := by
  have hcont : Continuous (positiveNatWeightedEvenPowerCoordinate n) := by
    simpa [positiveNatWeightedEvenPowerCoordinate] using
      (continuous_const.mul (continuous_pow (2 * (n : ℕ))))
  have hpow_conv :
      _root_.ConvexOn ℝ Set.univ (fun t : ℝ ↦ t ^ (2 * (n : ℕ))) := by
    have heven : Even (2 * (n : ℕ)) := even_two.mul_right (n : ℕ)
    simpa using heven.convexOn_pow
  have hconv :
      _root_.ConvexOn ℝ Set.univ (positiveNatWeightedEvenPowerCoordinate n) := by
    simpa [positiveNatWeightedEvenPowerCoordinate, smul_eq_mul] using
      hpow_conv.smul (show 0 ≤ (n : ℝ) by positivity)
  rw [mem_gammaZero_iff]
  constructor
  · change LowerSemicontinuous (Real.toEReal ∘ positiveNatWeightedEvenPowerCoordinate n)
    exact (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous
  · refine ⟨by simp [Function.effectiveDomain_toEReal], subset_rfl, ?_⟩
    intro x hx y hy a ha0 ha1
    have hreal :
        positiveNatWeightedEvenPowerCoordinate n (a • x + (1 - a) • y) ≤
          a * positiveNatWeightedEvenPowerCoordinate n x +
            (1 - a) * positiveNatWeightedEvenPowerCoordinate n y := by
      simpa [smul_eq_mul] using
        hconv.2 (by simp) (by simp) ha0.le (sub_nonneg.mpr ha1.le) (by linarith)
    have hcast :
        ((positiveNatWeightedEvenPowerCoordinate n (a • x + (1 - a) • y) : ℝ) : EReal) ≤
          ((a * positiveNatWeightedEvenPowerCoordinate n x +
            (1 - a) * positiveNatWeightedEvenPowerCoordinate n y : ℝ) : EReal) := by
      exact_mod_cast hreal
    simpa [Function.toEReal_apply, EReal.coe_mul, EReal.coe_add] using hcast

/-- Helper for Example 16 22: the scalar defect `t - t^(2n)` never exceeds `1`. -/
private theorem sub_even_power_le_one (n : ℕ+) (t : ℝ) :
    t - t ^ (2 * (n : ℕ)) ≤ 1 := by
  by_cases ht : t ≤ 1
  · have hpow_nonneg : 0 ≤ t ^ (2 * (n : ℕ)) := by
      simpa [pow_mul] using pow_nonneg (sq_nonneg t) (n : ℕ)
    exact (sub_le_self _ hpow_nonneg).trans ht
  · have ht1 : 1 < t := lt_of_not_ge ht
    have hpow : t ≤ t ^ (2 * (n : ℕ)) := by
      simpa using
        (pow_le_pow_right₀ ht1.le (show (1 : ℕ) ≤ 2 * (n : ℕ) by
          have hn : 1 ≤ (n : ℕ) := Nat.succ_le_of_lt n.2
          omega))
    linarith

/-- The function from Example 16.22 on `ℓ²(ℕ+, ℝ)`, given by
`f(ξ) = ∑ₙ n * ξₙ^(2n)`, realized through the canonical inner-product series owner from
Example 9.13 specialized to the standard unit vectors of `ℓ²(ℕ+, ℝ)`. -/
noncomputable def positiveNatWeightedEvenPowerSeries : L2pos → Set.Ioi (⊥ : EReal) :=
  innerProductSeriesFunction
    (fun n ↦ lp.single 2 n (1 : ℝ))
    (fun n ↦ (positiveNatWeightedEvenPowerCoordinate n).toEReal)
    positiveNatWeightedEvenPowerCoordinate_toEReal_zero
    positiveNatWeightedEvenPowerCoordinate_toEReal_nonneg

-- Proof sketch: unfold the canonical inner-product series specialization and simplify
-- `⟪ξ, lp.single 2 n 1⟫_ℝ = ξ n`.
/-- Coercing the Example 16.22 function to `EReal` recovers the explicit weighted coordinate
family sum. -/
@[simp] theorem positiveNatWeightedEvenPowerSeries_apply (x : L2pos) :
    (positiveNatWeightedEvenPowerSeries x : EReal) =
      familySum
        (fun (n : ℕ+) (ξ : L2pos) ↦
          (((n : ℝ) * (ξ n) ^ (2 * (n : ℕ)) : ℝ) : EReal)) x := by
  rw [positiveNatWeightedEvenPowerSeries, innerProductSeriesFunction_apply]
  congr 1
  ext n ξ
  simp only [Function.toEReal_apply, positiveNatWeightedEvenPowerCoordinate_apply,
    lp.inner_single_right]
  have hinner : inner ℝ (ξ n) 1 = ξ n := by
    change (1 : ℝ) * star (ξ n) = ξ n
    simp
  rw [hinner]

/-- Helper for Example 16 22: the weighted even-power series vanishes at the origin. -/
@[simp] theorem positiveNatWeightedEvenPowerSeries_zero :
    (positiveNatWeightedEvenPowerSeries 0 : EReal) = 0 := by
  simpa [positiveNatWeightedEvenPowerSeries] using
    innerProductSeriesFunction_zero
      (fun n ↦ lp.single 2 n (1 : ℝ))
      (fun n ↦ (positiveNatWeightedEvenPowerCoordinate n).toEReal)
      positiveNatWeightedEvenPowerCoordinate_toEReal_zero
      positiveNatWeightedEvenPowerCoordinate_toEReal_nonneg

/-- Helper for Example 16 22: finite sums of real numbers commute with coercion to `EReal`. -/
private theorem finset_sum_coe_real_local {ι : Type*} (s : Finset ι) (r : ι → ℝ) :
    (((Finset.sum s r : ℝ)) : EReal) = Finset.sum s (fun i ↦ ((r i : ℝ) : EReal)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha hs
    simp [Finset.sum_insert, ha, hs, EReal.coe_add]

/-- Helper for Example 16 22: every finite partial sum of the series is the cast of the
corresponding real partial sum. -/
private theorem positiveNatWeightedEvenPowerSeries_partialSum_eq_coe_real
    (J : Finset ℕ+) (x : L2pos) :
    Finset.sum J
        (fun n ↦ (((n : ℝ) * (x n) ^ (2 * (n : ℕ)) : ℝ) : EReal)) =
      ((Finset.sum J (fun n ↦ ((n : ℝ) * (x n) ^ (2 * (n : ℕ)) : ℝ)) : ℝ) : EReal) := by
  simpa using
    (finset_sum_coe_real_local J
      (fun k : ℕ+ ↦ ((k : ℝ) * (x k) ^ (2 * (k : ℕ)) : ℝ))).symm

/-- Helper for Example 16 22: for a nonnegative family over `ℕ+`, restricting the supremum of
nonempty finite partial sums to those containing a fixed index does not change its value. -/
private theorem familySum_eq_iSup_nonemptyFinitePartialSums_containing
    (g : ℕ+ → EReal) (hg_nonneg : ∀ n, 0 ≤ g n) (n : ℕ+) :
    (⨆ J : {s : Finset ℕ+ // s.Nonempty}, Finset.sum (J : Finset ℕ+) g) =
      ⨆ J : {s : Finset ℕ+ // s.Nonempty ∧ n ∈ s}, Finset.sum (J : Finset ℕ+) g := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun J ↦ ?_
    by_cases hn : n ∈ (J : Finset ℕ+)
    · exact le_iSup
        (fun K : {s : Finset ℕ+ // s.Nonempty ∧ n ∈ s} ↦ Finset.sum (K : Finset ℕ+) g)
        ⟨J, J.2, hn⟩
    · have hle :
          Finset.sum (J : Finset ℕ+) g ≤ Finset.sum (insert n (J : Finset ℕ+)) g := by
        rw [Finset.sum_insert hn]
        exact le_add_of_nonneg_left (hg_nonneg n)
      exact hle.trans <|
        le_iSup
          (fun K : {s : Finset ℕ+ // s.Nonempty ∧ n ∈ s} ↦ Finset.sum (K : Finset ℕ+) g)
          ⟨insert n (J : Finset ℕ+), Finset.insert_nonempty _ _, Finset.mem_insert_self _ _⟩
  · refine iSup_le fun J ↦ ?_
    exact le_iSup
      (fun K : {s : Finset ℕ+ // s.Nonempty} ↦ Finset.sum (K : Finset ℕ+) g)
      ⟨J, J.2.1⟩

/-- Helper for Example 16 22: the comparison sequence `n * (1 / 4)^n` is summable over `ℕ+`. -/
private theorem positiveNat_geometricComparison_summable :
    Summable (fun n : ℕ+ ↦ (n : ℝ) * (1 / 4 : ℝ) ^ (n : ℕ)) := by
  have hlog : 0 < Real.log 4 := by
    exact Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hnat :
      Summable (fun n : ℕ ↦ (n : ℝ) * (1 / 4 : ℝ) ^ n) := by
    refine (Real.summable_pow_mul_exp_neg_nat_mul 1 (r := Real.log 4) hlog).congr ?_
    intro n
    rw [pow_one, show -(Real.log 4) * (n : ℝ) = (n : ℝ) * (-(Real.log 4)) by ring,
      Real.exp_nat_mul, Real.exp_neg]
    congr 1
    rw [Real.exp_log (by positivity)]
    norm_num
  simpa using hnat.comp_injective (show Function.Injective (fun n : ℕ+ ↦ (n : ℕ)) from
    Subtype.coe_injective)

/-- Helper for Example 16 22: once a coordinate square is at most `1 / 4`, its weighted even-power
term is controlled by the geometric comparison sequence. -/
private theorem positiveNatWeightedEvenPower_term_le_geometric_of_sq_le_quarter
    {x : L2pos} {n : ℕ+} (hsmall : ‖x n‖ ^ (2 : ℕ) ≤ (1 / 4 : ℝ)) :
    ((n : ℝ) * (x n) ^ (2 * (n : ℕ)) : ℝ) ≤ (n : ℝ) * (1 / 4 : ℝ) ^ (n : ℕ) := by
  -- Rewrite the even power through the squared norm so the hypothesis can be iterated `n` times.
  have hxpow_eq : (x n) ^ (2 * (n : ℕ)) = ‖x n‖ ^ (2 * (n : ℕ)) := by
    rw [pow_mul, pow_mul, Real.norm_eq_abs]
    congr 1
    exact (sq_abs (x n)).symm
  have hsq_nonneg : 0 ≤ ‖x n‖ ^ (2 : ℕ) := by
    positivity
  have hpow : ‖x n‖ ^ (2 * (n : ℕ)) ≤ (1 / 4 : ℝ) ^ (n : ℕ) := by
    simpa [pow_mul] using pow_le_pow_left₀ hsq_nonneg hsmall (n : ℕ)
  calc
    (n : ℝ) * (x n) ^ (2 * (n : ℕ)) = (n : ℝ) * ‖x n‖ ^ (2 * (n : ℕ)) := by
      rw [hxpow_eq]
    _ ≤ (n : ℝ) * (1 / 4 : ℝ) ^ (n : ℕ) := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)

-- Proof sketch: apply Example 9.13 to the coordinate family `t ↦ n * t^(2n)`. Each coordinate
-- function is finite everywhere, lower semicontinuous, convex, vanishes at `0`, and is minimized
-- at `0` because the exponent `2n` is even.
/-- The weighted even-power series from Example 16.22 belongs to `Γ₀(ℓ²(ℕ+, ℝ))`. -/
theorem positiveNatWeightedEvenPowerSeries_mem_gammaZero :
    positiveNatWeightedEvenPowerSeries ∈ Γ₀(L2pos) := by
  simpa [positiveNatWeightedEvenPowerSeries] using
    innerProductSeriesFunction_mem_gammaZero
      (fun n ↦ lp.single 2 n (1 : ℝ))
      (fun n ↦ (positiveNatWeightedEvenPowerCoordinate n).toEReal)
      (fun n ↦ positiveNatWeightedEvenPowerCoordinate_mem_gammaZero n)
      positiveNatWeightedEvenPowerCoordinate_toEReal_zero
      positiveNatWeightedEvenPowerCoordinate_toEReal_nonneg

-- Proof sketch: for `x ∈ ℓ²(ℕ+, ℝ)`, the coordinates satisfy `x n → 0`. Since `n^(1 / n) → 1`,
-- eventually `x n ^ 2 ≤ 1 / (n^(3 / n))`, hence `n * x n^(2n) ≤ 1 / n^2`. Comparison with the
-- convergent `p`-series shows that every value is finite.
/-- The effective domain of the Example 16.22 series is all of `ℓ²(ℕ+, ℝ)`. -/
theorem positiveNatWeightedEvenPowerSeries_effectiveDomain_eq_univ :
    effectiveDomain positiveNatWeightedEvenPowerSeries = Set.univ := by
  ext x
  constructor
  · intro hx
    simp
  · intro hx
    let term : ℕ+ → ℝ := fun n ↦ (n : ℝ) * (x n) ^ (2 * (n : ℕ))
    let majorant : ℕ+ → ℝ := fun n ↦ (n : ℝ) * (1 / 4 : ℝ) ^ (n : ℕ)
    have hsquare_summable : Summable (fun n : ℕ+ ↦ ‖x n‖ ^ (2 : ℕ)) := by
      -- The `ℓ²` hypothesis is exactly the square-summability of the coordinate norms.
      simpa [pow_two] using
        (Memℓp.summable (f := (x : ℕ+ → ℝ)) (p := (2 : ENNReal)) (by norm_num) x.property)
    have hsmall_cofinite :
        {n : ℕ+ | ‖x n‖ ^ (2 : ℕ) ≤ (1 / 4 : ℝ)} ∈ Filter.cofinite := by
      have hzero := hsquare_summable.tendsto_cofinite_zero
      have hquarter :
          ∀ᶠ n : ℕ+ in Filter.cofinite, ‖x n‖ ^ (2 : ℕ) < (1 / 4 : ℝ) :=
        hzero.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
      -- Outside a finite set, every coordinate square is at most `1 / 4`.
      filter_upwards [hquarter] with n hn
      exact le_of_lt hn
    let K : Finset ℕ+ := (Filter.mem_cofinite.mp hsmall_cofinite).toFinset
    let C : ℝ := Finset.sum K term + ∑' n : ℕ+, majorant n
    have hnat : ¬ Finite ℕ+ := by
      intro hfinite
      exact hfinite.false
    rw [mem_effectiveDomain_iff, positiveNatWeightedEvenPowerSeries_apply,
      familySum_eq_iSup_nonemptyFinitePartialSums _ hnat]
    have hbound :
        (⨆ J : {s : Finset ℕ+ // s.Nonempty},
          Finset.sum (J : Finset ℕ+)
            (fun n ↦ ((term n : ℝ) : EReal))) ≤
          (C : EReal) := by
      refine iSup_le fun J ↦ ?_
      have hhead :
          Finset.sum ((J : Finset ℕ+).filter fun n ↦ n ∈ K) term ≤ Finset.sum K term := by
        -- The exceptional head is bounded by the full sum over the finite bad set `K`.
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun n hn ↦ (Finset.mem_filter.mp hn).2)
          (fun n hnK hnnot => by
            simpa [term] using positiveNatWeightedEvenPowerCoordinate_nonneg n (x n))
      have htail_terms :
          ∀ n ∈ (J : Finset ℕ+).filter fun n ↦ n ∉ K, term n ≤ majorant n := by
        intro n hn
        have hnK : n ∉ K := (Finset.mem_filter.mp hn).2
        have hsmall_n : ‖x n‖ ^ (2 : ℕ) ≤ (1 / 4 : ℝ) := by
          by_contra hbad
          have hn_bad : n ∈ K := by
            simpa [K, Set.mem_setOf_eq] using hbad
          exact hnK hn_bad
        simpa [term, majorant] using
          positiveNatWeightedEvenPower_term_le_geometric_of_sq_le_quarter (x := x) (n := n)
            hsmall_n
      have htail_sum_le :
          Finset.sum ((J : Finset ℕ+).filter fun n ↦ n ∉ K) term ≤
            Finset.sum ((J : Finset ℕ+).filter fun n ↦ n ∉ K) majorant := by
        -- On the tail, every term is dominated by the geometric majorant.
        exact Finset.sum_le_sum fun n hn ↦ htail_terms n hn
      have htail :
          Finset.sum ((J : Finset ℕ+).filter fun n ↦ n ∉ K) term ≤ ∑' n : ℕ+, majorant n := by
        exact le_trans htail_sum_le <|
          positiveNat_geometricComparison_summable.sum_le_tsum _
            (fun n hn ↦ by positivity)
      have hpartial_real :
          Finset.sum (J : Finset ℕ+) term ≤ C := by
        -- Split the partial sum into the bad head and the good tail, and bound each part
        -- separately.
        calc
          Finset.sum (J : Finset ℕ+) term =
              Finset.sum ((J : Finset ℕ+).filter fun n ↦ n ∈ K) term +
                Finset.sum ((J : Finset ℕ+).filter fun n ↦ n ∉ K) term := by
                  simpa using
                    (Finset.sum_filter_add_sum_filter_not
                      (s := (J : Finset ℕ+)) (p := fun n ↦ n ∈ K) (f := term)).symm
          _ ≤ Finset.sum K term + ∑' n : ℕ+, majorant n := by
            exact add_le_add hhead htail
          _ = C := by
            rfl
      have hpartial_cast :
          (((Finset.sum (J : Finset ℕ+) term : ℝ)) : EReal) ≤ (C : EReal) := by
        exact_mod_cast hpartial_real
      -- Every nonempty finite partial sum is therefore bounded by the same finite real constant.
      rw [positiveNatWeightedEvenPowerSeries_partialSum_eq_coe_real]
      exact hpartial_cast
    exact lt_of_le_of_lt hbound (EReal.coe_lt_top C)

-- Proof sketch: membership in `Γ₀(ℓ²(ℕ+, ℝ))` gives lower semicontinuity and convexity on the
-- effective domain. Since the previous theorem identifies that domain with `univ`, Corollary 8.39
-- yields continuity of the finite real representative at every point.
/-- The real-valued representative of the Example 16.22 series is continuous on all of
`ℓ²(ℕ+, ℝ)`. -/
theorem positiveNatWeightedEvenPowerSeries_continuous :
    Continuous fun x : L2pos ↦ ((positiveNatWeightedEvenPowerSeries x : EReal).toReal) := by
  let contPts : Set L2pos :=
    {x | ∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball x ρ ⊆ effectiveDomain positiveNatWeightedEvenPowerSeries ∧
      ContinuousAt (fun y : L2pos ↦ ((positiveNatWeightedEvenPowerSeries y : EReal).toReal)) x}
  have hcont_eq :
      contPts = interior (effectiveDomain positiveNatWeightedEvenPowerSeries) := by
    -- Corollary 8.39 applies because the series is in `Γ₀(L2pos)`, hence lower semicontinuous.
    simpa [contPts] using
      continuous_points_eq_interior_effectiveDomain_of_lowerSemicontinuous
        positiveNatWeightedEvenPowerSeries positiveNatWeightedEvenPowerSeries_mem_gammaZero
  rw [continuous_iff_continuousAt]
  intro x
  have hx_cont : x ∈ contPts := by
    rw [hcont_eq, positiveNatWeightedEvenPowerSeries_effectiveDomain_eq_univ]
    simp
  rcases hx_cont with ⟨ρ, hρ, hball, hcont⟩
  exact hcont

-- Proof sketch: by the domain theorem, every point lies in `effectiveDomain
-- positiveNatWeightedEvenPowerSeries`. The continuity theorem above gives continuity on the
-- effective domain, so Proposition 16.17(ii) yields a nonempty subdifferential at each point.
/-- The Example 16.22 series is subdifferentiable at every point of `ℓ²(ℕ+, ℝ)`. -/
theorem positiveNatWeightedEvenPowerSeries_subdifferentiableAt (x : L2pos) :
    SubdifferentiableAt positiveNatWeightedEvenPowerSeries x := by
  have hxcont : ContinuousPoint positiveNatWeightedEvenPowerSeries x := by
    refine ⟨1, by norm_num, ?_, ?_⟩
    · rw [positiveNatWeightedEvenPowerSeries_effectiveDomain_eq_univ]
      simp
    · simpa using positiveNatWeightedEvenPowerSeries_continuous.continuousAt
  have hsub_nonempty :
      ((∂ positiveNatWeightedEvenPowerSeries) x).Nonempty :=
    (subdifferential_nonempty_and_weaklyCompact_of_continuousPoint
      positiveNatWeightedEvenPowerSeries positiveNatWeightedEvenPowerSeries_mem_gammaZero.2
      hxcont).1
  simpa [subdifferentiableAt_iff_mem_dom, SetValuedOperator.mem_dom_iff] using hsub_nonempty

/-- Helper for Example 16 22: on the `n`th standard unit vector, the `i`th summand is `n` when
`i = n` and `0` otherwise. -/
private theorem positiveNatWeightedEvenPowerSeries_term_basisVector
    (n i : ℕ+) :
    (((i : ℝ) * ((lp.single 2 n (1 : ℝ) : L2pos) i) ^ (2 * (i : ℕ)) : ℝ) : EReal) =
      if i = n then ((n : ℝ) : EReal) else 0 := by
  by_cases hi : i = n
  · subst hi
    simp [lp.single_apply]
  · simp [lp.single_apply, hi]

-- Proof sketch: the standard basis vector `eₙ` has exactly one nonzero coordinate, equal to `1`
-- at index `n`. Hence every off-diagonal term in the family sum vanishes and the remaining term is
-- `n * 1^(2n) = n`.
/-- The Example 16.22 series takes the value `n` on the `n`th standard unit vector. -/
theorem positiveNatWeightedEvenPowerSeries_apply_basisVector (n : ℕ+) :
    (positiveNatWeightedEvenPowerSeries (lp.single 2 n (1 : ℝ)) : EReal) = ((n : ℝ) : EReal) := by
  classical
  let A : EReal := ((n : ℝ) : EReal)
  have hnat : ¬ Finite ℕ+ := by
    intro hfinite
    exact hfinite.false
  have hnonneg :
      ∀ i : ℕ+, (0 : EReal) ≤
        (((i : ℝ) * ((lp.single 2 n (1 : ℝ) : L2pos) i) ^ (2 * (i : ℕ)) : ℝ) : EReal) := by
    intro (i : ℕ+)
    exact_mod_cast
      positiveNatWeightedEvenPowerCoordinate_nonneg i
        ((lp.single 2 n (1 : ℝ) : L2pos) i)
  rw [positiveNatWeightedEvenPowerSeries_apply, familySum_eq_iSup_nonemptyFinitePartialSums _ hnat]
  change
    (⨆ J : {s : Finset ℕ+ // s.Nonempty},
      Finset.sum (J : Finset ℕ+)
        (fun i ↦ (((i : ℝ) * ((lp.single 2 n (1 : ℝ) : L2pos) i) ^ (2 * (i : ℕ)) : ℝ) : EReal))) =
      A
  rw [familySum_eq_iSup_nonemptyFinitePartialSums_containing
    (g := fun i ↦
      (((i : ℝ) * ((lp.single 2 n (1 : ℝ) : L2pos) i) ^ (2 * (i : ℕ)) : ℝ) : EReal))
    hnonneg n]
  have hpartial :
      ∀ J : {s : Finset ℕ+ // s.Nonempty ∧ n ∈ s},
        Finset.sum (J : Finset ℕ+)
          (fun i ↦
            (((i : ℝ) * ((lp.single 2 n (1 : ℝ) : L2pos) i) ^ (2 * (i : ℕ)) : ℝ) : EReal)) =
          A := by
    intro J
    -- Once `n ∈ J`, the finite partial sum has exactly one surviving coordinate.
    calc
      Finset.sum (J : Finset ℕ+)
          (fun i ↦
            (((i : ℝ) * ((lp.single 2 n (1 : ℝ) : L2pos) i) ^ (2 * (i : ℕ)) : ℝ) : EReal)) =
        Finset.sum (J : Finset ℕ+) (fun i ↦ if i = n then A else 0) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa [A] using positiveNatWeightedEvenPowerSeries_term_basisVector n i
      _ = A := by
        simp [A, J.2.2]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun J ↦ ?_
    rw [hpartial J]
  · let J₀ : {s : Finset ℕ+ // s.Nonempty ∧ n ∈ s} := ⟨{n}, by simp⟩
    have hJ₀ :
        Finset.sum (J₀ : Finset ℕ+)
          (fun i ↦
            (((i : ℝ) * ((lp.single 2 n (1 : ℝ) : L2pos) i) ^ (2 * (i : ℕ)) : ℝ) : EReal)) ≤
          ⨆ J : {s : Finset ℕ+ // s.Nonempty ∧ n ∈ s},
            Finset.sum (J : Finset ℕ+)
              (fun i ↦
                (((i : ℝ) * ((lp.single 2 n (1 : ℝ) : L2pos) i) ^ (2 * (i : ℕ)) : ℝ) : EReal)) :=
      le_iSup
        (fun J : {s : Finset ℕ+ // s.Nonempty ∧ n ∈ s} ↦
          Finset.sum (J : Finset ℕ+)
            (fun i ↦
              (((i : ℝ) * ((lp.single 2 n (1 : ℝ) : L2pos) i) ^ (2 * (i : ℕ)) : ℝ) : EReal)))
        J₀
    rwa [hpartial J₀] at hJ₀

/-- Helper for Example 16 22: once the series is finite everywhere, re-lifting its finite
representative through `toEReal` recovers the original `]-∞,+∞]`-valued function. -/
private theorem positiveNatWeightedEvenPowerSeries_toEReal_toReal :
    (fun x : L2pos ↦ ((positiveNatWeightedEvenPowerSeries x : EReal).toReal)).toEReal =
      positiveNatWeightedEvenPowerSeries := by
  funext x
  apply Subtype.ext
  simp [Function.toEReal_apply]
  have hx : x ∈ effectiveDomain positiveNatWeightedEvenPowerSeries := by
    rw [positiveNatWeightedEvenPowerSeries_effectiveDomain_eq_univ]
    simp
  have htop : (positiveNatWeightedEvenPowerSeries x : EReal) ≠ ⊤ := by
    exact ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hbot : (positiveNatWeightedEvenPowerSeries x : EReal) ≠ ⊥ := by
    exact ne_of_gt (positiveNatWeightedEvenPowerSeries x).2
  simpa using (EReal.coe_toReal htop hbot)

/-- Helper for Example 16 22: the full series dominates each individual weighted coordinate term. -/
private theorem positiveNatWeightedEvenPowerSeries_ge_coordinate_term
    (x : L2pos) (n : ℕ+) :
    ((((n : ℝ) * (x n) ^ (2 * (n : ℕ)) : ℝ) : EReal)) ≤
      positiveNatWeightedEvenPowerSeries x := by
  have hnat : ¬ Finite ℕ+ := by
    intro hfinite
    exact hfinite.false
  rw [positiveNatWeightedEvenPowerSeries_apply, familySum_eq_iSup_nonemptyFinitePartialSums _ hnat]
  let J₀ : {s : Finset ℕ+ // s.Nonempty} := ⟨{n}, by simp⟩
  have hJ₀ :
      Finset.sum (J₀ : Finset ℕ+)
        (fun i ↦ (((i : ℝ) * (x i) ^ (2 * (i : ℕ)) : ℝ) : EReal)) ≤
        ⨆ J : {s : Finset ℕ+ // s.Nonempty},
          Finset.sum (J : Finset ℕ+)
            (fun i ↦ (((i : ℝ) * (x i) ^ (2 * (i : ℕ)) : ℝ) : EReal)) :=
    le_iSup
      (fun J : {s : Finset ℕ+ // s.Nonempty} ↦
        Finset.sum (J : Finset ℕ+)
          (fun i ↦ (((i : ℝ) * (x i) ^ (2 * (i : ℕ)) : ℝ) : EReal)))
      J₀
  simpa [J₀] using hJ₀

/-- Helper for Example 16 22: the scaled basis vector `n • eₙ` has norm `n`. -/
private theorem positiveNatWeightedEvenPowerSeries_scaled_basis_norm (n : ℕ+) :
    ‖(n : ℝ) • (lp.single 2 n (1 : ℝ) : L2pos)‖ = (n : ℝ) := by
  -- The `ℓ²` norm of the standard unit vector is `1`, so scaling by `n` gives norm `n`.
  calc
    ‖(n : ℝ) • (lp.single 2 n (1 : ℝ) : L2pos)‖ =
        |(n : ℝ)| * ‖(lp.single 2 n (1 : ℝ) : L2pos)‖ := norm_smul _ _
    _ = |(n : ℝ)| * ‖(1 : ℝ)‖ := by
      rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
    _ = (n : ℝ) := by
      have habs : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (by positivity)
      simp [habs]

/-- Helper for Example 16 22: along the scaled basis direction `n • eₙ`, the Fenchel conjugate is
bounded above by `n`. -/
private theorem positiveNatWeightedEvenPowerSeries_conjugate_le_scaled_basis
    (n : ℕ+) :
    positiveNatWeightedEvenPowerSeries.asEReal∗ ((n : ℝ) • (lp.single 2 n (1 : ℝ) : L2pos)) ≤
      (n : ℝ) := by
  rw [conjugate_apply]
  refine iSup_le fun x ↦ ?_
  have hdom : x ∈ effectiveDomain positiveNatWeightedEvenPowerSeries := by
    rw [positiveNatWeightedEvenPowerSeries_effectiveDomain_eq_univ]
    simp
  have htop : (positiveNatWeightedEvenPowerSeries x : EReal) ≠ ⊤ := by
    exact ne_of_lt (mem_effectiveDomain_iff.mp hdom)
  have hbot : (positiveNatWeightedEvenPowerSeries x : EReal) ≠ ⊥ := by
    exact ne_of_gt (positiveNatWeightedEvenPowerSeries x).2
  have hfx :
      (positiveNatWeightedEvenPowerSeries x : EReal) =
        (((positiveNatWeightedEvenPowerSeries x : EReal).toReal : ℝ) : EReal) := by
    symm
    exact EReal.coe_toReal htop hbot
  have hcoord_real :
      ((n : ℝ) * (x n) ^ (2 * (n : ℕ)) : ℝ) ≤
        (positiveNatWeightedEvenPowerSeries x : EReal).toReal := by
    have hcoord := positiveNatWeightedEvenPowerSeries_ge_coordinate_term x n
    rw [hfx] at hcoord
    exact_mod_cast hcoord
  have hinner :
      inner ℝ x ((n : ℝ) • (lp.single 2 n (1 : ℝ) : L2pos)) = (n : ℝ) * x n := by
    have hsingle : inner ℝ x (lp.single 2 n (1 : ℝ) : L2pos) = x n := by
      rw [lp.inner_single_right]
      change (1 : ℝ) * star (x n) = x n
      simp
    calc
      inner ℝ x ((n : ℝ) • (lp.single 2 n (1 : ℝ) : L2pos)) =
          (n : ℝ) * inner ℝ x (lp.single 2 n (1 : ℝ) : L2pos) := by
            simpa using
              real_inner_smul_right x (lp.single 2 n (1 : ℝ) : L2pos) (n : ℝ)
      _ = (n : ℝ) * x n := by
            rw [hsingle]
  have hreal :
      (n : ℝ) * x n - (positiveNatWeightedEvenPowerSeries x : EReal).toReal ≤ (n : ℝ) := by
    have hsub :
        (n : ℝ) * x n - (positiveNatWeightedEvenPowerSeries x : EReal).toReal ≤
          (n : ℝ) * x n - ((n : ℝ) * (x n) ^ (2 * (n : ℕ)) : ℝ) := by
      linarith
    have hmain :
        (n : ℝ) * x n - ((n : ℝ) * (x n) ^ (2 * (n : ℕ)) : ℝ) ≤ (n : ℝ) := by
      -- The one-variable scalar estimate from the source proof controls the defect by `1`.
      have hone : x n - (x n) ^ (2 * (n : ℕ)) ≤ 1 := sub_even_power_le_one n (x n)
      nlinarith
    exact le_trans hsub hmain
  have hcast :
      ((((n : ℝ) * x n - (positiveNatWeightedEvenPowerSeries x : EReal).toReal : ℝ) : EReal)) ≤
        (n : ℝ) := by
    exact_mod_cast hreal
  -- Rewrite the affine defect through the finite real representative of the series.
  rw [hinner]
  change (((n : ℝ) * x n : ℝ) : EReal) - (positiveNatWeightedEvenPowerSeries x : EReal) ≤
    (n : ℝ)
  rw [hfx]
  simpa [EReal.coe_sub] using hcast

-- Proof sketch: the helper theorems above identify the series as an everywhere finite continuous
-- convex function on `ℓ²(ℕ+, ℝ)`. The basis-vector formula gives `f(eₙ) = n`, so `f` is unbounded
-- on the bounded set of standard unit vectors. Proposition 16.20 therefore rules out
-- supercoercivity of the Fenchel conjugate.
/-- Example 16 22: for the series `f(ξ) = ∑ₙ n * ξₙ^(2n)` on `ℓ²(ℕ+, ℝ)`, the Fenchel conjugate
`f*` is not supercoercive. -/
theorem positiveNatWeightedEvenPowerSeries_conjugate_not_supercoercive :
    ¬ Supercoercive positiveNatWeightedEvenPowerSeries.asEReal∗ := by
  intro hsuper
  rw [supercoercive_iff_tendsto_norm_atTop, EReal.tendsto_nhds_top_iff_real] at hsuper
  rcases Filter.mem_comap.1 (hsuper 1) with ⟨s, hs, hs_subset⟩
  rcases Filter.mem_atTop_sets.1 hs with ⟨R, hR⟩
  let n₀ : ℕ+ := ⟨Nat.ceil R + 1, Nat.succ_pos _⟩
  let u : L2pos := (n₀ : ℝ) • (lp.single 2 n₀ (1 : ℝ) : L2pos)
  have hunorm : ‖u‖ = (n₀ : ℝ) := by
    simpa [u] using positiveNatWeightedEvenPowerSeries_scaled_basis_norm n₀
  have hRnorm : R ≤ ‖u‖ := by
    rw [hunorm]
    change R ≤ ((Nat.ceil R + 1 : ℕ) : ℝ)
    have hceil : R ≤ (Nat.ceil R : ℝ) := Nat.le_ceil R
    have hsucc : (Nat.ceil R : ℝ) ≤ ((Nat.ceil R + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ (Nat.ceil R)
    exact le_trans hceil hsucc
  have hu_preimage : u ∈ (fun x : L2pos ↦ ‖x‖) ⁻¹' s := by
    simpa [u] using hR _ hRnorm
  have hlt : (1 : EReal) < positiveNatWeightedEvenPowerSeries.asEReal∗ u / ‖u‖ := by
    exact hs_subset hu_preimage
  have hratio_le : positiveNatWeightedEvenPowerSeries.asEReal∗ u / ‖u‖ ≤ (1 : EReal) := by
    rw [hunorm]
    have hnpos : (0 : EReal) < (n₀ : ℝ) := by
      exact_mod_cast n₀.2
    exact (EReal.div_le_iff_le_mul hnpos (EReal.coe_ne_top _)).2 <| by
      simpa [u] using positiveNatWeightedEvenPowerSeries_conjugate_le_scaled_basis n₀
  exact not_lt_of_ge hratio_le hlt

end ERealFunction

end
