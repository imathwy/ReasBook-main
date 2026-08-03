module

public import Topology_Munkres_2000.Book.Exercise_21_6.PowerSequence
public import Topology_Munkres_2000.Book.Exercise_21_9.MovingSpike
public import Topology_Munkres_2000.Book.Definition_45_2
public import Topology_Munkres_2000.Book.Definition_45_3.PointwiseBounded

public section

universe u v

/-- Helper for Exercise 45.4: a uniformly convergent strict subsequence has the same
pointwise limit as the original sequence. -/
private lemma eq_pointwiseLimit_of_strictMono_tendstoUniformly
    {X : Type u} {Y : Type v} [UniformSpace Y] [T2Space Y]
    {F : ℕ → X → Y} {f g : X → Y} {φ : ℕ → ℕ}
    (hpoint : ∀ x, Filter.Tendsto (fun n ↦ F n x) Filter.atTop (nhds (f x)))
    (hφ : StrictMono φ)
    (huniform : TendstoUniformly (fun n ↦ F (φ n)) g Filter.atTop) :
    g = f := by
  funext x
  -- The strict index map tends to infinity, so both pointwise limits can be compared.
  exact tendsto_nhds_unique (huniform.tendsto_at x) ((hpoint x).comp hφ.tendsto_atTop)

/-- Helper for Exercise 45.4: local uniform convergence of continuous members makes a
sequence equicontinuous at the base point. -/
private lemma equicontinuousAt_of_tendstoUniformlyOnFilter
    {X : Type u} {Y : Type v} [TopologicalSpace X] [PseudoMetricSpace Y]
    {F : ℕ → X → Y} {f : X → Y} {x : X}
    (hcontinuous : ∀ n, ContinuousAt (F n) x)
    (huniform : TendstoUniformlyOnFilter F f Filter.atTop (nhds x)) :
    EquicontinuousAt F x := by
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hεfive : 0 < ε / 5 := by
    positivity
  have htail := (Metric.tendstoUniformlyOnFilter_iff.mp huniform) (ε / 5) hεfive
  obtain ⟨pa, hpa, pb, hpb, htail⟩ := Filter.eventually_prod_iff.mp htail
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hpa
  have hhead : EquicontinuousAt (fun i : Fin N ↦ F i) x := by
    -- The finitely many initial functions have a common continuity neighborhood.
    rw [equicontinuousAt_finite]
    intro i
    exact hcontinuous i
  have hheadε := (Metric.equicontinuousAt_iff_right.mp hhead) ε hε
  have hrefε : ∀ᶠ y in nhds x, dist (F N x) (F N y) < ε / 5 := by
    have href := (hcontinuous N) (Metric.ball_mem_nhds (F N x) hεfive)
    filter_upwards [href] with y hy
    change dist (F N y) (F N x) < ε / 5 at hy
    rwa [dist_comm] at hy
  have hpbx : pb x := mem_of_mem_nhds hpb
  filter_upwards [hpb, hheadε, hrefε] with y hy hheady hrefy
  intro n
  by_cases hn : n < N
  · -- Initial indices are controlled by finite equicontinuity.
    exact hheady ⟨n, hn⟩
  · -- Tail indices are compared through the uniformly close reference member `F N`.
    have htailNx : dist (f x) (F N x) < ε / 5 := htail (hN N le_rfl) hpbx
    have htailNy : dist (f y) (F N y) < ε / 5 := htail (hN N le_rfl) hy
    have htailnx : dist (f x) (F n x) < ε / 5 :=
      htail (hN n (Nat.le_of_not_gt hn)) hpbx
    have htailny : dist (f y) (F n y) < ε / 5 :=
      htail (hN n (Nat.le_of_not_gt hn)) hy
    have htriangle : dist (F n x) (F n y) ≤
        dist (F n x) (f x) + dist (f x) (F N x) + dist (F N x) (F N y) +
          dist (F N y) (f y) + dist (f y) (F n y) := by
      have hlong := dist_triangle8 (F n x) (f x) (F N x) (F N y)
        (f y) (F n y) (F n y) (F n y)
      simpa only [dist_self, add_zero] using hlong
    calc
      dist (F n x) (F n y) ≤
          dist (F n x) (f x) + dist (f x) (F N x) + dist (F N x) (F N y) +
            dist (F N y) (f y) + dist (f y) (F n y) := htriangle
      _ < ε := by
        rw [dist_comm (F n x), dist_comm (F N y)]
        linarith

namespace UnitIntervalPower

/-- Helper for Exercise 45.4: the power sequence converges locally uniformly to zero away
from the right endpoint. -/
private lemma tendstoUniformlyOnFilter_zero_of_ne_one
    (x : Set.Icc (0 : ℝ) 1) (hx : x ≠ 1) :
    TendstoUniformlyOnFilter sequence (fun _ ↦ 0) Filter.atTop (nhds x) := by
  have hxreal : (x : ℝ) ≠ 1 := by
    intro h
    apply hx
    exact Subtype.ext h
  have hxlt : (x : ℝ) < 1 := lt_of_le_of_ne x.property.2 hxreal
  let r : ℝ := ((x : ℝ) + 1) / 2
  have hrnonneg : 0 ≤ r := by
    dsimp [r]
    linarith [x.property.1]
  have hx_lt_r : (x : ℝ) < r := by
    dsimp [r]
    linarith
  have hrlt : r < 1 := by
    dsimp [r]
    linarith
  have hpow : Filter.Tendsto (fun n : ℕ ↦ r ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hrnonneg hrlt
  rw [Metric.tendstoUniformlyOnFilter_iff]
  intro ε hε
  have hn : ∀ᶠ n in Filter.atTop, r ^ n < ε := hpow (Iio_mem_nhds hε)
  have hy : ∀ᶠ y : Set.Icc (0 : ℝ) 1 in nhds x, (y : ℝ) < r :=
    continuousAt_subtype_val.eventually (Iio_mem_nhds hx_lt_r)
  -- On this product neighborhood every base is bounded by the same `r < 1`.
  filter_upwards [hn.prod_mk hy] with z hz
  have hpowle : (z.2 : ℝ) ^ z.1 ≤ r ^ z.1 :=
    pow_le_pow_left₀ z.2.property.1 hz.2.le z.1
  simpa only [sequence_apply, Pi.zero_apply, dist_zero_left, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg z.2.property.1 z.1)] using hpowle.trans_lt hz.1

/-- Helper for Exercise 45.4: the pointwise power limit is discontinuous at the right
endpoint. -/
private lemma not_continuousAt_limit_one :
    ¬ ContinuousAt limit (1 : Set.Icc (0 : ℝ) 1) := by
  intro hcontinuous
  have hshift : Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hinv : Filter.Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ))⁻¹)
      Filter.atTop (nhds 0) := by
    exact hshift.inv_tendsto_atTop.congr'
      (Filter.Eventually.of_forall fun _ ↦ rfl)
  let realPoints : ℕ → ℝ := fun n ↦ 1 - (((n + 1 : ℕ) : ℝ))⁻¹
  have happReal : Filter.Tendsto realPoints Filter.atTop (nhds 1) := by
    -- The correction term `1 / (n+1)` tends to zero.
    simpa only [realPoints, sub_zero] using tendsto_const_nhds.sub hinv
  have hmemIcc (n : ℕ) : realPoints n ∈ Set.Icc (0 : ℝ) 1 := by
    have hden : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hinvPos : 0 < (((n + 1 : ℕ) : ℝ))⁻¹ := by
      positivity
    have hinvLe : (((n + 1 : ℕ) : ℝ))⁻¹ ≤ 1 := by
      have hdenPos : 0 < ((n + 1 : ℕ) : ℝ) := by
        positivity
      exact (inv_le_one₀ hdenPos).2 hden
    dsimp [realPoints]
    constructor
    · linarith
    · linarith
  let points : ℕ → Set.Icc (0 : ℝ) 1 := fun n ↦ ⟨realPoints n, hmemIcc n⟩
  have happ : Filter.Tendsto points Filter.atTop (nhds (1 : Set.Icc (0 : ℝ) 1)) := by
    rw [tendsto_subtype_rng]
    exact happReal
  have hlimit := hcontinuous.tendsto.comp happ
  have hzero : Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds
  have heq : limit ∘ points = fun _ : ℕ ↦ (0 : ℝ) := by
    funext n
    have hinvPos : 0 < (((n + 1 : ℕ) : ℝ))⁻¹ := by
      positivity
    have hne : (points n : ℝ) ≠ 1 := by
      dsimp [points, realPoints]
      linarith
    simp only [Function.comp_apply, limit_apply, if_neg hne]
  rw [heq] at hlimit
  -- Continuity would make the constant-zero values converge to the endpoint value one.
  have hone : limit (1 : Set.Icc (0 : ℝ) 1) = 1 := by
    simp
  rw [hone] at hlimit
  exact zero_ne_one (tendsto_nhds_unique hzero hlimit)

/-- Exercise 45.4 (1): The power functions on the closed unit interval are pointwise bounded. -/
theorem pointwiseBounded : PointwiseBounded sequence := by
  rw [_root_.pointwiseBounded_iff]
  intro x
  -- Every power of a point in `[0,1]` remains in the same bounded interval.
  refine (Metric.isBounded_Icc (0 : ℝ) 1).subset ?_
  rintro y ⟨n, rfl⟩
  exact ⟨pow_nonneg x.property.1 n, pow_le_one₀ x.property.1 x.property.2⟩

/-- Companion for Exercise 45.4 (2): The power sequence on the closed unit interval has no uniformly
convergent subsequence. -/
theorem noUniformlyConvergentSubsequence :
    ¬ ∃ (φ : ℕ → ℕ) (g : Set.Icc (0 : ℝ) 1 → ℝ),
      StrictMono φ ∧ TendstoUniformly (fun n ↦ sequence (φ n)) g Filter.atTop := by
  rintro ⟨φ, g, hφ, huniform⟩
  -- Pointwise uniqueness identifies the alleged subsequential limit with `limit`.
  have hgeq : g = limit :=
    eq_pointwiseLimit_of_strictMono_tendstoUniformly limit_at hφ huniform
  rw [hgeq] at huniform
  have hquarter : (0 : ℝ) < 1 / 4 := by
    norm_num
  have heventually := (Metric.tendstoUniformly_iff.mp huniform) (1 / 4) hquarter
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp heventually
  have hmemIco := approachOnePoint_mem_Ico (φ N)
  have hmemIcc : approachOnePoint (φ N) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hmemIco.1, hmemIco.2.le⟩
  let x : Set.Icc (0 : ℝ) 1 := ⟨approachOnePoint (φ N), hmemIcc⟩
  have hdist := hN N le_rfl x
  have hxne : (x : ℝ) ≠ 1 := ne_of_lt hmemIco.2
  have hdistEq : dist (limit x) (sequence (φ N) x) =
      approachOnePoint (φ N) ^ φ N := by
    simp [limit_apply, sequence_apply, hxne, x, Real.dist_eq,
      abs_of_nonneg (pow_nonneg hmemIco.1 (φ N))]
  rw [hdistEq] at hdist
  -- The matching near-endpoint witness stays at least `1/2`, contradicting `1/4`.
  linarith [half_le_approachOnePoint_pow (φ N)]

/-- Companion for Exercise 45.4 (3): The power functions are equicontinuous at exactly the points of
the closed unit interval other than `1`. -/
theorem equicontinuousAt_iff (x : Set.Icc (0 : ℝ) 1) :
    EquicontinuousAt sequence x ↔ x ≠ 1 := by
  constructor
  · intro hequicontinuous hx
    subst x
    -- Equicontinuity would force the pointwise limit to be continuous at the endpoint.
    exact not_continuousAt_limit_one
      (tendsto_limit.continuousAt_of_equicontinuousAt hequicontinuous)
  · intro hx
    -- Local uniform convergence and continuity of every power control the family away from `1`.
    refine equicontinuousAt_of_tendstoUniformlyOnFilter (fun n ↦ ?_)
      (tendstoUniformlyOnFilter_zero_of_ne_one x hx)
    have hsequence : sequence n = fun y : Set.Icc (0 : ℝ) 1 ↦ (y : ℝ) ^ n := by
      funext y
      exact sequence_apply n y
    rw [hsequence]
    exact
      ((continuous_pow n).comp continuous_subtype_val).continuousAt

end UnitIntervalPower

namespace MovingSpike

/-- Helper for Exercise 45.4: the centers of the moving spikes converge to zero. -/
private lemma center_tendsto_zero :
    Filter.Tendsto (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ)) Filter.atTop (nhds 0) := by
  have hshift : Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hinvEq : (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ))⁻¹ =ᶠ[Filter.atTop]
      fun n ↦ 1 / ((n + 1 : ℕ) : ℝ) := by
    filter_upwards with n
    simp only [one_div, Pi.inv_apply]
  exact hshift.inv_tendsto_atTop.congr' hinvEq

/-- Helper for Exercise 45.4: the moving-spike sequence converges locally uniformly to zero
away from the origin. -/
private lemma tendstoUniformlyOnFilter_zero_of_ne_zero (x : ℝ) (hx : x ≠ 0) :
    TendstoUniformlyOnFilter sequence (fun _ ↦ 0) Filter.atTop (nhds x) := by
  let a : ℝ := dist x 0 / 4
  let c : ℝ := dist x 0 / 2
  have hdistx : 0 < dist x 0 := dist_pos.mpr hx
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hcubic : Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ 3)
      Filter.atTop Filter.atTop := by
    have hshift : Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ))
        Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
    have hthree : (3 : ℕ) ≠ 0 := by
      norm_num
    exact (Filter.tendsto_pow_atTop (α := ℝ) hthree).comp hshift
  have hden : Filter.Tendsto (fun n : ℕ ↦
      ((n + 1 : ℕ) : ℝ) ^ 3 * c ^ 2 + 1) Filter.atTop Filter.atTop := by
    have hproduct : Filter.Tendsto (fun n : ℕ ↦
        ((n + 1 : ℕ) : ℝ) ^ 3 * c ^ 2) Filter.atTop Filter.atTop :=
      hcubic.atTop_mul_pos (sq_pos_of_pos hc) tendsto_const_nhds
    exact Filter.tendsto_atTop_mono
      (fun n ↦ le_add_of_nonneg_right zero_le_one) hproduct
  have hbound : Filter.Tendsto (fun n : ℕ ↦
      1 / (((n + 1 : ℕ) : ℝ) ^ 3 * c ^ 2 + 1)) Filter.atTop (nhds 0) := by
    have hinvEq : (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ 3 * c ^ 2 + 1)⁻¹
        =ᶠ[Filter.atTop] fun n ↦ 1 / (((n + 1 : ℕ) : ℝ) ^ 3 * c ^ 2 + 1) := by
      filter_upwards with n
      simp only [one_div, Pi.inv_apply]
    exact hden.inv_tendsto_atTop.congr' hinvEq
  rw [Metric.tendstoUniformlyOnFilter_iff]
  intro ε hε
  have hnBound : ∀ᶠ n in Filter.atTop,
      1 / (((n + 1 : ℕ) : ℝ) ^ 3 * c ^ 2 + 1) < ε :=
    hbound (Iio_mem_nhds hε)
  have hnCenter : ∀ᶠ n in Filter.atTop,
      dist (1 / ((n + 1 : ℕ) : ℝ)) 0 < a :=
    center_tendsto_zero (Metric.ball_mem_nhds 0 ha)
  have hy : ∀ᶠ y in nhds x, dist y x < a := Metric.ball_mem_nhds x ha
  -- Late centers and nearby arguments stay uniformly separated from one another.
  filter_upwards [(hnBound.and hnCenter).prod_mk hy] with z hz
  have htriangle : dist x 0 ≤ dist x z.2 +
      dist z.2 (1 / ((z.1 + 1 : ℕ) : ℝ)) +
        dist (1 / ((z.1 + 1 : ℕ) : ℝ)) 0 :=
    dist_triangle4 x z.2 (1 / ((z.1 + 1 : ℕ) : ℝ)) 0
  have hseparate : c ≤ dist z.2 (1 / ((z.1 + 1 : ℕ) : ℝ)) := by
    rw [dist_comm x z.2] at htriangle
    dsimp [a, c] at hz htriangle ⊢
    linarith
  have hsquare : c ^ 2 ≤ (z.2 - 1 / ((z.1 + 1 : ℕ) : ℝ)) ^ 2 := by
    rw [sq_le_sq]
    rw [abs_of_pos hc, ← Real.dist_eq]
    exact hseparate
  have hcubicNonneg : 0 ≤ ((z.1 + 1 : ℕ) : ℝ) ^ 3 := by
    positivity
  have hdenle : ((z.1 + 1 : ℕ) : ℝ) ^ 3 * c ^ 2 + 1 ≤
      ((z.1 + 1 : ℕ) : ℝ) ^ 3 *
        (z.2 - 1 / ((z.1 + 1 : ℕ) : ℝ)) ^ 2 + 1 := by
    gcongr
  have hrecip : sequence z.1 z.2 ≤
      1 / (((z.1 + 1 : ℕ) : ℝ) ^ 3 * c ^ 2 + 1) := by
    rw [sequence_apply]
    have hdenPos : 0 < ((z.1 + 1 : ℕ) : ℝ) ^ 3 * c ^ 2 + 1 := by
      positivity
    exact one_div_le_one_div_of_le hdenPos hdenle
  have hsequenceNonneg : 0 ≤ sequence z.1 z.2 := by
    rw [sequence_apply]
    positivity
  simpa only [Pi.zero_apply, dist_zero_left, Real.norm_eq_abs,
    abs_of_nonneg hsequenceNonneg] using
    hrecip.trans_lt hz.1.1

/-- Companion for Exercise 45.4 (4): The moving-spike functions are pointwise bounded. -/
theorem pointwiseBounded : PointwiseBounded sequence := by
  rw [_root_.pointwiseBounded_iff]
  intro x
  -- The denominator is at least one, so every spike value lies in `[0,1]`.
  refine (Metric.isBounded_Icc (0 : ℝ) 1).subset ?_
  rintro y ⟨n, rfl⟩
  simp only [sequence_apply]
  constructor
  · positivity
  · have hden : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 3 *
        (x - 1 / ((n + 1 : ℕ) : ℝ)) ^ 2 + 1 := by
      have hfactor : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ 3 *
          (x - 1 / ((n + 1 : ℕ) : ℝ)) ^ 2 :=
        mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 3) (sq_nonneg _)
      linarith
    simpa only [one_div_one] using one_div_le_one_div_of_le zero_lt_one hden

/-- Companion for Exercise 45.4 (5): The moving-spike sequence has no uniformly convergent
subsequence. -/
theorem noUniformlyConvergentSubsequence :
    ¬ ∃ (φ : ℕ → ℕ) (g : ℝ → ℝ),
      StrictMono φ ∧ TendstoUniformly (fun n ↦ sequence (φ n)) g Filter.atTop := by
  rintro ⟨φ, g, hφ, huniform⟩
  -- Pointwise uniqueness identifies the alleged limit with the zero function.
  have hgeq : g = fun _ : ℝ ↦ 0 :=
    eq_pointwiseLimit_of_strictMono_tendstoUniformly tendsto_at hφ huniform
  rw [hgeq] at huniform
  have hhalf : (0 : ℝ) < 1 / 2 := by
    norm_num
  have heventually := (Metric.tendstoUniformly_iff.mp huniform) (1 / 2) hhalf
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp heventually
  have hcenter := hN N le_rfl (1 / ((φ N + 1 : ℕ) : ℝ))
  -- The matching spike center always has value one, contradicting the uniform estimate.
  rw [sequence_center] at hcenter
  norm_num [Real.dist_eq] at hcenter

/-- Companion for Exercise 45.4 (6): The moving-spike functions are equicontinuous at exactly the
nonzero real points. -/
theorem equicontinuousAt_iff (x : ℝ) :
    EquicontinuousAt sequence x ↔ x ≠ 0 := by
  constructor
  · intro hequicontinuous hx
    subst x
    have hquarter : (0 : ℝ) < 1 / 4 := by
      norm_num
    have hmodulus := (Metric.equicontinuousAt_iff_right.mp hequicontinuous)
      (1 / 4) hquarter
    have hcenters := center_tendsto_zero.eventually hmodulus
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hcenters
    have hdist := hN N le_rfl N
    have hzero : sequence N 0 = 1 / (((N + 1 : ℕ) : ℝ) + 1) := by
      rw [sequence_apply]
      have hne : ((N + 1 : ℕ) : ℝ) ≠ 0 := by
        positivity
      field_simp
      ring
    have hzeroNonneg : 0 ≤ sequence N 0 := by
      rw [hzero]
      positivity
    have hden : (2 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) + 1 := by
      have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      norm_num
      linarith
    have hzeroLe : sequence N 0 ≤ 1 / 2 := by
      rw [hzero]
      have htwo : (0 : ℝ) < 2 := by
        norm_num
      exact one_div_le_one_div_of_le htwo hden
    rw [sequence_center] at hdist
    have hdistLower : (1 / 2 : ℝ) ≤ dist (sequence N 0) 1 := by
      rw [Real.dist_eq, abs_of_nonpos]
      · linarith
      · linarith
    -- At its center the spike is one, while its value at zero is at most one half.
    linarith
  · intro hx
    -- Away from zero, local uniform convergence and continuity give equicontinuity.
    exact equicontinuousAt_of_tendstoUniformlyOnFilter
      (fun n ↦ (continuous n).continuousAt)
      (tendstoUniformlyOnFilter_zero_of_ne_zero x hx)

end MovingSpike
