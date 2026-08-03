import Topology_Munkres_2000.Book.Exercise_49_2
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.Weierstrass

open Set
open scoped Polynomial

namespace UnitIntervalSecant

/-- Helper for Proposition 49.3: polynomial evaluation on the unit interval is Lipschitz. -/
private lemma polynomialEval_lipschitzOn_unitInterval (q : ℝ[X]) :
    ∃ K : NNReal, LipschitzWith K (q.toContinuousMapOn unitInterval) := by
  let K : NNReal := ‖q.derivative.toContinuousMapOn unitInterval‖₊
  refine ⟨K, ?_⟩
  -- Bound the derivative on the compact interval and apply the mean-value estimate.
  have hLip : LipschitzOnWith K (fun x : ℝ ↦ q.eval x) unitInterval := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
    · intro x hx
      exact (q.hasDerivAt x).differentiableAt
    · intro x hx
      simpa [K] using show ‖q.derivative.eval x‖₊ ≤ K from by
        exact_mod_cast ContinuousMap.norm_coe_le_norm
          (q.derivative.toContinuousMapOn unitInterval) ⟨x, hx⟩
    · exact ordConnected_Icc.convex
  -- Restrict the ambient Lipschitz estimate to the unit-interval subtype.
  intro x y
  simpa only [Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply,
    Subtype.edist_eq] using hLip x.property y.property

/-- Helper for Proposition 49.3: continuous maps admit arbitrarily close Lipschitz approximants. -/
private lemma exists_lipschitz_dist_lt (f : C(unitInterval, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : C(unitInterval, ℝ), ∃ K : NNReal, LipschitzWith K p ∧ dist f p < ε := by
  -- Polynomial functions are dense on the compact unit interval.
  have hDense : Dense (polynomialFunctions unitInterval : Set C(unitInterval, ℝ)) := by
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe,
      polynomialFunctions_closure_eq_top]
    rfl
  obtain ⟨p, hp, hdist⟩ := hDense.exists_dist_lt f hε
  -- Expose the approximating polynomial and attach its Lipschitz constant.
  rw [polynomialFunctions_coe] at hp
  obtain ⟨q, rfl⟩ := hp
  obtain ⟨K, hK⟩ := polynomialEval_lipschitzOn_unitInterval q
  exact ⟨q.toContinuousMapOn unitInterval, K, hK, hdist⟩

/-- Helper for Proposition 49.3: a pointwise perturbation bound controls uniform distance. -/
private lemma dist_add_le_of_abs_le (p s : C(unitInterval, ℝ)) {ε : ℝ} (hε : 0 ≤ ε)
    (hs : ∀ x, |s x| ≤ ε) :
    dist p (p + s) ≤ ε := by
  -- Reduce the uniform metric bound to the supplied pointwise amplitude bound.
  rw [ContinuousMap.dist_le hε]
  intro x
  simpa only [ContinuousMap.coe_add, Pi.add_apply, Real.dist_eq, sub_add_cancel_left,
    abs_neg] using hs x

/-- Helper for Proposition 49.3: a Lipschitz map has bounded secant slope. -/
private lemma abs_div_sub_le_of_lipschitz {p : C(unitInterval, ℝ)} {K : NNReal}
    (hp : LipschitzWith K p) {x y : unitInterval} {d : ℝ} (hd : d ≠ 0)
    (hy : (y : ℝ) = x + d) :
    |(p y - p x) / d| ≤ K := by
  -- Translate the Lipschitz distance estimate into the chosen displacement.
  have hdist := hp.dist_le_mul y x
  have hnum : |p y - p x| ≤ (K : ℝ) * |d| := by
    simpa only [Real.dist_eq, Subtype.dist_eq, hy, add_sub_cancel_left] using hdist
  rw [abs_div]
  exact (div_le_iff₀ (abs_pos.mpr hd)).2 hnum

/-- Helper for Proposition 49.3: a dominant summand controls an absolute-value sum. -/
private lemma sub_le_abs_add_of_abs_le_of_le_abs {a b K N : ℝ} (hb : |b| ≤ K)
    (ha : N ≤ |a|) :
    N - K ≤ |a + b| := by
  -- Apply the reverse triangle inequality with the small summand negated.
  have hreverse := abs_sub_abs_le_abs_sub a (-b)
  rw [abs_neg, sub_neg_eq_add] at hreverse
  linarith

/-- Helper for Proposition 49.3: a steep secant remains steep after a Lipschitz perturbation. -/
private lemma sub_le_abs_add_secant_of_lipschitz {p s : C(unitInterval, ℝ)}
    {K : NNReal} (hp : LipschitzWith K p) {x y : unitInterval} {d N : ℝ}
    (hd : d ≠ 0) (hy : (y : ℝ) = x + d) (hs : N ≤ |(s y - s x) / d|) :
    N - K ≤ |((p + s) y - (p + s) x) / d| := by
  -- Bound the background secant, then retain the sawtooth's remaining margin.
  have hpSlope : |(p y - p x) / d| ≤ K :=
    abs_div_sub_le_of_lipschitz hp hd hy
  have hsum := sub_le_abs_add_of_abs_le_of_le_abs hpSlope hs
  simpa only [ContinuousMap.coe_add, Pi.add_apply, add_sub_add_comm, add_div, add_comm]
    using hsum

/-- Helper for Proposition 49.3: adding a Lipschitz map preserves a larger secant bound. -/
private lemma add_mem_largeSecantSet_of_lipschitz (p s : C(unitInterval, ℝ)) (K : NNReal)
    (n N : ℕ) (hn : 2 ≤ n) (hp : LipschitzWith K p) (hs : s ∈ U_{N})
    (hmargin : (n : ℝ) + K < N) :
    p + s ∈ U_{n} := by
  rw [mem_largeSecantSet] at hs ⊢
  obtain ⟨h, hpos, hleN, hsInf⟩ := hs
  refine ⟨h, hpos, ?_, ?_⟩
  · -- The witness scale for `U_N` is also small enough for `U_n`.
    have hnpos : 0 < (n : ℝ) := by positivity
    have hnN : (n : ℝ) ≤ N := by
      have hK : 0 ≤ (K : ℝ) := K.coe_nonneg
      linarith
    calc
      h ≤ 1 / (N : ℝ) := hleN
      _ ≤ 1 / (n : ℝ) := one_div_le_one_div_of_le hnpos hnN
  · -- At every point, use the steep endpoint supplied by the sawtooth secant.
    have hNpos : 0 < (N : ℝ) := by
      have hK : 0 ≤ (K : ℝ) := K.coe_nonneg
      have hnreal : 0 < (n : ℝ) := by positivity
      linarith
    have htwoN : (2 : ℝ) ≤ N := by
      have htwoNnat : 2 ≤ N := by
        have hnN : n ≤ N := by
          have hK : 0 ≤ (K : ℝ) := K.coe_nonneg
          exact_mod_cast (show (n : ℝ) ≤ N by linarith)
        exact hn.trans hnN
      exact_mod_cast htwoNnat
    have hleHalf : h ≤ (1 / 2 : ℝ) := by
      exact hleN.trans (one_div_le_one_div_of_le (by norm_num) htwoN)
    have hMarginPos : 0 < (N : ℝ) - K := by linarith
    have hPoint : ∀ x, (N : ℝ) - K ≤ Δ (p + s) (x, h) := by
      intro x
      have hsPoint : (N : ℝ) ≤ Δ s (x, h) :=
        le_trans hsInf.le (infMagnitude_le s h hpos hleHalf x)
      rw [le_maxMagnitude_iff s hNpos x h] at hsPoint
      rw [le_maxMagnitude_iff (p + s) hMarginPos x h]
      rcases hsPoint with hsRight | hsLeft
      · left
        obtain ⟨y, hy, hySlope⟩ := hsRight
        refine ⟨y, hy, ?_⟩
        exact sub_le_abs_add_secant_of_lipschitz hp hpos.ne' hy hySlope
      · right
        obtain ⟨y, hy, hySlope⟩ := hsLeft
        refine ⟨y, hy, ?_⟩
        exact sub_le_abs_add_secant_of_lipschitz hp (neg_ne_zero.mpr hpos.ne') hy hySlope
    -- Pass the uniform pointwise margin to the infimum secant magnitude.
    have hLower : (N : ℝ) - K ≤ Δ_{h} (p + s) :=
      le_infMagnitude_iff (p + s) h hpos hleHalf |>.2 hPoint
    have hstrict : (n : ℝ) < (N : ℝ) - K := by linarith
    exact lt_of_lt_of_le hstrict hLower

/-- Proposition 49.3: for `2 ≤ n`, the set `Uₙ` is dense in the space of
continuous real-valued functions on the closed unit interval. -/
theorem dense_largeSecantSet (n : ℕ) (hn : 2 ≤ n) :
    Dense U_{n} := by
  rw [Metric.dense_iff]
  intro f ε hε
  have hhalf : 0 < ε / 2 := by positivity
  -- First approximate by a Lipschitz function so its secants have a uniform bound.
  obtain ⟨p, K, hpLip, hfp⟩ := exists_lipschitz_dist_lt f hhalf
  -- Then choose a sawtooth frequency exceeding the target slope by that bound.
  obtain ⟨N, hN⟩ := exists_nat_gt ((n : ℝ) + K)
  have hNnat : 2 ≤ N := by
    have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hK : 0 ≤ (K : ℝ) := K.coe_nonneg
    exact_mod_cast (show (2 : ℝ) ≤ N by linarith)
  obtain ⟨s, hsU, hsAbs⟩ := smallSawtooth_exists hNnat hhalf
  refine ⟨p + s, ?_, add_mem_largeSecantSet_of_lipschitz p s K n N hn hpLip hsU hN⟩
  -- The two half-radius estimates combine by the triangle inequality.
  rw [Metric.mem_ball]
  have hps : dist p (p + s) ≤ ε / 2 :=
    dist_add_le_of_abs_le p s hhalf.le hsAbs
  rw [dist_comm]
  exact lt_of_le_of_lt (dist_triangle f p (p + s)) (by linarith)

/-- The metric approximation formulation of density for `U_{n}`. -/
theorem exists_largeSecant_dist_lt (n : ℕ) (hn : 2 ≤ n)
    (f : C(unitInterval, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(unitInterval, ℝ), g ∈ U_{n} ∧ dist f g < ε :=
  (dense_largeSecantSet n hn).exists_dist_lt f hε

end UnitIntervalSecant
