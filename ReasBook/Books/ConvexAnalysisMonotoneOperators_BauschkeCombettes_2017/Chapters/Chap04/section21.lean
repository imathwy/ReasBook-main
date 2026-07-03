import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_4_21_1 (from Chap04) -/
universe u

open scoped InnerProductSpace

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable {C : Set 𝓗}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "P" =>
  projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)

-- Proof sketch: apply the projection characterization from
-- `eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex` to `P x`
-- with test point `P y`, and to `P y` with test point `P x`; adding the resulting inequalities and
-- rearranging yields the displayed firm nonexpansiveness inequality.
/-- Text 4.21.1 (1): the metric projection onto a nonempty closed convex subset of a real Hilbert
space is firmly nonexpansive. -/
theorem firmlyNonexpansive_projectionPoint_of_nonempty_isClosed_convex :
    FirmlyNonexpansive P := by
  rw [firmlyNonexpansive_iff_norm_sq_le_inner]
  intro x y
  exact
    norm_sq_projectionPoint_sub_le_inner_projectionPoint_sub_of_nonempty_isClosed_convex
      hC_nonempty hC_closed hC_convex x y

/-- Helper for Text 4.21.1: every point of `C` is fixed by the metric projection onto `C`. -/
private theorem projectionPoint_eq_self_of_mem_of_nonempty_isClosed_convex {x : 𝓗} (hx : x ∈ C) :
    P x = x := by
  -- The projection characterization is realized by `x` itself because the residual vanishes.
  have hxproj : x = P x := by
    exact
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex).mpr <| by
          refine ⟨hx, ?_⟩
          intro y hy
          simp
  simpa using hxproj.symm

-- Proof sketch: if `x ∈ C`, then the projection of `x` onto `C` is `x` itself because the
-- distance is `0`; conversely, every fixed point of `P` lies in `C` since projection points lie in
-- the target set.
/-- Text 4.21.1 (2): the fixed point set of the metric projection onto `C` is exactly `C`. -/
theorem fixedPoints_projectionPoint_eq_of_nonempty_isClosed_convex :
    Function.fixedPoints P = C := by
  ext x
  constructor
  · intro hx
    -- Fixed points belong to `C` because every projection point lies in the target set.
    rw [Function.mem_fixedPoints_iff] at hx
    simpa [hx] using
      projectionPoint_mem C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x
  · intro hx
    -- Points already in `C` are fixed by the projection by the helper lemma above.
    rw [Function.mem_fixedPoints_iff]
    exact
      projectionPoint_eq_self_of_mem_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex hx

-- Proof sketch: rewrite the fixed point set using
-- `fixedPoints_projectionPoint_eq_of_nonempty_isClosed_convex` and then use `hC_closed`.
/-- Text 4.21.1 (3): the fixed point set of the metric projection onto `C` is closed. -/
theorem isClosed_fixedPoints_projectionPoint_of_nonempty_isClosed_convex :
    IsClosed (Function.fixedPoints P) := by
  -- Identify the fixed-point set with `C` and inherit closedness from the hypothesis.
  simpa [fixedPoints_projectionPoint_eq_of_nonempty_isClosed_convex
    hC_nonempty hC_closed hC_convex] using hC_closed

-- Proof sketch: rewrite the fixed point set using
-- `fixedPoints_projectionPoint_eq_of_nonempty_isClosed_convex` and then use `hC_convex`.
/-- Text 4.21.1 (4): the fixed point set of the metric projection onto `C` is convex. -/
theorem convex_fixedPoints_projectionPoint_of_nonempty_isClosed_convex :
    Convex ℝ (Function.fixedPoints P) := by
  -- Identify the fixed-point set with `C` and inherit convexity from the hypothesis.
  simpa [fixedPoints_projectionPoint_eq_of_nonempty_isClosed_convex
    hC_nonempty hC_closed hC_convex] using hC_convex

end

/-! ### Proposition_4_21 (from Chap04) -/
open Filter
open scoped Topology InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- A sequence is norm-bounded once its distances to one point are eventually bounded above. -/
private lemma bounded_range_of_eventually_norm_sub_le
    {x : ℕ → H} {z : H} {R : ℝ}
    (hR : ∀ᶠ n in atTop, ‖x n - z‖ ≤ R) :
    Bornology.IsBounded (Set.range x) := by
  rw [eventually_atTop] at hR
  rcases hR with ⟨N, hN⟩
  let s₀ : Set H := {y | ∃ n < N, x n = y}
  let s₁ : Set H := Set.range fun n : ℕ ↦ x (n + N)
  have hs₀_finite : s₀.Finite := by
    classical
    have hs₀_eq : s₀ = x '' {n : ℕ | n < N} := by
      ext y
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨n, hn, rfl⟩
      · rintro ⟨n, hn, rfl⟩
        exact ⟨n, hn, rfl⟩
    rw [hs₀_eq]
    exact (Set.finite_lt_nat N).image x
  have hs₁_bounded : Bornology.IsBounded s₁ := by
    have hball : Bornology.IsBounded (Metric.closedBall z R) := Metric.isBounded_closedBall
    refine hball.subset ?_
    rintro y ⟨n, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hN (n + N) (Nat.le_add_left N n)
  have hrange_subset : Set.range x ⊆ s₀ ∪ s₁ := by
    rintro y ⟨n, rfl⟩
    by_cases hn : n < N
    · exact Or.inl ⟨n, hn, rfl⟩
    · exact Or.inr ⟨n - N, by simp [Nat.sub_add_cancel (Nat.le_of_not_lt hn)]⟩
  exact (hs₀_finite.isBounded.union hs₁_bounded).subset hrange_subset

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- An `ℝ≥0∞` limsup bound on a nonnegative real sequence gives both an eventual real upper bound
and the corresponding real-valued `Filter.limsup` bound. -/
private lemma isBoundedUnder_and_limsup_le_of_ennreal_limsup_le
    {x : ℕ → H} {z : H} {d : ℝ}
    (hd : 0 ≤ d)
    (hlimsup :
      Filter.limsup (fun n ↦ ENNReal.ofReal (‖x n - z‖)) atTop ≤ ENNReal.ofReal d) :
    atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ ‖x n - z‖) ∧
      Filter.limsup (fun n ↦ ‖x n - z‖) atTop ≤ d := by
  let u := fun n : ℕ ↦ ENNReal.ofReal (‖x n - z‖)
  have hu_lt : ∀ᶠ n in atTop, u n < ENNReal.ofReal (d + 1) := by
    refine eventually_lt_of_limsup_lt ?_
    refine lt_of_le_of_lt hlimsup ?_
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < d + 1)).2 (by linarith)
  have hu_le : ∀ᶠ n in atTop, u n ≤ ENNReal.ofReal (d + 1) :=
    hu_lt.mono fun _ hn ↦ le_of_lt hn
  have hreal_eventually : ∀ᶠ n in atTop, ‖x n - z‖ ≤ d + 1 := by
    filter_upwards [hu_le] with n hn
    simpa [u] using ENNReal.toReal_le_of_le_ofReal (by positivity : 0 ≤ d + 1) hn
  have hlimsup_eq :
      Filter.limsup (fun n ↦ ‖x n - z‖) atTop = (Filter.limsup u atTop).toReal := by
    simpa [u] using
      ENNReal.limsup_toReal_eq ENNReal.ofReal_ne_top hu_le
  refine ⟨⟨d + 1, hreal_eventually⟩, ?_⟩
  rw [hlimsup_eq]
  exact ENNReal.toReal_le_of_le_ofReal hd hlimsup

-- Proof sketch: let `p` be the metric projection of `z` onto `C`. The `ℝ≥0∞` limsup bound on the
-- nonnegative distance sequence yields an eventual real upper bound, hence `(xₙ)` is bounded.
-- Every weak sequential cluster point `y` belongs to `C` by hypothesis, and lower semicontinuity
-- of `u ↦ ‖u - z‖` along a weakly convergent subsequence shows `‖y - z‖ ≤ Metric.infDist z C`,
-- so `y` is a best approximation to `z` in `C`; uniqueness identifies `y` with `p`. Boundedness
-- together with uniqueness of weak sequential cluster points yields weak convergence of the whole
-- sequence to `p`, and the real limsup bound then upgrades this weak convergence to strong
-- convergence via `tendsto_iff_tendsto_weakly_and_limsup_norm_le`.
/-- Proposition 4.21: if `C` is a nonempty closed convex subset of a real Hilbert space, `z ∈ H`,
every weak sequential cluster point of a sequence `xₙ` belongs to `C`, and the nonnegative
distance sequence satisfies the canonical `ℝ≥0∞` limsup bound
`limsup ‖xₙ - z‖ ≤ dist(z, C)`, then `xₙ` converges strongly to the metric projection of `z`
onto `C`. -/
theorem tendsto_projectionPoint_of_limsup_norm_sub_le_infDist_of_weakSequentialClusterPts_mem
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (z : H) (xₙ : ℕ → H)
    (hlimsup :
      Filter.limsup (fun n ↦ ENNReal.ofReal (‖xₙ n - z‖)) atTop ≤
        ENNReal.ofReal (Metric.infDist z C))
    (hcluster :
      ∀ x : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H x) → x ∈ C) :
    Tendsto xₙ atTop
      (𝓝 (projectionPoint C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) z)) := by
  let hC_cheb := isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  let p := projectionPoint C hC_cheb z
  let d := Metric.infDist z C
  have hd_nonneg : 0 ≤ d := Metric.infDist_nonneg
  rcases isBoundedUnder_and_limsup_le_of_ennreal_limsup_le hd_nonneg hlimsup with
    ⟨⟨R, hR⟩, hlimsup_real⟩
  have hdist_boundedUnder : atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ ‖xₙ n - z‖) := ⟨R, hR⟩
  have hx_bounded : Bornology.IsBounded (Set.range xₙ) :=
    bounded_range_of_eventually_norm_sub_le hR
  have hp_best : IsBestApproximation z C p := projectionPoint_isBestApproximation C hC_cheb z
  have hp_norm : ‖p - z‖ = d := by
    simpa [p, d, dist_eq_norm, norm_sub_rev] using hp_best.2
  have hcluster_eq :
      ∀ {y : H},
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H y) →
          y = p := by
    intro y hy
    have hyC : y ∈ C := hcluster y hy
    rcases hy with ⟨φ, hφ, hφ_tendsto⟩
    have hweak_sub :
        Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ (φ n) - z)) atTop
          (𝓝 (toWeakSpace ℝ H (y - z))) := by
      have hconst :
          Tendsto (fun _ : ℕ ↦ toWeakSpace ℝ H z) atTop (𝓝 (toWeakSpace ℝ H z)) :=
        tendsto_const_nhds
      simpa [sub_eq_add_neg] using hφ_tendsto.sub hconst
    have hnorm_le_liminf :
        ‖y - z‖ ≤ Filter.liminf (fun n ↦ ‖xₙ (φ n) - z‖) atTop :=
      norm_le_liminf_of_tendsto_weakly (fun n ↦ xₙ (φ n) - z) (y - z) hweak_sub
    have hy_norm_le : ‖y - z‖ ≤ d := by
      refine le_of_forall_pos_le_add fun ε hε ↦ ?_
      have hsub_eventually :
          ∀ᶠ n in atTop, ‖xₙ (φ n) - z‖ < d + ε :=
        hφ.tendsto_atTop.eventually
          (eventually_lt_add_pos_of_limsup_le hdist_boundedUnder hlimsup_real hε)
      have hboundedBelow :
          atTop.IsBoundedUnder (· ≥ ·) (fun n ↦ ‖xₙ (φ n) - z‖) := by
        refine ⟨(0 : ℝ), ?_⟩
        show ∀ᶠ n : ℕ in atTop, ‖xₙ (φ n) - z‖ ≥ (0 : ℝ)
        exact Eventually.of_forall fun n : ℕ ↦ norm_nonneg (xₙ (φ n) - z)
      have hliminf_le :
          Filter.liminf (fun n ↦ ‖xₙ (φ n) - z‖) atTop ≤ d + ε := by
        refine Filter.liminf_le_of_le hboundedBelow ?_
        intro b hb
        obtain ⟨n, hn⟩ := (Eventually.and hb (hsub_eventually.mono fun _ h ↦ le_of_lt h)).exists
        exact hn.1.trans hn.2
      exact le_trans hnorm_le_liminf hliminf_le
    have hy_dist_eq : dist z y = d := by
      refine le_antisymm ?_ (Metric.infDist_le_dist_of_mem hyC)
      simpa [dist_eq_norm, norm_sub_rev, d] using hy_norm_le
    have hy_best : IsBestApproximation z C y :=
      (isBestApproximation_iff_mem_and_dist_eq_infDist z C y).2 ⟨hyC, hy_dist_eq⟩
    exact eq_projectionPoint_of_isBestApproximation C hC_cheb hy_best
  have hunique :
      ∀ y w : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H y) →
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H w) →
        y = w := by
    intro y w hy hw
    calc
      y = p := hcluster_eq hy
      _ = w := (hcluster_eq hw).symm
  rcases
      (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint xₙ).2
        ⟨hx_bounded, hunique⟩ with
    ⟨y, hy⟩
  have hy_cluster :
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H y) :=
    ⟨id, strictMono_id, by simpa using hy⟩
  have hy_eq : y = p := hcluster_eq hy_cluster
  have hweak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H p)) := by
    simpa [hy_eq] using hy
  have hweak_sub :
      Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n - z)) atTop (𝓝 (toWeakSpace ℝ H (p - z))) := by
    have hconst :
        Tendsto (fun _ : ℕ ↦ toWeakSpace ℝ H z) atTop (𝓝 (toWeakSpace ℝ H z)) :=
      tendsto_const_nhds
    simpa [sub_eq_add_neg] using hweak.sub hconst
  have hstrong_sub : Tendsto (fun n ↦ xₙ n - z) atTop (𝓝 (p - z)) := by
    exact
      (tendsto_iff_tendsto_weakly_and_limsup_norm_le (fun n ↦ xₙ n - z) (p - z)).2
        ⟨hweak_sub, by simpa [hp_norm] using hlimsup_real⟩
  have hconst : Tendsto (fun _ : ℕ ↦ z) atTop (𝓝 z) := tendsto_const_nhds
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, p] using hstrong_sub.add hconst
