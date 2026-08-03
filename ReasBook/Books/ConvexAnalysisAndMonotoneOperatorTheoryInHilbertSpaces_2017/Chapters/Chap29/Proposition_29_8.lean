import Mathlib
import BauschkeLean.Chap02.Lemma_2_12
import BauschkeLean.Chap03.Theorem_3_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology InnerProductSpace

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

variable (C : ℕ → Set H) (h_inter_nonempty : (⋂ n, C n).Nonempty)
variable (h_closed : ∀ n, IsClosed (C n)) (h_convex : ∀ n, Convex ℝ (C n))

local notation "C∞" => ⋂ n : ℕ, C n

local notation "hC∞" =>
  isChebyshev_of_nonempty_isClosed_convex h_inter_nonempty (isClosed_iInter h_closed)
    (convex_iInter h_convex)

/-- Helper for Proposition 29.8: the sequence `n ↦ P[C n] x` of projection points onto the nested
closed convex sets. -/
private noncomputable def projectionPointSeq (x : H) : ℕ → H :=
  fun n ↦
    P[C n, isChebyshev_of_nonempty_isClosed_convex
      (h_inter_nonempty.mono fun _ hy ↦ Set.mem_iInter.mp hy n) (h_closed n)
      (h_convex n)] x

/-- Helper for Proposition 29.8: the squared distance from `x` to the projection point on `C n`.
-/
private noncomputable def projectionDistanceSq (x : H) : ℕ → ℝ :=
  fun n ↦ ‖x - projectionPointSeq C h_inter_nonempty h_closed h_convex x n‖ ^ 2

/-- Helper for Proposition 29.8: a projection point onto a later set belongs to every earlier set
of the decreasing family. -/
private lemma projectionPoint_mem_of_le (hanti : Antitone C) (x : H) {m n : ℕ} (hmn : m ≤ n) :
    projectionPointSeq C h_inter_nonempty h_closed h_convex x n ∈ C m := by
  -- Nestedness transports the canonical projection point from level `n` back to level `m`.
  exact hanti hmn <|
    by
      simpa [projectionPointSeq] using
        projectionPoint_mem (C n)
          (isChebyshev_of_nonempty_isClosed_convex
            (h_inter_nonempty.mono fun _ hy ↦ Set.mem_iInter.mp hy n) (h_closed n)
            (h_convex n)) x

/-- Helper for Proposition 29.8: the squared distances `‖x - P[C n] x‖^2` form a monotone
sequence. -/
private lemma projectionDistanceSq_monotone (hanti : Antitone C) (x : H) :
    Monotone (projectionDistanceSq C h_inter_nonempty h_closed h_convex x) := by
  intro m n hmn
  let p := projectionPointSeq C h_inter_nonempty h_closed h_convex x
  -- The later projection point is an admissible competitor for the earlier projection problem.
  have hdist :
      dist x (p m) ≤ dist x (p n) := by
    calc
      dist x (p m) = Metric.infDist x (C m) := by
        simpa [p, projectionPointSeq] using
          (projectionPoint_isBestApproximation (C m)
            (isChebyshev_of_nonempty_isClosed_convex
              (h_inter_nonempty.mono fun y hy ↦ Set.mem_iInter.mp hy m) (h_closed m)
              (h_convex m)) x).2
      _ ≤ dist x (p n) :=
        Metric.infDist_le_dist_of_mem <|
          projectionPoint_mem_of_le C h_inter_nonempty h_closed h_convex hanti x hmn
  -- Squaring preserves the order because both distances are nonnegative.
  have hnorm : ‖x - p m‖ ≤ ‖x - p n‖ := by
    simpa [p, dist_eq_norm] using hdist
  dsimp [projectionDistanceSq]
  nlinarith [hnorm, norm_nonneg (x - p m), norm_nonneg (x - p n)]

/-- Helper for Proposition 29.8: the midpoint estimate controls the projection gap by the drop in
the squared-distance sequence. -/
private lemma projectionGap_sq_le_twice_distanceSq_drop
    (hanti : Antitone C) (x : H) {m n : ℕ} (hmn : m ≤ n) :
    ‖projectionPointSeq C h_inter_nonempty h_closed h_convex x n -
        projectionPointSeq C h_inter_nonempty h_closed h_convex x m‖ ^ 2 ≤
      2 * (projectionDistanceSq C h_inter_nonempty h_closed h_convex x n -
        projectionDistanceSq C h_inter_nonempty h_closed h_convex x m) := by
  let p := projectionPointSeq C h_inter_nonempty h_closed h_convex x
  have hpn_mem : p n ∈ C m := by
    -- The later projection point already lies in the earlier set.
    exact projectionPoint_mem_of_le C h_inter_nonempty h_closed h_convex hanti x hmn
  have hpm_mem : p m ∈ C m := by
    -- The level-`m` projection point lies in its own constraint set.
    simpa [p, projectionPointSeq] using
      projectionPoint_mem (C m)
        (isChebyshev_of_nonempty_isClosed_convex
          (h_inter_nonempty.mono fun _ hy ↦ Set.mem_iInter.mp hy m) (h_closed m)
          (h_convex m)) x
  have hmid_mem : midpoint ℝ (p n) (p m) ∈ C m := by
    -- Convexity keeps the midpoint of two admissible points inside `C m`.
    exact (h_convex m).midpoint_mem hpn_mem hpm_mem
  have hmid_dist :
      dist x (p m) ≤ dist x (midpoint ℝ (p n) (p m)) := by
    -- Projection optimality at level `m` compares `p m` with the midpoint competitor.
    calc
      dist x (p m) = Metric.infDist x (C m) := by
        simpa [p, projectionPointSeq] using
          (projectionPoint_isBestApproximation (C m)
            (isChebyshev_of_nonempty_isClosed_convex
              (h_inter_nonempty.mono fun y hy ↦ Set.mem_iInter.mp hy m) (h_closed m)
              (h_convex m)) x).2
      _ ≤ dist x (midpoint ℝ (p n) (p m)) :=
        Metric.infDist_le_dist_of_mem hmid_mem
  have hmid_sq : ‖x - p m‖ ^ 2 ≤ ‖x - midpoint ℝ (p n) (p m)‖ ^ 2 := by
    -- Squaring the metric comparison gives the term needed in Apollonius's identity.
    have hmid_norm : ‖x - p m‖ ≤ ‖x - midpoint ℝ (p n) (p m)‖ := by
      simpa [p, dist_eq_norm] using hmid_dist
    nlinarith [hmid_norm, norm_nonneg (x - p m), norm_nonneg (x - midpoint ℝ (p n) (p m))]
  have happ := apollonius_identity (p n) (p m) x
  -- Apollonius's identity and the midpoint bound yield the textbook estimate (29.4).
  dsimp [projectionDistanceSq]
  nlinarith [hmid_sq, happ]

/-- Helper for Proposition 29.8: the sequence of projection points is Cauchy. -/
private lemma projectionPointSeq_cauchy (hanti : Antitone C) (x : H) :
    CauchySeq (projectionPointSeq C h_inter_nonempty h_closed h_convex x) := by
  let p := projectionPointSeq C h_inter_nonempty h_closed h_convex x
  let s := projectionDistanceSq C h_inter_nonempty h_closed h_convex x
  have hs_mono : Monotone s :=
    projectionDistanceSq_monotone C h_inter_nonempty h_closed h_convex hanti x
  have hs_bdd : BddAbove (Set.range s) := by
    refine ⟨‖x - P[C∞, hC∞] x‖ ^ 2, ?_⟩
    rintro _ ⟨n, rfl⟩
    have hinter_mem : P[C∞, hC∞] x ∈ C n := by
      exact (Set.mem_iInter.mp (projectionPoint_mem C∞ hC∞ x)) n
    -- The projection onto the intersection is a fixed admissible competitor for every `C n`.
    have hdist :
        dist x (p n) ≤ dist x (P[C∞, hC∞] x) := by
      calc
        dist x (p n) = Metric.infDist x (C n) := by
          simpa [p, projectionPointSeq] using
            (projectionPoint_isBestApproximation (C n)
              (isChebyshev_of_nonempty_isClosed_convex
                (h_inter_nonempty.mono fun y hy ↦ Set.mem_iInter.mp hy n) (h_closed n)
                (h_convex n)) x).2
        _ ≤ dist x (P[C∞, hC∞] x) :=
          Metric.infDist_le_dist_of_mem hinter_mem
    have hnorm : ‖x - p n‖ ≤ ‖x - P[C∞, hC∞] x‖ := by
      simpa [p, dist_eq_norm] using hdist
    dsimp [s, projectionDistanceSq]
    nlinarith [hnorm, norm_nonneg (x - p n), norm_nonneg (x - P[C∞, hC∞] x)]
  let L : ℝ := ⨆ n, s n
  have hs_lim : Tendsto s atTop (𝓝 L) := by
    -- A monotone bounded real sequence converges to the supremum of its range.
    simpa [L] using tendsto_atTop_ciSup hs_mono hs_bdd
  have hsqrt_lim : Tendsto (fun N ↦ Real.sqrt (2 * (L - s N))) atTop (𝓝 0) := by
    -- The tail gap above the `N`th energy level tends to zero, and so does its square root.
    have htail_lim : Tendsto (fun N ↦ 2 * (L - s N)) atTop (𝓝 (2 * (L - L))) := by
      exact tendsto_const_nhds.mul (tendsto_const_nhds.sub hs_lim)
    have hsqrt' :
        Tendsto (fun N ↦ Real.sqrt (2 * (L - s N))) atTop
          (𝓝 (Real.sqrt (2 * (L - L)))) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp htail_lim
    simpa using hsqrt'
  refine cauchySeq_of_le_tendsto_0 (fun N ↦ Real.sqrt (2 * (L - s N))) ?_ hsqrt_lim
  intro n m N hNn hNm
  by_cases hnm : n ≤ m
  · have hgap :
        ‖p m - p n‖ ^ 2 ≤ 2 * (s m - s n) := by
      simpa [p, s, projectionDistanceSq, norm_sub_rev] using
        projectionGap_sq_le_twice_distanceSq_drop
          C h_inter_nonempty h_closed h_convex hanti x hnm
    have htail_nonneg : 0 ≤ 2 * (L - s N) := by
      have hsNL : s N ≤ L := le_ciSup hs_bdd N
      nlinarith
    have htail_sq : ‖p m - p n‖ ^ 2 ≤ 2 * (L - s N) := by
      have hsNn : s N ≤ s n := hs_mono hNn
      have hsmL : s m ≤ L := le_ciSup hs_bdd m
      nlinarith
    -- The tail control converts the squared estimate into a metric estimate.
    rw [dist_eq_norm, norm_sub_rev]
    nlinarith [htail_sq, Real.sq_sqrt htail_nonneg, norm_nonneg (p m - p n),
      Real.sqrt_nonneg (2 * (L - s N))]
  · have hmn : m ≤ n := le_of_not_ge hnm
    have hgap :
        ‖p n - p m‖ ^ 2 ≤ 2 * (s n - s m) := by
      simpa [p, s, projectionDistanceSq] using
        projectionGap_sq_le_twice_distanceSq_drop
          C h_inter_nonempty h_closed h_convex hanti x hmn
    have htail_nonneg : 0 ≤ 2 * (L - s N) := by
      have hsNL : s N ≤ L := le_ciSup hs_bdd N
      nlinarith
    have htail_sq : ‖p n - p m‖ ^ 2 ≤ 2 * (L - s N) := by
      have hsNm : s N ≤ s m := hs_mono hNm
      have hsnL : s n ≤ L := le_ciSup hs_bdd n
      nlinarith
    -- The symmetric index order gives the same tail bound.
    rw [dist_eq_norm]
    nlinarith [htail_sq, Real.sq_sqrt htail_nonneg, norm_nonneg (p n - p m),
      Real.sqrt_nonneg (2 * (L - s N))]

-- Semantic recall: `lean_leansearch` surfaced projection-limit owners for closed subspaces, but no
-- set-level owner for nested closed convex sets, so this item stays as a source-faithful theorem
-- in the project's `projectionPoint` API.
/-- Proposition 29.8: if `(C n)` is a decreasing sequence of closed convex subsets of a real
Hilbert space with nonempty intersection, then for every `x`, the projection points onto `C n`
converge to the projection point onto `⋂ n, C n`. -/
theorem tendsto_projectionPoint_of_nonempty_iInter_isClosed_convex_of_succ_subset
    (h_succ : ∀ n, C (n + 1) ⊆ C n) (x : H) :
    Tendsto
      (fun n ↦
        P[C n, isChebyshev_of_nonempty_isClosed_convex
          (h_inter_nonempty.mono fun _ hy ↦ Set.mem_iInter.mp hy n) (h_closed n)
          (h_convex n)] x)
      atTop
      (𝓝 (P[C∞, hC∞] x)) := by
  let p := projectionPointSeq C h_inter_nonempty h_closed h_convex x
  have hanti : Antitone C := antitone_nat_of_succ_le h_succ
  have hp_cauchy : CauchySeq p :=
    projectionPointSeq_cauchy C h_inter_nonempty h_closed h_convex hanti x
  rcases cauchySeq_tendsto_of_complete hp_cauchy with ⟨q, hq_lim⟩
  have hq_mem : q ∈ C∞ := by
    rw [Set.mem_iInter]
    intro n
    -- Each shifted tail stays inside `C n`, so closedness keeps its limit in `C n`.
    have htail_lim : Tendsto (fun k ↦ p (k + n)) atTop (𝓝 q) := by
      exact (Filter.tendsto_add_atTop_iff_nat n).2 hq_lim
    have htail_mem : ∀ k, p (k + n) ∈ C n := by
      intro k
      simpa [p, Nat.add_comm] using
        projectionPoint_mem_of_le C h_inter_nonempty h_closed h_convex hanti x
          (Nat.le_add_left n k)
    exact (h_closed n).mem_of_tendsto htail_lim (Filter.Eventually.of_forall htail_mem)
  have hdist_lim : Tendsto (fun n ↦ dist x (p n)) atTop (𝓝 (dist x q)) := by
    -- Distance to the fixed point `x` is continuous along the convergent projection sequence.
    exact ((continuous_const.dist continuous_id).tendsto q).comp hq_lim
  have hdist_le : dist x q ≤ dist x (P[C∞, hC∞] x) := by
    have hIic : dist x q ∈ Set.Iic (dist x (P[C∞, hC∞] x)) := by
      refine isClosed_Iic.mem_of_tendsto hdist_lim ?_
      refine Filter.Eventually.of_forall ?_
      intro n
      -- The projection onto the intersection bounds every earlier projection distance.
      have hinter_mem : P[C∞, hC∞] x ∈ C n := by
        exact (Set.mem_iInter.mp (projectionPoint_mem C∞ hC∞ x)) n
      have hbound :
          dist x (p n) ≤ dist x (P[C∞, hC∞] x) := by
        calc
          dist x (p n) = Metric.infDist x (C n) := by
            simpa [p, projectionPointSeq] using
              (projectionPoint_isBestApproximation (C n)
                (isChebyshev_of_nonempty_isClosed_convex
                  (h_inter_nonempty.mono fun y hy ↦ Set.mem_iInter.mp hy n) (h_closed n)
                  (h_convex n)) x).2
          _ ≤ dist x (P[C∞, hC∞] x) :=
            Metric.infDist_le_dist_of_mem hinter_mem
      exact hbound
    simpa [Set.mem_Iic] using hIic
  have hq_best : IsBestApproximation x C∞ q := by
    refine ⟨hq_mem, ?_⟩
    have hinf_le : Metric.infDist x C∞ ≤ dist x q :=
      Metric.infDist_le_dist_of_mem hq_mem
    -- The limit point cannot lie farther from `x` than the intersection projection.
    refine le_antisymm ?_ hinf_le
    calc
      dist x q ≤ dist x (P[C∞, hC∞] x) := hdist_le
      _ = Metric.infDist x C∞ := (projectionPoint_isBestApproximation C∞ hC∞ x).2
  have hq_eq : q = P[C∞, hC∞] x :=
    eq_projectionPoint_of_isBestApproximation C∞ hC∞ hq_best
  -- Identifying the unique best approximation in the intersection gives the announced limit.
  simpa [projectionPointSeq, hq_eq] using hq_lim

end
