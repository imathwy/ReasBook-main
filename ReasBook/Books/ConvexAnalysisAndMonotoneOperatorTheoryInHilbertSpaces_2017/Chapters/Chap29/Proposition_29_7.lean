import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap03.Theorem_3_34
import BauschkeLean.Chap04.Proposition_4_21

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology InnerProductSpace

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : ℕ → Set H}
variable (hC0_nonempty : (C 0).Nonempty)
variable (hC_closed : ∀ n, IsClosed (C n))
variable (hC_convex : ∀ n, Convex ℝ (C n))
variable (hinc : ∀ n, C n ⊆ C (n + 1))

local notation "C∞" => closure (⋃ n : ℕ, C n)

private theorem nonempty_of_zero_of_increasing (hC0_nonempty : (C 0).Nonempty)
    (hinc : ∀ n, C n ⊆ C (n + 1)) :
    ∀ n, (C n).Nonempty := by
  intro n
  rcases hC0_nonempty with ⟨x, hx⟩
  exact ⟨x, (monotone_nat_of_le_succ hinc) (Nat.zero_le n) hx⟩

local notation "hC_nonempty" => nonempty_of_zero_of_increasing hC0_nonempty hinc

-- Semantic recall: `Directed.convex_iUnion` and `Convex.closure` match the convexity helper here,
-- and the statement uses the verified project owner `projectionPoint`/`P[C, hC]` together with
-- the Chapter 3 Chebyshev theorem for nonempty closed convex sets.
/-- If `C 0` is nonempty and `(C n)` is increasing with each `C n` convex, then
`closure (⋃ n : ℕ, C n)` is Chebyshev. Nestedness propagates nonemptiness from `C 0` to every
`C n`, so the closure of the union is a nonempty closed convex set. -/
theorem isChebyshev_closure_iUnion_of_increasing_nonempty_convex
    (hC0_nonempty : (C 0).Nonempty)
    (hC_convex : ∀ n, Convex ℝ (C n))
    (hinc : ∀ n, C n ⊆ C (n + 1)) :
    IsChebyshev C∞ := by
  refine isChebyshev_of_nonempty_isClosed_convex ?_ isClosed_closure ?_
  · rcases hC0_nonempty with ⟨x, hx⟩
    exact ⟨x, subset_closure <| Set.mem_iUnion.2 ⟨0, hx⟩⟩
  · exact
      (Directed.convex_iUnion ((monotone_nat_of_le_succ hinc).directed_le) hC_convex).closure

local notation "hC∞" =>
  isChebyshev_closure_iUnion_of_increasing_nonempty_convex hC0_nonempty hC_convex hinc

/-- Helper for Proposition 29.7: a point in the closure of an increasing union has distance
tending to `0` to the stages of the union. -/
private lemma tendsto_zero_infDist_of_mem_closure_iUnion_of_increasing
    (hinc : ∀ n, C n ⊆ C (n + 1)) {p : H} (hp : p ∈ C∞) :
    Tendsto (fun n ↦ Metric.infDist p (C n)) atTop (𝓝 0) := by
  -- Approximate `p` by one point in the union and then keep that witness in every later set.
  rw [Metric.tendsto_nhds]
  intro ε hε
  rcases Metric.mem_closure_iff.1 hp ε hε with ⟨y, hyUnion, hyDist⟩
  rcases Set.mem_iUnion.1 hyUnion with ⟨N, hyN⟩
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  have hyCn : y ∈ C n := (monotone_nat_of_le_succ hinc) hn hyN
  have hlt : Metric.infDist p (C n) < ε :=
    lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hyCn) hyDist
  simpa [Real.dist_eq, abs_of_nonneg (Metric.infDist_nonneg : 0 ≤ Metric.infDist p (C n))] using hlt

/-- Helper for Proposition 29.7: projecting a point of `closure (⋃ n, C n)` onto the increasing
sets `C n` converges strongly back to that point. -/
private lemma tendsto_projectionPoint_to_limit_point_of_mem_closure_iUnion
    {p : H} (hp : p ∈ C∞) :
    Tendsto
      (fun n ↦
        P[C n, isChebyshev_of_nonempty_isClosed_convex (hC_nonempty n) (hC_closed n)
          (hC_convex n)] p)
      atTop
      (𝓝 p) := by
  -- Convert the convergence claim to the vanishing of the projection distances.
  rw [tendsto_iff_dist_tendsto_zero]
  have hzero : Tendsto (fun n ↦ Metric.infDist p (C n)) atTop (𝓝 0) :=
    tendsto_zero_infDist_of_mem_closure_iUnion_of_increasing hinc hp
  convert hzero using 1
  ext n
  simpa [dist_comm] using
    (projectionPoint_isBestApproximation (C n)
      (isChebyshev_of_nonempty_isClosed_convex (hC_nonempty n) (hC_closed n)
        (hC_convex n)) p).2

/-- Helper for Proposition 29.7: the distances from `x` to the projection points on `C n` converge
to the distance from `x` to the projection onto `closure (⋃ n, C n)`. -/
private lemma tendsto_norm_sub_projectionPoint_of_increasing_family (x : H) :
    Tendsto
      (fun n ↦
        ‖x - P[C n, isChebyshev_of_nonempty_isClosed_convex (hC_nonempty n) (hC_closed n)
          (hC_convex n)] x‖)
      atTop
      (𝓝 ‖x - P[C∞, hC∞] x‖) := by
  let p := P[C∞, hC∞] x
  let u : ℕ → H := fun n ↦
    P[C n, isChebyshev_of_nonempty_isClosed_convex (hC_nonempty n) (hC_closed n)
      (hC_convex n)] x
  let v : ℕ → H := fun n ↦
    P[C n, isChebyshev_of_nonempty_isClosed_convex (hC_nonempty n) (hC_closed n)
      (hC_convex n)] p
  have hp_mem : p ∈ C∞ := by
    change P[C∞, hC∞] x ∈ C∞
    exact projectionPoint_mem C∞ hC∞ x
  have hv : Tendsto v atTop (𝓝 p) := by
    change Tendsto
      (fun n ↦
        P[C n, isChebyshev_of_nonempty_isClosed_convex (hC_nonempty n) (hC_closed n)
          (hC_convex n)] p)
      atTop
      (𝓝 p)
    exact
      tendsto_projectionPoint_to_limit_point_of_mem_closure_iUnion
        (hC0_nonempty := hC0_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
        (hinc := hinc) hp_mem
  have hlower : ∀ n, ‖x - p‖ ≤ ‖x - u n‖ := by
    intro n
    have hu_mem : u n ∈ C∞ := by
      exact subset_closure <| Set.mem_iUnion.2 ⟨n, by
        change
          P[C n, isChebyshev_of_nonempty_isClosed_convex (hC_nonempty n) (hC_closed n)
            (hC_convex n)] x ∈ C n
        exact
          projectionPoint_mem (C n)
            (isChebyshev_of_nonempty_isClosed_convex (hC_nonempty n) (hC_closed n)
              (hC_convex n)) x⟩
    -- The projection onto the closure gives the smallest admissible distance in `C∞`.
    calc
      ‖x - p‖ = dist x p := by rw [dist_eq_norm]
      _ = Metric.infDist x C∞ := by
        simpa [p] using (projectionPoint_isBestApproximation C∞ hC∞ x).2
      _ ≤ dist x (u n) := Metric.infDist_le_dist_of_mem hu_mem
      _ = ‖x - u n‖ := by rw [dist_eq_norm]
  have hupper : ∀ n, ‖x - u n‖ ≤ ‖x - v n‖ := by
    intro n
    have hv_mem : v n ∈ C n := by
      change
        P[C n, isChebyshev_of_nonempty_isClosed_convex (hC_nonempty n) (hC_closed n)
          (hC_convex n)] p ∈ C n
      exact
        projectionPoint_mem (C n)
          (isChebyshev_of_nonempty_isClosed_convex (hC_nonempty n) (hC_closed n)
            (hC_convex n)) p
    -- The projection onto `C n` is no farther from `x` than any other point of `C n`.
    calc
      ‖x - u n‖ = dist x (u n) := by rw [dist_eq_norm]
      _ = Metric.infDist x (C n) := by
        simpa [u] using
          (projectionPoint_isBestApproximation (C n)
            (isChebyshev_of_nonempty_isClosed_convex (hC_nonempty n) (hC_closed n)
              (hC_convex n)) x).2
      _ ≤ dist x (v n) := Metric.infDist_le_dist_of_mem hv_mem
      _ = ‖x - v n‖ := by rw [dist_eq_norm]
  have hv_norm : Tendsto (fun n ↦ ‖x - v n‖) atTop (𝓝 ‖x - p‖) := by
    -- The approximating projections of `p` transfer to the distance-from-`x` sequence by continuity.
    exact ((continuous_const.sub continuous_id).norm.tendsto p).comp hv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hv_norm hlower hupper

/-- Helper for Proposition 29.7: every weak sequential cluster point of the projection sequence
belongs to `closure (⋃ n, C n)`. -/
private lemma weakSequentialClusterPt_mem_closure_iUnion_of_projection_sequence
    (x z : H)
    (hz :
      IsSequentialClusterPt
        (fun n ↦
          toWeakSpace ℝ H
            (P[C n, isChebyshev_of_nonempty_isClosed_convex (hC_nonempty n) (hC_closed n)
              (hC_convex n)] x))
        (toWeakSpace ℝ H z)) :
    z ∈ C∞ := by
  let u : ℕ → H := fun n ↦
    P[C n, isChebyshev_of_nonempty_isClosed_convex (hC_nonempty n) (hC_closed n)
      (hC_convex n)] x
  have hClosureConvex : Convex ℝ C∞ := by
    exact
      (Directed.convex_iUnion ((monotone_nat_of_le_succ hinc).directed_le) hC_convex).closure
  have hweakClosed : IsClosed ((toWeakSpace ℝ H) '' C∞) :=
    (isClosed_iff_weak_image_isClosed_of_convex hClosureConvex).1 isClosed_closure
  rcases hz.exists_subseq_tendsto with ⟨φ, hφ, hφz⟩
  have hsubseq_mem : ∀ n, toWeakSpace ℝ H (u (φ n)) ∈ (toWeakSpace ℝ H) '' C∞ := by
    intro n
    refine ⟨u (φ n), ?_, rfl⟩
    exact subset_closure <| Set.mem_iUnion.2 ⟨φ n, by
      change
        P[C (φ n), isChebyshev_of_nonempty_isClosed_convex (hC_nonempty (φ n))
          (hC_closed (φ n)) (hC_convex (φ n))] x ∈ C (φ n)
      exact
        projectionPoint_mem (C (φ n))
          (isChebyshev_of_nonempty_isClosed_convex (hC_nonempty (φ n)) (hC_closed (φ n))
            (hC_convex (φ n))) x⟩
  -- Closedness of the weak image of `C∞` keeps the weak limit inside `C∞`.
  have hz_mem : toWeakSpace ℝ H z ∈ closure ((toWeakSpace ℝ H) '' C∞) :=
    mem_closure_of_tendsto hφz (Filter.Eventually.of_forall hsubseq_mem)
  rw [hweakClosed.closure_eq] at hz_mem
  rcases hz_mem with ⟨y, hyClosure, hyz⟩
  exact (toWeakSpace ℝ H).injective hyz ▸ hyClosure

/-- Proposition 29.7: let `(C n)ₙ` be an increasing sequence of nonempty closed convex subsets of a
real Hilbert space, set `C = closure (⋃ n : ℕ, C n)`, and let `x ∈ H`. Since nestedness propagates
nonemptiness, it is enough to assume `(C 0).Nonempty`. Then the metric projections of `x` onto
`C n` converge strongly to the metric projection of `x` onto `C`. -/
theorem tendsto_projectionPoint_of_increasing_nonempty_isClosed_convex (x : H) :
    Tendsto
      (fun n ↦
        P[C n, isChebyshev_of_nonempty_isClosed_convex (hC_nonempty n) (hC_closed n)
          (hC_convex n)] x)
      atTop
      (𝓝 (P[C∞, hC∞] x)) := by
  let p := P[C∞, hC∞] x
  let u : ℕ → H := fun n ↦
    P[C n, isChebyshev_of_nonempty_isClosed_convex (hC_nonempty n) (hC_closed n)
      (hC_convex n)] x
  have hClosureNonempty : C∞.Nonempty := by
    rcases hC0_nonempty with ⟨y, hy⟩
    exact ⟨y, subset_closure <| Set.mem_iUnion.2 ⟨0, hy⟩⟩
  have hClosureConvex : Convex ℝ C∞ := by
    exact
      (Directed.convex_iUnion ((monotone_nat_of_le_succ hinc).directed_le) hC_convex).closure
  have hp_norm : ‖x - p‖ = Metric.infDist x C∞ := by
    simpa [p, dist_eq_norm] using (projectionPoint_isBestApproximation C∞ hC∞ x).2
  have hnorm_base : Tendsto (fun n ↦ ‖x - u n‖) atTop (𝓝 ‖x - p‖) := by
    change Tendsto
      (fun n ↦
        ‖x - P[C n, isChebyshev_of_nonempty_isClosed_convex (hC_nonempty n) (hC_closed n)
          (hC_convex n)] x‖)
      atTop
      (𝓝 ‖x - p‖)
    simpa [p] using
      tendsto_norm_sub_projectionPoint_of_increasing_family
        (hC0_nonempty := hC0_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
        (hinc := hinc) x
  have hnorm :
      Tendsto (fun n ↦ ‖u n - x‖) atTop (𝓝 (Metric.infDist x C∞)) := by
    -- This is the textbook squeeze `(29.3)` after reversing the subtraction order in the norm.
    have hnorm_rev : Tendsto (fun n ↦ ‖u n - x‖) atTop (𝓝 ‖x - p‖) := by
      convert hnorm_base using 1
      ext n
      rw [norm_sub_rev]
    exact hp_norm ▸ hnorm_rev
  have hlimsup :
      Filter.limsup (fun n ↦ ENNReal.ofReal (‖u n - x‖)) atTop ≤
        ENNReal.ofReal (Metric.infDist x C∞) := by
    have hENN :
        Tendsto (fun n ↦ ENNReal.ofReal (‖u n - x‖)) atTop
          (𝓝 (ENNReal.ofReal (Metric.infDist x C∞))) := by
      exact (ENNReal.continuous_ofReal.tendsto (Metric.infDist x C∞)).comp hnorm
    exact hENN.limsup_eq.le
  have hcluster :
      ∀ z : H, IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (u n)) (toWeakSpace ℝ H z) →
        z ∈ C∞ := by
    intro z hz
    simpa [u] using
      weakSequentialClusterPt_mem_closure_iUnion_of_projection_sequence
        (hC0_nonempty := hC0_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
        (hinc := hinc) x z hz
  -- Proposition 4.21 packages the standard weak-cluster-point argument once the distance squeeze
  -- and the closedness of weak cluster points have been established.
  simpa [u, p] using
    tendsto_projectionPoint_of_limsup_norm_sub_le_infDist_of_weakSequentialClusterPts_mem
      (C := C∞) hClosureNonempty isClosed_closure hClosureConvex x u hlimsup hcluster

end
