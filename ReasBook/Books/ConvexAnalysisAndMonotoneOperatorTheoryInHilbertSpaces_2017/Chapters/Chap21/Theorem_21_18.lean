import BauschkeLean.Chap01.Text_1_0_40
import BauschkeLean.Chap06.Corollary_6_52
import BauschkeLean.Chap06.Proposition_6_47
import BauschkeLean.Chap20.Proposition_20_36
import BauschkeLean.Chap20.Proposition_20_38
import BauschkeLean.Chap21.Corollary_21_14
import BauschkeLean.Chap21.Proposition_21_17
import BauschkeLean.Chap21.Proposition_21_11
import BauschkeLean.Chap21.Proposition_21_12

open Filter
open scoped InnerProductSpace Pointwise Set SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Theorem 21.18 identifies pointwise local boundedness with avoiding the
  frontier of the domain of a maximally monotone operator.
- `core/canonical`: the owner notions are `SetValuedOperator.IsLocallyBoundedAt`, `A.dom`, and
  `Maximal IsMonotone A`.
- `bridge/view`: Proposition 21.11 and Proposition 21.12 supply the Fitzpatrick-domain bridge
  from `interior A.dom` to local boundedness; points outside `closure A.dom` are handled directly
  from Definition 21.10, so no parallel wrapper API is introduced.

Primitive data: `A`, `hA`, and `x`.
Derived API: the equivalence between `A.IsLocallyBoundedAt x` and `x ∉ frontier A.dom`. -/

/-- Helper for Theorem 21.18: a closure point where `A` is locally bounded already belongs to
`A.dom`. -/
private lemma mem_dom_of_isLocallyBoundedAt_of_mem_closure_dom
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) {x : H}
    (hLoc : A.IsLocallyBoundedAt x) (hx : x ∈ closure A.dom) :
    x ∈ A.dom := by
  classical
  rcases hLoc with ⟨ρ, hρ, hbounded⟩
  have happrox :
      ∀ n : ℕ, ∃ y ∈ A.dom, dist x y < min ρ (1 / (n + 1 : ℝ)) := by
    intro n
    have hδ : 0 < min ρ (1 / (n + 1 : ℝ)) := by
      refine lt_min hρ ?_
      positivity
    rcases (Metric.mem_closure_iff.1 hx) (min ρ (1 / (n + 1 : ℝ))) hδ with ⟨y, hy, hxy⟩
    exact ⟨y, hy, hxy⟩
  choose y hyDom hyDist using happrox
  choose u hu using fun n ↦ (SetValuedOperator.mem_dom_iff A (y n)).1 (hyDom n)
  -- Every sampled value lies in the original bounded image witness around `x`.
  have hu_bounded : Bornology.IsBounded (Set.range u) := by
    refine hbounded.subset ?_
    rintro _ ⟨n, rfl⟩
    refine (SetValuedOperator.mem_image A (Metric.ball x ρ) (u n)).2 ?_
    refine ⟨y n, ?_, hu n⟩
    have hy_ball : dist x (y n) < ρ := lt_of_lt_of_le (hyDist n) (min_le_left _ _)
    simpa [Metric.mem_ball, dist_comm] using hy_ball
  rcases bounded_sequence_has_weakly_convergent_subsequence u hu_bounded with
    ⟨v, φ, hφ, hφweak⟩
  -- The closure approximation converges strongly to `x` after passing to the subsequence.
  have hy_tendsto : Tendsto (fun n ↦ y (φ n)) atTop (nhds x) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases exists_nat_one_div_lt hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hφn : N ≤ φ n := le_trans hn (StrictMono.id_le hφ n)
    have hy_lt :
        dist (y (φ n)) x < 1 / (φ n + 1 : ℝ) := by
      have hy_lt' : dist x (y (φ n)) < 1 / (φ n + 1 : ℝ) :=
        lt_of_lt_of_le (hyDist (φ n)) (min_le_right _ _)
      simpa [dist_comm] using hy_lt'
    have hcast : (N + 1 : ℝ) ≤ φ n + 1 := by
      exact_mod_cast Nat.succ_le_succ hφn
    have hdiv : 1 / (φ n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) :=
      one_div_le_one_div_of_le (by positivity) hcast
    exact lt_trans (lt_of_lt_of_le hy_lt hdiv) hN
  have hu_sub_bounded : Bornology.IsBounded (Set.range fun n ↦ u (φ n)) := by
    refine hu_bounded.subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨φ n, rfl⟩
  have hy_sub_bounded : Bornology.IsBounded (Set.range fun n ↦ y (φ n)) :=
    Metric.isBounded_range_of_tendsto _ hy_tendsto
  have hgraph_bounded :
      Bornology.IsBounded (Set.range fun n ↦ (y (φ n), u (φ n))) := by
    refine (hy_sub_bounded.prod hu_sub_bounded).subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨⟨n, rfl⟩, ⟨n, rfl⟩⟩
  -- Graph closedness for maximally monotone operators returns a graph point over `x`.
  have hmem :
      (x, v) ∈ gra A :=
    SetValuedOperator.Maximal.mem_graph_of_tendsto_of_tendsto_weakly hA
      (fun n ↦ hu (φ n)) hgraph_bounded hy_tendsto hφweak
  exact (SetValuedOperator.mem_dom_iff A x).2 ⟨v, hmem⟩

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 21.18: boundedness on `Metric.ball x (2 * δ)` gives local boundedness at
every `z ∈ Metric.ball x δ`. -/
private lemma isLocallyBoundedAt_of_mem_ball_of_boundedImage_doubleRadius
    (A : SetValuedOperator H H) {x z : H} {δ : ℝ} (hδ : 0 < δ)
    (hB : Bornology.IsBounded (A.image (Metric.ball x (2 * δ))))
    (hz : z ∈ Metric.ball x δ) :
    A.IsLocallyBoundedAt z := by
  refine ⟨δ, hδ, hB.subset ?_⟩
  rintro u hu
  rcases (SetValuedOperator.mem_image A (Metric.ball z δ) u).1 hu with ⟨y, hy, hu⟩
  refine (SetValuedOperator.mem_image A (Metric.ball x (2 * δ)) u).2 ⟨y, ?_, hu⟩
  rw [Metric.mem_ball] at hz hy ⊢
  calc
    dist y x ≤ dist y z + dist z x := by
      simpa [dist_comm, add_comm] using (dist_triangle_right y x z)
    _ < δ + δ := by linarith
    _ = 2 * δ := by ring

/-- Helper for Theorem 21.18: local boundedness at a frontier point of `A.dom` forces the same
point to lie on the frontier of `closure A.dom`. -/
private lemma mem_frontier_closure_dom_of_mem_frontier_dom_of_isLocallyBoundedAt
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) {x : H}
    (hLoc : A.IsLocallyBoundedAt x) (hx : x ∈ frontier A.dom) :
    x ∈ frontier (closure A.dom) := by
  rcases hLoc with ⟨r, hr, hbounded⟩
  -- If `x` were interior to `closure A.dom`, nearby closure points would all land in `A.dom`.
  have hx_not_interior : x ∉ interior (closure A.dom) := by
    intro hxInterior
    rcases Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hxInterior) with ⟨s, hs, hsSubset⟩
    let δ : ℝ := min (r / 2) s
    have hδ : 0 < δ := by
      dsimp [δ]
      refine lt_min ?_ hs
      positivity
    have htwoδ_le_r : 2 * δ ≤ r := by
      dsimp [δ]
      nlinarith [min_le_left (r / 2) s]
    have hbounded_small : Bornology.IsBounded (A.image (Metric.ball x (2 * δ))) := by
      refine hbounded.subset ?_
      intro u hu
      rcases (SetValuedOperator.mem_image A (Metric.ball x (2 * δ)) u).1 hu with ⟨y, hy, huy⟩
      refine (SetValuedOperator.mem_image A (Metric.ball x r) u).2 ⟨y, ?_, huy⟩
      rw [Metric.mem_ball] at hy ⊢
      exact lt_of_lt_of_le hy htwoδ_le_r
    have hball_dom : Metric.ball x δ ⊆ A.dom := by
      intro y hy
      have hyLoc :
          A.IsLocallyBoundedAt y :=
        isLocallyBoundedAt_of_mem_ball_of_boundedImage_doubleRadius A hδ hbounded_small hy
      have hyClosure : y ∈ closure A.dom := by
        refine hsSubset ?_
        rw [Metric.mem_ball] at hy ⊢
        exact lt_of_lt_of_le hy (min_le_right _ _)
      exact mem_dom_of_isLocallyBoundedAt_of_mem_closure_dom A hA hyLoc hyClosure
    have hxDomInterior : x ∈ interior A.dom := by
      refine mem_interior_iff_mem_nhds.2 ?_
      exact Filter.mem_of_superset (Metric.ball_mem_nhds x hδ) hball_dom
    exact ((mem_frontier_iff_notMem_interior (interior_subset hxDomInterior)).1 hx) hxDomInterior
  exact (mem_frontier_iff_notMem_interior hx.1).2 hx_not_interior

omit [CompleteSpace H] in
/-- Helper for Theorem 21.18: a nonzero normal vector at a domain point forces the value set to be
unbounded. -/
private lemma not_bounded_value_of_nonzero_mem_normalCone_closure_dom
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) {z w : H}
    (hz : z ∈ A.dom) (hw : w ∈ N[closure A.dom] z) (hw0 : w ≠ 0) :
    ¬ Bornology.IsBounded (A z) := by
  intro hbounded
  obtain ⟨u, hu⟩ := (SetValuedOperator.mem_dom_iff A z).1 hz
  have hw_rec : w ∈ rec (A z) := by
    rw [recessionCone_value_eq_normalCone_closure_dom A hA hz]
    exact hw
  have hw_zero :
      w = 0 :=
    Set.eq_zero_of_mem_recessionCone_of_bounded
      (C := A z) ⟨u, hu⟩ hbounded (Maximal.value_convex hA z) hw_rec
  exact hw0 hw_zero

/-- Theorem 21.18 (Rockafellar–Veselý): if `A : H → 2^H` is maximally monotone and `x ∈ H`, then
`A` is locally bounded at `x` if and only if `x ∉ frontier A.dom`. -/
theorem isLocallyBoundedAt_iff_not_mem_frontier_dom_of_maximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x : H) :
    A.IsLocallyBoundedAt x ↔ x ∉ frontier A.dom := by
  constructor
  · intro hLoc hx
    have hxClosureFrontier :
        x ∈ frontier (closure A.dom) :=
      mem_frontier_closure_dom_of_mem_frontier_dom_of_isLocallyBoundedAt A hA hLoc hx
    rcases hLoc with ⟨r, hr, hbounded⟩
    have hhalf : 0 < r / 2 := by positivity
    rw [frontier_eq_closure_inter_closure] at hxClosureFrontier
    have hxClosure : x ∈ closure A.dom := by
      simpa [IsClosed.closure_eq isClosed_closure] using hxClosureFrontier.1
    have hC_convex : Convex ℝ (closure A.dom) := convex_closure_dom_of_maximal A hA
    have hC_cheb :
        IsChebyshev (closure A.dom) :=
      isChebyshev_of_nonempty_isClosed_convex ⟨x, hxClosure⟩ isClosed_closure hC_convex
    -- Choose a nearby point outside `closure A.dom` and project it back onto the closed convex set.
    rcases (Metric.mem_closure_iff.1 hxClosureFrontier.2) (r / 2) hhalf with ⟨y, hyOut, hyx⟩
    let z : H := projectionPoint (closure A.dom) hC_cheb y
    have hzClosure : z ∈ closure A.dom := by
      exact projectionPoint_mem (closure A.dom) hC_cheb y
    have hzNormal : y - z ∈ N[closure A.dom] z := by
      exact
        (eq_projectionPoint_iff_sub_mem_normalCone_of_nonempty_isClosed_convex
          (C := closure A.dom) ⟨x, hxClosure⟩ isClosed_closure hC_convex).1 rfl
    have hyz_le : dist y z ≤ dist y x := by
      have hbest :
          IsBestApproximation y (closure A.dom) z := by
        simpa [z] using projectionPoint_isBestApproximation (closure A.dom) hC_cheb y
      have hz_inf :
          dist y z = Metric.infDist y (closure A.dom) :=
        (isBestApproximation_iff_mem_and_dist_eq_infDist y (closure A.dom) z).1 hbest |>.2
      rw [hz_inf]
      exact Metric.infDist_le_dist_of_mem hxClosure
    have hzBall : z ∈ Metric.ball x r := by
      rw [Metric.mem_ball]
      have hyx' : dist y x < r / 2 := by
        simpa [dist_comm] using hyx
      have hyz_lt : dist y z < r / 2 := lt_of_le_of_lt hyz_le hyx'
      have hyz_lt' : dist z y < r / 2 := by
        simpa [dist_comm] using hyz_lt
      calc
        dist z x ≤ dist z y + dist y x := by
          simpa [dist_comm] using (dist_triangle_right z x y)
        _ < r / 2 + r / 2 := by
              exact add_lt_add hyz_lt' hyx'
        _ = r := by ring
    have hzLoc : A.IsLocallyBoundedAt z := by
      let ε : ℝ := (r - dist z x) / 2
      have hε : 0 < ε := by
        dsimp [ε]
        rw [Metric.mem_ball] at hzBall
        linarith
      refine ⟨ε, hε, hbounded.subset ?_⟩
      intro u hu
      rcases (SetValuedOperator.mem_image A (Metric.ball z ε) u).1 hu with ⟨v, hv, huv⟩
      refine (SetValuedOperator.mem_image A (Metric.ball x r) u).2 ⟨v, ?_, huv⟩
      rw [Metric.mem_ball] at hv hzBall ⊢
      have hzxr : dist z x < r := hzBall
      calc
        dist v x ≤ dist v z + dist z x := by
          simpa [dist_comm] using (dist_triangle_right v x z)
        _ < ε + dist z x := by linarith
        _ < r := by
              dsimp [ε]
              linarith
    have hzDom : z ∈ A.dom :=
      mem_dom_of_isLocallyBoundedAt_of_mem_closure_dom A hA hzLoc hzClosure
    have hwNeZero : y - z ≠ 0 := by
      intro hyz
      have hyEq : y = z := sub_eq_zero.mp hyz
      exact hyOut (hyEq.symm ▸ hzClosure)
    have hAz_unbounded :
        ¬ Bornology.IsBounded (A z) :=
      not_bounded_value_of_nonzero_mem_normalCone_closure_dom A hA hzDom hzNormal hwNeZero
    rcases hzLoc with ⟨ρ, hρ, hρbounded⟩
    have hzSelf : z ∈ Metric.ball z ρ := by
      simpa [Metric.mem_ball] using hρ
    have hAz_bounded : Bornology.IsBounded (A z) := by
      refine hρbounded.subset ?_
      intro u hu
      exact (SetValuedOperator.mem_image A (Metric.ball z ρ) u).2 ⟨z, hzSelf, hu⟩
    exact hAz_unbounded hAz_bounded
  · intro hx
    by_cases hxClosure : x ∈ closure A.dom
    · -- Inside `closure A.dom`, avoiding the frontier means being interior to the domain.
      have hxInterior : x ∈ interior A.dom := by
        by_contra hxNotInterior
        exact hx ⟨hxClosure, hxNotInterior⟩
      have hxFitz :
          x ∈ interior A.fstImageDomFitzpatrick :=
        interior_dom_subset_interior_fst_image_dom_fitzpatrick_of_maximal A hA hxInterior
      exact
        isLocallyBoundedAt_of_mem_interior_fst_image_dom_fitzpatrick
          A (Maximal.isMonotone hA) hxFitz
    · -- Outside `closure A.dom`, a small ball has empty image under `A`.
      have hxCompl : x ∈ (closure A.dom)ᶜ := by
        simpa using hxClosure
      rcases Metric.mem_nhds_iff.1 (isClosed_closure.isOpen_compl.mem_nhds hxCompl) with
        ⟨ε, hε, hballSubset⟩
      refine ⟨ε, hε, ?_⟩
      have himage_empty : A.image (Metric.ball x ε) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.2
        intro u hu
        rcases (SetValuedOperator.mem_image A (Metric.ball x ε) u).1 hu with ⟨y, hy, huy⟩
        have hyNotClosure : y ∉ closure A.dom := by
          exact hballSubset hy
        have hyNotDom : y ∉ A.dom := fun hyDom ↦ hyNotClosure (subset_closure hyDom)
        exact hyNotDom ((SetValuedOperator.mem_dom_iff A y).2 ⟨u, huy⟩)
      simp [himage_empty]

end SetValuedOperator
