import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap01.Text_1_0_14
import BauschkeLean.Chap17.Proposition_17_39.SelectionContinuity
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap21.Theorem_21_18

open Filter
open scoped InnerProductSpace

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Source/core/bridge triage:
-- - `source-facing`: Corollary 21.21 is the interior-domain strong-to-weak continuity statement
--   for an at-most-single-valued maximally monotone operator.
-- - `core/canonical`: the continuity owner is `SelectionContinuousAt A`, and the local regularity
--   owner used to reach it is `A.IsLocallyBoundedAt x`.
-- - `bridge/view`: the reusable local bridge isolates the pointwise hypothesis actually used in
--   the continuity argument, namely local boundedness together with a singleton fiber at `x`.
--
-- Semantic recall: `lean_leansearch` only surfaced unrelated weak-operator-topology results, so
-- the source-facing owner stays a selection-based weak continuity statement on `interior A.dom`,
-- verified against Chapter 17's `SelectionContinuousAt` API and the local Chapter 21 precedent.

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 21.21: local boundedness at the base point bounds the values of any
selection along a domain sequence converging to that point. -/
private lemma boundedRange_selectionValues_of_tendsto_of_isLocallyBoundedAt
    (A : SetValuedOperator H H) {x0 : A.dom} (hLoc : A.IsLocallyBoundedAt (x0 : H))
    (G : Selection A) {z : ℕ → A.dom} (hz : Tendsto z atTop (nhds x0)) :
    Bornology.IsBounded (Set.range fun n ↦ (G (z n) : H)) := by
  -- Pass from convergence in the domain subtype to convergence in the ambient Hilbert space.
  have hz_base : Tendsto (fun n ↦ (z n : H)) atTop (nhds (x0 : H)) := by
    simpa using (continuous_subtype_val.tendsto x0).comp hz
  rcases hLoc with ⟨ρ, hρ, hbounded⟩
  have htail : ∀ᶠ n in atTop, (z n : H) ∈ Metric.ball (x0 : H) ρ := by
    exact hz_base.eventually (Metric.ball_mem_nhds (x0 : H) hρ)
  rcases eventually_atTop.mp htail with ⟨N, hN⟩
  let s0 : Set H := (fun n ↦ (G (z n) : H)) '' {n : ℕ | n < N}
  have hs0_finite : s0.Finite := by
    classical
    simpa [s0] using (Set.finite_lt_nat N).image (fun n ↦ (G (z n) : H))
  have hrange_subset :
      Set.range (fun n ↦ (G (z n) : H)) ⊆ s0 ∪ A.image (Metric.ball (x0 : H) ρ) := by
    rintro v ⟨n, rfl⟩
    by_cases hn : n < N
    · exact Or.inl ⟨n, hn, rfl⟩
    · exact Or.inr <|
        (SetValuedOperator.mem_image A (Metric.ball (x0 : H) ρ) (G (z n) : H)).2
          ⟨(z n : H), hN n (Nat.le_of_not_lt hn), selection_apply_mem G (z n)⟩
  -- Split the range into a finite prefix and the bounded local image furnished by `hLoc`.
  exact (hs0_finite.isBounded.union hbounded).subset hrange_subset

omit [CompleteSpace H] in
/-- Helper for Corollary 21.21: every weak sequential cluster point of selection values along a
strongly convergent domain sequence lies in the limiting fiber of a maximally monotone operator. -/
private lemma mem_fiber_of_weakClusterPoint_selectionValues_of_tendsto
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) {x0 : A.dom}
    (hLoc : A.IsLocallyBoundedAt (x0 : H)) (G : Selection A) {z : ℕ → A.dom}
    (hz : Tendsto z atTop (nhds x0)) {w : H}
    (hw :
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (G (z n) : H)) (toWeakSpace ℝ H w)) :
    w ∈ A (x0 : H) := by
  rcases hw.exists_subseq_tendsto with ⟨φ, hφ, hφw⟩
  have hzφ : Tendsto (fun n ↦ z (φ n)) atTop (nhds x0) :=
    hz.comp hφ.tendsto_atTop
  -- The subsequence still converges strongly to the same base point in the primal variable.
  have hzφ_base : Tendsto (fun n ↦ ((z (φ n)) : H)) atTop (nhds (x0 : H)) := by
    simpa using (continuous_subtype_val.tendsto x0).comp hzφ
  have hbounded_values :
      Bornology.IsBounded (Set.range fun n ↦ (G (z (φ n)) : H)) := by
    refine
      (boundedRange_selectionValues_of_tendsto_of_isLocallyBoundedAt A hLoc G hz).subset ?_
    rintro v ⟨n, rfl⟩
    exact ⟨φ n, rfl⟩
  have hbounded_domain :
      Bornology.IsBounded (Set.range fun n ↦ ((z (φ n)) : H)) :=
    Metric.isBounded_range_of_tendsto _ hzφ_base
  have hbounded_graph :
      Bornology.IsBounded (Set.range fun n ↦ (((z (φ n)) : H), (G (z (φ n)) : H))) := by
    refine (hbounded_domain.prod hbounded_values).subset ?_
    rintro p ⟨n, rfl⟩
    exact ⟨⟨n, rfl⟩, ⟨n, rfl⟩⟩
  have hgraph : ∀ n, (((z (φ n)) : H), (G (z (φ n)) : H)) ∈ gra A := by
    intro n
    exact selection_apply_mem G (z (φ n))
  -- Closedness of the graph under strong-weak convergence identifies the limiting value.
  have hmem_graph :
      ((x0 : H), w) ∈ gra A :=
    SetValuedOperator.Maximal.mem_graph_of_tendsto_of_tendsto_weakly hA hgraph hbounded_graph
      hzφ_base (by simpa [Function.comp] using hφw)
  simpa using hmem_graph

/-- Helper for Corollary 21.21: if the fiber over the limit point is a singleton, then the
selection values along any strongly convergent domain sequence converge weakly to that value. -/
private lemma selectionValues_tendsto_toWeakSpace_of_subsingleton_fiber
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) {x0 : A.dom}
    (hLoc : A.IsLocallyBoundedAt (x0 : H)) (hsinglex : (A (x0 : H)).Subsingleton)
    (G : Selection A) {z : ℕ → A.dom} (hz : Tendsto z atTop (nhds x0)) :
    Tendsto (fun n ↦ toWeakSpace ℝ H (G (z n) : H)) atTop
      (nhds (toWeakSpace ℝ H (G x0 : H))) := by
  have hbounded :
      Bornology.IsBounded (Set.range fun n ↦ (G (z n) : H)) :=
    boundedRange_selectionValues_of_tendsto_of_isLocallyBoundedAt A hLoc G hz
  have hcluster_eq :
      ∀ w : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (G (z n) : H))
          (toWeakSpace ℝ H w) →
        w = (G x0 : H) := by
    intro w hw
    have hwmem :
        w ∈ A (x0 : H) :=
      mem_fiber_of_weakClusterPoint_selectionValues_of_tendsto A hA hLoc G hz hw
    have hGmem : (G x0 : H) ∈ A (x0 : H) := selection_apply_mem G x0
    exact hsinglex hwmem hGmem
  -- Lemma 2.46 upgrades boundedness plus uniqueness of weak cluster points to weak convergence.
  rcases
      (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint
        (fun n ↦ (G (z n) : H))).2
        ⟨hbounded, fun y w hy hw ↦ by
          calc
            y = (G x0 : H) := hcluster_eq y hy
            _ = w := (hcluster_eq w hw).symm⟩ with
    ⟨w, hw⟩
  have hw_cluster :
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (G (z n) : H))
        (toWeakSpace ℝ H w) := by
    exact ⟨id, strictMono_id, by simpa using hw⟩
  have hw_eq : w = (G x0 : H) := hcluster_eq w hw_cluster
  simpa [hw_eq] using hw

/-- Local weak-continuity bridge for Chapter 21: if `A` is maximally monotone, locally bounded at
`x`, and has a singleton value set at `x`, then every selection of `A` is strong-to-weak
continuous at `x`. -/
theorem selectionContinuousAt_toWeakSpace_of_isLocallyBoundedAt_of_maximal_of_subsingleton
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) {x : H}
    (hLoc : A.IsLocallyBoundedAt x) (hsinglex : (A x).Subsingleton) :
    ∀ G : Selection A,
      SelectionContinuousAt A (fun z : A.dom ↦ toWeakSpace ℝ H (G z : H)) x := by
  intro G hxdom
  let x0 : A.dom := ⟨x, hxdom⟩
  have hcont0 :
      ContinuousAt (fun z : A.dom ↦ toWeakSpace ℝ H (G z : H)) x0 := by
    -- The subtype domain is first countable, so sequence convergence suffices for continuity.
    apply Filter.tendsto_of_seq_tendsto
    intro z hz
    simpa [Function.comp, x0] using
      selectionValues_tendsto_toWeakSpace_of_subsingleton_fiber A hA (x0 := x0)
        (by simpa [x0] using hLoc) (by simpa [x0] using hsinglex) G hz
  have hxeq : (⟨x, hxdom⟩ : A.dom) = x0 := by
    apply Subtype.ext
    rfl
  -- Transport the continuity statement back to the specific subtype point over `x`.
  simpa [x0, hxeq] using hcont0

/-- Corollary 21.21: let `A : H → 2^H` be maximally monotone and at most single-valued. Then `A`
is strong-to-weak continuous everywhere on `interior A.dom`, expressed as weak continuity at each
interior-domain point of every selection of `A`. -/
theorem selectionContinuousAt_toWeakSpace_of_mem_interior_dom_of_maximal_of_isAtMostSingleValued
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (hsingle : A.IsAtMostSingleValued) {x : H} (hx : x ∈ interior A.dom) :
    ∀ G : Selection A,
      SelectionContinuousAt A (fun z : A.dom ↦ toWeakSpace ℝ H (G z : H)) x := by
  have hLoc : A.IsLocallyBoundedAt x := by
    refine (isLocallyBoundedAt_iff_not_mem_frontier_dom_of_maximal A hA x).2 ?_
    have hxdom : x ∈ A.dom := interior_subset hx
    rw [mem_frontier_iff_notMem_interior hxdom]
    exact not_not_intro hx
  exact
    selectionContinuousAt_toWeakSpace_of_isLocallyBoundedAt_of_maximal_of_subsingleton
      A hA hLoc (hsingle x)

end SetValuedOperator
