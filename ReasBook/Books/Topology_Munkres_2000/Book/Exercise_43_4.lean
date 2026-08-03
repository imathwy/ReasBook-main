module

public import Mathlib.Topology.MetricSpace.Bounded

public section

open Filter Set

universe u

/-- Helper for Exercise 43.4: every finite initial intersection of an antitone
sequence of nonempty sets is nonempty. -/
private lemma nonempty_biInter_le_of_antitone {X : Type u} {A : ℕ → Set X}
    (h_antitone : Antitone A) (h_nonempty : ∀ n, (A n).Nonempty) (N : ℕ) :
    (⋂ n ≤ N, A n).Nonempty := by
  -- A point of the last set belongs to every preceding set by antitonicity.
  obtain ⟨x, hx⟩ := h_nonempty N
  refine ⟨x, mem_iInter.mpr fun n ↦ mem_iInter.mpr fun hn ↦ ?_⟩
  exact h_antitone hn hx

/-- Helper for Exercise 43.4: a pairwise distance bound on a sequence tail
extends to every pair of points in its closure. -/
private lemma dist_le_of_mem_closure_image_Ici {X : Type u} [MetricSpace X]
    (u : ℕ → X) (b : ℕ → ℝ)
    (h_control : ∀ N m n, N ≤ m → N ≤ n → dist (u m) (u n) ≤ b N)
    (N : ℕ) {x y : X} (hx : x ∈ closure (u '' Ici N))
    (hy : y ∈ closure (u '' Ici N)) : dist x y ≤ b N := by
  -- Continuity of distance carries the tail estimate through both closures.
  have h_dist : dist x y ∈ closure (Iic (b N)) := by
    apply map_mem_closure₂ continuous_dist hx hy
    rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
    exact h_control N m n hm hn
  exact isClosed_Iic.closure_subset h_dist

/-- Helper for Exercise 43.4: closed tails controlled by a radius tending to
zero have diameters tending to zero. -/
private lemma tendsto_diam_closure_image_Ici {X : Type u} [MetricSpace X]
    (u : ℕ → X) (b : ℕ → ℝ) (h_b : Tendsto b atTop (nhds 0))
    (h_control : ∀ N m n, N ≤ m → N ≤ n → dist (u m) (u n) ≤ b N) :
    Tendsto (fun n ↦ Metric.diam (closure (u '' Ici n))) atTop (nhds 0) := by
  -- Reflexivity of the tail estimate shows that every controlling radius is nonnegative.
  have h_nonneg : ∀ n, 0 ≤ b n := by
    intro n
    simpa only [dist_self] using h_control n n n le_rfl le_rfl
  -- The pairwise closure estimate squeezes each diameter below the original modulus.
  apply squeeze_zero (fun n ↦ Metric.diam_nonneg)
    (fun n ↦ Metric.diam_le_of_forall_dist_le (h_nonneg n)
      (fun x hx y hy ↦ dist_le_of_mem_closure_image_Ici u b h_control n hx hy))
  exact h_b

/-- Exercise 43.4: A metric space is complete if and only if every antitone sequence
of nonempty closed bounded sets whose diameters tend to zero has nonempty intersection. -/
theorem completeSpace_iff_nested_closed_iInter {X : Type u} [MetricSpace X] :
    CompleteSpace X ↔
      ∀ (A : ℕ → Set X) (h_antitone : Antitone A) (h_nonempty : ∀ n, (A n).Nonempty)
        (h_closed : ∀ n, IsClosed (A n)) (h_bounded : ∀ n, Bornology.IsBounded (A n))
        (h_diam : Tendsto (fun n ↦ Metric.diam (A n)) atTop (nhds 0)),
        (⋂ n, A n).Nonempty := by
  constructor
  · intro h_complete A h_antitone h_nonempty h_closed h_bounded h_diam
    -- Completeness turns the finite-intersection property into a total intersection point.
    letI : CompleteSpace X := h_complete
    apply Metric.nonempty_iInter_of_nonempty_biInter h_closed h_bounded
      (nonempty_biInter_le_of_antitone h_antitone h_nonempty)
    exact h_diam
  · intro h_nested
    -- It suffices to make every Cauchy sequence converge.
    apply Metric.complete_of_cauchySeq_tendsto
    intro u hu
    obtain ⟨b, -, h_bound, h_b⟩ := cauchySeq_iff_le_tendsto_0.mp hu
    have h_tail_control :
        ∀ N m n, N ≤ m → N ≤ n → dist (u m) (u n) ≤ b N := by
      intro N m n hm hn
      exact h_bound m n N hm hn
    let A : ℕ → Set X := fun n ↦ closure (u '' Ici n)
    have h_antitone : Antitone A := by
      intro n m hnm
      exact closure_mono (image_mono (Ici_subset_Ici.mpr hnm))
    have h_nonempty : ∀ n, (A n).Nonempty := by
      intro n
      refine ⟨u n, subset_closure ?_⟩
      exact ⟨n, self_mem_Ici, rfl⟩
    have h_closed : ∀ n, IsClosed (A n) := fun n ↦ isClosed_closure
    have h_bounded : ∀ n, Bornology.IsBounded (A n) := by
      intro n
      exact (hu.isBounded_range.subset (image_subset_range u (Ici n))).closure
    have h_diam : Tendsto (fun n ↦ Metric.diam (A n)) atTop (nhds 0) :=
      tendsto_diam_closure_image_Ici u b h_b h_tail_control
    -- A point in all closed tails is a cluster point, hence the limit of the Cauchy sequence.
    obtain ⟨x, hx⟩ := h_nested A h_antitone h_nonempty h_closed h_bounded h_diam
    refine ⟨x, le_nhds_of_cauchy_adhp hu ?_⟩
    exact mapClusterPt_atTop_iff_forall_mem_closure.mpr (mem_iInter.mp hx)
