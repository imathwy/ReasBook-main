/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

import Mathlib

universe u v

section Chap07
section Section04

section

open Filter

variable (X : Type u) [PseudoMetricSpace X]

/-- Definition 7.4.1. A sequence `{xₙ}` in a metric space is Cauchy when for
every `ε > 0` there exists `M ∈ ℕ` such that `dist (xₙ) (xₖ) < ε` for all
`n, k ≥ M`. -/
def MetricCauchySequence (x : ℕ → X) : Prop :=
  ∀ ε > 0, ∃ M : ℕ, ∀ ⦃n k : ℕ⦄, M ≤ n → M ≤ k → dist (x n) (x k) < ε

variable {X}

/-- The book's notion of a Cauchy sequence agrees with the standard filter
based definition in mathlib. -/
theorem metricCauchySequence_iff_cauchySeq (x : ℕ → X) :
    MetricCauchySequence (X := X) x ↔ CauchySeq x := by
  -- mathlib's `Metric.cauchySeq_iff` uses the same epsilon-tail formulation
  -- as the book's definition.
  constructor
  · intro hx
    refine (Metric.cauchySeq_iff (u := x)).2 ?_
    intro ε hε
    rcases hx ε hε with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro m hm n hn
    exact hM hm hn
  · intro hx ε hε
    rcases (Metric.cauchySeq_iff (u := x)).1 hx ε hε with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro n k hn hk
    exact hM n hn k hk

/-- Proposition 7.4.2. A sequence in a metric space that converges to a point
is Cauchy. -/
lemma metricCauchySequence_of_tendsto {x : ℕ → X} {l : X}
    (hx : Tendsto x atTop (nhds l)) : MetricCauchySequence (X := X) x := by
  -- A convergent sequence is Cauchy in the filter sense.
  have hxSeq : CauchySeq x := by
    simpa [CauchySeq] using
      (Filter.Tendsto.cauchy_map (f := x) (l := atTop) hx)
  exact (metricCauchySequence_iff_cauchySeq (X := X) x).2 hxSeq

end

section

open Filter

variable (X : Type u) [PseudoMetricSpace X]

/-- Definition 7.4.3. A metric space is complete (Cauchy-complete) when every
Cauchy sequence converges to a point of the space. -/
def metricCauchyCompleteSpace : Prop :=
  ∀ x : ℕ → X, MetricCauchySequence (X := X) x → ∃ l : X, Tendsto x atTop (nhds l)

/-- The book's sequential notion of completeness is equivalent to the standard
`CompleteSpace` typeclass in mathlib. -/
theorem metricCauchyCompleteSpace_iff_completeSpace :
    metricCauchyCompleteSpace (X := X) ↔ CompleteSpace X := by
  constructor
  · intro h
    refine UniformSpace.complete_of_cauchySeq_tendsto ?hseq
    intro u hu
    rcases h u ((metricCauchySequence_iff_cauchySeq (X := X) u).2 hu) with ⟨l, hl⟩
    exact ⟨l, hl⟩
  · intro hcomplete u hu
    -- Use the typeclass instance provided by `hcomplete`.
    letI := hcomplete
    have hseq : CauchySeq u :=
      (metricCauchySequence_iff_cauchySeq (X := X) u).1 hu
    rcases cauchySeq_tendsto_of_complete hseq with ⟨l, hl⟩
    exact ⟨l, hl⟩

end

/-- Proposition 7.4.4 (sequential version). Every Cauchy sequence in
`ℝ^n` converges. -/
lemma metricCauchyCompleteSpace_euclideanSpace (n : ℕ) :
    metricCauchyCompleteSpace (X := EuclideanSpace ℝ (Fin n)) := by
  -- Follows from the equivalence and the standard completeness instance.
  exact
    (metricCauchyCompleteSpace_iff_completeSpace
      (X := EuclideanSpace ℝ (Fin n))).2 inferInstance

/-- Proposition 7.4.4. The Euclidean space `ℝ^n` with its standard metric is
complete. -/
instance instCompleteSpace_realEuclideanSpace (n : ℕ) :
    CompleteSpace (EuclideanSpace ℝ (Fin n)) := by
  infer_instance

/-- Proposition 7.4.5. The metric space of continuous real-valued functions on
the closed interval `[a,b]`, equipped with the uniform norm metric, is
complete. -/
instance instCompleteSpace_continuousMap_interval (a b : ℝ) :
    CompleteSpace (ContinuousMap (Set.Icc a b) ℝ) := by
  infer_instance

/-- Proposition 7.4.6. If `(X,d)` is a complete metric space and `E ⊆ X` is
closed, then `E` is complete with the subspace metric. -/
instance instCompleteSpace_closed_subset {X : Type u} [PseudoMetricSpace X]
    [CompleteSpace X] {E : Set X} (hE : IsClosed E) : CompleteSpace E := by
  have hcomp : IsComplete E := hE.isComplete
  exact (completeSpace_coe_iff_isComplete (s := E)).2 hcomp

section

variable (X : Type u) [PseudoMetricSpace X]

/-- Definition 7.4.7. A subset `K` of a metric space is compact when every
open cover of `K` admits a finite subcover. -/
def compactCoverProperty (K : Set X) : Prop :=
  ∀ (ι : Type u) (U : ι → Set X), (∀ i, IsOpen (U i)) →
    K ⊆ ⋃ i, U i → ∃ t : Finset ι, K ⊆ ⋃ i ∈ t, U i

variable {X}

/-- The book's finite-subcover compactness property agrees with `IsCompact`. -/
theorem compactCoverProperty_iff_isCompact {K : Set X} :
    compactCoverProperty (X := X) K ↔ IsCompact K := by
  classical
  simpa [compactCoverProperty] using
    (isCompact_iff_finite_subcover (s := K)).symm

end

/-- Example 7.4.8. In `ℝ` with the standard metric: (i) the whole space `ℝ`
is not compact; (ii) the open interval `(0,1)` is not compact; (iii) the
singleton `{0}` is compact. -/
theorem real_univ_not_compact : ¬ IsCompact (Set.univ : Set ℝ) := by
  simpa using (noncompact_univ (X := ℝ))

/-- See also: Example 7.4.8 (ii). -/
theorem real_Ioo_zero_one_not_compact : ¬ IsCompact (Set.Ioo (0 : ℝ) 1) := by
  intro h
  have hclosed : IsClosed (Set.Ioo (0 : ℝ) 1) := h.isClosed
  have h0 : (0 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    have hclosure :
        closure (Set.Ioo (0 : ℝ) 1) = Set.Icc (0 : ℝ) 1 := by
      simpa using
        (closure_Ioo (a := (0 : ℝ)) (b := 1)
          (zero_ne_one : (0 : ℝ) ≠ 1))
    have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> norm_num
    exact hclosure ▸ hmem
  have hnot : (0 : ℝ) ∉ Set.Ioo (0 : ℝ) 1 := by simp
  exact hnot (hclosed.closure_subset h0)

/-- See also: Example 7.4.8 (iii). -/
theorem real_singleton_zero_compact : IsCompact ({0} : Set ℝ) := by
  simp

open Filter
open scoped Topology

lemma compact_isClosed {X : Type u} [PseudoMetricSpace X] [T2Space X]
    {K : Set X} (hK : IsCompact K) : IsClosed K := by
  simpa using hK.isClosed

lemma compact_isBounded {X : Type u} [PseudoMetricSpace X]
    {K : Set X} (hK : IsCompact K) : Bornology.IsBounded K := by
  simpa using hK.isBounded

/-- Proposition 7.4.9. In a metric space, a compact subset is closed and
bounded. -/
theorem compact_isClosed_and_bounded {X : Type u} [PseudoMetricSpace X]
    [T2Space X]
    {K : Set X} (hK : IsCompact K) : IsClosed K ∧ Bornology.IsBounded K := by
  exact ⟨compact_isClosed (K := K) hK, compact_isBounded (K := K) hK⟩

/-- Lemma 7.4.10 (Lebesgue covering lemma). If every sequence in a subset `K`
of a metric space has a subsequence converging to a point of `K`, then for
every open cover of `K` there exists `δ > 0` such that every `x ∈ K` has some
open set in the cover containing the ball `B(x, δ)`. -/
lemma lebesgue_covering_lemma {X : Type u} [PseudoMetricSpace X] {K : Set X}
    (hseq : ∀ u : ℕ → X, (∀ n, u n ∈ K) →
      ∃ l ∈ K, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 l))
    {I : Type v} (U : I → Set X) (hUopen : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ δ > 0, ∀ x ∈ K, ∃ i : I, Metric.ball x δ ⊆ U i := by
  classical
  by_contra hδ
  -- There is no positive Lebesgue number; extract a sequence witnessing the failure.
  push_neg at hδ
  have hbad :
      ∀ n : ℕ, ∃ x ∈ K, ∀ i : I,
        ¬ Metric.ball x (1 / (n + 1 : ℝ)) ⊆ U i := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by
      have hden : (0 : ℝ) < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
      exact one_div_pos.mpr hden
    simpa using hδ (1 / (n + 1 : ℝ)) hpos
  choose x hxK hxSub using hbad
  -- Extract a convergent subsequence from `x`.
  rcases hseq x hxK with ⟨l, hlK, φ, hφmono, hφconv⟩
  -- Choose the cover set containing the limit.
  have hlinU : l ∈ ⋃ i, U i := hcover hlK
  rcases Set.mem_iUnion.mp hlinU with ⟨i0, hli0⟩
  have hUopen0 : IsOpen (U i0) := hUopen i0
  have hnhds : U i0 ∈ 𝓝 l := hUopen0.mem_nhds hli0
  rcases Metric.mem_nhds_iff.1 hnhds with ⟨ε, hεpos, hεball⟩
  -- Convergence of the subsequence and shrinking radii.
  have hconv : ∀ᶠ n in atTop, dist (x (φ n)) l < ε / 2 := by
    have hmem : Metric.ball l (ε / 2) ∈ 𝓝 l := by
      have hpos : (0 : ℝ) < ε / 2 := by linarith
      exact Metric.ball_mem_nhds _ hpos
    have h :
        ∀ᶠ n in atTop, x (φ n) ∈ Metric.ball l (ε / 2) :=
      (tendsto_def.1 hφconv) (Metric.ball l (ε / 2)) hmem
    exact h.mono (by
      intro n hn
      simpa [Metric.mem_ball] using hn)
  have hdiv_tendsto :
      Tendsto (fun n : ℕ => (1 : ℝ) / (φ n + 1)) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      hφmono.tendsto_atTop
  have hsmall :
      ∀ᶠ n in atTop, (1 : ℝ) / (φ n + 1 : ℝ) < ε / 2 := by
    have hmem : Set.Iio (ε / 2) ∈ 𝓝 (0 : ℝ) := by
      have hpos : (0 : ℝ) < ε / 2 := by linarith
      exact Iio_mem_nhds hpos
    have h :
        ∀ᶠ n in atTop, (1 : ℝ) / (φ n + 1 : ℝ) ∈ Set.Iio (ε / 2) :=
      (tendsto_def.1 hdiv_tendsto) (Set.Iio (ε / 2)) hmem
    exact h.mono (by
      intro n hn
      simpa using hn)
  -- Eventually the balls of the subsequence fit in `U i0`.
  have hsubset :
      ∀ᶠ n in atTop,
        Metric.ball (x (φ n)) (1 / (φ n + 1 : ℝ)) ⊆ U i0 := by
    refine (hconv.and hsmall).mono ?_
    intro n hn z hz
    rcases hn with ⟨hxlim, hradius⟩
    have hzdist : dist z (x (φ n)) < 1 / (φ n + 1 : ℝ) := by
      simpa [Metric.mem_ball] using hz
    have htriangle :
        dist z l ≤ dist z (x (φ n)) + dist (x (φ n)) l :=
      dist_triangle _ _ _
    have hsum :
        dist z (x (φ n)) + dist (x (φ n)) l <
          1 / (φ n + 1 : ℝ) + ε / 2 :=
      add_lt_add hzdist hxlim
    have hltε : dist z l < ε := by
      apply lt_of_le_of_lt htriangle
      have hε : 1 / (φ n + 1 : ℝ) + ε / 2 < ε := by linarith
      exact lt_trans hsum hε
    have hzball : z ∈ Metric.ball l ε := by
      simpa [Metric.mem_ball] using hltε
    exact hεball hzball
  rcases (eventually_atTop.1 hsubset) with ⟨N, hN⟩
  have hcontr : Metric.ball (x (φ N)) (1 / (φ N + 1 : ℝ)) ⊆ U i0 :=
    hN N le_rfl
  exact (hxSub (φ N) i0) hcontr

/-- Theorem 7.4.11. In a metric space, a subset is compact if and only if every
sequence in the subset has a subsequence converging to a point of the subset. -/
theorem compact_iff_isSeqCompact {X : Type u} [PseudoMetricSpace X]
    {K : Set X} : IsCompact K ↔ IsSeqCompact K := by
  simpa using (UniformSpace.isCompact_iff_isSeqCompact (s := K) (X := X))

/-- Example 7.4.12. A closed bounded interval `[a,b] ⊆ ℝ` is sequentially
compact: every sequence in `Set.Icc a b` admits a convergent subsequence with
limit still in the interval. -/
theorem real_interval_isSeqCompact (a b : ℝ) :
    IsSeqCompact (Set.Icc a b) := by
  simpa using
    (isCompact_Icc : IsCompact (Set.Icc a b)).isSeqCompact

/-- Proposition 7.4.13. In a metric space, a closed subset of a compact set is
compact. -/
theorem compact_of_closed_subset {X : Type u} [PseudoMetricSpace X]
    {K E : Set X} (hK : IsCompact K) (hE : IsClosed E) (hEK : E ⊆ K) :
    IsCompact E := by
  exact hK.of_isClosed_subset hE hEK

/-- Theorem 7.4.14 (Heine--Borel). A closed bounded subset `K ⊆ ℝ^n` is
compact. -/
theorem heineBorel_closed_bounded {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hclosed : IsClosed K) (hbounded : Bornology.IsBounded K) :
    IsCompact K := by
  rcases hbounded.subset_closedBall
      (c := (0 : EuclideanSpace ℝ (Fin n))) with ⟨R, hsubset⟩
  have hcompact :
      IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) :=
    isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R
  exact hcompact.of_isClosed_subset hclosed hsubset

/-! Example 7.4.15. Let `X` be an infinite set endowed with the discrete
metric `dist x y = 1` for `x ≠ y`. Then:
(i) the space is complete;
(ii) every subset `K ⊆ X` is closed and bounded;
(iii) a subset `K` is compact if and only if it is finite;
(iv) the Lebesgue covering lemma holds for any `K` with `δ = 1/2`, even when
`K` is not compact. -/
section

variable {X : Type u} [PseudoMetricSpace X] [DecidableEq X]
variable (hdiscrete : ∀ x y : X, dist x y = (if x = y then 0 else 1))
variable (hXinf : Infinite X)

lemma discreteMetric_dist_lt_one_iff_eq
    (hdiscrete : ∀ x y : X, dist x y = (if x = y then 0 else 1))
    {x y : X} :
    dist x y < 1 ↔ x = y := by
  classical
  by_cases hxy : x = y
  · subst hxy
    simp
  · have hval : dist x y = 1 := by simpa [hxy] using hdiscrete x y
    constructor
    · intro hlt
      have : False := by linarith
      exact this.elim
    · intro hcontr
      exact (hxy hcontr).elim

lemma discreteMetric_ball_eq_singleton
    (hdiscrete : ∀ x y : X, dist x y = (if x = y then 0 else 1))
    (x : X) {r : ℝ}
    (hrpos : 0 < r) (hrle : r ≤ 1) :
    Metric.ball x r = ({x} : Set X) := by
  classical
  ext y
  constructor
  · intro hy
    have hy' : dist y x < 1 :=
      lt_of_lt_of_le (by simpa [Metric.mem_ball] using hy) hrle
    have hy_eq :
        y = x :=
      (discreteMetric_dist_lt_one_iff_eq (X := X) hdiscrete).1 hy'
    simp [hy_eq]
  · intro hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    have hpos : (0 : ℝ) < r := hrpos
    simpa [Metric.mem_ball] using hpos

lemma discreteMetric_cauchySeq_eventually_const
    (hdiscrete : ∀ x y : X, dist x y = (if x = y then 0 else 1))
    (u : ℕ → X)
    (hu : CauchySeq u) :
    ∃ x0, u =ᶠ[atTop] fun _ => x0 := by
  classical
  rcases (Metric.cauchySeq_iff (u := u)).1 hu (1 / 2 : ℝ) (by norm_num) with
    ⟨M, hM⟩
  refine ⟨u M, ?_⟩
  refine (eventually_atTop.2 ⟨M, ?_⟩)
  intro n hn
  have hdist : dist (u n) (u M) < (1 / 2 : ℝ) := hM n hn M le_rfl
  have hlt : dist (u n) (u M) < 1 := lt_of_lt_of_le hdist (by norm_num)
  exact (discreteMetric_dist_lt_one_iff_eq (X := X) hdiscrete).1 hlt

theorem discreteMetric_complete
    (hdiscrete : ∀ x y : X, dist x y = (if x = y then 0 else 1)) :
    CompleteSpace X := by
  classical
  refine (metricCauchyCompleteSpace_iff_completeSpace (X := X)).1 ?_
  intro u hu
  have hC : CauchySeq u := (metricCauchySequence_iff_cauchySeq (X := X) u).1 hu
  rcases
      discreteMetric_cauchySeq_eventually_const (X := X) hdiscrete u hC with
    ⟨x0, hx0⟩
  have hconst : Tendsto (fun _ : ℕ => x0) atTop (𝓝 x0) := tendsto_const_nhds
  have hlim :
      Tendsto u atTop (𝓝 x0) :=
    (tendsto_congr' (hx0.symm : (fun _ : ℕ => x0) =ᶠ[atTop] u)).mp hconst
  exact ⟨x0, hlim⟩

theorem discreteMetric_closed_and_bounded
    (hdiscrete : ∀ x y : X, dist x y = (if x = y then 0 else 1))
    (hXinf : Infinite X) (K : Set X) :
    IsClosed K ∧ Bornology.IsBounded K := by
  classical
  have hOpen : IsOpen K := by
    refine isOpen_iff_mem_nhds.mpr ?_
    intro x hxK
    have hsubset : Metric.ball x (1 / 2 : ℝ) ⊆ K := by
      intro y hy
      have hy' :
          y = x :=
        (discreteMetric_dist_lt_one_iff_eq (X := X) hdiscrete).1
          (lt_of_lt_of_le hy (by norm_num))
      simp [hy', hxK]
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
    have hballmem : Metric.ball x (1 / 2 : ℝ) ∈ 𝓝 x :=
      Metric.ball_mem_nhds _ hpos
    exact mem_of_superset hballmem hsubset
  have hOpenCompl : IsOpen Kᶜ := by
    refine isOpen_iff_mem_nhds.mpr ?_
    intro x hxKc
    have hsubset : Metric.ball x (1 / 2 : ℝ) ⊆ Kᶜ := by
      intro y hy
      have hy' :
          y = x :=
        (discreteMetric_dist_lt_one_iff_eq (X := X) hdiscrete).1
          (lt_of_lt_of_le hy (by norm_num))
      have hxnot : x ∉ K := by simpa using hxKc
      have hynot : y ∉ K := by simpa [hy'] using hxnot
      simpa using hynot
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
    have hballmem : Metric.ball x (1 / 2 : ℝ) ∈ 𝓝 x :=
      Metric.ball_mem_nhds _ hpos
    exact mem_of_superset hballmem hsubset
  have hClosed : IsClosed K := by
    simpa using hOpenCompl.isClosed_compl
  let x0 : X := Classical.choice hXinf.nonempty
  have hsubset : K ⊆ Metric.closedBall x0 1 := by
    intro x hx
    have hle : dist x x0 ≤ 1 := by
      have h := hdiscrete x x0
      by_cases hxx0 : x = x0
      · subst hxx0
        have : dist x0 x0 = (0 : ℝ) := dist_self _
        linarith
      · have hval : dist x x0 = 1 := by simpa [hxx0] using h
        linarith
    simpa [Metric.mem_closedBall] using hle
  have hbounded :
      Bornology.IsBounded K :=
    (Metric.isBounded_iff_subset_closedBall (c := x0) (s := K)).2
      ⟨1, hsubset⟩
  exact ⟨hClosed, hbounded⟩

theorem discreteMetric_compact_iff_finite
    (hdiscrete : ∀ x y : X, dist x y = (if x = y then 0 else 1))
    (K : Set X) :
    IsCompact K ↔ Set.Finite K := by
  classical
  constructor
  · intro hK
    let U : K → Set X := fun k => ({(k : X)} : Set X)
    have hUopen : ∀ k : K, IsOpen (U k) := by
      intro k
      have hball :
          Metric.ball (k : X) (1 / 2 : ℝ) = ({(k : X)} : Set X) :=
        discreteMetric_ball_eq_singleton (X := X) hdiscrete (k : X)
          (by norm_num) (by norm_num)
      have hsingleton : IsOpen ({(k : X)} : Set X) :=
        hball ▸ (Metric.isOpen_ball :
          IsOpen (Metric.ball (k : X) (1 / 2 : ℝ)))
      simpa [U] using hsingleton
    have hcover : K ⊆ ⋃ k : K, U k := by
      intro x hx
      refine Set.mem_iUnion.2 ?_
      refine ⟨⟨x, hx⟩, ?_⟩
      simp [U]
    rcases hK.elim_finite_subcover (U := U) hUopen hcover with ⟨t, hsub⟩
    have hfinite_image :
        (Set.Finite (Subtype.val '' (t : Set K))) :=
      (t.finite_toSet.image Subtype.val)
    have hsubset : K ⊆ Subtype.val '' (t : Set K) := by
      intro x hx
      have hx' := hsub hx
      rcases Set.mem_iUnion.mp hx' with ⟨k, hk⟩
      rcases Set.mem_iUnion.mp hk with ⟨hkt, hxk⟩
      have hx_eq : x = k := by
        have : x ∈ ({(k : X)} : Set X) := hxk
        simpa using this
      have hk' : k ∈ (t : Set K) := by simpa using hkt
      refine hx_eq ▸ ?_
      exact Set.mem_image_of_mem Subtype.val hk'
    exact hfinite_image.subset hsubset
  · intro hfin
    simpa using hfin.isCompact

theorem discreteMetric_lebesgue_covering
    (hdiscrete : ∀ x y : X, dist x y = (if x = y then 0 else 1))
    (K : Set X)
    {I : Type v} (U : I → Set X) (hUopen : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i, U i) :
    ∀ x ∈ K, ∃ i : I, Metric.ball x (1 / 2 : ℝ) ⊆ U i := by
  classical
  intro x hxK
  have hxU : x ∈ ⋃ i, U i := hcover hxK
  rcases Set.mem_iUnion.mp hxU with ⟨i, hi⟩
  have hUi : IsOpen (U i) := hUopen i
  refine ⟨i, ?_⟩
  intro y hy
  have hy' :
      y = x :=
    (discreteMetric_dist_lt_one_iff_eq (X := X) hdiscrete).1
      (lt_of_lt_of_le hy (by norm_num))
  simpa [hy'] using hi

end

end Section04
end Chap07
