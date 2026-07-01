/-
  Copyright (c) 2026 Zichen Wang. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
  -/

import Mathlib
import Books.Analysis2_Tao_2022.Chapters.Chap04.section02_part1

open Classical

section Chap04
section Section02

/-- Helper for Proposition 4.2.3: `|x|` is not real analytic at `0`. -/
lemma helperForProposition_4_2_3_notAnalyticAt_zero_abs :
    ¬AnalyticAt ℝ (fun x : ℝ => |x|) 0 := by
  intro hAnalytic
  have hDiffAbs : DifferentiableAt ℝ (fun x : ℝ => |x|) 0 := by
    simpa using hAnalytic.differentiableAt
  exact
    (not_differentiableAt_abs_zero : ¬DifferentiableAt ℝ (fun x : ℝ => |x|) 0) hDiffAbs

/-- Helper for Proposition 4.2.3: at positive points, `|x|` agrees locally with `x`. -/
lemma helperForProposition_4_2_3_eventuallyEq_abs_id_of_pos
    {a : ℝ} (ha : 0 < a) :
    (fun x : ℝ => |x|) =ᶠ[nhds a] (fun x : ℝ => x) := by
  filter_upwards [Ioi_mem_nhds ha] with x hx
  have hxPos : 0 < x := by
    simpa using hx
  simp [abs_of_pos hxPos]

/-- Helper for Proposition 4.2.3: at negative points, `|x|` agrees locally with `-x`. -/
lemma helperForProposition_4_2_3_eventuallyEq_abs_negId_of_neg
    {a : ℝ} (ha : a < 0) :
    (fun x : ℝ => |x|) =ᶠ[nhds a] (fun x : ℝ => -x) := by
  filter_upwards [Iio_mem_nhds ha] with x hx
  have hxNeg : x < 0 := by
    simpa using hx
  simp [abs_of_neg hxNeg]

/-- Helper for Proposition 4.2.3: `|x|` is real analytic at every nonzero real point. -/
lemma helperForProposition_4_2_3_analyticAt_abs_of_ne_zero
    {a : ℝ} (ha : a ≠ 0) :
    AnalyticAt ℝ (fun x : ℝ => |x|) a := by
  have hzero : 0 ≠ a := ha.symm
  rcases lt_or_gt_of_ne hzero with hpos | hneg
  · have hEq : (fun x : ℝ => x) =ᶠ[nhds a] (fun x : ℝ => |x|) :=
      (helperForProposition_4_2_3_eventuallyEq_abs_id_of_pos hpos).symm
    exact (analyticAt_id (𝕜 := ℝ) (z := a)).congr hEq
  · have hEq : (fun x : ℝ => -x) =ᶠ[nhds a] (fun x : ℝ => |x|) :=
      (helperForProposition_4_2_3_eventuallyEq_abs_negId_of_neg hneg).symm
    have hNegId : AnalyticAt ℝ (fun x : ℝ => -x) a :=
      (analyticAt_id (𝕜 := ℝ) (z := a)).neg
    exact hNegId.congr hEq

/-- Proposition 4.2.3: for `f(x) = |x|`, the function is not differentiable at `0`, hence
not real analytic at `0`; moreover, for every `a ≠ 0`, `f` is real analytic at `a`. -/
theorem abs_notDifferentiableAt_zero_notAnalyticAt_zero_analyticAt_nonzero :
    ¬DifferentiableAt ℝ (fun x : ℝ => |x|) 0 ∧
      ¬AnalyticAt ℝ (fun x : ℝ => |x|) 0 ∧
        ∀ a : ℝ, a ≠ 0 → AnalyticAt ℝ (fun x : ℝ => |x|) a := by
  constructor
  · simpa using
      (not_differentiableAt_abs_zero : ¬DifferentiableAt ℝ (fun x : ℝ => |x|) 0)
  constructor
  · exact helperForProposition_4_2_3_notAnalyticAt_zero_abs
  · intro a ha
    exact helperForProposition_4_2_3_analyticAt_abs_of_ne_zero ha

/-- Helper for Theorem 4.2.1: every open subset of `ℝ` has no isolated points. -/
lemma helperForTheorem_4_2_1_hasNoIsolatedPoints_of_isOpen
    {E : Set ℝ} (hE : IsOpen E) : HasNoIsolatedPoints E := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases (Metric.isOpen_iff.1 hE) x hx with ⟨δ, hδ, hδE⟩
  let t : ℝ := min (ε / 2) (δ / 2)
  have ht : 0 < t := by
    unfold t
    refine lt_min ?_ ?_
    · linarith
    · linarith
  have hxt_mem_ball : x + t ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    have htδ : t < δ := by
      have hle : t ≤ δ / 2 := by
        unfold t
        exact min_le_right _ _
      linarith
    have habs : |(x + t) - x| < δ := by
      simpa [sub_eq_add_neg, add_assoc, abs_of_nonneg (le_of_lt ht)] using htδ
    simpa [sub_eq_add_neg, add_assoc] using habs
  have hxt_mem : x + t ∈ E := hδE hxt_mem_ball
  have hxt_ne : x + t ≠ x := by
    linarith
  have hxt_not_mem_singleton : x + t ∉ ({x} : Set ℝ) := by
    simpa [Set.mem_singleton_iff] using hxt_ne
  have hxt_mem_diff : x + t ∈ E \ {x} := ⟨hxt_mem, hxt_not_mem_singleton⟩
  refine ⟨x + t, ?_, ?_⟩
  · exact hxt_mem_diff
  · have hdist : dist x (x + t) = t := by
      rw [Real.dist_eq]
      calc
        |x - (x + t)| = |-t| := by ring_nf
        _ = |t| := by rw [abs_neg]
        _ = t := by exact abs_of_nonneg (le_of_lt ht)
    rw [hdist]
    have hle : t ≤ ε / 2 := by
      unfold t
      exact min_le_left _ _
    linarith

/-- Helper for Theorem 4.2.1: local interval and ambient set are eventually equal at the center. -/
lemma helperForTheorem_4_2_1_intervalEventuallyEq_set_at_center
    {E : Set ℝ} {a r : ℝ} (hr : 0 < r)
    (hI : Set.Ioo (a - r) (a + r) ⊆ E) :
    Set.Ioo (a - r) (a + r) =ᶠ[nhds a] E := by
  have hIooNhds : Set.Ioo (a - r) (a + r) ∈ nhds a := by
    exact Ioo_mem_nhds (by linarith) (by linarith)
  refine Filter.eventuallyEq_iff_exists_mem.2 ?_
  refine ⟨Set.Ioo (a - r) (a + r), hIooNhds, ?_⟩
  intro x hx
  have hxE : x ∈ E := hI hx
  exact propext (Iff.intro (fun _ => hxE) (fun _ => hx))

/-- Helper for Theorem 4.2.1: a pointwise real-analytic witness yields analytic-within-at
for the canonical extension. -/
lemma helperForTheorem_4_2_1_analyticWithinAtSubtypeExtension_of_IsRealAnalyticAt
    {E : Set ℝ} (f : E → ℝ) (a : E)
    (ha : IsRealAnalyticAt E f a) :
    AnalyticWithinAt ℝ (SubtypeExtension E f) E (a : ℝ) := by
  rcases ha with ⟨-, r, hr, hI, c, hsummable, hseries⟩
  let I : Set ℝ := Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)
  let fI : I → ℝ := fun x => f ⟨x, hI x.property⟩
  have hseriesI :
      ∀ x (hx : x ∈ I),
        Summable (fun n : ℕ => c n * (x - (a : ℝ)) ^ n) ∧
          fI ⟨x, hx⟩ = ∑' n : ℕ, c n * (x - (a : ℝ)) ^ n := by
    intro x hx
    constructor
    · exact hsummable x hx
    · simpa [fI, I] using hseries x hx
  have hpow :
      HasFPowerSeriesWithinOnBall
        (SubtypeExtension I fI)
        (FormalMultilinearSeries.ofScalars ℝ c)
        I (a : ℝ) (ENNReal.ofReal r) :=
    helperForProposition_4_2_2_hasFPowerSeriesWithinOnBall_of_seriesData hr fI c hseriesI
  have hAnalyticI : AnalyticWithinAt ℝ (SubtypeExtension I fI) I (a : ℝ) :=
    hpow.analyticWithinAt
  have hEqOnI : Set.EqOn (SubtypeExtension E f) (SubtypeExtension I fI) I := by
    intro x hx
    have hxE : x ∈ E := hI (by simpa [I] using hx)
    simp [SubtypeExtension, fI, I, hx, hxE]
  have haI : (a : ℝ) ∈ I := by
    have hleft : (a : ℝ) - r < (a : ℝ) := by linarith
    have hright : (a : ℝ) < (a : ℝ) + r := by linarith
    exact by
      change (a : ℝ) ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)
      exact ⟨hleft, hright⟩
  have hAnalyticI' : AnalyticWithinAt ℝ (SubtypeExtension E f) I (a : ℝ) :=
    hAnalyticI.congr hEqOnI (hEqOnI haI)
  exact hAnalyticI'.congr_set
    (helperForTheorem_4_2_1_intervalEventuallyEq_set_at_center hr hI)

/-- Helper for Theorem 4.2.1: on open sets, analyticity of the canonical extension implies
the custom pointwise real-analytic property. -/
lemma helperForTheorem_4_2_1_isRealAnalyticAt_of_analyticWithinAtSubtypeExtension_open
    {E : Set ℝ} (g : E → ℝ) (hE : IsOpen E) (a : E)
    (ha : AnalyticWithinAt ℝ (SubtypeExtension E g) E (a : ℝ)) :
    IsRealAnalyticAt E g a := by
  have haInterior : (a : ℝ) ∈ interior E := by
    exact mem_interior_iff_mem_nhds.2 (hE.mem_nhds a.property)
  rcases (analyticWithinAt_iff_exists_analyticAt').1 ha with ⟨G, -, hEqOnInsert, hGan⟩
  rcases hGan with ⟨p, hpAt⟩
  rcases hpAt with ⟨R, hR⟩
  have hRpos : 0 < R := hR.r_pos
  rcases (ENNReal.lt_iff_exists_real_btwn).1 hRpos with ⟨ρ, hρnonneg, hρofPos, hρltR⟩
  have hρpos : 0 < ρ := ENNReal.ofReal_pos.1 hρofPos
  rcases (Metric.isOpen_iff.1 hE) (a : ℝ) a.property with ⟨δ, hδpos, hδsub⟩
  let r : ℝ := min ρ δ
  have hrpos : 0 < r := by
    unfold r
    exact lt_min hρpos hδpos
  have hI : Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) ⊆ E := by
    intro x hx
    have hxr : |x - (a : ℝ)| < r := by
      have hleft : -(r) < x - (a : ℝ) := by linarith [hx.1]
      have hright : x - (a : ℝ) < r := by linarith [hx.2]
      exact abs_lt.2 ⟨hleft, hright⟩
    have hrle : r ≤ δ := by
      unfold r
      exact min_le_right _ _
    have hdist : dist x (a : ℝ) < δ := by
      rw [Real.dist_eq]
      exact lt_of_lt_of_le hxr hrle
    exact hδsub (by simpa [Metric.mem_ball] using hdist)
  let c : ℕ → ℝ := fun n => p.coeff n
  refine ⟨haInterior, r, hrpos, hI, c, ?_, ?_⟩
  · intro x hx
    have hxr : |x - (a : ℝ)| < r := by
      have hleft : -(r) < x - (a : ℝ) := by linarith [hx.1]
      have hright : x - (a : ℝ) < r := by linarith [hx.2]
      exact abs_lt.2 ⟨hleft, hright⟩
    have hrle : r ≤ ρ := by
      unfold r
      exact min_le_left _ _
    have hdistρ : dist x (a : ℝ) < ρ := by
      rw [Real.dist_eq]
      exact lt_of_lt_of_le hxr hrle
    have hdistR : ENNReal.ofReal (dist x (a : ℝ)) < R := by
      have hdistρ' : ENNReal.ofReal (dist x (a : ℝ)) < ENNReal.ofReal ρ :=
        (ENNReal.ofReal_lt_ofReal_iff hρpos).2 hdistρ
      exact lt_trans hdistρ' hρltR
    have hxBall : x ∈ EMetric.ball (a : ℝ) R := by
      simpa [EMetric.mem_ball, edist_dist] using hdistR
    have hHasSumG : HasSum (fun n : ℕ => p n (fun _ : Fin n => x - (a : ℝ))) (G x) :=
      hR.hasSum_sub hxBall
    have hTermEq :
        (fun n : ℕ => p n (fun _ : Fin n => x - (a : ℝ))) =
          (fun n : ℕ => c n * (x - (a : ℝ)) ^ n) := by
      funext n
      calc
        p n (fun _ : Fin n => x - (a : ℝ)) = (∏ i : Fin n, (x - (a : ℝ))) * p.coeff n := by
          simpa [smul_eq_mul] using
            (FormalMultilinearSeries.apply_eq_prod_smul_coeff
              (p := p) (y := fun _ : Fin n => x - (a : ℝ)))
        _ = (x - (a : ℝ)) ^ n * p.coeff n := by simp
        _ = c n * (x - (a : ℝ)) ^ n := by
          simp [c, mul_comm, mul_left_comm, mul_assoc]
    have hHasSumTarget :
        HasSum (fun n : ℕ => c n * (x - (a : ℝ)) ^ n) (G x) := by
      rw [← hTermEq]
      exact hHasSumG
    exact hHasSumTarget.summable
  · intro x hx
    have hxinE : x ∈ E := hI hx
    have hEqSubtype : SubtypeExtension E g x = G x := hEqOnInsert (Or.inr hxinE)
    have hEqValue : G x = g ⟨x, hxinE⟩ := by
      calc
        G x = SubtypeExtension E g x := hEqSubtype.symm
        _ = g ⟨x, hxinE⟩ := by simp [SubtypeExtension, hxinE]
    have hxr : |x - (a : ℝ)| < r := by
      have hleft : -(r) < x - (a : ℝ) := by linarith [hx.1]
      have hright : x - (a : ℝ) < r := by linarith [hx.2]
      exact abs_lt.2 ⟨hleft, hright⟩
    have hrle : r ≤ ρ := by
      unfold r
      exact min_le_left _ _
    have hdistρ : dist x (a : ℝ) < ρ := by
      rw [Real.dist_eq]
      exact lt_of_lt_of_le hxr hrle
    have hdistR : ENNReal.ofReal (dist x (a : ℝ)) < R := by
      have hdistρ' : ENNReal.ofReal (dist x (a : ℝ)) < ENNReal.ofReal ρ :=
        (ENNReal.ofReal_lt_ofReal_iff hρpos).2 hdistρ
      exact lt_trans hdistρ' hρltR
    have hxBall : x ∈ EMetric.ball (a : ℝ) R := by
      simpa [EMetric.mem_ball, edist_dist] using hdistR
    have hHasSumG : HasSum (fun n : ℕ => p n (fun _ : Fin n => x - (a : ℝ))) (G x) :=
      hR.hasSum_sub hxBall
    have hTermEq :
        (fun n : ℕ => p n (fun _ : Fin n => x - (a : ℝ))) =
          (fun n : ℕ => c n * (x - (a : ℝ)) ^ n) := by
      funext n
      calc
        p n (fun _ : Fin n => x - (a : ℝ)) = (∏ i : Fin n, (x - (a : ℝ))) * p.coeff n := by
          simpa [smul_eq_mul] using
            (FormalMultilinearSeries.apply_eq_prod_smul_coeff
              (p := p) (y := fun _ : Fin n => x - (a : ℝ)))
        _ = (x - (a : ℝ)) ^ n * p.coeff n := by simp
        _ = c n * (x - (a : ℝ)) ^ n := by
          simp [c, mul_comm, mul_left_comm, mul_assoc]
    have hHasSumTarget :
        HasSum (fun n : ℕ => c n * (x - (a : ℝ)) ^ n) (G x) := by
      rw [← hTermEq]
      exact hHasSumG
    calc
      g ⟨x, hxinE⟩ = G x := hEqValue.symm
      _ = ∑' n : ℕ, c n * (x - (a : ℝ)) ^ n := by
        symm
        exact hHasSumTarget.tsum_eq

/-- Helper for Theorem 4.2.1: convert the custom `IsRealAnalyticOn` notion to
mathlib `AnalyticOn` for the canonical extension. -/
lemma helperForTheorem_4_2_1_analyticOnSubtypeExtension_of_IsRealAnalyticOn
    {E : Set ℝ} (f : E → ℝ) (hf : IsRealAnalyticOn E f) :
    AnalyticOn ℝ (SubtypeExtension E f) E := by
  intro x hx
  exact
    helperForTheorem_4_2_1_analyticWithinAtSubtypeExtension_of_IsRealAnalyticAt f ⟨x, hx⟩
      (hf.2 ⟨x, hx⟩)

/-- Helper for Theorem 4.2.1: convert analyticity of the canonical extension
on an open set back to the custom `IsRealAnalyticOn` predicate. -/
lemma helperForTheorem_4_2_1_isRealAnalyticOn_of_analyticOnSubtypeExtension
    {E : Set ℝ} (g : E → ℝ) (hE : IsOpen E)
    (hAnalytic : AnalyticOn ℝ (SubtypeExtension E g) E) :
    IsRealAnalyticOn E g := by
  refine ⟨hE, ?_⟩
  intro a
  exact
    helperForTheorem_4_2_1_isRealAnalyticAt_of_analyticWithinAtSubtypeExtension_open g hE a
      (hAnalytic a a.property)

/-- Helper for Theorem 4.2.1: analyticity of an extension propagates to all
iterated subtype derivatives. -/
lemma helperForTheorem_4_2_1_analyticOnSubtypeExtension_iteratedDerivativeSub
    {E : Set ℝ} (f : E → ℝ) (hE : IsOpen E)
    (hAnalytic : AnalyticOn ℝ (SubtypeExtension E f) E) :
    ∀ k : ℕ, AnalyticOn ℝ (SubtypeExtension E (IteratedDerivativeSub E f k)) E := by
  intro k
  have hUnique : UniqueDiffOn ℝ E := by
    simpa using hE.uniqueDiffOn
  have hIterF :
      AnalyticOn ℝ (iteratedFDerivWithin ℝ k (SubtypeExtension E f) E) E :=
    hAnalytic.iteratedFDerivWithin hUnique k
  let evalOnes :
      ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ) ℝ →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => ℝ) ℝ (fun _ => (1 : ℝ))
  have hScalar :
      AnalyticOn ℝ
        (fun x : ℝ => (iteratedFDerivWithin ℝ k (SubtypeExtension E f) E x) (fun _ => (1 : ℝ)))
        E := by
    simpa [evalOnes, Function.comp] using ContinuousLinearMap.comp_analyticOn evalOnes hIterF
  have hDerivWithin :
      AnalyticOn ℝ (iteratedDerivWithin k (SubtypeExtension E f) E) E := by
    refine hScalar.congr ?_
    intro x hx
    symm
    exact iteratedDerivWithin_eq_iteratedFDerivWithin
  have hEqOn :
      Set.EqOn
        (SubtypeExtension E (IteratedDerivativeSub E f k))
        (iteratedDerivWithin k (SubtypeExtension E f) E)
        E := by
    intro x hx
    have hxEq :=
      helperForProposition_4_2_2_iteratedDerivativeSub_eq_iteratedDerivWithin E f k x hx
    simpa [SubtypeExtension, hx] using hxEq
  exact hDerivWithin.congr hEqOn

/-- Helper for Theorem 4.2.1: real-analytic-on implies once differentiable on the set. -/
lemma helperForTheorem_4_2_1_isOnceDifferentiableSub_of_IsRealAnalyticOn
    {E : Set ℝ} (g : E → ℝ) (hg : IsRealAnalyticOn E g) :
    IsOnceDifferentiableSub E g := by
  have hAnalytic : AnalyticOn ℝ (SubtypeExtension E g) E :=
    helperForTheorem_4_2_1_analyticOnSubtypeExtension_of_IsRealAnalyticOn g hg
  intro x
  exact hAnalytic.differentiableOn x x.property

/-- Theorem 4.2.1: if `f : E → ℝ` is real analytic on `E`, then `f` is smooth on `E`.
Moreover, for every integer `k ≥ 0`, the iterated derivative `f^(k)` exists at every
point of `E` and is real analytic on `E`. -/
theorem realAnalyticOn_isSmooth_and_iteratedDerivative_realAnalytic
    {E : Set ℝ} (f : E → ℝ) (hf : IsRealAnalyticOn E f) :
    IsSmoothSub E f ∧
      ∀ k : ℕ,
        IsOnceDifferentiableSub E (IteratedDerivativeSub E f k) ∧
          IsRealAnalyticOn E (IteratedDerivativeSub E f k) := by
  have hE : IsOpen E := hf.1
  have hNoIso : HasNoIsolatedPoints E :=
    helperForTheorem_4_2_1_hasNoIsolatedPoints_of_isOpen hE
  have hAnalytic : AnalyticOn ℝ (SubtypeExtension E f) E :=
    helperForTheorem_4_2_1_analyticOnSubtypeExtension_of_IsRealAnalyticOn f hf
  have hIterAnalytic :
      ∀ k : ℕ, AnalyticOn ℝ (SubtypeExtension E (IteratedDerivativeSub E f k)) E :=
    helperForTheorem_4_2_1_analyticOnSubtypeExtension_iteratedDerivativeSub f hE hAnalytic
  have hIterRealAnalytic :
      ∀ k : ℕ, IsRealAnalyticOn E (IteratedDerivativeSub E f k) := by
    intro k
    exact
      helperForTheorem_4_2_1_isRealAnalyticOn_of_analyticOnSubtypeExtension
        (IteratedDerivativeSub E f k) hE (hIterAnalytic k)
  have hOnceAll :
      ∀ k : ℕ, IsOnceDifferentiableSub E (IteratedDerivativeSub E f k) := by
    intro k
    exact helperForTheorem_4_2_1_isOnceDifferentiableSub_of_IsRealAnalyticOn
      (IteratedDerivativeSub E f k) (hIterRealAnalytic k)
  have hSmooth : IsSmoothSub E f := by
    intro k
    exact
      helperForProposition_4_2_2_isKTimesDifferentiableSub_of_allOnceDifferentiable
        f hNoIso hOnceAll k
  constructor
  · exact hSmooth
  · intro k
    constructor
    · exact hOnceAll k
    · exact hIterRealAnalytic k

/-- Helper for Theorem 4.2.2: iterated derivatives within eventually equal sets agree at the center. -/
lemma helperForTheorem_4_2_2_iteratedDerivWithin_setChange_at_center
    {g : ℝ → ℝ} {a : ℝ} {s t : Set ℝ}
    (hst : s =ᶠ[nhds a] t) :
    ∀ k : ℕ, iteratedDerivWithin k g s a = iteratedDerivWithin k g t a := by
  intro k
  calc
    iteratedDerivWithin k g s a
        = (iteratedFDerivWithin ℝ k g s a : (Fin k → ℝ) → ℝ) (fun _ : Fin k => (1 : ℝ)) := by
            rw [iteratedDerivWithin_eq_iteratedFDerivWithin]
    _ = (iteratedFDerivWithin ℝ k g t a : (Fin k → ℝ) → ℝ) (fun _ : Fin k => (1 : ℝ)) := by
          rw [iteratedFDerivWithin_congr_set hst k]
    _ = iteratedDerivWithin k g t a := by
          rw [iteratedDerivWithin_eq_iteratedFDerivWithin]

/-- Helper for Theorem 4.2.2: identify ambient and interval iterated subtype derivatives at the center. -/
lemma helperForTheorem_4_2_2_iteratedDerivativeSub_eq_intervalRestriction_at_center
    {E : Set ℝ} (f : E → ℝ) (a : E) {r : ℝ} (hr : 0 < r)
    (hI : Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) ⊆ E)
    (haI : (a : ℝ) ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)) :
    ∀ k : ℕ,
      IteratedDerivativeSub E f k a =
        IteratedDerivativeSub
          (Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r))
          (fun x : Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) => f ⟨x, hI x.property⟩)
          k
          ⟨(a : ℝ), haI⟩ := by
  intro k
  let I : Set ℝ := Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)
  have hI_mem_of_mem_I :
      ∀ {x : ℝ}, x ∈ I → x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) := by
    intro x hx
    simpa [I] using hx
  let fI : I → ℝ := fun x => f ⟨x, hI (hI_mem_of_mem_I x.property)⟩
  have hEventually : E =ᶠ[nhds (a : ℝ)] I :=
    (helperForTheorem_4_2_1_intervalEventuallyEq_set_at_center hr hI).symm
  have haI' : (a : ℝ) ∈ I := by
    simpa [I] using haI
  have hEqOnI :
      Set.EqOn
        (SubtypeExtension E f)
        (SubtypeExtension I fI)
        I := by
    intro x hx
    have hxIoo : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) := hI_mem_of_mem_I hx
    have hxE : x ∈ E := hI hxIoo
    simp [SubtypeExtension, fI, I, hx, hxE, hxIoo]
  have hSetChange :
      iteratedDerivWithin k (SubtypeExtension E f) E (a : ℝ) =
        iteratedDerivWithin k (SubtypeExtension E f) I (a : ℝ) :=
    helperForTheorem_4_2_2_iteratedDerivWithin_setChange_at_center
      (g := SubtypeExtension E f) (a := (a : ℝ)) (s := E) (t := I) hEventually k
  have hCongrAt :
      iteratedDerivWithin k (SubtypeExtension E f) I (a : ℝ) =
        iteratedDerivWithin k (SubtypeExtension I fI) I (a : ℝ) := by
    exact (iteratedDerivWithin_congr (n := k) hEqOnI) haI'
  have hSubE :
      IteratedDerivativeSub E f k a =
        iteratedDerivWithin k (SubtypeExtension E f) E (a : ℝ) := by
    simpa using
      (helperForProposition_4_2_2_iteratedDerivativeSub_eq_iteratedDerivWithin
        E f k (a : ℝ) a.property)
  have hSubI :
      IteratedDerivativeSub I fI k ⟨(a : ℝ), haI'⟩ =
        iteratedDerivWithin k (SubtypeExtension I fI) I (a : ℝ) := by
    simpa using
      (helperForProposition_4_2_2_iteratedDerivativeSub_eq_iteratedDerivWithin
        I fI k (a : ℝ) haI')
  calc
    IteratedDerivativeSub E f k a
        = iteratedDerivWithin k (SubtypeExtension E f) E (a : ℝ) := hSubE
    _ = iteratedDerivWithin k (SubtypeExtension E f) I (a : ℝ) := hSetChange
    _ = iteratedDerivWithin k (SubtypeExtension I fI) I (a : ℝ) := hCongrAt
    _ = IteratedDerivativeSub I fI k ⟨(a : ℝ), haI'⟩ := hSubI.symm

/-- Helper for Theorem 4.2.2: the interval center value of the iterated derivative extracts factorial times the coefficient. -/
lemma helperForTheorem_4_2_2_interval_center_factorial_coeff
    {a r : ℝ} (hr : 0 < r)
    (f : Set.Ioo (a - r) (a + r) → ℝ) (c : ℕ → ℝ)
    (hseries :
      ∀ x (hx : x ∈ Set.Ioo (a - r) (a + r)),
        Summable (fun n : ℕ => c n * (x - a) ^ n) ∧
          f ⟨x, hx⟩ = ∑' n : ℕ, c n * (x - a) ^ n)
    (haI : a ∈ Set.Ioo (a - r) (a + r)) :
    ∀ k : ℕ,
      IteratedDerivativeSub (Set.Ioo (a - r) (a + r)) f k ⟨a, haI⟩ =
        (Nat.factorial k : ℝ) * c k := by
  intro k
  rcases
    helperForProposition_4_2_2_iteratedDerivWithin_series_formula hr f c hseries k a haI with
    ⟨-, hSeriesAtCenter⟩
  let term : ℕ → ℝ :=
    fun n => c (n + k) * ((Nat.factorial (n + k) : ℝ) / (Nat.factorial n : ℝ)) * (a - a) ^ n
  have hSub :
      IteratedDerivativeSub (Set.Ioo (a - r) (a + r)) f k ⟨a, haI⟩ =
        iteratedDerivWithin
          k
          (SubtypeExtension (Set.Ioo (a - r) (a + r)) f)
          (Set.Ioo (a - r) (a + r))
          a := by
    simpa using
      (helperForProposition_4_2_2_iteratedDerivativeSub_eq_iteratedDerivWithin
        (Set.Ioo (a - r) (a + r)) f k a haI)
  have hTsumSingle : (∑' n : ℕ, term n) = term 0 := by
    refine tsum_eq_single 0 ?_
    intro n hn
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    simp [term, hn, hnpos.ne']
  have hTermZero : term 0 = (Nat.factorial k : ℝ) * c k := by
    simp [term, mul_comm, mul_left_comm, mul_assoc]
  calc
    IteratedDerivativeSub (Set.Ioo (a - r) (a + r)) f k ⟨a, haI⟩
        = iteratedDerivWithin
            k
            (SubtypeExtension (Set.Ioo (a - r) (a + r)) f)
            (Set.Ioo (a - r) (a + r))
            a := hSub
    _ = ∑' n : ℕ, term n := by
          simpa [term] using hSeriesAtCenter
    _ = term 0 := hTsumSingle
    _ = (Nat.factorial k : ℝ) * c k := hTermZero

/-- Helper for Theorem 4.2.2: divide the factorial identity to recover coefficients. -/
lemma helperForTheorem_4_2_2_coeff_rewrite_from_factorial_identity
    {E : Set ℝ} (f : E → ℝ) (a : E) (c : ℕ → ℝ)
    (hfac : ∀ n : ℕ, IteratedDerivativeSub E f n a = (Nat.factorial n : ℝ) * c n) :
    ∀ n : ℕ, IteratedDerivativeSub E f n a / (Nat.factorial n : ℝ) = c n := by
  intro n
  have hne : (Nat.factorial n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  calc
    IteratedDerivativeSub E f n a / (Nat.factorial n : ℝ)
        = ((Nat.factorial n : ℝ) * c n) / (Nat.factorial n : ℝ) := by rw [hfac n]
    _ = c n := by
          exact mul_div_cancel_left₀ (c n) hne

/-- Theorem 4.2.2 (Taylor's formula): let `E ⊆ ℝ`, let `a : E` be an interior point,
and let `f : E → ℝ` be real analytic at `a`. If for some `r > 0` and coefficients
`c : ℕ → ℝ` one has `f(x) = ∑' n, c n (x-a)^n` for all `x ∈ (a-r, a+r)`, then for
every `k ≥ 0`, `f^(k)(a) = k! * c_k`; in particular,
`f(x) = ∑' n, (f^(n)(a) / n!) (x-a)^n` on `(a-r, a+r)`. -/
theorem taylorFormula_iteratedDerivativeSub_eq_factorial_mul_coeff
    {E : Set ℝ} (f : E → ℝ) (a : E) (hf : IsRealAnalyticAt E f a)
    {r : ℝ} (hr : 0 < r)
    (hI : Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) ⊆ E)
    (c : ℕ → ℝ)
    (hsummable :
      ∀ x (hx : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)),
        Summable (fun n : ℕ => c n * (x - (a : ℝ)) ^ n))
    (hseries :
      ∀ x (hx : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)),
        f ⟨x, hI hx⟩ = ∑' n : ℕ, c n * (x - (a : ℝ)) ^ n) :
    (∀ k : ℕ, IteratedDerivativeSub E f k a = (Nat.factorial k : ℝ) * c k) ∧
      ∀ x (hx : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)),
        f ⟨x, hI hx⟩ =
          ∑' n : ℕ,
            (IteratedDerivativeSub E f n a / (Nat.factorial n : ℝ)) *
              (x - (a : ℝ)) ^ n := by
  let I : Set ℝ := Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)
  have hI_mem_of_mem_I :
      ∀ {x : ℝ}, x ∈ I → x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) := by
    intro x hx
    simpa [I] using hx
  let fI : I → ℝ := fun x => f ⟨x, hI (hI_mem_of_mem_I x.property)⟩
  have haI : (a : ℝ) ∈ I := by
    have hleft : (a : ℝ) - r < (a : ℝ) := by linarith
    have hright : (a : ℝ) < (a : ℝ) + r := by linarith
    simpa [I] using And.intro hleft hright
  have haIoo : (a : ℝ) ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) := hI_mem_of_mem_I haI
  have hseriesI :
      ∀ x (hx : x ∈ I),
        Summable (fun n : ℕ => c n * (x - (a : ℝ)) ^ n) ∧
          fI ⟨x, hx⟩ = ∑' n : ℕ, c n * (x - (a : ℝ)) ^ n := by
    intro x hx
    have hxIoo : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) := hI_mem_of_mem_I hx
    constructor
    · exact hsummable x hxIoo
    · simpa [fI, I, hxIoo] using hseries x hxIoo
  have hIntervalFactorial :
      ∀ k : ℕ,
        IteratedDerivativeSub I fI k ⟨(a : ℝ), haI⟩ = (Nat.factorial k : ℝ) * c k := by
    intro k
    simpa [I, fI] using
      (helperForTheorem_4_2_2_interval_center_factorial_coeff
        (a := (a : ℝ)) (r := r) hr fI c hseriesI haIoo k)
  have hAmbientToInterval :
      ∀ k : ℕ,
        IteratedDerivativeSub E f k a = IteratedDerivativeSub I fI k ⟨(a : ℝ), haI⟩ := by
    intro k
    simpa [I, fI] using
      (helperForTheorem_4_2_2_iteratedDerivativeSub_eq_intervalRestriction_at_center
        (f := f) (a := a) (r := r) hr hI haIoo k)
  have hFactorial :
      ∀ k : ℕ, IteratedDerivativeSub E f k a = (Nat.factorial k : ℝ) * c k := by
    intro k
    calc
      IteratedDerivativeSub E f k a
          = IteratedDerivativeSub I fI k ⟨(a : ℝ), haI⟩ := hAmbientToInterval k
      _ = (Nat.factorial k : ℝ) * c k := hIntervalFactorial k
  have hCoeffRewrite :
      ∀ n : ℕ, IteratedDerivativeSub E f n a / (Nat.factorial n : ℝ) = c n :=
    helperForTheorem_4_2_2_coeff_rewrite_from_factorial_identity f a c hFactorial
  constructor
  · exact hFactorial
  · intro x hx
    calc
      f ⟨x, hI hx⟩ = ∑' n : ℕ, c n * (x - (a : ℝ)) ^ n := hseries x hx
      _ = ∑' n : ℕ,
            (IteratedDerivativeSub E f n a / (Nat.factorial n : ℝ)) *
              (x - (a : ℝ)) ^ n := by
            refine tsum_congr ?_
            intro n
            rw [← hCoeffRewrite n]

/-- Helper for Theorem 4.2.3: from interior membership and two positive radii,
construct a common positive interval radius contained in `E` and bounded by both
given radii. -/
lemma helperForTheorem_4_2_3_exists_commonIntervalRadius
    {E : Set ℝ} {a : ℝ} (ha : a ∈ interior E)
    {R_c R_d : ℝ} (hR_c : 0 < R_c) (hR_d : 0 < R_d) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R_c ∧ r ≤ R_d ∧ Set.Ioo (a - r) (a + r) ⊆ E := by
  have hnhds : E ∈ nhds a := mem_interior_iff_mem_nhds.1 ha
  rcases Metric.mem_nhds_iff.1 hnhds with ⟨δ, hδpos, hδsub⟩
  refine ⟨min δ (min R_c R_d), ?_, ?_, ?_, ?_⟩
  · exact lt_min hδpos (lt_min hR_c hR_d)
  · exact le_trans (min_le_right δ (min R_c R_d)) (min_le_left R_c R_d)
  · exact le_trans (min_le_right δ (min R_c R_d)) (min_le_right R_c R_d)
  · intro x hx
    have hxAbs : |x - a| < min δ (min R_c R_d) := by
      have hleft : -(min δ (min R_c R_d)) < x - a := by linarith [hx.1]
      have hright : x - a < min δ (min R_c R_d) := by linarith [hx.2]
      exact abs_lt.2 ⟨hleft, hright⟩
    have hxAbsδ : |x - a| < δ := lt_of_lt_of_le hxAbs (min_le_left δ (min R_c R_d))
    have hdist : dist x a < δ := by
      simpa [Real.dist_eq] using hxAbsδ
    have hxBall : x ∈ Metric.ball a δ := by
      simpa [Metric.mem_ball] using hdist
    exact hδsub hxBall

/-- Helper for Theorem 4.2.3: transport power-series data from a radius condition
`|x-a| < R` on `E` to data on a smaller symmetric interval around `a`. -/
lemma helperForTheorem_4_2_3_seriesData_on_commonInterval
    {E : Set ℝ} {f : E → ℝ} {a r R : ℝ} {u : ℕ → ℝ}
    (hI : Set.Ioo (a - r) (a + r) ⊆ E) (hrR : r ≤ R)
    (hu :
      ∀ x : ℝ, ∀ hxE : x ∈ E, |x - a| < R →
        Summable (fun n : ℕ => u n * (x - a) ^ n) ∧
          f ⟨x, hxE⟩ = ∑' n : ℕ, u n * (x - a) ^ n) :
    ∀ x : ℝ, ∀ hx : x ∈ Set.Ioo (a - r) (a + r),
      Summable (fun n : ℕ => u n * (x - a) ^ n) ∧
        f ⟨x, hI hx⟩ = ∑' n : ℕ, u n * (x - a) ^ n := by
  intro x hx
  have hxAbsR : |x - a| < r := by
    have hleft : -r < x - a := by linarith [hx.1]
    have hright : x - a < r := by linarith [hx.2]
    exact abs_lt.2 ⟨hleft, hright⟩
  exact hu x (hI hx) (lt_of_lt_of_le hxAbsR hrR)

/-- Helper for Theorem 4.2.3: interval power-series data gives real analyticity at
the center. -/
lemma helperForTheorem_4_2_3_isRealAnalyticAt_of_intervalSeriesData
    {E : Set ℝ} (f : E → ℝ) (a : E) (ha : (a : ℝ) ∈ interior E)
    {r : ℝ} (hr : 0 < r)
    (hI : Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) ⊆ E)
    (u : ℕ → ℝ)
    (hseriesData :
      ∀ x : ℝ, ∀ hx : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r),
        Summable (fun n : ℕ => u n * (x - (a : ℝ)) ^ n) ∧
          f ⟨x, hI hx⟩ = ∑' n : ℕ, u n * (x - (a : ℝ)) ^ n) :
    IsRealAnalyticAt E f a := by
  refine ⟨ha, r, hr, hI, u, ?_, ?_⟩
  · intro x hx
    exact (hseriesData x hx).1
  · intro x hx
    exact (hseriesData x hx).2

/-- Helper for Theorem 4.2.3: cancel a nonzero factorial factor in two identities
for the same iterated derivative sequence. -/
lemma helperForTheorem_4_2_3_cancel_factorial
    {E : Set ℝ} {f : E → ℝ} {a : E} {c d : ℕ → ℝ}
    (hc : ∀ n : ℕ, IteratedDerivativeSub E f n a = (Nat.factorial n : ℝ) * c n)
    (hd : ∀ n : ℕ, IteratedDerivativeSub E f n a = (Nat.factorial n : ℝ) * d n) :
    ∀ n : ℕ, c n = d n := by
  intro n
  have hEq : (Nat.factorial n : ℝ) * c n = (Nat.factorial n : ℝ) * d n := by
    calc
      (Nat.factorial n : ℝ) * c n = IteratedDerivativeSub E f n a := (hc n).symm
      _ = (Nat.factorial n : ℝ) * d n := hd n
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero n)
  exact mul_left_cancel₀ hfac hEq

/-- Theorem 4.2.3 (Uniqueness of power series): let `E ⊆ ℝ`, let `a` be an interior
point of `E`, and let `f : E → ℝ`. If there are radii `R_c, R_d > 0` and coefficient
sequences `c, d : ℕ → ℝ` such that for every `x ∈ E` with `|x-a| < R_c` one has
`f(x) = ∑' n, c n * (x-a)^n` with convergence, and for every `x ∈ E` with
`|x-a| < R_d` one has `f(x) = ∑' n, d n * (x-a)^n` with convergence, then
`c n = d n` for all `n`. -/
theorem powerSeries_coefficients_unique
    {E : Set ℝ} (f : E → ℝ) (a : E)
    (ha : (a : ℝ) ∈ interior E)
    (c d : ℕ → ℝ) {R_c R_d : ℝ} (hR_c : 0 < R_c) (hR_d : 0 < R_d)
    (hc :
      ∀ x : ℝ, ∀ hxE : x ∈ E, |x - (a : ℝ)| < R_c →
        Summable (fun n : ℕ => c n * (x - (a : ℝ)) ^ n) ∧
          f ⟨x, hxE⟩ = ∑' n : ℕ, c n * (x - (a : ℝ)) ^ n)
    (hd :
      ∀ x : ℝ, ∀ hxE : x ∈ E, |x - (a : ℝ)| < R_d →
        Summable (fun n : ℕ => d n * (x - (a : ℝ)) ^ n) ∧
          f ⟨x, hxE⟩ = ∑' n : ℕ, d n * (x - (a : ℝ)) ^ n) :
    ∀ n : ℕ, c n = d n := by
  rcases
      helperForTheorem_4_2_3_exists_commonIntervalRadius
        (a := (a : ℝ)) ha hR_c hR_d with
    ⟨r, hr, hrRc, hrRd, hI⟩
  have hcI :
      ∀ x : ℝ, ∀ hx : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r),
        Summable (fun n : ℕ => c n * (x - (a : ℝ)) ^ n) ∧
          f ⟨x, hI hx⟩ = ∑' n : ℕ, c n * (x - (a : ℝ)) ^ n :=
    helperForTheorem_4_2_3_seriesData_on_commonInterval
      (a := (a : ℝ)) (u := c) hI hrRc hc
  have hdI :
      ∀ x : ℝ, ∀ hx : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r),
        Summable (fun n : ℕ => d n * (x - (a : ℝ)) ^ n) ∧
          f ⟨x, hI hx⟩ = ∑' n : ℕ, d n * (x - (a : ℝ)) ^ n :=
    helperForTheorem_4_2_3_seriesData_on_commonInterval
      (a := (a : ℝ)) (u := d) hI hrRd hd
  have hfAnalytic : IsRealAnalyticAt E f a :=
    helperForTheorem_4_2_3_isRealAnalyticAt_of_intervalSeriesData
      f a ha hr hI c hcI
  have hTaylorC :
      ∀ k : ℕ, IteratedDerivativeSub E f k a = (Nat.factorial k : ℝ) * c k :=
    (taylorFormula_iteratedDerivativeSub_eq_factorial_mul_coeff
      f a hfAnalytic hr hI c
      (fun x hx => (hcI x hx).1)
      (fun x hx => (hcI x hx).2)).1
  have hTaylorD :
      ∀ k : ℕ, IteratedDerivativeSub E f k a = (Nat.factorial k : ℝ) * d k :=
    (taylorFormula_iteratedDerivativeSub_eq_factorial_mul_coeff
      f a hfAnalytic hr hI d
      (fun x hx => (hdI x hx).1)
      (fun x hx => (hdI x hx).2)).1
  exact helperForTheorem_4_2_3_cancel_factorial hTaylorC hTaylorD

/-- Helper for Proposition 4.2.4: convert `|x| < 1` into the norm inequality
`‖x‖ < 1` used by geometric-series lemmas. -/
lemma helperForProposition_4_2_4_norm_lt_one_of_abs_lt_one
    {x : ℝ} (hx : |x| < 1) : ‖x‖ < 1 := by
  simpa [Real.norm_eq_abs] using hx

/-- Helper for Proposition 4.2.4: under `‖x‖ < 1`, the geometric series has
sum `(1 - x)⁻¹`. -/
lemma helperForProposition_4_2_4_hasSum_geometric
    {x : ℝ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => x ^ n) ((1 - x)⁻¹) := by
  simpa using hasSum_geometric_of_norm_lt_one hx

/-- Helper for Proposition 4.2.4: rewrite the geometric-series sum in the form
`1 / (1 - x)`. -/
lemma helperForProposition_4_2_4_tsum_eq_one_div_form
    {x : ℝ} (hx : ‖x‖ < 1) :
    (∑' n : ℕ, x ^ n) = 1 / (1 - x) := by
  have hHasSum : HasSum (fun n : ℕ => x ^ n) ((1 - x)⁻¹) :=
    helperForProposition_4_2_4_hasSum_geometric hx
  have hTsum : (∑' n : ℕ, x ^ n) = (1 - x)⁻¹ := hHasSum.tsum_eq
  simpa [one_div] using hTsum

/-- Proposition 4.2.4: for every real number x with |x| < 1, the geometric
series ∑' n : ℕ, x^n converges and equals 1 / (1 - x). -/
theorem geometricSeries_converges_and_tsum_eq_inv_one_sub
    (x : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ => x ^ n) ∧
      (∑' n : ℕ, x ^ n) = 1 / (1 - x) := by
  have hNorm : ‖x‖ < 1 := helperForProposition_4_2_4_norm_lt_one_of_abs_lt_one hx
  have hSummable : Summable (fun n : ℕ => x ^ n) :=
    (helperForProposition_4_2_4_hasSum_geometric (x := x) hNorm).summable
  have hTsum : (∑' n : ℕ, x ^ n) = 1 / (1 - x) :=
    helperForProposition_4_2_4_tsum_eq_one_div_form (x := x) hNorm
  exact And.intro hSummable hTsum

/-- Helper for Proposition 4.2.5: convert `|x - 1/2| < 1/2` into the norm bound
`‖2 * (x - 1/2)‖ < 1` used by geometric-series lemmas. -/
lemma helperForProposition_4_2_5_norm_lt_one_scaledShift
    {x : ℝ} (hx : |x - (1 / 2 : ℝ)| < (1 / 2 : ℝ)) :
    ‖(2 : ℝ) * (x - (1 / 2 : ℝ))‖ < 1 := by
  have hmul : (2 : ℝ) * |x - (1 / 2 : ℝ)| < (2 : ℝ) * (1 / 2 : ℝ) := by
    have htwo : (0 : ℝ) < 2 := by
      norm_num
    exact mul_lt_mul_of_pos_left hx htwo
  have hAbs : |(2 : ℝ) * (x - (1 / 2 : ℝ))| < 1 := by
    calc
      |(2 : ℝ) * (x - (1 / 2 : ℝ))|
          = |(2 : ℝ)| * |x - (1 / 2 : ℝ)| := by
            rw [abs_mul]
      _ = (2 : ℝ) * |x - (1 / 2 : ℝ)| := by
            norm_num
      _ < (2 : ℝ) * (1 / 2 : ℝ) := hmul
      _ = 1 := by
            norm_num
  simpa [Real.norm_eq_abs] using hAbs

/-- Helper for Proposition 4.2.5: rewrite the centered-series term as a scaled
geometric term in the ratio `2 * (x - 1/2)`. -/
lemma helperForProposition_4_2_5_term_rewrite_to_scaledGeometric
    (x : ℝ) (n : ℕ) :
    (2 : ℝ) ^ (n + 1) * (x - (1 / 2 : ℝ)) ^ n =
      2 * ((2 : ℝ) * (x - (1 / 2 : ℝ))) ^ n := by
  calc
    (2 : ℝ) ^ (n + 1) * (x - (1 / 2 : ℝ)) ^ n
        = ((2 : ℝ) ^ n * 2) * (x - (1 / 2 : ℝ)) ^ n := by
            rw [pow_succ]
    _ = 2 * ((2 : ℝ) ^ n * (x - (1 / 2 : ℝ)) ^ n) := by
          ring
    _ = 2 * ((2 : ℝ) * (x - (1 / 2 : ℝ))) ^ n := by
          rw [← mul_pow]

/-- Helper for Proposition 4.2.5: the centered geometric series has the
closed-form sum `2 * (1 - 2*(x - 1/2))⁻¹`. -/
lemma helperForProposition_4_2_5_hasSum_centeredSeries
    {x : ℝ} (hx : |x - (1 / 2 : ℝ)| < (1 / 2 : ℝ)) :
    HasSum
      (fun n : ℕ => (2 : ℝ) ^ (n + 1) * (x - (1 / 2 : ℝ)) ^ n)
      (2 * (1 - (2 : ℝ) * (x - (1 / 2 : ℝ)))⁻¹) := by
  have hNorm : ‖(2 : ℝ) * (x - (1 / 2 : ℝ))‖ < 1 :=
    helperForProposition_4_2_5_norm_lt_one_scaledShift hx
  have hGeom :
      HasSum
        (fun n : ℕ => ((2 : ℝ) * (x - (1 / 2 : ℝ))) ^ n)
        ((1 - (2 : ℝ) * (x - (1 / 2 : ℝ)))⁻¹) :=
    helperForProposition_4_2_4_hasSum_geometric hNorm
  have hScaled :
      HasSum
        (fun n : ℕ => 2 * (((2 : ℝ) * (x - (1 / 2 : ℝ))) ^ n))
        (2 * ((1 - (2 : ℝ) * (x - (1 / 2 : ℝ)))⁻¹)) :=
    hGeom.mul_left (2 : ℝ)
  have hTermEq :
      (fun n : ℕ => (2 : ℝ) ^ (n + 1) * (x - (1 / 2 : ℝ)) ^ n) =
        (fun n : ℕ => 2 * (((2 : ℝ) * (x - (1 / 2 : ℝ))) ^ n)) := by
    funext n
    exact helperForProposition_4_2_5_term_rewrite_to_scaledGeometric x n
  convert hScaled using 1

/-- Helper for Proposition 4.2.5: simplify the centered closed form to
`1 / (1 - x)`. -/
lemma helperForProposition_4_2_5_sumValue_rewrite
    (x : ℝ) :
    2 * (1 - (2 : ℝ) * (x - (1 / 2 : ℝ)))⁻¹ = 1 / (1 - x) := by
  by_cases h : 1 - x = 0
  · have hx : x = 1 := by
      linarith
    subst hx
    norm_num
  · have hrewrite : 1 - (2 : ℝ) * (x - (1 / 2 : ℝ)) = 2 * (1 - x) := by
      ring
    rw [hrewrite, one_div]
    have htwo : (2 : ℝ) ≠ 0 := by
      norm_num
    have hmul : 2 * (1 - x) ≠ 0 := mul_ne_zero htwo h
    field_simp [h, hmul]

/-- Proposition 4.2.5: if `x : ℝ` satisfies `|x - 1/2| < 1/2`, then the geometric
series `∑' n : ℕ, 2^(n+1) * (x - 1/2)^n` converges and equals `1 / (1 - x)`. -/
theorem centeredGeometricSeries_converges_and_tsum_eq_inv_one_sub
    (x : ℝ) (hx : |x - (1 / 2 : ℝ)| < (1 / 2 : ℝ)) :
    Summable (fun n : ℕ => (2 : ℝ) ^ (n + 1) * (x - (1 / 2 : ℝ)) ^ n) ∧
      (∑' n : ℕ, (2 : ℝ) ^ (n + 1) * (x - (1 / 2 : ℝ)) ^ n) = 1 / (1 - x) := by
  have hHasSum :
      HasSum
        (fun n : ℕ => (2 : ℝ) ^ (n + 1) * (x - (1 / 2 : ℝ)) ^ n)
        (2 * (1 - (2 : ℝ) * (x - (1 / 2 : ℝ)))⁻¹) :=
    helperForProposition_4_2_5_hasSum_centeredSeries hx
  have hSummable :
      Summable (fun n : ℕ => (2 : ℝ) ^ (n + 1) * (x - (1 / 2 : ℝ)) ^ n) :=
    hHasSum.summable
  have hTsumAux :
      (∑' n : ℕ, (2 : ℝ) ^ (n + 1) * (x - (1 / 2 : ℝ)) ^ n) =
        2 * (1 - (2 : ℝ) * (x - (1 / 2 : ℝ)))⁻¹ :=
    hHasSum.tsum_eq
  have hValueRewrite :
      2 * (1 - (2 : ℝ) * (x - (1 / 2 : ℝ)))⁻¹ = 1 / (1 - x) :=
    helperForProposition_4_2_5_sumValue_rewrite x
  constructor
  · exact hSummable
  · calc
      (∑' n : ℕ, (2 : ℝ) ^ (n + 1) * (x - (1 / 2 : ℝ)) ^ n)
          = 2 * (1 - (2 : ℝ) * (x - (1 / 2 : ℝ)))⁻¹ := hTsumAux
      _ = 1 / (1 - x) := hValueRewrite


end Section02
end Chap04
