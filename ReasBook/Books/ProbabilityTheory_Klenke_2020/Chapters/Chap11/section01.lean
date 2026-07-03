import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_11_1_1 (from Items/Chap11) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Finset

universe u

variable {Ω : Type u} {m0 : MeasurableSpace Ω}
variable [m0]
variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration ℕ m0}

local macro:max "absMaxUpTo(" X:term ", " n:term ", " ω:term ")" : term =>
  `((range ($n + 1)).sup' nonempty_range_add_one fun k ↦ |($X k $ω)|)

/- Exercise 11.1.1 is a `source-facing` maximal-inequality corollary in the discrete-time
martingale domain. The owner abstraction for the maximal event is the canonical running maximum
already used by `MeasureTheory.maximal_ineq`, while the chapter-level bridge layer is
`doobLp_tail_bound` together with the canonical Doob decomposition and its predictable-part
monotonicity criterion from Theorem 10.1. This exercise therefore stays `source-facing`: it keeps
the textbook absolute-maximal tail inequality but relies on those owner declarations rather than a
parallel local wrapper. -/
recall MeasureTheory.maximal_ineq
recall doobLp_tail_bound
recall canonical_doobDecomposition
recall submartingale_ae_monotone_predictablePart

-- Proof sketch: if `X` is a submartingale, combine Doob's decomposition with Theorem 11.2 applied
-- to the martingale part and the predictable monotonicity estimates for the finite-variation part.
-- If `X` is a supermartingale, apply the same argument to `-X`, noting that the running maxima of
-- `|-X|` and `|X|` agree pointwise and that `|(-X) n| = |X n|`.
/-- Exercise 11.1.1: for a real-valued submartingale or supermartingale, the tail of the maximal
absolute process up to time `n` is bounded by `|X_0|` and `|X_n|` with constants `1 / 2` and `9`.
-/
theorem submartingale_or_supermartingale_absMaxUpTo_tail_bound {X : ℕ → Ω → ℝ}
    (hX : Submartingale X ℱ μ ∨ Supermartingale X ℱ μ) (n : ℕ) (c : NNReal) :
    c * μ {ω | (c : ℝ) ≤ absMaxUpTo(X, n, ω)} ≤
      ENNReal.ofReal (μ[fun ω ↦ |X 0 ω|] / 2 + 9 * μ[fun ω ↦ |X n ω|]) := sorry

/-! ### Lemma_11_1 (from Items/Chap11) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open Finset

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration ℕ mΩ}
variable {X : ℕ → Ω → ℝ}

/- Lemma 11.1 lies in the discrete maximal-inequality part of the submartingale API. The owner
abstraction is `MeasureTheory.maximal_ineq`, whose source-facing input is a nonnegative
submartingale. This file stays at the `bridge/view` layer: the textbook lemma is for an arbitrary
real-valued submartingale, so its public statement is recovered from the stopping-time bridge
behind the owner theorem rather than by promoting the owner's nonnegativity hypothesis into the
main API. -/
recall MeasureTheory.maximal_ineq

/-- Lemma 11.1: if `X` is a discrete real-valued submartingale and `A = {X_n^* ≥ λ}` is the event
that the running maximum of `X` up to time `n` reaches the positive threshold `λ`, then
`λ P[A] ≤ E[X_n 1_A] ≤ E[|X_n| 1_A]`. -/
theorem submartingale_maximal_event_expectation_bounds
    (hX : Submartingale X ℱ μ) (n : ℕ) {threshold : ℝ}
    (hthreshold : 0 < threshold) :
    threshold *
        μ.real {ω | threshold ≤ (range (n + 1)).sup' nonempty_range_add_one fun k ↦ X k ω} ≤
      ∫ ω in {ω | threshold ≤ (range (n + 1)).sup' nonempty_range_add_one fun k ↦ X k ω},
        X n ω ∂μ ∧
    ∫ ω in {ω | threshold ≤ (range (n + 1)).sup' nonempty_range_add_one fun k ↦ X k ω},
        X n ω ∂μ ≤
      ∫ ω in {ω | threshold ≤ (range (n + 1)).sup' nonempty_range_add_one fun k ↦ X k ω},
        |X n ω| ∂μ := by
  let A : Set Ω := {ω | threshold ≤ (range (n + 1)).sup' nonempty_range_add_one fun k ↦ X k ω}
  let τ : Ω → ℕ := fun ω ↦ hittingBtwn X {y : ℝ | threshold ≤ y} 0 n ω
  let τs : Ω → ℕ∞ := fun ω ↦ (τ ω : ℕ∞)
  have hX_adapted : Adapted ℱ X := hX.stronglyAdapted.adapted
  have hA : MeasurableSet A := by
    exact measurableSet_le measurable_const <|
      measurable_range_sup'' fun k _ ↦ (hX.stronglyMeasurable k).measurable.le (ℱ.le k)
  have hτ : IsStoppingTime ℱ τs := by
    simpa [τs, τ] using hX_adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hτ_le : ∀ ω, τs ω ≤ n := by
    intro ω
    have hω : hittingBtwn X {y : ℝ | threshold ≤ y} 0 n ω ≤ n := hittingBtwn_le ω
    change ((τ ω : ℕ∞) ≤ n)
    exact_mod_cast hω
  have hleft_stopped :
      threshold * μ.real A ≤ ∫ ω in A, stoppedValue X τs ω ∂μ := by
    let ε : NNReal := ⟨threshold, hthreshold.le⟩
    have hsmul :
        (ε : ENNReal) * μ A ≤ ENNReal.ofReal (∫ ω in A, stoppedValue X τs ω ∂μ) := by
      simpa [A, τs, τ, ε, Real.toNNReal_of_nonneg hthreshold.le, smul_eq_mul] using
        MeasureTheory.smul_le_stoppedValue_hittingBtwn hX n
    have hε_ne_top : (ε : ENNReal) ≠ ⊤ := by
      simp
    have htoReal :
        ((ε : ENNReal) * μ A).toReal ≤ (ENNReal.ofReal (∫ ω in A, stoppedValue X τs ω ∂μ)).toReal :=
      (ENNReal.toReal_le_toReal
        (by
          simpa [smul_eq_mul] using
            ENNReal.mul_ne_top hε_ne_top (measure_ne_top μ A))
        ENNReal.ofReal_ne_top
      ).2 hsmul
    have hstopped_nonneg : 0 ≤ ∫ ω in A, stoppedValue X τs ω ∂μ := by
      refine MeasureTheory.setIntegral_nonneg_of_ae_restrict ?_
      refine (ae_restrict_iff' hA).2 ?_
      filter_upwards with ω hω
      have hω' :
          threshold ≤ (range (n + 1)).sup' nonempty_range_add_one fun k ↦ X k ω := by
        simpa [A] using hω
      have hhit : threshold ≤ stoppedValue X τs ω := by
        simp_rw [le_sup'_iff, mem_range, Nat.lt_succ_iff] at hω'
        refine stoppedValue_hittingBtwn_mem ?_
        simp only [Set.mem_Icc, zero_le, true_and, Set.mem_setOf_eq]
        exact hω'
      exact le_trans hthreshold.le hhit
    rw [ENNReal.toReal_ofReal hstopped_nonneg] at htoReal
    simpa [measureReal_def, ε, A] using htoReal
  have hcomplement_eq :
      ∫ ω in Aᶜ, stoppedValue X τs ω ∂μ = ∫ ω in Aᶜ, X n ω ∂μ := by
    apply integral_congr_ae
    refine (ae_restrict_iff' hA.compl).2 ?_
    filter_upwards with ω hω
    have hω' : ¬ threshold ≤ (range (n + 1)).sup' nonempty_range_add_one fun k ↦ X k ω := by
      simpa [A] using hω
    have hτ_eq_nat : τ ω = n := by
      simp only [τ, hittingBtwn, Set.mem_setOf_eq, ite_eq_right_iff, forall_exists_index, and_imp]
      intro m hm hmthreshold
      exact False.elim <| hω' <|
        (le_sup'_iff _).2 ⟨m, mem_range.2 (Nat.lt_succ_of_le hm.2), hmthreshold⟩
    have hτ_eq : τs ω = n := by
      change ((τ ω : ℕ∞) = n)
      exact_mod_cast hτ_eq_nat
    simp [stoppedValue, τs, hτ_eq]
  have hstopped_split :
      μ[stoppedValue X τs] =
        ∫ ω in A, stoppedValue X τs ω ∂μ + ∫ ω in Aᶜ, stoppedValue X τs ω ∂μ := by
    rw [← setIntegral_union disjoint_compl_right hA.compl]
    · simp [A]
    · exact Integrable.integrableOn <| hX.integrable_stoppedValue hτ hτ_le
    · exact Integrable.integrableOn <| hX.integrable_stoppedValue hτ hτ_le
  have hterminal_split :
      μ[X n] = ∫ ω in A, X n ω ∂μ + ∫ ω in Aᶜ, X n ω ∂μ := by
    rw [← setIntegral_union disjoint_compl_right hA.compl]
    · simp [A]
    · exact Integrable.integrableOn <| hX.integrable n
    · exact Integrable.integrableOn <| hX.integrable n
  have hstopped_le_terminal :
      ∫ ω in A, stoppedValue X τs ω ∂μ ≤ ∫ ω in A, X n ω ∂μ := by
    have hmono : μ[stoppedValue X τs] ≤ μ[X n] := by
      simpa [τs, stoppedValue_const] using
        hX.expected_stoppedValue_mono hτ (isStoppingTime_const ℱ n)
          (fun ω ↦ by exact_mod_cast hτ_le ω) (fun _ ↦ by exact_mod_cast le_rfl)
    rw [hstopped_split, hterminal_split, hcomplement_eq] at hmono
    exact le_of_add_le_add_right hmono
  constructor
  · exact hleft_stopped.trans hstopped_le_terminal
  · refine MeasureTheory.setIntegral_mono_on
      (hX.integrable n).integrableOn (hX.integrable n).norm.integrableOn hA ?_
    intro ω hω
    exact le_abs_self (X n ω)
