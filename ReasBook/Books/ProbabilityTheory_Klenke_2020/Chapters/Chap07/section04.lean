import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_7_4_1 (from Items/Chap07) -/
open MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A binary digit is turned into the corresponding base-four digit `0` or `3`. -/
private def duplicatedBaseFourDigit (b : Bool) : Fin 4 :=
  cond b 3 0

/-- The base-four expansion obtained by replacing binary digits with `0` and `3`. -/
private noncomputable def duplicatedBaseFourMap (ω : BernoulliSequence) : unitInterval :=
  ⟨Real.ofDigits fun n ↦ duplicatedBaseFourDigit (ω n),
    ⟨Real.ofDigits_nonneg _, Real.ofDigits_le_one _⟩⟩

/-- The textbook binary digits on `[0,1]`: at positive dyadic rationals below `1`, replace the
terminating-zero expansion `...1000` by the equivalent eventually-one expansion `...0111`. -/
private noncomputable def textbookBinaryDigits (x : unitInterval) : BernoulliSequence :=
  let ω := canonicalBinaryDigits x
  if hω : ∃ N, 0 < N ∧ ω (N - 1) = true ∧ ∀ n ≥ N, ω n = false then
    let N := Nat.find hω
    fun n ↦ if n + 1 < N then ω n else if n + 1 = N then false else true
  else
    ω

/-- Exercise 7.4.1: the map `F : [0,1] → [0,1]` obtained by duplicating the textbook binary digits
of `x` into base-four digits `0` and `3`, using the eventually-one expansion at dyadic rationals
below `1`. -/
noncomputable def dyadicDuplicationMap (x : unitInterval) : unitInterval :=
  duplicatedBaseFourMap (textbookBinaryDigits x)

/-- The image measure of the uniform distribution on `[0,1]` under `dyadicDuplicationMap`. -/
noncomputable def dyadicDuplicationMeasure : Measure ℝ :=
  Measure.map (fun x : unitInterval ↦ (dyadicDuplicationMap x : ℝ)) volume

/-- `dyadicDuplicationMeasure` is the pushforward of the uniform measure on `[0,1]` under
`dyadicDuplicationMap`. -/
@[simp] theorem dyadicDuplicationMeasure_eq_map_dyadicDuplicationMap :
    dyadicDuplicationMeasure =
      Measure.map (fun x : unitInterval ↦ (dyadicDuplicationMap x : ℝ)) volume :=
  rfl

/-- The canonical pushforward description of `dyadicDuplicationMeasure` agrees with the Bernoulli
realization `F(U)` from Chapter 1. -/
theorem dyadicDuplicationMeasure_eq_map_fromBinary :
    dyadicDuplicationMeasure =
      Measure.map (fun ω : BernoulliSequence ↦ (dyadicDuplicationMap (Real.fromBinary ω) : ℝ))
        fairBernoulliMeasure := sorry

-- Proof sketch: identify the mass of a singleton with the probability of a single digit sequence;
-- the Bernoulli digit model has no dyadic ambiguity, so every singleton has measure `0`.
-- A monotone right-continuous cdf with no atoms is continuous.
/-- Exercise 7.4.1 (1): the distribution function of the image measure is continuous. -/
theorem dyadicDuplicationMeasure_cdf_continuous :
    Continuous (cdf dyadicDuplicationMeasure) := sorry

-- Proof sketch: the image of `dyadicDuplicationMap` is contained in the classical Cantor-type set
-- of numbers whose base-four digits are only `0` or `3`; that set has Lebesgue measure `0`, while
-- the pushforward measure assigns it full mass, yielding mutual singularity.
/-- Exercise 7.4.1 (2): the image measure is singular with respect to Lebesgue measure on
`(0,1]`. -/
theorem dyadicDuplicationMeasure_mutuallySingular_restrict_volume :
    dyadicDuplicationMeasure ⟂ₘ volume.restrict (Set.Ioc (0 : ℝ) 1) := sorry

end

/-! ### Exercise_7_4_2 (from Items/Chap07) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory unitInterval

variable (n : ℕ) (p q : I)

private theorem absolutelyContinuous_count (μ : Measure ℕ) : μ ≪ Measure.count := by
  refine Measure.AbsolutelyContinuous.mk fun s _ hs0 ↦ ?_
  rw [Measure.count_eq_zero_iff] at hs0
  rw [hs0, measure_empty]

private theorem rnDeriv_ae_eq_singleton (μ : Measure ℕ) :
    μ.rnDeriv Measure.count =ᵐ[Measure.count] fun k : ℕ ↦ μ {k} := by
  have hμ : Measure.count.withDensity (fun k : ℕ ↦ μ {k}) = μ := by
    rw [count_withDensity, Measure.sum_smul_dirac]
  simpa [hμ] using
    (Measure.rnDeriv_withDensity Measure.count (measurable_of_countable (fun k : ℕ ↦ μ {k})))

/-- Zero trials give the deterministic binomial law at `0`. -/
-- Proof sketch: `Set.Iio 0 = ∅`, so the defining Bernoulli product measure is supported on the
-- unique subset `∅`, and `Set.ncard ∅ = 0`.
@[simp] theorem binomial_zero_left :
    Bin(0, p) = Measure.dirac 0 := by
  let μ : Measure ℕ := Bin(0, p)
  have h_id : HasLaw id μ μ := HasLaw.id
  have hμ0 : ∀ᵐ k ∂μ, k = 0 := by
    filter_upwards [ae_le_of_hasLaw_binomial h_id] with k hk
    exact Nat.eq_zero_of_le_zero hk
  have h_restrict : μ.restrict ({0} : Set ℕ) = μ := by
    exact Measure.restrict_eq_self_of_ae_mem (by simpa [μ] using hμ0)
  have hsmul : μ = μ {0} • Measure.dirac 0 := by
    exact h_restrict.symm.trans (Measure.restrict_singleton μ 0)
  have hprob : μ {0} = 1 := by
    have h_univ := congrArg (fun ν : Measure ℕ ↦ ν Set.univ) hsmul
    simpa [μ] using h_univ.symm
  rw [show Bin(0, p) = μ by rfl, hsmul, hprob, one_smul]

/-- The endpoint parameter `p = 0` gives the deterministic binomial law at `0`. -/
-- Proof sketch: for parameter `0`, the underlying set-Bernoulli law is `dirac ∅`, and mapping by
-- `Set.ncard` sends `∅` to `0`.
@[simp] theorem binomial_zero_right :
    Bin(n, (0 : I)) = Measure.dirac 0 := by
  rw [ProbabilityTheory.binomial, setBernoulli_zero]
  simp

/-- The endpoint parameter `p = 1` gives the deterministic binomial law at `n`. -/
-- Proof sketch: for parameter `1`, the underlying set-Bernoulli law is `dirac (Set.Iio n)`, and
-- `Set.ncard (Set.Iio n) = n`.
@[simp] theorem binomial_one_right :
    Bin(n, (1 : I)) = Measure.dirac n := by
  rw [ProbabilityTheory.binomial, setBernoulli_one]
  simp

/-- Exercise 7.4.2: the binomial law `Bin(n, p)` is absolutely continuous with respect to
`Bin(n, q)` exactly in the trivial case `n = 0`, or else when the degenerate endpoint values of
`q` force the same endpoint values for `p`. -/
-- Proof sketch: identify when the support of `Bin(n, p)` is contained in the support of
-- `Bin(n, q)`. For `n = 0` both laws equal `dirac 0`, while for `n > 0` the only
-- obstructions come from the degenerate endpoint cases `q = 0` and `q = 1`.
theorem binomial_absolutelyContinuous_iff :
    Bin(n, p) ≪ Bin(n, q) ↔
      n = 0 ∨ (q = 0 → p = 0) ∧ (q = 1 → p = 1) := sorry

/-- The Radon--Nikodym derivative of one binomial law with respect to another is the ratio of
their singleton masses, almost everywhere with respect to the reference binomial law. -/
-- Proof sketch: on the countable measurable space `ℕ`, evaluate the Radon--Nikodym identity on
-- singleton sets and rewrite the resulting atoms as the singleton masses of the two binomial
-- measures.
theorem binomial_rnDeriv_ae_eq_singleton_ratio :
    (Bin(n, p)).rnDeriv (Bin(n, q)) =ᵐ[Bin(n, q)] fun k : ℕ ↦
      Bin(n, p) {k} / Bin(n, q) {k} := by
  let μ : Measure ℕ := Bin(n, p)
  let ν : Measure ℕ := Bin(n, q)
  have hμc : μ ≪ Measure.count := absolutelyContinuous_count μ
  have hνc : ν ≪ Measure.count := absolutelyContinuous_count ν
  have h_div :
      μ.rnDeriv ν =ᵐ[ν] fun k : ℕ ↦ μ.rnDeriv Measure.count k / ν.rnDeriv Measure.count k :=
    Measure.rnDeriv_eq_div hμc hνc
  have hμ_count : (fun k ↦ μ.rnDeriv Measure.count k) =ᵐ[ν] fun k ↦ μ {k} :=
    Measure.AbsolutelyContinuous.ae_eq hνc (rnDeriv_ae_eq_singleton μ)
  have hν_count : (fun k ↦ ν.rnDeriv Measure.count k) =ᵐ[ν] fun k ↦ ν {k} :=
    Measure.AbsolutelyContinuous.ae_eq hνc (rnDeriv_ae_eq_singleton ν)
  filter_upwards [h_div, hμ_count, hν_count] with k h1 h2 h3
  rw [h2, h3] at h1
  simpa [μ, ν] using h1

/-! ### Definition_7_4 (from Items/Chap07) -/
/- Definition 7.4: A convex subset of a vector space is the canonical mathlib predicate
`Convex 𝕜 G` on a set `G`, expressing closure under convex combinations of two points of `G`.
This is the owner abstraction used throughout mathlib for convexity. -/
recall Convex

/- The textbook coefficient formulation of convexity is the standard characterization
`convex_iff_add_mem`: if `x, y ∈ G` and `a, b ≥ 0` with `a + b = 1`, then
`a • x + b • y ∈ G`. Specializing to `a = λ` and `b = 1 - λ` recovers the
usual `λ x + (1 - λ) y` condition for `λ ∈ [0,1]`. -/
recall convex_iff_add_mem
