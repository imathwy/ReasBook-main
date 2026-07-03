import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_5_3_1 (from Items/Chap05) -/
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

noncomputable section

omit [IsProbabilityMeasure P] in
private lemma centered_average_eq_partialSum_centered
    (X : ℕ → Ω → ℝ) :
    centered_average P (fun n ↦ X (n + 1)) =
      fun n ω ↦
        partialSum (fun k ω ↦ X (k + 1) ω - P[X (k + 1)]) n ω / n := by
  funext n ω
  rw [centered_average, centered_partial_sum, partialSum]

-- Proof sketch: combine the pairwise-independent variance estimate for centered partial sums with
-- the bounded-variance hypothesis to obtain summable tail bounds along a dyadic subsequence, apply
-- Borel--Cantelli, and then upgrade the dyadic almost sure convergence of centered averages to the
-- full strong law.
/-- Exercise 5.3.1: the textbook sequence `X₁, X₂, …`, represented by `X 1, X 2, …`, satisfies
the strong law of large numbers as soon as its terms are pairwise independent, square integrable,
and have uniformly bounded variances. -/
theorem satisfies_strong_law_of_large_numbers_of_pairwise_indep_memLp_two_bounded_variance
    (X : ℕ → Ω → ℝ) (hX_memLp : ∀ n, MemLp (X (n + 1)) 2 P)
    (hX_pairwise_indep : Pairwise fun i j ↦ X (i + 1) ⟂ᵢ[P] X (j + 1))
    (hX_var_bdd : BddAbove (Set.range fun n : ℕ ↦ Var[X (n + 1); P])) :
    satisfies_strong_law_of_large_numbers P (fun n ↦ X (n + 1)) := by
  let Y : ℕ → Ω → ℝ := fun n ω ↦ X (n + 1) ω - P[X (n + 1)]
  have hY_memLp : ∀ n, MemLp (Y n) 2 P := by
    intro n
    exact (hX_memLp n).sub (memLp_const _)
  have hY_centered : ∀ n, P[Y n] = 0 := by
    intro n
    rw [show Y n = fun ω ↦ X (n + 1) ω - P[X (n + 1)] by rfl]
    rw [integral_sub ((hX_memLp n).integrable (by simp)) (integrable_const _)]
    simp
  have hY_uncorrelated : Pairwise fun i j ↦ cov[Y i, Y j; P] = 0 := by
    intro i j hij
    have hXi_int : Integrable (X (i + 1)) P := (hX_memLp i).integrable (by simp)
    have hXj_int : Integrable (X (j + 1)) P := (hX_memLp j).integrable (by simp)
    have hcov :
        cov[X (i + 1), X (j + 1); P] = 0 :=
      (hX_pairwise_indep hij).covariance_eq_zero (hX_memLp i) (hX_memLp j)
    simpa [Y, hXi_int, hXj_int] using hcov
  have hY_var :
      ∀ n, Var[Y n; P] = Var[X (n + 1); P] := by
    intro n
    simp [Y, variance_sub_const (hX_memLp n).aestronglyMeasurable]
  let a : ℕ → NNReal := fun n ↦ n + 1
  -- Canonical route: apply `rademacher_menshov_ae_limsup_weighted_partial_sums_eq_zero` to the
  -- centered sequence `Y` with the owner normalization `a n = n + 1`, using `hY_var` together
  -- with `hX_var_bdd` to bound the logarithmically weighted variance series, then rewrite the
  -- resulting normalized partial sums back to `centered_average` via
  -- `centered_average_eq_partialSum_centered`.
  refine ⟨fun n ↦ (hX_memLp n).integrable (by simp), ?_⟩
  sorry

/-! ### Exercise_5_3_2 (from Items/Chap05) -/
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: rewrite the event “`|X n| > n + 1` infinitely often” as membership in the limsup
-- of the tail events. For the forward implication, use the second Borel--Cantelli lemma together
-- with the i.i.d. hypothesis to force a divergent tail-probability series to give limsup measure
-- `1`; for the reverse implication, apply the first Borel--Cantelli lemma using the classical
-- tail characterization of integrability. This is internal bridge material for
-- `integrable_and_ae_eq_expectation_of_iid_ae_tendsto_average`, not a separate source-facing
-- chapter theorem.
private theorem measure_limsup_abs_gt_linear_eq_zero_iff_integrable_of_iid
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX_iid : IsIID X P) :
    P (limsup (fun n : ℕ ↦ {ω | (n + 1 : ℝ) < |X n ω|}) atTop) = 0 ↔ Integrable (X 0) P :=
  sorry

-- Proof sketch: apply the hint theorem to the shifted i.i.d. sequence `n ↦ X (n + 1)` to obtain
-- `Integrable (X 1) P` from the assumed almost sure convergence of the empirical averages. Then
-- apply the strong law of large numbers to the same shifted i.i.d. sequence and compare its almost
-- sure limit `P[X 1]` with the given almost sure limit `Y`, yielding `Y = P[X 1]` almost surely.
/-- Exercise 5.3.2: if the empirical averages of an independent identically distributed real
sequence `X₁, X₂, …` converge almost surely to a random variable `Y`, then `X₁` is integrable and
the limit `Y` is almost surely equal to the common expectation `𝔼[X₁]`. -/
theorem integrable_and_ae_eq_expectation_of_iid_ae_tendsto_average
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (h_tendsto :
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ (∑ i ∈ Finset.range n, X (i + 1) ω) / n) atTop (𝓝 (Y ω))) :
    Integrable (X 1) P ∧ Y =ᵐ[P] fun _ ↦ P[X 1] := sorry

/-! ### Exercise_5_3_3 (from Items/Chap05) -/
universe u

variable {E : Type u}

-- Proof sketch: expand `entropy` as the Shannon sum `-∑ p(e) log p(e)` and use the standard
-- inequality `x * log x ≤ 0` on `[0,1]` for each probability weight; this does not use
-- finiteness.
/-- Exercise 5.3.3 (1): entropy is bounded below by `0`. -/
theorem entropy_nonneg (p : PMF E) :
    0 ≤ entropy p := sorry

-- Proof sketch: evaluate the entropy of `PMF.pure e`; the pmf is `1` at `e` and `0` elsewhere, so
-- every summand vanishes; this does not use finiteness.
/-- Exercise 5.3.3 (2): a Dirac mass has entropy `0`. -/
theorem entropy_pure_eq_zero (e : E) :
    entropy (PMF.pure e) = 0 := by
  rw [entropy_def, tsum_eq_single e]
  · simp
  · intro e' he'
    simp [PMF.pure_apply, he']

section Fintype

variable [Fintype E]

-- Proof sketch: apply the classical finite-alphabet entropy bound, for instance via Jensen's
-- inequality for the concave function `x ↦ -x log x` under the constraint `∑ p(e) = 1`.
/-- Exercise 5.3.3 (3): on a finite set, entropy is bounded above by `log (#E)`. -/
theorem entropy_le_log_card (p : PMF E) :
    entropy p ≤ Real.log (Fintype.card E) := sorry

-- Proof sketch: compute the entropy of `PMF.uniformOfFintype E`; every atom has weight
-- `(Fintype.card E)⁻¹`, so the sum simplifies to `log (Fintype.card E)`.
/-- Exercise 5.3.3 (4): the uniform distribution on a finite nonempty set has entropy
`log (#E)`. -/
theorem entropy_uniformOfFintype_eq_log_card [Nonempty E] :
    entropy (PMF.uniformOfFintype E) = Real.log (Fintype.card E) := by
  rw [entropy_eq_sum]
  simp [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul, ENNReal.toReal_inv,
    Real.log_inv]

end Fintype

/-! ### Theorem_5_3 (from Items/Chap05) -/
open Filter MeasureTheory
open scoped Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

noncomputable section

/- Theorem 5.3 (1): Item (i). If two real random variables have the same distribution, equivalently
are identically distributed under `P`, then they have the same expectation. -/
recall ProbabilityTheory.IdentDistrib.integral_eq

/- Theorem 5.3 (2): Item (ii). For an integrable real random variable `X` and `c ∈ ℝ`, the scalar
multiple `cX` is again integrable. -/
recall MeasureTheory.Integrable.const_mul

/- Theorem 5.3 (3): Item (ii). If `X` and `Y` are integrable real random variables, then `X + Y`
is integrable as well. -/
recall MeasureTheory.Integrable.add

/- Theorem 5.3 (4): Item (ii). Expectation is homogeneous: `𝔼[cX] = c 𝔼[X]`. -/
recall MeasureTheory.integral_const_mul

/- Theorem 5.3 (5): Item (ii). Expectation is additive on integrable real random variables:
`𝔼[X + Y] = 𝔼[X] + 𝔼[Y]`. -/
recall MeasureTheory.integral_add

/- Theorem 5.3 (6): Item (iii). For a nonnegative integrable real random variable, expectation
vanishes exactly when the random variable is zero almost surely. -/
recall MeasureTheory.integral_eq_zero_iff_of_nonneg_ae

/- Theorem 5.3 (7): Item (iv). Expectation is monotone with respect to almost-sure order. -/
recall MeasureTheory.integral_mono_ae

/- Theorem 5.3 (8): Item (iv). Under an almost-sure inequality `X ≤ Y`, equality of expectations
is equivalent to almost-sure equality `X = Y`. -/
recall MeasureTheory.integral_eq_iff_of_ae_le

/- Theorem 5.3 (9): Item (v). The expectation satisfies the triangle inequality
`|𝔼[X]| ≤ 𝔼[|X|]`. -/
recall MeasureTheory.abs_integral_le_integral_abs

-- Proof sketch: apply `lintegral_tsum` to the nonnegative maps
-- `ω ↦ ENNReal.ofReal (X n ω)`, then identify each summand lower integral with the textbook
-- extended expectation `ENNReal.ofReal (∫ ω, X n ω ∂μ)` via
-- `ofReal_integral_eq_lintegral_ofReal`.
/-- Theorem 5.3 (1): Item (vi), written in the canonical lower-integral form. For a sequence of
nonnegative integrable real random variables, the lower-integral expectation of the pointwise
series is the series of the extended expectations of the summands. -/
theorem lintegral_tsum_of_nonnegative_integrable_sequence {μ : Measure Ω} {X : ℕ → Ω → ℝ}
    (hX_int : ∀ n, Integrable (X n) μ) (hX_nonneg : ∀ n, 0 ≤ᵐ[μ] X n) :
    ∫⁻ ω, ∑' n, ENNReal.ofReal (X n ω) ∂μ = ∑' n, ENNReal.ofReal (∫ ω, X n ω ∂μ) := by
  rw [lintegral_tsum fun n ↦ (hX_int n).1.aemeasurable.ennreal_ofReal]
  simp_rw [← ofReal_integral_eq_lintegral_ofReal (hX_int _) (hX_nonneg _)]

section MonotoneLimit

variable {μ : Measure Ω}
variable {ZSeq : ℕ → Ω → ℝ} {Z : Ω → ℝ}

/-- In the monotone-limit setting, the negative part of the limit is controlled by the negative
part of the first integrable term. -/
private theorem lintegral_neg_limit_lt_top_of_monotone_limit
    (hZSeq_int : ∀ n, Integrable (ZSeq n) μ)
    (h_mono : ∀ᵐ ω ∂μ, Monotone fun n ↦ ZSeq n ω)
    (h_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ZSeq n ω) atTop (𝓝 (Z ω))) :
    ∫⁻ ω, ENNReal.ofReal (-Z ω) ∂μ < ⊤ := by
  have h_le_limit : ZSeq 0 ≤ᵐ[μ] Z := by
    filter_upwards [h_mono, h_tendsto] with ω hω_mono hω_tendsto
    exact Monotone.ge_of_tendsto hω_mono hω_tendsto 0
  have hneg_bound :
      (fun ω ↦ ENNReal.ofReal (-Z ω)) ≤ᵐ[μ] fun ω ↦ ENNReal.ofReal (-ZSeq 0 ω) := by
    filter_upwards [h_le_limit] with ω hω
    exact ENNReal.ofReal_le_ofReal (neg_le_neg hω)
  exact lt_of_le_of_lt (lintegral_mono_ae hneg_bound) (hZSeq_int 0).neg.lintegral_lt_top

-- Proof sketch: shift the increasing sequence by the integrable lower bound `ZSeq 0` to obtain a
-- nonnegative monotone sequence, apply Beppo Levi to the shifted sequence, and then rewrite the
-- result in the textbook extended-expectation form as a difference of lower integrals.
/-- Theorem 5.3 (2): Item (vii). If an increasing sequence of integrable real random variables
converges almost surely to `Z`, then the expectations converge to the extended expectation of `Z`,
written canonically as the difference of the lower integrals of the positive and negative parts. -/
theorem expectation_tendsto_ereal_of_monotone_limit
    (hZSeq_int : ∀ n, Integrable (ZSeq n) μ)
    (h_mono : ∀ᵐ ω ∂μ, Monotone fun n ↦ ZSeq n ω)
    (h_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ZSeq n ω) atTop (𝓝 (Z ω))) :
    Tendsto
      (fun n ↦ ((∫ ω, ZSeq n ω ∂μ : ℝ) : EReal))
      atTop
      (𝓝
        (((∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ) : EReal) -
          ((∫⁻ ω, ENNReal.ofReal (-Z ω) ∂μ) : EReal))) := by
  have hpos :
      Tendsto (fun n ↦ ∫⁻ ω, ENNReal.ofReal (ZSeq n ω) ∂μ) atTop
        (𝓝 (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone ?_ ?_ ?_
    · intro n
      exact (hZSeq_int n).1.aemeasurable.ennreal_ofReal
    · exact h_mono.mono fun ω hω ↦
        fun i j hij ↦ ENNReal.ofReal_le_ofReal (hω hij)
    · exact h_tendsto.mono fun ω hω ↦
        (ENNReal.continuous_ofReal.tendsto _).comp hω
  have hneg :
      Tendsto (fun n ↦ ∫⁻ ω, ENNReal.ofReal (-ZSeq n ω) ∂μ) atTop
        (𝓝 (∫⁻ ω, ENNReal.ofReal (-Z ω) ∂μ)) := by
    refine lintegral_tendsto_of_tendsto_of_antitone ?_ ?_ ?_ ?_
    · intro n
      exact (hZSeq_int n).neg.1.aemeasurable.ennreal_ofReal
    · exact h_mono.mono fun ω hω ↦
        fun i j hij ↦ ENNReal.ofReal_le_ofReal (neg_le_neg (hω hij))
    · exact (hZSeq_int 0).neg.lintegral_lt_top.ne
    · exact h_tendsto.mono fun ω hω ↦
        (ENNReal.continuous_ofReal.tendsto _).comp (Filter.Tendsto.neg hω)
  have hneg_limit_ne_top : ∫⁻ ω, ENNReal.ofReal (-Z ω) ∂μ ≠ ⊤ :=
    (lintegral_neg_limit_lt_top_of_monotone_limit hZSeq_int h_mono h_tendsto).ne
  have hpos_ereal :
      Tendsto (fun n ↦ ((∫⁻ ω, ENNReal.ofReal (ZSeq n ω) ∂μ) : EReal)) atTop
        (𝓝 (((∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ) : EReal))) := by
    simpa using EReal.tendsto_coe_ennreal.2 hpos
  have hneg_ereal :
      Tendsto (fun n ↦ ((∫⁻ ω, ENNReal.ofReal (-ZSeq n ω) ∂μ) : EReal)) atTop
        (𝓝 (((∫⁻ ω, ENNReal.ofReal (-Z ω) ∂μ) : EReal))) := by
    simpa using EReal.tendsto_coe_ennreal.2 hneg
  have hneg_ereal_neg :
      Tendsto
        (fun n ↦ -(((∫⁻ ω, ENNReal.ofReal (-ZSeq n ω) ∂μ) : EReal))) atTop
        (𝓝 (-(((∫⁻ ω, ENNReal.ofReal (-Z ω) ∂μ) : EReal)))) := by
    exact Filter.Tendsto.neg hneg_ereal
  have hterm :
      (fun n ↦ ((∫ ω, ZSeq n ω ∂μ : ℝ) : EReal)) =
        fun n ↦
          (((∫⁻ ω, ENNReal.ofReal (ZSeq n ω) ∂μ) : EReal) -
            ((∫⁻ ω, ENNReal.ofReal (-ZSeq n ω) ∂μ) : EReal)) := by
    funext n
    have hpos_ne_top : ∫⁻ ω, ENNReal.ofReal (ZSeq n ω) ∂μ ≠ ⊤ :=
      (hZSeq_int n).lintegral_lt_top.ne
    have hneg_ne_top : ∫⁻ ω, ENNReal.ofReal (-ZSeq n ω) ∂μ ≠ ⊤ :=
      (hZSeq_int n).neg.lintegral_lt_top.ne
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hZSeq_int n)]
    rw [← EReal.coe_ennreal_toReal hpos_ne_top, ← EReal.coe_ennreal_toReal hneg_ne_top]
    norm_num
  rw [hterm]
  simpa [sub_eq_add_neg] using
    (EReal.continuousAt_add
      (Or.inr <| by simpa [EReal.neg_eq_bot_iff] using hneg_limit_ne_top)
      (Or.inl <| EReal.coe_ennreal_ne_bot (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ))).tendsto.comp
      (hpos_ereal.prodMk_nhds hneg_ereal_neg)

-- Proof sketch: the monotone limit dominates the first integrable term `ZSeq 0`, so its negative
-- part is controlled by the integrable function `-ZSeq 0`. This rules out the value `-∞` for the
-- extended expectation computed in the previous clause.
/-- Theorem 5.3 (3): Item (vii). In the monotone convergence situation, the extended expectation
of the limit belongs to `(-∞, ∞]`, equivalently it is not equal to `-∞`. -/
theorem extended_expectation_ne_bot_of_monotone_limit
    (hZSeq_int : ∀ n, Integrable (ZSeq n) μ)
    (h_mono : ∀ᵐ ω ∂μ, Monotone fun n ↦ ZSeq n ω)
    (h_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ZSeq n ω) atTop (𝓝 (Z ω))) :
    (((∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ) : EReal) -
        ((∫⁻ ω, ENNReal.ofReal (-Z ω) ∂μ) : EReal)) ≠ ⊥ := by
  have hneg_lt_top : ∫⁻ ω, ENNReal.ofReal (-Z ω) ∂μ < ⊤ :=
    lintegral_neg_limit_lt_top_of_monotone_limit hZSeq_int h_mono h_tendsto
  have hpos_ne_bot : (((∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ) : ENNReal) : EReal) ≠ ⊥ :=
    EReal.coe_ennreal_ne_bot _
  have hneg_ne_top : (((∫⁻ ω, ENNReal.ofReal (-Z ω) ∂μ) : ENNReal) : EReal) ≠ ⊤ := by
    intro h_top
    exact hneg_lt_top.ne (EReal.coe_ennreal_eq_top_iff.1 h_top)
  intro h_bot
  rw [sub_eq_add_neg, EReal.add_eq_bot_iff] at h_bot
  rcases h_bot with h_bot | h_bot
  · exact hpos_ne_bot h_bot
  · exact hneg_ne_top ((EReal.neg_eq_bot_iff.1 h_bot))

end MonotoneLimit

/-! ### Exercise_5_3_4 (from Items/Chap05) -/
open scoped BigOperators

universe u v

variable {E₁ : Type u} {E₂ : Type v} [Finite E₁] [Finite E₂]

-- Proof sketch: compare the joint law `p` with the product of its two marginal laws and apply the
-- nonnegativity of relative entropy (equivalently, the cross-entropy bound) to obtain
-- `H(p) ≤ H(p.map Prod.fst) + H(p.map Prod.snd)`.
/-- Exercise 5.3.4: the entropy of a joint probability mass function on a finite product is at
most the sum of the entropies of its two marginal probability mass functions. -/
theorem entropy_le_entropy_map_fst_add_entropy_map_snd
    (p : PMF (E₁ × E₂)) :
    entropy p ≤ entropy (p.map Prod.fst) + entropy (p.map Prod.snd) := by
  let b : LogBase := ⟨Real.exp 1, Real.exp_pos 1, ne_of_gt (Real.one_lt_exp_iff.2 zero_lt_one)⟩
  let p₁ : PMF E₁ := p.map Prod.fst
  let p₂ : PMF E₂ := p.map Prod.snd
  let q : E₁ × E₂ → ENNReal := fun x ↦ p₁ x.1 * p₂ x.2
  have hq : (∑' x : E₁ × E₂, q x) ≤ 1 := by
    sorry
  have hcross : crossEntropyInBase b p q = entropy p₁ + entropy p₂ := by
    sorry
  calc
    entropy p = entropyInBase b p := by
      simp [b]
    _ ≤ crossEntropyInBase b p q :=
      entropyInBase_le_crossEntropyInBase b (by
        change 1 < Real.exp 1
        exact Real.one_lt_exp_iff.2 zero_lt_one) p q hq
    _ = entropy p₁ + entropy p₂ := hcross

/-! ### Exercise_5_3_5 (from Items/Chap05) -/
open scoped BigOperators

universe u

/-- Helper for the base-`b` source-coding exercise: a natural base `b ≥ 2` gives a real
logarithmic base `> 1`. -/
private theorem nat_base_one_lt (b : ℕ) (hb : 2 ≤ b) : (1 : ℝ) < b := by
  have h : (1 : ℕ) < b := lt_of_lt_of_le one_lt_two hb
  exact_mod_cast h

/-- The logarithmic base attached to a natural base `b ≥ 2`. -/
def nat_base (b : ℕ) (hb : 2 ≤ b) : LogBase :=
  ⟨b, by positivity, ne_of_gt (nat_base_one_lt b hb)⟩

variable {E : Type u}

-- Proof sketch: apply the same Kraft-inequality and cross-entropy argument as in the binary case,
-- replacing the binary weights `2 ^ (-length)` by the `b`-ary weights `b ^ (-length)` and the
-- logarithm base `2` by base `b`.
/-- Exercise 5.3.5 (1): for a finite alphabet, the expected length of a prefix code over the digit
alphabet `Fin b` is
bounded below by the real value of the base-`b` entropy `H_b(p)` of the source law. -/
theorem entropy_in_nat_base_le_expected_length_of_b_adic_prefix_code [Fintype E]
    (b : ℕ) (hb : 2 ≤ b) (p : PMF E) (C : PrefixCode (Fin b) E) :
    (entropyInBase (nat_base b hb) p).toReal ≤ C.expectedLength p := sorry

-- Proof sketch: choose Shannon lengths `l(e) = ⌈-log_b p(e)⌉`, verify the `b`-ary Kraft
-- inequality, and build a `b`-adic prefix code with these lengths to obtain the usual `+ 1`
-- overhead bound.
/-- Exercise 5.3.5 (2): for a finite alphabet, there exists a prefix code over `Fin b` whose
expected length is at most the base-`b` entropy `H_b(p)` plus `1`. -/
theorem exists_b_adic_prefix_code_expected_length_le_entropy_in_nat_base_add_one [Fintype E]
    (b : ℕ) (hb : 2 ≤ b) (p : PMF E) :
    ∃ C : PrefixCode (Fin b) E,
      C.expectedLength p ≤ (entropyInBase (nat_base b hb) p).toReal + 1 := sorry

/-! ### Exercise_5_3_6 (from Items/Chap05) -/
open scoped BigOperators

/-- The 26 letters of the Latin alphabet used in the Morse-code table of the exercise. -/
inductive MorseLetter
  | A | B | C | D | E | F | G | H | I | J | K | L | M
  | N | O | P | Q | R | S | T | U | V | W | X | Y | Z
  deriving DecidableEq, Fintype

/-- The German letter frequencies from the Morse-code table in Exercise 5.3.6. -/
noncomputable def morseGermanWeight : MorseLetter → ENNReal
  | .A => 651 / 10000
  | .B => 189 / 10000
  | .C => 306 / 10000
  | .D => 508 / 10000
  | .E => 1740 / 10000
  | .F => 166 / 10000
  | .G => 301 / 10000
  | .H => 476 / 10000
  | .I => 755 / 10000
  | .J => 27 / 10000
  | .K => 121 / 10000
  | .L => 344 / 10000
  | .M => 253 / 10000
  | .N => 978 / 10000
  | .O => 251 / 10000
  | .P => 79 / 10000
  | .Q => 2 / 10000
  | .R => 7 / 100
  | .S => 727 / 10000
  | .T => 615 / 10000
  | .U => 435 / 10000
  | .V => 67 / 10000
  | .W => 189 / 10000
  | .X => 3 / 10000
  | .Y => 4 / 10000
  | .Z => 113 / 10000

-- Proof sketch: expand the finite sum over all 26 letters and check that the listed decimal
-- frequencies add up to `1`.
/-- The Morse-code frequency table defines a probability mass function on the alphabet. -/
theorem morseGermanWeight_sum : ∑ a : MorseLetter, morseGermanWeight a = 1 := sorry

/-- The German letter-frequency law from Exercise 5.3.6 as a probability mass function. -/
noncomputable def morseGermanPMF : PMF MorseLetter :=
  PMF.ofFintype morseGermanWeight morseGermanWeight_sum

/-- The ternary Morse code from Exercise 5.3.6, with `0 = dot`, `1 = dash`, and `2` the
terminating pause symbol. -/
def morseCodeWord : MorseLetter → List (Fin 3)
  | .A => [0, 1, 2]
  | .B => [1, 0, 0, 0, 2]
  | .C => [1, 0, 1, 0, 2]
  | .D => [1, 0, 0, 2]
  | .E => [0, 2]
  | .F => [0, 0, 1, 0, 2]
  | .G => [1, 1, 0, 2]
  | .H => [0, 0, 0, 0, 2]
  | .I => [0, 0, 2]
  | .J => [0, 1, 1, 1, 2]
  | .K => [1, 0, 1, 2]
  | .L => [0, 1, 0, 0, 2]
  | .M => [1, 1, 2]
  | .N => [1, 0, 2]
  | .O => [1, 1, 1, 2]
  | .P => [0, 1, 1, 0, 2]
  | .Q => [1, 1, 0, 1, 2]
  | .R => [0, 1, 0, 2]
  | .S => [0, 0, 0, 2]
  | .T => [1, 2]
  | .U => [0, 0, 1, 2]
  | .V => [0, 0, 0, 1, 2]
  | .W => [0, 1, 1, 2]
  | .X => [1, 0, 0, 1, 2]
  | .Y => [1, 0, 1, 1, 2]
  | .Z => [1, 1, 0, 0, 2]

/-- The Morse code is prefix-free once the terminating pause symbol is included. -/
theorem morseCodeWord_prefix_free :
    Pairwise fun a b : MorseLetter ↦ ¬ (morseCodeWord a <+: morseCodeWord b) := by
  simpa [Pairwise] using
    (show ∀ a b : MorseLetter, a ≠ b → ¬ (morseCodeWord a <+: morseCodeWord b) by
      decide)

/-- The ternary Morse code as a prefix code over the digit alphabet `Fin 3`. -/
def morseCode : PrefixCode (Fin 3) MorseLetter where
  encode := morseCodeWord
  prefix_free := morseCodeWord_prefix_free

-- Proof sketch: unfold `PrefixCode.expectedLength`, substitute the 26 values from the table, and
-- evaluate the resulting rational sum.
/-- The average ternary Morse-code length for the German frequency table is `3.4429`. -/
theorem morseAverageCodeLength_eq :
    morseCode.expectedLength morseGermanPMF = (34429 : ℝ) / 10000 := sorry

-- Proof sketch: use `morseAverageCodeLength_eq` for the explicit average length, then compare it
-- with the base-`3` entropy sum for `morseGermanPMF`.
/-- Exercise 5.3.6: For the German letter frequencies, the Morse code has average ternary length
`3.4429`, and the ternary entropy `H₃` is bounded above by this average length. -/
theorem morse_code_average_length_and_entropy_comparison :
    morseCode.expectedLength morseGermanPMF = (34429 : ℝ) / 10000 ∧
      (entropyInBase (nat_base 3 (show 2 ≤ 3 by norm_num)) morseGermanPMF).toReal ≤
        morseCode.expectedLength
        morseGermanPMF := by
  refine ⟨morseAverageCodeLength_eq, ?_⟩
  simpa using
    entropy_in_nat_base_le_expected_length_of_b_adic_prefix_code 3
      (show 2 ≤ 3 by norm_num) morseGermanPMF morseCode
