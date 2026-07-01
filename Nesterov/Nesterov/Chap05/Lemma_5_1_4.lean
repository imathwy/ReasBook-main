import Nesterov.Chap05.Definition_5_0_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set
open scoped SelfConcordantAuxiliaryFunction

/- Lemma 5.1.4 belongs to the one-variable self-concordant auxiliary-function / Fenchel-conjugacy
domain.

Relevant owner-style declarations sampled before refinement:
* `selfConcordantOmega`, `selfConcordantOmegaStar`, `selfConcordantOmegaDeriv`, and
  `selfConcordantOmegaPrimeStar` in `Definition_5_0_21`, the chapter owners for `ω`, `ω_*`,
  `ω'`, and `ω'_*`;
* `selfConcordantOmegaArg` and `selfConcordantOmegaStarArg` in `Definition_5_0_21`, the
  canonical Chapter 5 constructors for the natural `ω` and `ω_*` subtype arguments;
* `fenchelDual` in `Definition_5_0_27`, the project-level canonical owner for Fenchel conjugacy in
  higher dimension;
* `IsMaxOn` in mathlib, the canonical owner-level maximizer predicate behind the scalar Fenchel
  support formulas.

Best owner abstraction:
* source-facing: the fixed chapter owners `ω`, `ω_*`, together with their explicit derivative and
  inverse branches `ω'`, `ω'_*`, and the textbook maximization identities built from them;
* core/canonical: the already-defined chapter auxiliary functions from `Definition_5_0_21`;
* bridge/view: the explicit scalar formulas specialized to those owners.

Primitive data:
* `ω`;
* `ω_*`.

Derived API:
* `ω'` and `ω'_*`;
* the canonical subtype constructors `selfConcordantOmegaArg` and
  `selfConcordantOmegaStarArg`;
* the domain-membership lemmas for `ω'` and `ω'_*`;
* the seven source-facing Fenchel-conjugacy identities of Lemma 5.1.4, stated directly against
  the canonical owners on their mathematically forced domains: the full owner domains for the
  inverse identities `(1)`, `(2)`, `(6)`, `(7)`, and the constrained nonnegative maximization
  regimes for `(3)`, `(4)`, `(5)`, without a parallel local point/maximand wrapper API; the
  maximizer data for parts `(3)` and `(4)` is carried by the numbered statements themselves. -/

theorem neg_one_lt_selfConcordantUnit_of_nonneg {t : ℝ} (ht : 0 ≤ t) : -1 < t := by
  have h : -1 < ((1 : NNReal) : ℝ) * t := neg_one_lt_mf_mul_of_nonneg ht
  simpa using h

/-- For `t ≥ 0`, the derivative branch `ω'(t)` is nonnegative. -/
theorem selfConcordantOmegaDeriv_nonneg {t : ℝ} (ht : 0 ≤ t) :
    let tω := selfConcordantOmegaArg 1 t (by
      simpa using neg_one_lt_selfConcordantUnit_of_nonneg ht)
    0 ≤ ω' tω := sorry

/-- On its natural domain `(-1, ∞)`, the derivative branch `ω'(t)` lies below `1`. -/
theorem selfConcordantOmegaDeriv_lt_one (tω : Ioi (-1 : ℝ)) :
    ω' tω < 1 := sorry

/-- For `t ≥ 0`, the derivative branch `ω'(t)` belongs to the slope interval `[0, 1)`. -/
theorem selfConcordantOmegaDeriv_mem_Ico {t : ℝ} (ht : 0 ≤ t) :
    let tω := selfConcordantOmegaArg 1 t (by
      simpa using neg_one_lt_selfConcordantUnit_of_nonneg ht)
    ω' tω ∈ Ico (0 : ℝ) 1 := sorry

/-- For `τ ∈ [0, 1)`, the inverse branch `ω'_*(τ)` is nonnegative. -/
theorem selfConcordantOmegaPrimeStar_nonneg {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    0 ≤ ω'_* ⟨τ, hτ1⟩ := sorry

/-- On its natural domain `(-∞, 1)`, the inverse branch `ω'_*(τ)` lies above `-1`. -/
theorem selfConcordantOmegaPrimeStar_gt_neg_one (τω : Iio (1 : ℝ)) :
    -1 < ω'_* τω := sorry

-- Proof sketch: substitute the explicit formulas
-- `ω'(t) = t / (1 + t)` and `ω'_*(τ) = τ / (1 - τ)` and simplify.
/-- Lemma 5.1.4 (1): for `τ < 1`, applying `ω'` to `ω'_*(τ)` returns `τ`. -/
theorem selfConcordantOmegaDeriv_selfConcordantOmegaPrimeStar
    {τ : ℝ} (hτ1 : τ < 1) :
    let τω := selfConcordantOmegaStarArg 1 τ (by simpa using hτ1)
    let tω := selfConcordantOmegaArg 1 (ω'_* τω) (by
      simpa using selfConcordantOmegaPrimeStar_gt_neg_one τω)
    ω' tω = τ := sorry

-- Proof sketch: substitute the explicit formulas
-- `ω'(t) = t / (1 + t)` and `ω'_*(τ) = τ / (1 - τ)` and simplify.
/-- Lemma 5.1.4 (2): for `t > -1`, applying `ω'_*` to `ω'(t)` returns `t`. -/
theorem selfConcordantOmegaPrimeStar_selfConcordantOmegaDeriv
    {t : ℝ} (ht : -1 < t) :
    let tω := selfConcordantOmegaArg 1 t (by
      simpa using ht)
    let τω := selfConcordantOmegaStarArg 1 (ω' tω) (by
      simpa using selfConcordantOmegaDeriv_lt_one tω)
    ω'_* τω = t := sorry

-- Proof sketch: evaluate the support functional `ξ ↦ ξ * t - ω_*(ξ)` at its canonical maximizer
-- `ξ = ω'(t)`.
/-- Lemma 5.1.4 (3): for `t ≥ 0`, the value `ω(t)` is the maximal value of the Fenchel support
functional `ξ ↦ ξ t - ω_*(ξ)` on `[0, 1)`, realized at `ξ = ω'(t)`. -/
theorem selfConcordantOmega_eq_mul_selfConcordantOmegaDeriv_sub_selfConcordantOmegaStar_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) :
    let tω := selfConcordantOmegaArg 1 t (by
      simpa using neg_one_lt_selfConcordantUnit_of_nonneg ht)
    let ξω := selfConcordantOmegaStarArg 1 (ω' tω) (by
      simpa using selfConcordantOmegaDeriv_lt_one tω)
    ξω ∈ {ξ : Iio (1 : ℝ) | 0 ≤ (ξ : ℝ)} ∧
      IsMaxOn
        (fun ξ : Iio (1 : ℝ) ↦ (ξ : ℝ) * t - ω_* ξ)
        {ξ : Iio (1 : ℝ) | 0 ≤ (ξ : ℝ)} ξω ∧
      ω tω = t * ω' tω - ω_* ξω := sorry

-- Proof sketch: evaluate the support functional `ξ ↦ τ * ξ - ω(ξ)` at its canonical maximizer
-- `ξ = ω'_*(τ)`.
/-- Lemma 5.1.4 (4): for `τ ∈ [0, 1)`, the value `ω_*(τ)` is the maximal value of the Fenchel
support functional `ξ ↦ τ ξ - ω(ξ)` on `[0, ∞)`, realized at `ξ = ω'_*(τ)`. -/
theorem
    selfConcordantOmegaStar_eq_mul_selfConcordantOmegaPrimeStar_sub_selfConcordantOmega_of_mem_Ico
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    let τω := selfConcordantOmegaStarArg 1 τ (by simpa using hτ1)
    let tω := selfConcordantOmegaArg 1 (ω'_* τω) (by
      simpa using selfConcordantOmegaPrimeStar_gt_neg_one τω)
    tω ∈ {ξ : Ioi (-1 : ℝ) | 0 ≤ (ξ : ℝ)} ∧
      IsMaxOn
        (fun ξ : Ioi (-1 : ℝ) ↦ τ * (ξ : ℝ) - ω ξ)
        {ξ : Ioi (-1 : ℝ) | 0 ≤ (ξ : ℝ)} tω ∧
      ω_* τω = τ * ω'_* τω - ω tω := sorry

-- Proof sketch: combine the supremum characterization of `ω_*(τ)` with the admissible test point
-- `t`.
/-- Lemma 5.1.4 (5): the Fenchel--Young inequality
`ω(t) + ω_*(τ) ≥ τ t` holds for `t ≥ 0` and `τ < 1`. -/
theorem selfConcordantOmega_add_selfConcordantOmegaStar_ge_mul
    {t τ : ℝ} (ht : 0 ≤ t) (hτ1 : τ < 1) :
    let tω := selfConcordantOmegaArg 1 t (by
      simpa using neg_one_lt_selfConcordantUnit_of_nonneg ht)
    let τω := selfConcordantOmegaStarArg 1 τ (by simpa using hτ1)
    ω tω + ω_* τω ≥ τ * t := sorry

-- Proof sketch: evaluate the maximization formula for `ω_*(τ)` at the maximizing point
-- `ξ = ω'_*(τ)`.
/-- Lemma 5.1.4 (6): for `τ < 1`, the conjugate value is
`ω_*(τ) = τ ω'_*(τ) - ω(ω'_*(τ))`. -/
theorem selfConcordantOmegaStar_eq_mul_selfConcordantOmegaPrimeStar_sub_selfConcordantOmega
    {τ : ℝ} (hτ1 : τ < 1) :
    let τω := selfConcordantOmegaStarArg 1 τ (by simpa using hτ1)
    let tω := selfConcordantOmegaArg 1 (ω'_* τω) (by
      simpa using selfConcordantOmegaPrimeStar_gt_neg_one τω)
    ω_* τω = τ * ω'_* τω - ω tω := sorry

-- Proof sketch: substitute `τ = ω'(t)` into part `(6)` and use part `(2)` to identify the
-- maximizing point.
/-- Lemma 5.1.4 (7): for `t > -1`, the original function value can be recovered from the conjugate
by `ω(t) = t ω'(t) - ω_*(ω'(t))`. -/
theorem selfConcordantOmega_eq_mul_selfConcordantOmegaDeriv_sub_selfConcordantOmegaStar
    {t : ℝ} (ht : -1 < t) :
    let tω := selfConcordantOmegaArg 1 t (by
      simpa using ht)
    let τω := selfConcordantOmegaStarArg 1 (ω' tω) (by
      simpa using selfConcordantOmegaDeriv_lt_one tω)
    ω tω = t * ω' tω - ω_* τω := sorry

end
