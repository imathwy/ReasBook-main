import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

universe u

noncomputable section

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/- 
Domain-style sampling for Exercise 17.3.2:
- `IsExchangeable` in Chapter 12 is the source-facing owner for exchangeable sequences.
- `IsConditionallyBernoulliIID` in `Example_12_3` is the canonical Bernoulli-mixture bridge used
  for `{0,1}`-valued processes.
- `exists_conditionalBernoulliParameter_of_isExchangeable` in `Example_12_28` is the owner-level
  bridge from exchangeability to a Bernoulli directing parameter.
- `weightedUrnClockLaw` and `weightedUrnClockLaw_ae_eventually_single_color` in `Example_17_27`
  are the source-facing exponential-clock realization of the weighted Pólya urn.

Best owner abstraction:
- this file remains `source-facing`: `IsGeneralizedPolyaUrnWithWeights` is the owner for the
  textbook cylinder-probability specification of the generalized weighted urn process;
- the exponential-clock construction from Example 17.27 is a `bridge/view` under stronger
  realization hypotheses, not a replacement for this owner.

Primitive data:
- the ambient measure `μ`, the weight sequence `w`, and the `{0,1}`-valued process `X`.

Derived API:
- coordinate measurability and the one-step cylinder-probability formula are derived accessors of
  `IsGeneralizedPolyaUrnWithWeights`, not separate owner declarations.
-/

/-- The cylinder event that the first `n` draws of the urn process `X` match the prescribed
black/red pattern `x`, with `true` encoding a black draw and `false` a red draw. -/
def weightedUrnPrefixEvent (X : ℕ → Ω → Bool) {n : ℕ} (x : Fin n → Bool) : Set Ω :=
  {ω | ∀ i : Fin n, X i ω = x i}

/-- The number of black draws in a finite prefix `x`, where `true` encodes black. -/
def blackPrefixCount {n : ℕ} (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin n ↦ x i = true).card

/-- A `{0,1}`-valued process is the generalized two-color Pólya urn from Example 17.27 with
weight sequence `w` if every coordinate is measurable and each one-step cylinder probability is
given by the ratio `w_ℓ / (w_ℓ + w_{n-ℓ})`, where `ℓ` is the number of black draws seen so far. -/
def IsGeneralizedPolyaUrnWithWeights
    (μ : Measure Ω) (w : ℕ → NNReal) (X : ℕ → Ω → Bool) : Prop :=
  (∀ n : ℕ, Measurable (X n)) ∧
    ∀ ⦃n : ℕ⦄ (x : Fin n → Bool),
      let ℓ := blackPrefixCount x
      μ (weightedUrnPrefixEvent X x ∩ {ω | X n ω = true}) =
        (((w ℓ) / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ (weightedUrnPrefixEvent X x)

namespace IsGeneralizedPolyaUrnWithWeights

-- Proof sketch: measurability is part of the defining data of
-- `IsGeneralizedPolyaUrnWithWeights`; unpack the first conjunct.
/-- Every coordinate of a generalized weighted Pólya-urn draw sequence is measurable. -/
theorem measurable
    {μ : Measure Ω} {w : ℕ → NNReal} {X : ℕ → Ω → Bool}
    (hX : IsGeneralizedPolyaUrnWithWeights μ w X) (n : ℕ) :
    Measurable (X n) :=
  hX.1 n

/-- The defining one-step cylinder probability formula of a generalized weighted Pólya urn. -/
theorem prefixEvent_inter_true_eq
    {μ : Measure Ω} {w : ℕ → NNReal} {X : ℕ → Ω → Bool}
    (hX : IsGeneralizedPolyaUrnWithWeights μ w X) {n : ℕ} (x : Fin n → Bool) :
    let ℓ := blackPrefixCount x
    μ (weightedUrnPrefixEvent X x ∩ {ω | X n ω = true}) =
      (((w ℓ) / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ (weightedUrnPrefixEvent X x) :=
  hX.2 x

end IsGeneralizedPolyaUrnWithWeights

-- Proof sketch: use the exponential-clock embedding from Example 17.27. When
-- `∑ (w n)⁻¹ = ∞`, the independent explosion times for the red and black clocks are both almost
-- surely infinite, so neither color can stop appearing after finitely many draws.
/-- Exercise 17.3.2: in the generalized two-color Pólya urn of Example 17.27 with one red and one
black initial ball and weight sequence `w`, if `∑ 1 / w_n = ∞`, then almost surely the draw
sequence contains infinitely many black draws and infinitely many red draws. -/
theorem ae_infinitely_many_draws_each_color_of_tsum_inv_weights_eq_top
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → Bool) (w : ℕ → NNReal)
    (hX : IsGeneralizedPolyaUrnWithWeights μ w X) (hw_pos : ∀ n : ℕ, 0 < w n)
    (hw_div : (∑' n : ℕ, ((w n : ℝ≥0∞)⁻¹)) = ∞) :
    ∀ᵐ ω ∂μ, {n : ℕ | X n ω = true}.Infinite ∧ {n : ℕ | X n ω = false}.Infinite := sorry

end ProbabilityTheory
