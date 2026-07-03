import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap12.Example_12_3
import ProbabilityTheory_Klenke_2020.Items.Chap17.Exercise_17_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/- Domain-style sampling for Exercise 17.3.1:
- `weightedUrnPrefixEvent` and `blackPrefixCount` in `Exercise_17_3_2` are the Chapter 17
  primitive prefix-event and black-count declarations for Boolean-valued urn words.
- `IsGeneralizedPolyaUrnWithWeights` in `Exercise_17_3_2` is the nearby owner abstraction for the
  symmetric weighted urn with one common weight sequence. It is relevant domain style, but it is
  not the exact owner here because Exercise 17.3.1 has separate constant reinforcement parameters
  `r` and `s` for red and black draws and asks about the literal fraction of black balls in the
  urn.
- `IsConditionallyBernoulliIID` in `Example_12_3` is the canonical Chapter 12 bridge for a
  Bernoulli directing parameter.

Best owner abstraction:
- this file remains `source-facing`: the public owner is the constant-reinforcement generalized
  two-color urn with initial red/black counts `R`,`S` and reinforcement parameters `r`,`s`,
  encoded by the actual next-draw law coming from the current urn counts;
- `weightedUrnPrefixEvent` and `blackPrefixCount` are reused as the primitive prefix API instead
  of duplicated locally;
- `IsConditionallyBernoulliIID` is a downstream `bridge/view` consequence of this owner, not a
  replacement for it.

Primitive data:
- the measure `μ`, the initial red and black counts `R`,`S`, the constant reinforcement
  parameters `r`,`s`, and the `{0,1}`-valued draw process `X`.

Derived API:
- coordinate measurability and the one-step cylinder-probability formula are accessors of the
  owner abstraction;
- the fraction of black balls is the literal urn fraction
  `(S + s * L_n) / (R + S + r * (n - L_n) + s * L_n)`, where `L_n` is the black draw count in the
  first `n` draws;
- the Beta-law, conditional Bernoulli description, and almost-sure convergence statements are kept
  as source-facing exercise conclusions over that owner.
-/

/-- The source-facing fraction of black balls in the urn after the first `n` draws. If
`L_n(ω)` is the number of black draws among `X 0 ω, …, X (n - 1) ω`, then the urn contains
`S + s * L_n(ω)` black balls and `R + r * (n - L_n(ω))` red balls. -/
noncomputable def generalizedPolyaUrnBlackBallFraction
    (R S r s : ℕ) (X : ℕ → Ω → Bool) (n : ℕ) (ω : Ω) : ℝ :=
  let ℓ := blackPrefixCount (fun i : Fin n ↦ X i ω)
  (((S + s * ℓ : ℕ) : ℝ) / ((R + S + r * (n - ℓ) + s * ℓ : ℕ) : ℝ))

/-- A `{0,1}`-valued process is the constant-reinforcement generalized two-color Pólya urn with
initial red/black counts `R`,`S` and reinforcement parameters `r`,`s` if every coordinate is
measurable and, after a prefix `x` of length `n` with `ℓ` black draws, the next draw is black
with probability equal to the actual fraction of black balls currently present in the urn,
namely `(S + s * ℓ) / (R + S + r * (n - ℓ) + s * ℓ)`. -/
def IsGeneralizedPolyaUrn
    (μ : Measure Ω) (R S r s : ℕ) (X : ℕ → Ω → Bool) : Prop :=
  (∀ n : ℕ, Measurable (X n)) ∧
    ∀ ⦃n : ℕ⦄ (x : Fin n → Bool),
      let ℓ := blackPrefixCount x
      μ (weightedUrnPrefixEvent X x ∩ {ω | X n ω = true}) =
        ((((S + s * ℓ : ℕ) : NNReal) /
            ((R + S + r * (n - ℓ) + s * ℓ : ℕ) : NNReal)) : ℝ≥0∞) *
          μ (weightedUrnPrefixEvent X x)

namespace IsGeneralizedPolyaUrn

variable {μ : Measure Ω} {R S r s : ℕ} {X : ℕ → Ω → Bool}

/-- Every coordinate of a constant-reinforcement generalized Pólya urn is measurable. -/
theorem measurable
    (hX : IsGeneralizedPolyaUrn μ R S r s X) (n : ℕ) :
    Measurable (X n) :=
  hX.1 n

/-- The defining one-step cylinder probability formula of the literal generalized Pólya urn. -/
theorem prefixEvent_inter_true_eq
    (hX : IsGeneralizedPolyaUrn μ R S r s X) {n : ℕ} (x : Fin n → Bool) :
    let ℓ := blackPrefixCount x
    μ (weightedUrnPrefixEvent X x ∩ {ω | X n ω = true}) =
      ((((S + s * ℓ : ℕ) : NNReal) /
          ((R + S + r * (n - ℓ) + s * ℓ : ℕ) : NNReal)) : ℝ≥0∞) *
        μ (weightedUrnPrefixEvent X x) :=
  hX.2 x

/-- Exercise 17.3.1: the generalized urn admits a directing random parameter `Z ∈ [0,1]` such
that, conditionally on `Z`, the draws are i.i.d. Bernoulli with parameter `Z`. -/
theorem exists_conditionalBernoulliParameter
    [IsProbabilityMeasure μ] [StandardBorelSpace Ω]
    (hX : IsGeneralizedPolyaUrn μ R S r s X) :
    ∃ Z : Ω → unitInterval,
      IsConditionallyBernoulliIID Z X μ := sorry

end IsGeneralizedPolyaUrn

/-- Exercise 17.3.1: the directing parameter of the generalized Pólya urn has Beta law with the
parameters determined by the initial counts and constant reinforcements. -/
theorem generalizedPolyaUrn_limit_hasLaw_beta
    {μ : Measure Ω} [IsProbabilityMeasure μ] [StandardBorelSpace Ω]
    {X : ℕ → Ω → Bool}
    {R S r s : ℕ} (hX : IsGeneralizedPolyaUrn μ R S r s X)
    (hR : 0 < R) (hS : 0 < S) (hr : 0 < r) (hs : 0 < s) :
    ∃ Z : Ω → unitInterval,
      IsConditionallyBernoulliIID Z X μ ∧
        HasLaw (fun ω ↦ (Z ω : ℝ))
          (betaMeasure ((S : ℝ) / (s : ℝ)) ((R : ℝ) / (r : ℝ))) μ := sorry

/-- Exercise 17.3.1: the actual fraction of black balls in the urn converges almost surely to a
Beta-distributed directing random variable `Z`, and conditionally on `Z` the draw sequence is
i.i.d. Bernoulli with parameter `Z`. -/
theorem generalizedPolyaUrn_blackBallFraction_ae_tendsto_limit
    {μ : Measure Ω} [IsProbabilityMeasure μ] [StandardBorelSpace Ω]
    {X : ℕ → Ω → Bool}
    {R S r s : ℕ} (hX : IsGeneralizedPolyaUrn μ R S r s X)
    (hR : 0 < R) (hS : 0 < S) (hr : 0 < r) (hs : 0 < s) :
    ∃ Z : Ω → unitInterval,
      IsConditionallyBernoulliIID Z X μ ∧
        HasLaw (fun ω ↦ (Z ω : ℝ))
          (betaMeasure ((S : ℝ) / (s : ℝ)) ((R : ℝ) / (r : ℝ))) μ ∧
        ∀ᵐ ω ∂μ,
          Tendsto (fun n ↦ generalizedPolyaUrnBlackBallFraction R S r s X n ω) atTop
            (𝓝 (Z ω : ℝ)) := sorry

/-- At time `0`, the black-ball fraction is the initial proportion `S / (R + S)`. -/
@[simp] theorem generalizedPolyaUrnBlackBallFraction_zero
    {Ω' : Type u} [MeasurableSpace Ω']
    (R S r s : ℕ) (X : ℕ → Ω' → Bool) (ω : Ω') :
    generalizedPolyaUrnBlackBallFraction R S r s X 0 ω =
      (S : ℝ) / ((R + S : ℕ) : ℝ) := by
  simp [generalizedPolyaUrnBlackBallFraction]
