import Mathlib
import AchimKlenkeLean.Items.Chap02.Definition_2_14
import AchimKlenkeLean.Items.Chap12.Definition_12_20
import AchimKlenkeLean.Items.Chap12.Remark_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory unitInterval

universe u v w

/-- The set of binary words of length `N` containing exactly `M` black entries. -/
def blackIndicatorWordSet (N M : ℕ) : Set (Fin N → Bool) :=
  {x | (Finset.univ.filter fun i : Fin N ↦ x i).card = M}

/-- A `Bool`-valued family is conditionally i.i.d. Bernoulli with parameter `Y`: this is the
source-facing Bernoulli specialization of the chapter owner `IsConditionallyIID`, with the extra
requirement that each conditional coordinate law given `Y` is the Bernoulli law of parameter
`Y`. -/
abbrev IsConditionallyBernoulliIID {Ω : Type u} {ι : Type v}
    [mΩ : MeasurableSpace Ω]
    (Y : Ω → unitInterval) (X : ι → Ω → Bool)
    (μ : Measure Ω) [IsFiniteMeasure μ] : Prop :=
  Measurable Y ∧
    IsConditionallyIID (MeasurableSpace.comap Y inferInstance) X μ ∧
      ∀ i, ∀ᵐ y ∂μ.map Y,
        condDistrib (X i) Y μ y =
          (PMF.bernoulli (toNNReal y) (by simpa using y.2.2)).toMeasure

namespace IsConditionallyBernoulliIID

variable {Ω : Type u} {ι : Type v}
variable [mΩ : MeasurableSpace Ω]
variable {Y : Ω → unitInterval} {X : ι → Ω → Bool} {μ : Measure Ω} [IsFiniteMeasure μ]

/-- The Bernoulli specialization is defined over a measurable parameter `Y`. -/
theorem measurable (hX : IsConditionallyBernoulliIID Y X μ) : Measurable Y := by
  exact hX.1

/-- Forgetting the Bernoulli conditional-law clause leaves the chapter owner
`IsConditionallyIID`. -/
theorem isConditionallyIID (hX : IsConditionallyBernoulliIID Y X μ) :
    IsConditionallyIID (MeasurableSpace.comap Y inferInstance) X μ := by
  exact hX.2.1

theorem condDistrib_ae_eq_bernoulli (hX : IsConditionallyBernoulliIID Y X μ) (i : ι) :
    ∀ᵐ y ∂μ.map Y,
      condDistrib (X i) Y μ y =
        (PMF.bernoulli (toNNReal y) (by simpa using y.2.2)).toMeasure := by
  exact hX.2.2 i

end IsConditionallyBernoulliIID

-- Proof sketch: for each finite tuple, independence and pairwise identical distribution imply that
-- the tuple law is a product of identical marginals, and this product measure is invariant under
-- permuting the coordinates.
/-- Example 12.3 (1): An i.i.d. family of random variables is exchangeable. -/
theorem exchangeableFamily_of_isIID {Ω : Type u} {ι : Type v} {E : Type w}
    [MeasurableSpace Ω] [MeasurableSpace E] {μ : Measure Ω}
    {X : ι → Ω → E} (hX : IsIID X μ) :
    IsExchangeable X μ := sorry

-- Proof sketch: under the uniform measure on binary words with exactly `M` ones, every admissible
-- word has the same probability. Permuting coordinates preserves both admissibility and this
-- uniform weight, so the coordinate process is exchangeable.
/-- Example 12.3 (2): The coordinate process under the uniform law on black/white words of length
`N` with exactly `M` black draws is exchangeable; this is the without-replacement urn model. -/
theorem exchangeableFamily_coordinateProcess_uniformOn_blackIndicatorWordSet (N M : ℕ) :
    IsExchangeable (fun i (x : Fin N → Bool) ↦ x i)
      (uniformOn (blackIndicatorWordSet N M)) := sorry

-- Proof sketch: conditional on `Y = y`, the finite-dimensional laws are products of Bernoulli
-- measures with common parameter `y`, hence invariant under coordinate permutations. Integrating
-- these conditional laws over the law of `Y` preserves the permutation invariance.
/-- Example 12.3 (3): A Bernoulli family that is conditionally i.i.d. with parameter `Y ∈ [0,1]`
is exchangeable. -/
theorem exchangeableFamily_of_isConditionallyBernoulliIID {Ω : Type u} {ι : Type v}
    [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {Y : Ω → unitInterval} {X : ι → Ω → Bool}
    (hX : IsConditionallyBernoulliIID Y X μ) :
    IsExchangeable X μ := sorry
