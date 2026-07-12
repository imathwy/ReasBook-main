import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap12.Theorem_12_24

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u v

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "AmbientMeasure" => @Measure Ω mΩ

/- Domain-style sampling for Theorem 12.26:
- `ProbabilityMeasure E` is the owner object for the directing law.
- `IsConditionallyIID` from `Definition_12_20` is the chapter owner for the conditional i.i.d.
  part of de Finetti's theorem.
- `isExchangeable_iff_conditionallyIID_given_exchangeableSigmaAlgebra` from `Theorem_12_24`
  is the owner theorem that converts measurable exchangeability into the chapter's conditional
  i.i.d. abstraction.
- `exchangeableSigmaAlgebra (Function.swap X)` and `tailRandomVariableMeasurableSpace X` are the
  canonical conditioning `σ`-algebras already fixed upstream in `Theorem_12_24`.

Best owner abstraction:
- the theorem stays `source-facing`, because it asserts the existence of a directing random
  probability measure for an exchangeable sequence;
- the repeated payload attached to a candidate directing law is a `bridge/view` predicate on the
  owner object `Ω → ProbabilityMeasure E`, not a new packaged structure.

Primitive data:
- the sequence `X`, the ambient probability measure `μ`, and the candidate directing random
  measure `xiInf`.

Derived API:
- measurability of `xiInf` with respect to a chosen external conditioning `σ`-algebra `m`;
- conditional i.i.d. of `X` given the owner conditioning induced by `xiInf`;
- identification of the first conditional coordinate law with the sampled directing measure;
- the corresponding statements for the other coordinates are derived from conditional identical
  distribution and remain companion lemmas, not primitive fields.
-/
/-- A `ProbabilityMeasure E`-valued random variable is a directing random probability measure for
`X` if the sequence is conditionally i.i.d. given that random measure and the conditional law of
`X 0` is the sampled measure itself. Measurability with respect to an external conditioning
`σ`-algebra is a separate bridge/view condition used in the de Finetti existence theorems below.
The corresponding identities for the other coordinates are derived companion lemmas from the
conditional identical-distribution owner API. -/
abbrev IsDirectingProbabilityMeasure
    (xiInf : Ω → ProbabilityMeasure E) (X : ℕ → Ω → E)
    (μ : AmbientMeasure) [IsFiniteMeasure μ] : Prop :=
  letI : MeasurableSpace Ω := mΩ
  IsConditionallyIID (MeasurableSpace.comap xiInf inferInstance) X μ ∧
    ∀ᵐ ξ ∂μ.map xiInf, condDistrib (X 0) xiInf μ ξ = (ξ : Measure E)

namespace IsDirectingProbabilityMeasure

variable {xiInf : Ω → ProbabilityMeasure E} {X : ℕ → Ω → E}
variable {μ : AmbientMeasure} [IsFiniteMeasure μ]

/-- Forgetting the conditional-law identification leaves the chapter owner
`IsConditionallyIID`. -/
theorem isConditionallyIID (_hxiInf : IsDirectingProbabilityMeasure xiInf X μ) :
    IsConditionallyIID (MeasurableSpace.comap xiInf inferInstance) X μ :=
  match _hxiInf with
  | ⟨hIID, _⟩ => hIID

/-- For a directing random probability measure, the conditional law of `X 0` agrees almost surely
with the sampled directing measure. -/
theorem condDistrib_ae_eq_zero (_hxiInf : IsDirectingProbabilityMeasure xiInf X μ) :
    ∀ᵐ ξ ∂μ.map xiInf, condDistrib (X 0) xiInf μ ξ = (ξ : Measure E) :=
  match _hxiInf with
  | ⟨_, hcond⟩ => hcond

/-- The other coordinate conditional laws agree almost surely with the sampled directing measure
as a derived consequence of the conditional identical-distribution owner API. -/
theorem condDistrib_ae_eq (_hxiInf : IsDirectingProbabilityMeasure xiInf X μ) (i : ℕ) :
    ∀ᵐ ξ ∂μ.map xiInf, condDistrib (X i) xiInf μ ξ = (ξ : Measure E) := sorry

end IsDirectingProbabilityMeasure

-- Proof sketch: for the forward implication, condition on the
-- exchangeable `σ`-algebra, then realize the common conditional law of the coordinates as the
-- `ProbabilityMeasure E`-valued random variable induced by the regular conditional distribution of
-- `X 0`. For the reverse implication, conditional i.i.d. given the directing random measure
-- implies permutation-invariance of every finite-dimensional conditional law, hence exchangeability
-- after integrating out the directing measure.
/-- Theorem 12.26: an exchangeable `E`-valued sequence is exactly a sequence admitting an
exchangeable-`σ`-algebra-measurable directing random probability measure `Ξ∞` such that,
conditional on `Ξ∞`, the sequence is i.i.d. and the conditional law of `X₀` is `Ξ∞`. The
explicit coordinate measurability hypothesis matches the source-facing exchangeability owner with
the measurable owner theorem from `Theorem_12_24`. -/
theorem isExchangeable_iff_exists_directingProbabilityMeasure
    {X : ℕ → Ω → E} (hX_meas : ∀ n, Measurable (X n)) :
    IsExchangeable X μ ↔
      ∃ xiInf : Ω → ProbabilityMeasure E,
        Measurable[exchangeableSigmaAlgebra (Function.swap X)] xiInf ∧
          IsDirectingProbabilityMeasure xiInf X μ := sorry

-- Proof sketch: start from the exchangeable-`σ`-algebra directing random measure in
-- `isExchangeable_iff_exists_directingProbabilityMeasure`, then replace the conditioning
-- `σ`-algebra by `tailRandomVariableMeasurableSpace X`; the same
-- regular conditional law of `X 0` then serves as the tail-measurable directing measure.
/-- A directing random probability measure in de Finetti's theorem may also be chosen measurable
with respect to the tail `σ`-algebra of the sequence. -/
theorem exists_directingProbabilityMeasure_measurable_tailSigmaAlgebra
    {X : ℕ → Ω → E} (hX_meas : ∀ n, Measurable (X n)) (hX : IsExchangeable X μ) :
    ∃ xiInf : Ω → ProbabilityMeasure E,
      Measurable[tailRandomVariableMeasurableSpace X] xiInf ∧
        IsDirectingProbabilityMeasure xiInf X μ := sorry
