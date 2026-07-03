import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_12_24 (from Items/Chap12) -/
open MeasureTheory ProbabilityTheory

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-
Domain-style sampling for Theorem 12.24:
- `ProbabilityTheory.iCondIndepFun` in mathlib is the owner abstraction for conditional
  independence of random-variable families.
- `IsExchangeable` in `Definition_12_1` is the Chapter 12 source-facing owner for exchangeability.
- `exchangeableSigmaAlgebra` in `Definition_12_6` is the canonical Chapter 12 conditioning
  `σ`-algebra attached to a sequence-valued map.
- `IsConditionallyIID` in `Definition_12_20` is the chapter's source-facing conditional i.i.d.
  notion, built from the owner-level conditional-independence API plus the equal-conditional-law
  clause.
- `tailRandomVariableMeasurableSpace` in `Definition_2_34` is the canonical bridge/view
  conditioning `σ`-algebra, and `exchangeableAverage_limit_of_isExchangeable` in `Theorem_12_17`
  identifies it with the exchangeable conditioning for exchangeable sequences.

Best owner abstraction:
- the main theorem stays `source-facing`;
- its conditioning object should be the canonical owner
  `exchangeableSigmaAlgebra (Function.swap X)`;
- the independence half is controlled by the owner `ProbabilityTheory.iCondIndepFun`, exposed in
  this chapter through `IsConditionallyIID`;
- the tail-`σ`-algebra formulation is a `bridge/view` companion obtained from Theorem 12.17.

Primitive data:
- the sequence `X`, the ambient probability measure `μ`, and the coordinate measurability
  hypothesis.

Derived API:
- the conditioning `σ`-algebra is canonically determined by `X`, so this file should not add any
  wrapper around `exchangeableSigmaAlgebra (Function.swap X)` or around
  `tailRandomVariableMeasurableSpace X`.
-/

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

variable {X : ℕ → Ω → E}

-- Proof sketch: for the forward implication, use Theorem 12.17 to identify the exchangeable and
-- tail conditional expectations and then verify the conditional factorization criterion for finite
-- products, which yields conditional independence and equality of the conditional laws. The
-- explicit measurability hypothesis aligns the source-facing exchangeability owner
-- `IsExchangeable` with the genuinely measurable owner `IsConditionallyIID`. For the reverse
-- implication, condition on the exchangeable `σ`-algebra and use conditional independence
-- together with equality of the conditional laws to show that every finite coordinate permutation
-- preserves the joint distribution.
/-- Theorem 12.24: a measurable sequence is exchangeable if and only if it is conditionally i.i.d.
given its exchangeable `σ`-algebra; equivalently, the conditioning `σ`-algebra in de Finetti's
theorem can be chosen canonically. -/
theorem isExchangeable_iff_conditionallyIID_given_exchangeableSigmaAlgebra
    (hX_meas : ∀ n, Measurable (X n))
    : IsExchangeable X μ ↔
        IsConditionallyIID (exchangeableSigmaAlgebra (Function.swap X)) X μ := sorry

-- Proof sketch: combine the main de Finetti equivalence for the exchangeable `σ`-algebra with the
-- identification of exchangeable and tail conditioning from Theorem 12.17, which allows the
-- canonical conditioning `σ`-algebra to be replaced by the tail `σ`-algebra. The same
-- measurability hypothesis is kept explicit here so that the bridge theorem matches the owner
-- semantics of `IsConditionallyIID`.
/-- Bridge/view companion to Theorem 12.24: the tail `σ`-algebra is another canonical choice of
conditioning `σ`-algebra in de Finetti's theorem. -/
theorem isExchangeable_iff_conditionallyIID_given_tailSigmaAlgebra
    (hX_meas : ∀ n, Measurable (X n))
    : IsExchangeable X μ ↔ IsConditionallyIID (tailRandomVariableMeasurableSpace X) X μ := sorry
