import AchimKlenkeLean.Items.Chap12.Definition_12_6
import AchimKlenkeLean.Items.Chap12.Remark_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {μ : Measure Ω}

section

variable {X : ℕ → Ω → E}
variable {φ : (ℕ → E) → ℝ}

-- Proof sketch: if `A` is measurable with respect to `nExchangeableSigmaAlgebra`, then `A`
-- pulls back from an `n`-symmetric measurable event on sequence space. Multiplying by its
-- indicator and using exchangeability shows that the two conditional expectations have the same
-- integrals on every such event, hence they agree almost everywhere.
private theorem condExp_eq_condExp_permuteFirst_of_isExchangeable
    (hX : IsExchangeable X μ) (hφ_meas : Measurable φ)
    (hφ_int : Integrable (φ ∘ Function.swap X) μ) (n : ℕ)
    (ρ : Equiv.Perm (Fin n)) :
    μ[φ ∘ Function.swap X | nExchangeableSigmaAlgebra (Function.swap X) n] =ᵐ[μ]
      μ[φ ∘ permutePrefix n ρ ∘ Function.swap X |
        nExchangeableSigmaAlgebra (Function.swap X) n] := sorry

-- Proof sketch: average the permutation-invariance identity from
-- `condExp_eq_condExp_permuteFirst_of_isExchangeable` over all `ρ : Equiv.Perm (Fin n)`, then
-- use linearity of conditional expectation together with the fact that the resulting finite
-- average is measurable with respect to `nExchangeableSigmaAlgebra`.
/-- The averaged conditional expectation in Theorem 12.10 is the permutation average
`A_n(φ)(X) = (1 / n!) ∑_{ρ ∈ S(n)} φ(X^ρ)`. -/
theorem condExp_eq_exchangeableAverage_of_isExchangeable
    (hX : IsExchangeable X μ) (hφ_meas : Measurable φ)
    (hφ_int : Integrable (φ ∘ Function.swap X) μ) (n : ℕ) :
    μ[φ ∘ Function.swap X | nExchangeableSigmaAlgebra (Function.swap X) n] =ᵐ[μ]
      exchangeableAverage n φ ∘ Function.swap X := sorry

end
