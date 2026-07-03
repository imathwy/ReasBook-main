import ProbabilityTheory_Klenke_2020.Items.Chap14.Example_14_30

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open unitInterval

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

section

variable (n : ℕ) (P : Measure Ω) {X : Ω → ↑I} {Y : Ω → Fin n → Bool}

/-- Example after Theorem 8.37: if `X` is uniformly distributed on `[0,1]` and, for `P.map X`-
almost every `x`, the regular conditional law of the Boolean vector `Y` given `X = x` has
independent coordinates with one-coordinate Bernoulli law on `Bool` of parameter `x`, then the
whole conditional law is the canonical Bernoulli product kernel `coinTossingKernel n`. -/
theorem condDistrib_coinTossVector_given_uniform_ae_eq_coinTossingKernel
    (hX_law : HasLaw X volume P) :
    letI : IsProbabilityMeasure P := hX_law.isProbabilityMeasure
    ∀ (hcond_indep : Kernel.iIndepFun Function.eval (condDistrib Y X P) (P.map X))
      (hcond_marg :
        ∀ i : Fin n,
          (condDistrib Y X P).map (Function.eval i) =ᵐ[P.map X]
            fun x ↦ (PMF.bernoulli (toNNReal x) (by simpa using x.2.2)).toMeasure),
      condDistrib Y X P =ᵐ[volume] coinTossingKernel n := by
  letI : IsProbabilityMeasure P := hX_law.isProbabilityMeasure
  intro hcond_indep hcond_marg
  sorry

/-- Pointwise form of
`condDistrib_coinTossVector_given_uniform_ae_eq_coinTossingKernel`. For `volume`-almost every
`x : ↑I`, the regular conditional distribution of `Y` given `X = x` is the Bernoulli product law
`coinTossingKernel n x` on `Fin n → Bool`. -/
theorem condDistrib_coinTossVector_given_uniform_ae_eq_coinTossingKernel_apply
    (hX_law : HasLaw X volume P) :
    letI : IsProbabilityMeasure P := hX_law.isProbabilityMeasure
    ∀ (hcond_indep : Kernel.iIndepFun Function.eval (condDistrib Y X P) (P.map X))
      (hcond_marg :
        ∀ i : Fin n,
          (condDistrib Y X P).map (Function.eval i) =ᵐ[P.map X]
            fun x ↦ (PMF.bernoulli (toNNReal x) (by simpa using x.2.2)).toMeasure),
      ∀ᵐ x ∂volume, condDistrib Y X P x = coinTossingKernel n x := by
  letI : IsProbabilityMeasure P := hX_law.isProbabilityMeasure
  intro hcond_indep hcond_marg
  simpa using
    condDistrib_coinTossVector_given_uniform_ae_eq_coinTossingKernel n P hX_law hcond_indep
      hcond_marg

end
