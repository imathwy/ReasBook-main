import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_14_30 (from Items/Chap14) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory unitInterval
open unitInterval

private noncomputable def coinTossingMeasure (n : ℕ) (p : ↑I) : Measure (Fin n → Bool) :=
  Measure.pi fun _ : Fin n ↦
    (PMF.bernoulli (toNNReal p) (by simpa using p.2.2)).toMeasure

/-- The family of Bernoulli product measures depends measurably on the parameter `p`. -/
-- Proof sketch: On the finite space `Fin n → Bool`, it is enough to check measurability of the
-- mass of each measurable set, and those masses are finite polynomial expressions in `p`.
private theorem coinTossingMeasure_measurable (n : ℕ) : Measurable (coinTossingMeasure n) := sorry

/-- The stochastic kernel sending `p ∈ [0,1]` to the `n`-fold Bernoulli product law with
success probability `p`. -/
noncomputable def coinTossingKernel (n : ℕ) : Kernel ↑I (Fin n → Bool) :=
  ⟨coinTossingMeasure n, coinTossingMeasure_measurable n⟩

/-- At parameter `p`, `coinTossingKernel n` is the Bernoulli product measure on `Fin n → Bool`
with success probability `p`. -/
@[simp]
theorem coinTossingKernel_apply (n : ℕ) (p : ↑I) :
    coinTossingKernel n p =
      Measure.pi fun _ : Fin n ↦
        (PMF.bernoulli (toNNReal p) (by simpa using p.2.2)).toMeasure :=
  rfl

/-- Example 14.30: the joint measure obtained by choosing a uniform parameter `p ∈ [0,1]` and,
conditionally on `p`, sampling `n` independent Bernoulli variables with success probability `p`.
Here `{0,1}^n` is represented by `Fin n → Bool`. -/
noncomputable def coinTossingUniformMixture (n : ℕ) : Measure (↑I × (Fin n → Bool)) :=
  (volume : Measure ↑I) ⊗ₘ coinTossingKernel n

/-- The Bernoulli product family defines a Markov kernel from `[0,1]` to `{0,1}^n`. -/
-- Proof sketch: Each fiber is a product of probability measures on `Bool`, so every fiber has
-- total mass `1`; the kernel measurability is exactly `coinTossingMeasure_measurable`.
theorem coinTossingKernel_isMarkovKernel (n : ℕ) :
    IsMarkovKernel (coinTossingKernel n) := by
  refine ⟨fun p ↦ ?_⟩
  simpa [coinTossingKernel_apply] using
    (inferInstance : IsProbabilityMeasure
      (Measure.pi fun _ : Fin n ↦
        (PMF.bernoulli (toNNReal p) (by simpa using p.2.2)).toMeasure))

/-- The Bernoulli product kernel carries the canonical Markov-kernel instance. -/
instance (n : ℕ) : IsMarkovKernel (coinTossingKernel n) :=
  coinTossingKernel_isMarkovKernel n

/-- The first coordinate under the joint mixture law is uniformly distributed on `[0,1]`. -/
-- Proof sketch: The first marginal of a composition-product `μ ⊗ₘ κ` is `μ`, so the first
-- coordinate has law `volume` on the unit interval.
theorem coinTossingUniformMixture_fst_hasLaw (n : ℕ) :
    HasLaw Prod.fst (volume : Measure ↑I) (coinTossingUniformMixture n) where
  map_eq := by
    change (coinTossingUniformMixture n).fst = (volume : Measure ↑I)
    exact Measure.fst_compProd (volume : Measure ↑I) (coinTossingKernel n)

/-- The joint measure of the example is itself a probability measure. -/
-- Proof sketch: `volume` on the unit interval is a probability measure, and the previous theorem
-- upgrades `coinTossingKernel n` to a Markov kernel; then `μ ⊗ₘ κ` is a probability measure.
theorem coinTossingUniformMixture_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (coinTossingUniformMixture n) := by
  simpa [coinTossingUniformMixture] using
    (inferInstance : IsProbabilityMeasure ((volume : Measure ↑I) ⊗ₘ coinTossingKernel n))

/-- The second marginal of the joint law is the mixture of the Bernoulli product kernel against
the uniform parameter measure. -/
-- Proof sketch: This is the standard `snd_compProd` identity for composition-products of a measure
-- and a kernel, applied to the concrete joint measure of this example.
theorem coinTossingUniformMixture_snd_eq (n : ℕ) :
    (coinTossingUniformMixture n).snd = coinTossingKernel n ∘ₘ (volume : Measure ↑I) := by
  change (((volume : Measure ↑I) ⊗ₘ coinTossingKernel n).snd =
    coinTossingKernel n ∘ₘ (volume : Measure ↑I))
  exact Measure.snd_compProd (volume : Measure ↑I) (coinTossingKernel n)
