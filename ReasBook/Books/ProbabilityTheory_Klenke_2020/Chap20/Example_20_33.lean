import ProbabilityTheory_Klenke_2020.Chap20.Definition_20_30
import ProbabilityTheory_Klenke_2020.Chap20.Example_20_8
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/- Example 20.33 is `source-facing`: the textbook conclusion is that the uniform-measure rotation
on the finite cyclic system `ZMod n` has zero Kolmogorov--Sinai entropy. The iterate identity
below is only an auxiliary `bridge/view` fact witnessing the periodicity of the underlying finite
system, while the public owner remains `kolmogorov_sinai_entropy`. -/

-- Proof sketch: each application of the translation map `x ↦ x + r` adds `r` modulo `n`, so the
-- `n`-th iterate adds `n • r`, which vanishes in `ZMod n`.
/-- The `n`-fold iterate of the translation `x ↦ x + r` on `ZMod n` is the identity. -/
theorem zmodTranslation_iterate_eq_id (n r : ℕ) :
    (((· + (r : ZMod n)) : ZMod n → ZMod n)^[n]) = id := by
  ext x
  have hiter : ∀ m : ℕ, (((· + (r : ZMod n)) : ZMod n → ZMod n)^[m]) x = x + m • (r : ZMod n) := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m ihm =>
        rw [Function.iterate_succ_apply']
        rw [ihm]
        ring_nf
  rw [hiter n, nsmul_eq_mul]
  simp

variable (n r : ℕ) [NeZero n]

-- Proof sketch: the map `x ↦ x + r` is a finite periodic rotation of the uniform probability space
-- `ZMod n`; Example 20.8 supplies the canonical `MeasurePreserving` owner, and periodic finite
-- systems have zero Kolmogorov--Sinai entropy.
/-- Example 20.33: the Kolmogorov--Sinai entropy of the uniform rotation
`x ↦ x + r` on the finite cyclic group `ZMod n` is zero. -/
theorem zmodTranslationEntropy_eq_zero :
    h(uniformOn (Set.univ : Set (ZMod n)),
      ((· + (r : ZMod n)) : ZMod n → ZMod n), (zmodTranslation_measurePreserving n r).measurable) =
      0 := by
  sorry
