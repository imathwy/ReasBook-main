import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory unitInterval
open scoped ProbabilityTheory Topology unitInterval

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- With Lean's `0`-based indexing, the textbook Bernoulli parameters `1 / n` are represented by
`1 / (n + 1)`. -/
noncomputable def harmonicBernoulliParameter (n : ℕ) : I :=
  ⟨(1 : ℝ) / (n + 1), div_mem zero_le_one (by positivity) <| by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)⟩

-- Proof sketch: for convergence in measure, rewrite the deviation event
-- `{ω | ε ≤ |X n ω|}` using the `{0,1}`-valued Bernoulli law of `X n`, so its probability is
-- either `(n + 1)⁻¹` or `0` and therefore tends to `0`. For the almost-sure `limsup`, apply the
-- second Borel--Cantelli lemma to the events `{ω | X n ω = 1}`, whose probabilities form the
-- harmonic series.
/-- Remark 6.6: with Lean's `0`-based indexing, the textbook laws `\mathrm{Ber}_{1 / n}` are
formalized as the one-trial binomial laws `Bin(ℝ, 1, harmonicBernoulliParameter n)`. If
`(Xₙ)` is an independent sequence with these laws, then `Xₙ` converges in probability to `0`,
but `limsup_{n → ∞} Xₙ = 1` almost surely. Hence convergence in measure does not imply
almost-everywhere convergence. -/
theorem harmonicBernoulli_tendstoInMeasure_zero_and_ae_limsup_eq_one
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (h_indep : iIndepFun X P)
    (h_law : ∀ n, HasLaw (X n) (Bin(ℝ, 1, harmonicBernoulliParameter n)) P) :
    TendstoInMeasure P X atTop (fun _ ↦ (0 : ℝ)) ∧
      ∀ᵐ ω ∂P, limsup (fun n ↦ X n ω) atTop = 1 := sorry
