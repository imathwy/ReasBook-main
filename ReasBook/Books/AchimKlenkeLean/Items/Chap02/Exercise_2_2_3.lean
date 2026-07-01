import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

variable {Ω : Type u} {m n : ℕ}

/-- The count vector recording how often each value in `Fin m` appears among the samples
`X 0 ω, …, X (n - 1) ω`. -/
def multinomialCount (X : Fin n → Ω → Fin m) (ω : Ω) : Fin m → ℕ :=
  fun i ↦ Finset.card <| Finset.univ.filter fun j ↦ X j ω = i

/-- The entries of the count vector sum to the sample size. -/
theorem sum_multinomialCount (X : Fin n → Ω → Fin m) (ω : Ω) :
    ∑ i, multinomialCount X ω i = n := by
  let f : Fin n → Fin m := fun j ↦ X j ω
  have h_mapsTo :
      ((Finset.univ : Finset (Fin n)) : Set (Fin n)).MapsTo f (Finset.univ : Finset (Fin m)) :=
    fun _ _ ↦ Finset.mem_univ _
  simpa [multinomialCount] using
    (Finset.card_eq_sum_card_fiberwise h_mapsTo).symm

section

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Exercise 2.2.3: if `X : Fin n → Ω → Fin m` is an independent family with common law `p`,
then the count vector `ω ↦ (fun i ↦ #{j | X j ω = i})` has multinomial point mass
`Nat.multinomial Finset.univ k * ∏ i, p i ^ k i` at every
`k ∈ Finset.piAntidiag Finset.univ n`. -/
theorem multinomialCount_preimage_singleton_eq_multinomial
    (p : PMF (Fin m)) (X : Fin n → Ω → Fin m) (h_indep : iIndepFun X μ)
    (h_law : ∀ i, HasLaw (X i) p.toMeasure μ) (k : Fin m → ℕ)
    (hk : k ∈ Finset.piAntidiag Finset.univ n) :
    μ (multinomialCount X ⁻¹' {k}) =
      (Nat.multinomial Finset.univ k : ENNReal) * (∏ i, (p i) ^ k i) := sorry

/-- Source-style reformulation of Exercise 2.2.3 with the total-count hypothesis written as
`∑ i, k i = n`. -/
theorem multinomialCount_preimage_singleton_eq_multinomial_of_sum_eq
    (p : PMF (Fin m)) (X : Fin n → Ω → Fin m) (h_indep : iIndepFun X μ)
    (h_law : ∀ i, HasLaw (X i) p.toMeasure μ) (k : Fin m → ℕ) (hk : ∑ i, k i = n) :
    μ (multinomialCount X ⁻¹' {k}) =
      (Nat.multinomial Finset.univ k : ENNReal) * (∏ i, (p i) ^ k i) := by
  simpa [Finset.mem_piAntidiag, hk] using
    multinomialCount_preimage_singleton_eq_multinomial p X h_indep h_law k

end
