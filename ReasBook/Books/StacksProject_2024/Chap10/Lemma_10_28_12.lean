import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped nonZeroDivisors

section

variable {R : Type u} [CommRing R]

/-- Lemma 10.28.12 (1): an ideal of `R` that is maximal among the ideals containing no
nonzerodivisor is prime. -/
-- This is the source-facing specialization of the owner theorem
-- `Ideal.isPrime_of_maximally_disjoint` to the multiplicative set `nonZeroDivisors R`.
theorem ideal_isPrime_of_maximal_avoiding_nonZeroDivisors {I : Ideal R}
    (hI : Maximal
      (fun J : Ideal R ↦ Disjoint (J : Set R) (R⁰ : Set R)) I) :
    I.IsPrime :=
  Ideal.isPrime_of_maximally_disjoint I R⁰ hI.prop fun _ ↦ hI.not_prop_of_gt

/-- Lemma 10.28.12 (2): if `R` is nontrivial and every nonzero prime ideal of `R` contains a
nonzerodivisor, then `R` is a domain. -/
-- Proof sketch: apply the owner theorem `Ideal.exists_le_prime_disjoint` to the multiplicative
-- set `nonZeroDivisors R`; the hypothesis forces the resulting prime ideal to be `⊥`, so `(0)` is
-- prime and hence `R` is a domain.
theorem isDomain_of_nonzero_prime_contains_nonZeroDivisor [Nontrivial R]
    (hprime : ∀ P : Ideal R, P.IsPrime → P ≠ ⊥ →
      ∃ x : R, x ∈ P ∧ x ∈ R⁰) :
    IsDomain R := by
  have hbotDisj : Disjoint ((⊥ : Ideal R) : Set R) (R⁰ : Set R) :=
    Set.disjoint_left.2 fun x hx0 hxnd ↦ nonZeroDivisors.ne_zero hxnd (Ideal.mem_bot.mp hx0)
  obtain ⟨P, hPprime, -, hPdisj⟩ :=
    Ideal.exists_le_prime_disjoint (⊥ : Ideal R) R⁰ hbotDisj
  have hPbot : P = ⊥ := by
    by_contra hPne
    obtain ⟨x, hxP, hxnd⟩ := hprime P hPprime hPne
    exact Set.disjoint_left.mp hPdisj hxP hxnd
  letI : (⊥ : Ideal R).IsPrime := hPbot ▸ hPprime
  exact IsDomain.of_bot_isPrime R

end
