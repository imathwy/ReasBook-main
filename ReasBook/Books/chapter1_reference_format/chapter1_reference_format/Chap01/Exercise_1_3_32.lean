import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open Polynomial

section IntegerPolynomials

/-- Exercise 1.3.32 (1): if a prime integer divides every coefficient of the product `P * Q`, then
it divides every coefficient of `P` or every coefficient of `Q`. -/
theorem prime_dvd_all_coeffs_of_mul {P Q : Polynomial ℤ} {p : ℕ} (hp : Nat.Prime p)
    (hPQ : ∀ n : ℕ, (p : ℤ) ∣ (P * Q).coeff n) :
    (∀ n : ℕ, (p : ℤ) ∣ P.coeff n) ∨ (∀ n : ℕ, (p : ℤ) ∣ Q.coeff n) := by
  have hcontent : (p : ℤ) ∣ (P * Q).content := by
    rw [dvd_content_iff_C_dvd, C_dvd_iff_dvd_coeff]
    simpa using hPQ
  rw [content_mul] at hcontent
  rcases Int.Prime.dvd_mul' hp hcontent with hP | hQ
  · left
    exact fun n ↦ hP.trans (content_dvd_coeff n)
  · right
    exact fun n ↦ hQ.trans (content_dvd_coeff n)

/- Exercise 1.3.32: Gauss's lemma identifies the content of a product in `ℤ[X]` with the
product of the contents. -/
recall Polynomial.content_mul

/-- Exercise 1.3.32 (2): a nonconstant polynomial that is irreducible in `ℤ[X]` remains
irreducible after mapping to `ℚ[X]`. -/
-- Proof sketch: show that a nonconstant irreducible polynomial in `ℤ[X]` is primitive, then apply
-- `Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast`.
theorem irreducible_map_rat_of_irreducible {Φ : Polynomial ℤ} (hdeg : 0 < Φ.natDegree)
    (hΦ : Irreducible Φ) : Irreducible (Φ.map (Int.castRingHom ℚ)) := by
  exact
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      (hΦ.isPrimitive (Nat.pos_iff_ne_zero.mp hdeg))).mp hΦ

/-- Exercise 1.3.32 (3): Eisenstein's criterion implies that a nonconstant integer polynomial
whose lower coefficients are divisible by a prime `p`, whose leading coefficient is not divisible
by `p`, and whose constant coefficient is not divisible by `p^2` is irreducible over `ℚ`. -/
-- Proof sketch: pass from `P` to its primitive part, which inherits the same Eisenstein
-- divisibility pattern because the content is not divisible by `p`; apply
-- `Polynomial.IsEisensteinAt.irreducible` to that primitive part and then use Gauss's lemma.
theorem eisenstein_irreducible_map_rat {P : Polynomial ℤ} {p : ℕ} (hdeg : 0 < P.natDegree)
    (hp : Nat.Prime p) (hcoeff : ∀ k : ℕ, k < P.natDegree → (p : ℤ) ∣ P.coeff k)
    (hlead : ¬ (p : ℤ) ∣ P.leadingCoeff) (hconst : ¬ ((p : ℤ) ^ 2 ∣ P.coeff 0)) :
    Irreducible (P.map (Int.castRingHom ℚ)) := by
  have hP0 : P ≠ 0 := by
    intro hP0
    simp [hP0] at hdeg
  have hcontent_ndvd : ¬ (p : ℤ) ∣ P.content := by
    intro hcontent
    apply hlead
    rw [← P.coeff_natDegree]
    exact hcontent.trans (content_dvd_coeff P.natDegree)
  have hcoeff_eq (k : ℕ) : P.coeff k = P.content * P.primPart.coeff k := by
    simpa [coeff_C_mul] using
      congrArg (fun f : Polynomial ℤ ↦ f.coeff k) P.eq_C_content_mul_primPart
  have hprim_coeff : ∀ k : ℕ, k < P.primPart.natDegree → (p : ℤ) ∣ P.primPart.coeff k := by
    intro k hk
    have hk' : k < P.natDegree := by simpa [P.natDegree_primPart] using hk
    rcases Int.Prime.dvd_mul' hp (by simpa [hcoeff_eq k] using hcoeff k hk') with h | h
    · exact (hcontent_ndvd h).elim
    · exact h
  have hprim_lead : ¬ (p : ℤ) ∣ P.primPart.leadingCoeff := by
    intro h
    apply hlead
    have hlead_eq : P.leadingCoeff = P.content * P.primPart.leadingCoeff := by
      calc
        P.leadingCoeff = P.coeff P.natDegree := by symm; exact P.coeff_natDegree
        _ = P.content * P.primPart.coeff P.natDegree := hcoeff_eq P.natDegree
        _ = P.content * P.primPart.leadingCoeff := by
          rw [show P.primPart.coeff P.natDegree = P.primPart.leadingCoeff by
            simpa [P.natDegree_primPart] using P.primPart.coeff_natDegree]
    rw [hlead_eq]
    exact dvd_mul_of_dvd_right h P.content
  have hprim_const : ¬ ((p : ℤ) ^ 2 ∣ P.primPart.coeff 0) := by
    intro h
    apply hconst
    rw [hcoeff_eq 0]
    exact dvd_mul_of_dvd_right h P.content
  have hspan_prime : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime := by
    rw [Ideal.span_singleton_prime (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hp
  have hprim_eisenstein : P.primPart.IsEisensteinAt (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [Ideal.mem_span_singleton] using hprim_lead
    · intro n hn
      exact Ideal.mem_span_singleton.mpr (hprim_coeff n hn)
    · intro h
      apply hprim_const
      exact Ideal.mem_span_singleton.mp ((Ideal.span_singleton_pow (p : ℤ) 2).symm ▸ h)
  have hprim_irreducible : Irreducible P.primPart := by
    refine hprim_eisenstein.irreducible hspan_prime P.isPrimitive_primPart ?_
    simpa [P.natDegree_primPart] using hdeg
  have hmap_prim : Irreducible (P.primPart.map (Int.castRingHom ℚ)) := by
    exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast P.isPrimitive_primPart).mp
      hprim_irreducible
  have hcontent_ne_zero : P.content ≠ 0 := by
    exact fun h ↦ hP0 (content_eq_zero_iff.mp h)
  rw [P.eq_C_content_mul_primPart]
  simpa [Polynomial.map_mul] using
    (irreducible_isUnit_mul (isUnit_C.mpr (Int.cast_ne_zero.mpr hcontent_ne_zero).isUnit)).2
      hmap_prim

/-- Exercise 1.3.32 (4): for a prime `p`, the geometric-sum polynomial
`1 + X + ··· + X^(p - 1)` is irreducible over `ℚ`. -/
-- Proof sketch: identify the geometric sum with `Polynomial.cyclotomic p ℚ` via
-- `Polynomial.cyclotomic_prime`, then apply `Polynomial.cyclotomic.irreducible_rat`.
theorem prime_geometric_sum_irreducible_rat {p : ℕ} (hp : Nat.Prime p) :
    Irreducible (∑ i ∈ Finset.range p, (X : Polynomial ℚ) ^ i) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← cyclotomic_prime ℚ p]
  exact cyclotomic.irreducible_rat hp.pos

end IntegerPolynomials
