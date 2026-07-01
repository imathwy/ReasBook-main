import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Function
open Ideal
open scoped BigOperators

universe u

section

variable {R : Type u} [CommRing R]
variable {ι : Type*} [Fintype ι] (I : ι → Ideal R)

/-- Lemma 10.15.4 (Chinese remainder) (1): for pairwise comaximal ideals `I_i`, the product
`∏ i, I i` equals their intersection `⨅ i, I i`. -/
-- Proof sketch: this is `Ideal.prod_eq_iInf_of_pairwise_isCoprime` on `Finset.univ`.
theorem chinese_remainder_prod_eq_iInf
    (hI : Pairwise (IsCoprime on I)) :
    ∏ i, I i = ⨅ i, I i := by
  classical
  simpa using
    (show ∏ i ∈ (Finset.univ : Finset ι), I i = ⨅ i ∈ (Finset.univ : Finset ι), I i from
      prod_eq_iInf_of_pairwise_isCoprime
        (by
          intro i _ j _ hij
          exact hI hij))

/-- Lemma 10.15.4 (Chinese remainder) (2): for pairwise comaximal ideals `I_i`, the quotient by
their product is canonically isomorphic to the product of the quotients `R ⧸ I i`. -/
noncomputable def chinese_remainder_quotient_pi_ring_equiv
    (hI : Pairwise (IsCoprime on I)) :
    R ⧸ ∏ i, I i ≃+* ∀ i, R ⧸ I i :=
  (quotEquivOfEq (chinese_remainder_prod_eq_iInf I hI)).trans
    (quotientInfRingEquivPiQuotient I hI)

/-- The canonical Chinese remainder equivalence sends the class of `x` to the tuple of its classes
in the quotients `R ⧸ I i`. -/
@[simp]
theorem chinese_remainder_quotient_pi_ring_equiv_apply_mk
    (hI : Pairwise (IsCoprime on I)) (x : R) :
    chinese_remainder_quotient_pi_ring_equiv I hI (Ideal.Quotient.mk (∏ i, I i) x) =
      fun i ↦ Ideal.Quotient.mk (I i) x := by
  simpa [chinese_remainder_quotient_pi_ring_equiv, quotientInfRingEquivPiQuotient] using
    quotientInfToPiQuotient_mk I x

end
