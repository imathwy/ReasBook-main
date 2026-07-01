import stacks_project.Chap10.Definition_10_37_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (R : Type u) [CommRing R]

variable [IsReduced R]
variable [Finite (minimalPrimes R)]

/-- Lemma 10.37.16: for a reduced ring with finitely many minimal primes, the following are
equivalent: `R` is a normal ring, `R` is integrally closed in its total ring of fractions, and
`R` is a finite product of normal domains. -/
-- Proof sketch: combine the normal-ring criterion from the previous lemmas with the description
-- of the total quotient ring as the product of the localizations at the minimal primes. The
-- idempotents in that product split `R` as a finite product of the quotients by its minimal
-- primes. For the domain factors, the chapter's owner predicate for "normal domain" is the
-- canonical `IsIntegrallyClosed`, so the finite-product clause is stated directly with that API.
theorem normalRing_tfae_isIntegrallyClosed_isFiniteProductOfNormalDomains :
    List.TFAE
      [ IsNormalRing R
      , IsIntegrallyClosed R
      , ∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (_ : ∀ i, CommRing (S i))
          (_ : R ≃+* ∀ i, S i),
          (∀ i, IsDomain (S i)) ∧ ∀ i, IsIntegrallyClosed (S i)
      ] := sorry

end
