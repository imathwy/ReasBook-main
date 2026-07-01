import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
variable {S' : Type w} [CommRing S'] [Algebra R S'] [Algebra.FinitePresentation R S']

-- Proof sketch: choose a finite presentation of `S` and transport the images of finitely many
-- generators across the local `R`-algebra isomorphism `S_𝔮 ≃ S'_{𝔮'}`. After clearing the
-- denominators away from `𝔮'`, obtain an `R`-algebra map `S → S'_{g'}` inducing the given local
-- isomorphism. Lemma `10.6.2` keeps finite presentation after composing with this map, and Lemma
-- `10.126.6` then yields a product decomposition after shrinking once more, from which an open
-- neighborhood isomorphism `S_g ≃ S'_{g'}` follows.
/-- Lemma 10.126.7: if `S` and `S'` are finitely presented `R`-algebras and the local `R`-algebras
`S_𝔮` and `S'_𝔮'` are isomorphic at primes `𝔮 ∈ Spec(S)` and `𝔮' ∈ Spec(S')`, then after
shrinking to principal opens around those primes there is an `R`-algebra isomorphism
`S_g ≃ S'_{g'}`. -/
theorem exists_awayAlgEquiv_of_localizationAtPrime_algEquiv
    (q : PrimeSpectrum S) (q' : PrimeSpectrum S')
    (hlocal : Localization.AtPrime q.asIdeal ≃ₐ[R] Localization.AtPrime q'.asIdeal) :
    ∃ (g : S) (_ : g ∉ q.asIdeal) (g' : S') (_ : g' ∉ q'.asIdeal),
      Nonempty (Localization.Away g ≃ₐ[R] Localization.Away g') := sorry

end
