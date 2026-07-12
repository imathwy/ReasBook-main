import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open IsLocalRing

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [IsLocalRing R] [Infinite (IsLocalRing.ResidueField R)]
variable [CommRing S] [Algebra R S] [Finite (MaximalSpectrum S)]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Free S M] [Module.Finite S M]

/-- Lemma 10.78.8: if `R` is a local ring with infinite residue field, `S` is a semilocal
`R`-algebra such that the extension of the maximal ideal of `R` is contained in the Jacobson
radical of `S`, `M` is a finite free `S`-module, and the `R`-submodule `N` generates `M` as an
`S`-module, then `N` contains an `S`-basis of `M`. -/
-- Proof sketch: reduce modulo the Jacobson radical of `S` using Nakayama's lemma, so that `S`
-- becomes a finite product of fields. Then choose an element of `N` with nonzero component in each
-- factor by using the infinitude of the residue field of `R`; this generates a free direct summand.
-- Quotient by that summand and argue by induction on the rank of the free module.
theorem exists_basis_mem_submodule_of_span_eq_top
    (N : Submodule R M)
    (hmj : Ideal.map (algebraMap R S) (maximalIdeal R) ≤ Ring.jacobson S)
    (hN : Submodule.span S (N : Set M) = ⊤) :
    ∃ b : Module.Basis (Fin (Module.finrank S M)) S M, ∀ i, b i ∈ N := sorry

end
