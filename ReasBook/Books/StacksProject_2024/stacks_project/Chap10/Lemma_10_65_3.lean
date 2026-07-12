import Mathlib
import StacksProject_2024.Chap10.Lemma_10_65_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type x} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-
Domain triage: this item lies in commutative algebra of associated primes under flat base change.
The source-facing exact-annihilator set is `associatedPrimesOfModule`, while the Noetherian owner
abstraction is mathlib's `associatedPrimes`; this file stays at the source-facing layer, and any
Noetherian owner-form restatement should be obtained downstream via
`associatedPrimesOfModule_eq_associatedPrimes`. The quotient module `N / pN` is already exposed in
Lemma 10.65.1 as `relativeAssassinPrimeQuotient`, so this file reuses that chapter-level name
instead of keeping a parallel local definition.
-/

/-- Lemma 10.65.3 (1): if `N` is flat over `R`, then every associated prime of some quotient
`N / pN` with `p ∈ Ass_R(M)` is an associated prime of `M ⊗[R] N` over `S`. In Lean this tensor
product is represented by the canonically `S`-linear model `N ⊗[R] M`. -/
-- Proof sketch: for `p ∈ associatedPrimesOfModule R M`, choose an injection `R ⧸ p ↪ M` and
-- tensor it with the flat `R`-module `N`. Identify `(R ⧸ p) ⊗[R] N` with `N / pN`, then apply
-- `associatedPrimes.subset_of_injective` over `S`.
theorem associatedPrimesOfModule_iUnion_primeQuotients_subset_tensorProduct [Module.Flat R N] :
    (⋃ p : Ideal R, ⋃ _ : p ∈ associatedPrimesOfModule R M,
      associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p)) ⊆
      associatedPrimesOfModule S (N ⊗[R] M) := sorry

/-- Lemma 10.65.3 (2): if `R` is Noetherian and `N` is flat over `R`, then the associated primes
of `M ⊗[R] N` over `S` are exactly the associated primes of the quotients `N / pN` for
`p ∈ Ass_R(M)`. In Lean the tensor product is written in the canonically `S`-linear order
`N ⊗[R] M`. -/
-- Proof sketch: the previous theorem gives the inclusion from right to left. For the converse,
-- reduce to the finitely generated case by writing `M` as a directed union of finite submodules.
-- For finite `M`, choose a prime-quotient filtration and tensor it with `N`; flatness preserves
-- exactness, and `associatedPrimes.subset_union_of_exact` reduces an associated prime of
-- `M ⊗[R] N` to one of the subquotients `N / pN`.
theorem associatedPrimesOfModule_tensorProduct_eq_iUnion_primeQuotients_of_isNoetherianRing
    [Module.Flat R N] [IsNoetherianRing R] :
    associatedPrimesOfModule S (N ⊗[R] M) =
      (⋃ p : Ideal R, ⋃ _ : p ∈ associatedPrimesOfModule R M,
        associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p)) :=
    sorry

end
