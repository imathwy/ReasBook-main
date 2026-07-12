import StacksProject_2024.Chap10.Definition_10_63_1
import StacksProject_2024.Chap10.Definition_10_65_2

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open scoped TensorProduct

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module S N]

/- Domain triage: this file lies in commutative algebra of associated primes under base change.
The owner abstraction is the chapter definition `relativeAssassin R S N` from Definition 10.65.2.
The only primitive extra data needed here is the quotient module `N / pN`; the sets `A'`, `A_fin`,
`A'_fin`, `B`, and `B_fin` are source-facing derived views used to compare that owner with
fiberwise and finite-generation presentations from the source. -/

/-- The quotient module `N / pN` appearing in Lemma 10.65.1. -/
abbrev relativeAssassinPrimeQuotient
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module S N]
    (p : Ideal R) : Type w :=
  N ⧸ (Ideal.map (algebraMap R S) p) • (⊤ : Submodule S N)

/-- The fiber-spectrum image `A'` from Lemma 10.65.1. -/
abbrev relativeAssassinAprime
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module S N] :
    Set (PrimeSpectrum S) :=
  ⋃ p : PrimeSpectrum R,
    PrimeSpectrum.comap (algebraMap S (p.asIdeal.Fiber S)) ''
      { q : PrimeSpectrum (p.asIdeal.Fiber S) |
          q.asIdeal ∈ associatedPrimesOfModule (p.asIdeal.Fiber S) ((p.asIdeal.Fiber S) ⊗[S] N) }

/-- Membership in `A'` is by definition a fiber point mapping to the given prime of `S`. -/
@[simp] theorem mem_relativeAssassinAprime_iff (q : PrimeSpectrum S) :
    q ∈ relativeAssassinAprime R S N ↔
      ∃ p : PrimeSpectrum R,
        q ∈ PrimeSpectrum.comap (algebraMap S (p.asIdeal.Fiber S)) ''
          { q' : PrimeSpectrum (p.asIdeal.Fiber S) |
              q'.asIdeal ∈ associatedPrimesOfModule (p.asIdeal.Fiber S)
                ((p.asIdeal.Fiber S) ⊗[S] N) } := by
  constructor
  · intro hq
    exact Set.mem_iUnion.mp hq
  · rintro ⟨p, hp⟩
    exact Set.mem_iUnion.mpr ⟨p, hp⟩

/-- The finite-looking set `A_fin` from Lemma 10.65.1. -/
abbrev relativeAssassinAfin
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module S N] :
    Set (PrimeSpectrum S) :=
  { q : PrimeSpectrum S |
      q.asIdeal ∈ associatedPrimesOfModule S
        (relativeAssassinPrimeQuotient R S N (q.asIdeal.under R)) }

/-- Membership in `A_fin` is the associated-prime condition for the contracted prime quotient. -/
@[simp] theorem mem_relativeAssassinAfin_iff (q : PrimeSpectrum S) :
    q ∈ relativeAssassinAfin R S N ↔
      q.asIdeal ∈ associatedPrimesOfModule S
        (relativeAssassinPrimeQuotient R S N (q.asIdeal.under R)) := by
  rfl

/-- The set `A'_fin` from Lemma 10.65.1. -/
abbrev relativeAssassinAprimeFin
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module S N] :
    Set (PrimeSpectrum S) :=
  { q : PrimeSpectrum S |
      ∃ p : PrimeSpectrum R,
        q.asIdeal ∈ associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p.asIdeal) }

/-- Membership in `A'_fin` is by definition association to some prime-quotient `N / pN`. -/
@[simp] theorem mem_relativeAssassinAprimeFin_iff (q : PrimeSpectrum S) :
    q ∈ relativeAssassinAprimeFin R S N ↔
      ∃ p : PrimeSpectrum R,
        q.asIdeal ∈ associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p.asIdeal) := by
  rfl

end

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- The set `B` from Lemma 10.65.1. -/
abbrev relativeAssassinB
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    Set (PrimeSpectrum S) :=
  { q : PrimeSpectrum S | ∃ (M : Type x) (_ : AddCommGroup M) (_ : Module R M),
      q.asIdeal ∈ associatedPrimesOfModule S (N ⊗[R] M) }

/-- The set `B_fin` from Lemma 10.65.1. -/
abbrev relativeAssassinBfin
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    Set (PrimeSpectrum S) :=
  { q : PrimeSpectrum S | ∃ (M : Type x) (_ : AddCommGroup M) (_ : Module R M)
      (_ : Module.Finite R M),
      q.asIdeal ∈ associatedPrimesOfModule S (N ⊗[R] M) }

/-- Lemma 10.65.1 (1): the relative assassin `A` agrees with the fiber-spectrum image `A'`. -/
-- Proof sketch: for each `p ∈ Spec(R)`, compare the associated primes of `N ⊗[R] κ(p)` over `S`,
-- over `S / pS`, and over the fiber ring using Lemma 10.63.14 and Lemma 10.63.16 (1).
theorem relativeAssassinA_eq_relativeAssassinAprime :
    relativeAssassin R S N = relativeAssassinAprime R S N := sorry

/-- Lemma 10.65.1 (2a): `A_fin` is contained in `A`. -/
-- Proof sketch: for `q ∈ A_fin`, use the contraction identity built into the definition of
-- `A_fin` and the localization comparison of associated primes from Lemma 10.63.16 to pass from
-- `N / (R ∩ q)N` to `N ⊗[R] κ(R ∩ q)`.
theorem relativeAssassinAfin_subset_relativeAssassinA :
    relativeAssassinAfin R S N ⊆ relativeAssassin R S N := sorry

/-- Lemma 10.65.1 (2b): `B_fin` is contained in `B`. -/
-- Proof sketch: this is immediate from the definitions because every finite `R`-module is in
-- particular an `R`-module.
theorem relativeAssassinBfin_subset_relativeAssassinB :
    relativeAssassinBfin R S N ⊆ relativeAssassinB R S N := sorry

/-- Lemma 10.65.1 (2c): `A_fin` is contained in `A'_fin`. -/
-- Proof sketch: forget the contraction information encoded in the definition of `A_fin`.
theorem relativeAssassinAfin_subset_relativeAssassinAprimeFin :
    relativeAssassinAfin R S N ⊆ relativeAssassinAprimeFin R S N := sorry

/-- Lemma 10.65.1 (2d): `A'_fin` is contained in `B_fin`. -/
-- Proof sketch: if `q` is associated to `N / pN`, then take the finite module `R ⧸ p`; the module
-- `N / pN` is the corresponding tensor product, so `q` lies in `B_fin`.
theorem relativeAssassinAprimeFin_subset_relativeAssassinBfin :
    relativeAssassinAprimeFin R S N ⊆ relativeAssassinBfin R S N := sorry

/-- Lemma 10.65.1 (2e): `A` is contained in `B`. -/
-- Proof sketch: each residue field `κ(p)` is an `R`-module, so any associated prime coming from
-- `N ⊗[R] κ(p)` contributes directly to the defining union for `B`.
theorem relativeAssassinA_subset_relativeAssassinB :
    relativeAssassin R S N ⊆ relativeAssassinB R S N := sorry

/-- Lemma 10.65.1 (3a): if `S` is Noetherian, then `A = A_fin`. -/
-- Proof sketch: apply the Noetherian form of the localization comparison for associated primes to
-- `N / (R ∩ q)N`, identifying the associated primes of `N ⊗[R] κ(R ∩ q)` with those associated
-- primes of the quotient module lying over the contracted prime.
theorem relativeAssassinA_eq_relativeAssassinAfin_of_isNoetherianRing [IsNoetherianRing S] :
    relativeAssassin R S N = relativeAssassinAfin R S N := sorry

/-- Lemma 10.65.1 (3b): if `S` is Noetherian, then `B = B_fin`. -/
-- Proof sketch: start from an associated prime of `N ⊗[R] M`, choose an element with that prime
-- annihilator, and then cut down to a finite submodule containing the element and the finitely many
-- generators of the prime ideal.
theorem relativeAssassinB_eq_relativeAssassinBfin_of_isNoetherianRing [IsNoetherianRing S] :
    relativeAssassinB R S N = relativeAssassinBfin R S N := sorry

/-- Lemma 10.65.1 (4a): if `N` is flat over `R`, then `A = A_fin`. -/
-- Proof sketch: flatness makes tensoring exact, so associated primes of `N ⊗[R] κ(p)` come from
-- associated primes of `N / pN`; combine this with the contraction equality from flatness.
theorem relativeAssassinA_eq_relativeAssassinAfin_of_flat [Module.Flat R N] :
    relativeAssassin R S N = relativeAssassinAfin R S N := sorry

/-- Lemma 10.65.1 (4b): if `N` is flat over `R`, then `A_fin = A'_fin`. -/
-- Proof sketch: if `q` is associated to `N / pN`, flatness over the domain `R / p` shows that no
-- nonzero element of `R / p` can land in `q`, so the contraction of `q` to `R` is exactly `p`.
theorem relativeAssassinAfin_eq_relativeAssassinAprimeFin_of_flat [Module.Flat R N] :
    relativeAssassinAfin R S N = relativeAssassinAprimeFin R S N := sorry

/-- Lemma 10.65.1 (4c): if `N` is flat over `R`, then `B = B_fin`. -/
-- Proof sketch: exactness of `N ⊗[R] -` embeds `N ⊗[R] M'` into `N ⊗[R] M` for finite
-- submodules `M' ⊆ M`, so an element realizing an associated prime already lies in a finite
-- submodule without changing its annihilator.
theorem relativeAssassinB_eq_relativeAssassinBfin_of_flat [Module.Flat R N] :
    relativeAssassinB R S N = relativeAssassinBfin R S N := sorry

/-- Lemma 10.65.1 (5): if `R` is Noetherian and `N` is flat over `R`, then
`A = A' = A_fin = A'_fin = B = B_fin`. -/
-- Proof sketch: by part (4) it remains to show `B_fin ⊆ A'_fin`. For `q ∈ B_fin`, choose a
-- finite filtration of the finite module `M` with prime cyclic subquotients `R / pᵢ`; tensor the
-- filtration with the flat module `N` and apply Lemma 10.63.3 to reduce the associated prime of
-- `N ⊗[R] M` to one of the factors `N / pᵢN`.
theorem relativeAssassin_all_eq_of_isNoetherianRing_and_flat
    [IsNoetherianRing R] [Module.Flat R N] :
    relativeAssassin R S N = relativeAssassinAprime R S N ∧
      relativeAssassin R S N = relativeAssassinAfin R S N ∧
      relativeAssassin R S N = relativeAssassinAprimeFin R S N ∧
      relativeAssassin R S N = relativeAssassinB R S N ∧
      relativeAssassin R S N = relativeAssassinBfin R S N := sorry

end
