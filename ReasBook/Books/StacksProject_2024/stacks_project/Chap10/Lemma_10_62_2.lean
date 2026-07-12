import Mathlib.RingTheory.Support
import StacksProject_2024.Chap10.Lemma_10_62_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum RelSeries

section SupportAndDimensionOfModules

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace PrimeCyclicFiltration

/-- The `i`-th successive quotient in a prime-cyclic filtration. -/
abbrev successiveQuotient (s : PrimeCyclicFiltration R M) (i : Fin s.length) :=
  (s i.succ) ⧸ (s i.castSucc).submoduleOf (s i.succ)

/-- The prime points occurring as successive prime-quotient factors of a finite prime-cyclic
filtration. This is derived from the owner relation `PrimeCyclicFiltration R M`, not from an
auxiliary chosen enumeration. -/
def primeFactors (s : PrimeCyclicFiltration R M) : Set (PrimeSpectrum R) :=
  { 𝔭 | ∃ i : Fin s.length,
      Nonempty (s.successiveQuotient i ≃ₗ[R] R ⧸ 𝔭.asIdeal) }

end PrimeCyclicFiltration

variable (s : PrimeCyclicFiltration R M)

-- Proof sketch: induct on the length of the filtration. For each successive quotient, use
-- a chosen representative of the nonempty family of quotient isomorphisms to identify its
-- support with `Supp (R ⧸ pᵢ)`, rewrite that support as `V(pᵢ)` via `Module.support_eq_zeroLocus`,
-- and combine the stages using `Module.support_of_exact`.
/-- Lemma 10.62.2: for a finite prime cyclic filtration `s` of `M`, the support of `M` is the
union of the closed sets `V(𝔭)` as `𝔭` ranges over the prime points occurring in `s`. -/
theorem support_eq_iUnion_zeroLocus_of_prime_cyclic_filtration
    (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤) :
    Module.support R M = ⋃ 𝔭 : s.primeFactors, zeroLocus 𝔭.1.asIdeal := sorry

/-- The prime points occurring as successive quotients in a finite prime cyclic filtration of `M`
form a subset of `Module.support R M`. This is the invariant owner-form of the textbook statement
“every prime appearing in the filtration lies in the support.” -/
theorem primeFactors_subset_support_of_prime_cyclic_filtration
    (hs₀ : s.head = ⊥) (hs_top : s.last = ⊤) :
    s.primeFactors ⊆ Module.support R M := sorry

variable (p : Fin s.length → PrimeSpectrum R)

/-- A chosen enumeration of the prime-quotient factors of `s` recovers the intrinsic owner set
`s.primeFactors`. This is a bridge from a presentation by indices to the filtration itself. -/
theorem PrimeCyclicFiltration.primeFactors_eq_range
    (hp : ∀ i : Fin s.length,
      Nonempty (s.successiveQuotient i ≃ₗ[R] R ⧸ (p i).asIdeal)) :
    s.primeFactors = Set.range p := sorry

end SupportAndDimensionOfModules
