import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

namespace Ideal

/-
Domain triage: this file is in commutative algebra of weakly associated primes of modules.

* `source-facing`: `Ideal.IsWeaklyAssociatedToModule R M 𝔭`, which matches the textbook condition
  that `𝔭` is minimal over the annihilator of some element of `M`.
* `core/canonical` owner in this chapter: the set-valued declaration `weaklyAssociatedPrimes R M`,
  parallel to mathlib's `associatedPrimes`.
* `bridge/view`: `mem_weaklyAssociatedPrimes_iff`, turning the owner set back into the pointwise
  predicate.

Primitive data are only the witness `m : M` and the canonical annihilator ideal
`Ideal.torsionOf R M m`; primality is derived from membership in `minimalPrimes`.
-/
/-- Definition 10.66.1: a prime ideal `𝔭` of `R` is weakly associated to the `R`-module `M`
if `𝔭` is minimal among the prime ideals containing the annihilator of some element of `M`. -/
@[stacks 0547]
def IsWeaklyAssociatedToModule (𝔭 : Ideal R) : Prop :=
  ∃ m : M, 𝔭 ∈ (Ideal.torsionOf R M m).minimalPrimes

/-- A weakly associated ideal of `M` is prime. -/
theorem IsWeaklyAssociatedToModule.isPrime {𝔭 : Ideal R}
    (h𝔭 : IsWeaklyAssociatedToModule R M 𝔭) : 𝔭.IsPrime := by
  rcases h𝔭 with ⟨m, hm⟩
  exact Ideal.minimalPrimes_isPrime hm

end Ideal

/-- The set `WeakAss_R(M)` of weakly associated primes of the `R`-module `M`. -/
def weaklyAssociatedPrimes : Set (Ideal R) :=
  Ideal.IsWeaklyAssociatedToModule R M

@[simp] theorem mem_weaklyAssociatedPrimes_iff (𝔭 : Ideal R) :
    𝔭 ∈ weaklyAssociatedPrimes R M ↔ Ideal.IsWeaklyAssociatedToModule R M 𝔭 :=
  Iff.rfl

instance (𝔭 : weaklyAssociatedPrimes R M) : 𝔭.1.IsPrime :=
  𝔭.2.isPrime

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace Ideal

private theorem torsionOf_linearEquiv_eq
    {A : Type*} {N : Type*} {N' : Type*} [CommRing A]
    [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    (e : N ≃ₗ[A] N') (x : N) :
    Ideal.torsionOf A N' (e x) = Ideal.torsionOf A N x := by
  ext a
  rw [Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  constructor
  · intro ha
    apply e.injective
    simpa using ha
  · intro ha
    simpa using congrArg e ha

end Ideal

namespace LinearEquiv

/-- Weakly associated primes are preserved by an `R`-linear equivalence of `R`-modules. -/
theorem weaklyAssociatedPrimes_eq
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    {N' : Type*} [AddCommGroup N'] [Module A N']
    (e : N ≃ₗ[A] N') :
    weaklyAssociatedPrimes A N = weaklyAssociatedPrimes A N' := by
  ext p
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨e x, ?_⟩
    simpa [Ideal.torsionOf_linearEquiv_eq e x] using hx
  · rintro ⟨x, hx⟩
    refine ⟨e.symm x, ?_⟩
    simpa [Ideal.torsionOf_linearEquiv_eq e.symm x] using hx

end LinearEquiv

namespace weaklyAssociatedPrimes

theorem eq_empty_of_subsingleton [Subsingleton M] : weaklyAssociatedPrimes R M = ∅ := by
  ext 𝔭
  constructor
  · rintro ⟨m, hm⟩
    have htop : Ideal.torsionOf R M m = ⊤ := by
      simp [Subsingleton.elim m 0]
    simp [htop, Ideal.minimalPrimes_top] at hm
  · simp

theorem nonempty [Nontrivial M] : (weaklyAssociatedPrimes R M).Nonempty := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have hne_top : Ideal.torsionOf R M m ≠ ⊤ := by
    intro htop
    exact hm ((Ideal.torsionOf_eq_top_iff R m).mp htop)
  obtain ⟨𝔭, h𝔭⟩ := Ideal.nonempty_minimalPrimes hne_top
  exact ⟨𝔭, ⟨m, h𝔭⟩⟩

end weaklyAssociatedPrimes

end

end
