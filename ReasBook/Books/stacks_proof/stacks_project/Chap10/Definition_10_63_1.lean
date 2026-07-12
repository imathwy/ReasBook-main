import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

namespace Ideal

/-
Domain triage: this file is in commutative algebra of associated primes. The owner abstraction is
mathlib's `IsAssociatedPrime` / `associatedPrimes`, while Definition 10.63.1 is source-facing
because it remembers the exact annihilator of an element rather than only its radical. The
primitive data for that source-facing notion should therefore be the canonical annihilator ideal
`Ideal.torsionOf R M m`, with the bridge to the owner abstraction derived afterwards.
-/

/-- Definition 10.63.1: a prime ideal `𝔭` of `R` is associated to the `R`-module `M` if `𝔭`
is the annihilator ideal of some element of `M`. -/
@[stacks 00LA]
def IsAssociatedToModule (𝔭 : Ideal R) : Prop :=
  𝔭.IsPrime ∧ ∃ m : M, 𝔭 = torsionOf R M m

theorem isAssociatedToModule_map_of_injective {M' : Type*} [AddCommGroup M'] [Module R M']
    {𝔭 : Ideal R} (h𝔭 : IsAssociatedToModule R M 𝔭) (f : M →ₗ[R] M')
    (hf : Function.Injective f) :
    IsAssociatedToModule R M' 𝔭 := by
  rcases h𝔭 with ⟨hprime, m, hm⟩
  refine ⟨hprime, f m, ?_⟩
  ext r
  rw [hm, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff, ← map_smul, map_eq_zero_iff f hf]

private theorem torsionOf_eq_bot_colon_singleton (m : M) :
    torsionOf R M m = (⊥ : Submodule R M).colon ({m} : Set M) := by
  calc
    torsionOf R M m = (Submodule.span R ({m} : Set M)).annihilator := by
      simpa [Ideal.torsionOf] using (Submodule.annihilator_span_singleton m).symm
    _ = (⊥ : Submodule R M).colon ({m} : Set M) := by
      rw [Submodule.bot_colon']

/-- Companion re-expression of `IsAssociatedToModule` using `Ideal.torsionOf`, matching the
textbook annihilator-of-an-element wording. -/
theorem isAssociatedToModule_iff_exists_torsionOf (𝔭 : Ideal R) :
    IsAssociatedToModule R M 𝔭 ↔ 𝔭.IsPrime ∧ ∃ m : M, 𝔭 = torsionOf R M m := by
  rfl

/-- A textbook-associated prime is associated in mathlib's radical-based sense. -/
theorem IsAssociatedToModule.isAssociatedPrime {𝔭 : Ideal R}
    (h𝔭 : IsAssociatedToModule R M 𝔭) :
    IsAssociatedPrime 𝔭 M := by
  rcases h𝔭 with ⟨h𝔭, m, hm⟩
  refine ⟨h𝔭, m, ?_⟩
  calc
    𝔭 = (torsionOf R M m).radical := by
      simpa [hm] using h𝔭.radical.symm
    _ = ((⊥ : Submodule R M).colon ({m} : Set M)).radical := by
      rw [torsionOf_eq_bot_colon_singleton R M m]

theorem isAssociatedToModule_comap {S : Type*} [CommRing S] [Algebra R S]
    [Module S M] [IsScalarTower R S M] {P : Ideal S} (hP : IsAssociatedToModule S M P) :
    IsAssociatedToModule R M (Ideal.comap (algebraMap R S) P) := by
  rcases hP with ⟨hP, m, hm⟩
  refine ⟨hP.comap (algebraMap R S), m, ?_⟩
  ext r
  rw [hm, Ideal.mem_comap, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  simp [algebraMap_smul]

/-- In a Noetherian ring, the textbook notion of an associated prime agrees with mathlib's
`IsAssociatedPrime`. -/
theorem isAssociatedToModule_iff_isAssociatedPrime [IsNoetherianRing R] (𝔭 : Ideal R) :
    IsAssociatedToModule R M 𝔭 ↔ IsAssociatedPrime 𝔭 M := by
  rw [isAssociatedToModule_iff_exists_torsionOf, isAssociatedPrime_iff]
  constructor
  · rintro ⟨h𝔭, m, hm⟩
    exact ⟨h𝔭, m, hm.trans (torsionOf_eq_bot_colon_singleton R M m)⟩
  · rintro ⟨h𝔭, m, hm⟩
    exact ⟨h𝔭, m, hm.trans (torsionOf_eq_bot_colon_singleton R M m).symm⟩

end Ideal

namespace LinearEquiv

theorem isAssociatedToModule_iff {M' : Type*} [AddCommGroup M'] [Module R M']
    (e : M ≃ₗ[R] M') {𝔭 : Ideal R} :
    Ideal.IsAssociatedToModule R M 𝔭 ↔ Ideal.IsAssociatedToModule R M' 𝔭 := by
  constructor
  · intro h𝔭
    exact Ideal.isAssociatedToModule_map_of_injective R M h𝔭 e.toLinearMap e.injective
  · intro h𝔭
    exact Ideal.isAssociatedToModule_map_of_injective R M' h𝔭 e.symm.toLinearMap e.symm.injective

end LinearEquiv

/-- The set of textbook-associated primes of the `R`-module `M`. -/
def associatedPrimesOfModule : Set (Ideal R) :=
  Ideal.IsAssociatedToModule R M

/-- A prime ideal belongs to `associatedPrimesOfModule R M` exactly when it is associated to
`M` in the textbook sense. -/
@[simp] theorem mem_associatedPrimesOfModule_iff (𝔭 : Ideal R) :
    𝔭 ∈ associatedPrimesOfModule R M ↔ Ideal.IsAssociatedToModule R M 𝔭 :=
  Iff.rfl

namespace LinearEquiv

theorem associatedPrimesOfModule_eq {M' : Type*} [AddCommGroup M'] [Module R M']
    (e : M ≃ₗ[R] M') :
    associatedPrimesOfModule R M = associatedPrimesOfModule R M' := by
  ext 𝔭
  exact e.isAssociatedToModule_iff

end LinearEquiv

/-- The textbook-associated primes of `M` are contained in mathlib's owner set
`associatedPrimes R M`. -/
theorem associatedPrimesOfModule_subset_associatedPrimes :
    associatedPrimesOfModule R M ⊆ associatedPrimes R M := fun _ h ↦ h.isAssociatedPrime

/-- In a Noetherian ring, the textbook-associated primes of `M` coincide with mathlib's
`associatedPrimes R M`. -/
theorem associatedPrimesOfModule_eq_associatedPrimes [IsNoetherianRing R] :
    associatedPrimesOfModule R M = associatedPrimes R M := by
  ext 𝔭
  change Ideal.IsAssociatedToModule R M 𝔭 ↔ IsAssociatedPrime 𝔭 M
  exact Ideal.isAssociatedToModule_iff_isAssociatedPrime R M 𝔭

end
