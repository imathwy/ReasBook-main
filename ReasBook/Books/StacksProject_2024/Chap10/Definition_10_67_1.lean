import StacksProject_2024.Chap10.Definition_10_63_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/- Domain triage: this item lies in commutative algebra of associated primes of modules.
Sampled declarations in this domain are the chapter's source-facing `associatedPrimesOfModule`,
the chapter bridge `associatedPrimesOfModule_eq_associatedPrimes`, and mathlib's owner
`associatedPrimes` / `IsAssociatedPrime`. The numbered item has two `source-facing` layers:
the module-level owner `embeddedAssociatedPrimes R M`, and the ring-level specialization
`embeddedPrimes R := embeddedAssociatedPrimes R R`. Both are derived data on top of the owner set
of associated primes rather than primitive module data. -/

/-- Definition 10.67.1: the embedded associated primes of the `R`-module `M` are the associated
primes of `M` that are not minimal among the associated primes of `M`. -/
def embeddedAssociatedPrimes : Set (Ideal R) :=
  { p |
      p ∈ associatedPrimesOfModule R M ∧
        ¬ Minimal (· ∈ associatedPrimesOfModule R M) p }

/-- A prime ideal is an embedded associated prime exactly when it is associated to `M` and is not
minimal among the associated primes of `M`. -/
@[simp] theorem mem_embeddedAssociatedPrimes_iff (p : Ideal R) :
    p ∈ embeddedAssociatedPrimes R M ↔
      p ∈ associatedPrimesOfModule R M ∧
        ¬ Minimal (· ∈ associatedPrimesOfModule R M) p :=
  Iff.rfl

/-- Over a Noetherian ring, the embedded associated primes of `M` can be read using mathlib's
`associatedPrimes R M`. -/
theorem mem_embeddedAssociatedPrimes_iff_mem_associatedPrimes [IsNoetherianRing R]
    (p : Ideal R) :
    p ∈ embeddedAssociatedPrimes R M ↔
      p ∈ associatedPrimes R M ∧
        ¬ Minimal (· ∈ associatedPrimes R M) p := by
  simp [embeddedAssociatedPrimes, associatedPrimesOfModule_eq_associatedPrimes R M]

/-- Over a Noetherian ring, `M` has no embedded associated primes exactly when every associated
prime of `M` is minimal among the associated primes of `M`. -/
theorem embeddedAssociatedPrimes_eq_empty_iff [IsNoetherianRing R] :
    embeddedAssociatedPrimes R M = ∅ ↔
      ∀ p ∈ associatedPrimes R M, Minimal (· ∈ associatedPrimes R M) p := by
  constructor
  · intro h p hp
    by_contra hp_min
    have hp_emb : p ∈ embeddedAssociatedPrimes R M := by
      rw [mem_embeddedAssociatedPrimes_iff_mem_associatedPrimes]
      exact ⟨hp, hp_min⟩
    simp [h] at hp_emb
  · intro h
    ext p
    constructor
    · intro hp
      rw [mem_embeddedAssociatedPrimes_iff_mem_associatedPrimes] at hp
      exact (hp.2 (h p hp.1)).elim
    · intro hp
      exact hp.elim

end

section

variable (R : Type u) [CommRing R]

/-- Definition 10.67.1, ring specialization: the embedded primes of `R` are the embedded
associated primes of `R` viewed as an `R`-module. -/
abbrev embeddedPrimes : Set (Ideal R) :=
  embeddedAssociatedPrimes R R

/-- A prime ideal is an embedded prime of `R` exactly when it is an embedded associated prime of
`R` as a module over itself. -/
@[simp] theorem mem_embeddedPrimes_iff (p : Ideal R) :
    p ∈ embeddedPrimes R ↔ p ∈ embeddedAssociatedPrimes R R :=
  Iff.rfl

/-- A prime ideal is an embedded prime of `R` exactly when it is associated to `R` and is not
minimal among the associated primes of `R`. -/
@[simp] theorem mem_embeddedPrimes_iff_mem_associatedPrimes [IsNoetherianRing R] (p : Ideal R) :
    p ∈ embeddedPrimes R ↔
      p ∈ associatedPrimes R R ∧
        ¬ Minimal (· ∈ associatedPrimes R R) p := by
  exact mem_embeddedAssociatedPrimes_iff_mem_associatedPrimes R R p

/-- The ring `R` has no embedded primes exactly when every associated prime of `R` is minimal
among the associated primes of `R`. -/
theorem embeddedPrimes_eq_empty_iff [IsNoetherianRing R] :
    embeddedPrimes R = ∅ ↔
      ∀ p ∈ associatedPrimes R R, Minimal (· ∈ associatedPrimes R R) p := by
  exact embeddedAssociatedPrimes_eq_empty_iff R R

end
