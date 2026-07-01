import Mathlib.RingTheory.Conductor
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open Polynomial

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace RingHom

/-
Situation 10.123.4 introduces the conductor ideal
`J = conductor R (φ X)` for the `R`-algebra structure on `S` induced by `φ.comp C`.
-/
#check ∀ φ : Polynomial R →+* S,
  letI : Algebra R S := (φ.comp C).toAlgebra
  conductor R (φ X)

/-
Situation 10.123.4 assumes that the constant-image subring `((φ.comp C).range)` is integrally
closed in `S`. The source-facing owner for that hypothesis is the specialized proposition
`IsIntegrallyClosedIn ((φ.comp C).range) S`.
-/
#check ∀ φ : Polynomial R →+* S, IsIntegrallyClosedIn (φ.comp C).range S

/-
For the source-facing reformulation of integrally closed image, use the canonical owner theorem
`Subring.isIntegrallyClosedIn_iff` directly at `((φ.comp C).range)`.
-/
recall Subring.isIntegrallyClosedIn_iff

/-- Companion bridge for Situation 10.123.4: after equipping `S` with the `R`-algebra structure
induced by `φ.comp C`, membership in the canonical conductor ideal `conductor R (φ X)` says
exactly that multiplication by the given element carries all of `S` into `φ.range`. -/
theorem mem_conductor_iff (φ : Polynomial R →+* S) (b : S) :
    letI : Algebra R S := (φ.comp C).toAlgebra
    b ∈ conductor R (φ X) ↔ ∀ c : S, b * c ∈ φ.range := by
  letI : Algebra R S := (φ.comp C).toAlgebra
  have hφ : ((aeval (φ X) : Polynomial R →ₐ[R] S)).toRingHom = φ := by
    apply Polynomial.ringHom_ext'
    · ext r
      simp [RingHom.algebraMap_toAlgebra]
    · simp
  rw [_root_.mem_conductor_iff]
  constructor
  · intro hb c
    have hc : b * c ∈ Algebra.adjoin R ({φ X} : Set S) := hb c
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hc
    rcases hc with ⟨p, hp⟩
    rw [hφ] at hp
    exact ⟨p, hp⟩
  · intro hb c
    rcases hb c with ⟨p, hp⟩
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    refine ⟨p, ?_⟩
    rw [hφ]
    exact hp

end RingHom

end
