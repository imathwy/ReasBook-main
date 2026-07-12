import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommSemiring R] [Semiring S] [Algebra R S]
variable [AddCommMonoid M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite R S]

namespace Module.Finite

/-- Lemma 10.7.2: for a finite ring map `R → S` and an `S`-module `M`, finiteness of `M` as an
`R`-module is equivalent to finiteness of `M` as an `S`-module. -/
@[stacks 00GJ]
theorem iff_of_finite :
    Module.Finite R M ↔ Module.Finite S M :=
  ⟨fun _ ↦ of_restrictScalars_finite R S M, fun _ ↦ trans S M⟩

end Module.Finite
