import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import stacks_project.Chap10.IdempotentMap

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} [CommRing A]

namespace Ideal

/-- Reduction modulo `I B` induces a bijection on idempotents for every finite `A`-algebra. -/
def HasFiniteAlgebraIdempotentLifting (I : Ideal A) : Prop :=
  ∀ ⦃B : Type (max u v)⦄ [CommRing B] [Algebra A B] [Module.Finite A B],
    Function.Bijective (Ideal.Quotient.mk (Ideal.map (algebraMap A B) I)).idempotentMap

/-- The owner `I.HasFiniteAlgebraIdempotentLifting` specialized to the identity `A`-algebra. -/
theorem HasFiniteAlgebraIdempotentLifting.bijective_idempotentMap {I : Ideal A}
    (hI : I.HasFiniteAlgebraIdempotentLifting) :
    Function.Bijective (Ideal.Quotient.mk I).idempotentMap := by
  sorry

/-- Reduction modulo `I B` induces a bijection on idempotents for every integral `A`-algebra. -/
def HasIntegralAlgebraIdempotentLifting (I : Ideal A) : Prop :=
  ∀ ⦃B : Type (max u v)⦄ [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
    Function.Bijective (Ideal.Quotient.mk (Ideal.map (algebraMap A B) I)).idempotentMap

end Ideal

end
