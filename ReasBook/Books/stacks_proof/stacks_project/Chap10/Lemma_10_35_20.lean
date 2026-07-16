import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap10.Lemma_10_35_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A] [Algebra.FiniteType ℤ A]

/- Lemma 10.35.20: any finite type algebra over `ℤ` is a Jacobson ring. This is the canonical
theorem `isJacobsonRing_of_finiteType`, specialized to the Jacobson base ring `ℤ`; the required
instance `IsJacobsonRing ℤ` is supplied by Lemma `10.35.6`, while the `ℤ`-algebra structure on a
commutative ring is canonical. -/
recall isJacobsonRing_of_finiteType

end
