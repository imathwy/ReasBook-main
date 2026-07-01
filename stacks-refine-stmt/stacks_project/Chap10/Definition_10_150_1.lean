import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Definition 10.150.1: the textbook notion that a ring map `R → S` is formally étale is the
canonical predicate `RingHom.FormallyEtale`, which classically is equivalent to the unique lifting
property against square-zero thickenings. -/
recall RingHom.FormallyEtale

-- Proof sketch: convert the ring map `f` to its induced `R`-algebra structure on `S`, then apply
-- `Algebra.FormallyEtale.iff_comp_bijective` to identify formal étaleness with bijectivity of the
-- map obtained by postcomposing lifts with the quotient map `A → A ⧸ I`; bijectivity is exactly
-- existence and uniqueness of the dotted lift in the square-zero diagram.
/-- The infinitesimal lifting criterion for a formally étale ring map. -/
theorem formallyEtale_iff_existsUnique_lift (f : R →+* S) :
    f.FormallyEtale ↔
      letI := f.toAlgebra
      ∀ ⦃A : Type (max u v)⦄ [CommRing A] [Algebra R A] (I : Ideal A) (_ : I ^ 2 = ⊥)
        (g : S →ₐ[R] A ⧸ I), ∃! g' : S →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp g' = g := by
  letI := f.toAlgebra
  change Algebra.FormallyEtale R S ↔
    ∀ ⦃A : Type (max u v)⦄ [CommRing A] [Algebra R A] (I : Ideal A) (_ : I ^ 2 = ⊥)
      (g : S →ₐ[R] A ⧸ I), ∃! g' : S →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp g' = g
  rw [Algebra.FormallyEtale.iff_comp_bijective]
  constructor <;> intro h A _ _ I hI
  · simpa [Function.bijective_iff_existsUnique] using h I hI
  · simpa [Function.bijective_iff_existsUnique] using h I hI

end RingHom
