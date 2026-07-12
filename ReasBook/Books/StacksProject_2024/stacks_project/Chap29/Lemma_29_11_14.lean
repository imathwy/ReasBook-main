import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.RingTheory.Artinian.Ring

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CommRingCat

universe u

-- The source lemma is source-facing: for an Artinian ring `A`, every morphism `Spec(A) → S` is
-- affine. The previous refine incorrectly strengthened this to arbitrary `A`.

section

variable {S : Scheme.{u}} {A : CommRingCat.{u}}
variable [IsArtinianRing A]

/-- Lemma 29.11.14: any morphism `Spec(A) → S` is affine, hence in particular when `A` is
Artinian. -/
theorem isAffineHom_of_spec (f : Spec A ⟶ S) : IsAffineHom f := by
  sorry

end
