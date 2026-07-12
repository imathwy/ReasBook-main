import Mathlib
import StacksProject_2024.Chap29.Definition_29_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry RelativeDerivation

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism `Mono` owner and
-- local Chapter 29 precedent fixes the source-facing differential sheaf as `Ω[f.toShHom]`.

/-- Lemma 29.32.14: if `f : X ⟶ S` is a monomorphism of schemes, and in particular if it is an
immersion, then the sheaf of relative differentials `\Omega_{X/S}` is zero. -/
@[stacks 01UY]
theorem isZero_relativeDifferentials_of_mono
    (f : X ⟶ S) [Mono f] :
    IsZero (Ω[f.toShHom]) := sorry

end AlgebraicGeometry
