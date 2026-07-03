import Mathlib
import stacks_project.Chap06.Definition_6_26_1
import stacks_project.Chap20.Definition_20_46_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped AlgebraicGeometry
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

-- Proof sketch: the pullback functor on module sheaves induces a termwise pullback functor on
-- cochain complexes. Strict boundedness is preserved under this induced functor, and in each
-- degree a retract of a finite free module sheaf pulls back to a retract of a finite free module
-- sheaf.
/-- Lemma 20.46.4: if `f : (X, \mathcal O_X) \to (Y, \mathcal O_Y)` is a morphism of ringed
spaces and `\mathcal F^\bullet` is a strictly perfect complex of `\mathcal O_Y`-modules, then
the pulled-back complex `f^*\mathcal F^\bullet` is a strictly perfect complex of
`\mathcal O_X`-modules. -/
theorem cochainComplex_isStrictlyPerfect_pullback
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (E : CochainComplex (RingedSpace.Modules Y) ℤ)
    (hE : CochainComplex.IsStrictlyPerfect E) :
    CochainComplex.IsStrictlyPerfect (((f^*).mapHomologicalComplex (up ℤ)).obj E) := sorry

end AlgebraicGeometry.RingedSpace
