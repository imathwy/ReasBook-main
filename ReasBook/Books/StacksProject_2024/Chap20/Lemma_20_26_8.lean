import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap20.Definition_20_26_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules Y)] [MonoidalPreadditive (RingedSpace.Modules Y)]

-- Proof sketch: by Lemma `20.26.4`, it suffices to check K-flatness on stalk complexes. For
-- `x : X`, Lemma `6.26.4` identifies the stalk of the pullback complex with extension of scalars
-- of the stalk complex of `K` along `\mathcal O_{Y, f(x)} \to \mathcal O_{X, x}`. Then Lemma
-- `15.59.3` shows that extension of scalars preserves K-flatness.
/-- Lemma 20.26.8: for a morphism of ringed spaces
`f : (X, \mathcal O_X) \to (Y, \mathcal O_Y)`, the pullback of a K-flat complex of
`\mathcal O_Y`-modules is a K-flat complex of `\mathcal O_X`-modules. -/
lemma pullback_isKFlat (f : X ⟶ Y) (K : CochainComplex (RingedSpace.Modules Y) ℤ) (hK : IsKFlat K) :
    IsKFlat (((RingedSpace.Hom.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  sorry

end AlgebraicGeometry.RingedSpace
