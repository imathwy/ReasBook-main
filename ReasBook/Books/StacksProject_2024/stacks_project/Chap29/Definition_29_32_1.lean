import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap17.Definition_17_28_3

-- Declarations for this item will be appended below by the statement pipeline.

open TopCat.Sheaf

namespace AlgebraicGeometry.RingedSpace

open RingedSpace.Hom
open scoped AlgebraicGeometry RelativeDerivation

scoped[AlgebraicGeometry] notation3:max "Ω[" f "]" =>
  Ω(inverseImageStructureSheafHomComm f)

scoped[AlgebraicGeometry] notation3:max "d[" f "]" =>
  relativeDifferential (inverseImageStructureSheafHomComm f)

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry

open scoped AlgebraicGeometry RelativeDerivation

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S)

-- Semantic recall:
-- `lean_leansearch` recalled the relative-differentials owner, and local verification against
-- `stacks_project.Chap17.Definition_17_28_10` plus downstream use across Chapter 29 shows that for
-- scheme morphisms the stable source-facing surface is the Chapter 17 ringed-space notation
-- specialized along the canonical ringed-space morphism `f.toShHom`.

/- Definition 29.32.1: for a morphism of schemes `f : X ⟶ S`, the sheaf of differentials
`\Omega_{X/S}` is the sheaf of relative differentials of the underlying morphism of ringed
spaces. The canonical source-facing owner in this chapter is the specialized ringed-space notation
`Ω[f.toShHom]`, equipped with its universal `S`-derivation `d[f.toShHom]`. -/
#check Ω[f.toShHom]

/- Companion recall: the universal `S`-derivation of `Ω_{X/S}` is the canonical owner
`d[f.toShHom]`. -/
#check d[f.toShHom]

end AlgebraicGeometry
