import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_32_1
import StacksProject_2024.stacks_project.Chap29.Lemma_29_31_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced the scheme diagonal owner `pullback.diagonal` and
-- the closed-immersion API around it, while local Chapter 29 precedent fixes the source-facing
-- sheaf owners as `Ω[f.toShHom]` for relative differentials and `immersionConormalSheaf i` for
-- conormal sheaves.

/-- Lemma 29.32.7: for a morphism of schemes `f : X ⟶ S`, there is a canonical isomorphism
between the relative differential sheaf `\Omega_{X/S}` and the conormal sheaf of the diagonal
morphism `\Delta_{X/S} : X \to X \times_S X`. -/
@[stacks 08S2]
theorem exists_relativeDifferential_iso_diagonalConormalSheaf
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
    [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [(Opens.grothendieckTopology X).HasSheafCompose
      (CategoryTheory.forget CommRingCat.{u})]
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasBinaryCoproducts
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})]
    (f : X ⟶ S) :
    Nonempty
      (Ω[f.toShHom] ≅
        immersionConormalSheaf (pullback.diagonal f : X ⟶ pullback f f)) := sorry

end AlgebraicGeometry
