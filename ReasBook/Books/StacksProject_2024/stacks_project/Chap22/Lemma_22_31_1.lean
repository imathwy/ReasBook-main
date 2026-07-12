import StacksProject_2024.Chap22.Lemma_22_27_17

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory

noncomputable section

universe u v w

-- Source/core/bridge triage:
-- * source-facing: the internal-Hom DG functor attached to a bimodule `N`;
-- * core/canonical: the exactness owner `DgFunctor.mapK_exact`;
-- * bridge/view: the induced homotopy-category functor `homOverBFromN.mapK`.

section

variable {R : Type u} [CommRing R]
variable {DGModB : Type v} {DGModA : Type w}
variable [DifferentialGradedCategory R DGModB] [DifferentialGradedCategory R DGModA]

variable [HasShift (K R DGModB) ℤ] [HasShift (K R DGModA) ℤ]
variable [HasZeroObject (K R DGModB)] [HasZeroObject (K R DGModA)]
variable [Preadditive (K R DGModB)] [Preadditive (K R DGModA)]
variable [∀ n : ℤ, (shiftFunctor (K R DGModB) n).Additive]
variable [∀ n : ℤ, (shiftFunctor (K R DGModA) n).Additive]
variable [Pretriangulated (K R DGModB)] [Pretriangulated (K R DGModA)]

-- Semantic recall hits:
-- `CategoryTheory.Functor.IsTriangulated`,
-- `DifferentialGradedCategory.DgFunctor.mapK_exact`.
-- Local Chapter 22 precedent in `Lemma_22_30_1` and `Lemma_22_33_1` fixes the source functor on
-- the canonical DG owner `homOverBFromN.mapK`.

/-- Lemma 22.31.1: the functor of `22.31.0.1`, viewed on homotopy categories as
`homOverBFromN.mapK : K R DGModB ⥤ K R DGModA`, is exact in the
triangulated sense. -/
@[stacks 09LH]
theorem homOverBFromNOnHomotopyCategory_exact
    (homOverBFromN : DgFunctor R DGModB DGModA)
    [homOverBFromN.mapK.CommShift ℤ] :
    homOverBFromN.mapK.IsTriangulated :=
  DgFunctor.mapK_exact homOverBFromN

end
