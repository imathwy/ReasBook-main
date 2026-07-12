import StacksProject_2024.Chap22.Lemma_22_27_17

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory

noncomputable section

universe u v w

section

variable {R : Type u} [CommRing R]
variable {ModdgA : Type v} {ModdgB : Type w}
variable [DA : DifferentialGradedCategory R ModdgA]
variable [DB : DifferentialGradedCategory R ModdgB]

variable [HasShift (K R ModdgA) ℤ] [HasShift (K R ModdgB) ℤ]
variable [HasZeroObject (K R ModdgA)] [HasZeroObject (K R ModdgB)]
variable [Preadditive (K R ModdgA)] [Preadditive (K R ModdgB)]
variable [∀ n : ℤ, (shiftFunctor (K R ModdgA) n).Additive]
variable [∀ n : ℤ, (shiftFunctor (K R ModdgB) n).Additive]
variable [Pretriangulated (K R ModdgA)] [Pretriangulated (K R ModdgB)]

-- Source/core/bridge triage:
-- * source-facing: the tensor-by-bimodule DG functor of `22.33.0.1` on homotopy categories;
-- * core/canonical: the exactness owner `DgFunctor.mapK_exact`;
-- * bridge/view: the induced functor `tensorWithN.mapK`.
--
-- Semantic recall hits:
-- `CategoryTheory.Functor.IsTriangulated`,
-- `DifferentialGradedCategory.DgFunctor.mapK_exact`.
-- Local Chapter 22 precedent in `Lemma_22_29_1` and `Lemma_22_30_1` fixes the source functor
-- `(22.33.0.1)` on the project-local DG owner `tensorWithN.mapK`.

/-- Lemma 22.33.1: the functor of `22.33.0.1`, viewed on homotopy categories as
`tensorWithN.mapK : K R ModdgA ⥤ K R ModdgB`, is exact in the triangulated sense. -/
@[stacks 09LR]
theorem tensorWithNOnHomotopyCategory_exact
    (tensorWithN : DgFunctor R ModdgA ModdgB) [tensorWithN.mapK.CommShift ℤ] :
    tensorWithN.mapK.IsTriangulated :=
  inferInstance

end
