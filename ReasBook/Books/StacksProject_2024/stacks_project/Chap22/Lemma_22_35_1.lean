import StacksProject_2024.stacks_project.Chap22.Lemma_22_26_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory

universe u v w

section

variable {R : Type u} [CommRing R]
variable {DGModE : Type v} {ComplexdgO : Type w}
variable [DGModE_dg : DifferentialGradedCategory R DGModE]
variable [ComplexdgO_dg : DifferentialGradedCategory R ComplexdgO]

-- Source/core/bridge triage:
-- * source-facing: existence of the DG tensor functor `- ⊗_E K^•` with value `K^•`
--   on `E`;
-- * core/canonical: the Chapter 22 DG-functor owner `DgFunctor` and its induced functor
--   `DgFunctor.mapComp` on closed degree-`0` morphisms;
-- * bridge/view: `IsTensorWithKFunctor E K F`, which records the source-facing constraints on a
--   fixed DG functor `F` and exposes the direct-sum preservation theorem downstream.

/-- A DG functor `F` models the source tensor functor `- ⊗_E K^•` when it carries `E` to `K^•`
and its induced functor on closed degree-`0` morphisms preserves direct sums. -/
class IsTensorWithKFunctor
    (E : DGModE) (K : ComplexdgO) (F : DgFunctor R DGModE ComplexdgO) : Prop where
  obj_eq : F.obj E = K
  preservesDirectSums {ι : Type (max u v w)} :
    PreservesColimitsOfShape (Discrete ι) (DgFunctor.mapComp F)

attribute [simp] IsTensorWithKFunctor.obj_eq

theorem IsTensorWithKFunctor.preservesDirectSumsOfShape
    {E : DGModE} {K : ComplexdgO} {F : DgFunctor R DGModE ComplexdgO}
    (hF : IsTensorWithKFunctor E K F) {ι : Type (max u v w)} :
    PreservesColimitsOfShape (Discrete ι) (DgFunctor.mapComp F) :=
  hF.preservesDirectSums

/-- Lemma 22.35.1: in the ambient Chapter 22 differential graded setting, there exists a functor
`- ⊗_E K^• : Mod^{dg}_{(E, d)} ⟶ Comp^{dg}(𝒪)` whose value on `E` is `K^•` and whose induced
functor on closed degree-`0` morphisms commutes with direct sums. -/
@[stacks 09LV]
theorem exists_tensorWithKFunctor
    (E : DGModE) (K : ComplexdgO) :
    ∃ F : DgFunctor R DGModE ComplexdgO, IsTensorWithKFunctor E K F := sorry

end
