import Mathlib.Algebra.Homology.QuasiIso
import StacksProject_2024.stacks_project.Chap12.Lemma_12_7_2
import StacksProject_2024.stacks_project.Chap22.Lemma_22_20_4
import StacksProject_2024.stacks_project.Chap22.Lemma_22_28_3

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.Equivalence

section

variable {DGBimodAB : Type u} {AopTensorB : Type u}
variable [Category.{v} DGBimodAB] [HasZeroMorphisms DGBimodAB]
variable [Ring AopTensorB]

private abbrev propertyPFiltrationOfIso
    {P Q : CochainComplex (ModuleCat.{u, u} AopTensorB) ℤ}
    (F : CochainComplex.PropertyPFiltration P) (e : P ≅ Q) :
    CochainComplex.PropertyPFiltration Q where
  stage := F.stage
  stageZero := F.stageZero
  inclusion := F.inclusion
  mono := F.mono
  admissible := F.admissible
  hasColimit := F.hasColimit
  colimitIso := e.symm ≪≫ F.colimitIso
  pieceIndex := F.pieceIndex
  pieceDegree := F.pieceDegree
  pieceHasCoproduct := F.pieceHasCoproduct
  pieceIso := F.pieceIso

private theorem hasPropertyP_of_iso
    {P Q : CochainComplex (ModuleCat.{u, u} AopTensorB) ℤ}
    (e : P ≅ Q) (hP : CochainComplex.HasPropertyP P) :
    CochainComplex.HasPropertyP Q := by
  rcases hP with ⟨F⟩
  exact ⟨propertyPFiltrationOfIso F e⟩

/-- A differential graded `(A, B)`-bimodule has property `(P)` when its image under the equivalence
of Lemma `22.28.3` has the Chapter 22 module-side property `(P)` owner. -/
def HasPropertyP (e : DGBimodAB ≌ ModuleCat.{u, u} AopTensorB)
    (P : CochainComplex DGBimodAB ℤ) : Prop :=
  CochainComplex.HasPropertyP (((e.mapHomologicalComplex (up ℤ)).functor.obj P))

@[simp] theorem hasPropertyP_iff (e : DGBimodAB ≌ ModuleCat.{u, u} AopTensorB)
    (P : CochainComplex DGBimodAB ℤ) :
    e.HasPropertyP P ↔
      CochainComplex.HasPropertyP (((e.mapHomologicalComplex (up ℤ)).functor.obj P)) :=
  Iff.rfl

/-- The transported bimodule-side property `(P)` is witnessed by a Chapter 22 property `(P)`
filtration on the corresponding right differential graded `Aᵒᵖ ⊗_R B`-module. -/
@[simp] theorem hasPropertyP_iff_nonempty_propertyPFiltration
    (e : DGBimodAB ≌ ModuleCat.{u, u} AopTensorB) (P : CochainComplex DGBimodAB ℤ) :
    e.HasPropertyP P ↔
      Nonempty
        (CochainComplex.PropertyPFiltration (((e.mapHomologicalComplex (up ℤ)).functor.obj P))) :=
  Iff.rfl

/-- A chosen property `(P)` filtration on the right differential graded
`Aᵒᵖ ⊗_R B`-module corresponding to `P` exhibits property `(P)` on the original differential
graded `(A, B)`-bimodule. -/
theorem hasPropertyP_of_filtration (e : DGBimodAB ≌ ModuleCat.{u, u} AopTensorB)
    {P : CochainComplex DGBimodAB ℤ}
    (F : CochainComplex.PropertyPFiltration
      (((e.mapHomologicalComplex (up ℤ)).functor.obj P))) :
    e.HasPropertyP P :=
  F.hasPropertyP

end

section

variable {DGBimodAB : Type u} {AopTensorB : Type u}
variable [Category.{v} DGBimodAB] [Abelian DGBimodAB]
variable [Ring AopTensorB]

/-- Lemma 22.28.4: every differential graded `(A, B)`-bimodule admits a quasi-isomorphism from a
differential graded `(A, B)`-bimodule with property `(P)`. Here property `(P)` is the transported
Chapter 22 owner coming from the equivalence of Lemma `22.28.3`, and the source proof is the
module-side resolution theorem `22.20.4` applied after the induced additive equivalence on
cochain complexes. -/
@[stacks 0FQK]
theorem exists_quasiIso_from_hasPropertyP (e : DGBimodAB ≌ ModuleCat.{u, u} AopTensorB)
    (M : CochainComplex DGBimodAB ℤ) :
    ∃ (P : CochainComplex DGBimodAB ℤ) (π : P ⟶ M), QuasiIso π ∧ e.HasPropertyP P := by
  let E := e.mapHomologicalComplex (up ℤ)
  let _ : PreservesFiniteLimits e.functor := inferInstance
  have hLeft : leftExactFunctor _ _ e.functor := by
    simpa [leftExactFunctor_iff] using (inferInstance : PreservesFiniteLimits e.functor)
  letI : e.functor.Additive :=
    functor_additive_of_leftExact_or_rightExact e.functor (.inl hLeft)
  letI : e.inverse.Additive := e.toAdjunction.right_adjoint_additive
  rcases CochainComplex.exists_quasiIso_from_hasPropertyP (E.functor.obj M) with
    ⟨Q, π, hπ, hQ⟩
  refine ⟨E.inverse.obj Q, E.inverse.map π ≫ (E.unitIso.app M).inv, ?_, ?_⟩
  · have hπinv : QuasiIso (E.inverse.map π) := by
      simpa using
        (HomologicalComplex.quasiIso_map_iff_of_preservesHomology π e.inverse).2 hπ
    let _ : QuasiIso (E.inverse.map π) := hπinv
    exact quasiIso_comp _ _
  · change CochainComplex.HasPropertyP (E.functor.obj (E.inverse.obj Q))
    exact hasPropertyP_of_iso (E.counitIso.app Q).symm hQ

end

end CategoryTheory.Equivalence
