import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe uK vK uA vA uB vB uN vN

namespace DifferentialGradedModule

section

variable {KDGModA : Type uK} [Category.{vK} KDGModA]
variable {DerivedDGModA : Type uA} [Category.{vA} DerivedDGModA]
variable {DerivedDGModB : Type uB} [Category.{vB} DerivedDGModB]
variable {DGBimodAB : Type uN} [Category.{vN} DGBimodAB]

variable (QhA : KDGModA ⥤ DerivedDGModA)
variable (QisA : MorphismProperty KDGModA)
variable [QhA.IsLocalization QisA]
variable (isIsoOnCohomologySheaves : MorphismProperty DGBimodAB)
variable [QisA.ContainsIdentities]

-- Semantic search note: `lean_leansearch` returned `CategoryTheory.Functor.leftDerivedNatIso`,
-- and the owner/API choice was checked against the local uniqueness-of-derived-functor pattern in
-- `Lemma_20_27_2`, `Lemma_21_18_4`, and `Lemma_21_20_9`.

/-- Lemma 24.28.5: in the fixed-right-factor tensor situation above, if
`\mathcal N \to \mathcal N'` is an isomorphism on cohomology sheaves, formalized here by the
morphism property `isIsoOnCohomologySheaves`, and if such a morphism induces an isomorphism on
the corresponding underived tensor-to-derived source functors, then the induced transformation
between the left derived tensor functors
`(- \otimes^{\mathbf L}_{\mathcal A} \mathcal N)` and
`(- \otimes^{\mathbf L}_{\mathcal A} \mathcal N')` is an isomorphism of functors. -/
noncomputable abbrev leftDerivedTensorIsoOfIsIsoOnCohomologySheaves
    (tensorRightToDerived : DGBimodAB ⥤ (KDGModA ⥤ DerivedDGModB))
    (leftDerivedTensor : DGBimodAB → DerivedDGModA ⥤ DerivedDGModB)
    (tensorRightCounit :
      ∀ N : DGBimodAB, QhA ⋙ leftDerivedTensor N ⟶ tensorRightToDerived.obj N)
    (isLeftDerivedTensor :
      ∀ N : DGBimodAB,
        (leftDerivedTensor N).IsLeftDerivedFunctor (tensorRightCounit N) QisA)
    {N N' : DGBimodAB}
    (η : N ⟶ N')
    (hη : isIsoOnCohomologySheaves η)
    (hTensor :
      ∀ ⦃N N' : DGBimodAB⦄, (η : N ⟶ N') → isIsoOnCohomologySheaves η →
        IsIso (tensorRightToDerived.map η)) :
    leftDerivedTensor N ≅ leftDerivedTensor N' :=
  let _ := isLeftDerivedTensor N
  let _ := isLeftDerivedTensor N'
  let _ := hTensor η hη
  (show leftDerivedTensor N ≅ leftDerivedTensor N' from
    Functor.leftDerivedNatIso
      (leftDerivedTensor N)
      (leftDerivedTensor N')
      (tensorRightCounit N)
      (tensorRightCounit N')
      QisA
      (asIso (tensorRightToDerived.map η)))

/-- The natural transformation on left derived tensor functors coming from a cohomology-sheaf
isomorphism of right factors is pointwise an isomorphism. -/
theorem isIso_leftDerivedTensorHomOfIsIsoOnCohomologySheaves
    (tensorRightToDerived : DGBimodAB ⥤ (KDGModA ⥤ DerivedDGModB))
    (leftDerivedTensor : DGBimodAB → DerivedDGModA ⥤ DerivedDGModB)
    (tensorRightCounit :
      ∀ N : DGBimodAB, QhA ⋙ leftDerivedTensor N ⟶ tensorRightToDerived.obj N)
    (isLeftDerivedTensor :
      ∀ N : DGBimodAB,
        (leftDerivedTensor N).IsLeftDerivedFunctor (tensorRightCounit N) QisA)
    {N N' : DGBimodAB}
    (η : N ⟶ N')
    (hη : isIsoOnCohomologySheaves η)
    (hTensor :
      ∀ ⦃N N' : DGBimodAB⦄, (η : N ⟶ N') → isIsoOnCohomologySheaves η →
        IsIso (tensorRightToDerived.map η)) :
    IsIso
      ((leftDerivedTensorIsoOfIsIsoOnCohomologySheaves
        QhA
        QisA
        isIsoOnCohomologySheaves
        tensorRightToDerived
        leftDerivedTensor
        tensorRightCounit
        isLeftDerivedTensor
        η
        hη
        hTensor).hom) := sorry

end

end DifferentialGradedModule
