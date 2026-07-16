import StacksProject_2024.stacks_project.Chap13.Lemma_13_14_16
import StacksProject_2024.stacks_project.Chap22.«22_34_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe vA vB vC vDC uA uB uC uDC

namespace CategoryTheory

section

variable {KA : Type uA} {KB : Type uB} {KC : Type uC}
variable {DC : Type uDC}
variable [Category.{vA} KA] [Category.{vB} KB] [Category.{vC} KC]
variable [Category.{vDC} DC]
variable (QisA : MorphismProperty KA) (QisB : MorphismProperty KB)
variable [QisB.ContainsIdentities]
variable (QC : KC ⥤ DC)
variable (tensorN : KA ⥤ KB) (tensorN' : KB ⥤ KC) (tensorNN' : KA ⥤ KC)

-- Semantic recall: `Functor.leftDerivedCompComparison` is the canonical Chapter `13` owner for
-- the iterated left-derived comparison, and `Functor.leftDerivedNatIso` transports its codomain
-- along the underived associativity identification `tensorN ⋙ tensorN' ≅ tensorNN'`. The local
-- dependency `22.34.0.1` records the source comparison as the identity-denominator specialization
-- of `Functor.leftDerivedValueProjection`.

/-- The canonical comparison from the iterated derived tensor functor
`(- ⊗_Aᴸ N) ⊗_Bᴸ N'` to the direct derived tensor functor `- ⊗_Aᴸ N''`, obtained by
transporting `Functor.leftDerivedCompComparison` along the associativity identification
`tensorN ⋙ tensorN' ≅ tensorNN'`. -/
noncomputable def derivedTensorCompositionComparison
    [(tensorN ⋙ QisB.Q).HasLeftDerivedFunctor QisA]
    [(tensorN' ⋙ QC).HasLeftDerivedFunctor QisB]
    [(tensorNN' ⋙ QC).HasLeftDerivedFunctor QisA]
    (tensorAssoc : tensorN ⋙ tensorN' ≅ tensorNN') :
    ((tensorN ⋙ QisB.Q).totalLeftDerived QisA.Q QisA ⋙
        (tensorN' ⋙ QC).totalLeftDerived QisB.Q QisB) ⟶
      (tensorNN' ⋙ QC).totalLeftDerived QisA.Q QisA :=
  let tensorAssocQC : tensorN ⋙ (tensorN' ⋙ QC) ≅ tensorNN' ⋙ QC :=
    Functor.associator tensorN tensorN' QC ≪≫ Functor.isoWhiskerRight tensorAssoc QC
  letI : (tensorN ⋙ (tensorN' ⋙ QC)).HasLeftDerivedFunctor QisA :=
    (Functor.hasLeftDerivedFunctor_iff_of_iso tensorAssocQC QisA).2 inferInstance
  let iteratedDerived := (tensorN ⋙ (tensorN' ⋙ QC)).totalLeftDerived QisA.Q QisA
  let directDerived := (tensorNN' ⋙ QC).totalLeftDerived QisA.Q QisA
  let iteratedCounit := (tensorN ⋙ (tensorN' ⋙ QC)).totalLeftDerivedCounit QisA.Q QisA
  let directCounit := (tensorNN' ⋙ QC).totalLeftDerivedCounit QisA.Q QisA
  Functor.leftDerivedCompComparison QisA QisB tensorN (tensorN' ⋙ QC) ≫
    (Functor.leftDerivedNatIso
      iteratedDerived directDerived iteratedCounit directCounit QisA tensorAssocQC).hom

/-- Bridge/view API: the same canonical derived tensor composition comparison, now with the
left-derived-functor existence of `tensorNN' ⋙ QC` passed explicitly as ordinary data. This keeps
source-facing existential theorems free of statement-level instance switches while still reusing
`derivedTensorCompositionComparison` as the canonical owner. -/
noncomputable def derivedTensorCompositionComparisonOfHasLeftDerivedFunctor
    [(tensorN ⋙ QisB.Q).HasLeftDerivedFunctor QisA]
    [(tensorN' ⋙ QC).HasLeftDerivedFunctor QisB]
    (hTensorNN' : (tensorNN' ⋙ QC).HasLeftDerivedFunctor QisA)
    (tensorAssoc : tensorN ⋙ tensorN' ≅ tensorNN') :
    ((tensorN ⋙ QisB.Q).totalLeftDerived QisA.Q QisA ⋙
        (tensorN' ⋙ QC).totalLeftDerived QisB.Q QisB) ⟶
      (tensorNN' ⋙ QC).totalLeftDerived QisA.Q QisA :=
  letI := hTensorNN'
  derivedTensorCompositionComparison QisA QisB QC tensorN tensorN' tensorNN' tensorAssoc

/-- Lemma 22.34.1: let `tensorN`, `tensorN'`, and `tensorNN'` model tensoring with
differential graded bimodules `N`, `N'`, and `N'' = N ⊗_B N'`, respectively. If the
underived tensor functors are identified by associativity and the right tensor functor
`tensorN'` computes its left derived functor at a chosen source object `N'₀`, equivalently if
the comparison `22.34.0.1` for `N_B ⊗_Bᴸ N'₀` is an isomorphism, then the canonical natural
comparison from the composite derived tensor functor `(- ⊗_Aᴸ N) ⊗_Bᴸ N'` to `- ⊗_Aᴸ N''` is an
isomorphism. -/
@[stacks 0BZ3]
theorem derivedTensorCompositionComparison_isIso
    (N'₀ : KB)
    [tensorN'.ComputesLeftDerivedAt QisB N'₀]
    [(tensorN ⋙ QisB.Q).HasLeftDerivedFunctor QisA]
    [(tensorN' ⋙ QC).HasLeftDerivedFunctor QisB]
    [(tensorNN' ⋙ QC).HasLeftDerivedFunctor QisA]
    (tensorAssoc : tensorN ⋙ tensorN' ≅ tensorNN') :
    IsIso
      (derivedTensorCompositionComparison
        QisA QisB QC tensorN tensorN' tensorNN' tensorAssoc) := by
  sorry

end

end CategoryTheory
