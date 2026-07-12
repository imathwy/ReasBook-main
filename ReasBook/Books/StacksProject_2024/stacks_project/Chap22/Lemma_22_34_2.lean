import StacksProject_2024.Chap22.Lemma_22_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe vA vB vC vDA vDB vDC uA uB uC uDA uDB uDC

namespace CategoryTheory

section

variable {KA : Type uA} {KB : Type uB} {KC : Type uC}
variable {DA : Type uDA} {DB : Type uDB} {DC : Type uDC}
variable [Category.{vA} KA] [Category.{vB} KB] [Category.{vC} KC]
variable [Category.{vDA} DA] [Category.{vDB} DB] [Category.{vDC} DC]
variable (QisA : MorphismProperty KA) (QisB : MorphismProperty KB)
variable (QisC : MorphismProperty KC)
variable [QisB.ContainsIdentities]
variable (QC : KC ⥤ DC) [QC.IsLocalization QisC]
variable (tensorN : KA ⥤ KB) (tensorN' : KB ⥤ KC) (tensorNN' : KA ⥤ KC)

-- Semantic recall hits: Lemma `22.34.1` already owns the canonical `IsIso` statement for the
-- derived composition comparison once `tensorN'` is known to compute its left-derived value at the
-- chosen object. The source-facing content of Lemma `22.34.2` is the bridge from the displayed
-- identity-denominator comparison `22.34.1.1`, formalized by `leftDerivedValueProjection`, to
-- that canonical owner via `computesLeftDerivedAtOfIsIsoLeftDerivedValueProjection`.

/-- Lemma 22.34.2: if the displayed comparison `22.34.1.1`
`leftDerivedValueProjection QisB tensorN' (𝟙 freeLeftB) (QisB.id_mem freeLeftB)` is an
isomorphism for the right tensor functor `tensorN'`, then the canonical comparison morphism from
the composite derived tensor functor `(- ⊗_Aᴸ N) ⊗_Bᴸ N'` to `- ⊗_Aᴸ N''` is an isomorphism. This
is the source-facing bridge from the displayed tensor-algebra comparison to the canonical owner
`derivedTensorCompositionComparison_isIso` from Lemma `22.34.1`. -/
@[stacks 0BZ5]
theorem derivedTensorCompositionComparison_isIso_of_leftDerivedValueProjection_isIso
    (freeLeftB : KB)
    [tensorN'.HasPointwiseLeftDerivedFunctorAt QisB freeLeftB]
    (h :
      IsIso
        (leftDerivedValueProjection
          QisB tensorN' (𝟙 freeLeftB) (QisB.id_mem freeLeftB)))
    [(tensorN ⋙ QisB.Q).HasLeftDerivedFunctor QisA]
    [(tensorN' ⋙ QC).HasLeftDerivedFunctor QisB]
    [(tensorNN' ⋙ QC).HasLeftDerivedFunctor QisA]
    (tensorAssoc : tensorN ⋙ tensorN' ≅ tensorNN') :
    IsIso
      (derivedTensorCompositionComparison
        QisA QisB QC tensorN tensorN' tensorNN' tensorAssoc) :=
by
  letI : tensorN'.ComputesLeftDerivedAt QisB freeLeftB :=
    computesLeftDerivedAtOfIsIsoLeftDerivedValueProjection
      QisB tensorN' freeLeftB h
  exact
    derivedTensorCompositionComparison_isIso
      QisA QisB QC tensorN tensorN' tensorNN' freeLeftB tensorAssoc

-- Canonical instance companion to Lemma 22.34.2: once the displayed
-- identity-denominator comparison `22.34.1.1` is available as an `IsIso` instance,
-- the resulting comparison from `(- ⊗_Aᴸ N) ⊗_Bᴸ N'` to `- ⊗_Aᴸ N''` is inferred
-- by typeclass search.
set_option synthInstance.checkSynthOrder false in
instance derivedTensorCompositionComparison_isIso_of_leftDerivedValueProjection
    (freeLeftB : KB)
    [tensorN'.HasPointwiseLeftDerivedFunctorAt QisB freeLeftB]
    [IsIso
      (leftDerivedValueProjection
        QisB tensorN' (𝟙 freeLeftB) (QisB.id_mem freeLeftB))]
    [(tensorN ⋙ QisB.Q).HasLeftDerivedFunctor QisA]
    [(tensorN' ⋙ QC).HasLeftDerivedFunctor QisB]
    [(tensorNN' ⋙ QC).HasLeftDerivedFunctor QisA]
    (tensorAssoc : tensorN ⋙ tensorN' ≅ tensorNN') :
    IsIso
      (derivedTensorCompositionComparison
        QisA QisB QC tensorN tensorN' tensorNN' tensorAssoc) :=
  derivedTensorCompositionComparison_isIso_of_leftDerivedValueProjection_isIso
    QisA QisB QC tensorN tensorN' tensorNN' freeLeftB inferInstance tensorAssoc

end

end CategoryTheory
