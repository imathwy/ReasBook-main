import StacksProject_2024.stacks_project.Chap24.Lemma_24_28_7
import StacksProject_2024.stacks_project.Chap24.Lemma_24_29_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe uA vA uA' vA' uA'' vA'' uN vN uN' vN' uNN vNN

-- Semantic search note: `lean_leansearch` surfaced the right-adjoint uniqueness API
-- `CategoryTheory.Adjunction.rightAdjointUniq`; the statement below combines that owner with
-- the local tensor comparison formalization from `Lemma_24_28_7` and the derived tensor/Hom
-- adjunction interface from `Lemma_24_29_3`.

namespace DifferentialGradedModule

section

variable {DerivedDGModA : Type uA} [Category.{vA} DerivedDGModA]
variable {DerivedDGModA' : Type uA'} [Category.{vA'} DerivedDGModA']
variable {DerivedDGModA'' : Type uA''} [Category.{vA''} DerivedDGModA'']
variable {DGBimodAA' : Type uN} [Category.{vN} DGBimodAA']
variable {DGBimodA'A'' : Type uN'} [Category.{vN'} DGBimodA'A'']
variable {DGBimodAA'' : Type uNN} [Category.{vNN} DGBimodAA'']

/-- Lemma 24.29.7: let `(\mathcal{C}, \mathcal{O})` be a ringed site, let
`\mathcal A`, `\mathcal A'`, and `\mathcal A''` be differential graded `\mathcal O`-algebras,
and let `\mathcal N` and `\mathcal N'` be differential graded
`(\mathcal A, \mathcal A')`- and `(\mathcal A', \mathcal A'')`-bimodules. If the canonical map
`\mathcal N \otimes_{\mathcal A'}^{\mathbf L} \mathcal N' \to
  \mathcal N \otimes_{\mathcal A'} \mathcal N'`
is a quasi-isomorphism, encoded by `quasiIsoAA''` and `hCanonical`, then the derived internal-Hom
from the underived tensor product is canonically isomorphic, as a functor
`D(\mathcal A'', \mathrm d) ⥤ D(\mathcal A, \mathrm d)`, to the iterated derived internal-Hom
`R\mathcal H\!\mathit{om}_{\mathcal A'}(\mathcal N,
  R\mathcal H\!\mathit{om}_{\mathcal A''}(\mathcal N', -))`. -/
@[stacks 0FTV]
noncomputable def derivedInternalHomTensorComparisonIsoOfQuasiIso
    (leftDerivedTensorAA' : DGBimodAA' ⥤ (DerivedDGModA ⥤ DerivedDGModA'))
    (leftDerivedTensorA'A'' : DGBimodA'A'' ⥤ (DerivedDGModA' ⥤ DerivedDGModA''))
    (leftDerivedTensorAA'' : DGBimodAA'' ⥤ (DerivedDGModA ⥤ DerivedDGModA''))
    (derivedInternalHomAA' : DGBimodAA' ⥤ (DerivedDGModA' ⥤ DerivedDGModA))
    (derivedInternalHomA'A'' : DGBimodA'A'' ⥤ (DerivedDGModA'' ⥤ DerivedDGModA'))
    (derivedInternalHomAA'' : DGBimodAA'' ⥤ (DerivedDGModA'' ⥤ DerivedDGModA))
    (quasiIsoAA'' : MorphismProperty DGBimodAA'')
    (hLeftDerivedTensorAA'' : quasiIsoAA''.IsInvertedBy leftDerivedTensorAA'')
    (N : DGBimodAA') (N' : DGBimodA'A'')
    {derivedTensorNN' underivedTensorNN' : DGBimodAA''}
    (canonicalTensorComparison : derivedTensorNN' ⟶ underivedTensorNN')
    (hCanonical : quasiIsoAA'' canonicalTensorComparison)
    (derivedTensorAssociator :
      leftDerivedTensorAA'.obj N ⋙ leftDerivedTensorA'A''.obj N' ≅
        leftDerivedTensorAA''.obj derivedTensorNN')
    (hAdjN : leftDerivedTensorAA'.obj N ⊣ derivedInternalHomAA'.obj N)
    (hAdjN' : leftDerivedTensorA'A''.obj N' ⊣ derivedInternalHomA'A''.obj N')
    (hAdjTensor :
      leftDerivedTensorAA''.obj underivedTensorNN' ⊣
        derivedInternalHomAA''.obj underivedTensorNN') :
    derivedInternalHomAA''.obj underivedTensorNN' ≅
      derivedInternalHomA'A''.obj N' ⋙ derivedInternalHomAA'.obj N :=
  letI : IsIso (leftDerivedTensorAA''.map canonicalTensorComparison) :=
    hLeftDerivedTensorAA'' canonicalTensorComparison hCanonical
  letI :
      IsIso
        (derivedTensorAssociator.hom ≫
          leftDerivedTensorAA''.map canonicalTensorComparison) := inferInstance
  let tensorComparisonIso :
      leftDerivedTensorAA'.obj N ⋙ leftDerivedTensorA'A''.obj N' ≅
        leftDerivedTensorAA''.obj underivedTensorNN' :=
    asIso (derivedTensorAssociator.hom ≫ leftDerivedTensorAA''.map canonicalTensorComparison)
  hAdjTensor.rightAdjointUniq
    ((hAdjN.comp hAdjN').ofNatIsoLeft tensorComparisonIso)

/-- The forward natural transformation of
`derivedInternalHomTensorComparisonIsoOfQuasiIso` is pointwise invertible. -/
@[stacks 0FTV]
theorem isIso_derivedInternalHomTensorComparisonIsoOfQuasiIso_hom
    (leftDerivedTensorAA' : DGBimodAA' ⥤ (DerivedDGModA ⥤ DerivedDGModA'))
    (leftDerivedTensorA'A'' : DGBimodA'A'' ⥤ (DerivedDGModA' ⥤ DerivedDGModA''))
    (leftDerivedTensorAA'' : DGBimodAA'' ⥤ (DerivedDGModA ⥤ DerivedDGModA''))
    (derivedInternalHomAA' : DGBimodAA' ⥤ (DerivedDGModA' ⥤ DerivedDGModA))
    (derivedInternalHomA'A'' : DGBimodA'A'' ⥤ (DerivedDGModA'' ⥤ DerivedDGModA'))
    (derivedInternalHomAA'' : DGBimodAA'' ⥤ (DerivedDGModA'' ⥤ DerivedDGModA))
    (quasiIsoAA'' : MorphismProperty DGBimodAA'')
    (hLeftDerivedTensorAA'' : quasiIsoAA''.IsInvertedBy leftDerivedTensorAA'')
    (N : DGBimodAA') (N' : DGBimodA'A'')
    {derivedTensorNN' underivedTensorNN' : DGBimodAA''}
    (canonicalTensorComparison : derivedTensorNN' ⟶ underivedTensorNN')
    (hCanonical : quasiIsoAA'' canonicalTensorComparison)
    (derivedTensorAssociator :
      leftDerivedTensorAA'.obj N ⋙ leftDerivedTensorA'A''.obj N' ≅
        leftDerivedTensorAA''.obj derivedTensorNN')
    (hAdjN : leftDerivedTensorAA'.obj N ⊣ derivedInternalHomAA'.obj N)
    (hAdjN' : leftDerivedTensorA'A''.obj N' ⊣ derivedInternalHomA'A''.obj N')
    (hAdjTensor :
      leftDerivedTensorAA''.obj underivedTensorNN' ⊣
        derivedInternalHomAA''.obj underivedTensorNN') :
    IsIso
      ((derivedInternalHomTensorComparisonIsoOfQuasiIso
        leftDerivedTensorAA'
        leftDerivedTensorA'A''
        leftDerivedTensorAA''
        derivedInternalHomAA'
        derivedInternalHomA'A''
        derivedInternalHomAA''
        quasiIsoAA''
        hLeftDerivedTensorAA''
        N
        N'
        canonicalTensorComparison
        hCanonical
        derivedTensorAssociator
        hAdjN
        hAdjN'
        hAdjTensor).hom) := sorry

end

end DifferentialGradedModule
