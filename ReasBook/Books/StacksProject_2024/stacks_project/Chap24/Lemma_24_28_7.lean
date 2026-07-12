import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe uA vA uA' vA' uA'' vA'' uN vN uN' vN' uNN vNN

namespace DifferentialGradedModule

section

variable {DerivedDGModA : Type uA} [Category.{vA} DerivedDGModA]
variable {DerivedDGModA' : Type uA'} [Category.{vA'} DerivedDGModA']
variable {DerivedDGModA'' : Type uA''} [Category.{vA''} DerivedDGModA'']
variable {DGBimodAA' : Type uN} [Category.{vN} DGBimodAA']
variable {DGBimodA'A'' : Type uN'} [Category.{vN'} DGBimodA'A'']
variable {DGBimodAA'' : Type uNN} [Category.{vNN} DGBimodAA'']

-- Semantic search note: `lean_leansearch` surfaced the generic derived-functor comparison
-- owners `CategoryTheory.Functor.leftDerivedNatIso` and `CategoryTheory.Functor.associator`.
-- Nearby Chapter 24 tensor files use abstract fixed-right-factor derived tensor functors, so this
-- statement keeps the source bimodules and the composite bimodule comparison explicit at that
-- layer.

/-- Lemma 24.28.7: let `(\mathcal C, \mathcal O)` be a ringed site, let
`\mathcal A`, `\mathcal A'`, and `\mathcal A''` be differential graded
`\mathcal O`-algebras, and let `\mathcal N` and `\mathcal N'` be differential graded
`(\mathcal A, \mathcal A')`- and `(\mathcal A', \mathcal A'')`-bimodules. If the canonical
comparison
`\mathcal N \otimes_{\mathcal A'}^{\mathbf L} \mathcal N' \to
  \mathcal N \otimes_{\mathcal A'} \mathcal N'`
is a quasi-isomorphism, encoded here by the morphism property `quasiIsoAA''` and the hypothesis
that the composite right-factor derived tensor functor inverts it, then the standard
associativity comparison from
`(- \otimes_{\mathcal A}^{\mathbf L} \mathcal N) \otimes_{\mathcal A'}^{\mathbf L}
  \mathcal N'`
to
`- \otimes_{\mathcal A}^{\mathbf L}
  (\mathcal N \otimes_{\mathcal A'} \mathcal N')`
is an isomorphism of functors `D(\mathcal A, d) ⥤ D(\mathcal A'', d)`. -/
@[stacks 0FTL]
theorem isIso_leftDerivedTensor_assocComparison_of_quasiIso_bimoduleTensorComparison
    (leftDerivedTensorAA' : DGBimodAA' ⥤ (DerivedDGModA ⥤ DerivedDGModA'))
    (leftDerivedTensorA'A'' : DGBimodA'A'' ⥤ (DerivedDGModA' ⥤ DerivedDGModA''))
    (leftDerivedTensorAA'' : DGBimodAA'' ⥤ (DerivedDGModA ⥤ DerivedDGModA''))
    (quasiIsoAA'' : MorphismProperty DGBimodAA'')
    (hLeftDerivedTensorAA'' : quasiIsoAA''.IsInvertedBy leftDerivedTensorAA'')
    (N : DGBimodAA') (N' : DGBimodA'A'')
    {derivedTensorNN' underivedTensorNN' : DGBimodAA''}
    (canonicalTensorComparison : derivedTensorNN' ⟶ underivedTensorNN')
    (hCanonical : quasiIsoAA'' canonicalTensorComparison)
    (derivedTensorAssociator :
      leftDerivedTensorAA'.obj N ⋙ leftDerivedTensorA'A''.obj N' ≅
        leftDerivedTensorAA''.obj derivedTensorNN') :
    IsIso
      (derivedTensorAssociator.hom ≫
        leftDerivedTensorAA''.map canonicalTensorComparison) := sorry

end

end DifferentialGradedModule
