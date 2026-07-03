import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap18.Lemma_18_33_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v

-- Proof sketch: specialize Lemma `18.33.5` to the localization morphism of sites
-- `Over.forget U : Over U ⥤ C`. Its inverse-image on sheaves is the canonical localization
-- functor `J.overPullback`, so the pulled-back sheaf `(\Omega_{\mathcal O_2/\mathcal O_1}).over U`
-- is identified with the sheaf of relative differentials of the localized morphism
-- `\mathcal O_1|_U ⟶ \mathcal O_2|_U`; the compatibility with universal derivations is inherited
-- from the general inverse-image statement.
/-- Lemma 18.33.6: for any object `U` of a site `(\\mathcal C, J)`, the localization of the sheaf
of relative differentials `\Omega_{\mathcal O_2/\mathcal O_1}` to the slice site
`(\mathcal C/U, J.over U)` is canonically isomorphic to the sheaf of relative differentials of the
localized morphism `\mathcal O_1|_U \to \mathcal O_2|_U`, compatibly with universal
derivations. -/
theorem site_relative_differentials_over_has_universal_property
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (O₁ O₂ : Sheaf J CommRingCat.{max u v}) (φ : O₁ ⟶ O₂) (U : C) :
    IsIsomorphic
      ((SheafOfModules.toSheaf ((ringSheaf J O₂).over U)).obj
        ((Ω(φ)).over U))
      ((SheafOfModules.toSheaf (ringSheaf (J.over U) (O₂.over U))).obj
        (Ω(((J.overPullback CommRingCat.{max u v} U).map φ)))) :=
  sorry
