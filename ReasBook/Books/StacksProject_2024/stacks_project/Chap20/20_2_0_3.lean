import Mathlib.Tactic.Recall
import StacksProject_2024.Chap21.Lemma_21_10_5
import StacksProject_2024.Chap21.SiteAbelianDerived

open CategoryTheory Opposite Limits

universe u

namespace CategoryTheory
namespace Sheaf

noncomputable section

/-
Domain-style sampling for 20.2.0.3:
- primary domain: sheaf cohomology on a site, computed from injective resolutions by taking
  sections over a fixed object;
- sampled owner declarations:
  `CategoryTheory.Sheaf.H'`,
  `CategoryTheory.Sheaf.cohomologyPresheaf`,
  `CategoryTheory.sheafSections`,
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj`;
- best owner abstraction: the generic injective-resolution computation
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj`, specialized to the sections functor
  `(sheafSections J AddCommGrpCat).obj (op X)`;
- primitive data: a site `(C, J)`, an abelian sheaf `F`, an object `X : C`, an index `i : ℕ`,
  and a chosen injective resolution `I : InjectiveResolution F`;
- derived API: the source-facing identification of `H^i(X, F)` with the degree-`i` homology of
  the sections complex `Γ(X, I^•)`.

Source/core/bridge triage:
- `source-facing`: the Stacks computation of sheaf cohomology over a fixed object by the sections
  complex of an injective resolution;
- `core/canonical`: `CategoryTheory.InjectiveResolution.isoRightDerivedObj`;
- `bridge/view`: the specialization from the generic right-derived owner to the sheaf-cohomology
  owner `H'`.

The public API keeps the source-facing propositional `IsIsomorphic` theorem while deriving the
sections-complex comparison directly from `CategoryTheory.InjectiveResolution.isoRightDerivedObj`.
-/

/-
20.2.0.3: for an injective resolution `I^•` of an abelian sheaf `F`, the sheaf cohomology
`H^i(X, F)` is canonically identified with the `i`-th homology of the sections complex
`Γ(X, I^•)`. This is the objectwise specialization of
`CategoryTheory.InjectiveResolution.isoRightDerivedObj`.
-/
recall CategoryTheory.InjectiveResolution.isoRightDerivedObj

/-- Helper for 20.2.0.3: the right derived functor of `sheafToPresheaf J AddCommGrpCat`
is canonically identified with `Sheaf.cohomologyPresheafFunctor J i`. -/
@[stacks 0714]
private theorem abelianSheafInclusion_rightDerived_is_cohomologyPresheafFunctor_local
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{u})] (i : ℕ) :
    IsIsomorphic
      ((sheafToPresheaf J AddCommGrpCat.{u}).rightDerived i)
      (Sheaf.cohomologyPresheafFunctor J i :
        Sheaf J AddCommGrpCat.{u} ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{u}) := by
  -- Route correction: reuse the canonical Chapter 21 owner theorem instead of rebuilding the
  -- functor-level right-derived/cohomology-presheaf comparison locally.
  simpa using Sheaf.abelianSheafInclusion_rightDerived_is_cohomologyPresheafFunctor J i

/-- 20.2.0.3: for an injective resolution `I^•` of an abelian sheaf `F`, the sheaf cohomology
`H^i(X, F)` is canonically identified with the `i`-th homology of the sections complex
`Γ(X, I^•)`. -/
@[stacks 0714]
theorem cohomologyAtObject_isomorphic_to_homology_sections_of_injectiveResolution
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{u})]
    {X : C} {F : Sheaf J AddCommGrpCat.{u}} (I : InjectiveResolution F) (i : ℕ) :
    IsIsomorphic
      (F.H' i X)
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) i).obj
        ((((sheafSections J AddCommGrpCat.{u}).obj (op X)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)) := by
  rcases abelianSheafInclusion_rightDerived_is_cohomologyPresheafFunctor_local J i with ⟨e⟩
  let evalX := (_root_.CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)
  let eH' :
      F.H' i X ≅
        ((((sheafToPresheaf J AddCommGrpCat.{u}).rightDerived i).obj F).obj (op X)) := by
    simpa [Sheaf.H'] using (evalX.mapIso (e.app F)).symm
  refine ⟨eH' ≪≫ ?_⟩
  simpa [siteAbelianSectionsFunctor] using
    rightDerivedInclusion_app_obj_iso_homology_sections_complex J I X i

end
end Sheaf
end CategoryTheory
