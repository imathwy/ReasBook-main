import Mathlib.Tactic.Recall
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u

/- Domain-style sampling for 21.2.0.3:
- primary domain: global sheaf cohomology on a site, computed from a chosen injective resolution
  by applying the global-sections functor;
- sampled owner API:
  `CategoryTheory.Sheaf.H`,
  `CategoryTheory.Sheaf.Γ`,
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj`;
- best owner abstraction: `CategoryTheory.Sheaf.H`;
- primitive data: a site `(C, J)`, an abelian sheaf `F`, a chosen injective resolution
  `I : InjectiveResolution F`, and a degree `i : ℕ`;
- derived API: the source-facing injective-resolution model given by the degree-`i` homology of
  the global-sections complex `Γ(C, I•)`.

Source/core/bridge triage:
- `source-facing`: the Stacks formula computing `H^i(C, F)` from global sections of an
  injective resolution;
- `core/canonical`: the global cohomology owner `CategoryTheory.Sheaf.H`;
- `bridge/view`: the specialization of
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj` to the global-sections functor
  `CategoryTheory.Sheaf.Γ`.

This item does not own new mathematical data beyond `CategoryTheory.Sheaf.H`. In the minimal
compiling closure of this file, the injective-resolution model is therefore kept only as the
named global-sections specialization of the generic right-derived comparison, while the main
entry is a direct recall of the canonical cohomology owner. -/

/-
21.2.0.3: global sheaf cohomology on a site is canonically owned by `CategoryTheory.Sheaf.H`.
The injective-resolution computation remains a companion bridge statement, not a second owner.
-/
recall CategoryTheory.Sheaf.H

namespace CategoryTheory
namespace Sheaf

private instance abelianPresheafLimit_additive {C : Type u} [Category.{u} C] :
    (lim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).Additive := by
  constructor
  intro F G f g
  apply limit.hom_ext
  intro j
  change limMap (f + g) ≫ limit.π G j = (limMap f + limMap g) ≫ limit.π G j
  rw [limMap_π, Preadditive.add_comp, limMap_π, limMap_π]
  simp

instance sheafGlobalSections_additive {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat.{u}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{u}] :
    (Γ J AddCommGrpCat.{u}).Additive := by
  exact Functor.additive_of_iso (ΓNatIsoLim J AddCommGrpCat.{u}).symm

section

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{u}]
variable [HasGlobalSectionsFunctor J AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{u})]
variable {F : Sheaf J AddCommGrpCat.{u}} (I : InjectiveResolution F) (i : ℕ)

local instance : HasWeakSheafify J AddCommGrpCat.{u} :=
  HasSheafify.isRightAdjoint

/-- 21.2.0.3, companion bridge on the right-derived global-sections owner: applying global
sections to a chosen injective resolution computes the corresponding degree-`i` right-derived
value by the degree-`i` homology of the global-sections complex. -/
@[stacks 071E]
noncomputable abbrev globalSectionsRightDerivedObjIsoHomologyOfInjectiveResolution :
    (((Γ J AddCommGrpCat.{u}).rightDerived i).obj F) ≅
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) i).obj
        (((Γ J AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)) := by
  exact I.isoRightDerivedObj (Γ J AddCommGrpCat.{u}) i

end

end Sheaf
end CategoryTheory
