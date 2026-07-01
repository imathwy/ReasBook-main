import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe v u

variable {C : Type u} [Category.{v} C]
variable {𝒪 𝒪' : Cᵒᵖ ⥤ RingCat.{u}}
variable (p : 𝒪 ⟶ 𝒪') (X : Cᵒᵖ)
variable (𝒢 : PresheafOfModules 𝒪') (ℱ : PresheafOfModules 𝒪)

/- Domain-style sampling for Lemma 18.27.8:
- primary domain: change of rings for presheaves of modules, evaluated sectionwise;
- sampled owner declarations:
  `PresheafOfModules.restrictScalars`,
  `PresheafOfModules.evaluation`,
  `ModuleCat.restrictCoextendScalarsAdj`;
- best owner abstraction: the sectionwise canonical change-of-rings adjunction
  `ModuleCat.restrictCoextendScalarsAdj (p.app X).hom`;
- primitive data: the ring-presheaf morphism `p`, the section `X`, and the module presheaves
  `𝒢`, `ℱ`;
- derived API: the specialized Hom-set equivalence after evaluating at `X`.

Source/core/bridge triage:
- `source-facing`: the sectionwise change-of-rings Hom-bijection used in the internal-Hom
  construction;
- `core/canonical`: `ModuleCat.restrictCoextendScalarsAdj (p.app X).hom`;
- `bridge/view`: the typed specialization of `.homEquiv` to the `X`-sections of
  `PresheafOfModules.restrictScalars p`.

The previous file only wrapped this owner equivalence under a duplicate local name, so the refined
form keeps the canonical owner directly and exposes the textbook sectionwise statement only as its
specialized derived API.
-/

/- Lemma 18.27.8, owner form: for each `X`, the algebra controlling change of rings for
`\mathcal O`- and `\mathcal O'`-module sections is exactly the canonical adjunction
`ModuleCat.restrictCoextendScalarsAdj (p.app X).hom`. -/
recall ModuleCat.restrictCoextendScalarsAdj

/- Lemma 18.27.8 companion: after evaluating at `X`, the canonical adjunction above gives the
sectionwise Hom-set bijection
`Hom_{\mathcal O(X)}(\mathcal G(X), \mathcal F(X)) ≃
  Hom_{\mathcal O'(X)}(\mathcal G(X), \operatorname{Coext}(\mathcal F(X)))`,
with the source viewed via `PresheafOfModules.restrictScalars p`. -/
#check
  (((ModuleCat.restrictCoextendScalarsAdj (p.app X).hom).homEquiv (𝒢.obj X) (ℱ.obj X)) :
    (((PresheafOfModules.restrictScalars p).obj 𝒢).obj X ⟶ ℱ.obj X) ≃
      (𝒢.obj X ⟶ (ModuleCat.coextendScalars (p.app X).hom).obj (ℱ.obj X)))
