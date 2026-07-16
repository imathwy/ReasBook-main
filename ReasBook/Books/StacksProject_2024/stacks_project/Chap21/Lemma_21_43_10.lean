import StacksProject_2024.stacks_project.Chap21.Definition_21_43_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Opposite
open CategoryTheory.ObjectProperty

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory.ModulesOnCategory

section

/-
Domain-style sampling for Lemma 21.43.10:
- primary domain: object properties on derived categories and their canonical full subcategories,
  transported along a functor;
- sampled owner declarations:
  `CategoryTheory.ModulesOnCategory.isQuasiCoherent`,
  `CategoryTheory.ModulesOnCategory.QC`,
  `CategoryTheory.ObjectProperty.inverseImage`,
  `CategoryTheory.ObjectProperty.lift`;
- best owner abstraction:
  `source-facing`: the Section `21.43` owners `QC(𝒪)` and `QC(𝒪')`;
  `core/canonical`: the underlying `ObjectProperty` owners cut out by `isQuasiCoherent`, together
    with `inverseImage` and `lift`;
  `bridge/view`: the landing hypothesis `hLg`, which transports the source comparison-map
    isomorphisms along `leftDerivedPullback`.
- primitive data: `RGamma`, `RGamma'`, the restriction functors, the comparison transformations,
  and `leftDerivedPullback`;
- derived API: the owner-level landing statement
  `SrcQCP ≤ inverseImage TgtQCP leftDerivedPullback` together with its objectwise membership
  companion. Any restricted full-subcategory functor belongs in a later file once the landing
  theorem is available as proof rather than proof debt.

The restricted pullback is therefore expressed directly through the owner-level `QC` and
`ObjectProperty` APIs, rather than by repeating the defining base-change language in a local
wrapper name or by expanding the underlying full-subcategory machinery. -/

variable {C : Type u} [Category C]
variable {C' : Type u} [Category C']
variable {D : Type v} [Category D]
variable {D' : Type v} [Category D']
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}
variable {𝒪' : C'ᵒᵖ ⥤ CommRingCat.{u}}
variable {u : C' ⥤ C}
variable {RGamma : ∀ U : C, D ⥤ DerivedCategory (ModuleCat (𝒪.obj (op U)))}
variable {RGamma' : ∀ U' : C', D' ⥤ DerivedCategory (ModuleCat (𝒪'.obj (op U')))}
variable
  {derivedRestrict :
    ∀ {U V : C},
      (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒪.obj (op U)))}
variable
  {derivedRestrict' :
    ∀ {U' V' : C'},
      (U' ⟶ V') →
      DerivedCategory (ModuleCat (𝒪'.obj (op V'))) ⥤
        DerivedCategory (ModuleCat (𝒪'.obj (op U')))}
variable
  {comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U}
variable
  {comparison' :
    ∀ {U' V' : C'} (f' : U' ⟶ V'),
      RGamma' V' ⋙ derivedRestrict' f' ⟶ RGamma' U'}

local notation "SrcQCP" => isQuasiCoherent 𝒪 RGamma derivedRestrict comparison
local notation "TgtQCP" => isQuasiCoherent 𝒪' RGamma' derivedRestrict' comparison'

-- Proof sketch: for each arrow `f' : U' ⟶ V'`, the sectionwise base-change description of
-- `Lg^*` identifies the target comparison morphism for `leftDerivedPullback.obj K` with the
-- image of the source comparison morphism for `u.map f'`. Thus every isomorphism required by the
-- source `QC(𝒪)` condition transports to the corresponding isomorphism in the target.
/-- Lemma 21.43.10: if the comparison morphisms defining quasi-coherence on the target category
are obtained from those on the source category after applying the derived pullback `Lg^*`, then
`Lg^* : D(𝒪) ⥤ D(𝒪')` maps `QC(𝒪)` into `QC(𝒪')`. -/
@[stacks 0GZ1]
theorem qc_le_inverseImage_leftDerivedPullback
    (leftDerivedPullback : D ⥤ D')
    (hLg :
      ∀ {U' V' : C'} (f' : U' ⟶ V') {K : D},
        IsIso ((comparison (u.map f')).app K) →
          IsIso ((comparison' f').app (leftDerivedPullback.obj K))) :
    SrcQCP ≤ inverseImage TgtQCP leftDerivedPullback := sorry

/-- Objectwise companion to Lemma `21.43.10`: if `K ∈ QC(𝒪)`, then `Lg^* K ∈ QC(𝒪')` under the
same comparison-isomorphism transport hypothesis. -/
theorem leftDerivedPullback_obj_mem_qc_of_mem_qc
    (leftDerivedPullback : D ⥤ D')
    (hLg :
      ∀ {U' V' : C'} (f' : U' ⟶ V') {K : D},
        IsIso ((comparison (u.map f')).app K) →
          IsIso ((comparison' f').app (leftDerivedPullback.obj K)))
    {K : D} (hK : SrcQCP K) :
    TgtQCP (leftDerivedPullback.obj K) :=
  qc_le_inverseImage_leftDerivedPullback leftDerivedPullback hLg K hK

end

end CategoryTheory.ModulesOnCategory
