import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_6_20_1 (from Chap06) -/
open CategoryTheory TopCat TopologicalSpace
open PresheafOfModules

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) RingCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective RingCat.{u}]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

local notation "J" => Opens.grothendieckTopology X

/- Domain-style sampling for Lemma 6.20.1:
- primary domain: sheafification of presheaves of modules on a topological space;
- sampled owner API:
  `PresheafOfModules.sheafificationAdjunction`,
  `PresheafOfModules.sheafificationAdjunction_homEquiv_apply`,
  `PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app`;
- source/core/bridge triage:
  `source-facing`: the Stacks-style factorization through `ℱ ⟶ ℱ^#`;
  `core/canonical`: the module-sheafification adjunction and its underlying-additive compatibility;
  `bridge/view`: the existence-and-uniqueness reformulation derived from the owner Hom-equivalence.

Primitive data are the ring-presheaf map `toSheafify J 𝒪` and the canonical owner adjunction.
The additive compatibility statement is already an exact upstream owner theorem, and the
Hom-equivalence is derived API from that adjunction. The refined file therefore recalls the owner
theorem directly and keeps only the source-facing unique-factorization reformulation as a thin
bridge.
-/

/- Lemma 6.20.1: the compatibility of the sheafified `𝒪^#`-module with the sheafification of
the underlying additive presheaf is exactly the canonical compatibility theorem for the
module-sheafification adjunction. -/
recall PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app

section

variable (𝒪 : X.Presheaf RingCat.{u}) (ℱ : PresheafOfModules.{u} 𝒪)

-- Proof sketch: apply the adjunction
-- `PresheafOfModules.sheafification ⊣ SheafOfModules.forget ⋙ restrictScalars` along
-- `𝒪 ⟶ 𝒪^#`; the resulting hom-set bijection is equivalent to existence and uniqueness of the
-- factorization through the canonical map `ℱ ⟶ ℱ^#`.
/-- For a sheaf of `𝒪^#`-modules `𝒢`, every morphism of presheaves of `𝒪`-modules from `ℱ` to
the restriction of `𝒢` factors uniquely through the canonical map `ℱ ⟶ ℱ^#` by a morphism of
`𝒪^#`-modules. -/
theorem modulePresheafSheafification_factorsUniquely
    (𝒢 : SheafOfModules ((presheafToSheaf J RingCat.{u}).obj 𝒪))
    (η : ℱ ⟶
      (SheafOfModules.forget ((presheafToSheaf J RingCat.{u}).obj 𝒪) ⋙
        restrictScalars (toSheafify J 𝒪)).obj 𝒢) :
    ∃! γ : (sheafification (toSheafify J 𝒪)).obj ℱ ⟶ 𝒢,
      (sheafificationAdjunction (toSheafify J 𝒪)).unit.app ℱ ≫
          (SheafOfModules.forget ((presheafToSheaf J RingCat.{u}).obj 𝒪) ⋙
            restrictScalars (toSheafify J 𝒪)).map γ =
        η := by
  let e := (sheafificationAdjunction (toSheafify J 𝒪)).homEquiv ℱ 𝒢
  refine ⟨e.symm η, ?_, ?_⟩
  · -- The candidate lift is the inverse image of `η` under the adjunction equivalence.
    change e (e.symm η) = η
    exact Equiv.apply_symm_apply e η
  · intro γ hγ
    -- Translate the displayed factorization equation back through the adjunction unit formula.
    apply e.injective
    have hγη : e γ = η := by
      simpa [Adjunction.homEquiv_unit] using hγ
    rw [hγη]
    exact (Equiv.apply_symm_apply e η).symm

end

end

/-! ### Lemma_6_20_2 (from Chap06) -/
open CategoryTheory TopologicalSpace

noncomputable section

universe u

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪₁ 𝒪₂ : TopCat.Sheaf RingCat.{u} X}
variable (p : 𝒪₁ ⟶ 𝒪₂) (𝒢 : SheafOfModules 𝒪₁) (ℱ : SheafOfModules 𝒪₂)

local notation "J" => Opens.grothendieckTopology X

private abbrev ringSheafHomOverId :
    𝒪₁ ⟶ ((𝟭 (Opens X)).sheafPushforwardContinuous RingCat.{u} J J).obj 𝒪₂ :=
  p

/- Domain-style sampling for Lemma 6.20.2:
- primary domain: change of rings for sheaves of modules on one topological space;
- sampled owner declarations:
  `SheafOfModules.restrictScalars`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  the presheaf analogue `PresheafOfModules.pullbackPushforwardAdjunction`,
  `SheafOfModules.pullback`;
- best owner abstraction: the canonical adjunction owner
  `SheafOfModules.pullbackPushforwardAdjunction`;
- primitive data: the ring-sheaf morphism `p : 𝒪₁ ⟶ 𝒪₂` and the module sheaves `𝒢`, `ℱ`;
- derived API: the induced same-site Hom-set equivalence specialized from `.homEquiv`.

Source/core/bridge triage:
- `source-facing`: the Stacks-project Hom-bijection for change of rings on one space;
- `core/canonical`: `SheafOfModules.pullbackPushforwardAdjunction`;
- `bridge/view`: the identity-on-opens recasting `ringSheafHomOverId p`, kept private so no
  parallel public owner is introduced. -/

/- Lemma 6.20.2, owner form: for sheaves of modules on a topological space `X`, extension of
scalars along `p : 𝒪₁ ⟶ 𝒪₂` is left adjoint to the same-site pushforward functor, i.e. to
restriction of scalars along `p`. -/
recall SheafOfModules.pullbackPushforwardAdjunction

/- Lemma 6.20.2 companion: the Stacks-project Hom-set bijection is the specialized same-site
adjunction equivalence coming from
`SheafOfModules.pullbackPushforwardAdjunction (ringSheafHomOverId p)`. -/
#check
  (((SheafOfModules.pullbackPushforwardAdjunction (ringSheafHomOverId p)).homEquiv 𝒢 ℱ).symm :
    (𝒢 ⟶ (SheafOfModules.restrictScalars p).obj ℱ) ≃
      ((SheafOfModules.pullback (ringSheafHomOverId p)).obj 𝒢 ⟶ ℱ))

/-! ### Lemma_6_20_3 (from Chap06) -/
open CategoryTheory TopCat TopologicalSpace
open TopCat.Presheaf

noncomputable section

universe u

section

variable {X : TopCat.{u}} {𝒪 𝒪' : X.Sheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
variable
  (ℱ : SheafOfModules
    ((CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
      (CategoryTheory.forget₂ CommRingCat RingCat)).obj 𝒪))
variable (x : X)

local notation "J" => Opens.grothendieckTopology X

/- Domain-style sampling for Lemma 6.20.3:
- primary domain: stalkwise base change for pullback of sheaves of modules over sheaves of
  commutative rings on a topological space;
- sampled owner API:
  `TopCat.Presheaf.stalkBaseChangeComparison`,
  `TopCat.Presheaf.stalkBaseChangeComparison_isIso`,
  `SheafOfModules.pullbackIso`,
  `PresheafOfModules.sheafificationAdjunction`,
  `TopCat.Sheaf.stalkPullbackIso`;
- source/core/bridge triage:
  `source-facing`: the textbook stalkwise base-change isomorphism for sheaf pullback;
  `core/canonical`: the presheaf-level base-change owner
    `TopCat.Presheaf.stalkBaseChangeComparison`;
  `bridge/view`: the comparison from the sheaf pullback to the sheafification of the presheaf
    pullback, plus the resulting stalk comparison.

Primitive data are the morphism of sheaves of commutative rings `p : 𝒪 ⟶ 𝒪'` and the
`𝒪`-module sheaf `ℱ`. The presheaf-level stalk base-change map is already owned upstream, so this
file should reuse that owner directly and keep only the sheafification/pullback bridge local.
-/

/-- The underlying sheaf of rings obtained by forgetting commutativity. -/
private abbrev ringSheafOfComm (𝒪 : X.Sheaf CommRingCat.{u}) : X.Sheaf RingCat.{u} :=
  CategoryTheory.sheafCompose J (CategoryTheory.forget₂ CommRingCat RingCat) |>.obj 𝒪

/-- The forgotten ring-sheaf morphism induced by `p`, in the identity-on-opens shape consumed by
`SheafOfModules.pullback`. -/
private noncomputable abbrev ringSheafHomOverId :
    ringSheafOfComm 𝒪 ⟶
      (Functor.sheafPushforwardContinuous (𝟭 (Opens X)) RingCat J J).obj
        (ringSheafOfComm 𝒪') :=
  (CategoryTheory.sheafCompose J (CategoryTheory.forget₂ CommRingCat RingCat)).map p ≫
    (Functor.sheafPushforwardContinuousId RingCat J).inv.app (ringSheafOfComm 𝒪')

/-- The forgotten ring-presheaf morphism induced by `p`, in the shape consumed by
`PresheafOfModules.pullback`. -/
private abbrev ringPresheafHomOverId :
    (ringSheafOfComm 𝒪).obj ⟶ (𝟭 (Opens X)).op ⋙ (ringSheafOfComm 𝒪').obj :=
  show (ringSheafOfComm 𝒪).obj ⟶ (𝟭 (Opens X)).op ⋙ (ringSheafOfComm 𝒪').obj from
    Functor.whiskerRight p.hom (CategoryTheory.forget₂ CommRingCat RingCat)

local notation "sheafModulePullback" =>
  SheafOfModules.pullback (ringSheafHomOverId p)
local notation "presheafModulePullback" =>
  PresheafOfModules.pullback (ringPresheafHomOverId p)

private noncomputable abbrev presheafPullbackObj :=
  (presheafModulePullback).obj ℱ.val

private noncomputable abbrev commRingStalkToRingStalkIso (x : X) (𝒪 : X.Sheaf CommRingCat.{u}) :
    (forget₂ CommRingCat RingCat).obj (TopCat.Presheaf.stalk 𝒪.obj x) ≅
      (ringSheafOfComm 𝒪).presheaf.stalk x :=
  CategoryTheory.preservesColimitIso (forget₂ CommRingCat RingCat)
    ((OpenNhds.inclusion x).op ⋙ 𝒪.obj)

private local instance :
    Module ↑(TopCat.Presheaf.stalk 𝒪.obj x) ↑(TopCat.Presheaf.stalk ℱ.val.presheaf x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ℱ.val x

private noncomputable instance
    : Module ↑(TopCat.Presheaf.stalk 𝒪'.obj x)
        ↑(TopCat.Presheaf.stalk (presheafPullbackObj p ℱ).presheaf x) := by
  let restricted : ModuleCat ↑(TopCat.Presheaf.stalk 𝒪'.obj x) :=
    (ModuleCat.restrictScalars (commRingStalkToRingStalkIso x 𝒪').hom.hom).obj
      (ModuleCat.of ↑((ringSheafOfComm 𝒪').presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk (presheafPullbackObj p ℱ).presheaf x))
  change Module ↑(TopCat.Presheaf.stalk 𝒪'.obj x) ↑restricted
  infer_instance

private noncomputable instance
    : Module ↑(TopCat.Presheaf.stalk 𝒪'.obj x)
        ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x) := by
  let restricted : ModuleCat ↑(TopCat.Presheaf.stalk 𝒪'.obj x) :=
    (ModuleCat.restrictScalars (commRingStalkToRingStalkIso x 𝒪').hom.hom).obj
      (ModuleCat.of ↑((ringSheafOfComm 𝒪').presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x))
  change Module ↑(TopCat.Presheaf.stalk 𝒪'.obj x) ↑restricted
  infer_instance

/-- The stalk map induced by a morphism of module presheaves over a fixed ring sheaf. -/
private noncomputable abbrev stalkUnderlyingMap
    {R : X.Sheaf RingCat.{u}} {ℱ 𝒢 : PresheafOfModules R.obj} (x : X) (φ : ℱ ⟶ 𝒢) :
    TopCat.Presheaf.stalk ℱ.presheaf x ⟶ TopCat.Presheaf.stalk 𝒢.presheaf x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((PresheafOfModules.toPresheaf R.obj).map φ)

/-- The stalk map induced by a morphism of module presheaves is linear over the stalk ring. -/
private theorem stalkUnderlyingMap_smul
    {R : X.Sheaf RingCat.{u}} {ℱ 𝒢 : PresheafOfModules R.obj} (x : X) (φ : ℱ ⟶ 𝒢) :
    ∀ (r : R.presheaf.stalk x) (m : ↑(TopCat.Presheaf.stalk ℱ.presheaf x)),
      stalkUnderlyingMap x φ (r • m) = r • stalkUnderlyingMap x φ m := by
  -- Compare both stalk elements on a common neighborhood representative and use sectionwise
  -- linearity of `φ`.
  intro r m
  obtain ⟨U, hxU, rU, hr⟩ := TopCat.Presheaf.germ_exist R.presheaf x r
  obtain ⟨V, hxV, mV, hm⟩ := TopCat.Presheaf.germ_exist ℱ.presheaf x m
  let W : Opens X := U ⊓ V
  let iWU : W ⟶ U := homOfLE inf_le_left
  let iWV : W ⟶ V := homOfLE inf_le_right
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let rW : R.presheaf.obj (Opposite.op W) := R.presheaf.map iWU.op rU
  let mW : ℱ.presheaf.obj (Opposite.op W) := ℱ.presheaf.map iWV.op mV
  have hrW : R.presheaf.germ W x hxW rW = r := by
    simpa [W, iWU, hxW, rW] using (R.presheaf.germ_res_apply iWU x hxW rU).trans hr
  have hmW : TopCat.Presheaf.germ ℱ.presheaf W x hxW mW = m := by
    simpa [W, iWV, hxW, mW] using
      (TopCat.Presheaf.germ_res_apply ℱ.presheaf iWV x hxW mV).trans hm
  have hsmulW :
      TopCat.Presheaf.germ ℱ.presheaf W x hxW (rW • mW) = r • m := by
    calc
      TopCat.Presheaf.germ ℱ.presheaf W x hxW (rW • mW) =
          R.presheaf.germ W x hxW rW • TopCat.Presheaf.germ ℱ.presheaf W x hxW mW := by
            simpa using
              (PresheafOfModules.germ_ringCat_smul (R := R.obj) (M := ℱ) x W hxW rW mW)
      _ = r • m := by rw [hrW, hmW]
  have hmφW :
      (show ↑(TopCat.Presheaf.stalk 𝒢.presheaf x) from
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf R.obj).map φ)) m) =
        TopCat.Presheaf.germ 𝒢.presheaf W x hxW (φ.app (Opposite.op W) mW) := by
    rw [← hmW]
    simpa [W, hxW, mW] using
      (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW
        ((PresheafOfModules.toPresheaf R.obj).map φ) mW)
  calc
    stalkUnderlyingMap x φ (r • m) =
        TopCat.Presheaf.germ 𝒢.presheaf W x hxW (φ.app (Opposite.op W) (rW • mW)) := by
          rw [← hsmulW]
          simpa [W, hxW, rW, mW] using
            (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW
              ((PresheafOfModules.toPresheaf R.obj).map φ) (rW • mW))
    _ = TopCat.Presheaf.germ 𝒢.presheaf W x hxW (rW • φ.app (Opposite.op W) mW) := by
          congr 1
          exact (φ.app (Opposite.op W)).hom.map_smul rW mW
    _ = R.presheaf.germ W x hxW rW •
          TopCat.Presheaf.germ 𝒢.presheaf W x hxW (φ.app (Opposite.op W) mW) := by
          simpa using
            (PresheafOfModules.germ_ringCat_smul (R := R.obj) (M := 𝒢) x W hxW rW
              (φ.app (Opposite.op W) mW))
    _ = r • stalkUnderlyingMap x φ m := by
          rw [hrW]
          simpa [stalkUnderlyingMap] using (congrArg (fun z ↦ r • z) hmφW).symm

/-- The stalk map induced by a morphism of module presheaves, packaged as a module homomorphism. -/
private noncomputable def stalkModuleMap
    {R : X.Sheaf RingCat.{u}} {ℱ 𝒢 : PresheafOfModules R.obj} (x : X) (φ : ℱ ⟶ 𝒢) :
    ModuleCat.of (R.presheaf.stalk x) ↑(TopCat.Presheaf.stalk ℱ.presheaf x) ⟶
      ModuleCat.of (R.presheaf.stalk x) ↑(TopCat.Presheaf.stalk 𝒢.presheaf x) :=
  ModuleCat.ofHom
    { toFun := stalkUnderlyingMap x φ
      map_add' := by
        intro m n
        exact (stalkUnderlyingMap x φ).hom.map_add m n
      map_smul' := stalkUnderlyingMap_smul x φ }

/-- If the underlying additive stalk map is an isomorphism, then the corresponding packaged
module-valued stalk map is also an isomorphism. -/
private theorem stalkModuleMap_isIso
    {R : X.Sheaf RingCat.{u}} {ℱ 𝒢 : PresheafOfModules R.obj} (x : X) (φ : ℱ ⟶ 𝒢)
    [IsIso (stalkUnderlyingMap x φ)] :
    IsIso (stalkModuleMap x φ) := by
  let F := forget₂ (ModuleCat (R.presheaf.stalk x)) AddCommGrpCat
  haveI : IsIso (F.map (stalkModuleMap x φ)) := by
    change IsIso (stalkUnderlyingMap x φ)
    infer_instance
  exact isIso_of_reflects_iso (stalkModuleMap x φ) F

/-- The stalk map on the unit of module sheafification for the presheaf pullback. -/
private noncomputable def presheafPullbackSheafificationUnitStalkHom :
    ModuleCat.of ((ringSheafOfComm 𝒪').presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk (presheafPullbackObj p ℱ).presheaf x) ⟶
      ModuleCat.of ((ringSheafOfComm 𝒪').presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk
          (((PresheafOfModules.sheafification (𝟙 (ringSheafOfComm 𝒪').obj)).obj
            (presheafPullbackObj p ℱ)).val.presheaf) x) := by
  simpa using
    stalkModuleMap x
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheafOfComm 𝒪').obj)).unit.app
        (presheafPullbackObj p ℱ))

private instance presheafPullbackSheafificationUnitStalkHom_isIso :
    IsIso (presheafPullbackSheafificationUnitStalkHom p ℱ x) := by
  let φ :=
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheafOfComm 𝒪').obj)).unit.app
      (presheafPullbackObj p ℱ))
  haveI : IsIso (stalkUnderlyingMap x φ) := by
    change IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (CategoryTheory.toSheafify J (presheafPullbackObj p ℱ).presheaf))
    simpa [φ, stalkUnderlyingMap] using
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
        (presheafPullbackObj p ℱ).presheaf)
  simpa [presheafPullbackSheafificationUnitStalkHom, φ] using stalkModuleMap_isIso x φ

/-- The stalk map on the canonical identification between sheaf pullback and sheafified presheaf
pullback. -/
private noncomputable def sheafPullbackIsoStalkHom :
    ModuleCat.of ((ringSheafOfComm 𝒪').presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x) ⟶
      ModuleCat.of ((ringSheafOfComm 𝒪').presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk
          (((PresheafOfModules.sheafification (𝟙 (ringSheafOfComm 𝒪').obj)).obj
            (presheafPullbackObj p ℱ)).val.presheaf) x) := by
  simpa using
    stalkModuleMap x (((SheafOfModules.pullbackIso
      (ringSheafHomOverId p)).app ℱ).hom.val)

private instance sheafPullbackIsoStalkHom_isIso :
    IsIso (sheafPullbackIsoStalkHom p ℱ x) := by
  -- First transport the owner isomorphism `SheafOfModules.pullbackIso` through the forgetful
  -- functors down to the stalk additive map, then repackage it as a module isomorphism.
  let e := ((SheafOfModules.pullbackIso (ringSheafHomOverId p)).app ℱ)
  let φ := e.hom.val
  haveI : IsIso e.hom := by
    infer_instance
  haveI : IsIso φ := by
    simpa [φ] using (Functor.map_isIso (SheafOfModules.forget _) e.hom)
  have hφ : IsIso (stalkUnderlyingMap x φ) := by
    simpa [stalkUnderlyingMap, φ] using
      (Functor.map_isIso
        (SheafOfModules.forget _ ⋙
          PresheafOfModules.toPresheaf (ringSheafOfComm 𝒪').obj ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
        e.hom)
  simpa [sheafPullbackIsoStalkHom, φ] using (stalkModuleMap_isIso x φ)

/-- The stalk isomorphism identifying the stalk of the underlying presheaf pullback with the stalk
of the sheaf pullback. This is the private comparison used in the sheaf-level base-change
statement. -/
private noncomputable abbrev sheafOfModules_pullbackPresheafStalkIso := by
  exact asIso (presheafPullbackSheafificationUnitStalkHom p ℱ x) ≪≫
    (asIso (sheafPullbackIsoStalkHom p ℱ x)).symm

-- TODO: compare the commutative-ring stalk action with the restricted ring-valued stalk action by
-- choosing common neighborhood representatives for the scalar germ and section germ.
private noncomputable def presheafPullbackStalkRestrictedHom :
    ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪'.obj) x)
        ↑(TopCat.Presheaf.stalk
          ((PresheafOfModules.pullback
            (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
            ℱ.val).presheaf x) ⟶
      (ModuleCat.restrictScalars ((commRingStalkToRingStalkIso x 𝒪').hom.hom)).obj
        (ModuleCat.of ↑((ringSheafOfComm 𝒪').presheaf.stalk x)
          ↑(TopCat.Presheaf.stalk ((presheafPullbackObj p ℱ).presheaf) x)) := sorry

private instance presheafPullbackStalkRestrictedHom_isIso :
    IsIso (presheafPullbackStalkRestrictedHom p ℱ x) := by
  -- TODO: prove the adapter is an isomorphism by packaging the identity linear equivalence once
  -- the scalar-transport lemma for the identity map is available.
  sorry

private noncomputable abbrev presheafPullbackStalkRestrictedIso :
    ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪'.obj) x)
        ↑(TopCat.Presheaf.stalk
          ((PresheafOfModules.pullback
            (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
            ℱ.val).presheaf x) ≅
      (ModuleCat.restrictScalars ((commRingStalkToRingStalkIso x 𝒪').hom.hom)).obj
        (ModuleCat.of ↑((ringSheafOfComm 𝒪').presheaf.stalk x)
          ↑(TopCat.Presheaf.stalk ((presheafPullbackObj p ℱ).presheaf) x)) :=
  asIso (presheafPullbackStalkRestrictedHom p ℱ x)

private noncomputable abbrev sheafPullbackStalkRestrictedIso :
    ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪'.obj) x)
        ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x) ≅
      (ModuleCat.restrictScalars ((commRingStalkToRingStalkIso x 𝒪').hom.hom)).obj
        (ModuleCat.of ↑((ringSheafOfComm 𝒪').presheaf.stalk x)
          ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x)) := by
  exact Iso.refl _

/-- The stalk of the presheaf pullback identifies canonically with the stalk of the sheaf pullback.
-/
private noncomputable abbrev pullbackStalkComparisonIso :
    ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪'.obj) x)
        ↑(TopCat.Presheaf.stalk
          ((PresheafOfModules.pullback
            (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
            ℱ.val).presheaf x) ≅
      ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪'.obj) x)
        ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x) := by
  letI :
      Module ↑(TopCat.Presheaf.stalk 𝒪'.obj x)
        ↑(TopCat.Presheaf.stalk
          ((PresheafOfModules.pullback
            (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
            ℱ.val).presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      ((PresheafOfModules.pullback
        (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
            (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
          Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
        ℱ.val) x
  have hsource :
      ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪'.obj) x)
          ↑(TopCat.Presheaf.stalk
            ((PresheafOfModules.pullback
              (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
                  (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
                Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
              ℱ.val).presheaf x) ≅
        (ModuleCat.restrictScalars ((commRingStalkToRingStalkIso x 𝒪').hom.hom)).obj
          (ModuleCat.of ↑((ringSheafOfComm 𝒪').presheaf.stalk x)
            ↑(TopCat.Presheaf.stalk (((presheafModulePullback).obj ℱ.val).presheaf) x)) := by
    simpa [ringPresheafHomOverId, ringSheafOfComm] using
      presheafPullbackStalkRestrictedIso p ℱ x
  exact
    hsource ≪≫
      (ModuleCat.restrictScalars ((commRingStalkToRingStalkIso x 𝒪').hom.hom)).mapIso
        (sheafOfModules_pullbackPresheafStalkIso p ℱ x) ≪≫
      (sheafPullbackStalkRestrictedIso p ℱ x).symm

/-- Lemma 6.20.3 (Tag 008B): for a morphism `p : 𝒪 ⟶ 𝒪'` of sheaves of commutative rings on `X`,
an `𝒪`-module sheaf `ℱ`, and `x : X`, the canonical base-change map on stalks
`ℱ_x ⊗[𝒪_x] 𝒪'_x ≅ (ℱ ⊗_𝒪 𝒪')_x` is an isomorphism. -/
noncomputable abbrev sheafOfModules_pullback_stalkIso :
      (ModuleCat.extendScalars (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p.hom).hom)).obj
      (ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪.obj) x) ↑(TopCat.Presheaf.stalk ℱ.val.presheaf x)) ≅
        ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪'.obj) x)
          ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x) := by
  exact
    (by
      letI :
          Module ↑(TopCat.Presheaf.stalk 𝒪'.obj x)
            ↑(TopCat.Presheaf.stalk
              ((PresheafOfModules.pullback
                (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
                    (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
                  Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
                ℱ.val).presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          ((PresheafOfModules.pullback
            (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
            ℱ.val) x
      simpa [ringPresheafHomOverId, ringSheafOfComm] using
        asIso (TopCat.Presheaf.stalkBaseChangeComparison p.hom ℱ.val x)) ≪≫
      pullbackStalkComparisonIso p ℱ x

end
