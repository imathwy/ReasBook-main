import Mathlib

open CategoryTheory Opposite TopCat TopologicalSpace

noncomputable section

universe u

namespace TopCat.Presheaf

/-
Domain-style sampling for Lemma 6.14.2:
- primary domain: change of rings for presheaves of modules and stalkwise scalar extension on a
  topological space;
- sampled owner API:
  `PresheafOfModules.pullback`,
  `PresheafOfModules.restrictScalars`,
  `PresheafOfModules.pullbackPushforwardAdjunction`,
  `ModuleCat.extendRestrictScalarsAdj`;
- best owner abstraction: presheaf-level change of rings along the canonical underlying
  ring-presheaf morphism `Functor.whiskerRight p (forget₂ CommRingCat RingCat)`;
- source/core/bridge triage:
  `source-facing`: the stalkwise base-change comparison map and its induced isomorphism;
  `core/canonical`: the change-of-rings adjunction for `PresheafOfModules` and the
    `extendScalars ⊣ restrictScalars` adjunction on stalk modules;
  `bridge/view`: forgetting commutativity from `CommRingCat` to `RingCat`.

Primitive data are only the morphism `p : 𝒪 ⟶ 𝒪'`, the `𝒪`-module presheaf `ℱ`, and the point
`x`. The underlying ring-presheaf morphism is derived support, so this file should reuse the
canonical whiskered morphism directly instead of keeping a renamed shell for it.
-/

/-- The underlying presheaf map into a restricted-scalars target. -/
private noncomputable abbrev underlyingPresheafMapToRestricted
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    {ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)}
    {𝒢 : PresheafOfModules (𝒪' ⋙ forget₂ CommRingCat RingCat)}
    (φ : ℱ ⟶
      (PresheafOfModules.restrictScalars
        (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
            (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj 𝒢) :
    ℱ.presheaf ⟶ 𝒢.presheaf :=
  show ℱ.presheaf ⟶ 𝒢.presheaf from
    (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).map φ

/-- The underlying stalk map into a restricted-scalars target. -/
private noncomputable abbrev stalkUnderlyingMapToRestricted
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    {ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)}
    {𝒢 : PresheafOfModules (𝒪' ⋙ forget₂ CommRingCat RingCat)}
    (φ : ℱ ⟶
      (PresheafOfModules.restrictScalars
        (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
            (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj 𝒢) (x : X) :
    (stalkFunctor Ab x).obj ℱ.presheaf ⟶ (stalkFunctor Ab x).obj 𝒢.presheaf :=
  (stalkFunctor Ab x).map (underlyingPresheafMapToRestricted p φ)

/-- Semilinearity of the stalk map into a restricted-scalars target. -/
-- Proof sketch: the stalk map comes from a morphism of presheaf modules, so it is linear after
-- restricting scalars along the induced ring map on stalks.
private theorem stalkUnderlyingMapToRestricted_map_smul
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    {ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)}
    {𝒢 : PresheafOfModules (𝒪' ⋙ forget₂ CommRingCat RingCat)}
    (φ : ℱ ⟶
      (PresheafOfModules.restrictScalars
        (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
            (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj 𝒢) (x : X) :
    ∀ (r : 𝒪.stalk x) (m : ↑(stalk ℱ.presheaf x)),
      (show ↑(stalk 𝒢.presheaf x) from
        stalkUnderlyingMapToRestricted p φ x (r • m)) =
        (show 𝒪'.stalk x from ((stalkFunctor CommRingCat x).map p) r) •
          (show ↑(stalk 𝒢.presheaf x) from
            stalkUnderlyingMapToRestricted p φ x m) := sorry

/-- The stalk map into a restricted-scalars target induced by a morphism of presheaf modules. -/
private noncomputable def stalkModuleMapToRestrict
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    {ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)}
    {𝒢 : PresheafOfModules (𝒪' ⋙ forget₂ CommRingCat RingCat)}
    (φ : ℱ ⟶
      (PresheafOfModules.restrictScalars
        (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
            (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj 𝒢) (x : X) :
    ModuleCat.of (𝒪.stalk x) ↑(stalk ℱ.presheaf x) ⟶
      (ModuleCat.restrictScalars (((stalkFunctor CommRingCat x).map p).hom)).obj
        (ModuleCat.of (𝒪'.stalk x) ↑(stalk 𝒢.presheaf x)) :=
  let restrictedTarget :
      ModuleCat (𝒪.stalk x) :=
    (ModuleCat.restrictScalars (((stalkFunctor CommRingCat x).map p).hom)).obj
      (ModuleCat.of (𝒪'.stalk x) ↑(stalk 𝒢.presheaf x))
  let restrictedHom :
      ModuleCat.of (𝒪.stalk x) ↑(stalk ℱ.presheaf x) →ₗ[𝒪.stalk x]
        restrictedTarget :=
    { toFun := stalkUnderlyingMapToRestricted p φ x
      map_add' := fun m n ↦ by
        simpa using (stalkUnderlyingMapToRestricted p φ x).hom.map_add m n
      map_smul' := stalkUnderlyingMapToRestricted_map_smul p φ x }
  show ModuleCat.of (𝒪.stalk x) ↑(stalk ℱ.presheaf x) ⟶ restrictedTarget from
    ConcreteCategory.ofHom restrictedHom

/-- The canonical comparison from the extended-scalar stalk `ℱ_x ⊗[𝒪_x] 𝒪'_x` to the stalk of
the canonically pulled back presheaf. -/
noncomputable def stalkBaseChangeComparison
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    (ModuleCat.extendScalars (((stalkFunctor CommRingCat x).map p).hom)).obj
      (ModuleCat.of (𝒪.stalk x) ↑(stalk ℱ.presheaf x)) ⟶
        ModuleCat.of (𝒪'.stalk x)
          ↑(stalk
            ((PresheafOfModules.pullback
              (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                  (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj ℱ).presheaf x) :=
  ((ModuleCat.extendRestrictScalarsAdj (((stalkFunctor CommRingCat x).map p).hom)).homEquiv
      _ _).symm
    (stalkModuleMapToRestrict p
      (show ℱ ⟶
          (PresheafOfModules.restrictScalars
            (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj
            ((PresheafOfModules.pullback
              (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                  (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj ℱ) from
        (PresheafOfModules.pullbackPushforwardAdjunction
          (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
              (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
            Functor.whiskerRight p (forget₂ CommRingCat RingCat))).unit.app ℱ) x)

-- Proof sketch: the unit of the presheaf-level change-of-rings adjunction induces the canonical
-- map on stalks, and filtered colimits commute with extension of scalars.
/-- Lemma 6.14.2 (Tag 007K): for a morphism `p : 𝒪 ⟶ 𝒪'` of presheaves of commutative rings on
`X`, an `𝒪`-module presheaf `ℱ`, and `x : X`, the canonical comparison
`ℱ_x ⊗[𝒪_x] 𝒪'_x ⟶ (ℱ ⊗_{p, 𝒪} 𝒪')_x` is an isomorphism. -/
instance stalkBaseChangeComparison_isIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    IsIso (stalkBaseChangeComparison p ℱ x) := sorry

end TopCat.Presheaf
