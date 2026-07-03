import Mathlib
import StacksProject_2024.Chap17.Definition_17_28_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace
open PresheafOfModules.DifferentialsConstruction

noncomputable section

universe u

namespace TopCat.Sheaf

/- Domain-style sampling for Lemma 17.28.6:
- primary domain: inverse image compatibility for sheaves of relative differentials;
- sampled owner declarations:
  `TopCat.Sheaf.relativeDifferentials`,
  `TopCat.Sheaf.relativeDifferentials_def`,
  `TopCat.Sheaf.pullback`,
  `SheafOfModules.pullback`,
  `SheafOfModules.sheafificationCompPullback`;
- best owner abstraction: the source-facing owner `TopCat.Sheaf.relativeDifferentials`, with the
  inverse-image comparison expressed by the actual module pullback and the transported
  pulled-back owner over the raw `RingCat`-valued structure sheaf;
- primitive data: the owner `relativeDifferentials`, the actual pullback functor
  `SheafOfModules.pullback`, and the canonical restrict-scalars transport along
  `pullbackRingSheafIso`;
- derived API: the ring-sheaf comparison bridge `pullbackRingSheafIso`, the direct comparison
  isomorphism `inverseImage_relativeDifferentialsIso`, and its theorem-level `IsIsomorphic`
  companion.

Source/core/bridge triage:
- `core/canonical`: `TopCat.Sheaf.relativeDifferentials`;
- `bridge/view`: this lemma compares the actual inverse image of `Ω(φ)` with the same owner
  applied to the pulled-back morphism, then transported across the canonical ring-sheaf
  comparison;
- the public API should therefore expose that transport by a direct comparison isomorphism, rather
  than by a public `Classical.choice` witness extracted from an existence theorem. -/

-- Proof sketch: write `relativeDifferentials O₁ O₂ φ` as the sheafification of the
-- presheaf of relative differentials from Definition `17.28.3`, pull this presentation back along
-- `f^{-1}`, and use exactness of inverse image together with the objectwise identities
-- `f^{-1}(O₂[O₂]) = f^{-1}O₂[f^{-1}O₂]`,
-- `f^{-1}(O₂[O₂ \times O₂]) = f^{-1}O₂[f^{-1}O₂ \times f^{-1}O₂]`, and
-- `f^{-1}(O₂[O₁]) = f^{-1}O₂[f^{-1}O₁]`. The pulled-back universal derivation then represents
-- derivations for the pulled-back morphism, which is exactly the universal property of
-- `\Omega_{f^{-1}\mathcal O_2/f^{-1}\mathcal O_1}`.
private theorem pullbackRingSheaf_eq
    {X Y : TopCat.{u}} (f : Y ⟶ X)
    (O : X.Sheaf CommRingCat.{u}) :
    ringSheaf ((pullback CommRingCat.{u} f).obj O) =
      (pullback RingCat.{u} f).obj (ringSheaf O) := sorry

/-- The canonical ring-sheaf comparison between pulling back before or after forgetting
commutativity. -/
noncomputable def pullbackRingSheafIso
    {X Y : TopCat.{u}} (f : Y ⟶ X)
    (O : X.Sheaf CommRingCat.{u}) :
    ringSheaf ((pullback CommRingCat.{u} f).obj O) ≅
      (pullback RingCat.{u} f).obj (ringSheaf O) :=
  eqToIso (pullbackRingSheaf_eq f O)

private abbrev pulledBackRelativeDifferentialsPresentation
    {X Y : TopCat.{u}} (f : Y ⟶ X)
    {O₁ O₂ : X.Sheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂) :
    SheafOfModules ((pullback RingCat.{u} f).obj (ringSheaf O₂)) :=
  (PresheafOfModules.sheafification
      (𝟙 ((pullback RingCat.{u} f).obj (ringSheaf O₂)).obj)).obj
    ((PresheafOfModules.restrictScalars
        (pullbackRingSheafIso f O₂).inv.hom).obj
      (relativeDifferentials' ((pullback CommRingCat.{u} f).map φ).hom))

private theorem pulledBackRelativeDifferentialsPresheaf_eq
    {X Y : TopCat.{u}} (f : Y ⟶ X)
    {O₁ O₂ : X.Sheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂) :
    (PresheafOfModules.pullback
        ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂)).hom).obj
        (relativeDifferentials' φ.hom) =
      (PresheafOfModules.restrictScalars
          (pullbackRingSheafIso f O₂).inv.hom).obj
        (relativeDifferentials' ((pullback CommRingCat.{u} f).map φ).hom) := by
  sorry

private noncomputable abbrev pulledBackRelativeDifferentialsPresentation_hom
    {X Y : TopCat.{u}} (f : Y ⟶ X)
    {O₁ O₂ : X.Sheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂) :
    pulledBackRelativeDifferentialsPresentation f φ ⟶
      (SheafOfModules.restrictScalars (pullbackRingSheafIso f O₂).inv).obj
        Ω((pullback CommRingCat.{u} f).map φ) :=
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((pullback RingCat.{u} f).obj (ringSheaf O₂)).obj)).homEquiv
      ((PresheafOfModules.restrictScalars
          (pullbackRingSheafIso f O₂).inv.hom).obj
        (relativeDifferentials' ((pullback CommRingCat.{u} f).map φ).hom))
      ((SheafOfModules.restrictScalars (pullbackRingSheafIso f O₂).inv).obj
        Ω((pullback CommRingCat.{u} f).map φ))).symm
    ((PresheafOfModules.restrictScalars
        (pullbackRingSheafIso f O₂).inv.hom).map
      ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (ringSheaf ((pullback CommRingCat.{u} f).obj O₂)).obj)).unit.app
        (relativeDifferentials' ((pullback CommRingCat.{u} f).map φ).hom)))

private instance pulledBackRelativeDifferentialsPresentation_hom_isIso
    {X Y : TopCat.{u}} (f : Y ⟶ X)
    {O₁ O₂ : X.Sheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂) :
    IsIso (pulledBackRelativeDifferentialsPresentation_hom f φ) := by
  sorry

private noncomputable abbrev pulledBackRelativeDifferentialsPresentationIso
    {X Y : TopCat.{u}} (f : Y ⟶ X)
    {O₁ O₂ : X.Sheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂) :
    pulledBackRelativeDifferentialsPresentation f φ ≅
      (SheafOfModules.restrictScalars (pullbackRingSheafIso f O₂).inv).obj
        Ω((pullback CommRingCat.{u} f).map φ) :=
  asIso (pulledBackRelativeDifferentialsPresentation_hom f φ)

/-- The canonical inverse-image comparison for relative differentials. -/
noncomputable abbrev inverseImage_relativeDifferentialsIso
    {X Y : TopCat.{u}} (f : Y ⟶ X)
    {O₁ O₂ : X.Sheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂) :
    (SheafOfModules.pullback
        ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂))).obj
      Ω(φ) ≅
      (SheafOfModules.restrictScalars (pullbackRingSheafIso f O₂).inv).obj
        Ω((pullback CommRingCat.{u} f).map φ) :=
  (Functor.mapIso
      (SheafOfModules.pullback
        ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂)))
      (eqToIso (relativeDifferentials_def φ))) ≪≫
    (SheafOfModules.sheafificationCompPullback
      ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂))).app
      (relativeDifferentials' φ.hom) ≪≫
    (Functor.mapIso
      (PresheafOfModules.sheafification
        (𝟙 ((pullback RingCat.{u} f).obj (ringSheaf O₂)).obj))
      (eqToIso (pulledBackRelativeDifferentialsPresheaf_eq f φ))) ≪≫
    pulledBackRelativeDifferentialsPresentationIso f φ

/-- The inverse image of `Ω(φ)` is canonically identified with the relative differentials of the
pulled-back morphism, expressed over the canonical pulled-back `RingCat`-valued structure sheaf. -/
theorem inverseImage_relativeDifferentials_isIsomorphic
    {X Y : TopCat.{u}} (f : Y ⟶ X)
    {O₁ O₂ : X.Sheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂) :
    IsIsomorphic
      ((SheafOfModules.pullback
          ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂))).obj
        Ω(φ))
      ((SheafOfModules.restrictScalars (pullbackRingSheafIso f O₂).inv).obj
        Ω((pullback CommRingCat.{u} f).map φ)) := by
  exact ⟨inverseImage_relativeDifferentialsIso f φ⟩

end TopCat.Sheaf
