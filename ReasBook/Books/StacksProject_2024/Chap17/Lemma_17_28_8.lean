import Mathlib
import StacksProject_2024.Chap17.Definition_17_28_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace
open PresheafOfModules.DifferentialsConstruction
open RelativeDerivation
open scoped RelativeDerivation

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/- Domain-style sampling for Lemma 17.28.8:
- primary domain: functoriality of sheaves of relative differentials for a commutative square of
  sheaves of commutative rings on a fixed topological space;
- sampled owner declarations:
  `TopCat.Sheaf.relativeDifferentials`,
  `TopCat.Sheaf.relativeDifferentialDesc`,
  `SheafOfModules.restrictScalars`,
  `CategoryTheory.CommSq`;
- best owner abstraction: the source-facing sheaf owner `Ω(φ)`, with the canonical target
  `(SheafOfModules.restrictScalars (ringSheafMap β)).obj Ω(φ')`;
- primitive data: a commutative square `CommSq α φ φ' β` of sheaves of commutative rings;
- derived API: the induced comparison morphism on sheaves of relative differentials, together with
  its characterization on universal differentials `d(f)`.

Source/core/bridge triage:
- `source-facing`: the sheaf morphism
  `Ω(φ) ⟶ (SheafOfModules.restrictScalars (ringSheafMap β)).obj Ω(φ')`;
- `core/canonical`: `Ω(φ)`, `relativeDifferentialDesc`, `SheafOfModules.restrictScalars`, and
  `CommSq`;
- `bridge/view`: the objectwise Kähler map on `relativeDifferentials'`, used only internally to
  build the target derivation.

This file therefore keeps the presheaf comparison private and exposes only the sheaf-level map and
its source-facing characterization. -/

private abbrev presheafRestrictScalars
    {O O' : TopCat.Sheaf CommRingCat.{u} X} (α : O ⟶ O') :=
  PresheafOfModules.restrictScalars (ringSheafMap α).hom

private theorem relativeDifferentialsSquare_app
    {O₁ O₂ O₁' O₂' : TopCat.Sheaf CommRingCat.{u} X}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂')
    (sq : CommSq α φ φ' β)
    (U : (Opens X)ᵒᵖ) :
    α.hom.app U ≫ φ'.hom.app U = φ.hom.app U ≫ β.hom.app U := by
  simpa using congrArg (fun k ↦ k.hom.app U) sq.w

/-- The objectwise comparison map on relative differentials induced by a commutative square of
sheaves of commutative rings. -/
private abbrev relativeDifferentialsMapApp
    {O₁ O₂ O₁' O₂' : TopCat.Sheaf CommRingCat.{u} X}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂')
    (sq : CommSq α φ φ' β)
    (U : (Opens X)ᵒᵖ) :
    (relativeDifferentials' φ.hom).obj U ⟶
      ((presheafRestrictScalars β).obj (relativeDifferentials' φ'.hom)).obj U :=
  CommRingCat.KaehlerDifferential.map (relativeDifferentialsSquare_app φ φ' α β sq U)

private theorem relativeDifferentialsMapApp_naturality
    {O₁ O₂ O₁' O₂' : TopCat.Sheaf CommRingCat.{u} X}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂')
    (sq : CommSq α φ φ' β)
    {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    (relativeDifferentials' φ.hom).map f ≫
        (ModuleCat.restrictScalars (((ringSheaf O₂).obj.map f).hom)).map
          (relativeDifferentialsMapApp φ φ' α β sq V) =
      relativeDifferentialsMapApp φ φ' α β sq U ≫
        ((presheafRestrictScalars β).obj (relativeDifferentials' φ'.hom)).map f := by
  apply CommRingCat.KaehlerDifferential.ext
  intro b
  have hβ :
      β.hom.app V ((ringSheaf O₂).obj.map f b) =
        (ringSheaf O₂').obj.map f (β.hom.app U b) := by
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (β.hom.naturality f)) b
  have h₁ :
      (ConcreteCategory.hom (relativeDifferentialsMapApp φ φ' α β sq V))
          ((ConcreteCategory.hom ((relativeDifferentials' φ.hom).map f))
            (CommRingCat.KaehlerDifferential.d b)) =
        (ConcreteCategory.hom (relativeDifferentialsMapApp φ φ' α β sq V))
          (CommRingCat.KaehlerDifferential.d ((ringSheaf O₂).obj.map f b)) := by
    congr 1
    simpa using
      (relativeDifferentials'_map_d φ.hom f b)
  have h₂ :
      (ConcreteCategory.hom (relativeDifferentialsMapApp φ φ' α β sq V))
          (CommRingCat.KaehlerDifferential.d ((ringSheaf O₂).obj.map f b)) =
        CommRingCat.KaehlerDifferential.d
          (β.hom.app V ((ringSheaf O₂).obj.map f b)) := by
    change (ConcreteCategory.hom
        (CommRingCat.KaehlerDifferential.map
          (relativeDifferentialsSquare_app φ φ' α β sq V)))
        (CommRingCat.KaehlerDifferential.d ((ringSheaf O₂).obj.map f b)) =
      CommRingCat.KaehlerDifferential.d
        (β.hom.app V ((ringSheaf O₂).obj.map f b))
    exact CommRingCat.KaehlerDifferential.map_d
      (relativeDifferentialsSquare_app φ φ' α β sq V)
      ((ringSheaf O₂).obj.map f b)
  have h₃ :
      CommRingCat.KaehlerDifferential.d
          (β.hom.app V ((ringSheaf O₂).obj.map f b)) =
        (ConcreteCategory.hom
          (((presheafRestrictScalars β).obj (relativeDifferentials' φ'.hom)).map f))
          (CommRingCat.KaehlerDifferential.d (β.hom.app U b)) := by
    rw [hβ]
    symm
    simpa using
      (relativeDifferentials'_map_d φ'.hom f (β.hom.app U b))
  have h₄ :
      (ConcreteCategory.hom
          (((presheafRestrictScalars β).obj (relativeDifferentials' φ'.hom)).map f))
          (CommRingCat.KaehlerDifferential.d (β.hom.app U b)) =
        (ConcreteCategory.hom
          (((presheafRestrictScalars β).obj (relativeDifferentials' φ'.hom)).map f))
          ((ConcreteCategory.hom (relativeDifferentialsMapApp φ φ' α β sq U))
            (CommRingCat.KaehlerDifferential.d b)) := by
    congr 1
    symm
    change (ConcreteCategory.hom
        (CommRingCat.KaehlerDifferential.map
          (relativeDifferentialsSquare_app φ φ' α β sq U)))
        (CommRingCat.KaehlerDifferential.d b) =
      CommRingCat.KaehlerDifferential.d (β.hom.app U b)
    exact CommRingCat.KaehlerDifferential.map_d
      (relativeDifferentialsSquare_app φ φ' α β sq U) b
  exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- The presheaf comparison morphism on relative differentials induced by a commutative square of
sheaves of rings. This is private bridge data for the sheaf-level map. -/
private noncomputable def relativeDifferentialsMapPresheaf
    {O₁ O₂ O₁' O₂' : TopCat.Sheaf CommRingCat.{u} X}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂')
    (sq : CommSq α φ φ' β) :
    relativeDifferentials' φ.hom ⟶
      (presheafRestrictScalars β).obj (relativeDifferentials' φ'.hom) where
  app U := relativeDifferentialsMapApp φ φ' α β sq U
  naturality f := relativeDifferentialsMapApp_naturality φ φ' α β sq f

private abbrev relativeDifferentialsMapDerivation
    {O₁ O₂ O₁' O₂' : TopCat.Sheaf CommRingCat.{u} X}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂')
    (sq : CommSq α φ φ' β) :
    Der[φ ; (SheafOfModules.restrictScalars (ringSheafMap β)).obj Ω(φ')] :=
  (derivation' φ.hom).postcomp
    (relativeDifferentialsMapPresheaf φ φ' α β sq ≫
      (presheafRestrictScalars β).map
        ((PresheafOfModules.sheafificationAdjunction
            (𝟙 (ringSheaf O₂').obj)).unit.app
          (relativeDifferentials' φ'.hom)))

/-- Lemma 17.28.8: a commutative square of sheaves of commutative rings on `X` induces the
canonical morphism on sheaves of relative differentials
`Ω_{O₂/O₁} → Ω_{O₂'/O₁'}`, with the target viewed as an `O₂`-module via `β`. -/
noncomputable def relativeDifferentialsMap
    {O₁ O₂ O₁' O₂' : TopCat.Sheaf CommRingCat.{u} X}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂')
    (sq : CommSq α φ φ' β) :
    Ω(φ) ⟶ (SheafOfModules.restrictScalars (ringSheafMap β)).obj Ω(φ') :=
  relativeDifferentialDesc φ
    (relativeDifferentialsMapDerivation φ φ' α β sq)

-- This factorization theorem keeps the descended target derivation internal; the public API
-- exposes the sheaf map and its source-facing `d`-formula instead.
private theorem relativeDifferentialsMap_fac
    {O₁ O₂ O₁' O₂' : TopCat.Sheaf CommRingCat.{u} X}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂')
    (sq : CommSq α φ φ' β) :
    RelativeDerivation.postcomp (relativeDifferential φ)
      (relativeDifferentialsMap φ φ' α β sq) =
        relativeDifferentialsMapDerivation φ φ' α β sq :=
  relativeDifferentialDesc_fac φ
    (relativeDifferentialsMapDerivation φ φ' α β sq)

/-- The canonical sheaf-level map on relative differentials sends `d(f)` to `d(β(f))` on every
open set. -/
theorem relativeDifferentialsMap_d
    {O₁ O₂ O₁' O₂' : TopCat.Sheaf CommRingCat.{u} X}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂')
    (sq : CommSq α φ φ' β)
    (U : (Opens X)ᵒᵖ) (f : O₂.obj.obj U) :
    (relativeDifferentialsMap φ φ' α β sq).val.app U
      (((relativeDifferential φ).app U).d f) =
        ((relativeDifferential φ').app U).d (β.hom.app U f) := by
  calc
    (ConcreteCategory.hom ((relativeDifferentialsMap φ φ' α β sq).val.app U))
        (((relativeDifferential φ).app U).d f) =
      ((relativeDifferentialsMapDerivation φ φ' α β sq).app U).d f := by
        change ((RelativeDerivation.postcomp (relativeDifferential φ)
          (relativeDifferentialsMap φ φ' α β sq)).app U).d f = _
        simpa using
          congrArg (fun D ↦ (D.app U).d f)
            (relativeDifferentialsMap_fac φ φ' α β sq)
    _ = ((relativeDifferential φ').app U).d (β.hom.app U f) := by
      change (ConcreteCategory.hom
          (((presheafRestrictScalars β).map
              ((PresheafOfModules.sheafificationAdjunction
                  (𝟙 (ringSheaf O₂').obj)).unit.app
                (relativeDifferentials' φ'.hom))).app U))
          ((ConcreteCategory.hom (relativeDifferentialsMapApp φ φ' α β sq U))
            (((derivation' φ.hom).app U).d f)) =
        ((relativeDifferential φ').app U).d (β.hom.app U f)
      rw [show (ConcreteCategory.hom (relativeDifferentialsMapApp φ φ' α β sq U))
            (((derivation' φ.hom).app U).d f) =
              CommRingCat.KaehlerDifferential.d (β.hom.app U f) by
            change (ConcreteCategory.hom
                (CommRingCat.KaehlerDifferential.map
                  (relativeDifferentialsSquare_app φ φ' α β sq U)))
                (((derivation' φ.hom).app U).d f) =
              CommRingCat.KaehlerDifferential.d (β.hom.app U f)
            exact CommRingCat.KaehlerDifferential.map_d
              (relativeDifferentialsSquare_app φ φ' α β sq U) f]
      change (ConcreteCategory.hom
          (((PresheafOfModules.sheafificationAdjunction
              (𝟙 (ringSheaf O₂').obj)).unit.app
            (relativeDifferentials' φ'.hom)).app U))
          (CommRingCat.KaehlerDifferential.d (β.hom.app U f)) =
        ((relativeDifferential φ').app U).d (β.hom.app U f)
      rfl

/-- A morphism of sheaves of relative differentials is the canonical one once it sends each
generator `d(f)` to `d(β(f))`. -/
theorem relativeDifferentialsMap_unique
    {O₁ O₂ O₁' O₂' : TopCat.Sheaf CommRingCat.{u} X}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α : O₁ ⟶ O₁') (β : O₂ ⟶ O₂')
    (sq : CommSq α φ φ' β)
    (ψ : Ω(φ) ⟶ (SheafOfModules.restrictScalars (ringSheafMap β)).obj Ω(φ'))
    (hψ : ∀ (U : (Opens X)ᵒᵖ) (f : O₂.obj.obj U),
      ψ.val.app U (((relativeDifferential φ).app U).d f) =
        ((relativeDifferential φ').app U).d (β.hom.app U f)) :
    ψ = relativeDifferentialsMap φ φ' α β sq := by
  apply relativeDifferential_postcomp_injective φ
  ext U f
  change ψ.val.app U (((relativeDifferential φ).app U).d f) =
    (relativeDifferentialsMap φ φ' α β sq).val.app U
      (((relativeDifferential φ).app U).d f)
  exact Eq.trans (hψ U f) (by
    simpa using (relativeDifferentialsMap_d φ φ' α β sq U f).symm)

end TopCat.Sheaf
