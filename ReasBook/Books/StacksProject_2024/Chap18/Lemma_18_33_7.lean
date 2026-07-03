import Mathlib
import StacksProject_2024.Chap18.Lemma_18_33_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open PresheafOfModules.DifferentialsConstruction
open scoped SheafOfModules.RingedSite
open scoped RelativeDerivation

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 18.33.7:
- primary domain: functoriality of sheafified relative differentials for a commutative square of
  sheaves of commutative rings on a site;
- sampled owner declarations:
  `relativeDifferentials`,
  `relativeDifferentialDesc`,
  `SheafOfModules.restrictScalars`,
  `CategoryTheory.CommSq`,
  `PresheafOfModules.sheafificationAdjunction`;
- best owner abstraction: the source-facing sheaf owner `relativeDifferentials`, with the
  change-of-rings functor `SheafOfModules.restrictScalars` providing the
  canonical codomain;
- primitive data: the commutative square `sq : CommSq α₁ φ φ' α₂`;
- derived API: the private presheaf-level comparison map on `relativeDifferentials'`, the induced
  target derivation on the restricted sheaf of relative differentials, and the descended sheaf map.

Source/core/bridge triage:
- `source-facing`: the sheaf of relative differentials `relativeDifferentials φ`;
- `core/canonical`: the sheaf-level restriction of scalars functor and the sheafification
  adjunction;
- `bridge/view`: the comparison morphism induced by a commutative square of sheaves of rings.

The public statement in this file should therefore live at the sheaf level. The presheaf
comparison on `relativeDifferentials'` is only an internal bridge used to construct the descended
map on `relativeDifferentials φ`. -/

/-- The underlying sheaf of rings morphism attached to a morphism of sheaves of commutative rings.
-/
private abbrev ringSheafMap
    {O O' : Sheaf J CommRingCat} (α : O ⟶ O') :
    ringSheaf J O ⟶ ringSheaf J O' :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).map α

private abbrev presheafRestrictScalars
    {O O' : Sheaf J CommRingCat} (α : O ⟶ O') :=
  PresheafOfModules.restrictScalars (ringSheafMap α).hom

/-- The sectionwise commutativity relation attached to a commutative square of sheaves of
commutative rings. -/
private theorem relativeDifferentialsSquare_app
    {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α₁ : O₁ ⟶ O₁') (α₂ : O₂ ⟶ O₂')
    (sq : CommSq α₁ φ φ' α₂) (X : Cᵒᵖ) :
    α₁.hom.app X ≫ φ'.hom.app X = φ.hom.app X ≫ α₂.hom.app X := by
  simpa using congrArg (fun k ↦ k.hom.app X) sq.w

/-- The objectwise comparison map on relative differentials induced by a commutative square of
sheaves of commutative rings. -/
private abbrev relativeDifferentialsMapApp
    {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α₁ : O₁ ⟶ O₁') (α₂ : O₂ ⟶ O₂')
    (sq : CommSq α₁ φ φ' α₂) (X : Cᵒᵖ) :
    (relativeDifferentials' φ.hom).obj X ⟶
      ((presheafRestrictScalars α₂).obj (relativeDifferentials' φ'.hom)).obj X :=
  CommRingCat.KaehlerDifferential.map (relativeDifferentialsSquare_app φ φ' α₁ α₂ sq X)

-- Proof sketch: both sides are morphisms out of the objectwise Kähler differentials on `O₂(X)`.
-- Check equality on generators `d b`; there it reduces to the compatibility of
-- `CommRingCat.KaehlerDifferential.map_d` with the naturality of `α₂`.
/-- The objectwise comparison maps are compatible with restriction morphisms in the site. -/
private theorem relativeDifferentialsMapApp_naturality
    {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α₁ : O₁ ⟶ O₁') (α₂ : O₂ ⟶ O₂')
    (sq : CommSq α₁ φ φ' α₂)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (relativeDifferentials' φ.hom).map f ≫
        (ModuleCat.restrictScalars (((ringSheaf J O₂).obj.map f).hom)).map
          (relativeDifferentialsMapApp φ φ' α₁ α₂ sq Y) =
      relativeDifferentialsMapApp φ φ' α₁ α₂ sq X ≫
        ((presheafRestrictScalars α₂).obj (relativeDifferentials' φ'.hom)).map f := sorry

/-- The presheaf comparison morphism on relative differentials induced by a commutative square of
sheaves of commutative rings. This is a private bridge used to define the sheaf-level map on
`relativeDifferentials φ`. -/
private noncomputable def relativeDifferentialsMapPresheaf
    {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α₁ : O₁ ⟶ O₁') (α₂ : O₂ ⟶ O₂')
    (sq : CommSq α₁ φ φ' α₂) :
    relativeDifferentials' φ.hom ⟶
      (presheafRestrictScalars α₂).obj (relativeDifferentials' φ'.hom) where
  app X := relativeDifferentialsMapApp φ φ' α₁ α₂ sq X
  naturality f := relativeDifferentialsMapApp_naturality φ φ' α₁ α₂ sq f

variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The target derivation obtained by composing the presheaf comparison with the sheafification
unit for the target sheaf of relative differentials. -/
abbrev relativeDifferentialsMapDerivation
    {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α₁ : O₁ ⟶ O₁') (α₂ : O₂ ⟶ O₂')
    (sq : CommSq α₁ φ φ' α₂) :
    Der[φ ;
      (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map α₂)).obj (Ω(φ'))] :=
  (derivation' φ.hom).postcomp
    (relativeDifferentialsMapPresheaf φ φ' α₁ α₂ sq ≫
      (presheafRestrictScalars α₂).map
        ((PresheafOfModules.sheafificationAdjunction
            (𝟙 (ringSheaf J O₂').obj)).unit.app
          (relativeDifferentials' φ'.hom)))

/-- Lemma 18.33.7: a commutative square of sheaves of commutative rings induces a canonical map
from `Ω(φ)` to the restriction of scalars of `Ω(φ')` along `α₂`. This is the sheaf-level
comparison morphism on relative differentials attached to the square. -/
noncomputable def relativeDifferentialsMap
    {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α₁ : O₁ ⟶ O₁') (α₂ : O₂ ⟶ O₂')
    (sq : CommSq α₁ φ φ' α₂) :
    Ω(φ) ⟶
      (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map α₂)).obj (Ω(φ')) :=
  relativeDifferentialDesc φ
    (relativeDifferentialsMapDerivation φ φ' α₁ α₂ sq)

/-- The comparison morphism on sheafified relative differentials is characterized by postcomposing
the universal derivation with the target derivation induced by the commutative square. -/
theorem relativeDifferentialsMap_fac
    {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α₁ : O₁ ⟶ O₁') (α₂ : O₂ ⟶ O₂')
    (sq : CommSq α₁ φ φ' α₂) :
    RelativeDerivation.postcomp (relativeDifferential φ)
      (relativeDifferentialsMap φ φ' α₁ α₂ sq) =
    relativeDifferentialsMapDerivation φ φ' α₁ α₂ sq :=
  relativeDifferentialDesc_fac φ
    (relativeDifferentialsMapDerivation φ φ' α₁ α₂ sq)

end SheafOfModules.RingedSite
