import stacks_proof.stacks_project.Chap18.Lemma_18_33_2
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open PresheafOfModules.DifferentialsConstruction
open scoped SheafOfModules.RingedSite
open scoped RelativeDerivation

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]

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

section

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]

/-- The sectionwise commutativity relation attached to a commutative square of sheaves of
commutative rings. -/
private theorem relativeDifferentialsSquare_app
    {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α₁ : O₁ ⟶ O₁') (α₂ : O₂ ⟶ O₂')
    (sq : CommSq α₁ φ φ' α₂) (X : Cᵒᵖ) :
    α₁.hom.app X ≫ φ'.hom.app X = φ.hom.app X ≫ α₂.hom.app X := by
  simpa using congrArg (fun k ↦ k.hom.app X) sq.w

end

/-- Helper for Lemma 18.33.7: the presheaf-level restriction-of-scalars functor attached to a
morphism of sheaves of commutative rings. -/
private abbrev presheafRestrictScalars
    {O O' : Sheaf J CommRingCat} (α : O ⟶ O') :=
  PresheafOfModules.restrictScalars (ringSheafMap α).hom

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
        ((presheafRestrictScalars α₂).obj (relativeDifferentials' φ'.hom)).map f := by
  apply CommRingCat.KaehlerDifferential.ext
  intro b
  have hα₂ :
      α₂.hom.app Y ((ringSheaf J O₂).obj.map f b) =
        (ringSheaf J O₂').obj.map f (α₂.hom.app X b) := by
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (α₂.hom.naturality f)) b
  -- Both composites are determined by the image of the generator `d b`.
  have h₁ :
      (ConcreteCategory.hom (relativeDifferentialsMapApp φ φ' α₁ α₂ sq Y))
          ((ConcreteCategory.hom ((relativeDifferentials' φ.hom).map f))
            (CommRingCat.KaehlerDifferential.d b)) =
        (ConcreteCategory.hom (relativeDifferentialsMapApp φ φ' α₁ α₂ sq Y))
          (CommRingCat.KaehlerDifferential.d ((ringSheaf J O₂).obj.map f b)) := by
    congr 1
    simpa using relativeDifferentials'_map_d φ.hom f b
  have h₂ :
      (ConcreteCategory.hom (relativeDifferentialsMapApp φ φ' α₁ α₂ sq Y))
          (CommRingCat.KaehlerDifferential.d ((ringSheaf J O₂).obj.map f b)) =
        CommRingCat.KaehlerDifferential.d
          (α₂.hom.app Y ((ringSheaf J O₂).obj.map f b)) := by
    change (ConcreteCategory.hom
        (CommRingCat.KaehlerDifferential.map
          (relativeDifferentialsSquare_app φ φ' α₁ α₂ sq Y)))
        (CommRingCat.KaehlerDifferential.d ((ringSheaf J O₂).obj.map f b)) =
      CommRingCat.KaehlerDifferential.d
        (α₂.hom.app Y ((ringSheaf J O₂).obj.map f b))
    exact CommRingCat.KaehlerDifferential.map_d
      (relativeDifferentialsSquare_app φ φ' α₁ α₂ sq Y)
      ((ringSheaf J O₂).obj.map f b)
  have h₃ :
      CommRingCat.KaehlerDifferential.d
          (α₂.hom.app Y ((ringSheaf J O₂).obj.map f b)) =
        (ConcreteCategory.hom
          (((presheafRestrictScalars α₂).obj (relativeDifferentials' φ'.hom)).map f))
          (CommRingCat.KaehlerDifferential.d (α₂.hom.app X b)) := by
    rw [hα₂]
    symm
    simpa using relativeDifferentials'_map_d φ'.hom f (α₂.hom.app X b)
  have h₄ :
      (ConcreteCategory.hom
          (((presheafRestrictScalars α₂).obj (relativeDifferentials' φ'.hom)).map f))
          (CommRingCat.KaehlerDifferential.d (α₂.hom.app X b)) =
        (ConcreteCategory.hom
          (((presheafRestrictScalars α₂).obj (relativeDifferentials' φ'.hom)).map f))
          ((ConcreteCategory.hom (relativeDifferentialsMapApp φ φ' α₁ α₂ sq X))
            (CommRingCat.KaehlerDifferential.d b)) := by
    congr 1
    symm
    change (ConcreteCategory.hom
        (CommRingCat.KaehlerDifferential.map
          (relativeDifferentialsSquare_app φ φ' α₁ α₂ sq X)))
        (CommRingCat.KaehlerDifferential.d b) =
      CommRingCat.KaehlerDifferential.d (α₂.hom.app X b)
    exact CommRingCat.KaehlerDifferential.map_d
      (relativeDifferentialsSquare_app φ φ' α₁ α₂ sq X)
      b
  exact h₁.trans (h₂.trans (h₃.trans h₄))

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
private abbrev relativeDifferentialsMapDerivation
    {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α₁ : O₁ ⟶ O₁') (α₂ : O₂ ⟶ O₂')
    (sq : CommSq α₁ φ φ' α₂) :
    Der[φ ; (restrictionAlong α₂).obj Ω(φ')] :=
  (derivation' φ.hom).postcomp
    (relativeDifferentialsMapPresheaf φ φ' α₁ α₂ sq ≫
      (presheafRestrictScalars α₂).map
        ((PresheafOfModules.sheafificationAdjunction
            (𝟙 (ringSheaf J O₂').obj)).unit.app
          (relativeDifferentials' φ'.hom)))

/-- Lemma 18.33.7: a commutative square of sheaves of commutative rings induces a canonical map
from `Ω(φ)` to the restriction of scalars of `Ω(φ')` along `α₂`. This is the sheaf-level
comparison morphism on relative differentials attached to the square. -/
@[stacks 08TR]
noncomputable def relativeDifferentialsMap
    {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α₁ : O₁ ⟶ O₁') (α₂ : O₂ ⟶ O₂')
    (sq : CommSq α₁ φ φ' α₂) :
    Ω(φ) ⟶ (restrictionAlong α₂).obj Ω(φ') :=
  relativeDifferentialDesc φ
    (relativeDifferentialsMapDerivation φ φ' α₁ α₂ sq)

-- This factorization theorem keeps the descended target derivation internal; the public API
-- exposes the sheaf map and its source-facing `d`-formula instead.
private theorem relativeDifferentialsMap_fac
    {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α₁ : O₁ ⟶ O₁') (α₂ : O₂ ⟶ O₂')
    (sq : CommSq α₁ φ φ' α₂) :
    (relativeDifferential φ).postcomp (relativeDifferentialsMap φ φ' α₁ α₂ sq).val =
      relativeDifferentialsMapDerivation φ φ' α₁ α₂ sq :=
  relativeDifferentialDesc_fac φ
    (relativeDifferentialsMapDerivation φ φ' α₁ α₂ sq)

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- Helper for Lemma 18.33.7: objectwise, the presheaf comparison sends the universal generator
`d(f)` to `d(α₂(f))`. -/
private theorem relativeDifferentialsMapApp_d
    {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α₁ : O₁ ⟶ O₁') (α₂ : O₂ ⟶ O₂')
    (sq : CommSq α₁ φ φ' α₂)
    (X : Cᵒᵖ) (f : O₂.obj.obj X) :
    (ConcreteCategory.hom (relativeDifferentialsMapApp φ φ' α₁ α₂ sq X))
      (((derivation' φ.hom).app X).d f) =
        CommRingCat.KaehlerDifferential.d (α₂.hom.app X f) := by
  change (ConcreteCategory.hom
      (CommRingCat.KaehlerDifferential.map
        (relativeDifferentialsSquare_app φ φ' α₁ α₂ sq X)))
      (CommRingCat.KaehlerDifferential.d f) =
    CommRingCat.KaehlerDifferential.d (α₂.hom.app X f)
  exact CommRingCat.KaehlerDifferential.map_d
    (relativeDifferentialsSquare_app φ φ' α₁ α₂ sq X) f

/-- Helper for Lemma 18.33.7: the sheafification unit on the target relative differentials still
acts by the universal derivation on generators. -/
private theorem restrictedRelativeDifferentialsUnit_d
    {O₁' O₂' : Sheaf J CommRingCat}
    (φ' : O₁' ⟶ O₂') {O₂ : Sheaf J CommRingCat} (α₂ : O₂ ⟶ O₂')
    (X : Cᵒᵖ) (f : O₂'.obj.obj X) :
    (ConcreteCategory.hom
      (((presheafRestrictScalars α₂).map
          ((PresheafOfModules.sheafificationAdjunction
              (𝟙 (ringSheaf J O₂').obj)).unit.app
            (relativeDifferentials' φ'.hom))).app X))
      (CommRingCat.KaehlerDifferential.d f) =
        ((relativeDifferential φ').app X).d f := by
  rfl

/-- The canonical sheaf-level map on relative differentials sends `d(f)` to `d(α₂(f))` on every
object of the site. -/
theorem relativeDifferentialsMap_d
    {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α₁ : O₁ ⟶ O₁') (α₂ : O₂ ⟶ O₂')
    (sq : CommSq α₁ φ φ' α₂)
    (X : Cᵒᵖ) (f : O₂.obj.obj X) :
    (relativeDifferentialsMap φ φ' α₁ α₂ sq).val.app X
      (((relativeDifferential φ).app X).d f) =
        ((relativeDifferential φ').app X).d (α₂.hom.app X f) := by
  calc
    (ConcreteCategory.hom ((relativeDifferentialsMap φ φ' α₁ α₂ sq).val.app X))
        (((relativeDifferential φ).app X).d f) =
      ((relativeDifferentialsMapDerivation φ φ' α₁ α₂ sq).app X).d f := by
        change ((relativeDifferential φ).postcomp
          (relativeDifferentialsMap φ φ' α₁ α₂ sq).val).d f = _
        simpa using
          congrArg (fun D ↦ D.d f)
            (relativeDifferentialsMap_fac φ φ' α₁ α₂ sq)
    _ = ((relativeDifferential φ').app X).d (α₂.hom.app X f) := by
      change (ConcreteCategory.hom
          (((presheafRestrictScalars α₂).map
              ((PresheafOfModules.sheafificationAdjunction
                  (𝟙 (ringSheaf J O₂').obj)).unit.app
                (relativeDifferentials' φ'.hom))).app X))
          ((ConcreteCategory.hom (relativeDifferentialsMapApp φ φ' α₁ α₂ sq X))
            (((derivation' φ.hom).app X).d f)) =
        ((relativeDifferential φ').app X).d (α₂.hom.app X f)
      rw [relativeDifferentialsMapApp_d φ φ' α₁ α₂ sq X f]
      exact restrictedRelativeDifferentialsUnit_d φ' α₂ X (α₂.hom.app X f)

/-- A morphism of sheaves of relative differentials is the canonical one once it sends each
generator `d(f)` to `d(α₂(f))`. -/
theorem relativeDifferentialsMap_unique
    {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat}
    (φ : O₁ ⟶ O₂) (φ' : O₁' ⟶ O₂')
    (α₁ : O₁ ⟶ O₁') (α₂ : O₂ ⟶ O₂')
    (sq : CommSq α₁ φ φ' α₂)
    (ψ : Ω(φ) ⟶ (restrictionAlong α₂).obj Ω(φ'))
    (hψ : ∀ (X : Cᵒᵖ) (f : O₂.obj.obj X),
      ψ.val.app X (((relativeDifferential φ).app X).d f) =
        ((relativeDifferential φ').app X).d (α₂.hom.app X f)) :
    ψ = relativeDifferentialsMap φ φ' α₁ α₂ sq := by
  apply relativeDifferential_postcomp_injective φ
  ext X f
  change ψ.val.app X (((relativeDifferential φ).app X).d f) =
    (relativeDifferentialsMap φ φ' α₁ α₂ sq).val.app X
      (((relativeDifferential φ).app X).d f)
  exact Eq.trans (hψ X f) (by
    simpa using (relativeDifferentialsMap_d φ φ' α₁ α₂ sq X f).symm)

end SheafOfModules.RingedSite
