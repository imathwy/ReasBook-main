import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_18_33_1 (from Chap18) -/
open CategoryTheory
open scoped RelativeDerivation

universe u v

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (O₁ O₂ : Sheaf J CommRingCat)
variable (φ : O₁ ⟶ O₂)
variable (F : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O₂))

/- Domain-style sampling for Definition 18.33.1:
- primary domain: relative derivations of sheaves/presheaves of modules over a morphism of sheaves
  of commutative rings;
- sampled owner declarations:
  `PresheafOfModules.Derivation'`,
  `SheafOfModules.RelativeDerivation`,
  `PresheafOfModules.Derivation'.app`,
  `RelativeDerivation.postcomp`;
- owner abstraction: `PresheafOfModules.Derivation'`;
- primitive data: the additive sectionwise map together with vanishing on the image of `O₁` and the
  Leibniz rule;
- derived API: the sheaf-level bridge `SheafOfModules.RelativeDerivation` with notation
  `Der[φ ; F]`.

Source/core/bridge triage:
- `core/canonical`: `PresheafOfModules.Derivation'`;
- `bridge/view`: `SheafOfModules.RelativeDerivation φ F` and the notation `Der[φ ; F]`;
- this file is a canonical recall of the sheaf-level bridge, not a second owner declaration. -/

/- Definition 18.33.1: for a morphism `φ : O₁ ⟶ O₂` of sheaves of commutative rings on a site and
an `O₂`-module sheaf `F`, the type `Der[φ ; F]` is the canonical notion of a
`φ`-derivation `O₂ → F`, i.e. an additive map on local sections that vanishes on the image of
`O₁` and satisfies the Leibniz rule; this is the Lean realization of
`Der_{O₁}(O₂, F)`. -/
#check Der[φ ; F]

/- Companion recall: the upstream canonical owner is `PresheafOfModules.Derivation'`, and
`Der[φ ; F]` is its sheaf-level source-facing specialization from
`StacksProject_2024/Items/Chap17/Definition_17_28_1.lean`. -/
recall PresheafOfModules.Derivation'

/-! ### Lemma_18_33_2 (from Chap18) -/
open CategoryTheory
open PresheafOfModules
open PresheafOfModules.DifferentialsConstruction
open scoped RelativeDerivation

universe u v

noncomputable section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

namespace SheafOfModules.RingedSite

variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}
variable (φ : O₁ ⟶ O₂)

/- Domain-style sampling for Lemma 18.33.2:
- primary domain: sheafified relative differentials of a morphism of sheaves of commutative rings
  on a general site, together with their universal derivation;
- sampled owner declarations:
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`,
  `PresheafOfModules.DifferentialsConstruction.derivation'`,
  `PresheafOfModules.DifferentialsConstruction.isUniversal'`,
  `ringSheaf`,
  `TopCat.Sheaf.relativeDifferentials`,
  `TopCat.Sheaf.relativeDifferentials_representsDerivations`;
- best owner abstraction: the source-facing sheaf owner `relativeDifferentials` with textbook
  notation `Ω(φ)`, obtained by sheafifying the canonical presheaf owner
  `relativeDifferentials' φ.hom`;
- primitive data: the underlying `RingCat`-valued sheaf `ringSheaf J O₂`, the sheaf
  `relativeDifferentials φ`, and its universal derivation `relativeDifferential φ`;
- derived API: the descended universal map `relativeDifferentialDesc`, its factorization and
  injectivity lemmas, the representing theorem
  `relativeDifferentials_representsDerivations`, and the predicate
  `IsUniversalRelativeDifferentials`.

Source/core/bridge triage:
- `core/canonical`: the presheaf owner
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`;
- `source-facing`: the site-level sheafified owner `relativeDifferentials` written as `Ω(φ)`;
- `bridge/view`: the sheafification-adjunction descent API carrying the presheaf universal
  derivation to sheaf targets.

This file is therefore the owner for the generic-site construction; downstream files should reuse
`relativeDifferentials`, `relativeDifferential`, and `Ω(φ)` rather than reintroducing parallel
site-specific wrapper names. -/

/-- The sheaf of relative differentials of `O₂` over `O₁`, obtained by sheafifying the canonical
presheaf of relative differentials. -/
abbrev relativeDifferentials :
    SheafOfModules (ringSheaf J O₂) :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf J O₂).obj)).obj
    (relativeDifferentials' φ.hom)

@[inherit_doc relativeDifferentials]
scoped[SheafOfModules.RingedSite] notation:max "Ω(" φ ")" =>
  SheafOfModules.RingedSite.relativeDifferentials φ

open scoped SheafOfModules.RingedSite

/-- The sheaf of relative differentials is the sheafification of the presheaf-level relative
differentials construction. -/
theorem relativeDifferentials_def :
    Ω(φ) =
      (PresheafOfModules.sheafification (𝟙 (ringSheaf J O₂).obj)).obj
        (relativeDifferentials' φ.hom) :=
  rfl

/-- The canonical `O₁`-derivation from `O₂` to the sheaf of relative differentials on the site. -/
def relativeDifferential :
    Der[φ ; Ω(φ)] :=
  (derivation' φ.hom).postcomp
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf J O₂).obj)).unit.app (relativeDifferentials' φ.hom))

/-- The morphism induced from a target derivation by the universal property of relative
differentials. -/
def relativeDifferentialDesc
    {F : SheafOfModules (ringSheaf J O₂)} (D : Der[φ ; F]) :
    Ω(φ) ⟶ F :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O₂).obj)).homEquiv
      (relativeDifferentials' φ.hom) F).symm
    ((isUniversal' φ.hom).desc D)

-- Proof sketch: `relativeDifferentialDesc` is obtained by transporting the presheaf-level
-- universal morphism across the sheafification adjunction, so the factorization identity is the
-- adjoint form of `(isUniversal' φ.hom).fac`.
/-- The descended morphism factors the target derivation through the universal derivation. -/
theorem relativeDifferentialDesc_fac
    {F : SheafOfModules (ringSheaf J O₂)} (D : Der[φ ; F]) :
    RelativeDerivation.postcomp (relativeDifferential φ)
      (relativeDifferentialDesc φ D) = D :=
  sorry

-- Proof sketch: uniqueness is inherited from the presheaf-level universal property after applying
-- the sheafification adjunction equivalence.
/-- A morphism out of `Ω(φ)` is determined by its postcomposition with the universal derivation. -/
theorem relativeDifferential_postcomp_injective
    {F : SheafOfModules (ringSheaf J O₂)} ⦃α β : Ω(φ) ⟶ F⦄
    (h : RelativeDerivation.postcomp (relativeDifferential φ) α =
      RelativeDerivation.postcomp (relativeDifferential φ) β) :
    α = β :=
  sorry

/-- The universal property for a chosen sheaf of relative differentials on a site: every relative
derivation factors uniquely through the chosen universal derivation. -/
def IsUniversalRelativeDifferentials
    (Ω' : SheafOfModules (ringSheaf J O₂)) (d : Der[φ ; Ω']) : Prop :=
  ∀ (F : SheafOfModules (ringSheaf J O₂)) (D : Der[φ ; F]),
    ∃! α : Ω' ⟶ F, RelativeDerivation.postcomp d α = D

-- Proof sketch: combine the descended morphism with its factorization and uniqueness lemmas.
/-- Lemma 18.33.2: the functor `F ↦ Der_{O₁}(O₂, F)` on `O₂`-module sheaves is represented by
`Ω(φ)`; equivalently, every `O₁`-derivation `O₂ → F` factors uniquely through the canonical
derivation `relativeDifferential φ`. -/
theorem relativeDifferentials_representsDerivations
    (F : SheafOfModules (ringSheaf J O₂)) (D : Der[φ ; F]) :
    ∃! α : Ω(φ) ⟶ F,
      RelativeDerivation.postcomp (relativeDifferential φ) α = D := by
  refine ⟨relativeDifferentialDesc φ D, ?_, ?_⟩
  · exact relativeDifferentialDesc_fac φ D
  · intro α hα
    apply relativeDifferential_postcomp_injective φ
    calc
      RelativeDerivation.postcomp (relativeDifferential φ) α = D := hα
      _ = RelativeDerivation.postcomp (relativeDifferential φ)
            (relativeDifferentialDesc φ D) :=
        (relativeDifferentialDesc_fac φ D).symm

/-- The canonical sheaf of relative differentials with its universal derivation satisfies the
universal property of relative differentials. -/
theorem relativeDifferentials_hasUniversalProperty :
    IsUniversalRelativeDifferentials φ Ω(φ) (relativeDifferential φ) :=
  relativeDifferentials_representsDerivations φ

end SheafOfModules.RingedSite

/-! ### Definition_18_33_3 (from Chap18) -/
open CategoryTheory
open scoped SheafOfModules.RingedSite

universe u v

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O₁ O₂ : Sheaf J CommRingCat)
variable (φ : O₁ ⟶ O₂)

/- Domain-style sampling for Definition 18.33.3:
- primary domain: sheafified relative differentials of a morphism of sheaves of commutative rings
  on a site, together with the universal relative derivation;
- sampled owner declarations:
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`,
  `SheafOfModules.RingedSite.relativeDifferentials`,
  `SheafOfModules.RingedSite.relativeDifferentials_def`,
  `SheafOfModules.RingedSite.relativeDifferential`;
- best owner abstraction: the chapter owner `SheafOfModules.RingedSite.relativeDifferentials`,
  written `Ω(φ)`, with `relativeDifferentials_def` and `relativeDifferential` as its derived API;
- primitive data: only the morphism of sheaves of rings `φ : O₁ ⟶ O₂`;
- derived API: the sheafification identity for `Ω(φ)` and the universal derivation
  `relativeDifferential φ`.

Source/core/bridge triage:
- `core/canonical`: the presheaf-level owner
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`;
- `source-facing`: `SheafOfModules.RingedSite.relativeDifferentials`, written `Ω(φ)`;
- `bridge/view`: the theorem `relativeDifferentials_def` identifying `Ω(φ)` with the sheafified
  presheaf owner, and the universal derivation `relativeDifferential φ`.

This numbered definition is recall-only: the canonical chapter owner already exists in
`Lemma_18_33_2`, so this file should reuse that owner directly rather than rebuild the same
sheafification term on the public surface. -/

/- Definition 18.33.3, owner recall: for a morphism `φ : O₁ ⟶ O₂` of sheaves of commutative
rings on a site, the module of differentials `Ω_{O₂/O₁}` is the canonical owner
`SheafOfModules.RingedSite.relativeDifferentials`, written `Ω(φ)`. -/
recall SheafOfModules.RingedSite.relativeDifferentials

/- Companion recall: `Ω(φ)` is the sheafification of the canonical presheaf of relative
differentials. -/
#check SheafOfModules.RingedSite.relativeDifferentials_def φ

/- Companion recall: the universal `φ`-derivation
`d : O₂ ⟶ Ω_{O₂/O₁}` is the canonical owner `relativeDifferential φ`. -/
#check SheafOfModules.RingedSite.relativeDifferential φ

end

/-! ### Lemma_18_33_4 (from Chap18) -/
open CategoryTheory
open PresheafOfModules.DifferentialsConstruction
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v

/- Domain-style sampling for Lemma 18.33.4:
- primary domain: sheafification of presheaves of modules over a presheaf of commutative rings,
  applied to the canonical presheaf of relative differentials;
- sampled owner declarations:
  `PresheafOfModules.commRingSheafification`,
  `PresheafOfModules.moduleSheafification`,
  `SheafOfModules.RingedSite.relativeDifferentials`;
- best owner abstraction: the presheaf-side module sheafification functor
  `PresheafOfModules.moduleSheafification` and the sheaf-side relative-differentials owner `Ω(φ)`;
- primitive data: a morphism `φ : O₁ ⟶ O₂` of presheaves of commutative rings and its sheafified
  morphism `(presheafToSheaf J CommRingCat).map φ`;
- derived API: the canonical comparison isomorphism identifying the sheafification of the
  presheaf-level relative differentials with the relative-differentials sheaf of the sheafified
  morphism.

Source/core/bridge triage:
- `core/canonical`: `PresheafOfModules.moduleSheafification` and
  `SheafOfModules.RingedSite.relativeDifferentials`;
- `bridge/view`: the comparison isomorphism in this file.

This item is therefore a bridge theorem. The local wrapper definitions previously duplicating the
chapter owners are removed in favor of those canonical declarations. -/

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{max u v})
variable (φ : O₁ ⟶ O₂)

omit [J.WEqualsLocallyBijective CommRingCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- The sectionwise commutativity relation comparing `φ` with its sheafification. -/
private theorem sheafifiedRelativeDifferentialsSquare_app (X : Cᵒᵖ) :
    (CategoryTheory.toSheafify J O₁).app X ≫
        ((presheafToSheaf J CommRingCat.{max u v}).map φ).hom.app X =
      φ.app X ≫ (CategoryTheory.toSheafify J O₂).app X := by
  exact congrArg (fun k ↦ k.app X) (CategoryTheory.toSheafify_naturality J φ).symm

/-- The objectwise comparison on Kähler differentials induced by sheafification. -/
private abbrev sheafifiedRelativeDifferentialsMapApp (X : Cᵒᵖ) :
    (relativeDifferentials' φ).obj X ⟶
      ((PresheafOfModules.restrictScalars
          (PresheafOfModules.sheafificationRingMap J O₂)).obj
        (relativeDifferentials'
          ((presheafToSheaf J CommRingCat.{max u v}).map φ).hom)).obj X :=
  CommRingCat.KaehlerDifferential.map
    (sheafifiedRelativeDifferentialsSquare_app J O₁ O₂ φ X)

-- Proof sketch: both sides are morphisms out of the objectwise Kähler differentials on `O₂(X)`.
-- Equality on generators `d b` reduces to the naturality of `toSheafify` together with
-- `CommRingCat.KaehlerDifferential.map_d`.
/-- The objectwise sheafification comparison on relative differentials is natural in the site
variable. -/
private theorem sheafifiedRelativeDifferentialsMapApp_naturality
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (relativeDifferentials' φ).map f ≫
        (ModuleCat.restrictScalars
            (((O₂ ⋙ forget₂ CommRingCat RingCat).map f).hom)).map
          (sheafifiedRelativeDifferentialsMapApp J O₁ O₂ φ Y) =
      sheafifiedRelativeDifferentialsMapApp J O₁ O₂ φ X ≫
        ((PresheafOfModules.restrictScalars
            (PresheafOfModules.sheafificationRingMap J O₂)).obj
          (relativeDifferentials'
            ((presheafToSheaf J CommRingCat.{max u v}).map φ).hom)).map f := sorry

/-- The presheaf-level comparison on relative differentials induced by sheafifying `φ`. -/
private noncomputable def sheafifiedRelativeDifferentialsMapPresheaf :
    relativeDifferentials' φ ⟶
      (PresheafOfModules.restrictScalars
          (PresheafOfModules.sheafificationRingMap J O₂)).obj
        (relativeDifferentials'
          ((presheafToSheaf J CommRingCat.{max u v}).map φ).hom) where
  app X := sheafifiedRelativeDifferentialsMapApp J O₁ O₂ φ X
  naturality f := sheafifiedRelativeDifferentialsMapApp_naturality J O₁ O₂ φ f

-- Proof sketch: descend the presheaf comparison map through the module-sheafification adjunction,
-- then use the sheafification unit for the sheaf-level owner `Ω(O₁^# ⟶ O₂^#)`.
/-- The canonical comparison morphism from the sheafification of the presheaf-level relative
differentials to the sheaf of relative differentials of the sheafified morphism. -/
noncomputable def moduleSheafification_relativeDifferentials_comparison :
    (PresheafOfModules.moduleSheafification J O₂).obj (relativeDifferentials' φ) ⟶
      Ω((presheafToSheaf J CommRingCat.{max u v}).map φ) :=
  ((PresheafOfModules.sheafificationAdjunction
      (PresheafOfModules.sheafificationRingMap J O₂)).homEquiv
    (relativeDifferentials' φ)
    (Ω((presheafToSheaf J CommRingCat.{max u v}).map φ))).symm
    (sheafifiedRelativeDifferentialsMapPresheaf J O₁ O₂ φ ≫
      (PresheafOfModules.restrictScalars
          (PresheafOfModules.sheafificationRingMap J O₂)).map
        ((PresheafOfModules.sheafificationAdjunction
            (𝟙
              (ringSheaf J (PresheafOfModules.commRingSheafification J O₂)).obj)).unit.app
          (relativeDifferentials'
            ((presheafToSheaf J CommRingCat.{max u v}).map φ).hom)))

-- Proof sketch: both sides are obtained by sheafifying the objectwise cokernel presentation of
-- Kähler differentials from `18.33.2.1`. Exactness of module sheafification identifies the
-- resulting presentations, and hence the comparison morphism is an isomorphism.
/-- The canonical comparison morphism of Lemma 18.33.4 is an isomorphism. -/
instance moduleSheafification_relativeDifferentials_comparison_isIso :
    IsIso (moduleSheafification_relativeDifferentials_comparison J O₁ O₂ φ) := by
  sorry

/-- Lemma 18.33.4: for a morphism `φ : O₁ ⟶ O₂` of presheaves of commutative rings on a site, the
sheaf of relative differentials of the sheafified morphism `O₁^# ⟶ O₂^#` is canonically
isomorphic to the module sheafification of the presheaf `U ↦ Ω[O₂(U)⁄O₁(U)]`. -/
noncomputable abbrev moduleSheafification_relativeDifferentials_iso :
    (PresheafOfModules.moduleSheafification J O₂).obj (relativeDifferentials' φ) ≅
      Ω((presheafToSheaf J CommRingCat.{max u v}).map φ) :=
  asIso (moduleSheafification_relativeDifferentials_comparison J O₁ O₂ φ)

/-! ### Lemma_18_33_5 (from Chap18) -/
open CategoryTheory
open PresheafOfModules.DifferentialsConstruction
open scoped RelativeDerivation
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

/- Domain-style sampling for Lemma 18.33.5:
- primary domain: inverse image for sheaves of modules on sites and compatibility of relative
  differentials with site pullback;
- sampled owner declarations:
  `SheafOfModules.RingedSite.relativeDifferentials`,
  `SheafOfModules.RingedSite.relativeDifferentials_hasUniversalProperty`,
  `SheafOfModules.pullback`,
  `Functor.sheafPullback`,
  `Functor.sheafPushforwardContinuousId`;
- best owner abstraction: the source-facing sheaf owner `Ω(φ)` together with the canonical
  inverse-image bridge from `SheafOfModules.pullback` to the relative differentials of the
  pulled-back morphism;
- primitive data: the continuous functor `F`, the morphism `φ : O₁ ⟶ O₂`, the actual inverse
  image of `Ω(φ)`, and the canonical pulled-back morphism
  `(F.sheafPullback CommRingCat JC JD).map φ`;
- derived API: the direct comparison isomorphism between the actual inverse image of `Ω(φ)`,
  transported along the canonical pullback ring-sheaf comparison, and the canonical owner
  `Ω((F.sheafPullback CommRingCat JC JD).map φ)`.

Source/core/bridge triage:
- `source-facing`: the statement that inverse image preserves the sheaf of relative differentials;
- `core/canonical`: `Ω(φ)`, `relativeDifferential φ`, and
  `relativeDifferentials_hasUniversalProperty`;
- `bridge/view`: the comparison between the actual inverse image of `Ω(φ)` and the canonical owner
  for the pulled-back morphism.

The public API in this file should therefore expose the inverse-image comparison itself as the
main theorem, and avoid any public iso witness chosen noncanonically from `IsIsomorphic`. -/

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/-- Pullback of a commutative-ring sheaf along `F` commutes with forgetting to `RingCat`. -/
private theorem pullbackCommRingSheaf_ringSheaf_eq
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    [HasWeakSheafify JD CommRingCat.{max u v}]
    [HasWeakSheafify JD RingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
    (O : Sheaf JC CommRingCat.{max u v}) :
    ringSheaf JD ((F.sheafPullback CommRingCat JC JD).obj O) =
      (F.sheafPullback RingCat JC JD).obj (ringSheaf JC O) := by
  sorry

/-- The canonical ring-sheaf comparison between pulling back before or after forgetting
commutativity. -/
noncomputable def pullbackRingSheafIso
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    [HasWeakSheafify JD CommRingCat.{max u v}]
    [HasWeakSheafify JD RingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
    (O : Sheaf JC CommRingCat.{max u v}) :
    ringSheaf JD ((F.sheafPullback CommRingCat JC JD).obj O) ≅
      (F.sheafPullback RingCat JC JD).obj (ringSheaf JC O) :=
  eqToIso (pullbackCommRingSheaf_ringSheaf_eq F O)

section

variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable [HasWeakSheafify JD CommRingCat.{max u v}]
variable [HasWeakSheafify JD RingCat.{max u v}]
variable [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
variable [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
variable [HasWeakSheafify JC AddCommGrpCat.{max u v}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasWeakSheafify JD AddCommGrpCat.{max u v}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O₁ O₂ : Sheaf JC CommRingCat.{max u v}) (φ : O₁ ⟶ O₂)
variable [(SheafOfModules.pushforward
    ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app
      (ringSheaf JC O₂))).IsRightAdjoint]

private instance presheafPushforwardUnitIsRightAdjoint :
    (PresheafOfModules.pushforward
      ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app (ringSheaf JC O₂)).hom).IsRightAdjoint := by
  sorry

/-- The actual inverse image of `Ω(φ)` in the raw pulled-back module category. -/
abbrev inverseImageRelativeDifferentialsSource :
    SheafOfModules ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂)) :=
  (SheafOfModules.pullback
      ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app
        (ringSheaf JC O₂))).obj
    (Ω(φ))

/-- The owner `Ω((F.sheafPullback CommRingCat JC JD).map φ)`, viewed over the raw pulled-back
`RingCat`-valued structure sheaf. -/
abbrev pulledBackRelativeDifferentials :
    SheafOfModules ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂)) :=
  (SheafOfModules.restrictScalars (pullbackRingSheafIso F O₂).inv).obj
    (Ω((F.sheafPullback CommRingCat JC JD).map φ))

private abbrev pulledBackRelativeDifferentialsPresentation :
    SheafOfModules ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂)) :=
  (PresheafOfModules.sheafification
      (𝟙 ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂)).obj)).obj
    ((PresheafOfModules.restrictScalars
        (pullbackRingSheafIso F O₂).inv.hom).obj
      (relativeDifferentials' ((F.sheafPullback CommRingCat JC JD).map φ).hom))

private theorem pulledBackRelativeDifferentialsPresheaf_eq :
    (PresheafOfModules.pullback
        ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app (ringSheaf JC O₂)).hom).obj
        (relativeDifferentials' φ.hom) =
      (PresheafOfModules.restrictScalars
          (pullbackRingSheafIso F O₂).inv.hom).obj
        (relativeDifferentials' ((F.sheafPullback CommRingCat JC JD).map φ).hom) := by
  sorry

private theorem pulledBackRelativeDifferentialsPresentation_isomorphic :
    IsIsomorphic
      (pulledBackRelativeDifferentialsPresentation F O₁ O₂ φ)
      (pulledBackRelativeDifferentials F O₁ O₂ φ :
        SheafOfModules ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂))) := by
  sorry

private noncomputable abbrev pulledBackRelativeDifferentialsPresentationIso :
    pulledBackRelativeDifferentialsPresentation F O₁ O₂ φ ≅
      (pulledBackRelativeDifferentials F O₁ O₂ φ :
        SheafOfModules ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂))) :=
  Classical.choice
    (show Nonempty
      (pulledBackRelativeDifferentialsPresentation F O₁ O₂ φ ≅
        (pulledBackRelativeDifferentials F O₁ O₂ φ :
          SheafOfModules ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂)))) from
      pulledBackRelativeDifferentialsPresentation_isomorphic F O₁ O₂ φ)

-- Proof sketch: write `Ω(φ)` as the sheafification of the presheaf of relative differentials from
-- Lemma `18.33.2`, pull that presentation back along the inverse-image functor, and use exactness
-- of inverse image together with the objectwise identities
-- `f^{-1}(O₂[O₂]) = f^{-1}O₂[f^{-1}O₂]`,
-- `f^{-1}(O₂[O₂ × O₂]) = f^{-1}O₂[f^{-1}O₂ × f^{-1}O₂]`, and
-- `f^{-1}(O₂[O₁]) = f^{-1}O₂[f^{-1}O₁]`. This identifies the actual inverse image of `Ω(φ)` with
-- the canonical pulled-back owner `pulledBackRelativeDifferentials F O₁ O₂ φ`.
/-- Lemma 18.33.5: the actual inverse image of `Ω(φ)` is canonically isomorphic to the
pulled-back relative-differentials owner for `(F.sheafPullback CommRingCat JC JD).map φ`, viewed
over the raw pulled-back `RingCat`-valued structure sheaf. -/
noncomputable abbrev inverseImageRelativeDifferentialsIso :
    inverseImageRelativeDifferentialsSource F O₁ O₂ φ ≅
      (pulledBackRelativeDifferentials F O₁ O₂ φ :
        SheafOfModules ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂))) :=
  (Functor.mapIso
      (SheafOfModules.pullback
        ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app (ringSheaf JC O₂)))
      (eqToIso (relativeDifferentials_def φ))) ≪≫
    (SheafOfModules.sheafificationCompPullback
      ((F.sheafAdjunctionContinuous RingCat JC JD).unit.app (ringSheaf JC O₂))).app
      (relativeDifferentials' φ.hom) ≪≫
    (Functor.mapIso
      (PresheafOfModules.sheafification
        (𝟙 ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂)).obj))
      (eqToIso
        (pulledBackRelativeDifferentialsPresheaf_eq F O₁ O₂ φ))) ≪≫
    pulledBackRelativeDifferentialsPresentationIso F O₁ O₂ φ

/-- The actual inverse image of `Ω(φ)` and the pulled-back owner are isomorphic. -/
theorem inverseImage_relative_differentials :
    IsIsomorphic
      (inverseImageRelativeDifferentialsSource F O₁ O₂ φ)
      (pulledBackRelativeDifferentials F O₁ O₂ φ :
        SheafOfModules ((F.sheafPullback RingCat JC JD).obj (ringSheaf JC O₂))) := by
  exact ⟨inverseImageRelativeDifferentialsIso F O₁ O₂ φ⟩

end

end SheafOfModules.RingedSite

/-! ### Lemma_18_33_6 (from Chap18) -/
open CategoryTheory
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v

-- Proof sketch: specialize Lemma `18.33.5` to the localization morphism of sites
-- `Over.forget U : Over U ⥤ C`. Its inverse-image on sheaves is the canonical localization
-- functor `J.overPullback`, so the pulled-back sheaf `(\Omega_{\mathcal O_2/\mathcal O_1}).over U`
-- is identified with the sheaf of relative differentials of the localized morphism
-- `\mathcal O_1|_U ⟶ \mathcal O_2|_U`; the compatibility with universal derivations is inherited
-- from the general inverse-image statement.
/-- Lemma 18.33.6: for any object `U` of a site `(\\mathcal C, J)`, the localization of the sheaf
of relative differentials `\Omega_{\mathcal O_2/\mathcal O_1}` to the slice site
`(\mathcal C/U, J.over U)` is canonically isomorphic to the sheaf of relative differentials of the
localized morphism `\mathcal O_1|_U \to \mathcal O_2|_U`, compatibly with universal
derivations. -/
theorem site_relative_differentials_over_has_universal_property
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (O₁ O₂ : Sheaf J CommRingCat.{max u v}) (φ : O₁ ⟶ O₂) (U : C) :
    IsIsomorphic
      ((SheafOfModules.toSheaf ((ringSheaf J O₂).over U)).obj
        ((Ω(φ)).over U))
      ((SheafOfModules.toSheaf (ringSheaf (J.over U) (O₂.over U))).obj
        (Ω(((J.overPullback CommRingCat.{max u v} U).map φ)))) :=
  sorry

/-! ### Lemma_18_33_7 (from Chap18) -/
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

/-! ### Lemma_18_33_8 (from Chap18) -/
open CategoryTheory
open PresheafOfModules.DifferentialsConstruction
open scoped SheafOfModules.RingedSite TensorProduct

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₁ O₂ O₂' : Sheaf J CommRingCat.{u}}

/- Domain-style sampling for Lemma 18.33.8:
- primary domain: the conormal exact sequence for a locally surjective morphism of sheaves of
  commutative rings on a Grothendieck site;
- sampled owner declarations:
  `ringedSiteStructureMap`,
  `Ω(φ)`,
  `KaehlerDifferential.kerCotangentToTensor`,
  `KaehlerDifferential.mapBaseChange`,
  `SheafOfModules.pullback`;
- best owner abstraction: the site-level scalar-extended conormal sequence of `O₂'`-module sheaves
  attached to a composable pair `φ : O₁ ⟶ O₂`, `α : O₂ ⟶ O₂'`;
- primitive data: the source-side kernel ideal presheaf of `α`, its cotangent presheaf
  `Ker(α)/Ker(α)^2` over `O₂`, and the canonical Kähler maps on sections;
- derived API: the sheaf-level maps
  `conormalMap φ α : conormalSource α ⟶ conormalTensorTerm φ α` and
  `conormalToDifferentials φ α : conormalTensorTerm φ α ⟶ Ω(φ ≫ α)`, their exactness under local
  surjectivity of `α`, and the objectwise formula sending the class of `f` to `1 ⊗ df`.

Source/core/bridge triage:
- `source-facing`: the scalar-extended conormal sequence
  `conormalSource α ⟶ O₂' ⊗[O₂] Ω(O₂/O₁) ⟶ Ω(O₂'/O₁) ⟶ 0`, which agrees with the textbook
  `Ker(α)/Ker(α)^2` sequence once local surjectivity identifies the left term with the intrinsic
  target-side conormal module;
- `core/canonical`: `Ω(φ)`, `ringedSiteStructureMap α`, `SheafOfModules.pullback`, and the
  ring-level Kähler maps from mathlib/Chapter 10;
- `bridge/view`: the objectwise section maps and the internal presheaf-level realizations used to
  build the sheaf morphisms.

Accordingly, this file keeps the scalar-extended sheaf-level conormal sequence as the public owner
and relegates the sectionwise maps to companion bridge API. It also reuses the chapter owner
`Ω(φ)` instead of rephrasing the lemma purely as objectwise ring statements. -/

/-- The underlying `RingCat`-sheaf morphism of a morphism of sheaves of commutative rings. -/
private abbrev ringSheafMap {O O' : Sheaf J CommRingCat.{u}} (α : O ⟶ O') :
    ringSheaf J O ⟶ ringSheaf J O' :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).map α

private abbrev conormalScalarPresheaf (α : O₂ ⟶ O₂') :
    PresheafOfModules (ringSheaf J O₂).obj :=
  (PresheafOfModules.restrictScalars (ringSheafMap α).hom).obj
    (PresheafOfModules.unit (ringSheaf J O₂').obj)

private abbrev conormalTensorSpacePresheaf (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    PresheafOfModules (ringSheaf J O₂).obj :=
  PresheafOfModules.Monoidal.tensorObj
    (conormalScalarPresheaf α)
    (relativeDifferentials' φ.hom)

private abbrev conormalTensorTermOverSource
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    SheafOfModules (ringSheaf J O₂) :=
  (PresheafOfModules.sheafification
      (𝟙 (ringSheaf J O₂).obj)).obj
    (conormalTensorSpacePresheaf φ α)

private abbrev conormalIdeal
    (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    Ideal (O₂.obj.obj U) :=
  RingHom.ker ((α.hom.app U).hom)

private theorem conormalIdeal_le_comap
    (α : O₂ ⟶ O₂') {U V : Cᵒᵖ} (i : U ⟶ V) :
    conormalIdeal α U ≤
      (conormalIdeal α V).comap ((O₂.obj.map i).hom) := by
  sorry

private abbrev conormalObj
    (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    ModuleCat (O₂.obj.obj U) :=
  ModuleCat.of (O₂.obj.obj U) (conormalIdeal α U).Cotangent

private abbrev conormalRestriction
    (α : O₂ ⟶ O₂') {U V : Cᵒᵖ} (i : U ⟶ V) :
    conormalObj α U ⟶
      (ModuleCat.restrictScalars
        (((ringSheaf J O₂).obj.map i).hom)).obj
        (conormalObj α V) :=
  let R := O₂.obj.obj U
  let S := O₂.obj.obj V
  let _ : Algebra R R := RingHom.toAlgebra (RingHom.id R)
  let _ : Algebra R S := (O₂.obj.map i).hom.toAlgebra
  ModuleCat.ofHom
    (Ideal.mapCotangent
      (conormalIdeal α U)
      (conormalIdeal α V)
      { toRingHom := (O₂.obj.map i).hom
        commutes' := by
          intro r
          rfl }
      (conormalIdeal_le_comap α i))

private theorem conormalRestriction_id
    (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    conormalRestriction α (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        (((ringSheaf J O₂).obj.map (𝟙 U)).hom)
        (congrArg RingCat.Hom.hom
          ((ringSheaf J O₂).obj.map_id U))).inv.app
        (conormalObj α U) := by
  sorry

private theorem conormalRestriction_comp
    (α : O₂ ⟶ O₂') {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    conormalRestriction α (i ≫ j) =
      conormalRestriction α i ≫
        (ModuleCat.restrictScalars
          (((ringSheaf J O₂).obj.map i).hom)).map
          (conormalRestriction α j) ≫
        (ModuleCat.restrictScalarsComp'
          (((ringSheaf J O₂).obj.map i).hom)
          (((ringSheaf J O₂).obj.map j).hom)
          (((ringSheaf J O₂).obj.map (i ≫ j)).hom)
          (congrArg RingCat.Hom.hom
            ((ringSheaf J O₂).obj.map_comp i j))).inv.app
          (conormalObj α W) := by
  sorry

private def conormalPresheaf (α : O₂ ⟶ O₂') :
    PresheafOfModules (ringSheaf J O₂).obj :=
  { obj := conormalObj α
    map := conormalRestriction α
    map_id := conormalRestriction_id α
    map_comp := conormalRestriction_comp α }

private noncomputable def conormalSourceOverSource
    (α : O₂ ⟶ O₂') :
    SheafOfModules (ringSheaf J O₂) :=
  (PresheafOfModules.sheafification
      (𝟙 (ringSheaf J O₂).obj)).obj
    (conormalPresheaf α)

/-- The objectwise left map in the conormal sequence on sections over `U`. -/
abbrev sectionConormalMap
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
    (RingHom.ker ((α.hom.app U).hom)).Cotangent →ₗ[O₂.obj.obj U]
      O₂'.obj.obj U ⊗[O₂.obj.obj U] Ω[O₂.obj.obj U⁄O₁.obj.obj U] :=
  let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
  let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
  KaehlerDifferential.kerCotangentToTensor
    (O₁.obj.obj U) (O₂.obj.obj U) (O₂'.obj.obj U)

private abbrev sectionConormalHom
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    conormalObj α U ⟶
      (conormalTensorSpacePresheaf φ α).obj U := by
  let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
  let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
  change conormalObj α U ⟶
    ModuleCat.of (O₂.obj.obj U)
      (O₂'.obj.obj U ⊗[O₂.obj.obj U] Ω[O₂.obj.obj U⁄O₁.obj.obj U])
  exact ModuleCat.ofHom (sectionConormalMap φ α U)

private theorem sectionConormalHom_naturality
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') {U V : Cᵒᵖ} (i : U ⟶ V) :
    (conormalPresheaf α).map i ≫
        (ModuleCat.restrictScalars
          (((ringSheaf J O₂).obj.map i).hom)).map
          (sectionConormalHom φ α V) =
      sectionConormalHom φ α U ≫
        (conormalTensorSpacePresheaf φ α).map i := by
  sorry

private def conormalPresheafHom
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    conormalPresheaf α ⟶ conormalTensorSpacePresheaf φ α where
  app U := sectionConormalHom φ α U
  naturality i := sectionConormalHom_naturality φ α i

private noncomputable def conormalMapOverSource
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    conormalSourceOverSource α ⟶
      conormalTensorTermOverSource φ α :=
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf J O₂).obj)).homEquiv
      (conormalPresheaf α)
      (conormalTensorTermOverSource φ α)).symm
    (conormalPresheafHom φ α ≫
      by
        simpa [conormalTensorTermOverSource, conormalTensorSpacePresheaf] using
          (PresheafOfModules.sheafificationAdjunction
            (𝟙 (ringSheaf J O₂).obj)).unit.app
            (conormalTensorSpacePresheaf φ α))

/-- The objectwise right map in the conormal sequence on sections over `U`. -/
abbrev sectionBaseChangeMap
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
    let _ : Algebra (O₁.obj.obj U) (O₂'.obj.obj U) :=
      (((α.hom.app U).hom).comp ((φ.hom.app U).hom)).toAlgebra
    let _ : IsScalarTower (O₁.obj.obj U) (O₂.obj.obj U) (O₂'.obj.obj U) :=
      IsScalarTower.of_algebraMap_eq' rfl
    O₂'.obj.obj U ⊗[O₂.obj.obj U] Ω[O₂.obj.obj U⁄O₁.obj.obj U] →ₗ[O₂'.obj.obj U]
      Ω[O₂'.obj.obj U⁄O₁.obj.obj U] :=
  let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
  let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
  let _ : Algebra (O₁.obj.obj U) (O₂'.obj.obj U) :=
    (((α.hom.app U).hom).comp ((φ.hom.app U).hom)).toAlgebra
  let _ : IsScalarTower (O₁.obj.obj U) (O₂.obj.obj U) (O₂'.obj.obj U) :=
    IsScalarTower.of_algebraMap_eq' rfl
  KaehlerDifferential.mapBaseChange
    (O₁.obj.obj U) (O₂.obj.obj U) (O₂'.obj.obj U)

private theorem conormalTensorSpacePresheaf_obj_eq
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
    (conormalTensorSpacePresheaf φ α).obj U =
      ModuleCat.of (O₂.obj.obj U)
        (O₂'.obj.obj U ⊗[O₂.obj.obj U] Ω[O₂.obj.obj U⁄O₁.obj.obj U]) := by
  sorry

private theorem restrictedDifferentialsPresheaf_obj_eq
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
    let _ : Algebra (O₁.obj.obj U) (O₂'.obj.obj U) :=
      (((α.hom.app U).hom).comp ((φ.hom.app U).hom)).toAlgebra
    ((PresheafOfModules.restrictScalars (ringSheafMap α).hom).obj
      (relativeDifferentials' (φ ≫ α).hom)).obj U =
      ModuleCat.of (O₂.obj.obj U) Ω[O₂'.obj.obj U⁄O₁.obj.obj U] := by
  sorry

private abbrev sectionBaseChangeHom
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    (conormalTensorSpacePresheaf φ α).obj U ⟶
      ((PresheafOfModules.restrictScalars (ringSheafMap α).hom).obj
        (relativeDifferentials' (φ ≫ α).hom)).obj U := by
  let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
  let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
  let _ : Algebra (O₁.obj.obj U) (O₂'.obj.obj U) :=
    (((α.hom.app U).hom).comp ((φ.hom.app U).hom)).toAlgebra
  let _ : IsScalarTower (O₁.obj.obj U) (O₂.obj.obj U) (O₂'.obj.obj U) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact
    eqToHom (conormalTensorSpacePresheaf_obj_eq φ α U) ≫
      ModuleCat.ofHom
        ((sectionBaseChangeMap φ α U).restrictScalars (O₂.obj.obj U)) ≫
      eqToHom (restrictedDifferentialsPresheaf_obj_eq φ α U).symm

private def tensorToDifferentialsPresheafHom
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    conormalTensorSpacePresheaf φ α ⟶
      (PresheafOfModules.restrictScalars (ringSheafMap α).hom).obj
        (relativeDifferentials' (φ ≫ α).hom) where
  app U := sectionBaseChangeHom φ α U
  naturality := by
    intro U V i
    sorry

private abbrev restrictedDifferentialsUnit
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    (PresheafOfModules.restrictScalars (ringSheafMap α).hom).obj
        (relativeDifferentials' (φ ≫ α).hom) ⟶
      ((restrictionAlong α).obj Ω(φ ≫ α)).val :=
  (PresheafOfModules.restrictScalars (ringSheafMap α).hom).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O₂').obj)).unit.app
      (relativeDifferentials' (φ ≫ α).hom))

private noncomputable def tensorToDifferentialsOverSource
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    conormalTensorTermOverSource φ α ⟶
      (restrictionAlong α).obj Ω(φ ≫ α) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O₂).obj)).homEquiv
      (conormalTensorSpacePresheaf φ α)
      ((restrictionAlong α).obj Ω(φ ≫ α))).symm
    (tensorToDifferentialsPresheafHom φ α ≫
      restrictedDifferentialsUnit φ α)

private abbrev conormalPullback (α : O₂ ⟶ O₂') :
    SheafOfModules (ringSheaf J O₂) ⥤
      SheafOfModules (ringSheaf J O₂') :=
  SheafOfModules.pullback (ringedSiteStructureMap α)

/-- The pullback of the source-side conormal module `Ker(α) / Ker(α)^2` along `α`, viewed as a
sheaf of `O₂'`-modules.

This is the scalar-extended left term used in the site-level conormal sequence below. When `α` is
locally surjective, it models the textbook `O₂'`-module conormal sheaf. -/
abbrev conormalSource
    (α : O₂ ⟶ O₂') :
    SheafOfModules (ringSheaf J O₂') :=
  (conormalPullback α).obj (conormalSourceOverSource α)

/-- The tensor middle term `O₂' \otimes_{O₂} \Omega_{O₂/O₁}`, viewed as a sheaf of
`O₂'`-modules. -/
abbrev conormalTensorTerm
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    SheafOfModules (ringSheaf J O₂') :=
  (conormalPullback α).obj (conormalTensorTermOverSource φ α)

/-- The left map in the scalar-extended site-level conormal sequence attached to
`O₁ ⟶ O₂ ⟶ O₂'`. -/
noncomputable def conormalMap
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    conormalSource α ⟶ conormalTensorTerm φ α :=
  (conormalPullback α).map (conormalMapOverSource φ α)

/-- The canonical map `O₂' \otimes_{O₂} \Omega_{O₂/O₁} \to \Omega_{O₂'/O₁}`. -/
noncomputable def conormalToDifferentials
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    conormalTensorTerm φ α ⟶ Ω(φ ≫ α) :=
  ((SheafOfModules.pullbackPushforwardAdjunction
      (ringedSiteStructureMap α)).homEquiv
      (conormalTensorTermOverSource φ α)
      Ω(φ ≫ α)).symm
    (tensorToDifferentialsOverSource φ α)

-- Proof sketch: the composite is obtained by sheafifying the objectwise identity
-- `mapBaseChange ∘ kerCotangentToTensor = 0`.
/-- The scalar-extended canonical conormal sequence of sheaves has zero composite. -/
theorem conormal_comp_zero
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    conormalMap φ α ≫ conormalToDifferentials φ α = 0 := by
  sorry

-- Proof sketch: let `O₂''` be the image presheaf of `α.hom`. Algebra, Lemma `10.131.9` gives the
-- exact objectwise sequences for `O₂(U) → O₂''(U)`. Sheafifying those sequences and using local
-- surjectivity of `α` identifies `(O₂'')^#` with `O₂'`; Lemma `18.33.4` identifies the
-- sheafification of the right term with `Ω(φ ≫ α)`.
/-- Lemma 18.33.8: if `α : O₂ ⟶ O₂'` is locally surjective, then the scalar-extended canonical
conormal sequence of `O₂'`-modules
`conormalSource α ⟶ O₂' \otimes_{O₂} \Omega_{O₂/O₁} ⟶ \Omega_{O₂'/O₁} ⟶ 0`
is exact.

Here `conormalSource α` is, by definition, the pullback along `α` of the source-side conormal
module `Ker(α)/Ker(α)^2`; under local surjectivity this matches the textbook target-side conormal
module. -/
theorem conormalSequence_exact
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂')
    (hα : Sheaf.IsLocallySurjective α) :
    (ShortComplex.mk
      (conormalMap φ α)
      (conormalToDifferentials φ α)
      (conormal_comp_zero φ α)).Exact ∧
      Epi (conormalToDifferentials φ α) := by
  sorry

-- Proof sketch: objectwise surjectivity is a special case of local surjectivity of sheaves, so
-- the main sheaf-level exactness theorem applies directly.
/-- Companion bridge: sectionwise-surjective maps satisfy the hypotheses of the scalar-extended
conormal exact sequence. -/
theorem conormalSequence_exact_of_sectionwiseSurjective
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂')
    (hα : ∀ U : Cᵒᵖ, Function.Surjective ((α.hom.app U).hom)) :
    (ShortComplex.mk
      (conormalMap φ α)
      (conormalToDifferentials φ α)
      (conormal_comp_zero φ α)).Exact ∧
      Epi (conormalToDifferentials φ α) := by
  have hloc : Sheaf.IsLocallySurjective α := by
    exact Presheaf.isLocallySurjective_of_surjective J α.hom hα
  exact conormalSequence_exact φ α hloc

-- Proof sketch: this is exactly
-- `KaehlerDifferential.kerCotangentToTensor_toCotangent` for the section ring map
-- `O₂(U) → O₂'(U)`.
/-- Lemma 18.33.8, formula for the left map: in library tensor order, the class of a local section
`f` of the kernel ideal over `U` maps to `1 ⊗ df`. -/
theorem sectionConormalMap_toCotangent
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') (U : Cᵒᵖ)
    (x : RingHom.ker ((α.hom.app U).hom)) :
    let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
    sectionConormalMap φ α U (Ideal.toCotangent (RingHom.ker ((α.hom.app U).hom)) x) =
      (1 : O₂'.obj.obj U) ⊗ₜ[O₂.obj.obj U]
        KaehlerDifferential.D (O₁.obj.obj U) (O₂.obj.obj U) x := by
  sorry

end SheafOfModules.RingedSite

/-! ### Lemma_18_33_9 (from Chap18) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open SheafOfModules.RingedSite
open scoped RelativeDerivation

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/-
Domain-style sampling for Lemma 18.33.9:
- primary domain: square-zero extensions of sheaves of commutative rings on a general site, their
  intrinsic kernel ideal sheaves, restriction of scalars for sheaves of modules on a ringed site,
  and relative derivations into the kernel ideal viewed as an `O₂`-module via a chosen section;
- sampled owner declarations:
  `CategoryTheory.Limits.kernel`,
  `SheafOfModules.RingedSite.restrictionAlong`,
  `SheafOfModules.unitToPushforwardObjUnit`,
  `SheafOfModules.RingedSite.ringedSiteStructureMap`,
  `Der[φ ; F]`;
- best owner abstraction: the intrinsic kernel ideal sheaf
  `kernel (SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap π))` as an
  `A`-module, with the `O₂`-module structure for a fixed section `s : O₂ ⟶ A` obtained by the
  canonical owner `restrictionAlong s`;
- primitive data: the maps `φ : O₁ ⟶ O₂`, `ψ : O₁ ⟶ A`, `π : A ⟶ O₂`, one compatible section
  `s`, and the square-zero condition on the actual kernel ideal of `π`;
- derived API: compatible algebra sections, perturbations by derivations into the intrinsic kernel,
  and the torsor-style existence and uniqueness statements.

Source/core/bridge triage:
- `source-facing`: compatible algebra sections and their difference-by-a-derivation relation;
- `core/canonical`: `kernel`, `kernel.ι`, `restrictionAlong`, and
  `Der[φ ; F]`;
- `bridge/view`: the restriction-of-scalars identification sending an `A`-module sheaf to an
  `O₂`-module sheaf along a fixed section `s : O₂ ⟶ A`.

This file therefore refines to the intrinsic kernel owner `Ker π`, with its theorem-facing
`O₂`-module structure obtained directly from the canonical owner `restrictionAlong`, rather than
from auxiliary sectionwise lift data. -/

variable {O₁ O₂ A : Sheaf J CommRingCat.{u}}
variable (φ : O₁ ⟶ O₂) (ψ : O₁ ⟶ A) (π : A ⟶ O₂)

/-- A section of `π` compatible with the `O₁`-algebra structures on `A` and `O₂`. -/
abbrev IsAlgebraSection (s : O₂ ⟶ A) : Prop :=
  s ≫ π = 𝟙 O₂ ∧ φ ≫ s = ψ

variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

private abbrev structureSheafQuotient (π : A ⟶ O₂) :
    SheafOfModules.unit (ringSheaf J A) ⟶
      (SheafOfModules.pushforward (ringedSiteStructureMap π)).obj
        (SheafOfModules.unit (ringSheaf J O₂)) :=
  SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap π)

/-- The intrinsic kernel ideal sheaf of `π`, viewed as an `A`-module sheaf. -/
abbrev kernelIdealSheaf (π : A ⟶ O₂) : SheafOfModules (ringSheaf J A) :=
  kernel (structureSheafQuotient π)

/-- The canonical inclusion of `Ker π` into `A`. -/
abbrev kernelIdealInclusion (π : A ⟶ O₂) :
    kernelIdealSheaf π ⟶ SheafOfModules.unit (ringSheaf J A) :=
  kernel.ι (structureSheafQuotient π)

/-- The sectionwise inclusion of `Ker π` into `A`. -/
abbrev kernelIdealInclusionApp
    (π : A ⟶ O₂)
    (U : Cᵒᵖ) (x : (kernelIdealSheaf π).val.obj U) : A.obj.obj U :=
  show A.obj.obj U from (kernelIdealInclusion π).val.app U x

/-- The intrinsic kernel ideal of `π` has square zero when products of local kernel sections vanish
in `A`. -/
abbrev KernelSquareZero (π : A ⟶ O₂) : Prop :=
  ∀ U : Cᵒᵖ, ∀ x y : (kernelIdealSheaf π).val.obj U,
    kernelIdealInclusionApp π U x * kernelIdealInclusionApp π U y = 0

/-- The kernel ideal sheaf of `π`, viewed as an `O₂`-module by restricting scalars along a fixed
section `s : O₂ ⟶ A`. -/
abbrev kernelIdealSheafModule
    (π : A ⟶ O₂) (s : O₂ ⟶ A) :
    SheafOfModules (ringSheaf J O₂) :=
  (restrictionAlong s).obj (kernelIdealSheaf π)

/-- A section `s'` differs from `s` by the derivation `D` when their local sections satisfy the
pointwise formula `s' = s + D` through the canonical inclusion `Ker π ↪ A`. -/
abbrev IsSectionPerturbation
    (φ : O₁ ⟶ O₂) (π : A ⟶ O₂)
    (s s' : O₂ ⟶ A)
    (D : Der[φ ; kernelIdealSheafModule π s]) : Prop :=
  ∀ U : Cᵒᵖ, ∀ x : O₂.obj.obj U,
    s'.hom.app U x = s.hom.app U x +
      kernelIdealInclusionApp π U (show (kernelIdealSheaf π).val.obj U from D.d x)

-- Proof sketch: define the candidate section pointwise by `s + D`; the Leibniz rule and the
-- square-zero condition show that this is again a morphism of sheaves of rings, while the
-- derivation vanishes on `O₁` and lands in `Ker π`, giving the compatibility and section
-- identities. Uniqueness follows from extensionality of sheaf morphisms.
/-- Lemma 18.33.9 (1), existence-and-uniqueness form: a derivation into the intrinsic square-zero
kernel ideal determines a unique compatible section obtained by adding that derivation to a fixed
compatible section. -/
theorem existsUnique_algebraSection_of_derivation
    (s : O₂ ⟶ A) (hs : IsAlgebraSection φ ψ π s)
    (hzero : KernelSquareZero π)
    (D : Der[φ ; kernelIdealSheafModule π s]) :
    ∃! s' : O₂ ⟶ A,
      IsAlgebraSection φ ψ π s' ∧
        IsSectionPerturbation φ π s s' D := sorry

/-- The canonical section obtained from `s` by adding the derivation `D` in the square-zero kernel
ideal of `π`. -/
noncomputable def algebraSectionOfDerivation
    (s : O₂ ⟶ A) (hs : IsAlgebraSection φ ψ π s)
    (hzero : KernelSquareZero π)
    (D : Der[φ ; kernelIdealSheafModule π s]) :
    O₂ ⟶ A :=
  Classical.choose
    (existsUnique_algebraSection_of_derivation φ ψ π s hs hzero D)

private theorem algebraSectionOfDerivation_hasProperty
    (s : O₂ ⟶ A) (hs : IsAlgebraSection φ ψ π s)
    (hzero : KernelSquareZero π)
    (D : Der[φ ; kernelIdealSheafModule π s]) :
    IsAlgebraSection φ ψ π (algebraSectionOfDerivation φ ψ π s hs hzero D) ∧
      IsSectionPerturbation φ π s (algebraSectionOfDerivation φ ψ π s hs hzero D) D := by
  exact (Classical.choose_spec
    (existsUnique_algebraSection_of_derivation φ ψ π s hs hzero D)).1

/-- Lemma 18.33.9 (1): starting from a compatible algebra section `s`, a derivation into the
intrinsic square-zero kernel ideal of `π` produces the actual translated section `s + D`. -/
lemma derivation_yields_algebraSection
    (s : O₂ ⟶ A) (hs : IsAlgebraSection φ ψ π s)
    (hzero : KernelSquareZero π)
    (D : Der[φ ; kernelIdealSheafModule π s]) :
    IsAlgebraSection φ ψ π (algebraSectionOfDerivation φ ψ π s hs hzero D) ∧
      IsSectionPerturbation φ π s (algebraSectionOfDerivation φ ψ π s hs hzero D) D := by
  exact algebraSectionOfDerivation_hasProperty φ ψ π s hs hzero D

-- Proof sketch: for a second compatible section `s'`, the pointwise difference `s' - s` lands in
-- the actual kernel ideal sheaf because both sections split `π`. The square-zero hypothesis and
-- the ring-hom identities for `s` and `s'` then show that this lifted difference is a relative
-- derivation into `Ker π`, and uniqueness follows from the monicity of `kernel.ι`.
/-- Lemma 18.33.9 (2): relative to a fixed compatible section `s`, every other compatible section
arises from a unique derivation with values in the intrinsic square-zero kernel sheaf `Ker π`,
viewed as its descended canonical `O₂`-module. -/
lemma existsUnique_derivation_of_algebraSection
    (s s' : O₂ ⟶ A)
    (hs : IsAlgebraSection φ ψ π s)
    (hs' : IsAlgebraSection φ ψ π s')
    (hzero : KernelSquareZero π) :
    ∃! D : Der[φ ; kernelIdealSheafModule π s],
      IsSectionPerturbation φ π s s' D := sorry

end

/-! ### Definition_18_33_10 (from Chap18) -/
open CategoryTheory
open SheafOfModules.RingedSite
open scoped RelativeDerivation RingedSite.Hom

noncomputable section

universe u

namespace RingedSite.Hom

section

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf JC CommRingCat.{u}} {𝒪' : Sheaf JD CommRingCat.{u}}

local notation "X" => RingedSite.ofCommRingSheaf JC 𝒪
local notation "Y" => RingedSite.ofCommRingSheaf JD 𝒪'

/- Domain-style sampling for Definition 18.33.10:
- primary domain: relative differentials for a morphism of ringed topoi presented by a bundled
  morphism of ringed sites;
- sampled owner declarations:
  `RingedSite.Hom.inverseImageStructureSheafMap`,
  `SheafOfModules.RingedSite.relativeDifferentials`,
  `SheafOfModules.RingedSite.relativeDifferential`,
  `AlgebraicGeometry.RingedSpace.differentials`;
- best owner abstraction: the bundled morphism `f : X ⟶ Y`, with source-facing surface
  `Ω[f] = Ω_{X/Y}` and `d[f]`;
- primitive data: only the bundled morphism `f : X ⟶ Y`;
- derived API: the inverse-image structure-sheaf map `inverseImageStructureSheafMap f`, the sheaf
  of differentials `Ω[f]`, the relative derivation type `Derivation f F`, and the universal
  derivation `d[f]`.

Source/core/bridge triage:
- `source-facing`: the owner `Ω[f]` and universal derivation `d[f]` for a morphism of ringed
  sites `f : X ⟶ Y`;
- `core/canonical`: `SheafOfModules.RingedSite.relativeDifferentials` and
  `SheafOfModules.RingedSite.relativeDifferential`;
- `bridge/view`: `inverseImageStructureSheafMap f : f⁻¹𝒪_Y ⟶ 𝒪_X`.

This file therefore upgrades the public API from the bridge datum `f⁻¹𝒪_Y ⟶ 𝒪_X` to the bundled
owner `f : X ⟶ Y`, matching Chapter 17's source-facing differentials surface. -/

/-- Definition 18.33.10: the sheaf of relative differentials of a bundled morphism of ringed
sites `f : X ⟶ Y`. -/
abbrev differentials (f : X ⟶ Y) : SheafOfModules (ringSheaf JC 𝒪) :=
  Ω(inverseImageStructureSheafMap f)

scoped[RingedSite.Hom] notation3:max "Ω[" f "]" => RingedSite.Hom.differentials f

/-- The type of relative derivations from `\mathcal O_X` to an `\mathcal O_X`-module along
`f : X ⟶ Y`. -/
abbrev Derivation (f : X ⟶ Y) (F : SheafOfModules (ringSheaf JC 𝒪)) : Type _ :=
  Der[inverseImageStructureSheafMap f ; F]

/-- The sheaf of differentials of a bundled morphism is the generic owner specialized along its
inverse-image structure-sheaf map. -/
theorem differentials_def (f : X ⟶ Y) :
    Ω[f] = Ω(inverseImageStructureSheafMap f) :=
  rfl

/-- The universal derivation `d_{X/Y} : \mathcal O_X \to Ω_{X/Y}` attached to a bundled morphism
of ringed sites. -/
abbrev differential (f : X ⟶ Y) : Derivation f Ω[f] :=
  relativeDifferential (inverseImageStructureSheafMap f)

scoped[RingedSite.Hom] notation3:max "d[" f "]" => RingedSite.Hom.differential f

end

end RingedSite.Hom
