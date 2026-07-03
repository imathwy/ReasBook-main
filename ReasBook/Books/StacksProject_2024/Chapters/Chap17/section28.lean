import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_17_28_1 (from Chap17) -/
open CategoryTheory TopCat

universe u v

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {O₁ O₂ : Sheaf J CommRingCat}
variable (φ : O₁ ⟶ O₂)
variable (F : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O₂))

/-- The sheaf-level type of `φ`-derivations `O₂ → F`. This is the source-facing specialization of
the canonical owner `PresheafOfModules.Derivation'`; in the notation of the Stacks Project, it
realizes `Der_{O₁}(O₂, F)` while keeping the structural morphism `φ : O₁ ⟶ O₂` explicit. -/
abbrev RelativeDerivation : Type _ :=
  F.val.Derivation' φ.hom

end SheafOfModules

namespace RelativeDerivation

scoped notation "Der[" φ " ; " F "]" => SheafOfModules.RelativeDerivation φ F

end RelativeDerivation

/-- Postcomposition of a sheaf-level relative derivation by a morphism of sheaves of modules. -/
abbrev RelativeDerivation.postcomp
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {O₁ O₂ : Sheaf J CommRingCat} {φ : O₁ ⟶ O₂}
    {R : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O₂)}
    {F : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O₂)}
    (d : SheafOfModules.RelativeDerivation φ R) (α : R ⟶ F) :
    SheafOfModules.RelativeDerivation φ F :=
  d.postcomp α.val

open scoped RelativeDerivation

variable {X : TopCat.{u}}
variable (O₁ O₂ : TopCat.Sheaf CommRingCat.{u} X)
variable (φ : O₁ ⟶ O₂)
variable (F : SheafOfModules ((sheafCompose (Opens.grothendieckTopology X)
  (forget₂ CommRingCat RingCat)).obj O₂))

/- Domain-style sampling for Definition 17.28.1:
- primary domain: relative derivations of presheaves/sheaves of modules over a sheaf of rings;
- sampled owner declarations:
  `PresheafOfModules.Derivation'`,
  `SheafOfModules.RelativeDerivation`,
  `PresheafOfModules.Derivation'.app`,
  `PresheafOfModules.DifferentialsConstruction.derivation'`,
  `PresheafOfModules.Derivation'.Universal.mk`;
- owner abstraction: `PresheafOfModules.Derivation'`;
- primitive data: the additive map on local sections, together with vanishing on the image of
  `O₁` and the Leibniz rule;
- derived API: the sheaf-level bridge `SheafOfModules.RelativeDerivation` with notation
  `Der[φ ; F]`, evaluation on opens via `Derivation'.app`, the sheaf-level bridge
  `RelativeDerivation.postcomp`, and the universal
  structure used to define relative differentials.

Source/core/bridge triage:
- `core/canonical`: `PresheafOfModules.Derivation'`;
- `bridge/view`: `SheafOfModules.RelativeDerivation φ F` and the notation `Der[φ ; F]`;
- this item is the source-facing sheaf-level specialization of the canonical owner, not a second
  root owner. -/

/- Definition 17.28.1: for a topological space `X`, a morphism `φ : O₁ ⟶ O₂` of sheaves of
commutative rings on `X`, and an `O₂`-module sheaf `F`, the source-facing type
`Der[φ ; F]` is the sheaf-level specialization of the canonical owner
`PresheafOfModules.Derivation'` that realizes
`Der_{O₁}(O₂, F)`. -/
#check Der[φ ; F]

/- Companion recall: the owner of relative derivations on presheaves of modules is
`PresheafOfModules.Derivation'`. -/
recall PresheafOfModules.Derivation'

/-! ### Lemma_17_28_2 (from Chap17) -/
/- Domain-style sampling for Lemma 17.28.2:
- primary domain: sheafified relative differentials and their universal derivation on a
  topological space;
- sampled owner declarations:
  `TopCat.Sheaf.relativeDifferentials`,
  `TopCat.Sheaf.relativeDifferential`,
  `TopCat.Sheaf.relativeDifferentials_representsDerivations`,
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`;
- best owner abstraction: `TopCat.Sheaf.relativeDifferentials`, together with its universal
  derivation `TopCat.Sheaf.relativeDifferential`;
- primitive data: the sheafification of the presheaf of relative differentials and the induced
  universal derivation;
- derived API: the representing theorem
  `TopCat.Sheaf.relativeDifferentials_representsDerivations`.

Source/core/bridge triage:
- `source-facing`: `TopCat.Sheaf.relativeDifferentials` with
  `TopCat.Sheaf.relativeDifferential`;
- this file is a recall-only reuse of the owner theorem
  `TopCat.Sheaf.relativeDifferentials_representsDerivations`, not a second owner. -/

/- Lemma 17.28.2: the universal property of the sheaf of relative differentials on a topological
space is already owned by `TopCat.Sheaf.relativeDifferentials_representsDerivations` from Definition
`17.28.3`. -/
recall TopCat.Sheaf.relativeDifferentials_representsDerivations

/-! ### Definition_17_28_3 (from Chap17) -/
open CategoryTheory TopCat TopologicalSpace
open PresheafOfModules
open PresheafOfModules.DifferentialsConstruction
open TopCat.Sheaf
open RelativeDerivation
open scoped RelativeDerivation

universe u

noncomputable section

variable {X : TopCat.{u}}
variable {O₁ O₂ : TopCat.Sheaf CommRingCat.{u} X}
variable (φ : O₁ ⟶ O₂)

namespace TopCat.Sheaf

/- Domain-style sampling for Definition 17.28.3:
- primary domain: sheafified relative differentials of sheaves of commutative rings on a
  topological space;
- sampled owner declarations:
  `PresheafOfModules.sheafificationAdjunction`,
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`,
  `PresheafOfModules.DifferentialsConstruction.derivation'`,
  `PresheafOfModules.DifferentialsConstruction.isUniversal'`,
  `TopCat.Sheaf.relativeDifferentialDesc`;
- best owner abstraction: the source-facing sheafified owner
  `TopCat.Sheaf.relativeDifferentials`, obtained from the canonical presheaf differentials owner by
  sheafification;
  `relativeDifferentials' φ.hom`, the sheafified module `relativeDifferentials`, and its
  universal derivation `relativeDifferential`;
- derived API: the definitional sheafification theorem `relativeDifferentials_def`, the descended
  universal morphism `relativeDifferentialDesc`, its factorization and injectivity lemmas, and the
  representing theorem
  `relativeDifferentials_representsDerivations`.

Source/core/bridge triage:
- `core/canonical`: the presheaf owner
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`;
- `source-facing`: the sheafified owner `TopCat.Sheaf.relativeDifferentials`;
- `bridge/view`: the sheafification descent API from the presheaf universal derivation to sheaf
  targets;
- this file owns the sheaf-level construction and its primitive support data, so downstream files
  should reuse these declarations rather than reintroduce local copies. -/

/-- A sheaf of commutative rings on `X`, viewed as a sheaf with values in `RingCat`. -/
abbrev ringSheaf (O : TopCat.Sheaf CommRingCat.{u} X) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat)).obj O

/-- The underlying morphism of `RingCat`-valued sheaves induced by a morphism of sheaves of
commutative rings. -/
abbrev ringSheafMap {O O' : TopCat.Sheaf CommRingCat.{u} X} (α : O ⟶ O') :
    ringSheaf O ⟶ ringSheaf O' :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat)).map α

/-- Definition 17.28.3: for a morphism `φ : 𝒪₁ ⟶ 𝒪₂` of sheaves of rings on a topological
space, the module of differentials `Ω_{𝒪₂/𝒪₁}` is the sheaf representing the functor
`ℱ ↦ Der_{𝒪₁}(𝒪₂, ℱ)`. -/
noncomputable def relativeDifferentials :
    SheafOfModules (ringSheaf O₂) :=
  (PresheafOfModules.sheafification
      (𝟙 (ringSheaf O₂).obj)).obj
    (relativeDifferentials' φ.hom)

@[inherit_doc relativeDifferentials]
notation:max "Ω(" φ ")" => relativeDifferentials φ

/-- The sheaf of relative differentials is the sheafification of the presheaf of objectwise
Kähler differentials. -/
theorem relativeDifferentials_def :
    Ω(φ) =
      (PresheafOfModules.sheafification (𝟙 (ringSheaf O₂).obj)).obj
        (relativeDifferentials' φ.hom) := rfl

/-- The universal `φ`-derivation from `O₂` to `Ω(φ)`. -/
noncomputable def relativeDifferential :
    Der[φ ; Ω(φ)] :=
  (derivation' φ.hom).postcomp
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf O₂).obj)).unit.app
      (relativeDifferentials' φ.hom))

/-- The descended morphism induced by a `φ`-derivation into a sheaf of modules. -/
noncomputable def relativeDifferentialDesc
    {F : SheafOfModules (ringSheaf O₂)} (D : Der[φ ; F]) :
    Ω(φ) ⟶ F :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).homEquiv
    (relativeDifferentials' φ.hom) F).symm
      ((isUniversal' φ.hom).desc D)

-- Proof sketch: `relativeDifferentialDesc` is obtained by transporting the presheaf-level
-- universal morphism across the sheafification adjunction, so the factorization identity is the
-- adjoint form of `isUniversal' φ.hom |>.fac`.
/-- The descended morphism factors the target derivation through the universal derivation. -/
theorem relativeDifferentialDesc_fac
    {F : SheafOfModules (ringSheaf O₂)} (D : Der[φ ; F]) :
    RelativeDerivation.postcomp (relativeDifferential φ)
      (relativeDifferentialDesc φ D) = D := sorry

-- Proof sketch: uniqueness is inherited from the presheaf-level universal property after applying
-- the sheafification adjunction equivalence.
/-- A morphism out of `Ω(φ)` is determined by its postcomposition with the universal
derivation. -/
theorem relativeDifferential_postcomp_injective
    {F : SheafOfModules (ringSheaf O₂)} ⦃α β : Ω(φ) ⟶ F⦄
    (h : RelativeDerivation.postcomp (relativeDifferential φ) α =
      RelativeDerivation.postcomp (relativeDifferential φ) β) :
    α = β := sorry

/-- The sheaf of relative differentials represents `O₁`-derivations out of `O₂`. -/
theorem relativeDifferentials_representsDerivations
    (F : SheafOfModules (ringSheaf O₂)) (D : Der[φ ; F]) :
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

end TopCat.Sheaf

/-! ### Lemma_17_28_4 (from Chap17) -/
/- Domain-style sampling for Lemma 17.28.4:
- primary domain: sheafified relative differentials of sheaves of commutative rings on a
  topological space;
- sampled owner declarations:
  `TopCat.Sheaf.relativeDifferentials`,
  `TopCat.Sheaf.relativeDifferentials_def`,
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`;
- best owner abstraction: the source-facing owner `TopCat.Sheaf.relativeDifferentials`;
- primitive data: the owner `TopCat.Sheaf.relativeDifferentials` itself;
- derived API: its defining sheafification equation
  `TopCat.Sheaf.relativeDifferentials_def`.

Source/core/bridge triage:
- `source-facing`: `TopCat.Sheaf.relativeDifferentials`;
- `bridge/view`: `TopCat.Sheaf.relativeDifferentials_def`;
- this file is a recall-only reuse of the owner theorem from `Definition_17_28_3`, not a second
  owner declaration. -/

/- Lemma 17.28.4: the sheaf of relative differentials `Ω_{O₂/O₁}` on a topological space is
already canonically owned by `TopCat.Sheaf.relativeDifferentials`, and its associated-sheaf
presentation is exactly `TopCat.Sheaf.relativeDifferentials_def`. -/
recall TopCat.Sheaf.relativeDifferentials_def

/-! ### Lemma_17_28_5 (from Chap17) -/
open CategoryTheory TopCat TopologicalSpace
open TopCat.Sheaf

noncomputable section

universe u

variable {X : TopCat.{u}}

/- Domain-style sampling for Lemma 17.28.5:
- primary domain: restriction of sheaves of relative differentials to an open subset;
- sampled owner declarations:
  `TopCat.Sheaf.relativeDifferentials`,
  `TopCat.Sheaf.inverseImage_relativeDifferentialsIso`,
  `TopCat.Sheaf.pullback`,
  `moduleSheafRestrictionToOpen`;
- best owner abstraction: the owner-level inverse-image comparison
  `TopCat.Sheaf.inverseImage_relativeDifferentialsIso`, with this file keeping only the
  open-inclusion specialization written through the Chapter 6 restriction functor;
- primitive data: the owner `relativeDifferentials` and the canonical restriction functor
  `moduleSheafRestrictionToOpen`;
- derived API: the restriction comparison theorem below.

Source/core/bridge triage:
- `core/canonical`: `TopCat.Sheaf.relativeDifferentials` and its generic inverse-image comparison
  `TopCat.Sheaf.inverseImage_relativeDifferentialsIso`;
- `bridge/view`: this file rewrites that generic comparison for the open inclusion
  `U.inclusion'` and the source-facing restriction functor notation;
- the former local pullback/sheafification transport lemmas duplicated the owner theorem from
  Lemma `17.28.6`, so they should be deleted rather than maintained in parallel. -/

/-- Lemma 17.28.5: for an open subset `U ⊆ X`, the restriction of the sheaf of relative
differentials `Ω(φ)` is canonically isomorphic to the canonical relative-differentials owner for
the restricted morphism, specialized from
`TopCat.Sheaf.inverseImage_relativeDifferentialsIso` along the open inclusion `U ↪ X`. -/

theorem sheaf_relative_differentials_restrict_isIsomorphic
    (U : Opens X) {O₁ O₂ : TopCat.Sheaf CommRingCat.{u} X} (φ : O₁ ⟶ O₂) :
    IsIsomorphic ((moduleSheafRestrictionToOpen U (ringSheaf O₂)).obj Ω(φ))
      ((SheafOfModules.restrictScalars
          (pullbackRingSheafIso U.inclusion' O₂).inv).obj
        Ω((pullback CommRingCat.{u} U.inclusion').map φ)) := by
  exact ⟨by
    simpa [moduleSheafRestrictionToOpen] using
      inverseImage_relativeDifferentialsIso U.inclusion' φ⟩

/-! ### Lemma_17_28_6 (from Chap17) -/
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

/-! ### Lemma_17_28_7 (from Chap17) -/
open CategoryTheory TopCat TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/- Domain-style sampling for Lemma 17.28.7:
- primary domain: stalks of sheaves of relative differentials on a topological space;
- sampled owner declarations:
  `TopCat.Sheaf.relativeDifferentials`,
  `TopCat.Sheaf.relativeDifferentials_stalkIso`,
  `CommRingCat.KaehlerDifferential`,
  `TopCat.Presheaf.stalkFunctor`;
- best owner abstraction: the source-facing sheaf owner `Ω(φ)`, with the stalk comparison already
  exposed canonically by `TopCat.Sheaf.relativeDifferentials_stalkIso`;
- primitive data: none beyond that owner comparison;
- derived API: this file is recall-only.

Source/core/bridge triage:
- `source-facing`: the textbook stalk formula `(Ω_{O₂/O₁})_x ≅ Ω_{(O₂)_x/(O₁)_x}`;
- `core/canonical`: `Ω(φ)` and the canonical bridge
  `TopCat.Sheaf.relativeDifferentials_stalkIso`;
- `bridge/view`: this file simply recalls that exact comparison in the relative-differentials
  vocabulary, rather than keeping a parallel local wrapper. -/

/- Lemma 17.28.7: the stalk of `Ω(φ)` at `x` is canonically isomorphic to the Kähler
differential module of the induced morphism on stalk rings. This is exactly the owner comparison
`TopCat.Sheaf.relativeDifferentials_stalkIso`; no second local wrapper is needed. -/
recall TopCat.Sheaf.relativeDifferentials_stalkIso

end TopCat.Sheaf

/-! ### Lemma_17_28_8 (from Chap17) -/
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

/-! ### Lemma_17_28_9 (from Chap17) -/
open CategoryTheory TopCat TopologicalSpace
open TopCat.Presheaf
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite TensorProduct

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₁ O₂ O₂' : X.Sheaf CommRingCat.{u}}

/- Domain-style sampling for Lemma 17.28.9:
- primary domain: the conormal exact sequence for a composable pair
  `O₁ ⟶ O₂ ⟶ O₂'` of sheaves of commutative rings on a fixed topological space;
- sampled owner declarations:
  `SheafOfModules.RingedSite.conormalMap`,
  `SheafOfModules.RingedSite.conormalToDifferentials`,
  `SheafOfModules.RingedSite.conormalSequence_exact`,
  `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`,
  `KaehlerDifferential.kerCotangentToTensor_toCotangent`;
- best owner abstraction: the generic-site owner in namespace
  `SheafOfModules.RingedSite`, specialized here to the opens site of `X`;
- primitive data: the composable morphisms `φ : O₁ ⟶ O₂` and `α : O₂ ⟶ O₂'`;
- derived API: the opens-site exactness theorem and the stalkwise Kähler recalls obtained by
  specializing to `stalkFunctor CommRingCat x`.

Source/core/bridge triage:
- `source-facing`: Lemma 17.28.9 on a topological space and its stalkwise reformulations;
- `core/canonical`: the generic-site conormal sequence owner in
  `SheafOfModules.RingedSite`;
- `bridge/view`: this file is only the opens-site specialization of the site-level owner; the
  stalk statements are companion recalls of the existing ring-level Kähler owners, not new theorem
  wrappers. -/

/-- Lemma 17.28.9: if `α : O₂ ⟶ O₂'` is surjective on stalks, then the canonical opens-site
conormal sequence of sheaves of `O₂'`-modules
`conormalSource α ⟶ O₂' ⊗[O₂] Ω_{O₂/O₁} ⟶ Ω_{O₂'/O₁} ⟶ 0`
is exact. -/
theorem conormalSequence_exact_of_stalkwise_surjective
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂')
    (hsurj : ∀ x : X, Function.Surjective ((stalkFunctor CommRingCat x).map α.hom).hom) :
    (ShortComplex.mk
      (conormalMap φ α)
      (conormalToDifferentials φ α)
      (conormal_comp_zero φ α)).Exact ∧
      Epi (conormalToDifferentials φ α) := by
  have hloc : Sheaf.IsLocallySurjective α := by
    exact (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks α.hom).2 hsurj
  simpa using SheafOfModules.RingedSite.conormalSequence_exact φ α hloc

private abbrev stalkRing (O : X.Sheaf CommRingCat.{u}) (x : X) : CommRingCat :=
  (stalkFunctor CommRingCat x).obj O.obj

private abbrev stalkRingHom {O O' : X.Sheaf CommRingCat.{u}} (β : O ⟶ O') (x : X) :
    stalkRing O x ⟶ stalkRing O' x :=
  (stalkFunctor CommRingCat x).map β.hom

section StalkRecalls

variable (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂')
variable (x : X)

/- Companion recall: at each stalk `x`, the ring-level exact conormal sequence is exactly the
Kähler owner pair
`KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange` and
`KaehlerDifferential.mapBaseChange_surjective` for the stalk map
`(stalkRingHom α x).hom`. -/
#check
  (fun hsurj : ∀ x : X, Function.Surjective ((stalkFunctor CommRingCat x).map α.hom).hom ↦
    let _ : Algebra (stalkRing O₁ x) (stalkRing O₂ x) := (stalkRingHom φ x).hom.toAlgebra
    let _ : Algebra (stalkRing O₂ x) (stalkRing O₂' x) := (stalkRingHom α x).hom.toAlgebra
    let _ : Algebra (stalkRing O₁ x) (stalkRing O₂' x) :=
      ((stalkRingHom α x).hom.comp (stalkRingHom φ x).hom).toAlgebra
    let _ : IsScalarTower (stalkRing O₁ x) (stalkRing O₂ x) (stalkRing O₂' x) :=
      IsScalarTower.of_algebraMap_eq' rfl
    show
        Function.Exact
            (KaehlerDifferential.kerCotangentToTensor
              (stalkRing O₁ x) (stalkRing O₂ x) (stalkRing O₂' x))
            (KaehlerDifferential.mapBaseChange
              (stalkRing O₁ x) (stalkRing O₂ x) (stalkRing O₂' x)) ∧
          Function.Surjective
            (KaehlerDifferential.mapBaseChange
              (stalkRing O₁ x) (stalkRing O₂ x) (stalkRing O₂' x))
      from
        ⟨KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange
            (stalkRing O₁ x) (stalkRing O₂ x) (stalkRing O₂' x) (hsurj x),
          KaehlerDifferential.mapBaseChange_surjective
            (stalkRing O₁ x) (stalkRing O₂ x) (stalkRing O₂' x) (hsurj x)⟩)

/- Companion recall: on the class of an element in the kernel ideal of the stalk map
`(stalkRingHom α x).hom`, the
left conormal map is the canonical formula
`KaehlerDifferential.kerCotangentToTensor_toCotangent`. -/
#check
  (fun f : RingHom.ker (stalkRingHom α x).hom ↦
    let _ : Algebra (stalkRing O₁ x) (stalkRing O₂ x) := (stalkRingHom φ x).hom.toAlgebra
    let _ : Algebra (stalkRing O₂ x) (stalkRing O₂' x) := (stalkRingHom α x).hom.toAlgebra
    show
        KaehlerDifferential.kerCotangentToTensor
            (stalkRing O₁ x) (stalkRing O₂ x) (stalkRing O₂' x)
            (Ideal.toCotangent (RingHom.ker (stalkRingHom α x).hom) f) =
          (1 : stalkRing O₂' x) ⊗ₜ[stalkRing O₂ x]
            KaehlerDifferential.D
              (stalkRing O₁ x) (stalkRing O₂ x) (f : stalkRing O₂ x)
      from
        rfl)

end StalkRecalls

end TopCat.Sheaf

/-! ### Definition_17_28_10 (from Chap17) -/
open CategoryTheory TopCat TopologicalSpace
open AlgebraicGeometry
open PresheafOfModules.DifferentialsConstruction
open TopCat.Sheaf
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X S : RingedSpace.{u}}

/- Domain-style sampling for Definition 17.28.10:
- primary domain: relative differentials of a morphism of commutative ringed spaces;
- sampled owner declarations:
  `RingedSpace.Hom.inverseImageStructureSheafHomComm`,
  `AlgebraicGeometry.ringedSpaceRingCatSheaf`,
  `TopCat.Sheaf.relativeDifferentials`,
  `TopCat.Sheaf.relativeDifferential`,
  `TopCat.Sheaf.relativeDifferentials_representsDerivations`,
  `PresheafOfModules.sheafification`;
- best owner abstraction: `TopCat.Sheaf.relativeDifferentials`, specialized along the inverse-image
  structure-sheaf morphism `RingedSpace.Hom.inverseImageStructureSheafHomComm f` of a ringed-space
  map;
- primitive data in this file: no new primitive data beyond the canonical Chapter 6 inverse-image
  morphism `RingedSpace.Hom.inverseImageStructureSheafHomComm f : f⁻¹ 𝒪_S ⟶ 𝒪_X`;
- derived API: the source-facing notation `Ω[f]`, `d[f]`, together with the specialized
  definitional and representing theorems below.

Source/core/bridge triage:
- `source-facing`: the ringed-space notation `Ω[f]` for `Ω_{X/S}` and `d[f]` for the universal
  derivation attached to `f : X ⟶ S`;
- `core/canonical`: `TopCat.Sheaf.relativeDifferentials`;
- `bridge/view`: reuse of the existing Chapter 6 inverse-image morphism
  `RingedSpace.Hom.inverseImageStructureSheafHomComm f`;
- this item therefore exposes the source-facing ringed-space surface on top of the sheaf owner
  and reuses the established bridge/view layer rather than redeclaring a second public owner.
  The relative derivation type already has the canonical Chapter 17 owner surface `Der[φ ; F]`,
  so this file should use that directly instead of introducing a second ringed-space alias. -/

scoped[AlgebraicGeometry] notation3:max "Ω[" f "]" =>
  relativeDifferentials (RingedSpace.Hom.inverseImageStructureSheafHomComm f)

/-- The sheaf of differentials is the sheafification of the presheaf of relative differentials. -/
theorem differentials_def (f : X ⟶ S) :
    Ω[f] =
      (PresheafOfModules.sheafification (𝟙 (RingedSpace.ringCatSheaf X).obj)).obj
        (relativeDifferentials'
          (RingedSpace.Hom.inverseImageStructureSheafHomComm f).hom) :=
  rfl

scoped[AlgebraicGeometry] notation3:max "d[" f "]" =>
  relativeDifferential (RingedSpace.Hom.inverseImageStructureSheafHomComm f)

/-- The sheaf of differentials represents derivations out of `𝒪_X` relative to `S`. -/
theorem differentials_representsDerivations
    (f : X ⟶ S) (F : SheafOfModules.{u} (RingedSpace.ringCatSheaf X))
    (D : Der[RingedSpace.Hom.inverseImageStructureSheafHomComm f ; F]) :
    ∃! α : Ω[f] ⟶ F,
      RelativeDerivation.postcomp (d[f]) α = D := by
  simpa using
    (relativeDifferentials_representsDerivations
      (RingedSpace.Hom.inverseImageStructureSheafHomComm f) F D)

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_28_11 (from Chap17) -/
open CategoryTheory
open TopCat
open scoped RelativeDerivation

universe u

section

variable {X : TopCat.{u}}
variable {O₁ O₂ A : TopCat.Sheaf CommRingCat.{u} X}
variable (φ : O₁ ⟶ O₂) (α : O₁ ⟶ A) (π : A ⟶ O₂)

/- Domain-style sampling for Lemma 17.28.11:
- primary domain: square-zero extensions of sheaves of commutative rings on a fixed topological
  space, their intrinsic kernel ideal sheaves, restriction of scalars along a chosen section, and
  relative derivations into that kernel;
- sampled owner declarations:
  `IsAlgebraSection`,
  `kernelIdealSheaf`,
  `kernelIdealSheafModule`,
  `existsUnique_derivation_of_algebraSection`;
- best owner abstraction: the generic-site owner API from `Chap18/Lemma_18_33_9`, specialized to
  the site `Opens.grothendieckTopology X`;
- primitive data: only the structure maps `φ : O₁ ⟶ O₂`, `α : O₁ ⟶ A`, and `π : A ⟶ O₂`;
- derived API: compatible algebra sections, the intrinsic kernel ideal sheaf and its descended
  `O₂`-module structure, the perturbation predicate, and the two existence/uniqueness theorems.

Source/core/bridge triage:
- `core/canonical`: the general-site declarations from `Chap18/Lemma_18_33_9`;
- `bridge/view`: this file is only the specialization from an arbitrary site to the site of opens
  of a topological space.

This file therefore reuses the generic-site owner directly instead of redeclaring a second
topological-space-specific API with the same mathematical content. -/

/- Companion recall: the compatible-section predicate and the intrinsic kernel constructions used
in Lemma 17.28.11 are already owned by the generic-site API and specialize directly to
`TopCat.Sheaf`. -/
#check IsAlgebraSection φ α π
#check kernelIdealSheaf π
#check KernelSquareZero π
#check kernelIdealSheafModule π
#check IsSectionPerturbation φ π

/- Companion recall: perturbing a fixed compatible section by a derivation into the intrinsic
kernel ideal is already the generic-site theorem specialized to `TopCat.Sheaf`. -/
#check existsUnique_algebraSection_of_derivation φ α π

/- Lemma 17.28.11: on a topological space, the uniqueness of the derivation measuring the
difference between two compatible algebra sections is exactly the specialization of the generic-site
theorem `existsUnique_derivation_of_algebraSection`. -/
#check existsUnique_derivation_of_algebraSection φ α π

end

/-! ### Lemma_17_28_12 (from Chap17) -/
open CategoryTheory TopCat TopologicalSpace AlgebraicGeometry.RingedSpace.Hom
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RingedSite.Hom RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X X' S S' : RingedSpace.{u}}

/- Domain-style sampling for Lemma 17.28.12:
- primary domain: base change for relative differentials in a commutative square of ringed spaces;
- sampled owner declarations:
  `RingedSpace.Hom.pullback`,
  `AlgebraicGeometry.RingedSpace.Ω[_]`,
  `AlgebraicGeometry.RingedSpace.d[_]`,
  `RingedSite.Hom.pullbackDifferentialsComparison`,
  `RingedSite.Hom.existsUnique_pullbackDifferentialsComparison`;
- best owner abstraction:
  the Chapter 18 bundled owner theorem on `RingedSite.Hom`, specialized to the site of opens of a
  ringed space;
- primitive data:
  only the four morphisms `f`, `g`, `h`, `h'` and the commutative square `CommSq f h' h g`;
- derived API:
  the ringed-space comparison map `pullbackDifferentialsComparison` and its sectionwise
  characterization/uniqueness.

Source/core/bridge triage:
- `source-facing`: the ringed-space map `c_f : f^* Ω[h] ⟶ Ω[h']`;
- `core/canonical`: `RingedSite.Hom.pullbackDifferentialsComparison` and its existence/uniqueness
  theorem;
- `bridge/view`: the passage from a ringed space to the ringed site of opens together with
  `RingedSpace.Hom.toRingCatSheafHom`.

The previous file stored an objectwise pushed-forward derivation and its compatibility as public
primitive data. That was duplicated bridge scaffolding. The public ringed-space API should expose
only the comparison morphism and its intrinsic sectionwise characterization. -/

variable (f : X' ⟶ X) (g : S' ⟶ S) (h : X ⟶ S) (h' : X' ⟶ S')

private abbrev opensRingedSite (X : RingedSpace.{u}) : RingedSite :=
  RingedSite.ofCommRingSheaf (Opens.grothendieckTopology X) X.sheaf

private noncomputable abbrev opensRingedSiteHom {A B : RingedSpace.{u}} (φ : A ⟶ B) :
    opensRingedSite A ⟶ opensRingedSite B where
  base := Opens.map φ.hom.base
  structureSheafMap := toRingCatSheafHom φ

private theorem opensRingedSiteHom_hcomm
    (sq : CommSq f h' h g) :
    opensRingedSiteHom f ≫ opensRingedSiteHom h =
      opensRingedSiteHom h' ≫ opensRingedSiteHom g := by
  simpa using congrArg opensRingedSiteHom sq.w

private theorem opensRingedSite_inverseImageStructureSheafMap_eq
    {A B : RingedSpace.{u}} (φ : A ⟶ B) :
    RingedSite.Hom.inverseImageStructureSheafMap (opensRingedSiteHom φ) =
      inverseImageStructureSheafHomComm φ := by
  sorry

private noncomputable abbrev opensRingedSiteDifferentials {A B : RingedSpace.{u}} (φ : A ⟶ B) :
    SheafOfModules (opensRingedSite A).structureSheaf :=
  relativeDifferentials (RingedSite.Hom.inverseImageStructureSheafMap (opensRingedSiteHom φ))

private theorem opensRingedSite_differentials_eq
    {A B : RingedSpace.{u}} (φ : A ⟶ B) :
    opensRingedSiteDifferentials φ = Ω[φ] := by
  simpa [opensRingedSiteDifferentials, RingedSite.Hom.differentials,
    AlgebraicGeometry.RingedSpace.differentials_def] using
    congrArg relativeDifferentials (opensRingedSite_inverseImageStructureSheafMap_eq φ)

private theorem opensRingedSite_modulePullback_differentials_eq
    {A B C : RingedSpace.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    (RingedSite.Hom.modulePullback (opensRingedSiteHom φ)).obj
        (opensRingedSiteDifferentials ψ) =
      (φ^*).obj Ω[ψ] := by
  rw [RingedSite.Hom.modulePullback, RingedSpace.Hom.pullback, opensRingedSiteHom]
  exact congrArg (RingedSpace.Hom.pullback φ).obj (opensRingedSite_differentials_eq ψ)

-- Proof sketch: transport the Chapter 18 owner
-- `RingedSite.Hom.pullbackDifferentialsComparison` from the opens-site presentation of the four
-- ringed spaces back to the Chapter 17 ringed-space surface.
/-- The canonical base-change map on relative differentials associated to a commutative square of
ringed spaces. This is the ringed-space specialization of
`RingedSite.Hom.pullbackDifferentialsComparison`. -/
noncomputable abbrev pullbackDifferentialsComparison
    (sq : CommSq f h' h g) :
    (f^*).obj Ω[h] ⟶ Ω[h'] :=
  eqToHom (opensRingedSite_modulePullback_differentials_eq f h).symm ≫
    RingedSite.Hom.pullbackDifferentialsComparison
      (opensRingedSiteHom f)
      (opensRingedSiteHom g)
      (opensRingedSiteHom h)
      (opensRingedSiteHom h')
      (opensRingedSiteHom_hcomm f g h h' sq) ≫
    eqToHom (opensRingedSite_differentials_eq h')

/-- The source-facing sectionwise characterization property for the base-change morphism on
relative differentials. -/
def pullbackDifferentialsComparisonProperty
    (τ : (f^*).obj Ω[h] ⟶ Ω[h']) : Prop :=
  ∀ {U : (Opens X)ᵒᵖ} (t : X.presheaf.obj U),
    let U' := (Opens.map f.hom.base).op.obj U
    let fSharpU := (toRingCatSheafHom f).hom.app U
    ((((SheafOfModules.pullbackPushforwardAdjunction
          (toRingCatSheafHom f)).homEquiv _ _)
        τ).val.app U)
      (((d[h]).app U).d t) =
      ((d[h']).app U').d (fSharpU t)

-- Proof sketch: specialize the Chapter 18 characterization theorem along the opens-site bridge
-- and transport source/target through the equalities above.
/-- The canonical comparison morphism is characterized by sending `d_{X/S}(t)` to
`d_{X'/S'}(f^\sharp t)` after passage to the adjoint map `Ω_{X/S} → f_* Ω_{X'/S'}`. -/
theorem pullbackDifferentialsComparison_characterizing
    (sq : CommSq f h' h g) :
    pullbackDifferentialsComparisonProperty f h h'
      (pullbackDifferentialsComparison f g h h' sq) := by
  sorry

-- Proof sketch: transport the Chapter 18 uniqueness theorem along the same opens-site bridge.
/-- A morphism `f^* \Omega_{X/S} \to \Omega_{X'/S'}` is the canonical comparison morphism once its
adjoint sends `d_{X/S}(t)` to `d_{X'/S'}(f^\sharp t)` on local sections. -/
theorem pullbackDifferentialsComparison_unique
    (sq : CommSq f h' h g)
    (τ : (f^*).obj Ω[h] ⟶ Ω[h'])
    (hτ : pullbackDifferentialsComparisonProperty f h h' τ) :
    τ = pullbackDifferentialsComparison f g h h' sq := by
  sorry

-- Proof sketch: existence is witnessed by the canonical specialized owner morphism above, and
-- uniqueness is the preceding theorem.
/-- Lemma 17.28.12: for a commutative square of ringed spaces
`X' \xrightarrow{f} X`, `S' \xrightarrow{g} S`, there exists a unique
`\mathcal O_{X'}`-module morphism
`c_f : f^* \Omega_{X/S} \to \Omega_{X'/S'}`
whose adjoint sends `d_{X/S}(t)` to `d_{X'/S'}(f^\sharp t)` on every local section `t` of
`\mathcal O_X`. -/
theorem existsUnique_pullbackDifferentialsComparison
    (sq : CommSq f h' h g) :
    ∃! τ : (f^*).obj Ω[h] ⟶ Ω[h'],
      pullbackDifferentialsComparisonProperty f h h' τ := by
  refine ⟨pullbackDifferentialsComparison f g h h' sq, ?_, ?_⟩
  · exact pullbackDifferentialsComparison_characterizing f g h h' sq
  · intro τ hτ
    exact pullbackDifferentialsComparison_unique f g h h' sq τ hτ

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_28_13 (from Chap17) -/
open CategoryTheory AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Domain-style sampling for Lemma 17.28.13:
- primary domain: functoriality of the canonical base-change morphism on relative differentials;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.pullbackDifferentialsComparison`,
  `AlgebraicGeometry.RingedSpace.pullbackDifferentialsComparison_unique`,
  `SheafOfModules.pullbackComp`,
  `CategoryTheory.CommSq.horiz_comp`;
- best owner abstraction:
  the source-facing base-change morphism `pullbackDifferentialsComparison`, with
  `SheafOfModules.pullbackComp` as the canonical bridge from pullback along a composite to the
  iterated pullback;
- primitive data:
  only the two composable commutative squares `hf` and `hg`;
- derived API:
  compatibility of the canonical comparison morphism with composition.

Source/core/bridge triage:
- `source-facing`: the composition law for the comparison morphisms on relative differentials;
- `core/canonical`: `pullbackDifferentialsComparison`, `pullbackDifferentialsComparison_unique`,
  and `SheafOfModules.pullbackComp`;
- `bridge/view`: `CommSq.horiz_comp` and the adjunction transposes appearing in the proof.

The local theorem `pullbackDifferentialsComparison_outer_square_commutes` was a duplicate wrapper
around `CommSq.horiz_comp`, so this file should use the owner declaration directly. -/

namespace AlgebraicGeometry.RingedSpace

variable {X X' X'' S S' S'' : RingedSpace.{u}}

/-
Proof sketch: prove that the iterated base-change morphism satisfies the same sectionwise
characterization as the canonical morphism for the pasted square, then apply the uniqueness
statement from Lemma `17.28.12`.

Lemma 17.28.13: the comparison morphism on relative differentials is compatible with composition,
so the map for the outer rectangle equals `c_g ∘ g^* c_f` after identifying `(f \circ g)^*` with
the iterated pullback.
-/
theorem pullbackDifferentialsComparison_comp
    (f : X' ⟶ X) (g : X'' ⟶ X')
    (s : S' ⟶ S) (t : S'' ⟶ S')
    (h : X ⟶ S) (h' : X' ⟶ S') (h'' : X'' ⟶ S'')
    (hf : CommSq f h' h s) (hg : CommSq g h'' h' t) :
    pullbackDifferentialsComparison (g ≫ f) (t ≫ s) h h'' (hg.horiz_comp hf) =
      ((SheafOfModules.pullbackComp
            (toRingCatSheafHom f)
            (toRingCatSheafHom g)).symm.hom.app Ω[h]) ≫
        (g^*).map (pullbackDifferentialsComparison f s h h' hf) ≫
        pullbackDifferentialsComparison g t h' h'' hg := by
  sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_28_14 (from Chap17) -/
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y S : RingedSpace.{u}}

/- Domain-style sampling for Lemma 17.28.14:
- primary domain: the transitivity sequence for relative differentials of composable morphisms of
  ringed spaces;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.Ω[_]`,
  `AlgebraicGeometry.RingedSpace.pullbackDifferentialsComparison`,
  `SheafOfModules.pullbackId`,
  `CategoryTheory.ShortComplex`;
- best owner abstraction:
  the source-facing short complex
  `f^*Ω[g] → Ω[f ≫ g] → Ω[f] → 0`, built from the canonical base-change comparison
  `pullbackDifferentialsComparison` together with the canonical identity-pullback isomorphism
  `SheafOfModules.pullbackId`;
- primitive data:
  only the composable morphisms `f : X ⟶ Y` and `g : Y ⟶ S`;
- derived API:
  the two transitivity morphisms, the named short complex they define, and its exactness and
  epimorphy.

Source/core/bridge triage:
- `source-facing`: the transitivity short complex together with its two companion morphisms;
- `core/canonical`: `Ω[_]`, `pullbackDifferentialsComparison`, `SheafOfModules.pullbackId`, and
  `ShortComplex`;
- `bridge/view`: the identity-base-change square and the stalkwise exactness criterion used in the
  proof sketch.

The former theorem `modulePullback_id_obj_differentials_eq` was duplicate bridge data: the
identity pullback is already canonically owned by `SheafOfModules.pullbackId`, so the public
surface should use that owner directly. The source-facing owner in this file is therefore the
transitivity short complex itself, with the individual comparison maps as companion data. -/

/-- The canonical map `f^*Ω_{Y/S} → Ω_{X/S}` in the transitivity sequence for relative
differentials. -/
noncomputable def relativeDifferentialsTransitivityLeft
    (f : X ⟶ Y) (g : Y ⟶ S) :
    (f^*).obj Ω[g] ⟶ Ω[f ≫ g] :=
  pullbackDifferentialsComparison f (𝟙 S) g (f ≫ g) ⟨by simp⟩

/-- The canonical map `Ω_{X/S} → Ω_{X/Y}` in the transitivity sequence for relative differentials.
-/
noncomputable def relativeDifferentialsTransitivityRight
    (f : X ⟶ Y) (g : Y ⟶ S) :
    Ω[f ≫ g] ⟶ Ω[f] :=
  (SheafOfModules.pullbackId X.ringCatSheaf).inv.app Ω[f ≫ g] ≫
    pullbackDifferentialsComparison (𝟙 X) g (f ≫ g) f ⟨by simp⟩

-- Proof sketch: pass to stalks, where Lemma `17.28.12` identifies the two displayed sheaf maps
-- with the standard maps between Kähler differentials of local rings. The algebraic transitivity
-- sequence has zero composite, so the sheaf-level composite vanishes.
/-- The canonical transitivity morphisms on relative differentials compose to zero. -/
theorem relativeDifferentialsTransitivity_comp_zero
    (f : X ⟶ Y) (g : Y ⟶ S) :
    relativeDifferentialsTransitivityLeft f g ≫
      relativeDifferentialsTransitivityRight f g = 0 := sorry

/-- The canonical short complex
`f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y}`
in the transitivity sequence for relative differentials. -/
noncomputable def relativeDifferentialsTransitivity
    (f : X ⟶ Y) (g : Y ⟶ S) :
    ShortComplex (RingedSpace.Modules X) :=
  ShortComplex.mk
    (relativeDifferentialsTransitivityLeft f g)
    (relativeDifferentialsTransitivityRight f g)
    (relativeDifferentialsTransitivity_comp_zero f g)

-- Proof sketch: check the statement on stalks. Lemma `17.28.12` identifies the stalk maps with
-- the usual transitivity maps for Kähler differentials of the local ring maps
-- `𝒪_{S,g(f(x))} → 𝒪_{Y,f(x)} → 𝒪_{X,x}`, and Algebra, Lemma `10.131.7` gives exactness and
-- surjectivity there. Then use the stalkwise criterion for exactness of sheaves of modules and for
-- epimorphy.
/-- Lemma 17.28.14: for composable morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ S`, the
canonical transitivity short complex
`f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y}`
is exact. -/
theorem relativeDifferentialsTransitivity_exact
    (f : X ⟶ Y) (g : Y ⟶ S) :
    (relativeDifferentialsTransitivity f g).Exact := sorry

/-- The right map in the transitivity short complex for relative differentials is an epimorphism.
-/
theorem relativeDifferentialsTransitivity_epi
    (f : X ⟶ Y) (g : Y ⟶ S) :
    Epi ((relativeDifferentialsTransitivity f g).g) := sorry

end AlgebraicGeometry.RingedSpace
