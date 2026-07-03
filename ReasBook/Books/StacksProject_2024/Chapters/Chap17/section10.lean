import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_17_10_1 (from Chap17) -/
/- Definition 17.10.1: a quasi-coherent sheaf of `\mathcal O_X`-modules is the canonical
predicate `SheafOfModules.IsQuasicoherent`, expressing that locally it is the cokernel of a
morphism between coproducts of copies of the structure sheaf. -/
recall SheafOfModules.IsQuasicoherent

/-! ### Lemma_17_10_2 (from Chap17) -/
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe w u v

/-
Domain-style sampling for Lemma 17.10.2:
- primary domain: quasi-coherent sheaves of modules and their binary direct sums/biproducts;
- inspected owner declarations:
  `SheafOfModules.isQuasicoherent`,
  `SheafOfModules.Presentation.of_isIso`,
  `CategoryTheory.ObjectProperty.prop_of_isLimit_binaryFan`,
  `CategoryTheory.Limits.BinaryBiproduct.isLimit`,
  `CategoryTheory.HasBinaryBiproduct.of_hasBinaryProduct`;
- best owner abstraction: the canonical object property `SheafOfModules.isQuasicoherent R`;
- primitive data: two quasi-coherent sheaves of modules `M` and `N`;
- derived API: the source-facing direct-sum statement, with the binary-product cone used only as
  an internal bridge to the canonical owner abstraction.

Source/core/bridge triage:
- `source-facing`: the binary direct sum of two quasi-coherent modules is quasi-coherent;
- `core/canonical`: the owner predicate `SheafOfModules.isQuasicoherent R`;
- `bridge/view`: `BinaryBiproduct.isLimit M N`, viewing the source-facing direct sum as the
  binary-product cone used by the owner API.
-/

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
variable {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ X, HasSheafify (J.over X) AddCommGrpCat.{w}]
variable [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

-- Proof sketch: refine the local quasi-coherent presentations of the two summands to a common
-- cover, take the biproduct of the resulting local cokernel presentations, and then package that
-- local construction through the owner-level binary-product bridge.
/-- Lemma 17.10.2: the direct sum of two quasi-coherent `\mathcal O_X`-modules is
quasi-coherent. -/
theorem isQuasicoherent_biprod
    {M N : SheafOfModules.{w} R} [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⊞ N).IsQuasicoherent := by
  letI : (SheafOfModules.isQuasicoherent R).IsClosedUnderBinaryProducts := by
    sorry
  simpa using (SheafOfModules.isQuasicoherent R).prop_of_isLimit_binaryFan
    (BinaryBiproduct.isLimit M N) inferInstance inferInstance

instance instIsQuasicoherentBiprod
    {M N : SheafOfModules.{w} R} [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⊞ N).IsQuasicoherent :=
  isQuasicoherent_biprod

end SheafOfModules

/-! ### Remark_17_10_3 (from Chap17) -/
open CategoryTheory Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Remark 17.10.3:
- primary domain: quasi-coherent `\mathcal O_X`-modules on ringed spaces and arbitrary direct
  sums/coproducts;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.IsQuasicoherent`,
  `SheafOfModules.isQuasicoherent`,
  `ringedSpaceModule_sigmaComparison_isIso_of_isCompact`;
- best owner abstraction: the ambient owner is `(RingedSpace.Modules X)` with the owner predicate
  `SheafOfModules.IsQuasicoherent`; the direct sum from the source is the categorical coproduct
  `∐ ℱ`;
- primitive data: a ringed space `X`, an index type `I`, and a family
  `ℱ : I → RingedSpace.Modules X`;
- derived API: the source-facing existence statement that even when every `ℱ i` is
  quasi-coherent, the coproduct `∐ ℱ` need not be.

Layer triage:
- `source-facing`: the warning that infinite direct sums of quasi-coherent modules need not remain
  quasi-coherent;
- `core/canonical`: `RingedSpace.Modules` and `SheafOfModules.IsQuasicoherent`;
- `bridge/view`: the categorical coproduct `∐ ℱ`, viewed as the direct sum from the source.
-/

-- Proof sketch: the source gives this as a warning rather than a construction. The canonical Lean
-- shape is therefore an existence statement over the owner category `(RingedSpace.Modules X)` and
-- its coproducts.
/-- Remark 17.10.3: in general, an infinite direct sum of quasi-coherent
`\mathcal O_X`-modules need not be quasi-coherent. -/
theorem exists_infinite_directSum_of_quasicoherent_not_quasicoherent :
    ∃ (X : RingedSpace.{u}) (I : Type u) (_ : Infinite I) (ℱ : I → RingedSpace.Modules X),
      (∀ i, (ℱ i).IsQuasicoherent) ∧ ¬ (∐ ℱ).IsQuasicoherent := by
  sorry

end AlgebraicGeometry

/-! ### Lemma_17_10_4 (from Chap17) -/
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 17.10.4:
- primary domain: quasi-coherent module sheaves on ringed spaces and their behavior under the
  canonical pullback functor;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.IsQuasicoherent`,
  `RingedSpace.Hom.pullback`,
  `SheafOfModules.RingedSite.pullback_isQuasicoherent`,
  `RingedSpace.Hom.pullback_isFiniteType`;
- best owner abstraction: the Chapter 18 owner theorem
  `SheafOfModules.RingedSite.pullback_isQuasicoherent`, specialized to the ringed site of opens of
  a ringed space, together with the owner predicate `SheafOfModules.IsQuasicoherent` on
  `RingedSpace.Modules Y`;
- primitive data: a morphism of ringed spaces `f : X ⟶ Y` and a module sheaf
  `𝒢 : RingedSpace.Modules Y`;
- derived API: the source-facing ringed-space specialization asserting that pullback carries
  quasi-coherent modules to quasi-coherent modules.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that pullback preserves quasi-coherence;
- `core/canonical`: `SheafOfModules.RingedSite.pullback_isQuasicoherent`,
  `SheafOfModules.IsQuasicoherent`, and the pullback owner `f^*`;
- `bridge/view`: the specialization along `Opens.map f.hom.base` and
  `RingedSpace.Hom.toRingCatSheafHom f`, matching the Chapter 17 ringed-space pullback bridge
  pattern.
-/

variable {X Y : RingedSpace.{u}}

-- Proof sketch: this is the ringed-space specialization of the Chapter 18 owner theorem on
-- pullback preserving quasi-coherence for sheaves of modules on ringed sites, applied to the site
-- of opens of `Y` and `X` and the canonical structure-sheaf map
-- `RingedSpace.Hom.toRingCatSheafHom f`.
private theorem pullback_isQuasicoherent_onRingedSpaces
    (f : X ⟶ Y) (𝒢 : RingedSpace.Modules Y) [𝒢.IsQuasicoherent] :
    ((f^*).obj 𝒢).IsQuasicoherent :=
  SheafOfModules.RingedSite.pullback_isQuasicoherent.{u, u, u, u, u, u, u, u, u, u, u, u, u}
    (Opens.map f.hom.base) (RingedSpace.Hom.toRingCatSheafHom f) 𝒢

/-- Lemma 17.10.4: for a morphism of ringed spaces
`f : (X, \mathcal{O}_X) \to (Y, \mathcal{O}_Y)`, the pullback of a quasi-coherent
`\mathcal{O}_Y`-module is quasi-coherent. -/
theorem ringedSpaceModulePullback_isQuasicoherent
    (f : X ⟶ Y) (𝒢 : RingedSpace.Modules Y) [𝒢.IsQuasicoherent] :
    ((f^*).obj 𝒢).IsQuasicoherent :=
  by
    simpa using pullback_isQuasicoherent_onRingedSpaces f 𝒢

end AlgebraicGeometry

/-! ### Lemma_17_10_5 (from Chap17) -/
open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

attribute [local instance] Classical.propDecidable

variable {X : RingedSpace.{u}} {R : Type u} [CommRing R]

/- Domain-style sampling for Lemma 17.10.5:
- primary domain: the associated `\mathcal O_X`-module of an `R`-module, viewed through pullback
  of sheaves of modules on ringed spaces, presheaf sheafification, and free-presentation
  cokernels;
- inspected owner declarations:
  `RingedSpace.Hom.pullback`,
  `SheafOfModules.pullbackIso`,
  `sheafOfModules_pullback_stalkIso`,
  `SheafOfModules.pullbackPushforwardAdjunction`;
- best owner abstraction: the pullback owner along the morphism
  `π : X ⟶ (\{*\}, R)` determined by `α : R → Γ(X, \mathcal O_X)`, giving the core functor
  `globalSectionsModuleFunctor α : ModuleCat R ⥤ RingedSpace.Modules X`;
- primitive data: the ring map `α`, the singleton source ringed space over `R`, the module sheaf
  on that singleton attached to `M`, and a chosen free presentation of `M` when using the
  cokernel construction;
- derived API: the two source-facing bridge constructions `F₂` and `F₃`, plus quasicoherence,
  colimit preservation, stalk comparison, and the adjunction-style morphism/global-sections
  comparison attached to the owner `F₁ = π^* M`.

Source/core/bridge triage:
- `source-facing`: the three constructions `F₁`, `F₂`, and `F₃` from the Stacks lemma;
- `core/canonical`: `associatedModuleSheaf α M = π^* M`;
- `bridge/view`: the sheafification of the presheaf `U ↦ \mathcal O_X(U) ⊗_R M`, and the
  cokernel construction attached to a chosen free presentation of `M`.
-/

/-- The top open of a ringed space, viewed in `(Opens X)ᵒᵖ`, is an initial object. -/
private abbrev topOpensIsInitial (X : RingedSpace.{u}) : Limits.IsInitial (op (⊤ : Opens X)) :=
  Limits.IsInitial.ofUniqueHom
    (fun U : (Opens X)ᵒᵖ ↦
      (homOfLE (show unop U ≤ (⊤ : Opens X) from by
        intro x hx
        trivial)).op)
    (fun U f ↦ Subsingleton.elim _ _)

/-- The ring homomorphism from `R` to the stalk `\mathcal O_{X, x}` induced by a map
`R → Γ(X, \mathcal O_X)`. -/
abbrev ringedSpaceGlobalSectionsToStalk
    (α : R →+* X.presheaf.obj (op ⊤)) (x : X) :
    R →+* X.presheaf.stalk x :=
  (X.presheaf.Γgerm x).hom.comp α

/-- The underlying sheaf of `Γ(X, \mathcal O_X)`-modules obtained by viewing an
`\mathcal O_X`-module as a sheaf of modules over the global-section ring. -/
private abbrev ringedSpaceModuleGlobalSectionsOverGlobalSectionsRing
    (𝒢 : SheafOfModules ((RingedSpace.ringCatSheaf X))) :
    Sheaf (Opens.grothendieckTopology X) (ModuleCat (X.presheaf.obj (op ⊤))) :=
  (SheafOfModules.forgetToSheafModuleCat ((RingedSpace.ringCatSheaf X))
    (op (⊤ : Opens X)) (topOpensIsInitial X)).obj 𝒢

/-- The `R`-module of global sections of an `\mathcal O_X`-module, where `R` acts through the map
`R → Γ(X, \mathcal O_X)`. -/
abbrev ringedSpaceModuleGlobalSections
    (α : R →+* X.presheaf.obj (op ⊤))
    (𝒢 : SheafOfModules ((RingedSpace.ringCatSheaf X))) : ModuleCat R :=
  let M := ringedSpaceModuleGlobalSectionsOverGlobalSectionsRing 𝒢
  letI : Module R (ModuleCat.sectionsSubmodule M.1) :=
    Module.compHom (ModuleCat.sectionsSubmodule M.1) α
  ModuleCat.of R (ModuleCat.sectionsSubmodule M.1)

private noncomputable abbrev commRingStalkToRingStalkIso (x : X) :
    (forget₂ CommRingCat RingCat).obj (TopCat.Presheaf.stalk X.presheaf x) ≅
      ((RingedSpace.ringCatSheaf X)).presheaf.stalk x :=
  CategoryTheory.preservesColimitIso (forget₂ CommRingCat RingCat)
    ((OpenNhds.inclusion x).op ⋙ X.presheaf)

private abbrev globalSectionsSourceSpace : TopCat := TopCat.of PUnit

private abbrev globalSectionsSourcePoint : globalSectionsSourceSpace := PUnit.unit

private theorem globalSectionsSourceOpen_eq_top {U : Opens globalSectionsSourceSpace}
    (h : PUnit.unit ∈ U) :
    U = ⊤ := by
  ext y
  cases y
  simp [h]

private theorem globalSectionsSourceOpen_eq_bot {U : Opens globalSectionsSourceSpace}
    (h : PUnit.unit ∉ U) :
    U = ⊥ := by
  ext y
  cases y
  constructor
  · intro hy
    exact (h hy).elim
  · intro hy
    exact False.elim hy

/-- The singleton ringed space whose unique nonempty open has ring of sections `R`. -/
private noncomputable def globalSectionsSourceRingedSpace (R : Type u) [CommRing R] : RingedSpace :=
  let pointSheaf := skyscraperSheaf PUnit.unit (CommRingCat.of R)
  { carrier := globalSectionsSourceSpace
    presheaf := pointSheaf.obj
    IsSheaf := pointSheaf.property }

private noncomputable abbrev globalSectionsSourceRingCatSheaf (R : Type u) [CommRing R] :=
  RingedSpace.ringCatSheaf (globalSectionsSourceRingedSpace R)

private theorem globalSectionsSourceRingCatSheaf_obj_top (R : Type u) [CommRing R] :
    (globalSectionsSourceRingCatSheaf R).obj.obj (op (⊤ : Opens globalSectionsSourceSpace)) =
      RingCat.of R := by
  let pointSheaf : Sheaf CommRingCat globalSectionsSourceSpace :=
    skyscraperSheaf PUnit.unit (CommRingCat.of R)
  change
    (forget₂ CommRingCat RingCat).obj
        (pointSheaf.obj.obj (op ⊤)) =
      RingCat.of R
  simp [pointSheaf, skyscraperSheaf, skyscraperPresheaf]
  rfl

private theorem globalSectionsSourcePresheaf_obj_top (R : Type u) [CommRing R] :
    (globalSectionsSourceRingedSpace R).presheaf.obj (op (⊤ : Opens globalSectionsSourceSpace)) =
      CommRingCat.of R := by
  let pointSheaf : Sheaf CommRingCat globalSectionsSourceSpace :=
    skyscraperSheaf PUnit.unit (CommRingCat.of R)
  simp [globalSectionsSourceRingedSpace, skyscraperSheaf, skyscraperPresheaf]

private noncomputable def globalSectionsSourceModulePresheafObj
    (R : Type u) [CommRing R]
    (M : ModuleCat R) :
    (U : (Opens globalSectionsSourceSpace)ᵒᵖ) →
      ModuleCat ((globalSectionsSourceRingCatSheaf R).obj.obj U) :=
  fun U ↦ by
    by_cases hU : PUnit.unit ∈ unop U
    · have hU' : U = op ⊤ := by
        simpa using congrArg op (globalSectionsSourceOpen_eq_top hU)
      subst hU'
      exact
        (ModuleCat.restrictScalars
          (eqToHom (globalSectionsSourceRingCatSheaf_obj_top R)).hom).obj M
    · exact
        ⊤_ ModuleCat ((globalSectionsSourceRingCatSheaf R).obj.obj U)

private noncomputable def globalSectionsSourceModulePresheaf
    (R : Type u) [CommRing R]
    (M : ModuleCat R) :
    PresheafOfModules (globalSectionsSourceRingCatSheaf R).obj where
  obj := globalSectionsSourceModulePresheafObj R M
  map {U V} i := by
    by_cases hV : PUnit.unit ∈ unop V
    · have hU : PUnit.unit ∈ unop U := i.unop.le hV
      have hU' : U = op ⊤ := by
        simpa using congrArg op (globalSectionsSourceOpen_eq_top hU)
      have hV' : V = op ⊤ := by
        simpa using congrArg op (globalSectionsSourceOpen_eq_top hV)
      subst hU'
      subst hV'
      have hi : i = 𝟙 (op ⊤) := Subsingleton.elim _ _
      exact
        (ModuleCat.restrictScalarsId'App
          ((globalSectionsSourceRingCatSheaf R).obj.map i).hom
          (by
            subst hi
            exact congrArg RingCat.Hom.hom
              ((globalSectionsSourceRingCatSheaf R).obj.map_id (op ⊤)))
          (globalSectionsSourceModulePresheafObj R M (op ⊤))).inv
    · simpa [globalSectionsSourceModulePresheafObj, hV] using
        (0 :
          globalSectionsSourceModulePresheafObj R M U ⟶
            (ModuleCat.restrictScalars
              ((globalSectionsSourceRingCatSheaf R).obj.map i).hom).obj
                (globalSectionsSourceModulePresheafObj R M V))
  map_id := by
    intro U
    sorry
  map_comp := by
    intro U V W i j
    sorry

private noncomputable def globalSectionsSourceModuleSheaf
    (R : Type u) [CommRing R]
    (M : ModuleCat R) :
    SheafOfModules (globalSectionsSourceRingCatSheaf R) where
  val := globalSectionsSourceModulePresheaf R M
  isSheaf := by
    sorry

private noncomputable def globalSectionsSourceModuleSheafMap
    (R : Type u) [CommRing R]
    {M N : ModuleCat R} (f : M ⟶ N) :
    globalSectionsSourceModuleSheaf R M ⟶ globalSectionsSourceModuleSheaf R N where
  val :=
    { app := fun U ↦ by
        by_cases hU : PUnit.unit ∈ unop U
        · have hU' : U = op ⊤ := by
            simpa using congrArg op (globalSectionsSourceOpen_eq_top hU)
          subst hU'
          change globalSectionsSourceModulePresheafObj R M (op ⊤) ⟶
              globalSectionsSourceModulePresheafObj R N (op ⊤)
          dsimp [globalSectionsSourceModuleSheaf, globalSectionsSourceModulePresheaf,
            globalSectionsSourceModulePresheafObj]
          simpa using
            (ModuleCat.restrictScalars
              (eqToHom (globalSectionsSourceRingCatSheaf_obj_top R)).hom).map f
        · simpa [globalSectionsSourceModulePresheafObj, hU] using
            (0 :
              globalSectionsSourceModulePresheafObj R M U ⟶
                globalSectionsSourceModulePresheafObj R N U)
      naturality := by
        intro U V i
        sorry }

private noncomputable def globalSectionsSourceModuleFunctor
    (R : Type u) [CommRing R] :
    ModuleCat R ⥤ SheafOfModules (globalSectionsSourceRingCatSheaf R) where
  obj M := globalSectionsSourceModuleSheaf R M
  map f := globalSectionsSourceModuleSheafMap R f
  map_id := by
    intro M
    ext U
    sorry
  map_comp := by
    intro M N P f g
    ext U
    sorry

private noncomputable def globalSectionsSourceSheafMap
    (R : Type u) [CommRing R]
    (α : R →+* X.presheaf.obj (op ⊤)) :
    (globalSectionsSourceRingedSpace R).presheaf ⟶
      (ofHom (ContinuousMap.const X PUnit.unit)) _* X.presheaf where
  app U := by
    by_cases hU : PUnit.unit ∈ unop U
    · have hU' : U = op ⊤ := by
        simpa using congrArg op (globalSectionsSourceOpen_eq_top hU)
      subst hU'
      change
        ((skyscraperSheaf globalSectionsSourcePoint (CommRingCat.of R)).obj.obj (op ⊤)) ⟶
          X.presheaf.obj
            (op ((Opens.map (ofHom (ContinuousMap.const X PUnit.unit))).obj (⊤ : Opens globalSectionsSourceSpace)))
      dsimp [globalSectionsSourceRingedSpace, skyscraperSheaf, skyscraperPresheaf]
      simpa using CommRingCat.ofHom α
    · have hU' : unop U = (⊥ : Opens globalSectionsSourceSpace) := by
        ext y
        cases y
        constructor
        · exact fun hy ↦ (hU hy).elim
        · intro hy
          exact False.elim hy
      let F : TopCat.Sheaf CommRingCat globalSectionsSourceSpace :=
        (TopCat.Sheaf.pushforward CommRingCat (ofHom (ContinuousMap.const X PUnit.unit))).obj X.sheaf
      exact (F.isTerminalOfEqEmpty hU').from _
  naturality := by
    intro U V i
    sorry

private noncomputable def globalSectionsSourceMorphism
    (R : Type u) [CommRing R]
    (α : R →+* X.presheaf.obj (op ⊤)) :
    X ⟶ globalSectionsSourceRingedSpace R :=
  InducedCategory.homMk
    { base := ofHom (ContinuousMap.const X PUnit.unit)
      c := globalSectionsSourceSheafMap R α }

-- Proof sketch: define `π : X ⟶ *R` from `α : R → Γ(X, \mathcal O_X)`, place the module `M` on
-- the singleton ringed space `*R`, and pull it back along `π`.
/-- Lemma 17.10.5: for a ringed space `X` and a ring homomorphism
`α : R → Γ(X, \mathcal O_X)`, the associated-module-sheaf construction is a concrete functor
from `R`-modules to `\mathcal O_X`-modules. -/
noncomputable def globalSectionsModuleFunctor
    (α : R →+* X.presheaf.obj (op ⊤)) :
    ModuleCat R ⥤ SheafOfModules ((RingedSpace.ringCatSheaf X)) :=
  globalSectionsSourceModuleFunctor R ⋙ RingedSpace.Hom.pullback (globalSectionsSourceMorphism R α)

/-- The `\mathcal O_X`-module associated to the `R`-module `M` through
`α : R → Γ(X, \mathcal O_X)`. -/
abbrev associatedModuleSheaf
    (α : R →+* X.presheaf.obj (op ⊤)) (M : ModuleCat R) :
    RingedSpace.Modules X :=
  (globalSectionsModuleFunctor α).obj M

/-- The presheaf `U ↦ \mathcal O_X(U) \otimes_R M` underlying the third source construction in
Lemma `17.10.5`, expressed through the canonical presheaf pullback used by `π^*`. -/
abbrev associatedModulePresheaf
    (α : R →+* X.presheaf.obj (op ⊤)) (M : ModuleCat R) :
    PresheafOfModules (RingedSpace.ringCatSheaf X).obj :=
  ((SheafOfModules.forget (globalSectionsSourceRingCatSheaf R)) ⋙
      PresheafOfModules.pullback
        (RingedSpace.Hom.toRingCatSheafHom (globalSectionsSourceMorphism R α)).hom).obj
    (globalSectionsSourceModuleSheaf R M)

/-- The sheaf associated to the presheaf `U ↦ \mathcal O_X(U) \otimes_R M`, namely the third
construction `F₃` in Lemma `17.10.5`. -/
abbrev associatedModuleSheafFromPresheaf
    (α : R →+* X.presheaf.obj (op ⊤)) (M : ModuleCat R) :
    RingedSpace.Modules X :=
  (PresheafOfModules.sheafification (𝟙 (RingedSpace.ringCatSheaf X).obj)).obj
    (associatedModulePresheaf α M)

/-- The sheafification construction `F₃` is canonically isomorphic to the pullback owner
`F₁ = π^* M`. -/
noncomputable abbrev associatedModuleSheafFromPresheafIso
    (α : R →+* X.presheaf.obj (op ⊤)) (M : ModuleCat R) :
    associatedModuleSheaf α M ≅ associatedModuleSheafFromPresheaf α M := by
  simpa [associatedModuleSheaf, globalSectionsModuleFunctor, associatedModuleSheafFromPresheaf,
    associatedModulePresheaf] using
    (SheafOfModules.pullbackIso
      (RingedSpace.Hom.toRingCatSheafHom (globalSectionsSourceMorphism R α))).app
      (globalSectionsSourceModuleSheaf R M)

/-- The morphism between associated sheaves of free modules induced by a chosen presentation map
of `R`-modules. This is the bridge map whose cokernel realizes the second source construction
`F₂` after identifying associated sheaves of free modules with free `\mathcal O_X`-modules. -/
abbrev associatedModulePresentationMap
    (α : R →+* X.presheaf.obj (op ⊤))
    {I J : Type u}
    (f : ModuleCat.of R (J →₀ R) ⟶ ModuleCat.of R (I →₀ R)) :
    associatedModuleSheaf α (ModuleCat.of R (J →₀ R)) ⟶
      associatedModuleSheaf α (ModuleCat.of R (I →₀ R)) :=
  (globalSectionsModuleFunctor α).map f

/-- The cokernel sheaf attached to a chosen free presentation of `M`, i.e. the source construction
`F₂` written as a thin bridge on top of the owner functor `associatedModuleSheaf`. -/
abbrev associatedModuleSheafFromPresentation
    (α : R →+* X.presheaf.obj (op ⊤))
    {I J : Type u}
    (f : ModuleCat.of R (J →₀ R) ⟶ ModuleCat.of R (I →₀ R)) :
    RingedSpace.Modules X :=
  cokernel (associatedModulePresentationMap α f)

-- Proof sketch: the module sheaf on `*R` attached to `M` is quasi-coherent, and pullback along
-- `π : X ⟶ *R` preserves quasi-coherence.
/-- Every object of `globalSectionsModuleFunctor α` is quasi-coherent. -/
theorem globalSectionsModuleFunctor_isQuasicoherent
    (α : R →+* X.presheaf.obj (op ⊤)) (M : ModuleCat R) :
    (associatedModuleSheaf α M).IsQuasicoherent := sorry

-- Proof sketch: the source functor on `*R` preserves all colimits, and so does pullback along
-- `π : X ⟶ *R`.
/-- The associated-module-sheaf functor preserves arbitrary colimits. -/
theorem globalSectionsModuleFunctor_preservesColimits
    (α : R →+* X.presheaf.obj (op ⊤)) :
    PreservesColimits (globalSectionsModuleFunctor α) := sorry

/-- For any chosen free presentation of `M`, the corresponding cokernel construction `F₂` is
canonically isomorphic to the pullback owner `F₁ = π^* M`. -/
noncomputable def associatedModuleSheafFromPresentationIso
    (α : R →+* X.presheaf.obj (op ⊤))
    {I J : Type u} {M : ModuleCat R}
    (f : ModuleCat.of R (J →₀ R) ⟶ ModuleCat.of R (I →₀ R))
    (g : ModuleCat.of R (I →₀ R) ⟶ M)
    (H : f ≫ g = 0)
    (h : IsColimit (CokernelCofork.ofπ g H)) :
    associatedModuleSheafFromPresentation α f ≅ associatedModuleSheaf α M := by
  let F := globalSectionsModuleFunctor α
  letI : PreservesColimits F := globalSectionsModuleFunctor_preservesColimits α
  let e : M ≅ cokernel f := h.coconePointUniqueUpToIso (colimit.isColimit (parallelPair f 0))
  exact (PreservesCokernel.iso F f).symm ≪≫ (F.mapIso e).symm

/- Core owner recalls for the two remaining source-facing consequences of Lemma `17.10.5`. -/
recall RingedSpace.Hom.pullbackStalkIso
recall SheafOfModules.pullbackPushforwardAdjunction

section

variable (α : R →+* X.presheaf.obj (op ⊤)) (M : ModuleCat R) (x : X)
variable (𝒢 : RingedSpace.Modules X)

/- Lemma 17.10.5, stalk clause: for `F(M) = associatedModuleSheaf α M`, the stalk at `x` is the
canonical base change of `M` along the induced ring map
`R → \mathcal O_{X, x}`. This is the source-facing stalk formula extracted from the owner
`RingedSpace.Hom.pullbackStalkIso` specialized to `π : X ⟶ (*, R)`. -/
#check ((ModuleCat.extendScalars (ringedSpaceGlobalSectionsToStalk α x)).obj M ≅
  RingedSpace.stalkModuleCat (associatedModuleSheaf α M) x)

/- Lemma 17.10.5, adjunction clause: morphisms from the associated-module sheaf `F(M)` to an
`\mathcal O_X`-module `𝒢` are represented by `R`-linear maps from `M` to the global sections
module of `𝒢`. This is the source-facing Hom-bijection induced by the owner adjunction
`SheafOfModules.pullbackPushforwardAdjunction` for `π : X ⟶ (*, R)`. -/
#check ((associatedModuleSheaf α M ⟶ 𝒢) ≃ (M ⟶ ringedSpaceModuleGlobalSections α 𝒢))

end

end AlgebraicGeometry

/-! ### Definition_17_10_6 (from Chap17) -/
open CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-
Domain-style sampling for Definition 17.10.6:
- primary domain: associated `\mathcal O_X`-modules on a ringed space, attached to modules over
  the global-sections ring;
- inspected owner declarations:
  `globalSectionsModuleFunctor`,
  `associatedModuleSheaf`,
  `associatedModuleSheafFromPresheafIso`,
  `associatedModuleSheafFromPresentationIso`;
- best owner abstraction: the canonical owner is `associatedModuleSheaf α M : X.Modules`;
- primitive data: a ringed space `X`, a commutative ring `R`, a ring map
  `α : R → Γ(X, \mathcal O_X)`, and an `R`-module `M`;
- derived API: the source-facing notation `𝓕[α]_M` for that owner, its identity specialization
  `𝓕_ M` as the Lean surface for the textbook `𝓕_M`, together with the proposition that a given
  `X.Modules` object is isomorphic to the corresponding associated sheaf.

Source/core/bridge triage:
- `source-facing`: the proposition that an `\mathcal O_X`-module `ℱ` is associated to `M`;
- `core/canonical`: the owner object `associatedModuleSheaf α M`;
- `bridge/view`: the presheaf and presentation realizations already identified upstream by
  `associatedModuleSheafFromPresheafIso` and `associatedModuleSheafFromPresentationIso`.

Definition 17.10.6 does not introduce a second owner; it only refers back to the canonical module
sheaf from Lemma 17.10.5. The file therefore keeps the public surface at that owner and expresses
"being associated to `M`" directly as isomorphism to it.
-/
variable {X : RingedSpace.{u}} {R : Type u} [CommRing R]
variable (α : R →+* X.presheaf.obj (op ⊤)) (M : ModuleCat R) (ℱ : X.Modules)
variable (MΓ : ModuleCat (X.presheaf.obj (op ⊤)))

/- Core owner recall behind the source-facing notation for Definition 17.10.6. -/
recall associatedModuleSheaf

/- Definition 17.10.6: write the `\mathcal O_X`-module associated to `M` through
`α : R → Γ(X, \mathcal O_X)` as `𝓕[α]_M`. The notation keeps the source-facing `\mathcal F_M`
surface while leaving the ambient ring map explicit when Lean cannot infer it. -/
scoped notation:max "𝓕[" α "]_" M:max => associatedModuleSheaf α M

/- Source-facing identity specialization: when `R = Γ(X, \mathcal O_X)` and `α = RingHom.id _`,
write the associated module sheaf as `𝓕_ M`, the Lean surface corresponding to the textbook
notation `\mathcal F_M`. -/
scoped notation:max "𝓕_" M:max => associatedModuleSheaf (RingHom.id _) M

/- Source-facing owner surface for Definition 17.10.6. -/
#check 𝓕[α]_M
#check 𝓕_ MΓ

/- Source-facing specialization: an `\mathcal O_X`-module `ℱ` is associated to `M` exactly when
it is isomorphic to `𝓕[α]_M`. -/
#check Nonempty (ℱ ≅ 𝓕[α]_M)
#check Nonempty (ℱ ≅ 𝓕_ MΓ)

end AlgebraicGeometry

/-! ### Lemma_17_10_7 (from Chap17) -/
open CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 17.10.7:
- primary domain: pullback of associated module sheaves on ringed spaces, together with scalar
  extension on global-sections modules;
- sampled owner declarations:
  `associatedModuleSheaf`,
  `RingedSpace.Hom.pullback`,
  `ModuleCat.extendScalars`,
  `SheafOfModules.pullbackComp`;
- best owner abstraction: the source-facing lemma should be stated directly using the chapter owner
  `associatedModuleSheaf` with its source-facing notations `𝓕[α]_M` and `𝓕_ M`, the ringed-space
  inverse-image owner `g^*`, and the module-side change of rings owner `ModuleCat.extendScalars`,
  rather than a local tensor-product wrapper for the base-changed module;
- primitive data: a morphism of ringed spaces `g : Y ⟶ X` and a
  `Γ(X, \mathcal O_X)`-module `M`;
- derived API: the pullback comparison identifying `g^*` of the associated sheaf on `X` with the
  associated sheaf on `Y` attached to the extended module over `Γ(Y, \mathcal O_Y)`.

Source/core/bridge triage:
- `source-facing`: the pullback/base-change comparison for associated module sheaves;
- `core/canonical`: `associatedModuleSheaf`, `RingedSpace.Hom.pullback`, and
  `ModuleCat.extendScalars`;
- `bridge/view`: the global-sections ring map `((SheafedSpace.Γ.map g.op).hom)` and the
  owner comparison `SheafOfModules.pullbackComp` used in the proof route.
-/

-- Proof sketch: specialize the canonical pullback-composition isomorphism
-- `SheafOfModules.pullbackComp` to the owner construction from Lemma `17.10.5`, then simplify the
-- resulting composite pullback to the associated sheaf on `Y` attached to the extended module.
/-- Lemma 17.10.7: after pullback along `g : Y ⟶ X`, the pullback of the associated module sheaf
is canonically isomorphic to the associated sheaf on `Y`
attached to `Γ(Y, \mathcal O_Y) \otimes_{Γ(X, \mathcal O_X)} M`. -/
noncomputable abbrev pullback_associated_globalSectionsModule
    {X Y : RingedSpace.{u}} (g : Y ⟶ X)
    (M : ModuleCat (X.presheaf.obj (op ⊤))) :
    ((g^*).obj (𝓕_ M)) ≅
      𝓕_ ((ModuleCat.extendScalars ((SheafedSpace.Γ.map g.op).hom)).obj M) := by
  refine (SheafOfModules.pullbackComp _ _).app _ ≪≫ ?_
  -- This remaining comparison is the singleton-source change-of-rings identification.
  sorry

end AlgebraicGeometry

/-! ### Lemma_17_10_8 (from Chap17) -/
open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped Topology

noncomputable section

universe u

namespace AlgebraicGeometry

/-
Domain-style sampling for Lemma 17.10.8:
- primary domain: quasi-coherent `\mathcal O_X`-modules and associated module sheaves on open
  subspaces;
- inspected owner declarations:
  `associatedModuleSheaf`,
  `RingedSpace.restrict`,
  `RingedSpace.Hom.pullback`,
  `SheafedSpace.Γ`;
- best owner abstraction: the source-facing existence statement should be expressed directly on the
  restricted ringed space `X.restrict U.isOpenEmbedding`, with owner `associatedModuleSheaf` in its
  identity-map form `𝓕_ M`, rather than through a separate ring-map bridge from `Γ(U, \mathcal O_X)`;
- primitive data: `U`, `x ∈ U`, the open-inclusion morphism `X.ofRestrict U.isOpenEmbedding`, the
  restricted ringed space `X.restrict U.isOpenEmbedding`, and a module `M` over its top-sections
  ring `(X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)`;
- derived API: the neighborhood existence conclusion together with the direct isomorphism witness
  `((X.ofRestrict U.isOpenEmbedding)^*).obj ℱ ≅ 𝓕_ M`.

Source/core/bridge triage:
- `source-facing`: existence of an open neighbourhood on which `ℱ` is associated to a module over
  the ring of sections of that neighbourhood;
- `core/canonical`: `associatedModuleSheaf` on the restricted ringed space and the pullback owner
  `j^*` for `j := X.ofRestrict U.isOpenEmbedding`;
- `bridge/view`: the upstream identification between sections on `U` and global sections of the
  restricted ringed space stays internal and does not belong in the public theorem surface.
-/

-- Proof sketch: choose a quasi-compact neighbourhood basis element around `x`, shrink to an open
-- neighbourhood on which the local cokernel presentation of the quasi-coherent sheaf `ℱ` is given
-- by a genuine matrix of sections over that open, and then invoke the associated-module-sheaf
-- construction on the restricted ringed space.
/-- Lemma 17.10.8: if `x` has a neighbourhood basis consisting of quasi-compact neighbourhoods,
then every quasi-coherent `\mathcal O_X`-module becomes on some open neighbourhood of `x`
via an isomorphism to a module sheaf associated to a module over the ring of sections on that
neighbourhood. -/
theorem exists_open_neighborhood_associatedGlobalSectionsModuleSheaf_of_isQuasicoherent
    {X : RingedSpace.{u}} (x : X)
    (hx : (𝓝 x).HasBasis (fun K : Set X ↦ K ∈ 𝓝 x ∧ IsCompact K) id)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ∃ (U : Opens X) (_ : x ∈ U)
      (M : ModuleCat ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))),
        Nonempty
          (((X.ofRestrict U.isOpenEmbedding)^*).obj ℱ ≅
            𝓕_ M) := sorry

end AlgebraicGeometry

/-! ### Example_17_10_9 (from Chap17) -/
open CategoryTheory Limits Opposite TopologicalSpace
open TopCat
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

private instance : PreservesLimits (forget (CommAlgCat.{0} ℝ)) := by
  simpa using
    (inferInstance :
      PreservesLimits ((commAlgCatEquivUnder (CommRingCat.of ℝ)).functor ⋙
        Under.forget (CommRingCat.of ℝ) ⋙ forget CommRingCat))

private instance opensMapOfRestrictFinal {X : RingedSpace.{u}} (U : Opens X) :
    Functor.Final (Opens.map (X.ofRestrict U.isOpenEmbedding).hom.base) := by
  let hU : IsOpenMap U.inclusion' := U.isOpenEmbedding.isOpenMap
  simpa using
    (CategoryTheory.Functor.final_of_adjunction hU.adjunction :
      Functor.Final (Opens.map U.inclusion'))

/- Domain-style sampling for Example 17.10.9:
- primary domain: morphisms between restricted free `\mathcal O_X`-module sheaves and the
  canonical module-sheaf owner attached to free `Γ(U, \mathcal O_U)`-modules on the restricted
  ringed space `X|_U`;
- inspected owner declarations:
  `globalSectionsModuleFunctor`,
  `associatedModuleSheaf`,
  `SheafOfModules.pullbackObjFreeIso`,
  `continuousRealFunctionsSheaf`;
- best owner abstraction: on `X|_U`, the source-facing question is whether a restricted free-sheaf
  morphism is induced by a morphism between free `Γ(U, \mathcal O_U)`-modules; the public API
  should therefore quantify over those module maps directly, while any explicit bridge from module
  data to the restricted free sheaves remains internal;
- primitive data: an open `U`, basis types `I` and `J`, and a morphism between the free
  `Γ(U, \mathcal O_U)`-modules on those bases;
- derived API: the source-facing predicate saying that a restricted free-sheaf morphism is induced
  by such a module map, together with the glued-line counterexample below.

Source/core/bridge triage:
- `source-facing`: “this restricted morphism comes from a morphism of free
  `Γ(U, \mathcal O_U)`-modules”;
- `core/canonical`: the Chapter 17 owner `globalSectionsModuleFunctor` / `associatedModuleSheaf`
  on the restricted ringed space and the canonical restriction pullback `j^*`;
- `bridge/view`: the concrete map from a free `Γ(U, \mathcal O_U)`-module morphism to a morphism
  of restricted free sheaves, which stays private below. -/

private abbrev restrictedRingedSpace
    {X : RingedSpace.{u}} (U : Opens X) : RingedSpace.{u} :=
  X.restrict U.isOpenEmbedding

private abbrev restrictedRingCatSheaf
    {X : RingedSpace.{u}} (U : Opens X) :=
  RingedSpace.ringCatSheaf (restrictedRingedSpace U)

private abbrev restrictedGlobalSectionsRing
    {X : RingedSpace.{u}} (U : Opens X) :=
  (restrictedRingedSpace U).presheaf.obj (op ⊤)

private abbrev restrictedGlobalSectionsFreeModule
    {X : RingedSpace.{u}} (U : Opens X) (I : Type u) :
    ModuleCat (restrictedGlobalSectionsRing U) :=
  ModuleCat.of (restrictedGlobalSectionsRing U) (I →₀ restrictedGlobalSectionsRing U)

private abbrev topToRestrictedOpen
    {X : RingedSpace.{u}} (U : Opens X)
    (V : (Opens (restrictedRingedSpace U))ᵒᵖ) :
    op (⊤ : Opens (restrictedRingedSpace U)) ⟶ V :=
  (homOfLE (show unop V ≤ (⊤ : Opens (restrictedRingedSpace U)) from by
    intro x hx
    trivial)).op

/-- A global section `r ∈ Γ(U, \mathcal O_U)` determines the corresponding global section of the
unit sheaf on the restricted ringed space `X|_U`. -/
private noncomputable def unitSectionOfGlobalSectionsOnOpen
    {X : RingedSpace.{u}} (U : Opens X)
    (r : restrictedGlobalSectionsRing U) :
    (SheafOfModules.unit (restrictedRingCatSheaf U)).sections :=
  PresheafOfModules.sectionsMk
    (fun V ↦ ((restrictedRingedSpace U).presheaf.map (topToRestrictedOpen U V)).hom r)
    (by
      intro V W f
      change (CommRingCat.Hom.hom ((restrictedRingedSpace U).presheaf.map f))
          ((CommRingCat.Hom.hom
              ((restrictedRingedSpace U).presheaf.map (topToRestrictedOpen U V))) r) =
        (CommRingCat.Hom.hom
            ((restrictedRingedSpace U).presheaf.map (topToRestrictedOpen U W))) r
      have htop : topToRestrictedOpen U W = topToRestrictedOpen U V ≫ f := Subsingleton.elim _ _
      have hcomp :
          (CommRingCat.Hom.hom
              ((restrictedRingedSpace U).presheaf.map (topToRestrictedOpen U W))) r =
            (CommRingCat.Hom.hom ((restrictedRingedSpace U).presheaf.map f))
              ((CommRingCat.Hom.hom
                  ((restrictedRingedSpace U).presheaf.map (topToRestrictedOpen U V))) r) := by
        have hmapComp :=
          (restrictedRingedSpace U).presheaf.map_comp (topToRestrictedOpen U V) f
        have hmap := congrArg (fun g ↦ g r) (congrArg CommRingCat.Hom.hom hmapComp)
        simpa [htop] using hmap
      exact hcomp.symm)

/-- A finitely supported family of coefficients in `Γ(U, \mathcal O_U)` determines the
corresponding global section of the free sheaf on `X|_U`. -/
private noncomputable def freeSectionOfGlobalSectionsFinsuppOnOpen
    {X : RingedSpace.{u}} (U : Opens X)
    {J : Type u}
    (a : J →₀ restrictedGlobalSectionsRing U) :
    (SheafOfModules.free.{u} J : (restrictedRingedSpace U).Modules).sections :=
  (SheafOfModules.unitHomEquiv
      (SheafOfModules.free.{u} J : (restrictedRingedSpace U).Modules))
    (a.sum fun j r ↦
      (SheafOfModules.unitHomEquiv
          (SheafOfModules.unit (restrictedRingCatSheaf U))).symm
        (unitSectionOfGlobalSectionsOnOpen U r) ≫
          (show SheafOfModules.unit (restrictedRingCatSheaf U) ⟶
              (SheafOfModules.free.{u} J : (restrictedRingedSpace U).Modules)
            from @SheafOfModules.ιFree _ _ _ (restrictedRingCatSheaf U) _ _ _ J j))

/-- A morphism of free `Γ(U, \mathcal O_U)`-modules induces canonically a morphism of free sheaves
on the restricted ringed space `X|_U`. This is private bridge data for the public predicate
`IsInducedByGlobalSectionsModuleMapOnOpen`. -/
private noncomputable def freeSheafMapOnOpen
    {X : RingedSpace.{u}} (U : Opens X)
    {I J : Type u}
    (ψ : restrictedGlobalSectionsFreeModule U I ⟶ restrictedGlobalSectionsFreeModule U J) :
    (SheafOfModules.free.{u} I : (restrictedRingedSpace U).Modules) ⟶
      (SheafOfModules.free.{u} J : (restrictedRingedSpace U).Modules) :=
  (SheafOfModules.freeHomEquiv
      (SheafOfModules.free.{u} J : (restrictedRingedSpace U).Modules)).symm
    (fun i ↦
      freeSectionOfGlobalSectionsFinsuppOnOpen U ((ψ.hom) (Finsupp.single i 1)))

/-- The canonical morphism between restricted free sheaves obtained from a morphism of free
`Γ(U, \mathcal O_U)`-modules, transported through the restriction isomorphisms
`SheafOfModules.pullbackObjFreeIso`. This bridge stays private; the public surface keeps only the
source-facing proposition that such a module map exists. -/
private noncomputable def restrictedFreeSheafMapOnOpen
    {X : RingedSpace.{u}} (U : Opens X)
    {I J : Type u}
    (ψ : restrictedGlobalSectionsFreeModule U I ⟶ restrictedGlobalSectionsFreeModule U J) :
    ((X.ofRestrict U.isOpenEmbedding)^*).obj (SheafOfModules.free.{u} I : X.Modules) ⟶
      ((X.ofRestrict U.isOpenEmbedding)^*).obj (SheafOfModules.free.{u} J : X.Modules) :=
  let eI :
      ((X.ofRestrict U.isOpenEmbedding)^*).obj (SheafOfModules.free.{u} I : X.Modules) ≅
        (SheafOfModules.free.{u} I : (restrictedRingedSpace U).Modules) :=
    SheafOfModules.pullbackObjFreeIso
      (RingedSpace.Hom.toRingCatSheafHom (X.ofRestrict U.isOpenEmbedding)) I
  let eJ :
      ((X.ofRestrict U.isOpenEmbedding)^*).obj (SheafOfModules.free.{u} J : X.Modules) ≅
        (SheafOfModules.free.{u} J : (restrictedRingedSpace U).Modules) :=
    SheafOfModules.pullbackObjFreeIso
      (RingedSpace.Hom.toRingCatSheafHom (X.ofRestrict U.isOpenEmbedding)) J
  let m :
      (SheafOfModules.free.{u} I : (restrictedRingedSpace U).Modules) ⟶
        (SheafOfModules.free.{u} J : (restrictedRingedSpace U).Modules) :=
    freeSheafMapOnOpen U ψ
  eI.hom ≫ m ≫ eJ.inv

/-- A morphism between the restrictions of two free `\mathcal O_X`-module sheaves to `U` is
induced by a morphism of free `Γ(U, \mathcal O_U)`-modules if, after transport through the
canonical free-sheaf restriction isomorphisms, it is the induced morphism on the restricted
ringed space. The module map is part of the public data; the concrete bridge to restricted free
sheaves is kept internal. -/
def IsInducedByGlobalSectionsModuleMapOnOpen
    {X : RingedSpace.{u}} (U : Opens X)
    {I J : Type u}
    (φ :
      ((X.ofRestrict U.isOpenEmbedding)^*).obj (SheafOfModules.free.{u} I : X.Modules) ⟶
        ((X.ofRestrict U.isOpenEmbedding)^*).obj (SheafOfModules.free.{u} J : X.Modules)) :
    Prop :=
  ∃ ψ :
      ModuleCat.of ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))
          (I →₀ (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) ⟶
        ModuleCat.of ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))
          (J →₀ (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)),
    φ = restrictedFreeSheafMapOnOpen U ψ

/-- A morphism of free `\mathcal O_X`-module sheaves is locally induced by a module map at `x` if
this happens on some open neighbourhood of `x`. -/
def LocallyIsInducedByGlobalSectionsModuleMapAt
    {X : RingedSpace.{u}}
    (x : X)
    {I J : Type u}
    (φ : (SheafOfModules.free.{u} I : X.Modules) ⟶ SheafOfModules.free.{u} J) : Prop :=
  ∃ (U : Opens X) (_ : x ∈ U),
    IsInducedByGlobalSectionsModuleMapOnOpen U
      (((X.ofRestrict U.isOpenEmbedding)^*).map φ)

-- Proof sketch: unfold `LocallyIsInducedByGlobalSectionsModuleMapAt`; the statement is exactly the
-- defining expansion saying that the restricted morphism is induced by a module map on some
-- neighbourhood of `x`.
/-- A free-sheaf morphism is locally induced by a module map at `x` exactly when some
neighbourhood of `x` carries such a description for its restriction. -/
theorem locallyIsInducedByGlobalSectionsModuleMapAt_iff
    {X : RingedSpace.{u}}
    (x : X)
    {I J : Type u}
    (φ : (SheafOfModules.free.{u} I : X.Modules) ⟶ SheafOfModules.free.{u} J) :
    LocallyIsInducedByGlobalSectionsModuleMapAt x φ ↔
      ∃ (U : Opens X) (_ : x ∈ U),
        IsInducedByGlobalSectionsModuleMapOnOpen U
          (((X.ofRestrict U.isOpenEmbedding)^*).map φ) :=
  Iff.rfl

/-- Two points `(n, x)` and `(m, y)` in countably many copies of `\mathbb R` represent the same
point of the glued real line when the real coordinates agree and the branch index matters only at
the origin. -/
def gluedRealLineSetoid : Setoid (ℕ × ℝ) where
  r a b := a.2 = b.2 ∧ (a.2 = 0 → a.1 = b.1)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ⟨rfl, fun _ ↦ rfl⟩
    · intro a b hab
      rcases hab with ⟨h₂, h₀⟩
      refine ⟨h₂.symm, ?_⟩
      intro hb0
      exact (h₀ (by simpa [h₂] using hb0)).symm
    · intro a b c hab hbc
      rcases hab with ⟨hab₂, hab₀⟩
      rcases hbc with ⟨hbc₂, hbc₀⟩
      refine ⟨hab₂.trans hbc₂, ?_⟩
      intro ha0
      have hb0 : b.2 = 0 := by
        simpa [hab₂] using ha0
      exact (hab₀ ha0).trans (hbc₀ hb0)

/-- The topological space obtained by gluing countably many copies of `\mathbb R` away from the
origin. -/
abbrev gluedRealLine : TopCat :=
  TopCat.of (Quotient gluedRealLineSetoid)

/-- The distinguished origin on the `0`th branch of the glued real line. -/
def gluedRealLineOrigin : gluedRealLine :=
  Quotient.mk'' (0, (0 : ℝ))

/-- The ringed space whose structure sheaf is the sheaf of continuous real-valued functions on the
glued real line. -/
private abbrev continuousRealFunctionsCommRingSheaf (X : TopCat.{0}) :
    TopCat.Sheaf CommRingCat X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ (CommAlgCat.{0} ℝ) CommRingCat)).obj
    (continuousRealFunctionsSheaf X)

/-- The ringed space whose structure sheaf is the sheaf of continuous real-valued functions on the
glued real line. -/
noncomputable def gluedRealLineRingedSpace : RingedSpace :=
  { carrier := gluedRealLine
    presheaf := (continuousRealFunctionsCommRingSheaf gluedRealLine).1
    IsSheaf := (continuousRealFunctionsCommRingSheaf gluedRealLine).2 }

/-- The distinguished glued origin, now regarded as a point of the ringed-space counterexample. -/
noncomputable def gluedRealLinePoint : gluedRealLineRingedSpace := by
  change gluedRealLine
  exact gluedRealLineOrigin

-- Proof sketch: take the ringed space obtained from countably many copies of `\mathbb R` glued at
-- the origin and its sheaf of continuous real-valued functions. The displayed morphism from the
-- countable free module sheaf to the doubly countable free module sheaf is defined by the locally
-- finite family `e_j ↦ \sum_i f_j 1_{L_i} e_{ij}`; the argument in the text shows that on every
-- neighbourhood of the glued point this restriction cannot be represented by a matrix with only
-- finitely many nonzero entries in each column, hence it is not induced by a module map over
-- `Γ(U, \mathcal O_U)`.
/-- Example 17.10.9: on the glued real line with structure sheaf of continuous real-valued
functions, there exists a morphism from the countable free `\mathcal O_X`-module sheaf to the
doubly countable free `\mathcal O_X`-module sheaf whose restriction to no neighbourhood of the
glued origin is induced by a morphism between the corresponding free
`Γ(U, \mathcal O_U)`-modules. In the textbook example, the morphism sends
`e_j` to `\sum_i f_j 1_{L_i} e_{ij}`. -/
theorem gluedRealLine_exists_free_module_sheaf_morphism_not_locally_induced_by_globalSectionsModuleMap :
    ∃ φ :
      (SheafOfModules.free (ULift ℕ) : gluedRealLineRingedSpace.Modules) ⟶
        (SheafOfModules.free (ULift (ℕ × ℕ)) : gluedRealLineRingedSpace.Modules),
      ¬ LocallyIsInducedByGlobalSectionsModuleMapAt gluedRealLinePoint φ := sorry

/-- The glued-line counterexample yields the source-facing existential statement that a morphism of
sheaves associated to free modules need not locally come from a morphism of modules. -/
theorem exists_free_module_sheaf_morphism_not_locally_induced_by_globalSectionsModuleMap :
    ∃ (X : RingedSpace) (x : X),
      ∃ φ :
        (SheafOfModules.free (ULift ℕ) : X.Modules) ⟶
          (SheafOfModules.free (ULift (ℕ × ℕ)) : X.Modules),
        ¬ LocallyIsInducedByGlobalSectionsModuleMapAt x φ := by
  obtain ⟨φ, hφ⟩ :=
    gluedRealLine_exists_free_module_sheaf_morphism_not_locally_induced_by_globalSectionsModuleMap
  exact ⟨gluedRealLineRingedSpace, gluedRealLinePoint, φ, hφ⟩

end AlgebraicGeometry
