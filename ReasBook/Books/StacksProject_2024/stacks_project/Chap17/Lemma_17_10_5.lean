import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap06.Lemma_6_26_4
import StacksProject_2024.Chap17.Definition_17_4_1
import StacksProject_2024.Chap17.Lemma_17_10_4

-- Declarations for this item will be appended below by the statement pipeline.

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
    -- Reduce to the unique nonempty open; on the empty open every endomorphism is forced.
    by_cases hU : PUnit.unit ∈ unop U
    · have hU' : U = op ⊤ := by
        simpa using congrArg op (globalSectionsSourceOpen_eq_top hU)
      subst hU'
      ext x
      simp [globalSectionsSourceModulePresheafObj]
    · simpa [globalSectionsSourceModulePresheafObj, hU] using
        (Subsingleton.elim _ _)
  map_comp := by
    intro U V W i j
    -- Only the `⊤` branch carries information; if the target is `⊥`, all maps coincide.
    by_cases hW : PUnit.unit ∈ unop W
    · have hV : PUnit.unit ∈ unop V := j.unop.le hW
      have hU : PUnit.unit ∈ unop U := i.unop.le hV
      have hU' : U = op ⊤ := by
        simpa using congrArg op (globalSectionsSourceOpen_eq_top hU)
      have hV' : V = op ⊤ := by
        simpa using congrArg op (globalSectionsSourceOpen_eq_top hV)
      have hW' : W = op ⊤ := by
        simpa using congrArg op (globalSectionsSourceOpen_eq_top hW)
      subst hU'
      subst hV'
      subst hW'
      ext x
      simp [globalSectionsSourceModulePresheafObj]
    · simpa [globalSectionsSourceModulePresheafObj, hW] using
        (Subsingleton.elim _ _)

/-- Helper for Lemma 17.10.5: the top-open coefficient ring of the singleton source identifies
with `R`, packaged as a ring equivalence for later transport. -/
private noncomputable abbrev globalSectionsSourceTopRingEquiv
    (R : Type u) [CommRing R] :
    ↑((globalSectionsSourceRingCatSheaf R).obj.obj
        (op (⊤ : Opens globalSectionsSourceSpace))) ≃+* R :=
  (eqToIso (globalSectionsSourceRingCatSheaf_obj_top R)).ringCatIsoToRingEquiv

/-- Helper for Lemma 17.10.5: evaluating a module sheaf on the singleton source at the top open
recovers an `R`-module after transporting scalars along the canonical top-ring identification. -/
private noncomputable abbrev globalSectionsSourceTopModuleObj
    (R : Type u) [CommRing R]
    (𝒢 : SheafOfModules (globalSectionsSourceRingCatSheaf R)) :
    ModuleCat R :=
  ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (globalSectionsSourceTopRingEquiv R)).inverse).obj
    (𝒢.val.obj (op (⊤ : Opens globalSectionsSourceSpace)))

/-- Helper for Lemma 17.10.5: the singleton-source module presheaf is a skyscraper presheaf in
its underlying additive sheaf, so its sheaf condition is inherited from
`skyscraperPresheaf_isSheaf`. -/
private theorem globalSectionsSourceModulePresheaf_isSheaf
    (R : Type u) [CommRing R]
    (M : ModuleCat R) :
    (globalSectionsSourceModulePresheaf R M).presheaf.IsSheaf := by
  -- Proof comment: forgetting scalar actions leaves exactly the additive skyscraper presheaf with
  -- fiber `M` at the unique point of `PUnit`.
  simpa [globalSectionsSourceModulePresheaf, globalSectionsSourceModulePresheafObj,
    globalSectionsSourceRingCatSheaf_obj_top] using
    (skyscraperPresheaf_isSheaf PUnit.unit ((forget₂ (ModuleCat R) AddCommGrpCat).obj M))

private noncomputable def globalSectionsSourceModuleSheaf
    (R : Type u) [CommRing R]
    (M : ModuleCat R) :
    SheafOfModules (globalSectionsSourceRingCatSheaf R) where
  val := globalSectionsSourceModulePresheaf R M
  isSheaf := by
    -- Proof comment: use the underlying additive skyscraper description proved just above.
    simpa using globalSectionsSourceModulePresheaf_isSheaf R M

/-- Helper for Lemma 17.10.5: a morphism out of the singleton-source module sheaf is determined
by its component on the unique nonempty open, then transported back to an `R`-linear map. -/
private noncomputable def globalSectionsSourceModuleSheaf_homEquivTop
    (R : Type u) [CommRing R]
    (M : ModuleCat R)
    (𝒢 : SheafOfModules (globalSectionsSourceRingCatSheaf R)) :
    (globalSectionsSourceModuleSheaf R M ⟶ 𝒢) ≃
      (M ⟶ globalSectionsSourceTopModuleObj R 𝒢) := by
  -- Route correction: the singleton-source functor should be left adjoint, so we need morphisms
  -- *out of* `globalSectionsSourceModuleSheaf R M`, not into it.
  let eTop :
      (globalSectionsSourceModuleSheaf R M ⟶ 𝒢) ≃
        (globalSectionsSourceModulePresheafObj R M (op ⊤) ⟶
          𝒢.val.obj (op (⊤ : Opens globalSectionsSourceSpace))) where
    toFun f := f.val.app (op ⊤)
    invFun φ :=
      { val :=
          { app := fun U ↦ by
              by_cases hU : PUnit.unit ∈ unop U
              · have hU' : U = op ⊤ := by
                  simpa using congrArg op (globalSectionsSourceOpen_eq_top hU)
                subst hU'
                exact φ
              · exact 0
            naturality := by
              intro U V i
              -- Proof comment: only the top-open branch carries information; the empty-open
              -- branch is forced because the source is terminal there.
              by_cases hV : PUnit.unit ∈ unop V
              · have hU : PUnit.unit ∈ unop U := i.unop.le hV
                have hU' : U = op ⊤ := by
                  simpa using congrArg op (globalSectionsSourceOpen_eq_top hU)
                have hV' : V = op ⊤ := by
                  simpa using congrArg op (globalSectionsSourceOpen_eq_top hV)
                subst hU'
                subst hV'
                ext x
                simp [globalSectionsSourceModulePresheafObj]
              · simpa [globalSectionsSourceModulePresheafObj, hV] using
                  (Subsingleton.elim _ _) } }
    left_inv f := by
      ext U
      -- Proof comment: check the unique nonempty open explicitly; on the empty open there is only
      -- one morphism out of the terminal source module.
      by_cases hU : PUnit.unit ∈ unop U
      · have hU' : U = op ⊤ := by
          simpa using congrArg op (globalSectionsSourceOpen_eq_top hU)
        subst hU'
        rfl
      · simpa [globalSectionsSourceModulePresheafObj, hU] using
          (Subsingleton.elim _ _)
    right_inv φ := by
      rfl
  exact
    eTop.trans <|
      by
        -- Proof comment: the top-open module is precisely `M` after transporting scalars across
        -- the canonical ring equivalence on the singleton source.
        simpa [globalSectionsSourceTopModuleObj, globalSectionsSourceModulePresheafObj,
          globalSectionsSourceTopRingEquiv] using
          (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
            (globalSectionsSourceTopRingEquiv R)).homEquiv M
              (𝒢.val.obj (op (⊤ : Opens globalSectionsSourceSpace)))

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
        -- Normalize to the top open when possible; otherwise the empty target makes the square tautological.
        by_cases hV : PUnit.unit ∈ unop V
        · have hU : PUnit.unit ∈ unop U := i.unop.le hV
          have hU' : U = op ⊤ := by
            simpa using congrArg op (globalSectionsSourceOpen_eq_top hU)
          have hV' : V = op ⊤ := by
            simpa using congrArg op (globalSectionsSourceOpen_eq_top hV)
          subst hU'
          subst hV'
          ext x
          simp [globalSectionsSourceModulePresheafObj]
        · simpa [globalSectionsSourceModulePresheafObj, hV] using
            (Subsingleton.elim _ _) }

private noncomputable def globalSectionsSourceModuleFunctor
    (R : Type u) [CommRing R] :
    ModuleCat R ⥤ SheafOfModules (globalSectionsSourceRingCatSheaf R) where
  obj M := globalSectionsSourceModuleSheaf R M
  map f := globalSectionsSourceModuleSheafMap R f
  map_id := by
    intro M
    ext U
    -- Evaluate on the unique nonempty open; on `⊥` the target module is terminal.
    by_cases hU : PUnit.unit ∈ unop U
    · have hU' : U = op ⊤ := by
        simpa using congrArg op (globalSectionsSourceOpen_eq_top hU)
      subst hU'
      ext x
      simp [globalSectionsSourceModuleSheafMap, globalSectionsSourceModulePresheafObj]
    · simpa [globalSectionsSourceModuleSheafMap, globalSectionsSourceModulePresheafObj, hU] using
        (Subsingleton.elim _ _)
  map_comp := by
    intro M N P f g
    ext U
    -- The top-open component is the ordinary module map; the empty-open component is forced.
    by_cases hU : PUnit.unit ∈ unop U
    · have hU' : U = op ⊤ := by
        simpa using congrArg op (globalSectionsSourceOpen_eq_top hU)
      subst hU'
      ext x
      simp [globalSectionsSourceModuleSheafMap, globalSectionsSourceModulePresheafObj]
    · simpa [globalSectionsSourceModuleSheafMap, globalSectionsSourceModulePresheafObj, hU] using
        (Subsingleton.elim _ _)

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
    -- Reduce to `⊤` when the target open is nonempty; otherwise maps into the empty-open ring are unique.
    by_cases hV : PUnit.unit ∈ unop V
    · have hU : PUnit.unit ∈ unop U := i.unop.le hV
      have hU' : U = op ⊤ := by
        simpa using congrArg op (globalSectionsSourceOpen_eq_top hU)
      have hV' : V = op ⊤ := by
        simpa using congrArg op (globalSectionsSourceOpen_eq_top hV)
      subst hU'
      subst hV'
      ext x
      simp [globalSectionsSourceRingedSpace, skyscraperSheaf, skyscraperPresheaf]
    · have hV' : unop V = (⊥ : Opens globalSectionsSourceSpace) := by
        ext y
        cases y
        constructor
        · exact fun hy ↦ (hV hy).elim
        · intro hy
          exact False.elim hy
      let F : TopCat.Sheaf CommRingCat globalSectionsSourceSpace :=
        (TopCat.Sheaf.pushforward CommRingCat (ofHom (ContinuousMap.const X PUnit.unit))).obj X.sheaf
      have hsub :
          Subsingleton
            (((globalSectionsSourceRingedSpace R).presheaf.obj U) ⟶
              F.obj V) := by
        let hTerminal := F.isTerminalOfEqEmpty hV'
        exact ⟨fun f g ↦ hTerminal.hom_ext f g⟩
      exact Subsingleton.elim _ _

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
