import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_49_1 (from Chap21) -/
open CategoryTheory Opposite

noncomputable section

universe u v

namespace RingedSite

section GlobalSections

variable {X : RingedSite.{u, v}}
variable [HasWeakSheafify X.siteTopology AddCommGrpCat]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat]

/-- The ring of global sections `\Gamma(X, \mathcal O_X)` of a ringed site. -/
abbrev globalSectionsRing (X : RingedSite.{u, v}) :=
  RingCat.sectionsSubring X.structureSheaf.obj

private abbrev globalSectionsRingPresheaf (X : RingedSite.{u, v}) :=
  (Functor.const Xᵒᵖ).obj (RingCat.of (globalSectionsRing X))

private abbrev globalSectionsRingHom (X : RingedSite.{u, v}) :
    globalSectionsRingPresheaf X ⟶ X.structureSheaf.obj where
  app U :=
    RingCat.ofHom
      { toFun := fun s ↦ s.1 U
        map_one' := rfl
        map_mul' _ _ := rfl
        map_zero' := rfl
        map_add' _ _ := rfl }
  naturality {U V} f := by
    ext s
    exact (s.2 f).symm

private abbrev globalSectionsPresheaf
    (X : RingedSite.{u, v}) (ℱ : SheafOfModules X.structureSheaf) :
    PresheafOfModules (globalSectionsRingPresheaf X) :=
  (PresheafOfModules.restrictScalars (globalSectionsRingHom X)).obj ℱ.val

private abbrev globalSectionsDiagram
    (X : RingedSite.{u, v}) (ℱ : SheafOfModules X.structureSheaf) :
    Xᵒᵖ ⥤ ModuleCat (globalSectionsRing X) where
  obj := (globalSectionsPresheaf X ℱ).obj
  map := (globalSectionsPresheaf X ℱ).map
  map_id := (globalSectionsPresheaf X ℱ).map_id
  map_comp := (globalSectionsPresheaf X ℱ).map_comp

/-- The global-sections functor on `\mathcal O_X`-modules, valued in modules over
`\Gamma(X, \mathcal O_X)`. -/
noncomputable abbrev moduleGlobalSectionsFunctor (X : RingedSite.{u, v}) :
    SheafOfModules X.structureSheaf ⥤ ModuleCat (globalSectionsRing X) where
  obj ℱ :=
    ModuleCat.of (globalSectionsRing X) (ModuleCat.sectionsSubmodule (globalSectionsDiagram X ℱ))
  map {ℱ 𝒢} φ := by
    let φΓ := (PresheafOfModules.restrictScalars (globalSectionsRingHom X)).map φ.val
    exact ModuleCat.ofHom
      { toFun := fun s ↦
          show (globalSectionsPresheaf X 𝒢).sections from PresheafOfModules.sectionsMap φΓ s
        map_add' s t := by
          apply PresheafOfModules.sections_ext
          intro U
          exact (φΓ.app U).hom.map_add (s.1 U) (t.1 U)
        map_smul' r s := by
          apply PresheafOfModules.sections_ext
          intro U
          exact (φΓ.app U).hom.map_smul r (s.1 U) }
  map_id ℱ := by
    apply ModuleCat.hom_ext
    ext s U
    rfl
  map_comp φ ψ := by
    apply ModuleCat.hom_ext
    ext s U
    rfl

end GlobalSections

end RingedSite

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]

/-
Domain-style sampling for Lemma 21.49.1:
- primary domain: sheaves of modules on a ringed site and finite projective modules over the
  global-sections ring;
- sampled owner declarations:
  `SheafOfModules`,
  `SheafOfModules.IsFiniteFree`,
  `CategoryTheory.ObjectProperty.retractClosure`,
  `RingedSite.globalSectionsRing`,
  `RingedSite.moduleGlobalSectionsFunctor`,
  `FiniteProjectiveModuleCat`;
- best owner abstraction: the primitive owner for the source category is `SheafOfModules 𝒪` for a
  general sheaf of rings `𝒪 : Sheaf J RingCat`, with finite freeness owned by
  `SheafOfModules.IsFiniteFree` and the retract-of-finite-free source condition formed by the
  canonical `ObjectProperty.retractClosure`; the global-sections ring and the module-valued
  global-sections functor are already owned by the bundled ringed-site object `RingedSite`;
- primitive data: a sheaf of rings `𝒪 : Sheaf J RingCat`, an `𝒪`-module, and a finite index type
  only for the upstream `IsFiniteFree` owner witness; the retract condition itself is derived via
  `ObjectProperty.retractClosure`;
- derived API: the full subcategory cut out by that retract closure, and after bundling
  `(\mathcal C, J, \mathcal O)` as a `RingedSite`, the canonical global-sections functor to
  modules over `Γ(\mathcal C, \mathcal O)` together with the source-facing equivalence theorem
  expressed as `Functor.IsEquivalence`.

Source/core/bridge triage:
- `source-facing`: the retract closure of the finite-free owner and its full subcategory on
  `SheafOfModules 𝒪`;
- `core/canonical`: `SheafOfModules 𝒪`, `RingedSite.globalSectionsRing`,
  `RingedSite.moduleGlobalSectionsFunctor`, `FiniteProjectiveModuleCat`,
  `SheafOfModules.IsFiniteFree`, and `ObjectProperty.retractClosure`;
- `bridge/view`: for a bundled `X : RingedSite`, the global-sections functor from the
  source-facing full subcategory of `SheafOfModules X.structureSheaf` to finite projective modules
  over `RingedSite.globalSectionsRing X`.

The old commutative specialization through `ringedSiteModuleCategory` kept the public source
predicate below the true owner level. The refined API below keeps the source-facing
retract-of-finite-free condition directly on `SheafOfModules 𝒪` for general `RingCat`-valued
structure sheaves, but now builds it from the canonical finite-free owner
`SheafOfModules.IsFiniteFree` using `ObjectProperty.retractClosure`; the bundled `RingedSite`
owner is used only for the global-sections bridge.
-/

/-- The object property of `\mathcal O`-modules that are retracts of finite free
`\mathcal O`-modules. -/
abbrev finiteFreeRetractModuleProperty
    (𝒪 : Sheaf J RingCat.{max u v}) :
    ObjectProperty (SheafOfModules 𝒪) :=
  ObjectProperty.retractClosure
    (fun ℱ : SheafOfModules 𝒪 ↦ SheafOfModules.IsFiniteFree ℱ)

/-- The full subcategory of `\mathcal O`-modules that are summands of finite free
`\mathcal O`-modules. -/
abbrev finiteFreeRetractModuleCat
    (𝒪 : Sheaf J RingCat.{max u v}) :=
  (finiteFreeRetractModuleProperty 𝒪).FullSubcategory

end

section

variable {X : RingedSite.{u, v}}
variable [HasWeakSheafify X.siteTopology AddCommGrpCat]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat]

-- Proof sketch: if `ℱ` is a retract of a finite free sheaf `\mathcal O^{\oplus I}`, then taking
-- compatible families of sections identifies `Γ(\mathcal C, ℱ)` with a retract of the finite free
-- `Γ(\mathcal C, \mathcal O)`-module `Γ(\mathcal C, \mathcal O)^{\oplus I}`. A retract of a
-- finite free module is finite projective.
/-- Global sections send a direct summand of a finite free `\mathcal O`-module to a finite
projective module over `\Gamma(\mathcal C, \mathcal O)`. -/
theorem moduleGlobalSections_mem_finiteProjectiveModuleProperty
    (X : RingedSite.{u, v}) (ℱ : finiteFreeRetractModuleCat X.structureSheaf) :
    finiteProjectiveModuleProperty (RingedSite.globalSectionsRing X)
      ((RingedSite.moduleGlobalSectionsFunctor X).obj ℱ.obj) := by
  sorry

/-- The global-sections functor restricted to `\mathcal O`-modules that are direct summands of
finite free `\mathcal O`-modules. -/
noncomputable abbrev finiteFreeRetractGlobalSectionsFunctor
    (X : RingedSite.{u, v}) :
    finiteFreeRetractModuleCat X.structureSheaf ⥤
      FiniteProjectiveModuleCat (RingedSite.globalSectionsRing X) :=
  (finiteProjectiveModuleProperty (RingedSite.globalSectionsRing X)).lift
    ((finiteFreeRetractModuleProperty X.structureSheaf).ι ⋙ RingedSite.moduleGlobalSectionsFunctor X)
    (fun ℱ ↦ moduleGlobalSections_mem_finiteProjectiveModuleProperty X ℱ)

-- Proof sketch: the equivalence is given by the global-sections functor above. A summand of a
-- finite free `\mathcal O`-module goes to a summand of a finite free `Γ(\mathcal C, \mathcal O)`-
-- module, hence to a finite projective module. Conversely, a finite projective
-- `Γ(\mathcal C, \mathcal O)`-module is a summand of a finite free one, and the corresponding
-- constant module sheaf yields an object of `finiteFreeRetractModuleCat 𝒪`. The usual pullback /
-- pushforward adjunction then provides the inverse hom-set comparison.
/-- Lemma 21.49.1: if `R = \Gamma(\mathcal C, \mathcal O)`, then the global-sections functor
identifies the category of `\mathcal O`-modules that are summands of finite free
`\mathcal O`-modules with the category of finite projective `R`-modules. -/
theorem finiteFreeRetractModules_equiv_finiteProjectiveModules
    (X : RingedSite.{u, v}) :
    Functor.IsEquivalence (finiteFreeRetractGlobalSectionsFunctor X) := by
  sorry

end

end CategoryTheory
