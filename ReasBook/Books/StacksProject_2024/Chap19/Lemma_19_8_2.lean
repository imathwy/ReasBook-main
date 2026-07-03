import Mathlib
import StacksProject_2024.Chap18.Example_18_29_1
import StacksProject_2024.Chap18.Lemma_18_19_2
import StacksProject_2024.Chap18.«18_19_2_1»

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open Opposite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{u}}

private abbrev ringSheaf (𝒪 : Sheaf J CommRingCat.{u}) : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪

private abbrev Mod (𝒪 : Sheaf J CommRingCat.{u}) : Type (u + 1) :=
  SheafOfModules.{u} (ringSheaf 𝒪)

/- Domain-style sampling for Lemma 19.8.2:
- primary domain: double-dual evaluation in the monoidal closed category of `𝒪`-module sheaves on
  a ringed site, together with coseparators and the source-facing localization owner for sections;
- inspected owner declarations:
  `ringedSiteModuleCategory`,
  `CategoryTheory.ihom`,
  `CategoryTheory.ihom.ev`,
  `ringedSiteModuleDual`,
  `IsCoseparator.def`,
  `localizedStructureModuleExtensionByZero_homEquiv`;
- best owner abstraction: the ambient owner category `ringedSiteModuleCategory J 𝒪`, with the
  source-facing dual owner `ringedSiteModuleDualTo 𝒥 ℱ = Hom(ℱ, 𝒥)` and the induced bidual
  morphism `ℱ ⟶ (ℱ^∨[𝒥])^∨[𝒥]`; local sections are related to genuine morphisms through the existing bridge
  `localizedStructureModuleExtensionByZero_homEquiv`;
- primitive data: the fixed object `𝒥 : ringedSiteModuleCategory J 𝒪`, the module
  `ℱ : ringedSiteModuleCategory J 𝒪`, and the categorical
  hypothesis `IsCoseparator 𝒥`;
- derived API: the evaluation-at-`φ` morphism, the factorization
  `ev ≫ evaluateAt φ = φ`, and the monomorphism statement for `ev`.

Source/core/bridge triage:
- `source-facing`: the dual owner `ℱ^∨[𝒥] = Hom(ℱ, 𝒥)` for the fixed chosen `𝒥`, together with the
  canonical bidual map `ℱ ⟶ (ℱ^∨[𝒥])^∨[𝒥]`;
- `core/canonical`: `ringedSiteModuleCategory J 𝒪`, `ihom`, `ihom.ev`, `ringedSiteModuleDual`, and
  `IsCoseparator`;
- `bridge/view`: `localizedStructureModuleExtensionByZero_homEquiv`, which converts a section over
  `U` into a morphism from `j_{U!}\mathcal O_U`.

This file therefore keeps `ℱ ↦ Hom(ℱ, 𝒥)` as the public owner, writes its theorem surface in the
textbook notation `ℱ^∨[𝒥]`, and derives the bidual morphism and its monomorphism from the existing
categorical owners `ihom` and `IsCoseparator 𝒥`, instead of replacing them by parallel wrapper
objects.
-/

section DualTo

variable [MonoidalCategory (Mod 𝒪)]
variable [MonoidalClosed (Mod 𝒪)]

/-- The `𝒥`-dual `\mathcal F^\vee = \mathcal H\!\mathit{om}_\mathcal O(\mathcal F, \mathcal J)`
of a module on the ringed site. -/
abbrev ringedSiteModuleDualTo
    (𝒥 : Mod 𝒪) (ℱ : Mod 𝒪) :
    Mod 𝒪 :=
  (ihom ℱ).obj 𝒥

notation:max ℱ:max "^∨[" 𝒥:max "]" => ringedSiteModuleDualTo 𝒥 ℱ

end DualTo

section DoubleDualEvaluation

variable [MonoidalCategory (Mod 𝒪)]
variable [BraidedCategory (Mod 𝒪)]
variable [MonoidalClosed (Mod 𝒪)]

/-- The canonical bidual morphism `\mathcal F \to (\mathcal F^\vee)^\vee`, where
`\mathcal F^\vee = \mathcal H\!\mathit{om}_\mathcal O(\mathcal F, \mathcal J)`. -/
noncomputable def ringedSiteModuleBidualMap
    (𝒥 ℱ : Mod 𝒪) :
    ℱ ⟶ (ℱ^∨[𝒥])^∨[𝒥] :=
  MonoidalClosed.curry ((β_ (ℱ^∨[𝒥]) ℱ).hom ≫ (ihom.ev ℱ).app 𝒥)

/-- Evaluation at a morphism `φ : ℱ ⟶ 𝒥`, viewed as a morphism from the `𝒥`-bidual of `ℱ` back
to `𝒥`. -/
noncomputable def ringedSiteModuleBidualEvaluateAt
    (𝒥 ℱ : Mod 𝒪) (φ : ℱ ⟶ 𝒥) :
    (ℱ^∨[𝒥])^∨[𝒥] ⟶ 𝒥 :=
  (MonoidalClosed.pre (MonoidalClosed.curry' φ)).app 𝒥 ≫
    (MonoidalClosed.unitIsoSelf 𝒥).hom

omit [BraidedCategory (Mod 𝒪)] in
private theorem curry_leftUnitor_comp
    (𝒥 ℱ : Mod 𝒪) (φ : ℱ ⟶ 𝒥) :
    MonoidalClosed.curry ((λ_ ℱ).hom ≫ φ) ≫
        (MonoidalClosed.unitIsoSelf 𝒥).hom =
      φ := by
  rw [curry_natural_right]
  have hUnit :
      (MonoidalClosed.unitNatIso.app ℱ).hom =
        MonoidalClosed.curry ((λ_ ℱ).hom) := by
    simpa [MonoidalClosed.unitNatIso, MonoidalClosed.curry_eq] using
      (CategoryTheory.unit_conjugateEquiv
        Adjunction.id
        (ihom.adjunction (𝟙_ (Mod 𝒪)))
        (MonoidalCategory.leftUnitorNatIso (Mod 𝒪)).hom
        ℱ).symm
  rw [← hUnit]
  have hNat :=
    congrArg
      (fun k ↦ k ≫ (MonoidalClosed.unitIsoSelf 𝒥).hom)
      (unitNatIso.hom.naturality φ)
  calc
    (MonoidalClosed.unitNatIso.app ℱ).hom ≫
        (ihom (𝟙_ (Mod 𝒪))).map φ ≫
        (MonoidalClosed.unitIsoSelf 𝒥).hom =
      φ ≫ (MonoidalClosed.unitNatIso.app 𝒥).hom ≫
        (MonoidalClosed.unitIsoSelf 𝒥).hom := by
        simpa [Category.assoc] using hNat.symm
    _ = φ := by
      simpa [MonoidalClosed.unitIsoSelf, Category.assoc] using
        congrArg (fun k ↦ φ ≫ k) (MonoidalClosed.unitNatIso.app 𝒥).hom_inv_id

/-- Evaluating the canonical bidual morphism at `φ : ℱ ⟶ 𝒥` recovers `φ`. -/
theorem ringedSiteModuleBidualMap_comp_evaluateAt
    (𝒥 ℱ : Mod 𝒪) (φ : ℱ ⟶ 𝒥) :
    ringedSiteModuleBidualMap 𝒥 ℱ ≫
        ringedSiteModuleBidualEvaluateAt 𝒥 ℱ φ =
      φ := by
  rw [ringedSiteModuleBidualMap, ringedSiteModuleBidualEvaluateAt,
    ← Category.assoc, MonoidalClosed.curry_pre_app]
  have hInside :
      MonoidalClosed.curry' φ ▷ ℱ ≫ (β_ (ℱ^∨[𝒥]) ℱ).hom ≫
          (ihom.ev ℱ).app 𝒥 =
        (λ_ ℱ).hom ≫ φ := by
    calc
      MonoidalClosed.curry' φ ▷ ℱ ≫ (β_ (ℱ^∨[𝒥]) ℱ).hom ≫
          (ihom.ev ℱ).app 𝒥 =
        (β_ (𝟙_ (Mod 𝒪)) ℱ).hom ≫
          ℱ ◁ MonoidalClosed.curry' φ ≫
          (ihom.ev ℱ).app 𝒥 := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ k ≫ (ihom.ev ℱ).app 𝒥)
              (BraidedCategory.braiding_naturality (MonoidalClosed.curry' φ) (𝟙 ℱ))
      _ = (β_ (𝟙_ (Mod 𝒪)) ℱ).hom ≫
            (ρ_ ℱ).hom ≫ φ := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ (β_ (𝟙_ (Mod 𝒪)) ℱ).hom ≫ k)
            (MonoidalClosed.whiskerLeft_curry'_ihom_ev_app φ)
      _ = (λ_ ℱ).hom ≫ φ := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ k ≫ φ) (braiding_rightUnitor ℱ)
  calc
    MonoidalClosed.curry
        (MonoidalClosed.curry' φ ▷ ℱ ≫ (β_ (ℱ^∨[𝒥]) ℱ).hom ≫
          (ihom.ev ℱ).app 𝒥) ≫
        (MonoidalClosed.unitIsoSelf 𝒥).hom =
      MonoidalClosed.curry ((λ_ ℱ).hom ≫ φ) ≫
        (MonoidalClosed.unitIsoSelf 𝒥).hom := by
        simpa using
          congrArg
            (fun k ↦ MonoidalClosed.curry k ≫
              (MonoidalClosed.unitIsoSelf 𝒥).hom)
            hInside
    _ = φ := curry_leftUnitor_comp 𝒥 ℱ φ

end DoubleDualEvaluation

variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

section LocalizationBridge

theorem localizedStructureModuleExtensionByZero_homEquiv_comp (U : C)
    {ℱ 𝒢 : Mod 𝒪}
    (δ : localizedStructureModuleExtensionByZero 𝒪 U ⟶ ℱ) (φ : ℱ ⟶ 𝒢) :
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U 𝒢 (δ ≫ φ) =
      (SheafOfModules.evaluation (ringSheaf 𝒪) (op U)).map φ
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ δ) :=
  rfl

variable [Preadditive (Mod 𝒪)]

theorem localizedStructureModuleExtensionByZero_homEquiv_zero (U : C)
    (ℱ : Mod 𝒪) :
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ 0 = 0 := by
  calc
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ 0 =
        localizedStructureModuleExtensionByZero_homEquiv
          J 𝒪 U ℱ
            ((0 : localizedStructureModuleExtensionByZero 𝒪 U ⟶ ℱ) ≫
              (0 : ℱ ⟶ ℱ)) := by simp
    _ =
        (SheafOfModules.evaluation (ringSheaf 𝒪) (op U)).map
            (0 : ℱ ⟶ ℱ)
            (localizedStructureModuleExtensionByZero_homEquiv
              J 𝒪 U ℱ 0) := by
          simpa using
            (localizedStructureModuleExtensionByZero_homEquiv_comp
              U
              (0 : localizedStructureModuleExtensionByZero 𝒪 U ⟶ ℱ)
              (0 : ℱ ⟶ ℱ))
    _ = 0 := by
      have hmap0 :
          (SheafOfModules.evaluation (ringSheaf 𝒪) (op U)).map
              (0 : ℱ ⟶ ℱ) =
            0 := by
            rw [Functor.map_zero]
      rw [hmap0]
      change
        (((0 :
            (SheafOfModules.evaluation (ringSheaf 𝒪) (op U)).obj ℱ ⟶
              (SheafOfModules.evaluation (ringSheaf 𝒪) (op U)).obj ℱ).hom)
          (localizedStructureModuleExtensionByZero_homEquiv
            J 𝒪 U ℱ 0) = 0)
      rw [ModuleCat.hom_zero]
      rfl

end LocalizationBridge

section DoubleDualMono

variable [MonoidalCategory (Mod 𝒪)]
variable [BraidedCategory (Mod 𝒪)]
variable [MonoidalClosed (Mod 𝒪)]
variable [Preadditive (Mod 𝒪)]

-- Proof sketch: for a nonzero local section difference `s - t` over `U`, use
-- `localizedStructureModuleExtensionByZero_homEquiv` to view it as a nonzero morphism
-- `j_{U!}\mathcal O_U ⟶ ℱ`. Since `𝒥` is a coseparator, some `φ : ℱ ⟶ 𝒥` detects that
-- morphism. The factorization `ev ≫ evaluateAt φ = φ` then forces the detected morphism to vanish
-- whenever the image of `s - t` under `ev` vanishes, giving injectivity objectwise and hence
-- monicity of `ev`.
/-- Lemma 19.8.2: if `𝒥` is a coseparator in `Mod(\mathcal O)`, then the canonical double-dual
evaluation morphism `ℱ ⟶ (ℱ^∨)^∨` is a monomorphism. -/
theorem ringedSiteModuleBidualMap_mono_of_isCoseparator
    (𝒥 ℱ : Mod 𝒪) (h𝒥 : IsCoseparator 𝒥) :
    Mono (ringedSiteModuleBidualMap 𝒥 ℱ) := by
  classical
  apply (SheafOfModules.forget (ringSheaf 𝒪)).mono_of_mono_map
  exact PresheafOfModules.mono_of_injective fun U ↦ by
    intro s t hst
    by_contra hne
    let m : (SheafOfModules.evaluation (ringSheaf 𝒪) U).obj ℱ := s - t
    have hm_ne : m ≠ 0 := sub_ne_zero.mpr hne
    let δ :
        localizedStructureModuleExtensionByZero 𝒪 U.unop ⟶ ℱ :=
      (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U.unop ℱ).symm m
    have hδ_ne : δ ≠ 0 := by
      intro hδ
      apply hm_ne
      have := congrArg
        (localizedStructureModuleExtensionByZero_homEquiv
          J 𝒪 U.unop ℱ) hδ
      have hzero_section :
          localizedStructureModuleExtensionByZero_homEquiv
              J 𝒪 U.unop ℱ 0 =
            0 :=
        localizedStructureModuleExtensionByZero_homEquiv_zero
          U.unop ℱ
      simpa [δ, m, hzero_section] using this
    have hst' :
        (ringedSiteModuleBidualMap 𝒥 ℱ).val.app U s =
          (ringedSiteModuleBidualMap 𝒥 ℱ).val.app U t :=
      hst
    have hzero :
        (ringedSiteModuleBidualMap 𝒥 ℱ).val.app U m = 0 := by
      change (ringedSiteModuleBidualMap 𝒥 ℱ).val.app U (s - t) = 0
      calc
        (ringedSiteModuleBidualMap 𝒥 ℱ).val.app U (s - t) =
            (ringedSiteModuleBidualMap 𝒥 ℱ).val.app U s -
              (ringedSiteModuleBidualMap 𝒥 ℱ).val.app U t := by
              exact ((ringedSiteModuleBidualMap 𝒥 ℱ).val.app U).hom.map_sub s t
        _ = 0 := by rw [hst', sub_self]
    have hδev_zero : δ ≫ ringedSiteModuleBidualMap 𝒥 ℱ = 0 := by
      apply (localizedStructureModuleExtensionByZero_homEquiv
        J 𝒪 U.unop _).injective
      change
        localizedStructureModuleExtensionByZero_homEquiv
            J 𝒪 U.unop _ (δ ≫ ringedSiteModuleBidualMap 𝒥 ℱ) =
          localizedStructureModuleExtensionByZero_homEquiv
            J 𝒪 U.unop _ 0
      rw [localizedStructureModuleExtensionByZero_homEquiv_comp]
      rw [localizedStructureModuleExtensionByZero_homEquiv_zero
        U.unop ((ℱ^∨[𝒥])^∨[𝒥])]
      simpa [δ] using hzero
    have hdetect : ∃ φ : ℱ ⟶ 𝒥, δ ≫ φ ≠ 0 := by
      by_contra hdetect
      push Not at hdetect
      apply hδ_ne
      exact (IsCoseparator.def h𝒥 δ 0) fun φ ↦ by simpa using hdetect φ
    obtain ⟨φ, hφ⟩ := hdetect
    have : δ ≫ φ = 0 := by
      calc
        δ ≫ φ =
            δ ≫ ringedSiteModuleBidualMap 𝒥 ℱ ≫
              ringedSiteModuleBidualEvaluateAt 𝒥 ℱ φ := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ δ ≫ k)
                  (ringedSiteModuleBidualMap_comp_evaluateAt 𝒥 ℱ φ).symm
        _ = 0 := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ ringedSiteModuleBidualEvaluateAt 𝒥 ℱ φ) hδev_zero
    exact hφ this

end DoubleDualMono

end SheafOfModules.RingedSite
