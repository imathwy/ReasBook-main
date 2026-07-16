import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Sites.Monoidal
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategoryBasic

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{u}}

local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

/- Domain-style sampling for Lemma 19.8.2:
- primary domain: double-dual evaluation in the monoidal closed category of `𝒪`-module sheaves on
  a ringed site, together with the categorical owner notion of coseparator used only as a bridge
  back to the fixed chapter object `𝒥`;
- inspected owner declarations:
  `ringedSiteModuleCategory`,
  `CategoryTheory.ihom`,
  `CategoryTheory.ihom.ev`,
  `CategoryTheory.IsCoseparator.def`,
  `MonoidalClosed.pre`;
- best owner abstraction: the ambient owner category `ringedSiteModuleCategory J 𝒪`, with the
  source-facing dual notation `ℱ^∨[𝒥] = Hom(ℱ, 𝒥)` built directly on the canonical owner `ihom`,
  and the induced bidual morphism `ℱ ⟶ (ℱ^∨[𝒥])^∨[𝒥]`;
- primitive data: the fixed object `𝒥 : Mod(𝒪)`, the module `ℱ : Mod(𝒪)`, and the explicit
  source hypothesis `h𝒥 : IsCoseparator 𝒥` needed for the injectivity statement;
- derived API: the evaluation-at-`φ` morphism
  `(ℱ^∨[𝒥])^∨[𝒥] ⟶ 𝒥`, the factorization `ev ≫ evaluateAt φ = φ`, and the monomorphism statement
  for `ev`; the abstract coseparator hypothesis belongs on the theorem surface as an explicit
  mathematical input, while the evaluation map remains private bridge data.

Source/core/bridge triage:
- `source-facing`: for the fixed chapter object `𝒥`, the dual owner `ℱ^∨[𝒥] = Hom(ℱ, 𝒥)` together
  with the canonical bidual map `ℱ ⟶ (ℱ^∨[𝒥])^∨[𝒥]` and the mono statement for each `ℱ`;
- `core/canonical`: `ringedSiteModuleCategory J 𝒪`, `ihom`, `ihom.ev`, and `IsCoseparator.def`;
- `bridge/view`: the private evaluation-at-`φ` morphism obtained from `MonoidalClosed.pre`, used
  to reduce the source-facing monomorphism statement to the categorical owner `IsCoseparator.def`.

This file therefore keeps `ℱ ↦ Hom(ℱ, 𝒥)` as the public owner, writes the theorem surface for the
fixed chapter object `𝒥` in the textbook notation `ℱ^∨[𝒥]`, and keeps the `IsCoseparator 𝒥`
hypothesis explicit on the single source-facing mono theorem.
-/

section DualNotation

variable [MonoidalCategory (Mod(𝒪))]
variable [MonoidalClosed (Mod(𝒪))]

notation:max ℱ:max "^∨[" 𝒥:max "]" => Functor.obj (ihom ℱ) 𝒥

end DualNotation

section DoubleDualEvaluation

variable [MonoidalCategory (Mod(𝒪))]
variable [MonoidalClosed (Mod(𝒪))]

/-- Helper for Lemma 19.8.2: the `𝒥`-dual of `ℱ`. -/
private abbrev dual
    (𝒥 ℱ : Mod(𝒪)) :
    Mod(𝒪) :=
  ℱ^∨[𝒥]

/-- Helper for Lemma 19.8.2: currying the left-unitor composite and then evaluating at the unit
object recovers the original morphism. -/
private theorem curry_leftUnitor_comp
    (𝒥 ℱ : Mod(𝒪)) (φ : ℱ ⟶ 𝒥) :
    MonoidalClosed.curry ((λ_ ℱ).hom ≫ φ) ≫
        (MonoidalClosed.unitIsoSelf 𝒥).hom =
      φ := by
  -- Proof comment: rewrite the curried left-unitor map through the unit natural isomorphism, so
  -- the remaining comparison is just naturality followed by cancellation of `unitIsoSelf`.
  let modCat := Mod(𝒪)
  rw [MonoidalClosed.curry_natural_right]
  have hUnit :
      (MonoidalClosed.unitNatIso.app ℱ).hom =
        MonoidalClosed.curry ((λ_ ℱ).hom) := by
    simpa [MonoidalClosed.unitNatIso, MonoidalClosed.curry_eq] using
      (CategoryTheory.unit_conjugateEquiv
        Adjunction.id
        (ihom.adjunction (𝟙_ modCat))
        (MonoidalCategory.leftUnitorNatIso modCat).hom
        ℱ).symm
  rw [← hUnit]
  have hNat :=
    congrArg
      (fun k ↦ k ≫ (MonoidalClosed.unitIsoSelf 𝒥).hom)
      (MonoidalClosed.unitNatIso.hom.naturality φ)
  calc
    (MonoidalClosed.unitNatIso.app ℱ).hom ≫
        (ihom (𝟙_ (Mod(𝒪)))).map φ ≫
        (MonoidalClosed.unitIsoSelf 𝒥).hom =
      φ ≫ (MonoidalClosed.unitNatIso.app 𝒥).hom ≫
        (MonoidalClosed.unitIsoSelf 𝒥).hom := by
        simpa [Category.assoc] using hNat.symm
    _ = φ := by
      simpa [MonoidalClosed.unitIsoSelf, Category.assoc] using
        congrArg (fun k ↦ φ ≫ k) (MonoidalClosed.unitNatIso.app 𝒥).hom_inv_id

variable [BraidedCategory (Mod(𝒪))]

/-- The canonical bidual morphism `\mathcal F \to (\mathcal F^\vee)^\vee`, where
`\mathcal F^\vee = \mathcal H\!\mathit{om}_\mathcal O(\mathcal F, \mathcal J)`. -/
noncomputable def bidualMap
    (𝒥 ℱ : Mod(𝒪)) :
    ℱ ⟶ dual 𝒥 (dual 𝒥 ℱ) :=
  MonoidalClosed.curry ((β_ (dual 𝒥 ℱ) ℱ).hom ≫ (ihom.ev ℱ).app 𝒥)

/-- Evaluation at a morphism `φ : ℱ ⟶ 𝒥`, viewed as a morphism from the `𝒥`-bidual of `ℱ` back
to `𝒥`. -/
private noncomputable def evaluateAt
    (𝒥 ℱ : Mod(𝒪)) (φ : ℱ ⟶ 𝒥) :
    dual 𝒥 (dual 𝒥 ℱ) ⟶ 𝒥 :=
  (MonoidalClosed.pre (MonoidalClosed.curry' φ)).app 𝒥 ≫
    (MonoidalClosed.unitIsoSelf 𝒥).hom

/-- Evaluating the canonical bidual morphism at `φ : ℱ ⟶ 𝒥` recovers `φ`. -/
private theorem bidualMap_comp_evaluateAt
    (𝒥 ℱ : Mod(𝒪)) (φ : ℱ ⟶ 𝒥) :
    bidualMap 𝒥 ℱ ≫ evaluateAt 𝒥 ℱ φ =
      φ := by
  -- Proof comment: move `pre` past the curried bidual map, then normalize the internal
  -- evaluation composite to the left-unitor composite handled by `curry_leftUnitor_comp`.
  let 𝒟 : Mod(𝒪) := dual 𝒥 ℱ
  rw [bidualMap, evaluateAt, ← Category.assoc, MonoidalClosed.curry_pre_app]
  have hInside :
      MonoidalClosed.curry' φ ▷ ℱ ≫ (β_ 𝒟 ℱ).hom ≫
          (ihom.ev ℱ).app 𝒥 =
        (λ_ ℱ).hom ≫ φ := by
    calc
      MonoidalClosed.curry' φ ▷ ℱ ≫ (β_ 𝒟 ℱ).hom ≫
          (ihom.ev ℱ).app 𝒥 =
        (β_ (𝟙_ (Mod(𝒪))) ℱ).hom ≫
          ℱ ◁ MonoidalClosed.curry' φ ≫
          (ihom.ev ℱ).app 𝒥 := by
          simp [Category.assoc]
      _ = (β_ (𝟙_ (Mod(𝒪))) ℱ).hom ≫
            (ρ_ ℱ).hom ≫ φ := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦
              (β_ (𝟙_ (Mod(𝒪))) ℱ).hom ≫ k)
            (MonoidalClosed.whiskerLeft_curry'_ihom_ev_app φ)
      _ = (λ_ ℱ).hom ≫ φ := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ k ≫ φ) (braiding_rightUnitor ℱ)
  rw [hInside]
  exact curry_leftUnitor_comp 𝒥 ℱ φ

end DoubleDualEvaluation

section DoubleDualMono

variable [MonoidalCategory (Mod(𝒪))]
variable [BraidedCategory (Mod(𝒪))]
variable [MonoidalClosed (Mod(𝒪))]

-- Proof sketch: if two maps become equal after postcomposing with the bidual map, then they
-- become equal after postcomposing with every evaluation map `evaluateAt φ`. Since
-- `ev ≫ evaluateAt φ = φ` for all `φ : ℱ ⟶ 𝒥`, the coseparator property of `𝒥` recovers equality of
-- the original maps.
/-- Lemma 19.8.2: if `𝒥` is a coseparator, then the canonical double-dual evaluation morphism
`ℱ ⟶ (ℱ^∨[𝒥])^∨[𝒥]` is monic. -/
theorem bidualMap_mono
    (𝒥 ℱ : Mod(𝒪)) (h𝒥 : IsCoseparator 𝒥) :
    Mono (bidualMap 𝒥 ℱ) where
  right_cancellation {X} g h hgh := by
    -- Proof comment: test equality after postcomposition with every `evaluateAt φ`; the previous
    -- computation turns those tests into equality after every `φ : ℱ ⟶ 𝒥`, and `𝒥` being a
    -- coseparator finishes the cancellation.
    apply IsCoseparator.def h𝒥 g h
    intro φ
    calc
      g ≫ φ =
          g ≫ (bidualMap 𝒥 ℱ ≫ evaluateAt 𝒥 ℱ φ) := by
            rw [bidualMap_comp_evaluateAt]
      _ = g ≫ bidualMap 𝒥 ℱ ≫ evaluateAt 𝒥 ℱ φ := by
            simp [Category.assoc]
      _ = h ≫ bidualMap 𝒥 ℱ ≫ evaluateAt 𝒥 ℱ φ := by
            rw [← Category.assoc, hgh, Category.assoc]
      _ = h ≫ (bidualMap 𝒥 ℱ ≫ evaluateAt 𝒥 ℱ φ) := by
            simp [Category.assoc]
      _ = h ≫ φ := by
            rw [bidualMap_comp_evaluateAt]

end DoubleDualMono

end SheafOfModules.RingedSite
