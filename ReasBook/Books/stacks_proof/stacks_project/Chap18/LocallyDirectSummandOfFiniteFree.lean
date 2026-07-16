import Mathlib
import stacks_proof.stacks_project.Chap18.RingedSiteModuleCategoryBasic

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- A ringed-site module is locally a direct summand of a finite free module if, after passing to a
covering of every object `U`, each restriction `\mathcal F|_{U_i}` is a retract of a finite free
`\mathcal O_{U_i}`-module. -/
class IsLocallyDirectSummandOfFiniteFree (ℱ : ringedSiteModuleCategory J 𝒪) : Prop where
  /-- Every object admits a covering on which the restriction of `ℱ` is a retract of a finite free
  module. -/
  exists_cover_retract_free (U : C) :
    ∃ (I : Type (max u v)) (Ui : I → Over U), (J.over U).CoversTop Ui ∧
      ∀ i : I,
        ∃ α : Type (max u v), Finite α ∧
          Nonempty
            (Retract
              ((ℱ.over U).over (Ui i))
              (SheafOfModules.free α :
                ringedSiteModuleCategory ((J.over U).over (Ui i)) ((𝒪.over U).over (Ui i))))

-- Proof sketch: unpack each local retract into its inclusion and retraction maps, and conversely
-- package explicit split morphisms into `Retract`.
/-- Unfolding `IsLocallyDirectSummandOfFiniteFree` gives the explicit local split-map data on each
localized ringed site. -/
theorem isLocallyDirectSummandOfFiniteFree_iff
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsLocallyDirectSummandOfFiniteFree ℱ ↔
      ∀ U : C,
        ∃ (I : Type (max u v)) (Ui : I → Over U), (J.over U).CoversTop Ui ∧
          ∀ i : I,
            ∃ α : Type (max u v), Finite α ∧
              ∃ ι :
                  (ℱ.over U).over (Ui i) ⟶
                    (SheafOfModules.free α :
                      ringedSiteModuleCategory
                        ((J.over U).over (Ui i)) ((𝒪.over U).over (Ui i))),
                ∃ π :
                    (SheafOfModules.free α :
                      ringedSiteModuleCategory
                        ((J.over U).over (Ui i)) ((𝒪.over U).over (Ui i))) ⟶
                      (ℱ.over U).over (Ui i),
                  ι ≫ π = 𝟙 ((ℱ.over U).over (Ui i)) := by
  constructor
  · intro h U
    rcases h.exists_cover_retract_free U with ⟨I, Ui, hUi, hsplit⟩
    refine ⟨I, Ui, hUi, ?_⟩
    intro i
    rcases hsplit i with ⟨α, hα, ⟨r⟩⟩
    -- Proof comment: unpack the chosen retract into its split inclusion and retraction.
    exact ⟨α, hα, r.i, r.r, r.retract⟩
  · intro h
    refine ⟨fun U ↦ ?_⟩
    rcases h U with ⟨I, Ui, hUi, hsplit⟩
    refine ⟨I, Ui, hUi, ?_⟩
    intro i
    rcases hsplit i with ⟨α, hα, ι, π, hιπ⟩
    -- Proof comment: repackage the explicit split maps as a `Retract`.
    exact ⟨α, hα, ⟨⟨ι, π, hιπ⟩⟩⟩

end SheafOfModules.RingedSite
