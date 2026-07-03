import Mathlib
import StacksProject_2024.Chap18.Definition_18_23_1
import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap18.Example_18_29_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat}

/- Domain-style sampling for Lemma 18.29.3:
- primary domain: finitely presented flat sheaves of modules on a ringed site and their local
  finite-free splitting behavior on iterated slice sites;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.RingedSite.IsFinitePresentation`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.free`;
- best owner abstraction: the chapter owner `ringedSiteModuleCategory J 𝒪`, with the source
  hypotheses carried by the ringed-site owners `IsFinitePresentation` and `IsFlat`;
- primitive data: a module `ℱ : ringedSiteModuleCategory J 𝒪`, the localized restrictions
  `ℱ.over U` and `((ℱ.over U).over V)`, and finite free modules on the iterated localized site
  `((J.over U).over V, ((𝒪.over U).over V))`;
- derived API: the local split inclusion/retraction maps exhibiting each iterated restriction as a
  direct summand of a finite free module.

Source/core/bridge triage:
- `source-facing`: the local direct-summand criterion for finitely presented flat modules on a
  ringed site;
- `core/canonical`: `ringedSiteModuleCategory J 𝒪`,
  `SheafOfModules.RingedSite.IsFinitePresentation`,
  `SheafOfModules.RingedSite.IsFlat`, and `SheafOfModules.free`;
- `bridge/view`: the explicit split maps on the iterated slice sites.

The chapter owner for the local direct-summand condition is already
`IsLocallyDirectSummandOfFiniteFree` from Example `18.29.1`, with
`isLocallyDirectSummandOfFiniteFree_iff` as its explicit split-map companion. This file therefore
keeps the owner theorem primary and derives the textbook split-map form from that owner instead of
maintaining a parallel coordinate-level public API.
-/

-- Proof sketch: finite presentation is local on the ringed site, so after restricting to each
-- object `U` and refining by a cover one obtains a finite global presentation of `ℱ.over U`.
-- Apply the local factorization criterion for flat modules to the relation morphism and the
-- resulting surjection; after refining once more, the surjection factors through a finite free
-- module with zero composite from the relations, so the induced surjection admits a section and
-- `ℱ` becomes locally a direct summand of a finite free module.
/-- Lemma 18.29.3: a finitely presented flat `\mathcal O`-module on a ringed site is locally a
direct summand of a finite free module. -/
theorem isLocallyDirectSummandOfFiniteFree_of_isFinitePresentation_of_flat
    (ℱ : ringedSiteModuleCategory J 𝒪)
    [ℱ.IsFinitePresentation] [IsFlat 𝒪 ℱ] :
    IsLocallyDirectSummandOfFiniteFree ℱ := sorry

-- Proof sketch: apply the owner theorem above and then unpack the owner through
-- `isLocallyDirectSummandOfFiniteFree_iff`.
/-- Unfolding Lemma 18.29.3 recovers the explicit local split-map data on a covering of each
object. -/
theorem exists_cover_directSummandOfFiniteFree_of_isFinitePresentation_of_flat
    (ℱ : ringedSiteModuleCategory J 𝒪)
    [ℱ.IsFinitePresentation] [IsFlat 𝒪 ℱ]
    (U : C) :
    ∃ (I : Type (max u v)) (Ui : I → Over U), (J.over U).CoversTop Ui ∧
      ∀ i : I,
        ∃ (α : Type (max u v)) (_ : Finite α),
          ∃ ι :
              (ℱ.over U).over (Ui i) ⟶
                (SheafOfModules.free α :
                  ringedSiteModuleCategory ((J.over U).over (Ui i))
                    ((𝒪.over U).over (Ui i))),
            ∃ π :
                (SheafOfModules.free α :
                  ringedSiteModuleCategory ((J.over U).over (Ui i))
                    ((𝒪.over U).over (Ui i))) ⟶
                  (ℱ.over U).over (Ui i),
              ι ≫ π = 𝟙 ((ℱ.over U).over (Ui i)) := by
  letI : IsLocallyDirectSummandOfFiniteFree ℱ :=
    isLocallyDirectSummandOfFiniteFree_of_isFinitePresentation_of_flat ℱ
  rcases (isLocallyDirectSummandOfFiniteFree_iff ℱ).mp inferInstance U with
    ⟨I, Ui, hUi, hsplit⟩
  refine ⟨I, Ui, hUi, ?_⟩
  intro i
  rcases hsplit i with ⟨α, hα, ι, π, hπ⟩
  exact ⟨α, hα, ι, π, hπ⟩

end SheafOfModules.RingedSite
