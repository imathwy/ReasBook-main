import Mathlib
import stacks_project.Chap07.Lemma_7_17_8
import stacks_project.Chap18.Lemma_18_27_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite

noncomputable section

universe u w

namespace SheafOfModules

/- Domain-style sampling for Lemma 18.27.12:
- primary domain: categorical finite presentability in `SheafOfModules 𝒪`, expressed through
  preservation of filtered colimits by the represented functor `Hom_𝒪(ℱ, -)`;
- sampled owner declarations:
  `CategoryTheory.IsFinitelyPresentable`,
  `CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimits`,
  `SheafOfModules.isIso_internalHomColimitComparison_of_isFinitePresentation`,
  `CategoryTheory.GrothendieckTopology.globalSectionsColimitComparison_bijective_of_quasiCompactTestSet`;
- best owner abstraction: the canonical owner is `CategoryTheory.IsFinitelyPresentable ℱ`, with
  the represented functor `coyoneda.obj (op ℱ)` preserving filtered colimits as the standard
  bridge characterization;
- primitive data: a ring-valued sheaf `𝒪`, a finitely presented `\mathcal O`-module `ℱ`, a
  filtered diagram `𝒢`, and the quasi-compact test-set hypothesis on `J`;
- derived API: the fixed-diagram comparison map `colimit.post 𝒢 (coyoneda.obj (op ℱ))`, the
  internal-Hom comparison from Lemma `18.27.11`, and the global-sections comparison from
  Lemma `7.17.8 (4)`.

Source/core/bridge triage:
- `source-facing`: finite presentation of `ℱ` together with the Stacks claim that
  `Hom_𝒪(ℱ, -)` preserves filtered colimits under the quasi-compact test-set hypothesis;
- `core/canonical`: `CategoryTheory.IsFinitelyPresentable ℱ`;
- `bridge/view`: `CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimits` and the
  fixed-diagram comparison map `colimit.post 𝒢 (coyoneda.obj (op ℱ))`. -/

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type u)]
variable {𝒪 : Sheaf J RingCat.{u}}
variable {Λ : Type w} [SmallCategory Λ] [IsFiltered Λ]

-- Proof sketch: apply Lemma `18.27.11` to identify the internal Hom into `colim_λ 𝒢_λ` with the
-- filtered colimit of the internal Homs, then apply Sites, Lemma `7.17.8 (4)` to the resulting
-- filtered diagram of internal Hom sheaves. By the standard owner theorem
-- `isFinitelyPresentable_iff_preservesFilteredColimits`, this upgrades finite presentation of `ℱ`
-- to categorical finite presentability.
/-- Lemma 18.27.12: under the quasi-compact test-set hypothesis of Sites, Lemma `7.17.8 (4)`, a
finitely presented `\mathcal O`-module `\mathcal F` is finitely presentable in the category
`SheafOfModules 𝒪`. Equivalently, the represented functor `Hom_\mathcal O(\mathcal F, -)`
preserves filtered colimits. -/
theorem preservesFilteredColimits_coyoneda_of_isFinitePresentation
    (hJ : ∃ S : Set (Sheaf J (Type u)),
      CategoryTheory.GrothendieckTopology.IsQuasiCompactTestSet J S)
    (ℱ : SheafOfModules.{u} 𝒪) [ℱ.IsFinitePresentation] :
    PreservesFilteredColimits (coyoneda.obj (op ℱ)) := sorry

/-- Lemma 18.27.12: under the quasi-compact test-set hypothesis, a finitely presented
`\mathcal O`-module is finitely presentable in the categorical sense. -/
theorem isFinitelyPresentable_of_isFinitePresentation
    (hJ : ∃ S : Set (Sheaf J (Type u)),
      CategoryTheory.GrothendieckTopology.IsQuasiCompactTestSet J S)
    (ℱ : SheafOfModules.{u} 𝒪) [ℱ.IsFinitePresentation] :
    IsFinitelyPresentable.{u} ℱ := by
  exact
    (isFinitelyPresentable_iff_preservesFilteredColimits :
      IsFinitelyPresentable.{u} ℱ ↔ PreservesFilteredColimits (coyoneda.obj (op ℱ))).2
      (preservesFilteredColimits_coyoneda_of_isFinitePresentation hJ ℱ)

/-- Companion to Lemma 18.27.12: for a fixed filtered diagram `\mathcal G_\lambda`, the canonical
comparison map
`colim_\lambda Hom_\mathcal O(\mathcal F, \mathcal G_\lambda) →
Hom_\mathcal O(\mathcal F, colim_\lambda \mathcal G_\lambda)` is bijective. -/
theorem homColimitComparison_bijective_of_isFinitePresentation
    (hJ : ∃ S : Set (Sheaf J (Type u)),
      CategoryTheory.GrothendieckTopology.IsQuasiCompactTestSet J S)
    (ℱ : SheafOfModules.{u} 𝒪) [ℱ.IsFinitePresentation]
    (𝒢 : Λ ⥤ SheafOfModules.{u} 𝒪)
    [HasColimit 𝒢] [HasColimit (𝒢 ⋙ coyoneda.obj (op ℱ))] :
    Function.Bijective (colimit.post 𝒢 (coyoneda.obj (op ℱ))) := sorry

end SheafOfModules
