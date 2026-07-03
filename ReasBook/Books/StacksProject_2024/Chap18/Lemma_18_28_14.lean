import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]

private abbrev finiteIndex (n : ℕ) : Type u :=
  ULift.{u} (Fin n)

private abbrev localizedModuleCategory
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat) (U : C) :=
  ringedSiteModuleCategory (J.over U) (𝒪.over U)

private abbrev iteratedLocalizedModuleCategory
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat) {U : C} (V : Over U) :=
  ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V)

private abbrev localizedFiniteFreeModule
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat) (U : C) (n : ℕ) :
    localizedModuleCategory J 𝒪 U :=
  SheafOfModules.free (finiteIndex n)

private abbrev iteratedLocalizedFiniteFreeModule
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat) {U : C} (V : Over U) (n : ℕ) :
    iteratedLocalizedModuleCategory J 𝒪 V :=
  SheafOfModules.free (finiteIndex n)

private abbrev iteratedRestriction
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat) {U : C} (V : Over U) :
    localizedModuleCategory J 𝒪 U ⥤ iteratedLocalizedModuleCategory J 𝒪 V :=
  SheafOfModules.pushforward (𝟙 (((ringSheaf J 𝒪).over U).over V))

private def localFiniteFreeFactorization
    (ℱ : ringedSiteModuleCategory J 𝒪) {U : C} {m n : ℕ}
    (relation : localizedFiniteFreeModule J 𝒪 U m ⟶ localizedFiniteFreeModule J 𝒪 U n)
    (s : localizedFiniteFreeModule J 𝒪 U n ⟶ ℱ.over U) : Prop :=
  let Free := localizedFiniteFreeModule J 𝒪 U
  ∃ (I : Type u) (Ui : I → Over U), (J.over U).CoversTop Ui ∧
    ∀ i : I,
      let restriction := iteratedRestriction J 𝒪 (Ui i)
      let Free' := iteratedLocalizedFiniteFreeModule J 𝒪 (Ui i)
      ∃ (l : ℕ)
        (B : restriction.obj (Free n) ⟶ Free' l)
        (t : Free' l ⟶ (ℱ.over U).over (Ui i)),
        restriction.map s = B ≫ t ∧
          restriction.map relation ≫ B = 0

/- Domain-style sampling for Lemma 18.28.14:
- primary domain: flat sheaves of modules on a ringed site, tested by localized finite-free
  factorization criteria;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.free`,
  `SheafOfModules.over`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pushforwardOver`;
- best owner abstraction: the ambient module object should live in the chapter-level owner
  `ringedSiteModuleCategory J 𝒪`, while localization is expressed through the canonical
  restriction objects `ℱ ↦ ℱ.over U`, `((ℱ.over U).over V)`, and the canonical localization
  functor to iterated slice sites;
- primitive data: a module `ℱ : ringedSiteModuleCategory J 𝒪`, finite free modules on localized
  sites, and the further-localization functor from `(C/U, \mathcal O_U)` to
  `((C/U)/V, \mathcal O_V)`;
- derived API: the uniform local finite-free factorization predicate and its source-facing
  one-relation / finite-presentation specializations.

Source/core/bridge triage:
- `source-facing`: the two local factorization predicates and their equivalence with flatness;
- `core/canonical`: `ringedSiteModuleCategory J 𝒪`,
  `SheafOfModules.RingedSite.IsFlat`, `SheafOfModules.free`,
  `SheafOfModules.over`, `SheafOfModules.pushforward`, and
  `SheafOfModules.pushforwardOver`;
- `bridge/view`: the further-localization functor from `ℱ.over U` to `((ℱ.over U).over V)` and
  the uniform factorization predicate `localFiniteFreeFactorization`.

This file should therefore reuse the upstream owner `ringedSiteModuleCategory` from
`Lemma_18_19_2`, with localized finite free modules and iterated restrictions expressed through a
thin internal layer over the chapter's canonical `over` / `pushforward` surface rather than
repeating the raw sheaf expressions in every public statement.
-/

/-- The single-relation local factorization criterion for flatness on a ringed site. -/
def flatSingleRelationFactorization
    (ℱ : ringedSiteModuleCategory J 𝒪) : Prop :=
  ∀ (U : C) (n : ℕ),
    let Free := localizedFiniteFreeModule J 𝒪 U
    ∀ (f : Free 1 ⟶ Free n) (s : Free n ⟶ ℱ.over U) (_ : f ≫ s = 0),
      localFiniteFreeFactorization ℱ f s

/-- The finite-presentation local factorization criterion for flatness on a ringed site. -/
def flatMatrixFactorization
    (ℱ : ringedSiteModuleCategory J 𝒪) : Prop :=
  ∀ (U : C) (m n : ℕ),
    let Free := localizedFiniteFreeModule J 𝒪 U
    ∀ (A : Free m ⟶ Free n) (s : Free n ⟶ ℱ.over U) (_ : A ≫ s = 0),
      localFiniteFreeFactorization ℱ A s

-- Proof sketch: `(1) → (2)` is the standard local syzygy criterion obtained by applying
-- flatness to the ideal generated by one relation. `(2) → (3)` is an induction on the number of
-- columns of the presentation matrix. `(3) → (1)` is the finite-presentation criterion for
-- injectivity after tensoring, using that sections of `ℱ` are filtered colimits of finitely
-- presented modules and then applying the local factorization through finite free modules.
/-- Lemma 18.28.14: for a ringed site `(\mathcal C, \mathcal O)` and an `\mathcal O`-module
`\mathcal F`, flatness of `\mathcal F` is equivalent to the local finite-relation factorization
criterion for one relation and to its finite-presentation version for arbitrary maps
`\mathcal O_U^{\oplus m} \to \mathcal O_U^{\oplus n}`. -/
theorem isFlat_tfae_factorizationCriteria
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    List.TFAE [
      IsFlat 𝒪 ℱ,
      flatSingleRelationFactorization ℱ,
      flatMatrixFactorization ℱ
    ] := sorry

end SheafOfModules.RingedSite
