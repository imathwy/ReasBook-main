import Mathlib
import StacksProject_2024.stacks_project.Chap04.Lemma_4_43_3
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategory
import StacksProject_2024.stacks_project.Chap18.Lemma_18_29_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

/- Domain-style sampling for Lemma 18.32.2:
- primary domain: invertible `\mathcal O`-modules on a ringed site and their standard derived
  consequences;
- sampled owner declarations:
  `Functor.IsEquivalence (tensorRight ℒ)`, `SheafOfModules.RingedSite.IsFlat`,
  `IsFinitePresentation`, `IsLocallyDirectSummandOfFiniteFree`, and the internal-Hom owner
  `(ihom ℒ).obj (SheafOfModules.unit (ringSheaf J 𝒪))`;
- source-facing clauses: tensor inverse, flatness, finite presentation, local direct summand of a
  finite free module, and the internal-Hom dual comparison.

This file is an upstream statement dependency for later chapters.  The previous version attempted
large proof constructions through several fragile slice and tensor helpers, which made `.olean`
generation slow or unstable.  Keep the public API available and leave the proofs explicit. -/

section TensorInverse

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "𝒪Mod" => (𝟙_ Mod : Mod)

/-- Lemma 18.32.2 (1): an `\mathcal O`-module on a ringed site is invertible if and only if it
admits a tensor inverse `\mathcal N` with `\mathcal L \otimes_{\mathcal O} \mathcal N \cong
\mathcal O`. -/
theorem isInvertible_iff_exists_tensor_inverse
    (ℒ : Mod) :
    Functor.IsEquivalence (tensorRight ℒ) ↔
      ∃ 𝒩 : Mod, Nonempty ((ℒ ⊗ 𝒩) ≅ 𝒪Mod) := by
  sorry

end TensorInverse

section Flat

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
local notation "Mod" => ringedSiteModuleCategory J 𝒪

/-- Lemma 18.32.2 (2): an invertible `\mathcal O`-module on a ringed site is flat. -/
theorem isFlat_of_isInvertible
    (ℒ : Mod)
    [Functor.IsEquivalence (tensorRight ℒ)] :
    IsFlat 𝒪 ℒ := by
  sorry

end Flat

section FinitePresentation

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [∀ U : C, ∀ X : Over U, HasWeakSheafify ((J.over U).over X) AddCommGrpCat]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]
local notation "Mod" => ringedSiteModuleCategory J 𝒪

/-- Lemma 18.32.2 (3): an invertible `\mathcal O`-module on a ringed site is of finite
presentation. -/
theorem isFinitePresentation_of_isInvertible
    (ℒ : Mod)
    [Functor.IsEquivalence (tensorRight ℒ)] :
    Fact (∀ U : C, (ℒ.over U).IsFinitePresentation) := by
  sorry

end FinitePresentation

section LocalDirectSummand

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
local notation "Mod" => ringedSiteModuleCategory J 𝒪

/-- Lemma 18.32.2 (4): an invertible `\mathcal O`-module on a ringed site is locally a direct
summand of a finite free `\mathcal O`-module. -/
theorem isLocallyDirectSummandOfFiniteFree_of_isInvertible
    (ℒ : Mod)
    [Functor.IsEquivalence (tensorRight ℒ)] :
    IsLocallyDirectSummandOfFiniteFree ℒ := by
  sorry

end LocalDirectSummand

section InternalHom

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]
local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "𝒪Mod" => (𝟙_ Mod : Mod)
set_option quotPrecheck false in
local notation A " ⟶[Mod] " B:10 => ((ihom A).obj B)

/-- Lemma 18.32.2 (5): if `\mathcal L \otimes_{\mathcal O} \mathcal N \cong \mathcal O`, then
`\mathcal N` is canonically isomorphic to the internal-Hom dual
`\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L, \mathcal O)`. -/
noncomputable def iso_internalHom_unit_of_tensor_inverse
    (ℒ 𝒩 : Mod)
    (e : (ℒ ⊗ 𝒩) ≅ 𝒪Mod) :
    𝒩 ≅ (ℒ ⟶[Mod] 𝒪Mod) := by
  sorry

end InternalHom

end SheafOfModules.RingedSite
