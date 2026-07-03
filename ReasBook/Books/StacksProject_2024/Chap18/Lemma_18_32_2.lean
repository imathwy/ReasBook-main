import Mathlib
import StacksProject_2024.Chap18.Definition_18_23_1
import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap18.Definition_18_32_1
import StacksProject_2024.Chap18.Lemma_18_29_2
import StacksProject_2024.Chap18.Lemma_18_29_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalClosed

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
  `SheafOfModules.RingedSite.IsInvertible`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.RingedSite.IsFinitePresentation`,
  `IsLocallyDirectSummandOfFiniteFree`,
  `CategoryTheory.tensorRight_isEquivalence_iff_exists_tensor_inverse`,
  `(ihom ℒ).obj (SheafOfModules.unit (ringSheaf J 𝒪))`,
  `leftDualToRingedSiteModuleDual`,
  `isIso_leftDualToRingedSiteModuleDual`;
- best owner abstractions:
  the chapter owners `IsInvertible`, `IsFlat`,
  `IsFinitePresentation`, `IsLocallyDirectSummandOfFiniteFree`, and the source-facing internal Hom
  to the structure sheaf on `ringedSiteModuleCategory J 𝒪`, together with the Chapter 4 tensor
  inverse owner theorem specialized to `ringedSiteModuleCategory J 𝒪`;
- primitive data:
  an invertible module `ℒ`, the two-sided tensor-inverse witness owned upstream by
  `tensorRight_isEquivalence_iff_exists_tensor_inverse`, its symmetric one-sided reformulation
  `ℒ ⊗ 𝒩 ≅ \mathcal O`, and the source-facing internal-Hom object
  `(ihom ℒ).obj (SheafOfModules.unit (ringSheaf J 𝒪))`;
- derived API:
  flatness, finite presentation, the local direct-summand criterion, and the canonical comparison
  with internal Hom.

Source/core/bridge triage:
- `source-facing`: the five clauses of Stacks Lemma 18.32.2;
- `core/canonical`: `IsInvertible`, `IsFlat`, `IsFinitePresentation`,
  `IsLocallyDirectSummandOfFiniteFree`,
  `tensorRight_isEquivalence_iff_exists_tensor_inverse`,
  `(ihom ℒ).obj (SheafOfModules.unit (ringSheaf J 𝒪))`,
  `leftDualToRingedSiteModuleDual`, and `isIso_leftDualToRingedSiteModuleDual`;
- `bridge/view`: the symmetric one-sided tensor-trivialization statement in clause `(1)`.
-/

section TensorInverse

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]

-- Proof sketch: the canonical owner theorem in Chapter 4 identifies invertibility with a
-- two-sided tensor inverse. In the symmetric monoidal category of `\mathcal O`-modules, the
-- second trivialization is equivalent to the first via the braiding, so the source-facing
-- one-sided statement is equivalent to the owner theorem.
/-- Lemma 18.32.2 (1): an `\mathcal O`-module on a ringed site is invertible if and only if it
admits a tensor inverse `\mathcal N` with `\mathcal L \otimes_{\mathcal O} \mathcal N \cong
\mathcal O`. -/
theorem isInvertible_iff_exists_tensor_inverse
    (ℒ : ringedSiteModuleCategory J 𝒪) :
    IsInvertible ℒ ↔
      ∃ 𝒩 : ringedSiteModuleCategory J 𝒪,
        Nonempty (ℒ ⊗ 𝒩 ≅ SheafOfModules.unit (ringSheaf J 𝒪)) := sorry

end TensorInverse

section Flat

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]

-- Proof sketch: tensoring with an invertible module is an equivalence, hence an exact functor,
-- and flatness is defined by exactness of tensoring with the given module.
/-- Lemma 18.32.2 (2): an invertible `\mathcal O`-module on a ringed site is flat. -/
theorem isFlat_of_isInvertible
    (ℒ : ringedSiteModuleCategory J 𝒪)
    [IsInvertible ℒ] :
    IsFlat 𝒪 ℒ := sorry

end Flat

-- Proof sketch: invertible modules are locally tensor-trivial, hence locally free of rank one;
-- the Chapter 18 ringed-site owner `IsFinitePresentation` is local on restrictions, and free
-- rank-one modules are finitely presented on every localized site.
section FinitePresentation

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [∀ U : C, ∀ X : Over U, HasWeakSheafify ((J.over U).over X) AddCommGrpCat]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]

/-- Lemma 18.32.2 (3): an invertible `\mathcal O`-module on a ringed site is of finite
presentation. -/
theorem isFinitePresentation_of_isInvertible
    (ℒ : ringedSiteModuleCategory J 𝒪)
    [IsInvertible ℒ] :
    IsFinitePresentation ℒ := sorry

end FinitePresentation

section LocalDirectSummand

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : C, ∀ X : Over U, HasWeakSheafify ((J.over U).over X) AddCommGrpCat]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]

-- Proof sketch: combine the flatness from clause (2) with clause (3), then apply the canonical
-- local direct-summand criterion of Lemma `18.29.3`.
/-- Lemma 18.32.2 (4): an invertible `\mathcal O`-module on a ringed site is locally a direct
summand of a finite free `\mathcal O`-module. Equivalently, for every object `U`, after passing to
a covering of `U`, the restriction becomes a direct summand of a finite free `\mathcal O_U`-module.
-/
theorem isLocallyDirectSummandOfFiniteFree_of_isInvertible
    (ℒ : ringedSiteModuleCategory J 𝒪)
    [IsInvertible ℒ] :
    IsLocallyDirectSummandOfFiniteFree ℒ := sorry

end LocalDirectSummand

section InternalHom

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]

-- Proof sketch: the trivialization `e` supplies left-duality data for `𝒩` against `ℒ`; reuse
-- the owner comparison morphism from Lemma `18.29.2` rather than restating the conclusion as a
-- chosen comparison morphism. The chosen exact pairing remains private proof scaffolding, while
-- the public clause stays source-facing as an existential isomorphism.
private theorem nonempty_exactPairing_of_tensor_inverse
    (ℒ 𝒩 : ringedSiteModuleCategory J 𝒪)
    (e : ℒ ⊗ 𝒩 ≅ SheafOfModules.unit (ringSheaf J 𝒪)) :
    Nonempty (ExactPairing 𝒩 ℒ) := sorry

@[implicit_reducible] private noncomputable def exactPairingOfTensorInverse
    (ℒ 𝒩 : ringedSiteModuleCategory J 𝒪)
    (e : ℒ ⊗ 𝒩 ≅ SheafOfModules.unit (ringSheaf J 𝒪)) :
    ExactPairing 𝒩 ℒ :=
  Classical.choice (nonempty_exactPairing_of_tensor_inverse ℒ 𝒩 e)

/-- Lemma 18.32.2 (5): if `\mathcal L \otimes_{\mathcal O} \mathcal N \cong \mathcal O`, then
`\mathcal N` is isomorphic to the internal-Hom dual
`\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L, \mathcal O)`. -/
theorem nonempty_iso_ringedSiteModuleDual_of_tensor_inverse
    (ℒ 𝒩 : ringedSiteModuleCategory J 𝒪)
    (e : ℒ ⊗ 𝒩 ≅ SheafOfModules.unit (ringSheaf J 𝒪)) :
    Nonempty (𝒩 ≅ ringedSiteModuleDual ℒ) := by
  letI : ExactPairing 𝒩 ℒ := exactPairingOfTensorInverse ℒ 𝒩 e
  letI : IsIso (leftDualToRingedSiteModuleDual ℒ 𝒩) :=
    isIso_leftDualToRingedSiteModuleDual ℒ 𝒩
  exact ⟨asIso (leftDualToRingedSiteModuleDual ℒ 𝒩)⟩

end InternalHom

end SheafOfModules.RingedSite
