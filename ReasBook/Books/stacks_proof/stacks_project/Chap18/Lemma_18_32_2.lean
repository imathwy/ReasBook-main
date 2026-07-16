import Mathlib
import stacks_proof.stacks_project.Chap04.Lemma_4_43_3
import stacks_proof.stacks_project.Chap18.RingedSiteModuleCategory
import stacks_proof.stacks_project.Chap18.Lemma_18_29_2

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

local notation "IsFinitePresentation" => fun (ℱ : ringedSiteModuleCategory J 𝒪) ↦
  Fact (∀ U : C, (ℱ.over U).IsFinitePresentation)

/- Domain-style sampling for Lemma 18.32.2:
- primary domain: invertible `\mathcal O`-modules on a ringed site and their standard derived
  consequences;
- sampled owner declarations:
  `Functor.IsEquivalence (tensorRight ℒ)`,
  `CategoryTheory.ExactPairing`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.RingedSite.IsFinitePresentation`,
  `IsLocallyDirectSummandOfFiniteFree`,
  `SheafOfModules.RingedSite.exactPairing_isLocallyDirectSummandOfFiniteFree`,
  `SheafOfModules.RingedSite.isIso_curry_exactPairingEvaluation`,
  `(ihom ℒ).obj (SheafOfModules.unit (ringSheaf J 𝒪))`,
  `CategoryTheory.tensorRight_isEquivalence_iff_exists_tensor_inverse`;
- best owner abstractions:
  the canonical tensor-right equivalence owner together with `IsFlat`,
  `IsFinitePresentation`, the exact-pairing owner `ExactPairing 𝒩 ℒ`, and its chapter-level
  derived API `exactPairing_isLocallyDirectSummandOfFiniteFree` and
  `isIso_curry_exactPairingEvaluation`, together with the source-facing internal Hom to the
  structure sheaf on `ringedSiteModuleCategory J 𝒪`;
- primitive data:
  a module `ℒ` with `Functor.IsEquivalence (tensorRight ℒ)`, and the two-sided tensor-inverse
  witness owned upstream by `tensorRight_isEquivalence_iff_exists_tensor_inverse`, the
  source-facing one-sided trivialization `ℒ ⊗ 𝒩 ≅ \mathcal O`, and the resulting exact pairing
  `ExactPairing 𝒩 ℒ`;
- derived API:
  flatness, finite presentation, the local direct-summand criterion, and the canonical comparison
  with internal Hom.

Source/core/bridge triage:
- `source-facing`: the five clauses of Stacks Lemma 18.32.2;
- `core/canonical`: `Functor.IsEquivalence (tensorRight ℒ)`, `IsFlat`,
  `IsFinitePresentation`,
  `IsLocallyDirectSummandOfFiniteFree`,
  `tensorRight_isEquivalence_iff_exists_tensor_inverse`, `ExactPairing 𝒩 ℒ`,
  `(ihom ℒ).obj (SheafOfModules.unit (ringSheaf J 𝒪))`,
  `exactPairing_isLocallyDirectSummandOfFiniteFree`, and
  `isIso_curry_exactPairingEvaluation`;
- `bridge/view`: the symmetric one-sided tensor-trivialization statement in clause `(1)`.
-/

section TensorInverse

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "𝒪Mod" => (𝟙_ Mod : Mod)

-- Proof sketch: the canonical owner theorem in Chapter 4 identifies invertibility with a
-- two-sided tensor inverse. In the symmetric monoidal category of `\mathcal O`-modules, the
-- second trivialization is equivalent to the first via the braiding, so the source-facing
-- one-sided statement is equivalent to the owner theorem.
/-- Lemma 18.32.2 (1): an `\mathcal O`-module on a ringed site is invertible if and only if it
admits a tensor inverse `\mathcal N` with `\mathcal L \otimes_{\mathcal O} \mathcal N \cong
\mathcal O`. -/
@[stacks 0B8N]
theorem isInvertible_iff_exists_tensor_inverse
    (ℒ : Mod) :
    Functor.IsEquivalence (tensorRight ℒ) ↔
      ∃ 𝒩 : Mod, Nonempty ((ℒ ⊗ 𝒩) ≅ 𝒪Mod) := by
  constructor
  · intro hℒ
    rcases (tensorRight_isEquivalence_iff_exists_tensor_inverse ℒ).1 hℒ with
      ⟨𝒩, ⟨⟨e⟩, -⟩⟩
    exact ⟨𝒩, ⟨e⟩⟩
  · rintro ⟨𝒩, ⟨e⟩⟩
    exact (tensorRight_isEquivalence_iff_exists_tensor_inverse ℒ).2
      ⟨𝒩, ⟨⟨e⟩, ⟨(β_ 𝒩 ℒ) ≪≫ e⟩⟩⟩

end TensorInverse

section TensorInverseExactPairing

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "𝒪Mod" => (𝟙_ Mod : Mod)

/-- Helper for Lemma 18.32.2: after expanding the swapped evaluation map, the first triangle
composite is exactly the braiding from `𝒩 ⊗ \mathcal O` to `\mathcal O ⊗ 𝒩`. -/
private theorem tensor_inverse_left_triangle_normal_form
    (ℒ 𝒩 : Mod)
    (e : (ℒ ⊗ 𝒩) ≅ 𝒪Mod) :
    𝒩 ◁ e.inv ≫
        (α_ _ _ _).inv ≫
        (((β_ 𝒩 ℒ).hom ≫ e.hom) ▷ 𝒩) =
      (β_ 𝒩 𝒪Mod).hom := by
  -- Proof comment: first expose the hexagon branch sending `𝒩` past `ℒ ⊗ 𝒩`, then use braiding
  -- naturality to move the tensor trivialization `e` across the remaining braiding.
  rw [whiskerRight_comp, Category.assoc]
  calc
    𝒩 ◁ e.inv ≫
        (α_ _ _ _).inv ≫
        ((β_ 𝒩 ℒ).hom ▷ 𝒩) ≫
        (e.hom ▷ 𝒩) =
      𝒩 ◁ e.inv ≫
        (β_ 𝒩 (ℒ ⊗ 𝒩)).hom ≫
        (e.hom ▷ 𝒩) := by
          simpa [Category.assoc] using
            (BraidedCategory.hexagon_forward_assoc (X := 𝒩) (Y := ℒ) (Z := 𝒩)).symm
    _ = (β_ 𝒩 𝒪Mod).hom := by
      simpa [Category.assoc] using
        (CategoryTheory.BraidedCategory.braiding_naturality (𝟙 𝒩) e.hom).symm

/-- Helper for Lemma 18.32.2: the coevaluation and evaluation maps coming from a tensor
trivialization satisfy the first triangle identity for the induced exact pairing. -/
private theorem tensor_inverse_coevaluation_evaluation
    (ℒ 𝒩 : Mod)
    (e : (ℒ ⊗ 𝒩) ≅ 𝒪Mod) :
    𝒩 ◁ e.inv ≫
        (α_ _ _ _).inv ≫
        (((β_ 𝒩 ℒ) ≪≫ e).hom ▷ 𝒩) =
      (ρ_ 𝒩).hom ≫
        (λ_ 𝒩).inv := by
  -- Route correction: normalize the tensor-trivialization into an exposed braiding/evaluation
  -- composite, then collapse the remaining coherence against the unit object.
  rw [Iso.trans_hom]
  -- Proof comment: the normal-form lemma isolates the braiding with the tensor unit.
  rw [tensor_inverse_left_triangle_normal_form]
  -- Proof comment: the standard braiding-unitor coherence identifies that braiding with the
  -- desired right-unitor/left-unitor composite.
  simpa using BraidedCategory.braiding_tensorUnit_right 𝒩

/-- Helper for Lemma 18.32.2: after expanding the swapped evaluation map, the second triangle
composite is exactly the braiding from `\mathcal O \otimes \mathcal L` to
`\mathcal L \otimes \mathcal O`. -/
private theorem tensor_inverse_right_triangle_normal_form
    (ℒ 𝒩 : Mod)
    (e : (ℒ ⊗ 𝒩) ≅ 𝒪Mod) :
    e.inv ▷ ℒ ≫
        (α_ _ _ _).hom ≫
        ℒ ◁ ((β_ 𝒩 ℒ).hom ≫ e.hom) =
      (β_ 𝒪Mod ℒ).hom := by
  -- Proof comment: first expose the reverse-hexagon branch sending `ℒ ⊗ 𝒩` past `ℒ`, then use
  -- braiding naturality to move the tensor trivialization `e` across the remaining braiding.
  rw [whiskerLeft_comp, Category.assoc]
  calc
    e.inv ▷ ℒ ≫
        (α_ _ _ _).hom ≫
        ℒ ◁ (β_ 𝒩 ℒ).hom ≫
        ℒ ◁ e.hom =
      e.inv ▷ ℒ ≫
        (β_ (ℒ ⊗ 𝒩) ℒ).hom ≫
        (ℒ ◁ e.hom) := by
          simpa [Category.assoc] using
            BraidedCategory.hexagon_reverse_assoc (X := ℒ) (Y := 𝒩) (Z := ℒ)
    _ = (β_ 𝒪Mod ℒ).hom := by
      simpa [Category.assoc] using
        CategoryTheory.BraidedCategory.braiding_naturality e.hom (𝟙 ℒ)

/-- Helper for Lemma 18.32.2: the same tensor-trivialization data also satisfies the second
triangle identity for the induced exact pairing. -/
private theorem tensor_inverse_evaluation_coevaluation
    (ℒ 𝒩 : Mod)
    (e : (ℒ ⊗ 𝒩) ≅ 𝒪Mod) :
    e.inv ▷ ℒ ≫
        (α_ _ _ _).hom ≫
        ℒ ◁ ((β_ 𝒩 ℒ) ≪≫ e).hom =
      (λ_ ℒ).hom ≫
        (ρ_ ℒ).inv := by
  -- Route correction: rewrite the swapped evaluation as a braiding followed by `e.hom`, then
  -- reduce to the symmetric unit-triangle coherence on `ℒ`.
  rw [Iso.trans_hom]
  -- Proof comment: the normal-form lemma isolates the braiding with the tensor unit.
  rw [tensor_inverse_right_triangle_normal_form]
  -- Proof comment: the standard braiding-unitor coherence identifies that braiding with the
  -- desired left-unitor/right-unitor composite.
  simpa using BraidedCategory.braiding_tensorUnit_left ℒ

/-- A tensor-trivialization `\mathcal L \otimes_{\mathcal O} \mathcal N \cong \mathcal O`
canonically determines an exact pairing with `\mathcal N` as the left dual of `\mathcal L`. -/
private noncomputable def exactPairingOfTensorInverse
    (ℒ 𝒩 : Mod)
    (e : (ℒ ⊗ 𝒩) ≅ 𝒪Mod) :
    ExactPairing 𝒩 ℒ :=
  letI : ExactPairing ℒ 𝒩 :=
    { coevaluation' := e.inv
      evaluation' := ((β_ 𝒩 ℒ) ≪≫ e).hom
      coevaluation_evaluation' := tensor_inverse_coevaluation_evaluation ℒ 𝒩 e
      evaluation_coevaluation' := tensor_inverse_evaluation_coevaluation ℒ 𝒩 e }
  BraidedCategory.exactPairing_swap ℒ 𝒩

end TensorInverseExactPairing

section Flat

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
local notation "Mod" => ringedSiteModuleCategory J 𝒪

/-- Helper for Lemma 18.32.2: tensoring on the right with an invertible module is exact because an
equivalence preserves finite limits and finite colimits. -/
private theorem exact_tensorRight_of_isInvertible
    (ℒ : Mod)
    [Functor.IsEquivalence (tensorRight ℒ)] :
    exactFunctor Mod Mod (tensorRight ℒ) := by
  -- An equivalence automatically preserves the finite limits and colimits used by
  -- `exactFunctor_iff`.
  exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩

-- Proof sketch: tensoring with an invertible module is an equivalence, hence an exact functor,
-- and flatness is defined by exactness of tensoring with the given module.
/-- Lemma 18.32.2 (2): an invertible `\mathcal O`-module on a ringed site is flat. -/
@[stacks 0B8N]
theorem isFlat_of_isInvertible
    (ℒ : Mod)
    [Functor.IsEquivalence (tensorRight ℒ)] :
    IsFlat 𝒪 ℒ := by
  -- Flatness is the owner predicate asserting exactness of `tensorRight ℒ`.
  exact ⟨exact_tensorRight_of_isInvertible (𝒪 := 𝒪) ℒ⟩

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
local notation "Mod" => ringedSiteModuleCategory J 𝒪

/-- Helper for Lemma 18.32.2: on an iterated slice site, restricting a finite presentation to a
further slice keeps the same finite generator and relation index types. -/
private theorem presentation_map_isFinite_on_iterated_slice
    {U : C} {X : Over U}
    {M : ringedSiteModuleCategory ((J.over U).over X) ((𝒪.over U).over X)}
    (P : M.Presentation) [P.IsFinite] (Y : Over X) :
    ((P.map (pushforward (𝟙 ((((𝒪.over U).over X).over Y)))) (by rfl))).IsFinite := by
  -- Proof comment: `Presentation.map` keeps the same generator and relation index types, so
  -- finiteness is inherited directly after unfolding the mapped presentation.
  refine ⟨?_, ?_⟩
  · dsimp [SheafOfModules.Presentation.map, SheafOfModules.presentationOfIsCokernelFree,
      SheafOfModules.generatorsOfIsCokernelFree]
    refine ⟨?_⟩
    change Finite P.generators.I
    infer_instance
  · dsimp [SheafOfModules.Presentation.map, SheafOfModules.presentationOfIsCokernelFree,
      SheafOfModules.relationsOfIsCokernelFree]
    infer_instance

/-- Helper for Lemma 18.32.2: on an iterated slice site, a finite global presentation upgrades to
the owner `IsFinitePresentation`. -/
private theorem isFinitePresentation_of_finite_presentation_on_iterated_slice
    {U : C} {X : Over U}
    {M : ringedSiteModuleCategory ((J.over U).over X) ((𝒪.over U).over X)}
    (P : M.Presentation) [P.IsFinite] :
    M.IsFinitePresentation := by
  -- Proof comment: use the trivial-cover quasicoherent data from `P`; each restricted
  -- presentation stays finite by the previous restriction lemma.
  refine ⟨P.quasicoherentData, ?_⟩
  constructor
  intro Y
  simpa using presentation_map_isFinite_on_iterated_slice (𝒪 := 𝒪) (P := P) Y

/-- Helper for Lemma 18.32.2: on an iterated slice site, a retract of a finite free module is
finitely presented. -/
private theorem isFinitePresentation_of_retract_free_on_iterated_slice
    {U : C} {X : Over U} {α : Type (max u v)} [Finite α]
    {M : ringedSiteModuleCategory ((J.over U).over X) ((𝒪.over U).over X)}
    (hret : Retract M (SheafOfModules.free α)) :
    M.IsFinitePresentation := by
  let φ :
      (SheafOfModules.free α :
        ringedSiteModuleCategory ((J.over U).over X) ((𝒪.over U).over X)) ⟶
      (SheafOfModules.free α :
        ringedSiteModuleCategory ((J.over U).over X) ((𝒪.over U).over X)) :=
    𝟙 _ - hret.r ≫ hret.i
  have hφr : φ ≫ hret.r = 0 := by
    -- Proof comment: the split identity `hret.i ≫ hret.r = 𝟙` annihilates the cokernel map.
    simp [φ, Category.assoc, hret.retract]
  have hcok : IsColimit (CokernelCofork.ofπ hret.r hφr) := by
    -- Proof comment: any cofork vanishing on `φ` factors uniquely through the retraction map.
    refine CokernelCofork.IsColimit.ofπ' hret.r hφr ?_
    intro Z s hs
    refine ⟨hret.i ≫ s.π, ?_⟩
    have hs' : s.π = hret.r ≫ hret.i ≫ s.π := by
      have hs'' : s.π - hret.r ≫ hret.i ≫ s.π = 0 := by
        simpa [φ, Category.assoc] using hs
      exact sub_eq_zero.mp hs''
    simpa [Category.assoc] using hs'
  let P : M.Presentation :=
    SheafOfModules.presentationOfIsCokernelFree φ hret.r hφr hcok
  let _ : P.IsFinite := by
    -- Proof comment: the cokernel presentation uses the same finite free index type `α` for both
    -- generators and relations.
    refine ⟨?_, ?_⟩
    · dsimp [P, SheafOfModules.presentationOfIsCokernelFree,
        SheafOfModules.generatorsOfIsCokernelFree]
      refine ⟨?_⟩
      infer_instance
    · dsimp [P, SheafOfModules.presentationOfIsCokernelFree,
        SheafOfModules.relationsOfIsCokernelFree]
      infer_instance
  exact isFinitePresentation_of_finite_presentation_on_iterated_slice (𝒪 := 𝒪) P

/-- Helper for Lemma 18.32.2: on a ringed site, a module that is locally a direct summand of a
finite free module is finitely presented. -/
private theorem sheaf_isFinitePresentation_of_coversTop
    {U : C}
    {M : ringedSiteModuleCategory (J.over U) (𝒪.over U)}
    {I : Type (max u v)} (X : I → Over U)
    (hX : (J.over U).CoversTop X)
    (hfp : ∀ i : I, ((M.over (X i))).IsFinitePresentation) :
    M.IsFinitePresentation := by
  let D : ∀ i : I, ((M.over (X i))).QuasicoherentData :=
    fun i ↦ by
      let _ : ((M.over (X i))).IsFinitePresentation := hfp i
      exact (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
        (M.over (X i))).choose
  let q : M.QuasicoherentData :=
    SheafOfModules.QuasicoherentData.bind M X hX D
  let _ : q.IsFinitePresentation := by
    refine ⟨?_⟩
    intro ij
    dsimp [q, D, SheafOfModules.QuasicoherentData.bind]
    infer_instance
  exact ⟨q, inferInstance⟩

/-- Helper for Lemma 18.32.2: on a ringed site, a module that is locally a direct summand of a
finite free module is finitely presented. -/
private theorem isFinitePresentation_of_locallyDirectSummandOfFiniteFree
    (ℱ : Mod)
    (hℱ : IsLocallyDirectSummandOfFiniteFree ℱ) :
    IsFinitePresentation ℱ := by
  -- Route correction: port the Chapter 17 retract-of-finite-free presentation argument directly on
  -- each slice site, then glue the local finite-presentation data with `QuasicoherentData.bind`.
  refine ⟨?_⟩
  intro U
  rcases (isLocallyDirectSummandOfFiniteFree_iff ℱ).mp hℱ U with
    ⟨I, Ui, hUi, hsplit⟩
  refine sheaf_isFinitePresentation_of_coversTop (𝒪 := 𝒪) (M := ℱ.over U) Ui hUi ?_
  intro i
  rcases hsplit i with ⟨α, hα, ι, π, hιπ⟩
  let _ : Finite α := hα
  let hret :
      Retract
        ((ℱ.over U).over (Ui i))
        (SheafOfModules.free α :
          ringedSiteModuleCategory ((J.over U).over (Ui i)) ((𝒪.over U).over (Ui i))) :=
    ⟨⟨ι, π, hιπ⟩⟩
  -- Proof comment: on each cover member the split maps exhibit the iterated restriction as a
  -- retract of a finite free sheaf, so the previous bridge applies.
  exact isFinitePresentation_of_retract_free_on_iterated_slice (𝒪 := 𝒪) hret

/-- Helper for Lemma 18.32.2: a tensor inverse for `\mathcal L` yields the exact pairing needed
to conclude that `\mathcal L` is locally a direct summand of a finite free module. -/
private theorem isLocallyDirectSummandOfFiniteFree_of_tensorRight_equivalence
    (ℒ : Mod)
    [Functor.IsEquivalence (tensorRight ℒ)] :
    IsLocallyDirectSummandOfFiniteFree ℒ := by
  rcases (isInvertible_iff_exists_tensor_inverse ℒ).1 inferInstance with ⟨𝒩, ⟨e⟩⟩
  letI : ExactPairing 𝒩 ℒ :=
    exactPairingOfTensorInverse ℒ 𝒩 e
  exact exactPairing_isLocallyDirectSummandOfFiniteFree ℒ 𝒩

/-- Lemma 18.32.2 (3): an invertible `\mathcal O`-module on a ringed site is of finite
presentation. -/
@[stacks 0B8N]
theorem isFinitePresentation_of_isInvertible
    (ℒ : Mod)
    [Functor.IsEquivalence (tensorRight ℒ)] :
    IsFinitePresentation ℒ := by
  let hℒ : IsLocallyDirectSummandOfFiniteFree ℒ :=
    isLocallyDirectSummandOfFiniteFree_of_tensorRight_equivalence (𝒪 := 𝒪) ℒ
  -- Finite presentation is the local retract consequence promised by the textbook proof.
  exact isFinitePresentation_of_locallyDirectSummandOfFiniteFree (𝒪 := 𝒪) ℒ hℒ

end FinitePresentation

section LocalDirectSummand

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
local notation "Mod" => ringedSiteModuleCategory J 𝒪

-- Proof sketch: choose a tensor inverse `\mathcal N` using clause `(1)`, package the
-- trivialization `\mathcal L \otimes_{\mathcal O} \mathcal N \cong \mathcal O` as an exact
-- pairing `ExactPairing 𝒩 ℒ`, and apply the canonical Chapter `18` owner theorem
-- `exactPairing_isLocallyDirectSummandOfFiniteFree`.
/-- Lemma 18.32.2 (4): an invertible `\mathcal O`-module on a ringed site is locally a direct
summand of a finite free `\mathcal O`-module. Equivalently, for every object `U`, after passing to
a covering of `U`, the restriction becomes a direct summand of a finite free `\mathcal O_U`-module.
-/
@[stacks 0B8N]
theorem isLocallyDirectSummandOfFiniteFree_of_isInvertible
    (ℒ : Mod)
    [Functor.IsEquivalence (tensorRight ℒ)] :
    IsLocallyDirectSummandOfFiniteFree ℒ := by
  exact isLocallyDirectSummandOfFiniteFree_of_tensorRight_equivalence (𝒪 := 𝒪) ℒ

end LocalDirectSummand

section InternalHom

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]
local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "𝒪Mod" => (𝟙_ Mod : Mod)
set_option quotPrecheck false in
local notation A " ⟶[Mod] " B:10 => ((ihom A).obj B)

-- Proof sketch: the trivialization `e` supplies left-duality data for `𝒩` against `ℒ`, and
-- `isIso_curry_exactPairingEvaluation` from Lemma `18.29.2` identifies that left dual directly
-- with the internal-Hom dual. No local direct-summand hypothesis belongs in the public API of
-- this clause.

/-- Lemma 18.32.2 (5): if `\mathcal L \otimes_{\mathcal O} \mathcal N \cong \mathcal O`, then
`\mathcal N` is canonically isomorphic to the internal-Hom dual
`\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L, \mathcal O)`. -/
@[stacks 0B8N]
noncomputable def iso_internalHom_unit_of_tensor_inverse
    (ℒ 𝒩 : Mod)
    (e : (ℒ ⊗ 𝒩) ≅ 𝒪Mod) :
    𝒩 ≅ (ℒ ⟶[Mod] 𝒪Mod) :=
  letI : ExactPairing 𝒩 ℒ :=
    exactPairingOfTensorInverse ℒ 𝒩 e
  letI : IsIso (MonoidalClosed.curry (ε_ 𝒩 ℒ)) :=
    isIso_curry_exactPairingEvaluation ℒ 𝒩
  asIso (MonoidalClosed.curry (ε_ 𝒩 ℒ))

end InternalHom

end SheafOfModules.RingedSite
