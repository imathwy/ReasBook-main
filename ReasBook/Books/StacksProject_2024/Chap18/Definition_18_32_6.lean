import Mathlib
import StacksProject_2024.Chap04.Lemma_4_43_3
import StacksProject_2024.Chap18.Example_18_29_1
import StacksProject_2024.Chap18.Lemma_18_32_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable (𝒪 : Sheaf J CommRingCat.{u})
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Domain-style sampling for Definition 18.32.6:
- primary domain: Picard groups of ringed sites as isomorphism classes of invertible
  `\mathcal O`-modules under tensor product;
- sampled owner declarations:
  `CommRing.Pic`,
  `IsInvertible`,
  `ObjectProperty.FullSubcategory`,
  `Skeleton`;
- best owner abstraction:
  the canonical owner is the units group of the skeleton of the full subcategory of invertible
  `\mathcal O`-modules, exactly mirroring the mathlib `CommRing.Pic` design but at the ambient
  ringed-site module category;
- primitive data:
  the invertible-module object property on `ringedSiteModuleCategory J 𝒪`;
- derived API:
  the Picard-group owner type, its additive-group structure, the canonical class map, scoped
  textbook notation, and the source-facing tensor/unit/dual class formulas.

Source/core/bridge triage:
- `source-facing`: the Picard group `\mathrm{Pic}(\mathcal O)` of a ringed site;
- `core/canonical`: the skeleton of the full subcategory of invertible `\mathcal O`-modules,
  viewed through its units;
- `bridge/view`: the class map sending an invertible module to the corresponding unit in that
  skeleton.
-/

local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

private abbrev InvertibleModuleCat
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)] : Type _ :=
  ObjectProperty.FullSubcategory
    (IsInvertible : ObjectProperty (ringedSiteModuleCategory J 𝒪))

private theorem tensorUnit_isInvertible :
    IsInvertible (𝟙_ (ringedSiteModuleCategory J 𝒪)) := by
  let e :
      tensorRight (𝟙_ (ringedSiteModuleCategory J 𝒪)) ≅
        𝟭 (ringedSiteModuleCategory J 𝒪) :=
    MonoidalCategory.rightUnitorNatIso (ringedSiteModuleCategory J 𝒪)
  exact { toIsEquivalence := (Functor.isEquivalence_iff_of_iso e).2 inferInstance }

private instance isInvertibleIsMonoidal :
    ObjectProperty.IsMonoidal
      (IsInvertible : ObjectProperty (ringedSiteModuleCategory J 𝒪)) where
  prop_unit := tensorUnit_isInvertible (J := J) (𝒪 := 𝒪)
  prop_tensor X Y hX hY := by
    let e :
        tensorRight
            (MonoidalCategoryStruct.tensorObj X Y :
              ringedSiteModuleCategory J 𝒪) ≅
          tensorRight X ⋙ tensorRight Y :=
      tensorRightTensor X Y
    letI : IsInvertible X := hX
    letI : IsInvertible Y := hY
    exact { toIsEquivalence := (Functor.isEquivalence_iff_of_iso e).2 inferInstance }

private theorem exists_chosenTensorInverse
    (ℒ : ringedSiteModuleCategory J 𝒪) [IsInvertible ℒ] :
    ∃ D : ringedSiteModuleCategory J 𝒪,
      Nonempty
        ((MonoidalCategoryStruct.tensorObj ℒ D :
            ringedSiteModuleCategory J 𝒪) ≅
          𝟙_ (ringedSiteModuleCategory J 𝒪)) ∧
      Nonempty
        ((MonoidalCategoryStruct.tensorObj D ℒ :
            ringedSiteModuleCategory J 𝒪) ≅
          𝟙_ (ringedSiteModuleCategory J 𝒪)) :=
  (tensorRight_isEquivalence_iff_exists_tensor_inverse ℒ).1
    (show (tensorRight ℒ).IsEquivalence from inferInstance)

private noncomputable def chosenTensorInverseObj
    (ℒ : ringedSiteModuleCategory J 𝒪) [IsInvertible ℒ] :
    ringedSiteModuleCategory J 𝒪 := by
  classical
  exact Classical.choose (exists_chosenTensorInverse J 𝒪 ℒ)

private theorem chosenTensorInverseObj_leftIso
    (ℒ : ringedSiteModuleCategory J 𝒪) [IsInvertible ℒ] :
    Nonempty
      ((MonoidalCategoryStruct.tensorObj ℒ (chosenTensorInverseObj J 𝒪 ℒ) :
          ringedSiteModuleCategory J 𝒪) ≅
        𝟙_ (ringedSiteModuleCategory J 𝒪)) := by
  classical
  exact (Classical.choose_spec (exists_chosenTensorInverse J 𝒪 ℒ)).1

private theorem chosenTensorInverseObj_rightIso
    (ℒ : ringedSiteModuleCategory J 𝒪) [IsInvertible ℒ] :
    Nonempty
      ((MonoidalCategoryStruct.tensorObj (chosenTensorInverseObj J 𝒪 ℒ) ℒ :
          ringedSiteModuleCategory J 𝒪) ≅
        𝟙_ (ringedSiteModuleCategory J 𝒪)) := by
  classical
  exact (Classical.choose_spec (exists_chosenTensorInverse J 𝒪 ℒ)).2

private noncomputable def chosenTensorInverse
    (ℒ : ringedSiteModuleCategory J 𝒪) [IsInvertible ℒ] :
    InvertibleModuleCat J 𝒪 := by
  classical
  let D := chosenTensorInverseObj J 𝒪 ℒ
  have hLD := chosenTensorInverseObj_leftIso J 𝒪 ℒ
  have hDL := chosenTensorInverseObj_rightIso J 𝒪 ℒ
  have hD : IsInvertible D := by
    refine { toIsEquivalence := ?_ }
    exact (tensorRight_isEquivalence_iff_exists_tensor_inverse D).2 ⟨ℒ, hDL, hLD⟩
  exact ⟨D, hD⟩

private theorem chosenTensorInverse_tensorIso
    (ℒ : ringedSiteModuleCategory J 𝒪) [IsInvertible ℒ] :
    Nonempty
      ((⟨ℒ, inferInstance⟩ : InvertibleModuleCat J 𝒪) ⊗
          chosenTensorInverse J 𝒪 ℒ ≅
        𝟙_ (InvertibleModuleCat J 𝒪)) := by
  classical
  let P : ObjectProperty (ringedSiteModuleCategory J 𝒪) := IsInvertible
  let D := chosenTensorInverseObj J 𝒪 ℒ
  have hLD := chosenTensorInverseObj_leftIso J 𝒪 ℒ
  have hDL := chosenTensorInverseObj_rightIso J 𝒪 ℒ
  have hD : IsInvertible D := by
    refine { toIsEquivalence := ?_ }
    exact (tensorRight_isEquivalence_iff_exists_tensor_inverse D).2 ⟨ℒ, hDL, hLD⟩
  change
    Nonempty
      ((⟨ℒ, inferInstance⟩ : InvertibleModuleCat J 𝒪) ⊗ ⟨D, hD⟩ ≅
        𝟙_ (InvertibleModuleCat J 𝒪))
  rcases hLD with ⟨e⟩
  exact ⟨P.isoMk e⟩

private theorem chosenTensorInverse_tensorIso_symm
    (ℒ : ringedSiteModuleCategory J 𝒪) [IsInvertible ℒ] :
    Nonempty
      (chosenTensorInverse J 𝒪 ℒ ⊗
          (⟨ℒ, inferInstance⟩ : InvertibleModuleCat J 𝒪) ≅
        𝟙_ (InvertibleModuleCat J 𝒪)) := by
  classical
  let P : ObjectProperty (ringedSiteModuleCategory J 𝒪) := IsInvertible
  let D := chosenTensorInverseObj J 𝒪 ℒ
  have hLD := chosenTensorInverseObj_leftIso J 𝒪 ℒ
  have hDL := chosenTensorInverseObj_rightIso J 𝒪 ℒ
  have hD : IsInvertible D := by
    refine { toIsEquivalence := ?_ }
    exact (tensorRight_isEquivalence_iff_exists_tensor_inverse D).2 ⟨ℒ, hDL, hLD⟩
  change
    Nonempty
      (⟨D, hD⟩ ⊗ (⟨ℒ, inferInstance⟩ : InvertibleModuleCat J 𝒪) ≅
        𝟙_ (InvertibleModuleCat J 𝒪))
  rcases hDL with ⟨e⟩
  exact ⟨P.isoMk e⟩

private abbrev PicardMultiplicative
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)] : Type _ :=
  (Skeleton (InvertibleModuleCat J 𝒪))ˣ

/-- Definition 18.32.6: the Picard group `\mathrm{Pic}(\mathcal O)` of a ringed site is the
abelian group of isomorphism classes of invertible `\mathcal O`-modules, with addition induced by
tensor product. -/
def ringedSitePicardGroup : Type _ :=
  Additive (PicardMultiplicative J 𝒪)

/- Textbook notation for the Picard group `\mathrm{Pic}(\mathcal O)` of a ringed site. -/
scoped[RingedSitePicard] notation:max "Pic(" 𝒪 ")" => _root_.ringedSitePicardGroup _ 𝒪

open scoped RingedSitePicard

namespace ringedSitePicardGroup

local notation "Picard" => _root_.ringedSitePicardGroup J 𝒪

instance : AddGroup Picard :=
  Additive.addGroup

section Tensor

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]

private instance instIsInvertibleTensor
    (ℒ 𝒩 : Mod)
    [IsInvertible ℒ]
    [IsInvertible 𝒩] :
    IsInvertible (MonoidalCategoryStruct.tensorObj ℒ 𝒩 : Mod) := by
  let e :
      tensorRight (MonoidalCategoryStruct.tensorObj ℒ 𝒩 : Mod) ≅
        tensorRight ℒ ⋙ tensorRight 𝒩 :=
    tensorRightTensor ℒ 𝒩
  exact { toIsEquivalence := (Functor.isEquivalence_iff_of_iso e).2 inferInstance }

private noncomputable def mkMul
    (ℒ : Mod) [IsInvertible ℒ] :
    PicardMultiplicative J 𝒪 :=
  let L : InvertibleModuleCat J 𝒪 := ⟨ℒ, inferInstance⟩
  let D := chosenTensorInverse J 𝒪 ℒ
  have hLD : toSkeleton L * toSkeleton D = 1 := by
    rw [Skeleton.mul_eq, Skeleton.one_eq]
    rcases chosenTensorInverse_tensorIso J 𝒪 ℒ with ⟨e⟩
    exact (toSkeleton_eq_toSkeleton_iff).2
      ⟨(fromSkeletonToSkeletonIso L ⊗ᵢ fromSkeletonToSkeletonIso D) ≪≫ e⟩
  have hDL : toSkeleton D * toSkeleton L = 1 := by
    rw [Skeleton.mul_eq, Skeleton.one_eq]
    rcases chosenTensorInverse_tensorIso_symm J 𝒪 ℒ with ⟨e⟩
    exact (toSkeleton_eq_toSkeleton_iff).2
      ⟨(fromSkeletonToSkeletonIso D ⊗ᵢ fromSkeletonToSkeletonIso L) ≪≫ e⟩
  Units.mk (toSkeleton L) (toSkeleton D) hLD hDL

/-- The Picard class of an invertible `\mathcal O`-module. -/
protected noncomputable def mk
    (ℒ : Mod) [IsInvertible ℒ] :
    Picard :=
  Additive.ofMul (mkMul J 𝒪 ℒ)

-- Proof sketch: equality in the quotient of invertible modules is exactly isomorphism of the
-- underlying modules.
/-- Two invertible `\mathcal O`-modules define the same Picard class exactly when they are
isomorphic. -/
theorem mk_eq_mk_iff
    (ℒ 𝒩 : Mod)
    [IsInvertible ℒ]
    [IsInvertible 𝒩] :
    _root_.ringedSitePicardGroup.mk J 𝒪 ℒ = _root_.ringedSitePicardGroup.mk J 𝒪 𝒩 ↔
      Nonempty (ℒ ≅ 𝒩) := by
  let P : ObjectProperty Mod := IsInvertible
  let L : InvertibleModuleCat J 𝒪 := ⟨ℒ, inferInstance⟩
  let N : InvertibleModuleCat J 𝒪 := ⟨𝒩, inferInstance⟩
  change mkMul J 𝒪 ℒ = mkMul J 𝒪 𝒩 ↔ Nonempty (ℒ ≅ 𝒩)
  constructor
  · intro h
    have hs : toSkeleton L = toSkeleton N := by
      simpa [mkMul, L, N] using congrArg Units.val h
    rcases (toSkeleton_eq_toSkeleton_iff).1 hs with ⟨e⟩
    exact ⟨P.ι.mapIso e⟩
  · intro h
    rcases h with ⟨e⟩
    apply Units.ext
    have hs : toSkeleton L = toSkeleton N := by
      exact (toSkeleton_eq_toSkeleton_iff).2 ⟨P.isoMk e⟩
    simpa [mkMul, L, N] using hs

/-- The Picard group of a ringed site carries its canonical abelian-group structure. -/
instance : AddCommGroup Picard :=
  Additive.addCommGroup

-- Proof sketch: the neutral class is the quotient class of the structure module itself.
/-- The neutral class in `\mathrm{Pic}(\mathcal O)` is represented by the structure module
`\mathcal O`. -/
theorem mk_unit :
    _root_.ringedSitePicardGroup.mk J 𝒪 (SheafOfModules.unit (ringSheaf J 𝒪) : Mod) =
      (0 : Pic(𝒪)) := by
  sorry

-- Proof sketch: combine `mk_eq_mk_iff` with the fact that `0` is the class of the structure
-- module.
/-- An invertible `\mathcal O`-module is trivial in the Picard group exactly when it is
isomorphic to the structure module. -/
theorem mk_eq_zero_iff
    (ℒ : Mod)
    [IsInvertible ℒ] :
    _root_.ringedSitePicardGroup.mk J 𝒪 ℒ = (0 : Pic(𝒪)) ↔
      Nonempty (ℒ ≅ SheafOfModules.unit (ringSheaf J 𝒪)) := by
  sorry

-- Proof sketch: addition on the quotient is induced by tensor product on representatives.
/-- Addition in `\mathrm{Pic}(\mathcal O)` is induced by tensor product of invertible
`\mathcal O`-modules. -/
theorem mk_tensor
    (ℒ 𝒩 : Mod)
    [IsInvertible ℒ]
    [IsInvertible 𝒩] :
    (_root_.ringedSitePicardGroup.mk J 𝒪
      (MonoidalCategoryStruct.tensorObj ℒ 𝒩 : Mod) : Pic(𝒪)) =
      _root_.ringedSitePicardGroup.mk J 𝒪 ℒ + _root_.ringedSitePicardGroup.mk J 𝒪 𝒩 := by
  sorry

-- Proof sketch: inversion in the quotient is induced by the internal-Hom dual on
-- representatives.
/-- Negation in `\mathrm{Pic}(\mathcal O)` is represented by the internal-Hom dual
`\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L, \mathcal O)`. -/
theorem mk_internalHom_unit
    (ℒ : Mod)
    [IsInvertible ℒ] :
    (_root_.ringedSitePicardGroup.mk J 𝒪 (ringedSiteModuleDual ℒ) : Pic(𝒪)) =
      -_root_.ringedSitePicardGroup.mk J 𝒪 ℒ := by
  sorry

end Tensor

end ringedSitePicardGroup

end
