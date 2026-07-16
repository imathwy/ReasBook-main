import Mathlib
import StacksProject_2024.stacks_project.Chap13.Lemma_13_25_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

attribute [local instance] HasDerivedCategory.standard

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [EnoughInjectives 𝒜]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

/- Domain-style sampling for Remark 13.25.2:
- primary domain: bounded-below right derived functors computed via injective representatives and
  the induced exact functors on `D^+` and `K^+`;
- sampled owner declarations:
  `Functor.rightDerivedUnique`,
  `Localization.Lifting`,
  `HomotopyResolutionFunctor.lift_unique`,
  `Functor.CommShift.ofComp`,
  `Functor.isTriangulated_iff_comp_right`;
- best owner abstraction: the comparison between the canonical bounded-below right derived functor
  and any functor built from a lift `j'` is owned by `Functor.rightDerivedUnique`, while the
  exactness assertions belong to the owner predicates `Functor.CommShift` and
  `Functor.IsTriangulated`, not to ad hoc existential packages;
- primitive data: the additive functor `F`, the homotopy resolution functor `j`, a lift
  `j' : D^+(\mathcal A) ⥤ K^+(\mathcal I)`, together with the canonical lift datum carried by
  `Localization.Lifting`;
- derived API: the factorization isomorphism for `RF` and the inherited
  `CommShift`/`IsTriangulated` structures on the lifted functors.

Source/core/bridge triage:
- `source-facing`: the factorization of `RF` through `K^+(\mathcal B)` and the exactness of the
  lifted functors in Remark 13.25.2;
- `core/canonical`: `Functor.totalRightDerived`, `Functor.rightDerivedUnique`,
  `Functor.CommShift`, and `Functor.IsTriangulated`;
- `bridge/view`: the composites through `K⁺ᵢ(𝒜)` and `K⁺(ℬ)` built from a chosen lift `j'`.
-/

local notation "DplusA" => boundedBelowDerivedCategory 𝒜
local notation "Q" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ DplusA)
local notation "KinjIncl" => ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)
local notation "KinjToKplusB" =>
  KinjIncl ⋙ mapBoundedBelowHomotopyCategory F
local notation "KinjToDplusB" =>
  KinjIncl ⋙ mapBoundedBelowHomotopyCategoryToDerivedBelow F

attribute [local instance] mapBoundedBelowHomotopyToDerivedBelow_isLocalization

-- Proof sketch: both sides are the same composite through the inclusion
-- `K^+(\mathcal I) ↪ K^+(\mathcal A)` followed by the canonical bounded-below homotopy and
-- derived functors induced by `F`.
/-- Localizing the lifted homotopy-valued functor on the target side recovers the functor
`D^+(\mathcal A) ⥤ D^+(\mathcal B)` obtained by applying `F` to bounded-below injective
complexes and then passing to the derived category. -/
theorem lift_comp_mapBoundedBelowInjectiveHomotopyToHomotopy_toDerived
    (j' : DplusA ⥤ K⁺ᵢ(𝒜)) :
    j' ⋙ KinjToKplusB ⋙
        mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 ℬ) =
      j' ⋙ KinjToDplusB := sorry

/- Canonical owner recall: the factorization isomorphism in Remark `13.25.2` is the chapter
specialization of `Functor.rightDerivedUnique`, followed by transport along the bridge equality
`lift_comp_mapBoundedBelowInjectiveHomotopyToHomotopy_toDerived`. -/
recall Functor.rightDerivedUnique

/- Remark `13.25.2`: for a chosen lift `j'`, the factorization of the bounded-below right derived
functor through `K^+(\mathcal B)` is exactly the canonical uniqueness isomorphism for right
derived functors, composed with the bridge equality above. -/
#check
  fun (j : HomotopyResolutionFunctor 𝒜) (j' : DplusA ⥤ K⁺ᵢ(𝒜))
    (e : Q ⋙ j' ≅ j.toFunctor) ↦
      let hj' : Localization.Lifting Q (Qis⁺(𝒜)) j.toFunctor j' := ⟨e⟩
      letI :
          (j' ⋙ KinjToDplusB).IsRightDerivedFunctor
            (resolutionLiftComparison F j j' hj') (Qis⁺(𝒜)) :=
        resolution_lift_comp_isRightDerivedFunctor F j j' hj'
      ((Functor.totalRightDerived
          (mapBoundedBelowHomotopyCategoryToDerivedBelow F) Q (Qis⁺(𝒜))).rightDerivedUnique
        (j' ⋙ KinjToDplusB)
        (Functor.totalRightDerivedUnit
          (mapBoundedBelowHomotopyCategoryToDerivedBelow F) Q (Qis⁺(𝒜)))
        (resolutionLiftComparison F j j' hj')
        (Qis⁺(𝒜))) ≪≫
        eqToIso (lift_comp_mapBoundedBelowInjectiveHomotopyToHomotopy_toDerived F j').symm

end

section

variable {𝒜 : Type u₁}
  [Category.{v₁} 𝒜]
  [Abelian 𝒜]

local notation "DplusA" => boundedBelowDerivedCategory 𝒜
local notation "Q" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ DplusA)
local notation "KinjIncl" => ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)
local notation "IToD" =>
  KinjIncl ⋙ mapBoundedBelowHomotopyToDerivedBelow

attribute [local instance] mapBoundedBelowHomotopyToDerivedBelow_isLocalization

open HomotopyResolutionFunctor

private noncomputable def resolutionLiftCompIso
    (j : HomotopyResolutionFunctor 𝒜) (j' : DplusA ⥤ K⁺ᵢ(𝒜))
    (e : Q ⋙ j' ≅ j.toFunctor) :
    j' ⋙ IToD ≅ 𝟭 DplusA :=
  Functor.isoWhiskerRight (lift_unique j j' e) IToD ≪≫ (j.lift_unitIso).symm

/- Canonical owner recall: the chosen lift `j'` commutes with shifts via
`Functor.CommShift.ofComp`, applied to its comparison isomorphism with `𝟭 DplusA`. -/
recall Functor.CommShift.ofComp

/- Canonical owner recall: exactness of the chosen lift `j'` is the corresponding owner
consequence of `Functor.isTriangulated_iff_comp_right`. -/
recall Functor.isTriangulated_iff_comp_right

#check
  fun (j : HomotopyResolutionFunctor 𝒜) (j' : DplusA ⥤ K⁺ᵢ(𝒜))
    (e : Q ⋙ j' ≅ j.toFunctor) ↦
      by
        letI : Functor.IsEquivalence IToD := toDerived_isEquivalence j
        letI : Functor.Full IToD := (Functor.asEquivalence IToD).fullyFaithfulFunctor.full
        letI : Functor.Faithful IToD := (Functor.asEquivalence IToD).fullyFaithfulFunctor.faithful
        letI : j'.CommShift ℤ := Functor.CommShift.ofComp (resolutionLiftCompIso j j' e) ℤ
        change j'.CommShift ℤ
        infer_instance

#check
  fun (j : HomotopyResolutionFunctor 𝒜) (j' : DplusA ⥤ K⁺ᵢ(𝒜))
    (e : Q ⋙ j' ≅ j.toFunctor) ↦
      by
        letI : Functor.IsEquivalence IToD := toDerived_isEquivalence j
        letI : Functor.Full IToD := (Functor.asEquivalence IToD).fullyFaithfulFunctor.full
        letI : Functor.Faithful IToD := (Functor.asEquivalence IToD).fullyFaithfulFunctor.faithful
        letI : j'.CommShift ℤ := Functor.CommShift.ofComp (resolutionLiftCompIso j j' e) ℤ
        letI : NatTrans.CommShift (resolutionLiftCompIso j j' e).hom ℤ :=
          Functor.CommShift.ofComp_compatibility (resolutionLiftCompIso j j' e) ℤ
        change j'.IsTriangulated
        exact (Functor.isTriangulated_iff_comp_right (resolutionLiftCompIso j j' e)).2
          inferInstance

end

end CategoryTheory
