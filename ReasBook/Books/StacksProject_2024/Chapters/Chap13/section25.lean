import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_13_25_1 (from Chap13) -/
noncomputable section

open CategoryTheory
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

/-
Domain-style sampling:
- primary domain: bounded-below right derived functors computed via injective complexes and a lift
  of the homotopy resolution functor;
- sampled owner declarations:
  `HomotopyResolutionFunctor`,
  `Localization.Lifting`,
  `ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)`,
  `mapBoundedBelowHomotopyToDerivedBelow`,
  `Functor.IsRightDerivedFunctor`;
- best owner abstraction: the canonical localization owner is
  `mapBoundedBelowHomotopyToDerivedBelow`, and the injective-complex inclusion is owned by
  `ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)`; the localization lift itself is
  owned canonically by `Localization.Lifting`, and the passage through `K^+(\mathcal I)` is a
  bridge/view built from those owners rather than a separate root functor declaration;
- primitive data: the additive functor `F`, the homotopy resolution functor `j`, the lifted
  functor `j' : D^+(\mathcal A) ⥤ K^+(\mathcal I)`, and the explicit lift datum
  `hj' : Localization.Lifting Q (Qis⁺(𝒜)) j.toFunctor j'`;
- existence data such as `[EnoughInjectives 𝒜]` belongs upstream, where one proves that
  a `HomotopyResolutionFunctor 𝒜` exists, not in this bridge lemma about a fixed choice;
- derived API: the comparison 2-cell and the induced `IsRightDerivedFunctor` structure on the
  composite through bounded-below injectives.

Source/core/bridge triage:
- `source-facing`: Lemma 13.25.1 itself;
- `core/canonical`: `mapBoundedBelowHomotopyToDerivedBelow`,
  `Localization.Lifting`,
  `ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)`, and
  `Functor.IsRightDerivedFunctor`;
- `bridge/view`: the composite `j' ⋙
  ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) ⋙
  mapBoundedBelowHomotopyCategoryToDerivedBelow F`.
-/
local notation "DplusA" => boundedBelowDerivedCategory 𝒜
local notation "Q" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ DplusA)
local notation "KinjIncl" => ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)
local notation "KinjToDplusB" =>
  KinjIncl ⋙ mapBoundedBelowHomotopyCategoryToDerivedBelow F

attribute [local instance] mapBoundedBelowHomotopyToDerivedBelow_isLocalization

/-- The comparison 2-cell from the cochain-level functor `K^+(\mathcal A) ⥤ D^+(\mathcal B)` to
the composite through a lifted injective-resolution functor `j'`, packaged by the canonical
localization-lift datum `hj'`. -/
noncomputable def resolutionLiftComparison
    (j : HomotopyResolutionFunctor 𝒜) (j' : DplusA ⥤ K⁺ᵢ(𝒜))
    (hj' : Localization.Lifting Q (Qis⁺(𝒜)) j.toFunctor j') :
    mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶
      Q ⋙ (j' ⋙ KinjToDplusB) :=
  Functor.whiskerRight j.ι (mapBoundedBelowHomotopyCategoryToDerivedBelow F) ≫
    (Functor.associator j.toFunctor KinjIncl
      (mapBoundedBelowHomotopyCategoryToDerivedBelow F)).hom ≫
    (Functor.isoWhiskerRight hj'.iso.symm KinjToDplusB).hom ≫
    (Functor.associator Q j' KinjToDplusB).hom

-- Proof sketch: by Lemma 13.20.1, every bounded-below complex of injective objects computes the
-- right derived functor of `K^+(\mathcal A) ⟶ D^+(\mathcal B)`. The functor `j'` sends a derived
-- object to such an injective representative, and the comparison 2-cell is induced from the
-- resolution quasi-isomorphism `ι`; hence the composite through `K^+(\mathcal I)` is itself a
-- right derived functor, and therefore is naturally isomorphic to `RF` by uniqueness.
/-- Lemma 13.25.1: if `j' : D^+(\mathcal A) ⥤ K^+(\mathcal I)` is the lift of a homotopy
resolution functor `j` through the localization functor `K^+(\mathcal A) ⥤ D^+(\mathcal A)`,
encoded by `hj' : Localization.Lifting Q (Qis⁺(𝒜)) j.toFunctor j'`, then the composite
`j' ⋙ F` with the induced functor
`F : K^+(\mathcal I) ⥤ D^+(\mathcal B)` is a right derived functor of
`K^+(\mathcal A) ⥤ D^+(\mathcal B)`; equivalently, it is naturally isomorphic to the bounded-
below right derived functor `RF`. -/
theorem resolution_lift_comp_isRightDerivedFunctor
    (j : HomotopyResolutionFunctor 𝒜) (j' : DplusA ⥤ K⁺ᵢ(𝒜))
    (hj' : Localization.Lifting Q (Qis⁺(𝒜)) j.toFunctor j') :
    (j' ⋙ KinjToDplusB).IsRightDerivedFunctor
      (resolutionLiftComparison F j j' hj')
      (Qis⁺(𝒜)) := sorry

end

end CategoryTheory

/-! ### Remark_13_25_2 (from Chap13) -/
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
