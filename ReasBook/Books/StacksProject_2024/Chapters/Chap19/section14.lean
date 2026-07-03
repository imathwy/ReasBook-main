import Mathlib
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_19_14_1 (from Chap19) -/
universe v u

namespace CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
variable (U : C)

/- Lemma 19.14.1: in the Gabriel-Popescu setup, the functor
`preadditiveCoyonedaObj U : C ⥤ ModuleCat (End U)ᵐᵒᵖ` has a left adjoint
`tensorObj U : ModuleCat (End U)ᵐᵒᵖ ⥤ C`. This is exactly the canonical adjunction
`tensorObjPreadditiveCoyonedaObjAdjunction`. -/
recall tensorObjPreadditiveCoyonedaObjAdjunction

end CategoryTheory.IsGrothendieckAbelian

/-! ### Lemma_19_14_2 (from Chap19) -/
open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
variable {U A : C} {M : ModuleCat (End U)ᵐᵒᵖ}

/-- Lemma 19.14.2: in the Gabriel-Popescu setup for a separator `U`, if
`f : M ⟶ (preadditiveCoyonedaObj U).obj A` is injective, i.e. a monomorphism in the module
category, then its adjoint transpose `tensorObj U ⟶ A` is also a monomorphism. -/
-- Proof sketch: the Gabriel-Popescu theorem makes `preadditiveCoyonedaObj U` fully faithful when
-- `U` is a separator, so the counit of `tensorObjPreadditiveCoyonedaObjAdjunction U` is an
-- isomorphism. The transpose of `f` is `tensorObj U` applied to `f`, followed by this counit; the
-- first map is mono because `tensorObj U` preserves monomorphisms, and composing with an
-- isomorphism preserves monomorphisms.
theorem adjoint_map_mono_of_mono (hU : IsSeparator U)
    {f : M ⟶ (preadditiveCoyonedaObj U).obj A} (hf : Mono f) :
    Mono (((tensorObjPreadditiveCoyonedaObjAdjunction U).homEquiv M A).symm f) := by
  let adj := tensorObjPreadditiveCoyonedaObjAdjunction U
  letI : Mono f := hf
  letI : PreservesFiniteLimits (tensorObj U) := GabrielPopescu.preservesFiniteLimits U hU
  letI : (preadditiveCoyonedaObj U).Full := GabrielPopescu.full U hU
  letI : (preadditiveCoyonedaObj U).Faithful :=
    (isSeparator_iff_faithful_preadditiveCoyonedaObj U).1 hU
  rw [adj.homEquiv_counit]
  have hmap : Mono ((tensorObj U).map f) := Functor.map_mono (tensorObj U) f
  have hsplit : IsSplitMono (adj.counit.app A) := by infer_instance
  have hCounit : Mono (adj.counit.app A) := by
    letI : IsSplitMono (adj.counit.app A) := hsplit
    infer_instance
  exact mono_comp' hmap hCounit

end CategoryTheory.IsGrothendieckAbelian

/-! ### Theorem_19_14_3 (from Chap19) -/
open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.IsGrothendieckAbelian

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]

/-
Domain-style sampling:
* primary domain: the Gabriel-Popescu module embedding for Grothendieck abelian categories.
* inspected owner declarations: `tensorObj`, `tensorObjPreadditiveCoyonedaObjAdjunction`,
  `GabrielPopescu.full`, and `GabrielPopescu.preservesFiniteLimits`.
* best owner abstraction: the canonical functor pair
  `tensorObj U ⊣ preadditiveCoyonedaObj U` attached to a separator `U`.
* layer: `bridge/view`; the source theorem is an existence statement, while the canonical owner API
  already lives on `tensorObj U` and `preadditiveCoyonedaObj U`.
* primitive data: the separator object `separator A`.
* derived API: exactness of `tensorObj (separator A)`, the adjunction, and the full/faithful
  properties of `preadditiveCoyonedaObj (separator A)`.
-/

/-- Theorem 19.14.3 for the canonical separator: the functor
`preadditiveCoyonedaObj (separator A)` is fully faithful, and its left adjoint
`tensorObj (separator A)` is exact. -/
theorem separator_gabriel_popescu :
    exactFunctor _ _ (tensorObj (separator A)) ∧
      (preadditiveCoyonedaObj (separator A)).Full ∧
      (preadditiveCoyonedaObj (separator A)).Faithful := by
  let U := separator A
  have hU : IsSeparator U := isSeparator_separator A
  letI : PreservesFiniteLimits (tensorObj U) := GabrielPopescu.preservesFiniteLimits U hU
  letI : (preadditiveCoyonedaObj U).Full := GabrielPopescu.full U hU
  letI : (preadditiveCoyonedaObj U).Faithful :=
    (isSeparator_iff_faithful_preadditiveCoyonedaObj U).1 hU
  refine ⟨?_, inferInstance, inferInstance⟩
  exact (exactFunctor_iff (tensorObj U)).2 ⟨inferInstance, inferInstance⟩

/-- The existence form of the Gabriel-Popescu theorem for a Grothendieck abelian category. -/
-- Proof sketch: take `R := (End (separator A))ᵐᵒᵖ`, `G := preadditiveCoyonedaObj (separator A)`,
-- and `F := ExactFunctor.of (tensorObj (separator A))`. The adjunction is the canonical
-- `tensorObjPreadditiveCoyonedaObjAdjunction`, fullness comes from `GabrielPopescu.full`,
-- faithfulness from `isSeparator_iff_faithful_preadditiveCoyonedaObj`, and exactness of `F`
-- combines `GabrielPopescu.preservesFiniteLimits` with the fact that a left adjoint preserves
-- finite colimits.
theorem exists_gabriel_popescu_functors :
    ∃ (R : Type v) (_ : Ring R) (G : A ⥤ ModuleCat.{v} R) (F : ModuleCat.{v} R ⥤ₑ A),
      ∃ _ : F.1 ⊣ G, G.Full ∧ G.Faithful := by
  have h :
      exactFunctor _ _ (tensorObj (separator A)) ∧
        (preadditiveCoyonedaObj (separator A)).Full ∧
        (preadditiveCoyonedaObj (separator A)).Faithful :=
    separator_gabriel_popescu
  rcases h with ⟨hExact, hFull, hFaithful⟩
  letI : PreservesFiniteLimits (tensorObj (separator A)) := (exactFunctor_iff _).1 hExact |>.1
  letI : PreservesFiniteColimits (tensorObj (separator A)) := (exactFunctor_iff _).1 hExact |>.2
  refine ⟨(End (separator A))ᵐᵒᵖ, inferInstance, preadditiveCoyonedaObj (separator A),
    ExactFunctor.of (tensorObj (separator A)), ?_⟩
  refine ⟨?_, hFull, hFaithful⟩
  simpa using tensorObjPreadditiveCoyonedaObjAdjunction (separator A)

end CategoryTheory.IsGrothendieckAbelian

/-! ### Lemma_19_14_4 (from Chap19) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]

/-
Domain-style sampling:
* primary domain: derived Gabriel-Popescu theory for Grothendieck abelian categories.
* sampled owner declarations:
  `separator_gabriel_popescu`,
  `mapHomologicalComplexQ_hasRightDerivedFunctor`,
  `Functor.mapDerivedCategory`,
  `additiveFunctorTotalRightDerived`,
  `Adjunction.fullyFaithfulROfIsIsoCounit`.
* best owner abstraction: the canonical functor pair on derived categories built from
  `tensorObj (separator C)` and the chapter-level owner
  `additiveFunctorTotalRightDerived (preadditiveCoyonedaObj (separator C))`.
* source/core/bridge triage:
  - `source-facing`: the existence of the derived Gabriel-Popescu adjunction and the identity
    comparison `RG ⋙ F ≅ 𝟭`;
  - `core/canonical`: `Adjunction`, `Functor.mapDerivedCategory`, and
    `additiveFunctorTotalRightDerived`;
  - `bridge/view`: the fully faithful consequence obtained from
    `Adjunction.fullyFaithfulROfIsIsoCounit`.
* primitive data: the separator `separator C` and the underived Gabriel-Popescu functors.
* derived API: exactness of `tensorObj (separator C)`, the induced derived functor
  `Functor.mapDerivedCategory`, the canonical right derived functor
  `additiveFunctorTotalRightDerived`, and the adjunction consequences.
-/

local notation "RMod" => ModuleCat ((End (separator C))ᵐᵒᵖ)

/-- The standard derived-category model used for `C` in this item file. -/
local instance : HasDerivedCategory C :=
  HasDerivedCategory.standard C

/-- The standard derived-category model used for the Gabriel-Popescu module category. -/
local instance : HasDerivedCategory RMod :=
  HasDerivedCategory.standard RMod

-- The canonical Gabriel-Popescu left adjoint `tensorObj (separator C)` is exact.
private theorem tensorObj_separator_exact :
    exactFunctor _ _ (tensorObj (separator C)) :=
  separator_gabriel_popescu.1

/-- The Gabriel-Popescu left adjoint `tensorObj (separator C)` preserves finite limits. -/
local instance tensorObj_separator_preservesFiniteLimits :
    PreservesFiniteLimits (tensorObj (separator C)) :=
  (exactFunctor_iff _).1 tensorObj_separator_exact |>.1

/-- The Gabriel-Popescu left adjoint `tensorObj (separator C)` preserves finite colimits. -/
local instance tensorObj_separator_preservesFiniteColimits :
    PreservesFiniteColimits (tensorObj (separator C)) :=
  (exactFunctor_iff _).1 tensorObj_separator_exact |>.2

/-- The Gabriel-Popescu left adjoint `tensorObj (separator C)` is additive. -/
local instance tensorObj_separator_additive :
    (tensorObj (separator C)).Additive := by
  have : PreservesBinaryBiproducts (tensorObj (separator C)) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

private noncomputable abbrev gabrielPopescuLeftDerived :
    DerivedCategory RMod ⥤ DerivedCategory C :=
  (tensorObj (separator C)).mapDerivedCategory

private noncomputable abbrev gabrielPopescuRightDerived :
    DerivedCategory C ⥤ DerivedCategory RMod :=
  additiveFunctorTotalRightDerived (preadditiveCoyonedaObj (separator C))

private abbrev tensorObjComplex :
    CochainComplex RMod ℤ ⥤ CochainComplex C ℤ :=
  (tensorObj (separator C)).mapHomologicalComplex (up ℤ)

private abbrev preadditiveCoyonedaComplex :
    CochainComplex C ℤ ⥤ CochainComplex RMod ℤ :=
  (preadditiveCoyonedaObj (separator C)).mapHomologicalComplex (up ℤ)

local instance :
    (preadditiveCoyonedaComplex ⋙ DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso C (up ℤ)) :=
  _root_.CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor
    (preadditiveCoyonedaObj (separator C))

local notation "QMod" => (DerivedCategory.Q : CochainComplex RMod ℤ ⥤ DerivedCategory RMod)
local notation "QC" => (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C)
local notation "QisMod" => HomologicalComplex.quasiIso RMod (up ℤ)
local notation "QisC" => HomologicalComplex.quasiIso C (up ℤ)

/-- The unit of the Gabriel-Popescu adjunction on cochain complexes. -/
private abbrev gabrielPopescuComplexUnit :
    𝟭 (CochainComplex RMod ℤ) ⟶ tensorObjComplex ⋙ preadditiveCoyonedaComplex :=
  (Functor.mapHomologicalComplexIdIso RMod (up ℤ)).hom ≫
    NatTrans.mapHomologicalComplex
      (tensorObjPreadditiveCoyonedaObjAdjunction (separator C)).unit
      (up ℤ)

/-- The counit of the Gabriel-Popescu adjunction on cochain complexes. -/
private abbrev gabrielPopescuComplexCounit :
    preadditiveCoyonedaComplex ⋙ tensorObjComplex ⟶ 𝟭 (CochainComplex C ℤ) :=
  NatTrans.mapHomologicalComplex
      (tensorObjPreadditiveCoyonedaObjAdjunction (separator C)).counit
      (up ℤ) ≫
    (Functor.mapHomologicalComplexIdIso C (up ℤ)).hom

/-- The left triangle identity for the Gabriel-Popescu adjunction on cochain complexes. -/
private theorem gabrielPopescuComplex_leftTriangle :
    Functor.whiskerRight gabrielPopescuComplexUnit tensorObjComplex ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft tensorObjComplex gabrielPopescuComplexCounit =
      NatTrans.id (𝟭 (CochainComplex RMod ℤ) ⋙ tensorObjComplex) := sorry

/-- The right triangle identity for the Gabriel-Popescu adjunction on cochain complexes. -/
private theorem gabrielPopescuComplex_rightTriangle :
    Functor.whiskerLeft preadditiveCoyonedaComplex gabrielPopescuComplexUnit ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight gabrielPopescuComplexCounit preadditiveCoyonedaComplex =
      NatTrans.id (preadditiveCoyonedaComplex ⋙ 𝟭 (CochainComplex RMod ℤ)) := sorry

/-- The Gabriel-Popescu adjunction lifted to cochain complexes. -/
private noncomputable def gabrielPopescuComplexAdjunction :
    ((tensorObj (separator C)).mapHomologicalComplex (up ℤ)) ⊣
      ((preadditiveCoyonedaObj (separator C)).mapHomologicalComplex (up ℤ)) :=
  Adjunction.mkOfUnitCounit <|
    Adjunction.CoreUnitCounit.mk
      gabrielPopescuComplexUnit
      gabrielPopescuComplexCounit
      gabrielPopescuComplex_leftTriangle
      gabrielPopescuComplex_rightTriangle

/-- The comparison morphism exhibiting the right derived Gabriel-Popescu functor. -/
private abbrev gabrielPopescuRightDerivedUnit :
    preadditiveCoyonedaComplex ⋙ QMod ⟶ QC ⋙ gabrielPopescuRightDerived :=
  (preadditiveCoyonedaComplex ⋙ QMod).totalRightDerivedUnit QC QisC

/-- The exact-functor lift on derived categories is the left derived Gabriel-Popescu functor. -/
private theorem gabrielPopescuLeftDerived_isLeftDerivedFunctor :
    gabrielPopescuLeftDerived.IsLeftDerivedFunctor
      ((tensorObj (separator C)).mapDerivedCategoryFactors.hom)
      QisMod := sorry

attribute [local instance] gabrielPopescuLeftDerived_isLeftDerivedFunctor

/-- The chapter-level right derived Gabriel-Popescu functor is the right derived functor of the
cochain-level embedding. -/
private theorem gabrielPopescuRightDerived_isRightDerivedFunctor :
    gabrielPopescuRightDerived.IsRightDerivedFunctor
      gabrielPopescuRightDerivedUnit
      QisC := by
  dsimp [gabrielPopescuRightDerived, gabrielPopescuRightDerivedUnit,
    additiveFunctorTotalRightDerived]
  infer_instance

attribute [local instance] gabrielPopescuRightDerived_isRightDerivedFunctor

/-- The composite `F ⋙ RG` carries the left-derived structure required by `Adjunction.derived`. -/
private theorem gabrielPopescu_leftDerived_rightDerived_comp_isLeftDerivedFunctor :
    (gabrielPopescuLeftDerived ⋙ gabrielPopescuRightDerived).IsLeftDerivedFunctor
      ((Functor.associator QMod gabrielPopescuLeftDerived gabrielPopescuRightDerived).inv ≫
        Functor.whiskerRight
          ((tensorObj (separator C)).mapDerivedCategoryFactors.hom)
          gabrielPopescuRightDerived)
      QisMod := sorry

attribute [local instance] gabrielPopescu_leftDerived_rightDerived_comp_isLeftDerivedFunctor

/-- The composite `RG ⋙ F` carries the right-derived structure required by `Adjunction.derived`. -/
private theorem gabrielPopescu_rightDerived_leftDerived_comp_isRightDerivedFunctor :
    (gabrielPopescuRightDerived ⋙ gabrielPopescuLeftDerived).IsRightDerivedFunctor
      (Functor.whiskerRight gabrielPopescuRightDerivedUnit gabrielPopescuLeftDerived ≫
        (Functor.associator QC gabrielPopescuRightDerived gabrielPopescuLeftDerived).hom)
      QisC := sorry

attribute [local instance] gabrielPopescu_rightDerived_leftDerived_comp_isRightDerivedFunctor

-- Proof sketch: apply `Adjunction.derived` to the cochain-level Gabriel-Popescu adjunction
-- induced by `tensorObjPreadditiveCoyonedaObjAdjunction (separator C)`. The left derived functor
-- is the exact-functor owner `gabrielPopescuLeftDerived`, and the right derived functor is the
-- chapter-level owner `gabrielPopescuRightDerived`.
/-- Lemma 19.14.4: for the canonical Gabriel-Popescu functors attached to the separator of a
Grothendieck abelian category, the induced functor
`F : D(\operatorname{Mod}_{(End(\mathrm{separator}\, C))^{op}}) ⥤ D(C)` is left adjoint to the
right derived Gabriel-Popescu embedding `RG`. This is the owner-level derived adjunction attached
to the fixed Gabriel-Popescu functor pair. -/
noncomputable def gabriel_popescu_derived_adjunction :
    ((tensorObj (separator C)).mapDerivedCategory) ⊣
      (additiveFunctorTotalRightDerived (preadditiveCoyonedaObj (separator C))) :=
  Adjunction.derived
    gabrielPopescuComplexAdjunction
    QisMod
    QisC
    ((tensorObj (separator C)).mapDerivedCategoryFactors.hom)
    gabrielPopescuRightDerivedUnit

-- Proof sketch: compute the derived counit on K-injective representatives and compare it with the
-- underived Gabriel-Popescu counit `preadditiveCoyonedaObj (separator C) ⋙ tensorObj
-- (separator C) ⟶ 𝟭 C`, which is an isomorphism because `preadditiveCoyonedaObj (separator C)` is
-- fully faithful by Theorem `19.14.3`.
/-- The counit `RG ⋙ F ⟶ 𝟭_{D(C)}` of the derived Gabriel-Popescu adjunction is an isomorphism. -/
theorem gabriel_popescu_derived_counit_isIso :
    IsIso
      (gabriel_popescu_derived_adjunction.counit :
        (additiveFunctorTotalRightDerived (preadditiveCoyonedaObj (separator C))) ⋙
            ((tensorObj (separator C)).mapDerivedCategory) ⟶
          𝟭 (DerivedCategory C)) := sorry

-- Proof sketch: by the previous theorem, `F` is left adjoint to `RG` and the counit
-- `RG ⋙ F ⟶ 𝟭` is an isomorphism. The standard adjunction criterion then yields the `Full` and
-- `Faithful` properties of `RG` from the canonical owner construction
-- `Adjunction.fullyFaithfulROfIsIsoCounit`.
/-- The derived Gabriel-Popescu embedding `RG : D(C) ⥤ D(\operatorname{Mod}_R)` is full and
faithful. -/
noncomputable def gabriel_popescu_rightDerived_fullyFaithful :
    (additiveFunctorTotalRightDerived
      (preadditiveCoyonedaObj (separator C))).FullyFaithful := by
  letI :
      IsIso
        (gabriel_popescu_derived_adjunction.counit :
          (additiveFunctorTotalRightDerived (preadditiveCoyonedaObj (separator C))) ⋙
              ((tensorObj (separator C)).mapDerivedCategory) ⟶
            𝟭 (DerivedCategory C)) :=
    gabriel_popescu_derived_counit_isIso
  exact gabriel_popescu_derived_adjunction.fullyFaithfulROfIsIsoCounit

end CategoryTheory.IsGrothendieckAbelian
