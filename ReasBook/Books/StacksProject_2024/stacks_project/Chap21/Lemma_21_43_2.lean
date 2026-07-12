import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.Triangulated.Subcategory
import StacksProject_2024.Chap21.Definition_21_43_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open Opposite
open scoped ZeroObject

noncomputable section

universe w uC vC uD vD

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ModulesOnCategory

section

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{uC})
variable
  (RGamma : ∀ U : C, D ⥤ DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (derivedRestrict :
    ∀ {U V : C}, (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)

local notation "QCP" => isQuasiCoherent 𝒪 RGamma derivedRestrict comparison

/- Domain-style sampling for Lemma 21.43.2:
- primary domain: source-facing full subcategories of triangulated categories cut out by
  comparison-isomorphism object properties;
- sampled owner declarations:
  `CategoryTheory.ModulesOnCategory.isQuasiCoherent`,
  `CategoryTheory.ModulesOnCategory.QC`,
  `CategoryTheory.ObjectProperty.IsTriangulated`,
  `CategoryTheory.NatTrans.CommShift`,
  `CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape`;
- best owner abstraction:
  `source-facing`: the Section `21.43` object property `QCP` and its full subcategory `QC`;
  `core/canonical`: `ObjectProperty` closure predicates and the induced structure on
    `QCP.FullSubcategory`;
  `bridge/view`: the later identification of this owner with the Chapter 13 cohomologywise owner
    `derivedCategoryCohomologyInProperty`, which is support for proofs but not the main statement
    layer here.
- primitive-vs-derived split:
  primitive data: `𝒪`, `RGamma`, `derivedRestrict`, and `comparison`;
  derived API: strict fullness and saturation for arbitrary comparison data, plus triangulatedity
    only after the comparison functors are assumed exact together with
    `NatTrans.CommShift` compatibility of the comparison maps, and direct-sum closure after the
    comparison functors are assumed coproduct-preserving.

This file therefore keeps the source-facing `QC` owner central and records the structural closure
facts directly on that owner, rather than replacing them by a recall of the later Chapter 13
bridge. -/

/-- Helper for Lemma 21.43.2: a component of a natural transformation is an isomorphism at any
object isomorphic to one where it is already an isomorphism. -/
lemma natTrans_app_isIso_of_iso {E : Type*} [Category E] {F G : D ⥤ E} (τ : F ⟶ G)
    {X Y : D} (e : X ≅ Y) (hY : IsIso (τ.app Y)) : IsIso (τ.app X) := by
  letI := hY
  let inverse : G.obj X ⟶ F.obj X :=
    G.map e.hom ≫ inv (τ.app Y) ≫ F.map e.inv
  refine ⟨⟨inverse, ?_, ?_⟩⟩
  · -- Move the inverse across the naturality square for `e`.
    dsimp [inverse]
    rw [← NatTrans.naturality_assoc]
    simp
  · -- Do the same across the naturality square for `e.inv`.
    dsimp [inverse]
    rw [Category.assoc, Category.assoc, NatTrans.naturality]
    simp

/-- Helper for Lemma 21.43.2: a component of a natural transformation is an isomorphism at any
retract of an object where it is already an isomorphism. -/
lemma natTrans_app_isIso_of_retract {E : Type*} [Category E] {F G : D ⥤ E} (τ : F ⟶ G)
    {X Y : D} (r : Retract X Y) (hY : IsIso (τ.app Y)) : IsIso (τ.app X) := by
  letI := hY
  let inverse : G.obj X ⟶ F.obj X :=
    G.map r.i ≫ inv (τ.app Y) ≫ F.map r.r
  refine ⟨⟨inverse, ?_, ?_⟩⟩
  · -- The split mono/epi identities collapse the transported inverse.
    dsimp [inverse]
    rw [← NatTrans.naturality_assoc]
    simp [← F.map_comp, r.retract]
  · -- The same argument on the right uses naturality for the retraction map.
    dsimp [inverse]
    rw [Category.assoc, Category.assoc, NatTrans.naturality]
    simp [← G.map_comp, r.retract]

-- Proof sketch: the Section `21.43` comparison condition is invariant under isomorphism in the
-- ambient derived category, so the defining object property is strictly full.
/-- Lemma 21.43.2 (1): the Section `21.43` object property defining `QC(C, 𝒪)`
is closed under isomorphisms. Equivalently, `QC(C, 𝒪)` is a strictly full
subcategory of `D`. -/
@[stacks 0GYW]
instance qc_isClosedUnderIsomorphisms :
    IsClosedUnderIsomorphisms (isQuasiCoherent 𝒪 RGamma derivedRestrict comparison) where
  of_iso {X Y} e hX U V f := by
    let τ : RGamma V ⋙ derivedRestrict f ⟶ RGamma U := comparison f
    -- Transport the comparison isomorphism across the ambient isomorphism `e`.
    simpa [τ] using natTrans_app_isIso_of_iso τ e.symm (hX f)

-- Proof sketch: retracts preserve the comparison-isomorphism condition, so the source-facing
-- owner is saturated.
/-- Lemma 21.43.2 (2): the Section `21.43` object property is stable under retracts. Equivalently,
`QC(C, 𝒪)` is saturated in `D`. -/
@[stacks 0GYW]
instance qc_isStableUnderRetracts :
    IsStableUnderRetracts (isQuasiCoherent 𝒪 RGamma derivedRestrict comparison) where
  of_retract {X Y} r hY U V f := by
    let τ : RGamma V ⋙ derivedRestrict f ⟶ RGamma U := comparison f
    -- Transport the comparison isomorphism along the mapped retract diagram.
    simpa [τ] using natTrans_app_isIso_of_retract τ r (hY f)

end

section

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor D n).Additive]
variable [Pretriangulated D]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{uC})
variable
  (RGamma : ∀ U : C, D ⥤ DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (derivedRestrict :
    ∀ {U V : C}, (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)
variable [∀ U : C, (RGamma U).CommShift ℤ]
variable [∀ U : C, (RGamma U).IsTriangulated]
variable [∀ {U V : C} (f : U ⟶ V), (derivedRestrict f).CommShift ℤ]
variable [∀ {U V : C} (f : U ⟶ V), (derivedRestrict f).IsTriangulated]
variable [∀ {U V : C} (f : U ⟶ V), NatTrans.CommShift (comparison f) ℤ]

local notation "QCP" => isQuasiCoherent 𝒪 RGamma derivedRestrict comparison

omit [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
/-- Helper for Lemma 21.43.2: shifting an object preserves the pointwise comparison-isomorphism
condition for a fixed comparison natural transformation. -/
lemma natTrans_app_isIso_of_shift {E : Type*} [Category E] [HasShift D ℤ] [HasShift E ℤ]
    {F G : D ⥤ E} [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
    (n : ℤ) {X : D} (hX : IsIso (τ.app X)) : IsIso (τ.app (X⟦n⟧)) := by
  letI := hX
  have hshifted : IsIso ((τ.app X)⟦n⟧') := by
    change IsIso ((shiftFunctor E n).map (τ.app X))
    infer_instance
  -- Rewrite the shifted component as a composition of the shift-commutation isomorphisms and
  -- the shifted original component.
  letI := hshifted
  let e₁ := (F.commShiftIso n).app X
  let e₂ : (F.obj X)⟦n⟧ ≅ (G.obj X)⟦n⟧ := asIso ((τ.app X)⟦n⟧')
  let e₃ := ((G.commShiftIso n).app X).symm
  have hcomp : IsIso (e₁.hom ≫ e₂.hom ≫ e₃.hom) := by
    change IsIso ((e₁ ≪≫ e₂ ≪≫ e₃).hom)
    infer_instance
  simpa [NatTrans.app_shift, e₁, e₂, e₃, Category.assoc] using hcomp

/-- Helper for Lemma 21.43.2: the comparison maps on a distinguished triangle form a morphism
between the triangles obtained by applying the two exact functors. -/
def comparison_triangle_morphism
    (comparisonNat :
      ∀ {U V : C} (f : U ⟶ V),
        RGamma V ⋙ derivedRestrict f ⟶ RGamma U)
    [∀ {U V : C} (f : U ⟶ V), NatTrans.CommShift (comparisonNat f) ℤ]
    {U V : C} (f : U ⟶ V) (T : Pretriangulated.Triangle D) :
    (RGamma V ⋙ derivedRestrict f).mapTriangle.obj T ⟶ (RGamma U).mapTriangle.obj T where
  hom₁ := (comparisonNat f).app T.obj₁
  hom₂ := (comparisonNat f).app T.obj₂
  hom₃ := (comparisonNat f).app T.obj₃
  comm₁ := by
    -- The first square is the naturality square for `T.mor₁`.
    simpa using NatTrans.naturality (comparisonNat f) T.mor₁
  comm₂ := by
    -- The second square is the naturality square for `T.mor₂`.
    simpa using NatTrans.naturality (comparisonNat f) T.mor₂
  comm₃ := by
    -- The third square combines naturality for `T.mor₃` with shift compatibility.
    dsimp [Functor.mapTriangle]
    have hshift :=
      congrArg
        (fun k ↦ (derivedRestrict f).map ((RGamma V).map T.mor₃) ≫ k)
        (NatTrans.shift_app_comm (comparisonNat f) (1 : ℤ) T.obj₁)
    simp only [Functor.commShiftIso_comp_hom_app] at hshift
    have hnat :
        (derivedRestrict f).map ((RGamma V).map T.mor₃) ≫
            (comparisonNat f).app (T.obj₁⟦(1 : ℤ)⟧) ≫
            ((RGamma U).commShiftIso (1 : ℤ)).hom.app T.obj₁ =
          (comparisonNat f).app T.obj₃ ≫
            (RGamma U).map T.mor₃ ≫
            ((RGamma U).commShiftIso (1 : ℤ)).hom.app T.obj₁ := by
      simpa [Functor.comp_map, Category.assoc] using
        (NatTrans.naturality_assoc (comparisonNat f) T.mor₃
          (((RGamma U).commShiftIso (1 : ℤ)).hom.app T.obj₁))
    simpa [Functor.commShiftIso_comp_hom_app, Category.assoc] using hshift.trans hnat

-- Proof sketch: the comparison-isomorphism condition is stable under zero, shifts, and
-- distinguished triangles once every comparison functor is exact in the triangulated sense and
-- the comparison maps themselves commute with shifts.
/-- Lemma 21.43.2 (3): if each `RΓ(U,-)` and each derived restriction functor is exact, and
the comparison natural transformations commute with shifts, then the Section `21.43` object
property is triangulated. -/
@[stacks 0GYW]
instance qc_isTriangulated :
    ObjectProperty.IsTriangulated (isQuasiCoherent 𝒪 RGamma derivedRestrict comparison) where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    intro U V f
    let τ : RGamma V ⋙ derivedRestrict f ⟶ RGamma U := comparison f
    -- Both sides evaluate the zero object to zero objects, so the comparison map is automatic.
    exact isIso_of_source_target_iso_zero
      (τ.app (0 : D))
      (Functor.map_isZero (RGamma V ⋙ derivedRestrict f) (isZero_zero D)).isoZero
      (Functor.map_isZero (RGamma U) (isZero_zero D)).isoZero
  toIsStableUnderShift := by
    refine ⟨fun n ↦ ⟨fun X hX U V f ↦ ?_⟩⟩
    -- Shift compatibility of the comparison natural transformation transports the isomorphism.
    simpa using
      natTrans_app_isIso_of_shift (comparison f) n (hX f)
  toIsTriangulatedClosed₂ :=
    ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ U V f ↦ by
      -- Apply the five-lemma style triangle argument to the comparison morphism of triangles.
      let φ := comparison_triangle_morphism 𝒪 RGamma derivedRestrict comparison f T
      have hφ₁ : IsIso φ.hom₁ := by
        simpa [φ] using h₁ f
      have hφ₃ : IsIso φ.hom₃ := by
        simpa [φ] using h₃ f
      exact isIso₂_of_isIso₁₃ φ
        ((RGamma V ⋙ derivedRestrict f).map_distinguished T hT)
        ((RGamma U).map_distinguished T hT)
        hφ₁ hφ₃)

end

section

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{uC})
variable
  (RGamma : ∀ U : C, D ⥤ DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (derivedRestrict :
    ∀ {U V : C}, (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)

local notation "QCP" => isQuasiCoherent 𝒪 RGamma derivedRestrict comparison

/-- Helper for Lemma 21.43.2: if a `Discrete ι`-colimit is built from objects whose comparison
maps for `f` are isomorphisms, then the comparison map at the colimit object is also an
isomorphism. -/
lemma comparison_app_isIso_of_discrete_colimit (ι : Type w) {X : D}
    (p :
      ObjectProperty.ColimitOfShape
        (isQuasiCoherent 𝒪 RGamma derivedRestrict comparison) (Discrete ι) X)
    {U V : C} (f : U ⟶ V)
    [PreservesColimitsOfShape (Discrete ι) (RGamma U)]
    [PreservesColimitsOfShape (Discrete ι) (RGamma V ⋙ derivedRestrict f)] :
    IsIso ((comparison f).app X) := by
  let τ : RGamma V ⋙ derivedRestrict f ⟶ RGamma U := comparison f
  have hα : ∀ j : Discrete ι, IsIso ((Functor.whiskerLeft p.diag τ).app j) := by
    intro j
    simpa using p.prop_diag_obj j f
  letI : IsIso (Functor.whiskerLeft p.diag τ) :=
    NatIso.isIso_of_isIso_app (Functor.whiskerLeft p.diag τ)
  -- Once the whiskered transformation is a natural isomorphism, its component at the colimit
  -- point is an isomorphism because both functors preserve this colimit.
  simpa [τ] using isIso_app_coconePt_of_preservesColimit p.diag τ p.cocone p.isColimit

-- Proof sketch: the source comparison maps commute with `ι`-indexed direct sums, so the
-- comparison-isomorphism condition is preserved by those sums when the comparison functors
-- preserve them.
/-- Lemma 21.43.2 (4): the Section `21.43` object property is closed under `ι`-indexed direct
sums. -/
@[stacks 0GYW]
instance qc_isClosedUnderDirectSums (ι : Type w)
    [∀ U : C, PreservesColimitsOfShape (Discrete ι) (RGamma U)]
    [∀ {U V : C} (f : U ⟶ V), PreservesColimitsOfShape (Discrete ι) (derivedRestrict f)] :
    IsClosedUnderColimitsOfShape
      (isQuasiCoherent 𝒪 RGamma derivedRestrict comparison) (Discrete ι) :=
  ObjectProperty.IsClosedUnderColimitsOfShape.mk' (fun X hX U V f ↦ by
    rcases hX with ⟨F, hF⟩
    -- Replace the chosen strict colimit by the packaged colimit presentation used by the
    -- generic colimit-transport lemma above.
    exact
      comparison_app_isIso_of_discrete_colimit
        𝒪 RGamma derivedRestrict comparison ι
        (ObjectProperty.ColimitOfShape.colimit F hF) f)

end

end CategoryTheory.ModulesOnCategory
