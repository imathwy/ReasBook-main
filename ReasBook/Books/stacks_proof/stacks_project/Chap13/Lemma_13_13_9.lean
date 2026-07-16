import Mathlib
import stacks_proof.stacks_project.Chap12.Lemma_12_16_2
import stacks_proof.stacks_project.Chap12.Lemma_12_19_2
import stacks_proof.stacks_project.Chap13.Definition_13_11_3
import stacks_proof.stacks_project.Chap13.Lemma_13_11_6
import stacks_proof.stacks_project.Chap13.Lemma_13_10_6
import stacks_proof.stacks_project.Chap13.Lemma_13_6_10
import stacks_proof.stacks_project.Chap13.Definition_13_13_1
import stacks_proof.stacks_project.Chap13.Lemma_13_13_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory.TStructure
open scoped CategoryTheory

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/- Domain-style sampling for Lemma `13.13.9`.
- primary domain: bounded filtered homotopy categories, filtered acyclic complexes, filtered
  quasi-isomorphisms, and their localization in the filtered derived category;
- sampled owner declarations:
  `DF⁺(𝒜)`, `DF⁻(𝒜)`, `DFᵇ(𝒜)`,
  `FQis(𝒜)`,
  `FAc(𝒜)`,
  `MorphismProperty.Q`,
  `boundedBelowHomotopyProperty`,
  `boundedAboveHomotopyProperty`,
  `boundedHomotopyProperty`;
- best owner abstraction: the source-facing derived owners are already the chapter notations
  `DF⁺(𝒜)`, `DF⁻(𝒜)`, and `DFᵇ(𝒜)` from Definition `13.13.7`; this lemma should therefore live
  at the bridge/view layer, expressing the bounded filtered localizations of
  `K⁺(Fil^f(𝒜))`, `K⁻(Fil^f(𝒜))`, and `Kᵇ(Fil^f(𝒜))` into those existing owners rather than
  introducing a second bounded filtered derived-category owner;
- primitive data: the chapter owners `FQis(𝒜)`, `FAc(𝒜)`,
  `((FAc(𝒜) : ObjectProperty KFilt).trW).Q`,
  together with the bounded homotopy object properties on `K(Fil^f(𝒜))`;
- derived API: the bounded filtered quasi-isomorphism owners `FQis⁺/⁻/ᵇ`, the notation-only
  bounded filtered acyclic views `FAc⁺/⁻/ᵇ`, and the canonical bounded bridge functors
  `K⁺(Fil^f(𝒜)) ⥤ DF⁺(𝒜)`, `K⁻(Fil^f(𝒜)) ⥤ DF⁻(𝒜)`, `Kᵇ(Fil^f(𝒜)) ⥤ DFᵇ(𝒜)`.

Source/core/bridge triage:
- `source-facing`: the bounded filtered localization statements of Lemma `13.13.9`;
- `core/canonical`: `DF⁺(𝒜)`, `DF⁻(𝒜)`, `DFᵇ(𝒜)`, `FQis(𝒜)`, `FAc(𝒜)`,
  `((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DF(𝒜))`, and the bounded homotopy owners on
  `K(Fil^f(𝒜))`;
- `bridge/view`: the bounded filtered quasi-isomorphism owners, the notation-only restricted
  acyclic views, and the induced functors from bounded filtered homotopy categories into the
  existing bounded filtered derived categories. -/

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]
variable [HasBinaryBiproducts (finiteFilteredObjectCat 𝒜)]
variable [Pretriangulated (HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ))]

local notation "FilF" => finiteFilteredObjectCat 𝒜
local notation "KFilt" => HomotopyCategory FilF (up ℤ)

local instance gradedObject_preadditive_13_13_9 : Preadditive (GradedObject ℤ 𝒜) := by
  infer_instance

/-- Helper for Lemma 13.13.9: the map induced on the `p`-th graded piece by a morphism of finite
filtered objects. -/
private abbrev filtered_graded_piece_map {A B : FilteredObject 𝒜} (f : A ⟶ B) (p : ℤ) :
    gr^{p} A ⟶ gr^{p} B :=
  cokernel.map (A.filtration.stageInclusion p) (B.filtration.stageInclusion p)
    (FilteredObject.Hom.stageMap f (p + 1)) (FilteredObject.Hom.stageMap f p)
    (FilteredObject.Hom.stageInclusion_naturality f p)

/-- Helper for Lemma 13.13.9: the associated graded map induced by a morphism of filtered
objects. -/
private def filtered_associated_graded_map {A B : FilteredObject 𝒜} (f : A ⟶ B) :
    A.associatedGraded ⟶ B.associatedGraded :=
  fun p ↦ filtered_graded_piece_map f p

/-- Helper for Lemma 13.13.9: stage maps of identity morphisms are identities. -/
private theorem filtered_stage_map_id (A : FilteredObject 𝒜) (p : ℤ) :
    FilteredObject.Hom.stageMap (𝟙 A) p = 𝟙 (F^{p} A) := by
  -- Compare both maps after postcomposing with the mono stage inclusion.
  exact (cancel_mono (A.filtration.obj p).arrow).1 (by
    rw [FilteredObject.Hom.stageMap_comm]
    simp)

/-- Helper for Lemma 13.13.9: stage maps respect composition of filtered morphisms. -/
private theorem filtered_stage_map_comp {A B D : FilteredObject 𝒜} (f : A ⟶ B) (g : B ⟶ D)
    (p : ℤ) :
    FilteredObject.Hom.stageMap (f ≫ g) p =
      FilteredObject.Hom.stageMap f p ≫ FilteredObject.Hom.stageMap g p := by
  -- Compare both composites after postcomposing with the target stage inclusion.
  exact (cancel_mono (D.filtration.obj p).arrow).1 (by
    calc
      FilteredObject.Hom.stageMap (f ≫ g) p ≫ (D.filtration.obj p).arrow
          = (A.filtration.obj p).arrow ≫ (f ≫ g).hom := by
              rw [FilteredObject.Hom.stageMap_comm]
      _ = ((A.filtration.obj p).arrow ≫ f.hom) ≫ g.hom := by
            simp [Category.assoc]
      _ = (FilteredObject.Hom.stageMap f p ≫ (B.filtration.obj p).arrow) ≫ g.hom := by
            rw [FilteredObject.Hom.stageMap_comm]
      _ = FilteredObject.Hom.stageMap f p ≫
            (FilteredObject.Hom.stageMap g p ≫ (D.filtration.obj p).arrow) := by
            rw [FilteredObject.Hom.stageMap_comm]
            simp [Category.assoc]
      _ = (FilteredObject.Hom.stageMap f p ≫ FilteredObject.Hom.stageMap g p) ≫
            (D.filtration.obj p).arrow := by
            simp [Category.assoc])

/-- Helper for Lemma 13.13.9: stage maps preserve addition. -/
private theorem filtered_stage_map_add {A B : FilteredObject 𝒜} (f g : A ⟶ B) (p : ℤ) :
    FilteredObject.Hom.stageMap (f + g) p =
      FilteredObject.Hom.stageMap f p + FilteredObject.Hom.stageMap g p := by
  -- Compare both maps after postcomposing with the mono target stage inclusion.
  exact (cancel_mono (B.filtration.obj p).arrow).1 (by
    calc
      FilteredObject.Hom.stageMap (f + g) p ≫ (B.filtration.obj p).arrow
          = (A.filtration.obj p).arrow ≫ (f + g).hom := by
              rw [FilteredObject.Hom.stageMap_comm]
      _ = (A.filtration.obj p).arrow ≫ f.hom + (A.filtration.obj p).arrow ≫ g.hom := by
            simp
      _ = (FilteredObject.Hom.stageMap f p + FilteredObject.Hom.stageMap g p) ≫
            (B.filtration.obj p).arrow := by
            rw [Preadditive.add_comp, FilteredObject.Hom.stageMap_comm,
              FilteredObject.Hom.stageMap_comm])

/-- Helper for Lemma 13.13.9: stage maps of zero filtered morphisms are zero. -/
private theorem filtered_stage_map_zero (A B : FilteredObject 𝒜) (p : ℤ) :
    FilteredObject.Hom.stageMap (0 : A ⟶ B) p = 0 := by
  -- Compare after postcomposing with the target stage inclusion.
  exact (cancel_mono (B.filtration.obj p).arrow).1 (by
    rw [FilteredObject.Hom.stageMap_comm]
    simp)

/-- Helper for Lemma 13.13.9: graded-piece maps preserve identities. -/
private theorem filtered_graded_piece_map_id (A : FilteredObject 𝒜) (p : ℤ) :
    filtered_graded_piece_map (𝟙 A) p = 𝟙 (gr^{p} A) := by
  -- Compare after precomposing with the cokernel projection.
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [filtered_graded_piece_map, filtered_stage_map_id])

/-- Helper for Lemma 13.13.9: graded-piece maps respect composition. -/
private theorem filtered_graded_piece_map_comp {A B D : FilteredObject 𝒜} (f : A ⟶ B)
    (g : B ⟶ D) (p : ℤ) :
    filtered_graded_piece_map (f ≫ g) p =
      filtered_graded_piece_map f p ≫ filtered_graded_piece_map g p := by
  -- Compare after precomposing with the source cokernel projection.
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [filtered_graded_piece_map, Category.assoc, filtered_stage_map_comp])

/-- Helper for Lemma 13.13.9: graded-piece maps preserve addition. -/
private theorem filtered_graded_piece_map_add {A B : FilteredObject 𝒜} (f g : A ⟶ B) (p : ℤ) :
    filtered_graded_piece_map (f + g) p =
      filtered_graded_piece_map f p + filtered_graded_piece_map g p := by
  -- Compare after precomposing with the source cokernel projection.
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [filtered_graded_piece_map, filtered_stage_map_add])

/-- Helper for Lemma 13.13.9: graded-piece maps of zero morphisms are zero. -/
private theorem filtered_graded_piece_map_zero (A B : FilteredObject 𝒜) (p : ℤ) :
    filtered_graded_piece_map (0 : A ⟶ B) p = 0 := by
  -- Compare after precomposing with the source cokernel projection.
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [filtered_graded_piece_map, filtered_stage_map_zero])

/-- Helper for Lemma 13.13.9: associated graded maps preserve identities. -/
private theorem filtered_associated_graded_map_id (A : FilteredObject 𝒜) :
    filtered_associated_graded_map (𝟙 A) = 𝟙 A.associatedGraded := by
  -- Extensionality reduces the claim to the degreewise identity statement.
  ext p
  simpa using filtered_graded_piece_map_id A p

/-- Helper for Lemma 13.13.9: associated graded maps respect composition. -/
private theorem filtered_associated_graded_map_comp {A B D : FilteredObject 𝒜} (f : A ⟶ B)
    (g : B ⟶ D) :
    filtered_associated_graded_map (f ≫ g) =
      filtered_associated_graded_map f ≫ filtered_associated_graded_map g := by
  -- Extensionality reduces the claim to the degreewise composition statement.
  ext p
  simpa using filtered_graded_piece_map_comp f g p

/-- Helper for Lemma 13.13.9: associated graded maps preserve addition. -/
private theorem filtered_associated_graded_map_add {A B : FilteredObject 𝒜} (f g : A ⟶ B) :
    filtered_associated_graded_map (f + g) =
      filtered_associated_graded_map f + filtered_associated_graded_map g := by
  -- TODO: reduce the addition on `GradedObject` morphisms to the degreewise pointwise formula.
  sorry

/-- Helper for Lemma 13.13.9: associated graded maps of zero morphisms are zero. -/
private theorem filtered_associated_graded_map_zero {A B : FilteredObject 𝒜} :
    filtered_associated_graded_map (0 : A ⟶ B) = 0 := by
  -- Morphisms of graded objects are determined degreewise, so reduce to the graded-piece formula.
  ext p
  change filtered_graded_piece_map (0 : A ⟶ B) p = 0
  exact filtered_graded_piece_map_zero A B p

/-- Helper for Lemma 13.13.9: the associated graded functor on filtered objects. -/
private def filtered_associated_graded_functor : Fil(𝒜) ⥤ GradedObject ℤ 𝒜 where
  obj A := A.associatedGraded
  map f := filtered_associated_graded_map f
  map_id A := filtered_associated_graded_map_id A
  map_comp f g := filtered_associated_graded_map_comp f g

/-- Helper for Lemma 13.13.9: the associated graded functor on filtered objects is additive. -/
private instance filtered_associated_graded_functor_additive :
    (filtered_associated_graded_functor (𝒜 := 𝒜)).Additive where
  map_add := by
    intro A B f g
    simpa using filtered_associated_graded_map_add f g

/-- Helper for Lemma 13.13.9: the associated graded functor preserves zero morphisms. -/
private instance filtered_associated_graded_functor_preservesZeroMorphisms :
    (filtered_associated_graded_functor (𝒜 := 𝒜)).PreservesZeroMorphisms where
  map_zero A B := filtered_associated_graded_map_zero

variable (𝒜) in
/-- Helper for Lemma 13.13.9: the associated graded functor restricted to finite filtered
objects. -/
abbrev finiteFilteredAssociatedGradedFunctor : FilF ⥤ GradedObject ℤ 𝒜 :=
  ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))) ⋙
    filtered_associated_graded_functor (𝒜 := 𝒜)

variable (𝒜) in
/-- Helper for Lemma 13.13.9: the associated graded functor induced on the homotopy category of
finite filtered objects. -/
abbrev filteredAssociatedGradedHomotopyFunctor :
    KFilt ⥤ HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ) :=
  (finiteFilteredAssociatedGradedFunctor 𝒜).mapHomotopyCategory (up ℤ)

variable (𝒜) in
/-- Helper for Lemma 13.13.9: the morphism property of filtered quasi-isomorphisms on
`K(Fil^f(\mathcal A))`. -/
abbrev filteredQuasiIso : MorphismProperty KFilt :=
  (HomotopyCategory.quasiIso (GradedObject ℤ 𝒜) (up ℤ)).inverseImage
    (filteredAssociatedGradedHomotopyFunctor 𝒜)

scoped notation "FQis(" A:arg ")" => filteredQuasiIso A

variable (𝒜) in
/-- Helper for Lemma 13.13.9: a morphism is a filtered quasi-isomorphism exactly when its
associated graded image is a quasi-isomorphism. -/
theorem filteredQuasiIso_iff {K L : KFilt} (α : K ⟶ L) :
    (filteredQuasiIso 𝒜 : MorphismProperty KFilt) α ↔
      HomotopyCategory.quasiIso (GradedObject ℤ 𝒜) (up ℤ)
        ((filteredAssociatedGradedHomotopyFunctor 𝒜).map α) := by
  rfl

variable (𝒜) in
/-- Helper for Lemma 13.13.9: the object property of filtered acyclic complexes on
`K(Fil^f(\mathcal A))`. -/
abbrev filteredAcyclic : ObjectProperty KFilt :=
  (HomotopyCategory.subcategoryAcyclic (GradedObject ℤ 𝒜)).inverseImage
    (filteredAssociatedGradedHomotopyFunctor 𝒜)

scoped notation "FAc(" A:arg ")" => filteredAcyclic A

variable (𝒜) in
/-- Helper for Lemma 13.13.9: a finite filtered complex is filtered acyclic exactly when its
associated graded complex is acyclic. -/
theorem filteredAcyclic_iff (K : KFilt) :
    (filteredAcyclic 𝒜 : ObjectProperty KFilt) K ↔
      HomotopyCategory.subcategoryAcyclic (GradedObject ℤ 𝒜)
        ((filteredAssociatedGradedHomotopyFunctor 𝒜).obj K) := by
  rfl

variable (𝒜) in
/-- Helper for Lemma 13.13.9: the filtered derived category is the localization of
`K(Fil^f(\mathcal A))` at the filtered quasi-isomorphisms. -/
abbrev filteredDerivedCategory : Type (max u v) :=
  (FQis(𝒜) : MorphismProperty KFilt).Localization

scoped notation "DF(" A:arg ")" => filteredDerivedCategory A

local instance finiteFiltered_hasFiniteBiproducts_13_13_9 : HasFiniteBiproducts FilF :=
  Limits.HasFiniteBiproducts.of_hasFiniteProducts

local instance pretriangulated_filtered_homotopy_13_13_9 : Pretriangulated KFilt := by
  -- Reuse the standard pretriangulated structure on filtered homotopy categories.
  exact HomotopyCategory.instPretriangulatedIntUp FilF

local instance isTriangulated_filtered_homotopy_13_13_9 : IsTriangulated KFilt := by
  -- The standard homotopy-category triangulation upgrades the pretriangulated structure.
  infer_instance

/-- Helper for Lemma 13.13.9: the associated graded functor on filtered homotopy categories is
triangulated. -/
/-- Helper for Lemma 13.13.9: filtered acyclic objects define the same Verdier morphism property
as filtered quasi-isomorphisms. -/
theorem filteredAcyclic_trW_eq_filteredQuasiIso :
    (FAc(𝒜) : ObjectProperty KFilt).trW =
      (FQis(𝒜) : MorphismProperty KFilt) := by
  -- TODO: rewrite the inverse-image `trW` class through the ordinary graded acyclic owner.
  sorry

/-- Helper for Lemma 13.13.9: the kernel of the filtered quasi-isomorphism localization functor is
the filtered acyclic subcategory. -/
theorem kernel_filteredQuasiIsomorphismLocalizationFunctor :
    Functor.kernel
        (((FQis(𝒜) : MorphismProperty KFilt).Q) :
          KFilt ⥤
            (FQis(𝒜) : MorphismProperty KFilt).Localization) =
      (FAc(𝒜) : ObjectProperty KFilt) := by
  -- TODO: transport the canonical `kernel_trW_eq_self` statement across `FAc.trW = FQis`.
  sorry

private abbrev QFilt : KFilt ⥤ DF(𝒜) :=
  (((FQis(𝒜) : MorphismProperty KFilt).Q) : KFilt ⥤ DF(𝒜))

/-- Helper for Lemma 13.13.9: the associated graded homotopy functor followed by the ordinary
derived localization. -/
abbrev filteredAssociatedGradedHomotopyToDerivedFunctor :
    KFilt ⥤ DerivedCategory (GradedObject ℤ 𝒜) :=
  filteredAssociatedGradedHomotopyFunctor 𝒜 ⋙ DerivedCategory.Qh

/-- Helper for Lemma 13.13.9: the associated graded homotopy-to-derived functor inverts filtered
quasi-isomorphisms. -/
theorem filteredAssociatedGradedHomotopyToDerivedFunctor_inverts_filteredQuasiIsomorphisms :
    (FQis(𝒜) : MorphismProperty KFilt).IsInvertedBy
      (filteredAssociatedGradedHomotopyToDerivedFunctor (𝒜 := 𝒜)) := by
  intro X Y f hf
  rw [filteredQuasiIso_iff (𝒜 := 𝒜) f] at hf
  exact Localization.inverts
    (DerivedCategory.Qh : HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ) ⥤
      DerivedCategory (GradedObject ℤ 𝒜))
    (HomotopyCategory.quasiIso (GradedObject ℤ 𝒜) (up ℤ))
    ((filteredAssociatedGradedHomotopyFunctor 𝒜).map f)
    hf

/-- Helper for Lemma 13.13.9: the associated graded homotopy-to-derived functor descends through
the filtered localization. -/
abbrev filteredDerivedAssociatedGradedFunctor :
    DF(𝒜) ⥤ DerivedCategory (GradedObject ℤ 𝒜) :=
  Localization.lift
    (filteredAssociatedGradedHomotopyToDerivedFunctor (𝒜 := 𝒜))
    (filteredAssociatedGradedHomotopyToDerivedFunctor_inverts_filteredQuasiIsomorphisms
      (𝒜 := 𝒜))
    QFilt

-- Route correction: the owner files `Definition_13_13_7`, `Lemma_13_11_6`, and
-- `Lemma_13_13_4` are not type-correct in this workspace. This file therefore rebuilds only the
-- small bounded-owner and boundedness-transfer API needed for Lemma 13.13.9 directly from the
-- stable earlier Chapter 13 owners `DF(𝒜)`, `gr : DF(𝒜) ⥤ D(Gr(\mathcal A))`, and `QFilt`.

variable (𝒜) in
/-- Helper for Lemma 13.13.9: the bounded-below filtered derived owner is the inverse image of
`t.plus` along the descended associated graded functor. -/
abbrev filteredDerivedPlusProperty :
    ObjectProperty (DF(𝒜)) :=
  (t.plus : ObjectProperty (DerivedCategory (GradedObject ℤ 𝒜))).inverseImage
    (filteredDerivedAssociatedGradedFunctor (𝒜 := 𝒜))

variable (𝒜) in
/-- Helper for Lemma 13.13.9: the bounded-above filtered derived owner is the inverse image of
`t.minus` along the descended associated graded functor. -/
abbrev filteredDerivedMinusProperty :
    ObjectProperty (DF(𝒜)) :=
  (t.minus : ObjectProperty (DerivedCategory (GradedObject ℤ 𝒜))).inverseImage
    (filteredDerivedAssociatedGradedFunctor (𝒜 := 𝒜))

variable (𝒜) in
/-- Helper for Lemma 13.13.9: the bounded filtered derived owner is the inverse image of
`t.bounded` along the descended associated graded functor. -/
abbrev filteredDerivedBoundedProperty :
    ObjectProperty (DF(𝒜)) :=
  (t.bounded : ObjectProperty (DerivedCategory (GradedObject ℤ 𝒜))).inverseImage
    (filteredDerivedAssociatedGradedFunctor (𝒜 := 𝒜))

variable (𝒜) in
/-- Helper for Lemma 13.13.9: the bounded-below filtered derived category. -/
abbrev filteredDerivedPlusCategory : Type (max u v) :=
  (filteredDerivedPlusProperty 𝒜).FullSubcategory

variable (𝒜) in
/-- Helper for Lemma 13.13.9: the bounded-above filtered derived category. -/
abbrev filteredDerivedMinusCategory : Type (max u v) :=
  (filteredDerivedMinusProperty 𝒜).FullSubcategory

variable (𝒜) in
/-- Helper for Lemma 13.13.9: the bounded filtered derived category. -/
abbrev filteredDerivedBoundedCategory : Type (max u v) :=
  (filteredDerivedBoundedProperty 𝒜).FullSubcategory

scoped notation "DF⁺(" A:arg ")" => filteredDerivedPlusCategory A
scoped notation "DF⁻(" A:arg ")" => filteredDerivedMinusCategory A
scoped notation "DFᵇ(" A:arg ")" => filteredDerivedBoundedCategory A

/-- Helper for Lemma 13.13.9: the bounded-below graded homotopy category. -/
private abbrev gradedHomotopyPlus : Type (max u v) :=
  (HomotopyCategory.plus (GradedObject ℤ 𝒜)).FullSubcategory

/-- Helper for Lemma 13.13.9: the bounded-above graded homotopy category. -/
private abbrev gradedHomotopyMinus : Type (max u v) :=
  (HomotopyCategory.minus (GradedObject ℤ 𝒜)).FullSubcategory

/-- Helper for Lemma 13.13.9: the bounded graded homotopy category. -/
private abbrev gradedHomotopyBounded : Type (max u v) :=
  (HomotopyCategory.bounded (GradedObject ℤ 𝒜)).FullSubcategory

/-- Helper for Lemma 13.13.9: the quotient functor to the ordinary derived category sends a
bounded-below homotopy object to a bounded-below derived object. -/
theorem graded_qh_obj_mem_t_plus
    (X : gradedHomotopyPlus (𝒜 := 𝒜)) :
    (t.plus : ObjectProperty (DerivedCategory (GradedObject ℤ 𝒜)))
      (DerivedCategory.Qh.obj X.obj) := by
  -- Reuse the ordinary bounded-below `Qh` bridge on the graded abelian category.
  simpa [gradedHomotopyPlus] using
    (qh_obj_mem_t_plus (𝒜 := GradedObject ℤ 𝒜) X)

/-- Helper for Lemma 13.13.9: the quotient functor to the ordinary derived category sends a
bounded-above homotopy object to a bounded-above derived object. -/
theorem graded_qh_obj_mem_t_minus
    (X : gradedHomotopyMinus (𝒜 := 𝒜)) :
    (t.minus : ObjectProperty (DerivedCategory (GradedObject ℤ 𝒜)))
      (DerivedCategory.Qh.obj X.obj) := by
  -- Reuse the ordinary bounded-above `Qh` bridge on the graded abelian category.
  simpa [gradedHomotopyMinus] using
    (qh_obj_mem_t_minus (𝒜 := GradedObject ℤ 𝒜) X)

/-- Helper for Lemma 13.13.9: the quotient functor to the ordinary derived category sends a
bounded homotopy object to a bounded derived object. -/
theorem graded_qh_obj_mem_t_bounded
    (X : gradedHomotopyBounded (𝒜 := 𝒜)) :
    (t.bounded : ObjectProperty (DerivedCategory (GradedObject ℤ 𝒜)))
      (DerivedCategory.Qh.obj X.obj) := by
  -- Reuse the ordinary bounded `Qh` bridge on the graded abelian category.
  simpa [gradedHomotopyBounded] using
    (qh_obj_mem_t_bounded (𝒜 := GradedObject ℤ 𝒜) X)

/-- Helper for Lemma 13.13.9: the descended associated graded functor factors the ambient
filtered localization functor exactly through the ordinary associated graded homotopy-to-derived
functor. -/
abbrev filteredDerived_associated_graded_fac
    (X : KFilt) :
    (filteredDerivedAssociatedGradedFunctor (𝒜 := 𝒜)).obj (QFilt.obj X) ≅
      DerivedCategory.Qh.obj ((filteredAssociatedGradedHomotopyFunctor 𝒜).obj X) := by
  -- This is the canonical localization factorization from Lemma 13.13.6.
  simpa [QFilt, filteredDerivedAssociatedGradedFunctor] using
    (Localization.fac
      (filteredAssociatedGradedHomotopyToDerivedFunctor (𝒜 := 𝒜))
      (filteredAssociatedGradedHomotopyToDerivedFunctor_inverts_filteredQuasiIsomorphisms
        (𝒜 := 𝒜))
      (QFilt : KFilt ⥤ DF(𝒜))).app X

/-- Helper for Lemma 13.13.9: a fixed representative complex for the associated graded homotopy
image of a filtered complex. -/
private abbrev associated_graded_representative (X : KFilt) :=
  ((filteredAssociatedGradedHomotopyFunctor 𝒜).obj X).as

/-- Helper for Lemma 13.13.9: the homotopy-category homology object of the associated graded
image. -/
private abbrev associated_graded_representative_homology (X : KFilt) (n : ℤ) :=
  ((HomotopyCategory.homologyFunctor (GradedObject ℤ 𝒜) (up ℤ) n).obj
    ((filteredAssociatedGradedHomotopyFunctor 𝒜).obj X))

/-- Helper for Lemma 13.13.9: vanishing of derived homology of the associated graded image forces
vanishing of the ordinary homology of the associated graded representative complex. -/
theorem associated_graded_representative_homology_isZero_of_derived
    {X : KFilt} {n : ℤ}
    (h :
      IsZero
        ((H^n).obj
          (DerivedCategory.Qh.obj ((filteredAssociatedGradedHomotopyFunctor 𝒜).obj X)))) :
    IsZero (associated_graded_representative_homology (𝒜 := 𝒜) X n) := by
  let Y := (filteredAssociatedGradedHomotopyFunctor 𝒜).obj X
  -- Compare derived homology with homotopy-category homology on the same representative.
  simpa [associated_graded_representative_homology, Y] using
    (((DerivedCategory.homologyFunctorFactorsh (GradedObject ℤ 𝒜) n).app Y).isZero_iff).1 h

/-- Helper for Lemma 13.13.9: an object of `DF⁺(\mathcal A)` has associated graded homology
vanishing in sufficiently low degrees on any filtered homotopy representative. -/
theorem filteredDerivedPlus_homology_vanishesBelow
    (X : (ObjectProperty.inverseImage (filteredDerivedPlusProperty 𝒜) QFilt).FullSubcategory) :
    ∃ a : ℤ, ∀ n : ℤ, n < a →
      IsZero (associated_graded_representative_homology (𝒜 := 𝒜) X.obj n) := by
  let e := filteredDerived_associated_graded_fac (𝒜 := 𝒜) X.obj
  have hDerived :
      (t.plus : ObjectProperty (DerivedCategory (GradedObject ℤ 𝒜)))
        (DerivedCategory.Qh.obj ((filteredAssociatedGradedHomotopyFunctor 𝒜).obj X.obj)) := by
    -- Transport the defining bounded-below property of `X` across the canonical comparison.
    exact
      (t.plus : ObjectProperty (DerivedCategory (GradedObject ℤ 𝒜))).prop_of_iso e X.property
  rcases
      (derivedCategory_t_plus_iff
        (𝒜 := GradedObject ℤ 𝒜)
        (DerivedCategory.Qh.obj ((filteredAssociatedGradedHomotopyFunctor 𝒜).obj X.obj))).1
        hDerived with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  intro n hn
  exact associated_graded_representative_homology_isZero_of_derived
    (𝒜 := 𝒜) (X := X.obj) (n := n) (ha n hn)

/-- Helper for Lemma 13.13.9: an object of `DF⁻(\mathcal A)` has associated graded homology
vanishing in sufficiently high degrees on any filtered homotopy representative. -/
theorem filteredDerivedMinus_homology_vanishesAbove
    (X : (ObjectProperty.inverseImage (filteredDerivedMinusProperty 𝒜) QFilt).FullSubcategory) :
    ∃ b : ℤ, ∀ n : ℤ, b < n →
      IsZero (associated_graded_representative_homology (𝒜 := 𝒜) X.obj n) := by
  let e := filteredDerived_associated_graded_fac (𝒜 := 𝒜) X.obj
  have hDerived :
      (t.minus : ObjectProperty (DerivedCategory (GradedObject ℤ 𝒜)))
        (DerivedCategory.Qh.obj ((filteredAssociatedGradedHomotopyFunctor 𝒜).obj X.obj)) := by
    -- Transport the defining bounded-above property of `X` across the canonical comparison.
    exact
      (t.minus : ObjectProperty (DerivedCategory (GradedObject ℤ 𝒜))).prop_of_iso e X.property
  rcases
      (derivedCategory_t_minus_iff
        (𝒜 := GradedObject ℤ 𝒜)
        (DerivedCategory.Qh.obj ((filteredAssociatedGradedHomotopyFunctor 𝒜).obj X.obj))).1
        hDerived with
    ⟨b, hb⟩
  refine ⟨b, ?_⟩
  intro n hn
  exact associated_graded_representative_homology_isZero_of_derived
    (𝒜 := 𝒜) (X := X.obj) (n := n) (hb n hn)

/-- Helper for Lemma 13.13.9: an object of `DFᵇ(\mathcal A)` has associated graded homology
vanishing outside a finite interval on any filtered homotopy representative. -/
theorem filteredDerivedBounded_homology_eventuallyVanishes
    (X : (ObjectProperty.inverseImage (filteredDerivedBoundedProperty 𝒜) QFilt).FullSubcategory) :
    ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n →
      IsZero (associated_graded_representative_homology (𝒜 := 𝒜) X.obj n) := by
  let e := filteredDerived_associated_graded_fac (𝒜 := 𝒜) X.obj
  have hDerived :
      (t.bounded : ObjectProperty (DerivedCategory (GradedObject ℤ 𝒜)))
        (DerivedCategory.Qh.obj ((filteredAssociatedGradedHomotopyFunctor 𝒜).obj X.obj)) := by
    -- Transport the defining bounded property of `X` across the canonical comparison.
    exact
      (t.bounded : ObjectProperty (DerivedCategory (GradedObject ℤ 𝒜))).prop_of_iso e X.property
  rcases
      (derivedCategory_t_bounded_iff
        (𝒜 := GradedObject ℤ 𝒜)
        (DerivedCategory.Qh.obj ((filteredAssociatedGradedHomotopyFunctor 𝒜).obj X.obj))).1
        hDerived with
    ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  refine ⟨a, b, ?_⟩
  intro n hn
  cases hn with
  | inl hna =>
      exact associated_graded_representative_homology_isZero_of_derived
        (𝒜 := 𝒜) (X := X.obj) (n := n) (ha n hna)
  | inr hbn =>
      exact associated_graded_representative_homology_isZero_of_derived
        (𝒜 := 𝒜) (X := X.obj) (n := n) (hb n hbn)

-- The `CommShift` and triangulated-instance bridge for `QFilt` is deferred until the local owner
-- chain provides `HasShift (DF(𝒜)) ℤ`. The current rescue pass isolates earlier parser and
-- transport blockers first.

/- The filtered quasi-isomorphisms in `K^+(\mathrm{Fil}^f(\mathcal A))` are the morphisms whose
images in `K(\mathrm{Fil}^f(\mathcal A))` are filtered quasi-isomorphisms. -/
variable (𝒜) in
abbrev boundedBelowFilteredQuasiIso :
    MorphismProperty (K⁺(FilF)) :=
  (FQis(𝒜) : MorphismProperty KFilt).inverseImage
    (HomotopyCategory.plus FilF).ι

/- The filtered quasi-isomorphisms in `K^-(\mathrm{Fil}^f(\mathcal A))` are the morphisms whose
images in `K(\mathrm{Fil}^f(\mathcal A))` are filtered quasi-isomorphisms. -/
variable (𝒜) in
abbrev boundedAboveFilteredQuasiIso :
    MorphismProperty (K⁻(FilF)) :=
  (FQis(𝒜) : MorphismProperty KFilt).inverseImage
    (HomotopyCategory.minus FilF).ι

/- The filtered quasi-isomorphisms in `K^b(\mathrm{Fil}^f(\mathcal A))` are the morphisms whose
images in `K(\mathrm{Fil}^f(\mathcal A))` are filtered quasi-isomorphisms. -/
variable (𝒜) in
abbrev boundedFilteredQuasiIso :
    MorphismProperty (Kᵇ(FilF)) :=
  (FQis(𝒜) : MorphismProperty KFilt).inverseImage
    (HomotopyCategory.bounded FilF).ι

scoped notation "FQis⁺(" A:arg ")" => boundedBelowFilteredQuasiIso A
scoped notation "FQis⁻(" A:arg ")" => boundedAboveFilteredQuasiIso A
scoped notation "FQisᵇ(" A:arg ")" => boundedFilteredQuasiIso A

/-- Helper for Lemma 13.13.9: bounded-below filtered quasi-isomorphisms are exactly the ambient
filtered quasi-isomorphisms after applying the inclusion into `K(Fil^f(\mathcal A))`. -/
private theorem boundedBelowFilteredQuasiIso_iff
    {X Y : K⁺(FilF)} (f : X ⟶ Y) :
    (FQis⁺(𝒜) : MorphismProperty (K⁺(FilF))) f ↔
      (FQis(𝒜) : MorphismProperty KFilt)
        ((HomotopyCategory.plus FilF).ι.map f) := by
  rfl
scoped notation "FAc⁺(" A:arg ")" =>
  ObjectProperty.inverseImage
    (FAc(A))
    (ObjectProperty.ι (HomotopyCategory.plus (finiteFilteredObjectCat A)))
scoped notation "FAc⁻(" A:arg ")" =>
  ObjectProperty.inverseImage
    (FAc(A))
    (ObjectProperty.ι (HomotopyCategory.minus (finiteFilteredObjectCat A)))
scoped notation "FAcᵇ(" A:arg ")" =>
  ObjectProperty.inverseImage
    (FAc(A))
    (ObjectProperty.ι (HomotopyCategory.bounded (finiteFilteredObjectCat A)))

-- Proof sketch: the associated graded functor on filtered homotopy categories preserves
-- bounded-below complexes, and Lemma `13.11.6 (1)` shows that the derived image of a bounded-
-- below graded complex lies in `D⁺(Gr(\mathcal A))`.
variable (𝒜) in
/-- The canonical functor `K(Fil^f(\mathcal A)) ⟶ DF(\mathcal A)` sends bounded-below filtered
homotopy objects to `DF⁺(\mathcal A)`. -/
theorem filteredDerivedQuotientFunctor_obj_mem_boundedBelowFilteredDerivedCategory
    (X : K⁺(FilF)) :
    filteredDerivedPlusProperty 𝒜
      (QFilt.obj X.obj) := by
  let G : FilF ⥤ GradedObject ℤ 𝒜 := finiteFilteredAssociatedGradedFunctor 𝒜
  let Xgr : gradedHomotopyPlus (𝒜 := 𝒜) := (mapBoundedBelowHomotopyCategory (F := G)).obj X
  have hXgr :
      (t.plus : ObjectProperty (DerivedCategory (GradedObject ℤ 𝒜)))
        (DerivedCategory.Qh.obj Xgr.obj) := by
    -- The associated graded of a bounded-below filtered complex is again bounded below.
    exact graded_qh_obj_mem_t_plus (𝒜 := 𝒜) Xgr
  let e :
      (filteredDerivedAssociatedGradedFunctor (𝒜 := 𝒜)).obj (QFilt.obj X.obj) ≅
        DerivedCategory.Qh.obj Xgr.obj := by
    -- Compare the descended associated graded object with the chosen bounded-below representative.
    simpa [Xgr, G, filteredAssociatedGradedHomotopyFunctor] using
      filteredDerived_associated_graded_fac (𝒜 := 𝒜) X.obj
  exact
    (t.plus : ObjectProperty (DerivedCategory (GradedObject ℤ 𝒜))).prop_of_iso e.symm hXgr

-- Proof sketch: the same argument with bounded-above associated graded complexes lands in
-- `D⁻(Gr(\mathcal A))`.
variable (𝒜) in
/-- The canonical functor `K(Fil^f(\mathcal A)) ⟶ DF(\mathcal A)` sends bounded-above filtered
homotopy objects to `DF⁻(\mathcal A)`. -/
theorem filteredDerivedQuotientFunctor_obj_mem_boundedAboveFilteredDerivedCategory
    (X : K⁻(FilF)) :
    filteredDerivedMinusProperty 𝒜
      (QFilt.obj X.obj) := by
  let G : FilF ⥤ GradedObject ℤ 𝒜 := finiteFilteredAssociatedGradedFunctor 𝒜
  let Xgr : gradedHomotopyMinus (𝒜 := 𝒜) := (mapBoundedAboveHomotopyCategory (F := G)).obj X
  have hXgr :
      (t.minus : ObjectProperty (DerivedCategory (GradedObject ℤ 𝒜)))
        (DerivedCategory.Qh.obj Xgr.obj) := by
    -- The associated graded of a bounded-above filtered complex is again bounded above.
    exact graded_qh_obj_mem_t_minus (𝒜 := 𝒜) Xgr
  let e :
      (filteredDerivedAssociatedGradedFunctor (𝒜 := 𝒜)).obj (QFilt.obj X.obj) ≅
        DerivedCategory.Qh.obj Xgr.obj := by
    -- Compare the descended associated graded object with the chosen bounded-above representative.
    simpa [Xgr, G, filteredAssociatedGradedHomotopyFunctor] using
      filteredDerived_associated_graded_fac (𝒜 := 𝒜) X.obj
  exact
    (t.minus : ObjectProperty (DerivedCategory (GradedObject ℤ 𝒜))).prop_of_iso e.symm hXgr

/-- Helper for Lemma 13.13.9: the associated graded homotopy functor sends bounded filtered
objects to bounded graded homotopy objects. -/
theorem associated_graded_homotopy_obj_mem_bounded
    (X : Kᵇ(FilF)) :
    HomotopyCategory.bounded (GradedObject ℤ 𝒜)
      ((filteredAssociatedGradedHomotopyFunctor 𝒜).obj X.obj) := by
  -- Apply the bounded homotopy transfer lemma to the associated graded functor.
  simpa [filteredAssociatedGradedHomotopyFunctor] using
    (mapHomotopyCategory_obj_mem_bounded (F := finiteFilteredAssociatedGradedFunctor 𝒜) X)

-- Proof sketch: a bounded filtered homotopy object has bounded associated graded complex, so its
-- image in `DF(\mathcal A)` lies in `DFᵇ(\mathcal A)`.
variable (𝒜) in
/-- The canonical functor `K(Fil^f(\mathcal A)) ⟶ DF(\mathcal A)` sends bounded filtered homotopy
objects to `DFᵇ(\mathcal A)`. -/
theorem filteredDerivedQuotientFunctor_obj_mem_boundedFilteredDerivedCategory
    (X : Kᵇ(FilF)) :
    filteredDerivedBoundedProperty 𝒜
      (QFilt.obj X.obj) := by
  let Xgr : gradedHomotopyBounded (𝒜 := 𝒜) :=
    ⟨(filteredAssociatedGradedHomotopyFunctor 𝒜).obj X.obj,
      associated_graded_homotopy_obj_mem_bounded (𝒜 := 𝒜) X⟩
  have hXgr :
      (t.bounded : ObjectProperty (DerivedCategory (GradedObject ℤ 𝒜)))
        (DerivedCategory.Qh.obj Xgr.obj) := by
    -- The associated graded of a bounded filtered complex is bounded in the graded homotopy category.
    exact graded_qh_obj_mem_t_bounded (𝒜 := 𝒜) Xgr
  let e :
      (filteredDerivedAssociatedGradedFunctor (𝒜 := 𝒜)).obj (QFilt.obj X.obj) ≅
        DerivedCategory.Qh.obj Xgr.obj := by
    -- Compare the descended associated graded object with the bounded homotopy representative.
    simpa [Xgr, filteredAssociatedGradedHomotopyFunctor] using
      filteredDerived_associated_graded_fac (𝒜 := 𝒜) X.obj
  exact
    (t.bounded : ObjectProperty (DerivedCategory (GradedObject ℤ 𝒜))).prop_of_iso e.symm hXgr

/-- Helper for Lemma 13.13.9: the ambient filtered quotient functor already lands in the
bounded-below filtered derived owner on bounded-below homotopy objects. -/
theorem plus_to_filteredDerivedPlus_mem
    (X : K⁺(FilF)) :
    filteredDerivedPlusProperty 𝒜
      (((HomotopyCategory.plus FilF).ι ⋙ QFilt).obj X) := by
  -- This is the bounded-below landing statement proved just above.
  simpa using filteredDerivedQuotientFunctor_obj_mem_boundedBelowFilteredDerivedCategory
    (𝒜 := 𝒜) X

/-- Helper for Lemma 13.13.9: the ambient filtered quotient functor already lands in the
bounded-above filtered derived owner on bounded-above homotopy objects. -/
theorem minus_to_filteredDerivedMinus_mem
    (X : K⁻(FilF)) :
    filteredDerivedMinusProperty 𝒜
      (((HomotopyCategory.minus FilF).ι ⋙ QFilt).obj X) := by
  -- This is the bounded-above landing statement proved just above.
  simpa using filteredDerivedQuotientFunctor_obj_mem_boundedAboveFilteredDerivedCategory
    (𝒜 := 𝒜) X

/-- Helper for Lemma 13.13.9: the ambient filtered quotient functor already lands in the
bounded filtered derived owner on bounded homotopy objects. -/
theorem bounded_to_filteredDerivedBounded_mem
    (X : Kᵇ(FilF)) :
    filteredDerivedBoundedProperty 𝒜
      (((HomotopyCategory.bounded FilF).ι ⋙ QFilt).obj X) := by
  -- This is the bounded landing statement proved just above.
  simpa using filteredDerivedQuotientFunctor_obj_mem_boundedFilteredDerivedCategory
    (𝒜 := 𝒜) X

variable (𝒜) in
/-- The canonical functor `K^+(\mathrm{Fil}^f(\mathcal A)) ⟶ DF^+(\mathcal A)`. -/
abbrev mapBoundedBelowFilteredHomotopyToDerivedBelow :
    K⁺(FilF) ⥤ DF⁺(𝒜) :=
  (filteredDerivedPlusProperty 𝒜).lift
    ((HomotopyCategory.plus FilF).ι ⋙ QFilt)
    (plus_to_filteredDerivedPlus_mem (𝒜 := 𝒜))

variable (𝒜) in
/-- The canonical functor `K^-(\mathrm{Fil}^f(\mathcal A)) ⟶ DF^-(\mathcal A)`. -/
abbrev mapBoundedAboveFilteredHomotopyToDerivedAbove :
    K⁻(FilF) ⥤ DF⁻(𝒜) :=
  (filteredDerivedMinusProperty 𝒜).lift
    ((HomotopyCategory.minus FilF).ι ⋙ QFilt)
    (minus_to_filteredDerivedMinus_mem (𝒜 := 𝒜))

variable (𝒜) in
/-- The canonical functor `K^b(\mathrm{Fil}^f(\mathcal A)) ⟶ DF^b(\mathcal A)`. -/
abbrev mapBoundedFilteredHomotopyToDerivedBounded :
    Kᵇ(FilF) ⥤ DFᵇ(𝒜) :=
  (filteredDerivedBoundedProperty 𝒜).lift
    ((HomotopyCategory.bounded FilF).ι ⋙ QFilt)
    (bounded_to_filteredDerivedBounded_mem (𝒜 := 𝒜))


-- Proof sketch: restrict Lemma `13.13.4` from `K(Fil^f(\mathcal A))` to the bounded-below full
-- subcategory, exactly as in Lemma `13.11.6 (1)`.
/-- Lemma 13.13.9 (1): the saturated multiplicative system corresponding to
`FAc^{+}(\mathcal A)` is precisely `FQis^{+}(\mathcal A)`. -/
@[stacks 05S6]
theorem boundedBelowFilteredAcyclicProperty_trW_eq_quasiIso :
    (FAc⁺(𝒜)).trW =
      FQis⁺(𝒜) := by
  -- Restrict the ambient identification `FAc.trW = FQis` along the bounded-below inclusion.
  ext X Y f
  rw [ObjectProperty.inverseImage_trW_iff]
  simp [boundedBelowFilteredQuasiIso, filteredAcyclic_trW_eq_filteredQuasiIso]

-- Proof sketch: an object of `K^{+}(Fil^{f}(\mathcal A))` maps to zero in `DF^{+}(\mathcal A)`
-- exactly when its image in `DF(\mathcal A)` is filtered acyclic.
/-- Lemma 13.13.9 (2): the kernel of
`K^{+}(Fil^{f}(\mathcal A)) ⟶ DF^{+}(\mathcal A)` is `FAc^{+}(\mathcal A)`. -/
@[stacks 05S6]
theorem kernel_mapBoundedBelowFilteredHomotopyToDerivedBelow_eq_acyclic :
    Functor.kernel (mapBoundedBelowFilteredHomotopyToDerivedBelow 𝒜) =
      FAc⁺(𝒜) := by
  -- TODO: transport `Functor.kernel QFilt = FAc(𝒜)` across
  -- `ObjectProperty.liftCompιIso (filteredDerivedPlusProperty 𝒜)`.
  sorry

-- Proof sketch: use Lemma `13.13.8 (1)` to obtain bounded-below filtered representatives and
-- then repeat the localization argument of Lemma `13.11.6 (3)`.
/-- Lemma 13.13.9 (3): the canonical functor
`K^{+}(Fil^{f}(\mathcal A)) ⟶ DF^{+}(\mathcal A)` realizes `DF^{+}(\mathcal A)` as the
localization of `K^{+}(Fil^{f}(\mathcal A))` at `FQis^{+}(\mathcal A)`. -/
@[stacks 05S6]
theorem mapBoundedBelowFilteredHomotopyToDerivedBelow_isLocalization :
    Functor.IsLocalization
      (mapBoundedBelowFilteredHomotopyToDerivedBelow 𝒜)
      (FQis⁺(𝒜)) := by
  -- TODO: convert the bounded-below replacement from Lemma 13.13.8 into an object of `K⁺(FilF)`.
  sorry

-- Proof sketch: restrict Lemma `13.13.4` to the bounded-above full subcategory, as in
-- Lemma `13.11.6 (4)`.
/-- Lemma 13.13.9 (4): the saturated multiplicative system corresponding to
`FAc^{-}(\mathcal A)` is precisely `FQis^{-}(\mathcal A)`. -/
@[stacks 05S6]
theorem boundedAboveFilteredAcyclicProperty_trW_eq_quasiIso :
    (FAc⁻(𝒜)).trW =
      FQis⁻(𝒜) := by
  -- Restrict the ambient identification `FAc.trW = FQis` along the bounded-above inclusion.
  ext X Y f
  rw [ObjectProperty.inverseImage_trW_iff]
  simp [boundedAboveFilteredQuasiIso, filteredAcyclic_trW_eq_filteredQuasiIso]

-- Proof sketch: bounded-above filtered objects die in `DF^{-}(\mathcal A)` exactly when their
-- ambient filtered derived objects are filtered acyclic.
/-- Lemma 13.13.9 (5): the kernel of
`K^{-}(Fil^{f}(\mathcal A)) ⟶ DF^{-}(\mathcal A)` is `FAc^{-}(\mathcal A)`. -/
@[stacks 05S6]
theorem kernel_mapBoundedAboveFilteredHomotopyToDerivedAbove_eq_acyclic :
    Functor.kernel (mapBoundedAboveFilteredHomotopyToDerivedAbove 𝒜) =
      FAc⁻(𝒜) := by
  -- TODO: transport `Functor.kernel QFilt = FAc(𝒜)` across
  -- `ObjectProperty.liftCompιIso (filteredDerivedMinusProperty 𝒜)`.
  sorry

-- Proof sketch: use Lemma `13.13.8 (2)` to obtain bounded-above filtered representatives and
-- then repeat the localization argument of Lemma `13.11.6 (6)`.
/-- Lemma 13.13.9 (6): the canonical functor
`K^{-}(Fil^{f}(\mathcal A)) ⟶ DF^{-}(\mathcal A)` realizes `DF^{-}(\mathcal A)` as the
localization of `K^{-}(Fil^{f}(\mathcal A))` at `FQis^{-}(\mathcal A)`. -/
@[stacks 05S6]
theorem mapBoundedAboveFilteredHomotopyToDerivedAbove_isLocalization :
    Functor.IsLocalization
      (mapBoundedAboveFilteredHomotopyToDerivedAbove 𝒜)
      (FQis⁻(𝒜)) := by
  -- TODO: convert the bounded-above replacement from Lemma 13.13.8 into an object of `K⁻(FilF)`.
  sorry

-- Proof sketch: restrict Lemma `13.13.4` to the bounded full subcategory, as in
-- Lemma `13.11.6 (7)`.
/-- Lemma 13.13.9 (7): the saturated multiplicative system corresponding to
`FAc^{b}(\mathcal A)` is precisely `FQis^{b}(\mathcal A)`. -/
@[stacks 05S6]
theorem boundedFilteredAcyclicProperty_trW_eq_quasiIso :
    (FAcᵇ(𝒜)).trW =
      FQisᵇ(𝒜) := by
  -- Restrict the ambient identification `FAc.trW = FQis` along the bounded inclusion.
  ext X Y f
  rw [ObjectProperty.inverseImage_trW_iff]
  simp [boundedFilteredQuasiIso, filteredAcyclic_trW_eq_filteredQuasiIso]

-- Proof sketch: a bounded filtered homotopy object becomes zero in `DF^{b}(\mathcal A)` exactly
-- when it is filtered acyclic.
/-- Lemma 13.13.9 (8): the kernel of
`K^{b}(Fil^{f}(\mathcal A)) ⟶ DF^{b}(\mathcal A)` is `FAc^{b}(\mathcal A)`. -/
@[stacks 05S6]
theorem kernel_mapBoundedFilteredHomotopyToDerivedBounded_eq_acyclic :
    Functor.kernel (mapBoundedFilteredHomotopyToDerivedBounded 𝒜) =
      FAcᵇ(𝒜) := by
  -- TODO: transport `Functor.kernel QFilt = FAc(𝒜)` across
  -- `ObjectProperty.liftCompιIso (filteredDerivedBoundedProperty 𝒜)`.
  sorry

-- Proof sketch: use Lemma `13.13.8 (3)` to choose bounded filtered representatives and then
-- repeat the bounded localization argument of Lemma `13.11.6 (9)`.
/-- Lemma 13.13.9 (9): the canonical functor
`K^{b}(Fil^{f}(\mathcal A)) ⟶ DF^{b}(\mathcal A)` realizes `DF^{b}(\mathcal A)` as the
localization of `K^{b}(Fil^{f}(\mathcal A))` at `FQis^{b}(\mathcal A)`. -/
@[stacks 05S6]
theorem mapBoundedFilteredHomotopyToDerivedBounded_isLocalization :
    Functor.IsLocalization
      (mapBoundedFilteredHomotopyToDerivedBounded 𝒜)
      (FQisᵇ(𝒜)) := by
  -- TODO: convert the bounded replacement square from Lemma 13.13.8 into an object of `Kᵇ(FilF)`.
  sorry

end CategoryTheory
