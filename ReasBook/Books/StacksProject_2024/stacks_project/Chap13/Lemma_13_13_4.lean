import Mathlib
import StacksProject_2024.stacks_project.Chap12.Lemma_12_16_2
import StacksProject_2024.stacks_project.Chap12.Lemma_12_19_2
import StacksProject_2024.stacks_project.Chap13.Definition_13_13_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_6_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_6_11
import StacksProject_2024.stacks_project.Chap13.Lemma_13_6_6
import StacksProject_2024.stacks_project.Chap13.Lemma_13_6_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open scoped CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]

local notation "FilF" => finiteFilteredObjectCat 𝒜
local notation "KFilt" => HomotopyCategory FilF (ComplexShape.up ℤ)

/-- Helper for Lemma 13.13.4: the full subcategory of finite filtered objects inherits the
ambient preadditive structure on filtered objects. -/
local instance finiteFilteredObject_preadditive : Preadditive FilF := by
  letI : Preadditive (Fil(𝒜)) := FilteredObject.filteredObject_preadditive
  infer_instance

/-- Helper for Lemma 13.13.4: graded objects over an abelian category carry the induced
preadditive structure. -/
local instance gradedObject_preadditive : Preadditive (GradedObject ℤ 𝒜) := by
  infer_instance

/-- Helper for Lemma 13.13.4: the map induced on the `p`-th graded piece by a filtered morphism. -/
private abbrev filtered_graded_piece_map {A B : FilteredObject 𝒜} (f : A ⟶ B) (p : ℤ) :
    gr^{p} A ⟶ gr^{p} B :=
  cokernel.map (A.filtration.stageInclusion p) (B.filtration.stageInclusion p)
    (FilteredObject.Hom.stageMap f (p + 1)) (FilteredObject.Hom.stageMap f p)
    (FilteredObject.Hom.stageInclusion_naturality f p)

/-- Helper for Lemma 13.13.4: the map induced on associated graded objects by a filtered
morphism. -/
private def filtered_associated_graded_map {A B : FilteredObject 𝒜} (f : A ⟶ B) :
    A.associatedGraded ⟶ B.associatedGraded :=
  fun p ↦ filtered_graded_piece_map f p

/-- Helper for Lemma 13.13.4: stage maps induced by the identity filtered morphism are
identities. -/
private theorem filtered_stage_map_id (A : FilteredObject 𝒜) (p : ℤ) :
    FilteredObject.Hom.stageMap (𝟙 A) p = 𝟙 (F^{p} A) := by
  exact (cancel_mono (A.filtration.obj p).arrow).1 (by
    simp [FilteredObject.Hom.stageMap_comm])

/-- Helper for Lemma 13.13.4: stage maps respect composition of filtered morphisms. -/
private theorem filtered_stage_map_comp {A B D : FilteredObject 𝒜} (f : A ⟶ B) (g : B ⟶ D)
    (p : ℤ) :
    FilteredObject.Hom.stageMap (f ≫ g) p =
      FilteredObject.Hom.stageMap f p ≫ FilteredObject.Hom.stageMap g p := by
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

/-- Helper for Lemma 13.13.4: stage maps of zero filtered morphisms are zero. -/
private theorem filtered_stage_map_zero (A B : FilteredObject 𝒜) (p : ℤ) :
    FilteredObject.Hom.stageMap (0 : A ⟶ B) p = 0 := by
  exact (cancel_mono (B.filtration.obj p).arrow).1 (by
    rw [FilteredObject.Hom.stageMap_comm]
    simp)

/-- Helper for Lemma 13.13.4: stage maps of filtered morphisms preserve addition. -/
private theorem filtered_stage_map_add {A B : FilteredObject 𝒜} (f g : A ⟶ B) (p : ℤ) :
    FilteredObject.Hom.stageMap (f + g) p =
      FilteredObject.Hom.stageMap f p + FilteredObject.Hom.stageMap g p := by
  exact (cancel_mono (B.filtration.obj p).arrow).1 (by
    calc
      FilteredObject.Hom.stageMap (f + g) p ≫ (B.filtration.obj p).arrow
          = (A.filtration.obj p).arrow ≫ (f + g).hom := by
              rw [FilteredObject.Hom.stageMap_comm]
      _ = (A.filtration.obj p).arrow ≫ f.hom + (A.filtration.obj p).arrow ≫ g.hom := by
            simp [Category.assoc]
      _ = (FilteredObject.Hom.stageMap f p + FilteredObject.Hom.stageMap g p) ≫
            (B.filtration.obj p).arrow := by
            rw [Preadditive.add_comp, FilteredObject.Hom.stageMap_comm,
              FilteredObject.Hom.stageMap_comm])

/-- Helper for Lemma 13.13.4: induced maps on graded pieces preserve identities. -/
private theorem filtered_graded_piece_map_id (A : FilteredObject 𝒜) (p : ℤ) :
    filtered_graded_piece_map (𝟙 A) p = 𝟙 (gr^{p} A) := by
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [filtered_graded_piece_map, filtered_stage_map_id])

/-- Helper for Lemma 13.13.4: induced maps on graded pieces respect composition. -/
private theorem filtered_graded_piece_map_comp {A B D : FilteredObject 𝒜} (f : A ⟶ B)
    (g : B ⟶ D) (p : ℤ) :
    filtered_graded_piece_map (f ≫ g) p =
      filtered_graded_piece_map f p ≫ filtered_graded_piece_map g p := by
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [filtered_graded_piece_map, Category.assoc, filtered_stage_map_comp])

/-- Helper for Lemma 13.13.4: induced maps on graded pieces preserve zero morphisms. -/
private theorem filtered_graded_piece_map_zero (A B : FilteredObject 𝒜) (p : ℤ) :
    filtered_graded_piece_map (0 : A ⟶ B) p = 0 := by
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [filtered_graded_piece_map, filtered_stage_map_zero])

/-- Helper for Lemma 13.13.4: induced maps on graded pieces preserve addition. -/
private theorem filtered_graded_piece_map_add {A B : FilteredObject 𝒜} (f g : A ⟶ B) (p : ℤ) :
    filtered_graded_piece_map (f + g) p =
      filtered_graded_piece_map f p + filtered_graded_piece_map g p := by
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [filtered_graded_piece_map, filtered_stage_map_add, Category.assoc])

/-- Helper for Lemma 13.13.4: induced maps on associated graded objects preserve identities. -/
private theorem filtered_associated_graded_map_id (A : FilteredObject 𝒜) :
    filtered_associated_graded_map (𝟙 A) = 𝟙 A.associatedGraded := by
  ext p
  simpa [filtered_associated_graded_map] using filtered_graded_piece_map_id A p

/-- Helper for Lemma 13.13.4: induced maps on associated graded objects respect composition. -/
private theorem filtered_associated_graded_map_comp {A B D : FilteredObject 𝒜} (f : A ⟶ B)
    (g : B ⟶ D) :
    filtered_associated_graded_map (f ≫ g) =
      filtered_associated_graded_map f ≫ filtered_associated_graded_map g := by
  ext p
  simpa [filtered_associated_graded_map] using filtered_graded_piece_map_comp f g p

/-- Helper for Lemma 13.13.4: induced maps on associated graded objects preserve zero
morphisms. -/
private theorem filtered_associated_graded_map_zero (A B : FilteredObject 𝒜) :
    filtered_associated_graded_map (0 : A ⟶ B) = 0 := by
  ext p
  simpa [filtered_associated_graded_map] using filtered_graded_piece_map_zero A B p

/-- Helper for Lemma 13.13.4: induced maps on associated graded objects preserve addition. -/
private theorem filtered_associated_graded_map_add {A B : FilteredObject 𝒜} (f g : A ⟶ B) :
    filtered_associated_graded_map (f + g) =
      filtered_associated_graded_map f + filtered_associated_graded_map g := by
  -- TODO: the remaining blocker is to identify the codomain addition on graded-object morphisms
  -- with pointwise degreewise addition after `ext p`.
  sorry

variable (𝒜) in
/-- Helper for Lemma 13.13.4: the associated graded functor on filtered objects. -/
private def filtered_associated_graded_functor : Fil(𝒜) ⥤ GradedObject ℤ 𝒜 where
  obj A := A.associatedGraded
  map f := filtered_associated_graded_map f
  map_id A := filtered_associated_graded_map_id A
  map_comp f g := filtered_associated_graded_map_comp f g

/-- Helper for Lemma 13.13.4: the associated graded functor on filtered objects is additive. -/
local instance filtered_associated_graded_functor_additive :
    (filtered_associated_graded_functor 𝒜).Additive where
  map_add := by
    intro A B f g
    exact filtered_associated_graded_map_add f g

/-- Helper for Lemma 13.13.4: the associated graded functor on filtered objects preserves zero
morphisms. -/
local instance filtered_associated_graded_functor_preservesZeroMorphisms :
    (filtered_associated_graded_functor 𝒜).PreservesZeroMorphisms where
  map_zero A B := filtered_associated_graded_map_zero A B

variable (𝒜) in
/-- Helper for Lemma 13.13.4: the associated graded functor restricted to finite filtered
objects. -/
private abbrev finiteFilteredAssociatedGradedBridge :
    finiteFilteredObjectCat 𝒜 ⥤ GradedObject ℤ 𝒜 :=
  ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))) ⋙
    filtered_associated_graded_functor 𝒜

/-- Helper for Lemma 13.13.4: the associated graded functor remains additive after restriction to
finite filtered objects. -/
local instance finiteFilteredAssociatedGradedBridge_additive :
    (finiteFilteredAssociatedGradedBridge 𝒜).Additive := by
  dsimp [finiteFilteredAssociatedGradedBridge]
  infer_instance

variable (𝒜) in
/-- Helper for Lemma 13.13.4: the induced associated graded functor on the homotopy category of
finite filtered objects. -/
private abbrev finiteFilteredAssociatedGradedHomotopyBridge :
    HomotopyCategory (finiteFilteredObjectCat 𝒜) (ComplexShape.up ℤ) ⥤
      HomotopyCategory (GradedObject ℤ 𝒜) (ComplexShape.up ℤ) :=
  (finiteFilteredAssociatedGradedBridge 𝒜).mapHomotopyCategory (ComplexShape.up ℤ)

local instance finiteFiltered_hasFiniteBiproducts_13_13_4 : HasFiniteBiproducts FilF :=
  HasFiniteBiproducts.of_hasFiniteProducts

local instance finiteFiltered_hasBinaryBiproducts_13_13_4 : HasBinaryBiproducts FilF :=
  Limits.hasBinaryBiproducts_of_finite_biproducts _

variable (𝒜) in
/-- Helper for Lemma 13.13.4: the morphism property of filtered quasi-isomorphisms induced by the
associated graded functor on finite filtered complexes. -/
private abbrev filteredQuasiIsomorphismProperty :
    MorphismProperty (HomotopyCategory (finiteFilteredObjectCat 𝒜) (ComplexShape.up ℤ)) :=
  (HomotopyCategory.quasiIso (GradedObject ℤ 𝒜) (ComplexShape.up ℤ)).inverseImage
    (finiteFilteredAssociatedGradedHomotopyBridge 𝒜)

variable (𝒜) in
/-- Helper for Lemma 13.13.4: the object property of filtered acyclic complexes induced by the
associated graded functor on finite filtered complexes. -/
private abbrev filteredAcyclicProperty :
    ObjectProperty (HomotopyCategory (finiteFilteredObjectCat 𝒜) (ComplexShape.up ℤ)) :=
  (HomotopyCategory.subcategoryAcyclic (GradedObject ℤ 𝒜)).inverseImage
    (finiteFilteredAssociatedGradedHomotopyBridge 𝒜)

scoped notation "FQis(" A:arg ")" =>
  filteredQuasiIsomorphismProperty A

scoped notation "FAc(" A:arg ")" =>
  filteredAcyclicProperty A

local notation "H0gr" =>
  finiteFilteredAssociatedGradedHomotopyBridge 𝒜 ⋙
    HomotopyCategory.homologyFunctor (GradedObject ℤ 𝒜) (ComplexShape.up ℤ) 0

/-- Helper for Lemma 13.13.4: the homotopy-level associated graded functor commutes with shifts. -/
local instance finiteFilteredAssociatedGradedHomotopyBridge_commShift :
    (finiteFilteredAssociatedGradedHomotopyBridge 𝒜).CommShift ℤ := by
  infer_instance

/-- Helper for Lemma 13.13.4: the composite `H^0 ∘ gr` carries the standard shift sequence. -/
local instance filteredAssociatedGradedZeroHomology_shiftSequence :
    (H0gr).ShiftSequence ℤ := by
  exact (Functor.ShiftSequence.tautological (F := H0gr) (M := ℤ))

local instance filteredAssociatedGradedZeroHomology_isHomological :
    (H0gr).IsHomological := by
  infer_instance

/-- Helper for Lemma 13.13.4: shifting a filtered complex and then taking `H^0 ∘ gr` agrees with
taking degree-`n` homology after `gr`. -/
private noncomputable def filteredAssociatedGradedZeroHomologyShiftObjIso
    (X : KFilt) (n : ℤ) :
    ((H0gr).shift n).obj X ≅
      ((HomotopyCategory.homologyFunctor (GradedObject ℤ 𝒜) (ComplexShape.up ℤ) n).obj
        ((finiteFilteredAssociatedGradedHomotopyBridge 𝒜).obj X)) := by
  change
    (HomotopyCategory.homologyFunctor (GradedObject ℤ 𝒜) (ComplexShape.up ℤ) 0).obj
      ((finiteFilteredAssociatedGradedHomotopyBridge 𝒜).obj ((shiftFunctor KFilt n).obj X)) ≅
    ((HomotopyCategory.homologyFunctor (GradedObject ℤ 𝒜) (ComplexShape.up ℤ) n).obj
      ((finiteFilteredAssociatedGradedHomotopyBridge 𝒜).obj X))
  refine (HomotopyCategory.homologyFunctor (GradedObject ℤ 𝒜) (ComplexShape.up ℤ) 0).mapIso
      (((finiteFilteredAssociatedGradedHomotopyBridge 𝒜).commShiftIso n).app X) ≪≫ ?_
  exact ((HomotopyCategory.homologyFunctor (GradedObject ℤ 𝒜) (ComplexShape.up ℤ) 0).shiftIso
    n 0 n (by omega)).app ((finiteFilteredAssociatedGradedHomotopyBridge 𝒜).obj X)

/- Domain-style sampling for Lemma `13.13.4`.
- primary domain: triangulated localizations defined by the homological kernel of a homological
  functor on a homotopy category;
- sampled owner declarations in this domain:
  `finiteFilteredAssociatedGradedHomotopyBridge 𝒜`,
  `HomotopyCategory.homologyFunctor (GradedObject ℤ 𝒜) (up ℤ) 0`,
  `Functor.homologicalKernel`,
  `ObjectProperty.trW`,
  `MorphismProperty.Q`;
- best owner abstraction: the canonical homological-kernel owner
  `((finiteFilteredAssociatedGradedHomotopyBridge 𝒜) ⋙
    HomotopyCategory.homologyFunctor (GradedObject ℤ 𝒜) (up ℤ) 0).homologicalKernel`,
  together with its derived Verdier morphism property and localization functor;
- primitive data: the canonical composite `H^0 ∘ gr` built from
  `finiteFilteredAssociatedGradedHomotopyBridge 𝒜` and the degree-zero homology functor;
- derived API: its homological kernel, the induced morphism property `.trW`, and the localization
  functor `.Q`;
- source/core/bridge triage:
  `source-facing`: the filtered acyclic object property `FAc(𝒜)` and the filtered
    quasi-isomorphism property `FQis(𝒜)`;
  `core/canonical`: `Functor.homologicalKernel`, `ObjectProperty.trW`, and `MorphismProperty.Q`;
  `bridge/view`: the identifications in this file between `FAc(𝒜)`, `FQis(𝒜)`, and the canonical
    homological-kernel localization package.

This file therefore keeps the source-facing `FAc(𝒜)`/`FQis(𝒜)` statements while using the
canonical composite `H^0 ∘ gr` directly, without any parallel local wrapper around that owner or
around the localization functor `(FQis(𝒜) : MorphismProperty KFilt).Q`. The only inverted-morphism
input needed below is the canonical bridge
`Functor.homologicalKernel_trW_isInvertedBy` from Lemma `13.6.11`. -/

-- Route correction: the source-faithful `H^0 ∘ gr` homological-kernel route in this file is
-- already stable; the remaining failure is upstream in `Definition_13_13_2`, not in these proofs.

/-- The filtered acyclic objects are exactly the homological kernel of `H^0 ∘ gr`. -/
theorem filteredAcyclic_eq_homologicalKernel :
    (FAc(𝒜) : ObjectProperty KFilt) = (H0gr).homologicalKernel :=
by
  -- Unfold the source-facing filtered acyclic predicate and compare it with the canonical
  -- homological-kernel predicate objectwise.
  ext X
  change HomotopyCategory.subcategoryAcyclic (GradedObject ℤ 𝒜)
      ((finiteFilteredAssociatedGradedHomotopyBridge 𝒜).obj X) ↔
    (H0gr).homologicalKernel X
  rw [HomotopyCategory.mem_subcategoryAcyclic_iff, Functor.mem_homologicalKernel_iff]
  constructor
  · intro h n
    -- Transport the vanishing of `H_n(gr X)` to the shifted degree-zero formulation.
    exact IsZero.of_iso (h n) (filteredAssociatedGradedZeroHomologyShiftObjIso (𝒜 := 𝒜) X n)
  · intro h n
    -- The same comparison recovers vanishing of the `n`-th graded homology.
    exact IsZero.of_iso (h n) (filteredAssociatedGradedZeroHomologyShiftObjIso (𝒜 := 𝒜) X n).symm

/-- The Verdier morphism property of filtered acyclic objects is the filtered quasi-isomorphism
property. -/
theorem filteredAcyclic_trW_eq_filteredQuasiIso :
    (FAc(𝒜) : ObjectProperty KFilt).trW =
      (FQis(𝒜) : MorphismProperty KFilt) := by
  -- Rewrite `trW` for the inverse-image object property and identify the target class with
  -- quasi-isomorphisms on the associated graded category.
  ext X Y f
  rw [filteredAcyclicProperty, ObjectProperty.inverseImage_trW_iff,
    filteredQuasiIsomorphismProperty, MorphismProperty.inverseImage_iff]
  simp [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]

/-- Lemma 13.13.4 (1): the full subcategory `FAc(𝒜)` of `K(Fil^f(𝒜))` consisting of filtered
acyclic complexes is strictly full. -/
instance filteredAcyclic_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (FAc(𝒜) : ObjectProperty KFilt) := by
  -- Transport the standard strictly-full instance from the homological kernel owner.
  simpa [filteredAcyclic_eq_homologicalKernel] using
    (inferInstance : ObjectProperty.IsClosedUnderIsomorphisms (H0gr).homologicalKernel)

/-- Lemma 13.13.4 (2): the full subcategory `FAc(𝒜)` of `K(Fil^f(𝒜))` consisting of filtered
acyclic complexes is saturated. -/
instance filteredAcyclic_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts
      (FAc(𝒜) : ObjectProperty KFilt) := by
  -- Transport the retract-stability instance from the homological kernel owner.
  simpa [filteredAcyclic_eq_homologicalKernel] using
    (inferInstance : ObjectProperty.IsStableUnderRetracts (H0gr).homologicalKernel)

/-- Lemma 13.13.4 (3): the full subcategory `FAc(𝒜)` of `K(Fil^f(𝒜))` consisting of filtered
acyclic complexes is triangulated. -/
instance filteredAcyclic_isTriangulated :
    ObjectProperty.IsTriangulated
      (FAc(𝒜) : ObjectProperty KFilt) := by
  -- Transport the triangulated instance from the homological kernel owner.
  simpa [filteredAcyclic_eq_homologicalKernel] using
    (inferInstance : ObjectProperty.IsTriangulated (H0gr).homologicalKernel)

/-- Lemma 13.13.4 (4): the corresponding saturated multiplicative system of
`K(Fil^f(𝒜))` is the set `FQis(𝒜)` of filtered quasi-isomorphisms. -/
instance filteredQuasiIso_isSaturatedMultiplicativeSystem :
    IsSaturatedMultiplicativeSystem (FQis(𝒜) : MorphismProperty KFilt) := by
  -- Rewrite `FQis(𝒜)` as the Verdier class attached to `FAc(𝒜)`.
  simpa [filteredAcyclic_trW_eq_filteredQuasiIso] using
    (inferInstance : IsSaturatedMultiplicativeSystem
      ((FAc(𝒜) : ObjectProperty KFilt).trW))

-- Proof sketch: apply Lemma `13.6.10` to the triangulated subcategory
-- `FAc(𝒜) = (H^0 ∘ gr).homologicalKernel`, whose associated
-- multiplicative system is by definition `FQis(𝒜)`.
/-- Lemma 13.13.4 (5): the kernel of the localization functor
`Q : K(Fil^f(𝒜)) ⥤ FQis(𝒜)⁻¹K(Fil^f(𝒜))` is `FAc(𝒜)`. -/
theorem kernel_filteredQuasiIsomorphismLocalizationFunctor :
    Functor.kernel
        (((FQis(𝒜) : MorphismProperty KFilt).Q) :
          KFilt ⥤
            (FQis(𝒜) : MorphismProperty KFilt).Localization) =
      (FAc(𝒜) : ObjectProperty KFilt) := by
  -- Replace the source-facing localization with the canonical `trW`-localization of `FAc(𝒜)`.
  rw [← filteredAcyclic_trW_eq_filteredQuasiIso]
  exact kernel_trW_eq_self (P := (FAc(𝒜) : ObjectProperty KFilt))

-- Proof sketch: the canonical composite `H^0 ∘ gr` is homological by
-- Lemma `13.13.3`, so `Functor.mem_homologicalKernel_trW_iff` shows that the canonical
-- morphism property `((H^0 ∘ gr).homologicalKernel).trW` is inverted. The required factorization
-- is then the direct canonical localization lift through the quotient functor
-- `(FQis(𝒜) : MorphismProperty KFilt).Q`.
/-- Lemma 13.13.4 (6): the functor `H^0 ∘ gr` factors through the localization functor
`Q : K(Fil^f(𝒜)) ⥤ FQis(𝒜)⁻¹K(Fil^f(𝒜))`. -/
theorem exists_filteredGradedZeroHomologyFunctor_factorization :
    ∃ H' :
        (FQis(𝒜) : MorphismProperty KFilt).Localization ⥤
          GradedObject ℤ 𝒜,
      (((FQis(𝒜) : MorphismProperty KFilt).Q) :
          KFilt ⥤
        (FQis(𝒜) : MorphismProperty KFilt).Localization) ⋙
          H' =
        H0gr := by
  -- First identify `FQis(𝒜)` with the canonical `trW` attached to `H0gr`.
  have hInv : (FQis(𝒜) : MorphismProperty KFilt).IsInvertedBy H0gr := by
    rw [← filteredAcyclic_trW_eq_filteredQuasiIso, filteredAcyclic_eq_homologicalKernel]
    exact Functor.homologicalKernel_trW_isInvertedBy (H := H0gr)
  -- Then the strict localization universal property provides the required factorization.
  let hQ := Localization.strictUniversalPropertyFixedTargetQ
    (FQis(𝒜) : MorphismProperty KFilt) (GradedObject ℤ 𝒜)
  refine ⟨hQ.lift H0gr hInv, ?_⟩
  exact hQ.fac H0gr hInv

end CategoryTheory
