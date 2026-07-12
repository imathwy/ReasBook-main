import Mathlib
import StacksProject_2024.Chap12.Definition_12_16_1
import StacksProject_2024.Chap12.Lemma_12_16_2
import StacksProject_2024.Chap12.Lemma_12_19_2
import StacksProject_2024.Chap13.Definition_13_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape
open HomotopyCategory

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "FilF" =>
  ObjectProperty.FullSubcategory (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜)))
local notation "KFilt" => HomotopyCategory FilF (up ℤ)

/-- Helper for Definition 13.13.2: the full subcategory `Fil^f(𝒜)` inherits the ambient
preadditive structure on filtered objects. -/
instance finiteFilteredObject_preadditive :
    Preadditive (Fil^f(𝒜)) := by
  -- The finite-filtered owner is a full subcategory of `Fil(𝒜)`, so the ambient preadditive
  -- structure restricts directly.
  letI : Preadditive (Fil(𝒜)) := FilteredObject.filteredObject_preadditive
  infer_instance

/-- Helper for Definition 13.13.2: the map on the `p`-th graded piece induced by a filtered
morphism. -/
private abbrev filtered_graded_piece_map {A B : FilteredObject 𝒜} (f : A ⟶ B) (p : ℤ) :
    gr^{p} A ⟶ gr^{p} B :=
  cokernel.map (A.filtration.stageInclusion p) (B.filtration.stageInclusion p)
    (FilteredObject.Hom.stageMap f (p + 1)) (FilteredObject.Hom.stageMap f p)
    (FilteredObject.Hom.stageInclusion_naturality f p)

/-- Helper for Definition 13.13.2: the associated graded morphism induced by a filtered
morphism. -/
private def filtered_associated_graded_map {A B : FilteredObject 𝒜} (f : A ⟶ B) :
    A.associatedGraded ⟶ B.associatedGraded :=
  fun p ↦ filtered_graded_piece_map f p

omit [Abelian 𝒜] in
/-- Helper for Definition 13.13.2: stage maps of identity morphisms are identities. -/
private theorem filtered_stage_map_id (A : FilteredObject 𝒜) (p : ℤ) :
    FilteredObject.Hom.stageMap (𝟙 A) p = 𝟙 (F^{p} A) := by
  exact (cancel_mono (A.filtration.obj p).arrow).1 (by
    rw [FilteredObject.Hom.stageMap_comm]
    simp)

omit [Abelian 𝒜] in
/-- Helper for Definition 13.13.2: stage maps respect composition of filtered morphisms. -/
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

/-- Helper for Definition 13.13.2: stage maps preserve addition. -/
private theorem filtered_stage_map_add {A B : FilteredObject 𝒜} (f g : A ⟶ B) (p : ℤ) :
    FilteredObject.Hom.stageMap (f + g) p =
      FilteredObject.Hom.stageMap f p + FilteredObject.Hom.stageMap g p := by
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

/-- Helper for Definition 13.13.2: the induced maps on graded pieces preserve identities. -/
private theorem filtered_graded_piece_map_id (A : FilteredObject 𝒜) (p : ℤ) :
    filtered_graded_piece_map (𝟙 A) p = 𝟙 (gr^{p} A) := by
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [filtered_graded_piece_map, filtered_stage_map_id])

/-- Helper for Definition 13.13.2: the induced maps on graded pieces respect composition. -/
private theorem filtered_graded_piece_map_comp {A B D : FilteredObject 𝒜} (f : A ⟶ B)
    (g : B ⟶ D) (p : ℤ) :
    filtered_graded_piece_map (f ≫ g) p =
      filtered_graded_piece_map f p ≫ filtered_graded_piece_map g p := by
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [filtered_graded_piece_map, Category.assoc, filtered_stage_map_comp])

/-- Helper for Definition 13.13.2: the induced maps on graded pieces preserve addition. -/
private theorem filtered_graded_piece_map_add {A B : FilteredObject 𝒜} (f g : A ⟶ B) (p : ℤ) :
    filtered_graded_piece_map (f + g) p =
      filtered_graded_piece_map f p + filtered_graded_piece_map g p := by
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [filtered_graded_piece_map, filtered_stage_map_add])

/-- Helper for Definition 13.13.2: the induced maps on associated graded objects preserve
identities. -/
private theorem filtered_associated_graded_map_id (A : FilteredObject 𝒜) :
    filtered_associated_graded_map (𝟙 A) = 𝟙 A.associatedGraded := by
  ext p
  simpa using filtered_graded_piece_map_id A p

/-- Helper for Definition 13.13.2: the induced maps on associated graded objects respect
composition. -/
private theorem filtered_associated_graded_map_comp {A B D : FilteredObject 𝒜} (f : A ⟶ B)
    (g : B ⟶ D) :
    filtered_associated_graded_map (f ≫ g) =
      filtered_associated_graded_map f ≫ filtered_associated_graded_map g := by
  ext p
  simpa using filtered_graded_piece_map_comp f g p

/-- Helper for Definition 13.13.2: the induced maps on associated graded objects preserve
addition. -/
private theorem filtered_associated_graded_map_add {A B : FilteredObject 𝒜} (f g : A ⟶ B) :
    filtered_associated_graded_map (f + g) =
      filtered_associated_graded_map f + filtered_associated_graded_map g := by
  -- Morphisms of graded objects are determined degreewise, and addition is pointwise.
  ext p
  have h_degreewise :
      filtered_associated_graded_map (f + g) p =
        filtered_graded_piece_map f p + filtered_graded_piece_map g p := by
    simpa [filtered_associated_graded_map] using filtered_graded_piece_map_add f g p
  have h_eval_add :
      (filtered_associated_graded_map f + filtered_associated_graded_map g) p =
        filtered_graded_piece_map f p + filtered_graded_piece_map g p := by
    simpa [filtered_associated_graded_map] using
      (Functor.map_add (F := GradedObject.eval p)
        (f := filtered_associated_graded_map f) (g := filtered_associated_graded_map g))
  exact h_degreewise.trans h_eval_add.symm

/-- Helper for Definition 13.13.2: the associated graded functor on filtered objects. -/
private def filtered_associated_graded_functor : Fil(𝒜) ⥤ GradedObject ℤ 𝒜 where
  obj A := A.associatedGraded
  map f := filtered_associated_graded_map f
  map_id A := filtered_associated_graded_map_id A
  map_comp f g := filtered_associated_graded_map_comp f g

/-- Helper for Definition 13.13.2: the associated graded functor on filtered objects is
additive. -/
private instance filtered_associated_graded_functor_additive :
    (filtered_associated_graded_functor (𝒜 := 𝒜)).Additive where
  map_add := by
    intro A B f g
    exact filtered_associated_graded_map_add f g

/- Domain-style sampling for Definition `13.13.2`.
- primary domain: filtered complexes in the homotopy category and their associated graded images;
- sampled owner declarations in this domain:
  `finiteFilteredObjectCat 𝒜`,
  `FilteredObject.associatedGradedFunctor`,
  `Functor.mapHomotopyCategory`,
  `HomotopyCategory.quasiIso`,
  `HomotopyCategory.subcategoryAcyclic`;
- best owner abstraction: the source-facing bridge functor from `K(Fil^f(𝒜))` to `K(Gr(𝒜))`
  induced by the associated graded functor on filtered objects, together with the canonical
  homotopy-category owners `HomotopyCategory.quasiIso` and
  `HomotopyCategory.subcategoryAcyclic` on the target;
- primitive data: the finite-filtered full-subcategory owner and the canonical associated-graded
  functor on filtered objects;
- derived API: the associated-graded homotopy functor and its inverse-image morphism and object
  properties on `K(Fil^f(𝒜))`;
- ambient structure check: the target graded category `GradedObject ℤ 𝒜` is already abelian
  upstream from `[Abelian 𝒜]`, so no separate file-scope assumption
  `[Abelian (GradedObject ℤ 𝒜)]` belongs in this local API;
- source/core/bridge triage:
  `source-facing`: the Stacks notations `FQis(𝒜)` and `FAc(𝒜)` on `K(Fil^f(𝒜))`;
  `core/canonical`: `HomotopyCategory.quasiIso` and `HomotopyCategory.subcategoryAcyclic`;
  `bridge/view`: the associated-graded homotopy functor from `K(Fil^f(𝒜))` to `K(Gr(𝒜))`.

This file therefore owns the associated-graded homotopy bridge used to define the Stacks
properties, so later files can reuse that bridge directly instead of redeclaring the same functor
under a second chapter-level name. -/

variable (𝒜) in
/-- Helper for Definition 13.13.2: the associated graded functor on the full subcategory of finite
filtered objects is obtained by restricting the ambient associated graded functor. -/
abbrev finiteFilteredAssociatedGradedFunctor : FilF ⥤ GradedObject ℤ 𝒜 :=
  ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))) ⋙
    filtered_associated_graded_functor

variable (𝒜) in
/-- Helper for Definition 13.13.2: the canonical forgetful functor on finite filtered objects is
the ambient forgetful functor restricted along the full-subcategory inclusion. -/
abbrev finiteFilteredObjectForgetFunctor : Fil^f(𝒜) ⥤ 𝒜 :=
  ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))) ⋙
    FilteredObject.forget

variable (𝒜) in
/-- Helper for Definition 13.13.2: the canonical owner name for the associated graded functor on
finite filtered objects. -/
abbrev finiteFilteredObjectAssociatedGradedFunctor :
    Fil^f(𝒜) ⥤ GradedObject ℤ 𝒜 :=
  finiteFilteredAssociatedGradedFunctor 𝒜

variable (𝒜) in
/-- The associated graded functor induced on the homotopy category of finite filtered objects. -/
abbrev filteredAssociatedGradedHomotopyFunctor :
    KFilt ⥤ HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ) :=
  (finiteFilteredAssociatedGradedFunctor 𝒜).mapHomotopyCategory (up ℤ)

/-
Definition 13.13.2 (1): the morphism property of filtered quasi-isomorphisms on the homotopy
category of finite filtered complexes.
-/
variable (𝒜) in
/-- Definition 13.13.2 (1): the owner morphism property of filtered quasi-isomorphisms on the
homotopy category of finite filtered complexes. -/
@[stacks 05RZ]
abbrev filteredQuasiIso : MorphismProperty KFilt :=
  (quasiIso (GradedObject ℤ 𝒜) (up ℤ)).inverseImage
    (filteredAssociatedGradedHomotopyFunctor 𝒜)

scoped notation "FQis(" A:arg ")" => filteredQuasiIso A

variable (𝒜) in
/-- Helper for Definition 13.13.2: a morphism of finite filtered complexes is a filtered
quasi-isomorphism exactly when its associated graded morphism is a quasi-isomorphism. -/
theorem filteredQuasiIso_iff {K L : KFilt} (α : K ⟶ L) :
    (filteredQuasiIso 𝒜 : MorphismProperty KFilt) α ↔
      quasiIso (GradedObject ℤ 𝒜) (up ℤ)
        ((filteredAssociatedGradedHomotopyFunctor 𝒜).map α) := by
  rfl

/-
Definition 13.13.2 (2): the object property of filtered acyclic complexes on the homotopy
category of finite filtered complexes.
-/
variable (𝒜) in
/-- Definition 13.13.2 (2): the owner object property of filtered acyclic complexes on the
homotopy category of finite filtered complexes. -/
@[stacks 05RZ]
abbrev filteredAcyclic : ObjectProperty KFilt :=
  (subcategoryAcyclic (GradedObject ℤ 𝒜)).inverseImage
    (filteredAssociatedGradedHomotopyFunctor 𝒜)

scoped notation "FAc(" A:arg ")" => filteredAcyclic A

variable (𝒜) in
/-- Helper for Definition 13.13.2: a finite filtered complex is filtered acyclic exactly when its
associated graded complex is acyclic. -/
theorem filteredAcyclic_iff (K : KFilt) :
    (filteredAcyclic 𝒜 : ObjectProperty KFilt) K ↔
      subcategoryAcyclic (GradedObject ℤ 𝒜)
        ((filteredAssociatedGradedHomotopyFunctor 𝒜).obj K) := by
  rfl

/- Companion checks: the associated-graded homotopy bridge and the Stacks notations `FQis(𝒜)` and
`FAc(𝒜)` are the canonical public owners used in later files. -/
#check
  (filteredAssociatedGradedHomotopyFunctor 𝒜 :
    KFilt ⥤ HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ))
#check
  (finiteFilteredObjectForgetFunctor 𝒜 :
    Fil^f(𝒜) ⥤ 𝒜)
#check
  (finiteFilteredObjectAssociatedGradedFunctor 𝒜 :
    Fil^f(𝒜) ⥤ GradedObject ℤ 𝒜)
#check (filteredQuasiIso 𝒜 : MorphismProperty KFilt)
#check (filteredAcyclic 𝒜 : ObjectProperty KFilt)
#check (FQis(𝒜) : MorphismProperty KFilt)
#check (FAc(𝒜) : ObjectProperty KFilt)
#check filteredQuasiIso_iff (𝒜 := 𝒜)
#check filteredAcyclic_iff (𝒜 := 𝒜)

end CategoryTheory
