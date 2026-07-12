import Mathlib
import StacksProject_2024.Chap12.Definition_12_19_1
import StacksProject_2024.Chap12.Lemma_12_19_2
import StacksProject_2024.Chap12.Lemma_12_16_2
import StacksProject_2024.Chap13.Lemma_13_5_4
import StacksProject_2024.Chap13.Lemma_13_5_7
import StacksProject_2024.Chap13.Lemma_13_11_2
import StacksProject_2024.Chap13.Definition_13_13_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open ComplexShape
open scoped CategoryTheory

universe u v

namespace CategoryTheory

/- Domain-style sampling for Lemma `13.13.6`.
- primary domain: filtered derived associated-graded functors and the passage from
  `D(Gr(\mathcal A))` to graded objects in `D(\mathcal A)`;
- sampled owner declarations:
  `filteredAssociatedGradedHomotopyFunctor`,
  `filteredDerivedCategory`,
  `Localization.lift`,
  `Functor.mapDerivedCategory`,
  `GradedObject.eval`;
- best owner abstraction: the descended associated-graded functor
  `DF(\mathcal A) ⥤ D(Gr(\mathcal A))` together with its direct descended graded-piece functors
  `gr^p : DF(\mathcal A) ⥤ D(\mathcal A)`, each defined as the localization lift of the
  homotopy-level `gr^p`; the bundled bridge `DF(\mathcal A) ⥤ Gr(D(\mathcal A))` is only a
  companion view obtained from `D(Gr(\mathcal A)) ⥤ Gr(D(\mathcal A))`;
- primitive data: the homotopy-level associated-graded owner
  `filteredAssociatedGradedHomotopyFunctor 𝒜`, the homotopy-level graded-piece functors, the
  canonical quotient functor `((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DFilt)`, and the
  localization lifts of
  these source-facing functors;
- derived API: the bridge functor to `Gr(D(\mathcal A))`, the comparison isomorphism between its
  degree-`p` evaluation and the direct descended `gr^p`, and the exactness data for the
  source-facing lifts;
- source/core/bridge triage:
  `source-facing`: the descended associated-graded functor on `DF(\mathcal A)` and the direct
    descended `p`-th graded-piece functors;
  `core/canonical`: `filteredDerivedCategory`,
    `((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DFilt)`,
    `Localization.lift`, `Functor.mapDerivedCategory`, and `GradedObject.eval`;
  `bridge/view`: the comparison functor `D(Gr(\mathcal A)) ⥤ Gr(D(\mathcal A))` and the bundled
    graded-object-valued packaging of the direct `gr^p`.

This file therefore keeps the localization lift to `D(Gr(\mathcal A))` as the source-facing
descended `gr`, defines the descended `gr^p` directly by localization, and treats
`DF(\mathcal A) ⥤ Gr(D(\mathcal A))` only as a companion bridge/view. -/

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]
variable [HasBinaryBiproducts (finiteFilteredObjectCat 𝒜)]

local notation "FilF" => finiteFilteredObjectCat 𝒜
local notation "KFilt" => HomotopyCategory FilF (up ℤ)
local notation "DFilt" => filteredDerivedCategory 𝒜
local notation "DGr" => DerivedCategory (GradedObject ℤ 𝒜)

/-- Helper for Lemma 13.13.6: the full subcategory of finite filtered objects inherits the
ambient preadditive structure on filtered objects. -/
local instance finiteFilteredObject_preadditive_13_13_6 : Preadditive FilF := by
  letI : Preadditive (Fil(𝒜)) := FilteredObject.filteredObject_preadditive
  infer_instance

/-- Helper for Lemma 13.13.6: graded objects over an abelian category inherit the canonical
preadditive structure needed for evaluation functors and homotopy-level exactness. -/
local instance gradedObject_preadditive_13_13_6 : Preadditive (GradedObject ℤ 𝒜) := by
  infer_instance

/-- Helper for Lemma 13.13.6: the map induced on the `p`-th graded piece by a filtered morphism. -/
private abbrev filtered_graded_piece_map {A B : FilteredObject 𝒜} (f : A ⟶ B) (p : ℤ) :
    gr^{p} A ⟶ gr^{p} B :=
  cokernel.map (A.filtration.stageInclusion p) (B.filtration.stageInclusion p)
    (FilteredObject.Hom.stageMap f (p + 1)) (FilteredObject.Hom.stageMap f p)
    (FilteredObject.Hom.stageInclusion_naturality f p)

/-- Helper for Lemma 13.13.6: the map induced on associated graded objects by a filtered
morphism. -/
private def filtered_associated_graded_map {A B : FilteredObject 𝒜} (f : A ⟶ B) :
    A.associatedGraded ⟶ B.associatedGraded :=
  fun p ↦ filtered_graded_piece_map f p

/-- Helper for Lemma 13.13.6: stage maps induced by the identity filtered morphism are
identities. -/
private theorem filtered_stage_map_id (A : FilteredObject 𝒜) (p : ℤ) :
    FilteredObject.Hom.stageMap (𝟙 A) p = 𝟙 (F^{p} A) := by
  -- Cancel the filtration inclusion to compare with the defining commutativity relation.
  exact (cancel_mono (A.filtration.obj p).arrow).1 (by
    simp [FilteredObject.Hom.stageMap_comm])

/-- Helper for Lemma 13.13.6: stage maps respect composition of filtered morphisms. -/
private theorem filtered_stage_map_comp {A B D : FilteredObject 𝒜} (f : A ⟶ B) (g : B ⟶ D)
    (p : ℤ) :
    FilteredObject.Hom.stageMap (f ≫ g) p =
      FilteredObject.Hom.stageMap f p ≫ FilteredObject.Hom.stageMap g p := by
  -- Compare both maps after composing with the target-stage inclusion.
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

/-- Helper for Lemma 13.13.6: stage maps of zero filtered morphisms are zero. -/
private theorem filtered_stage_map_zero (A B : FilteredObject 𝒜) (p : ℤ) :
    FilteredObject.Hom.stageMap (0 : A ⟶ B) p = 0 := by
  -- Cancel the target-stage inclusion and simplify the ambient zero morphism.
  exact (cancel_mono (B.filtration.obj p).arrow).1 (by
    rw [FilteredObject.Hom.stageMap_comm]
    simp)

/-- Helper for Lemma 13.13.6: stage maps of filtered morphisms preserve addition. -/
private theorem filtered_stage_map_add {A B : FilteredObject 𝒜} (f g : A ⟶ B) (p : ℤ) :
    FilteredObject.Hom.stageMap (f + g) p =
      FilteredObject.Hom.stageMap f p + FilteredObject.Hom.stageMap g p := by
  -- Again cancel the target-stage inclusion and use additivity in the ambient category.
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

/-- Helper for Lemma 13.13.6: induced maps on graded pieces preserve identities. -/
private theorem filtered_graded_piece_map_id (A : FilteredObject 𝒜) (p : ℤ) :
    filtered_graded_piece_map (𝟙 A) p = 𝟙 (gr^{p} A) := by
  -- Cancel the defining cokernel projection and use the stage-map identity formula.
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [filtered_graded_piece_map, filtered_stage_map_id])

/-- Helper for Lemma 13.13.6: induced maps on graded pieces respect composition. -/
private theorem filtered_graded_piece_map_comp {A B D : FilteredObject 𝒜} (f : A ⟶ B)
    (g : B ⟶ D) (p : ℤ) :
    filtered_graded_piece_map (f ≫ g) p =
      filtered_graded_piece_map f p ≫ filtered_graded_piece_map g p := by
  -- Cancel the same cokernel projection and invoke stage-map functoriality.
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [filtered_graded_piece_map, Category.assoc, filtered_stage_map_comp])

/-- Helper for Lemma 13.13.6: induced maps on graded pieces preserve zero morphisms. -/
private theorem filtered_graded_piece_map_zero (A B : FilteredObject 𝒜) (p : ℤ) :
    filtered_graded_piece_map (0 : A ⟶ B) p = 0 := by
  -- The zero comparison is detected after cancelling the source cokernel projection.
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [filtered_graded_piece_map, filtered_stage_map_zero])

/-- Helper for Lemma 13.13.6: induced maps on graded pieces preserve addition. -/
private theorem filtered_graded_piece_map_add {A B : FilteredObject 𝒜} (f g : A ⟶ B) (p : ℤ) :
    filtered_graded_piece_map (f + g) p =
      filtered_graded_piece_map f p + filtered_graded_piece_map g p := by
  -- Cancel the same cokernel projection and reduce to stage-map additivity.
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [filtered_graded_piece_map, filtered_stage_map_add, Category.assoc])

/-- Helper for Lemma 13.13.6: induced maps on associated graded objects preserve identities. -/
private theorem filtered_associated_graded_map_id (A : FilteredObject 𝒜) :
    filtered_associated_graded_map (𝟙 A) = 𝟙 A.associatedGraded := by
  -- Morphisms of graded objects are determined degreewise.
  ext p
  simpa [filtered_associated_graded_map] using filtered_graded_piece_map_id A p

/-- Helper for Lemma 13.13.6: induced maps on associated graded objects respect composition. -/
private theorem filtered_associated_graded_map_comp {A B D : FilteredObject 𝒜} (f : A ⟶ B)
    (g : B ⟶ D) :
    filtered_associated_graded_map (f ≫ g) =
      filtered_associated_graded_map f ≫ filtered_associated_graded_map g := by
  -- Reduce to the degreewise composition formula on graded pieces.
  ext p
  simpa [filtered_associated_graded_map] using filtered_graded_piece_map_comp f g p

/-- Helper for Lemma 13.13.6: induced maps on associated graded objects preserve zero
morphisms. -/
private theorem filtered_associated_graded_map_zero (A B : FilteredObject 𝒜) :
    filtered_associated_graded_map (0 : A ⟶ B) = 0 := by
  -- Again the statement is degreewise.
  ext p
  simpa [filtered_associated_graded_map] using filtered_graded_piece_map_zero A B p

/-- Helper for Lemma 13.13.6: induced maps on associated graded objects preserve addition. -/
private theorem filtered_associated_graded_map_add {A B : FilteredObject 𝒜} (f g : A ⟶ B) :
    filtered_associated_graded_map (f + g) =
      filtered_associated_graded_map f + filtered_associated_graded_map g := by
  -- Morphisms of graded objects are determined degreewise, so we reduce to the graded-piece case.
  ext p
  simpa [filtered_associated_graded_map] using filtered_graded_piece_map_add f g p

/-- Helper for Lemma 13.13.6: the associated graded functor on filtered objects. -/
private def filtered_associated_graded_functor : Fil(𝒜) ⥤ GradedObject ℤ 𝒜 where
  obj A := A.associatedGraded
  map f := filtered_associated_graded_map f
  map_id A := filtered_associated_graded_map_id A
  map_comp f g := filtered_associated_graded_map_comp f g

/-- Helper for Lemma 13.13.6: the associated graded functor on filtered objects is additive. -/
private instance filtered_associated_graded_functor_additive_13_13_6 :
    (filtered_associated_graded_functor (𝒜 := 𝒜)).Additive where
  map_add := by
    intro A B f g
    -- The additivity statement is exactly the associated-graded map-add lemma above.
    exact filtered_associated_graded_map_add f g

/-- Helper for Lemma 13.13.6: the associated graded functor on filtered objects preserves zero
morphisms. -/
private instance filtered_associated_graded_functor_preservesZeroMorphisms_13_13_6 :
    (filtered_associated_graded_functor (𝒜 := 𝒜)).PreservesZeroMorphisms where
  map_zero A B := filtered_associated_graded_map_zero A B

/-- Helper for Lemma 13.13.6: the forgetful functor on finite filtered objects. -/
abbrev finiteFilteredObjectForgetFunctor : FilF ⥤ 𝒜 :=
  ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))) ⋙
    FilteredObject.forget

/-- Helper for Lemma 13.13.6: the associated graded functor restricted to finite filtered
objects. -/
abbrev finiteFilteredObjectAssociatedGradedFunctor :
    FilF ⥤ GradedObject ℤ 𝒜 :=
  ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))) ⋙
    filtered_associated_graded_functor (𝒜 := 𝒜)

/-- Helper for Lemma 13.13.6: the homotopy-level associated graded functor on finite filtered
complexes. -/
abbrev filteredAssociatedGradedHomotopyFunctor :
    KFilt ⥤ HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ) :=
  (finiteFilteredObjectAssociatedGradedFunctor (𝒜 := 𝒜)).mapHomotopyCategory (up ℤ)

/-- Helper for Lemma 13.13.6: the restricted associated graded functor remains additive on the
finite filtered subcategory. -/
local instance finiteFilteredObjectAssociatedGradedFunctor_additive_13_13_6 :
    (finiteFilteredObjectAssociatedGradedFunctor (𝒜 := 𝒜)).Additive := by
  dsimp [finiteFilteredObjectAssociatedGradedFunctor]
  infer_instance

/-- Helper for Lemma 13.13.6: evaluation of a graded object is additive in each degree. -/
local instance gradedObject_eval_additive_13_13_6 (p : ℤ) :
    (GradedObject.eval p : GradedObject ℤ 𝒜 ⥤ 𝒜).Additive := by
  infer_instance

/-- Helper for Lemma 13.13.6: derived evaluation needs finite-limit preservation to descend from
graded objects to the derived category. -/
local instance gradedObject_eval_preservesFiniteLimits_13_13_6 (p : ℤ) :
    PreservesFiniteLimits (GradedObject.eval p : GradedObject ℤ 𝒜 ⥤ 𝒜) := by
  infer_instance

/-- Helper for Lemma 13.13.6: evaluating a graded complex in one degree preserves acyclicity. -/
private theorem gradedObject_eval_mapHomologicalComplex_acyclic (p : ℤ)
    {L : CochainComplex (GradedObject ℤ 𝒜) ℤ} (hL : L.Acyclic) :
    (((GradedObject.eval p).mapHomologicalComplex (up ℤ)).obj L).Acyclic := by
  -- Read acyclicity degreewise as exactness of the short complexes and evaluate each degree.
  rw [HomologicalComplex.acyclic_iff] at hL ⊢
  intro n
  simpa using (ShortComplex.graded_shortComplex_exact_iff_exact_app (S := L.sc n)).1 (hL n) p

/-- Helper for Lemma 13.13.6: if the associated graded of a finite filtered complex is acyclic,
then the underlying unfiltered complex is acyclic. -/
private theorem finiteFilteredObject_forget_acyclic_of_associatedGraded_acyclic
    {L : CochainComplex FilF ℤ}
    (hL :
      (((finiteFilteredObjectAssociatedGradedFunctor : FilF ⥤ GradedObject ℤ 𝒜)
          .mapHomologicalComplex (up ℤ)).obj L).Acyclic) :
    (((finiteFilteredObjectForgetFunctor : FilF ⥤ 𝒜).mapHomologicalComplex (up ℤ)).obj L).Acyclic :=
    by
  -- Apply the Chapter 12 exactness bridge degreewise to the short complexes of `L`.
  rw [HomologicalComplex.acyclic_iff] at hL ⊢
  intro n
  let S : ShortComplex (FilteredObject 𝒜) :=
    (L.sc n).map (ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))))
  have hS₁fin : S.X₁.IsFinite := (L.X n).property
  have hS₂fin : S.X₂.IsFinite := (L.X (n + 1)).property
  have hS₃fin : S.X₃.IsFinite := (L.X (n + 2)).property
  have hgr :
      ShortComplex.Exact (S.map FilteredObject.associatedGradedFunctor) := by
    -- The associated-graded short complex of `S` is the degree-`n` short complex of `gr(L)`.
    simpa [S, finiteFilteredObjectAssociatedGradedFunctor, filtered_associated_graded_functor] using
      hL n
  -- Forgetting the filtration is exactly the degree-`n` short complex of the forgotten complex.
  simpa [S, finiteFilteredObjectForgetFunctor] using
    ShortComplex.underlying_exact_of_associatedGraded_exact
      (S := S) hS₁fin hS₂fin hS₃fin hgr

/-- Helper for Lemma 13.13.6: the imported filtered quasi-isomorphism predicate is equivalent to
asking that the local associated-graded homotopy functor send a morphism to a quasi-isomorphism. -/
theorem filteredQuasiIso_iff {K L : KFilt} (α : K ⟶ L) :
    (FQis(𝒜) : MorphismProperty KFilt) α ↔
      HomotopyCategory.quasiIso (GradedObject ℤ 𝒜) (up ℤ)
        ((filteredAssociatedGradedHomotopyFunctor (𝒜 := 𝒜)).map α) := by
  constructor
  · intro hα
    -- Unfold both owner layers down to the homotopy map induced by the same associated-graded
    -- functor on finite filtered objects.
    simpa [filteredAssociatedGradedHomotopyFunctor, finiteFilteredObjectAssociatedGradedFunctor,
      filtered_associated_graded_functor] using hα
  · intro hα
    -- The converse is the same definitional comparison in the opposite direction.
    simpa [filteredAssociatedGradedHomotopyFunctor, finiteFilteredObjectAssociatedGradedFunctor,
      filtered_associated_graded_functor] using hα

/-- Helper for Lemma 13.13.6: the imported filtered acyclic predicate is equivalent to asking
that the local associated-graded homotopy functor land in the acyclic subcategory. -/
theorem filteredAcyclic_iff (K : KFilt) :
    (FAc(𝒜) : ObjectProperty KFilt) K ↔
      HomotopyCategory.subcategoryAcyclic (GradedObject ℤ 𝒜)
        ((filteredAssociatedGradedHomotopyFunctor (𝒜 := 𝒜)).obj K) := by
  constructor
  · intro hK
    -- As above, compare the imported owner layer with the local associated-graded homotopy functor.
    simpa [filteredAssociatedGradedHomotopyFunctor, finiteFilteredObjectAssociatedGradedFunctor,
      filtered_associated_graded_functor] using hK
  · intro hK
    -- The reverse direction uses the same definitional unfolding.
    simpa [filteredAssociatedGradedHomotopyFunctor, finiteFilteredObjectAssociatedGradedFunctor,
      filtered_associated_graded_functor] using hK

/-- Route correction: the direct import of `Definition_13_13_2` is currently broken in this
workspace, so this file stabilizes its proof frontier by rebuilding only the thin associated-
graded and forgetful owner layer it actually consumes. The localization argument itself remains
source-faithful and continues to use the Chapter 13 `FQis(𝒜)`/`FAc(𝒜)` owners from
`Definition_13_13_5`. -/

private abbrev QFilt : KFilt ⥤ DFilt :=
  (((FAc(𝒜) : ObjectProperty KFilt).trW).Q : KFilt ⥤ DFilt)

instance qFilt_isLocalization :
    Functor.IsLocalization QFilt (FQis(𝒜) : MorphismProperty KFilt) := by
  rw [← filteredAcyclic_trW_eq_filteredQuasiIso]
  simpa [QFilt] using
    (Functor.q_isLocalization ((FAc(𝒜) : ObjectProperty KFilt).trW) :
      Functor.IsLocalization
        (((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DFilt))
        ((FAc(𝒜) : ObjectProperty KFilt).trW))

private noncomputable instance filteredDerived_shift_additive
    [IsTriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))] (n : ℤ) :
    (shiftFunctor DFilt n).Additive := by
  infer_instance

section AssociatedGraded

variable [HasDerivedCategory (GradedObject ℤ 𝒜)]

/-- The associated graded functor from `K(Fil^f(\mathcal A))` to `D(Gr(\mathcal A))`. -/
abbrev filteredAssociatedGradedHomotopyToDerivedFunctor :
    KFilt ⥤ DGr :=
  filteredAssociatedGradedHomotopyFunctor ⋙
    (DerivedCategory.Qh : HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ) ⥤ DGr)

section DerivedGradedObject

variable [HasDerivedCategory 𝒜]

private noncomputable abbrev gradedObjectEvalMapDerivedCategory (p : ℤ) :
    DGr ⥤ DerivedCategory 𝒜 :=
  (GradedObject.eval p).mapDerivedCategory

/-- The bridge/view functor `D(Gr(\mathcal A)) ⥤ Gr(D(\mathcal A))` obtained by derived
evaluation in each degree. -/
abbrev gradedDerivedObjectFunctor :
    DGr ⥤ GradedObject ℤ (DerivedCategory 𝒜) where
  obj K := fun p ↦ (gradedObjectEvalMapDerivedCategory p).obj K
  map f := fun p ↦ (gradedObjectEvalMapDerivedCategory p).map f
  map_id X := by
    ext p
    simp
  map_comp f g := by
    ext p
    simp

section DerivedPiece

/-- The `p`-th graded piece functor from `K(Fil^f(\mathcal A))` to `D(\mathcal A)`. -/
abbrev filteredGradedPieceHomotopyToDerivedFunctor (p : ℤ) :
    KFilt ⥤ DerivedCategory 𝒜 :=
  filteredAssociatedGradedHomotopyFunctor ⋙
    (GradedObject.eval p).mapHomotopyCategory (up ℤ) ⋙
    DerivedCategory.Qh

/-- Helper for Lemma 13.13.6: derived evaluation of the descended associated graded functor
recovers the direct homotopy-level graded-piece functor. -/
noncomputable abbrev filteredGradedPieceHomotopyToDerivedFunctorCompIso (p : ℤ) :
      filteredAssociatedGradedHomotopyToDerivedFunctor (𝒜 := 𝒜) ⋙
          gradedObjectEvalMapDerivedCategory (𝒜 := 𝒜) p ≅
        filteredGradedPieceHomotopyToDerivedFunctor (𝒜 := 𝒜) p :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (GradedObject.eval p).mapDerivedCategoryFactorsh ≪≫
    (Functor.associator _ _ _).symm

end DerivedPiece

end DerivedGradedObject

end AssociatedGraded

section Forget

variable [HasDerivedCategory 𝒜]

/-- The forgetful functor from `K(Fil^f(\mathcal A))` to `D(\mathcal A)`. -/
abbrev filteredForgetHomotopyToDerivedFunctor :
    KFilt ⥤ DerivedCategory 𝒜 :=
  (finiteFilteredObjectForgetFunctor : FilF ⥤ 𝒜).mapHomotopyCategory (up ℤ) ⋙
    DerivedCategory.Qh

end Forget

section AssociatedGraded

variable [HasDerivedCategory (GradedObject ℤ 𝒜)]
variable [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

-- Proof sketch: a filtered quasi-isomorphism is, by definition, a quasi-isomorphism after
-- applying the associated graded functor, and `DerivedCategory.Qh` inverts quasi-isomorphisms.
/-- The associated graded functor to the derived category inverts filtered quasi-isomorphisms. -/
theorem filteredAssociatedGradedHomotopyToDerivedFunctor_inverts_filteredQuasiIsomorphisms :
    (FQis(𝒜) : MorphismProperty KFilt).IsInvertedBy
      (filteredAssociatedGradedHomotopyToDerivedFunctor : KFilt ⥤ DGr) := by
  intro X Y f hf
  -- Unpack the definition of filtered quasi-isomorphism into the associated-graded statement.
  rw [filteredQuasiIso_iff] at hf
  -- The localization functor `Qh` inverts quasi-isomorphisms on the graded target homotopy
  -- category, which is exactly the current mapped morphism.
  simpa [filteredAssociatedGradedHomotopyToDerivedFunctor] using
    (Localization.inverts
      (DerivedCategory.Qh :
        HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ) ⥤ DGr)
      (HomotopyCategory.quasiIso (GradedObject ℤ 𝒜) (up ℤ))
      (filteredAssociatedGradedHomotopyFunctor.map f) hf)

end AssociatedGraded

section GradedPiece

variable [HasDerivedCategory 𝒜]
variable [HasDerivedCategory (GradedObject ℤ 𝒜)]
variable [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

/-- Helper for Lemma 13.13.6: evaluation at a fixed degree sends acyclic graded homotopy objects
to acyclic ordinary homotopy objects. -/
lemma gradedObject_eval_mapHomotopyCategory_mem_subcategoryAcyclic
    (p : ℤ) (K : HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ))
    (hK : HomotopyCategory.subcategoryAcyclic (GradedObject ℤ 𝒜) K) :
    HomotopyCategory.subcategoryAcyclic 𝒜
      (((GradedObject.eval p).mapHomotopyCategory (up ℤ)).obj K) := by
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  -- Replace the homotopy-category acyclicity claim by acyclicity of a representing complex.
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK ⊢
  -- Evaluate the representative complex degreewise and use the Chapter 12 exactness criterion.
  simpa using gradedObject_eval_mapHomologicalComplex_acyclic (𝒜 := 𝒜) p hK

-- Proof sketch: a filtered quasi-isomorphism becomes a quasi-isomorphism after taking associated
-- graded objects, evaluation at `p` preserves quasi-isomorphisms degreewise, and `Qh` localizes
-- at quasi-isomorphisms.
/-- The `p`-th graded piece functor to the derived category inverts filtered quasi-isomorphisms. -/
theorem filteredGradedPieceHomotopyToDerivedFunctor_inverts_filteredQuasiIsomorphisms (p : ℤ) :
    (FQis(𝒜) : MorphismProperty KFilt).IsInvertedBy
      (filteredGradedPieceHomotopyToDerivedFunctor p : KFilt ⥤ DerivedCategory 𝒜) := by
  intro X Y f hf
  rw [filteredQuasiIso_iff] at hf
  have hConeGr :
      HomotopyCategory.subcategoryAcyclic (GradedObject ℤ 𝒜)
        (HomotopyCategory.mappingCone
          ((filteredAssociatedGradedHomotopyFunctor (𝒜 := 𝒜)).map f)) := by
    -- The standard mapping-cone triangle for the associated-graded morphism realizes the `trW`
    -- witness coming from `hf`.
    rw [← HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W] at hf
    exact
      ((HomotopyCategory.subcategoryAcyclic (GradedObject ℤ 𝒜)).trW_iff_of_distinguished
        (HomotopyCategory.mappingCone.triangleh
          ((filteredAssociatedGradedHomotopyFunctor (𝒜 := 𝒜)).map f))
        (HomotopyCategory.mappingCone_triangleh_distinguished
          ((filteredAssociatedGradedHomotopyFunctor (𝒜 := 𝒜)).map f))).1 hf
  have hConeEval :
      HomotopyCategory.subcategoryAcyclic 𝒜
        ((((GradedObject.eval p).mapHomotopyCategory (up ℤ)).mapTriangle.obj
            (HomotopyCategory.mappingCone.triangleh
              ((filteredAssociatedGradedHomotopyFunctor (𝒜 := 𝒜)).map f))).obj₃) := by
    -- Evaluation preserves acyclic cone terms objectwise.
    simpa using
      gradedObject_eval_mapHomotopyCategory_mem_subcategoryAcyclic
        (𝒜 := 𝒜) p
        (HomotopyCategory.mappingCone
          ((filteredAssociatedGradedHomotopyFunctor (𝒜 := 𝒜)).map f))
        hConeGr
  have hEvalQuasiIso :
      HomotopyCategory.quasiIso 𝒜 (up ℤ)
        (((filteredAssociatedGradedHomotopyFunctor (𝒜 := 𝒜) ⋙
            (GradedObject.eval p).mapHomotopyCategory (up ℤ)).map f)) := by
    rw [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]
    -- Read off the acyclic cone in the mapped distinguished triangle.
    exact
      ((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished
        (((GradedObject.eval p).mapHomotopyCategory (up ℤ)).mapTriangle.obj
          (HomotopyCategory.mappingCone.triangleh
            ((filteredAssociatedGradedHomotopyFunctor (𝒜 := 𝒜)).map f)))
        (((GradedObject.eval p).mapHomotopyCategory (up ℤ)).map_distinguished _ <|
          HomotopyCategory.mappingCone_triangleh_distinguished
            ((filteredAssociatedGradedHomotopyFunctor (𝒜 := 𝒜)).map f))).2 hConeEval
  -- Finally `DerivedCategory.Qh` inverts quasi-isomorphisms on the ordinary homotopy category.
  simpa [filteredGradedPieceHomotopyToDerivedFunctor, Functor.assoc] using
    (Localization.inverts
      (DerivedCategory.Qh : HomotopyCategory 𝒜 (up ℤ) ⥤ DerivedCategory 𝒜)
      (HomotopyCategory.quasiIso 𝒜 (up ℤ))
      (((filteredAssociatedGradedHomotopyFunctor (𝒜 := 𝒜) ⋙
          (GradedObject.eval p).mapHomotopyCategory (up ℤ)).map f))
      hEvalQuasiIso)

/-- Lemma 13.13.6: the `p`-th graded-piece functor on `K(Fil^f(\mathcal A))` descends directly
to the canonical exact functor `DF(\mathcal A) ⥤ D(\mathcal A)` induced by `gr^p`. -/
abbrev filteredDerivedGradedPieceFunctor (p : ℤ) :
    DFilt ⥤ DerivedCategory 𝒜 :=
  Localization.lift
    (filteredGradedPieceHomotopyToDerivedFunctor p)
    (filteredGradedPieceHomotopyToDerivedFunctor_inverts_filteredQuasiIsomorphisms p)
    QFilt

/-- Textbook surface notation for the descended graded-piece functor `DF(\mathcal A) ⥤
D(\mathcal A)`. -/
scoped notation:max "gr^{" p "}" => filteredDerivedGradedPieceFunctor p

/-- The descended `p`-th graded piece functor commutes with shifts. -/
noncomputable instance filteredDerivedGradedPieceFunctor_commShift (p : ℤ) :
    (gr^{p} : DFilt ⥤ DerivedCategory 𝒜).CommShift ℤ := by
  infer_instance

section Exact

variable [IsTriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

-- Proof sketch: the source-facing `gr^p` on `DF(\mathcal A)` is itself a localization lift of the
-- homotopy-level `gr^p`, so Lemma 13.5.7 applies directly. The bridge
-- `DF(\mathcal A) ⥤ Gr(D(\mathcal A))` is only a companion comparison.
/-- The descended `p`-th graded piece functor is exact. -/
instance filteredDerivedGradedPieceFunctor_isTriangulated (p : ℤ) :
    (gr^{p} : DFilt ⥤ DerivedCategory 𝒜).IsTriangulated := by
  letI : (gr^{p} : DFilt ⥤ DerivedCategory 𝒜).CommShift ℤ := inferInstance
  letI :
      Functor.EssSurj ((QFilt : KFilt ⥤ DFilt).mapArrow) :=
    Localization.essSurj_mapArrow
      (QFilt : KFilt ⥤ DFilt) (FQis(𝒜) : MorphismProperty KFilt)
  -- Exactness of the localization lift is the generic precomposition criterion.
  exact
    Functor.isTriangulated_of_precomp_iso
      (Localization.Lifting.iso
        (QFilt : KFilt ⥤ DFilt)
        (FQis(𝒜) : MorphismProperty KFilt)
        (filteredGradedPieceHomotopyToDerivedFunctor (𝒜 := 𝒜) p)
        (gr^{p} : DFilt ⥤ DerivedCategory 𝒜))

end Exact

end GradedPiece

section Forget

variable [HasDerivedCategory 𝒜]
variable [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

/-- Helper for Lemma 13.13.6: a filtered-acyclic object becomes acyclic after forgetting the
filtration. -/
lemma filteredAcyclic_forget_mem_subcategoryAcyclic
    (K : KFilt) (hK : (FAc(𝒜) : ObjectProperty KFilt) K) :
    HomotopyCategory.subcategoryAcyclic 𝒜
      (((finiteFilteredObjectForgetFunctor : FilF ⥤ 𝒜).mapHomotopyCategory (up ℤ)).obj K) := by
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [filteredAcyclic_iff] at hK
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK ⊢
  -- Translate filtered acyclicity of the representative to acyclicity of its forgotten complex.
  simpa [filteredAssociatedGradedHomotopyFunctor] using
    finiteFilteredObject_forget_acyclic_of_associatedGraded_acyclic (𝒜 := 𝒜) hK

-- Proof sketch: if a morphism is a filtered quasi-isomorphism, then its cone is filtered acyclic.
-- Lemma 13.13.4 identifies this with the filtered acyclic subcategory, and the forgetful functor
-- sends filtered acyclic complexes to acyclic complexes, so `DerivedCategory.Qh` inverts it.
/-- The forgetful functor to the derived category inverts filtered quasi-isomorphisms. -/
theorem filteredForgetHomotopyToDerivedFunctor_inverts_filteredQuasiIsomorphisms :
    (FQis(𝒜) : MorphismProperty KFilt).IsInvertedBy
      (filteredForgetHomotopyToDerivedFunctor : KFilt ⥤ DerivedCategory 𝒜) := by
  intro X Y f hf
  rw [← filteredAcyclic_trW_eq_filteredQuasiIso] at hf
  have hConeFilt :
      (FAc(𝒜) : ObjectProperty KFilt) (HomotopyCategory.mappingCone f) := by
    -- The mapping cone realizes the `trW` witness for `f` in the filtered acyclic subcategory.
    exact
      ((FAc(𝒜) : ObjectProperty KFilt).trW_iff_of_distinguished
        (HomotopyCategory.mappingCone.triangleh f)
        (HomotopyCategory.mappingCone_triangleh_distinguished f)).1 hf
  have hConeForget :
      HomotopyCategory.subcategoryAcyclic 𝒜
        ((((finiteFilteredObjectForgetFunctor : FilF ⥤ 𝒜).mapHomotopyCategory (up ℤ))
            .mapTriangle.obj (HomotopyCategory.mappingCone.triangleh f)).obj₃) := by
    -- Forgetting the filtration preserves acyclicity of the cone term.
    simpa using filteredAcyclic_forget_mem_subcategoryAcyclic (𝒜 := 𝒜)
      (HomotopyCategory.mappingCone f) hConeFilt
  have hForgetQuasiIso :
      HomotopyCategory.quasiIso 𝒜 (up ℤ)
        (((finiteFilteredObjectForgetFunctor : FilF ⥤ 𝒜).mapHomotopyCategory (up ℤ)).map f) := by
    rw [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]
    -- The mapped standard triangle has acyclic third term, hence its first morphism is a
    -- quasi-isomorphism.
    exact
      ((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished
        (((finiteFilteredObjectForgetFunctor : FilF ⥤ 𝒜).mapHomotopyCategory (up ℤ))
          .mapTriangle.obj (HomotopyCategory.mappingCone.triangleh f))
        (((finiteFilteredObjectForgetFunctor : FilF ⥤ 𝒜).mapHomotopyCategory (up ℤ))
          .map_distinguished _ (HomotopyCategory.mappingCone_triangleh_distinguished f))).2
        hConeForget
  -- `DerivedCategory.Qh` now inverts the resulting ordinary quasi-isomorphism.
  simpa [filteredForgetHomotopyToDerivedFunctor, Functor.assoc] using
    (Localization.inverts
      (DerivedCategory.Qh : HomotopyCategory 𝒜 (up ℤ) ⥤ DerivedCategory 𝒜)
      (HomotopyCategory.quasiIso 𝒜 (up ℤ))
      (((finiteFilteredObjectForgetFunctor : FilF ⥤ 𝒜).mapHomotopyCategory (up ℤ)).map f)
      hForgetQuasiIso)

end Forget

section AssociatedGraded

variable [HasDerivedCategory (GradedObject ℤ 𝒜)]
variable [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

/-- Lemma 13.13.6: the associated graded functor on `K(Fil^f(\mathcal A))` descends to a
canonical exact functor `DF(\mathcal A) ⥤ D(Gr(\mathcal A))` commuting with the localization
functor. -/
abbrev filteredDerivedAssociatedGradedFunctor :
    DFilt ⥤ DGr :=
  Localization.lift
    filteredAssociatedGradedHomotopyToDerivedFunctor
    filteredAssociatedGradedHomotopyToDerivedFunctor_inverts_filteredQuasiIsomorphisms
    QFilt

/-- Textbook surface notation for the descended associated-graded functor
`DF(\mathcal A) ⥤ D(Gr(\mathcal A))`. -/
scoped notation "gr" => filteredDerivedAssociatedGradedFunctor

/-- The descended associated graded functor commutes with shifts. -/
noncomputable instance filteredDerivedAssociatedGradedFunctor_commShift :
    (gr : DFilt ⥤ DGr).CommShift ℤ := by
  infer_instance

section Exact

variable [IsTriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

-- Proof sketch: the functor on the homotopy category obtained from the associated graded functor
-- is exact, and Lemma 13.5.7 upgrades exactness to the localization lift.
/-- The descended associated graded functor is exact. -/
theorem filteredDerivedAssociatedGradedFunctor_isTriangulated :
    (gr : DFilt ⥤ DGr).IsTriangulated := by
  letI : (gr : DFilt ⥤ DGr).CommShift ℤ := inferInstance
  letI :
      Functor.EssSurj ((QFilt : KFilt ⥤ DFilt).mapArrow) :=
    Localization.essSurj_mapArrow
      (QFilt : KFilt ⥤ DFilt) (FQis(𝒜) : MorphismProperty KFilt)
  -- Apply the generic exactness criterion to the localization lift of `gr`.
  exact
    Functor.isTriangulated_of_precomp_iso
      (Localization.Lifting.iso
        (QFilt : KFilt ⥤ DFilt)
        (FQis(𝒜) : MorphismProperty KFilt)
        (filteredAssociatedGradedHomotopyToDerivedFunctor (𝒜 := 𝒜))
        (gr : DFilt ⥤ DGr))

/-- The canonical exactness instance for the descended associated graded functor. -/
instance :
    (gr : DFilt ⥤ DGr).IsTriangulated :=
  filteredDerivedAssociatedGradedFunctor_isTriangulated

end Exact

end AssociatedGraded

section GradedDerivedObject

variable [HasDerivedCategory 𝒜]
variable [HasDerivedCategory (GradedObject ℤ 𝒜)]
variable [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

/-- Companion bridge/view for Lemma 13.13.6: package the descended associated graded functor as a
graded object in `D(\mathcal A)`. Its degree-`p` evaluation is compared to the source-facing
functor `gr^{p}` by `filteredDerivedGradedFunctorEvalIso`. -/
abbrev filteredDerivedGradedFunctor :
    DFilt ⥤ GradedObject ℤ (DerivedCategory 𝒜) :=
  gr ⋙ gradedDerivedObjectFunctor

section GradedPiece

/-- Evaluating the graded-object bridge in degree `p` recovers the source-facing descended
graded-piece functor `gr^p`. -/
noncomputable abbrev filteredDerivedGradedFunctorEvalIso (p : ℤ) :
    filteredDerivedGradedFunctor ⋙
        (GradedObject.eval p : GradedObject ℤ (DerivedCategory 𝒜) ⥤ DerivedCategory 𝒜) ≅
      gr^{p} := by
  change (gr : DFilt ⥤ DGr) ⋙ gradedObjectEvalMapDerivedCategory (𝒜 := 𝒜) p ≅ gr^{p}
  -- Lift the canonical homotopy-level comparison through the localization functor `QFilt`.
  exact
    Localization.liftNatIso
      (QFilt : KFilt ⥤ DFilt)
      (FQis(𝒜) : MorphismProperty KFilt)
      (filteredAssociatedGradedHomotopyToDerivedFunctor (𝒜 := 𝒜) ⋙
        gradedObjectEvalMapDerivedCategory (𝒜 := 𝒜) p)
      (filteredGradedPieceHomotopyToDerivedFunctor (𝒜 := 𝒜) p)
      ((gr : DFilt ⥤ DGr) ⋙ gradedObjectEvalMapDerivedCategory (𝒜 := 𝒜) p)
      (gr^{p} : DFilt ⥤ DerivedCategory 𝒜)
      (filteredGradedPieceHomotopyToDerivedFunctorCompIso (𝒜 := 𝒜) p)

end GradedPiece

end GradedDerivedObject

section Forget

variable [HasDerivedCategory 𝒜]
variable [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

/-- The forgetful functor on `DF(\mathcal A)`. -/
abbrev filteredDerivedForgetFunctor :
    DFilt ⥤ DerivedCategory 𝒜 :=
  Localization.lift
    filteredForgetHomotopyToDerivedFunctor
    filteredForgetHomotopyToDerivedFunctor_inverts_filteredQuasiIsomorphisms
    QFilt

/-- The descended forgetful functor commutes with shifts. -/
noncomputable instance filteredDerivedForgetFunctor_commShift :
    (filteredDerivedForgetFunctor : DFilt ⥤ DerivedCategory 𝒜).CommShift ℤ := by
  infer_instance

section Exact

variable [IsTriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

-- Proof sketch: the forgetful functor on filtered complexes is exact on the homotopy category,
-- and once it is known to invert filtered quasi-isomorphisms, Lemma 13.5.7 gives exactness of
-- the descended localization lift.
/-- The descended forgetful functor is exact. -/
instance filteredDerivedForgetFunctor_isTriangulated :
    (filteredDerivedForgetFunctor : DFilt ⥤ DerivedCategory 𝒜).IsTriangulated := by
  letI : (filteredDerivedForgetFunctor : DFilt ⥤ DerivedCategory 𝒜).CommShift ℤ :=
    inferInstance
  letI :
      Functor.EssSurj ((QFilt : KFilt ⥤ DFilt).mapArrow) :=
    Localization.essSurj_mapArrow
      (QFilt : KFilt ⥤ DFilt) (FQis(𝒜) : MorphismProperty KFilt)
  -- The forgetful functor is again a localization lift of an exact homotopy-level functor.
  exact
    Functor.isTriangulated_of_precomp_iso
      (Localization.Lifting.iso
        (QFilt : KFilt ⥤ DFilt)
        (FQis(𝒜) : MorphismProperty KFilt)
        (filteredForgetHomotopyToDerivedFunctor (𝒜 := 𝒜))
        (filteredDerivedForgetFunctor (𝒜 := 𝒜)))

end Exact

end Forget

end CategoryTheory
