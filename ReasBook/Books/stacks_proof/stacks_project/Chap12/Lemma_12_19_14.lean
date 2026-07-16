import stacks_proof.stacks_project.Chap12.Aux_12_20_2_1
import stacks_proof.stacks_project.Chap12.Definition_12_19_3
import Mathlib.Tactic.StacksAttribute

open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜]

namespace FilteredObject

variable (A : FilteredObject 𝒜)

section Abelian

variable [Abelian 𝒜]

/-- Helper for Lemma 12.19.14: the induced filtered object on a subobject `X ⊆ A`. -/
def subobjectFilteredObject (X : Subobject A.obj) : FilteredObject 𝒜 where
  obj := X
  filtration := A.filtration.induced X

/-- Helper for Lemma 12.19.14: the quotient filtered object `A / X`. -/
def quotientFilteredObject (X : Subobject A.obj) : FilteredObject 𝒜 where
  obj := cokernel X.arrow
  filtration := A.filtration.quotient (cokernel.π X.arrow)

/-- Helper for Lemma 12.19.14: the canonical filtered object on the subquotient `Y / X`, viewed
as a subobject of `A / X` with the induced filtration. -/
abbrev subobjectSubquotientFilteredObject {X Y : Subobject A.obj} (hXY : X ≤ Y) :
    FilteredObject 𝒜 :=
  (A.quotientFilteredObject X).subobjectFilteredObject (subobjectSubquotientSubobject hXY)

end Abelian

end FilteredObject

namespace FilteredObject.Hom

open FilteredObject

variable {A B C : FilteredObject 𝒜}

/-- Helper for Lemma 12.19.14: the stage map of a composite is the composite of the stage maps. -/
private theorem stageMap_comp
    {X Y Z : FilteredObject 𝒜} (f : X ⟶ Y) (g : Y ⟶ Z) (p : ℤ) :
    stageMap (f ≫ g) p = stageMap f p ≫ stageMap g p := by
  exact (cancel_mono (Z.filtration.obj p).arrow).1 (by
    calc
      stageMap (f ≫ g) p ≫ (Z.filtration.obj p).arrow
          = (X.filtration.obj p).arrow ≫ (f ≫ g).hom := by
              rw [stageMap_comm]
      _ = ((X.filtration.obj p).arrow ≫ f.hom) ≫ g.hom := by
            simp [Category.assoc]
      _ = (stageMap f p ≫ (Y.filtration.obj p).arrow) ≫ g.hom := by
            rw [stageMap_comm]
      _ = stageMap f p ≫ (stageMap g p ≫ (Z.filtration.obj p).arrow) := by
            rw [stageMap_comm]
            simp [Category.assoc]
      _ = (stageMap f p ≫ stageMap g p) ≫ (Z.filtration.obj p).arrow := by
            simp [Category.assoc])

section Abelian

variable [Abelian 𝒜]

/-- Helper for Lemma 12.19.14: the zero filtered morphism induces the zero stage map. -/
private theorem stageMap_zero (X Y : FilteredObject 𝒜) (p : ℤ) :
    stageMap (0 : X ⟶ Y) p = 0 := by
  exact (cancel_mono (Y.filtration.obj p).arrow).1 (by
    rw [stageMap_comm]
    simp)

/-- Helper for Lemma 12.19.14: the map induced on the `p`-th graded piece by a filtered
morphism. -/
noncomputable abbrev gradedPieceMap {X Y : FilteredObject 𝒜} (f : X ⟶ Y) (p : ℤ) :
    gr^{p} X ⟶ gr^{p} Y :=
  cokernel.map (X.filtration.stageInclusion p) (Y.filtration.stageInclusion p)
    (stageMap f (p + 1)) (stageMap f p)
    (stageInclusion_naturality f p)

/-- Helper for Lemma 12.19.14: the induced map on graded pieces preserves composition. -/
private theorem gradedPieceMap_comp
    {X Y Z : FilteredObject 𝒜} (f : X ⟶ Y) (g : Y ⟶ Z) (p : ℤ) :
    gradedPieceMap (f ≫ g) p = gradedPieceMap f p ≫ gradedPieceMap g p := by
  exact (cancel_epi (cokernel.π (X.filtration.stageInclusion p))).1 (by
    simp [gradedPieceMap, Category.assoc, stageMap_comp])

/-- Helper for Lemma 12.19.14: the zero filtered morphism induces the zero map on graded pieces.
-/
private theorem gradedPieceMap_zero (X Y : FilteredObject 𝒜) (p : ℤ) :
    gradedPieceMap (0 : X ⟶ Y) p = 0 := by
  exact (cancel_epi (cokernel.π (X.filtration.stageInclusion p))).1 (by
    simp [gradedPieceMap, stageMap_zero])

/-- Helper for Lemma 12.19.14: a zero composite of filtered morphisms stays zero on graded
pieces. -/
theorem gradedPieceMap_comp_zero
    {X Y Z : FilteredObject 𝒜} (f : X ⟶ Y) (g : Y ⟶ Z) (hcomp : f ≫ g = 0) (p : ℤ) :
    gradedPieceMap f p ≫ gradedPieceMap g p = 0 := by
  rw [← gradedPieceMap_comp f g p, hcomp, gradedPieceMap_zero]

/-- Lemma 12.19.14: for a complex `A ⟶ B ⟶ C` of filtered objects in an abelian category with
strict maps `α` and `β`, the associated graded of `ker β / im α` is canonically isomorphic to the
homology of the graded complex `gr A ⟶ gr B ⟶ gr C`. -/
@[stacks 0128]
noncomputable def graded_homology_iso_graded_complex_homology
    (α : A ⟶ B) (β : B ⟶ C) (hcomp : α ≫ β = 0)
    (hα : Strict α) (hβ : Strict β) (p : ℤ) :
    let hcomp_hom : α.hom ≫ β.hom = 0 := congrArg FilteredObject.Hom.hom hcomp
    (B.subobjectSubquotientFilteredObject (image_le_kernel α.hom β.hom hcomp_hom)).gradedPiece p ≅
      (ShortComplex.mk (gradedPieceMap α p) (gradedPieceMap β p)
        (gradedPieceMap_comp_zero α β hcomp p)).homology := by
  admit

end Abelian

end FilteredObject.Hom

end CategoryTheory
