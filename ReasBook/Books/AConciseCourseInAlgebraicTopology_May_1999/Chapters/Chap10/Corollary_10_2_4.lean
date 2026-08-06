import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.CellularPushout
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_2_4

open CategoryTheory CategoryTheory.Limits
open Topology

noncomputable section

universe u

section

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

-- Semantic recall via `lean_leansearch`: no source-exact pushout-quotient identification surfaced
-- in the current environment. The repository already fixes the adjunction-space owner
-- `cellularPushout A f` and the quotient model `collapseSubsetType`, so this corollary is kept
-- source-facing as the statement that the canonical comparison map `X / A ⟶ (Y ∪_f X) / Y` is a
-- homeomorphism.

/-- The quotient model `(Y ∪_f X) / Y` obtained by collapsing the copy of `Y` inside the
adjunction space `cellularPushout A f`. -/
abbrev cellularPushoutCollapseLeft (A : Set X) (f : C(A, Y)) :=
  collapseSubsetType (cellularPushout A f) (cellularPushoutLeftRange A f)

private theorem cellularPushoutCollapseComparison_respects
    (A : Set X) (f : C(A, Y)) {x y : X} (hxy : collapseSubsetSetoid A x y) :
    collapseSubsetSetoid (cellularPushoutLeftRange A f)
      ((pushout.inr (TopCat.ofHom f) (TopCat.subtypeInclusion A)).hom x)
      ((pushout.inr (TopCat.ofHom f) (TopCat.subtypeInclusion A)).hom y) := by
  induction hxy with
  | rel _ _ hxy =>
      rcases hxy with rfl | ⟨hx, hy⟩
      · exact Relation.EqvGen.refl _
      · exact Relation.EqvGen.rel _ _ <| Or.inr ⟨
          cellularPushout_inr_mem_leftRange_of_mem A f hx,
          cellularPushout_inr_mem_leftRange_of_mem A f hy⟩
  | refl _ =>
      exact Relation.EqvGen.refl _
  | symm _ _ _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihxy hyz =>
      exact Relation.EqvGen.trans _ _ _ ihxy hyz

/-- The quotient map `X / A ⟶ (Y ∪_f X) / Y` induced by the right pushout leg
`X ⟶ Y ∪_f X`. -/
def cellularPushoutCollapseComparison (A : Set X) (f : C(A, Y)) :
    C(collapseSubsetType X A, cellularPushoutCollapseLeft A f) := by
  let g : X → cellularPushoutCollapseLeft A f :=
    fun x ↦
      Quotient.mk'' ((pushout.inr (TopCat.ofHom f) (TopCat.subtypeInclusion A)).hom x)
  have hg : ∀ x y : X, collapseSubsetSetoid A x y → g x = g y := by
    intro x y hxy
    exact Quotient.sound (cellularPushoutCollapseComparison_respects A f hxy)
  have hcont : Continuous g := by
    dsimp [g]
    exact continuous_quotient_mk'.comp
      (pushout.inr (TopCat.ofHom f) (TopCat.subtypeInclusion A)).hom.continuous_toFun
  exact ⟨Quotient.lift g hg, hcont.quotient_lift hg⟩

/-- On a quotient class represented by `x : X`, the comparison map to `(Y ∪_f X) / Y` is induced
by the right pushout leg. -/
theorem cellularPushoutCollapseComparison_apply_mk
    (A : Set X) (f : C(A, Y)) (x : X) :
    cellularPushoutCollapseComparison A f (Quotient.mk'' x) =
      Quotient.mk''
        ((pushout.inr (TopCat.ofHom f) (TopCat.subtypeInclusion A)).hom x) :=
  rfl

/-- Corollary 10.2.4. For a continuous map `f : A → Y`, the quotient obtained from the adjunction
space `Y ∪_f X` by collapsing the copy of `Y`, formalized as `cellularPushoutCollapseLeft A f`,
is related to the quotient `X / A`, formalized as `collapseSubsetType X A`, by the canonical
comparison map `cellularPushoutCollapseComparison A f : X / A ⟶ (Y ∪_f X) / Y`, and this map is a
homeomorphism. -/
theorem cellularPushoutCollapseLeftHomeomorphicToCollapseSubset
    (A : Set X) (f : C(A, Y)) :
    IsHomeomorph (cellularPushoutCollapseComparison A f) := by
  sorry

end
