import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.Topology.Sets.OpenCover
import StacksProject_2024.stacks_project.Chap25.«25_11_0_3»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

universe u v

namespace SSet

-- Source/core/bridge triage:
-- `OpenHypercovering` is the source-facing owner for the topological-space hypercoverings used in
-- this section. `OpenFamily` and its nonempty-index restriction are the bridge layer used to
-- refine an open hypercovering so that every indexed open is nonempty.

variable {X : TopCat.{u}} {I : SSet.{v}}

/-- A simplicial-indexed family of opens on `X`, constant along the simplicial operators of `I`. -/
structure OpenFamily (X : TopCat.{u}) (I : SSet.{v}) where
  openAt {Δ : SimplexCategoryᵒᵖ} : I.obj Δ → Opens X
  map_eq {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') (i : I.obj Δ) :
    openAt (I.map f i) = openAt i

attribute [simp] OpenFamily.map_eq

/-- A hypercovering of a topological space by simplicial-indexed opens. -/
structure OpenHypercovering (X : TopCat.{u}) where
  /-- The underlying simplicial set of indices. -/
  I : SSet.{v}
  /-- The simplicial-indexed family of opens on `X`. -/
  family : OpenFamily X I
  /-- The level-`0` opens cover `X`. -/
  zero_isOpenCover :
    TopologicalSpace.IsOpenCover
      (fun i : I.obj (op <| SimplexCategory.mk 0) ↦ family.openAt i)
  /-- Each degree `n + 1` family covers the intersections prescribed by the degree-`n` faces. -/
  succ (n : ℕ) :
    HypercoveringIntersectionCondition
      (fun a j ↦ I.map (SimplexCategory.δ a).op j)
      (fun i : I.obj (op <| SimplexCategory.mk n) ↦ family.openAt i)
      (fun j : I.obj (op <| SimplexCategory.mk (n + 1)) ↦ family.openAt j)

namespace OpenHypercovering

variable {X : TopCat.{u}}

/-- An open hypercovering is degreewise nonempty when every indexed open is nonempty. -/
def degreewiseNonempty (H : OpenHypercovering X) : Prop :=
  ∀ ⦃Δ : SimplexCategoryᵒᵖ⦄ (i : H.I.obj Δ),
    (H.family.openAt i : Set X).Nonempty

/-- Unfolding `degreewiseNonempty` says exactly that each indexed open of the hypercovering is
nonempty. -/
theorem degreewiseNonempty_iff (H : OpenHypercovering X) :
    H.degreewiseNonempty ↔
      ∀ ⦃Δ : SimplexCategoryᵒᵖ⦄ (i : H.I.obj Δ),
        (H.family.openAt i : Set X).Nonempty :=
  Iff.rfl

/-- Every indexed open of a degreewise nonempty hypercovering is nonempty. -/
theorem degreewiseNonempty.openAt_nonempty
    {H : OpenHypercovering X} (hH : H.degreewiseNonempty)
    {Δ : SimplexCategoryᵒᵖ} (i : H.I.obj Δ) :
    (H.family.openAt i : Set X).Nonempty :=
  hH i

/-- An indexed open is nonempty exactly when it is not the bottom open. -/
theorem openAt_nonempty_iff_ne_bot
    (H : OpenHypercovering X) {Δ : SimplexCategoryᵒᵖ} (i : H.I.obj Δ) :
    (H.family.openAt i : Set X).Nonempty ↔ H.family.openAt i ≠ ⊥ := by
  simpa using (Opens.ne_bot_iff_nonempty (H.family.openAt i)).symm

/-- Degreewise nonemptiness can be checked by asking that each indexed open is not bottom. -/
theorem degreewiseNonempty_iff_ne_bot (H : OpenHypercovering X) :
    H.degreewiseNonempty ↔
      ∀ ⦃Δ : SimplexCategoryᵒᵖ⦄ (i : H.I.obj Δ), H.family.openAt i ≠ ⊥ := by
  constructor
  · intro hH Δ i
    exact (H.openAt_nonempty_iff_ne_bot i).mp (hH i)
  · intro hH Δ i
    exact (H.openAt_nonempty_iff_ne_bot i).mpr (hH i)

/-- Every indexed open of a degreewise nonempty hypercovering is not bottom. -/
theorem degreewiseNonempty.openAt_ne_bot
    {H : OpenHypercovering X} (hH : H.degreewiseNonempty)
    {Δ : SimplexCategoryᵒᵖ} (i : H.I.obj Δ) :
    H.family.openAt i ≠ ⊥ :=
  (H.openAt_nonempty_iff_ne_bot i).mp (hH i)

/-- Remark 25.11.1 (1): the simplices with nonempty associated opens form a subsimplicial set of
the indexing simplicial set of an open hypercovering. -/
@[stacks 01H5]
def nonemptySubfunctor (H : OpenHypercovering X) : Subfunctor H.I where
  obj _ := { i | (H.family.openAt i : Set X).Nonempty }
  map f := by
    intro i hi
    simpa using hi

@[simp] theorem mem_nonemptySubfunctor_obj
    (H : OpenHypercovering X) {Δ : SimplexCategoryᵒᵖ} (i : H.I.obj Δ) :
    i ∈ (H.nonemptySubfunctor.obj Δ) ↔ (H.family.openAt i : Set X).Nonempty :=
  Iff.rfl

@[simp] theorem mem_nonemptySubfunctor_obj_iff_ne_bot
    (H : OpenHypercovering X) {Δ : SimplexCategoryᵒᵖ} (i : H.I.obj Δ) :
    i ∈ (H.nonemptySubfunctor.obj Δ) ↔ H.family.openAt i ≠ ⊥ := by
  rw [mem_nonemptySubfunctor_obj, H.openAt_nonempty_iff_ne_bot]

/-- Every indexed open is nonempty exactly when the associated subsimplicial set of nonempty
simplices is the whole simplicial set. -/
theorem nonemptySubfunctor_eq_top_iff (H : OpenHypercovering X) :
    H.nonemptySubfunctor = ⊤ ↔ H.degreewiseNonempty := by
  constructor
  · intro hH Δ i
    have hi : i ∈ H.nonemptySubfunctor.obj Δ := by
      simpa [hH] using (Set.mem_univ i : i ∈ (⊤ : Subfunctor H.I).obj Δ)
    exact (H.mem_nonemptySubfunctor_obj i).mp hi
  · intro hH
    ext Δ i
    simp [H.mem_nonemptySubfunctor_obj, hH i]

/-- The simplicial set of indices whose associated opens are nonempty. -/
private abbrev nonemptyIndices (H : OpenHypercovering X) : SSet.{v} :=
  H.nonemptySubfunctor.toFunctor

/-- The restriction of the open family of `H` to the nonempty simplices. -/
private def nonemptyFamily (H : OpenHypercovering X) : OpenFamily X H.nonemptyIndices where
  openAt i := H.family.openAt i.1
  map_eq f i := H.family.map_eq f i.1

/-- The degree-`0` opens indexed by the nonempty simplices still cover `X`. -/
private theorem restrictToNonempty_zero_isOpenCover (H : OpenHypercovering X) :
    TopologicalSpace.IsOpenCover
      (fun i : H.nonemptyIndices.obj (op <| SimplexCategory.mk 0) ↦ H.nonemptyFamily.openAt i) := by
  sorry

/-- The nonempty simplices of an open hypercovering still satisfy the hypercovering intersection
condition in every simplicial degree. -/
private theorem restrictToNonempty_succ
    (H : OpenHypercovering X) (n : ℕ) :
    HypercoveringIntersectionCondition
      (fun a j ↦ H.nonemptyIndices.map (SimplexCategory.δ a).op j)
      (fun i : H.nonemptyIndices.obj (op <| SimplexCategory.mk n) ↦ H.nonemptyFamily.openAt i)
      (fun j : H.nonemptyIndices.obj (op <| SimplexCategory.mk (n + 1)) ↦ H.nonemptyFamily.openAt j) := by
  sorry

/-- Restricting an open hypercovering to the simplices with nonempty associated opens again gives
an open hypercovering. -/
def restrictToNonempty (H : OpenHypercovering X) : OpenHypercovering X where
  I := H.nonemptyIndices
  family := H.nonemptyFamily
  zero_isOpenCover := H.restrictToNonempty_zero_isOpenCover
  succ := H.restrictToNonempty_succ

/-- Any pointwise property of the indexed opens of `H` is inherited by the restriction to the
nonempty simplices. -/
theorem restrictToNonempty_openAt_property
    (H : OpenHypercovering X) {P : Opens X → Prop}
    (hP : ∀ ⦃Δ : SimplexCategoryᵒᵖ⦄ (i : H.I.obj Δ), P (H.family.openAt i)) :
    ∀ ⦃Δ : SimplexCategoryᵒᵖ⦄ (i : H.nonemptySubfunctor.obj Δ),
      P (H.family.openAt i.1) :=
  by
    intro Δ i
    simpa using hP i.1

/-- Remark 25.11.1 (2): after restricting to the nonempty simplices, every indexed open is
nonempty. -/
@[stacks 01H5]
theorem restrictToNonempty_nonempty
    (H : OpenHypercovering X) {Δ : SimplexCategoryᵒᵖ}
    (i : H.nonemptySubfunctor.obj Δ) :
    (H.family.openAt i.1 : Set X).Nonempty := by
  simpa using (H.mem_nonemptySubfunctor_obj i.1).mp i.2

/-- Every indexed open of the restricted hypercovering is not bottom. -/
@[simp] theorem restrictToNonempty_openAt_ne_bot
    (H : OpenHypercovering X) {Δ : SimplexCategoryᵒᵖ}
    (i : H.nonemptySubfunctor.obj Δ) :
    H.family.openAt i.1 ≠ ⊥ :=
  (H.openAt_nonempty_iff_ne_bot i.1).mp (H.restrictToNonempty_nonempty i)

/-- Remark 25.11.1 (2), (3): restricting to the nonempty simplices gives a refinement whose
indexed opens are all nonempty. -/
@[stacks 01H5]
theorem restrictToNonempty_degreewiseNonempty
    (H : OpenHypercovering X) :
    H.restrictToNonempty.degreewiseNonempty := by
  intro Δ i
  simpa using H.restrictToNonempty_nonempty i

end OpenHypercovering
end SSet
