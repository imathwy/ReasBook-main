import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Topology.Category.TopCat.Basic
import StacksProject_2024.stacks_project.Chap05.Lemma_5_13_2
import StacksProject_2024.stacks_project.Chap07.Definition_7_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open Topology
open CategoryTheory.SemiRepresentableFamily.Over

/- Domain-style sampling for Definition 21.31.2:
- primary domain: fixed-target families in the `LC` category and the qc-covering condition they
  satisfy near each point of the target;
- inspected owner declarations:
  `CategoryTheory.SemiRepresentableFamily.Over`,
  `CategoryTheory.SemiRepresentableFamily.Over.ofArrows`,
  `CategoryTheory.ObjectProperty.FullSubcategory`,
  `LocallyCompactSpace`,
  `locallyCompactSpace_iff_weaklyLocallyCompactSpace`;
- best owner abstraction: the source-facing owner should be a predicate on the canonical fixed-
  target family object `SemiRepresentableFamily.Over X`, not a parallel raw pair of an index type
  and arrow family;
- primitive vs derived:
  primitive data are only the fixed-target family `𝒰 : SemiRepresentableFamily.Over X`;
  the finite compact-image neighborhood condition is the owner predicate itself, while the
  indexed-arrow presentation is only a bridge via `ofArrows`.

Source/core/bridge triage:
- `source-facing`: qc coverings 1 in `LC`;
- `core/canonical`: `SemiRepresentableFamily.Over X`;
- `bridge/view`: `SemiRepresentableFamily.Over.ofArrows`, which recovers the textbook indexed
  family presentation from the owner object, while the Hausdorff weakly-locally-compact wording is
  only a Chapter 5 bridge to the canonical owner `LocallyCompactSpace`.
-/

/-- The object property on `TopCat` selecting Hausdorff locally compact spaces. -/
abbrev HausdorffLocallyCompactObject : CategoryTheory.ObjectProperty TopCat.{u} :=
  fun X ↦ T2Space X ∧ LocallyCompactSpace X

namespace HausdorffLocallyCompactObject

/-- The `LC` object property can equivalently be read with the Stacks source wording
`WeaklyLocallyCompactSpace` in the Hausdorff case. -/
theorem iff (X : TopCat.{u}) :
    HausdorffLocallyCompactObject X ↔ T2Space X ∧ WeaklyLocallyCompactSpace X := by
  constructor
  · intro h
    letI : T2Space X := h.1
    letI : LocallyCompactSpace X := h.2
    exact ⟨h.1, (locallyCompactSpace_iff_weaklyLocallyCompactSpace).mp inferInstance⟩
  · intro h
    letI : T2Space X := h.1
    exact ⟨h.1, (locallyCompactSpace_iff_weaklyLocallyCompactSpace).mpr h.2⟩

end HausdorffLocallyCompactObject

/-- The category of Hausdorff locally compact spaces, equivalently Hausdorff locally
quasi-compact spaces, used for the `LC` site. -/
abbrev LCCat : Type (u + 1) :=
  HausdorffLocallyCompactObject.FullSubcategory

namespace LCCat

/-- Objects of `LCCat` carry their canonical Hausdorff structure on the underlying topological
space. -/
instance instT2SpaceObj (X : LCCat.{u}) : T2Space X.obj :=
  X.property.1

/-- Objects of `LCCat` carry their canonical locally compact structure on the underlying
topological space. -/
instance instLocallyCompactSpaceObj (X : LCCat.{u}) : LocallyCompactSpace X.obj :=
  X.property.2

end LCCat

section

variable {X : LCCat.{u}}

namespace CategoryTheory.SemiRepresentableFamily.Over

/-- Definition 21.31.2: a fixed-target family in `LC` is a qc covering 1 if every point of the
target has a neighborhood contained in a finite union of images of quasi-compact subsets of the
source spaces. -/
@[stacks 09X0]
def IsQcCoveringOne (𝒰 : Over X) : Prop :=
  ∀ x : X.obj, ∃ s : Finset 𝒰.index, ∃ E : ∀ i : s, Set ((𝒰.obj i.1).left.obj),
    (∀ i : s, IsCompact (E i)) ∧ (⋃ i : s, (𝒰.obj i.1).hom '' E i) ∈ 𝓝 x

-- Proof sketch: unfold `IsQcCoveringOne` at the point `x` and read off the finite index set, the
-- compact subsets upstairs, and the neighborhood condition for their image union.
/-- A qc covering 1 provides, around each point, finitely many source indices and compact subsets
whose images form a neighborhood of that point. -/
theorem IsQcCoveringOne.exists_finite_compact_image_neighborhood
    {𝒰 : Over X} (h : 𝒰.IsQcCoveringOne) (x : X.obj) :
    ∃ s : Finset 𝒰.index, ∃ E : ∀ i : s, Set ((𝒰.obj i.1).left.obj),
      (∀ i : s, IsCompact (E i)) ∧ (⋃ i : s, (𝒰.obj i.1).hom '' E i) ∈ 𝓝 x :=
  h x

/-- Source-facing companion to `IsQcCoveringOne`: around each point of the target, one can choose
an open neighborhood contained in a finite union of images of compact subsets upstairs. -/
theorem IsQcCoveringOne.exists_open_subset_finite_compact_image_union
    {𝒰 : Over X} (h : 𝒰.IsQcCoveringOne) (x : X.obj) :
    ∃ s : Finset 𝒰.index, ∃ E : ∀ i : s, Set ((𝒰.obj i.1).left.obj), ∃ V : Set X.obj,
      (∀ i : s, IsCompact (E i)) ∧ IsOpen V ∧ x ∈ V ∧
        V ⊆ ⋃ i : s, (𝒰.obj i.1).hom '' E i := by
  obtain ⟨s, E, hEcompact, hNhds⟩ := h.exists_finite_compact_image_neighborhood x
  rcases mem_nhds_iff.mp hNhds with ⟨V, hVsubset, hVopen, hxV⟩
  exact ⟨s, E, V, hEcompact, hVopen, hxV, hVsubset⟩

/-- The owner-level qc-covering predicate on `SemiRepresentableFamily.Over X` recovers the
textbook indexed-arrow formulation via `ofArrows`. -/
theorem ofArrows_isQcCoveringOne_iff {I : Type v} (X_ : I → LCCat.{u}) (f : ∀ i, X_ i ⟶ X) :
    (ofArrows X_ f).IsQcCoveringOne ↔
      ∀ x : X.obj, ∃ s : Finset I, ∃ E : ∀ i : s, Set ((X_ i.1).obj),
        (∀ i : s, IsCompact (E i)) ∧ (⋃ i : s, f i.1 '' E i) ∈ 𝓝 x :=
  Iff.rfl

end CategoryTheory.SemiRepresentableFamily.Over

end
