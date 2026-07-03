import Mathlib
import StacksProject_2024.Chap07.Definition_7_6_1

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
  `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`;
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
  family presentation from the owner object.
-/

/-- The object property on `TopCat` selecting Hausdorff weakly locally compact spaces. -/
abbrev HausdorffWeaklyLocallyCompactObject : CategoryTheory.ObjectProperty TopCat.{u} :=
  fun X ↦ T2Space X ∧ WeaklyLocallyCompactSpace X

/-- The category of Hausdorff weakly locally compact spaces, equivalently Hausdorff locally
quasi-compact spaces, used for the `LC` site. -/
abbrev LCCat : Type (u + 1) :=
  HausdorffWeaklyLocallyCompactObject.FullSubcategory

section

variable {X : LCCat.{u}}

namespace CategoryTheory.SemiRepresentableFamily.Over

/-- Definition 21.31.2: a fixed-target family in `LC` is a qc covering 1 if every point of the
target has a neighborhood contained in a finite union of images of quasi-compact subsets of the
source spaces. -/
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

/-- The owner-level qc-covering predicate on `SemiRepresentableFamily.Over X` recovers the
textbook indexed-arrow formulation via `ofArrows`. -/
theorem ofArrows_isQcCoveringOne_iff {I : Type v} (X_ : I → LCCat.{u}) (f : ∀ i, X_ i ⟶ X) :
    (ofArrows X_ f).IsQcCoveringOne ↔
      ∀ x : X.obj, ∃ s : Finset I, ∃ E : ∀ i : s, Set ((X_ i.1).obj),
        (∀ i : s, IsCompact (E i)) ∧ (⋃ i : s, f i.1 '' E i) ∈ 𝓝 x :=
  Iff.rfl

end CategoryTheory.SemiRepresentableFamily.Over

end
