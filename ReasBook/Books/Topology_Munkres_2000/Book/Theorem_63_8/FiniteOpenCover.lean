module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.Sets.OpenCover

public section

open CategoryTheory Set TopologicalSpace

universe u v

namespace InvarianceOfDomainSupport

/-- Helper for Theorem 63.8: a finite indexed open cover, retaining its index type so
that refinement can later induce a map of nerves. -/
structure FiniteOpenCover (X : Type u) [TopologicalSpace X] where
  /-- The finite type indexing the cover. -/
  Index : Type v
  /-- The cover has finitely many members. -/
  [indexFintype : Fintype Index]
  /-- The indexed family of open sets. -/
  opens : Index → Opens X
  /-- The indexed family covers the space. -/
  isCover : IsOpenCover opens

namespace FiniteOpenCover

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Theorem 63.8: `V` refines `U` when every member of `V` lies in a
member of `U`. -/
def Refines (U V : FiniteOpenCover.{u, v} X) : Prop :=
  ∀ j : V.Index, ∃ i : U.Index, V.opens j ≤ U.opens i

/-- Helper for Theorem 63.8: every finite indexed open cover refines itself. -/
lemma refines_refl (U : FiniteOpenCover.{u, v} X) : U.Refines U := by
  -- Use the same index as parent for every member of the cover.
  intro i
  exact ⟨i, le_rfl⟩

/-- Helper for Theorem 63.8: refinement of finite indexed open covers is transitive. -/
lemma refines_trans {U V W : FiniteOpenCover.{u, v} X}
    (hUV : U.Refines V) (hVW : V.Refines W) : U.Refines W := by
  -- Compose the two choices of parent cover member.
  intro k
  obtain ⟨j, hkj⟩ := hVW k
  obtain ⟨i, hji⟩ := hUV j
  exact ⟨i, hkj.trans hji⟩

/-- Helper for Theorem 63.8: refinement gives finite open covers the preorder used
to index the Čech direct system; larger objects are finer covers. -/
instance : Preorder (FiniteOpenCover.{u, v} X) where
  le := Refines
  le_refl := refines_refl
  le_trans _ _ _ := refines_trans

/-- Helper for Theorem 63.8: the preorder relation is exactly open-cover
refinement. -/
lemma le_iff_refines {U V : FiniteOpenCover.{u, v} X} : U ≤ V ↔ U.Refines V := by
  -- Expose the refinement interpretation without unfolding the owner definition downstream.
  rfl

/-- Helper for Theorem 63.8: a finer cover member has a containing parent in every
coarser cover below it. -/
lemma exists_parent_of_le {U V : FiniteOpenCover.{u, v} X} (hUV : U ≤ V)
    (j : V.Index) : ∃ i : U.Index, V.opens j ≤ U.opens i := by
  -- Eliminate the opaque refinement relation through its preorder interface.
  exact le_iff_refines.mp hUV j

/-- Helper for Theorem 63.8: pairwise intersections of two finite open covers still
cover the space. -/
lemma interFamily_isCover (U V : FiniteOpenCover.{u, v} X) :
    IsOpenCover (fun ij : U.Index × V.Index ↦ U.opens ij.1 ⊓ V.opens ij.2) := by
  -- At a point, choose one member from each cover and intersect the two choices.
  apply IsOpenCover.of_sets
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, hxi⟩ := U.isCover.exists_mem x
  obtain ⟨j, hxj⟩ := V.isCover.exists_mem x
  exact Set.mem_iUnion.mpr ⟨(i, j), hxi, hxj⟩

/-- Helper for Theorem 63.8: the cover by pairwise intersections is a common finite
refinement of two finite indexed open covers. -/
def commonRefinement (U V : FiniteOpenCover.{u, v} X) : FiniteOpenCover.{u, v} X :=
  { Index := U.Index × V.Index
    indexFintype := @instFintypeProd U.Index V.Index U.indexFintype V.indexFintype
    opens := fun ij ↦ U.opens ij.1 ⊓ V.opens ij.2
    isCover := interFamily_isCover U V }

/-- Helper for Theorem 63.8: the intersection cover refines its left input. -/
lemma le_commonRefinement_left (U V : FiniteOpenCover.{u, v} X) :
    U ≤ commonRefinement U V := by
  -- Project an intersection to its left-hand member.
  intro ij
  exact ⟨ij.1, inf_le_left⟩

/-- Helper for Theorem 63.8: the intersection cover refines its right input. -/
lemma le_commonRefinement_right (U V : FiniteOpenCover.{u, v} X) :
    V ≤ commonRefinement U V := by
  -- Project an intersection to its right-hand member.
  intro ij
  exact ⟨ij.2, inf_le_right⟩

/-- Helper for Theorem 63.8: finite indexed open covers are directed by common
refinement. -/
instance : IsDirectedOrder (FiniteOpenCover.{u, v} X) where
  directed U V :=
    ⟨commonRefinement U V, le_commonRefinement_left U V,
      le_commonRefinement_right U V⟩

/-- Helper for Theorem 63.8: the one-member family consisting of the whole space
is an open cover. -/
lemma topFamily_isCover :
    IsOpenCover (fun _ : PUnit ↦ (⊤ : Opens X)) := by
  -- Its unique member contains every point.
  apply IsOpenCover.of_sets
  exact Set.iUnion_const Set.univ

/-- Helper for Theorem 63.8: the one-member cover supplies a base object for the
filtered refinement category. -/
def topCover : FiniteOpenCover.{u, v} X :=
  { Index := PUnit
    indexFintype := PUnit.fintype
    opens := fun _ ↦ ⊤
    isCover := topFamily_isCover }

/-- Helper for Theorem 63.8: the refinement preorder of finite indexed open covers
is nonempty. -/
instance : Nonempty (FiniteOpenCover.{u, v} X) := ⟨topCover⟩

/-- Helper for Theorem 63.8: finite indexed open covers form a filtered category
under refinement. -/
lemma isFiltered : IsFiltered (FiniteOpenCover.{u, v} X) := by
  -- The generic preorder construction uses common refinements and the top cover.
  infer_instance

end FiniteOpenCover

end InvarianceOfDomainSupport

end
