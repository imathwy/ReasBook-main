module

public import Topology_Munkres_2000.Book.Theorem_63_8.FiniteOpenCover
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

public section

open Finset Set TopologicalSpace

universe u v

namespace InvarianceOfDomainSupport

namespace FiniteOpenCover

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Theorem 63.8: a chosen refinement map assigns to each member of a
fine cover a containing member of the coarse cover. -/
structure RefinementMap (U V : FiniteOpenCover.{u, v} X) where
  /-- The chosen parent of each member of the fine cover. -/
  toFun : V.Index → U.Index
  /-- Every fine member is contained in its chosen parent. -/
  opens_le : ∀ j, V.opens j ≤ U.opens (toFun j)

/-- Helper for Theorem 63.8: every refinement relation admits a chosen refinement
map. -/
lemma refinementMap_nonempty {U V : FiniteOpenCover.{u, v} X} (hUV : U ≤ V) :
    Nonempty (RefinementMap U V) := by
  -- Choose one coarse parent for each member of the fine cover.
  classical
  refine ⟨⟨fun j ↦ Classical.choose (exists_parent_of_le hUV j), ?_⟩⟩
  intro j
  exact Classical.choose_spec (exists_parent_of_le hUV j)

/-- Helper for Theorem 63.8: the identity function is a refinement map from a cover
to itself. -/
def RefinementMap.id (U : FiniteOpenCover.{u, v} X) : RefinementMap U U :=
  ⟨fun i ↦ i, fun _ ↦ le_rfl⟩

/-- Helper for Theorem 63.8: chosen refinement maps compose. -/
def RefinementMap.comp {U V W : FiniteOpenCover.{u, v} X}
    (f : RefinementMap U V) (g : RefinementMap V W) : RefinementMap U W :=
  ⟨f.toFun ∘ g.toFun, fun k ↦ (g.opens_le k).trans (f.opens_le (g.toFun k))⟩

/-- Helper for Theorem 63.8: the parent function of a composite refinement is
the composite of the two parent functions. -/
@[simp] lemma RefinementMap.comp_toFun {U V W : FiniteOpenCover.{u, v} X}
    (f : RefinementMap U V) (g : RefinementMap V W) :
    (f.comp g).toFun = f.toFun ∘ g.toFun := by
  -- Expose the function projection without unfolding the refinement structure downstream.
  rfl

/-- Helper for Theorem 63.8: the parent function of a composite refinement is
the composite of the two parent functions. -/
@[simp] lemma RefinementMap.comp_toFun_apply {U V W : FiniteOpenCover.{u, v} X}
    (f : RefinementMap U V) (g : RefinementMap V W) (k : W.Index) :
    (f.comp g).toFun k = f.toFun (g.toFun k) := by
  -- Expose the projection formula without unfolding the refinement structure downstream.
  rfl

/-- Helper for Theorem 63.8: the faces of a cover nerve are the nonempty finite
families of cover members with nonempty total intersection. -/
def nerveFaces (U : FiniteOpenCover.{u, v} X) : Set (Finset U.Index) :=
  {s | s.Nonempty ∧ (⋂ i ∈ s, (U.opens i : Set X)).Nonempty}

/-- Helper for Theorem 63.8: nonempty-intersection nerve faces are downward closed
among nonempty finite families. -/
lemma nerveFaces_isRelLowerSet (U : FiniteOpenCover.{u, v} X) :
    IsRelLowerSet U.nerveFaces Finset.Nonempty := by
  -- A witness in the larger intersection remains in every member of a subfamily.
  intro s hs
  refine ⟨hs.1, ?_⟩
  intro t hts ht
  refine ⟨ht, ?_⟩
  obtain ⟨x, hx⟩ := hs.2
  refine ⟨x, ?_⟩
  simp only [Set.mem_iInter] at hx ⊢
  intro i hi
  exact hx i (hts hi)

/-- Helper for Theorem 63.8: the abstract nerve of a finite indexed open cover. -/
def nerve (U : FiniteOpenCover.{u, v} X) : PreAbstractSimplicialComplex U.Index :=
  { faces := U.nerveFaces
    isRelLowerSet_faces := U.nerveFaces_isRelLowerSet }

/-- Helper for Theorem 63.8: a chosen refinement map sends every nerve face of the
fine cover to a nerve face of the coarse cover. -/
lemma RefinementMap.image_mem_nerve {U V : FiniteOpenCover.{u, v} X}
    [DecidableEq U.Index] (f : RefinementMap U V)
    {s : Finset V.Index} (hs : s ∈ V.nerve) :
    s.image f.toFun ∈ U.nerve := by
  -- The same intersection point lies in every selected coarse parent.
  classical
  refine ⟨Finset.image_nonempty.mpr hs.1, ?_⟩
  obtain ⟨x, hx⟩ := hs.2
  refine ⟨x, ?_⟩
  simp only [Set.mem_iInter] at hx ⊢
  intro i hi
  obtain ⟨j, hjs, rfl⟩ := Finset.mem_image.mp hi
  exact f.opens_le j (hx j hjs)

/-- Helper for Theorem 63.8: mapping the fine nerve along a refinement choice gives
a subcomplex of the coarse nerve. -/
lemma RefinementMap.map_nerve_le {U V : FiniteOpenCover.{u, v} X}
    [DecidableEq U.Index] (f : RefinementMap U V) :
    V.nerve.map f.toFun ≤ U.nerve := by
  -- Unpack a mapped face and apply the pointwise refinement calculation.
  rintro _ ⟨s, hs, rfl⟩
  exact f.image_mem_nerve hs

/-- Helper for Theorem 63.8: two choices witnessing the same cover refinement are
contiguous on every fine nerve face. -/
lemma RefinementMap.image_union_mem_nerve {U V : FiniteOpenCover.{u, v} X}
    [DecidableEq U.Index] (f g : RefinementMap U V)
    {s : Finset V.Index} (hs : s ∈ V.nerve) :
    s.image f.toFun ∪ s.image g.toFun ∈ U.nerve := by
  -- A common point of the fine face lies in parents chosen by either map.
  classical
  refine ⟨Finset.Nonempty.mono Finset.subset_union_left
    (Finset.image_nonempty.mpr hs.1), ?_⟩
  obtain ⟨x, hx⟩ := hs.2
  refine ⟨x, ?_⟩
  simp only [Set.mem_iInter] at hx ⊢
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · obtain ⟨j, hjs, rfl⟩ := Finset.mem_image.mp hi
    exact f.opens_le j (hx j hjs)
  · obtain ⟨j, hjs, rfl⟩ := Finset.mem_image.mp hi
    exact g.opens_le j (hx j hjs)

end FiniteOpenCover

end InvarianceOfDomainSupport

end
