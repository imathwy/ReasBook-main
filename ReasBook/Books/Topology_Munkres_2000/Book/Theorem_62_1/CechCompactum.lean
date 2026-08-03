module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Topology.Sets.OpenCover

public section

open CategoryTheory Finset Set TopologicalSpace

universe u v

namespace InvarianceOfDomainSupport

/-- Helper for Theorem 62.1: a finite indexed open cover, retaining its index type
so that refinement choices can induce maps of nerves. -/
structure CechFiniteOpenCover (X : Type u) [TopologicalSpace X] where
  /-- The finite type indexing the cover. -/
  Index : Type v
  /-- The cover has finitely many members. -/
  [indexFintype : Fintype Index]
  /-- The indexed family of open sets. -/
  opens : Index → Opens X
  /-- The indexed family covers the space. -/
  isCover : IsOpenCover opens

namespace CechFiniteOpenCover

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Theorem 62.1: `V` refines `U` when every member of `V` lies in a
member of `U`. -/
def Refines (U V : CechFiniteOpenCover.{u, v} X) : Prop :=
  ∀ j : V.Index, ∃ i : U.Index, V.opens j ≤ U.opens i

/-- Helper for Theorem 62.1: every finite indexed open cover refines itself. -/
lemma refines_refl (U : CechFiniteOpenCover.{u, v} X) : U.Refines U := by
  -- Each cover member chooses itself as its containing parent.
  intro i
  exact ⟨i, le_rfl⟩

/-- Helper for Theorem 62.1: refinement of finite indexed open covers is
transitive. -/
lemma refines_trans {U V W : CechFiniteOpenCover.{u, v} X}
    (hUV : U.Refines V) (hVW : V.Refines W) : U.Refines W := by
  -- Compose the two successive choices of containing cover members.
  intro k
  obtain ⟨j, hkj⟩ := hVW k
  obtain ⟨i, hji⟩ := hUV j
  exact ⟨i, hkj.trans hji⟩

/-- Helper for Theorem 62.1: refinement gives finite open covers the preorder
used to index the Čech direct system; larger objects are finer covers. -/
instance : Preorder (CechFiniteOpenCover.{u, v} X) where
  le := Refines
  le_refl := refines_refl
  le_trans _ _ _ := refines_trans

/-- Helper for Theorem 62.1: the preorder relation is exactly open-cover
refinement. -/
lemma le_iff_refines {U V : CechFiniteOpenCover.{u, v} X} : U ≤ V ↔ U.Refines V := by
  -- Expose the interpretation without unfolding the preorder downstream.
  rfl

/-- Helper for Theorem 62.1: a finer cover member has a containing parent in
every coarser cover below it. -/
lemma exists_parent_of_le {U V : CechFiniteOpenCover.{u, v} X} (hUV : U ≤ V)
    (j : V.Index) : ∃ i : U.Index, V.opens j ≤ U.opens i := by
  -- Eliminate refinement through its preorder-facing statement.
  exact le_iff_refines.mp hUV j

/-- Helper for Theorem 62.1: pairwise intersections of two finite open covers
still cover the space. -/
lemma interFamily_isCover (U V : CechFiniteOpenCover.{u, v} X) :
    IsOpenCover (fun ij : U.Index × V.Index ↦ U.opens ij.1 ⊓ V.opens ij.2) := by
  -- At a point, intersect one member chosen from each original cover.
  apply IsOpenCover.of_sets
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, hxi⟩ := U.isCover.exists_mem x
  obtain ⟨j, hxj⟩ := V.isCover.exists_mem x
  exact Set.mem_iUnion.mpr ⟨(i, j), hxi, hxj⟩

/-- Helper for Theorem 62.1: pairwise intersections form a common finite
refinement of two finite indexed open covers. -/
def commonRefinement (U V : CechFiniteOpenCover.{u, v} X) :
    CechFiniteOpenCover.{u, v} X :=
  { Index := U.Index × V.Index
    indexFintype := @instFintypeProd U.Index V.Index U.indexFintype V.indexFintype
    opens := fun ij ↦ U.opens ij.1 ⊓ V.opens ij.2
    isCover := interFamily_isCover U V }

/-- Helper for Theorem 62.1: the intersection cover refines its left input. -/
lemma le_commonRefinement_left (U V : CechFiniteOpenCover.{u, v} X) :
    U ≤ commonRefinement U V := by
  -- Project every intersection to its left-hand member.
  intro ij
  exact ⟨ij.1, inf_le_left⟩

/-- Helper for Theorem 62.1: the intersection cover refines its right input. -/
lemma le_commonRefinement_right (U V : CechFiniteOpenCover.{u, v} X) :
    V ≤ commonRefinement U V := by
  -- Project every intersection to its right-hand member.
  intro ij
  exact ⟨ij.2, inf_le_right⟩

/-- Helper for Theorem 62.1: finite indexed open covers are directed by common
refinement. -/
instance : IsDirectedOrder (CechFiniteOpenCover.{u, v} X) where
  directed U V :=
    ⟨commonRefinement U V, le_commonRefinement_left U V,
      le_commonRefinement_right U V⟩

/-- Helper for Theorem 62.1: the one-member family consisting of the whole
space is an open cover. -/
lemma topFamily_isCover : IsOpenCover (fun _ : PUnit ↦ (⊤ : Opens X)) := by
  -- Its unique member contains every point.
  apply IsOpenCover.of_sets
  exact Set.iUnion_const Set.univ

/-- Helper for Theorem 62.1: the one-member cover supplies a base object for the
filtered refinement category. -/
def topCover : CechFiniteOpenCover.{u, v} X :=
  { Index := PUnit
    indexFintype := PUnit.fintype
    opens := fun _ ↦ ⊤
    isCover := topFamily_isCover }

/-- Helper for Theorem 62.1: the refinement preorder of finite indexed open
covers is nonempty. -/
instance : Nonempty (CechFiniteOpenCover.{u, v} X) := ⟨topCover⟩

/-- Helper for Theorem 62.1: finite indexed open covers form a filtered category
under refinement. -/
lemma isFiltered : IsFiltered (CechFiniteOpenCover.{u, v} X) := by
  -- The preorder category is filtered because covers are nonempty and directed.
  infer_instance

/-- Helper for Theorem 62.1: a chosen refinement map assigns to each member of a
fine cover a containing member of the coarse cover. -/
structure RefinementMap (U V : CechFiniteOpenCover.{u, v} X) where
  /-- The chosen parent of each fine cover member. -/
  toFun : V.Index → U.Index
  /-- Every fine cover member is contained in its chosen parent. -/
  opens_le : ∀ j, V.opens j ≤ U.opens (toFun j)

/-- Helper for Theorem 62.1: every refinement relation admits a chosen
refinement map. -/
lemma refinementMap_nonempty {U V : CechFiniteOpenCover.{u, v} X} (hUV : U ≤ V) :
    Nonempty (RefinementMap U V) := by
  -- Choose one containing coarse member for each fine member.
  classical
  refine ⟨⟨fun j ↦ Classical.choose (exists_parent_of_le hUV j), ?_⟩⟩
  intro j
  exact Classical.choose_spec (exists_parent_of_le hUV j)

/-- Helper for Theorem 62.1: identity on indices is a refinement map from a
cover to itself. -/
def RefinementMap.id (U : CechFiniteOpenCover.{u, v} X) : RefinementMap U U :=
  ⟨fun i ↦ i, fun _ ↦ le_rfl⟩

/-- Helper for Theorem 62.1: chosen refinement maps compose. -/
def RefinementMap.comp {U V W : CechFiniteOpenCover.{u, v} X}
    (f : RefinementMap U V) (g : RefinementMap V W) : RefinementMap U W :=
  ⟨f.toFun ∘ g.toFun, fun k ↦ (g.opens_le k).trans (f.opens_le (g.toFun k))⟩

/-- Helper for Theorem 62.1: the parent function of a composite refinement is
the composite of the two parent functions. -/
@[simp] lemma RefinementMap.comp_toFun_apply {U V W : CechFiniteOpenCover.{u, v} X}
    (f : RefinementMap U V) (g : RefinementMap V W) (k : W.Index) :
    (f.comp g).toFun k = f.toFun (g.toFun k) := by
  -- Reveal only the computational projection used by subsequent nerve maps.
  rfl

/-- Helper for Theorem 62.1: the nerve faces are nonempty finite families of
cover members with nonempty total intersection. -/
def nerveFaces (U : CechFiniteOpenCover.{u, v} X) : Set (Finset U.Index) :=
  {s | s.Nonempty ∧ (⋂ i ∈ s, (U.opens i : Set X)).Nonempty}

/-- Helper for Theorem 62.1: membership in the nerve faces is nonemptiness of
the finite family together with nonemptiness of its total intersection. -/
lemma mem_nerveFaces_iff (U : CechFiniteOpenCover.{u, v} X)
    (s : Finset U.Index) :
    s ∈ U.nerveFaces ↔
      s.Nonempty ∧ (⋂ i ∈ s, (U.opens i : Set X)).Nonempty := by
  -- Expose the defining predicate once at its canonical owner.
  rfl

/-- Helper for Theorem 62.1: nonempty-intersection nerve faces are downward
closed among nonempty finite families. -/
lemma nerveFaces_isRelLowerSet (U : CechFiniteOpenCover.{u, v} X) :
    IsRelLowerSet U.nerveFaces Finset.Nonempty := by
  -- A common point for a face remains common to each nonempty subface.
  intro s hs
  refine ⟨hs.1, ?_⟩
  intro t hts ht
  refine ⟨ht, ?_⟩
  obtain ⟨x, hx⟩ := hs.2
  refine ⟨x, ?_⟩
  simp only [Set.mem_iInter] at hx ⊢
  intro i hi
  exact hx i (hts hi)

/-- Helper for Theorem 62.1: the abstract nerve of a finite indexed open cover. -/
def nerve (U : CechFiniteOpenCover.{u, v} X) :
    PreAbstractSimplicialComplex U.Index :=
  { faces := U.nerveFaces
    isRelLowerSet_faces := U.nerveFaces_isRelLowerSet }

/-- Helper for Theorem 62.1: a refinement map sends every fine nerve face to a
coarse nerve face. -/
lemma RefinementMap.image_mem_nerve {U V : CechFiniteOpenCover.{u, v} X}
    [DecidableEq U.Index] (f : RefinementMap U V)
    {s : Finset V.Index} (hs : s ∈ V.nerve) : s.image f.toFun ∈ U.nerve := by
  -- The same intersection point lies in every selected coarse parent.
  classical
  refine ⟨Finset.image_nonempty.mpr hs.1, ?_⟩
  obtain ⟨x, hx⟩ := hs.2
  refine ⟨x, ?_⟩
  simp only [Set.mem_iInter] at hx ⊢
  intro i hi
  obtain ⟨j, hjs, rfl⟩ := Finset.mem_image.mp hi
  exact f.opens_le j (hx j hjs)

/-- Helper for Theorem 62.1: mapping a fine nerve along a refinement choice
lands in the coarse nerve. -/
lemma RefinementMap.map_nerve_le {U V : CechFiniteOpenCover.{u, v} X}
    [DecidableEq U.Index] (f : RefinementMap U V) :
    V.nerve.map f.toFun ≤ U.nerve := by
  -- Unpack a mapped face and apply the common-intersection calculation.
  rintro _ ⟨s, hs, rfl⟩
  exact f.image_mem_nerve hs

/-- Helper for Theorem 62.1: two choices witnessing one refinement are
contiguous on every fine nerve face. -/
lemma RefinementMap.image_union_mem_nerve {U V : CechFiniteOpenCover.{u, v} X}
    [DecidableEq U.Index] (f g : RefinementMap U V)
    {s : Finset V.Index} (hs : s ∈ V.nerve) :
    s.image f.toFun ∪ s.image g.toFun ∈ U.nerve := by
  -- One fine-face intersection point lies in parents chosen by either map.
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

/-- Helper for Theorem 62.1: the face poset of a finite-cover nerve consists of
its nonempty nerve faces, ordered by inclusion. -/
abbrev NerveFace (U : CechFiniteOpenCover.{u, v} X) :=
  {s : Finset U.Index // s ∈ U.nerve}

/-- Helper for Theorem 62.1: the face poset of a finite-cover nerve is finite. -/
noncomputable instance instFintypeNerveFace (U : CechFiniteOpenCover.{u, v} X) :
    Fintype U.NerveFace :=
  letI : Fintype U.Index := U.indexFintype
  Fintype.ofInjective (fun s : U.NerveFace ↦ (s : Finset U.Index))
    Subtype.val_injective

/-- Helper for Theorem 62.1: taking the image under a refinement choice is
monotone on nerve faces. -/
lemma RefinementMap.monotone_faceImage {U V : CechFiniteOpenCover.{u, v} X}
    [DecidableEq U.Index] (f : RefinementMap U V) :
    Monotone (fun s : NerveFace V ↦ s.1.image f.toFun) := by
  -- Inclusion of fine faces is preserved by taking the image of their vertices.
  intro s t hst
  exact Finset.image_mono f.toFun hst

/-- Helper for Theorem 62.1: a refinement choice induces a monotone map from
the fine nerve-face poset to the coarse nerve-face poset. -/
def RefinementMap.faceMap {U V : CechFiniteOpenCover.{u, v} X}
    [DecidableEq U.Index] (f : RefinementMap U V) : NerveFace V →o NerveFace U :=
  ⟨fun s ↦ ⟨s.1.image f.toFun, f.image_mem_nerve s.property⟩,
    f.monotone_faceImage⟩

/-- Helper for Theorem 62.1: the underlying face of the refinement face map is
the image of the original face. -/
@[simp] lemma RefinementMap.coe_faceMap_apply {U V : CechFiniteOpenCover.{u, v} X}
    [DecidableEq U.Index] (f : RefinementMap U V) (s : NerveFace V) :
    (f.faceMap s : Finset U.Index) = s.1.image f.toFun := by
  -- Expose the stable finite-set computation without unfolding the order map downstream.
  rfl

/-- Helper for Theorem 62.1: the union of the images under two refinement
choices is monotone on nerve faces. -/
lemma RefinementMap.monotone_unionFaceImage {U V : CechFiniteOpenCover.{u, v} X}
    [DecidableEq U.Index] (f g : RefinementMap U V) :
    Monotone (fun s : NerveFace V ↦ s.1.image f.toFun ∪ s.1.image g.toFun) := by
  -- Both image inclusions pass through the union coordinatewise.
  intro s t hst
  exact Finset.union_subset_union (Finset.image_mono f.toFun hst)
    (Finset.image_mono g.toFun hst)

/-- Helper for Theorem 62.1: two refinement choices have a common monotone
union-face map. -/
def RefinementMap.unionFaceMap {U V : CechFiniteOpenCover.{u, v} X}
    [DecidableEq U.Index] (f g : RefinementMap U V) : NerveFace V →o NerveFace U :=
  ⟨fun s ↦
      ⟨s.1.image f.toFun ∪ s.1.image g.toFun,
        f.image_union_mem_nerve g s.property⟩,
    f.monotone_unionFaceImage g⟩

/-- Helper for Theorem 62.1: the first refinement face map is pointwise below
the common union-face map. -/
lemma RefinementMap.faceMap_le_unionFaceMap_left
    {U V : CechFiniteOpenCover.{u, v} X} [DecidableEq U.Index]
    (f g : RefinementMap U V) : f.faceMap ≤ f.unionFaceMap g := by
  -- Every first image is contained in the union of the two images.
  intro s
  exact Finset.subset_union_left

/-- Helper for Theorem 62.1: the second refinement face map is pointwise below
the common union-face map. -/
lemma RefinementMap.faceMap_le_unionFaceMap_right
    {U V : CechFiniteOpenCover.{u, v} X} [DecidableEq U.Index]
    (f g : RefinementMap U V) : g.faceMap ≤ f.unionFaceMap g := by
  -- Every second image is contained in the union of the two images.
  intro s
  exact Finset.subset_union_right

/-- Helper for Theorem 62.1: the identity refinement induces the identity map
of the nerve-face poset. -/
lemma RefinementMap.faceMap_id (U : CechFiniteOpenCover.{u, v} X)
    [DecidableEq U.Index] : (RefinementMap.id U).faceMap = OrderHom.id := by
  -- Compare the underlying finite faces; imaging by the identity changes nothing.
  apply OrderHom.ext
  funext s
  apply Subtype.ext
  exact Finset.image_id

/-- Helper for Theorem 62.1: face maps turn composition of refinement choices
into composition of monotone maps. -/
lemma RefinementMap.faceMap_comp {U V W : CechFiniteOpenCover.{u, v} X}
    [DecidableEq U.Index] [DecidableEq V.Index]
    (f : RefinementMap U V) (g : RefinementMap V W) :
    (f.comp g).faceMap = f.faceMap.comp g.faceMap := by
  -- Compare finite faces and use functoriality of `Finset.image`.
  apply OrderHom.ext
  funext s
  apply Subtype.ext
  exact Finset.image_comp (s := (s : Finset W.Index))
    (f := g.toFun) (g := f.toFun)

end CechFiniteOpenCover

end InvarianceOfDomainSupport

end
