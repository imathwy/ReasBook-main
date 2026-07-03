import Mathlib
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Category
import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered
import Mathlib.CategoryTheory.Sites.Point.Presheaf
import Mathlib.Tactic.Recall
import Mathlib.Topology.Sheaves.Points
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sober

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_7_33_6 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice
open TopCat
open TopologicalSpace

universe u

namespace CategoryTheory

variable {X : TopCat.{u}}

/- Domain-style sampling for Example 7.33.6:
- primary domain: points of the opens site of a topological space, their classification by
  irreducible closed subsets, and the sober-space identification of irreducible closed subsets with
  points;
- sampled owner API:
  `GrothendieckTopology.Point`,
  `Opens.pointGrothendieckTopology`,
  `IrreducibleCloseds`,
  `IsGenericPoint`,
  `irreducibleSetEquivPoints`;
- best owner abstraction: the site-point owner `GrothendieckTopology.Point` together with the
  canonical topological owners `IrreducibleCloseds` and `irreducibleSetEquivPoints`.

Source/core/bridge triage:
- `source-facing`: the point `irreducibleClosedSitePoint Z` attached to an irreducible closed
  subset and the recovered irreducible closed subset `sitePointIrreducibleClosed Φ`;
- `core/canonical`: `GrothendieckTopology.Point`, `Opens.pointGrothendieckTopology`,
  `IrreducibleCloseds`, `IsGenericPoint`, and `irreducibleSetEquivPoints`;
- `bridge/view`: the comparison isomorphisms between an arbitrary opens-site point, the
  irreducible-closed point extracted from it, and in the sober case the standard point attached to
  the corresponding space point.

Primitive data versus derived API:
- primitive data: an irreducible closed subset `Z` or an opens-site point `Φ`;
- derived API: singleton-or-empty fiber descriptions, the recovered support
  `sitePointIrreducibleClosed Φ`, the generic-point comparison, and the sober-space point
  classification. The sober-case point itself is therefore best expressed directly via the canonical
  owner `irreducibleSetEquivPoints`, not via a parallel one-off wrapper definition.
-/

private def irreducibleClosedPointFiberObj (Z : IrreducibleCloseds X) (U : Opens X) : Type u :=
  ULift (PLift (((Z : Set X) ∩ U).Nonempty))

private def irreducibleClosedPointFiberMap (Z : IrreducibleCloseds X) {U V : Opens X} (i : U ⟶ V) :
    irreducibleClosedPointFiberObj Z U ⟶ irreducibleClosedPointFiberObj Z V :=
  fun h ↦ ⟨⟨Set.Nonempty.mono (fun _ hx ↦ ⟨hx.1, i.le hx.2⟩) h.down.down⟩⟩

private theorem irreducibleClosedPointFiberMap_id (Z : IrreducibleCloseds X) (U : Opens X) :
    irreducibleClosedPointFiberMap Z (𝟙 U) = 𝟙 (irreducibleClosedPointFiberObj Z U) := by
  -- The identity inclusion leaves the witness of `Z ∩ U` unchanged.
  funext h
  cases h
  rfl

private theorem irreducibleClosedPointFiberMap_comp (Z : IrreducibleCloseds X)
    {U V W : Opens X} (i : U ⟶ V) (j : V ⟶ W) :
    irreducibleClosedPointFiberMap Z (i ≫ j) =
      irreducibleClosedPointFiberMap Z i ≫ irreducibleClosedPointFiberMap Z j := by
  -- Both sides transport the same intersection witness along the same inclusion chain.
  funext h
  cases h
  rfl

private def irreducibleClosedPointFiber (Z : IrreducibleCloseds X) : Opens X ⥤ Type u where
  obj := irreducibleClosedPointFiberObj Z
  map := irreducibleClosedPointFiberMap Z
  map_id := irreducibleClosedPointFiberMap_id Z
  map_comp := irreducibleClosedPointFiberMap_comp Z

private instance irreducibleClosedPointFiber_elements_initiallySmall (Z : IrreducibleCloseds X) :
    InitiallySmall.{u} (irreducibleClosedPointFiber Z).Elements :=
  initiallySmall_of_essentiallySmall _

private instance : OrderTop (Opens X) where
  top := ⟨Set.univ, isOpen_univ⟩
  le_top := by
    intro U x hx
    trivial

private noncomputable instance : HasFiniteLimits (Opens X) :=
  hasFiniteLimits_of_semilatticeInf_orderTop

-- Proof sketch: irreducibility shows that two opens meeting `Z` have intersection meeting `Z`,
-- and thinness of the opens category resolves the parallel-arrow axiom.
/-- Helper for Example 7.33.6: the category of elements of the singleton-or-empty fiber functor
attached to an irreducible closed subset is cofiltered. -/
private theorem irreducibleClosedPointFiber_isCofiltered (Z : IrreducibleCloseds X) :
    IsCofiltered (irreducibleClosedPointFiber Z).Elements where
  nonempty := by
    -- The top open meets `Z` because irreducible subsets are nonempty.
    refine ⟨⟨⊤, ?_⟩⟩
    refine ⟨⟨?_⟩⟩
    exact Set.Nonempty.mono (fun x hxZ ↦ ⟨hxZ, by trivial⟩) Z.2.nonempty
  cone_objs := by
    rintro ⟨U, sU⟩ ⟨V, sV⟩
    -- If both opens meet `Z`, irreducibility gives a point in the intersection.
    have hUV : ((Z : Set X) ∩ (U ⊓ V : Opens X)).Nonempty := by
      exact Z.2.isPreirreducible U V U.2 V.2 sU.down.down sV.down.down
    refine ⟨⟨U ⊓ V, ⟨⟨hUV⟩⟩⟩, ?_, ?_, ?_⟩
    · exact ⟨homOfLE inf_le_left, rfl⟩
    · exact ⟨homOfLE inf_le_right, rfl⟩
    · exact ⟨⟩
  cone_maps := by
    rintro ⟨U, sU⟩ ⟨V, sV⟩ ⟨f, hf⟩ ⟨g, hg⟩
    -- Parallel morphisms already agree in the thin category of opens.
    exact ⟨⟨U, sU⟩, 𝟙 _, rfl⟩

private theorem irreducibleClosedPointFiber_jointly_surjective (Z : IrreducibleCloseds X)
    {U : Opens X} (R : Sieve U) (hR : R ∈ Opens.grothendieckTopology X U)
    (s : (irreducibleClosedPointFiber Z).obj U) :
    ∃ (V : Opens X) (i : V ⟶ U), R i ∧ ∃ t : (irreducibleClosedPointFiber Z).obj V,
      (irreducibleClosedPointFiber Z).map i t = s := by
  -- Refine the covering sieve at a point of `Z ∩ U`.
  rcases s.down.down with ⟨x, hxZ, hxU⟩
  rcases hR x hxU with ⟨V, i, hi, hxV⟩
  refine ⟨V, i, hi, ⟨⟨⟨x, hxZ, hxV⟩⟩⟩, ?_⟩
  rfl

/- Internally, the point attached to `Z` uses the singleton-or-empty fiber over each open `U`:
it is empty when `Z ∩ U = ∅` and a singleton when `Z ∩ U` is nonempty. -/
/-- The point of the opens site attached to an irreducible closed subset `Z`. -/
noncomputable def irreducibleClosedSitePoint (Z : IrreducibleCloseds X) :
    (Opens.grothendieckTopology X).Point := by
  -- Package the singleton-or-empty fibers with their direct cofilteredness proof.
  exact
    { fiber := irreducibleClosedPointFiber Z
      isCofiltered := irreducibleClosedPointFiber_isCofiltered Z
      jointly_surjective := by
        intro U R hR s
        rcases irreducibleClosedPointFiber_jointly_surjective Z R hR s with
          ⟨V, i, hi, t, ht⟩
        exact ⟨V, i, hi, t, ht⟩ }

-- Proof sketch: once `irreducibleClosedPointFiber Z` is realized as the fiber of a site point,
-- finite-limit preservation is the standard exactness property of point fibers.
private theorem irreducibleClosedPointFiber_preservesFiniteLimits (Z : IrreducibleCloseds X) :
    PreservesFiniteLimits (irreducibleClosedPointFiber Z) := by
  -- Reuse the canonical exactness instance for the fiber of a site point.
  change PreservesFiniteLimits (irreducibleClosedSitePoint Z).fiber
  infer_instance

private noncomputable instance (Z : IrreducibleCloseds X) :
    PreservesFiniteLimits (irreducibleClosedPointFiber Z) :=
  irreducibleClosedPointFiber_preservesFiniteLimits Z

/-- The fiber of the point attached to `Z` over an open `U` is nonempty exactly when `U` meets
`Z`; since fibers of points on the opens site are subsingletons, this means the fiber is then a
singleton. -/
@[simp] theorem irreducibleClosedSitePoint_fiber_nonempty_iff
    (Z : IrreducibleCloseds X) (U : Opens X) :
    Nonempty ((irreducibleClosedSitePoint Z).fiber.obj U) ↔ ((Z : Set X) ∩ U).Nonempty := by
  -- The canonical fiber is definitionally the lifted witness type for `Z ∩ U`.
  change Nonempty (ULift (PLift (((Z : Set X) ∩ U).Nonempty))) ↔ ((Z : Set X) ∩ U).Nonempty
  constructor
  · rintro ⟨⟨⟨h⟩⟩⟩
    exact h
  · intro h
    exact ⟨⟨⟨h⟩⟩⟩

/-- The fiber of the point attached to `Z` over an open `U` is empty exactly when `U` is disjoint
from `Z`. -/
@[simp] theorem irreducibleClosedSitePoint_fiber_isEmpty_iff
    (Z : IrreducibleCloseds X) (U : Opens X) :
    IsEmpty ((irreducibleClosedSitePoint Z).fiber.obj U) ↔ Disjoint (Z : Set X) U := by
  -- The canonical fiber is empty precisely when no point of `Z` lies in `U`.
  change IsEmpty (ULift (PLift (((Z : Set X) ∩ U).Nonempty))) ↔ Disjoint (Z : Set X) U
  constructor
  · intro h
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    constructor
    · intro hx
      exact (h.false ⟨⟨⟨x, hx⟩⟩⟩).elim
    · intro hx
      simp at hx
  · intro h
    refine ⟨?_⟩
    intro s
    rcases s.down.down with ⟨x, hx⟩
    exact h.le_bot hx

private def sitePointEmptyFiberOpens (Φ : (Opens.grothendieckTopology X).Point) : Set (Opens X) :=
  {U | IsEmpty (Φ.fiber.obj U)}

private def sitePointEmptyFiberUnion (Φ : (Opens.grothendieckTopology X).Point) : Set X :=
  ⋃ U ∈ sitePointEmptyFiberOpens Φ, (U : Set X)

private def sitePointIrreducibleClosedCarrier (Φ : (Opens.grothendieckTopology X).Point) : Set X :=
  (sitePointEmptyFiberUnion Φ)ᶜ

-- Proof sketch: every member of `sitePointEmptyFiberOpens Φ` is open, so their union is open and
-- its complement is closed.
private theorem sitePointIrreducibleClosedCarrier_isClosed
    (Φ : (Opens.grothendieckTopology X).Point) :
    IsClosed (sitePointIrreducibleClosedCarrier Φ) := by
  -- The empty-fiber locus is a union of open subsets.
  simpa [sitePointIrreducibleClosedCarrier, sitePointEmptyFiberUnion] using
    (isOpen_iUnion fun U => isOpen_iUnion fun _ => U.2).isClosed_compl

/-- Helper for Example 7.33.6: every point of the opens site has a nonempty fiber over the top
open, because any element of the category of elements maps into `⊤`. -/
private theorem sitePoint_top_fiber_nonempty
    (Φ : (Opens.grothendieckTopology X).Point) :
    Nonempty (Φ.fiber.obj (⊤ : Opens X)) := by
  classical
  let z : Φ.fiber.Elements := Classical.choice
    (show Nonempty Φ.fiber.Elements from (inferInstance : IsCofiltered Φ.fiber.Elements).nonempty)
  -- Move any existing fiber element to the terminal open.
  exact ⟨Φ.fiber.map (homOfLE le_top) z.2⟩

/-- Helper for Example 7.33.6: if the fiber over `V` is empty, then the fiber over any smaller
open `U ⟶ V` is empty as well. -/
private theorem isEmpty_fiber_of_hom (Φ : (Opens.grothendieckTopology X).Point)
    {U V : Opens X} (i : U ⟶ V) (hV : IsEmpty (Φ.fiber.obj V)) :
    IsEmpty (Φ.fiber.obj U) := by
  -- Any element over `U` would map to an impossible element over `V`.
  refine ⟨?_⟩
  intro s
  exact hV.false (Φ.fiber.map i s)

/-- Helper for Example 7.33.6: if two opens have nonempty fibers for a site point, then their
intersection also has nonempty fiber. -/
private theorem nonempty_fiber_inf_of_nonempty
    (Φ : (Opens.grothendieckTopology X).Point) (U V : Opens X)
    (hU : Nonempty (Φ.fiber.obj U)) (hV : Nonempty (Φ.fiber.obj V)) :
    Nonempty (Φ.fiber.obj (U ⊓ V)) := by
  classical
  let f : U ⟶ (⊤ : Opens X) := homOfLE le_top
  let g : V ⟶ (⊤ : Opens X) := homOfLE le_top
  let t : (Types.pullbackCone (Φ.fiber.map f) (Φ.fiber.map g)).pt := by
    refine ⟨⟨Classical.choice hU, Classical.choice hV⟩, ?_⟩
    have hsub : Subsingleton (Φ.fiber.obj (⊤ : Opens X)) :=
      Φ.subsingleton_fiber_obj (homOfLE le_top) Limits.isTerminalTop
    exact Subsingleton.elim _ _
  -- Pullback preservation identifies the fiber over `U ⊓ V` with this pullback.
  have hs : Nonempty (Φ.fiber.obj (pullback f g)) := by
    refine ⟨(PreservesPullback.iso Φ.fiber f g).inv
      ((Types.pullbackIsoPullback (Φ.fiber.map f) (Φ.fiber.map g)).inv t)⟩
  have hpullback : pullback f g = U ⊓ V := by
    exact CompleteLattice.pullback_eq_inf f g
  exact hpullback ▸ hs

/-- Helper for Example 7.33.6: an open has empty fiber exactly when it is disjoint from the raw
carrier recovered from all empty-fiber opens. -/
private theorem isEmpty_fiber_iff_disjoint_sitePointIrreducibleClosedCarrier
    (Φ : (Opens.grothendieckTopology X).Point) (U : Opens X) :
    IsEmpty (Φ.fiber.obj U) ↔ Disjoint (sitePointIrreducibleClosedCarrier Φ) U := by
  constructor
  · intro hU
    -- If `U` itself has empty fiber, then every point of `U` lies in the excluded union.
    refine Set.disjoint_left.2 ?_
    intro x hxCarrier hxUmem
    have hxUnion : x ∈ sitePointEmptyFiberUnion Φ := by
      change x ∈ ⋃ U : Opens X, ⋃ (_ : U ∈ sitePointEmptyFiberOpens Φ), (U : Set X)
      exact Set.mem_iUnion.2 ⟨U, Set.mem_iUnion.2 ⟨hU, hxUmem⟩⟩
    exact hxCarrier hxUnion
  · intro hDisj
    -- Route correction: cover `U` by smaller opens whose fibers are already empty.
    by_contra hU
    rw [not_isEmpty_iff] at hU
    let R : Sieve U := {
      arrows := fun V i => IsEmpty (Φ.fiber.obj V)
      downward_closed := by
        intro Y Z f hf g
        exact isEmpty_fiber_of_hom Φ g hf
    }
    have hR : R ∈ Opens.grothendieckTopology X U := by
      intro x hxU
      have hxnot : x ∉ sitePointIrreducibleClosedCarrier Φ := by
        intro hxCarrier
        exact Set.disjoint_left.1 hDisj hxCarrier hxU
      have hxUnion : x ∈ sitePointEmptyFiberUnion Φ := by
        simpa [sitePointIrreducibleClosedCarrier] using hxnot
      rcases Set.mem_iUnion.1 hxUnion with ⟨V, hxV⟩
      rcases Set.mem_iUnion.1 hxV with ⟨hV, hxV⟩
      refine ⟨U ⊓ V, homOfLE inf_le_left, ?_, ⟨hxU, hxV⟩⟩
      exact isEmpty_fiber_of_hom Φ (homOfLE inf_le_right) hV
    rcases hU with ⟨s⟩
    rcases Φ.jointly_surjective R hR s with ⟨V, i, hi, t, ht⟩
    exact hi.false t

-- Proof sketch: use the finite-limit and covering properties of a site point on the opens site to
-- show that if the complementary closed subset were the union of two proper closed subsets, then
-- one of them would already equal the whole support.
private theorem sitePointIrreducibleClosedCarrier_isIrreducible
    (Φ : (Opens.grothendieckTopology X).Point) :
    IsIrreducible (sitePointIrreducibleClosedCarrier Φ) := by
  refine ⟨?_, ?_⟩
  · -- The top open cannot have empty fiber, so the recovered carrier is nonempty.
    by_contra hEmpty
    have hDisj : Disjoint (sitePointIrreducibleClosedCarrier Φ) (⊤ : Opens X) :=
      Set.disjoint_left.2 fun x hx _ ↦ hEmpty ⟨x, hx⟩
    have hTopEmpty :
        IsEmpty (Φ.fiber.obj (⊤ : Opens X)) :=
      (isEmpty_fiber_iff_disjoint_sitePointIrreducibleClosedCarrier Φ ⊤).2 hDisj
    exact not_isEmpty_iff.mpr (sitePoint_top_fiber_nonempty Φ) hTopEmpty
  · -- If the carrier is covered by two closed sets, one complement already has empty fiber.
    rw [isPreirreducible_iff_isClosed_union_isClosed]
    intro z₁ z₂ hz₁ hz₂ hcover
    let U₁ : Opens X := ⟨z₁ᶜ, hz₁.isOpen_compl⟩
    let U₂ : Opens X := ⟨z₂ᶜ, hz₂.isOpen_compl⟩
    have hDisjInf : Disjoint (sitePointIrreducibleClosedCarrier Φ) (U₁ ⊓ U₂ : Opens X) :=
      Set.disjoint_left.2 fun x hxS hxU ↦ by
        have hxCover : x ∈ z₁ ∪ z₂ := hcover hxS
        have hxNotCover : x ∉ z₁ ∪ z₂ := by
          rcases hxU with ⟨hxU₁, hxU₂⟩
          intro hx
          rcases hx with hx | hx
          · exact hxU₁ hx
          · exact hxU₂ hx
        exact (hxNotCover hxCover).elim
    have hInfEmpty :
        IsEmpty (Φ.fiber.obj (U₁ ⊓ U₂ : Opens X)) :=
      (isEmpty_fiber_iff_disjoint_sitePointIrreducibleClosedCarrier Φ (U₁ ⊓ U₂)).2 hDisjInf
    have hEither :
        IsEmpty (Φ.fiber.obj U₁) ∨ IsEmpty (Φ.fiber.obj U₂) := by
      by_cases hU₁ : IsEmpty (Φ.fiber.obj U₁)
      · exact Or.inl hU₁
      · by_cases hU₂ : IsEmpty (Φ.fiber.obj U₂)
        · exact Or.inr hU₂
        · exfalso
          rcases nonempty_fiber_inf_of_nonempty Φ U₁ U₂
              (not_isEmpty_iff.mp hU₁) (not_isEmpty_iff.mp hU₂) with ⟨s⟩
          exact hInfEmpty.false s
    rcases hEither with hU₁ | hU₂
    · left
      have hDisj :
          Disjoint (sitePointIrreducibleClosedCarrier Φ) U₁ :=
        (isEmpty_fiber_iff_disjoint_sitePointIrreducibleClosedCarrier Φ U₁).1 hU₁
      intro x hxS
      by_contra hxz₁
      exact Set.disjoint_left.1 hDisj hxS hxz₁
    · right
      have hDisj :
          Disjoint (sitePointIrreducibleClosedCarrier Φ) U₂ :=
        (isEmpty_fiber_iff_disjoint_sitePointIrreducibleClosedCarrier Φ U₂).1 hU₂
      intro x hxS
      by_contra hxz₂
      exact Set.disjoint_left.1 hDisj hxS hxz₂

/-- The irreducible closed subset canonically associated to a point of the opens site. -/
def sitePointIrreducibleClosed (Φ : (Opens.grothendieckTopology X).Point) :
    IrreducibleCloseds X :=
  ⟨sitePointIrreducibleClosedCarrier Φ,
    sitePointIrreducibleClosedCarrier_isIrreducible Φ,
    sitePointIrreducibleClosedCarrier_isClosed Φ⟩

/-- The irreducible closed subset recovered from `Φ` consists of those points all of whose open
neighbourhoods have nonempty fiber under `Φ`. -/
theorem coe_sitePointIrreducibleClosed (Φ : (Opens.grothendieckTopology X).Point) :
    (sitePointIrreducibleClosed Φ : Set X) =
      {x | ∀ U : Opens X, x ∈ U → Nonempty (Φ.fiber.obj U)} := by
  ext x
  change x ∈ sitePointIrreducibleClosedCarrier Φ ↔
      ∀ U : Opens X, x ∈ U → Nonempty (Φ.fiber.obj U)
  rw [sitePointIrreducibleClosedCarrier, Set.mem_compl_iff]
  constructor
  · intro hx U hxU
    -- If `x` lies in an empty-fiber open, then it lies in the excluded union.
    by_contra hU
    apply hx
    change x ∈ ⋃ U : Opens X, ⋃ (_ : U ∈ sitePointEmptyFiberOpens Φ), (U : Set X)
    exact Set.mem_iUnion.2 ⟨U, Set.mem_iUnion.2 ⟨⟨fun s ↦ hU ⟨s⟩⟩, hxU⟩⟩
  · intro hx hxUnion
    -- Any witness that `x` lies in the excluded union contradicts the claimed nonemptiness.
    rcases Set.mem_iUnion.1 hxUnion with ⟨U, hxUnionU⟩
    rcases Set.mem_iUnion.1 hxUnionU with ⟨hU, hxU⟩
    rcases hx U hxU with ⟨s⟩
    exact hU.false s

/-- Membership in the irreducible closed subset recovered from `Φ` is equivalent to every open
neighbourhood having nonempty fiber. -/
@[simp] theorem mem_sitePointIrreducibleClosed_iff
    (Φ : (Opens.grothendieckTopology X).Point) {x : X} :
    x ∈ sitePointIrreducibleClosed Φ ↔
      ∀ U : Opens X, x ∈ U → Nonempty (Φ.fiber.obj U) := by
  change x ∈ ((sitePointIrreducibleClosed Φ : Set X)) ↔
      ∀ U : Opens X, x ∈ U → Nonempty (Φ.fiber.obj U)
  rw [coe_sitePointIrreducibleClosed]
  simp

/-- An open is disjoint from the irreducible closed subset recovered from `Φ` exactly when its
fiber under `Φ` is empty. -/
@[simp] theorem isEmpty_fiber_iff_disjoint_sitePointIrreducibleClosed
    (Φ : (Opens.grothendieckTopology X).Point) (U : Opens X) :
    IsEmpty (Φ.fiber.obj U) ↔ Disjoint (sitePointIrreducibleClosed Φ : Set X) U := by
  -- This is the bundled version of the carrier-level emptiness/disjointness bridge.
  simpa [sitePointIrreducibleClosed] using
    isEmpty_fiber_iff_disjoint_sitePointIrreducibleClosedCarrier Φ U

/-- Helper for Example 7.33.6: two points of the opens site are isomorphic once they have the same
nonempty opens, because every fiber is a subsingleton. -/
private theorem iso_of_fiber_nonempty_iff
    {Φ Ψ : (Opens.grothendieckTopology X).Point}
    (h : ∀ U : Opens X, Nonempty (Φ.fiber.obj U) ↔ Nonempty (Ψ.fiber.obj U)) :
    Nonempty (Φ ≅ Ψ) := by
  classical
  refine ⟨{
    hom := {
      hom := {
        app := fun U s ↦ Classical.choice ((h U).2 ⟨s⟩)
        naturality := by
          intro U V f
          ext s
          let hsub : Subsingleton (Φ.fiber.obj V) :=
            Φ.subsingleton_fiber_obj (homOfLE le_top) Limits.isTerminalTop
          exact @Subsingleton.elim _ hsub _ _
      }
    }
    inv := {
      hom := {
        app := fun U s ↦ Classical.choice ((h U).1 ⟨s⟩)
        naturality := by
          intro U V f
          ext s
          let hsub : Subsingleton (Ψ.fiber.obj V) :=
            Ψ.subsingleton_fiber_obj (homOfLE le_top) Limits.isTerminalTop
          exact @Subsingleton.elim _ hsub _ _
      }
    }
    hom_inv_id := by
      ext U s
      let hsub : Subsingleton (Φ.fiber.obj U) :=
        Φ.subsingleton_fiber_obj (homOfLE le_top) Limits.isTerminalTop
      exact @Subsingleton.elim _ hsub _ _
    inv_hom_id := by
      ext U s
      let hsub : Subsingleton (Ψ.fiber.obj U) :=
        Ψ.subsingleton_fiber_obj (homOfLE le_top) Limits.isTerminalTop
      exact @Subsingleton.elim _ hsub _ _
  }⟩

/-- Helper for Example 7.33.6: the irreducible closed subset recovered from a point depends only on
its isomorphism class. -/
private theorem sitePointIrreducibleClosed_eq_of_iso
    {Φ Ψ : (Opens.grothendieckTopology X).Point} (e : Φ ≅ Ψ) :
    sitePointIrreducibleClosed Φ = sitePointIrreducibleClosed Ψ := by
  ext x
  constructor
  · intro hx
    -- Transport a neighborhood fiber witness across the inverse point morphism.
    have hx' := (mem_sitePointIrreducibleClosed_iff Φ).1 hx
    exact (mem_sitePointIrreducibleClosed_iff Ψ).2 fun U hxU ↦ by
      rcases hx' U hxU with ⟨s⟩
      exact ⟨e.inv.hom.app U s⟩
  · intro hx
    -- Transport a neighborhood fiber witness across the forward point morphism.
    have hx' := (mem_sitePointIrreducibleClosed_iff Ψ).1 hx
    exact (mem_sitePointIrreducibleClosed_iff Φ).2 fun U hxU ↦ by
      rcases hx' U hxU with ⟨s⟩
      exact ⟨e.hom.hom.app U s⟩

-- Proof sketch: the example constructs the support `Z` of a site point `Φ` as the complement of
-- the largest open with empty fiber and shows that `Φ` is uniquely determined, up to isomorphism,
-- by the singleton-or-empty functor attached to this irreducible closed subset.
/-- Example 7.33.6: a point of the opens site is isomorphic to the canonical site point attached
to the irreducible closed subset extracted from its empty fibers. -/
theorem opensSitePoint_iso_irreducibleClosedSitePoint
    (Φ : (Opens.grothendieckTopology X).Point) :
    Nonempty (Φ ≅ irreducibleClosedSitePoint (sitePointIrreducibleClosed Φ)) := by
  -- Compare the two points objectwise through the nonemptiness of their fibers.
  refine iso_of_fiber_nonempty_iff (Φ := Φ)
    (Ψ := irreducibleClosedSitePoint (sitePointIrreducibleClosed Φ)) ?_
  intro U
  constructor
  · intro hU
    have hNotDisjoint : ¬ Disjoint (sitePointIrreducibleClosed Φ : Set X) U := by
      intro hDisj
      have hEmpty : IsEmpty (Φ.fiber.obj U) :=
        (isEmpty_fiber_iff_disjoint_sitePointIrreducibleClosed Φ U).2 hDisj
      exact (not_isEmpty_iff.mpr hU) hEmpty
    exact (irreducibleClosedSitePoint_fiber_nonempty_iff (sitePointIrreducibleClosed Φ) U).2
      (Set.not_disjoint_iff_nonempty_inter.1 hNotDisjoint)
  · intro hU
    rcases
      (irreducibleClosedSitePoint_fiber_nonempty_iff (sitePointIrreducibleClosed Φ) U).1 hU with
        ⟨x, hxZ, hxU⟩
    exact (mem_sitePointIrreducibleClosed_iff Φ).1 hxZ U hxU

/-- Helper for Example 7.33.6: recovering the irreducible closed subset attached to the canonical
singleton-or-empty point returns the original subset. -/
private theorem sitePointIrreducibleClosed_of_irreducibleClosedSitePoint_aux
    (Z : IrreducibleCloseds X) :
    sitePointIrreducibleClosed (irreducibleClosedSitePoint Z) = Z := by
  -- Compare the two irreducible closed subsets by testing which opens have nonempty fiber.
  ext x
  constructor
  · intro hx
    by_contra hxZ
    let U : Opens X := ⟨(Z : Set X)ᶜ, Z.3.isOpen_compl⟩
    have hxU : x ∈ U := hxZ
    have hxFiber : Nonempty ((irreducibleClosedSitePoint Z).fiber.obj U) :=
      (mem_sitePointIrreducibleClosed_iff (irreducibleClosedSitePoint Z)).1 hx U hxU
    have hEmpty : IsEmpty ((irreducibleClosedSitePoint Z).fiber.obj U) := by
      refine (irreducibleClosedSitePoint_fiber_isEmpty_iff Z U).2 ?_
      exact disjoint_compl_right
    rcases hxFiber with ⟨s⟩
    exact hEmpty.false s
  · intro hxZ
    -- Any open neighbourhood of a point of `Z` meets `Z`, hence has nonempty canonical fiber.
    change x ∈ sitePointIrreducibleClosed (irreducibleClosedSitePoint Z)
    rw [mem_sitePointIrreducibleClosed_iff]
    intro U hxU
    exact (irreducibleClosedSitePoint_fiber_nonempty_iff Z U).2 ⟨x, hxZ, hxU⟩

/-- Companion uniqueness form of Example 7.33.6: points of the opens site `X_{Zar}`, and hence
points of `Sh(X)`, are in one-to-one correspondence up to isomorphism with irreducible closed
subsets of `X`. -/
theorem opensSitePoint_existsUnique_irreducibleClosedSubset
    (Φ : (Opens.grothendieckTopology X).Point) :
    ∃! Z : IrreducibleCloseds X, Nonempty (Φ ≅ irreducibleClosedSitePoint Z) := by
  refine ⟨sitePointIrreducibleClosed Φ, opensSitePoint_iso_irreducibleClosedSitePoint Φ, ?_⟩
  intro Z hZ
  rcases hZ with ⟨e⟩
  -- The extracted support is invariant under isomorphism, and the canonical point of `Z`
  -- recovers `Z` itself.
  exact ((sitePointIrreducibleClosed_eq_of_iso e).trans
    (sitePointIrreducibleClosed_of_irreducibleClosedSitePoint_aux Z)).symm

-- Proof sketch: for the singleton-or-empty point attached to `Z`, the largest open with empty
-- fiber is exactly `X \ Z`, so the complementary irreducible closed subset recovered by the
-- construction is `Z` itself.
/-- Recovering the irreducible closed subset attached to its own singleton-or-empty site point
returns the original subset. -/
theorem sitePointIrreducibleClosed_of_irreducibleClosedSitePoint (Z : IrreducibleCloseds X) :
    sitePointIrreducibleClosed (irreducibleClosedSitePoint Z) = Z := by
  exact sitePointIrreducibleClosed_of_irreducibleClosedSitePoint_aux Z

-- Proof sketch: if `x` is a generic point of `Z`, then an open subset meets `Z` if and only if
-- it contains `x`, so the singleton-or-empty point attached to `Z` and the standard site point
-- attached to `x` have isomorphic fiber functors.
/-- If `x` is a generic point of an irreducible closed subset `Z`, then the site point attached to
`Z` is isomorphic to the standard opens-site point attached to `x`. -/
theorem irreducibleClosedSitePoint_iso_pointGrothendieckTopology_of_isGenericPoint
    {x : X} {Z : IrreducibleCloseds X} (hx : IsGenericPoint x Z) :
    Nonempty (irreducibleClosedSitePoint Z ≅ Opens.pointGrothendieckTopology x) := by
  -- The generic-point criterion says that `U` meets `Z` exactly when `x ∈ U`.
  refine iso_of_fiber_nonempty_iff (Φ := irreducibleClosedSitePoint Z)
    (Ψ := Opens.pointGrothendieckTopology x) ?_
  intro U
  constructor
  · intro hU
    have hMeet : ((Z : Set X) ∩ U).Nonempty :=
      (irreducibleClosedSitePoint_fiber_nonempty_iff Z U).1 hU
    have hxU : x ∈ U := (hx.mem_open_set_iff U.2).2 hMeet
    simpa [Opens.pointGrothendieckTopology] using hxU
  · intro hU
    have hxU : x ∈ U := by
      simpa [Opens.pointGrothendieckTopology] using hU
    exact (irreducibleClosedSitePoint_fiber_nonempty_iff Z U).2
      ((hx.mem_open_set_iff U.2).1 hxU)

attribute [local instance] specializationOrder

-- Proof sketch: apply the irreducible-closed classification theorem, then use sobriety to identify
-- the resulting irreducible closed subset with the closure of a unique generic point.
/-- In a sober topological space, every point of the opens site is isomorphic to the standard site
point attached to its canonically associated point of `X`. -/
theorem opensSitePoint_iso_pointGrothendieckTopology_of_quasiSober
    [T0Space X] [QuasiSober X] (Φ : (Opens.grothendieckTopology X).Point) :
    Nonempty (Φ ≅ Opens.pointGrothendieckTopology
      (irreducibleSetEquivPoints (sitePointIrreducibleClosed Φ))) := by
  -- Compare `Φ` first with its recovered irreducible closed subset, then use its generic point.
  let Z := sitePointIrreducibleClosed Φ
  have hgeneric : IsGenericPoint (irreducibleSetEquivPoints Z) (Z : Set X) := by
    simpa [irreducibleSetEquivPoints, Z] using Z.2.isGenericPoint_genericPoint Z.3
  rcases opensSitePoint_iso_irreducibleClosedSitePoint Φ with ⟨e₁⟩
  rcases irreducibleClosedSitePoint_iso_pointGrothendieckTopology_of_isGenericPoint
      (x := irreducibleSetEquivPoints Z) (Z := Z) hgeneric with ⟨e₂⟩
  exact ⟨e₁ ≪≫ e₂⟩

/-- Companion uniqueness form of Example 7.33.6 in the sober case. -/
theorem opensSitePoint_existsUnique_spacePoint [T0Space X] [QuasiSober X]
    (Φ : (Opens.grothendieckTopology X).Point) :
    ∃! x : X, Nonempty (Φ ≅ Opens.pointGrothendieckTopology x) := by
  refine ⟨irreducibleSetEquivPoints (sitePointIrreducibleClosed Φ),
    opensSitePoint_iso_pointGrothendieckTopology_of_quasiSober Φ, ?_⟩
  intro y hy
  rcases opensSitePoint_iso_pointGrothendieckTopology_of_quasiSober Φ with ⟨e₁⟩
  rcases hy with ⟨e₂⟩
  let e : Opens.pointGrothendieckTopology (irreducibleSetEquivPoints (sitePointIrreducibleClosed Φ))
      ≅ Opens.pointGrothendieckTopology y := e₁.symm ≪≫ e₂
  have hxy :
      irreducibleSetEquivPoints (sitePointIrreducibleClosed Φ) ⤳ y :=
    Opens.pointGrothendieckTopologyHomEquiv e.hom
  have hyx :
      y ⤳ irreducibleSetEquivPoints (sitePointIrreducibleClosed Φ) :=
    Opens.pointGrothendieckTopologyHomEquiv e.inv
  exact (hxy.antisymm hyx).eq.symm

end CategoryTheory

/-! ### Example_7_33_7 (from Chap07) -/
open CategoryTheory Limits Opposite
open GrothendieckTopology.Point

universe u

namespace CategoryTheory

noncomputable section

open scoped MorphismOfTopoiIn

variable (G : Type u) [Group G]

/- Domain-style sampling for Example 7.33.7:
- sampled owner declarations:
  `Point.skyscraperSheafFunctor`,
  `Point.toToposPoint_pointPushforwardIso`,
  `sheafSectionsOnLeftRegularFunctor`,
  `gSetForgetfulPointMapMulAction`;
- core/canonical owners:
  the direct-image/skyscraper owner of the point `gSetForgetfulPoint G`,
  together with the left-regular-sections functor from Proposition 7.9.1;
- source-facing declarations in this file:
  the fiber comparison `p⁻¹(p_* S) ≃ Map(G, S)` and the resulting action-level description of
  `p_* S`;
- primitive data:
  the point `gSetForgetfulPoint G`, its left regular object, and the chapter's canonical
  right-translation action on `G → S`;
- derived API:
  the objectwise `Map(G, S)` equivalence and the section/counit comparison theorems.
-/

private noncomputable abbrev gSetForgetfulPoint_pushforwardObj
    (S : Type u) :
    Sheaf (Action.jointlySurjectiveTopology G) (Type u) :=
  ((gSetForgetfulPoint G).toToposPoint).typePushforward.obj S

/-- The value of `p_* S` on the left regular `G`-set is canonically the set `Map(G, S)`. -/
private noncomputable abbrev pushforwardLeftRegularObjEquiv
    (S : Type u) :
    ((gSetForgetfulPoint_pushforwardObj G S).1.obj (op (Action.leftRegular G))) ≃
      (G → S) :=
  let Φ := gSetForgetfulPoint G
  let e' :
      ((gSetForgetfulPoint_pushforwardObj G S).1.obj (op (Action.leftRegular G))) ≃
        (Φ.skyscraperPresheaf S).obj (op (Action.leftRegular G)) :=
    (((evaluation (Action (Type u) G)ᵒᵖ (Type u)).obj (op (Action.leftRegular G))).mapIso
      ((sheafToPresheaf _ _).mapIso
        ((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso Φ).app S))).toEquiv
  e'.trans
    (Types.productIso (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S)).toEquiv

/-- The canonical map `Map(G, S) → p^{-1}(p_* S)` obtained from the generator `1 ∈ G` of the left
regular `G`-set. -/
noncomputable def gSetForgetfulPoint_pushforwardFiberMap
    (S : Type u) (ψ : G → S) :
    ((gSetForgetfulPoint G).toToposPoint).typeInverseImage.obj
      (((gSetForgetfulPoint G).toToposPoint).typePushforward.obj S) :=
    let Φ := gSetForgetfulPoint G
    let F := gSetForgetfulPoint_pushforwardObj G S
    let x :
        Φ.sheafFiber.obj F :=
      Φ.toPresheafFiber (Action.leftRegular G)
        ((1 : G) : Φ.fiber.obj (Action.leftRegular G))
        F.1
        ((pushforwardLeftRegularObjEquiv G S).symm ψ)
    ((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso Φ).app F).inv x

/-- Helper for Example 7.33.7: the distinguished object `({}_G G, 1)` in the element category of
the forgetful fiber functor. -/
private noncomputable abbrev leftRegularBaseObj :
    (gSetForgetfulPoint G).fiber.Elements :=
  (gSetForgetfulPoint G).fiber.elementsMk (Action.leftRegular G) ((1 : G) : G)

/-- Helper for Example 7.33.7: the orbit map out of the left regular `G`-set through a chosen
point of a `G`-set. -/
private def left_regular_hom_of_point {U : Action (Type u) G} (u : U.V) :
    Action.leftRegular G ⟶ U where
  hom := fun g ↦ U.ρ (show G from g) u
  comm := by
    -- Multiplication in the left regular action records the orbit relation.
    intro g
    ext h
    exact congrFun (MonoidHom.map_mul U.ρ (show G from g) (show G from h)) u

/-- Helper for Example 7.33.7: the point `(Action.leftRegular G, 1)` is initial in the element
category of the forgetful point. -/
private noncomputable def left_regular_one_isInitial :
    IsInitial (leftRegularBaseObj G) := by
  letI : ∀ Y : (gSetForgetfulPoint G).fiber.Elements, Unique (leftRegularBaseObj G ⟶ Y) :=
    fun Y ↦
      let f0 : leftRegularBaseObj G ⟶ Y := ⟨left_regular_hom_of_point G Y.2, by
        -- The orbit map sends `1` to the chosen point.
        change (left_regular_hom_of_point G Y.2).hom ((1 : G) : G) = Y.2
        simp [left_regular_hom_of_point]⟩
      { default := f0
        uniq := by
          intro f
          apply CategoryOfElements.ext (gSetForgetfulPoint G).fiber f f0
          -- An equivariant map out of the left regular action is determined by the value at `1`.
          apply Action.hom_ext
          ext g
          have hbase : f.1.hom ((1 : G) : G) = Y.2 := f.2
          have hcomm := congrFun (f.1.comm (show G from g)) (show G from ((1 : G) : G))
          simp only [types_comp_apply] at hcomm
          rw [hbase] at hcomm
          simpa [f0, left_regular_hom_of_point] using hcomm }
  exact IsInitial.ofUnique _

/-- Helper for Example 7.33.7: the opposite of `({}_G G, 1)` is terminal in the opposite element
category. -/
private noncomputable abbrev leftRegularTerminalObj :
    (gSetForgetfulPoint G).fiber.Elementsᵒᵖ :=
  op (leftRegularBaseObj G)

/-- Helper for Example 7.33.7: the terminal object in the opposite element category controlling
the fiber colimit. -/
private noncomputable def leftRegularTerminal :
    IsTerminal (leftRegularTerminalObj G) :=
  terminalOpOfInitial (left_regular_one_isInitial G)

/-- Helper for Example 7.33.7: the presheaf fiber at the forgetful point is evaluation on the
left regular `G`-set. -/
private noncomputable def gSetForgetfulPoint_presheafFiberObjIso_leftRegular
    (P : (Action (Type u) G)ᵒᵖ ⥤ Type u) :
    (gSetForgetfulPoint G).presheafFiber.obj P ≅ P.obj (op (Action.leftRegular G)) := by
  let Q := (CategoryOfElements.π (gSetForgetfulPoint G).fiber).op ⋙ P
  change colimit Q ≅ Q.obj (leftRegularTerminalObj G)
  exact IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (colimitOfDiagramTerminal
    (leftRegularTerminal G) Q)

/-- Helper for Example 7.33.7: the canonical map from the left regular section into the fiber
becomes the identity after the evaluation comparison. -/
private lemma toPresheafFiber_gSetForgetfulPoint_presheafFiberObjIso_leftRegular_hom
    (P : (Action (Type u) G)ᵒᵖ ⥤ Type u) :
    (gSetForgetfulPoint G).toPresheafFiber (Action.leftRegular G)
        ((1 : G) : (gSetForgetfulPoint G).fiber.obj (Action.leftRegular G)) P ≫
      (gSetForgetfulPoint_presheafFiberObjIso_leftRegular G P).hom =
        𝟙 (P.obj (op (Action.leftRegular G))) := by
  -- The defining colimit leg from the terminal object becomes the identity map.
  simpa [gSetForgetfulPoint_presheafFiberObjIso_leftRegular, GrothendieckTopology.Point.presheafFiber,
    leftRegularTerminalObj, leftRegularTerminal] using
    (colimit.comp_coconePointUniqueUpToIso_hom
      (hc := colimitOfDiagramTerminal (leftRegularTerminal G)
        ((CategoryOfElements.π (gSetForgetfulPoint G).fiber).op ⋙ P))
      (op (leftRegularBaseObj G)))

/-- Helper for Example 7.33.7: the fiber leg at any point factors through the orbit map from
`({}_G G, 1)`. -/
private lemma toPresheafFiber_gSetForgetfulPoint_presheafFiberObjIso_leftRegular_hom_apply
    (P : (Action (Type u) G)ᵒᵖ ⥤ Type u) (X : Action (Type u) G)
    (x : (gSetForgetfulPoint G).fiber.obj X) :
    (gSetForgetfulPoint G).toPresheafFiber X x P ≫
      (gSetForgetfulPoint_presheafFiberObjIso_leftRegular G P).hom =
        P.map (left_regular_hom_of_point G x).op := by
  have hw :
      P.map (left_regular_hom_of_point G x).op ≫
          (gSetForgetfulPoint G).toPresheafFiber (Action.leftRegular G)
            ((1 : G) : (gSetForgetfulPoint G).fiber.obj (Action.leftRegular G)) P =
        (gSetForgetfulPoint G).toPresheafFiber X x P := by
    have hx :
        (gSetForgetfulPoint G).fiber.map (left_regular_hom_of_point G x)
          ((1 : G) : (gSetForgetfulPoint G).fiber.obj (Action.leftRegular G)) = x := by
      change X.ρ 1 x = x
      exact congrFun (MonoidHom.map_one X.ρ) x
    simpa [hx] using
      (gSetForgetfulPoint G).toPresheafFiber_w (left_regular_hom_of_point G x)
        ((1 : G) : (gSetForgetfulPoint G).fiber.obj (Action.leftRegular G)) P
  -- Move the comparison to `({}_G G, 1)` using the canonical orbit map.
  calc
    (gSetForgetfulPoint G).toPresheafFiber X x P ≫
        (gSetForgetfulPoint_presheafFiberObjIso_leftRegular G P).hom =
      P.map (left_regular_hom_of_point G x).op ≫
        (gSetForgetfulPoint G).toPresheafFiber (Action.leftRegular G)
          ((1 : G) : (gSetForgetfulPoint G).fiber.obj (Action.leftRegular G)) P ≫
          (gSetForgetfulPoint_presheafFiberObjIso_leftRegular G P).hom := by
            rw [← hw, Category.assoc]
    _ = P.map (left_regular_hom_of_point G x).op := by
      rw [toPresheafFiber_gSetForgetfulPoint_presheafFiberObjIso_leftRegular_hom]
      simp

/-- Helper for Example 7.33.7: the fiber functor on sheaves is evaluation on the left regular
`G`-set. -/
private noncomputable def gSetForgetfulPoint_sheafFiberIso_leftRegular :
    (gSetForgetfulPoint G).sheafFiber ≅
      sheafToPresheaf (Action.jointlySurjectiveTopology G) (Type u) ⋙
        (evaluation (Action (Type u) G)ᵒᵖ (Type u)).obj (op (Action.leftRegular G)) := by
  simpa [GrothendieckTopology.Point.sheafFiber] using
    Functor.isoWhiskerLeft
      (sheafToPresheaf (Action.jointlySurjectiveTopology G) (Type u))
      (NatIso.ofComponents
        (fun P ↦ gSetForgetfulPoint_presheafFiberObjIso_leftRegular G P)
        (by
          intro P Q f
          apply (gSetForgetfulPoint G).presheafFiber_hom_ext
          intro X x
          rw [toPresheafFiber_naturality_assoc]
          calc
            (f.app (op X) ≫
                (gSetForgetfulPoint G).toPresheafFiber X x Q) ≫
                  (gSetForgetfulPoint_presheafFiberObjIso_leftRegular G Q).hom =
                f.app (op X) ≫
                  ((gSetForgetfulPoint G).toPresheafFiber X x Q ≫
                    (gSetForgetfulPoint_presheafFiberObjIso_leftRegular G Q).hom) := by
                      simp [Category.assoc]
            _ = f.app (op X) ≫ Q.map (show Action.leftRegular G ⟶ X from
                  left_regular_hom_of_point G x).op := by
                  rw [toPresheafFiber_gSetForgetfulPoint_presheafFiberObjIso_leftRegular_hom_apply]
            _ = P.map (show Action.leftRegular G ⟶ X from left_regular_hom_of_point G x).op ≫
                  ((evaluation (Action (Type u) G)ᵒᵖ (Type u)).obj
                    (op (Action.leftRegular G))).map f := by
                  simpa using
                    (NatTrans.naturality f
                      (show op X ⟶ op (Action.leftRegular G) from
                        (show Action.leftRegular G ⟶ X from left_regular_hom_of_point G x).op)).symm
            _ = (gSetForgetfulPoint G).toPresheafFiber X x P ≫
                  (gSetForgetfulPoint_presheafFiberObjIso_leftRegular G P).hom ≫
                    ((evaluation (Action (Type u) G)ᵒᵖ (Type u)).obj
                      (op (Action.leftRegular G))).map f := by
                  simpa [Category.assoc] using
                    congrArg
                      (fun k ↦
                        k ≫ ((evaluation (Action (Type u) G)ᵒᵖ (Type u)).obj
                          (op (Action.leftRegular G))).map f)
                      (toPresheafFiber_gSetForgetfulPoint_presheafFiberObjIso_leftRegular_hom_apply
                        (G := G) P X x).symm))

/-- Helper for Example 7.33.7: the distinguished left-regular leg becomes the identity after the
sheaf-fiber comparison. -/
private lemma toPresheafFiber_gSetForgetfulPoint_sheafFiberIso_leftRegular_hom
    (F : Sheaf (Action.jointlySurjectiveTopology G) (Type u)) :
    (gSetForgetfulPoint G).toPresheafFiber (Action.leftRegular G)
        ((1 : G) : (gSetForgetfulPoint G).fiber.obj (Action.leftRegular G)) F.1 ≫
      ((gSetForgetfulPoint_sheafFiberIso_leftRegular G).app F).hom =
        𝟙 (F.1.obj (op (Action.leftRegular G))) := by
  -- This is the sheaf-level restatement of the presheaf comparison above.
  simpa [gSetForgetfulPoint_sheafFiberIso_leftRegular] using
    toPresheafFiber_gSetForgetfulPoint_presheafFiberObjIso_leftRegular_hom (G := G) F.1

/-- Helper for Example 7.33.7: the point fiber of `p_* S` is canonically the function type
`Map(G, S)`. -/
private noncomputable def gSetForgetfulPoint_pushforwardFiberIso
    (S : Type u) :
    ((gSetForgetfulPoint G).toToposPoint).typeInverseImage.obj
      (((gSetForgetfulPoint G).toToposPoint).typePushforward.obj S) ≅
      (G → S) :=
  ((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso
      (gSetForgetfulPoint G)).app (gSetForgetfulPoint_pushforwardObj G S)) ≪≫
    ((gSetForgetfulPoint_sheafFiberIso_leftRegular G).app
      (gSetForgetfulPoint_pushforwardObj G S)) ≪≫
    (pushforwardLeftRegularObjEquiv G S).toIso

/-- Helper for Example 7.33.7: the explicit map `Map(G, S) → p^{-1}(p_* S)` is the inverse of
the canonical fiber comparison. -/
private theorem gSetForgetfulPoint_pushforwardFiberIso_hom_map
    (S : Type u) (ψ : G → S) :
    (gSetForgetfulPoint_pushforwardFiberIso G S).hom
      (gSetForgetfulPoint_pushforwardFiberMap G S ψ) = ψ := by
  let Φ := gSetForgetfulPoint G
  let F := gSetForgetfulPoint_pushforwardObj G S
  -- Evaluate the composite comparison on the distinguished left-regular section.
  have hcomp :=
    congrArg
      (fun k : F.1.obj (op (Action.leftRegular G)) ⟶
          F.1.obj (op (Action.leftRegular G)) ↦
        k ((pushforwardLeftRegularObjEquiv G S).symm ψ))
      (toPresheafFiber_gSetForgetfulPoint_sheafFiberIso_leftRegular_hom (G := G) F)
  dsimp [gSetForgetfulPoint_pushforwardFiberIso, gSetForgetfulPoint_pushforwardFiberMap, Φ, F]
  calc
    (pushforwardLeftRegularObjEquiv G S)
        (((gSetForgetfulPoint_sheafFiberIso_leftRegular G).hom.app F)
          (((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso Φ).app F).hom
            (((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso Φ).app F).inv
              ((gSetForgetfulPoint G).toPresheafFiber (Action.leftRegular G)
                ((1 : G) : (gSetForgetfulPoint G).fiber.obj (Action.leftRegular G))
                F.1
                ((pushforwardLeftRegularObjEquiv G S).symm ψ))))) =
      (pushforwardLeftRegularObjEquiv G S)
        (((gSetForgetfulPoint_sheafFiberIso_leftRegular G).hom.app F)
          ((gSetForgetfulPoint G).toPresheafFiber (Action.leftRegular G)
            ((1 : G) : (gSetForgetfulPoint G).fiber.obj (Action.leftRegular G))
            F.1
            ((pushforwardLeftRegularObjEquiv G S).symm ψ))) := by
              simp
    _ = ψ := by
      exact ((pushforwardLeftRegularObjEquiv G S).apply_eq_iff_eq_symm_apply).2 hcomp

-- Proof sketch: the sheaf condition on the surjective site identifies the stalk of the
-- skyscraper sheaf `p_* S` with its value on the left regular `G`-set, and the chosen generator
-- `1 ∈ G` yields the inverse direction explicitly.
/-- Example 7.33.7: the canonical map `Map(G, S) → p^{-1}(p_* S)` is bijective. -/
theorem gSetForgetfulPoint_pushforwardFiberMap_bijective
    (S : Type u) :
    Function.Bijective (gSetForgetfulPoint_pushforwardFiberMap G S) :=
  by
    refine ⟨?_, ?_⟩
    · -- The canonical fiber comparison is a left inverse to the explicit map.
      intro ψ₁ ψ₂ h
      have h' := congrArg (fun x ↦ (gSetForgetfulPoint_pushforwardFiberIso G S).hom x) h
      simpa [gSetForgetfulPoint_pushforwardFiberIso_hom_map] using h'
    · -- Surjectivity follows by evaluating an arbitrary fiber point through the comparison iso.
      intro x
      refine ⟨(gSetForgetfulPoint_pushforwardFiberIso G S).hom x, ?_⟩
      have hsurj :
          (gSetForgetfulPoint_pushforwardFiberIso G S).hom
            (gSetForgetfulPoint_pushforwardFiberMap G S
              ((gSetForgetfulPoint_pushforwardFiberIso G S).hom x)) =
            (gSetForgetfulPoint_pushforwardFiberIso G S).hom x := by
        simpa using
          gSetForgetfulPoint_pushforwardFiberIso_hom_map G S
            ((gSetForgetfulPoint_pushforwardFiberIso G S).hom x)
      exact (gSetForgetfulPoint_pushforwardFiberIso G S).toEquiv.injective hsurj

/-- The canonical identification `p^{-1}(p_* S) = Map(G, S)` from Example 7.33.7. -/
noncomputable def gSetForgetfulPoint_pushforwardFiberEquiv
    (S : Type u) :
    ((gSetForgetfulPoint G).toToposPoint).typeInverseImage.obj
      (((gSetForgetfulPoint G).toToposPoint).typePushforward.obj S) ≃
      (G → S) :=
  (Equiv.ofBijective
    (gSetForgetfulPoint_pushforwardFiberMap G S)
    (gSetForgetfulPoint_pushforwardFiberMap_bijective G S)).symm

@[simp] theorem gSetForgetfulPoint_pushforwardFiberEquiv_symm_apply
    (S : Type u) (ψ : G → S) :
    (gSetForgetfulPoint_pushforwardFiberEquiv G S).symm ψ =
      gSetForgetfulPoint_pushforwardFiberMap G S ψ :=
  rfl

/-- Helper for Example 7.33.7: the `PUnit`-valued explicit fiber map agrees with the canonical
section from Lemma 7.32.9. -/
private theorem gSetForgetfulPoint_pushforwardFiberMap_punit :
    gSetForgetfulPoint_pushforwardFiberMap G PUnit (fun _ ↦ PUnit.unit) =
      MorphismOfTopoiIn.pointPushforwardFiberSection
        ((gSetForgetfulPoint G).toToposPoint) PUnit PUnit.unit := by
  -- The `PUnit`-valued fiber is a subsingleton, so the explicit map and the canonical section coincide.
  apply (gSetForgetfulPoint_pushforwardFiberIso G PUnit).toEquiv.injective
  exact Subsingleton.elim _ _

/-- Helper for Example 7.33.7: on left-regular sections, the pushforward along a map of sets acts
coordinatewise under the explicit `Map(G, -)` identification. -/
private theorem pushforwardLeftRegularObjEquiv_symm_map
    {A B : Type u} (f : A → B) (ψ : G → A) :
    ((((gSetForgetfulPoint G).toToposPoint).typePushforward.map f).hom.app
      (op (Action.leftRegular G)))
      ((pushforwardLeftRegularObjEquiv G A).symm ψ) =
        (pushforwardLeftRegularObjEquiv G B).symm (fun x ↦ f (ψ x)) := by
  let Φ := gSetForgetfulPoint G
  -- Transport naturality of `toToposPoint_pointPushforwardIso` to the left regular component.
  have hnat :=
    congrArg
      (fun k :
        ((gSetForgetfulPoint_pushforwardObj G A).1.obj (op (Action.leftRegular G))) →
          ((Φ.skyscraperPresheaf B).obj (op (Action.leftRegular G))) ↦
        k ((pushforwardLeftRegularObjEquiv G A).symm ψ))
      (congrArg
        (fun η :
          gSetForgetfulPoint_pushforwardObj G A ⟶ Φ.skyscraperSheafFunctor.obj B ↦
          (((evaluation (Action (Type u) G)ᵒᵖ (Type u)).obj (op (Action.leftRegular G))).map
            ((sheafToPresheaf (Action.jointlySurjectiveTopology G) (Type u)).map η)))
        ((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso Φ).hom.naturality f))
  -- After this rewrite, the skyscraper map is coordinatewise application of `f`.
  apply (pushforwardLeftRegularObjEquiv G B).injective
  ext x
  have hnat_apply :=
    congrArg
      (fun z : ((Φ.skyscraperPresheaf B).obj (op (Action.leftRegular G))) ↦
        ((Types.productIso
          (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ B)).hom z) x)
      hnat
  calc
    (pushforwardLeftRegularObjEquiv G B)
        ((((gSetForgetfulPoint G).toToposPoint).typePushforward.map f).hom.app
          (op (Action.leftRegular G))
          ((pushforwardLeftRegularObjEquiv G A).symm ψ))
        x =
      f ((pushforwardLeftRegularObjEquiv G A) ((pushforwardLeftRegularObjEquiv G A).symm ψ) x) := by
        simpa [pushforwardLeftRegularObjEquiv, Φ, Category.assoc, Types.productIso_hom_comp_eval,
          Types.productIso_inv_comp_π] using hnat_apply
    _ = f (ψ x) := by
      rw [Equiv.apply_symm_apply]
    _ = (pushforwardLeftRegularObjEquiv G B)
          ((pushforwardLeftRegularObjEquiv G B).symm (fun x ↦ f (ψ x))) x := by
            rw [Equiv.apply_symm_apply]

/-- Helper for Example 7.33.7: the explicit fiber map is natural in the set variable. -/
private theorem gSetForgetfulPoint_pushforwardFiberMap_naturality
    {A B : Type u} (f : A → B) (ψ : G → A) :
    ((gSetForgetfulPoint G).toToposPoint).typeInverseImage.map
      (((gSetForgetfulPoint G).toToposPoint).typePushforward.map f)
      (gSetForgetfulPoint_pushforwardFiberMap G A ψ) =
        gSetForgetfulPoint_pushforwardFiberMap G B (fun x ↦ f (ψ x)) := by
  let Φ := gSetForgetfulPoint G
  let FA := gSetForgetfulPoint_pushforwardObj G A
  let FB := gSetForgetfulPoint_pushforwardObj G B
  have hnat :=
    congrArg
      (fun k : Φ.sheafFiber.obj FA ⟶ Φ.toToposPoint.typeInverseImage.obj FB ↦
        k (Φ.toPresheafFiber (Action.leftRegular G)
          ((1 : G) : Φ.fiber.obj (Action.leftRegular G))
          FA.1
          ((pushforwardLeftRegularObjEquiv G A).symm ψ)))
      ((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso Φ).inv.naturality
        (Φ.toToposPoint.typePushforward.map f))
  have hfiber :
      Φ.sheafFiber.map (Φ.toToposPoint.typePushforward.map f)
        (Φ.toPresheafFiber (Action.leftRegular G)
          ((1 : G) : Φ.fiber.obj (Action.leftRegular G))
          FA.1
          ((pushforwardLeftRegularObjEquiv G A).symm ψ)) =
      Φ.toPresheafFiber (Action.leftRegular G)
        ((1 : G) : Φ.fiber.obj (Action.leftRegular G))
        FB.1
        ((pushforwardLeftRegularObjEquiv G B).symm (fun x ↦ f (ψ x))) := by
    have hnat_fiber :=
      congrArg
        (fun k :
          FA.1.obj (op (Action.leftRegular G)) ⟶ Φ.sheafFiber.obj FB ↦
          k ((pushforwardLeftRegularObjEquiv G A).symm ψ))
        (Φ.toPresheafFiber_naturality (Φ.toToposPoint.typePushforward.map f).hom
          (Action.leftRegular G)
          ((1 : G) : Φ.fiber.obj (Action.leftRegular G)))
    calc
      Φ.sheafFiber.map (Φ.toToposPoint.typePushforward.map f)
          (Φ.toPresheafFiber (Action.leftRegular G)
            ((1 : G) : Φ.fiber.obj (Action.leftRegular G))
            FA.1
            ((pushforwardLeftRegularObjEquiv G A).symm ψ)) =
        Φ.toPresheafFiber (Action.leftRegular G)
          ((1 : G) : Φ.fiber.obj (Action.leftRegular G))
          FB.1
          ((((Φ.toToposPoint.typePushforward.map f).hom.app
            (op (Action.leftRegular G)))
            ((pushforwardLeftRegularObjEquiv G A).symm ψ))) := by
              simpa [GrothendieckTopology.Point.sheafFiber, FA, FB, Category.assoc] using hnat_fiber
      _ = Φ.toPresheafFiber (Action.leftRegular G)
            ((1 : G) : Φ.fiber.obj (Action.leftRegular G))
            FB.1
            ((pushforwardLeftRegularObjEquiv G B).symm (fun x ↦ f (ψ x))) := by
              rw [pushforwardLeftRegularObjEquiv_symm_map]
  -- The inverse-image comparison transports the stalk map to the sheaf-fiber map.
  exact hnat.symm.trans <|
    congrArg (((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso Φ).app FB).inv) hfiber

/-- Helper for Example 7.33.7: pullback along right multiplication becomes precomposition by
`x ↦ x * g` under the explicit `Map(G, S)` identification. -/
private theorem pushforwardLeftRegularObjEquiv_rightMul
    (S : Type u) (g : G)
    (ψ : (gSetForgetfulPoint_pushforwardObj G S).1.obj (op (Action.leftRegular G))) :
    pushforwardLeftRegularObjEquiv G S
        ((gSetForgetfulPoint_pushforwardObj G S).1.map
          (op (gSetForgetfulPointLeftRegularRightMul G g)) ψ) =
      fun x ↦ (pushforwardLeftRegularObjEquiv G S ψ) (x * g) := by
  let Φ := gSetForgetfulPoint G
  have hnat :=
    congrArg
      (fun k :
        ((gSetForgetfulPoint_pushforwardObj G S).1.obj (op (Action.leftRegular G))) →
          ((Φ.skyscraperPresheaf S).obj (op (Action.leftRegular G))) ↦
        k ψ)
      (((sheafToPresheaf (Action.jointlySurjectiveTopology G) (Type u)).mapIso
        ((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso Φ).app S)).hom.naturality
          (op (gSetForgetfulPointLeftRegularRightMul G g)))
  have hnat_apply (x : G) :=
    congrArg
      (fun z : ((Φ.skyscraperPresheaf S).obj (op (Action.leftRegular G))) ↦
        ((Types.productIso
          (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S)).hom z) x)
      hnat
  let z :
      ∏ᶜ fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S :=
    (((Φ.toToposPoint_pointPushforwardIso.hom.app S).hom.app
      (op (Action.leftRegular G))) ψ)
  -- On the skyscraper side, pullback along right multiplication just shifts the coordinate index.
  ext x
  have hπ_mor :
      ((Pi.map'
        (Φ.fiber.map (gSetForgetfulPointLeftRegularRightMul G g))
        (fun _ ↦ (𝟙 S : S ⟶ S))) :
          (∏ᶜ fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S) ⟶
            ∏ᶜ fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S) ≫
        Pi.π (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S) x =
      Pi.π (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S)
        ((Φ.fiber.map (gSetForgetfulPointLeftRegularRightMul G g)) x) := by
    simpa using
      (Pi.map'_comp_π
        (f := fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S)
        (g := fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S)
        (p := Φ.fiber.map (gSetForgetfulPointLeftRegularRightMul G g))
        (q := fun _ ↦ (𝟙 S : S ⟶ S)) x)
  have hπ :
      Pi.π (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S) x
          (((Pi.map'
            (Φ.fiber.map (gSetForgetfulPointLeftRegularRightMul G g))
            (fun _ ↦ 𝟙 S)) :
            (∏ᶜ fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S) ⟶
              ∏ᶜ fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S) z) =
        Pi.π (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S)
          ((Φ.fiber.map (gSetForgetfulPointLeftRegularRightMul G g)) x)
          z := by
    simpa using
      congrArg
        (fun k :
          (∏ᶜ fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S) ⟶ S ↦
          k z)
        hπ_mor
  calc
    (pushforwardLeftRegularObjEquiv G S)
        ((gSetForgetfulPoint_pushforwardObj G S).1.map
          (op (gSetForgetfulPointLeftRegularRightMul G g)) ψ) x =
      Pi.π (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S) x
        ((((Pi.map'
          (Φ.fiber.map (gSetForgetfulPointLeftRegularRightMul G g))
          (fun _ ↦ 𝟙 S)) :
          (∏ᶜ fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S) ⟶
            ∏ᶜ fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S)) z) := by
        simpa [pushforwardLeftRegularObjEquiv, Φ, Category.assoc] using hnat_apply x
    _ =
      Pi.π (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S)
        ((Φ.fiber.map (gSetForgetfulPointLeftRegularRightMul G g)) x)
        (((Φ.toToposPoint_pointPushforwardIso.hom.app S).hom.app
          (op (Action.leftRegular G))) ψ) := hπ
    _ = Pi.π (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S) (x * g) z := by
      rfl
    _ = (pushforwardLeftRegularObjEquiv G S) ψ (x * g) := by
      rfl

/-- Helper for Example 7.33.7: under the canonical fiber comparison, the section from Lemma 7.32.9
becomes the constant function. -/
private theorem gSetForgetfulPoint_pushforwardFiberIso_hom_section_eq_const
    (S : Type u) (s : S) :
    (gSetForgetfulPoint_pushforwardFiberIso G S).hom
      (MorphismOfTopoiIn.pointPushforwardFiberSection
        ((gSetForgetfulPoint G).toToposPoint) S s) =
      fun _ ↦ s := by
  have hsection :
      ((gSetForgetfulPoint G).toToposPoint).typeInverseImage.map
        (((gSetForgetfulPoint G).toToposPoint).typePushforward.map (fun _ : PUnit ↦ s))
        (MorphismOfTopoiIn.pointPushforwardFiberSection
          ((gSetForgetfulPoint G).toToposPoint) PUnit PUnit.unit) =
        MorphismOfTopoiIn.pointPushforwardFiberSection
          ((gSetForgetfulPoint G).toToposPoint) S s := by
    letI :
        Subsingleton (((gSetForgetfulPoint G).toToposPoint).typeInverseImage.obj
          (((gSetForgetfulPoint G).toToposPoint).typePushforward.obj PUnit)) := by
      refine ⟨fun a b ↦ ?_⟩
      apply (gSetForgetfulPoint_pushforwardFiberIso G PUnit).toEquiv.injective
      exact Subsingleton.elim _ _
    -- The canonical section is defined by functoriality from the terminal point in the `PUnit`
    -- fiber, and the intermediate `PUnit` fiber is a subsingleton.
    simpa [MorphismOfTopoiIn.pointPushforwardFiberSection] using
      congrArg
        (((gSetForgetfulPoint G).toToposPoint).typeInverseImage.map
          (((gSetForgetfulPoint G).toToposPoint).typePushforward.map (fun _ : PUnit ↦ s)))
        (Subsingleton.elim _ _)
  have hconst :
      MorphismOfTopoiIn.pointPushforwardFiberSection
        ((gSetForgetfulPoint G).toToposPoint) S s =
        gSetForgetfulPoint_pushforwardFiberMap G S (fun _ ↦ s) := by
    calc
      MorphismOfTopoiIn.pointPushforwardFiberSection
          ((gSetForgetfulPoint G).toToposPoint) S s =
        ((gSetForgetfulPoint G).toToposPoint).typeInverseImage.map
          (((gSetForgetfulPoint G).toToposPoint).typePushforward.map (fun _ : PUnit ↦ s))
          (MorphismOfTopoiIn.pointPushforwardFiberSection
            ((gSetForgetfulPoint G).toToposPoint) PUnit PUnit.unit) := by
              symm
              exact hsection
      _ = gSetForgetfulPoint_pushforwardFiberMap G S (fun _ ↦ s) := by
        simpa [gSetForgetfulPoint_pushforwardFiberMap_punit] using
          gSetForgetfulPoint_pushforwardFiberMap_naturality G (fun _ : PUnit ↦ s)
            (fun _ ↦ PUnit.unit)
  -- Rewrite the canonical section by the explicit constant-function map and evaluate via the fiber
  -- comparison iso.
  rw [hconst]
  simpa using gSetForgetfulPoint_pushforwardFiberIso_hom_map G S (fun _ ↦ s)

/-- Helper for Example 7.33.7: the explicit fiber map sends a constant function to the canonical
section from Lemma 7.32.9. -/
private theorem gSetForgetfulPoint_pushforwardFiberMap_const
    (S : Type u) (s : S) :
    gSetForgetfulPoint_pushforwardFiberMap G S (fun _ ↦ s) =
      MorphismOfTopoiIn.pointPushforwardFiberSection
        ((gSetForgetfulPoint G).toToposPoint) S s := by
  -- Compare both sides under the explicit equivalence `p^{-1}(p_* S) ≃ Map(G, S)`.
  apply (gSetForgetfulPoint_pushforwardFiberIso G S).toEquiv.injective
  calc
    (gSetForgetfulPoint_pushforwardFiberIso G S).hom
        (gSetForgetfulPoint_pushforwardFiberMap G S (fun _ ↦ s)) =
      fun _ ↦ s := by
        simpa using gSetForgetfulPoint_pushforwardFiberIso_hom_map G S (fun _ ↦ s)
    _ =
      (gSetForgetfulPoint_pushforwardFiberIso G S).hom
        (MorphismOfTopoiIn.pointPushforwardFiberSection
          ((gSetForgetfulPoint G).toToposPoint) S s) := by
            symm
            exact gSetForgetfulPoint_pushforwardFiberIso_hom_section_eq_const G S s

/-- Helper for Example 7.33.7: the `typeEquiv` counit at `yoneda' S`, evaluated at `PUnit`,
reads off the unique coordinate. -/
private theorem typeEquiv_evalEquiv_symm_apply_unit
    (S : Type u) (h : PUnit → ((typeEquiv.functor.obj S).1.obj (op PUnit))) :
    (evalEquiv (typeEquiv.functor.obj S).1 (typeEquiv.functor.obj S).2 PUnit).symm
      h PUnit.unit =
      h PUnit.unit PUnit.unit := by
  -- Rewrite the inverse equivalence as `typesGlue`, then evaluate the glued section at the unique
  -- point of `PUnit`.
  change typesGlue (typeEquiv.functor.obj S).1
      ((isSheaf_iff_isSheaf_of_type _ _).1 (typeEquiv.functor.obj S).2) PUnit h PUnit.unit = _
  have hglue := eval_typesGlue (S := (typeEquiv.functor.obj S).1)
    (hs := (isSheaf_iff_isSheaf_of_type _ _).1 (typeEquiv.functor.obj S).2)
    (α := PUnit) h
  have hval := congrFun hglue PUnit.unit
  simp [typeEquiv, yoneda', eval] at hval
  simpa using congrFun hval PUnit.unit

/-- Helper for Example 7.33.7: the `typeEquiv` counit at `yoneda' S`, evaluated at `PUnit`,
reduces to applying the underlying map at `PUnit.unit`. -/
private theorem typeEquiv_toAdjunction_counit_apply_unit
    (S : Type u) (z : (typeEquiv.functor.obj (PUnit → S)).1.obj (op PUnit)) :
    ((((typeEquiv.toAdjunction).counit.app (typeEquiv.functor.obj S)).hom.app
      (op PUnit)) z) PUnit.unit =
      z PUnit.unit PUnit.unit := by
  -- The `typeEquiv` counit is the inverse of the explicit `evalEquiv`.
  change (evalEquiv (typeEquiv.functor.obj S).1 (typeEquiv.functor.obj S).2 PUnit).symm
      z PUnit.unit = _
  rw [typeEquiv_evalEquiv_symm_apply_unit]

/-- Helper for Example 7.33.7: under `toToposPoint_pointInverseImageIso`, evaluating the inverse
image fiber at `PUnit.unit` returns the original sheaf fiber point. -/
private theorem gSetForgetfulPoint_pointInverseImageIso_inv_apply_unit
    (S : Type u)
    (x : (gSetForgetfulPoint G).sheafFiber.obj (gSetForgetfulPoint_pushforwardObj G S)) :
    (((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso (gSetForgetfulPoint G)).app
      (gSetForgetfulPoint_pushforwardObj G S)).inv x) PUnit.unit = x := by
  -- The comparison `p⁻¹ ≅ sheafFiber` is induced by `typeEquiv.unitIso`, so evaluation at the
  -- unique point undoes the inserted `PUnit` coordinate.
  simp [GrothendieckTopology.Point.toToposPoint_pointInverseImageIso,
    GrothendieckTopology.Point.toToposPoint]

/-- Helper for Example 7.33.7: the pushforward comparison to the skyscraper sheaf is induced by
evaluation at `PUnit.unit`. -/
private theorem gSetForgetfulPoint_pointPushforwardIso_hom_eval
    (S : Type u) :
    ((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso
      (gSetForgetfulPoint G)).app S).hom =
      (gSetForgetfulPoint G).skyscraperSheafFunctor.map (typeEquiv.unitIso.inv.app S) := by
  -- Unfold the `typePushforward` comparison: the remaining morphism is the identity whiskered
  -- with the skyscraper functor.
  dsimp [GrothendieckTopology.Point.toToposPoint_pointPushforwardIso,
    GrothendieckTopology.Point.toToposPoint]
  exact Category.id_comp _

/-- Helper for Example 7.33.7: the `Type`-valued counit of the induced topos point is the
`PUnit`-evaluation of the underlying sheaf-valued counit. -/
private theorem gSetForgetfulPoint_typeAdjunction_counit_apply
    (S : Type u)
    (z : ((gSetForgetfulPoint G).toToposPoint).typeInverseImage.obj
      (((gSetForgetfulPoint G).toToposPoint).typePushforward.obj S)) :
    (((gSetForgetfulPoint G).toToposPoint).typeAdjunction.counit.app S) z =
      ((((gSetForgetfulPoint G).toToposPoint).adjunction.counit.app
        (typeEquiv.functor.obj S)).hom.app (op PUnit)) z PUnit.unit := by
  -- Expand the transported adjunction once so the final `Type`-valued counit is read as the
  -- `PUnit`-component of the sheaf-valued counit.
  simp [MorphismOfTopoiIn.typeAdjunction, CategoryTheory.Adjunction.comp_counit_app]

/-- Helper for Example 7.33.7: the counit of `p⁻¹ ⊣ p_*` becomes the skyscraper-sheaf counit
after transporting through the point comparison isomorphisms. -/
private theorem gSetForgetfulPoint_typeAdjunction_counit_to_skyscraper
    (S : Type u)
    (x : (gSetForgetfulPoint G).sheafFiber.obj (gSetForgetfulPoint_pushforwardObj G S)) :
    (((gSetForgetfulPoint G).toToposPoint).typeAdjunction.counit.app S)
      ((((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso
        (gSetForgetfulPoint G)).app (gSetForgetfulPoint_pushforwardObj G S)).inv) x) =
      ((gSetForgetfulPoint G).skyscraperSheafAdjunction.counit.app S)
        (((gSetForgetfulPoint G).sheafFiber.map
          (((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso
            (gSetForgetfulPoint G)).app S).hom)) x) := by
  -- Route correction: normalize the `typeAdjunction` counit through the owner-level `typeEquiv`
  -- and skyscraper adjunctions before returning to the explicit `Map(G, S)` model.
  rw [gSetForgetfulPoint_typeAdjunction_counit_apply]
  let Φ := gSetForgetfulPoint G
  have hnat :=
    congrArg
      (fun k : ((Φ.skyscraperSheafFunctor ⋙ Φ.sheafFiber).obj (PUnit → S)) ⟶ S ↦
        k x)
      (Φ.skyscraperSheafAdjunction.counit.naturality (typeEquiv.unitIso.inv.app S))
  calc
    (((gSetForgetfulPoint G).toToposPoint).adjunction.counit.app
          (typeEquiv.functor.obj S)).hom.app
        (op PUnit)
        ((((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso
          (gSetForgetfulPoint G)).app (gSetForgetfulPoint_pushforwardObj G S)).inv) x)
        PUnit.unit =
      ((gSetForgetfulPoint G).skyscraperSheafAdjunction.counit.app (PUnit → S))
        x PUnit.unit := by
          -- Compute the `typeEquiv` counit on the `PUnit` component explicitly.
          simpa [GrothendieckTopology.Point.toToposPoint, CategoryTheory.Adjunction.comp_counit_app,
            gSetForgetfulPoint_pointInverseImageIso_inv_apply_unit] using
            (typeEquiv_toAdjunction_counit_apply_unit (S := S)
              (z := ((typeEquiv.functor.map
                ((gSetForgetfulPoint G).skyscraperSheafAdjunction.counit.app
                  (PUnit → S))).hom.app (op PUnit))
                ((((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso
                  (gSetForgetfulPoint G)).app (gSetForgetfulPoint_pushforwardObj G S)).inv) x)))
    _ = ((gSetForgetfulPoint G).skyscraperSheafAdjunction.counit.app S)
          (((gSetForgetfulPoint G).sheafFiber.map
            (((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso
              (gSetForgetfulPoint G)).app S).hom)) x) := by
                -- Naturality of the skyscraper counit transports evaluation at `PUnit.unit`
                -- across the pushforward comparison.
                simpa [gSetForgetfulPoint_pointPushforwardIso_hom_eval] using hnat.symm

/-- Helper for Example 7.33.7: after transporting the `typeAdjunction` counit to the skyscraper
adjunction, the explicit stalk element attached to `ψ : G → S` evaluates to `ψ 1`. -/
private theorem gSetForgetfulPoint_pushforwardFiber_counit_on_map
    (S : Type u) (ψ : G → S) :
    (((gSetForgetfulPoint G).toToposPoint).typeAdjunction.counit.app S)
      (gSetForgetfulPoint_pushforwardFiberMap G S ψ) = ψ 1 := by
  let Φ := gSetForgetfulPoint G
  let F := gSetForgetfulPoint_pushforwardObj G S
  let t := (pushforwardLeftRegularObjEquiv G S).symm ψ
  have hs :
      Φ.toPresheafFiber (Action.leftRegular G)
          ((1 : G) : Φ.fiber.obj (Action.leftRegular G))
          ((Φ.skyscraperSheafFunctor.obj S).1) ≫
        (Φ.skyscraperSheafAdjunction.counit.app S) =
      Pi.π (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S)
        ((1 : G) : Φ.fiber.obj (Action.leftRegular G)) := by
    let f : Φ.skyscraperSheafFunctor.obj S ⟶ Φ.skyscraperSheafFunctor.obj S := 𝟙 _
    -- The skyscraper counit at the chosen point is projection to the corresponding factor.
    simpa [f] using
      (Φ.toPresheafFiber_skyscraperPresheafHomEquiv_symm
        (A := Type u)
        (P := (Φ.skyscraperSheafFunctor.obj S).1)
        (M := S) (f.hom) (Action.leftRegular G)
        ((1 : G) : Φ.fiber.obj (Action.leftRegular G)))
  have hnat_fiber :=
    congrArg
      (fun k : F.1.obj (op (Action.leftRegular G)) ⟶
          Φ.sheafFiber.obj (Φ.skyscraperSheafFunctor.obj S) ↦
        k t)
      (Φ.toPresheafFiber_naturality
        (((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso Φ).app S).hom.hom)
        (Action.leftRegular G)
        ((1 : G) : Φ.fiber.obj (Action.leftRegular G)))
  calc
    (((gSetForgetfulPoint G).toToposPoint).typeAdjunction.counit.app S)
        (gSetForgetfulPoint_pushforwardFiberMap G S ψ) =
      (Φ.skyscraperSheafAdjunction.counit.app S)
        (Φ.sheafFiber.map
          (((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso Φ).app S).hom)
          (Φ.toPresheafFiber (Action.leftRegular G)
            ((1 : G) : Φ.fiber.obj (Action.leftRegular G)) F.1 t)) := by
              -- First transport the `Type`-valued counit to the owner-level skyscraper counit.
              simpa [gSetForgetfulPoint_pushforwardFiberMap, Φ, F, t] using
                gSetForgetfulPoint_typeAdjunction_counit_to_skyscraper G S
                  (Φ.toPresheafFiber (Action.leftRegular G)
                    ((1 : G) : Φ.fiber.obj (Action.leftRegular G)) F.1 t)
    _ =
      (Φ.skyscraperSheafAdjunction.counit.app S)
        (Φ.toPresheafFiber (Action.leftRegular G)
          ((1 : G) : Φ.fiber.obj (Action.leftRegular G))
          ((Φ.skyscraperSheafFunctor.obj S).1)
          ((((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso Φ).app S).hom.hom.app
            (op (Action.leftRegular G))) t)) := by
              -- Rewrite the sheaf-fiber map through the left-regular leg, then apply the counit.
              simpa [GrothendieckTopology.Point.sheafFiber, F, Category.assoc] using
                congrArg (Φ.skyscraperSheafAdjunction.counit.app S) hnat_fiber
    _ =
      Pi.π (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S)
        ((1 : G) : Φ.fiber.obj (Action.leftRegular G))
        ((((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso Φ).app S).hom.hom.app
          (op (Action.leftRegular G))) t) := by
            -- The skyscraper counit now reduces to projecting to the coordinate indexed by `1`.
            simpa [Category.assoc] using
              congrArg
                (fun k ↦
                  k ((((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso Φ).app S).hom.hom.app
                    (op (Action.leftRegular G))) t))
                hs
    _ = ψ 1 := by
      -- Under the explicit left-regular identification, the `1`-coordinate is the value `ψ 1`.
      simpa [pushforwardLeftRegularObjEquiv, Φ, t, Types.productIso_inv_comp_π] using
        congrArg (fun f : G → S ↦ f 1)
          (Equiv.apply_symm_apply (pushforwardLeftRegularObjEquiv G S) ψ)

/-- Helper for Example 7.33.7: after identifying `p_* S` with the skyscraper sheaf on `S`, the
counit evaluates a function `G → S` at `1`. -/
private theorem gSetForgetfulPoint_pushforwardFiberIso_hom_eval_one
    (S : Type u)
    (z :
      ((gSetForgetfulPoint G).toToposPoint).typeInverseImage.obj
        (((gSetForgetfulPoint G).toToposPoint).typePushforward.obj S)) :
    (gSetForgetfulPoint_pushforwardFiberIso G S).hom z 1 =
      (((gSetForgetfulPoint G).toToposPoint).typeAdjunction.counit.app S) z := by
  -- Compare `z` with the explicit inverse-image model `Map(G, S)` and then reduce to the map case.
  let ψ := (gSetForgetfulPoint_pushforwardFiberIso G S).hom z
  have hz' :
      (gSetForgetfulPoint_pushforwardFiberIso G S).hom
        (gSetForgetfulPoint_pushforwardFiberMap G S ψ) =
          (gSetForgetfulPoint_pushforwardFiberIso G S).hom z := by
    simpa [ψ] using gSetForgetfulPoint_pushforwardFiberIso_hom_map G S ψ
  have hz : gSetForgetfulPoint_pushforwardFiberMap G S ψ = z :=
    (gSetForgetfulPoint_pushforwardFiberIso G S).toEquiv.injective hz'
  -- After rewriting by `hz`, the arbitrary fiber point is reduced to the explicit `Map(G, S)` case.
  rw [← hz]
  calc
    (gSetForgetfulPoint_pushforwardFiberIso G S).hom
        (gSetForgetfulPoint_pushforwardFiberMap G S ψ) 1 = ψ 1 := by
          simpa using congrArg (fun f : G → S ↦ f 1)
            (gSetForgetfulPoint_pushforwardFiberIso_hom_map G S ψ)
    _ = (((gSetForgetfulPoint G).toToposPoint).typeAdjunction.counit.app S)
          (gSetForgetfulPoint_pushforwardFiberMap G S ψ) := by
            symm
            exact gSetForgetfulPoint_pushforwardFiber_counit_on_map G S ψ

/-- Under the canonical equivalence `p^{-1}(p_* S) ≃ Map(G, S)` from Example 7.33.7, the section
`S → p^{-1}(p_* S)` of Lemma 7.32.9 is the constant-function map. -/
theorem gSetForgetfulPoint_pushforwardFiber_section_eq_const
    (S : Type u) :
    (fun s ↦
      gSetForgetfulPoint_pushforwardFiberEquiv G S
        (MorphismOfTopoiIn.pointPushforwardFiberSection
          ((gSetForgetfulPoint G).toToposPoint) S s)) =
      fun s _ ↦ s :=
  by
    funext s
    -- Rewrite the target through the inverse equivalence, where the statement is explicit.
    exact ((gSetForgetfulPoint_pushforwardFiberEquiv G S).apply_eq_iff_eq_symm_apply).2
      (gSetForgetfulPoint_pushforwardFiberMap_const G S s).symm

/-- Under the canonical equivalence `p^{-1}(p_* S) ≃ Map(G, S)` from Example 7.33.7, the counit
map `p^{-1}(p_* S) → S` of Lemma 7.32.9 is evaluation at `1 ∈ G`. -/
theorem gSetForgetfulPoint_pushforwardFiber_counit_eq_eval_one
    (S : Type u) :
    (fun ψ ↦
      (((gSetForgetfulPoint G).toToposPoint).typeAdjunction.counit.app S)
        ((gSetForgetfulPoint_pushforwardFiberEquiv G S).symm ψ)) =
      fun ψ ↦ ψ 1 :=
  by
    funext ψ
    -- Rewrite the inverse equivalence by the explicit fiber map and evaluate the counit there.
    simpa using gSetForgetfulPoint_pushforwardFiber_counit_on_map G S ψ

-- Proof sketch: under the canonical identification of `p_* S` on the left regular `G`-set with
-- `Map(G, S)`, pullback along right multiplication by `g` becomes precomposition by the map
-- `x ↦ x * g`.
private theorem pushforwardRightTranslation_comm
    (S : Type u) (g : G) :
    ((sheafSectionsOnLeftRegularFunctor G).obj
        (gSetForgetfulPoint_pushforwardObj G S)).ρ g ≫
      (pushforwardLeftRegularObjEquiv G S).toIso.hom =
        (pushforwardLeftRegularObjEquiv G S).toIso.hom ≫
          (Action.ofMulAction G (G → S)).ρ g :=
  by
    ext ψ x
    -- The left action is pullback along right multiplication, and the explicit equivalence sends
    -- that pullback to precomposition by `x ↦ x * g`.
    simpa [sheafSectionsOnLeftRegularFunctor, gSetForgetfulPointMapMulAction_smul_apply] using
      congrArg (fun f : G → S ↦ f x)
        (pushforwardLeftRegularObjEquiv_rightMul G S g ψ)

/-- After identifying sheaves on `\mathcal T_G` with `G`-sets via evaluation on the left regular
object, the pushforward `p_* S` is the right-translation `G`-set `Map(G, S)`. -/
noncomputable def gSetForgetfulPoint_pushforwardRightTranslationIso
    (S : Type u) :
    (sheafSectionsOnLeftRegularFunctor G).obj
        (((gSetForgetfulPoint G).toToposPoint).typePushforward.obj S) ≅
      Action.ofMulAction G (G → S) :=
  Action.mkIso
    (pushforwardLeftRegularObjEquiv G S).toIso
    (pushforwardRightTranslation_comm G S)

end

end CategoryTheory
