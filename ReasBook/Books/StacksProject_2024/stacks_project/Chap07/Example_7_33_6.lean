import Mathlib
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Category
import Mathlib.Topology.Sheaves.Points
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sober
import StacksProject_2024.Chap07.Proposition_7_33_3

-- Declarations for this item will be appended below by the statement pipeline.

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
    irreducibleClosedPointFiberMap Z (𝟙 U) = 𝟙 (irreducibleClosedPointFiberObj Z U) := sorry

private theorem irreducibleClosedPointFiberMap_comp (Z : IrreducibleCloseds X)
    {U V W : Opens X} (i : U ⟶ V) (j : V ⟶ W) :
    irreducibleClosedPointFiberMap Z (i ≫ j) =
      irreducibleClosedPointFiberMap Z i ≫ irreducibleClosedPointFiberMap Z j := sorry

private def irreducibleClosedPointFiber (Z : IrreducibleCloseds X) : Opens X ⥤ Type u where
  obj := irreducibleClosedPointFiberObj Z
  map := irreducibleClosedPointFiberMap Z
  map_id := irreducibleClosedPointFiberMap_id Z
  map_comp := irreducibleClosedPointFiberMap_comp Z

private instance irreducibleClosedPointFiber_elements_initiallySmall (Z : IrreducibleCloseds X) :
    InitiallySmall.{u} (irreducibleClosedPointFiber Z).Elements :=
  initiallySmall_of_essentiallySmall _

-- Proof sketch: the singleton-or-empty fiber functor sends `⊤` to a singleton and identifies the
-- value on an intersection with the pullback of the values on the two opens, so Lemma 7.33.2
-- yields finite-limit preservation.
private theorem irreducibleClosedPointFiber_preservesFiniteLimits (Z : IrreducibleCloseds X) :
    PreservesFiniteLimits (irreducibleClosedPointFiber Z) := sorry

private noncomputable instance (Z : IrreducibleCloseds X) :
    PreservesFiniteLimits (irreducibleClosedPointFiber Z) :=
  irreducibleClosedPointFiber_preservesFiniteLimits Z

private instance : OrderTop (Opens X) where
  top := ⟨Set.univ, isOpen_univ⟩
  le_top := by
    intro U x hx
    trivial

private noncomputable instance : HasFiniteLimits (Opens X) :=
  hasFiniteLimits_of_semilatticeInf_orderTop

private theorem irreducibleClosedPointFiber_jointly_surjective (Z : IrreducibleCloseds X)
    {U : Opens X} (R : Sieve U) (hR : R ∈ Opens.grothendieckTopology X U)
    (s : (irreducibleClosedPointFiber Z).obj U) :
    ∃ (V : Opens X) (i : V ⟶ U), R i ∧ ∃ t : (irreducibleClosedPointFiber Z).obj V,
      (irreducibleClosedPointFiber Z).map i t = s := sorry

/- Internally, the point attached to `Z` uses the singleton-or-empty fiber over each open `U`:
it is empty when `Z ∩ U = ∅` and a singleton when `Z ∩ U` is nonempty. -/
/-- The point of the opens site attached to an irreducible closed subset `Z`. -/
noncomputable def irreducibleClosedSitePoint (Z : IrreducibleCloseds X) :
    (Opens.grothendieckTopology X).Point := by
  let u := irreducibleClosedPointFiber Z
  letI : IsCofiltered u.Elements := Functor.isCofiltered_elements u
  exact
    { fiber := u
      jointly_surjective := by
        intro U R hR s
        rcases irreducibleClosedPointFiber_jointly_surjective Z R hR s with
          ⟨V, i, hi, t, ht⟩
        exact ⟨V, i, hi, t, ht⟩ }

/-- The fiber of the point attached to `Z` over an open `U` is nonempty exactly when `U` meets
`Z`; since fibers of points on the opens site are subsingletons, this means the fiber is then a
singleton. -/
@[simp] theorem irreducibleClosedSitePoint_fiber_nonempty_iff
    (Z : IrreducibleCloseds X) (U : Opens X) :
    Nonempty ((irreducibleClosedSitePoint Z).fiber.obj U) ↔ ((Z : Set X) ∩ U).Nonempty := sorry

/-- The fiber of the point attached to `Z` over an open `U` is empty exactly when `U` is disjoint
from `Z`. -/
@[simp] theorem irreducibleClosedSitePoint_fiber_isEmpty_iff
    (Z : IrreducibleCloseds X) (U : Opens X) :
    IsEmpty ((irreducibleClosedSitePoint Z).fiber.obj U) ↔ Disjoint (Z : Set X) U := sorry

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
    IsClosed (sitePointIrreducibleClosedCarrier Φ) := sorry

-- Proof sketch: use the finite-limit and covering properties of a site point on the opens site to
-- show that if the complementary closed subset were the union of two proper closed subsets, then
-- one of them would already equal the whole support.
private theorem sitePointIrreducibleClosedCarrier_isIrreducible
    (Φ : (Opens.grothendieckTopology X).Point) :
    IsIrreducible (sitePointIrreducibleClosedCarrier Φ) := sorry

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
      {x | ∀ U : Opens X, x ∈ U → Nonempty (Φ.fiber.obj U)} := sorry

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
    IsEmpty (Φ.fiber.obj U) ↔ Disjoint (sitePointIrreducibleClosed Φ : Set X) U := sorry

-- Proof sketch: the example constructs the support `Z` of a site point `Φ` as the complement of
-- the largest open with empty fiber and shows that `Φ` is uniquely determined, up to isomorphism,
-- by the singleton-or-empty functor attached to this irreducible closed subset.
/-- Example 7.33.6: a point of the opens site is isomorphic to the canonical site point attached
to the irreducible closed subset extracted from its empty fibers. -/
theorem opensSitePoint_iso_irreducibleClosedSitePoint
    (Φ : (Opens.grothendieckTopology X).Point) :
    Nonempty (Φ ≅ irreducibleClosedSitePoint (sitePointIrreducibleClosed Φ)) := sorry

/-- Companion uniqueness form of Example 7.33.6: points of the opens site `X_{Zar}`, and hence
points of `Sh(X)`, are in one-to-one correspondence up to isomorphism with irreducible closed
subsets of `X`. -/
theorem opensSitePoint_existsUnique_irreducibleClosedSubset
    (Φ : (Opens.grothendieckTopology X).Point) :
    ∃! Z : IrreducibleCloseds X, Nonempty (Φ ≅ irreducibleClosedSitePoint Z) := sorry

-- Proof sketch: for the singleton-or-empty point attached to `Z`, the largest open with empty
-- fiber is exactly `X \ Z`, so the complementary irreducible closed subset recovered by the
-- construction is `Z` itself.
/-- Recovering the irreducible closed subset attached to its own singleton-or-empty site point
returns the original subset. -/
theorem sitePointIrreducibleClosed_of_irreducibleClosedSitePoint (Z : IrreducibleCloseds X) :
    sitePointIrreducibleClosed (irreducibleClosedSitePoint Z) = Z := sorry

-- Proof sketch: if `x` is a generic point of `Z`, then an open subset meets `Z` if and only if
-- it contains `x`, so the singleton-or-empty point attached to `Z` and the standard site point
-- attached to `x` have isomorphic fiber functors.
/-- If `x` is a generic point of an irreducible closed subset `Z`, then the site point attached to
`Z` is isomorphic to the standard opens-site point attached to `x`. -/
theorem irreducibleClosedSitePoint_iso_pointGrothendieckTopology_of_isGenericPoint
    {x : X} {Z : IrreducibleCloseds X} (hx : IsGenericPoint x Z) :
    Nonempty (irreducibleClosedSitePoint Z ≅ Opens.pointGrothendieckTopology x) := sorry

attribute [local instance] specializationOrder

-- Proof sketch: apply the irreducible-closed classification theorem, then use sobriety to identify
-- the resulting irreducible closed subset with the closure of a unique generic point.
/-- In a sober topological space, every point of the opens site is isomorphic to the standard site
point attached to its canonically associated point of `X`. -/
theorem opensSitePoint_iso_pointGrothendieckTopology_of_quasiSober
    [T0Space X] [QuasiSober X] (Φ : (Opens.grothendieckTopology X).Point) :
    Nonempty (Φ ≅ Opens.pointGrothendieckTopology
      (irreducibleSetEquivPoints (sitePointIrreducibleClosed Φ))) := sorry

/-- Companion uniqueness form of Example 7.33.6 in the sober case. -/
theorem opensSitePoint_existsUnique_spacePoint [T0Space X] [QuasiSober X]
    (Φ : (Opens.grothendieckTopology X).Point) :
    ∃! x : X, Nonempty (Φ ≅ Opens.pointGrothendieckTopology x) := sorry

end CategoryTheory
