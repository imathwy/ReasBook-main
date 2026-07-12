import StacksProject_2024.Chap20.Open_subspace_module_pushforward_core
import StacksProject_2024.Chap20.Lemma_20_34_1

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace TopologicalSpace.Opens

/-- An open subset is disjoint from a subset if their underlying sets are disjoint. -/
abbrev DisjointSet {X : Type u} [TopologicalSpace X] (U : Opens X) (Z : Set X) : Prop :=
  Disjoint U.1 Z

end TopologicalSpace.Opens

namespace AlgebraicGeometry.RingedSpace

open scoped RingedSpaceClosedSubsetDerived

/- Domain-style sampling for Lemma 20.34.7:
- primary domain: derived local cohomology for `𝒪_X`-modules and its vanishing on
  derived open pushforward from an open subspace disjoint from the closed support;
- sampled owner declarations:
  `moduleDerivedOnOpen`,
  `modulePushforwardFromOpenDerived`,
  `closedSubsetModuleSectionsWithSupportDerived`;
- best owner abstraction:
  `source-facing`: the vanishing statement `R𝓗_Z(Rj_* K) = 0`;
  `core/canonical`: the Chapter 20 open-pushforward owner
    `moduleDerivedOnOpen X U` together with
    `modulePushforwardFromOpenDerived U`,
    and the closed-support owner
    `closedSubsetModuleSectionsWithSupportDerived`;
  `bridge/view`: none in this file, since both the open pushforward and the closed-support
    functor are already owned upstream.

Primitive data are just the ringed space `X`, the open subset `U`, the closed subset `Z`,
the disjointness hypothesis, and the derived object `K` on `U`. The local-cohomology object
itself is derived API from the existing chapter owners and should not be replaced by a weaker
support-containment surrogate.
-/

section

variable {X : RingedSpace.{u}} (U : Opens X.carrier)
variable {Z : Set X} (hZ : IsClosed Z)

local notation "DMod[" U "]" => moduleDerivedOnOpen X U
local notation "RPush[" U "]" => modulePushforwardFromOpenDerived U

@[simp] theorem disjointSet_iff_le_closedSubsetOpenComplement :
    U.DisjointSet Z ↔ U ≤ closedSubsetOpenComplement hZ := by
  constructor
  · intro hUZ x hxU
    have hxZ : x ∉ Z := by
      exact Set.disjoint_left.mp hUZ hxU
    simpa [closedSubsetOpenComplement] using hxZ
  · intro hUZ
    change Disjoint U.1 Z
    rw [Set.disjoint_left]
    intro x hxU hxZ
    have hx : x ∈ closedSubsetOpenComplement hZ := hUZ hxU
    exact (by simpa [closedSubsetOpenComplement] using hx : x ∉ Z) hxZ

-- Proof sketch: the support of `Rj_* K` is contained in the image of the open inclusion
-- `j : U ↪ X`. If `U ∩ Z = ∅`, then `Rj_* K` has no stalks on `Z`, so its local cohomology with
-- support in `Z` vanishes.
/-- Technical bridge for Lemma 20.34.7 using the equivalent inclusion hypothesis
`U ≤ closedSubsetOpenComplement hZ`. -/
theorem pushforwardFromOpenDerived_closedSubsetModuleSectionsWithSupportDerived_obj_isZero_of_le_closedSubsetOpenComplement
    (hUZ : U ≤ closedSubsetOpenComplement hZ)
    (K : DMod[U]) :
    IsZero (((RPush[U]) ⋙ R𝓗[hZ]).obj K) := sorry

-- Proof sketch: use the equivalent complement-inclusion formulation and then apply the bridge
-- theorem above.
/-- Lemma 20.34.7: if `j : U ↪ X` is the inclusion of an open subset disjoint from a closed
subset `Z`, then for every `K ∈ D(𝒪_U)` the local-cohomology object `R𝓗_Z(Rj_* K)` is zero.
In this file the composite `R𝓗_Z ∘ Rj_*` is formalized by
`modulePushforwardFromOpenDerived U ⋙ R𝓗[hZ]`. -/
@[stacks 0G73]
theorem pushforwardFromOpenDerived_closedSubsetModuleSectionsWithSupportDerived_obj_isZero_of_disjoint
    (hUZ : U.DisjointSet Z)
    (K : DMod[U]) :
    IsZero (((RPush[U]) ⋙ R𝓗[hZ]).obj K) := by
  rw [disjointSet_iff_le_closedSubsetOpenComplement U hZ] at hUZ
  exact
    pushforwardFromOpenDerived_closedSubsetModuleSectionsWithSupportDerived_obj_isZero_of_le_closedSubsetOpenComplement
      U hZ hUZ K

/-- Typeclass form of Lemma 20.34.7: if `U ∩ Z = ∅`, then `R𝓗_Z(Rj_* K)` is zero for every
`K ∈ D(𝒪_U)`. -/
instance instIsZeroPushforwardFromOpenDerivedClosedSubsetModuleSectionsWithSupportDerivedObjOfDisjoint
    [hUZ : Fact (U.DisjointSet Z)] (K : DMod[U]) :
    IsZero (((RPush[U]) ⋙ R𝓗[hZ]).obj K) :=
  pushforwardFromOpenDerived_closedSubsetModuleSectionsWithSupportDerived_obj_isZero_of_disjoint
    U hZ hUZ.out K

end

end AlgebraicGeometry.RingedSpace
