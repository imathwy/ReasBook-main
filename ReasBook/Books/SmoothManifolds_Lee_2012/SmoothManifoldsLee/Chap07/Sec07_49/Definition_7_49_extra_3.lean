import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic.Recall

/- Definition 7.49-extra-3: the identity component of a Lie group is the connected component
containing the identity. The source-facing set-level owner is `connectedComponent (1 : G)`.
For topological groups, mathlib also packages the same object canonically as the subgroup
`Subgroup.connectedComponentOfOne G`. -/

universe u

section SetLevel

variable {G : Type u} [One G] [TopologicalSpace G]

/-- Source-facing alias: for a Lie group `G`, the connected component containing the identity
element `1` is called the identity component of `G`. In mathlib this set-level owner is
`connectedComponent (1 : G)`. -/
abbrev identityComponent (G : Type u) [One G] [TopologicalSpace G] : Set G :=
  connectedComponent (1 : G)

/- The source-facing owner of the connected component containing the identity is the generic
`connectedComponent` construction specialized at `1`. -/
#check (connectedComponent (1 : G) : Set G)

end SetLevel

/- The identity element belongs to the identity component by specializing
`mem_connectedComponent` at `x = 1`. -/
recall mem_connectedComponent {X : Type u} [TopologicalSpace X] (x : X) :
    x ∈ connectedComponent x

/- The identity component is connected by specializing `isConnected_connectedComponent`
at `x = 1`. -/
recall isConnected_connectedComponent {X : Type u} [TopologicalSpace X] (x : X) :
    IsConnected (connectedComponent x : Set X)

section SubgroupLevel

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- The subgroup structure on the identity component is obtained by showing that
the connected component of `1` is closed under multiplication and inversion. -/

/-- Helper for Definition 7.49-extra-3: if `g` and `h` lie in the connected component of `1`,
then so does `g * h`. -/
@[to_additive
  /-- Helper for Definition 7.49-extra-3: if `g` and `h` lie in the connected component of `0`,
  then so does `g + h`. -/]
theorem mul_mem_connectedComponent_one {G : Type*} [TopologicalSpace G] [MulOneClass G]
    [ContinuousMul G] {g h : G} (hg : g ∈ connectedComponent (1 : G))
    (hh : h ∈ connectedComponent (1 : G)) : g * h ∈ connectedComponent (1 : G) := by
  rw [connectedComponent_eq hg]
  have hmul : g ∈ connectedComponent (g * h) := by
    -- Left multiplication sends the component of `h` into the component of `g * h`.
    apply Continuous.image_connectedComponent_subset (continuous_const_mul g)
    rw [← connectedComponent_eq hh]
    exact ⟨(1 : G), mem_connectedComponent, by simp only [mul_one]⟩
  simpa [← connectedComponent_eq hmul] using mem_connectedComponent

/-- Helper for Definition 7.49-extra-3: inversion preserves the connected component of `1`. -/
@[to_additive
  /-- Helper for Definition 7.49-extra-3: negation preserves the connected component of `0`. -/]
theorem inv_mem_connectedComponent_one {G : Type*} [TopologicalSpace G] [DivisionMonoid G]
    [ContinuousInv G] {g : G} (hg : g ∈ connectedComponent (1 : G)) :
    g⁻¹ ∈ connectedComponent (1 : G) := by
  rw [← inv_one]
  exact
    Continuous.image_connectedComponent_subset continuous_inv _
      ((Set.mem_image _ _ _).mp ⟨g, hg, rfl⟩)

/-- Definition 7.49-extra-3: for a topological group `G`, mathlib packages the identity
component canonically as the subgroup `Subgroup.connectedComponentOfOne G`. -/
@[to_additive /-- Definition 7.49-extra-3: for a topological additive group `G`, mathlib packages
the identity component canonically as the additive subgroup
`AddSubgroup.connectedComponentZero G`. -/]
def Subgroup.connectedComponentOfOne (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] : Subgroup G where
  carrier := connectedComponent (1 : G)
  one_mem' := mem_connectedComponent
  mul_mem' hg hh := mul_mem_connectedComponent_one hg hh
  inv_mem' hg := inv_mem_connectedComponent_one hg

/-- Helper for Definition 7.49-extra-3: the carrier of the subgroup-valued identity component is
the source-facing set `connectedComponent (1 : G)`. -/
theorem connectedComponentOfOne_coe :
    ((Subgroup.connectedComponentOfOne G : Subgroup G) : Set G) = connectedComponent (1 : G) := by
  -- This bridge is definitional because `Subgroup.connectedComponentOfOne` is built with
  -- carrier `connectedComponent (1 : G)`.
  rfl

end SubgroupLevel
