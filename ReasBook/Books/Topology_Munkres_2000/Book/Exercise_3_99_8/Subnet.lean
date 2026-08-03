module

public import Mathlib.Order.Filter.AtTopBot.Tendsto

public section

universe u v w

namespace Net

/-- An admissible subnet reindexing is a monotone map with cofinal range. -/
def IsSubnetMap {K : Type u} {J : Type v} [Preorder K] [Preorder J]
    (g : K → J) : Prop :=
  Monotone g ∧ IsCofinal (Set.range g)

/-- A subnet reindexing is equivalently monotone with cofinal range. -/
theorem isSubnetMap_iff {K : Type u} {J : Type v} [Preorder K] [Preorder J]
    {g : K → J} : IsSubnetMap g ↔ Monotone g ∧ IsCofinal (Set.range g) :=
  Iff.rfl

/-- A subnet reindexing is monotone. -/
theorem IsSubnetMap.monotone {K : Type u} {J : Type v} [Preorder K] [Preorder J]
    {g : K → J} (h : IsSubnetMap g) : Monotone g :=
  h.1

/-- The range of a subnet reindexing is cofinal. -/
theorem IsSubnetMap.isCofinal_range {K : Type u} {J : Type v} [Preorder K]
    [Preorder J] {g : K → J} (h : IsSubnetMap g) : IsCofinal (Set.range g) :=
  h.2

/-- A subnet reindexing tends from `Filter.atTop` to `Filter.atTop`. -/
theorem IsSubnetMap.tendsto_atTop {K : Type u} {J : Type v} [Preorder K]
    [Preorder J] {g : K → J} (h : IsSubnetMap g) :
    Filter.Tendsto g Filter.atTop Filter.atTop :=
  h.monotone.tendsto_atTop_atTop fun j ↦ by
    obtain ⟨_, ⟨k, rfl⟩, hj⟩ := h.isCofinal_range j
    exact ⟨k, hj⟩

/-- Precomposition by a subnet reindexing preserves convergence to any filter. -/
theorem IsSubnetMap.tendsto_comp {K : Type u} {J : Type v} {X : Type w} [Preorder K]
    [Preorder J] {g : K → J} {f : J → X} {l : Filter X} (h : IsSubnetMap g)
    (hf : Filter.Tendsto f Filter.atTop l) :
    Filter.Tendsto (f ∘ g) Filter.atTop l :=
  hf.comp h.tendsto_atTop

/-- A subnet of a net, indexed by a directed preorder and obtained by an admissible
subnet reindexing. -/
structure Subnet {J : Type u} {X : Type v} [Preorder J] (net : J → X) where
  index : Type (max u v)
  [nonemptyIndex : Nonempty index]
  [preorderIndex : Preorder index]
  [isDirectedOrderIndex : IsDirectedOrder index]
  map : index → J
  isSubnetMap : IsSubnetMap map

namespace Subnet

/-- A subnet's index type is nonempty. -/
instance instNonemptyIndex {J : Type u} {X : Type v} [Preorder J] {net : J → X}
    (subnet : Subnet net) : Nonempty subnet.index :=
  subnet.nonemptyIndex

/-- A subnet's index type carries its stored preorder. -/
instance instPreorderIndex {J : Type u} {X : Type v} [Preorder J]
    {net : J → X} (subnet : Subnet net) : Preorder subnet.index :=
  subnet.preorderIndex

/-- A subnet's index type is directed by its stored directed-order structure. -/
instance instIsDirectedOrderIndex {J : Type u} {X : Type v} [Preorder J]
    {net : J → X} (subnet : Subnet net) : IsDirectedOrder subnet.index :=
  subnet.isDirectedOrderIndex

/-- The net obtained by evaluating the original net along a subnet reindexing. -/
@[expose]
def values {J : Type u} {X : Type v} [Preorder J] {net : J → X}
    (subnet : Subnet net) : subnet.index → X :=
  net ∘ subnet.map

/-- Evaluation of a subnet agrees with evaluation along its reindexing map. -/
@[simp]
theorem values_apply {J : Type u} {X : Type v} [Preorder J] {net : J → X}
    (subnet : Subnet net) (i : subnet.index) :
    subnet.values i = net (subnet.map i) :=
  rfl

/-- The reindexing map of a subnet tends from `Filter.atTop` to `Filter.atTop`. -/
theorem tendsto_map {J : Type u} {X : Type v} [Preorder J]
    {net : J → X} (subnet : Subnet net) :
    Filter.Tendsto subnet.map Filter.atTop Filter.atTop :=
  subnet.isSubnetMap.tendsto_atTop

end Subnet

end Net
