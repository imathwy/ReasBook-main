module

public import Mathlib.Topology.Connected.PathConnected

public section

universe u v

/-- A chosen path between the distinguished points of two indexed sets, contained in their union. -/
structure SelectPath {X : Type u} [TopologicalSpace X] {ι : Type v}
    (U : ι → Set X) (p : (i : ι) → U i) (i j : ι) where
  /-- The underlying path between the distinguished points. -/
  toPath : Path (p i : X) (p j : X)
  /-- The range of the path lies in the union of the two indexed sets. -/
  range_subset_union : Set.range toPath ⊆ U i ∪ U j

namespace SelectPath

/-- A select path evaluates through its underlying path. -/
instance instCoeFun {X : Type u} [TopologicalSpace X] {ι : Type v} {U : ι → Set X}
    {p : (i : ι) → U i} {i j : ι} : CoeFun (SelectPath U p i j) (fun _ ↦ unitInterval → X) where
  coe g := g.toPath

/-- A select path and its underlying path have the same values. -/
@[simp]
theorem coe_apply {X : Type u} [TopologicalSpace X] {ι : Type v} {U : ι → Set X}
    {p : (i : ι) → U i} {i j : ι} (g : SelectPath U p i j) (t : unitInterval) :
    g t = g.toPath t := rfl

/-- Every point of a select path lies in the union of its two indexed sets. -/
theorem mem_union {X : Type u} [TopologicalSpace X] {ι : Type v} {U : ι → Set X}
    {p : (i : ι) → U i} {i j : ι} (g : SelectPath U p i j) (t : unitInterval) :
    g t ∈ U i ∪ U j :=
  g.range_subset_union ⟨t, rfl⟩

/-- The distinguished points are joined inside the union by the underlying select path. -/
theorem joinedIn {X : Type u} [TopologicalSpace X] {ι : Type v} {U : ι → Set X}
    {p : (i : ι) → U i} {i j : ι} (g : SelectPath U p i j) :
    JoinedIn (U i ∪ U j) (p i) (p j) :=
  ⟨g.toPath, g.mem_union⟩

end SelectPath

end
