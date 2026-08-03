module

public import Topology_Munkres_2000.Book.Definition_22_4
public import Mathlib.Data.Setoid.Partition

public section

universe u

namespace Setoid.Partitions

variable {X : Type u}

/-- The block of a partition containing `x`. -/
def block (P : Partitions X) (x : X) : P.toSet :=
  ⟨{y | mkClasses P.toSet P.isPartition.2 y x}, by
    have h : {y | mkClasses P.toSet P.isPartition.2 y x} ∈
        (mkClasses P.toSet P.isPartition.2).classes := mem_classes _ x
    rw [classes_mkClasses P.toSet P.isPartition] at h
    exact h⟩

/-- A point belongs to its block. -/
theorem mem_block (P : Partitions X) (x : X) : x ∈ (P.block x : Set X) :=
  (mkClasses P.toSet P.isPartition.2).refl' x

/-- A block containing `x` is the block selected by `P.block`. -/
theorem eq_block_of_mem (P : Partitions X) {x : X} {s : P.toSet}
    (hx : x ∈ (s : Set X)) : s = P.block x := by
  apply Subtype.ext
  exact (P.isPartition.2 x).unique ⟨s.property, hx⟩
    ⟨(P.block x).property, P.mem_block x⟩

/-- Two points have the same block exactly when they lie in the same block of `P`. -/
theorem block_eq_iff (P : Partitions X) (x y : X) :
    P.block x = P.block y ↔ y ∈ (P.block x : Set X) := by
  constructor
  · intro h
    rw [h]
    exact P.mem_block y
  · intro hy
    exact P.eq_block_of_mem hy

/-- The canonical map from a type to the blocks of a partition is surjective. -/
theorem block_surjective (P : Partitions X) : Function.Surjective P.block := by
  intro s
  obtain ⟨x, hx⟩ := nonempty_of_mem_partition P.isPartition s.property
  exact ⟨x, (P.eq_block_of_mem hx).symm⟩

/-- The quotient topology on the blocks of `P`, coinduced by the canonical block map. -/
@[reducible]
def quotientTopology [t : TopologicalSpace X] (P : Partitions X) : TopologicalSpace P.toSet :=
  t.coinduced P.block

/-- The topology on the blocks of `P` is the quotient topology induced by the canonical block
map. -/
theorem isQuotientTopology [t : TopologicalSpace X] (P : Partitions X) :
    Topology.IsQuotientTopology t P.block P.quotientTopology := by
  rw [Topology.isQuotientTopology_iff]
  exact ⟨rfl, P.block_surjective⟩

end Setoid.Partitions

end
