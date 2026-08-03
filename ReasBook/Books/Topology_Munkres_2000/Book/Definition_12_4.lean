module

public import Mathlib.Order.Comparable
public import Mathlib.Topology.Order

universe u

/-
Definition 12.4. For topologies `𝒯` and `𝒯'` on `X`:
* `𝒯' ≤ 𝒯` means that `𝒯'` is finer than `𝒯`;
* `𝒯' < 𝒯` means that `𝒯'` is strictly finer than `𝒯`;
* `𝒯 ≤ 𝒯'` and `𝒯 < 𝒯'` mean respectively that `𝒯` is coarser and
  strictly coarser than `𝒯'`;
* `Relation.SymmGen (· ≤ ·) 𝒯 𝒯'` means that `𝒯` and `𝒯'` are comparable.
-/
#check fun {X : Type u} (𝒯 𝒯' : TopologicalSpace X) ↦ 𝒯' ≤ 𝒯
#check fun {X : Type u} (𝒯 𝒯' : TopologicalSpace X) ↦ 𝒯' < 𝒯
#check fun {X : Type u} (𝒯 𝒯' : TopologicalSpace X) ↦ 𝒯 ≤ 𝒯'
#check fun {X : Type u} (𝒯 𝒯' : TopologicalSpace X) ↦ 𝒯 < 𝒯'
#check fun {X : Type u} (𝒯 𝒯' : TopologicalSpace X) ↦ Relation.SymmGen (· ≤ ·) 𝒯 𝒯'
