module

import Mathlib.Topology.PartitionOfUnity

universe u

/- Definition 36.4. Let `U : Fin n → Set X` be a finite indexed open cover of
`X`, so each `U i` is open and `⋃ i, U i = Set.univ`. A partition of unity
dominated by `U` is canonically represented by
`ρ : PartitionOfUnity (Fin n) X Set.univ` together with
`ρ.IsSubordinate U`, which says `tsupport (ρ i) ⊆ U i` for every `i`.
The continuous real-valued functions `ρ i` take values in `[0, 1]` by
`ρ.nonneg` and `ρ.le_one`, and `ρ.sum_eq_one` gives their pointwise finite sum
as `1` on all of `X`. -/
#check PartitionOfUnity
#check PartitionOfUnity.IsSubordinate
#check PartitionOfUnity.nonneg
#check PartitionOfUnity.le_one
#check PartitionOfUnity.sum_eq_one
#check fun {X : Type u} [TopologicalSpace X] {n : ℕ} (U : Fin n → Set X)
    (ρ : PartitionOfUnity (Fin n) X Set.univ) ↦ ρ.IsSubordinate U
