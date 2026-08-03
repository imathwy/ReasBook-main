module

public import Mathlib.Topology.Constructions

public section

universe u

open Topology

/- Theorem 17.4: If `A` is a subset of a subspace `Y` of `X`, then its closure in
`Y` is the inverse image of the closure of its image in `X`. -/
#check IsEmbedding.subtypeVal.closure_eq_preimage_closure_image

/-- The ambient image of the closure of `A : Set Y` is the ambient closure of
its image intersected with `Y`. -/
theorem image_closure_eq_inter {X : Type u} [TopologicalSpace X]
    (Y : Set X) (A : Set Y) :
    Subtype.val '' closure A = closure (Subtype.val '' A) ∩ Y := by
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image A,
    Set.image_preimage_eq_inter_range, Subtype.range_coe]
