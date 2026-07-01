import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

namespace IsCoveringMap

variable {p : E → B}

/-- Theorem 3.2.3: a covering map `p : E → B` induces an injective homomorphism
`p_* : π₁(E, e) → π₁(B, p e)` on fundamental groups. -/
-- Proof sketch: specialize `IsCoveringMap.injective_path_homotopic_map` to loops based at `e`.
theorem fundamentalGroup_map_injective (hp : IsCoveringMap p) (e : E) :
    Function.Injective (FundamentalGroup.map ⟨p, hp.continuous⟩ e) := by
  simpa using hp.injective_path_homotopic_map e e

end IsCoveringMap
