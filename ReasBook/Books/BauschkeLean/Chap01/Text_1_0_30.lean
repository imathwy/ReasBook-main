import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

universe u

namespace Net

variable {A : Type u} [Nonempty A] [Preorder A] [IsDirectedOrder A]

/-- Text 1.0.30: for an `EReal`-valued net on a nonempty directed index set, the lower limit is
bounded above by the upper limit. -/
theorem liminf_le_limsup (ξ : A → EReal) :
    liminf ξ atTop ≤ limsup ξ atTop := by
  simpa using (Filter.liminf_le_limsup : liminf ξ atTop ≤ limsup ξ atTop)

end Net
