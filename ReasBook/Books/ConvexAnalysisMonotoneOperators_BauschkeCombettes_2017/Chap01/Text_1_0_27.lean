import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set

namespace EReal

/-- Text 1.0.27: the extended interval `]ξ, +∞]` is the usual real interval `]ξ, +∞[`,
embedded into `EReal`, with the point `+∞` adjoined. -/
theorem openClosedUpperInfiniteInterval_eq_image_Ioi_union_top (ξ : ℝ) :
    Ioi (ξ : EReal) = Real.toEReal '' Ioi ξ ∪ ({(⊤ : EReal)} : Set EReal) := by
  rw [image_coe_Ioi]
  ext x
  simp [lt_top_iff_ne_top]

end EReal
