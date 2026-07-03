import Mathlib
import SmoothManifolds_Lee_2012.Chap04.Sec04_23.Theorem_4_15

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool unavailable in this environment; `lean_leansearch` was not present, so
-- this item follows the local constant-rank and boundary normal-form APIs from
-- `Exercise_4_4`, `Theorem_4_12`, and `Theorem_4_15`.

noncomputable section

open Set
open scoped ContDiff Manifold

universe uM uN

section BoundaryRankTheorem

variable {m n r : ℕ}
variable [NeZero m]
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace m) M]
  [IsManifold (𝓡∂ m) ∞ M]
variable {N : Type uN} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ N]

local notation "J_m" => 𝓡∂ m
local notation "I_n" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

/-- The half-space rank normal form keeps the first `r` ambient coordinates and sends the
remaining target coordinates to `0`. -/
def boundary_rank_normal_form (m n r : ℕ) [NeZero m] :
    EuclideanHalfSpace m → EuclideanSpace ℝ (Fin n) :=
  fun x ↦ rank_normal_form m n r x.1

/-- Problem 4-3: if `F : M → N` is a smooth map of constant rank `r`, with `M` a smooth
`m`-manifold with boundary and `N` a smooth `n`-manifold without boundary, then every boundary
point `p ∈ ∂M` admits a centered smooth boundary chart on `M` and a centered smooth coordinate
chart on `N` in which `F` is written in the standard rank-`r` normal form on the half-space. -/
theorem constant_rank_boundary_local_coordinate_normal_form {F : M → N}
    (hFsmooth : ContMDiff J_m I_n ∞ F) (hFrank : Manifold.HasConstantRank J_m I_n F r)
    {p : M} (hp : p ∈ (𝓡∂ m).boundary M) :
    ∃ h : BoundaryLocalCoordinateNormalFormAt F p (boundary_rank_normal_form m n r), True :=
  sorry

end BoundaryRankTheorem
