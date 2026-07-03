import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_4_15 (from Chap04/Sec04_23) -/
-- Semantic search tool unavailable in this environment; local precedents used:
-- `Theorem_4_12`, `Problem_4_1`, and nearby manifold-with-boundary files using `𝓡∂ n`.

noncomputable section

open Set
open scoped ContDiff Manifold

universe uM uN

section LocalImmersionBoundary

variable {m n : ℕ}
variable [NeZero m]
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace m) M]
  [IsManifold (𝓡∂ m) ∞ M]
variable {N : Type uN} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ N]

local notation "J_m" => 𝓡∂ m
local notation "I_n" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

/-- The half-space normal form for an immersion sends a boundary-model point to the corresponding
ambient `m`-tuple followed by `0` in the remaining target coordinates. -/
def boundary_immersion_normal_form (m n : ℕ) [NeZero m] :
    EuclideanHalfSpace m → EuclideanSpace ℝ (Fin n) :=
  fun x ↦ rank_normal_form m n m x.1

/-- On a half-space point, the boundary immersion normal form is the rank-`m` Euclidean normal
form applied to the underlying ambient coordinate tuple. -/
theorem boundary_immersion_normal_form_apply (x : EuclideanHalfSpace m) :
    boundary_immersion_normal_form m n x = rank_normal_form m n m x.1 := rfl

/-- A local coordinate normal form for a map from a manifold with boundary to a boundaryless
manifold consists of a centered smooth boundary chart on the source and a centered smooth chart on
the target in which the coordinate representative agrees with a prescribed half-space model map. -/
structure BoundaryLocalCoordinateNormalFormAt (F : M → N) (p : M)
    (normalForm : EuclideanHalfSpace m → EuclideanSpace ℝ (Fin n)) where
  domChart : OpenPartialHomeomorph M (EuclideanHalfSpace m)
  codChart : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin n))
  domChart_mem_maximalAtlas :
    domChart ∈ IsManifold.maximalAtlas J_m ∞ M
  codChart_mem_maximalAtlas :
    codChart ∈ IsManifold.maximalAtlas I_n ∞ N
  domChart_centered : p ∈ domChart.source ∧ domChart p = 0
  codChart_centered : F p ∈ codChart.source ∧ codChart (F p) = 0
  mapsTo : MapsTo F domChart.source codChart.source
  eqOn : EqOn (codChart ∘ F ∘ domChart.symm) normalForm domChart.target

namespace BoundaryLocalCoordinateNormalFormAt

/-- Any boundary local coordinate normal form carries the source chart domain into the target chart
domain. -/
theorem mapsTo_source {F : M → N} {p : M}
    {normalForm : EuclideanHalfSpace m → EuclideanSpace ℝ (Fin n)}
    (h : BoundaryLocalCoordinateNormalFormAt F p normalForm) :
    MapsTo F h.domChart.source h.codChart.source := sorry

end BoundaryLocalCoordinateNormalFormAt

/-- Theorem 4.15 (Local Immersion Theorem for Manifolds with Boundary): if `F : M → N` is a smooth
immersion, with `M` a smooth `m`-manifold with boundary and `N` a smooth `n`-manifold, then every
boundary point `p ∈ ∂M` admits a centered smooth boundary chart on `M` and a centered smooth
coordinate chart on `N` in which `F` is written as `(x¹, …, xᵐ) ↦ (x¹, …, xᵐ, 0, …, 0)`. -/
theorem smooth_immersion_boundary_local_inclusion_form {F : M → N}
    (hF : Manifold.IsImmersion J_m I_n ∞ F) {p : M} (hp : p ∈ (𝓡∂ m).boundary M) :
    ∃ h : BoundaryLocalCoordinateNormalFormAt F p (boundary_immersion_normal_form m n), True :=
  sorry

end LocalImmersionBoundary
