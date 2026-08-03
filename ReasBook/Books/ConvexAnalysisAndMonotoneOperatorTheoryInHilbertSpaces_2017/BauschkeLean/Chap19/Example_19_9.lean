import Mathlib
import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Proposition_12_32
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap16.Example_16_32
import BauschkeLean.Chap19.Example_19_8
import BauschkeLean.Chap19.Proposition_19_5

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

noncomputable section

universe u v

namespace ERealFunction

section PrimalSolutionsViaDualSolutions

variable {H : Type u} {G : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/- Source/core/bridge triage:
- `source-facing`: Example 19.9 is the cone-constrained residual-norm proximal problem
  `(19.15)` and its dual `(19.16)`.
- `core/canonical`: Proposition 19.5 is the proximal-composite dual-attainment owner.
- `bridge/view`: specialize Proposition 19.5 to `φ = ι[K]` and `ψ = ‖·‖`, then use
  Example 13.3 (5) for the conjugate of the norm, Example 12.25 for the projection form of the
  indicator proximity operator, and Proposition 12.32 for the cone-distance rewrite.
- Semantic recall note: `lean_leansearch` was unavailable in this session, so the owner search was
  verified from local Chapter 12, 13, and 19 precedent.
-/

variable (K : Set H) (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K)
variable (hK_convex : Convex ℝ K) (hK_cone : IsCone K)
variable (z : H) (r : G) (L : H →L[ℝ] G)

local notation "hK_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hK_nonempty hK_closed hK_convex

local notation "P_K" => P[K, hK_cheb]
local notation "unitBall" => Metric.closedBall (0 : G) 1
local notation "dualObj" =>
  fun v : G ↦
    ((1 / 2 : ℝ) * Metric.infDist (z - L.adjoint v) (Kᵒ⊖ : Set H) ^ 2 + ⟪v, r⟫_ℝ : ℝ)
local notation "primalObj" =>
  fun x : H ↦ (‖L x - r‖ + (1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ)

/-- Helper for Example 19.9: at the origin, the norm subdifferential is the closed unit ball. -/
lemma subdifferential_norm_zero_eq_closedUnitBall :
    (∂ ((norm : G → ℝ).toEReal)) (0 : G) = Metric.closedBall (0 : G) 1 := by
  -- Example 16.32 evaluates the norm subdifferential explicitly and the origin picks the ball branch.
  simpa using subdifferential_norm_eq_singleton_or_closedBall (x := (0 : G))

/-- Example 19.9 (1): if `K` is a nonempty closed convex cone in a real Hilbert space, then the
dual problem `(19.16)`,
`min { (1 / 2) d_{Kᵒ⊖}(z - L^* v)^2 + ⟪v, r⟫ | ‖v‖ ≤ 1 }`,
has at least one solution. -/
theorem argminOn_dual_unitBall_nonempty_for_cone_residualNorm_problem :
    (Argmin[unitBall] dualObj).Nonempty := by
  -- Specialize Example 19.8 to `ψ = ‖·‖` and rewrite `(∂ψ)(0)` as the unit ball.
  simpa [unitBall, dualObj, subdifferential_norm_zero_eq_closedUnitBall] using
    (argminOn_dual_subdifferential_zero_nonempty_for_cone_positivelyHomogeneous_problem
      (K := K) (ψ := (norm : G → ℝ).toEReal) (z := z) (r := r) (L := L))

/-- Example 19.9 (2): if `v` solves the dual problem `(19.16)`, then the unique solution of the
cone-constrained primal problem `(19.15)`,
`min { ‖Lx - r‖ + (1 / 2) ‖x - z‖^2 | x ∈ K }`,
is the metric projection `P_K (z - L^* v)`. -/
theorem argminOn_cone_residualNorm_plus_half_sqDist_eq_singleton_projection_of_mem_dualArgmin
    {v : G} (hv : v ∈ Argmin[unitBall] dualObj) :
    Argmin[K] primalObj = ({P_K (z - L.adjoint v)} : Set H) := by
  have hv' : v ∈ Argmin[(∂ ((norm : G → ℝ).toEReal)) (0 : G)] dualObj := by
    -- Convert the closed-unit-ball feasible set into Example 19.8's subdifferential notation.
    simpa [unitBall, subdifferential_norm_zero_eq_closedUnitBall] using hv
  -- Apply the primal-recovery statement from Example 19.8 after the same specialization.
  simpa [primalObj] using
    (argminOn_cone_positivelyHomogeneous_plus_half_sqDist_eq_singleton_projection_of_mem_dualArgmin
      (K := K) (hK_nonempty := hK_nonempty) (hK_closed := hK_closed)
      (hK_convex := hK_convex) (ψ := (norm : G → ℝ).toEReal)
      (z := z) (r := r) (L := L) hv')

end PrimalSolutionsViaDualSolutions

end ERealFunction
