import BauschkeLean.Chap02.Definition_2_54
import BauschkeLean.Chap08.Definition_8_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Example 17.49 records regularity properties of the quadratic
  `x ↦ (f x) ^ 2` attached to a real linear functional.
- `core/canonical`: the owner abstractions are `ConvexOn`,
  `Function.effectiveDomain_toEReal`, `_root_.GateauxDifferentiableAt`,
  `LowerSemicontinuousAt` on the direct `EReal` coercion, `ContinuousAt`, and `DifferentiableAt`.
- `bridge/view`: `Function.toEReal` is only the finite-valued bridge needed for the effective-domain
  clause; the lower-semicontinuity clause should live directly on the `EReal`-valued owner surface
  instead of on the composite bridge `toEReal.asEReal`. For the failure clauses, the relevant
  continuity owner is pointwise continuity at `0`; for linear maps this is the intrinsic local form
  of global continuity failure.

Primitive data: a bare linear functional `f : H →ₗ[ℝ] ℝ`.
Derived API: convexity, full `EReal` domain, Gâteaux differentiability at `0`,
lower semicontinuity at `0`, and failure of continuity/differentiability when `f` is
discontinuous. -/

section Algebraic

variable {H : Type u} [AddCommMonoid H] [Module ℝ H]

-- Proof sketch: apply the canonical scalar owner `Even.convexOn_pow` to `t ↦ t ^ 2` on `ℝ`, then
-- compose with the linear owner `f` via `ConvexOn.comp_linearMap`.
/-- Example 17.49 (1): if `g = f^2` for a real linear functional `f`, then `g` is convex on the
whole space. -/
theorem convexOn_univ_sq_linearForm (f : H →ₗ[ℝ] ℝ) :
    ConvexOn ℝ Set.univ (fun x : H ↦ (f x) ^ 2) := sorry

-- Proof sketch: this is the direct specialization of the canonical owner theorem
-- `Function.effectiveDomain_toEReal` to the quadratic `x ↦ (f x)^2`.
/-- Example 17.49 (2): after coercion to `]-∞,+∞]`, the square `g = f^2` has full domain. -/
theorem effectiveDomain_sq_linearForm_toEReal_eq_univ (f : H →ₗ[ℝ] ℝ) :
    effectiveDomain ((fun x : H ↦ (f x) ^ 2).toEReal) = Set.univ := sorry

end Algebraic

section Gateaux

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

-- Proof sketch: along every line through the origin, the restriction of `x ↦ (f x)^2` is the
-- scalar quadratic `t ↦ (t * f y)^2`, whose derivative at `0` is `0`.
/-- Example 17.49 (3): the square `g = f^2` is Gâteaux differentiable at `0`. -/
theorem gateauxDifferentiableAt_sq_linearForm_zero (f : H →ₗ[ℝ] ℝ) :
    GateauxDifferentiableAt (fun x : H ↦ (f x) ^ 2) (0 : H) := sorry

end Gateaux

section LowerSemicontinuity

variable {H : Type u} [TopologicalSpace H] [AddCommMonoid H] [Module ℝ H]

-- Proof sketch: the direct `EReal`-valued coercion `x ↦ ((f x)^2 : EReal)` is nonnegative
-- everywhere, so every strict lower bound of its value `0` at the origin is automatically
-- satisfied on all neighborhoods of `0`.
/-- Example 17.49 (4): after coercion to `]-∞,+∞]`, the square `g = f^2` is lower
semicontinuous at `0`. -/
theorem lowerSemicontinuousAt_sq_linearForm_zero (f : H →ₗ[ℝ] ℝ) :
    LowerSemicontinuousAt (fun x : H ↦ ((f x) ^ 2 : EReal)) (0 : H) := sorry

end LowerSemicontinuity

section Normed

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

-- Proof sketch: if `x ↦ (f x)^2` were continuous at `0`, then some neighborhood of `0` would make
-- `|f x|^2` uniformly small, hence `|f x|` uniformly bounded. A linear map that is bounded on a
-- neighborhood of `0` is continuous at `0`, contradicting the hypothesis.
/-- Example 17.49 (5): if `f` is not continuous at `0`, then `g = f^2` is not continuous at `0`. -/
theorem not_continuousAt_sq_linearForm_zero_of_not_continuousAt_zero (f : H →ₗ[ℝ] ℝ)
    (hfdisc : ¬ ContinuousAt f (0 : H)) :
    ¬ ContinuousAt (fun x : H ↦ (f x) ^ 2) (0 : H) := sorry

-- Proof sketch: Fréchet differentiability at a point implies continuity there. Apply this to
-- `g = f^2` and use the previous clause to rule out continuity at the origin.
/-- Example 17.49 (6): if `f` is not continuous at `0`, then `g = f^2` is not Fréchet
differentiable at `0`. -/
theorem not_differentiableAt_sq_linearForm_zero_of_not_continuousAt_zero (f : H →ₗ[ℝ] ℝ)
    (hfdisc : ¬ ContinuousAt f (0 : H)) :
    ¬ DifferentiableAt ℝ (fun x : H ↦ (f x) ^ 2) (0 : H) := sorry

end Normed
