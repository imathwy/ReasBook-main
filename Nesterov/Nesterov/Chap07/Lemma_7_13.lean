import Mathlib
import Nesterov.Chap05.Definition_5_0_20
import Nesterov.Chap05.Definition_5_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped Gradient HessianDualLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-
Lemma 7.13 lies in the Chapter 7 barrier-subgradient / self-concordant local-dual-norm domain.

Mandatory domain-style sampling before refinement:
- `IsSelfConcordantBarrierOnWith (interior Q) ν F` in `Chap05/Definition_5_3_2`, the Chapter 5
  owner for the barrier structure on the intrinsic strict feasible region;
- `dualLocalNorm` together with the determinant bridge `HessianDualLocalNorm.ofDetNeZero` in
  `Chap05/Definition_5_0_20`, the owner of the Hessian dual local norm and its determinant-based
  source-facing bridge;
- `IsSelfConcordantOnWith.hessian_isPositive` in `Chap05/Definition_5_1_1`, inherited from the
  barrier owner and supplying the local Hessian positivity needed by `dualLocalNorm`;
- mathlib `ConcaveOn`, the canonical owner for the concavity hypothesis on `interior Q`.

Best owner abstraction:
- source-facing: the dual-local-norm bound on `∇ ψ x` for a positive concave function on
  `interior Q`;
- core/canonical: `IsSelfConcordantBarrierOnWith (interior Q) ν F`, `ConcaveOn`, and
  `HessianDualLocalNorm.ofDetNeZero F x hPos hH g`;
- bridge/view: the supporting-hyperplane inequality for `ψ` along the inverse-Hessian direction.

Primitive data:
- the barrier owner on `interior Q`;
- the point `x ∈ interior Q`;
- the gradient witness for `ψ` at `x`;
- concavity and positivity of `ψ` on `interior Q`;
- Hessian nondegeneracy at `x`.

Derived API:
- local Hessian positivity at `x`, derived from the barrier owner;
- the dual local norm of the gradient covector, expressed through the Chapter 5 determinant
  bridge.

The previous statement kept both Hessian positivity and Hessian nondegeneracy as primitive public
inputs, even though positivity is already derived canonically from the barrier owner. This
refinement keeps the source-facing theorem, but moves it onto the chapter owner surface on
`interior Q` and leaves only the genuinely independent nondegeneracy witness explicit.
-/

-- Proof sketch: move from `x` in the inverse-Hessian direction of `∇ ψ x` by any local-norm
-- radius `r < 1`, use the self-concordant barrier inclusion to stay inside `interior Q`, apply
-- positivity of `ψ` at the new point, and then use the supporting-hyperplane inequality from
-- concavity together with the explicit choice of direction. Letting `r ↑ 1` yields the bound.
/-- Lemma 7.13: if `F` is a `ν`-self-concordant barrier on `interior Q` and `ψ` is a positive
concave function there, then at every interior point `x` where `ψ` has gradient `∇ ψ x`, the
dual local norm of that gradient with respect to the barrier Hessian of `F` is bounded by the
value `ψ x`. -/
theorem dualLocalNorm_gradient_le_value_of_concaveOn_pos
    {Q : Set E} {ν : NNReal} {F ψ : E → ℝ} {x : E}
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hx : x ∈ interior Q)
    (hgrad : HasGradientAt ψ (∇ ψ x) x)
    (hψ_concave : ConcaveOn ℝ (interior Q) ψ)
    (hψ_pos : ∀ ⦃y : E⦄, y ∈ interior Q → 0 < ψ y)
    (hH : (hessian F x).det ≠ 0) :
    let hPos := hF.toIsStandardSelfConcordantOn.hessian_isPositive hx
    HessianDualLocalNorm.ofDetNeZero F x hPos hH ((toDual ℝ E) (∇ ψ x)) ≤ ψ x := sorry

end
