import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_0_21
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_0_20
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_3_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_53

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianDualLocalNorm SelfConcordantAuxiliaryFunction

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Lemma 7.10 lies in the Chapter 7 barrier-smoothed support-function / self-concordant upper-model
domain.

Mandatory domain-style sampling before refinement:
- `Uβ` and `Argmaxβ` in `Chap07/Definition_7_53`, the Chapter 7 source-facing owners of the
  smoothed support-function value and its canonical argmax set;
- `smoothedPrimalObjectiveArgmax_unique` in `Chap06/Proposition_6_24` and
  `supportFunctionApproximation_hasFDerivAt_of_unique_argmax` in `Chap07/Proposition_7_28`, the
  owner-level uniqueness and derivative bridge for the positive support-function smoothing problem;
- `Uβ_apply` in `Chap07/Definition_7_53`, the source-facing expansion theorem for `U_β`;
- `IsSelfConcordantBarrierOnWith` in `Chap05/Definition_5_3_2`, the chapter owner for the
  self-concordant barrier structure on `interior Q`;
- `dualLocalNorm` and the determinant bridge `HessianDualLocalNorm.ofDetNeZero` in
  `Chap05/Definition_5_0_20`, the canonical owner of the Hessian dual local norm;
- `selfConcordant_value_bounds_of_dualLocalNorm_gradient_sub` in `Chap05/Theorem_5_1_12`, the
  owner-level Chapter 5 upper/lower value estimate that actually justifies the `ω_*` remainder;
- `ω_*` in `Chap05/Definition_5_0_21`, the canonical Chapter 5 owner of the self-concordant upper
  remainder term.

Best owner abstraction:
- source-facing: Lemma 7.10's derivative identification and upper model for the specialized
  support-function approximation `U_β`;
- core/canonical: `Uβ`, `Argmaxβ`,
  `IsSelfConcordantBarrierOnWith (interior Q) ν F`,
  `HessianDualLocalNorm.ofDetNeZero F x hPos hH g`, and `ω_*`;
- bridge/view: the derivative bridge from unique argmax data together with the Hilbert-space
  evaluation map `x - x₀`.

Primitive data:
- the feasible set `hatP`, ambient barrier set `Q`, barrier `F`, base point `x₀`, and smoothing
  parameter `β`;
- the active maximizer `x` at the dual point `s`;
- the self-concordant barrier owner on `interior Q`;
- the local Hessian nondegeneracy data at `x`.

Derived API:
- the smoothed support-function value owner `Uβ`;
- the argmax predicate owner `Argmaxβ`;
- the local Hessian positivity at `x`, derived from the barrier owner and `hx_int`;
- the local perturbation size `HessianDualLocalNorm.ofDetNeZero F x hPos hH g`;
- the self-concordant remainder `ω_*`.

This lemma stays source-facing: it adds the support-function-specific derivative and perturbation
statement, so it should not collapse to the more general Chapter 6 owner theorem. The refinement
therefore keeps the local statement but rewrites its public surface to the existing owner
abstractions instead of mixing raw `fderiv`/logarithm formulas with the chapter owners. The
Fréchet-derivative clause must still pass through the unique-argmax bridge; the barrier-local
interior and Hessian hypotheses control only the self-concordant upper model, not uniqueness of
the maximizer in the canonical argmax owner.
-/

section

variable (hatP Q : Set E) (F : E → ℝ) (x0 : E) (β : {β : ℝ // 0 < β})
-- Proof sketch: under the additional owner-level uniqueness hypothesis on `x` inside
-- `Argmaxβ hatP F β s`, apply the Chapter 7 unique-argmax derivative bridge to identify the
-- Fréchet derivative of `Uβ hatP F x0 β` as evaluation at `x - x0`. For the upper
-- model, compare the value at `s + g` with the value at the maximizer `x`, use the Chapter 5
-- self-concordant barrier owner on `interior Q` to derive the needed local Hessian positivity and
-- value bound for `F`, estimate the linear term by the local dual norm
-- `HessianDualLocalNorm.ofDetNeZero F x hPos hH g`, and then invoke the Fenchel conjugacy
-- between the self-concordant auxiliary functions `ω` and `ω_*`.
/-- Lemma 7.10: if `x` is the barrier-regularized maximizer defining `U_β(s)` and lies in the
strict barrier domain, then uniqueness of `x` in the canonical argmax owner at `s` yields the
Fréchet derivative formula `D U_β(s) = ev_{x - x0}`. Moreover, if `F` is a
self-concordant barrier on `interior Q`, then every perturbation `g` with local dual norm
`HessianDualLocalNorm.ofDetNeZero F x hPos hH g < β` satisfies the upper model
`U_β(s + g) ≤ U_β(s) + g (x - x0) + β ω_*(‖g‖*ₓ / β)`, expressed through the canonical
Chapter 5 owner `ω_*`. -/
theorem smoothSupportFunctionApproximation_hasFDerivAt_and_omegaStar_upper_bound
    {ν : NNReal} {s : StrongDual ℝ E} {x : E}
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hx_int : x ∈ interior Q)
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hH : (hessian F x).det ≠ 0) :
    let hPos := hF.toIsStandardSelfConcordantOn.hessian_isPositive hx_int
    ((∀ y : E, y ∈ Argmaxβ hatP F β s → y = x) →
        HasFDerivAt (Uβ hatP F x0 β)
          (ContinuousLinearMap.apply ℝ ℝ (x - x0)) s) ∧
      ∀ g : StrongDual ℝ E,
        ∀ hg : HessianDualLocalNorm.ofDetNeZero F x hPos hH g < (β : ℝ),
        let τω : Set.Iio (1 : ℝ) := ⟨
          HessianDualLocalNorm.ofDetNeZero F x hPos hH g / (β : ℝ), by
          have hlt : HessianDualLocalNorm.ofDetNeZero F x hPos hH g < 1 * (β : ℝ) := by
            simpa [one_mul] using hg
          exact (div_lt_iff₀ β.2).2 hlt⟩
        Uβ hatP F x0 β (s + g) ≤
          Uβ hatP F x0 β s +
            g (x - x0) +
              (β : ℝ) * ω_* τω := sorry

end
