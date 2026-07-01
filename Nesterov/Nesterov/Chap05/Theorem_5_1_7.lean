import Mathlib
import Nesterov.Chap05.Definition_5_0_13
import Nesterov.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm DikinEllipsoidNotation

noncomputable section

universe u

/-
Theorem 5.1.7 lies in the Chapter 5 self-concordance / Hessian-comparison domain.

Sampled owner-style declarations in this domain:
* `hessian` from `Chap01/Definition_1_4_16`, the canonical second-order owner replacing the raw
  `fderiv ℝ (∇ f)` surface;
* `thirdDirectionalDerivative` from `Chap05/Definition_5_0_10`, the source-facing Chapter 5 owner
  for the cubic derivative `D³f(x)[u,u,u]`;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Definition_5_1_1`, the chapter owner for
  the Hessian local norm;
* `openDikinEllipsoid` together with the notation `W⁰[f; x](r)` and
  `mem_openDikinEllipsoid_iff` from `Definition_5_0_13`, the owner and bridge for the
  Dikin-radius hypothesis `y ∈ W⁰[f; x](1 / M_f)`;
* `selfConcordant_diagonal_bound_iff_trilinear_bound` from `Lemma_5_1_2`, the canonical bridge
  from the Chapter 5 cubic owner surface to the full trilinear third-derivative estimate;
* `selfConcordant_iff_thirdDerivative_operator_le` from `Corollary_5_1_1`, the operator-level
  bridge from the same cubic owner surface to a Hessian differential inequality;
* `IsSelfConcordantOnWith.hessian_loewner_bounds_of_mem_openDikinEllipsoid` from
  `Proposition_5_0_15`, the stronger operator-level comparison theorem under the bundled owner
  `IsSelfConcordantOnWith dom Mf f`.

Source/core/bridge triage:
* source-facing: the segment-local Hessian operator comparison at `x` and `y`;
* core/canonical: `hessian f z`, `‖u‖[f; z]`, and `W⁰[f; x](r)`;
* bridge/view: `mem_openDikinEllipsoid_iff`, the scalarized quadratic-form inequalities obtained
  by testing the operator bounds on a direction `h`, and the stronger bundled-owner Loewner
  comparison from `Proposition_5_0_15`.

Primitive data:
* an open set `dom` containing the segment from `x` to `y`;
* `C³` regularity of `f` on `dom`;
* pointwise positivity of the Hessian along the segment from `x` to `y`;
* the Chapter 5 diagonal cubic bound on `thirdDirectionalDerivative f z u` along that segment;
* the Dikin-radius membership of `y`.

Derived API:
* the lower and upper Loewner-order comparison of the endpoint Hessians;
* the quadratic-form inequalities obtained from that operator comparison by evaluating on a
  direction `h`.

This theorem remains source-facing because the sampled bundled owner
`IsSelfConcordantOnWith dom Mf f` from `Definition_5_1_1` would strengthen the assumptions to a
global convex-domain self-concordance hypothesis. The refinement therefore keeps the original
segment-local semantics but moves the main public surface from the quadratic-form bridge to the
canonical Hessian owner already used by `hessianLocalNorm`, `openDikinEllipsoid`, and the nearby
Loewner-order API. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: for each fixed direction `h`, scalarize the Hessian operator along the segment by
-- `ψ_h(t) = inner ℝ h (hessian f (x + t • (y - x)) h)`. The diagonal Chapter 5 cubic bound on
-- `thirdDirectionalDerivative` converts, via the standard local bridge to the Hessian
-- differential inequality, into control of `|ψ_h'(t)|` by the local norm of `y - x` at the
-- intermediate point times `ψ_h(t)`. Use the Dikin-radius hypothesis
-- `y ∈ W⁰[f; x](1 / M_f)` together with the standard local norm comparison along
-- the segment to obtain
-- `|ψ_h'(t)| ≤ 2 M_f r / (1 - t M_f r) * ψ_h(t)`, integrate the differential inequality for
-- `log ψ_h(t)`, and then reassemble the resulting pointwise quadratic-form bounds into the
-- Loewner-order comparison of the endpoint Hessians. The Dikin-radius hypothesis already rules
-- out the degenerate `Mf = 0` case, since then `W⁰[f; x](1 / (Mf : ℝ))` is empty.
/-- Theorem 5.1.7: if `f` is `C³` on an open set containing the segment from `x` to `y`, its
third directional derivative satisfies the Chapter 5 local-norm bound with constant `M_f` along
that segment, the Hessian is positive along the segment, and `y ∈ W⁰[f; x](1 / M_f)`, then with
`r = ‖y - x‖[f; x]` the Hessians at `x` and `y` satisfy the Loewner-order bounds
`(1 - M_f r)^2 • ∇²f(x) ≤ ∇²f(y) ≤ (1 - M_f r)⁻² • ∇²f(x)`. -/
theorem hessian_loewner_bounds_along_segment
    {dom : Set E} {Mf : NNReal} {f : E → ℝ} {x y : E}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hsegment : segment ℝ x y ⊆ dom)
    (hpsd : ∀ ⦃z : E⦄, z ∈ segment ℝ x y → (hessian f z).IsPositive)
    (hthird : ∀ ⦃z : E⦄ (hz : z ∈ segment ℝ x y) (u : E),
      |thirdDirectionalDerivative f z u| ≤
        2 * (Mf : ℝ) * ‖u‖[f; z] ^ (3 : ℕ))
    (hy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[f; x]
    ((1 - (Mf : ℝ) * r) ^ (2 : ℕ)) • hessian f x ≤ hessian f y ∧
      hessian f y ≤ ((1 - (Mf : ℝ) * r) ^ (2 : ℕ))⁻¹ • hessian f x := sorry

end
