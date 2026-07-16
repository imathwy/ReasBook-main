import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_0_13
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_0_21
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_1_1
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Theorem_5_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DikinEllipsoidNotation Gradient HessianLocalNorm SelfConcordantAuxiliaryFunction

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.1.9 lies in the Chapter 5 self-concordance / local Taylor-upper-bound domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the chapter owner for quantitative
  self-concordance;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Definition_5_1_1`, the owner for the
  local Hessian norm;
* `IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset` and
  `IsSelfConcordantOnWith.displacement_localNorm_upper_bound` from `Theorem_5_1_5`, the canonical
  owner-level admissible-step transport API;
* `ω_* : Set.Iio (1 : ℝ) → ℝ` and `selfConcordantOmegaStarArg` from `Definition_5_0_21`, the
  chapter owners for the self-concordant upper remainder.

Source/core/bridge triage:
* source-facing: Theorem 5.1.9 itself, stated for `IsSelfConcordantOnWith dom Mf f` and an
  admissible Dikin step `y ∈ W⁰[f; x](1 / (Mf : ℝ))`;
* core/canonical: `IsSelfConcordantOnWith dom Mf f`, `‖u‖[f; x]`, `hessian f z`, and `ω_*`;
* bridge/view: the transport-data helper below, which isolates the proof-route ingredients
  extracted canonically from the owner.

Primitive data:
* the owner witness `hself : IsSelfConcordantOnWith dom Mf f`;
* the center membership `hx : x ∈ dom`;
* the admissible-step hypothesis `hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))`.

Derived API:
* domain membership of the endpoint `y`;
* the local-norm transport bound at the endpoint;
* Hessian quadratic-form nonnegativity along the admissible step;
* the gradient-pairing and first-order Taylor upper bounds.

The numbered item is therefore owner-level. The transport-data theorem remains only as a private
proof bridge; the public theorem surface lives in `namespace IsSelfConcordantOnWith`. -/

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}
variable (hf_C2 : ContDiffOn ℝ 2 f dom)
variable (hstep :
  ∀ ⦃x h : E⦄, x ∈ dom → ‖h‖[f; x] < 1 / (Mf : ℝ) → x + h ∈ dom)
variable (htransport :
  ∀ ⦃x h : E⦄, x ∈ dom → x + h ∈ dom →
    ‖h‖[f; x] < 1 / (Mf : ℝ) →
      ‖h‖[f; x + h] ≤ ‖h‖[f; x] / (1 - (Mf : ℝ) * ‖h‖[f; x]))
variable (hquad_nonneg :
  ∀ ⦃x h : E⦄, x ∈ dom → x + h ∈ dom →
    ‖h‖[f; x] < 1 / (Mf : ℝ) →
      0 ≤ inner ℝ h (hessian f (x + h) h))

include hf_C2 hstep htransport hquad_nonneg

-- Proof sketch: set `h := y - x` and `r := ‖h‖[f; x]`. For the gradient pairing, integrate
-- `τ ↦ inner ℝ h (hessian f (x + τ • h) h)` along the segment, use the admissible-step
-- hypothesis to keep the segment inside `dom`, apply the local-norm transport bound and
-- `hessianLocalNorm_def` pointwise together with `Real.sq_sqrt` using `hquad_nonneg`, and
-- evaluate the resulting scalar
-- integral `∫₀¹ r² / (1 - τ M_f r)²`. For the function-value estimate, integrate the first bound
-- once more along the same segment and compute
-- `∫₀¹ τ r² / (1 - τ M_f r) = M_f⁻² ω_*(M_f r)`.
private theorem localNorm_gradient_pairing_and_value_upper_bounds_of_transport_data
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[f; x]
    let τω := selfConcordantOmegaStarArg Mf r (by
      exact mf_mul_lt_one_of_lt_inv <|
        by simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy)
    inner ℝ (∇ f y - ∇ f x) (y - x) ≤
        r ^ (2 : ℕ) / (1 - (Mf : ℝ) * r) ∧
      f y ≤
        f x + inner ℝ (∇ f x) (y - x) +
          (1 / ((Mf : ℝ) ^ (2 : ℕ))) * ω_* τω := sorry

end

namespace IsSelfConcordantOnWith

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}

-- Proof sketch: feed the source-facing Theorem 5.1.9 with the canonical owner data already
-- available from `IsSelfConcordantOnWith dom Mf f` and Theorem 5.1.5: `C²` regularity comes from
-- `contDiffOn`, admissible steps stay in `dom` by `openDikinEllipsoid_inv_constant_subset`, the
-- local-norm transport bound is `displacement_localNorm_upper_bound`, and Hessian
-- positive-semidefiniteness is `hessian_posSemidef`.
/-- Under the Chapter 5 owner `IsSelfConcordantOnWith dom Mf f`, every admissible Dikin step
satisfies the gradient-pairing and first-order Taylor upper bounds from Theorem 5.1.9. This is
the canonical owner-level bridge from self-concordance to the source-facing local estimate. -/
theorem localNorm_gradient_pairing_and_value_upper_bounds
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[f; x]
    let τω := selfConcordantOmegaStarArg Mf r (by
      exact mf_mul_lt_one_of_lt_inv <|
        by simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy)
    inner ℝ (∇ f y - ∇ f x) (y - x) ≤
        r ^ (2 : ℕ) / (1 - (Mf : ℝ) * r) ∧
      f y ≤
        f x + inner ℝ (∇ f x) (y - x) +
          (1 / ((Mf : ℝ) ^ (2 : ℕ))) * ω_* τω := by
  let hf_C2 : ContDiffOn ℝ 2 f dom := hself.contDiffOn.of_le (by norm_num)
  let hstep :
      ∀ ⦃x h : E⦄, x ∈ dom → ‖h‖[f; x] < 1 / (Mf : ℝ) → x + h ∈ dom :=
    fun {x h} hx hh ↦
      (openDikinEllipsoid_inv_constant_subset hself hx)
        ((mem_openDikinEllipsoid_iff f x (x + h) (1 / (Mf : ℝ))).2 (by simpa using hh))
  let htransport :
      ∀ ⦃x h : E⦄, x ∈ dom → x + h ∈ dom →
        ‖h‖[f; x] < 1 / (Mf : ℝ) →
          ‖h‖[f; x + h] ≤ ‖h‖[f; x] / (1 - (Mf : ℝ) * ‖h‖[f; x]) :=
    fun {x h} hx _ hh ↦
      by
        simpa using
          displacement_localNorm_upper_bound hself hx
            ((mem_openDikinEllipsoid_iff f x (x + h) (1 / (Mf : ℝ))).2 (by simpa using hh))
  let hquad_nonneg :
      ∀ ⦃x h : E⦄, x ∈ dom → x + h ∈ dom →
        ‖h‖[f; x] < 1 / (Mf : ℝ) →
          0 ≤ inner ℝ h (hessian f (x + h) h) :=
    fun {x h} _ hxh _ ↦ hself.hessian_posSemidef hxh h
  simpa using
    (localNorm_gradient_pairing_and_value_upper_bounds_of_transport_data
      hf_C2 hstep htransport hquad_nonneg hx hxy)

-- Proof sketch: project the first component of the owner-level theorem above.
/-- The owner-level gradient-pairing upper bound derived from `IsSelfConcordantOnWith dom Mf f`
and the admissible Dikin-step hypothesis. -/
theorem localNorm_gradient_pairing_upper_bound
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    inner ℝ (∇ f y - ∇ f x) (y - x) ≤
      ‖y - x‖[f; x] ^ (2 : ℕ) / (1 - (Mf : ℝ) * ‖y - x‖[f; x]) := by
  simpa using
    (localNorm_gradient_pairing_and_value_upper_bounds
      hself hx hxy).1

-- Proof sketch: project the second component of the owner-level theorem above.
/-- The owner-level Taylor upper bound with remainder `ω_*`, derived from
`IsSelfConcordantOnWith dom Mf f` and the admissible Dikin-step hypothesis. -/
theorem localNorm_taylor_upper_bound_with_selfConcordantOmegaStar
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[f; x]
    let τω := selfConcordantOmegaStarArg Mf r (by
      exact mf_mul_lt_one_of_lt_inv <|
        by simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy)
    f y ≤
      f x + inner ℝ (∇ f x) (y - x) +
        (1 / ((Mf : ℝ) ^ (2 : ℕ))) * ω_* τω := by
  simpa using
    (localNorm_gradient_pairing_and_value_upper_bounds
      hself hx hxy).2

end

end IsSelfConcordantOnWith

end
