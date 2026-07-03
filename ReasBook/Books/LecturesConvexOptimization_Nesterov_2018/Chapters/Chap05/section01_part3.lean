import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_5_1_9 (from Chap05) -/
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

/-! ### Theorem_5_1_10 (from Chap05) -/
open scoped DikinEllipsoidNotation HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.1.10 lies in the Chapter 5 self-concordance / Dikin-ellipsoid transport domain.

Sampled owner declarations:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the quantitative Chapter 5 owner for
  self-concordance on a domain;
* `IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset` from `Theorem_5_1_5`, the
  canonical owner theorem for the Dikin-inclusion clause;
* `IsSelfConcordantOnWith.displacement_localNorm_lower_bound` from `Theorem_5_1_5`, the canonical
  owner theorem for the lower transport inequality `(5.1.9)`;
* `IsSelfConcordantOnWith.displacement_localNorm_upper_bound` from `Theorem_5_1_5`, the canonical
  owner theorem for the upper transport inequality `(5.1.10)`.

Source/core/bridge triage:
* source-facing: the three forward consequences of quantitative self-concordance appearing as the
  clauses of Theorem 5.1.10;
* core/canonical: `IsSelfConcordantOnWith dom Mf f`;
* bridge/view: no new bridge layer is needed, because each clause already has the correct
  owner-level statement upstream.

Primitive data:
* a domain `dom`, a self-concordance constant `Mf`, and an objective `f`;
* the owner hypothesis `IsSelfConcordantOnWith dom Mf f`.

Derived API:
* `W⁰[f; x](1 / (Mf : ℝ)) ⊆ dom`;
* the lower displacement transport inequality `(5.1.9)`;
* the upper displacement transport inequality `(5.1.10)`.

The previous version incorrectly replaced this source item by a stronger qualitative
characterization theorem for `IsSelfConcordantOn dom f`. The textbook content here is already
owned canonically by the three Chapter 5 methods below, so this file refines to direct recall of
those owner declarations instead of keeping a parallel wrapper theorem. -/

/- Theorem 5.1.10 (1) is the canonical Dikin-inclusion theorem
`IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset`. -/
recall IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset

/- Theorem 5.1.10 (2) is the canonical lower transport theorem
`IsSelfConcordantOnWith.displacement_localNorm_lower_bound`. -/
recall IsSelfConcordantOnWith.displacement_localNorm_lower_bound

/- Theorem 5.1.10 (3) is the canonical upper transport theorem
`IsSelfConcordantOnWith.displacement_localNorm_upper_bound`. -/
recall IsSelfConcordantOnWith.displacement_localNorm_upper_bound

end

/-! ### Theorem_5_1_11 (from Chap05) -/
open scoped ConstrainedArgmin ConvexAnalysis Gradient

noncomputable section

universe u₁ u₂

variable {E₁ : Type u₁} {E₂ : Type u₂}

variable [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
variable [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
variable [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

local notation "Z" => WithLp 2 (E₁ × E₂)

/- Theorem 5.1.11 lies in the chapter's partial-minimization / self-concordance calculus.

Sampled owner-style declarations in this domain:
- `IsSelfConcordantOnWith` from `Definition_5_1_1`, the Chapter 5 owner for quantitative
  self-concordance on an ambient Hilbert space;
- `partialInfProjection` from Chapter 3 and `extendedRealRealPart` from `Definition_5_0_18`, the
  canonical owners for the partial-minimization objective;
- `argmin[Q] f` and `mem_constrainedArgmin_iff` from `Chap01/Definition_1_3_3`, the project
  owner for chosen constrained minimizers;
- mathlib `WithLp 2 (E₁ × E₂)` together with the canonical bridge `z ↦ z.ofLp`, the intrinsic
  `L²` product owner determined by `E₁` and `E₂`;
- mathlib/project `hessian`, applied to the frozen `y`-slice `Φ ∘ Prod.mk x`, the canonical
  Chapter 5 owner for the `yy` second-derivative data.

Best owner abstraction:
- source-facing: the self-concordance of `Φ : E₁ × E₂ → ℝ` on `interior Q`;
- core/canonical:
  `IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) Mf
    (Φ ∘ WithLp.ofLp)`,
  `partialInfProjection Q (Real.toEReal ∘ Φ)`, its real surface, and the frozen-slice Hessian
  `hessian (Φ ∘ Prod.mk x) (y x)`;
- bridge/view: the chosen minimizer branch `y`, used to evaluate the slice Hessian at the
  minimizing point.

Primitive data:
- the feasible set `Q : Set (E₁ × E₂)`;
- the objective `Φ : E₁ × E₂ → ℝ`;
- the selected minimizing branch `y : E₁ → E₂`, recorded by membership in the canonical fiberwise
  owner `argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x)`.

Derived API:
- the partial-minimization objective
  `extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))`;
- the frozen-slice Hessian `hessian (Φ ∘ Prod.mk x) (y x)`.

This refinement keeps the main theorem on the intrinsic product-space owner
`IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) Mf
  (Φ ∘ WithLp.ofLp)`; the `WithLp` realization is now the canonical ambient owner rather than
extra raw-product instance data, while the fiberwise data is expressed through the canonical map
`Prod.mk x : E₂ → E₁ × E₂` instead of coordinate-level set comprehensions and lambdas. -/

-- Proof sketch: combine the global lower Taylor inequality for the self-concordant function `Φ`
-- on `interior Q` with the envelope identities at the canonical fiber minimizer
-- `y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x)`. The minimizing property removes the
-- `y`-gradient term, and the positive-definite frozen-slice `yy` Hessian identifies the Hessian
-- of the value
-- function with the Schur complement of the ambient Hessian, yielding the same self-concordance
-- constant for the partial minimization objective.
/-- Theorem 5.1.11: if `Φ` is self-concordant with constant `M_Φ` on `interior Q` for a chosen
intrinsic `L²` product lift of `E₁ × E₂`, and each fiberwise infimum is attained at an interior
point `y(x)` where the frozen `y`-slice Hessian `∇² (Φ ∘ Prod.mk x) (y x)` is positive
definite, then the canonical real surface of the partial infimal projection is self-concordant on
its natural domain with the same constant. -/
theorem partialMinimizationObjective_isSelfConcordantOnWith
    {Q : Set (E₁ × E₂)} {Mf : NNReal} {Φ : E₁ × E₂ → ℝ} {y : E₁ → E₂}
    (hself :
      IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) Mf
        (Φ ∘ WithLp.ofLp))
    (hy_mem_interior :
      ∀ ⦃x : E₁⦄, x ∈ dom (partialInfProjection Q (Real.toEReal ∘ Φ)) → (x, y x) ∈ interior Q)
    (hy_argmin :
      ∀ ⦃x : E₁⦄, x ∈ dom (partialInfProjection Q (Real.toEReal ∘ Φ)) →
        y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hyy_pos :
      ∀ ⦃x : E₁⦄, x ∈ dom (partialInfProjection Q (Real.toEReal ∘ Φ)) → ∀ v : E₂, v ≠ 0 →
        0 < inner ℝ v ((hessian (Φ ∘ Prod.mk x) (y x)) v)) :
    IsSelfConcordantOnWith (dom (partialInfProjection Q (Real.toEReal ∘ Φ))) Mf
      (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))) := sorry

end

/-! ### Theorem_5_1_12 (from Chap05) -/
open InnerProductSpace
open scoped Gradient HessianDualLocalNorm SelfConcordantAuxiliaryFunction

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}
variable [IsSelfConcordantOnWith dom Mf f] [HasPositiveDefiniteHessianOn dom f]

/- Theorem 5.1.12 lies in the Chapter 5 self-concordance / dual-local-norm domain.

Sampled owner declarations:
* `HasPositiveDefiniteHessianOn` from `Definition_5_0_23`, the chapter owner for the
  positive-definite-Hessian regime in which the dual local norm is evaluated from domain
  membership alone;
* `HessianDualLocalNorm.ofPosDefMem` from `Definition_5_0_20`, the canonical domain-level bridge
  to the dual local norm;
* `selfConcordantOmegaArg` and `selfConcordantOmegaStarArg` from `Definition_5_0_21`, the
  canonical Chapter 5 owners of the `ω` and `ω_*` arguments;
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the owner for quantitative
  self-concordance;
* `firstOrderTaylorModelAt` from `Chap01/FirstOrderTaylorModel`, the canonical affine Taylor
  owner against which the remainder is measured.

Source/core/bridge triage:
* source-facing: the lower and upper value bounds expressed by the dual local norm of
  `∇ f y - ∇ f x` at `y`;
* core/canonical: `IsSelfConcordantOnWith dom Mf f`, `HasPositiveDefiniteHessianOn dom f`,
  `HessianDualLocalNorm.ofPosDefMem`, and the Chapter 5 auxiliary-function owners `ω` and `ω_*`;
* bridge/view: the gradient-difference covector
  `(toDual ℝ E) (∇ f y - ∇ f x)` and the affine Taylor remainder
  `f y - firstOrderTaylorModelAt f x y`.

Primitive data:
* `dom`, `Mf`, `f`, the points `x` and `y`;
* domain membership of `x` and `y`;
* positive definiteness of the Hessian on `dom`.

Derived API:
* the gradient-difference covector at `y`;
* the domain-level dual local norm bridge `HessianDualLocalNorm.ofPosDefMem`;
* the lower `ω` and upper `ω_*` remainder terms, expressed through the canonical subtype owners
  `selfConcordantOmegaArg` and `selfConcordantOmegaStarArg`.

This file stays source-facing. The theorem is not a new owner: it is a derived consequence of the
dual-local-norm owner, the canonical first-order Taylor model, and the Chapter 5 auxiliary
function owners. -/

private theorem gradientDifferenceDualLocalNorm_nonneg
    (x y : E) (hy : y ∈ dom) :
    0 ≤
      HessianDualLocalNorm.ofPosDefMem f hy
        ((toDual ℝ E) (∇ f y - ∇ f x)) := by
  simpa [HessianDualLocalNorm.ofPosDefMem] using
    dualLocalNorm_nonneg f y
      (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hy)
      (hessian_isInvertible_of_det_ne_zero
        (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hy))
      ((toDual ℝ E) (∇ f y - ∇ f x))

-- Proof sketch: compare `f y` to the first-order Taylor model at `x`, write the remainder in
-- terms of the gradient-difference covector at `y`, and express the resulting lower and upper
-- self-concordant remainders through the canonical Chapter 5 subtype owners
-- `selfConcordantOmegaArg` and `selfConcordantOmegaStarArg`. The only local helper retained here
-- is the nonnegativity witness needed to build the `ω` argument from the domain-level dual local
-- norm bridge.
/-- Theorem 5.1.12: if `f` is self-concordant on `dom` with constant `M_f`, then the
value at `y` is bounded below by the affine Taylor model at `x` plus the remainder term
`M_f⁻² ω(M_f ‖∇ f(y) - ∇ f(x)‖*_y)`, interpreted as
`(1 / 2) ‖∇ f(y) - ∇ f(x)‖*²_y` when `M_f = 0`. In the same zero-parameter limit, the
upper branch also reduces to the quadratic remainder `(1 / 2) ‖∇ f(y) - ∇ f(x)‖*²_y`;
otherwise, if the dual local norm of the gradient difference at `y` is smaller than `1 / M_f`,
then `f y` is bounded above by the affine model plus
`M_f⁻² ω_*(M_f ‖∇ f(y) - ∇ f(x)‖*_y)`. -/
theorem selfConcordant_value_bounds_of_dualLocalNorm_gradient_sub
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom) :
    let δ :=
      HessianDualLocalNorm.ofPosDefMem f hy
        ((toDual ℝ E) (∇ f y - ∇ f x))
    let taylor := firstOrderTaylorModelAt f x y
    let tω := selfConcordantOmegaArg Mf δ
      (neg_one_lt_mf_mul_of_nonneg (gradientDifferenceDualLocalNorm_nonneg x y hy))
    f y ≥
        taylor +
          (if hMf : Mf = 0 then
            δ ^ (2 : ℕ) / 2
          else
            (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω) ∧
      (if hMf : Mf = 0 then
        f y ≤
          taylor +
            δ ^ (2 : ℕ) / 2
      else
        ∀ hδ : δ < 1 / (Mf : ℝ),
          let τω := selfConcordantOmegaStarArg Mf δ (mf_mul_lt_one_of_lt_inv hδ)
          f y ≤
            taylor +
              (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω) := sorry

/-! ### Theorem_5_1_13 (from Chap05) -/
open InnerProductSpace
open scoped Gradient NewtonDecrement SelfConcordantAuxiliaryFunction

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 5.1.13 lies in the Chapter 5 self-concordant minimization domain.

Sampled owner declarations:
* `HasPositiveDefiniteHessianOn` from `Definition_5_0_23`, the chapter owner for strict Hessian
  positivity on the domain;
* `newtonDecrement` and `NewtonDecrement.ofPosDefMem` from `Definition_5_0_24`, the canonical
  Newton-decrement owner, its domain-membership bridge, and the canonical small-decrement
  `ω_*` argument `NewtonDecrement.omegaStarArgOfPosDefMem`;
* `selfConcordantOmegaStar` and the notation `ω_*` from `Definition_5_0_21`, the standard
  self-concordant remainder term.

Best owner abstraction:
* source-facing: existence and uniqueness of a minimizer together with the `ω_*` suboptimality
  bound under the small-Newton-decrement hypothesis;
* core/canonical: `IsSelfConcordantOnWith dom Mf f`, `HasPositiveDefiniteHessianOn dom f`, and
  `NewtonDecrement.ofPosDefMem`;
* bridge/view: the canonical `ω_*` argument `M_f λ_f(x) ∈ (-∞, 1)`.

This file keeps the textbook theorem as a single source-facing declaration. After correcting
`Theorem_5_0_25` back to the convex recession-direction theorem, this result now depends directly
on the underlying Chapter 5 self-concordant owners instead of a transitive theorem from the wrong
numbered item.
-/

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}
variable [IsSelfConcordantOnWith dom Mf f] [HasPositiveDefiniteHessianOn dom f]

-- Proof sketch: the small-Newton-decrement hypothesis already forces `Mf > 0`, because
-- `NewtonDecrement.ofPosDefMem_nonneg` gives `0 ≤ λ_f(x)` while `Mf = 0` would rewrite
-- `λ_f(x) < 1 / M_f` to the impossible inequality `λ_f(x) < 0`. From that hypothesis we obtain a
-- minimizer and then apply the standard self-concordant upper model `ω_*` at that minimizer.
-- Strict convexity from the positive-definite Hessian gives uniqueness.
/-- Theorem 5.1.13: if `f` is self-concordant on `dom`, its Hessian is positive definite on
`dom`, and some `x ∈ dom` satisfies `λ_f(x) < 1 / M_f`, then `f` admits a unique minimizer on
`dom`, and that minimizer satisfies the standard `ω_*` suboptimality bound measured from `x`.
The small-decrement hypothesis forces `M_f > 0` internally, so no separate positivity binder is
needed on the theorem surface. -/
theorem existsUnique_isMinOn_with_suboptimality_bound_of_newtonDecrement_lt_inv
    {x : E} (hx : x ∈ dom)
    (hlambda : λ[f; x | hx] < 1 / (Mf : ℝ)) :
    let τω := NewtonDecrement.omegaStarArgOfPosDefMem Mf f x hx hlambda
    ∃! xStar : dom,
      IsMinOn f dom (xStar : E) ∧
        f x - f xStar ≤
          (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω := by
  have hMf : 0 < Mf := by
    by_contra hMf
    have hMf0 : Mf = 0 := le_antisymm (not_lt.mp hMf) Mf.2
    have hnonneg : 0 ≤ λ[f; x | hx] :=
      NewtonDecrement.ofPosDefMem_nonneg f x hx
    have hlt0 : λ[f; x | hx] < 0 := by
      simpa [hMf0] using hlambda
    linarith
  sorry

end

end

/-! ### Theorem_5_1_14 (from Chap05) -/
open scoped Gradient HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.1.14 lies in the Chapter 5 self-concordance / recession-direction domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the quantitative Chapter 5 owner for
  self-concordance on a domain;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Definition_5_1_1`, the canonical owner
  for the Hessian local norm;
* `associatedUnivariateFunctionDomain` from `Definition_5_0_12`, the source-facing owner for the
  natural positivity domain of the reciprocal local-norm slice `τ ↦ ‖h‖[f; x + τ • h]⁻¹`;
* `abs_derivWithin_associatedUnivariateFunction_le` from `Lemma_5_1_3`, the source-facing
  derivative bound for that reciprocal local-norm slice on its natural domain;
* `associatedUnivariateFunction_hasDerivWithinAt` from `Lemma_5_1_3`, the auxiliary derivative
  formula behind that bound;
* `associatedUnivariateFunctionDomain_contains_interval` from `Corollary_5_1_4`, the Chapter 5
  interval-control bridge that keeps the ray argument on the canonical slice-domain owner.

Best owner abstraction:
* source-facing: the recession-direction estimate itself, with the textbook backward-frontier and
  nonascent hypotheses left explicit;
* core/canonical: `IsSelfConcordantOnWith dom Mf f` together with `‖h‖[f; x]`;
* bridge/view: the boundary hypothesis on the backward ray and the nonascent pairing
  `inner ℝ (∇ f x) h ≤ 0`.

Primitive data:
* the self-concordant owner `IsSelfConcordantOnWith dom Mf f`;
* the recession direction `h`;
* the chosen base point `x ∈ dom`;
* the backward-frontier hypothesis for the backward ray from `x` along `-h`;
* the nonascent hypothesis for `h` at `x`.

Derived API:
* the local-norm bound `‖h‖[f; x] ≤ M_f ⟪-∇f(x), h⟫`.

The theorem remains source-facing, but its public surface is refined to the Chapter 5 owner API
instead of a long top-level name carrying the owner in its identifier. Its proof route should use
the canonical slice owners `associatedUnivariateFunction` and
`associatedUnivariateFunctionDomain` rather than rebuilding a separate ray package inside this
file. The chapter's lower Taylor remainder bound is already carried by
`Theorem_5_1_8.taylor_lower_bound_of_hessian_loewner_lower`; this file is the distinct
recession-direction item `(5.1.14)`.
-/

namespace IsSelfConcordantOnWith

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}

-- Proof sketch: work on the canonical slice owner `associatedUnivariateFunction dom f x h`.
-- Corollary 5.1.4 keeps a whole interval around `0` inside
-- `associatedUnivariateFunctionDomain dom f x h`, and Lemma 5.1.3 gives the derivative bound for
-- the reciprocal local norm on that domain. The recession and backward-frontier hypotheses show
-- that the maximal backward parameter is finite, so integrating the derivative estimate from that
-- endpoint to `0` yields the lower bound on `‖h‖[f; x]⁻¹`, equivalently the displayed upper bound
-- on `‖h‖[f; x]`.
/-- Theorem 5.1.14: if `f` is self-concordant with positive parameter `M_f` on `dom`, the
direction `h` is a recession direction for `dom`, the backward ray `x - τ h` from a chosen point
`x ∈ dom` meets `frontier dom` at finite distance, and `h` is a nonascent direction for `f` at
`x`, then the local Hessian norm of `h` at `x` is bounded by `M_f` times the pairing of `h` with
the negative gradient. -/
theorem hessianLocalNorm_le_neg_gradient_inner_of_recession_direction
    (hself : IsSelfConcordantOnWith dom Mf f) (hMf : 0 < Mf) {h : E}
    (hrecession : ∀ ⦃x : E⦄, x ∈ dom → ∀ t : ℝ, 0 ≤ t → x + t • h ∈ dom)
    {x : E} (hx : x ∈ dom)
    (hfrontier : ∃ τ : ℝ, 0 < τ ∧ x - τ • h ∈ frontier dom)
    (hnonascent : inner ℝ (∇ f x) h ≤ 0) :
    ‖h‖[f; x] ≤ (Mf : ℝ) * inner ℝ (-∇ f x) h := by
  letI : IsSelfConcordantOnWith dom Mf f := hself
  sorry

end

end IsSelfConcordantOnWith

end

/-! ### Theorem_5_1_15 (from Chap05) -/
open scoped Gradient NewtonDecrement SelfConcordantAuxiliaryFunction
open SelfConcordantNewtonVariant

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 5.1.15 lies in the Chapter 5 self-concordant damped-Newton domain.

Sampled owner declarations:
* `newtonDecrement`, the notation `λ[f; x | hPos; hInv]`, and the bridge
  `NewtonDecrement.ofDetNeZero` in `Definition_5_0_24`, the Chapter 5 owner for the Newton
  decrement;
* `selfConcordantNewtonShift` in `Definition_5_2_1`, whose `.damped` branch is the textbook
  shift formula `ξ = M_f λ`;
* `selfConcordantNewtonNextPoint` in `Definition_5_2_1`, the chapter owner for one-step
  self-concordant Newton updates and their `.damped` specialization;
* `localNorm_taylor_upper_bound_with_selfConcordantOmegaStar` in `Theorem_5_1_9`, the chapter
  owner for the upper Taylor bound with the canonical `ω_*` remainder on an admissible step.

Best owner abstraction:
* source-facing: the one-step value decrease for the damped specialization of
  `selfConcordantNewtonNextPoint`;
* core/canonical: `selfConcordantNewtonNextPoint` together with `newtonDecrement`;
* bridge/view: the admissible damped-step norm
  `λ_f(x) / (1 + M_f λ_f(x))`, the corresponding `ω_*` upper remainder, and the Fenchel bridge
  back to the source-facing `ω(M_f λ_f(x))` term.

Primitive data:
* a self-concordant function `f` on `dom` with parameter `Mf`;
* a point `x ∈ dom`;
* Hessian nondegeneracy at `x`.

Derived API:
* the damped self-concordant Newton next point at `x` as the specialization
  `selfConcordantNewtonNextPoint f Mf .damped x hx hH`;
* the Newton decrement `λ_f(x)` supplied by `NewtonDecrement.ofDetNeZero`;
* the canonical auxiliary-function argument
  `NewtonDecrement.omegaArgOfDetNeZero Mf f hx hH`, whose coercion is `(Mf : ℝ) * λ_f(x)`.

The previous version still depended on a parallel damped-step wrapper. This refinement states the
value decrease directly for the canonical `.damped` specialization of
`selfConcordantNewtonNextPoint`, keeps the decrement side on the Chapter 5 owner surface, and is
organized around the chapter's upper-bound `ω_*` Taylor layer rather than the lower-bound
Hessian-comparison theorem.
-/

-- Proof sketch: write the step `d = x₊ - x` as the damped inverse-Hessian gradient direction, so
-- `‖d‖_x = λ_f(x) / (1 + M_f λ_f(x))`. Theorem 5.1.9 applies directly to this admissible step,
-- giving the upper Taylor remainder `ω_*` at the damped step norm, while the gradient pairing
-- along the Newton direction is
-- `-λ_f(x)^2 / (1 + M_f λ_f(x))`. Rewriting with the Fenchel relation
-- `ω(t) = t ω'(t) - ω_*(ω'(t))` gives the canonical remainder `M_f⁻² ω(M_f λ_f(x))` when
-- `0 < M_f`; at `M_f = 0`, the limiting branch is `(1 / 2) λ_f(x)^2`.
/-- Theorem 5.1.15: the damped Newton step
`x ↦ x - (1 + M_f λ_f(x))⁻¹ (∇² f(x))⁻¹ ∇ f(x)` decreases the objective by at least
`M_f⁻² ω(M_f λ_f(x))`, interpreted as `(1 / 2) λ_f(x)^2` when `M_f = 0`. -/
theorem selfConcordant_dampedNewtonStep_value_decrease
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    [IsSelfConcordantOnWith dom Mf f]
    {x : E} (hx : x ∈ dom)
    (hH : (hessian f x).det ≠ 0) :
    let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
    f (selfConcordantNewtonNextPoint f Mf .damped x hx hH) ≤
      f x -
        (if Mf = 0 then
          δ ^ (2 : ℕ) / 2
        else
          (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω (NewtonDecrement.omegaArgOfDetNeZero Mf f hx hH)) :=
  sorry

end

/-! ### Theorem_5_1_16 (from Chap05) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 5.1.16 lies in the finite-dimensional Chapter 5 self-concordant minimization domain.

Sampled owner-style declarations:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, specialized here to the whole-space owner
  `IsSelfConcordantOnWith Set.univ Mf f`;
* `HasPositiveDefiniteHessianOn` from `Definition_5_0_23`, likewise specialized to
  `Set.univ`;
* `IsMinOn` and `isMinOn_univ_iff` in mathlib, the canonical owner and textbook bridge for
  whole-space minimizers;
* `isMinOn_iff_eq_sInf_range` from `Chap03/Definition_3_33`, the project owner bridge between
  whole-space attainment and the infimum of `Set.range f`.

Source/core/bridge triage:
* source-facing: bounded-below existence and uniqueness of a global minimizer of `f`;
* core/canonical: `IsSelfConcordantOnWith Set.univ Mf f`,
  `HasPositiveDefiniteHessianOn Set.univ f`, and `IsMinOn f Set.univ x`;
* bridge/view: the attained-infimum identity `f xStar = sInf (Set.range f)`.

Primitive data:
* the ambient objective `f : E → ℝ`;
* self-concordance of `f` on `Set.univ`;
* positive definiteness of its Hessian on `Set.univ`;
* lower boundedness of the range `Set.range f`.

Derived API:
* existence of a global minimizer of `f`;
* uniqueness of that minimizer.

The previous revision incorrectly strengthened the textbook finite-dimensional whole-space
attainment theorem to an arbitrary complete real inner-product space, where bounded below need not
imply attainment. The public owner is restored here to the source-faithful whole-space
finite-dimensional formulation. -/

namespace IsSelfConcordantOnWith

section

variable {Mf : NNReal} {f : E → ℝ}
variable [IsSelfConcordantOnWith Set.univ Mf f] [HasPositiveDefiniteHessianOn Set.univ f]

-- Proof sketch: boundedness below is expressed by `BddBelow (Set.range f)`, the canonical
-- whole-space image owner. Positive-definite Hessian on `Set.univ` supplies the strict convexity
-- needed for uniqueness once existence is obtained.
/-- Theorem 5.1.16: on a finite-dimensional real inner-product space, if a self-concordant
objective on the whole space has positive-definite Hessian everywhere and is bounded below, then
it attains a unique global minimum. -/
theorem existsUnique_isMinOn_of_bddBelow
    (hbelow : BddBelow (Set.range f)) :
    ∃! xStar : E, IsMinOn f Set.univ xStar := by
  sorry

end

end IsSelfConcordantOnWith

end

/-! ### Theorem_5_1_17 (from Chap05) -/
open scoped ConvexAnalysis Gradient WithTopConvexAnalysis

noncomputable section

universe u

variable {E : Type u}

/- Theorem 5.1.17 lies in the chapter's Fenchel-duality / self-concordance domain.

Sampled owner-style declarations before refinement:
- `fenchelDual` / notation `f⋆` and the dual effective domain `dom (f⋆)` in
  `Chap05/Definition_5_0_27`, the chapter owner surface for Fenchel conjugacy;
- `fenchelPrimalExtension` in `Chap05/FenchelPrimalExtension`, the chapter owner for extending a
  real-valued primal function by `+∞` off a feasible set;
- `constrainedEpigraph` in `Chap03/Definition_3_3`, the chapter owner for the closed primal
  epigraph over a feasible set;
- `dom_fenchelDual_subset_image_gradient_of_selfConcordant` and
  `image_gradient_subset_dom_fenchelDual_of_selfConcordant` in `Chap05/Lemma_5_1_6`, the
  chapter's dual-domain / gradient-image bridge under the standing self-concordant hypotheses;
- `fenchelConjugate_hasGradientAt` and `fenchelConjugate_hessian_eq_inverse` in
  `Chap05/Proposition_5_0_29`, the chapter owner theorems for the gradient / inverse-Hessian
  transfer on the Fenchel dual;
- `IsSelfConcordantOnWith` in `Chap05/Definition_5_1_1`, the chapter owner for self-concordance.

Best owner abstraction:
- source-facing: the `+∞`-extension of a real-valued primal function `f` off a feasible set `Q`,
  together with the dual self-concordance transfer;
- core/canonical: `F⋆`, `dom (F⋆)`, and `extendedRealRealPart (F⋆)` for
  `F = fenchelPrimalExtension Q f`;
- bridge/view: the effective-domain identification `dom F = Q` and the chapter's Legendre /
  maximizer / inverse-Hessian bridges.

Primitive data:
- a feasible set `Q : Set E`;
- a real-valued primal function `f : E → ℝ`.

Derived API in this file:
- the self-concordance theorem on the canonical dual owner surface
  `extendedRealRealPart ((fenchelPrimalExtension Q f)⋆)`.

This file therefore reuses the extracted chapter owner `fenchelPrimalExtension` instead of
redeclaring it locally. The source-facing theorem is the dual self-concordance transfer for the
canonical Fenchel dual `extendedRealRealPart (F⋆)` under the standing primal hypotheses. A chosen
maximizer branch `xStar` and its calculus data are only bridge-level auxiliary input for the proof
route through `Proposition_5_0_29` and `5_0_30`; they do not belong on the main theorem boundary.
The closedness input is kept at the primitive owner level
`constrainedEpigraph Q (fun y ↦ (f y : WithTop ℝ))`, instead of the stronger packaged hypothesis
`ClosedConvexFunction (fenchelPrimalExtension Q f)`, because convexity is already supplied by
`IsSelfConcordantOnWith Q Mf f`. -/

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {Q : Set E} {Mf : NNReal} {f : E → ℝ}

local notation "F" => fenchelPrimalExtension Q f

/-- Theorem 5.1.17: let `F` be the `+∞`-extension of a real-valued function `f` off `Q`. If `f`
is self-concordant on `Q` with constant `M_f`, the constrained epigraph of `f` over `Q` is closed,
and `Q` contains no affine line, then the finite real part of the Fenchel dual `F⋆` is
self-concordant on its finite-value domain with the same constant `M_f`. This is the source-facing
owner statement: the theorem surface keeps only the standing primal hypotheses, while any chosen
maximizer branch or inverse-Hessian calculus used in a proof is auxiliary bridge data. -/
theorem fenchelPrimalExtension_dualRealPart_isSelfConcordantOnWith
    (hself : IsSelfConcordantOnWith Q Mf f)
    (hclosed :
      IsClosed (constrainedEpigraph Q (fun y ↦ (f y : WithTop ℝ))))
    (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) :
    IsSelfConcordantOnWith
      (dom (F⋆))
      Mf
      (extendedRealRealPart (F⋆)) := by
  let _ := hself
  sorry

end

end
