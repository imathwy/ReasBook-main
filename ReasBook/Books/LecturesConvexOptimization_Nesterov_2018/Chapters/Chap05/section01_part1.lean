import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_5_1_1 (from Chap05) -/
open scoped Gradient HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}

/-
Corollary 5.1.1 lies in the Chapter 5 self-concordance differential-inequality domain.

Sampled owner-style declarations in this domain:
* `hessian` from `Chap01/Definition_1_4_16`, the chapter owner for the Hessian operator;
* `thirdDirectionalDerivative` from `Chap05/Definition_5_0_10`, the source-facing owner for the
  diagonal third derivative;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Chap05/Definition_5_1_1`;
* `IsSelfConcordantOnWith.third_deriv_bound` from `Chap05/Definition_5_1_1`, the chapter owner
  field whose surface this corollary compares with the Hessian-operator inequality.

Source/core/bridge triage:
* source-facing: the textbook equivalence between the cubic self-concordance bound and the Loewner
  operator inequality;
* core/canonical: `hessian`, `thirdDirectionalDerivative`, and `hessianLocalNorm`;
* bridge/view: this corollary translating between those two source-facing formulations.

Primitive data:
* the objective `f`;
* the domain `dom`;
* the self-concordance constant `Mf`.

Derived API:
* the owner hypothesis `IsSelfConcordantOnWith dom Mf f`;
* the operator inequality `fderiv ℝ (hessian f) x u ≤ (2 M_f ‖u‖[f; x]) • hessian f x`.

This file therefore stays at the source-facing corollary layer, but it reuses the chapter owners
instead of restating the same mathematics through raw `iteratedFDeriv`, `Real.sqrt`, and
`fderiv ℝ (∇ f)` formulas. -/

-- Proof sketch: under the standing open-domain, `C³`, and convexity assumptions, the owner
-- `IsSelfConcordantOnWith dom Mf f` is equivalent to its defining cubic bound. Polarize that
-- bound to obtain the quadratic-form estimate for the bilinear form `D³f(x)[u]`, then translate
-- it into Loewner order for the corresponding Hessian-direction operator. Conversely, evaluate
-- the operator inequality on the quadratic form at `u` and `-u` to recover the absolute cubic
-- bound, then rebuild the owner with the standing structural hypotheses.
namespace IsSelfConcordantOnWith

/-- Corollary 5.1.1, forward direction: the Chapter 5 owner `IsSelfConcordantOnWith dom Mf f`
implies the Hessian-direction operator inequality
`D³f(x)[u] ≤ 2 M_f ‖u‖_{∇² f(x)} ∇² f(x)` on `dom`. -/
theorem thirdDerivative_operator_le
    (hself : IsSelfConcordantOnWith dom Mf f) {x : E} (hx : x ∈ dom) (u : E) :
    fderiv ℝ (hessian f) x u ≤
      (2 * (Mf : ℝ) * ‖u‖[f; x]) • hessian f x := by
  sorry

/-- Corollary 5.1.1, converse direction: under the standing open-domain, `C³`, and convexity
assumptions, the Hessian-direction operator inequality reconstructs
`IsSelfConcordantOnWith dom Mf f`. -/
theorem of_thirdDerivative_operator_le
    (h_open : IsOpen dom) (h_contDiff : ContDiffOn ℝ 3 f dom) (h_convexOn : ConvexOn ℝ dom f)
    (hoperator : ∀ ⦃x : E⦄ (_hx : x ∈ dom) (u : E),
      fderiv ℝ (hessian f) x u ≤
        (2 * (Mf : ℝ) * ‖u‖[f; x]) • hessian f x) :
    IsSelfConcordantOnWith dom Mf f := by
  sorry

end IsSelfConcordantOnWith

/-- Corollary 5.1.1: for a thrice continuously differentiable convex function on an open convex
domain, the quantitative self-concordance owner `IsSelfConcordantOnWith dom Mf f` is equivalent
to the Loewner-order bound `D³f(x)[u] ≤ 2 M_f ‖u‖_{∇² f(x)} ∇² f(x)` on the directional
derivative of the Hessian. -/
theorem selfConcordant_iff_thirdDerivative_operator_le
    (h_open : IsOpen dom) (h_contDiff : ContDiffOn ℝ 3 f dom) (h_convexOn : ConvexOn ℝ dom f) :
    IsSelfConcordantOnWith dom Mf f ↔
      ∀ ⦃x : E⦄ (_hx : x ∈ dom) (u : E),
        fderiv ℝ (hessian f) x u ≤
          (2 * (Mf : ℝ) * ‖u‖[f; x]) • hessian f x := by
  constructor
  · intro hself x hx u
    exact hself.thirdDerivative_operator_le hx u
  · intro hoperator
    exact
      IsSelfConcordantOnWith.of_thirdDerivative_operator_le
        h_open h_contDiff h_convexOn hoperator

end

/-! ### Definition_5_1_1 (from Chap05) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 5.1.1 lies in the chapter's self-concordance / Hessian-local-norm domain.

Sampled owner declarations:
* `hessian` from `Chap01/Definition_1_4_16`, the intrinsic second-order owner used throughout the
  chapter;
* `thirdDirectionalDerivative` from `Definition_5_0_10`, the canonical cubic-derivative owner;
* `ConvexOn` from mathlib, the canonical owner for convexity on a fixed domain;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the downstream barrier owner that
  extends the standard-self-concordant case defined here.

Source/core/bridge triage:
* source-facing: `IsSelfConcordantOnWith dom Mf f`, the textbook bundled notion carrying the
  constant `M_f`;
* core/canonical: the Hessian owner `hessian f x`, the local norm owner `‖u‖[f; x]`, and the
  convexity owner `ConvexOn ℝ dom f`;
* bridge/view: the derived qualitative abbreviation `IsSelfConcordantOn dom f` and the standard
  specialization `IsStandardSelfConcordantOn dom f`.

Primitive data:
* the domain `dom`;
* the self-concordance constant `Mf`;
* the function `f`;
* openness of `dom`, `C³` regularity of `f` on `dom`, convexity on `dom`, and the cubic
  third-derivative bound.

Derived API:
* the local norm notation `‖u‖[f; x]`;
* domain convexity and Hessian positivity/semidefiniteness on `dom`;
* the qualitative and standard-self-concordant specializations.

This file keeps the quantitative owner as the public core. The qualitative and standard forms stay
as thin source-facing views, while Hessian positivity is exposed through inferable theorem-level
API rather than through an extra `Fact` wrapper around the defining class field. -/

/-- The Hessian local norm attached to `f` at `x`, evaluated on the direction `u`. -/
def hessianLocalNorm (f : E → ℝ) (x u : E) : ℝ :=
  Real.sqrt (inner ℝ u (hessian f x u))

namespace HessianLocalNorm

/-- Source-facing notation for the Hessian local norm of `u` at `x` for `f`. -/
scoped notation:max "‖" u "‖[" f "; " x "]" => hessianLocalNorm f x u

end HessianLocalNorm

open scoped HessianLocalNorm

-- Proof sketch: unfold `hessianLocalNorm`.
/-- Expanding `hessianLocalNorm f x u` gives the square root of the Hessian quadratic form. -/
theorem hessianLocalNorm_def (f : E → ℝ) (x u : E) :
    ‖u‖[f; x] = Real.sqrt (inner ℝ u (hessian f x u)) :=
  rfl

/-- The Hessian local norm is always nonnegative. -/
theorem hessianLocalNorm_nonneg (f : E → ℝ) (x u : E) :
    0 ≤ ‖u‖[f; x] := by
  rw [hessianLocalNorm_def]
  exact Real.sqrt_nonneg _

/-- The Hessian local norm is even in the direction argument. -/
@[simp] theorem hessianLocalNorm_neg (f : E → ℝ) (x u : E) :
    ‖-u‖[f; x] = ‖u‖[f; x] := by
  rw [hessianLocalNorm_def, hessianLocalNorm_def]
  congr 1
  simp

/-- Definition 5.1.1: `f` is self-concordant with constant `M_f` on the open convex domain `dom`
when `f` is a convex `C³` function on `dom` and the third directional derivative is bounded by
`2 M_f` times the cube of the local Hessian norm; the case `M_f = 1` is the standard
self-concordant condition. -/
class IsSelfConcordantOnWith (dom : Set E) (Mf : NNReal) (f : E → ℝ) : Prop where
  /-- The domain of definition is open. -/
  isOpen_domain : IsOpen dom
  /-- The objective is three-times continuously differentiable on `dom`. -/
  contDiffOn : ContDiffOn ℝ 3 f dom
  /-- The objective is convex on the domain. -/
  convexOn : ConvexOn ℝ dom f
  /-- The third directional derivative is controlled by the cube of the local Hessian norm. -/
  third_deriv_bound {x : E} (hx : x ∈ dom) (u : E) :
      |thirdDirectionalDerivative f x u| ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ)

namespace IsSelfConcordantOnWith

variable {dom : Set E} {f : E → ℝ}

/-- Increasing the self-concordance constant preserves self-concordance on the same domain. -/
theorem of_le
    {Mf Mg : NNReal} (h : IsSelfConcordantOnWith dom Mf f) (hMfMg : Mf ≤ Mg) :
    IsSelfConcordantOnWith dom Mg f where
  isOpen_domain := h.isOpen_domain
  contDiffOn := h.contDiffOn
  convexOn := h.convexOn
  third_deriv_bound {x} hx u := by
    calc
      |thirdDirectionalDerivative f x u| ≤
          2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) :=
        h.third_deriv_bound hx u
      _ ≤ 2 * (Mg : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := by
        have hMfMg' : (Mf : ℝ) ≤ (Mg : ℝ) := by
          exact_mod_cast hMfMg
        have hnorm : 0 ≤ ‖u‖[f; x] := hessianLocalNorm_nonneg f x u
        have hpow : 0 ≤ ‖u‖[f; x] ^ (3 : ℕ) := by
          exact pow_nonneg hnorm _
        nlinarith

/-- A self-concordant function has convex domain. -/
theorem convex_domain
    {Mf : NNReal} (h : IsSelfConcordantOnWith dom Mf f) :
    Convex ℝ dom :=
  h.convexOn.1

/-- The Hessian of a self-concordant function is positive on its domain. -/
theorem hessian_isPositive
    {Mf : NNReal} (h : IsSelfConcordantOnWith dom Mf f) {x : E} (hx : x ∈ dom) :
    (hessian f x).IsPositive := by
  have hC2 : ContDiffOn ℝ 2 f dom := h.contDiffOn.of_le (by norm_num)
  exact ((convexOn_iff_hessian_isPositive h.isOpen_domain h.convex_domain hC2).1 h.convexOn) x hx

/-- A self-concordant-on-with instance canonically supplies Hessian positivity at each point of
its domain. -/
theorem hessian_isPositive_of_mem
    (Mf : NNReal) [h : IsSelfConcordantOnWith dom Mf f] {x : E} (hx : x ∈ dom) :
    (hessian f x).IsPositive :=
  h.hessian_isPositive hx

/-- A self-concordant-on-with instance canonically supplies the defining cubic derivative bound on
its domain. -/
theorem third_deriv_bound_of_mem
    (Mf : NNReal) [h : IsSelfConcordantOnWith dom Mf f] {x : E} (hx : x ∈ dom) (u : E) :
    |thirdDirectionalDerivative f x u| ≤
      2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) :=
  h.third_deriv_bound hx u

/-- The Hessian quadratic form of a self-concordant function is nonnegative on its domain. -/
theorem hessian_posSemidef
    {Mf : NNReal} (h : IsSelfConcordantOnWith dom Mf f) {x : E} (hx : x ∈ dom) (u : E) :
    0 ≤ inner ℝ u (hessian f x u) := by
  have hC2 : ContDiffOn ℝ 2 f dom := h.contDiffOn.of_le (by norm_num)
  simpa [real_inner_comm] using
    ((convexOn_iff_hessian_quadratic_form_nonneg h.isOpen_domain h.convex_domain hC2).1
      h.convexOn) x hx u

end IsSelfConcordantOnWith

/-- `f` is self-concordant on `dom` when it is self-concordant with some nonnegative constant. -/
abbrev IsSelfConcordantOn (dom : Set E) (f : E → ℝ) : Prop :=
  ∃ Mf : NNReal, IsSelfConcordantOnWith dom Mf f

/-- `f` is standard self-concordant on `dom` when the self-concordance constant is `1`. -/
abbrev IsStandardSelfConcordantOn (dom : Set E) (f : E → ℝ) : Prop :=
  IsSelfConcordantOnWith dom 1 f

end

/-! ### Example_5_1_1 (from Chap05) -/
universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (α : ℝ) (a : E)

/- Example 5.1.1 lies in the Chapter 5 self-concordance domain.

Sampled owner-style declarations:
* `IsSelfConcordantOnWith`
* `quadraticAffineObjective`
* `quadraticAffineObjective_zero_operator`
* `quadraticAffineObjective_isSelfConcordantOnWith_zero`

Best owner abstraction:
* source-facing: the affine objective `x ↦ α + ⟪a, x⟫`
* core/canonical: `quadraticAffineObjective α a A`
* bridge/view: the specialization `A = 0`

Primitive data:
* the offset `α`
* the linear term `a`

Derived API:
* the affine self-concordance statement, obtained by specializing the chapter owner theorem to the
  zero quadratic part

This item adds no new mathematics beyond the chapter owner theorem
`quadraticAffineObjective_isSelfConcordantOnWith_zero`, so the file keeps only the specialization
check and does not introduce a parallel wrapper theorem. -/

/- Example 5.1.1 is the zero-quadratic specialization of
`quadraticAffineObjective_isSelfConcordantOnWith_zero`. -/
#check
  (show IsSelfConcordantOnWith (Set.univ : Set E) 0 (fun x ↦ α + inner ℝ a x) from by
    simpa using
      quadraticAffineObjective_isSelfConcordantOnWith_zero
        α a (0 : E →L[ℝ] E) ContinuousLinearMap.isPositive_zero)

/-! ### Lemma_5_1_1 (from Chap05) -/
open scoped Gradient HessianLocalNorm

noncomputable section

universe u v

/- Lemma 5.1.1 is the affine-precomposition bridge for the Chapter 5 self-concordance data.

Primary domain:
- affine pullbacks in the Chapter 5 self-concordance / differential-calculus layer

Sampled owner-style declarations in this domain:
- `hessian`
- `hessianLocalNorm`
- `secondDirectionalDerivative_eq_hessian_quadratic_form`
- `thirdDirectionalDerivative`
- `ContinuousAffineMap`
- `IsSelfConcordantOnWith`

Source/core/bridge triage:
- source-facing: the Chapter 5.1 affine change-of-variables formulas
- core/canonical: the continuous affine pullback `g : E →ᴬ[ℝ] E₁` together with `hessian`,
  `thirdDirectionalDerivative`, and the Chapter 5 local-norm owner from `Definition_5_1_1`
- bridge/view: the textbook presentation `x ↦ A x + b`, recovered from
  `A.toContinuousAffineMap + ContinuousAffineMap.const ℝ E b`

Primitive data:
- the objective `f`
- the continuous affine map `g`
- the Hessian operator and third Fréchet derivative

Derived API:
- the linear part `g.contLinear`
- `‖u‖[f; x]`
- the self-concordance transfer theorem proved downstream in `Theorem_5_1_2`

This file therefore records only the affine-precomposition identities for the Chapter 5 owner
data, reusing the existing upstream owners instead of introducing another parallel wrapper API.
The previous `(A, b)` surface was too low-level for the Fréchet-calculus owners `hessian` and
`hessianLocalNorm`, because those identities are naturally statements about continuous affine
pullbacks. The textbook `A x + b` presentation is a thin view of this owner abstraction rather
than the primitive public data. -/

private theorem directionalSlice_comp_affine
    {E : Type u} {E₁ : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    (f : E₁ → ℝ) (g : E →ᴬ[ℝ] E₁) (x u : E) :
    directionalSlice (f ∘ g) x u = directionalSlice f (g x) (g.contLinear u) := by
  funext t
  simpa [directionalSlice, vadd_eq_add, add_comm, add_left_comm, add_assoc] using
    congrArg f (g.map_vadd x (t • u))

section Hilbert

variable {E : Type u} {E₁ : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]

private theorem differentiableAt_gradient_of_contDiffAt_two
    {f : E₁ → ℝ} {x : E₁} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (∇ f) x := by
  let D : StrongDual ℝ E₁ →L[ℝ] E₁ :=
    (InnerProductSpace.toDual ℝ E₁).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    exact
      (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ f y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Lemma 5.1.1, owner form: the Hessian quadratic form of a continuous affine pullback `f ∘ g` at
`x` in the direction `u` is the Hessian quadratic form of `f` at `g x` in the image direction
`g.contLinear u`, provided `f` is `C²` at `g x`. -/
theorem hessianQuadraticForm_comp_affine
    (f : E₁ → ℝ) (g : E →ᴬ[ℝ] E₁) (x u : E) (hf : ContDiffAt ℝ 2 f (g x)) :
    inner ℝ u (hessian (f ∘ g) x u) =
      inner ℝ (g.contLinear u) (hessian f (g x) (g.contLinear u)) := by
  have hcomp : ContDiffAt ℝ 2 (f ∘ g) x := hf.comp x g.contDiff.contDiffAt
  have hdiff_comp : DifferentiableAt ℝ (f ∘ g) x := hcomp.differentiableAt (by norm_num)
  have hgrad_comp : DifferentiableAt ℝ (∇ (f ∘ g)) x :=
    differentiableAt_gradient_of_contDiffAt_two hcomp
  have hdiff_f : DifferentiableAt ℝ f (g x) := hf.differentiableAt (by norm_num)
  have hgrad_f : DifferentiableAt ℝ (∇ f) (g x) :=
    differentiableAt_gradient_of_contDiffAt_two hf
  calc
    inner ℝ u (hessian (f ∘ g) x u) = secondDirectionalDerivative (f ∘ g) x u := by
      symm
      exact secondDirectionalDerivative_eq_hessian_quadratic_form hdiff_comp hgrad_comp
    _ = secondDirectionalDerivative f (g x) (g.contLinear u) := by
      simp [secondDirectionalDerivative, directionalSlice_comp_affine]
    _ = inner ℝ (g.contLinear u) (hessian f (g x) (g.contLinear u)) := by
      exact secondDirectionalDerivative_eq_hessian_quadratic_form hdiff_f hgrad_f

/-- Lemma 5.1.1, local-norm form: the Hessian local norm of a continuous affine pullback `f ∘ g`
at `x` in the direction `u` is the Hessian local norm of `f` at `g x` in the image direction
`g.contLinear u`, provided `f` is `C²` at `g x`. -/
theorem hessianLocalNorm_comp_affine
    (f : E₁ → ℝ) (g : E →ᴬ[ℝ] E₁) (x u : E) (hf : ContDiffAt ℝ 2 f (g x)) :
    ‖u‖[f ∘ g; x] = ‖g.contLinear u‖[f; g x] := by
  rw [hessianLocalNorm_def, hessianLocalNorm_def, hessianQuadraticForm_comp_affine f g x u hf]

end Hilbert

section Normed

variable {E : Type u} {E₁ : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]

/-- Lemma 5.1.1, third-derivative form: the third directional derivative of a continuous affine
pullback `f ∘ g` at `x` along `u` is the third directional derivative of `f` at `g x` along
`g.contLinear u`. -/
theorem thirdDirectionalDerivative_comp_affine
    (f : E₁ → ℝ) (g : E →ᴬ[ℝ] E₁) (x u : E) :
    thirdDirectionalDerivative (f ∘ g) x u =
      thirdDirectionalDerivative f (g x) (g.contLinear u) := by
  simp [thirdDirectionalDerivative, directionalSlice_comp_affine]

end Normed

end

/-! ### Theorem_5_1_1 (from Chap05) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.1.1 lies in the Chapter 5 self-concordance calculus domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the chapter owner for self-concordance on an
  open convex domain;
* mathlib `ContDiffOn.add` and `ConvexOn.add`, the canonical additive calculus owners reused by
  self-concordance proofs;
* `quadraticAffineObjective_isSelfConcordantOnWith_zero` from `Example_5_1_2`, the canonical
  zero-self-concordance perturbation owner used downstream in Corollary 5.1.2;
* `IsSelfConcordantOnWith.comp_continuousAffineMap` from `Theorem_5_1_2`, the nearby owner-level
  closure theorem showing the same namespace pattern for derived self-concordance calculus.

Source/core/bridge triage:
* source-facing: the weighted-sum closure theorem for self-concordant functions;
* core/canonical: the owner predicate `IsSelfConcordantOnWith`;
* bridge/view: the unweighted additive specialization `add`.

Primitive data:
* two owner witnesses `h₁ : IsSelfConcordantOnWith dom₁ M₁ f₁` and
  `h₂ : IsSelfConcordantOnWith dom₂ M₂ f₂`;
* positive weights `α` and `β`, carried canonically by `NNRealˣ`.

Derived API:
* the weighted-sum closure theorem itself;
* the additive specialization obtained by setting `α = β = 1`.

The refined file keeps the source-facing weighted theorem as the primary declaration and treats the
plain sum as its thin specialization, rather than as a second independent calculus theorem. -/

namespace IsSelfConcordantOnWith

-- Proof sketch: first rescale each summand by Corollary 5.1.3, which replaces `M₁` and `M₂` by
-- `M₁ / √α` and `M₂ / √β`. Then apply `add` to the rescaled summands on
-- `dom₁ ∩ dom₂`.
/-- Theorem 5.1.1: if `f₁` and `f₂` are self-concordant on `dom₁` and `dom₂` with constants
`M₁` and `M₂`, then for positive weights `α` and `β` the weighted sum
`(α : ℝ) • f₁ + (β : ℝ) • f₂` is self-concordant on the intersection domain `dom₁ ∩ dom₂` with
self-concordance constant `max (M₁ / √α) (M₂ / √β)`. -/
theorem weightedSum
    {dom₁ dom₂ : Set E} {M₁ M₂ : NNReal} {α β : NNRealˣ} {f₁ f₂ : E → ℝ}
    (h₁ : IsSelfConcordantOnWith dom₁ M₁ f₁)
    (h₂ : IsSelfConcordantOnWith dom₂ M₂ f₂) :
    IsSelfConcordantOnWith (dom₁ ∩ dom₂)
      (max (M₁ / NNReal.sqrt α) (M₂ / NNReal.sqrt β))
      ((α : ℝ) • f₁ + (β : ℝ) • f₂) := by
  sorry

-- Proof sketch: specialize `weightedSum` to `α = β = 1`, then simplify the weights, the square
-- roots, and the resulting self-concordance constants.
/-- The owner-level additive specialization of Theorem 5.1.1: if `f₁` and `f₂` are
self-concordant on `dom₁` and `dom₂` with constants `M₁` and `M₂`, then their pointwise sum is
self-concordant on the intersection domain `dom₁ ∩ dom₂` with constant `max M₁ M₂`. -/
theorem add
    {dom₁ dom₂ : Set E} {M₁ M₂ : NNReal} {f₁ f₂ : E → ℝ}
    (h₁ : IsSelfConcordantOnWith dom₁ M₁ f₁)
    (h₂ : IsSelfConcordantOnWith dom₂ M₂ f₂) :
    IsSelfConcordantOnWith (dom₁ ∩ dom₂) (max M₁ M₂) (f₁ + f₂) := by
  have hsum :
      IsSelfConcordantOnWith (dom₁ ∩ dom₂)
        (max (M₁ / NNReal.sqrt (1 : NNRealˣ)) (M₂ / NNReal.sqrt (1 : NNRealˣ)))
        (((1 : NNRealˣ) : ℝ) • f₁ + ((1 : NNRealˣ) : ℝ) • f₂) :=
    h₁.weightedSum h₂
  simpa using hsum

end IsSelfConcordantOnWith

end

/-! ### Corollary_5_1_2 (from Chap05) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace IsSelfConcordantOnWith

/- Corollary 5.1.2 lies in the Chapter 5 self-concordance / affine-quadratic perturbation domain.

Sampled owner declarations in this domain:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the chapter owner predicate;
* `IsSelfConcordantOnWith.add` from `Theorem_5_1_1`, the owner-level additive calculus theorem;
* `quadraticAffineObjective` from `Example_5_1_2`, the source-facing affine-quadratic owner;
* `quadraticAffineObjective_isSelfConcordantOnWith_zero` from `Example_5_1_2`, the canonical
  zero-self-concordance witness for that owner.

Best owner abstraction:
* `IsSelfConcordantOnWith` together with its additive calculus API.

Primitive data:
* the owner witness `hf : IsSelfConcordantOnWith dom Mf f`;
* the affine-quadratic perturbation data `α`, `a`, and `A`;
* the positivity witness `hA : A.IsPositive`.

Derived API:
* the self-concordance of `quadraticAffineObjective α a A` on `Set.univ` with constant `0`;
* the perturbation corollary below, obtained by the owner theorem `IsSelfConcordantOnWith.add`.

Source/core/bridge triage:
* source-facing: the textbook quadratic-affine perturbation corollary;
* core/canonical: `IsSelfConcordantOnWith.add`;
* bridge/view: the specialization supplied by
  `quadraticAffineObjective_isSelfConcordantOnWith_zero`.

The refined file therefore keeps the corollary as a thin source-facing bridge, rather than
introducing a parallel owner or restating the additive calculus in a second wrapper API. -/

-- Proof sketch: `quadraticAffineObjective α a A` is self-concordant on `Set.univ` with constant
-- `0` by Example 5.1.2. Apply the owner method `IsSelfConcordantOnWith.add` to this
-- quadratic-affine term and `f`; the intersection domain simplifies to `dom`, and the resulting
-- constant simplifies from `max 0 Mf` to `Mf`.
/-- Corollary 5.1.2: if `f` is self-concordant on an open convex domain `dom ⊆ E` with
self-concordance constant `M_f`, then the quadratic-affine perturbation
`φ(x) = α + ⟪a, x⟫ + (1 / 2) ⟪Ax, x⟫ + f(x)` is self-concordant on `dom` with the same
self-concordance constant `M_f` whenever `A` is positive semidefinite. This reuses the canonical
Chapter 5 owner `quadraticAffineObjective α a A`. -/
theorem add_quadraticAffineObjective
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hf : IsSelfConcordantOnWith dom Mf f)
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (hA : A.IsPositive) :
    IsSelfConcordantOnWith dom Mf (quadraticAffineObjective α a A + f) := by
  simpa using (quadraticAffineObjective_isSelfConcordantOnWith_zero α a A hA).add hf

end IsSelfConcordantOnWith

end

/-! ### Example_5_1_2 (from Chap05) -/
open scoped Gradient

noncomputable section

universe u

/- Example 5.1.2 lies in the Chapter 5 self-concordance / quadratic-objective domain.

Sampled owner-style declarations in this domain:
* `hessian` from `Chap01/Definition_1_4_16`, the canonical second-order owner;
* `thirdDirectionalDerivative` from `Chap05/Definition_5_0_10`, the Chapter 5 source-facing
  owner for diagonal third derivatives;
* `IsSelfConcordantOnWith` from `Chap05/Definition_5_1_1`, the chapter owner predicate;
* `quadraticObjective` from `Chap01/Definition_1_9_1`, the Euclidean matrix-model quadratic owner;
* `nesterovQuadraticObjective` from `Chap02/Proposition_2_6`, the specialized operator quadratic
  owner without an affine term.

Source/core/bridge triage:
* source-facing: the affine-quadratic objective `x ↦ α + ⟪a, x⟫ + (1 / 2) ⟪A x, x⟫`;
* core/canonical: `hessian`, `thirdDirectionalDerivative`, and `IsSelfConcordantOnWith`;
* bridge/view: the Euclidean matrix model `quadraticObjective` and the Chapter 2 specialization
  `nesterovQuadraticObjective`.

Primitive data:
* the scalar offset `α`;
* the linear coefficient `a`;
* the bounded operator `A : E →L[ℝ] E`.

Derived API:
* the gradient identity `∇f(x) = a + A x`;
* the constant-Hessian identity `hessian f x = A`;
* the vanishing third directional derivative;
* the self-concordance conclusion with constant `0`.

No upstream owner packages this exact affine operator-valued quadratic objective at the intrinsic
Hilbert-space level, so this file remains the source-facing owner. The supporting API is refined to
the canonical Chapter 1/5 differential owners rather than the raw `fderiv ℝ (∇ ·)` surface. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic-affine objective `x ↦ α + ⟪a, x⟫ + (1 / 2) ⟪A x, x⟫` on `E`. -/
def quadraticAffineObjective (α : ℝ) (a : E) (A : E →L[ℝ] E) : E → ℝ :=
  fun x ↦ α + inner ℝ a x + (1 / 2 : ℝ) * inner ℝ (A x) x

/-- Evaluating the quadratic-affine objective gives its defining formula. -/
@[simp]
theorem quadraticAffineObjective_apply (α : ℝ) (a : E) (A : E →L[ℝ] E) (x : E) :
    quadraticAffineObjective α a A x =
      α + inner ℝ a x + (1 / 2 : ℝ) * inner ℝ (A x) x :=
  rfl

/-- The zero-quadratic specialization of `quadraticAffineObjective` is the affine objective
`x ↦ α + ⟪a, x⟫`. -/
@[simp]
theorem quadraticAffineObjective_zero_operator (α : ℝ) (a : E) :
    quadraticAffineObjective α a (0 : E →L[ℝ] E) = fun x ↦ α + inner ℝ a x := by
  funext x
  simp [quadraticAffineObjective]

/-- The third directional derivative of a quadratic-affine objective vanishes identically. -/
-- Proof sketch: the Hessian is constant, so differentiating it once more gives zero.
theorem quadraticAffineObjective_thirdDirectionalDerivative_eq_zero
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (x u : E) :
    thirdDirectionalDerivative (quadraticAffineObjective α a A) x u = 0 := sorry

variable [CompleteSpace E]

/-- The gradient of the quadratic-affine objective is `x ↦ a + A x` when `A` is self-adjoint. -/
-- Proof sketch: differentiate the affine term and the quadratic form; self-adjointness identifies
-- the symmetrized Hessian contribution with `A`.
theorem quadraticAffineObjective_gradient_eq
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) :
    ∇ (quadraticAffineObjective α a A) = fun x ↦ a + A x := sorry

/-- The Hessian of the quadratic-affine objective is the constant operator `A` when `A` is
self-adjoint. -/
-- Proof sketch: differentiate `quadraticAffineObjective_gradient_eq`; the affine term vanishes and
-- the derivative of `x ↦ A x` is the constant operator `A`.
theorem quadraticAffineObjective_hessian_eq
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (x : E) :
    hessian (quadraticAffineObjective α a A) x = A := sorry

/-- Example 5.1.2: if `A` is positive, then the quadratic-affine objective
`f(x) = α + ⟪a, x⟫ + (1 / 2) ⟪A x, x⟫` on all of `E` is self-concordant with self-concordance
constant `M_f = 0`. -/
-- Proof sketch: `A.IsPositive` gives the Hessian positive-semidefinite condition, the quadratic
-- objective is `C^3` on all of `E`, and
-- `quadraticAffineObjective_thirdDirectionalDerivative_eq_zero` makes the cubic bound with
-- constant `0` immediate.
theorem quadraticAffineObjective_isSelfConcordantOnWith_zero
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (hA : A.IsPositive) :
    IsSelfConcordantOnWith (Set.univ : Set E) 0 (quadraticAffineObjective α a A) := sorry

end

/-! ### Lemma_5_1_2 (from Chap05) -/
open scoped Gradient
open scoped HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Lemma 5.1.2 lies in the chapter's self-concordance / higher-derivative multilinear domain.

Sampled owner declarations in this domain:
* `hessian` from `Chap01/Definition_1_4_16`, the chapter owner for the Hessian operator;
* `hessianLocalNorm` and its notation `‖u‖[f; x]` from `Chap05/Definition_5_1_1`;
* `thirdDirectionalDerivative_eq_iteratedFDeriv` from `Chap05/Definition_5_0_10`, the canonical
  bridge from the diagonal third directional derivative to the trilinear third Fréchet derivative;
* `(hessian f x).IsPositive`, the canonical pointwise Hessian-positivity owner used throughout
  Chapter 5 instead of a raw quadratic-form semidefiniteness binder;
* `ContinuousMultilinearMap.le_opNorm`, the canonical multilinear operator-norm estimate in
  mathlib.

Source/core/bridge triage:
* source-facing: the diagonal cubic self-concordance bound;
* core/canonical: the trilinear map `iteratedFDeriv ℝ 3 f x`;
* bridge/view: this equivalence between the diagonal bound and the full trilinear estimate.

Primitive data:
* the objective `f`;
* the domain point `x`;
* the pointwise Hessian positivity owner `(hessian f x).IsPositive`;
* the third Fréchet derivative of `f`.

Derived API:
* the source-facing diagonal bound `|D³f(x)[u, u, u]| ≤ 2 M_f ‖u‖[f; x]^3`;
* the Hessian quadratic-form nonnegativity needed to interpret `‖u‖[f; x]`;
* the full trilinear estimate with respect to the same local norm.

This file keeps the source-facing diagonal statement, but rewrites the public surface through the
chapter owners `hessian`, `thirdDirectionalDerivative`, and `‖u‖[f; x]` instead of duplicating
their raw formulas. The old raw pointwise semidefiniteness binder is replaced by the canonical
owner `(hessian f x).IsPositive`. Since the bridge to `iteratedFDeriv` is pointwise, the domain is
kept open so that `ContDiffOn ℝ 3 f dom` upgrades to `ContDiffAt ℝ 3 f x` for `x ∈ dom`. -/

-- Proof sketch: for the forward direction, apply the norm equality for symmetric trilinear forms
-- on the Hessian-induced inner-product space at each `x` to pass from the diagonal cubic bound to
-- the full multilinear operator-norm bound, then rescale by the three local Hessian norms. For
-- the reverse direction, specialize the trilinear estimate to `u₁ = u₂ = u₃ = u`.
/-- Lemma 5.1.2: for a `C³` function with positive-semidefinite Hessian on an open set `dom`, the
diagonal cubic bound in the definition of `M_f`-self-concordance is equivalent to the full
trilinear estimate on the third derivative. -/
theorem selfConcordant_diagonal_bound_iff_trilinear_bound
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hH : ∀ {x : E} (hx : x ∈ dom), (hessian f x).IsPositive) :
    (∀ {x : E} (hx : x ∈ dom) (u : E),
      |thirdDirectionalDerivative f x u| ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ)) ↔
      ∀ {x : E} (hx : x ∈ dom) (u₁ u₂ u₃ : E),
        |iteratedFDeriv ℝ 3 f x ![u₁, u₂, u₃]| ≤
          2 * (Mf : ℝ) * ‖u₁‖[f; x] * ‖u₂‖[f; x] * ‖u₃‖[f; x] := sorry

namespace IsSelfConcordantOnWith

/-- A self-concordant function satisfies the full trilinear third-derivative estimate on its
domain. -/
theorem iteratedFDeriv_bound
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f) {x : E} (hx : x ∈ dom) (u₁ u₂ u₃ : E) :
    |iteratedFDeriv ℝ 3 f x ![u₁, u₂, u₃]| ≤
      2 * (Mf : ℝ) * ‖u₁‖[f; x] * ‖u₂‖[f; x] * ‖u₃‖[f; x] := by
  have htrilinear :
      ∀ {y : E} (hy : y ∈ dom) (v₁ v₂ v₃ : E),
        |iteratedFDeriv ℝ 3 f y ![v₁, v₂, v₃]| ≤
          2 * (Mf : ℝ) * ‖v₁‖[f; y] * ‖v₂‖[f; y] * ‖v₃‖[f; y] :=
    (selfConcordant_diagonal_bound_iff_trilinear_bound
      hself.isOpen_domain
      hself.contDiffOn
      fun hx' ↦ hself.hessian_isPositive hx').1
      (fun hx' u ↦ hself.third_deriv_bound hx' u)
  exact htrilinear hx u₁ u₂ u₃

end IsSelfConcordantOnWith

/-! ### Theorem_5_1_2 (from Chap05) -/
universe u v

open scoped HessianLocalNorm

variable {E : Type u} {E₁ : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]

namespace IsSelfConcordantOnWith

/- Theorem 5.1.2 lies in the Chapter 5 self-concordance affine-pullback calculus.

Primary domain:
- self-concordant functions on open convex domains and affine precomposition

Sampled owner-style declarations in this domain:
- `IsSelfConcordantOnWith`
- `ConvexC1On.comp_continuousAffineMap`
- `ClosedConvexOn.comp_continuousAffineMap`
- mathlib `HasFTaylorSeriesUpToOn.comp_continuousAffineMap`

Best owner abstraction:
- `IsSelfConcordantOnWith.comp_continuousAffineMap`

Primitive data:
- the owner witness `hf : IsSelfConcordantOnWith dom Mf f`
- the continuous affine map `g : E →ᴬ[ℝ] E₁`

Derived API:
- the finite-dimensional affine-map specialization `comp_affineMap`
- the linear-plus-translation source presentation `x ↦ A x + b`

Source/core/bridge triage:
- source-facing: affine pullback closure of self-concordance
- core/canonical: `IsSelfConcordantOnWith.comp_continuousAffineMap`
- bridge/view: finite-dimensional affine maps, then the textbook `A x + b` presentation

The old statement used a plain `LinearMap` together with finite-dimensional hypotheses only to
recover continuity. The canonical owner surface is the continuous-affine-map pullback theorem;
finite-dimensional affine-map presentations should be derived from it rather than kept as the main
API. -/

-- Proof sketch: openness and convexity pull back along a continuous affine map, `ContDiffOn`
-- composes with continuous affine maps, and the affine bridge identities for the Hessian local
-- norm and third directional derivative transfer the cubic bound with the same constant `Mf`.
/-- Theorem 5.1.2: precomposing a self-concordant function with a continuous affine map preserves
self-concordance on the affine preimage with the same self-concordance constant. This is the
canonical owner-level affine-pullback theorem. -/
theorem comp_continuousAffineMap
    {dom : Set E₁} {Mf : NNReal} {f : E₁ → ℝ}
    (hf : IsSelfConcordantOnWith dom Mf f) (g : E →ᴬ[ℝ] E₁) :
    IsSelfConcordantOnWith (g ⁻¹' dom) Mf (f ∘ g) := by
  refine
    { isOpen_domain := hf.isOpen_domain.preimage g.continuous
      contDiffOn := hf.contDiffOn.comp g.contDiff.contDiffOn (fun _ hx ↦ hx)
      convexOn := by
        simpa using hf.convexOn.comp_affineMap (g : E →ᵃ[ℝ] E₁)
      third_deriv_bound := ?_ }
  intro x hx u
  have hx_dom : g x ∈ dom := hx
  have hcont :
      ContDiffAt ℝ 2 f (g x) := by
    exact (hf.contDiffOn.of_le (by norm_num)).contDiffAt (hf.isOpen_domain.mem_nhds hx_dom)
  simpa [thirdDirectionalDerivative_comp_affine, hessianLocalNorm_comp_affine f g x u hcont] using
    hf.third_deriv_bound hx_dom (g.contLinear u)

-- Proof sketch: regard an affine map on a finite-dimensional domain as a continuous affine map and
-- apply `comp_continuousAffineMap`.
/-- Theorem 5.1.2, finite-dimensional specialization: affine precomposition preserves
self-concordance on the affine preimage. -/
theorem comp_affineMap
    [FiniteDimensional ℝ E]
    {dom : Set E₁} {Mf : NNReal} {f : E₁ → ℝ}
    (hf : IsSelfConcordantOnWith dom Mf f) (g : E →ᵃ[ℝ] E₁) :
    IsSelfConcordantOnWith (g ⁻¹' dom) Mf (f ∘ g) := by
  simpa using hf.comp_continuousAffineMap ⟨g, g.continuous_of_finiteDimensional⟩

end IsSelfConcordantOnWith

/-! ### Corollary_5_1_3 (from Chap05) -/
open scoped Gradient HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace IsSelfConcordantOnWith

-- Proof sketch: scale the owner fields directly. Openness is unchanged, `C³` regularity is
-- preserved by `ContDiffOn.const_smul`, convexity by `ConvexOn.smul`, the third directional
-- derivative scales linearly with `α`, and the Hessian local norm scales by `√α`.
/-- Corollary 5.1.3: if `f` is self-concordant on `dom` with constant `Mf`, then for every
positive scalar `α` the rescaled function `(α : ℝ) • f` is self-concordant on the same domain
with constant `Mf / √α`. -/
theorem pos_smul
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (h : IsSelfConcordantOnWith dom Mf f) (α : NNRealˣ) :
    IsSelfConcordantOnWith dom (Mf / NNReal.sqrt α) ((α : ℝ) • f) := by
  have hα : 0 < (α : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero α))
  have hα_nonneg : 0 ≤ (α : ℝ) := le_of_lt hα
  refine
    { isOpen_domain := h.isOpen_domain
      contDiffOn := by
        simpa using h.contDiffOn.const_smul (α : ℝ)
      convexOn := by
        simpa using ConvexOn.smul hα_nonneg h.convexOn
      third_deriv_bound := ?_ }
  intro x hx u
  have hthird :
      thirdDirectionalDerivative (((α : ℝ) • f)) x u =
        (α : ℝ) * thirdDirectionalDerivative f x u := by
    rw [thirdDirectionalDerivative]
    have hs : directionalSlice (((α : ℝ) • f)) x u = (α : ℝ) • directionalSlice f x u := by
      funext t
      simp [directionalSlice]
    rw [hs, iteratedDeriv_const_smul_field]
    simp [thirdDirectionalDerivative, smul_eq_mul]
  have hnorm :
      hessianLocalNorm ((α : ℝ) • f) x u = Real.sqrt α * ‖u‖[f; x] := by
    have hhess : hessian (((α : ℝ) • f)) = (α : ℝ) • hessian f := by
      funext y
      unfold hessian
      rw [show ∇ (((α : ℝ) • f)) = (α : ℝ) • ∇ f by
        funext z
        unfold gradient
        rw [fderiv_const_smul_field]
        exact (InnerProductSpace.toDual ℝ E).symm.map_smul (α : ℝ) (fderiv ℝ f z)]
      rw [fderiv_const_smul_field]
    rw [hessianLocalNorm_def, hessianLocalNorm_def, hhess]
    simp only [Pi.smul_apply, ContinuousLinearMap.smul_apply, inner_smul_right]
    rw [Real.sqrt_mul hα_nonneg]
  calc
    |thirdDirectionalDerivative (((α : ℝ) • f)) x u|
        = (α : ℝ) * |thirdDirectionalDerivative f x u| := by
            rw [hthird, abs_mul, abs_of_nonneg hα_nonneg]
    _ ≤ (α : ℝ) * (2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ)) := by
      gcongr
      exact h.third_deriv_bound hx u
    _ = 2 * ((Mf / NNReal.sqrt α : NNReal) : ℝ) * (Real.sqrt α * ‖u‖[f; x]) ^ (3 : ℕ) := by
      rw [NNReal.coe_div, Real.coe_sqrt]
      have hsqrt_ne : Real.sqrt (α : ℝ) ≠ 0 := by
        exact Real.sqrt_ne_zero'.2 hα
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt hα_nonneg]
      ring
    _ = 2 * ((Mf / NNReal.sqrt α : NNReal) : ℝ) * hessianLocalNorm ((α : ℝ) • f) x u ^ (3 : ℕ) := by
      rw [hnorm]

end IsSelfConcordantOnWith

end

/-! ### Example_5_1_3 (from Chap05) -/
/- Example 5.1.3 lives in the scalar self-concordance domain.

Sampled owner declarations:
* `IsSelfConcordantOnWith`, the chapter owner for self-concordance with constant `Mf`;
* `IsStandardSelfConcordantOn`, the canonical chapter owner for the case `Mf = 1`;
* `IsSelfConcordantBarrierOnWith`, the later barrier refinement extending the standard owner;
* `Real.deriv_log`, the mathlib scalar logarithm derivative owner used in proofs.

Best owner abstraction:
* source-facing: the logarithmic barrier on `(0, ∞)`;
* core/canonical: `IsStandardSelfConcordantOn (Set.Ioi (0 : ℝ))`;
* bridge/view: `IsSelfConcordantBarrierOnWith`, which adds the barrier parameter inequality.

The scalar derivative identities for `x ↦ -log x` are proof-level derived API here, not the
mathematical owner of the example, so the file keeps only the canonical self-concordance
statement. -/

-- Proof sketch: verify the standard self-concordance conditions for `x ↦ -Real.log x` on
-- `(0, ∞)` using the canonical scalar logarithm derivative identities.
/-- Example 5.1.3: the univariate logarithmic barrier `x ↦ -log x` on `(0, ∞)` is standard
self-concordant. -/
instance negLog_isStandardSelfConcordantOn :
    IsStandardSelfConcordantOn (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -Real.log x) := sorry

/-! ### Lemma_5_1_3 (from Chap05) -/
open scoped HessianLocalNorm

noncomputable section

universe u

/- Lemma 5.1.3 lies in the chapter's self-concordance / line-derivative domain.

Sampled owner declarations in this domain:
* `thirdDirectionalDerivative` from `Definition_5_0_10`, the chapter owner for the cubic
  directional derivative;
* `directionalSlice` from `Definition_5_0_10`, the chapter owner for affine-line restriction;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Definition_5_1_1`, the chapter owner for
  the Hessian local norm;
* `associatedUnivariateFunction` from `Definition_5_0_12`, the source-facing reciprocal
  local-norm slice owner on the positivity domain;
* `associatedUnivariateFunctionDomain` from `Definition_5_0_12`, the source-facing owner for the
  natural positivity domain of that slice;
* nearby Chapter 5 line-derivative statements such as `Corollary_5_1_1` and `Theorem_5_1_4`,
  which already work over arbitrary complete real inner-product spaces.

Source/core/bridge triage:
* source-facing: the associated univariate reciprocal local-norm function and its natural domain
  along the affine line `t ↦ x + t • h`;
* core/canonical: `directionalSlice`, `thirdDirectionalDerivative f (x + t • h) h`, and
  `‖h‖[f; x + t • h]`;
* bridge/view: the ambient representative
  `directionalSlice (fun y ↦ 1 / ‖h‖[f; y]) x h` of
  `associatedUnivariateFunction dom f x h` on `associatedUnivariateFunctionDomain dom f x h`.

Primitive data:
* the objective `f`;
* the line data `x` and `h`;
* the open domain carrying `C³` regularity;
* the single point `t` of `associatedUnivariateFunctionDomain dom f x h`.

Derived API:
* the source-facing derivative bound for the reciprocal local-norm slice in terms of the chapter
  owners `thirdDirectionalDerivative` and `hessianLocalNorm`;
* the explicit derivative formula for the canonical affine-line bridge
  `directionalSlice (fun y ↦ 1 / ‖h‖[f; y]) x h` on
  `associatedUnivariateFunctionDomain dom f x h`.

This file therefore keeps `associatedUnivariateFunction` as the source-facing owner from
`Definition_5_0_12`, and its main public entry is the source-facing derivative bound for that
reciprocal local-norm slice. The explicit `HasDerivWithinAt` formula is only a bridge/view
statement because the one-variable calculus owner lives on ambient functions. Both statements use
the canonical ambient bridge `directionalSlice (fun y ↦ 1 / ‖h‖[f; y]) x h` on the natural domain
`associatedUnivariateFunctionDomain dom f x h`, not an ad hoc zero-extension. The Chapter 5
differential-calculus API used here already lives over complete real inner-product spaces, so
finite dimensionality is not part of the canonical statement. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {dom : Set E} {f : E → ℝ} {x h : E}

section AssociatedUnivariateFunctionBridge

local notation "sliceDomain" => associatedUnivariateFunctionDomain dom f x h
local notation "reciprocalLocalNormSlice" =>
  directionalSlice (fun y ↦ 1 / ‖h‖[f; y]) x h

-- Proof sketch: differentiate the reciprocal local-norm slice on its natural domain using the
-- explicit `HasDerivWithinAt` bridge below; the uniform quotient hypothesis bounds the resulting
-- derivative formula by `M_f` at the chosen point.
/-- Lemma 5.1.3: if `f` is `C³` on an open set `dom` and the quotient
`|D³f(x + t h)[h,h,h]| / (2 ‖h‖[f; x + t • h]^3)` is bounded by `M_f` throughout the natural
domain of the associated univariate function, then the derivative within that domain of the
canonical ambient representative `directionalSlice (fun y ↦ 1 / ‖h‖[f; y]) x h`, equivalently
`associatedUnivariateFunction dom f x h`, has absolute value at most `M_f` at every
`t ∈ associatedUnivariateFunctionDomain dom f x h`. -/
theorem abs_derivWithin_associatedUnivariateFunction_le
    {Mf : NNReal} {t : ℝ}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (ht : t ∈ sliceDomain)
    (hbound :
      ∀ {s : ℝ}, s ∈ sliceDomain →
        |thirdDirectionalDerivative f (x + s • h) h| /
            (2 * ‖h‖[f; x + s • h] ^ (3 : ℕ)) ≤ (Mf : ℝ)) :
    |derivWithin
        reciprocalLocalNormSlice
        sliceDomain
        t| ≤ (Mf : ℝ) := sorry

-- Proof sketch: let `g(t) = hessianLocalNorm f (x + t • h) h ^ 2`, so `g` is the Hessian
-- quadratic form along the line. Differentiate `g` using the `C³` regularity of `f` on the open
-- set containing the line, identify `g'` with `thirdDirectionalDerivative f (x + t • h) h`, and
-- then apply the chain rule to `g ↦ g^(-1/2)` rewritten as the reciprocal local norm.
/-- Bridge form of Lemma 5.1.3: at each `t ∈ associatedUnivariateFunctionDomain dom f x h` the
canonical ambient representative `directionalSlice (fun y ↦ 1 / ‖h‖[f; y]) x h`, equivalently
`associatedUnivariateFunction dom f x h` on its natural domain, has derivative within that domain
`-D³f(x + t h)[h,h,h] / (2 ‖h‖[f; x + t • h]^3)`. -/
theorem associatedUnivariateFunction_hasDerivWithinAt
    {t : ℝ}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (ht : t ∈ sliceDomain) :
    HasDerivWithinAt
      reciprocalLocalNormSlice
      (-(thirdDirectionalDerivative f (x + t • h) h /
          (2 * ‖h‖[f; x + t • h] ^ (3 : ℕ))))
      sliceDomain
      t := sorry

end AssociatedUnivariateFunctionBridge

end

/-! ### Theorem_5_1_3 (from Chap05) -/
noncomputable section

open Filter Set Topology
open scoped Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 5.1.3 lies in the self-concordance / barrier-function domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the chapter owner for self-concordance on an
  open convex domain;
* `IsBarrierFunctionOn` from `Chap01/Definition_1_10_18`, the canonical barrier owner on a closed
  feasible set via a bundled map on its interior;
* `liftedConeLogSumExpBarrier_restriction_isBarrierFunctionOn` from `Chap05/Theorem_5_4_7_7`,
  showing the same frontier-blow-up property on a relative ambient space via the canonical owner
  `IsBarrierFunctionOn`.

Best owner abstraction:
* source-facing input: `IsSelfConcordantOnWith dom Mf f`, with `IsSelfConcordantOn dom f` kept for
  the purely propositional companion consequence;
* core/canonical output: `IsBarrierFunctionOn (closure dom) F`, where `F` is the canonical
  restriction of `f` to `interior (closure dom) = dom`;
* bridge/view: the displayed `Tendsto` statement for sequences in `dom`.

Primitive data:
* the self-concordance-with-constant hypothesis on `dom`;
* nonemptiness of the open domain, needed only for the barrier-owner theorem, not for the
  restricted owner map itself.

Derived API:
* the restricted continuous owner map `hself.toBarrierMap`;
* the sequence-level frontier blow-up statement as a consequence of the barrier owner.
-/

namespace IsSelfConcordantOnWith

/-- On a self-concordant domain, taking interior after closure recovers the original domain. -/
theorem interior_closure_eq
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f) :
    interior (closure dom) = dom := by
  by_cases hdom : dom.Nonempty
  · have hinterior : (interior dom).Nonempty := by
      simpa [hself.isOpen_domain.interior_eq] using hdom
    calc
      interior (closure dom) = interior dom :=
        hself.convex_domain.interior_closure_eq_interior_of_nonempty_interior hinterior
      _ = dom := hself.isOpen_domain.interior_eq
  · simp [Set.not_nonempty_iff_eq_empty.mp hdom]

/-- The canonical bundled owner map of a self-concordant function on the intrinsic barrier domain
`interior (closure dom) = dom`. -/
abbrev toBarrierMap
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f) :
    C(interior (closure dom), ℝ) :=
  let hcont : ContinuousOn f (interior (closure dom)) := by
    simpa [hself.interior_closure_eq] using hself.contDiffOn.continuousOn
  { toFun := (interior (closure dom)).restrict f
    continuous_toFun := hcont.restrict }

/-- Theorem 5.1.3: a self-concordant function on a nonempty open convex domain is a barrier for
that domain in the canonical closed-set owner sense, namely for `closure dom` with owner map given
by restricting `f` to `interior (closure dom) = dom`. The self-concordance constant is explicit in
the hypothesis only so the bundled owner map can remain canonical without introducing a public
choice-based definition from the existential abbreviation `IsSelfConcordantOn`. -/
-- Proof sketch: the self-concordance hypothesis already packages openness, convexity, and `C³`
-- regularity on `dom`, hence continuity on `dom`. For a nonempty open convex set in finite
-- dimension, `interior (closure dom) = dom`, so `f` canonically defines a bundled continuous map
-- on `interior (closure dom)`. The textbook boundary blow-up statement is then exactly the barrier
-- axiom on `closure dom`.
theorem isBarrierFunctionOn
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f) (hdom : dom.Nonempty) :
    IsBarrierFunctionOn (closure dom) hself.toBarrierMap := sorry

end IsSelfConcordantOnWith

namespace IsSelfConcordantOn

/-- Companion consequence of Theorem 5.1.3: along any sequence in `dom` converging to a frontier
point of `dom`, the function values tend to `+∞`. -/
theorem tendsto_atTop_of_tendsto_frontier
    {dom : Set E} {f : E → ℝ} (hself : IsSelfConcordantOn dom f) (x : ℕ → dom) {xBar : E}
    (hx : Tendsto (fun k ↦ (x k : E)) atTop (𝓝 xBar))
    (hxBar : xBar ∈ frontier dom) :
    Tendsto (fun k ↦ f (x k)) atTop atTop := by
  rcases hself with ⟨Mf, hMf⟩
  let xClosure : ℕ → interior (closure dom) :=
    fun k ↦ ⟨x k, by simp [hMf.interior_closure_eq]⟩
  have hdom : dom.Nonempty := ⟨x 0, (x 0).property⟩
  have hxBarClosure : xBar ∈ frontier (closure dom) := by
    simpa [frontier, closure_closure, hMf.interior_closure_eq, hMf.isOpen_domain.interior_eq] using
      hxBar
  have hbarrier : IsBarrierFunctionOn (closure dom) hMf.toBarrierMap :=
    hMf.isBarrierFunctionOn hdom
  simpa [IsSelfConcordantOnWith.toBarrierMap, xClosure] using
    hbarrier.tendsTo_atTop_of_tendsto_frontier xClosure hx hxBarClosure

end IsSelfConcordantOn

/-! ### Corollary_5_1_4 (from Chap05) -/
open scoped HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Corollary 5.1.4 lies in the Chapter 5 self-concordance / one-dimensional slice domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOnWith` from `Chap05/Definition_5_1_1`, the chapter owner for
  self-concordance on an open convex domain;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Chap05/Definition_5_1_1`, the canonical
  local norm owner;
* `associatedUnivariateFunctionDomain` from `Chap05/Definition_5_0_12`, the source-facing owner
  for the reciprocal local-norm slice domain.

Best owner abstraction:
* source-facing: the natural parameter domain of the associated univariate reciprocal local-norm
  function along `t ↦ x + t • h`;
* core/canonical: the Hessian local norm `‖h‖[f; x + t • h]`;
* bridge/view: the textbook expansion
  `0 < inner ℝ h ((fderiv ℝ (∇ f) (x + t • h)) h)`.

Primitive data:
* a domain `dom`;
* the self-concordance owner `IsSelfConcordantOnWith dom Mf f`;
* a self-concordant objective `f`;
* a base point `x`;
* a direction `h` with positive local norm at `x`.

Derived API:
* the slice-domain owner `associatedUnivariateFunctionDomain dom f x h`;
* the interval inclusion corollary below, exposed as an owner-level method of
  `IsSelfConcordantOnWith`.

This corollary therefore reuses `associatedUnivariateFunctionDomain` directly as its public owner
and introduces no parallel local slice-domain alias. Its theorem surface follows the surrounding
Chapter 5 owner pattern by living in `namespace IsSelfConcordantOnWith`.
-/

namespace IsSelfConcordantOnWith

-- Proof sketch: restrict `f` to the affine slice `t ↦ x + t • h`. Under the source-faithful
-- positivity hypothesis `0 < (Mf : ℝ) * ‖h‖[f; x]`, self-concordance bounds the derivative of the
-- reciprocal local norm by `Mf`, so the reciprocal local norm stays positive on the displayed
-- interval; equivalently, the associated univariate function remains defined there.
/-- Corollary 5.1.4: if `f` is self-concordant on an open convex domain `dom` and `x ∈ dom`,
then the natural domain of the associated univariate function
`t ↦ (⟪∇² f (x + t • h) h, h⟫)^{-1/2}` contains the interval
`(-1 / (M_f ‖h‖[f; x]), 1 / (M_f ‖h‖[f; x]))` whenever the reciprocal radius is well-defined,
that is, under `0 < (M_f : ℝ) * ‖h‖[f; x]`. -/
theorem associatedUnivariateFunctionDomain_contains_interval
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f) {x h : E} (hx : x ∈ dom)
    (hMh : 0 < (Mf : ℝ) * ‖h‖[f; x]) :
    Set.Ioo (-(1 / ((Mf : ℝ) * ‖h‖[f; x]))) (1 / ((Mf : ℝ) * ‖h‖[f; x])) ⊆
      associatedUnivariateFunctionDomain dom f x h := sorry

end IsSelfConcordantOnWith

end

/-! ### Example_5_1_4 (from Chap05) -/
noncomputable section

universe u

/- Example 5.1.4 lies in the Chapter 5 self-concordance / logarithmic-sublevel-barrier domain.

Sampled owner-style declarations:
* `quadraticAffineObjective` from `Example_5_1_2`, the chapter source-facing owner for affine-
  quadratic objectives on a real Hilbert space;
* `sublevelLogBarrier` from `Theorem_5_1_4`, the chapter owner for barriers `x ↦ -log (β - f x)`;
* `IsStandardSelfConcordantOn` from `Definition_5_1_1`, the core self-concordance owner for
  constant `1`;
* `ContinuousLinearMap.IsPositive`, the canonical positivity owner for self-adjoint positive
  semidefinite operators.

Source/core/bridge triage:
* source-facing: the logarithmic barrier of the concave affine-quadratic potential
  `φ(x) = α + ⟪a, x⟫ - (1 / 2) ⟪A x, x⟫`;
* core/canonical: `sublevelLogBarrier (quadraticAffineObjective (-α) (-a) A) 0` on
  `{x : E | x ∈ (Set.univ : Set E) ∧ quadraticAffineObjective (-α) (-a) A x < 0}`;
* bridge/view: the sign rewrite
  `0 - quadraticAffineObjective (-α) (-a) A x = α + ⟪a, x⟫ - (1 / 2) ⟪A x, x⟫`.

Primitive data:
* `α`, `a`, and `A`.

Derived API:
* the generic strict sublevel set expression as a proof bridge for the textbook positivity set;
* the generic Chapter 5 sublevel barrier as a proof bridge for the textbook `-log φ`.

This example remains source-facing at the theorem surface: the public statement keeps the textbook
positivity domain and logarithmic barrier, while the Chapter 5 sublevel-barrier owners remain the
canonical internal bridge. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- The canonical strict-sublevel domain
`{x | quadraticAffineObjective (-α) (-a) A x < 0}` is exactly the textbook positivity domain
`{x | 0 < α + ⟪a, x⟫ - (1 / 2) ⟪A x, x⟫}`. -/
theorem quadraticAffineObjective_neg_strictSublevel_eq
    (α : ℝ) (a : E) (A : E →L[ℝ] E) :
    {x : E | quadraticAffineObjective (-α) (-a) A x < 0} =
      {x : E | 0 < α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x} := by
  ext x
  change quadraticAffineObjective (-α) (-a) A x < 0 ↔
    0 < α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x
  rw [quadraticAffineObjective_apply]
  simp only [inner_neg_left]
  constructor <;> intro hx <;> linarith

/- The canonical sublevel-log-barrier owner
`sublevelLogBarrier (quadraticAffineObjective (-α) (-a) A) 0` evaluates to the textbook
logarithmic barrier of the concave affine-quadratic potential. -/
theorem sublevelLogBarrier_quadraticAffineObjective_neg_eq
    (α : ℝ) (a : E) (A : E →L[ℝ] E) :
    sublevelLogBarrier (quadraticAffineObjective (-α) (-a) A) 0 =
      fun x ↦ -Real.log (α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x) := by
  funext x
  rw [sublevelLogBarrier_apply, quadraticAffineObjective_apply]
  simp only [inner_neg_left]
  congr 1
  ring_nf

variable [CompleteSpace E]

/-- Example 5.1.4: if `A` is positive, then the logarithmic barrier attached to the affine-
quadratic potential `φ(x) = α + ⟪a, x⟫ - (1 / 2) ⟪A x, x⟫` is standard self-concordant on its
positivity domain `{x | 0 < φ(x)}`. The generic Chapter 5 sublevel-barrier owners are only a
proof bridge behind this source-facing formulation. -/
theorem logAffineQuadraticBarrier_isStandardSelfConcordantOn
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (hA : A.IsPositive) :
    IsStandardSelfConcordantOn
      {x : E | 0 < α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x}
      (fun x ↦ -Real.log (α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x)) := sorry

end

/-! ### Lemma_5_1_4 (from Chap05) -/
noncomputable section

open Set
open scoped SelfConcordantAuxiliaryFunction

/- Lemma 5.1.4 belongs to the one-variable self-concordant auxiliary-function / Fenchel-conjugacy
domain.

Relevant owner-style declarations sampled before refinement:
* `selfConcordantOmega`, `selfConcordantOmegaStar`, `selfConcordantOmegaDeriv`, and
  `selfConcordantOmegaPrimeStar` in `Definition_5_0_21`, the chapter owners for `ω`, `ω_*`,
  `ω'`, and `ω'_*`;
* `selfConcordantOmegaArg` and `selfConcordantOmegaStarArg` in `Definition_5_0_21`, the
  canonical Chapter 5 constructors for the natural `ω` and `ω_*` subtype arguments;
* `fenchelDual` in `Definition_5_0_27`, the project-level canonical owner for Fenchel conjugacy in
  higher dimension;
* `IsMaxOn` in mathlib, the canonical owner-level maximizer predicate behind the scalar Fenchel
  support formulas.

Best owner abstraction:
* source-facing: the fixed chapter owners `ω`, `ω_*`, together with their explicit derivative and
  inverse branches `ω'`, `ω'_*`, and the textbook maximization identities built from them;
* core/canonical: the already-defined chapter auxiliary functions from `Definition_5_0_21`;
* bridge/view: the explicit scalar formulas specialized to those owners.

Primitive data:
* `ω`;
* `ω_*`.

Derived API:
* `ω'` and `ω'_*`;
* the canonical subtype constructors `selfConcordantOmegaArg` and
  `selfConcordantOmegaStarArg`;
* the domain-membership lemmas for `ω'` and `ω'_*`;
* the seven source-facing Fenchel-conjugacy identities of Lemma 5.1.4, stated directly against
  the canonical owners on their mathematically forced domains: the full owner domains for the
  inverse identities `(1)`, `(2)`, `(6)`, `(7)`, and the constrained nonnegative maximization
  regimes for `(3)`, `(4)`, `(5)`, without a parallel local point/maximand wrapper API; the
  maximizer data for parts `(3)` and `(4)` is carried by the numbered statements themselves. -/

theorem neg_one_lt_selfConcordantUnit_of_nonneg {t : ℝ} (ht : 0 ≤ t) : -1 < t := by
  have h : -1 < ((1 : NNReal) : ℝ) * t := neg_one_lt_mf_mul_of_nonneg ht
  simpa using h

/-- For `t ≥ 0`, the derivative branch `ω'(t)` is nonnegative. -/
theorem selfConcordantOmegaDeriv_nonneg {t : ℝ} (ht : 0 ≤ t) :
    let tω := selfConcordantOmegaArg 1 t (by
      simpa using neg_one_lt_selfConcordantUnit_of_nonneg ht)
    0 ≤ ω' tω := sorry

/-- On its natural domain `(-1, ∞)`, the derivative branch `ω'(t)` lies below `1`. -/
theorem selfConcordantOmegaDeriv_lt_one (tω : Ioi (-1 : ℝ)) :
    ω' tω < 1 := sorry

/-- For `t ≥ 0`, the derivative branch `ω'(t)` belongs to the slope interval `[0, 1)`. -/
theorem selfConcordantOmegaDeriv_mem_Ico {t : ℝ} (ht : 0 ≤ t) :
    let tω := selfConcordantOmegaArg 1 t (by
      simpa using neg_one_lt_selfConcordantUnit_of_nonneg ht)
    ω' tω ∈ Ico (0 : ℝ) 1 := sorry

/-- For `τ ∈ [0, 1)`, the inverse branch `ω'_*(τ)` is nonnegative. -/
theorem selfConcordantOmegaPrimeStar_nonneg {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    0 ≤ ω'_* ⟨τ, hτ1⟩ := sorry

/-- On its natural domain `(-∞, 1)`, the inverse branch `ω'_*(τ)` lies above `-1`. -/
theorem selfConcordantOmegaPrimeStar_gt_neg_one (τω : Iio (1 : ℝ)) :
    -1 < ω'_* τω := sorry

-- Proof sketch: substitute the explicit formulas
-- `ω'(t) = t / (1 + t)` and `ω'_*(τ) = τ / (1 - τ)` and simplify.
/-- Lemma 5.1.4 (1): for `τ < 1`, applying `ω'` to `ω'_*(τ)` returns `τ`. -/
theorem selfConcordantOmegaDeriv_selfConcordantOmegaPrimeStar
    {τ : ℝ} (hτ1 : τ < 1) :
    let τω := selfConcordantOmegaStarArg 1 τ (by simpa using hτ1)
    let tω := selfConcordantOmegaArg 1 (ω'_* τω) (by
      simpa using selfConcordantOmegaPrimeStar_gt_neg_one τω)
    ω' tω = τ := sorry

-- Proof sketch: substitute the explicit formulas
-- `ω'(t) = t / (1 + t)` and `ω'_*(τ) = τ / (1 - τ)` and simplify.
/-- Lemma 5.1.4 (2): for `t > -1`, applying `ω'_*` to `ω'(t)` returns `t`. -/
theorem selfConcordantOmegaPrimeStar_selfConcordantOmegaDeriv
    {t : ℝ} (ht : -1 < t) :
    let tω := selfConcordantOmegaArg 1 t (by
      simpa using ht)
    let τω := selfConcordantOmegaStarArg 1 (ω' tω) (by
      simpa using selfConcordantOmegaDeriv_lt_one tω)
    ω'_* τω = t := sorry

-- Proof sketch: evaluate the support functional `ξ ↦ ξ * t - ω_*(ξ)` at its canonical maximizer
-- `ξ = ω'(t)`.
/-- Lemma 5.1.4 (3): for `t ≥ 0`, the value `ω(t)` is the maximal value of the Fenchel support
functional `ξ ↦ ξ t - ω_*(ξ)` on `[0, 1)`, realized at `ξ = ω'(t)`. -/
theorem selfConcordantOmega_eq_mul_selfConcordantOmegaDeriv_sub_selfConcordantOmegaStar_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) :
    let tω := selfConcordantOmegaArg 1 t (by
      simpa using neg_one_lt_selfConcordantUnit_of_nonneg ht)
    let ξω := selfConcordantOmegaStarArg 1 (ω' tω) (by
      simpa using selfConcordantOmegaDeriv_lt_one tω)
    ξω ∈ {ξ : Iio (1 : ℝ) | 0 ≤ (ξ : ℝ)} ∧
      IsMaxOn
        (fun ξ : Iio (1 : ℝ) ↦ (ξ : ℝ) * t - ω_* ξ)
        {ξ : Iio (1 : ℝ) | 0 ≤ (ξ : ℝ)} ξω ∧
      ω tω = t * ω' tω - ω_* ξω := sorry

-- Proof sketch: evaluate the support functional `ξ ↦ τ * ξ - ω(ξ)` at its canonical maximizer
-- `ξ = ω'_*(τ)`.
/-- Lemma 5.1.4 (4): for `τ ∈ [0, 1)`, the value `ω_*(τ)` is the maximal value of the Fenchel
support functional `ξ ↦ τ ξ - ω(ξ)` on `[0, ∞)`, realized at `ξ = ω'_*(τ)`. -/
theorem
    selfConcordantOmegaStar_eq_mul_selfConcordantOmegaPrimeStar_sub_selfConcordantOmega_of_mem_Ico
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    let τω := selfConcordantOmegaStarArg 1 τ (by simpa using hτ1)
    let tω := selfConcordantOmegaArg 1 (ω'_* τω) (by
      simpa using selfConcordantOmegaPrimeStar_gt_neg_one τω)
    tω ∈ {ξ : Ioi (-1 : ℝ) | 0 ≤ (ξ : ℝ)} ∧
      IsMaxOn
        (fun ξ : Ioi (-1 : ℝ) ↦ τ * (ξ : ℝ) - ω ξ)
        {ξ : Ioi (-1 : ℝ) | 0 ≤ (ξ : ℝ)} tω ∧
      ω_* τω = τ * ω'_* τω - ω tω := sorry

-- Proof sketch: combine the supremum characterization of `ω_*(τ)` with the admissible test point
-- `t`.
/-- Lemma 5.1.4 (5): the Fenchel--Young inequality
`ω(t) + ω_*(τ) ≥ τ t` holds for `t ≥ 0` and `τ < 1`. -/
theorem selfConcordantOmega_add_selfConcordantOmegaStar_ge_mul
    {t τ : ℝ} (ht : 0 ≤ t) (hτ1 : τ < 1) :
    let tω := selfConcordantOmegaArg 1 t (by
      simpa using neg_one_lt_selfConcordantUnit_of_nonneg ht)
    let τω := selfConcordantOmegaStarArg 1 τ (by simpa using hτ1)
    ω tω + ω_* τω ≥ τ * t := sorry

-- Proof sketch: evaluate the maximization formula for `ω_*(τ)` at the maximizing point
-- `ξ = ω'_*(τ)`.
/-- Lemma 5.1.4 (6): for `τ < 1`, the conjugate value is
`ω_*(τ) = τ ω'_*(τ) - ω(ω'_*(τ))`. -/
theorem selfConcordantOmegaStar_eq_mul_selfConcordantOmegaPrimeStar_sub_selfConcordantOmega
    {τ : ℝ} (hτ1 : τ < 1) :
    let τω := selfConcordantOmegaStarArg 1 τ (by simpa using hτ1)
    let tω := selfConcordantOmegaArg 1 (ω'_* τω) (by
      simpa using selfConcordantOmegaPrimeStar_gt_neg_one τω)
    ω_* τω = τ * ω'_* τω - ω tω := sorry

-- Proof sketch: substitute `τ = ω'(t)` into part `(6)` and use part `(2)` to identify the
-- maximizing point.
/-- Lemma 5.1.4 (7): for `t > -1`, the original function value can be recovered from the conjugate
by `ω(t) = t ω'(t) - ω_*(ω'(t))`. -/
theorem selfConcordantOmega_eq_mul_selfConcordantOmegaDeriv_sub_selfConcordantOmegaStar
    {t : ℝ} (ht : -1 < t) :
    let tω := selfConcordantOmegaArg 1 t (by
      simpa using ht)
    let τω := selfConcordantOmegaStarArg 1 (ω' tω) (by
      simpa using selfConcordantOmegaDeriv_lt_one tω)
    ω tω = t * ω' tω - ω_* τω := sorry

end
