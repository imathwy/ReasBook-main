import Mathlib
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_5_1 (from Chap01) -/
/- Definition 1.5.1 is the Chapter 1 `source-facing` recall point in the multivariable
Taylor-series regularity domain.

Primary domain: higher-order Taylor control on a set together with a Lipschitz bound on a fixed
Taylor coefficient.

Sampled owner-style declarations:
* `HasFTaylorSeriesUpToOn`
* `HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn`
* `HasFTaylorSeriesUpToOn.continuousLinearMap_comp`
* `HasFTaylorSeriesUpToOn.add`

Owner abstraction:
* the source-facing class `taylorCoeffLipschitzClass k p L Q`, with notation
  `𝒞^{k,p}_{L}(Q)`
* the Taylor-series-on-a-set predicate `HasFTaylorSeriesUpToOn k f P Q`

Source/core/bridge triage:
* `source-facing`: the textbook class `C^{k,p}_L(Q)`, expressed as
  `p ≤ k ∧ ∃ P, HasFTaylorSeriesUpToOn k f P Q ∧ LipschitzOnWith L (fun x ↦ P x p) Q`
* `core/canonical`: the owner predicate `HasFTaylorSeriesUpToOn`
* `bridge/view`: on `UniqueDiffOn ℝ Q`, the coordinate formula through `iteratedFDerivWithin`
  recovered by `HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn`

Primitive data:
* the order constraint `p ≤ k`
* a Taylor witness `P`
* the owner predicate `HasFTaylorSeriesUpToOn k f P Q`
* the Lipschitz bound on the `p`-th Taylor coefficient `fun x ↦ P x p`

Derived API:
* the source-facing membership surface `f ∈ 𝒞^{k,p}_{L}(Q)`
* the `iteratedFDerivWithin` description under `UniqueDiffOn`
* linearity transport of Taylor witnesses via `HasFTaylorSeriesUpToOn.continuousLinearMap_comp`
* addition of Taylor witnesses via `HasFTaylorSeriesUpToOn.add`

This file keeps the textbook class as a thin source-facing owner on functions, while the
Taylor-series owner declarations remain the canonical core/bridge companions for downstream use.
-/

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (k p : ℕ) (L : NNReal) (f : E → ℝ) (Q : Set E)

local notation "TaylorSeries" => E → FormalMultilinearSeries ℝ E ℝ

/-- Definition 1.5.1: the textbook class `C^{k,p}_L(Q)` of real-valued functions on `Q`
consists of functions that admit a Taylor-series witness up to order `k` on `Q` whose `p`-th
coefficient is `L`-Lipschitz on `Q`. -/
def taylorCoeffLipschitzClass (k p : ℕ) (L : NNReal) (Q : Set E) : Set (E → ℝ) :=
  {g | p ≤ k ∧ ∃ P : TaylorSeries,
    HasFTaylorSeriesUpToOn k g P Q ∧
      LipschitzOnWith L (fun x ↦ P x p) Q}

notation "𝒞^{" k "," p "}_{" L "}(" Q ")" => taylorCoeffLipschitzClass k p L Q

/-- Writing the source-facing owner with the textbook notation `𝒞^{k,p}_{L}(Q)` does not change
its membership criterion. -/
-- Proof sketch: unfold the notation `𝒞^{k,p}_{L}(Q)`.
@[simp] theorem mem_taylorCoeffLipschitzClass_notation_iff :
    f ∈ 𝒞^{k,p}_{L}(Q) ↔
      p ≤ k ∧ ∃ P : TaylorSeries,
        HasFTaylorSeriesUpToOn k f P Q ∧
          LipschitzOnWith L (fun x ↦ P x p) Q :=
  Iff.rfl

namespace taylorCoeffLipschitzClass

/-- Membership in the textbook class `𝒞^{k,p}_{L}(Q)` implies the order bound `p ≤ k`. -/
-- Proof sketch: extract the first conjunct from
-- `mem_taylorCoeffLipschitzClass_notation_iff`.
theorem order_le {k p : ℕ} {L : NNReal} {f : E → ℝ} {Q : Set E}
    (hf : f ∈ 𝒞^{k,p}_{L}(Q)) :
    p ≤ k := by
  exact hf.1

/-- Membership in the textbook class `𝒞^{k,p}_{L}(Q)` yields the Taylor witness and the
corresponding Lipschitz bound from Definition 1.5.1. -/
-- Proof sketch: extract the existential witness from
-- `mem_taylorCoeffLipschitzClass_notation_iff`.
theorem exists_taylorSeries
    {k p : ℕ} {L : NNReal} {f : E → ℝ} {Q : Set E}
    (hf : f ∈ 𝒞^{k,p}_{L}(Q)) :
    ∃ P : TaylorSeries,
      HasFTaylorSeriesUpToOn k f P Q ∧
        LipschitzOnWith L (fun x ↦ P x p) Q := by
  exact hf.2

end taylorCoeffLipschitzClass

#check (f ∈ 𝒞^{k,p}_{L}(Q))

end

recall HasFTaylorSeriesUpToOn
recall HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn
recall HasFTaylorSeriesUpToOn.continuousLinearMap_comp
recall HasFTaylorSeriesUpToOn.add

/-! ### Definition_1_5_1 (from Items/Chap01) -/
/- Definition 1.5.1 lies in the higher-order Taylor-coefficient regularity domain.

Relevant owner-style declarations sampled before refining:
* `taylorCoeffLipschitzClass` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_5_1.lean`, the project's
  source-facing owner for the textbook class `C^{k,p}_L(Q)`;
* `HasFTaylorSeriesUpToOn`, the canonical mathlib owner for Taylor data on a set;
* `mem_taylorCoeffLipschitzClass_notation_iff`, the source-facing membership bridge for the
  textbook notation;
* `taylorCoeffLipschitzClass.exists_taylorSeries`, the canonical witness-extraction theorem used
  by direct downstream files such as `Chap04/Definition_4_2_10`.

Best owner abstraction:
* source-facing owner: `taylorCoeffLipschitzClass k p L Q`;
* core/canonical owner: `HasFTaylorSeriesUpToOn`;
* bridge/view: the notation surface `f ∈ 𝒞^{k,p}_{L}(Q)` and the witness-extraction API.

Primitive data:
* the orders `k` and `p`;
* the Lipschitz constant `L`;
* the set `Q`;
* a Taylor witness `P` together with `HasFTaylorSeriesUpToOn k f P Q`;
* the Lipschitz bound on the `p`-th Taylor coefficient.

Derived API:
* the source-facing class membership `f ∈ 𝒞^{k,p}_{L}(Q)`;
* the order consequence `p ≤ k`;
* extraction of the Taylor witness and its Lipschitz estimate.

Source/core/bridge triage:
* source-facing: the textbook class `C^{k,p}_L(Q)`;
* core/canonical: `HasFTaylorSeriesUpToOn`;
* bridge/view: the notation and witness theorems exported by the Chapter 1 owner file.

This item is therefore a source-facing recall of the existing Chapter 1 owner rather than a new
local definition. Keeping a second item-local set-valued wrapper here would duplicate the owner
already used downstream. -/

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (k p : ℕ) (L : NNReal) (Q : Set E) (f : E → ℝ)

/- Definition 1.5.1: the textbook class `C^{k,p}_L(Q)` is the Chapter 1 owner
`taylorCoeffLipschitzClass k p L Q`. -/
recall taylorCoeffLipschitzClass

/- The textbook notation already uses this owner directly. -/
#check (f ∈ 𝒞^{k,p}_{L}(Q))

/- Membership in the textbook notation is exactly the source-facing Taylor-witness condition. -/
recall mem_taylorCoeffLipschitzClass_notation_iff

/- Membership provides the textbook order bound `p ≤ k`. -/
recall taylorCoeffLipschitzClass.order_le

/- Membership also provides the underlying Taylor witness and its Lipschitz coefficient bound. -/
recall taylorCoeffLipschitzClass.exists_taylorSeries

end

/-! ### Definition_1_5_2 (from Chap01) -/
open scoped Gradient

/- Definition 1.5.2 is the Chapter 1 source-facing recall point for the textbook class
`C^{1,1}_L`.

Source/core/bridge triage:
* source-facing: the textbook `C^{1,1}_L` condition on a real-valued function
* core/canonical: the owner predicates `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)`
* bridge/view: the pointwise estimate `hgrad.norm_sub_le x y` and the differentiability
  consequence `ContDiff.differentiable_one`

Primary domain:
* first-order smooth optimization on real Hilbert spaces

Sampled owner-style declarations:
* `gradient`
* `ContDiff ℝ 1 f`
* `LipschitzWith L (∇ f)`
* `ContDiff.differentiable_one`
* `LipschitzWith.norm_sub_le`

Owner abstraction:
* the canonical pair `ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f)`

Primitive data:
* a function `f`
* a Lipschitz constant `L`

Derived API:
* ordinary differentiability from `ContDiff.differentiable_one`
* the textbook estimate `‖∇ f x - ∇ f y‖ ≤ L ‖x - y‖` from `LipschitzWith.norm_sub_le`

This item is treated as a canonical type-expression recall rather than a new owner definition:
nearby Chapter 1 files use the pair `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)` directly,
so introducing a second wrapper or notation here would create a parallel API. -/

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {L : NNReal}

/- Definition 1.5.2: the textbook class `C_{L}^{1,1}(ℝ^n)` is represented in this chapter by
the conjunction `ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f)`, meaning that `f` is `C¹` and its
gradient is globally `L`-Lipschitz. -/
#check (ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f))

/- The `C¹` component of Definition 1.5.2 supplies ordinary differentiability. -/
recall ContDiff.differentiable_one

/- The Lipschitz-gradient component of Definition 1.5.2 yields the textbook pointwise estimate
`‖∇ f x - ∇ f y‖ ≤ L ‖x - y‖`. -/
recall LipschitzWith.norm_sub_le

end

/-! ### Definition_1_5_3 (from Chap01) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Domain design notes:

Primary domain:
* functions with Lipschitz-continuous Hessian on a real Hilbert space

Sampled owner-style declarations:
* `HasLipschitzContinuousHessian` in `Chap04/Definition_4_2_7`
* `HasLipschitzContinuousHessian.contDiff`
* `HasLipschitzContinuousHessian.norm_sub_le`
* the theorem-surface notation `f ∈ C22[M]`

Best owner abstraction:
* source-facing: the textbook class `C_M^{2,2}(ℝⁿ)`
* core/canonical: `HasLipschitzContinuousHessian M f`
* bridge/view: the theorem-surface notation `f ∈ C22[M]`, the `C²` projection
  `HasLipschitzContinuousHessian.contDiff`, and the Hessian-difference estimate
  `HasLipschitzContinuousHessian.norm_sub_le`

Primitive data:
* none; this is a recall-only item

Derived API:
* the owner predicate `HasLipschitzContinuousHessian M f`
* the notation `f ∈ C22[M]`
* the `C²` regularity projection
* the operator-norm Hessian estimate

This item is a pure recall of the chapter owner, not a place to introduce a parallel local
wrapper. The textbook `ℝⁿ` statement is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/

section

variable {M : NNReal} {f : E → ℝ}

/- Definition 1.5.3: the textbook class `C_M^{2,2}(ℝⁿ)` is represented in this project by the
canonical owner `HasLipschitzContinuousHessian M f`, written on theorem surfaces as `f ∈ C22[M]`.
Its defining consequences are the inherited `C²` regularity and the displayed Hessian Lipschitz
estimate `‖∇² f(x) - ∇² f(y)‖ ≤ M ‖x - y‖`. -/
recall HasLipschitzContinuousHessian

set_option linter.hashCommand false in
#check (f ∈ C22[M])

recall HasLipschitzContinuousHessian.contDiff

recall HasLipschitzContinuousHessian.norm_sub_le

end

/-! ### Lemma_1_5_4 (from Chap01) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {L : NNReal} {f : E → ℝ}

/- Lemma 1.5.4 is `source-facing` in second-order smooth optimization.

Source/core/bridge triage:
* `source-facing`: the textbook equivalence between an `L`-Lipschitz gradient and the pointwise
  operator-norm bound `‖∇² f(x)‖ ≤ L` under `C²` regularity
* `core/canonical`: the owner hypotheses `LipschitzWith L (∇ f)` from Definition 1.5.2 and the
  Hessian operator `hessian f x` from Definition 1.4.16
* `bridge/view`: the pointwise real inequality `‖hessian f x‖ ≤ L`

Sampled owner-style declarations:
* `gradient`
* `hessian f x`, the chapter's intrinsic Hessian owner from Definition 1.4.16
* `norm_fderiv_le_of_lipschitz`
* `lipschitzWith_of_nnnorm_fderiv_le`

Owner abstraction:
* the gradient map `∇ f` together with its canonical Hessian operator `hessian f x`

Primitive data:
* a twice continuously differentiable function `f`
* a Lipschitz constant `L`

Derived API:
* the global Lipschitz predicate `LipschitzWith L (∇ f)`
* the pointwise Hessian-operator bound `∀ x, ‖hessian f x‖ ≤ L`

The theorem is stated on a real Hilbert space, and specializing `E` to `EuclideanSpace ℝ (Fin n)`
recovers the textbook `ℝⁿ` formulation. -/
/-- Helper for Lemma 1.5.4: a pointwise operator-norm bound on the Hessian makes the gradient
globally `L`-Lipschitz once the gradient is differentiable. -/
-- Proof sketch: apply the mean value theorem in the form
-- `lipschitzWith_of_nnnorm_fderiv_le` to the gradient map, using differentiability of `∇ f` as
-- primitive data and the pointwise Hessian-operator bound as the derivative estimate.
theorem lipschitzGradient_of_norm_hessian_le
    (hgrad : Differentiable ℝ (∇ f))
    (hbound : ∀ x : E, ‖hessian f x‖ ≤ (L : ℝ)) :
    LipschitzWith L (∇ f) := by
  refine lipschitzWith_of_nnnorm_fderiv_le hgrad ?_
  intro x
  simpa [hessian] using hbound x

/-- Bridge form of Lemma 1.5.4: once the gradient map is differentiable, `∇ f` is globally
`L`-Lipschitz if and only if the Hessian operator satisfies the pointwise norm bound
`‖∇² f(x)‖ ≤ L`, expressed through the chapter owner `hessian f x`. -/
-- Proof sketch: if `∇ f` is globally `L`-Lipschitz, apply
-- `norm_fderiv_le_of_lipschitz` to the map `x ↦ ∇ f x`. Conversely, use
-- `lipschitzWith_of_nnnorm_fderiv_le` for `∇ f`, with differentiability supplied directly by
-- `hgrad`.
theorem lipschitzGradient_iff_norm_hessian_le
    (hgrad : Differentiable ℝ (∇ f)) :
    LipschitzWith L (∇ f) ↔ ∀ x : E, ‖hessian f x‖ ≤ (L : ℝ) := by
  constructor
  · intro hgrad x
    simpa [hessian] using norm_fderiv_le_of_lipschitz ℝ hgrad
  · exact lipschitzGradient_of_norm_hessian_le hgrad

/-- Helper for Lemma 1.5.4: a `C²` function has a differentiable gradient field. -/
-- Proof sketch: first upgrade the gradient to a `C¹` map by composing the derivative of `f`
-- with the inverse Riesz isomorphism, then read off differentiability of that gradient map.
theorem differentiable_gradient_of_contDiff_two
    (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (∇ f) := by
  have hcontDiffGradient : ContDiff ℝ 1 (∇ f) := by
    simpa [gradient, Function.comp] using
      ((InnerProductSpace.toDual ℝ E).symm.contDiff.comp
        (hf.fderiv_right (by norm_num)))
  -- A `C¹` map is differentiable everywhere, which is the only bridge the main equivalence needs.
  exact hcontDiffGradient.differentiable_one

/-- Lemma 1.5.4 in textbook `C²` form: if `f` is twice continuously differentiable, then the
gradient-Lipschitz condition is equivalent to the pointwise Hessian operator-norm bound. -/
theorem lipschitzGradient_iff_norm_hessian_le_of_contDiff
    (hf : ContDiff ℝ 2 f) :
    LipschitzWith L (∇ f) ↔ ∀ x : E, ‖hessian f x‖ ≤ (L : ℝ) := by
  -- The `C²` hypothesis provides differentiability of `∇ f`.
  -- That bridge lets us invoke the abstract Hessian/Lipschitz equivalence.
  have hgrad : Differentiable ℝ (∇ f) := differentiable_gradient_of_contDiff_two hf
  exact lipschitzGradient_iff_norm_hessian_le hgrad

end

end

/-! ### Proposition_1_5_5 (from Chap01) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {k p : ℕ}

namespace taylorCoeffLipschitzClass

/-- Proposition 1.5.5: if two functions belong to the textbook class `C^{k,p}_L(Q)`, written in
this file as `𝒞^{k,p}_{L}(Q)`, then any linear combination remains in the same class, with
Lipschitz constant `‖α₁‖₊ * L₁ + ‖α₂‖₊ * L₂`. -/
-- Proof sketch: extract the source-facing class data, transport the underlying Taylor witnesses
-- through scalar multiplication and addition, and combine the resulting Lipschitz bounds on the
-- `p`-th coefficient.
theorem smul_add
    {Q : Set E}
    {L₁ L₂ : NNReal}
    {f₁ f₂ : E → ℝ}
    {α₁ α₂ : ℝ}
    (hf₁ : f₁ ∈ 𝒞^{k,p}_{L₁}(Q))
    (hf₂ : f₂ ∈ 𝒞^{k,p}_{L₂}(Q)) :
    α₁ • f₁ + α₂ • f₂ ∈ 𝒞^{k,p}_{(‖α₁‖₊ * L₁ + ‖α₂‖₊ * L₂)}(Q) := by
  rcases exists_taylorSeries hf₁ with ⟨P₁, hP₁, hLip₁⟩
  rcases exists_taylorSeries hf₂ with ⟨P₂, hP₂, hLip₂⟩
  refine ⟨order_le hf₁, ⟨α₁ • P₁ + α₂ • P₂, ?_, ?_⟩⟩
  · simpa [Pi.smul_apply, Pi.add_apply] using
      (hP₁.continuousLinearMap_comp (ContinuousLinearMap.lsmul ℝ ℝ α₁)).add
        (hP₂.continuousLinearMap_comp (ContinuousLinearMap.lsmul ℝ ℝ α₂))
  · have hLip₁' : LipschitzOnWith (‖α₁‖₊ * L₁) (fun x ↦ α₁ • P₁ x p) Q := by
      simpa using (lipschitzWith_smul α₁).comp_lipschitzOnWith hLip₁
    have hLip₂' : LipschitzOnWith (‖α₂‖₊ * L₂) (fun x ↦ α₂ • P₂ x p) Q := by
      simpa using (lipschitzWith_smul α₂).comp_lipschitzOnWith hLip₂
    simpa [Pi.smul_apply, Pi.add_apply] using hLip₁'.add hLip₂'

end taylorCoeffLipschitzClass

end

/-! ### Proposition_1_5_6 (from Chap01) -/
open scoped Gradient

noncomputable section

/- Proposition 1.5.6 is `source-facing` in first-order smooth optimization.

Source/core/bridge triage:
* source-facing: the textbook affine objective `x ↦ α + ⟪a, x⟫` belongs to `C^{1,1}_0`
* core/canonical: the primitive affine owner `E →ᴬ[ℝ] ℝ` together with the Chapter 1 target
  predicate `ContDiff ℝ 1 f ∧ LipschitzWith 0 (∇ f)` from Definition 1.5.2
* bridge/view: coercion from `ContinuousAffineMap` to functions, and the owner-side gradient
  formula below

Primary domain:
* affine real-valued objectives on real Hilbert spaces

Sampled owner-style declarations:
* `ContinuousAffineMap.contDiff`
* `ContinuousAffineMap.hasFDerivAt`
* `ContDiff ℝ 1 f`
* `LipschitzWith L (∇ f)`
* `LipschitzWith.const`

Best owner abstraction:
* `ContinuousAffineMap ℝ E ℝ` for the affine objective itself

Primitive data:
* a continuous affine functional `f : E →ᴬ[ℝ] ℝ`

Derived API:
* its `C¹` regularity
* the constant-gradient formula
* the global `0`-Lipschitz bound on the gradient

The proposition stays source-facing, but its proof now factors through the canonical affine owner
instead of rebuilding the affine calculus directly on the raw lambda term.

The textbook statement is about `ℝⁿ`, but the proof only uses the real Hilbert-space gradient API,
so the canonical owner theorem lives at that intrinsic level.
-/

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace ContinuousAffineMap

/-- The gradient of a real-valued continuous affine functional is the constant field given by its
linear part under the Riesz identification. -/
theorem gradient_eq (f : E →ᴬ[ℝ] ℝ) :
    ∇ (f : E → ℝ) = fun _ : E ↦ (InnerProductSpace.toDual ℝ E).symm f.contLinear :=
  _root_.gradient_eq fun _ ↦ f.hasFDerivAt.hasGradientAt

/-- A real-valued continuous affine functional is `C¹` and has globally `0`-Lipschitz gradient. -/
theorem contDiff_one_and_gradient_lipschitz_zero (f : E →ᴬ[ℝ] ℝ) :
    ContDiff ℝ 1 (f : E → ℝ) ∧ LipschitzWith 0 (∇ (f : E → ℝ)) := by
  refine ⟨by simpa using f.contDiff, ?_⟩
  rw [f.gradient_eq]
  exact LipschitzWith.const ((InnerProductSpace.toDual ℝ E).symm f.contLinear)

end ContinuousAffineMap

/-- Proposition 1.5.6: the affine function `x ↦ α + ⟪a, x⟫` is `C¹` and its gradient is globally
`0`-Lipschitz, equivalently it belongs to the class `C^{1,1}_0`. This is the intrinsic
Hilbert-space form of the textbook `ℝⁿ` statement. -/
-- Proof sketch: package `x ↦ α + ⟪a, x⟫` as the continuous affine functional
-- `(innerSL ℝ a).toContinuousAffineMap +ᵥ ContinuousAffineMap.const ℝ E α`, apply the owner-level
-- `ContinuousAffineMap.contDiff_one_and_gradient_lipschitz_zero`, and then evaluate the coercion.
theorem affineFunction_contDiff_and_gradient_lipschitz_zero
    (α : ℝ) (a : E) :
    ContDiff ℝ 1 (fun x : E ↦ α + inner ℝ a x) ∧
      LipschitzWith 0 (∇ (fun x : E ↦ α + inner ℝ a x)) := by
  let f : E →ᴬ[ℝ] ℝ :=
    (innerSL ℝ a).toContinuousAffineMap +ᵥ ContinuousAffineMap.const ℝ E α
  have hf : (f : E → ℝ) = fun x : E ↦ α + inner ℝ a x := by
    funext x
    simp [f, add_comm]
  simpa [hf] using f.contDiff_one_and_gradient_lipschitz_zero

end

/-! ### Proposition_1_5_7 (from Chap01) -/
open Matrix
open scoped Gradient

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 1.5.7 is `source-facing` in first-order smooth optimization for quadratic
objectives on `ℝⁿ`.

Source/core/bridge triage:
* source-facing: the symmetric quadratic objective `quadraticObjective α a A`
* core/canonical: the owner predicates `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)` from
  Definition 1.5.2
* bridge/view: the pointwise gradient formula `quadraticObjective_gradient_eq`

Primary domain:
* symmetric quadratic objectives on finite-dimensional real inner-product spaces

Sampled owner-style declarations:
* `quadraticObjective` in Definition 1.9.1
* `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)` in Definition 1.5.2
* `UnconstrainedQuadraticMinimizationProblem.gradient_eq` in Proposition 1.9.11, which gives the
  same gradient owner-side under the stronger positive-definite hypothesis
* `ContinuousLinearMap.lipschitz`, the canonical linear-map Lipschitz API

Best owner abstraction:
* `quadraticObjective`

Primitive data:
* the scalar `α`
* the linear coefficient `a`
* the symmetric matrix `A`

Derived API:
* the explicit gradient formula
* `C¹` regularity
* the global Lipschitz bound for the gradient
-/

/-- The gradient of a symmetric quadratic objective is `x ↦ a + A x`. -/
theorem quadraticObjective_gradient_eq
    (α : ℝ) (a : E) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    ∇ (quadraticObjective α a A) = fun x ↦ a + A.toEuclideanLin x := by
  let B : E →L[ℝ] E := A.toEuclideanLin.toContinuousLinearMap
  have hBsymm : (B : E →ₗ[ℝ] E).IsSymmetric := by
    have hAherm : A.IsHermitian := by
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA
    change A.toEuclideanLin.IsSymmetric
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hAherm
  have hgradAt : ∀ x : E, HasGradientAt (quadraticObjective α a A) (a + B x) x := by
    intro x
    have hAffine : HasFDerivAt (fun y : E ↦ inner ℝ a y) (innerSL ℝ a) x := by
      simpa using (innerSL ℝ a).hasFDerivAt
    have hQuad' : HasFDerivAt (fun y : E ↦ inner ℝ (B y) y) (2 • innerSL ℝ (B x)) x := by
      convert (B.hasFDerivAt.inner ℝ (hasFDerivAt_id x))
      ext y
      simp only [ContinuousLinearMap.coe_smul', coe_innerSL_apply, Pi.smul_apply, nsmul_eq_mul,
        Nat.cast_ofNat, id_eq, ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', fderivInnerCLM_apply]
      calc
        2 * inner ℝ (B x) y = inner ℝ y (B x) + inner ℝ y (B x) := by
          rw [real_inner_comm y (B x)]
          ring
        _ = inner ℝ y (B x) + inner ℝ (B y) x := by
          congr 1
          exact (hBsymm y x).symm
        _ = inner ℝ (B x) y + inner ℝ (B y) x := by
          rw [real_inner_comm y (B x)]
    have hQuad0 : HasFDerivAt (fun y : E ↦ (1 / 2 : ℝ) • inner ℝ (B y) y)
        ((1 / 2 : ℝ) • (2 • innerSL ℝ (B x))) x :=
      hQuad'.const_smul (1 / 2 : ℝ)
    have hlin : ((1 / 2 : ℝ) • (2 • innerSL ℝ (B x))) = innerSL ℝ (B x) := by
      apply ContinuousLinearMap.ext
      intro y
      simp
    have hQuad : HasFDerivAt (fun y : E ↦ (1 / 2 : ℝ) • inner ℝ (B y) y)
        (innerSL ℝ (B x)) x :=
      hlin ▸ hQuad0
    have hSum : HasFDerivAt
        (fun y : E ↦ inner ℝ a y + (1 / 2 : ℝ) • inner ℝ (B y) y)
        (innerSL ℝ a + innerSL ℝ (B x)) x := by
      simpa [Pi.add_apply, add_assoc] using hAffine.add hQuad
    have hDeriv0 : HasFDerivAt
        (fun y : E ↦ α + (inner ℝ a y + (1 / 2 : ℝ) • inner ℝ (B y) y))
        (innerSL ℝ a + innerSL ℝ (B x)) x :=
      hSum.const_add α
    have hDeriv : HasFDerivAt (quadraticObjective α a A) (innerSL ℝ a + innerSL ℝ (B x)) x := by
      convert hDeriv0 using 1
      funext y
      simp [quadraticObjective, B, add_assoc, smul_eq_mul]
    have hdual : (InnerProductSpace.toDual ℝ E).symm (innerSL ℝ a + innerSL ℝ (B x)) = a + B x := by
      apply (InnerProductSpace.toDual ℝ E).injective
      ext z
      simp [innerSL_apply_apply]
    simpa [hdual] using hDeriv.hasGradientAt
  exact gradient_eq hgradAt

/-- Proposition 1.5.7: if `A` is symmetric, then the quadratic objective
`quadraticObjective α a A` is `C¹` on `ℝⁿ` and its gradient is globally Lipschitz
with constant equal to the operator norm of `A`, i.e. it belongs to `C^{1,1}_L(ℝⁿ)` for
`L = ‖A‖`. -/
-- Proof sketch: differentiate the affine and quadratic parts to obtain
-- `∇ (quadraticObjective α a A) x = a + (Matrix.toEuclideanLin A) x`, where
-- symmetry identifies the Hessian with `A`. Then the quadratic objective is `C¹`, and the linear
-- estimate `‖A (x - y)‖ ≤ ‖A‖ ‖x - y‖` gives the global Lipschitz bound for the gradient.
theorem symmetric_quadratic_contDiff_and_gradient_lipschitz
    (α : ℝ) (a : E) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    ContDiff ℝ 1 (quadraticObjective α a A) ∧
      LipschitzWith ‖A.toEuclideanLin.toContinuousLinearMap‖₊
        (∇ (quadraticObjective α a A)) := by
  let B : E →L[ℝ] E := A.toEuclideanLin.toContinuousLinearMap
  have hAffineContDiff : ContDiff ℝ 1 (fun x : E ↦ inner ℝ a x) := by
    simpa using (innerSL ℝ a).contDiff
  have hcontQuad : ContDiff ℝ 1 (fun x : E ↦ inner ℝ (B x) x) := by
    simpa using ContDiff.inner ℝ B.contDiff contDiff_id
  have hcontSum : ContDiff ℝ 1
      (fun x : E ↦ inner ℝ a x + (1 / 2 : ℝ) • inner ℝ (B x) x) := by
    simpa [Pi.add_apply, add_assoc] using hAffineContDiff.add (hcontQuad.const_smul (1 / 2 : ℝ))
  have hcontDiff0 : ContDiff ℝ 1
      (fun x : E ↦ α + (inner ℝ a x + (1 / 2 : ℝ) • inner ℝ (B x) x)) :=
    contDiff_const.add hcontSum
  have hcontDiff : ContDiff ℝ 1 (quadraticObjective α a A) := by
    convert hcontDiff0 using 1
    funext x
    simp [quadraticObjective, B, add_assoc, smul_eq_mul]
  have hgradLip' : LipschitzWith ‖B‖₊ (fun x : E ↦ B x + a) := by
    simpa [Function.comp] using
      ((IsometryEquiv.vaddConst a).isometry.lipschitz.comp B.lipschitz)
  have hgradLip : LipschitzWith ‖B‖₊ (fun x : E ↦ a + B x) := by
    simpa [add_comm] using hgradLip'
  refine ⟨hcontDiff, ?_⟩
  simpa [B] using (quadraticObjective_gradient_eq α a A hA ▸ hgradLip)

end

/-! ### Proposition_1_5_8 (from Chap01) -/
open scoped Gradient

noncomputable section

/- Proposition 1.5.8 is `source-facing` in first-order smooth optimization.

Source/core/bridge triage:
* source-facing: the specific scalar function `x ↦ √(1 + x²)` belongs to the textbook class
  `C^{1,1}_1(ℝ)`
* core/canonical: the owner predicates `ContDiff ℝ 1 f` and `LipschitzWith 1 (∇ f)` from
  Definition 1.5.2
* bridge/view: on `ℝ`, mathlib's `gradient_eq_deriv'` identifies the gradient with the usual
  derivative, while `lipschitzWith_of_nnnorm_deriv_le` upgrades a derivative bound to the
  canonical `LipschitzWith` owner

Primary domain:
* first-order smooth optimization on the real line

Sampled owner-style declarations:
* `ContDiff.sqrt`
* `gradient_eq_deriv'`
* `lipschitzWith_of_nnnorm_deriv_le`
* `LipschitzWith.norm_sub_le`

Primitive data:
* the concrete function `fun x : ℝ ↦ √(1 + x ^ 2)`

Derived API:
* its `C¹` regularity
* the global `1`-Lipschitz bound for its gradient

No extra local alias is kept here: the owner abstraction already lives in the canonical pair
`ContDiff ℝ 1 f` and `LipschitzWith 1 (∇ f)`, so the theorem is stated directly on the concrete
function. -/

/-- Proposition 1.5.8: the scalar function `x ↦ √(1 + x^2)` on `ℝ` belongs to the class
`C^{1,1}_1(ℝ)`. -/
-- Proof sketch: the function `x ↦ 1 + x^2` is smooth and never vanishes, so
-- `x ↦ √(1 + x^2)` is `C¹`. On `ℝ`, the gradient agrees with the derivative; the derivative is
-- `x / √(1 + x^2)` and the second derivative is `(1 + x^2)^(-3 / 2)`, which is bounded above by
-- `1` on `ℝ`. Hence the gradient is globally `1`-Lipschitz.
private theorem hasDerivAt_sqrt_one_add_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ √(1 + y ^ 2)) (x / √(1 + x ^ 2)) x := by
  have h_inner : HasDerivAt (fun y : ℝ ↦ 1 + y ^ 2) (2 * x) x := by
    simpa [pow_two, two_mul, add_comm, add_left_comm, add_assoc] using
      (((hasDerivAt_id x).pow 2).const_add 1)
  have hx : (1 + x ^ 2) ≠ 0 := by
    nlinarith
  convert h_inner.sqrt hx using 1
  field_simp [hx]

private theorem hasDerivAt_div_sqrt_one_add_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y / √(1 + y ^ 2)) ((√(1 + x ^ 2))⁻¹ ^ (3 : ℕ)) x := by
  have hsqrt := hasDerivAt_sqrt_one_add_sq x
  have hx0 : √(1 + x ^ 2) ≠ 0 := by
    exact (Real.sqrt_ne_zero (show 0 ≤ 1 + x ^ 2 by positivity)).2 (by nlinarith)
  have hdiv := (hasDerivAt_id x).div hsqrt hx0
  convert hdiv using 1
  · field_simp [hx0]
    simp only [id_eq]
    rw [Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)]
    ring

theorem sqrt_one_add_sq_mem_contDiffOne_withLipschitzGradient_one :
    ContDiff ℝ 1 (fun x : ℝ ↦ √(1 + x ^ 2)) ∧
      LipschitzWith 1 (∇ (fun x : ℝ ↦ √(1 + x ^ 2))) := by
  have hcontDiff : ContDiff ℝ 1 (fun x : ℝ ↦ √(1 + x ^ 2)) := by
    have hpoly : ContDiff ℝ 1 (fun x : ℝ ↦ 1 + x ^ 2) := by
      fun_prop
    refine hpoly.sqrt ?_
    intro x
    nlinarith
  have hgrad :
      ∇ (fun x : ℝ ↦ √(1 + x ^ 2)) = fun x : ℝ ↦ x / √(1 + x ^ 2) := by
    funext x
    simpa [gradient_eq_deriv'] using (hasDerivAt_sqrt_one_add_sq x).deriv
  refine ⟨hcontDiff, ?_⟩
  rw [hgrad]
  refine lipschitzWith_of_nnnorm_deriv_le ?_ ?_
  · intro x
    exact (hasDerivAt_div_sqrt_one_add_sq x).differentiableAt
  · intro x
    rw [(hasDerivAt_div_sqrt_one_add_sq x).deriv, nnnorm_pow, nnnorm_inv]
    let s : NNReal := ‖√(1 + x ^ 2)‖₊
    have hsqrt_ge_one : 1 ≤ √(1 + x ^ 2) := by
      rw [Real.one_le_sqrt]
      nlinarith [sq_nonneg x]
    have hs_ge_one : (1 : NNReal) ≤ s := by
      change (1 : ℝ) ≤ ‖√(1 + x ^ 2)‖
      simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hsqrt_ge_one
    have hs_inv_le_one : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs_ge_one
    have hs_inv_nonneg : (0 : NNReal) ≤ s⁻¹ := by
      positivity
    have hpow : s⁻¹ ^ (3 : ℕ) ≤ 1 := pow_le_one₀ hs_inv_nonneg hs_inv_le_one
    simpa [s] using hpow

end

/-! ### Proposition_1_5_9 (from Chap01) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 1.5.9 is source-facing in first-order smooth optimization.

Source/core/bridge triage:
* source-facing: the converse implication from a global quadratic bound on the absolute affine
  first-order remainder with an explicit field `g` to the textbook Lipschitz conclusion
  `LipschitzWith L g`
* core/canonical: the explicit-data affine-model owner `affineModelAt f g x`
* bridge/view: under completeness, `HasGradientAt f (g x) x`, the identity `∇ f = g`, and the
  chapter owner pair `ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f)` from Definition 1.5.2

Primary domain:
* first-order smooth optimization on a real inner-product space, with complete-space companions
  only where the canonical gradient owner `∇ f` is used

Sampled owner-style declarations:
* `affineModelAt` in `FirstOrderTaylorModel`, the explicit-data affine approximation owner
* `ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f)` in `Definition_1_5_2`, the chapter owner for
  `C^{1,1}_L`
* `LipschitzWith L g` and `LipschitzWith.norm_sub_le`
* `HasGradientAt`
* `gradient_eq`

Owner abstraction:
* the explicit-data affine-model owner `affineModelAt f g x`
* under completeness, the canonical gradient specialization `firstOrderTaylorModelAt f x` and the
  Chapter 1 owner pair `ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f)`

Primitive data:
* a Lipschitz constant `L`
* a candidate gradient field `g : E → E`
* the global quadratic remainder estimate against the owner affine model `affineModelAt f g x`

Derived API:
* the source-facing smoothness statement `LipschitzWith L g`
* under completeness, the local gradient statement `HasGradientAt f (g x) x`
* under completeness, the identification `∇ f = g`
* under completeness, the canonical `C^{1,1}_L` owner statement
  `ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f)`

No extra wrapper is introduced here. The main proposition stays on the source-facing field `g`,
and the complete-space companions reuse the chapter owner directly instead of packaging a parallel
`... ∧ LipschitzWith L g` API. -/

variable {L : NNReal} {f : E → ℝ} {g : E → E}
variable (hquad :
  ∀ x y,
    |f y - affineModelAt f g x y| ≤
      (L : ℝ) / 2 * ‖y - x‖ ^ 2)

include hquad

/-- Helper for Proposition 1.5.9: adding the forward and reverse affine-model bounds along the
secant `y - x` yields the source-style pairing estimate
`|⟪g y - g x, y - x⟫| ≤ L ‖y - x‖²`. -/
lemma gradient_secant_inner_bound_of_sub_affineApproximation_norm_sq_bound
    (x y : E) :
    |inner ℝ (g y - g x) (y - x)| ≤ (L : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
  have hxy := hquad x y
  have hyx := hquad y x
  have hxy_lower_raw :
      -((L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ)) ≤
        f y - (f x + inner ℝ (g x) (y - x)) := by
    -- Expand the affine model at `x` before taking the lower half of the absolute-value bound.
    simpa [affineModelAt_apply] using (abs_le.mp hxy).1
  have hxy_lower :
      -((L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ)) ≤
        f y - f x - inner ℝ (g x) (y - x) := by
    -- Reassociate the forward affine-model error into the subtraction form used below.
    linarith
  have hxy_upper_raw :
      f y - (f x + inner ℝ (g x) (y - x)) ≤
        (L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) := by
    -- The upper half of the forward remainder estimate has the same expanded affine model.
    simpa [affineModelAt_apply] using (abs_le.mp hxy).2
  have hxy_upper :
      f y - f x - inner ℝ (g x) (y - x) ≤
        (L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) := by
    -- Reassociate the forward inequality into the same subtraction normal form.
    linarith
  have hyx_lower_raw :
      -((L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ)) ≤
        f x - (f y + inner ℝ (g y) (x - y)) := by
    -- After swapping the endpoints, the secant length is unchanged because `‖x - y‖ = ‖y - x‖`.
    simpa [affineModelAt_apply, norm_sub_rev] using (abs_le.mp hyx).1
  have hyx_lower :
      -((L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ)) ≤
        f x - f y + inner ℝ (g y) (y - x) := by
    -- Replace `x - y` by `-(y - x)` so the reversed affine term matches the forward secant vector.
    have hxyeq : inner ℝ (g y) (x - y) = -inner ℝ (g y) (y - x) := by
      rw [show x - y = -(y - x) by abel_nf, inner_neg_right]
    linarith
  have hyx_upper_raw :
      f x - (f y + inner ℝ (g y) (x - y)) ≤
        (L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) := by
    -- The reversed upper bound has the same normalization of the secant length.
    simpa [affineModelAt_apply, norm_sub_rev] using (abs_le.mp hyx).2
  have hyx_upper :
      f x - f y + inner ℝ (g y) (y - x) ≤
        (L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) := by
    -- Again rewrite the inner product against `x - y` as the negated pairing against `y - x`.
    have hxyeq : inner ℝ (g y) (x - y) = -inner ℝ (g y) (y - x) := by
      rw [show x - y = -(y - x) by abel_nf, inner_neg_right]
    linarith
  have hupper :
      inner ℝ (g y - g x) (y - x) ≤ (L : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
    -- Adding the two upper inequalities cancels the function values and leaves the secant pairing.
    rw [inner_sub_left]
    linarith
  have hlower :
      -((L : ℝ) * ‖y - x‖ ^ (2 : ℕ)) ≤ inner ℝ (g y - g x) (y - x) := by
    -- Adding the two lower inequalities gives the matching lower bound.
    rw [inner_sub_left]
    linarith
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Helper for Proposition 1.5.9: translating both endpoints by `t • u` isolates the first-order
term `t * ⟪g y - g x, u⟫`, and the remaining error is still quadratic in the translation size. -/
lemma translated_endpoint_difference_linearization_error_bound
    (x y u : E) (t : ℝ) :
    |(f (y + t • u) - f (x + t • u)) - (f y - f x) - t * inner ℝ (g y - g x) u| ≤
      (L : ℝ) * ‖t • u‖ ^ (2 : ℕ) := by
  have hy :
      |f (y + t • u) - (f y + t * inner ℝ (g y) u)| ≤
        (L : ℝ) / 2 * ‖t • u‖ ^ (2 : ℕ) := by
    -- Apply the quadratic remainder bound at base point `y` along the translated direction `t • u`.
    simpa [affineModelAt_apply, sub_eq_add_neg, inner_smul_right] using hquad y (y + t • u)
  have hx :
      |f (x + t • u) - (f x + t * inner ℝ (g x) u)| ≤
        (L : ℝ) / 2 * ‖t • u‖ ^ (2 : ℕ) := by
    -- The same expansion at base point `x` gives the matching error term for the second endpoint.
    simpa [affineModelAt_apply, sub_eq_add_neg, inner_smul_right] using hquad x (x + t • u)
  let ry : ℝ := f (y + t • u) - (f y + t * inner ℝ (g y) u)
  let rx : ℝ := f (x + t • u) - (f x + t * inner ℝ (g x) u)
  have hremainder :
      (f (y + t • u) - f (x + t • u)) - (f y - f x) - t * inner ℝ (g y - g x) u =
        ry - rx := by
    -- Group the translated endpoint difference into the two one-point Taylor remainders.
    dsimp [ry, rx]
    rw [inner_sub_left]
    ring_nf
  calc
    |(f (y + t • u) - f (x + t • u)) - (f y - f x) - t * inner ℝ (g y - g x) u|
        = |ry - rx| := by rw [hremainder]
    _ ≤ |ry| + |rx| := by
      simpa [sub_eq_add_neg] using abs_add_le ry (-rx)
    _ ≤ (L : ℝ) / 2 * ‖t • u‖ ^ (2 : ℕ) + ((L : ℝ) / 2 * ‖t • u‖ ^ (2 : ℕ)) := by
      exact add_le_add (by simpa [ry] using hy) (by simpa [rx] using hx)
    _ = (L : ℝ) * ‖t • u‖ ^ (2 : ℕ) := by ring

/-- Helper for Proposition 1.5.9: the translated endpoint difference has derivative
`⟪g y - g x, u⟫` at `t = 0` because the solved remainder is quadratic in `t`. -/
lemma translated_endpoint_difference_hasDerivAt
    (x y u : E) :
    HasDerivAt
      (fun t : ℝ ↦ (f (y + t • u) - f (x + t • u)) - (f y - f x))
      (inner ℝ (g y - g x) u) 0 := by
  let R : ℝ → ℝ :=
    fun t ↦
      (f (y + t • u) - f (x + t • u)) - (f y - f x) - t * inner ℝ (g y - g x) u
  have hBigO : R =O[nhds (0 : ℝ)] fun t ↦ ‖t - 0‖ ^ (2 : ℕ) := by
    refine Asymptotics.IsBigO.of_bound ((L : ℝ) * ‖u‖ ^ (2 : ℕ)) ?_
    filter_upwards with t
    -- Rewrite the quadratic remainder bound into the standard `O(‖t‖²)` normal form.
    have hR :=
      translated_endpoint_difference_linearization_error_bound
        (hquad := hquad) x y u t
    calc
      ‖R t‖ = |(f (y + t • u) - f (x + t • u)) - (f y - f x) - t * inner ℝ (g y - g x) u| := by
        simp [R, Real.norm_eq_abs]
      _ ≤ (L : ℝ) * ‖t • u‖ ^ (2 : ℕ) := hR
      _ = (L : ℝ) * (|t| ^ (2 : ℕ) * ‖u‖ ^ (2 : ℕ)) := by
        rw [norm_smul, Real.norm_eq_abs]
        ring
      _ = (L : ℝ) * ‖u‖ ^ (2 : ℕ) * ‖‖t - 0‖ ^ (2 : ℕ)‖ := by
        simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
  have hR' : HasDerivAt R 0 0 := by
    -- A quadratic remainder has zero derivative at the origin.
    simpa using (hBigO.hasFDerivAt (by norm_num : 1 < 2)).hasDerivAt
  have hlin :
      HasDerivAt
        (fun t : ℝ ↦ t * inner ℝ (g y - g x) u)
        (inner ℝ (g y - g x) u) 0 := by
    -- The linear term contributes exactly the desired pairing coefficient.
    simpa [one_mul] using (hasDerivAt_id 0).mul_const (inner ℝ (g y - g x) u)
  -- Reassemble the translated difference from the quadratic remainder and the linear part.
  convert hR'.add hlin using 1
  · ext t
    simp [R, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    abel_nf
  · ring

/-- Helper for Proposition 1.5.9: a direct decomposition against the affine model at `x` controls
the translated endpoint difference, but it leaves a quadratic tail in `‖y - x‖`. -/
lemma translated_endpoint_difference_bound_with_quadratic_tail
    (x y u : E) (t : ℝ) :
    |(f (y + t • u) - f (x + t • u)) - (f y - f x)| ≤
      (L : ℝ) / 2 * ‖(y - x) + t • u‖ ^ (2 : ℕ) +
        ((L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) + (L : ℝ) / 2 * ‖t • u‖ ^ (2 : ℕ)) := by
  let r₁ : ℝ := f (y + t • u) - affineModelAt f g x (y + t • u)
  let r₂ : ℝ := f y - affineModelAt f g x y
  let r₃ : ℝ := f (x + t • u) - affineModelAt f g x (x + t • u)
  have hr₁ :
      |r₁| ≤ (L : ℝ) / 2 * ‖(y - x) + t • u‖ ^ (2 : ℕ) := by
    -- Evaluate the remainder bound at the translated endpoint `y + t • u`.
    simpa [r₁, affineModelAt_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hquad x (y + t • u)
  have hr₂ : |r₂| ≤ (L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) := by
    -- The same remainder bound at `y` provides the second tail term.
    simpa [r₂] using hquad x y
  have hr₃ : |r₃| ≤ (L : ℝ) / 2 * ‖t • u‖ ^ (2 : ℕ) := by
    -- At `x + t • u`, the affine displacement from `x` is exactly `t • u`.
    simpa [r₃, affineModelAt_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hquad x (x + t • u)
  have hdecomp :
      (f (y + t • u) - f (x + t • u)) - (f y - f x) = r₁ - r₂ - r₃ := by
    -- Isolate the translated difference as the alternating sum of the three affine-model errors.
    dsimp [r₁, r₂, r₃]
    simp [affineModelAt_apply, sub_eq_add_neg, inner_add_right, inner_sub_right,
      add_assoc, add_left_comm, add_comm]
    ring_nf
  calc
    |(f (y + t • u) - f (x + t • u)) - (f y - f x)| = |r₁ - r₂ - r₃| := by rw [hdecomp]
    _ ≤ |r₁| + |r₂| + |r₃| := by
      have htri : |r₁ + (-r₂ + -r₃)| ≤ |r₁| + |-r₂ + -r₃| := abs_add_le _ _
      have htri' : |-r₂ + -r₃| ≤ |r₂| + |r₃| := by
        simpa using (abs_add_le (-r₂) (-r₃))
      have hmid : |r₁| + |-r₂ + -r₃| ≤ |r₁| + (|r₂| + |r₃|) := by
        simpa [add_assoc, add_left_comm, add_comm] using (add_le_add_right htri' |r₁|)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htri.trans hmid
    _ ≤ (L : ℝ) / 2 * ‖(y - x) + t • u‖ ^ (2 : ℕ) +
          ((L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) + (L : ℝ) / 2 * ‖t • u‖ ^ (2 : ℕ)) := by
      linarith [hr₁, hr₂, hr₃]

/-- Helper for Proposition 1.5.9: the centered second difference at `c` is controlled by the same
quadratic modulus because the affine terms at `c` cancel between the two symmetric endpoints. -/
lemma centered_second_difference_bound_of_sub_affineApproximation_norm_sq_bound
    (c v : E) :
    |f (c + v) + f (c - v) - 2 * f c| ≤ (L : ℝ) * ‖v‖ ^ (2 : ℕ) := by
  have hplus :
      |f (c + v) - (f c + inner ℝ (g c) v)| ≤
        (L : ℝ) / 2 * ‖v‖ ^ (2 : ℕ) := by
    -- Apply the affine-model remainder bound at `c` to the forward symmetric endpoint.
    simpa [affineModelAt_apply] using hquad c (c + v)
  have hminus :
      |f (c - v) - (f c + inner ℝ (g c) (-v))| ≤
        (L : ℝ) / 2 * ‖v‖ ^ (2 : ℕ) := by
    -- Apply the same bound at the backward symmetric endpoint.
    simpa [affineModelAt_apply, norm_neg, sub_eq_add_neg] using hquad c (c - v)
  have hplus_lower :
      -((L : ℝ) / 2 * ‖v‖ ^ (2 : ℕ)) ≤
        f (c + v) - f c - inner ℝ (g c) v := by
    -- Rewrite the lower half of the forward absolute-value bound into subtraction form.
    linarith [(abs_le.mp hplus).1]
  have hplus_upper :
      f (c + v) - f c - inner ℝ (g c) v ≤
        (L : ℝ) / 2 * ‖v‖ ^ (2 : ℕ) := by
    -- Rewrite the upper half of the forward absolute-value bound into subtraction form.
    linarith [(abs_le.mp hplus).2]
  have hminus_lower :
      -((L : ℝ) / 2 * ‖v‖ ^ (2 : ℕ)) ≤
        f (c - v) - f c + inner ℝ (g c) v := by
    -- Replace the backward affine term by the negated pairing against `v`.
    have hneg : inner ℝ (g c) (-v) = -inner ℝ (g c) v := by
      rw [inner_neg_right]
    linarith [(abs_le.mp hminus).1]
  have hminus_upper :
      f (c - v) - f c + inner ℝ (g c) v ≤
        (L : ℝ) / 2 * ‖v‖ ^ (2 : ℕ) := by
    -- The same normalization works for the upper half of the backward bound.
    have hneg : inner ℝ (g c) (-v) = -inner ℝ (g c) v := by
      rw [inner_neg_right]
    linarith [(abs_le.mp hminus).2]
  have hupper :
      f (c + v) + f (c - v) - 2 * f c ≤ (L : ℝ) * ‖v‖ ^ (2 : ℕ) := by
    -- Adding the two upper inequalities cancels the affine terms at the center point.
    linarith
  have hlower :
      -((L : ℝ) * ‖v‖ ^ (2 : ℕ)) ≤ f (c + v) + f (c - v) - 2 * f c := by
    -- Adding the two lower inequalities gives the matching lower bound.
    linarith
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Helper for Proposition 1.5.9: rewriting around the midpoint of the four translated endpoints
turns the translated endpoint difference into a difference of centered second differences. -/
lemma translated_endpoint_difference_eq_centered_second_difference_sub
    (x y u : E) (t : ℝ) :
    let d : E := y - x
    let h : E := t • u
    let c : E := x + (1 / 2 : ℝ) • (d + h)
    let a : E := (1 / 2 : ℝ) • (d + h)
    let b : E := (1 / 2 : ℝ) • (d - h)
    ((f (y + h) - f (x + h)) - (f y - f x)) =
      (f (c + a) + f (c - a) - 2 * f c) -
        (f (c + b) + f (c - b) - 2 * f c) := by
  dsimp
  have hca :
      x + (1 / 2 : ℝ) • ((y - x) + t • u) + (1 / 2 : ℝ) • ((y - x) + t • u) = y + t • u := by
    -- The midpoint plus the forward half-displacement reaches the translated endpoint `y + t • u`.
    linear_combination (norm := module)
  have hcmA :
      x + (1 / 2 : ℝ) • ((y - x) + t • u) - (1 / 2 : ℝ) • ((y - x) + t • u) = x := by
    -- The same midpoint minus that half-displacement returns to the original left endpoint.
    linear_combination (norm := module)
  have hcb :
      x + (1 / 2 : ℝ) • ((y - x) + t • u) + (1 / 2 : ℝ) • ((y - x) - t • u) = y := by
    -- Replacing the forward half-step by the complementary one reaches the original right endpoint.
    linear_combination (norm := module)
  have hcmB :
      x + (1 / 2 : ℝ) • ((y - x) + t • u) - (1 / 2 : ℝ) • ((y - x) - t • u) = x + t • u := by
    -- The complementary reflected point is the translated left endpoint `x + t • u`.
    linear_combination (norm := module)
  rw [hca, hcmA, hcb, hcmB]
  ring

omit hquad in
/-- Helper for Proposition 1.5.9: the four-point centered difference can be rewritten exactly as
an alternating sum of three affine-model remainders based at the corner `c + a`. -/
lemma centered_second_difference_eq_corner_remainder_combination
    (c a b : E) :
    (f (c + a) + f (c - a) - 2 * f c) - (f (c + b) + f (c - b) - 2 * f c) =
      (f (c - a) - affineModelAt f g (c + a) (c - a)) -
        (f (c + b) - affineModelAt f g (c + a) (c + b)) -
        (f (c - b) - affineModelAt f g (c + a) (c - b)) := by
  -- Expand the three affine-model errors at the common corner `c + a`.
  simp [affineModelAt_apply, sub_eq_add_neg]
  -- Normalize the scalar algebra so that only the combined affine pairing remains.
  ring_nf
  have hinner :
      -inner ℝ (g (c + a)) (c + -a + (-a + -c)) +
          inner ℝ (g (c + a)) (c + b + (-a + -c)) +
        inner ℝ (g (c + a)) (c + -b + (-a + -c)) = 0 := by
    -- The three displacement vectors sum to zero, so their common affine contribution cancels.
    have hneg :
        -inner ℝ (g (c + a)) (c + -a + (-a + -c)) =
          inner ℝ (g (c + a)) (-(c + -a + (-a + -c))) := by
      rw [inner_neg_right]
    rw [hneg, ← inner_add_right, ← inner_add_right]
    have hsum :
        -(c + -a + (-a + -c)) + (c + b + (-a + -c)) + (c + -b + (-a + -c)) = 0 := by
      abel_nf
    rw [hsum, inner_zero_right]
  -- The remaining equality is the pure four-point identity.
  linarith [hinner]

/-- Helper for Proposition 1.5.9: for a fixed translation `h`, the increment map
`z ↦ f (z + h) - f z` still has a quadratic affine-model remainder, now with candidate field
`z ↦ g (z + h) - g z`. -/
lemma increment_difference_linearization_error_bound
    (x y h : E) :
    |((f (y + h) - f y) - (f (x + h) - f x)) -
        inner ℝ (g (x + h) - g x) (y - x)| ≤
      (L : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
  let A : ℝ := f (y + h) - affineModelAt f g (x + h) (y + h)
  let B : ℝ := f y - affineModelAt f g x y
  have hshift : (y + h) - (x + h) = y - x := by
    abel_nf
  have hA : |A| ≤ (L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) := by
    -- Translate both endpoints by `h`; the secant vector itself does not change.
    simpa [A, affineModelAt_apply, hshift] using hquad (x + h) (y + h)
  have hB : |B| ≤ (L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) := by
    -- The original pair `(x, y)` contributes the matching quadratic remainder.
    simpa [B] using hquad x y
  have hdecomp :
      ((f (y + h) - f y) - (f (x + h) - f x)) -
          inner ℝ (g (x + h) - g x) (y - x) =
        A - B := by
    -- Expand both affine remainders and regroup the function values and pairings.
    dsimp [A, B]
    rw [hshift, inner_sub_left]
    ring
  calc
    |((f (y + h) - f y) - (f (x + h) - f x)) -
        inner ℝ (g (x + h) - g x) (y - x)| = |A - B| := by
          rw [hdecomp]
    _ ≤ |A| + |B| := by
      simpa [sub_eq_add_neg] using abs_add_le A (-B)
    _ ≤ (L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) + ((L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ)) := by
      exact add_le_add hA hB
    _ = (L : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by ring

/-- Helper for Proposition 1.5.9: the centered-second-difference gap is a translated increment
whose linearization is the off-diagonal pairing `⟪g (c + a) - g (c - b), a - b⟫`. -/
lemma centered_second_difference_linearization_error_bound
    (c a b : E) :
    |((f (c + a) + f (c - a) - 2 * f c) - (f (c + b) + f (c - b) - 2 * f c)) -
        inner ℝ (g (c + a) - g (c - b)) (a - b)| ≤
      (L : ℝ) * ‖a - b‖ ^ (2 : ℕ) := by
  have hinc :=
    increment_difference_linearization_error_bound
      (hquad := hquad) (x := c - b) (y := c - a) (h := a + b)
  have hyh : c - a + (a + b) = c + b := by
    abel_nf
  have hxh : c - b + (a + b) = c + a := by
    abel_nf
  have hyx : (c - a) - (c - b) = -(a - b) := by
    abel_nf
  -- Rewrite the translated increment identity into the desired centered-difference form.
  have hinc' :
      |inner ℝ (g (c + a) - g (c - b)) (a - b) -
          ((f (c + a) + f (c - a) - 2 * f c) - (f (c + b) + f (c - b) - 2 * f c))| ≤
        (L : ℝ) * ‖a - b‖ ^ (2 : ℕ) := by
    convert hinc using 1
    · congr 1
      rw [hyh, hxh, hyx, inner_neg_right]
      ring
    · rw [hyx, norm_neg]
  simpa [abs_sub_comm] using hinc'

/-- Helper for Proposition 1.5.9: the difference of two centered second differences should obey
the sharp four-point polarization bound. -/
lemma centered_second_difference_polarization_bound
    (c a b : E) :
    |(f (c + a) + f (c - a) - 2 * f c) - (f (c + b) + f (c - b) - 2 * f c)| ≤
      (L : ℝ) * ‖a + b‖ * ‖a - b‖ := by
  -- Route correction: the previous direct absolute-value attack obscured the finite-difference
  -- cancellation. The proved corner identity reduces the frontier to one sharp signed estimate.
  have hcorner :
      (f (c + a) + f (c - a) - 2 * f c) - (f (c + b) + f (c - b) - 2 * f c) =
        (f (c - a) - affineModelAt f g (c + a) (c - a)) -
          (f (c + b) - affineModelAt f g (c + a) (c + b)) -
          (f (c - b) - affineModelAt f g (c + a) (c - b)) := by
    -- Rewrite the centered difference through the exact corner-based remainder decomposition.
    exact centered_second_difference_eq_corner_remainder_combination
      (f := f) (g := g) c a b
  have hdiag :=
    centered_second_difference_linearization_error_bound
      (hquad := hquad) c a b
  -- TODO: the current signed-corner subplan is structurally wrong. The proved diagonal
  -- linearization `hdiag` shows that the remaining blocker is now exactly the off-diagonal pairing
  -- estimate `|⟪g (c + a) - g (c - b), a - b⟫| ≤ (L : ℝ) * ‖a + b‖ * ‖a - b‖`, which must be
  -- obtained by a genuinely nonnegative mixed-increment argument rather than the false signed
  -- inequality `… ≤ L * inner ℝ (a + b) (a - b)`.
  have _ := hcorner
  have _ := hdiag
  sorry

/-- Helper for Proposition 1.5.9: the midpoint rewrite reduces the translated endpoint difference
to the centered-second-difference polarization bound, which is exactly the sharp mixed estimate
needed for the derivative-at-zero route. -/
lemma translated_endpoint_difference_le_mul_norm_mul
    (x y u : E) (t : ℝ) :
    |(f (y + t • u) - f (x + t • u)) - (f y - f x)| ≤
      (L : ℝ) * ‖y - x‖ * ‖t • u‖ := by
  let d : E := y - x
  let h : E := t • u
  let c : E := x + (1 / 2 : ℝ) • (d + h)
  let a : E := (1 / 2 : ℝ) • (d + h)
  let b : E := (1 / 2 : ℝ) • (d - h)
  have hrewrite :
      ((f (y + h) - f (x + h)) - (f y - f x)) =
        (f (c + a) + f (c - a) - 2 * f c) -
          (f (c + b) + f (c - b) - 2 * f c) := by
    -- Rewrite the translated difference around the midpoint configuration from the new route.
    simpa [d, h, c, a, b] using
      translated_endpoint_difference_eq_centered_second_difference_sub
        (hquad := hquad) (f := f) x y u t
  have hab_sum : a + b = d := by
    -- The midpoint decomposition splits `d` into the sum of the two half-displacements.
    dsimp [a, b]
    linear_combination (norm := module)
  have hab_diff : a - b = h := by
    -- Their difference recovers the translation increment `h`.
    dsimp [a, b]
    linear_combination (norm := module)
  calc
    |(f (y + t • u) - f (x + t • u)) - (f y - f x)|
        = |(f (c + a) + f (c - a) - 2 * f c) -
            (f (c + b) + f (c - b) - 2 * f c)| := by
            rw [show t • u = h by rfl, hrewrite]
    _ ≤ (L : ℝ) * ‖a + b‖ * ‖a - b‖ := by
      -- Invoke the centered-second-difference polarization step at the midpoint configuration.
      exact centered_second_difference_polarization_bound (hquad := hquad) c a b
    _ = (L : ℝ) * ‖y - x‖ * ‖t • u‖ := by
      -- Simplify the midpoint variables back to the original displacement and translation size.
      simp [d, h, hab_sum, hab_diff]

/-- Helper for Proposition 1.5.9: a uniform pairing bound against every test direction implies the
desired norm bound by testing with `u = g y - g x`. -/
lemma norm_sub_le_of_inner_bound
    (x y : E)
    (hinner :
      ∀ u : E, |inner ℝ (g y - g x) u| ≤ (L : ℝ) * ‖y - x‖ * ‖u‖) :
    ‖g y - g x‖ ≤ (L : ℝ) * ‖y - x‖ := by
  let v : E := g y - g x
  have hpair : |inner ℝ v v| ≤ (L : ℝ) * ‖y - x‖ * ‖v‖ := by
    simpa [v] using hinner v
  have hsq : ‖v‖ ^ (2 : ℕ) ≤ (L : ℝ) * ‖y - x‖ * ‖v‖ := by
    -- The upper half of the absolute-value bound gives the quadratic norm inequality.
    simpa [v, real_inner_self_eq_norm_sq] using (abs_le.mp hpair).2
  have hnonneg : 0 ≤ (L : ℝ) * ‖y - x‖ := by
    positivity
  by_cases hv : ‖v‖ = 0
  · -- In the degenerate case the gradient difference vanishes, so the bound is immediate.
    simp [v, hv, hnonneg]
  · -- Otherwise divide the quadratic inequality by the positive norm.
    have hv' : ‖v‖ ≠ 0 := hv
    have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) hv'.symm
    have : ‖v‖ ≤ (L : ℝ) * ‖y - x‖ := by
      nlinarith [hsq]
    simpa [v] using this

/-- Helper for Proposition 1.5.9: a scalar function differentiable at `0` with increment bounded
by `C ‖t‖` near `0` has derivative at `0` bounded in absolute value by `C`. -/
lemma abs_derivAt_zero_le_of_bound
    {φ : ℝ → ℝ} {m C : ℝ}
    (hderiv : HasDerivAt φ m 0)
    (hC : 0 ≤ C)
    (hbound : ∀ t, |φ t - φ 0| ≤ C * ‖t - 0‖) :
    |m| ≤ C := by
  have hlip : ∀ᶠ t in nhds (0 : ℝ), ‖φ t - φ 0‖ ≤ C * ‖t - 0‖ := by
    -- Rewrite the pointwise absolute-value estimate as the norm bound needed by
    -- `HasFDerivAt.le_of_lip'`.
    refine Filter.Eventually.of_forall ?_
    intro t
    simpa [Real.norm_eq_abs] using hbound t
  -- The derivative norm cannot exceed any local Lipschitz constant at the base point.
  have hnorm := hderiv.hasFDerivAt.le_of_lip' hC hlip
  simpa [Real.norm_eq_abs] using hnorm

/-- Helper for Proposition 1.5.9: once the translated endpoint function is shown to be
`L ‖y - x‖ ‖u‖`-Lipschitz in `t`, its derivative at `0` gives the arbitrary-direction pairing
bound. -/
lemma gradient_sub_inner_le_mul_norm_mul
    (x y u : E) :
    |inner ℝ (g y - g x) u| ≤ (L : ℝ) * ‖y - x‖ * ‖u‖ := by
  let φ : ℝ → ℝ := fun t ↦ (f (y + t • u) - f (x + t • u)) - (f y - f x)
  have hderiv :
      HasDerivAt φ (inner ℝ (g y - g x) u) 0 := by
    -- The translated endpoint difference has the desired derivative at the origin.
    simpa [φ] using translated_endpoint_difference_hasDerivAt (hquad := hquad) x y u
  have hC_nonneg : 0 ≤ (L : ℝ) * ‖y - x‖ * ‖u‖ := by
    positivity
  have hbound :
      ∀ t, |φ t - φ 0| ≤ ((L : ℝ) * ‖y - x‖ * ‖u‖) * ‖t - 0‖ := by
    intro t
    -- The sharp mixed-increment estimate gives a linear bound in `‖t‖`.
    simpa [φ, norm_smul, Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using
      translated_endpoint_difference_le_mul_norm_mul (hquad := hquad) x y u t
  -- Apply the general derivative-versus-local-Lipschitz comparison at `t = 0`.
  exact abs_derivAt_zero_le_of_bound (hquad := hquad) hderiv hC_nonneg hbound

/-- Proposition 1.5.9: if the affine-model remainder of `f` with respect to a field `g` is
globally bounded by `(L / 2) ‖y - x‖²`, then `g` is globally `L`-Lipschitz. This statement uses
only the intrinsic field `g`, so it does not assume ambient completeness. -/
theorem lipschitzGradient_of_sub_affineApproximation_norm_sq_bound :
    LipschitzWith L g := by
  -- Route correction: the source proof's secant estimate along `y - x` is not sufficient by
  -- itself to control `‖g y - g x‖`; the missing step is an arbitrary-direction pairing bound.
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  -- Once the arbitrary-direction pairing bound is available, test it against the gradient
  -- difference itself to recover the operator norm estimate.
  simpa [norm_sub_rev] using
    norm_sub_le_of_inner_bound (hquad := hquad) (L := L) (g := g) y x
      (fun u ↦ gradient_sub_inner_le_mul_norm_mul (hquad := hquad) y x u)

section CompleteSpace

variable [CompleteSpace E]

include hquad

/-- Helper for Proposition 1.5.9: the quadratic remainder bound upgrades the affine-model error at
`x` from `O(‖y - x‖²)` to `o(‖y - x‖)`. -/
lemma sub_affineApproximation_isLittleO_of_norm_sq_bound
    (x : E) :
    (fun y ↦ f y - affineModelAt f g x y) =o[nhds x] fun y ↦ ‖y - x‖ := by
  let r : E → ℝ := fun y ↦ f y - affineModelAt f g x y
  -- First record the global quadratic estimate as a local `O(‖y - x‖²)` bound near `x`.
  have hBigO :
      r =O[nhds x] fun y ↦ ‖y - x‖ ^ 2 := by
    refine Asymptotics.IsBigO.of_bound ((L : ℝ) / 2) ?_
    filter_upwards with y
    simpa [r, Real.norm_eq_abs] using hquad x y
  -- A quadratic bound forces zero derivative for the remainder term, which is exactly the desired
  -- little-o statement after simplifying the zero linear part and the vanishing base value.
  have hDeriv0 : HasFDerivAt r (0 : E →L[ℝ] ℝ) x :=
    hBigO.hasFDerivAt (by norm_num : 1 < 2)
  simpa [r] using (hasFDerivAt_iff_isLittleO).mp hDeriv0

/-- The quadratic affine-model remainder bound in Proposition 1.5.9 forces the prescribed field
`g` to be the genuine first-order gradient witness of `f` at every point. -/
theorem hasGradientAt_of_sub_affineApproximation_norm_sq_bound
    (x : E) :
    HasGradientAt f (g x) x := by
  -- Convert the quadratic remainder estimate to the textbook little-o affine-approximation form.
  have hLittle := sub_affineApproximation_isLittleO_of_norm_sq_bound hquad x
  -- The chapter bridge `Definition_1_4_6` then identifies the prescribed field as the gradient.
  simpa [affineModelAt] using
    (hasGradientAt_iff_sub_affineApproximation_isLittleO).mpr hLittle

/-- Helper for Proposition 1.5.9: a pointwise gradient field with a global Lipschitz bound gives a
continuous Fréchet derivative field, hence a `C¹` function. -/
lemma contDiffOne_of_hasGradientAt_and_lipschitzField
    (hgrad : ∀ x, HasGradientAt f (g x) x)
    (hLip : LipschitzWith L g) :
    ContDiff ℝ 1 f := by
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨fun x ↦ (InnerProductSpace.toDual ℝ E) (g x), ?_, ?_⟩
  · -- Transport the Lipschitz field through the Riesz map to obtain a continuous derivative field.
    exact (LinearIsometryEquiv.continuous (InnerProductSpace.toDual ℝ E)).comp hLip.continuous
  · -- Each pointwise gradient witness packages directly as the corresponding Fréchet derivative.
    intro x
    simpa using (hgrad x).hasFDerivAt

/-- The recovered affine-model field from Proposition 1.5.9 agrees with the totalized gradient. -/
theorem gradient_eq_of_sub_affineApproximation_norm_sq_bound :
    ∇ f = g := by
  exact gradient_eq (hasGradientAt_of_sub_affineApproximation_norm_sq_bound hquad)

/-- Complete-space owner strengthening of Proposition 1.5.9: under the same quadratic affine-model
remainder bound, the canonical gradient belongs to the chapter's `C^{1,1}_L` owner class from
Definition 1.5.2. -/
theorem mem_contDiffOne_withLipschitzGradient_of_sub_affineApproximation_norm_sq_bound :
    ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f) := by
  -- Reuse the local affine-approximation bridge to recover the intended gradient field everywhere.
  have hgrad : ∀ x, HasGradientAt f (g x) x :=
    hasGradientAt_of_sub_affineApproximation_norm_sq_bound hquad
  -- The noncomplete-space theorem supplies the global Lipschitz estimate for the prescribed field.
  have hLip : LipschitzWith L g :=
    lipschitzGradient_of_sub_affineApproximation_norm_sq_bound hquad
  refine ⟨contDiffOne_of_hasGradientAt_and_lipschitzField (hquad := hquad) hgrad hLip, ?_⟩
  -- Finally rewrite the canonical totalized gradient to the recovered field `g`.
  simpa [gradient_eq_of_sub_affineApproximation_norm_sq_bound hquad] using hLip

end CompleteSpace

end

/-! ### Proposition_1_5_9 (from Items/Chap01) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 1.5.9 lies in the first-order smooth optimization / Taylor remainder domain.

Primary mathematical domain:
* first-order smooth optimization on a real Hilbert space

Sampled owner-style declarations:
* `HasGradientAt`
* `mem_contDiffOne_withLipschitzGradient_of_sub_affineApproximation_norm_sq_bound` in
  `LecturesConvexOptimization_Nesterov_2018.Chap01.Proposition_1_5_9`
* `LipschitzWith L g`
* `LipschitzWith.norm_sub_le`

Best owner abstraction:
* the pointwise gradient owner `HasGradientAt f (g x) x`

Primitive data:
* a function `f`
* a Lipschitz constant `L`
* a candidate gradient field `g`
* the global quadratic remainder estimate for the affine approximation
  `y ↦ f x + inner ℝ (g x) (y - x)`

Derived API:
* the `C¹` conclusion
* the identity `∇ f = g`
* the gradient-Lipschitz conclusion used in the textbook proposition

Source/core/bridge triage:
* source-facing: the textbook conclusion that the prescribed gradient field is globally
  `L`-Lipschitz
* core/canonical: the pointwise owner `HasGradientAt f (g x) x`
* bridge/view: the `C^{1,1}_L` owner theorem and its Lipschitz projection

This item now recalls the source-facing bridge theorem directly from the owner file instead of
redeclaring a parallel one-line projection. The public statement is now phrased against explicit
affine first-order data rather than the totalized gradient. -/

#check lipschitzGradient_of_sub_affineApproximation_norm_sq_bound

end
