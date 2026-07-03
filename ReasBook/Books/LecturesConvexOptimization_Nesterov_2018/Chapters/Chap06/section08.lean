import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_8 (from Chap06) -/
universe u

noncomputable section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 6.8 lies in the composite convex optimization / prox-subproblem domain.

Sampled owner-style declarations:
- `CompositeConvexMinimizationProblem` and `compositeObjective` in `Chap03/Definition_3_21`;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`;
- `ConvexC1On` in `Chap02/Definition_2_4`;
- `IsProxFunction` in `Chap06/Definition_6_31`.

Best owner abstraction:
- source-facing: `CompositeLipschitzGradientModel`;
- core/canonical: `CompositeConvexMinimizationProblem E`;
- bridge/view: the prox-subproblem objective `compositeAuxiliaryObjective`, together with the
  derived `IsProxFunction` witness for the prox term.

Primitive data:
- the ambient composite convex problem, owned by `CompositeConvexMinimizationProblem E`;
- a chosen dual-valued gradient field for the inherited smooth part, with its feasible-set
  derivative and Lipschitz data;
- a differentiable prox-function together with its canonical ambient-norm prox-function owner;
- attainment of the auxiliary prox subproblems.

Derived API:
- closedness/convexity of the feasible set and the closed-convex nonsmooth owner, inherited from
  `CompositeConvexMinimizationProblem`;
- the full extended-valued composite objective, reused directly from the inherited Chapter 3
  owner instead of a second local `objective` wrapper;
- the prox-function owner `IsProxFunction`, stored directly in its ambient-norm specialization
  instead of keeping a parallel raw `StrongConvexOn` field. -/

/-- The auxiliary objective of the prox subproblem on the feasible set `Q`, with linear term `s`,
prox weight `α`, and regularizer weight `β`. -/
def compositeAuxiliaryObjective
    (Q : Set E) (s : StrongDual ℝ E) (α β : NNReal) (d : E → ℝ) (Ψ : E → WithTop ℝ) :
    Q → WithTop ℝ :=
  _root_.compositeObjective
    (fun x : Q ↦ s x + (α : ℝ) * d x)
    (fun x : Q ↦ ((β : ℝ) : WithTop ℝ) * Ψ x)

/-- Evaluating the auxiliary objective gives the linear term plus prox penalty plus weighted
extended-valued regularizer. -/
-- Proof sketch: unfold `compositeAuxiliaryObjective`.
@[simp] theorem compositeAuxiliaryObjective_apply
    (Q : Set E) (s : StrongDual ℝ E) (α β : NNReal) (d : E → ℝ) (Ψ : E → WithTop ℝ)
    (x : Q) :
    compositeAuxiliaryObjective Q s α β d Ψ x =
      (((s x + (α : ℝ) * d x : ℝ) : WithTop ℝ) + ((β : ℝ) : WithTop ℝ) * Ψ x) :=
  rfl

/-- Definition 6.8: a composite convex optimization model with Lipschitz gradient consists of an
ambient composite convex problem from Definition 3.21, a chosen dual-valued gradient field for
its inherited smooth part with `L`-Lipschitz control on the feasible set, and a differentiable
`1`-strongly convex prox-function whose auxiliary subproblems admit minimizers. -/
structure CompositeLipschitzGradientModel (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    extends CompositeConvexMinimizationProblem E where
  /-- The chosen gradient map `∇f : E → E*`. -/
  smoothGradient : E → StrongDual ℝ E
  /-- The chosen gradient represents the derivative of the inherited smooth part at every
  feasible point. -/
  smoothPart_hasGradientWithinAt :
    ∀ ⦃x : E⦄, x ∈ feasibleSet →
      HasFDerivWithinAt objective (smoothGradient x) feasibleSet x
  /-- The Lipschitz constant for the gradient. -/
  L : NNReal
  /-- The gradient is `L`-Lipschitz on `Q` in the dual norm. -/
  smoothGradient_lipschitz :
    LipschitzOnWith L smoothGradient feasibleSet
  /-- The prox-function `d : E → ℝ`. -/
  proxFunction : E → ℝ
  /-- The prox-function is differentiable on `Q`. -/
  proxFunction_differentiable : DifferentiableOn ℝ proxFunction feasibleSet
  /-- The prox-function is a canonical ambient-norm prox-function on `Q`. -/
  proxFunction_isProxFunction : IsProxFunction (normSeminorm ℝ E) feasibleSet proxFunction
  /-- Every auxiliary prox subproblem with nonnegative weights admits a minimizer on `Q`. -/
  auxiliaryProblem_tractable :
    ∀ s : StrongDual ℝ E, ∀ α β : NNReal,
      ∃ x : feasibleSet, IsMinOn
        (compositeAuxiliaryObjective feasibleSet s α β proxFunction nonsmoothPart) Set.univ x

namespace CompositeLipschitzGradientModel

/-- A Definition 6.8 model can be evaluated as the inherited Chapter 3 composite objective. -/
instance : CoeFun (CompositeLipschitzGradientModel E) (fun _ ↦ E → WithTop ℝ) where
  coe model := model.toCompositeConvexMinimizationProblem

/-- Evaluating a Definition 6.8 model uses the inherited Chapter 3 composite objective. -/
@[simp] theorem coe_apply (model : CompositeLipschitzGradientModel E) (x : E) :
    model x = (model.objective x : WithTop ℝ) + model.nonsmoothPart x :=
  rfl

/-- The model's auxiliary prox subproblem objective on `Q` for parameters `s`, `α`, and `β`. -/
def auxiliaryObjective
    (model : CompositeLipschitzGradientModel E) (s : StrongDual ℝ E) (α β : NNReal) :
    model.feasibleSet → WithTop ℝ :=
  _root_.compositeAuxiliaryObjective
    model.feasibleSet s α β model.proxFunction model.nonsmoothPart

/-- Evaluating the model auxiliary objective gives the textbook affine-plus-prox-plus-regularizer
formula. -/
@[simp] theorem auxiliaryObjective_apply
    (model : CompositeLipschitzGradientModel E) (s : StrongDual ℝ E) (α β : NNReal)
    (x : model.feasibleSet) :
    model.auxiliaryObjective s α β x =
      (((s x + (α : ℝ) * model.proxFunction x : ℝ) : WithTop ℝ) +
        ((β : ℝ) : WithTop ℝ) * model.nonsmoothPart x) :=
  rfl

end CompositeLipschitzGradientModel

end

/-! ### Lemma_6_8 (from Chap06) -/
noncomputable section

open scoped Gradient

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]

/- Lemma 6.8 lies in the Chapter 6 smoothed dual / excessive-gap domain.

Sampled owner-style declarations:
- `smoothed_pair_excessive_gap_of_linearized_prox_minimizers` in `Chap06/Lemma_6_2_3`, the
  existing Chapter 6 owner theorem for the linearized prox-model excessive-gap inequality;
- `IsSmoothedDualMinimizerSelection` in `Chap06/Definition_6_33`, the chapter owner for the
  primal prox-point selection surface, showing that the relevant primitive data are the selected
  minimizers rather than an auxiliary wrapper;
- `satisfiesExcessiveGapCondition` in `Chap06/Definition_6_34`, the source-facing excessive-gap
  owner whose scalar inequality is the conclusion proved here;
- mathlib `IsMinOn`, the canonical minimizer owner used by the upstream Chapter 6 theorem.

Best owner abstraction:
- core/canonical: `smoothed_pair_excessive_gap_of_linearized_prox_minimizers`;
- bridge/view: the present ambient-point spelling, which differs from the owner only by replacing
  the shifted linear term `⟪g, x - x₀⟫` with the equivalent affine model `⟪g, x⟫`.

Primitive data:
- the feasible set `Q₁`, the smoothed primal objective `fμ₂`, the prox term `d₁`, and the points
  `x₀`, `xBar`, `uBar`, and `xμ₁uBar`;
- the convexity and gradient hypotheses at `x₀`;
- the two minimizer hypotheses for the `Lfμ₂`- and `μ₁`-weighted prox models;
- the identity expressing `φμ₁ uBar`.

Derived API:
- the excessive-gap inequality `fμ₂ xBar ≤ φμ₁ uBar`.

Source/core/bridge triage:
- source-facing: the textbook ambient-point statement at the chosen pair `(xBar, uBar)`;
- core/canonical: `smoothed_pair_excessive_gap_of_linearized_prox_minimizers`;
- bridge/view: removing the additive constant `⟪∇ fμ₂(x₀), x₀⟫` from the linearized model.

The owner theorem in `Lemma_6_2_3` now already uses the actual dual point and the actual prox
point, so the only remaining bridge work in this file is the affine-vs-shifted linearization
rewrite. This refinement keeps the source-facing ambient spelling and routes the proof through the
existing owner theorem without any auxiliary selector wrappers.
-/

-- Proof sketch: subtract the constant `⟪∇ fμ₂(x₀), x₀⟫` from the affine linearized model to
-- recover the shifted owner model `x ↦ ⟪∇ fμ₂(x₀), x - x₀⟫ + L₁(fμ₂) d₁(x)`, then specialize the
-- Chapter 6 owner theorem `smoothed_pair_excessive_gap_of_linearized_prox_minimizers` to the
-- single dual point `uBar` and the single selected primal prox point `xμ₁uBar`.
/-- Lemma 6.8: let `x₀ ∈ Q₁`, let `xBar ∈ Q₁` minimize the affine linearized prox model
`x ↦ ⟪∇ f_{μ₂}(x₀), x⟫ + L₁(f_{μ₂}) d₁(x)`, and let `xμ₁uBar ∈ Q₁` be the selected primal prox
point attached to `uBar`. If `φ_{μ₁}(uBar)` is given by the standard excessive-gap identity and
`μ₁ ≥ L₁(f_{μ₂})`, then the smoothed excessive-gap inequality
`f_{μ₂}(xBar) ≤ φ_{μ₁}(uBar)` holds. -/
theorem smoothed_pair_satisfies_excessive_gap_of_linearized_prox_minimizers
    {Q₁ : Set E₁} {fμ₂ : E₁ → ℝ} {φμ₁ : E₂ → ℝ} {d₁ : E₁ → ℝ}
    {x₀ xBar xμ₁uBar : Q₁} {uBar : E₂} {μ₁ Lfμ₂ : ℝ}
    (hconv : ConvexOn ℝ Q₁ fμ₂)
    (hfμ₂_grad :
      HasGradientWithinAt fμ₂ (gradientWithin fμ₂ Q₁ x₀) Q₁ x₀)
    (hbar_min :
      IsMinOn
        (fun x ↦ inner ℝ (gradientWithin fμ₂ Q₁ x₀) x + Lfμ₂ * d₁ x)
        Q₁
        xBar)
    (hxμ₁_min :
      IsMinOn
        (fun x ↦ inner ℝ (gradientWithin fμ₂ Q₁ x₀) x + μ₁ * d₁ x)
        Q₁
        xμ₁uBar)
    (hφμ₁ :
      φμ₁ uBar =
        fμ₂ x₀ + μ₁ * (d₁ x₀ - d₁ xμ₁uBar))
    (hμ₁ : Lfμ₂ ≤ μ₁) :
    fμ₂ xBar ≤ φμ₁ uBar := by
  have hbar_min' :
      IsMinOn
        (fun x ↦ inner ℝ (gradientWithin fμ₂ Q₁ x₀) (x - x₀) + Lfμ₂ * d₁ x)
        Q₁
        xBar := by
    simpa [sub_eq_add_neg, inner_add_right, inner_neg_right, add_assoc, add_left_comm, add_comm]
      using
        hbar_min.add (isMinOn_const : IsMinOn
          (fun _ : E₁ ↦ -inner ℝ (gradientWithin fμ₂ Q₁ x₀) x₀) Q₁ xBar)
  simpa using
    (smoothed_pair_excessive_gap_of_linearized_prox_minimizers
      hconv
      hfμ₂_grad
      hbar_min'
      hxμ₁_min
      hφμ₁
      hμ₁)

end

/-! ### Proposition_6_8 (from Chap06) -/
universe u

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

-- Proof sketch: the estimate `‖v k - xStar‖² ≤ 2 * D` gives a uniform closed ball centered
-- at `xStar` containing every `v k`. Since each `x k` and `y k` lies in the convex hull of the
-- finite prefix `v 0, ..., v k`, convexity of that closed ball implies the same uniform bound for
-- `x k` and `y k`. Therefore the union of the three ranges is bounded.
/-- Core owner form: if `v` has bounded range and each `x_k` and `y_k` lies in the convex hull of
the finite prefix `v_0, ..., v_k`, then the union of the three ranges is bounded. -/
theorem bounded_union_of_prefix_convex_hull_sequences_of_isBounded
    (v x y : ℕ → E)
    (hx : ∀ k, x k ∈ convexHull ℝ (Set.range (fun i : Fin (k + 1) ↦ v i)))
    (hy : ∀ k, y k ∈ convexHull ℝ (Set.range (fun i : Fin (k + 1) ↦ v i)))
    (hv : Bornology.IsBounded (Set.range v)) :
    Bornology.IsBounded (Set.range v ∪ Set.range x ∪ Set.range y) := sorry

/-- The pointwise squared-distance estimate `‖v_k - xStar‖² ≤ 2 D` places the full range of `v`
in a common closed ball, hence `Set.range v` is bounded. -/
theorem isBounded_range_of_sqDist_le
    (xStar : E) (D : ℝ) (v : ℕ → E)
    (hv : ∀ k, ‖v k - xStar‖ ^ 2 ≤ 2 * D) :
    Bornology.IsBounded (Set.range v) := sorry

/-- Proposition 6.8: if each `x_k` and `y_k` lies in the convex hull of the finite prefix
`v_0, ..., v_k` and the points `v_k` satisfy `‖v_k - xStar‖² ≤ 2 D` for all `k ≥ 0`, then
the three sequences are bounded, equivalently the union of their ranges is bounded. Here `D`
is the scalar value corresponding to the source quantity `d(xStar)`. -/
theorem bounded_union_of_prefix_convex_hull_sequences
    (xStar : E) (D : ℝ) (v x y : ℕ → E)
    (hx : ∀ k, x k ∈ convexHull ℝ (Set.range (fun i : Fin (k + 1) ↦ v i)))
    (hy : ∀ k, y k ∈ convexHull ℝ (Set.range (fun i : Fin (k + 1) ↦ v i)))
    (hv : ∀ k, ‖v k - xStar‖ ^ 2 ≤ 2 * D) :
    Bornology.IsBounded (Set.range v ∪ Set.range x ∪ Set.range y) := sorry

/-! ### Theorem_6_8 (from Chap06) -/
universe u v

section

variable {X : Type u} {U : Type v}
  {f : X → ℝ} {φ : U → ℝ}
  {fμ₂ : ℝ → X → ℝ}
  {barx : ℕ → X} {baru : ℕ → U}
  {L2phi D2 : ℝ}

/- This item lies in the chapter's excessive-gap / smoothing-rate domain.

Sampled owner-style declarations:
- `scheme_6_2_37_primal_dual_gap_le_rate` in `Chap06/Theorem_6_2_4`, the canonical Chapter 6
  theorem with the same gap-rate conclusion;
- `primal_dual_gap_bound_of_smoothed_lower_approximation` in `Chap06/Lemma_6_12`, the chapter
  bridge from a lower smoothing estimate and a smoothed residual gap bound to a raw primal-dual
  gap estimate;
- `satisfiesExcessiveGapCondition` in `Chap06/Theorem_6_4`, the source-facing excessive-gap owner
  behind the stagewise inequality used to derive this rate.

Best owner abstraction:
- source-facing: the explicit rate estimate for the raw primal-dual gap along scheme `(6.2.37)`;
- core/canonical: the Chapter 6 primal-dual gap rate theorem;
- bridge/view: none is needed in the statement itself, since the item is already the direct
  source-facing rate claim.

Primitive data:
- the lower smoothing estimate `f x - μ₂ D₂ ≤ f_{μ₂}(x)`;
- the stagewise inequality
  `f_{μ₂,k}(\bar x_k) ≤ φ(\bar u_k)` with
  `μ₂,k = 4 L₂(φ) / ((k + 1) (k + 2))`.

Derived API:
- the explicit rate
  `f(\bar x_k) - φ(\bar u_k) ≤ 4 L₂(φ) D₂ / ((k + 1) (k + 2))`.

The upstream Chapter 6 file currently packages the same statement through a dependency chain that
is failing earlier in the build, so this item file keeps the statement directly as a theorem
skeleton instead of using a `recall`.
-/

-- Proof sketch: specialize the lower smoothing estimate at
-- `μ₂ = 4 L₂(φ) / ((k + 1) (k + 2))` and `x = \bar x_k`, combine it with the stagewise scheme
-- inequality `f_{μ₂,k}(\bar x_k) ≤ φ(\bar u_k)`, and rearrange.
/-- Theorem 6.8: if scheme `(6.2.37)` yields
`f_{μ₂,k}(\bar x_k) ≤ φ(\bar u_k)` with
`μ₂,k = 4 L₂(φ) / ((k + 1) (k + 2))`, and if the smoothing family satisfies
`f(x) - μ₂ D₂ ≤ f_{μ₂}(x)` for every `μ₂` and `x`, then
`f(\bar x_k) - φ(\bar u_k) ≤ 4 L₂(φ) D₂ / ((k + 1) (k + 2))` for every integer `k ≥ 0`. -/
theorem primal_dual_gap_le_scheme_6_2_37_rate
    (happrox : ∀ μ₂ x, f x - μ₂ * D2 ≤ fμ₂ μ₂ x)
    (hscheme :
      ∀ k : ℕ,
        fμ₂ ((4 * L2phi) / (((k : ℝ) + 1) * ((k : ℝ) + 2))) (barx k) ≤ φ (baru k))
    (k : ℕ) :
    f (barx k) - φ (baru k) ≤
      (4 * L2phi * D2) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := sorry

end
