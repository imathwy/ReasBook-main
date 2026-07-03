import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_36 (from Chap02) -/
open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

local notation "p" => normSeminorm ℝ E

/- Primary domain: constrained smooth strongly convex objectives on feasible sets in a real
Hilbert space.

Sampled owner-style declarations:
* `IsStrongConvexSmoothObjective`, `𝓢[μ, L]¹¹`, and `mem_S11_iff` in `Definition_2_17`;
* `ConvexC1SeminormSmoothOn` and `𝓕[L, p]¹¹(Q)` in `Theorem_2_5`;
* mathlib `StrongConvexOn`;
* `StrongConvexOnWith.lower_tangent_quadratic` in `Definition_2_14`.

Best owner abstraction:
* source-facing: the constrained textbook class `𝓢[μ, L]¹¹(Q)`;
* core/canonical: the conjunction
  `0 < μ ∧ μ ≤ L ∧ StrongConvexOn Q μ f ∧
    ConvexC1SeminormSmoothOn (normSeminorm ℝ E) (Real.toNNReal L) Q f`;
* bridge/view: the whole-space owner bridge
  `IsStrongConvexSmoothObjective.toConstrainedStrongConvexSmooth_univ`.

Primitive data:
* the feasible set `Q`;
* the parameters `μ` and `L`;
* the canonical strong-convex owner `StrongConvexOn Q μ f`;
* the canonical smooth owner
  `ConvexC1SeminormSmoothOn (normSeminorm ℝ E) (Real.toNNReal L) Q f`.

Derived API:
* positivity and parameter comparison;
* convexity of `Q`, `C¹` regularity on `Q`, the ambient gradient witnesses on `Q`, and the
  gradient-Lipschitz bound on `Q`;
* the upper and lower tangent quadratic inequalities.

Definition 2.36 therefore uses the chapter's `𝓢[μ, L]¹¹` notation surface directly, specialized
from the whole-space class to the feasible-set class on the same finite-dimensional owner layer as
`ConvexC1SeminormSmoothOn`, instead of introducing a parallel wrapper predicate. -/

/-- The constrained smooth strongly convex class as a set of objectives on `Q`. The source-facing
surface is the notation `𝓢[μ, L]¹¹(Q)`. -/
abbrev S11On (μ L : ℝ) (Q : Set E) : Set (E → ℝ) :=
  setOf (fun f ↦
    0 < μ ∧
      μ ≤ L ∧
      StrongConvexOn Q μ f ∧
      ConvexC1SeminormSmoothOn (normSeminorm ℝ E) (Real.toNNReal L) Q f)

scoped[StrongConvexSmooth] notation "𝓢[" μ ", " L "]¹¹(" Q ")" =>
  S11On μ L Q

/-- The constrained notation `𝓢[μ, L]¹¹(Q)` is the source-facing set view of the canonical
strong-convex/smooth owner data on `Q`. -/
theorem mem_S11On_iff {μ L : ℝ} {Q : Set E} {f : E → ℝ} :
    f ∈ 𝓢[μ, L]¹¹(Q) ↔
      0 < μ ∧
        μ ≤ L ∧
        StrongConvexOn Q μ f ∧
        ConvexC1SeminormSmoothOn (normSeminorm ℝ E) (Real.toNNReal L) Q f :=
  Iff.rfl

namespace StrongConvexSmoothOn

variable {μ L : ℝ} {Q : Set E} {f : E → ℝ}

/-- Membership in `𝓢[μ, L]¹¹(Q)` forces positivity of the strong-convexity parameter. -/
theorem mu_pos (hf : f ∈ 𝓢[μ, L]¹¹(Q)) :
    0 < μ := by
  rcases hf with ⟨hμ, _, _, _⟩
  exact hμ

/-- Membership in `𝓢[μ, L]¹¹(Q)` includes the parameter relation `μ ≤ L`. -/
theorem mu_le_L (hf : f ∈ 𝓢[μ, L]¹¹(Q)) :
    μ ≤ L := by
  rcases hf with ⟨_, hμL, _, _⟩
  exact hμL

/-- Membership in `𝓢[μ, L]¹¹(Q)` includes the reused Chapter 2 smooth owner on `Q`. -/
theorem smooth (hf : f ∈ 𝓢[μ, L]¹¹(Q)) :
    ConvexC1SeminormSmoothOn p (Real.toNNReal L) Q f := by
  rcases hf with ⟨_, _, _, hsmooth⟩
  exact hsmooth

/-- Membership in `𝓢[μ, L]¹¹(Q)` includes `C¹` regularity on `Q`. -/
theorem contDiffOn (hf : f ∈ 𝓢[μ, L]¹¹(Q)) :
    ContDiffOn ℝ 1 f Q := by
  exact (StrongConvexSmoothOn.smooth hf).contDiffOn

/-- Membership in `𝓢[μ, L]¹¹(Q)` includes strong convexity on `Q`. -/
theorem strongConvexOn (hf : f ∈ 𝓢[μ, L]¹¹(Q)) :
    StrongConvexOn Q μ f := by
  rcases hf with ⟨_, _, hstrong, _⟩
  exact hstrong

/-- A function in `𝓢[μ, L]¹¹(Q)` has a convex feasible set `Q`. -/
theorem convex (hf : f ∈ 𝓢[μ, L]¹¹(Q)) :
    Convex ℝ Q := by
  rcases strongConvexOn hf with ⟨hQ_convex, _⟩
  exact hQ_convex

/-- Membership in `𝓢[μ, L]¹¹(Q)` includes the stated ambient-gradient Lipschitz bound on `Q`. -/
theorem gradient_lipschitz
    (hf : f ∈ 𝓢[μ, L]¹¹(Q))
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    ‖∇ f x - ∇ f y‖ ≤ L * ‖x - y‖ := by
  have hL : 0 ≤ L := le_trans (StrongConvexSmoothOn.mu_pos hf).le (StrongConvexSmoothOn.mu_le_L hf)
  simpa [Real.toNNReal_of_nonneg hL, Seminorm.dualNorm_normSeminorm_eq_norm] using
    (StrongConvexSmoothOn.smooth hf).dualNorm_gradient_sub_le hx hy

/-- The original upper tangent-plane inequality on `Q` is a derived consequence of the local
`𝓢[μ, L]¹¹(Q)` owner data. -/
theorem upper_tangent_quadratic
    (hf : f ∈ 𝓢[μ, L]¹¹(Q))
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y ≤ f x + inner ℝ (∇ f x) (y - x) + (L / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  have hL : 0 ≤ L := le_trans (StrongConvexSmoothOn.mu_pos hf).le (StrongConvexSmoothOn.mu_le_L hf)
  have hbound :
      f y - f x - inner ℝ (∇ f x) (y - x) ≤
        ((Real.toNNReal L : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) := by
    simpa using (StrongConvexSmoothOn.smooth hf).tangentErrorBounds.upperBound hx hy
  have hbound' :
      f y - f x - inner ℝ (∇ f x) (y - x) ≤
        (L / 2) * ‖x - y‖ ^ (2 : ℕ) := by
    simpa [Real.toNNReal_of_nonneg hL] using hbound
  have hbound'' :
      f y - f x - inner ℝ (∇ f x) (y - x) ≤
        (L / 2) * ‖y - x‖ ^ (2 : ℕ) := by
    simpa [norm_sub_rev] using hbound'
  linarith

/-- The original lower tangent-plane inequality on `Q` is a derived consequence of the owner
strong-convexity abstraction together with `C¹` regularity. -/
  theorem lower_tangent_quadratic
    (hf : f ∈ 𝓢[μ, L]¹¹(Q))
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y ≥ f x + inner ℝ (∇ f x) (y - x) + (μ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  -- Project the strong-convexity owner from the constrained `𝓢[μ, L]¹¹(Q)` data.
  have hstrong : StrongConvexOn Q μ f := StrongConvexSmoothOn.strongConvexOn hf
  -- The smooth owner supplies the ambient gradient witness needed by the tangent inequality.
  have hgrad : HasGradientAt f (∇ f x) x := (StrongConvexSmoothOn.smooth hf).hasGradientAt hx
  -- Apply the canonical lower tangent theorem at the feasible pair `(x, y)`.
  simpa using
    StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt hstrong hx hy hgrad

end StrongConvexSmoothOn

namespace SetConstrainedMinimizationProblem

variable {μ L : ℝ}

/-- Definition 2.36: a constrained smooth strongly convex minimization problem with parameters `μ`
and `L` is a set-constrained minimization problem on a real Hilbert space whose feasible set is
nonempty and closed and whose objective belongs to `𝓢^{1,1}_{μ,L}(Q)` on that feasible set. -/
structure IsConstrainedStrongConvexSmooth
    (problem : SetConstrainedMinimizationProblem E)
    (μ L : ℝ) : Prop where
  nonempty : problem.feasibleSet.Nonempty
  isClosed : IsClosed problem.feasibleSet
  objective_mem : problem.objective ∈ 𝓢[μ, L]¹¹(problem.feasibleSet)

variable {problem : SetConstrainedMinimizationProblem E}

/-- The feasible set of a constrained smooth strongly convex problem is convex. -/
theorem IsConstrainedStrongConvexSmooth.convex
    (h : problem.IsConstrainedStrongConvexSmooth μ L) :
    Convex ℝ problem.feasibleSet := by
  exact StrongConvexSmoothOn.convex h.objective_mem

/- Definition 2.36 is therefore expressed by a value
`problem : SetConstrainedMinimizationProblem E` together with a proof
`h : problem.IsConstrainedStrongConvexSmooth μ L`.

A global minimizer is expressed directly by the canonical predicate
`IsMinOn problem.objective problem.feasibleSet x`; no additional wrapper declaration is needed
here. -/

end SetConstrainedMinimizationProblem

namespace IsStrongConvexSmoothObjective

variable {μ L : ℝ} {f : E → ℝ}

/-- A whole-space strongly convex smooth objective canonically induces the constrained owner
problem on feasible set `Set.univ` on the finite-dimensional Chapter 2 owner layer. -/
-- Proof sketch: package `f` as the ambient constrained problem on `Set.univ`. The set geometry is
-- immediate, while the objective-side constrained smooth/strongly-convex data come from the
-- whole-space owner hypothesis together with `hf.mu_le_L`.
theorem toConstrainedStrongConvexSmooth_univ [Nontrivial E]
    (hf : IsStrongConvexSmoothObjective μ L f) :
    (SetConstrainedMinimizationProblem.unconstrained f).IsConstrainedStrongConvexSmooth
      μ L := by
  exact
    ⟨Set.univ_nonempty, isClosed_univ,
      ⟨hf.mu_pos, hf.mu_le_L, hf.strongConvexOn, hf.toConvexC1SeminormSmooth.toOn⟩⟩

end IsStrongConvexSmoothObjective

/-! ### Theorem_2_36 (from Chap02) -/
open scoped Gradient ProjectedGradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
The primary domain here is ambient projected-gradient lower bounds over a nonempty closed convex
set in a complete real inner-product space.

Owner declarations sampled for this refinement:
* `IsStrongConvexSmoothObjective` in `Definition_2_17`, which owns the global `C¹`, strong
  convexity, and gradient-Lipschitz hypotheses on `f`;
* `IsStrongConvexSmoothObjective.lower_tangent_quadratic` in `Definition_2_17`, the owner lower
  tangent inequality used at the ambient base point `xBar`;
* `IsStrongConvexSmoothObjective.upper_tangent_quadratic` in `Definition_2_17`, the owner upper
  tangent inequality used at the projected-gradient point;
* `gradientMapping_minimizes_objective` in `Definition_2_35`, the bridge from the source-facing
  projected-gradient point to the minimizing property of the affine-tangent quadratic model.

Best owner abstraction:
* the source-facing objective class notation `f ∈ 𝓢[μ, (L : ℝ)]¹¹`, together with the
  projected-gradient pair `gradientMapping` and `reducedGradient`.

Source/core/bridge triage:
* source-facing: Theorem 2.36 as the textbook lower bound for `x_Q(xBar; γ)` and
  `g_Q(xBar; γ)`;
* core/canonical: `IsStrongConvexSmoothObjective`, `gradientMapping`, and `reducedGradient`;
* bridge/view: `gradientMapping_minimizes_objective`, which identifies `x_Q(xBar; γ)` as the
  minimizer of the affine-tangent quadratic model over `Q`.

Primitive data: the feasible set geometry, the ambient objective owner hypothesis, the base point
`xBar`, the regularization parameter `γ`, and the comparison point `x ∈ Q`.

Derived API: the projected-gradient point `x_Q(xBar; γ)`, the reduced gradient `g_Q(xBar; γ)`,
and the model-minimizing property from `gradientMapping_minimizes_objective`.

This file therefore states Theorem 2.36 on the chapter's source-facing objective notation while
reusing the owner declarations internally, and it adds no parallel `projectedGradient...`
wrappers.
-/

section

variable
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {μ : ℝ} {γ : NNRealˣ} {L : NNReal} {f : E → ℝ}
    (xBar : E)

local notation "xQ" =>
  x_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; γ](xBar)

local notation "gQ" =>
  g_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; γ](xBar)

/-- Theorem 2.36: for a nonempty closed convex set `Q` in a complete real inner-product space, the
canonical projected-gradient
point `gradientMapping ...` and reduced gradient `reducedGradient ...` give the lower bound
`f x ≥ f(x_Q(xBar; γ)) + ⟪g_Q(xBar; γ), x - xBar⟫ + (1 / (2γ)) ‖g_Q(xBar; γ)‖²
+ (μ / 2) ‖x - xBar‖²`
for every `x ∈ Q` whenever `f ∈ 𝓢^{1,1}_{μ,L}` on the ambient space and `γ ≥ L`. This is the
canonical-owner generalization of the textbook `ℝⁿ` statement. The base point `xBar` is ambient:
no hypothesis `xBar ∈ Q` is required. -/
-- Proof sketch: apply `hf.lower_tangent_quadratic xBar x` and compare the affine-tangent model at
-- `x` with its minimum on `Q` given by `gradientMapping_minimizes_objective`, after converting
-- `hf` internally through `mem_S11_iff`. Then use the corresponding upper tangent inequality at
-- `xQ` together with `(L : ℝ) ≤ γ` to compare that model minimum with `f xQ`. The positivity
-- hypothesis needed for `gradientMapping_minimizes_objective` is derived internally from the core
-- owner predicate and `(L : ℝ) ≤ γ` in the nontrivial case.
-- On a subsingleton ambient space the statement is tautological.
-- Finally rewrite the remaining model terms via `gQ = γ • (xBar - xQ)`.
theorem gradientMapping_objective_lower_bound
    (hf : f ∈ 𝓢[μ, (L : ℝ)]¹¹)
    (hγ_ge_L : (L : ℝ) ≤ (γ : ℝ)) (x : E) (hx : x ∈ Q) :
    f x ≥
      f xQ +
        inner ℝ gQ (x - xBar) +
        (1 / (2 * (γ : ℝ))) *
          ‖gQ‖ ^ (2 : ℕ) +
        (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
  let hf' : IsStrongConvexSmoothObjective μ (L : ℝ) f := (mem_S11_iff.mp hf)
  have hγpos : 0 < (γ : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
  have hγne : (γ : ℝ) ≠ 0 := hγpos.ne'
  let hproj :
      IsProjectionPointOn Q (gradientStep f xBar γ) xQ :=
    gradientMapping_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex f γ xBar
  -- First recover the source variational inequality at the projected point.
  have hopt_projection :
      0 ≤ inner ℝ (xQ - gradientStep f xBar γ) (x - xQ) := by
    simpa using hproj.inner_sub_nonneg hQ_convex hx
  have hstep_rewrite :
      xQ - gradientStep f xBar γ = (γ : ℝ)⁻¹ • ((∇ f xBar) - gQ) := by
    rw [gradientStep, reducedGradient]
    simp [smul_sub, smul_smul, hγne]
    abel_nf
  have hopt :
      0 ≤ inner ℝ ((∇ f xBar) - gQ) (x - xQ) := by
    have hscaled :
        0 ≤ (γ : ℝ)⁻¹ * inner ℝ ((∇ f xBar) - gQ) (x - xQ) := by
      simpa [hstep_rewrite, real_inner_smul_left] using hopt_projection
    have hscaled' :
        0 ≤ inner ℝ ((∇ f xBar) - gQ) (x - xQ) * (γ : ℝ)⁻¹ := by
      simpa [mul_comm] using hscaled
    exact nonneg_of_mul_nonneg_left hscaled' (inv_pos.mpr hγpos)
  have hopt' :
      inner ℝ gQ (x - xQ) ≤ inner ℝ (∇ f xBar) (x - xQ) := by
    simpa [inner_sub_left, sub_nonneg] using hopt
  -- Insert the projected point into the affine term and replace the remainder by `gQ`.
  have hlinear :
      f xBar + inner ℝ (∇ f xBar) (x - xBar) ≥
        f xBar + inner ℝ (∇ f xBar) (xQ - xBar) + inner ℝ gQ (x - xQ) := by
    have hdecomp :
        inner ℝ (∇ f xBar) (x - xBar) =
          inner ℝ (∇ f xBar) (xQ - xBar) +
            inner ℝ (∇ f xBar) (x - xQ) := by
      have hxsplit : x - xBar = (xQ - xBar) + (x - xQ) := by
        abel_nf
      rw [hxsplit, inner_add_right]
    rw [hdecomp]
    linarith
  -- Strong convexity gives the lower tangent inequality at the ambient base point.
  have hlower :
      f x ≥
        f xBar + inner ℝ (∇ f xBar) (x - xBar) +
          (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) :=
    hf'.lower_tangent_quadratic xBar x
  have hlower' :
      f x ≥
        f xBar + inner ℝ (∇ f xBar) (xQ - xBar) +
          inner ℝ gQ (x - xQ) +
          (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
    linarith
  -- Smoothness compares the quadratic model at `xQ` with the true value `f xQ`.
  have hupper :
      f xQ ≤
        f xBar + inner ℝ (∇ f xBar) (xQ - xBar) +
          ((L : ℝ) / 2) * ‖xQ - xBar‖ ^ (2 : ℕ) :=
    hf'.upper_tangent_quadratic xBar xQ
  have hmodel :
      f xQ ≤
        f xBar + inner ℝ (∇ f xBar) (xQ - xBar) +
          ((γ : ℝ) / 2) * ‖xQ - xBar‖ ^ (2 : ℕ) := by
    have hsq_nonneg : 0 ≤ ‖xQ - xBar‖ ^ (2 : ℕ) := by
      positivity
    nlinarith
  -- Rewrite the residual correction entirely in terms of the reduced gradient.
  have hxQ_eq :
      xQ = xBar - (γ : ℝ)⁻¹ • gQ := by
    rw [reducedGradient]
    simp [smul_smul, hγne]
  have hxQ_sub :
      xQ - xBar = -((γ : ℝ)⁻¹ • gQ) := by
    rw [hxQ_eq]
    abel_nf
  have hx_sub :
      x - xQ = (x - xBar) + (γ : ℝ)⁻¹ • gQ := by
    rw [hxQ_eq]
    abel_nf
  have hcorrection :
      -((γ : ℝ) / 2) * ‖xQ - xBar‖ ^ (2 : ℕ) + inner ℝ gQ (x - xQ) =
        inner ℝ gQ (x - xBar) +
          (1 / (2 * (γ : ℝ))) * ‖gQ‖ ^ (2 : ℕ) := by
    rw [hxQ_sub, hx_sub]
    rw [norm_neg, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hγpos), mul_pow]
    field_simp [hγne]
    ring
  calc
    f x ≥
        f xBar + inner ℝ (∇ f xBar) (xQ - xBar) +
          inner ℝ gQ (x - xQ) +
          (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := hlower'
    _ ≥
        f xQ - ((γ : ℝ) / 2) * ‖xQ - xBar‖ ^ (2 : ℕ) +
          inner ℝ gQ (x - xQ) +
          (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
        linarith
    _ =
        f xQ +
          (-((γ : ℝ) / 2) * ‖xQ - xBar‖ ^ (2 : ℕ) +
            inner ℝ gQ (x - xQ)) +
          (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
        ring
    _ =
        f xQ +
          (inner ℝ gQ (x - xBar) +
            (1 / (2 * (γ : ℝ))) * ‖gQ‖ ^ (2 : ℕ)) +
          (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
        rw [hcorrection]
    _ =
        f xQ +
          inner ℝ gQ (x - xBar) +
          (1 / (2 * (γ : ℝ))) * ‖gQ‖ ^ (2 : ℕ) +
          (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
        ring

end

end
