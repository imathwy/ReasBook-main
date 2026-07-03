import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_4_4_2 (from Chap04) -/
noncomputable section

open SmoothNonlinearEquationProblem
open scoped InnerProduct LevelSetNotation Manifold MinimalSingularValue

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
variable [CompleteSpace E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
variable [CompleteSpace E₂]

/- Theorem 4.4.2 lies in the local modified Gauss--Newton / nondegenerate-solution domain.

Sampled owner-style declarations:
* `ModifiedGaussNewtonMethod` in `Algorithm_4_4_1`, the chapter owner for the iterate dynamics
  and accepted trial points;
* `jacobian_lipschitz_taylor_remainder_le` in `Proposition_4_4_5`, the chapter owner for the
  quadratic first-order Taylor remainder on a convex set;
* `SmoothNonlinearEquationProblem.solutionSet` in `Definition_4_4_8`, the chapter owner for the
  exact-solution locus `problem x = 0`;
* mathlib `LipschitzOnWith L (fun x ↦ fderiv ℝ problem x) 𝓕`, the canonical on-set
  Jacobian-Lipschitz owner;
* `minimalSingularValue` / `σ_min(_)` in `Definition_4_4_5`, the chapter owner for the dual
  nondegeneracy quantity;
* the complete-inner-product-space ambient layer already used by `Assumption_4_4_3`,
  `Theorem_4_4_3`, `Theorem_4_4_4`, and `Theorem_4_4_5`.

Best owner abstraction:
* source-facing: the local quadratic contraction of the modified Gauss--Newton iteration near a
  nondegenerate exact solution;
* core/canonical: a convex neighborhood `𝓕` carrying the on-set Jacobian-Lipschitz bound,
  together with the exact-solution owner `xStar ∈ solutionSet problem` and the dual
  nondegeneracy owner at `xStar`;
* bridge/view: containment of the initial sublevel set `𝓛[f]((f x0))` in `𝓕`, which places the
  iterate orbit and the exact solution inside the convex Lipschitz domain needed by the Taylor
  bound.

Primitive data:
* the method `method`;
* the exact solution point `xStar ∈ solutionSet problem`;
* the convex set `𝓕` containing `𝓛[f]((f x0))`;
* the Jacobian-Lipschitz owner on `𝓕`.

Derived API:
* the one-step sublevel-set invariance and quadratic contraction estimate.

The earlier statement put the Jacobian-Lipschitz hypothesis only on the initial sublevel set
`𝓛[f]((f x0))`. That is too weak for the chapter Taylor-remainder owner, whose segment argument
needs a convex set containing the whole segment between the relevant points. This refinement keeps
the source-facing contraction theorem but upgrades its smoothness hypothesis to the correct convex
ambient domain and uses sublevel containment only as the bridge back to the iterate orbit.
The exact-solution input is also refined to the chapter owner `solutionSet problem` instead of the
raw equation `problem xStar = 0`, matching the nearby Chapter 4 theorem surfaces.
A finite-dimensional ambient hypothesis is not part of the theorem's mathematical content: the
public surface only uses the smooth-map owner, on-set Jacobian Lipschitz control, and the adjoint
minimal-singular-value nondegeneracy condition, so the file lives on the same complete
inner-product-space layer as the neighboring Chapter 4 owners.
-/

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯

section

variable {problem : SmoothMap}
variable {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
variable {L0 : ℝ} {L : NNReal} {γφ : ℝ} {x0 xStar : E₁}

local notation "f" => meritFunctionReformulation problem φ
local notation "𝓛0" => (𝓛[f]((f x0)) : Set E₁)

-- Proof sketch: `mem_solutionSet_iff.mp hxStar` and the merit-function axioms imply
-- `f xStar = 0 ≤ f x0`, so
-- `xStar ∈ 𝓛0 ⊆ 𝓕`. Proposition 4.4.7 gives `f (method (k + 1)) ≤ f (method k) ≤ f x0`, so the
-- current and next iterates stay in `𝓛0 ⊆ 𝓕` without a separate feasibility hypothesis. Since
-- `𝓕` is convex, the segment joining `method k` to `xStar` lies in the Lipschitz domain, so
-- Proposition 4.4.5 controls the first-order Taylor remainder there. Combine that remainder bound
-- with the sharp lower bound with constant `γφ` and the dual nondegeneracy owner
-- `0 < σ_min((F'(x*))†)` to solve for `‖x_{k+1} - x*‖`.
/-- Theorem 4.4.2: if `x* ∈ solutionSet problem`, if the Jacobian at `x*` is nondegenerate in the
dual sense `0 < σ_min((F'(x*))†)`, if `γφ` is the sharpness constant from Definition 4.4.9, and
if the Jacobian is `L`-Lipschitz on a convex set `𝓕` containing the initial sublevel set
`𝓛[f]((f x₀))`, then every sufficiently close modified Gauss--Newton iterate satisfies the local
quadratic error estimate from `(4.4.20)` and the next iterate `x_{k+1}` remains in
`𝓛[f]((f x₀))`. -/
theorem local_contraction_near_nondegenerate_solution
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    {𝓕 : Set E₁} {k : ℕ}
    (h𝓕 : Convex ℝ 𝓕)
    (h𝓛0_subset : 𝓛0 ⊆ 𝓕)
    (hxStar : xStar ∈ solutionSet problem)
    (hσ_pos : 0 < σ_min((fderiv ℝ problem xStar)†))
    (hγφ_mem : γφ ∈ Set.Ioc (0 : ℝ) 1)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (hclose :
      ‖method k - xStar‖ ≤
        (2 / (L : ℝ)) * (σ_min((fderiv ℝ problem xStar)†) * γφ / (3 + 5 * γφ))) :
    (method (k + 1) ∈ 𝓛0 ∧
      ‖method (k + 1) - xStar‖ ≤
        (3 * (1 + γφ) * (L : ℝ) * ‖method k - xStar‖ ^ (2 : ℕ)) /
          (2 * γφ *
            (σ_min((fderiv ℝ problem xStar)†) -
              (L : ℝ) * ‖method k - xStar‖))) := by
  sorry

-- Proof sketch: starting from the smallness assumption on `‖x_k - x*‖`, rearrange the scalar
-- inequality exactly as in the textbook estimate to show that the fraction appearing in
-- `(4.4.20)` is bounded above by `‖x_k - x*‖`.
/-- If `γφ ∈ (0, 1]` and the current error satisfies the smallness condition from
Theorem 4.4.2, then the explicit quadratic error bound from `(4.4.20)` is itself at most the
current error `‖x_k - x*‖`. -/
theorem local_contraction_bound_le_current_error
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    {k : ℕ}
    (hγφ_mem : γφ ∈ Set.Ioc (0 : ℝ) 1)
    (hclose :
      ‖method k - xStar‖ ≤
        (2 / (L : ℝ)) * (σ_min((fderiv ℝ problem xStar)†) * γφ / (3 + 5 * γφ))) :
    ((3 * (1 + γφ) * (L : ℝ) * ‖method k - xStar‖ ^ (2 : ℕ)) /
        (2 * γφ *
          (σ_min((fderiv ℝ problem xStar)†) -
            (L : ℝ) * ‖method k - xStar‖)) ≤
      ‖method k - xStar‖) := by
  sorry

end

/-! ### Assumption_4_4_3 (from Chap04) -/
noncomputable section

universe u v

open scoped InnerProduct LevelSetNotation Manifold MinimalSingularValue

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯

/- Assumption 4.4.3 lies in the modified Gauss--Newton / sublevel-set nondegeneracy domain.

Sampled owner-style declarations:
* the bundled smooth-map owner `C^⊤⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯` from `Definition_4_4_8`
* `meritFunctionReformulation problem φ` in `Definition_4_4_10`, the chapter owner for the
  scalarized modified Gauss--Newton objective
* `𝓛[f](a)` together with `mem_levelSet_iff` in `Definition_4_1_1`, the chapter owner for
  initial sublevel sets
* `minimalSingularValue` with notation `σ_min(A)` in `Definition_4_4_5`, the chapter owner for
  least singular values

Best owner abstraction:
* source-facing: `HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x₀ σ`
* core/canonical: a bundled smooth residual map `problem : SmoothMap`, positivity of `σ`, and a
  lower bound for `σ_min((fderiv ℝ problem x)†)` on the canonical initial merit sublevel set
  `𝓛[meritFunctionReformulation problem φ]((meritFunctionReformulation problem φ x₀))`
* bridge/view: `meritFunctionReformulation_apply` and `mem_levelSet_iff` for the textbook
  inequality `φ (problem x) ≤ φ (problem x₀)`

Primitive data:
* the smooth residual map `problem`
* the merit function `φ`
* the base point `x₀`
* the constant `σ`

Derived API:
* positivity of `σ` and the pointwise lower bound, obtained directly by conjunction projections
  from the source-facing owner predicate

There is no upstream owner for the full uniform-on-sublevel conjunction, so the source-facing
predicate stays. The duplicate wheels were the unbundled residual-map parameter and the inline
merit/sublevel encoding. This file now reuses the chapter owner `SmoothMap` for the nonlinear
system and the owner `meritFunctionReformulation problem φ` for the scalarized objective, while
keeping the Euclidean textbook case as a specialization of this inner-product-space statement.
-/

/-- Assumption 4.4.3: for a smooth nonlinear equation problem `problem`, the Jacobian operators
`problem'(x)` have a uniform dual nondegeneracy on the initial merit sublevel set
`𝓛[meritFunctionReformulation problem φ]((meritFunctionReformulation problem φ x₀))`, meaning
that a single constant `σ > 0` satisfies `σ ≤ σ_min(problem'(x)*)` for every `x` in that set. -/
def HasUniformDualNondegeneracyOnInitialSublevelSet
    (problem : SmoothMap) (φ : F → ℝ) (x0 : E) (σ : ℝ) : Prop :=
  let f := meritFunctionReformulation problem φ
  0 < σ ∧
    ∀ ⦃x : E⦄, x ∈ (𝓛[f]((f x0)) : Set E) → σ ≤ σ_min((fderiv ℝ problem x)†)

namespace HasUniformDualNondegeneracyOnInitialSublevelSet

variable {problem : SmoothMap} {φ : F → ℝ} {x0 x : E} {σ : ℝ}

local notation "f" => meritFunctionReformulation problem φ

/-- Uniform dual nondegeneracy on the initial sublevel set forces the constant `σ` to be
strictly positive. -/
theorem sigma_pos
    (_hσ :
      HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ) :
    0 < σ :=
  _hσ.1

/-- Uniform dual nondegeneracy on the initial sublevel set yields the pointwise lower bound
`σ ≤ σ_min(problem'(x)*)` at every point of the initial merit sublevel set. -/
theorem lower_bound
    (_hσ :
      HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (_hx : x ∈ (𝓛[f]((f x0)) : Set E)) :
    σ ≤ σ_min((fderiv ℝ problem x)†) :=
  _hσ.2 _hx

end HasUniformDualNondegeneracyOnInitialSublevelSet

/-! ### Definition_4_4_3 (from Chap04) -/
open Module

universe u v w

/- Definition 4.4.3 lies in the algebraic-duality domain for linear maps and their dual
transposes.

Sampled owner-style declarations:
- mathlib `Module.Dual`
- mathlib `Module.Dual.transpose`
- mathlib `LinearMap.dualMap`
- mathlib `LinearMap.dualMap_apply`

Best owner abstraction:
- core/canonical: `LinearMap.dualMap`

Primitive data:
- a commutative semiring `R`
- `R`-modules `E₁` and `E₂`
- a linear map `A : E₁ →ₗ[R] E₂`

Derived API:
- the induced dual map `A.dualMap : Dual R E₂ →ₗ[R] Dual R E₁`
- its pointwise evaluation formula `LinearMap.dualMap_apply`

Source/core/bridge triage:
- source-facing: the textbook adjoint-on-dual-spaces construction `A* : E₂* → E₁*`
- core/canonical: `LinearMap.dualMap`
- bridge/view: the textbook reading of `A.dualMap` as the adjoint on dual spaces

The previous local alias `adjointOnDualSpaces` and its companion theorem were exact-interface
duplicates of mathlib owners. This file therefore recalls the canonical declarations directly
instead of keeping a parallel chapter-local wrapper. -/

variable {R : Type u} {E₁ : Type v} {E₂ : Type w}
variable [CommSemiring R] [AddCommMonoid E₁] [Module R E₁]
variable [AddCommMonoid E₂] [Module R E₂]

/- Definition 4.4.3: for a linear operator `A : E₁ → E₂`, the adjoint operator on dual spaces is
exactly the canonical dual map `A.dualMap : E₂⋆ → E₁⋆`. -/
recall LinearMap.dualMap
    (A : E₁ →ₗ[R] E₂) :
    Dual R E₂ →ₗ[R] Dual R E₁

/- Evaluating the canonical dual map gives the defining pairing identity. -/
recall LinearMap.dualMap_apply
    (A : E₁ →ₗ[R] E₂) (φ : Dual R E₂) (x : E₁) :
    A.dualMap φ x = φ (A x)

/-! ### Lemma_4_4_3 (from Chap04) -/
noncomputable section

open scoped LocalModelNotation Manifold
open scoped ModifiedGaussNewtonLocalModelNotation
open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯

section

variable (problem : SmoothMap) (φ : E₂ → ℝ) [IsSharpMeritFunction φ]

local notation "f" => meritFunctionReformulation problem φ
local notation "ψ" => ψ[problem; φ; (fderiv ℝ problem)]

/-- The modified Gauss--Newton local model is finite on every closed trust-region ball, so the
source-facing local-model decrease `Δ_r(x)` is defined at every point. -/
theorem modifiedGaussNewtonLocalModel_mem_finiteDomain
    (problem : SmoothMap) (φ : E₂ → ℝ) [IsSharpMeritFunction φ]
    (r : NNReal) (x : E₁) :
    x ∈ localModelFiniteDomain (ψ[problem; φ; (fderiv ℝ problem)]) r :=
  mem_localModelFiniteDomain_of_bddBelow (ψ[problem; φ; (fderiv ℝ problem)]) r x
    (bddBelow_image_closedBall_of_nonneg (ψ[problem; φ; (fderiv ℝ problem)]) r
      (fun x y ↦
        show 0 ≤ φ (problem x + fderiv ℝ problem x (y - x)) from
          IsMeritFunction.nonneg _)
      x)

/-- The scalar cutoff function `χ` from the quadratic-regularization lower bound, given by
`χ(t) = t - 1 / 2` for `t ≥ 1` and `χ(t) = t² / 2` for `t < 1`. -/
def modifiedGaussNewtonQuadraticChi (t : ℝ) : ℝ :=
  if 1 ≤ t then t - 1 / 2 else (1 / 2 : ℝ) * t ^ (2 : ℕ)

namespace ModifiedGaussNewtonQuadraticChiNotation

scoped notation:max "χ" => modifiedGaussNewtonQuadraticChi

end ModifiedGaussNewtonQuadraticChiNotation

open scoped ModifiedGaussNewtonQuadraticChiNotation

-- Proof sketch: unfold `modifiedGaussNewtonQuadraticChi` and use the branch condition `t < 1`
-- to select the quadratic branch of the `if`.
/-- Below the threshold `t = 1`, the cutoff function `χ` is equal to `t² / 2`. -/
theorem modifiedGaussNewtonQuadraticChi_of_lt_one {t : ℝ} (ht : t < 1) :
    χ t = (1 / 2 : ℝ) * t ^ (2 : ℕ) := by
  simp [modifiedGaussNewtonQuadraticChi, if_neg (not_le_of_gt ht)]

-- Proof sketch: unfold `modifiedGaussNewtonQuadraticChi` and use the branch condition `1 ≤ t`
-- to select the affine branch of the `if`.
/-- Above the threshold `t = 1`, the cutoff function `χ` is equal to `t - 1 / 2`. -/
theorem modifiedGaussNewtonQuadraticChi_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    χ t = t - 1 / 2 := by
  simp [modifiedGaussNewtonQuadraticChi, if_pos ht]

/-- The modified Gauss--Newton specialization of the canonical local-model decrease `Δ_r(x)`,
obtained by supplying the finite-domain proof coming from the nonnegativity of the sharp merit
function on each closed trust-region ball. The source-facing notation is
`Δ[problem; φ; r](x)`. -/
abbrev modifiedGaussNewtonLocalDecrease
    (problem : SmoothMap) (φ : E₂ → ℝ) [IsSharpMeritFunction φ]
    (r : NNReal) (x : E₁) : ℝ :=
  localModelDecreaseAt
    (meritFunctionReformulation problem φ)
    (ψ[problem; φ; (fderiv ℝ problem)])
    r x
    (modifiedGaussNewtonLocalModel_mem_finiteDomain problem φ r x)

namespace ModifiedGaussNewtonLocalDecreaseNotation

/- Source-facing Lean notation for the textbook modified Gauss--Newton local decrease `Δ_r(x)`. -/
scoped notation:max "Δ[" problem:arg "; " φ:arg "; " r:arg "](" x:arg ")" =>
  modifiedGaussNewtonLocalDecrease problem φ r x

end ModifiedGaussNewtonLocalDecreaseNotation

open scoped ModifiedGaussNewtonLocalDecreaseNotation

-- Proof sketch: compare the quadratic-regularized model value at the minimizer `step x` with the
-- one-dimensional path `y = x + τ (y₀ - x)` for a point `y₀` in the radius-`r` ball that nearly
-- attains the local-model infimum; convexity of the sharp merit function gives
-- `ψ(x; x + τ (y₀ - x)) ≤ f(x) - τ Δ_r(x)`, and maximizing the resulting scalar quadratic over
-- `τ ∈ [0, 1]` yields the factor `M r² χ(Δ_r(x) / (M r²))`.
/-- Lemma 4.4.3: for a smooth nonlinear equation problem `problem`, a sharp merit function `φ`,
and a modified Gauss--Newton step with positive regularization parameter `M`, the model gap
`δ_M(x)` is bounded below by `M r² χ(Δ_r(x) / (M r²))` for every `x` and every radius `r`. -/
theorem modifiedGaussNewton_modelGap_ge_localModelDecrease_chi
    (M : ℝ)
    (hM : 0 < M)
    (step :
      ModifiedGaussNewtonStep
        ψ
        Set.univ M)
    (x : E₁) (r : NNReal) :
    δ[step; f](x) ≥
      M * (r : ℝ) ^ (2 : ℕ) *
        χ (Δ[problem; φ; r](x) /
          (M * (r : ℝ) ^ (2 : ℕ))) := sorry

-- Proof sketch: write the right-hand side as a scalar function of `M > 0`, split into the
-- regimes `Δ_r(x) / (M r²) ≥ 1` and `Δ_r(x) / (M r²) < 1`, and check directly in each branch
-- that increasing `M` decreases the value.
/-- For fixed `problem`, `φ`, `x`, and radius `r`, the right-hand side of the lower
bound in `modifiedGaussNewton_modelGap_ge_localModelDecrease_chi` is decreasing as a function of
the regularization parameter `M > 0`. -/
theorem modifiedGaussNewton_lowerBound_rhs_antitoneOn
    (x : E₁) (r : NNReal) :
    AntitoneOn
      (fun M : ℝ ↦
        M * (r : ℝ) ^ (2 : ℕ) *
          χ (Δ[problem; φ; r](x) /
            (M * (r : ℝ) ^ (2 : ℕ))))
      (Set.Ioi (0 : ℝ)) := sorry

end

/-! ### Proposition_4_4_3 (from Chap04) -/
noncomputable section

open scoped MinimalSingularValue

universe u₀ u₁ u₂ u₃

/-
Proposition 4.4.3 lies in the chapter's continuous-linear-operator / minimal-singular-value
domain.

Sampled owner-style declarations:
- `minimalSingularValue` and `minimalSingularValue_def` in `Definition_4_4_5`, the source-facing
  owner for `σ_min`
- `minimalSingularValue_eq_zero` in `Definition_4_4_5`, the owner-level degenerate-domain API
- `ContinuousLinearMap.minimalSingularValue_mul_norm_le` in `Proposition_4_4_1`, the canonical
  lower-bound API derived from that owner
- mathlib `ContinuousLinearMap.opNorm_comp_le`, the ambient operator-composition comparison pattern

Best owner abstraction:
- source-facing/core: `minimalSingularValue` with its derived lower-bound theorem
  `ContinuousLinearMap.minimalSingularValue_mul_norm_le`

Primitive data:
- continuous linear maps `A₁ : E₁ →L[𝕜] E₂` and `A₂ : E₀ →L[𝕜] E₁`

Derived API:
- the supermultiplicative lower bound for `σ_min(A₁.comp A₂)`

Source/core/bridge triage:
- source-facing: the textbook supermultiplicativity statement for the minimal singular value
- core/canonical: `minimalSingularValue` and
  `ContinuousLinearMap.minimalSingularValue_mul_norm_le`
- bridge/view: `minimalSingularValue_eq_zero` for the degenerate-domain boundary case

This file therefore reuses the chapter owner theorem from Proposition 4.4.1 directly, in the same
normed-space `σ_min` regime as Definition 4.4.5. -/

variable {𝕜 : Type u₃} {E₀ : Type u₀} {E₁ : Type u₁} {E₂ : Type u₂}
  [NormedField 𝕜]
  [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

-- Proof sketch: apply Proposition 4.4.1 first to `A₂ x`, obtaining
-- `‖A₁ (A₂ x)‖ ≥ σ_min(A₁) * ‖A₂ x‖`, and then again to `A₂` to bound
-- `‖A₂ x‖` from below by `σ_min(A₂) * ‖x‖`. Dividing by `‖x‖` for each nonzero `x` gives the
-- lower bound for `σ_min(A₁.comp A₂)`.
namespace ContinuousLinearMap

/-- Proposition 4.4.3: the minimal singular value is supermultiplicative under composition,
so `σ_min(A₁.comp A₂)` is at least `σ_min(A₁) * σ_min(A₂)`. -/
theorem minimalSingularValue_comp_ge_mul
    (A₁ : E₁ →L[𝕜] E₂) (A₂ : E₀ →L[𝕜] E₁) :
    σ_min(A₁.comp A₂) ≥ σ_min(A₁) * σ_min(A₂) := by
  by_cases hE₀ : Subsingleton E₀
  · letI := hE₀
    rw [minimalSingularValue_eq_zero (A₁.comp A₂), minimalSingularValue_eq_zero A₂]
    simp
  · letI : Nontrivial E₀ := not_subsingleton_iff_nontrivial.mp hE₀
    rw [minimalSingularValue_def]
    refine le_csInf ?_ ?_
    · obtain ⟨x, hx⟩ := exists_ne (0 : E₀)
      exact Set.range_nonempty_iff_nonempty.mpr ⟨⟨x, hx⟩⟩
    · rintro _ ⟨x, rfl⟩
      have hxnorm : 0 < ‖x.1‖ := norm_pos_iff.mpr x.2
      have hA₂ : σ_min(A₂) * ‖x.1‖ ≤ ‖A₂ x.1‖ := by
        simpa using A₂.minimalSingularValue_mul_norm_le x.1
      have hA₁ : σ_min(A₁) * ‖A₂ x.1‖ ≤ ‖A₁ (A₂ x.1)‖ := by
        simpa using A₁.minimalSingularValue_mul_norm_le (A₂ x.1)
      have hmul : (σ_min(A₁) * σ_min(A₂)) * ‖x.1‖ ≤ ‖A₁ (A₂ x.1)‖ := by
        calc
          (σ_min(A₁) * σ_min(A₂)) * ‖x.1‖ = σ_min(A₁) * (σ_min(A₂) * ‖x.1‖) := by
            ring
          _ ≤ σ_min(A₁) * ‖A₂ x.1‖ := by
            exact mul_le_mul_of_nonneg_left hA₂ (minimalSingularValue_nonneg A₁)
          _ ≤ ‖A₁ (A₂ x.1)‖ := hA₁
      exact (le_div_iff₀ hxnorm).2 <| by
        simpa using hmul

end ContinuousLinearMap

/-! ### Theorem_4_4_3 (from Chap04) -/
noncomputable section

open scoped InnerProduct Manifold
open scoped LevelSetNotation

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯

/- Theorem 4.4.3 lies in the modified Gauss--Newton / merit-threshold decrease domain.

Sampled owner-style declarations:
* `ModifiedGaussNewtonMethod` in `Algorithm_4_4_1`, the chapter owner for the iterate dynamics;
* `jacobian_lipschitz_taylor_remainder_le` in `Proposition_4_4_5`, the chapter owner for the
  first-order Taylor remainder bound on a convex Lipschitz domain;
* `abs_meritFunctionReformulation_sub_modifiedGaussNewtonLocalModel_le` in `Lemma_4_4_1`, the
  chapter owner for the merit/model discrepancy on that same convex domain;
* mathlib `LipschitzOnWith L (fderiv ℝ problem) 𝓕`, the canonical Jacobian-Lipschitz owner on a
  feasible set;
* `𝓛[f]((f x0)) ⊆ 𝓕`, the chapter's canonical initial-sublevel containment bridge already used in
  nearby Chapter 4 theorem surfaces;
* `HasUniformDualNondegeneracyOnInitialSublevelSet` in `Assumption_4_4_3`, the source-facing
  owner for the uniform dual nondegeneracy assumption.

Best owner abstraction:
* source-facing: the textbook one-step decrease and quadratic-decay estimates in the large-value
  and small-value regimes;
* core/canonical: a bundled smooth map `problem`, a sharp merit function `φ`, a modified
  Gauss--Newton method `method`, a convex feasible domain `𝓕`, the canonical sublevel-containment
  bridge `𝓛[f]((f x0)) ⊆ 𝓕`, the chapter dual-nondegeneracy owner, and the Jacobian-Lipschitz
  owner on `problem`;
* bridge/view: an explicit sharpness witness `γφ` for the merit function, because the displayed
  thresholds and decay constants depend on that particular witness, together with the convex-domain
  Taylor/model comparison supplied by Proposition 4.4.5 and Lemma 4.4.1.

Primitive data:
* the smooth map `problem`;
* the sharp merit function `φ`;
* the method `method`;
* the convex feasible domain `𝓕`;
* the Jacobian-Lipschitz hypothesis `LipschitzOnWith L (fderiv ℝ problem) 𝓕`;
* the sublevel containment bridge `𝓛[f]((f x0)) ⊆ 𝓕`;
* the threshold parameter `γφ`.

Derived API:
* convex feasible-domain geometry `Convex ℝ 𝓕`;
* positivity of `σ` and the initial-sublevel lower bound, bundled in
  `HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ`.

The earlier file put Theorem 4.4.3 on the scalar smoothness owner
`HasLipschitzDerivativeOnWith L 𝓕 (meritFunctionReformulation problem φ)`. That shifts the
mathematical content away from the Gauss--Newton residual map `problem`, while the chapter
comparison lemmas actually used here are stated on the Jacobian-Lipschitz owner
`LipschitzOnWith L (fderiv ℝ problem) 𝓕` over a convex domain. This refinement keeps the same
source-facing decrease theorems, but moves their smoothness hypothesis onto that canonical owner
and leaves the scalar merit reformulation as derived API rather than as the primitive smoothness
input.
-/

section

variable {problem : SmoothMap}
variable {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
variable {𝓕 : Set E₁}
variable {L0 : ℝ} {L : NNReal} {σ γφ : ℝ} {x0 : E₁}

local notation "f" => meritFunctionReformulation problem φ
local notation "𝓛0" => (𝓛[f]((f x0)) : Set E₁)

/-- The merit-value threshold `(σ² / (2L)) γ_φ²` separating the large-value and quadratic-decay
regimes in Theorem 4.4.3. -/
def modifiedGaussNewtonQuadraticMeritThreshold
    (σ γφ : ℝ) (L : NNReal) : ℝ :=
  ((σ ^ (2 : ℕ)) / (2 * (L : ℝ))) * γφ ^ (2 : ℕ)

-- Proof sketch: use monotonicity of the merit values along Algorithm 4.4.1 to keep `x_k` inside
-- the initial sublevel set, apply the uniform dual nondegeneracy assumption there, and invoke
-- Lemma 4.4.6 to obtain a correction `h_k*` with `‖h_k*‖ ≤ f(x_k) / (σ γφ)`. Evaluating the
-- quadratic-regularized local model along the segment `t ↦ t h_k*` and using the upper bound
-- `M_k ≤ 2L` yields a one-variable quadratic majorant; when
-- `f(x_k) ≥ (σ² / (2L)) γφ²`, its minimizer gives the decrease estimate `(4.4.23)`.
/-- Theorem 4.4.3 (1): under Assumptions 4.4.1, 4.4.2, and 4.4.3, if a modified Gauss--Newton
iterate satisfies `f(x_k) ≥ (σ² / (2L)) γ_φ²`, then the next merit value decreases by at least
`(σ² / (4L)) γ_φ²`. On the theorem surface, the only part of Assumption 4.4.2 used here is the
sublevel containment `𝓛[f]((f x₀)) ⊆ 𝓕`. -/
theorem modifiedGaussNewton_large_value_oneStep_decrease
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (h𝓛0_subset : 𝓛0 ⊆ 𝓕)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    (k : ℕ)
    (hk :
      modifiedGaussNewtonQuadraticMeritThreshold σ γφ L ≤
        f (method k)) :
    f (method (k + 1)) ≤
      f (method k) - ((σ ^ (2 : ℕ)) / (4 * (L : ℝ))) * γφ ^ (2 : ℕ) := sorry

-- Proof sketch: follow the same comparison with the one-dimensional model along `t h_k*`. In the
-- regime `f(x_k) < (σ² / (2L)) γφ²`, the scalar majorant is minimized at `t = 1`, which yields
-- the quadratic estimate `(4.4.24)`.
/-- Theorem 4.4.3 (2): under the same hypotheses, if
`f(x_k) < (σ² / (2L)) γ_φ²`, then
`f(x_{k+1}) ≤ (L / (σ² γ_φ²)) f(x_k)^2`. -/
theorem modifiedGaussNewton_small_value_quadratic_decay
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (h𝓛0_subset : 𝓛0 ⊆ 𝓕)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    (k : ℕ)
    (hk :
      f (method k) <
        modifiedGaussNewtonQuadraticMeritThreshold σ γφ L) :
    f (method (k + 1)) ≤
      ((L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * (f (method k)) ^ (2 : ℕ) := sorry

-- Proof sketch: combine the threshold hypothesis
-- `f(x_k) < (σ² / (2L)) γφ²` with elementary scalar algebra to bound the quadratic factor from
-- Theorem 4.4.3 (2) by `1 / 2`.
/-- Under the small-value hypothesis from Theorem 4.4.3 (2), the quadratic upper bound is at most
half of the current merit value. -/
theorem modifiedGaussNewton_small_value_quadratic_decay_le_half_current
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (k : ℕ)
    (hk :
      f (method k) <
        modifiedGaussNewtonQuadraticMeritThreshold σ γφ L) :
    ((L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * (f (method k)) ^ (2 : ℕ) ≤
      (1 / 2 : ℝ) * f (method k) := sorry

-- Proof sketch: repeat the argument from the first part, but use the fixed-parameter hypothesis
-- `M_k = L`. The same one-dimensional majorant now has quadratic coefficient `L / 2`, so when
-- `f(x_k) ≥ (σ² / L) γφ²` its minimizer yields the sharper linear decrease `(4.4.25)`.
/-- Theorem 4.4.3 (3): if Algorithm 4.4.1 is run with the fixed regularization rule `M_k ≡ L`
and `f(x_k) ≥ (σ² / L) γ_φ²`, then
`f(x_{k+1}) ≤ f(x_k) - (σ² / (2L)) γ_φ²`. As above, the feasible-set input is only the
sublevel containment `𝓛[f]((f x₀)) ⊆ 𝓕`. -/
theorem modifiedGaussNewton_fixed_regularization_large_value_oneStep_decrease
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (h𝓛0_subset : 𝓛0 ⊆ 𝓕)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    (hregularization : ∀ k : ℕ, method.regularization k = (L : ℝ))
    (k : ℕ)
    (hk :
      ((σ ^ (2 : ℕ)) / (L : ℝ)) * γφ ^ (2 : ℕ) ≤
        f (method k)) :
    f (method (k + 1)) ≤
      f (method k) - ((σ ^ (2 : ℕ)) / (2 * (L : ℝ))) * γφ ^ (2 : ℕ) := sorry

-- Proof sketch: in the fixed-parameter case `M_k = L`, the scalar majorant from the textbook
-- proof is minimized at `t = 1` whenever `f(x_k) < (σ² / L) γφ²`. This gives the quadratic bound
-- in `(4.4.26)`.
/-- Theorem 4.4.3 (4): if Algorithm 4.4.1 is run with `M_k ≡ L` and
`f(x_k) < (σ² / L) γ_φ²`, then
`f(x_{k+1}) ≤ (L / (2 σ² γ_φ²)) f(x_k)^2`, again using only the sublevel containment
`𝓛[f]((f x₀)) ⊆ 𝓕` from Assumption 4.4.2. -/
theorem modifiedGaussNewton_fixed_regularization_small_value_quadratic_decay
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (h𝓛0_subset : 𝓛0 ⊆ 𝓕)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    (hregularization : ∀ k : ℕ, method.regularization k = (L : ℝ))
    (k : ℕ)
    (hk :
      f (method k) <
        ((σ ^ (2 : ℕ)) / (L : ℝ)) * γφ ^ (2 : ℕ)) :
    f (method (k + 1)) ≤
      ((L : ℝ) / (2 * σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * (f (method k)) ^ (2 : ℕ) := sorry

-- Proof sketch: the stronger threshold `f(x_k) < (σ² / L) γφ²` implies by scalar algebra that
-- the quadratic upper bound from Theorem 4.4.3 (4) is bounded by one half of `f(x_k)`.
/-- In the fixed-regularization small-value regime, the quadratic upper bound from
`modifiedGaussNewton_fixed_regularization_small_value_quadratic_decay` is at most half of the
current merit value. -/
theorem modifiedGaussNewton_fixed_regularization_small_value_quadratic_decay_le_half_current
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (k : ℕ)
    (hk :
      f (method k) <
        ((σ ^ (2 : ℕ)) / (L : ℝ)) * γφ ^ (2 : ℕ)) :
    ((L : ℝ) / (2 * σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * (f (method k)) ^ (2 : ℕ) ≤
      (1 / 2 : ℝ) * f (method k) := sorry

end

/-! ### Definition_4_4_4 (from Chap04) -/
noncomputable section

open Metric

universe u

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]

/- Domain review for this item: the dual norm already lives on the canonical owner
`StrongDual ℝ E₁`, so the main entry should recall that existing norm rather than introduce a
new wrapper.

Layer targeted by this refinement:
- source-facing recall of the canonical norm owner on `StrongDual ℝ E₁`, plus the textbook
  support-function bridge

Sampled owner-style declarations:
- mathlib `StrongDual`
- mathlib `ContinuousLinearMap.sSup_unitClosedBall_eq_norm`
- mathlib `ContinuousLinearMap.le_opNorm_of_le`
- project `Seminorm.dualNorm_normSeminorm_eq_norm` in `Chap02/Lemma_2_3`
- project `LinearMap.BilinForm.dualNorm_eq_sSup_primalUnitBall_strongDual` in
  `Chap04/Definition_4_2_6`

Best owner abstraction:
- core/canonical: the existing norm `‖·‖ : StrongDual ℝ E₁ → ℝ`

Primitive data:
- a continuous linear functional `s : StrongDual ℝ E₁`

Derived API:
- mathlib's absolute-value support formula
  `ContinuousLinearMap.sSup_unitClosedBall_eq_norm`
- the source-facing support-function formula on the symmetric closed unit ball, obtained by
  removing the absolute value using symmetry of the ball

Source/core/bridge triage:
- source-facing: the textbook dual-norm formula `sup_{‖x‖≤1} s x`
- core/canonical: the norm on `StrongDual ℝ E₁`
- bridge/view: passing from `sup_{‖x‖≤1} ‖s x‖` to `sup_{‖x‖≤1} s x` by replacing `x` with `-x`
  when needed
-/

/- Definition 4.4.4: the dual norm on `E₁⋆` is exactly the existing norm on the continuous dual
`StrongDual ℝ E₁`. -/
#check (‖·‖ : StrongDual ℝ E₁ → ℝ)

-- Proof sketch: start from the operator-norm formula
-- `ContinuousLinearMap.sSup_unitClosedBall_eq_norm`, then use the symmetry of the closed unit
-- ball to replace `|s x|` by `s x`; in finite dimensions the resulting supremum is a maximum.
/-- Companion bridge for Definition 4.4.4: the canonical norm on the continuous dual is the
supremum of the evaluation pairing over the closed unit ball of `E₁`; in finite dimensions this
supremum is the textbook maximum. -/
theorem dual_norm_eq_sSup_closedUnitBall (s : StrongDual ℝ E₁) :
    ‖s‖ = sSup (s '' closedBall (0 : E₁) 1) := by
  let S : Set ℝ := s '' closedBall (0 : E₁) 1
  let T : Set ℝ := (fun x : E₁ ↦ ‖s x‖) '' closedBall (0 : E₁) 1
  have hS_nonempty : S.Nonempty := ⟨0, ⟨0, by simp, by simp⟩⟩
  have hS_bound : ∀ y ∈ S, y ≤ ‖s‖ := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx_norm : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hsx : |s x| ≤ ‖s‖ * ‖x‖ := by
      simpa [Real.norm_eq_abs] using s.le_opNorm x
    calc
      s x ≤ |s x| := le_abs_self _
      _ ≤ ‖s‖ * ‖x‖ := hsx
      _ ≤ ‖s‖ * 1 := mul_le_mul_of_nonneg_left hx_norm (norm_nonneg _)
      _ = ‖s‖ := by ring
  have hS_bdd : BddAbove S := ⟨‖s‖, hS_bound⟩
  have hT_nonempty : T.Nonempty := ⟨0, ⟨0, by simp, by simp⟩⟩
  have hT_subset : T ⊆ S := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    by_cases hsx : 0 ≤ s x
    · exact ⟨x, hx, by simp [abs_of_nonneg hsx]⟩
    · refine ⟨-x, by simpa [Metric.mem_closedBall, dist_eq_norm] using hx, ?_⟩
      simp [abs_of_neg (lt_of_not_ge hsx)]
  have hsSup_T_le : sSup T ≤ sSup S := by
    refine csSup_le hT_nonempty ?_
    intro y hy
    exact le_csSup hS_bdd (hT_subset hy)
  have hT_eq : sSup T = ‖s‖ := by
    simpa [T, Real.norm_eq_abs] using ContinuousLinearMap.sSup_unitClosedBall_eq_norm s
  have hsSup_S_le : sSup S ≤ ‖s‖ := csSup_le hS_nonempty hS_bound
  have hnorm_le : ‖s‖ ≤ sSup S := by
    rw [← hT_eq]
    exact hsSup_T_le
  have hS_eq : sSup S = ‖s‖ := le_antisymm hsSup_S_le hnorm_le
  simpa [S] using hS_eq.symm

end

/-! ### Lemma_4_4_4 (from Chap04) -/
noncomputable section

open Set
open scoped LevelSetNotation
open scoped ModifiedGaussNewtonLocalModelNotation

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

section

variable {F : E₁ → E₂} {φ : E₂ → ℝ} {J : E₁ → E₁ →L[ℝ] E₂}

local notation "f" => meritFunctionReformulation F φ

-- Proof sketch: argue by contradiction. If `step x` left the level set, then because the whole
-- level set `𝓛(f(x))` lies in `interior 𝓕`, the segment from `x` to `step x` would meet the
-- boundary of `𝓕`. At that boundary point, use the quadratic upper-model estimate together with
-- convexity of the local-model slice `ψ[F; φ; J](x; ·)` to compare the true objective with the
-- modified Gauss--Newton model. The inequality `L ≤ M` and the basic model-gap estimate from
-- Lemma 4.4.2 then force a contradiction.
/-- Lemma 4.4.4: if the local-model slice `ψ[F; φ; J](x; ·)` is convex, the textbook level set
`𝓛(f(x))` of the continuous merit reformulation is contained in `interior 𝓕`, and
`M ≥ L ≥ 0`, then the modified Gauss--Newton iterate `V_M(x)` belongs to the same level set. -/
theorem modifiedGaussNewton_step_mem_levelSet_of_levelSet_subset_interior
    {𝓕 : Set E₁} {L : NNReal} {M : ℝ}
    (step : ModifiedGaussNewtonStep (ψ[F; φ; J]) 𝓕 M)
    (x : 𝓕)
    (hcont : Continuous f)
    (hconv : ConvexOn ℝ Set.univ (ψ[F; φ; J] x))
    (hupper :
      ∀ ⦃y : E₁⦄, y ∈ 𝓕 →
        f y ≤
          quadraticallyRegularizedObjective
            (ψ[F; φ; J] x)
            (L : ℝ) x y)
    (hlevel : (𝓛[f]((f x)) : Set E₁) ⊆ interior 𝓕)
    (hLM : (L : ℝ) ≤ M) :
    step x ∈ 𝓛[f]((f x)) := by
  let x0 : E₁ := x
  have hconv0 : ConvexOn ℝ Set.univ (ψ[F; φ; J] x0) := by
    simpa [x0] using hconv
  have hcont0 : Continuous (meritFunctionReformulation F φ) := hcont
  have hupper0 :
      ∀ ⦃y : E₁⦄, y ∈ 𝓕 →
        meritFunctionReformulation F φ y ≤
          quadraticallyRegularizedObjective
            (ψ[F; φ; J] x0)
            (L : ℝ) x0 y := by
    simpa [x0] using hupper
  have hlevel0 : (𝓛[f]((f x0)) : Set E₁) ⊆ interior 𝓕 := by
    simpa [x0] using hlevel
  let y := step x
  let z : ℝ → E₁ := fun t ↦ x0 + t • (y - x0)
  let qL : E₁ → ℝ :=
    quadraticallyRegularizedObjective (ψ[F; φ; J] x0) (L : ℝ) x0
  let I : Set ℝ := Set.Icc (0 : ℝ) 1
  have hy_min :
      IsMinOn (quadraticallyRegularizedObjective (ψ[F; φ; J] x0) M x0) Set.univ y := by
    simpa [y] using step.isMinOn_apply x
  have hqMy_le : quadraticallyRegularizedObjective (ψ[F; φ; J] x0) M x0 y ≤ f x0 := by
    simpa [quadraticallyRegularizedObjective_apply, x0, y] using (isMinOn_univ_iff.mp hy_min) x0
  have hqLy_le : qL y ≤ f x0 := by
    have hqL_le_qM :
        qL y ≤ quadraticallyRegularizedObjective (ψ[F; φ; J] x0) M x0 y := by
      simp [qL, quadraticallyRegularizedObjective_apply]
      nlinarith [sq_nonneg ‖y - x0‖, hLM]
    exact hqL_le_qM.trans hqMy_le
  have hz_sub (t : ℝ) : z t - x0 = t • (y - x0) := by
    simp [z]
  have hpsi_le (t : ℝ) (ht : t ∈ I) :
      ψ[F; φ; J] x0 (z t) ≤ (1 - t) * ψ[F; φ; J] x0 x0 + t * ψ[F; φ; J] x0 y := by
    have hconv_t :
        ψ[F; φ; J] x0 (AffineMap.lineMap x0 y t) ≤
          (1 - t) * ψ[F; φ; J] x0 x0 + t * ψ[F; φ; J] x0 y := by
      simpa [AffineMap.lineMap_apply_module, smul_eq_mul] using
        hconv0.2 (show x0 ∈ Set.univ by simp) (show y ∈ Set.univ by simp)
          (sub_nonneg.mpr ht.2) ht.1 (by ring)
    have hsegment : z t = AffineMap.lineMap x0 y t := by
      rw [AffineMap.lineMap_apply_module']
      ac_rfl
    simpa [hsegment] using hconv_t
  have hqL_le (t : ℝ) (ht : t ∈ I) : qL (z t) ≤ f x0 := by
    have ht_sq_le : t ^ (2 : ℕ) ≤ t := by
      nlinarith [ht.1, ht.2]
    have hnorm :
        ‖z t - x0‖ ^ (2 : ℕ) = t ^ (2 : ℕ) * ‖y - x0‖ ^ (2 : ℕ) := by
      rw [hz_sub, norm_smul, Real.norm_of_nonneg ht.1, mul_pow]
    have hqLy' :
        ψ[F; φ; J] x0 y + ((L : ℝ) / 2 : ℝ) * ‖y - x0‖ ^ (2 : ℕ) ≤ f x0 := by
      simpa [qL, quadraticallyRegularizedObjective_apply, x0] using hqLy_le
    have hxx : ψ[F; φ; J] x0 x0 = f x0 := by
      simp [meritFunctionReformulation_apply]
    let c : ℝ := ((L : ℝ) / 2 : ℝ) * ‖y - x0‖ ^ (2 : ℕ)
    have hc_nonneg : 0 ≤ c := by
      dsimp [c]
      positivity
    have hpenalty_le :
        ((L : ℝ) / 2 : ℝ) * (t ^ (2 : ℕ) * ‖y - x0‖ ^ (2 : ℕ)) ≤
          t * (((L : ℝ) / 2 : ℝ) * ‖y - x0‖ ^ (2 : ℕ)) := by
      have hct : c * t ^ (2 : ℕ) ≤ c * t :=
        mul_le_mul_of_nonneg_left ht_sq_le hc_nonneg
      simpa [c, mul_assoc, mul_left_comm, mul_comm] using hct
    change ψ[F; φ; J] x0 (z t) + ((L : ℝ) / 2 : ℝ) * ‖z t - x0‖ ^ (2 : ℕ) ≤ f x0
    rw [hnorm]
    have hpsi := hpsi_le t ht
    nlinarith
  have hlevel_closed : IsClosed (𝓛[f]((f x0)) : Set E₁) := by
    simpa [levelSet_eq_setOf] using isClosed_Iic.preimage hcont0
  let segment : I → E₁ := fun t ↦ z t
  have hsegment_cont : Continuous segment := by
    exact (continuous_const.add (continuous_subtype_val.smul continuous_const))
  let U : Set I := segment ⁻¹' interior 𝓕
  have hU_open : IsOpen U := isOpen_interior.preimage hsegment_cont
  have hU_eq :
      U = segment ⁻¹' (𝓛[f]((f x0)) : Set E₁) := by
    ext t
    constructor
    · intro htU
      have ht𝓕 : segment t ∈ 𝓕 := interior_subset htU
      have ht_upper :
          f (segment t) ≤ qL (segment t) :=
        hupper0 ht𝓕
      have ht_level : segment t ∈ 𝓛[f]((f x0)) := by
        simpa [segment] using ht_upper.trans (hqL_le t t.2)
      exact ht_level
    · intro ht_level
      exact hlevel0 ht_level
  have hU_closed : IsClosed U := by
    rw [hU_eq]
    exact hlevel_closed.preimage hsegment_cont
  have hU_clopen : IsClopen U := ⟨hU_closed, hU_open⟩
  letI : PreconnectedSpace I := Subtype.preconnectedSpace isPreconnected_Icc
  have h0 : (⟨0, by constructor <;> norm_num⟩ : I) ∈ U := by
    have hx0_level : x0 ∈ 𝓛[f]((f x0)) := by
      simp [x0]
    simpa [U, segment, z, x0] using hlevel0 hx0_level
  have hU_univ : U = Set.univ := hU_clopen.eq_univ ⟨_, h0⟩
  have h1U : (⟨1, by constructor <;> norm_num⟩ : I) ∈ U := by
    simp [hU_univ]
  have hy𝓕 : y ∈ 𝓕 := by
    have : segment ⟨1, by constructor <;> norm_num⟩ ∈ interior 𝓕 := h1U
    simpa [segment, z, y, x0] using interior_subset this
  have hy_upper : f y ≤ qL y := hupper0 hy𝓕
  simpa [y] using hy_upper.trans hqLy_le

end

/-! ### Proposition_4_4_4 (from Chap04) -/
universe u v

variable {E₁ : Type u} {E₂ : Type v} [Zero E₂]

/- Proposition 4.4.4 lies in the merit-scalarization / nonlinear-system-solvability domain.

Sampled owner-style declarations:
* `IsMeritFunction` in `Definition_4_4_1`, the chapter owner for nonnegative residual
  scalarizations vanishing exactly at `0`
* `IsMeritFunction.eq_zero_iff`, the owner zero-detection theorem for merit functions
* `IsMinOn` in mathlib, the canonical owner for minimizers on a set
* `isMinOn_univ_iff` in mathlib, the textbook bridge from `IsMinOn ... Set.univ ...` to the
  pointwise inequality form

Best owner abstraction:
* source-facing: solvability of `F x = 0` detected through the merit reformulation
  `meritFunctionReformulation F φ` at a global minimizer
* core/canonical: `IsMeritFunction φ` together with `IsMinOn (fun x ↦ φ (F x)) Set.univ xStar`
* bridge/view: the zero-detection consequence obtained by specializing
  `IsMeritFunction.eq_zero_iff` to residuals of the form `F x`

Primitive data:
* the residual map `F`
* the merit scalarizer `φ`
* the chosen minimizer `xStar`

Derived API:
* the residual zero-detection step `φ (F x) = 0 ↔ F x = 0`
* the minimizer comparison
  `meritFunctionReformulation F φ xStar ≤ meritFunctionReformulation F φ x` for every `x`

Source/core/bridge triage:
* source-facing: the iff between solvability of `F x = 0` and vanishing minimum merit value of
  `meritFunctionReformulation F φ`
* core/canonical: `IsMeritFunction` and `IsMinOn`
* bridge/view: specializing the owner zero-detection theorem to `F x`

The theorem surface is organized around the canonical owners
`meritFunctionReformulation F φ` and `IsMinOn`, rather than a parallel free-standing wrapper for
the same minimizer data. The proof still derives the zero-detection step directly from
`IsMeritFunction.eq_zero_iff`.
-/

-- Proof sketch: if `F x = 0` for some `x`, then `IsMeritFunction.eq_zero_iff` gives
-- `φ (F x) = 0`, and the minimizer inequality at `xStar` forces the minimum value to be at most
-- `0`; `IsMeritFunction.nonneg` makes it exactly `0`. Conversely, if the minimizing value at
-- `xStar` is `0`, then `IsMeritFunction.eq_zero_iff` gives `F xStar = 0`, so `xStar` solves the
-- nonlinear system.

/-- Any exact solution `F xStar = 0` globally minimizes the merit reformulation when the merit
function is nonnegative and vanishes only at the zero residual. -/
theorem exact_solution_isMinOn_meritFunctionReformulation
    {F : E₁ → E₂} {φ : E₂ → ℝ} [IsMeritFunction φ] {xStar : E₁}
    (hxStar : F xStar = 0) :
    IsMinOn (meritFunctionReformulation F φ) Set.univ xStar := by
  rw [isMinOn_univ_iff]
  intro x
  have hxStar_zero : meritFunctionReformulation F φ xStar = 0 := by
    simpa using (IsMeritFunction.eq_zero_iff (F xStar)).2 hxStar
  rw [hxStar_zero]
  simpa using IsMeritFunction.nonneg (F x)

namespace IsMinOn

/-- Proposition 4.4.4: if `xStar` realizes the minimum value `f*` of the merit reformulation
`meritFunctionReformulation F φ`, and `φ` is nonnegative and vanishes only at the zero residual,
then that minimum value is `0` if and only if the nonlinear equation `F x = 0` is solvable. -/
theorem meritFunctionReformulation_eq_zero_iff_exists_zero_residual
    {F : E₁ → E₂} {φ : E₂ → ℝ} [IsMeritFunction φ] {xStar : E₁}
    (hxStar : IsMinOn (meritFunctionReformulation F φ) Set.univ xStar) :
    meritFunctionReformulation F φ xStar = 0 ↔ ∃ x : E₁, F x = 0 := by
  constructor
  · intro hxStar_zero
    exact ⟨xStar, (IsMeritFunction.eq_zero_iff (F xStar)).1 hxStar_zero⟩
  · rintro ⟨x, hx⟩
    have hx_zero : meritFunctionReformulation F φ x = 0 := by
      simpa using (IsMeritFunction.eq_zero_iff (F x)).2 hx
    have hxMin : IsMinOn (meritFunctionReformulation F φ) Set.univ x :=
      exact_solution_isMinOn_meritFunctionReformulation hx
    have hxStar_le_x :
        meritFunctionReformulation F φ xStar ≤ meritFunctionReformulation F φ x :=
      (isMinOn_univ_iff.mp hxStar) x
    have hx_le_xStar :
        meritFunctionReformulation F φ x ≤ meritFunctionReformulation F φ xStar :=
      (isMinOn_univ_iff.mp hxMin) xStar
    exact le_antisymm (hx_zero ▸ hxStar_le_x) (hx_zero ▸ hx_le_xStar)

end IsMinOn

/-! ### Theorem_4_4_4 (from Chap04) -/
noncomputable section

open SmoothNonlinearEquationProblem
open scoped Manifold

universe u v

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/- Theorem 4.4.4 lies in the whole-space modified Gauss--Newton / exact-solvability domain.

Sampled owner-style declarations:
* `SmoothNonlinearEquationProblem.solutionSet` in `Definition_4_4_8`, the chapter owner for the
  exact-solution locus `problem x = 0`;
* mathlib `LipschitzOnWith L (fun x ↦ fderiv ℝ problem x) Set.univ`, the canonical whole-space
  Jacobian-Lipschitz owner for the residual map;
* `HasUniformDualNondegeneracyOnInitialSublevelSet` in `Assumption_4_4_3`, the source-facing
  nondegeneracy owner on the norm-merit initial sublevel set;
* `IsMinOn` in mathlib, the canonical owner for global minimizers on `Set.univ`;
* `exact_solution_isMinOn_meritFunctionReformulation` in `Proposition_4_4_4`, the thin bridge
  from an exact solution back to the minimizer reformulation.

Best owner abstraction:
* source-facing: existence of an exact solution `xStar ∈ solutionSet problem` together with the
  displayed distance bound from the initial point;
* core/canonical: the residual map `problem` together with the whole-space Jacobian-Lipschitz
  owner `LipschitzOnWith L (fderiv ℝ problem) Set.univ`;
* bridge/view: the norm-merit reformulation `meritFunctionReformulation problem norm` on whose
  initial sublevel set Assumption 4.4.3 is imposed.

Primitive data:
* the bundled smooth residual map `problem`;
* the initial point `x0`;
* the nondegeneracy constant `σ`;
* the whole-space Jacobian-Lipschitz hypothesis on `problem`;
* the norm-merit nondegeneracy assumption
  `HasUniformDualNondegeneracyOnInitialSublevelSet`.

Derived API:
* the exact-solution owner `xStar ∈ solutionSet problem`;
* the initial-residual distance bound.

This refinement keeps the labeled theorem at the source-facing exact-solution layer. The
minimizer reformulation is left to the upstream bridge from `Proposition_4_4_4`
`exact_solution_isMinOn_meritFunctionReformulation` instead of being repackaged locally. It also
removes the nonfaithful global `C¹` hypothesis on the raw norm merit `x ↦ ‖problem x‖`, whose
nondifferentiability at nondegenerate zeros conflicts with Assumption 4.4.3, and instead places
the smoothness input on the canonical owner layer already used by the chapter Taylor-remainder
bridge: the whole-space Jacobian-Lipschitz control of `problem`.
-/

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯

section

variable {problem : SmoothMap}
variable {x0 : E} {σ : ℝ}

-- Proof sketch: apply the global modified Gauss--Newton method to the norm-merit reformulation
-- `x ↦ ‖problem x‖` with constant regularization `M_k = L`. The whole-space Jacobian-Lipschitz
-- hypothesis supplies the smooth residual-map owner needed for the chapter Taylor-remainder and
-- one-step decrease estimates, while Assumption 4.4.3 controls the same norm-merit sublevel set.
-- The first phase gives uniform merit decrease until the threshold `σ^2 / L`, and the second
-- phase gives geometric decay of the merit values together with summable step lengths via the
-- residual bound from Lemma 4.4.7. The iterate sequence therefore converges to a point
-- `xStar ∈ solutionSet problem`, and summing the two phases yields
-- `‖xStar - x0‖ ≤ (2 / σ) * ‖problem x0‖`.
/-- Theorem 4.4.4: if the residual map `problem` has `L`-Lipschitz Jacobian on `Set.univ` and
Assumption 4.4.3 holds on the initial sublevel set of the norm-merit reformulation
`x ↦ ‖problem x‖`, then there exists an exact solution `x* ∈ solutionSet problem` whose distance
from the initial point is bounded by `(2 / σ) * ‖problem x₀‖`. -/
theorem exists_exact_solution_dist_le_two_div_sigma_mul_initialResidual
    (L : NNReal)
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) Set.univ)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem norm x0 σ) :
    ∃ xStar : E,
      xStar ∈ solutionSet problem ∧
        ‖xStar - x0‖ ≤ (2 / σ) * ‖problem x0‖ := sorry

end

/-! ### Definition_4_4_5 (from Chap04) -/
noncomputable section

universe u v w

variable {𝕜 : Type w} {E₁ : Type u} {E₂ : Type v}

/-
Definition 4.4.5 lies in the normed-space operator / minimal-singular-value domain.

Sampled owner-style declarations:
- `ContinuousLinearMap.opNorm` with `ratio_le_opNorm`, the canonical mathlib owner for quotient
  norms of continuous linear maps;
- `FiniteDimensional.proper`, the compactness bridge that turns the unit sphere into a compact set
  in finite-dimensional normed spaces;
- `LinearMap.singularValues`, the stronger finite-dimensional inner-product bridge for identifying
  `σ_min(A)` with the last singular value when that extra structure is available;
- `LinearMap.singularValues_nonneg`, the canonical nonnegativity API on that stronger bridge side.

Best owner abstraction:
- source-facing: the textbook least singular value `σ_min(A)` of a continuous linear operator `A`;
- core/canonical: the infimum of the ratio `‖A x‖ / ‖x‖` over nonzero vectors;
- bridge/view: the finite-dimensional unit-sphere formula and, under stronger inner-product
  hypotheses, the identification with the last singular value.

Primitive data:
- a continuous linear operator `A : E₁ →L[𝕜] E₂`.

Derived API:
- the source-facing notation `σ_min(A)`;
- the nonnegativity theorem;
- the defining infimum formula over nonzero vectors;
- the finite-dimensional unit-sphere bridge;
- the stronger singular-value identification under inner-product hypotheses.
-/
namespace ContinuousLinearMap

section Owner

variable [NormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

/-- Definition 4.4.5: the least singular value of `A` is the infimum of the quotients
`‖A x‖ / ‖x‖` over nonzero vectors `x`. -/
def minimalSingularValue (A : E₁ →L[𝕜] E₂) : ℝ :=
  sInf (Set.range fun x : {x : E₁ // x ≠ 0} ↦ ‖A x.1‖ / ‖x.1‖)

end Owner

end ContinuousLinearMap

namespace MinimalSingularValue

/- Source-facing Lean notation for the textbook least singular value `σ_min(A)`. -/
scoped notation:max "σ_min(" A ")" => ContinuousLinearMap.minimalSingularValue A

end MinimalSingularValue

open scoped MinimalSingularValue

namespace ContinuousLinearEquiv

section Bridge

variable [NormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

/-- Coercion bridge: the least singular value of a continuous linear equivalence, viewed through
the canonical coercion to a continuous linear map. -/
abbrev minimalSingularValue (A : E₁ ≃L[𝕜] E₂) : ℝ :=
  ContinuousLinearMap.minimalSingularValue (A : E₁ →L[𝕜] E₂)

/- Source-facing Lean notation for the textbook least singular value of a continuous linear
equivalence. -/
scoped notation:max "σ_min(" A ")" => ContinuousLinearEquiv.minimalSingularValue A

end Bridge

section NormBridge

variable [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

/- Thin operator-norm bridge: a continuous linear equivalence carries the operator norm of its
underlying continuous linear map. -/
instance : Norm (E₁ ≃L[𝕜] E₂) where
  norm A := ‖(A : E₁ →L[𝕜] E₂)‖

@[simp] theorem norm_toContinuousLinearMap (A : E₁ ≃L[𝕜] E₂) :
    ‖A.toContinuousLinearMap‖ = ‖A‖ :=
  rfl

end NormBridge

end ContinuousLinearEquiv

section Owner

variable [NormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

/-- Source-facing bridge: `σ_min(A)` equals the infimum of `‖A x‖ / ‖x‖` over nonzero vectors. -/
theorem minimalSingularValue_def (A : E₁ →L[𝕜] E₂) :
    σ_min(A) =
      sInf (Set.range fun x : {x : E₁ // x ≠ 0} ↦ ‖A x.1‖ / ‖x.1‖) := by
  rfl

/-- The least singular value is nonnegative. -/
theorem minimalSingularValue_nonneg (A : E₁ →L[𝕜] E₂) :
    0 ≤ σ_min(A) := by
  rw [minimalSingularValue_def]
  refine Real.sInf_nonneg ?_
  rintro _ ⟨x, rfl⟩
  exact div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- If the domain is subsingleton, then the least singular value is zero. -/
theorem minimalSingularValue_eq_zero [Subsingleton E₁] (A : E₁ →L[𝕜] E₂) :
    σ_min(A) = 0 := by
  rw [minimalSingularValue_def]
  have hrange :
      Set.range (fun x : {x : E₁ // x ≠ 0} ↦ ‖A x.1‖ / ‖x.1‖) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact x.2 <| Subsingleton.elim _ _
  simp [hrange, Real.sInf_empty]

end Owner

section SingularValuesBridge

variable [RCLike 𝕜]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]

/-- Stronger bridge: over finite-dimensional inner-product spaces, `σ_min(A)` is the last singular
value of `A.toLinearMap`. -/
theorem minimalSingularValue_eq_singularValues_last (A : E₁ →L[𝕜] E₂) :
    σ_min(A) = A.toLinearMap.singularValues (Module.finrank 𝕜 E₁ - 1) := by
  sorry

end SingularValuesBridge

section FiniteDimensional

variable [RCLike 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

/-- Over finite-dimensional normed spaces, `σ_min(A)` is the infimum of `‖A x‖` over the unit
sphere. -/
theorem minimalSingularValue_eq_sInf_norm_image_unitSphere
    (A : E₁ →L[𝕜] E₂) :
    σ_min(A) =
      sInf (Set.range fun x : Metric.sphere (0 : E₁) 1 ↦ ‖A x.1‖) := by
  sorry

end FiniteDimensional

/-! ### Lemma_4_4_5 (from Chap04) -/
noncomputable section

open SetConstrainedMinimizationProblem
open scoped Manifold
open scoped ModifiedGaussNewtonLocalModelNotation

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Lemma 4.4.5 lies in the merit-scalarization / quadratic-regularized local-model domain.

Sampled owner-style declarations:
* `abs_meritFunctionReformulation_sub_modifiedGaussNewtonLocalModel_le` in `Lemma_4_4_1`, the
  chapter owner for comparing the true merit objective with the modified Gauss--Newton local
  model under the primitive scalarizer hypothesis `LipschitzWith 1 φ`;
* `modifiedGaussNewtonLocalModel` in `Definition_4_4_11`, the source-facing owner for the local
  model `ψ(x; y)`;
* `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17`, the canonical project owner
  for the quadratic penalty added to a model;
* `SetConstrainedMinimizationProblem` and `SetConstrainedMinimizationProblem.optimalValue` in
  `Chap01/Definition_1_3_3` and `Chap01/Definition_1_3_7`, the canonical owner for the feasible
  minimization-value layer;
* `LipschitzWith.norm_sub_le` in mathlib, the canonical pointwise estimate used to compare
  scalarizer values.

Best owner abstraction:
* source-facing: the textbook upper bound on the modified Gauss--Newton model value `f_M(x)`;
* core/canonical: `LipschitzWith`, `modifiedGaussNewtonLocalModel`,
  `quadraticallyRegularizedObjective`, `ModifiedGaussNewtonStep`, and the Chapter 1 owner
  `SetConstrainedMinimizationProblem.optimalValue`;
* bridge/view: the textbook `sInf` formula over the feasible subtype `𝓕`.

Primitive data:
* the residual map `problem`;
* the scalarizer `φ` together with its primitive canonical regularity input `LipschitzWith 1 φ`;
* the feasible set `𝓕` and Jacobian-Lipschitz bound on `problem`;
* the chosen modified Gauss--Newton step `step`.

Derived API:
* the pointwise comparison with the feasible merit-plus-quadratic objective
  `y ↦ meritFunctionReformulation problem φ y + (((L : ℝ) + M) / 2) * ‖y - x‖²`;
* the textbook real-valued `sInf` bound over the feasible subtype `𝓕`.

This refinement keeps Lemma 4.4.5 at the source-facing textbook `sInf` layer while reusing the
chapter and project owner API directly, without introducing a one-off public wrapper around
`SetConstrainedMinimizationProblem.mk`.
-/

-- Proof sketch: global minimality of `step x` bounds `step.modelValue x` by the
-- quadratic-regularized local model at every comparison point `y`. The discrepancy estimate from
-- Lemma 4.4.1 then bounds the local model by the merit reformulation plus `(L / 2) ‖y - x‖²`,
-- and adding the existing `(M / 2) ‖y - x‖²` term yields the comparison objective.
/-- For every feasible comparison point `y ∈ 𝓕`, the model value `f_M(x)` is bounded above by
the feasible merit-plus-quadratic objective from Lemma 4.4.5 evaluated at `y`. -/
theorem modifiedGaussNewton_modelValue_le_feasibleMeritQuadraticObjective
    (problem : C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯)
    (φ : E₂ → ℝ) (hφ : LipschitzWith 1 φ)
    {𝓕 : Set E₁} {L : NNReal} {M : ℝ}
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (step :
      ModifiedGaussNewtonStep
        (ψ[problem; φ; (fderiv ℝ problem)])
        𝓕 M)
    (x : 𝓕) {y : E₁} (hy : y ∈ 𝓕) :
    step.modelValue x ≤
      meritFunctionReformulation problem φ y +
        (((L : ℝ) + M) / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
  have hmin :
      step.modelValue x ≤
        quadraticallyRegularizedObjective
          (ψ[problem; φ; (fderiv ℝ problem)] x) M x y :=
    (isMinOn_univ_iff.mp (step.isMinOn_apply x)) y
  have hmodel :
      ψ[problem; φ; (fderiv ℝ problem)](x; y) ≤
        meritFunctionReformulation problem φ y +
          ((L : ℝ) / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
    have hdiscrepancy :=
      abs_meritFunctionReformulation_sub_modifiedGaussNewtonLocalModel_le
        problem φ hφ h𝓕 h_jacobian_lipschitz x.2 hy
    have hlower :
        -(((L : ℝ) / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)) ≤
          meritFunctionReformulation problem φ y -
            ψ[problem; φ; (fderiv ℝ problem)](x; y) :=
      (abs_le.mp hdiscrepancy).1
    linarith
  have hcompare :
      quadraticallyRegularizedObjective
          (ψ[problem; φ; (fderiv ℝ problem)] x) M x y ≤
        meritFunctionReformulation problem φ y +
          (((L : ℝ) + M) / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
    rw [quadraticallyRegularizedObjective_apply]
    linarith
  exact hmin.trans hcompare

-- Proof sketch: the feasible-value set is nonempty because it contains the base point `x`, and
-- the pointwise comparison theorem shows it is bounded below by `step.modelValue x`. The desired
-- real-valued `sInf` bound then follows from `le_csInf`.
/-- Lemma 4.4.5:
`f_M(x)` is bounded above by
`inf_{y ∈ 𝓕} [f(y) + ((L + M) / 2) ‖y - x‖²]`,
written as the infimum over the feasible subtype. -/
theorem modifiedGaussNewton_modelValue_le_sInf_feasible_merit_plus_quadratic
    (problem : C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯)
    (φ : E₂ → ℝ) (hφ : LipschitzWith 1 φ)
    {𝓕 : Set E₁} {L : NNReal} {M : ℝ}
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (step :
      ModifiedGaussNewtonStep
        (ψ[problem; φ; (fderiv ℝ problem)])
        𝓕 M)
    (x : 𝓕) :
    step.modelValue x ≤
      sInf (Set.range fun y : 𝓕 ↦
        meritFunctionReformulation problem φ (y : E₁) +
          (((L : ℝ) + M) / 2 : ℝ) * ‖(y : E₁) - x‖ ^ (2 : ℕ)) := by
  refine le_csInf ?_ ?_
  · exact ⟨_, ⟨x, rfl⟩⟩
  · intro b hb
    rcases hb with ⟨y, rfl⟩
    exact modifiedGaussNewton_modelValue_le_feasibleMeritQuadraticObjective
      problem φ hφ h𝓕 h_jacobian_lipschitz step x y.2

/-! ### Proposition_4_4_5 (from Chap04) -/
noncomputable section

universe u v

open scoped Manifold

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯

/- Proposition 4.4.5 lies in the local first-order smooth remainder domain for vector-valued maps
on convex subsets of real normed spaces.

Sampled owner-style declarations:
* the bundled smooth-map owner `C^⊤⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯` from `Definition_4_4_8`;
* mathlib `LipschitzOnWith L (fun z ↦ fderiv ℝ f z) s`, the canonical on-set Jacobian-Lipschitz
  owner;
* mathlib `AffineMap.lineMap`, the canonical segment parameterization bridge;
* mathlib `taylor_mean_remainder_bound`, the codomain-general first-order Taylor remainder bound on
  a segment;
* mathlib `norm_image_sub_le_of_norm_deriv_le_segment'`, the one-dimensional mean-value estimate
  behind that Taylor bound.

Best owner abstraction:
* source-facing: the quadratic first-order Taylor remainder bound for a residual map with
  Jacobian Lipschitz on a convex feasible set;
* core/canonical: the bundled smooth map together with `LipschitzOnWith` on the derivative map;
* bridge/view: restriction to the affine line segment from `x` to `y`.

Primitive data:
* the smooth residual map `problem`;
* the feasible set `𝓕`;
* the derivative-Lipschitz owner `h_jacobian_lipschitz`.

Derived API:
* the pointwise quadratic remainder estimate at `x` and `y`.

The previous quantified hypothesis duplicated the owner content of `LipschitzOnWith`. This file
keeps the source-facing proposition but exposes the derivative control through the canonical
owner abstraction directly. The earlier interval-integral route would have imported the
proof-artifact hypothesis `[CompleteSpace F]` from `taylor_integral_remainder`; the proposition
itself is only about a first-order Taylor bound in an arbitrary real normed codomain, so the
ambient completeness assumption is removed from the public API. -/

namespace ContMDiffMap

-- Proof sketch: restrict `problem` to the affine segment from `x` to `y`, apply the codomain-free
-- first-order Taylor remainder bound on `[0, 1]`, use convexity of `𝓕` to keep the segment inside
-- the feasible set, and bound the second derivative along the segment by the Jacobian-Lipschitz
-- estimate coming from `h_jacobian_lipschitz`. This yields the textbook factor `1 / 2` without
-- assuming completeness of the codomain.
/-- Proposition 4.4.5: if the Jacobian of a smooth nonlinear equation problem is `L`-Lipschitz on
a convex feasible set `𝓕`, then for all `x, y ∈ 𝓕` the first-order Taylor remainder of the
residual map satisfies
`‖F(y) - F(x) - F'(x)(y - x)‖ ≤ (L / 2) * ‖y - x‖²`. -/
theorem jacobian_lipschitz_taylor_remainder_le
    (problem : SmoothMap)
    {𝓕 : Set E} {L : NNReal}
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (x y : E) (hx : x ∈ 𝓕) (hy : y ∈ 𝓕) :
    ‖problem y - problem x - fderiv ℝ problem x (y - x)‖ ≤
      ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := sorry

end ContMDiffMap
