import Mathlib
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Order.Filter.Extr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Recall
import Mathlib.Tactic.Ring

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_4_1_12 (from Chap04) -/
open scoped BigOperators Topology
open scoped CubicRegularizedDiagonalInvariants

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.1.12 lies in the diagonal cubic-regularized quadratic / boundary-degeneration
domain.

Sampled owner declarations:
* `cubicRegularizedDiagonalPerturbedGradient` in `Proposition_4_1_11`, the source-facing owner of
  the perturbation `g + δ e_k`;
* `cubicRegularizedQuadraticObjective` in `Theorem_4_1_11`, the chapter owner of the primal cubic
  model;
* `cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos` in
  `Proposition_4_1_9`, the nondegenerate dual-domain owner for `G² > 0`;
* `cubicRegularizedQuadraticDiagonal_primalMinimizer_of_dualMaximizer_of_minimalGradientSquare_pos`
  in `Theorem_4_1_10`, the diagonal owner theorem sending a nondegenerate dual maximizer to the
  corresponding primal minimizer;
* `cubicRegularizedDiagonalResolvent_apply` in `Proposition_4_1_10`, the coordinate bridge for
  the canonical diagonal resolvent point;
* `cubicRegularizedDiagonalResolvent_isMinOn` in `Proposition_4_1_10`, the owner-level minimizer
  theorem for that same resolvent point.

Best owner abstraction:
* source-facing: the explicit boundary limit point in the degenerate case;
* core/canonical: the diagonal resolvent point
  `-((Matrix.diagonal fun i ↦ Hdiag i + lam)⁻¹).mulVec g'`;
* bridge/view: the coordinate formulas identifying that resolvent with the textbook entrywise
  description.

Primitive data:
* `g`, `Hdiag`, `M`, the active index `k`, and the perturbed gradient
  `cubicRegularizedDiagonalPerturbedGradient g k δ`.

Derived API:
* the canonical diagonal resolvent expression above, already supported upstream by the existing
  owner-level minimizer theorems;
* the strict interior fact `-H_min < λ_δ*`, derived upstream from perturbed dual optimality in the
  nondegenerate `G² > 0` regime;
* the source-facing boundary limit point `cubicRegularizedDiagonalBoundaryMinimizer`.

This file therefore keeps the boundary-point owner, but deletes the redundant local perturbed
minimizer wrapper and rewrites the proposition surface directly in terms of the canonical
resolvent point and the existing perturbed dual-maximizer-to-primal-minimizer API. -/

/-- The boundary point obtained by letting the perturbed minimizers approach the degenerate dual
boundary `λ = -H_min` while keeping the `k`-th active coordinate negative. -/
def cubicRegularizedDiagonalBoundaryMinimizer
    (g : E) (Hdiag : Fin n → ℝ) (M : ℝ) (k : Fin n) : E :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm fun i ↦
    if i = k then
      -Real.sqrt
        ((4 : ℝ) * H_min[Hdiag] ^ (2 : ℕ) / M ^ (2 : ℕ) -
          Finset.sum
            (Finset.univ.filter fun j : Fin n ↦
              j ∉ I*[Hdiag])
            (fun j ↦
              (g j) ^ (2 : ℕ) /
                (Hdiag j - H_min[Hdiag]) ^ (2 : ℕ)))
    else if i ∈ I*[Hdiag] then
      0
    else
      -g i / (Hdiag i - H_min[Hdiag])

/-- Evaluating `cubicRegularizedDiagonalBoundaryMinimizer` gives the inactive-coordinate formula
`-g^(i) / (H_i - H_min)`, the zero coordinates on `I* \\ {k}`, and the negative square-root value
for the distinguished active coordinate `k`. -/
-- Proof sketch: unfold `cubicRegularizedDiagonalBoundaryMinimizer`.
theorem cubicRegularizedDiagonalBoundaryMinimizer_apply
    (g : E) (Hdiag : Fin n → ℝ) (M : ℝ) (k i : Fin n) :
    cubicRegularizedDiagonalBoundaryMinimizer g Hdiag M k i =
      if i = k then
        -Real.sqrt
          ((4 : ℝ) * H_min[Hdiag] ^ (2 : ℕ) / M ^ (2 : ℕ) -
            Finset.sum
              (Finset.univ.filter fun j : Fin n ↦
                j ∉ I*[Hdiag])
              (fun j ↦
                (g j) ^ (2 : ℕ) /
                  (Hdiag j - H_min[Hdiag]) ^ (2 : ℕ)))
      else if i ∈ I*[Hdiag] then
        0
      else
        -g i / (Hdiag i - H_min[Hdiag]) := by
  simp [cubicRegularizedDiagonalBoundaryMinimizer]

section

variable (g : E) (Hdiag : Fin n → ℝ) (M : ℝ) (k : Fin n)

local notation "H" => Matrix.diagonal Hdiag
local notation "Dplus(" g' ")" =>
  cubicRegularizedQuadraticDualDomain g' H M ∩ Set.Ici (0 : ℝ)
local notation "gδ(" δ ")" => cubicRegularizedDiagonalPerturbedGradient g k δ
local notation "Aδ(" lamDelta "," δ ")" => Matrix.diagonal fun i ↦ Hdiag i + lamDelta δ
local notation "hδ(" lamDelta "," δ ")" => -Matrix.mulVec ((Aδ(lamDelta, δ))⁻¹) (gδ(δ))

-- Proof sketch: for each `δ > 0`, the perturbed active squared mass is `δ² > 0`, so the
-- perturbed problem is in the nondegenerate `G² > 0` regime. The Chapter 4 domain owner then
-- puts `λ_δ*` in the strict interior region `-H_min < λ_δ*`. Combining that with
-- `perturbedDiagonalDualMaximizer_satisfies_boundaryEquation` from `Proposition_4_1_11`, one
-- rules out every cluster point strictly larger than `-H_min`, leaving `-H_min` as the only
-- possible limit as `δ → 0+`.
/-- Under the hypotheses of Proposition 4.1.12, the perturbed optimal dual parameters satisfy
`λ_δ* → -H_min` as `δ → 0+`. -/
theorem cubicRegularizedDiagonalPerturbedDualMaximizer_tendsto_boundary
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ)) :
    Filter.Tendsto lamDelta (𝓝[>] (0 : ℝ))
      (𝓝 (-H_min[Hdiag])) := sorry

-- Proof sketch: first apply
-- `cubicRegularizedDiagonalPerturbedDualMaximizer_tendsto_boundary` to obtain
-- `λ_δ* → -H_min`. For each `δ > 0`, the same perturbed optimality hypothesis gives the scalar
-- boundary equation from `Proposition_4_1_11` and places `λ_δ*` in the strict interior region
-- `-H_min < λ_δ*`. These derived facts identify the inactive-coordinate limits from the canonical
-- perturbed resolvent formula, while the boundary equation determines the limiting value of
-- the distinguished active coordinate. For global minimality, route each perturbed dual maximizer
-- through the existing Chapter 4 owner theorem to identify the same resolvent point as a global
-- minimizer of the perturbed objective, then compare with the unperturbed objective and pass to
-- the limit as `δ → 0+`.
/-- Proposition 4.1.12: in the degenerate boundary case `G² = 0`, if `k ∈ I*` and each perturbed
objective `v_δ(h) = v(h) + δ h^(k)` has optimal dual point `λ_δ*`, then the corresponding
perturbed minimizers `h_*(δ) = -(H + λ_δ* I)⁻¹ (g + δ e_k)` converge as `δ → 0+` to the explicit
boundary point whose inactive coordinates are `-g^(i) / (H_i - H_min)` and whose `k`-th
coordinate is the negative square root appearing in the textbook formula; moreover, this boundary
point is a global minimizer of the original cubic-regularized quadratic objective. -/
theorem
    cubicRegularizedDiagonalPerturbedMinimizer_tendsto_boundary_and_isMinimizer
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ)) :
    Filter.Tendsto (fun δ : ℝ ↦ hδ(lamDelta, δ))
        (𝓝[>] (0 : ℝ))
        (𝓝 (cubicRegularizedDiagonalBoundaryMinimizer g Hdiag M k)) ∧
      IsMinOn
        (cubicRegularizedQuadraticObjective g H M)
        Set.univ
        (cubicRegularizedDiagonalBoundaryMinimizer g Hdiag M k) := sorry

/-- Under the hypotheses of Proposition 4.1.12, the corresponding perturbed minimizers
`h_*(δ) = -(H + λ_δ* I)⁻¹ (g + δ e_k)` converge as `δ → 0+` to the explicit boundary point whose
inactive coordinates are `-g^(i) / (H_i - H_min)` and whose `k`-th coordinate is the negative
square root appearing in the textbook formula. -/
theorem cubicRegularizedDiagonalPerturbedMinimizer_tendsto_boundaryMinimizer
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ)) :
    Filter.Tendsto (fun δ : ℝ ↦ hδ(lamDelta, δ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (cubicRegularizedDiagonalBoundaryMinimizer g Hdiag M k)) := by
  exact
    (cubicRegularizedDiagonalPerturbedMinimizer_tendsto_boundary_and_isMinimizer
      g Hdiag M k lamDelta hM hk hGzero hopt_max).1

/-- The boundary limit point is a global minimizer of the original cubic-regularized quadratic
problem once the perturbed dual maximizers are routed through the existing owner-level primal
minimizer API. -/
theorem cubicRegularizedDiagonalBoundaryMinimizer_isMinimizer_of_perturbedMinimizers
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ)) :
    IsMinOn
      (cubicRegularizedQuadraticObjective g H M)
      Set.univ
      (cubicRegularizedDiagonalBoundaryMinimizer g Hdiag M k) := by
  exact
    (cubicRegularizedDiagonalPerturbedMinimizer_tendsto_boundary_and_isMinimizer
      g Hdiag M k lamDelta hM hk hGzero hopt_max).2

end

/-! ### Definition_4_1_13 (from Chap04) -/
noncomputable section

open EuclideanSpace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 4.1.13 lies in the chapter's cubic-regularized Lagrangian-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticScalarLagrangian` in `Theorem_4_1_11`, the existing source-facing
  scalar Lagrangian for the cubic epigraph reformulation;
* `cubicRegularizedQuadraticDualFunction` in `Theorem_4_1_11`, the existing chapter owner of the
  scalar dual function `ψ(λ)`;
* `cubicRegularizedQuadraticEpigraphProblem` in `Definition_4_1_14`, the owner
  `LagrangianProblem` packaging of the same one-constraint epigraph subproblem;
* `LagrangianProblem.dualFunction` in `Chap01/Definition_1_10_2`, the core/canonical dual-value
  owner for finitely constrained Lagrangian problems.

Best owner abstraction:
* source-facing: `cubicRegularizedQuadraticDualFunction g H M`;
* core/canonical:
  `(cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction`;
* bridge/view:
  `cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction`.

Primitive data:
* the cubic-regularized epigraph problem data `g`, `H`, and `M`;
* the induced owner problem `cubicRegularizedQuadraticEpigraphProblem g H M`.

Derived API:
* the scalar Lagrangian `cubicRegularizedQuadraticScalarLagrangian`;
* the source-facing scalar dual function `cubicRegularizedQuadraticDualFunction`;
* the canonical `LagrangianProblem.dualFunction` view on the epigraph owner.

Source/core/bridge triage:
* source-facing: the scalar dual function `ψ(λ)` attached to the cubic-regularized quadratic
  subproblem;
* core/canonical: the Chapter 1 owner `LagrangianProblem.dualFunction` on the epigraph problem;
* bridge/view: the specialization theorem below identifying the source-facing scalar owner with
  the generic dual-value owner.

This file therefore deletes the parallel local `...PrimalObjective`, `...Constraint`,
`...Lagrangian`, and `...DualFunction` stack and reuses the established owner declarations
directly. -/

/- The scalar Lagrangian `𝓛(h, τ, λ)` for the cubic-regularized quadratic subproblem is already
the chapter owner `cubicRegularizedQuadraticScalarLagrangian`. -/
recall cubicRegularizedQuadraticScalarLagrangian

/- Definition 4.1.13 is the existing source-facing owner
`cubicRegularizedQuadraticDualFunction`. -/
recall cubicRegularizedQuadraticDualFunction

/- Expanding the source-facing dual function recovers the defining infimum of the scalar
Lagrangian over `(h, τ)`. -/
recall cubicRegularizedQuadraticDualFunction_eq_sInf

/-- The Chapter 4 scalar dual owner is exactly the generic `LagrangianProblem.dualFunction`
specialized to the one-constraint epigraph problem and the scalar multiplier `λ`. -/
theorem cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M lam : ℝ) :
    cubicRegularizedQuadraticDualFunction g H M lam =
      (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction
        (single 0 lam) := by
  rw [LagrangianProblem.dualFunction, SetConstrainedMinimizationProblem.optimalValue,
    cubicRegularizedQuadraticDualFunction]
  congr 1
  ext y
  constructor
  · rintro ⟨x, -, rfl⟩
    refine ⟨x, ?_⟩
    simpa using
      (congrArg (fun t : ℝ ↦ (t : EReal))
        (cubicRegularizedQuadraticEpigraphProblem_lagrangian_eq g H M x.1 x.2 lam)).symm
  · rintro ⟨x, -, rfl⟩
    refine ⟨x, ?_⟩
    simpa using
      congrArg (fun t : ℝ ↦ (t : EReal))
        (cubicRegularizedQuadraticEpigraphProblem_lagrangian_eq g H M x.1 x.2 lam)

/-! ### Proposition_4_1_13 (from Chap04) -/
noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.1.13 lies in the cubic-regularized quadratic / scalar-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticObjective` in `Theorem_4_1_11`, the chapter owner of the primal cubic
  model;
* `cubicRegularizedQuadraticDualFunction` and `cubicRegularizedQuadraticDualDomain` in
  `Theorem_4_1_11`, the chapter owners of the scalar dual value and its effective domain;
* `cubicRegularizedQuadraticScalarDualFunction_eq_sInf_quadratic` in `Proposition_4_1_8`, the
  bridge that eliminates the slack variable and reduces the dual value to the shifted quadratic
  subproblem;
* `Matrix.leastEigenvalue` and the notation `λ_min(H)` in `Definition_4_1_6`, the chapter owner
  for the least-eigenvalue quantity of a real matrix;
* `quadraticObjective` in `Chap01/Definition_1_9_1`, the owner of the shifted quadratic
  `h ↦ ⟪g, h⟫ + (1 / 2) ⟪(H + λ I) h, h⟫`.

Best owner abstraction:
* source-facing: the first-order optimality identity and primal-minimizer statement attached to a
  dual maximizer `λ*`;
* core/canonical: `cubicRegularizedQuadraticObjective`, `cubicRegularizedQuadraticDualFunction`,
  `cubicRegularizedQuadraticDualDomain`, the shifted quadratic `quadraticObjective 0 g
  (H + λ • I)`, and the spectral interior condition `-λ_min(H) < λ`;
* bridge/view: the explicit resolvent point `-((H + λ I)⁻¹).mulVec g`.

Primitive data:
* `g`, `H`, `M`, the symmetry hypothesis `H.IsSymm`, and the shifted matrix `H + λ I`;
* dual optimality on `cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)`.

Derived API:
* the explicit resolvent point above;
* the norm identity `‖h*‖ = (2 / M) λ*`;
* the global primal minimizer statement for that same `h*`.

Source/core/bridge triage:
* source-facing: the two textbook consequences for a dual maximizer `λ*`;
* core/canonical: the existing objective/dual owner family from `Theorem_4_1_11`;
* bridge/view: the resolvent formula expressing the source point as `-A⁻¹ g`.

This file therefore stays at the theorem layer and does not introduce a second local owner for the
dual problem or the shifted quadratic subproblem. -/

section

variable (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)

local notation "Dplus" => cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)
local notation "A" lam => H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)
local notation "resolvent" lam => -Matrix.mulVec ((A lam)⁻¹) g

variable {lamStar : ℝ}
variable (hM : 0 < M) (hH : H.IsSymm)
variable (hmax : IsMaxOn (cubicRegularizedQuadraticDualFunction g H M) Dplus lamStar)
variable (hlam : -λ_min(H) < lamStar)

-- Proof sketch: since `λ*` maximizes `ψ` on `Dplus`, the Hessian is symmetric, and
-- `λ* > -λ_min(H)`, the shifted quadratic owner lies in the positive-definite spectral region.
-- Differentiate the explicit formula for the dual value at interior points, use the resolvent
-- identity for the minimizing `h`-subproblem, and solve `ψ'(λ*) = 0` for the norm of the
-- resolvent point `-((A λ*)⁻¹).mulVec g`.
/-- Proposition 4.1.13: if `λ*` maximizes the dual function `ψ` over `dom ψ ∩ ℝ₊` and the
shifted symmetric Hessian lies in the interior region `λ* > -λ_min(H)`, then the
scalar first-order optimality condition holds:
`‖-(H + λ* I)⁻¹ g‖ = (2 / M) λ*`. -/
theorem cubicRegularizedQuadratic_resolvent_norm_eq_of_dualMaximizer
    (hM : 0 < M) (hH : H.IsSymm)
    (hmax : IsMaxOn (cubicRegularizedQuadraticDualFunction g H M) Dplus lamStar)
    (hlam : -λ_min(H) < lamStar)
    : ‖resolvent lamStar‖ = (2 / M : ℝ) * lamStar := sorry

-- Proof sketch: minimize the quadratic `h`-subproblem in the Lagrangian at the maximizing
-- multiplier `λ*`; the symmetry and spectral-interior hypotheses place `H + λ* I` in the
-- positive-definite quadratic region, so the unique minimizer is `-(H + λ* I)⁻¹ g`. Then
-- combine strong duality at `λ*` with the first-order condition from
-- `cubicRegularizedQuadratic_resolvent_norm_eq_of_dualMaximizer` to conclude that this resolvent
-- point globally minimizes the primal cubic-regularized quadratic objective.
/-- Under the hypotheses of Proposition 4.1.13, the corresponding resolvent point
`-(H + λ* I)⁻¹ g` is a global minimizer of the primal cubic-regularized quadratic objective. -/
theorem cubicRegularizedQuadratic_resolvent_isMinimizer_of_dualMaximizer
    (hM : 0 < M) (hH : H.IsSymm)
    (hmax : IsMaxOn (cubicRegularizedQuadraticDualFunction g H M) Dplus lamStar)
    (hlam : -λ_min(H) < lamStar)
    :
    IsMinOn (cubicRegularizedQuadraticObjective g H M) Set.univ
      (resolvent lamStar) := sorry

end

/-! ### Definition_4_1_14 (from Chap04) -/
noncomputable section

open EuclideanSpace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The cubic-regularized quadratic objective
`v(h) = ⟪g, h⟫ + (1 / 2) ⟪H h, h⟫ + (M / 6) ‖h‖^3`. -/
def cubicRegularizedQuadraticObjective
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) : E → ℝ :=
  fun h ↦
    dotProduct g h +
      (1 / 2 : ℝ) * dotProduct (H.mulVec h) h +
        (M / 6 : ℝ) * ‖h‖ ^ (3 : ℕ)

/-- Evaluating `cubicRegularizedQuadraticObjective g H M` recovers the displayed formula for
`v(h)`. -/
theorem cubicRegularizedQuadraticObjective_apply
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) (h : E) :
    cubicRegularizedQuadraticObjective g H M h =
      dotProduct g h +
        (1 / 2 : ℝ) * dotProduct (H.mulVec h) h +
          (M / 6 : ℝ) * ‖h‖ ^ (3 : ℕ) :=
  rfl

/-- The scalar epigraph Lagrangian `𝓛(h, τ, λ)` for the cubic-regularized quadratic model. -/
def cubicRegularizedQuadraticScalarLagrangian
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) (h : E) (τ lam : ℝ) : ℝ :=
  dotProduct g h +
    (1 / 2 : ℝ) * dotProduct (H.mulVec h) h +
      (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) +
        lam * ((1 / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * τ)

/-- The scalar dual function `ψ(λ)` obtained by infimizing the epigraph Lagrangian over
`(h, τ) ∈ ℝⁿ × ℝ`. -/
def cubicRegularizedQuadraticDualFunction
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) (lam : ℝ) : EReal :=
  sInf (Set.range fun z : E × ℝ ↦
    (cubicRegularizedQuadraticScalarLagrangian g H M z.1 z.2 lam : EReal))

/-- Expanding `cubicRegularizedQuadraticDualFunction g H M lam` gives the infimum definition of
`ψ(λ)`. -/
theorem cubicRegularizedQuadraticDualFunction_eq_sInf
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M lam : ℝ) :
    cubicRegularizedQuadraticDualFunction g H M lam =
      sInf (Set.range fun z : E × ℝ ↦
        (cubicRegularizedQuadraticScalarLagrangian g H M z.1 z.2 lam : EReal)) :=
  rfl

/-- The effective domain `dom ψ = {λ | ψ(λ) > -∞}` of the scalar dual function. -/
def cubicRegularizedQuadraticDualDomain
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) : Set ℝ :=
  { lam | ⊥ < cubicRegularizedQuadraticDualFunction g H M lam }

/-- Membership in `cubicRegularizedQuadraticDualDomain g H M` means exactly that the dual value
`ψ(λ)` is finite from below. -/
theorem mem_cubicRegularizedQuadraticDualDomain_iff
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M lam : ℝ) :
    lam ∈ cubicRegularizedQuadraticDualDomain g H M ↔
      ⊥ < cubicRegularizedQuadraticDualFunction g H M lam :=
  Iff.rfl

/-- The explicit slack-variable minimizer `τ(λ) = 4 λ |λ| / M²`. -/
def cubicRegularizedQuadraticTauMinimizer
    (M lam : ℝ) : ℝ :=
  (4 : ℝ) * lam * |lam| / M ^ (2 : ℕ)

/-- Expanding `cubicRegularizedQuadraticTauMinimizer M lam` recovers the formula
`4 λ |λ| / M²`. -/
theorem cubicRegularizedQuadraticTauMinimizer_def
    (M lam : ℝ) :
    cubicRegularizedQuadraticTauMinimizer M lam =
      (4 : ℝ) * lam * |lam| / M ^ (2 : ℕ) :=
  rfl

/-- Helper for Definition 4.1.14: the zero-offset quadratic owner agrees with the displayed
coordinate formula `⟪g, h⟫ + (1 / 2) ⟪Ah, h⟫`. -/
lemma quadraticObjective_zero_eq_dotProduct
    (g : E) (A : Matrix (Fin n) (Fin n) ℝ) (h : E) :
    quadraticObjective 0 g A h =
      dotProduct g h + (1 / 2 : ℝ) * dotProduct (A.mulVec h) h := by
  -- Convert the abstract inner products in `quadraticObjective` to the coordinate `dotProduct`
  -- form used by the scalar Lagrangian.
  rw [quadraticObjective]
  have hg : inner ℝ g h = dotProduct g h := by
    simpa [dotProduct_comm] using (EuclideanSpace.inner_eq_star_dotProduct g h)
  have hA : inner ℝ (A.toEuclideanLin h) h = dotProduct (A.mulVec h) h := by
    simpa [Matrix.toLpLin_apply, dotProduct_comm] using
      (EuclideanSpace.inner_eq_star_dotProduct (A.toEuclideanLin h) h)
  rw [hg, hA]
  ring

/-- Helper for Definition 4.1.14: the scalar Lagrangian splits into the shifted quadratic
`q_λ(h)` plus the pure slack-variable objective. -/
lemma cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) (h : E) (τ lam : ℝ) :
    cubicRegularizedQuadraticScalarLagrangian g H M h τ lam =
      quadraticObjective 0 g (H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h +
        ((M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ) := by
  -- Separate the `h`-dependent quadratic part from the scalar `τ`-objective.
  rw [cubicRegularizedQuadraticScalarLagrangian, quadraticObjective_zero_eq_dotProduct]
  have hnorm : dotProduct h h = ‖h‖ ^ (2 : ℕ) := by
    -- The identity-matrix contribution is exactly the Euclidean norm square.
    have hdot := (EuclideanSpace.inner_eq_star_dotProduct h h).symm
    simp at hdot
    exact hdot.trans (real_inner_self_eq_norm_sq h)
  simp [Matrix.add_mulVec, Matrix.smul_mulVec, hnorm, add_assoc, add_left_comm, add_comm,
    sub_eq_add_neg, mul_add]
  ring

/-- Helper for Definition 4.1.14: the slack objective is bounded below by the explicit cubic
penalty `-(2 / (3 M²)) |λ|³`. -/
lemma cubicRegularizedQuadraticTauObjective_ge_minValue
    (M : ℝ) (lam : ℝ) (hM : 0 < M) (τ : ℝ) :
    -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) ≤
      (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ := by
  -- First dominate the linear term by replacing `lam * τ` with `|lam| * |τ|`.
  have hlin : -(|lam| / 2 : ℝ) * |τ| ≤ -(lam / 2 : ℝ) * τ := by
    have hmul : lam * τ ≤ |lam| * |τ| := by
      calc
        lam * τ ≤ |lam * τ| := le_abs_self _
        _ = |lam| * |τ| := by rw [abs_mul]
    nlinarith
  let s : ℝ := Real.sqrt |τ|
  have hpow : |τ| ^ (3 / 2 : ℝ) = s ^ (3 : ℕ) := by
    -- Rewrite the `3 / 2` power as a cubic in `sqrt |τ|`.
    calc
      |τ| ^ (3 / 2 : ℝ) = (|τ| ^ (1 / 2 : ℝ)) ^ (3 : ℝ) := by
        rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) * 3 by norm_num, Real.rpow_mul (abs_nonneg τ)]
      _ = s ^ (3 : ℕ) := by
        simp [s, Real.sqrt_eq_rpow]
  have hs_sq : s ^ (2 : ℕ) = |τ| := by
    -- `s = sqrt |τ|` was chosen precisely so that its square recovers `|τ|`.
    dsimp [s]
    exact Real.sq_sqrt (abs_nonneg τ)
  have hpoly :
      -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) ≤
        (M / 6 : ℝ) * s ^ (3 : ℕ) - (|lam| / 2 : ℝ) * s ^ (2 : ℕ) := by
    -- The remaining inequality is the nonnegativity of a factored cubic polynomial.
    have hnonneg : 0 ≤ (M / 6 : ℝ) * (s - 2 * |lam| / M) ^ (2 : ℕ) * (s + |lam| / M) := by
      positivity
    have hidentity :
        (M / 6 : ℝ) * (s - 2 * |lam| / M) ^ (2 : ℕ) * (s + |lam| / M) =
          (M / 6 : ℝ) * s ^ (3 : ℕ) - (|lam| / 2 : ℝ) * s ^ (2 : ℕ) +
            (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ) := by
      field_simp [hM.ne']
      ring
    nlinarith
  have hpoly' :
      -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) ≤
        (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (|lam| / 2 : ℝ) * |τ| := by
    rw [hpow, ← hs_sq]
    exact hpoly
  nlinarith

/-- Helper for Definition 4.1.14: the explicit slack minimizer attains the lower-bound value
`-(2 / (3 M²)) |λ|³`. -/
lemma cubicRegularizedQuadraticTauObjective_eq_minValue_at_minimizer
    (M : ℝ) (lam : ℝ) (hM : 0 < M) :
    (M / 6 : ℝ) * |cubicRegularizedQuadraticTauMinimizer M lam| ^ (3 / 2 : ℝ) -
        (lam / 2 : ℝ) * cubicRegularizedQuadraticTauMinimizer M lam =
      -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) := by
  have habs :
      |cubicRegularizedQuadraticTauMinimizer M lam| = ((2 : ℝ) * |lam| / M) ^ (2 : ℕ) := by
    -- The minimizer has squared magnitude `(2 |λ| / M)²`.
    rw [cubicRegularizedQuadraticTauMinimizer, abs_div, abs_mul, abs_mul,
      abs_of_nonneg (by positivity), abs_abs, abs_of_pos (pow_pos hM 2)]
    field_simp [hM.ne']
    ring_nf
  have hpow :
      |cubicRegularizedQuadraticTauMinimizer M lam| ^ (3 / 2 : ℝ) =
        ((2 : ℝ) * |lam| / M) ^ (3 : ℕ) := by
    -- Raising that squared magnitude to `3 / 2` gives the expected cubic term.
    rw [habs]
    calc
      (((2 : ℝ) * |lam| / M) ^ (2 : ℕ) : ℝ) ^ (3 / 2 : ℝ) =
          (((2 : ℝ) * |lam| / M) ^ (1 : ℕ) : ℝ) ^ (3 : ℕ) := by
        rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ (2 : ℝ) * |lam| / M) 2 (3 / 2 : ℝ)]
        norm_num
      _ = ((2 : ℝ) * |lam| / M) ^ (3 : ℕ) := by ring
  have hlamtau :
      lam * cubicRegularizedQuadraticTauMinimizer M lam =
        |lam| * (((2 : ℝ) * |lam| / M) ^ (2 : ℕ)) := by
    -- The minimizer has the same sign as `lam`, so the linear term also depends only on `|lam|`.
    rw [cubicRegularizedQuadraticTauMinimizer]
    field_simp [hM.ne']
    ring_nf
    rw [← sq_abs lam]
    ring
  have hlinterm :
      (lam / 2 : ℝ) * cubicRegularizedQuadraticTauMinimizer M lam =
        (|lam| / 2 : ℝ) * (((2 : ℝ) * |lam| / M) ^ (2 : ℕ)) := by
    nlinarith [hlamtau]
  rw [hpow, hlinterm]
  field_simp [hM.ne']
  ring

-- Proof sketch: minimize the scalar function
-- `τ ↦ (M / 6) |τ|^(3 / 2) - (lam / 2) τ` directly; the critical point is the explicit owner
-- `cubicRegularizedQuadraticTauMinimizer M lam`, and convexity yields global minimality.
/-- For `M > 0`, the scalar function
`τ ↦ (M / 6) |τ|^(3 / 2) - (lam / 2) τ` is minimized at
`cubicRegularizedQuadraticTauMinimizer M lam`. -/
theorem cubicRegularizedQuadraticTauMinimizer_isMinOn
    (M : ℝ) (hM : 0 < M) (lam : ℝ) :
    IsMinOn
      (fun τ : ℝ ↦
        (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ)
      Set.univ
      (cubicRegularizedQuadraticTauMinimizer M lam) := by
  rw [isMinOn_univ_iff]
  intro τ
  -- Compare every slack value with the explicit minimum value attained at `τ(λ)`.
  calc
    (M / 6 : ℝ) * |cubicRegularizedQuadraticTauMinimizer M lam| ^ (3 / 2 : ℝ) -
        (lam / 2 : ℝ) * cubicRegularizedQuadraticTauMinimizer M lam =
        -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) :=
      cubicRegularizedQuadraticTauObjective_eq_minValue_at_minimizer M lam hM
    _ ≤ (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ :=
      cubicRegularizedQuadraticTauObjective_ge_minValue M lam hM τ

/-- Definition 4.1.14: the auxiliary cubic subproblem is encoded by the equivalent one-constraint
epigraph Lagrangian problem with objective `\tilde v(h, τ) = ⟪g, h⟫ + (1 / 2) ⟪H h, h⟫ +
(M / 6) |τ|^{3/2}` and constraint `(1 / 2) ‖h‖² - (1 / 2) τ ≤ 0`; its generic Lagrangian and the
downstream scalar dual function are derived from this owner. -/
def cubicRegularizedQuadraticEpigraphProblem
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) : LagrangianProblem (E × ℝ) 1 :=
  { objective := fun z ↦
      dotProduct g z.1 +
        (1 / 2 : ℝ) * dotProduct (H.mulVec z.1) z.1 +
          (M / 6 : ℝ) * |z.2| ^ (3 / 2 : ℝ)
    constraints := fun _ z ↦ (1 / 2 : ℝ) * ‖z.1‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * z.2 }

-- Proof sketch: unfold `cubicRegularizedQuadraticEpigraphProblem`,
-- and reuse the canonical single-constraint expansion
-- `LagrangianProblem.lagrangian_single_eq`.
/-- Expanding the epigraph problem Lagrangian recovers
`\tilde v(h, τ) + λ ((1 / 2) ‖h‖² - (1 / 2) τ)`. -/
theorem cubicRegularizedQuadraticEpigraphProblem_lagrangian_eq
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) (h : E) (τ lam : ℝ) :
    (cubicRegularizedQuadraticEpigraphProblem g H M).lagrangian (h, τ)
        (single 0 lam) =
      cubicRegularizedQuadraticScalarLagrangian g H M h τ lam := by
  simp [cubicRegularizedQuadraticEpigraphProblem, cubicRegularizedQuadraticScalarLagrangian,
    LagrangianProblem.lagrangian_single_eq]

-- Proof sketch: evaluate the epigraph objective at the tight slack `τ = ‖h‖²` and simplify
-- `|‖h‖²|^(3/2)` to `‖h‖^3` using the nonnegative real-power identity for `‖h‖`.
/-- At the tight epigraph value `τ = ‖h‖²`, the epigraph objective recovers the displayed cubic
subproblem objective `⟪g, h⟫ + (1 / 2) ⟪H h, h⟫ + (M / 6) ‖h‖^3`. -/
theorem cubicRegularizedQuadraticEpigraphObjective_eq_formula_at_norm_sq
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) (h : E) :
    cubicRegularizedQuadraticEpigraphProblem g H M (h, ‖h‖ ^ (2 : ℕ)) =
      cubicRegularizedQuadraticObjective g H M h := by
  have hpow : (‖h‖ ^ (2 : ℕ) : ℝ) ^ (3 / 2 : ℝ) = ‖h‖ ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast_mul (norm_nonneg h) 2 (3 / 2 : ℝ)]
    norm_num
  rw [cubicRegularizedQuadraticObjective_apply]
  simp [cubicRegularizedQuadraticEpigraphProblem, hpow]

-- Proof sketch: eliminating the slack variable shows that the cubic penalty contributes only a
-- finite additive constant, so the effective dual domain is controlled exactly by boundedness
-- below of the shifted quadratic form `q_λ`. This is the canonical bridge reused downstream in
-- Proposition 4.1.8 and its diagonal specialization.
/-- The effective domain of the scalar dual function consists exactly of those multipliers `λ`
for which the shifted quadratic objective `q_λ` is bounded below. -/
theorem cubicRegularizedQuadraticScalarDualDomain_eq
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) {M : ℝ}
    (hM : 0 < M) :
    cubicRegularizedQuadraticDualDomain g H M =
      { lam |
        BddBelow
          (Set.range
            (quadraticObjective 0 g
              (H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)))) } := by
  ext lam
  constructor
  · intro hdom
    change ⊥ < cubicRegularizedQuadraticDualFunction g H M lam at hdom
    let κ : ℝ := (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)
    refine ⟨(cubicRegularizedQuadraticDualFunction g H M lam).toReal + κ, ?_⟩
    rintro y ⟨h, rfl⟩
    have hsle : cubicRegularizedQuadraticDualFunction g H M lam ≤
        (cubicRegularizedQuadraticScalarLagrangian g H M h
          (cubicRegularizedQuadraticTauMinimizer M lam) lam : EReal) := by
      -- Evaluate the infimum at the explicit slack minimizer.
      rw [cubicRegularizedQuadraticDualFunction]
      exact sInf_le ⟨(h, cubicRegularizedQuadraticTauMinimizer M lam), rfl⟩
    have hsle_real :
        (cubicRegularizedQuadraticDualFunction g H M lam).toReal ≤
          cubicRegularizedQuadraticScalarLagrangian g H M h
            (cubicRegularizedQuadraticTauMinimizer M lam) lam :=
      EReal.toReal_le_toReal hsle (ne_of_gt hdom) (EReal.coe_ne_top _)
    have hvalue :
        cubicRegularizedQuadraticScalarLagrangian g H M h
            (cubicRegularizedQuadraticTauMinimizer M lam) lam =
          quadraticObjective 0 g (H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h - κ := by
      -- After minimizing over `τ`, only the shifted quadratic in `h` remains.
      dsimp [κ]
      rw [cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term,
        cubicRegularizedQuadraticTauObjective_eq_minValue_at_minimizer M lam hM]
      ring
    rw [hvalue] at hsle_real
    dsimp [κ]
    nlinarith
  · rintro ⟨b, hb⟩
    change ⊥ < cubicRegularizedQuadraticDualFunction g H M lam
    let κ : ℝ := (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)
    refine lt_of_lt_of_le (EReal.bot_lt_coe (b - κ)) ?_
    rw [cubicRegularizedQuadraticDualFunction]
    refine le_sInf ?_
    rintro y ⟨⟨h, τ⟩, rfl⟩
    have hq : b ≤ quadraticObjective 0 g (H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h :=
      hb ⟨h, rfl⟩
    have hτ : -κ ≤ (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ := by
      -- The slack-variable objective is always at least the explicit minimum value.
      dsimp [κ]
      simpa using cubicRegularizedQuadraticTauObjective_ge_minValue M lam hM τ
    have hsum : b - κ ≤ cubicRegularizedQuadraticScalarLagrangian g H M h τ lam := by
      -- Combine the quadratic lower bound with the universal scalar lower bound.
      rw [cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term]
      nlinarith
    exact EReal.coe_le_coe_iff.2 hsum

/-! ### Proposition_4_1_14 (from Chap04) -/
noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.1.14 lies in the cubic-regularized quadratic / scalar-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticObjective`, `cubicRegularizedQuadraticDualFunction`, and
  `cubicRegularizedQuadraticDualDomain` in `Theorem_4_1_11`, the chapter owners of the primal
  cubic model and scalar dual problem;
* `cubicRegularizedQuadratic_resolvent_norm_eq_of_dualMaximizer` in `Proposition_4_1_13`, the
  owner theorem for the step-length identity attached to a symmetric Hessian and dual maximizer;
* `cubicRegularizedQuadratic_resolvent_isMinimizer_of_dualMaximizer` in `Proposition_4_1_13`,
  the owner theorem identifying the same resolvent point as a primal minimizer;
* `Matrix.leastEigenvalue` and the notation `λ_min(H)` in `Definition_4_1_6`, the chapter owner
  for the least-eigenvalue quantity of a real symmetric matrix;
* `posPart_def`, the canonical bridge rewriting `x⁺` as `max x 0`.

Best owner abstraction:
* source-facing: a chosen point `hStar` with the textbook resolvent representation
  `hStar = -(H + λ* I)⁻¹ g`, together with the derived step length `r := ‖hStar‖`;
* core/canonical: the objective/dual/domain family together with the symmetry and interior
  spectral hypotheses on `H`;
* bridge/view: the dual-maximizer-to-resolvent theorems from `Proposition_4_1_13`.

Primitive data:
* `g`, `H`, `M`, `hH : H.IsSymm`, a dual maximizer `lamStar`, and the interior condition
  `-λ_min(H) < lamStar`;
* a chosen point `hStar` identified with the canonical resolvent point.

Derived API:
* the norm identity `‖hStar‖ = (2 / M) λ*`;
* the fixed-point reformulation for `r := ‖hStar‖`;
* the spectral lower bound for that same `r`.

Source/core/bridge triage:
* source-facing: the three textbook conclusions about `r := ‖hStar‖`;
* core/canonical: the dual-maximizer owner theorems from `Proposition_4_1_13`;
* bridge/view: the equality `hStar = -(H + λ* I)⁻¹ g`.

This file therefore keeps Proposition 4.1.14 at the chosen-minimizer / step-length layer, while
reusing `Proposition_4_1_13` as the proof engine instead of restating a second dual-owner theorem.
-/

section

variable (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)

local notation "ψ" => cubicRegularizedQuadraticDualFunction g H M
local notation "Dplus" => cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)
local notation "A" lam => H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)
local notation "resolvent" lam => -Matrix.mulVec ((A lam)⁻¹) g

variable {lamStar : ℝ}

-- Proof sketch: rewrite the chosen point `hStar` by the resolvent representation and then apply
-- `cubicRegularizedQuadratic_resolvent_norm_eq_of_dualMaximizer`.
/-- Proposition 4.1.14 (1): if the chosen point `hStar` is represented by
`hStar = -(H + λ* I)⁻¹ g` and `r := ‖hStar‖`, then `r = (2 / M) λ*`. -/
theorem cubicRegularizedQuadratic_stepLength_eq
    (hM : 0 < M) (hH : H.IsSymm)
    (hmax : IsMaxOn ψ Dplus lamStar)
    (hlam : -λ_min(H) < lamStar)
    (hStar : E) (hhStar : hStar = resolvent lamStar) :
    let r := ‖hStar‖
    r = (2 / M : ℝ) * lamStar := sorry

-- Proof sketch: Proposition 4.1.14 (1) identifies `r` with `(2 / M) λ*`, so
-- `(M * r) / 2 = λ*`. Substituting that identity into the resolvent formula yields the claimed
-- fixed-point relation.
/-- Proposition 4.1.14 (2): if `hStar = -(H + λ* I)⁻¹ g` and `r := ‖hStar‖`, then
`r = ‖-(H + (M r / 2) I)⁻¹ g‖`. -/
theorem cubicRegularizedQuadratic_stepLength_fixedPoint
    (hM : 0 < M) (hH : H.IsSymm)
    (hmax : IsMaxOn ψ Dplus lamStar)
    (hlam : -λ_min(H) < lamStar)
    (hStar : E) (hhStar : hStar = resolvent lamStar) :
    let r := ‖hStar‖
    r = ‖resolvent ((M * r) / 2)‖ := sorry

-- Proof sketch: the maximizer hypothesis gives `0 ≤ λ*`, while `hlam` yields
-- `-λ_min(H) ≤ λ*`. Hence `(-λ_min(H))⁺ ≤ λ*`. Multiply by the nonnegative factor `2 / M` and
-- use Proposition 4.1.14 (1).
/-- Proposition 4.1.14 (3): if `hStar = -(H + λ* I)⁻¹ g` and `r := ‖hStar‖`, then
`(2 / M) (-λ_min(H))_+ ≤ r`. -/
theorem cubicRegularizedQuadratic_stepLength_lower_bound
    (hM : 0 < M) (hH : H.IsSymm)
    (hmax : IsMaxOn ψ Dplus lamStar)
    (hlam : -λ_min(H) < lamStar)
    (hStar : E) (hhStar : hStar = resolvent lamStar) :
    let r := ‖hStar‖
    (2 / M : ℝ) * (-λ_min(H))⁺ ≤ r := sorry

end

/-! ### Definition_4_1_15 (from Chap04) -/
noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 4.1.15 lies in the diagonal cubic-regularized quadratic / scalar-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticDualDomain` in `Definition_4_1_14`, the chapter owner of `dom ψ`;
* `cubicRegularizedQuadraticScalarDualDomain_eq` in `Definition_4_1_14`, the canonical bridge
  from `dom ψ` to bounded-below shifted quadratics;
* `quadraticObjective` in `Chap01/Definition_1_9_1`, the owner of the shifted quadratic
  `q_λ`;
* `sInf (Set.range Hdiag)`, the canonical order-theoretic owner of the minimum value of the
  finite diagonal family;
* `Finset.filter` on `Finset.univ`, the canonical finite-index realization of the active set `I*`.

Best owner abstraction:
* source-facing: the diagonal invariants `H_min`, `I*`, and `G²`;
* core/canonical: `cubicRegularizedQuadraticDualDomain` together with
  `cubicRegularizedQuadraticScalarDualDomain_eq`;
* bridge/view: specialize the generic dual-domain owner to `H = Matrix.diagonal Hdiag`.

Primitive data:
* the diagonal data `Hdiag`;
* the active gradient coordinates of `g` on the minimal-index set.

Derived API:
* `cubicRegularizedDiagonalMinimum Hdiag`;
* `cubicRegularizedMinimalDiagonalIndices Hdiag`;
* `cubicRegularizedMinimalDiagonalGradientSquare g Hdiag`;
* the diagonal specialization of the existing owner `cubicRegularizedQuadraticDualDomain`.

This file therefore keeps the source-facing diagonal invariants, but deletes the duplicate local
`dom ψ` owner and reuses the chapter owner `cubicRegularizedQuadraticDualDomain` for the diagonal
case. -/

/-- The minimal diagonal entry `H_min` of a diagonal matrix with entries `Hdiag`, realized as the
infimum of the finite diagonal value set. -/
def cubicRegularizedDiagonalMinimum (Hdiag : Fin n → ℝ) : ℝ :=
  sInf (Set.range Hdiag)

/-- The finite index set `I* = { i | H_i = H_min }` of minimal diagonal entries. -/
def cubicRegularizedMinimalDiagonalIndices (Hdiag : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i ↦ Hdiag i = cubicRegularizedDiagonalMinimum Hdiag)

/-- The squared gradient mass `G² = ∑_{i ∈ I*} (g^(i))²` on the minimal diagonal indices. -/
def cubicRegularizedMinimalDiagonalGradientSquare (g : E) (Hdiag : Fin n → ℝ) : ℝ :=
  Finset.sum (cubicRegularizedMinimalDiagonalIndices Hdiag) (fun i ↦ (g i) ^ (2 : ℕ))

namespace CubicRegularizedDiagonalInvariants

scoped notation:max "H_min[" Hdiag "]" =>
  cubicRegularizedDiagonalMinimum Hdiag

scoped notation:max "I*[" Hdiag "]" =>
  cubicRegularizedMinimalDiagonalIndices Hdiag

scoped notation:max "G²[" g ";" Hdiag "]" =>
  cubicRegularizedMinimalDiagonalGradientSquare g Hdiag

end CubicRegularizedDiagonalInvariants

open scoped CubicRegularizedDiagonalInvariants

/- Definition 4.1.15's domain `dom ψ` is the existing owner
`cubicRegularizedQuadraticDualDomain`; in the diagonal case, the bounded-below characterization of
`q_λ` is the existing bridge theorem `cubicRegularizedQuadraticScalarDualDomain_eq`. -/
recall cubicRegularizedQuadraticDualDomain

/- The bounded-below characterization of the diagonal `dom ψ` is the existing theorem
`cubicRegularizedQuadraticScalarDualDomain_eq`, specialized to `H = Matrix.diagonal Hdiag`. -/
recall cubicRegularizedQuadraticScalarDualDomain_eq

-- Proof sketch: unfold `cubicRegularizedMinimalDiagonalIndices`; membership in the filtered
-- finite set is exactly the defining equality `H_i = H_min`.
/-- An index lies in `I*[Hdiag]` exactly when its diagonal entry equals `H_min[Hdiag]`. -/
theorem mem_cubicRegularizedMinimalDiagonalIndices_iff
    (Hdiag : Fin n → ℝ) (i : Fin n) :
    i ∈ I*[Hdiag] ↔ Hdiag i = H_min[Hdiag] := by
  simp [cubicRegularizedMinimalDiagonalIndices]

/-! ### Proposition_4_1_15 (from Chap04) -/
noncomputable section
open scoped CubicRegularizedDiagonalInvariants

/- Proposition 4.1.15 lies in the diagonal cubic-regularized quadratic / scalar-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticObjective` in `Theorem_4_1_11`, the chapter owner of the primal cubic
  model;
* `cubicRegularizedQuadraticDualFunction` and `cubicRegularizedQuadraticDualDomain` in
  `Theorem_4_1_11`, the chapter owners of the scalar dual value and its effective domain;
* `cubicRegularizedDiagonalMinimum` in `Definition_4_1_15`, imported through
  `Theorem_4_1_11`, the chapter owner for the boundary value `-H_min`;
* `IsMinOn` and `IsMaxOn` in mathlib, the canonical owner predicates for primal and dual
  optimality.

Best owner abstraction:
* source-facing: the explicit two-dimensional counterexample itself, with the concrete data
  `g = (-1, 0)ᵀ`, `H = diag(0, -1)`, `M = 1`, the two minimizers `(1, ±√3)ᵀ`, and the boundary
  maximizer `λ* = -H_min[Hdiag] = 1`;
* core/canonical: `cubicRegularizedQuadraticObjective`, `cubicRegularizedQuadraticDualFunction`,
  `cubicRegularizedQuadraticDualDomain`, together with `IsMinOn` and `IsMaxOn`;
* bridge/view: the concrete specialization to `n = 2`.

Primitive data:
* the explicit example vectors/matrix `CubicRegularizedQuadraticCounterexample.g`,
  `CubicRegularizedQuadraticCounterexample.Hdiag`,
  `CubicRegularizedQuadraticCounterexample.H`,
  `CubicRegularizedQuadraticCounterexample.minimizerPos`, and
  `CubicRegularizedQuadraticCounterexample.minimizerNeg`.

Derived API:
* the optimality statements for the two explicit minimizers via `IsMinOn`;
* the identity `-H_min[Hdiag] = 1`;
* dual optimality of the same explicit boundary multiplier on
  `cubicRegularizedQuadraticDualDomain g H 1 ∩ Set.Ici (0 : ℝ)` via `IsMaxOn`.

Source/core/bridge triage:
* source-facing: the explicit counterexample data and witness optimality statements below;
* core/canonical: the chapter owner objective/dual/domain family and the order-owner predicates;
* bridge/view: the concrete `n = 2` specialization of those owners.

This file therefore removes the existential wrapper around “multiple minimizers”, keeps the
explicit textbook witnesses as public data, and reuses the canonical expression
`-H_min[Hdiag]` directly instead of introducing a second public owner for the boundary
multiplier. -/

namespace CubicRegularizedQuadraticCounterexample

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The example gradient `g = (-1, 0)ᵀ`. -/
def g : E :=
  WithLp.toLp 2 ![-(1 : ℝ), (0 : ℝ)]

/-- The diagonal entries of the example Hessian `H = diag(0, -1)`. -/
def Hdiag : Fin 2 → ℝ :=
  ![(0 : ℝ), (-1 : ℝ)]

/-- The example Hessian `H = diag(0, -1)`. -/
def H : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal Hdiag

/-- The positive-sign primal minimizer `(1, √3)ᵀ`. -/
def minimizerPos : E :=
  WithLp.toLp 2 ![(1 : ℝ), Real.sqrt 3]

/-- The negative-sign primal minimizer `(1, -√3)ᵀ`. -/
def minimizerNeg : E :=
  WithLp.toLp 2 ![(1 : ℝ), -(Real.sqrt 3)]

local notation "v" => cubicRegularizedQuadraticObjective g H 1
local notation "ψ" => cubicRegularizedQuadraticDualFunction g H 1
local notation "Dplus" => cubicRegularizedQuadraticDualDomain g H 1 ∩ Set.Ici (0 : ℝ)

-- Proof sketch: the two vectors differ in their second coordinate, since `√3 ≠ -√3`.
/-- Proposition 4.1.15 (1): the two explicit minimizers in the counterexample are distinct. -/
theorem minimizerPos_ne_minimizerNeg :
    minimizerPos ≠ minimizerNeg := sorry

-- Proof sketch: compute the stationary equations for the explicit cubic model with
-- `g = (-1, 0)ᵀ`, `H = diag(0, -1)`, and `M = 1`, then verify that `(1, √3)ᵀ` globally minimizes
-- the primal objective.
/-- Proposition 4.1.15 (2): the point `(1, √3)ᵀ` is a global minimizer of the explicit
cubic-regularized quadratic counterexample. -/
theorem minimizerPos_isMinOn :
    IsMinOn v Set.univ minimizerPos := sorry

-- Proof sketch: the same stationary-point computation gives the symmetric second minimizer
-- `(1, -√3)ᵀ`.
/-- Proposition 4.1.15 (3): the point `(1, -√3)ᵀ` is also a global minimizer of the explicit
cubic-regularized quadratic counterexample. -/
theorem minimizerNeg_isMinOn :
    IsMinOn v Set.univ minimizerNeg := sorry

-- Proof sketch: for `Hdiag = (0, -1)`, the minimum diagonal entry is `H_min = -1`.
/-- Proposition 4.1.15 (4): for the explicit Hessian `diag(0, -1)`, the boundary multiplier
`-H_min` equals `1`. -/
theorem boundaryMultiplier_eq_one :
    -H_min[Hdiag] = 1 := sorry

-- Proof sketch: evaluate the scalar dual function on `dom ψ ∩ ℝ₊` for the explicit data and
-- verify that the maximum is attained at the boundary multiplier `-H_min[Hdiag] = 1`.
/-- Proposition 4.1.15 (5): the scalar dual optimum for the explicit counterexample is attained
at the boundary multiplier `λ* = -H_min`. -/
theorem boundaryMultiplier_isMaxOn :
    IsMaxOn ψ Dplus (-H_min[Hdiag]) := sorry

end CubicRegularizedQuadraticCounterexample

/-! ### Definition_4_1_16 (from Chap04) -/
universe u

variable {X : Type u}

/- Definition 4.1.16 lies in the cubic-regularization acceptance domain.

Sampled owner declarations:
* `Set` and `Set.mem_setOf` in mathlib, the canonical owner/view pair for parameter predicates;
* `RelaxedRegularizedNewtonIteration.regularization_mem_Ioc` in `Definition_4_1_5`, which keeps
  interval data separate from the update law;
* `CubicRegularizationMethod.step_value_le_modelValue` in `Algorithm_4_1_5`, which likewise keeps
  the model-comparison inequality separate from the regularization bounds;
* `CubicRegularizationBacktrackingAccepts` in `Definition_4_1_17`, the downstream inequality-only
  acceptance test that should reuse the same core owner.

Best owner abstraction:
* core/canonical: the set of parameters satisfying the acceptance inequality at a fixed point `x`;
* source-facing: the subset of those parameters lying in `[L₀, 2L]`.

Primitive data:
* `f`, `stepMap`, `modelValue`, and the current point `x`;
* for the source-facing layer, the interval endpoints `L₀` and `L`.

Derived API:
* membership characterizations;
* the source-facing introduction lemma from interval membership and the acceptance inequality.

Source/core/bridge triage:
* source-facing: `RegularizedNewton.acceptedParameters`;
* core/canonical: `RegularizedNewton.acceptingParameters`;
* bridge/view: the membership lemmas relating set membership to the textbook inequalities.
-/

namespace RegularizedNewton

variable (f : X → ℝ) (stepMap : ℝ → X → X) (modelValue : ℝ → X → ℝ)
variable (L0 L : ℝ) (x : X)

/-- The core acceptance set at a current point `x`: a parameter `M` belongs to
`acceptingParameters f stepMap modelValue x` exactly when the trial point `T_M(x)` satisfies the
acceptance inequality `f (T_M(x)) ≤ \tilde f_M(x)`. -/
def acceptingParameters
    : Set ℝ :=
  { M | f (stepMap M x) ≤ modelValue M x }

/-- Membership in `acceptingParameters` is exactly the regularized-Newton acceptance inequality at
the current point. -/
@[simp] theorem mem_acceptingParameters_iff
    (M : ℝ) :
    M ∈ acceptingParameters f stepMap modelValue x ↔
      f (stepMap M x) ≤ modelValue M x :=
  Iff.rfl

/-- Definition 4.1.16: the accepted regularized-Newton parameters at `x` are the admissible
parameters `M ∈ [L₀, 2L]` that satisfy the acceptance inequality
`f (T_M(x)) ≤ \tilde f_M(x)`. -/
def acceptedParameters
    : Set ℝ :=
  Set.Icc L0 (2 * L) ∩ acceptingParameters f stepMap modelValue x

/-- Membership in `acceptedParameters` recovers the textbook interval condition together with the
acceptance inequality. -/
@[simp] theorem mem_acceptedParameters_iff
    (M : ℝ) :
    M ∈ acceptedParameters f stepMap modelValue L0 L x ↔
      M ∈ Set.Icc L0 (2 * L) ∧ f (stepMap M x) ≤ modelValue M x := by
  simp [acceptedParameters, acceptingParameters]

/-- An admissible parameter belongs to `acceptedParameters` as soon as it satisfies the
regularized-Newton acceptance inequality at the same current point. -/
theorem mem_acceptedParameters_of_mem_Icc_of_le_modelValue
    {f : X → ℝ} {stepMap : ℝ → X → X} {modelValue : ℝ → X → ℝ}
    {L0 L : ℝ} (x : X) (M : ℝ)
    (hMmem : M ∈ Set.Icc L0 (2 * L))
    (haccept : f (stepMap M x) ≤ modelValue M x) :
    M ∈ acceptedParameters f stepMap modelValue L0 L x := by
  simpa using And.intro hMmem haccept

end RegularizedNewton

/-! ### Proposition_4_1_16 (from Chap04) -/
open scoped BigOperators

noncomputable section

universe u

variable {X : Type u}

/- Proposition 4.1.16 lies in the finite-horizon conservative cubic-regularization backtracking
complexity domain.

Sampled owner declarations:
* `RegularizedNewton.acceptingParameters` and
  `RegularizedNewton.mem_acceptingParameters_iff` in `Definition_4_1_16`, the canonical
  acceptance-set owner and view;
* `CubicRegularizationBacktracking.acceptingExponents`,
  `CubicRegularizationBacktracking.index`, and
  `CubicRegularizationBacktracking.nextRegularization` in `Definition_4_1_17`, the chapter owner
  API for the accepted-exponent set, its least element, and the conservative update
  `M_(k+1) = max {L₀, hat M_k / 2}`;
* `CubicRegularizationMethod.regularization_mem_Icc` in `Algorithm_4_1_5`, the nearby chapter
  pattern where regularization bounds remain theorem-level trajectory data rather than a second
  local owner.

Best owner abstraction:
* source-facing: the finite-horizon conservative complexity statement for a regularization
  schedule `M₀, …, M_(N+1)` and iterate sequence `x₀, x₁, …`;
* core/canonical: `RegularizedNewton.acceptingParameters` for automatic acceptance and
  `CubicRegularizationBacktracking.nextRegularization` for the conservative parameter update;
* bridge/view: `CubicRegularizationBacktracking.IsNextRegularization`, which records the
  witness-free conservative one-step update used by the finite-horizon trajectory hypotheses.

Primitive data:
* the iterate sequence `x₀, x₁, …`;
* the regularization sequence `M₀, M₁, …`;
* the initial bound `M₀ ∈ [L₀, 2L]`;
* the theorem-level conservative update law
  `IsNextRegularization ... x_k M_k L₀ M_(k+1)`.

Derived API:
* automatic acceptance above `L`, phrased directly through `acceptingParameters`;
* existence of accepted exponents at each step under the automatic-acceptance hypothesis;
* propagated interval bounds, the intrinsic endpoint-ratio control on total backtracking
  increments, and the resulting conservative bound on computed trial maps.

Source/core/bridge triage:
* source-facing: the total-backtracking and total-trial-mapping bounds in Proposition 4.1.16;
* core/canonical: `RegularizedNewton.acceptingParameters` and
  `CubicRegularizationBacktracking.nextRegularization`;
* bridge/view: `CubicRegularizationBacktracking.IsNextRegularization`.
-/

namespace CubicRegularizationBacktracking

open RegularizedNewton

variable {f : X → ℝ} {stepMap : ℝ → X → X} {modelValue : ℝ → X → ℝ}
variable {x : ℕ → X} {regularization : ℕ → ℝ} {L0 L : ℝ} {N : ℕ}

/-- The initial interval condition `M₀ ∈ [L₀, 2L]` together with `L₀ > 0` already forces
`L > 0`. -/
theorem L_pos_of_regularization_zero_mem_Icc
    (hregularization_zero_mem_Icc : regularization 0 ∈ Set.Icc L0 (2 * L))
    (hL0 : 0 < L0) :
    0 < L := by
  have hM0_pos : 0 < regularization 0 :=
    lt_of_lt_of_le hL0 hregularization_zero_mem_Icc.1
  have hM0_le : regularization 0 ≤ 2 * L :=
    hregularization_zero_mem_Icc.2
  linarith

section AutomaticAcceptanceAboveL

variable
  (hautomatic :
    ∀ k : ℕ, k ≤ N → ∀ ⦃M : ℝ⦄,
      M ∈ Set.Ici L →
        M ∈ acceptingParameters f stepMap modelValue (x k))
  (hL0 : 0 < L0)

include hautomatic hL0

/-- If the current regularization parameter lies in `[L₀, 2L]`, then automatic acceptance above
`L` produces some accepted backtracking exponent at that step. -/
theorem acceptingExponents_nonempty_of_mem_Icc
    {k : ℕ} (hk : k ≤ N)
    (hk_regularization : regularization k ∈ Set.Icc L0 (2 * L)) :
    (acceptingExponents f stepMap modelValue (x k) (regularization k)).Nonempty := sorry

end AutomaticAcceptanceAboveL

section FiniteHorizon

variable
  (htrajectory :
    ∀ i : Fin (N + 1),
      IsNextRegularization
        f stepMap modelValue (x i.1) (regularization i.1) L0
        (regularization (i.1 + 1)))
  (hautomatic :
    ∀ k : ℕ, k ≤ N → ∀ ⦃M : ℝ⦄,
      M ∈ Set.Ici L →
        M ∈ acceptingParameters f stepMap modelValue (x k))
  (hregularization_zero_mem_Icc : regularization 0 ∈ Set.Icc L0 (2 * L))
  (hL0 : 0 < L0)

include htrajectory hautomatic hregularization_zero_mem_Icc hL0

-- Proof sketch: start from `hregularization_zero_mem_Icc`, derive accepted exponents from
-- `hautomatic`, and use `htrajectory` together with the minimality of the least
-- accepted exponent to show `hat M_k < 2L`; then `nextRegularization` keeps the next parameter
-- inside `[L₀, L] ⊆ [L₀, 2L]`.
/-- Under automatic acceptance above `L`, every regularization parameter produced by the canonical
conservative backtracking update up to index `N + 1` stays in the admissible interval
`[L₀, 2L]`. -/
theorem regularization_mem_Icc
    :
    ∀ k : ℕ, k ≤ N + 1 → regularization k ∈ Set.Icc L0 (2 * L) := sorry

/-- Every regularization parameter produced up to index `N + 1` stays bounded by `2L`. -/
theorem regularization_le_two_mul_L
    :
    ∀ k : ℕ, k ≤ N + 1 → regularization k ≤ 2 * L := by
  intro k hk
  exact (regularization_mem_Icc
    htrajectory hautomatic hregularization_zero_mem_Icc hL0 k hk).2

/-- Under the automatic-acceptance hypothesis, every step `k ≤ N` admits an accepted backtracking
exponent. -/
theorem acceptingExponents_nonempty
    {k : ℕ} (hk : k ≤ N) :
    (acceptingExponents f stepMap modelValue (x k) (regularization k)).Nonempty := by
  exact acceptingExponents_nonempty_of_mem_Icc
    hautomatic hL0 hk
    (regularization_mem_Icc
      htrajectory hautomatic hregularization_zero_mem_Icc hL0
      k (le_trans hk (Nat.le_succ N)))

/-- The total number of backtracking increments accumulated from steps `0` through `N`. -/
def totalBacktrackingIncrements
    :
    ℕ :=
  ∑ i : Fin (N + 1),
    index f stepMap modelValue (x i) (regularization i)
      (acceptingExponents_nonempty
        htrajectory hautomatic hregularization_zero_mem_Icc hL0
        (Nat.lt_succ_iff.mp i.2))

/-- The total number of evaluated trial mappings `T_M` over the first `N + 1` iterations equals
one trial per iteration plus the extra backtracking increments. -/
def totalComputedMappings
    :
    ℕ :=
  (N + 1) +
    totalBacktrackingIncrements
      htrajectory hautomatic hregularization_zero_mem_Icc hL0

-- Proof sketch: for each step `k`, the conservative update law gives
-- `2^(i_k - 1) M_k ≤ M_(k+1)`, so the least accepted exponent satisfies
-- `i_k ≤ 1 + log₂ (M_(k+1) / M_k)`. Summing these inequalities over `k = 0, …, N` telescopes the
-- logarithmic term to the endpoint ratio `M_(N+1) / M₀`.
/-- The total number of conservative backtracking increments is bounded by the number of
iterations plus the base-`2` logarithm of the endpoint regularization ratio. -/
theorem totalBacktrackingIncrements_le_numSteps_add_logb_endpoint_ratio
    :
    (totalBacktrackingIncrements
      htrajectory hautomatic hregularization_zero_mem_Icc hL0 : ℝ) ≤
      (N + 1 : ℝ) + Real.logb 2 (regularization (N + 1) / regularization 0) := sorry

-- Proof sketch: combine
-- `totalBacktrackingIncrements_le_numSteps_add_logb_endpoint_ratio` with the propagated interval
-- bounds `regularization 0 ≥ L₀` and `regularization (N + 1) ≤ 2L`.
/-- The total number of conservative backtracking increments is bounded by the number of
iterations plus `log₂ (2L / L₀)`. -/
theorem totalBacktrackingIncrements_le_numSteps_add_logb_double_ratio
    :
    (totalBacktrackingIncrements
      htrajectory hautomatic hregularization_zero_mem_Icc hL0 : ℝ) ≤
      (N + 1 : ℝ) + Real.logb 2 ((2 * L) / L0) := sorry

-- Proof sketch: by definition,
-- `totalComputedMappings = (N + 1) + totalBacktrackingIncrements`. Apply
-- `totalBacktrackingIncrements_le_numSteps_add_logb_double_ratio` and rearrange the constants.
/-- Proposition 4.1.16: for the conservative backtracking rule, if the acceptance inequality holds
for every tested parameter `M ≥ L` and the initial regularization satisfies `M₀ ∈ [L₀, 2L]`,
then the total number of computed trial mappings `T_M` through iteration `N` is at most
`2 (N + 1) + log₂ (2L / L₀)`. -/
theorem totalComputedMappings_le_conservative_backtracking_cost_bound
    :
    (totalComputedMappings
      htrajectory hautomatic hregularization_zero_mem_Icc hL0 : ℝ) ≤
      (2 : ℝ) * (N + 1 : ℝ) + Real.logb 2 ((2 * L) / L0) := sorry

end FiniteHorizon

end CubicRegularizationBacktracking

/-! ### Definition_4_1_17 (from Chap04) -/
noncomputable section

universe u

variable {X : Type u}

/- Definition 4.1.17 lies in the cubic-regularization backtracking domain.

Relevant declarations sampled before refining:
* `RegularizedNewton.acceptingParameters` and
  `RegularizedNewton.mem_acceptingParameters_iff` in `Definition_4_1_16`, the canonical owner
  of the acceptance condition for a trial regularization parameter;
* `GeneralIterativeScheme.IsAnalyticalComplexity` in `Chap01/Definition_1_2_11`, which keeps the
  source-facing least stage directly as an `IsLeast` owner;
* `stopIndexAt` / `stopIndexAt_isLeast` in `Chap02/Algorithm_2_11`, the project's local
  `Nat.find` pattern for first accepted indices;
* `Nat.isLeast_find` in mathlib, the standard least-natural-number API.

Best owner abstraction:
* source-facing: the set of accepted backtracking exponents `i` for which `2^i M_k` is an
  accepting parameter, together with its least element `i_k`;
* core/canonical: `RegularizedNewton.acceptingParameters f stepMap modelValue xk` and
  `IsLeast (acceptingExponents ...) iₖ`;
* bridge/view: `mem_acceptingExponents_iff`.

Primitive data:
* the current regularization estimate `M_k`;
* existence of an accepted backtracking exponent.

Derived API:
* minimality and acceptance of the chosen exponent;
* failure of all smaller exponents;
* the accepted regularization, next iterate, and next regularization;
* the witness-free bridge `IsNextRegularization` for downstream trajectory statements.

The interval condition `M_k ∈ [L₀, 2L]` remains theorem-level auxiliary data downstream, rather
than primitive owner data for the intrinsic update objects themselves. -/

namespace CubicRegularizationBacktracking

open RegularizedNewton

variable (f : X → ℝ) (stepMap : ℝ → X → X) (modelValue : ℝ → X → ℝ) (xk : X) (Mk : ℝ)

/-- The accepted backtracking exponents are exactly the natural numbers `i` such that the trial
parameter `2^i M_k` belongs to the canonical acceptance set at `x_k`. -/
def acceptingExponents : Set ℕ :=
  { i | (2 : ℝ) ^ i * Mk ∈ acceptingParameters f stepMap modelValue xk }

/-- Membership in `acceptingExponents` is exactly the regularized-Newton acceptance inequality for
the trial parameter `2^i M_k`. -/
@[simp] theorem mem_acceptingExponents_iff
    (i : ℕ) :
    i ∈ acceptingExponents f stepMap modelValue xk Mk ↔
      f (stepMap ((2 : ℝ) ^ i * Mk) xk) ≤ modelValue ((2 : ℝ) ^ i * Mk) xk := by
  simp [acceptingExponents]

/-- Definition 4.1.17: `i_k` is the least backtracking exponent whose trial parameter
`2^i M_k` satisfies the acceptance inequality. -/
noncomputable def index
    (hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty) :
    ℕ :=
  let _ : DecidablePred (· ∈ acceptingExponents f stepMap modelValue xk Mk) := Classical.decPred _
  Nat.find hAccepts

/-- The chosen exponent `i_k` is least among all accepted backtracking exponents. -/
theorem index_isLeast
    (hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty) :
    IsLeast
      (acceptingExponents f stepMap modelValue xk Mk)
      (index f stepMap modelValue xk Mk hAccepts) := by
  classical
  let _ : DecidablePred (· ∈ acceptingExponents f stepMap modelValue xk Mk) := Classical.decPred _
  simpa [index] using Nat.isLeast_find hAccepts

/-- The least backtracking exponent `i_k` belongs to the accepted-exponent set. -/
theorem index_mem_acceptingExponents
    (hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty) :
    index f stepMap modelValue xk Mk hAccepts ∈
      acceptingExponents f stepMap modelValue xk Mk := by
  simpa using (index_isLeast f stepMap modelValue xk Mk hAccepts).1

/-- The accepted regularization parameter `hat M_k = 2^i_k M_k`. -/
def acceptedRegularization
    (hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty) :
    ℝ :=
  (2 : ℝ) ^ index f stepMap modelValue xk Mk hAccepts * Mk

/-- The next iterate `x_(k+1) = T_(hat M_k)(x_k)` selected by the least accepted exponent. -/
def nextIterate
    (hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty) :
    X :=
  stepMap (acceptedRegularization f stepMap modelValue xk Mk hAccepts) xk

/-- The next regularization estimate `M_(k+1) = max{L0, hat M_k / 2}`. -/
def nextRegularization
    (L0 : ℝ)
    (hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty) :
    ℝ :=
  max L0 (acceptedRegularization f stepMap modelValue xk Mk hAccepts / 2)

/-- The conservative update `nextRegularization` is independent of which proof of acceptance
existence is supplied. -/
theorem nextRegularization_eq
    (L0 : ℝ)
    (hAccepts hAccepts' : (acceptingExponents f stepMap modelValue xk Mk).Nonempty) :
    nextRegularization f stepMap modelValue xk Mk L0 hAccepts =
      nextRegularization f stepMap modelValue xk Mk L0 hAccepts' := by
  have h : hAccepts = hAccepts' := Subsingleton.elim _ _
  subst h
  rfl

/-- A value `Mk'` is the conservative next regularization estimate if it agrees with the canonical
update for some accepted backtracking witness. The witness stays internal because
`nextRegularization` is proof-irrelevant in that argument. -/
def IsNextRegularization
    (L0 Mk' : ℝ) : Prop :=
  ∃ hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty,
    Mk' = nextRegularization f stepMap modelValue xk Mk L0 hAccepts

/-- Any witness-free conservative update can be evaluated against any proof that an accepted
backtracking exponent exists. -/
theorem IsNextRegularization.eq
    {L0 Mk' : ℝ}
    (hMk' : IsNextRegularization f stepMap modelValue xk Mk L0 Mk')
    (hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty) :
    Mk' = nextRegularization f stepMap modelValue xk Mk L0 hAccepts := by
  rcases hMk' with ⟨hAccepts', rfl⟩
  exact nextRegularization_eq f stepMap modelValue xk Mk L0 hAccepts' hAccepts

-- Proof sketch: unfold `nextIterate` and `acceptedRegularization`, then use
-- `index_mem_acceptingExponents` through `mem_acceptingExponents_iff`.
/-- The next iterate selected by the least accepted exponent satisfies the accepted model
comparison. -/
theorem objective_nextIterate_le_modelValue
    (hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty) :
    f (nextIterate f stepMap modelValue xk Mk hAccepts) ≤
      modelValue (acceptedRegularization f stepMap modelValue xk Mk hAccepts) xk := by
  simpa [nextIterate, acceptedRegularization] using
    (mem_acceptingExponents_iff
      f stepMap modelValue xk Mk
      (index f stepMap modelValue xk Mk hAccepts)).1
      (index_mem_acceptingExponents f stepMap modelValue xk Mk hAccepts)

-- Proof sketch: this is exactly the minimality clause in `index_isLeast`.
/-- Any smaller backtracking exponent lies outside the accepted-exponent set. -/
theorem not_mem_acceptingExponents_of_lt_index
    (hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty)
    {j : ℕ} (hj : j < index f stepMap modelValue xk Mk hAccepts) :
    j ∉ acceptingExponents f stepMap modelValue xk Mk := by
  intro hjAccepts
  exact (not_le_of_gt hj) ((index_isLeast f stepMap modelValue xk Mk hAccepts).2 hjAccepts)

-- Proof sketch: unfold `nextRegularization`; it is the maximum of `L0` and another real number.
/-- The update rule always keeps the next regularization estimate at least `L0`. -/
theorem le_nextRegularization
    (L0 : ℝ)
    (hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty) :
    L0 ≤ nextRegularization f stepMap modelValue xk Mk L0 hAccepts := by
  exact le_max_left _ _

end CubicRegularizationBacktracking
