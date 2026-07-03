import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_15 (from Chap07) -/
noncomputable section

open Matrix

variable {m n : ℕ}

local notation "Eₘ" => EuclideanSpace ℝ (Fin m)
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Definition 7.15 lies in the chapter's prox-smoothed support-function domain.

Sampled owner-style declarations:
- `supportFunction` in `Chap03/Definition_3_9`, the unsmoothed support-function owner;
- `smoothedPrimalObjective` and `smoothedPrimalObjectiveMaximand` in `Chap06/Definition_6_30`,
  the chapter's canonical regularized-max owner;
- `quadraticDistanceTo` in `Chap06/Remark_6_1_1`, the chapter owner of the Euclidean quadratic
  prox term;
- `continuousLocationSmoothApproximation` and `quadratic_box_smoothed_objective` in
  `Chap06/Definition_6_16` and `Chap06/Definition_6_24`, which show the owner-style for
  source-facing smoothing specializations.

Best owner abstraction:
- source-facing: Definition 7.15's smoothed support-function approximation formula;
- core/canonical: `smoothedPrimalObjective`;
- bridge/view: this numbered file, which only specializes the Chapter 6 owner through the
  matrix-to-dual map `x ↦ innerSL ℝ (A x)` and the prox term `quadraticDistanceTo 0`.

Primitive data:
- the feasible dual set `Q₂`, the matrix `A`, and the positive smoothing parameter `μ`.

Derived API:
- the Euclidean prox term, reused from `quadraticDistanceTo 0`;
- the regularized supremum formula, reused from `smoothedPrimalObjective_apply`.

The previous public alias was a duplicate wheel: the Euclidean prox term is already owned by
`quadraticDistanceTo`, and the regularized-max construction is already owned by
`smoothedPrimalObjective`. This file is therefore recall-first: the numbered item is presented by
direct reuse of the specialized Chapter 6 owner, with only the textbook expansion kept as a
companion theorem. -/

/-- The matrix-to-dual map `x ↦ (u ↦ ⟪Ax, u⟫)` used to specialize the chapter smoothing owner to
Definition 7.15. -/
def supportFunctionSmoothingMap
    (A : Matrix (Fin m) (Fin n) ℝ) : Eₙ →L[ℝ] StrongDual ℝ Eₘ :=
  (innerSL ℝ).comp A.toEuclideanLin.toContinuousLinearMap

@[simp] private theorem supportFunctionSmoothingMap_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Eₙ) (u : Eₘ) :
    supportFunctionSmoothingMap A x u = inner ℝ (A.toEuclideanLin x) u := by
  simp [supportFunctionSmoothingMap, innerSL_apply_apply]

section

variable (Q2 : Set Eₘ) (A : Matrix (Fin m) (Fin n) ℝ) (μ : {μ : ℝ // 0 < μ}) (x : Eₙ)

/- Definition 7.15 is the Chapter 6 regularized-supremum owner specialized to the matrix-to-dual
map `x ↦ (u ↦ ⟪Ax, u⟫)`, zero smooth terms, and the Euclidean prox term
`d₂(u) = (1 / 2) ‖u‖² = quadraticDistanceTo 0 u`. -/
recall smoothedPrimalObjective

set_option linter.hashCommand false in
#check
  smoothedPrimalObjective
    (supportFunctionSmoothingMap A)
    Q2
    0
    0
    (quadraticDistanceTo (0 : Eₘ))
    (μ : ℝ)
    x

end

/- The source-facing companion theorem expands the specialized owner back to the textbook
support-function smoothing formula. -/
@[simp] theorem smoothedPrimalObjective_supportFunction_apply
    (Q2 : Set Eₘ) (A : Matrix (Fin m) (Fin n) ℝ) (μ : ℝ) (x : Eₙ) :
    smoothedPrimalObjective
      (supportFunctionSmoothingMap A)
      Q2
      0
      0
      (quadraticDistanceTo (0 : Eₘ))
      μ
      x =
      sSup ((fun u : Eₘ ↦
        inner ℝ (A.toEuclideanLin x) u - μ * ((1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ))) '' Q2) := by
  rw [smoothedPrimalObjective_apply]
  simp only [Pi.zero_apply, zero_add]
  apply congrArg sSup
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, hu, ?_⟩
    simp [smoothedPrimalObjectiveMaximand]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, hu, ?_⟩
    simp [smoothedPrimalObjectiveMaximand]

end

/-! ### Lemma_7_15 (from Chap07) -/
noncomputable section

open Matrix
open scoped BigOperators MatrixOrder RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ
local notation "Eₙ" => Fin n → ℝ
local notation "SymmMat" => 𝕊^n

/-
Lemma 7.15 lies in Chapter 7's positive-definite / semidefinite-factorization domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n`, `𝕊^n₊`, and `𝕊^n₊₊`, the project owners for symmetric, positive-semidefinite,
  and strict positive-definite matrices;
- `StrictPositiveSemidefiniteCone.inv`, the canonical inverse view of a strict-cone point;
- `mem_positiveSemidefiniteCone_iff`, the bridge from intrinsic cone membership to
  `Matrix.PosSemidef`;
- mathlib `Matrix.toQuadraticMap'`, the canonical quadratic-form owner on `Fin n → ℝ`.

Best owner abstraction:
- source-facing: Lemma 7.15's inverse-diagonal relaxation value and its semidefinite
  representation;
- core/canonical: the Chapter 5 symmetric-matrix cone owners together with
  `Matrix.toQuadraticMap'`;
- bridge/view: the textbook matrix-order and trace formulas recovered by the membership and
  expansion lemmas below.

Primitive data:
- `A : 𝕊^n₊₊`;
- `L : Mₙ`.

Derived API:
- inverse-diagonal feasibility expressed intrinsically by the PSD slack
  `A⁻¹ - diag(u) ∈ 𝕊^n₊`;
- semidefinite feasibility expressed on the symmetric carrier by `X ∈ 𝕊^n₊` and `trace X = 1`;
- the semidefinite objective written through the canonical quadratic-map owner instead of the
  duplicate entrywise formula `dotProduct (X.mulVec v) v`.

This refinement keeps the source-facing real-valued `inf`/`sup` statements, but removes the
parallel subtype `{A // A.PosDef}` and raw `Matrix.PosSemidef` surface from the primitive public
API. The textbook inequalities remain as bridge theorems.
-/

/-- The feasible diagonal vectors `u` for the inverse-diagonal relaxation, expressed intrinsically
by requiring the symmetric slack matrix `A⁻¹ - diag(u)` to be positive semidefinite and each
coordinate of `u` to be positive. -/
def factorizationDiagonalInverseFeasibleSet
    (A : 𝕊^n₊₊) : Set Eₙ :=
  {u |
    (StrictPositiveSemidefiniteCone.inv A -
        ⟨Matrix.diagonal u, by
          rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
          simp
        ⟩ : SymmMat) ∈ 𝕊^n₊ ∧
      ∀ i : Fin n, 0 < u i}

-- Proof sketch: expand membership in `𝕊^n₊` for the slack matrix `A⁻¹ - diag(u)`, then use
-- `Matrix.nonneg_iff_posSemidef` to recover the textbook matrix-order inequality
-- `diag(u) ≤ A⁻¹`.
/-- Membership in the inverse-diagonal feasible set means exactly that `diag(u) ≤ A⁻¹` and every
coordinate of `u` is positive. -/
theorem mem_factorizationDiagonalInverseFeasibleSet_iff
    (A : 𝕊^n₊₊) (u : Eₙ) :
    u ∈ factorizationDiagonalInverseFeasibleSet A ↔
      Matrix.diagonal u ≤ (((A : SymmMat) : Mₙ)⁻¹) ∧ ∀ i : Fin n, 0 < u i := by
  rw [factorizationDiagonalInverseFeasibleSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hfeas, hpos⟩
    rw [mem_positiveSemidefiniteCone_iff] at hfeas
    refine ⟨?_, hpos⟩
    exact sub_nonneg.mp <| by
      simpa using (Matrix.nonneg_iff_posSemidef).mpr hfeas
  · rintro ⟨hdiag, hpos⟩
    refine ⟨?_, hpos⟩
    rw [mem_positiveSemidefiniteCone_iff]
    exact (Matrix.nonneg_iff_posSemidef).mp <| by
      simpa using sub_nonneg.mpr hdiag

/-- The inverse-diagonal relaxation value
`inf {∑ᵢ uᵢ⁻¹ | diag(u) ≤ A⁻¹, uᵢ > 0}` attached to a positive-definite matrix `A`. -/
def factorizationDiagonalInverseRelaxationValue
    (A : 𝕊^n₊₊) : ℝ :=
  sInf ((fun u : Eₙ ↦ ∑ i : Fin n, (u i)⁻¹) '' factorizationDiagonalInverseFeasibleSet A)

/-- Expanding `factorizationDiagonalInverseRelaxationValue A` recovers the defining infimum over
the feasible diagonal vectors `u`. -/
theorem factorizationDiagonalInverseRelaxationValue_eq_sInf
    (A : 𝕊^n₊₊) :
    factorizationDiagonalInverseRelaxationValue A =
      sInf ((fun u : Eₙ ↦ ∑ i : Fin n, (u i)⁻¹) '' factorizationDiagonalInverseFeasibleSet A) :=
  rfl

/-- The feasible matrices `X` in the semidefinite representation: positive semidefinite symmetric
matrices with unit trace. -/
def factorizationSemidefiniteFeasibleSet : Set SymmMat :=
  {X | X ∈ 𝕊^n₊ ∧ Matrix.trace (X : Mₙ) = 1}

/-- Membership in the semidefinite feasible set means being positive semidefinite with unit trace.
-/
theorem mem_factorizationSemidefiniteFeasibleSet_iff
    (X : SymmMat) :
    X ∈ factorizationSemidefiniteFeasibleSet ↔
      (X : Mₙ).PosSemidef ∧ Matrix.trace (X : Mₙ) = 1 := by
  rw [factorizationSemidefiniteFeasibleSet, Set.mem_setOf_eq, mem_positiveSemidefiniteCone_iff]

/-- The semidefinite objective
`X ↦ (∑ᵢ √(qᵢᵀ X qᵢ))²`, where `qᵢ` is the `i`-th column of `L`, written as the `i`-th row of
`Lᵀ`. -/
def factorizationSemidefiniteObjective (L : Mₙ) (X : SymmMat) : ℝ :=
  (∑ i : Fin n, Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i))) ^ (2 : ℕ)

/-- The semidefinite relaxation value attached to the factor matrix `L`. -/
def factorizationSemidefiniteRelaxationValue (L : Mₙ) : ℝ :=
  sSup (factorizationSemidefiniteObjective L '' factorizationSemidefiniteFeasibleSet)

/-- Expanding `factorizationSemidefiniteRelaxationValue L` gives the defining supremum of
`(∑ᵢ √(qᵢᵀ X qᵢ))²` over positive-semidefinite trace-one matrices `X`. -/
theorem factorizationSemidefiniteRelaxationValue_eq_sSup
    (L : Mₙ) :
    factorizationSemidefiniteRelaxationValue L =
      sSup (factorizationSemidefiniteObjective L '' factorizationSemidefiniteFeasibleSet) :=
  rfl

-- Proof sketch: start from the inverse-diagonal formulation of `ψ⋆`, form the Lagrange dual with
-- a positive-semidefinite multiplier, maximize along a fixed ray to obtain the quadratic-root
-- objective, and then apply the change of variables `X = L^{-T} Y L^{-1}` using
-- `A = Lᵀ L`.
/-- Lemma 7.15: if `A = Lᵀ L`, then the value
`ψ⋆ = inf {∑ᵢ uᵢ⁻¹ | diag(u) ≤ A⁻¹, uᵢ > 0}` admits the semidefinite representation
`sup {([∑ᵢ √(qᵢᵀ X qᵢ)]^2) | X ⪰ 0, trace X = 1}`, where `qᵢ` are the columns of `L`. -/
theorem factorizationDiagonalInverseRelaxationValue_eq_semidefiniteRelaxationValue
    (A : 𝕊^n₊₊) (L : Mₙ) (hA : ((A : SymmMat) : Mₙ) = Lᵀ * L) :
    factorizationDiagonalInverseRelaxationValue A =
      factorizationSemidefiniteRelaxationValue L := by
  sorry

/-! ### Proposition_7_15 (from Chap07) -/
noncomputable section

open scoped Gradient PositiveDefMatrixNorm SmoothConvex

variable {m n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 7.15 lies in the Chapter 7 smoothing / weighted-seminorm smoothness domain.

Sampled owner-style declarations:
- `absLinearLogSumExp_contDiff` in `Proposition_7_14`
- `absLinearLogSumExp_hessian_quadraticForm_eq` in `Proposition_7_14`
- `positiveDefMatrixNorm` in `Definition_7_23`
- `ConvexC1SeminormSmooth.dualNorm_gradient_sub_le` in `Chap02/Theorem_2_5`

Best owner abstraction:
- source-facing: the weighted `G`-norm Hessian and gradient estimates for `absLinearLogSumExp μ a`
- core/canonical: `absLinearLogSumExp μ a ∈ 𝓕[L, positiveDefMatrixNorm G.1 G.2]¹¹`
- bridge/view: the explicit Hessian quadratic-form bound and its source-facing dual-gradient
  Lipschitz corollary

Primitive data:
- the family `a : Fin m → E`
- the positive-definite matrix owner `G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}`
- the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`
- the weighted dual-norm bound on the vectors `a i`

Derived API:
- `ContDiff ℝ 2 (absLinearLogSumExp μ a)`, already owned by `Proposition_7_14`
- the weighted Hessian quadratic-form upper bound
- the owner-level smooth-convex membership theorem
- the source-facing weighted dual-gradient Lipschitz estimate

Source/core/bridge triage:
- source-facing: the weighted Hessian and gradient bounds
- core/canonical: the smooth-convex owner `𝓕[L, p]¹¹`
- bridge/view: the explicit quadratic-form estimate needed to enter that owner API

The previous conjunction theorem duplicated the upstream owner `absLinearLogSumExp_contDiff` and
attached the weighted-norm hypothesis `ha` to a smoothness statement that does not use it. This
refinement keeps only the genuinely new weighted estimates and routes the gradient conclusion
through the Chapter 2 owner API. -/

section

variable (a : Fin m → E) (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) {ν : ℝ}
variable (μ : {μ : ℝ // 0 < μ})
variable (ha : ∀ i : Fin m, ‖a i‖[G,*] ≤ ν * Real.sqrt n)

-- Proof sketch: combine Proposition 7.14 with the chapter owner `positiveDefMatrixNorm`: the
-- smoothness is `absLinearLogSumExp_contDiff`, the Hessian quadratic form is
-- `absLinearLogSumExp_hessian_quadraticForm_eq`, and the weighted dual-norm bound on the `aᵢ`
-- controls the second-moment term by `ν² n / μ`.
/-- Proposition 7.15: if `‖aᵢ‖_G^* ≤ ν √n` for every `i`, then the Hessian quadratic form of
`f_μ(x) = μ log ∑ᵢ (exp(⟪aᵢ, x⟫ / μ) + exp(-⟪aᵢ, x⟫ / μ))`
is bounded above by `(ν² n / μ) ‖h‖_G²`. The `C²` regularity is already the owner theorem
`absLinearLogSumExp_contDiff` from `Proposition_7_14`. -/
theorem absLinearLogSumExp_hessian_quadraticForm_le (x h : E) :
    inner ℝ (hessian (absLinearLogSumExp μ a) x h) h ≤
      (((ν ^ (2 : ℕ)) * (n : ℝ)) / (μ : ℝ)) * ‖h‖[G] ^ (2 : ℕ) := sorry

-- Proof sketch: `absLinearLogSumExp_contDiff μ` gives the regularity input, while
-- `absLinearLogSumExp_hessian_quadraticForm_le` supplies the upper Hessian bound. Combine these
-- with the Chapter 2 owner bridge `convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded` to
-- place `absLinearLogSumExp μ a` in the smooth-convex class for the weighted norm
-- `positiveDefMatrixNorm G.1 G.2`.
/-- The Chapter 2 smooth-convex owner view of Proposition 7.15 for the weighted norm `‖·‖_G`. -/
theorem absLinearLogSumExp_mem_F11_positiveDefMatrixNorm :
    absLinearLogSumExp μ a ∈
      𝓕[Real.toNNReal ((((ν ^ (2 : ℕ)) * (n : ℝ)) / (μ : ℝ))), positiveDefMatrixNorm G.1 G.2]¹¹ :=
  sorry

-- Proof sketch: apply the owner theorem
-- `absLinearLogSumExp_mem_F11_positiveDefMatrixNorm`, then specialize the defining
-- `dualNorm_gradient_sub_le` consequence of `𝓕[L, p]¹¹` to the weighted seminorm
-- `positiveDefMatrixNorm G.1 G.2`.
/-- The gradient of the log-sum-exp smoothing is Lipschitz with respect to the `G`-norm and its
dual norm, with constant `ν² n / μ`. -/
theorem absLinearLogSumExp_dual_gradient_sub_le (x y : E) :
    ‖∇ (absLinearLogSumExp μ a) x - ∇ (absLinearLogSumExp μ a) y‖[G,*] ≤
      (((ν ^ (2 : ℕ)) * (n : ℝ)) / (μ : ℝ)) * ‖x - y‖[G] := sorry

end

end

/-! ### Theorem_7_15 (from Chap07) -/
noncomputable section

open scoped Gradient HessianDualLocalNorm WithTopConvexAnalysis

universe u

/- Theorem 7.15 lies in Chapter 7's barrier-subgradient explicit-rate domain.

Mandatory domain-style sampling:
- `DualBarrierSubgradientMethod.maximalGap_upper_bound` in `Chap07/Theorem_7_14`, the upstream
  maximal-gap owner theorem that still carries the source error term `A_k`;
- `DualBarrierSubgradientMethod.maximalGap` and `barrierSubgradientWeightSum` in
  `Chap07/Definition_7_57`, the Chapter 7 owners of `ℓ_k⋆` and `S_k`;
- `HessianDualLocalNorm.ofPosDefMem` in `Chap05/Definition_5_0_20`, the canonical owner of the
  barrier Hessian dual norm attached to the actual chosen subgradient field of the method;
- `barrierSubgradientLambda` and `barrierSubgradientBeta` in `Chap07/Definition_7_58`, the
  chapter owners of the parameter choice `(7.3.19)`.

Best owner abstraction:
- source-facing: Theorem 7.15's explicit rate for the normalized maximal gap of a
  `DualBarrierSubgradientMethod`;
- core/canonical: `method.maximalGap_upper_bound`, `method.maximalGap`,
  `barrierSubgradientWeightSum`, `HessianDualLocalNorm.ofPosDefMem`,
  `barrierSubgradientLambda`, and `barrierSubgradientBeta`;
- bridge/view: the generic algebraic simplification theorem
  `barrierSubgradient_rate_le_explicit_rate_of_preliminary_bound` and the parameter-choice
  preliminary estimate below.

Primitive data:
- the Chapter 7 method owner `method : DualBarrierSubgradientMethod P f`;
- the barrier complexity parameter `ν` and subgradient bound `M`;
- the canonical Chapter 5 Hessian-dual local-norm bound on the actual selected field of `method`,
  namely
  `HessianDualLocalNorm.ofPosDefMem method.F x.2 (method.dualSubgradient x) ≤ M`;
- the parameter-choice identities `λ_k = barrierSubgradientLambda k` and
  `β_k = barrierSubgradientBeta M ν k`.

Derived API:
- the owner-level barrier-subgradient-class membership of `-f`, reconstructed internally from the
  actual selected field and the canonical Hessian-dual bound;
- the local ratio hypothesis `hω`, derived in the bridge layer from the owner-level bounded
  subgradient data and the parameter choice `(7.3.19)`;
- the accumulated error term `method.accumulatedOmegaStarError ... k` from Theorem 7.14;
- the preliminary normalized maximal-gap estimate obtained from Theorem 7.14 under the parameter
  choice `(7.3.19)`;
- the closed-form explicit rate obtained by the generic algebraic bridge theorem.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: apply the assumed pre-simplified barrier-subgradient gap estimate, then use the
-- two elementary inequalities from the textbook proof to bound the algebraic prefactor by
-- `sqrt (ν / (k + 1)) + ν / (k + 1)` and the logarithmic factor by
-- `2 * (1 + log (2 + (3 / 2) * sqrt (ν (k + 1))))`.
/-- If a pre-simplified scalar bound for the normalized maximal-gap rate is already available,
then the two scalar inequalities used in the textbook proof convert it into the closed-form
explicit rate. This is the bridge/view algebraic step behind Theorem 7.15. -/
theorem barrierSubgradient_rate_le_explicit_rate_of_preliminary_bound
    (rate : ℕ → ℝ) (M : NNReal) (ν : {ν : ℝ // 0 < ν})
    (hpreliminary :
      ∀ k : ℕ,
        rate k ≤
          (((M : ℝ) *
              ((Real.sqrt (ν : ℝ) / ((k : ℝ) + 1)) * ((1 / 2 : ℝ) + Real.sqrt (k : ℝ)) +
                (((ν : ℝ) + Real.sqrt ((ν : ℝ) * ((k : ℝ) + 1))) / ((k : ℝ) + 1)) *
                  (1 + 2 * Real.log
                    (1 + Real.sqrt (1 + 3 * Real.sqrt ((ν : ℝ) * ((k : ℝ) + 1))))))) : ℝ))
    (k : ℕ) :
    rate k ≤
      ((2 * (M : ℝ) *
          (Real.sqrt ((ν : ℝ) / ((k : ℝ) + 1)) + (ν : ℝ) / ((k : ℝ) + 1)) *
            (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((k : ℝ) + 1)))) : ℝ)) :=
  sorry

namespace DualBarrierSubgradientMethod

variable {P : Set E} {f : E → ℝ}

-- Proof sketch: use Theorem 7.14 for `method.maximalGap`, specialize the Chapter 7 parameter
-- choice `λ_k = 1` and `β_k = M (1 + sqrt (max k 1 / ν))`, divide by `S_k`, and insert the two
-- component estimates supplied by the textbook derivation of `(7.3.19)` to obtain the
-- pre-simplified normalized bound.
/-- Under the Chapter 7 parameter choice `(7.3.19)`, Theorem 7.14 and the two component bounds
produced in the textbook proof yield the pre-simplified estimate for `(1 / S_k) ℓ_k⋆` used in
Theorem 7.15. This is the source-to-bridge step; unlike the generic algebraic lemma above, it
still works directly with the actual method owner and the Chapter 7 data `A_k`, `S_k`, `λ_k`,
and `β_k`. -/
theorem maximalGap_le_preliminary_rate_of_parameter_choice
    (method : DualBarrierSubgradientMethod P f)
    [IsStandardSelfConcordantOn P method.F]
    (M : NNReal) (ν : {ν : ℝ // 0 < ν})
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (hstep : ∀ i : ℕ, (method.stepSize i : ℝ) = barrierSubgradientLambda i)
    (hbeta : ∀ i : ℕ, (method.beta i : ℝ) = barrierSubgradientBeta M ν i)
    (hω :
      ∀ i : ℕ,
        (method.stepSize i : ℝ) *
            HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
              (method.iterate_hessian_isPositive i) (hH i)
              (method.dualSubgradient (method i)) <
          method.beta i)
    (herror :
      ∀ k : ℕ,
        method.accumulatedOmegaStarError hH hω k /
            barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k ≤
          (M : ℝ) *
            (Real.sqrt (ν : ℝ) / ((k : ℝ) + 1)) *
              ((1 / 2 : ℝ) + Real.sqrt (k : ℝ)))
    (hlog :
      ∀ k : ℕ,
        let A := method.accumulatedOmegaStarError hH hω k;
        let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k;
        Real.sqrt (A / ((method.beta (k + 1) : ℝ) * (ν : ℝ))) +
            3 *
              ((S / (method.beta (k + 1) : ℝ)) *
                HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
                  (method.iterate_hessian_isPositive 0) (hH 0)
                  (method.dualSubgradient (method 0))) ≤
          Real.sqrt (1 + 3 * Real.sqrt ((ν : ℝ) * ((k : ℝ) + 1))))
    (k : ℕ) :
    method.maximalGap k /
        barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k ≤
      (M : ℝ) *
        ((Real.sqrt (ν : ℝ) / ((k : ℝ) + 1)) * ((1 / 2 : ℝ) + Real.sqrt (k : ℝ)) +
          (((ν : ℝ) + Real.sqrt ((ν : ℝ) * ((k : ℝ) + 1))) / ((k : ℝ) + 1)) *
            (1 + 2 * Real.log
              (1 + Real.sqrt (1 + 3 * Real.sqrt ((ν : ℝ) * ((k : ℝ) + 1)))))) :=
  sorry

-- Proof sketch: `method.subgradient_spec x` is the Chapter 7 concave-subgradient owner for `f`
-- at `x`; by the sign-flip bridge from Definition 7.50 and the constrained-subdifferential owner
-- from Chapter 3, the negated chosen vector belongs to the constrained subdifferential of `-f`
-- over `P` at `x`.
/-- The actual chosen field of a `DualBarrierSubgradientMethod` supplies a constrained subgradient
of `-f` over `P` at each iterate point, after the canonical sign flip from concave to convex
subgradients. This is the bridge/view connecting Algorithm 7.12's chosen witnesses to the
source-facing owner `barrierSubgradientClass`. -/
theorem neg_subgradient_mem_subdifferentialWithin
    (method : DualBarrierSubgradientMethod P f) (x : P) :
    -method.subgradient x ∈ ∂[P] (fun y ↦ ((-f y : ℝ) : WithTop ℝ)) ((x : E)) :=
  sorry

/-- If the actual chosen field of a `DualBarrierSubgradientMethod` satisfies the pointwise owner
dual-norm bound `‖-method.subgradient x‖ₓ* ≤ M`, then the negated objective belongs to the
Chapter 7 barrier-subgradient class with the same bound. This is the canonical bridge from the
selected-witness layer to the owner-level class `𝓑_M(P)`. -/
private theorem neg_mem_barrierSubgradientClass_of_selected_dualNorm_le
    (method : DualBarrierSubgradientMethod P f)
    {pointNorm : P → Seminorm ℝ E}
    (hpointNorm : ∀ x : P, Seminorm.IsNorm (pointNorm x))
    (M : NNReal)
    (hselected :
      ∀ x : P,
        let _ : Seminorm.IsNorm (pointNorm x) := hpointNorm x
        (pointNorm x).dualNorm (-method.subgradient x) ≤ (M : ℝ)) :
    (fun y ↦ -f y) ∈ barrierSubgradientClass P P pointNorm hpointNorm M := by
  rw [mem_barrierSubgradientClass_iff]
  intro x
  refine ⟨-method.subgradient x, ?_⟩
  let _ : Seminorm.IsNorm (pointNorm x) := hpointNorm x
  exact ⟨method.neg_subgradient_mem_subdifferentialWithin x, hselected x⟩

-- Proof sketch: first apply the parameter-choice preliminary theorem above to recover the
-- normalized maximal-gap estimate supplied by the Chapter 7 maximal-gap machinery; then invoke the
-- generic algebraic bridge theorem to put that estimate into the closed-form rate displayed in the
-- textbook.
/-- Theorem 7.15: if a dual barrier subgradient method uses the Chapter 7 parameter choice
`λ_k = barrierSubgradientLambda k = 1` and
`β_k = barrierSubgradientBeta M ⟨ν, hν⟩ k = M (1 + √(max k 1 / ν))`, where `ν` is the actual
barrier parameter of `method.F` and `M` bounds the actual chosen field of `method` through the
canonical Chapter 5 Hessian dual local norm
`HessianDualLocalNorm.ofPosDefMem method.F x.2 (method.dualSubgradient x)`. The corresponding
owner-level class membership `-f ∈ 𝓑_M(P)` and the local ratio condition remain internal bridge
data, so the public theorem stays on the method owner together with the canonical Hessian-dual
bound. Then for every `k ≥ 0` the normalized maximal gap of the actual method satisfies the
displayed explicit rate. -/
theorem maximalGap_le_explicit_rate
    (method : DualBarrierSubgradientMethod P f)
    (M ν : NNReal) [IsSelfConcordantBarrierOnWith P ν method.F]
    [HasPositiveDefiniteHessianOn P method.F]
    (hν : 0 < (ν : ℝ))
    (hdual :
      ∀ x : P,
        HessianDualLocalNorm.ofPosDefMem method.F x.2 (method.dualSubgradient x) ≤ (M : ℝ))
    (hstep : ∀ i : ℕ, (method.stepSize i : ℝ) = barrierSubgradientLambda i)
    (hbeta : ∀ i : ℕ, (method.beta i : ℝ) = barrierSubgradientBeta M ⟨(ν : ℝ), hν⟩ i)
    (k : ℕ) :
    method.maximalGap k /
      barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k ≤
      ((2 * (M : ℝ) *
          (Real.sqrt ((ν : ℝ) / ((k : ℝ) + 1)) + (ν : ℝ) / ((k : ℝ) + 1)) *
            (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt ((ν : ℝ) * ((k : ℝ) + 1)))) : ℝ)) :=
  sorry

end DualBarrierSubgradientMethod
