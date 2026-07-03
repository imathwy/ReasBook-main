import Mathlib
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_11 (from Chap02) -/
open Matrix
open scoped Gradient

noncomputable section

/- Definition 2.11 lies in finite-dimensional quadratic lower-bound constructions on Euclidean
coordinate spaces.

Source/core/bridge triage:
* source-facing: the textbook tridiagonal matrix `A_k` and the corresponding lower-bound function
  `f_k`
* core/canonical: the Chapter 1 owner `quadraticObjective`
* bridge/view: the explicit coordinate formula for `f_k` and the Hessian matrix identity

Sampled owner-style declarations in this domain:
* `quadraticObjective` in `Definition_1_9_1`
* `hessianMatrix` in `Definition_1_4_16`
* `EuclideanSpace.single` in mathlib for the canonical first basis vector

Best owner abstraction:
* `quadraticObjective`

Primitive data:
* `pathTridiagonalMatrix k`

Derived API:
* `smoothLowerBoundFunction L k` as the specific owner quadratic with Hessian data
  `(L / 4) • pathTridiagonalMatrix k` and first-coordinate linear term
* the explicit textbook expansion `smoothLowerBoundFunction_apply`
* the canonical affine-profile point `smoothLowerBoundFunctionStationaryPoint k`
* the coordinate formula `smoothLowerBoundFunctionStationaryPoint_apply`
* the Hessian identity `smoothLowerBoundFunction_hessian_eq_tridiagonal`
-/

/-- The tridiagonal matrix `A_k` with diagonal entries `2` and first off-diagonal entries `-1`. -/
def pathTridiagonalMatrix (k : ℕ+) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j ↦
    if i = j then
      2
    else if (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) then
      -1
    else
      0

/-- The entries of `pathTridiagonalMatrix k` are `2` on the diagonal, `-1` on the first
sub- and super-diagonals, and `0` elsewhere. -/
-- Proof sketch: unfold `pathTridiagonalMatrix` and read off the three cases in the piecewise
-- definition of the tridiagonal entries.
theorem pathTridiagonalMatrix_apply (k : ℕ+) (i j : Fin k) :
    pathTridiagonalMatrix k i j =
      if i = j then 2 else if (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) then -1 else 0 :=
  rfl

/-- The tridiagonal matrix `A_k` is symmetric. -/
theorem pathTridiagonalMatrix_isSymm (k : ℕ+) :
    (pathTridiagonalMatrix k).IsSymm := by
  refine Matrix.IsSymm.ext fun i j ↦ ?_
  by_cases hij : i = j
  · subst hij
    simp [pathTridiagonalMatrix]
  · have hji : j ≠ i := by simpa [eq_comm] using hij
    simp [pathTridiagonalMatrix, hij, hji, or_comm]

/-- The quadratic test function used for the lower-bound construction; this is the textbook
function `f_k`, presented through the Chapter 1 owner `quadraticObjective`. -/
def smoothLowerBoundFunction (L : ℝ) (k : ℕ+) :
    EuclideanSpace ℝ (Fin k) → ℝ :=
  quadraticObjective 0
    (-(L / 4) • EuclideanSpace.single (0 : Fin k) (1 : ℝ))
    ((L / 4) • pathTridiagonalMatrix k)

/-- The gradient of `smoothLowerBoundFunction L k` is the affine map
`x ↦ (L / 4) A_k x - (L / 4) e₁`. -/
theorem smoothLowerBoundFunction_gradient_eq (L : ℝ) (k : ℕ+) :
    ∇ (smoothLowerBoundFunction L k) =
      fun x ↦
        -(L / 4) • EuclideanSpace.single (0 : Fin k) (1 : ℝ) +
          (((L / 4) • pathTridiagonalMatrix k).toEuclideanLin x) := by
  simpa [smoothLowerBoundFunction] using
    (quadraticObjective_gradient_eq 0
      (-(L / 4) • EuclideanSpace.single (0 : Fin k) (1 : ℝ))
      ((L / 4) • pathTridiagonalMatrix k)
      ((pathTridiagonalMatrix_isSymm k).smul (L / 4)))

/-- Helper for Definition 2.11: the Euclidean quadratic form of the path tridiagonal matrix agrees
with the matrix quadratic form `xᵀ A_k x`. -/
private lemma pathTridiagonal_inner_eq_dotProduct_mulVec (k : ℕ+)
    (x : EuclideanSpace ℝ (Fin k)) :
    inner ℝ ((pathTridiagonalMatrix k).toEuclideanLin x) x =
      dotProduct x (pathTridiagonalMatrix k *ᵥ x) := by
  -- First rewrite the Euclidean inner product as a dot product on coordinates.
  calc
    inner ℝ ((pathTridiagonalMatrix k).toEuclideanLin x) x =
        dotProduct x ((pathTridiagonalMatrix k).toEuclideanLin x) := by
          simpa [dotProduct_comm] using
            (EuclideanSpace.inner_eq_star_dotProduct ((pathTridiagonalMatrix k).toEuclideanLin x) x)
    _ = dotProduct x (pathTridiagonalMatrix k *ᵥ x) := by
          simp [Matrix.toEuclideanLin_apply, Matrix.toLin'_apply]

-- Proof sketch: unfold `smoothLowerBoundFunction` and `quadraticObjective`, then rewrite the
-- quadratic term in coordinates.
/-- The lower-bound quadratic function is the quadratic form associated to `A_k` together with the
linear term `-(L / 4) x₁`. -/
theorem smoothLowerBoundFunction_apply (L : ℝ) (k : ℕ+)
    (x : EuclideanSpace ℝ (Fin k)) :
    smoothLowerBoundFunction L k x =
      (L / 8) * dotProduct x (pathTridiagonalMatrix k *ᵥ x) -
        (L / 4) * x 0 := by
  -- Rewrite the owner quadratic objective into its linear and quadratic coordinate pieces.
  rw [smoothLowerBoundFunction, quadraticObjective]
  have hlinear :
      inner ℝ (-(L / 4) • EuclideanSpace.single (0 : Fin k) (1 : ℝ)) x =
        -(L / 4) * x 0 := by
    -- Evaluate the first-coordinate basis vector against `x`.
    calc
      inner ℝ (-(L / 4) • EuclideanSpace.single (0 : Fin k) (1 : ℝ)) x =
          -(L / 4) * inner ℝ (EuclideanSpace.single (0 : Fin k) (1 : ℝ)) x := by
            rw [real_inner_smul_left]
      _ = -(L / 4) * ((1 : ℝ) * x 0) := by
            congr 1
            exact EuclideanSpace.inner_single_left (0 : Fin k) (1 : ℝ) x
      _ = -(L / 4) * x 0 := by
            ring
  have hquadratic :
      inner ℝ (((L / 4) • pathTridiagonalMatrix k).toEuclideanLin x) x =
        (L / 4) * dotProduct x (pathTridiagonalMatrix k *ᵥ x) := by
    -- Rewrite the scaled matrix action in coordinates, then factor out the scalar `(L / 4)`.
    calc
      inner ℝ (((L / 4) • pathTridiagonalMatrix k).toEuclideanLin x) x =
          dotProduct x (((L / 4) • pathTridiagonalMatrix k).toEuclideanLin x) := by
            simpa [dotProduct_comm] using
              (EuclideanSpace.inner_eq_star_dotProduct
                (((L / 4) • pathTridiagonalMatrix k).toEuclideanLin x) x)
      _ = dotProduct x ((L / 4) • (pathTridiagonalMatrix k *ᵥ x)) := by
            simp [Matrix.toEuclideanLin_apply, Matrix.toLin'_apply]
      _ = (L / 4) * dotProduct x (pathTridiagonalMatrix k *ᵥ x) := by
            simp
  rw [hlinear, hquadratic]
  ring

/-- The canonical affine-profile point for the lower-bound quadratic on `ℝᵏ`. It is the source
point later extended by zero tails to the ambient hard-instance stationary point in Text 2.13. -/
def smoothLowerBoundFunctionStationaryPoint (k : ℕ+) : EuclideanSpace ℝ (Fin k) :=
  (EuclideanSpace.equiv (Fin k) ℝ).symm
    (fun i : Fin k ↦ 1 - (((i : ℕ) + 1 : ℝ) / ((k : ℕ) + 1 : ℝ)))

/-- Evaluating the canonical affine-profile point of `smoothLowerBoundFunction` returns the
displayed coordinate formula. -/
@[simp] theorem smoothLowerBoundFunctionStationaryPoint_apply (k : ℕ+) (i : Fin k) :
    smoothLowerBoundFunctionStationaryPoint k i =
      1 - (((i : ℕ) + 1 : ℝ) / ((k : ℕ) + 1 : ℝ)) := rfl

/-- Helper for Definition 2.11: differentiating the affine gradient formula shows that the
Hessian operator of `smoothLowerBoundFunction L k` is the constant linear map
`((L / 4) • A_k).toEuclideanLin`. -/
private lemma smoothLowerBoundFunction_hessian_eq_toEuclideanLin (L : ℝ) (k : ℕ+)
    (x : EuclideanSpace ℝ (Fin k)) :
    hessian (smoothLowerBoundFunction L k) x =
      ((((L / 4) • pathTridiagonalMatrix k).toEuclideanLin).toContinuousLinearMap :
        EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) := by
  let A :
      EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
    ((L / 4) • pathTridiagonalMatrix k).toEuclideanLin
  have hgrad :
      ∇ (smoothLowerBoundFunction L k) =
        fun y : EuclideanSpace ℝ (Fin k) ↦
          -(L / 4) • EuclideanSpace.single (0 : Fin k) (1 : ℝ) + A y := by
    simpa [A] using smoothLowerBoundFunction_gradient_eq L k
  -- Rewrite the gradient as a constant plus a linear map and differentiate that affine map.
  change fderiv ℝ (∇ (smoothLowerBoundFunction L k)) x = A.toContinuousLinearMap
  rw [hgrad]
  simpa [hessian, A] using
    (((A.toContinuousLinearMap.hasFDerivAt).const_add
      (-(L / 4) • EuclideanSpace.single (0 : Fin k) (1 : ℝ))).fderiv)

-- Proof sketch: rewrite `smoothLowerBoundFunction L k` through the owner `quadraticObjective`,
-- differentiate the quadratic form
-- `x ↦ (L / 8) * ⟪x, A_k x⟫ - (L / 4) * x₁`; the linear term contributes zero to the Hessian,
-- and the quadratic term has constant Hessian `(L / 4) • A_k`.
/-- Definition 2.11: for the textbook lower-bound quadratic `f_k`, the Chapter 1 Hessian matrix is
the constant tridiagonal matrix `(L / 4) A_k`. -/
theorem smoothLowerBoundFunction_hessian_eq_tridiagonal (L : ℝ) (k : ℕ+)
    (x : EuclideanSpace ℝ (Fin k)) :
    ∇² (smoothLowerBoundFunction L k) x =
      (L / 4) • pathTridiagonalMatrix k :=
    by
  -- Compare the Hessian matrix with the intrinsic Hessian operator, then identify that operator.
  apply Matrix.toEuclideanLin.injective
  calc
    (∇² (smoothLowerBoundFunction L k) x).toEuclideanLin =
        hessian (smoothLowerBoundFunction L k) x := by
          simpa using hessianMatrix_toEuclideanLin (smoothLowerBoundFunction L k) x
    _ =
        (((L / 4) • pathTridiagonalMatrix k).toEuclideanLin :
          EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) := by
            exact congrArg ContinuousLinearMap.toLinearMap
              (smoothLowerBoundFunction_hessian_eq_toEuclideanLin L k x)

/-! ### Lemma_2_11 (from Chap02) -/
/-
Lemma 2.11 is a recall-only source-facing item in the convex-sublevel-set domain.

Sampled owner-style declarations:
* `ConvexOn.convex_le`, the owner theorem for convex sublevel sets on an ambient set;
* `ConvexOn.convex_lt`, the open-sublevel analogue in the same owner API;
* `Convex.quasiconvexOn_of_convex_le`, showing that convex sublevel sets are the canonical route
  to quasiconvexity;
* `convex_euclidean_posSemidef_quadratic_sublevelSet` in `Chap02/Exmaple_2_18_1.lean`, a
  downstream chapter use that already calls `ConvexOn.convex_le` directly.

Best owner abstraction:
* `ConvexOn ℝ Set.univ f`.

Primitive data:
* a function `f : ℝⁿ → ℝ`;
* the owner hypothesis `ConvexOn ℝ Set.univ f`.

Derived API:
* convexity of the sublevel set `{x | f x ≤ β}`.

Source/core/bridge triage:
* source-facing: the textbook whole-space sublevel-set convexity lemma;
* core/canonical: the owner predicate `ConvexOn ℝ Set.univ f`;
* bridge/view: `ConvexOn.convex_le`, which produces the sublevel-set convexity statement from the
  owner predicate.

So this file stays as direct canonical recall/use. It intentionally adds no parallel wrapper
theorem, and downstream files should use `ConvexOn.convex_le` directly.
-/

recall ConvexOn.convex_le

/-! ### Proposition_2_11 (from Chap02) -/
/- Proposition 2.11 is recall-only.

Primary domain:
- type-II accelerated Euclidean momentum recurrences.

Sampled owner-style declarations:
- `OptimalMethodRecurrence.y_eq` in `Algorithm_2_2`, the heavier interpolation formula from
  which the type-II momentum update is derived;
- `OptimalMethodRecurrence.gamma_succ_eq_L_mul_sq` in `Algorithm_2_2`, the heavier curvature
  identity used in the same elimination;
- `constantStepSchemeIIAlpha_succ_equation` in `Algorithm_2_4`, the source-facing scalar
  recurrence for Algorithm 2.4;
- `constantStepSchemeIIY_succ` in `Algorithm_2_4`, the source-facing momentum update
  `y_{k+1} = x_{k+1} + β_k (x_{k+1} - x_k)`.

Best owner abstraction:
- the recursive source-facing trajectory `constantStepSchemeII` for Proposition 2.11 itself;
- `OptimalMethodRecurrence` only as upstream bridge/provenance for the eliminated auxiliary
  parameters.

Primitive data:
- the recursive trajectory `constantStepSchemeII` together with
  `constantStepSchemeIIAlpha_succ_equation` and `constantStepSchemeIIY_succ`.

Derived API:
- the textbook coefficient `β_k`;
- the derivation from the heavier optimal-method owner via `y_eq` and
  `gamma_succ_eq_L_mul_sq`.

Source/core/bridge triage:
- source-facing: Proposition 2.11's displayed type-II scalar and momentum formulas;
- core/canonical: `ConstantStepSchemeIIMomentumRecurrence`;
- bridge/view: `constantStepSchemeIIToMomentumRecurrence`, together with elimination of the
  heavier optimal-method fields `v`, `γ` via `y_eq` and `gamma_succ_eq_L_mul_sq`.

This file therefore recalls the source-facing Algorithm 2.4 theorems directly. The generic
momentum owner remains background provenance available through
`constantStepSchemeIIToMomentumRecurrence`, but the main labeled entry stays on the textbook
recursive trajectory. This file intentionally adds no local
`estimatingSequenceMomentumCoefficient` wrapper and no parallel proposition-specific momentum
theorem. -/

recall constantStepSchemeIIAlpha_succ_equation
recall constantStepSchemeIIY_succ

/-! ### Text_2_11 (from Chap02) -/
open scoped Gradient MatrixOrder SmoothConvex

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "p" => normSeminorm ℝ E

/- Primary domain: Euclidean smooth convex objectives.

Source/core/bridge triage:
* source-facing: the hard instance `quadraticHardInstanceFamily (L : ℝ) k`;
  together with the textbook Hessian sandwich
  `0 ≤ ∇² (quadraticHardInstanceFamily (L : ℝ) k) x ≤ L • 1`;
* core/canonical: `quadraticHardInstanceFamily (L : ℝ) k ∈ 𝓕[L, p]¹¹`;
* bridge/view: the Hessian-quadratic-form characterization
  `convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded`.

Relevant owner-style declarations sampled in this domain:
* `quadraticHardInstanceFamily` in `Definition_2_10`;
* `quadraticObjective` and `quadraticObjective_gradient_eq` in `Definition_1_9_1` /
  `Proposition_1_5_7`;
* `convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded` in `Theorem_2_6`;
* `hessianMatrix_toEuclideanLin` and
  `fderiv_gradient_isSymmetric_of_contDiffAt` in Chapter 1 Hessian API.

Primitive data:
- the hard instance `quadraticHardInstanceFamily (L : ℝ) k : E → ℝ`.

Derived API:
- the source-facing Hessian quadratic-form and Loewner bounds of Text 2.11;
- the canonical owner-membership corollary
  `quadraticHardInstanceFamily (L : ℝ) k ∈ 𝓕[L, p]¹¹`;
- convexity and Euclidean `L`-Lipschitz continuity of the gradient as owner-derived
  consequences.
-/

private theorem quadraticObjective_contDiff
    {m : ℕ} (α : ℝ) (a : EuclideanSpace ℝ (Fin m))
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsSymm) :
    ContDiff ℝ 2 (quadraticObjective α a A) := by
  obtain ⟨hcontDiff, _⟩ :=
    symmetric_quadratic_contDiff_and_gradient_lipschitz α a A hA
  rw [show (2 : WithTop ℕ∞) = (1 : ℕ) + 1 by norm_num, contDiff_succ_iff_hasFDerivAt]
  refine ⟨fun x ↦ innerSL ℝ (a + A.toEuclideanLin x), ?_, ?_⟩
  · have hAffine :
        ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin m) ↦ a + A.toEuclideanLin x) := by
      simpa [Pi.add_apply, add_assoc, add_comm, add_left_comm] using
        contDiff_const.add
          (ContinuousLinearMap.contDiff A.toEuclideanLin.toContinuousLinearMap)
    exact (innerSL ℝ).contDiff.comp hAffine
  · intro x
    have hgrad :
        HasGradientAt (quadraticObjective α a A) (∇ (quadraticObjective α a A) x) x :=
      (hcontDiff.contDiffAt.differentiableAt one_ne_zero).hasGradientAt
    rw [quadraticObjective_gradient_eq α a A hA] at hgrad
    simpa using hgrad.hasFDerivAt

private theorem smoothLowerBoundFunction_contDiff (L : ℝ) (k : ℕ+) :
    ContDiff ℝ 2 (smoothLowerBoundFunction L k) := by
  unfold smoothLowerBoundFunction
  simpa using
    quadraticObjective_contDiff 0
      (-(L / 4) • EuclideanSpace.single (0 : Fin k) (1 : ℝ))
      ((L / 4) • pathTridiagonalMatrix k)
      ((pathTridiagonalMatrix_isSymm k).smul (L / 4))

private def hardInstancePrefix (k : Fin n) (x : E) :
    EuclideanSpace ℝ (Fin (k.1 + 1)) :=
  (EuclideanSpace.equiv (Fin (k.1 + 1)) ℝ).symm
    (fun i ↦ x (Fin.castLE (Nat.succ_le_of_lt k.2) i))

/-- Helper for Text 2.11: the prefix restriction is the continuous linear map that keeps the
first `k.1 + 1` coordinates. -/
private def hardInstancePrefixLinear (k : Fin n) :
    E →L[ℝ] EuclideanSpace ℝ (Fin (k.1 + 1)) :=
  ((EuclideanSpace.equiv (Fin (k.1 + 1)) ℝ).symm.toContinuousLinearEquiv :
      (Fin (k.1 + 1) → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (k.1 + 1))).toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun i : Fin (k.1 + 1) =>
        (ContinuousLinearMap.proj (R := ℝ)
          (i := Fin.castLE (Nat.succ_le_of_lt k.2) i) :
            (Fin n → ℝ) →L[ℝ] ℝ)).comp
      ((EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearEquiv.toContinuousLinearMap))

/-- Helper for Text 2.11: the linear prefix map evaluates to the same coordinates as the
source-facing prefix restriction. -/
private theorem hardInstancePrefix_eq_linear_apply (k : Fin n) (x : E) :
    hardInstancePrefixLinear k x = hardInstancePrefix k x := by
  ext i
  simp [hardInstancePrefixLinear, hardInstancePrefix]

private theorem hardInstancePrefix_contDiff (k : Fin n) :
    ContDiff ℝ 2 (hardInstancePrefix k) := by
  -- Use the continuous linear prefix map, then return to the source-facing definition.
  simpa [funext (hardInstancePrefix_eq_linear_apply k)] using
    ContinuousLinearMap.contDiff (hardInstancePrefixLinear k)

/-- Helper for Text 2.11: a `C²` scalar field has a differentiable gradient. -/
private theorem differentiableAt_gradient_of_contDiffAt_two
    {m : Type*} [NormedAddCommGroup m] [InnerProductSpace ℝ m] [CompleteSpace m]
    {f : m → ℝ} {x : m} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (∇ f) x := by
  let D : StrongDual ℝ m →L[ℝ] m :=
    (InnerProductSpace.toDual ℝ m).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    exact
      (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  -- Rewrite the gradient through the Riesz map so the chain rule applies directly.
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ f y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Text 2.11: precomposing a differentiable scalar field with a continuous linear map
pulls back its gradient by the adjoint. -/
private theorem hasGradientAt_comp_continuousLinearMap
    {m : Type*} [NormedAddCommGroup m] [InnerProductSpace ℝ m] [CompleteSpace m]
    {f : m → ℝ} (A : E →L[ℝ] m) {x : E}
    (hf : DifferentiableAt ℝ f (A x)) :
    HasGradientAt (f ∘ A) (A.adjoint (∇ f (A x))) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hcomp := (hf.hasGradientAt.hasFDerivAt).comp x A.hasFDerivAt
  convert hcomp using 1
  ext y
  calc
    inner ℝ (A.adjoint (∇ f (A x))) y = inner ℝ y (A.adjoint (∇ f (A x))) := by
      rw [real_inner_comm]
    _ = inner ℝ (A y) (∇ f (A x)) := A.adjoint_inner_right y (∇ f (A x))
    _ = inner ℝ (∇ f (A x)) (A y) := by
      rw [real_inner_comm]

/-- Helper for Text 2.11: precomposing by a continuous linear map transports the Hessian
quadratic form to the image direction. -/
private theorem hessian_quadratic_form_comp_continuousLinearMap
    {m : Type*} [NormedAddCommGroup m] [InnerProductSpace ℝ m] [CompleteSpace m]
    {f : m → ℝ} (A : E →L[ℝ] m) (hf : ContDiff ℝ 2 f) (x h : E) :
    inner ℝ (hessian (f ∘ A) x h) h =
      inner ℝ (hessian f (A x) (A h)) (A h) := by
  have hgradEq :
      ∇ (f ∘ A) = fun y : E ↦ A.adjoint (∇ f (A y)) := by
    refine gradient_eq ?_
    intro y
    exact hasGradientAt_comp_continuousLinearMap A
      (hf.contDiffAt.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0))
  have hgradDiff : DifferentiableAt ℝ (∇ f) (A x) :=
    differentiableAt_gradient_of_contDiffAt_two hf.contDiffAt
  have hinner :
      HasFDerivAt (fun y : E ↦ ∇ f (A y)) ((hessian f (A x)).comp A) x := by
    -- Differentiate the gradient after the linear prefix map.
    change HasFDerivAt (∇ f ∘ A) ((hessian f (A x)).comp A) x
    exact hgradDiff.hasFDerivAt.comp x A.hasFDerivAt
  have houter :
      HasFDerivAt (fun y : E ↦ A.adjoint (∇ f (A y)))
        ((A.adjoint).comp ((hessian f (A x)).comp A)) x := by
    -- The adjoint itself is linear, so its derivative is constant.
    exact A.adjoint.hasFDerivAt.comp x hinner
  have hderivEq :
      fderiv ℝ (fun y : E ↦ A.adjoint (∇ f (A y))) x =
        (A.adjoint).comp ((hessian f (A x)).comp A) := houter.fderiv
  -- Replace the pulled-back gradient by its derivative formula.
  suffices hmain :
      inner ℝ ((A.adjoint) ((hessian f (A x)).comp A h)) h =
        inner ℝ (hessian f (A x) (A h)) (A h) by
    simpa [hessian, hgradEq, hderivEq] using hmain
  calc
    inner ℝ ((A.adjoint) ((hessian f (A x)).comp A h)) h =
        inner ℝ h ((A.adjoint) ((hessian f (A x)).comp A h)) := by
          rw [real_inner_comm]
    _ = inner ℝ (A h) ((hessian f (A x)).comp A h) :=
        A.adjoint_inner_right h ((hessian f (A x)).comp A h)
    _ = inner ℝ (hessian f (A x) (A h)) (A h) := by
          rw [ContinuousLinearMap.comp_apply, real_inner_comm]

private theorem quadraticHardInstanceFamily_contDiff (L : NNReal) (k : Fin n) :
    ContDiff ℝ 2 (quadraticHardInstanceFamily (L : ℝ) k) := by
  unfold quadraticHardInstanceFamily
  exact
    (smoothLowerBoundFunction_contDiff (L : ℝ) (Nat.succPNat k.1)).comp
      (hardInstancePrefix_contDiff k)

/-- Helper for Text 2.11: the Euclidean inner product with the prefix tridiagonal matrix agrees
with the corresponding coordinate `dotProduct`. -/
private theorem pathTridiagonal_inner_eq_dotProduct_mulVec_prefix
    (k : Fin n) (y : EuclideanSpace ℝ (Fin (k.1 + 1))) :
    inner ℝ (((pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin y)) y =
      dotProduct y (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k.1)) y) := by
  -- Rewrite the Euclidean inner product as the coordinate dot product used by `Matrix.mulVec`.
  calc
    inner ℝ (((pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin y)) y =
        dotProduct y (((pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin y)) := by
          simpa [dotProduct_comm] using
            (EuclideanSpace.inner_eq_star_dotProduct
              (((pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin y)) y)
    _ = dotProduct y (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k.1)) y) := by
          rw [Matrix.toEuclideanLin_apply]
          rfl

/-- Helper for Text 2.11: each tridiagonal entry contributes its diagonal term and subtracts its
two possible neighboring terms. -/
private theorem pathTridiagonal_entry_mul_eq_diag_sub_neighbors
    {m : ℕ} (y : EuclideanSpace ℝ (Fin (m + 1))) (i j : Fin (m + 1)) :
    pathTridiagonalMatrix (Nat.succPNat m) i j * y j =
      (if i = j then 2 * y j else 0) -
      (if (i : ℕ) + 1 = (j : ℕ) then y j else 0) -
      (if (j : ℕ) + 1 = (i : ℕ) then y j else 0) := by
  -- Split the matrix entry into the diagonal, forward-edge, and backward-edge cases.
  by_cases hij : i = j
  · subst hij
    simp [pathTridiagonalMatrix_apply]
  · by_cases hnext : (i : ℕ) + 1 = (j : ℕ)
    · have hprev : ¬(j : ℕ) + 1 = (i : ℕ) := by
        omega
      simp [pathTridiagonalMatrix_apply, hij, hnext, hprev]
    · by_cases hprev : (j : ℕ) + 1 = (i : ℕ)
      · simp [pathTridiagonalMatrix_apply, hij, hnext, hprev]
      · simp [pathTridiagonalMatrix_apply, hij, hnext, hprev]

/-- Helper for Text 2.11: the diagonal part of the tridiagonal quadratic form is exactly
`2 * ∑ y_i^2`. -/
private theorem pathTridiagonal_diag_sum
    {m : ℕ} (y : EuclideanSpace ℝ (Fin (m + 1))) :
    (∑ x : Fin (m + 1), y x * ∑ x1 : Fin (m + 1), if x = x1 then 2 * y x1 else 0) =
      2 * ∑ x : Fin (m + 1), y x ^ 2 := by
  -- Only the diagonal entry survives in each inner sum, so the result is twice the square sum.
  simp [pow_two]
  ring_nf
  rw [Finset.sum_mul]

/-- Helper for Text 2.11: the forward off-diagonal contribution is the chain sum
`∑ y_i y_{i+1}`. -/
private theorem pathTridiagonal_forward_sum
    {m : ℕ} (y : EuclideanSpace ℝ (Fin (m + 1))) :
    (∑ x : Fin (m + 1), y x * ∑ x1 : Fin (m + 1),
      if (x : ℕ) + 1 = (x1 : ℕ) then y x1 else 0) =
      ∑ i : Fin m, y (Fin.castLE (Nat.le_succ m) i) * y i.succ := by
  -- Split off the last coordinate, whose forward neighbor does not exist, and identify the
  -- remaining inner sums with the successor coordinates.
  rw [Fin.sum_univ_castSucc]
  have hlast :
      (∑ x1 : Fin (m + 1), if ↑(Fin.last m) + 1 = (x1 : ℕ) then y x1 else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x hx
    have hEq : ¬m + 1 = (x : ℕ) := (Nat.ne_of_lt x.2).symm
    simp [Fin.val_last, hEq]
  rw [hlast, mul_zero, add_zero]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hinner :
      (∑ x1 : Fin (m + 1), if ↑x.castSucc + 1 = (x1 : ℕ) then y x1 else 0) = y x.succ := by
    rw [Fintype.sum_eq_single x.succ]
    · simp
    · intro z hz
      by_cases hEq : ↑x + 1 = (z : ℕ)
      · exfalso
        apply hz
        ext
        simpa using hEq.symm
      · simp [hEq]
  rw [hinner]
  congr 1

/-- Helper for Text 2.11: the backward off-diagonal contribution is the same chain sum
`∑ y_i y_{i+1}`. -/
private theorem pathTridiagonal_backward_sum
    {m : ℕ} (y : EuclideanSpace ℝ (Fin (m + 1))) :
    (∑ x : Fin (m + 1), y x * ∑ x1 : Fin (m + 1),
      if (x1 : ℕ) + 1 = (x : ℕ) then y x1 else 0) =
      ∑ i : Fin m, y (Fin.castLE (Nat.le_succ m) i) * y i.succ := by
  -- Split off the first coordinate, whose backward neighbor does not exist, and match each
  -- remaining inner sum with the predecessor coordinate.
  rw [Fin.sum_univ_succ]
  -- The head contribution vanishes because no index precedes `0`.
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.add_eq_zero_iff, Fin.val_eq_zero_iff,
    one_ne_zero, and_false, ↓reduceIte, Finset.sum_const_zero, mul_zero, Fin.val_succ,
    Nat.add_right_cancel_iff, zero_add]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hinner :
      (∑ x1 : Fin (m + 1), if (x1 : ℕ) = x then y x1 else 0) = y x.castSucc := by
    rw [Fintype.sum_eq_single x.castSucc]
    · simp
    · intro z hz
      by_cases hEq : (z : ℕ) = x
      · exfalso
        apply hz
        ext
        simpa using hEq
      · simp [hEq]
  rw [hinner]
  simpa [show y (Fin.castLE (Nat.le_succ m) x) = y x.castSucc by rfl] using
    (mul_comm (y x.castSucc) (y x.succ)).symm

/-- Helper for Text 2.11: the path tridiagonal quadratic form has the normal form
`2 * ∑ y_i^2 - 2 * ∑ y_i y_{i+1}` on the active prefix coordinates. -/
private theorem pathTridiagonal_dotProduct_eq_normal_form
    (k : Fin n) (y : EuclideanSpace ℝ (Fin (k.1 + 1))) :
    dotProduct y (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k.1)) y) =
      2 * (∑ i : Fin (k.1 + 1), y i ^ 2) -
        2 * ∑ i : Fin k.1, y (Fin.castLE (Nat.le_succ k.1) i) * y i.succ := by
  -- Expand each tridiagonal entry into one diagonal and two neighboring contributions, then
  -- evaluate those three sums separately.
  calc
    dotProduct y (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k.1)) y) =
        ∑ x : Fin (k.1 + 1), y x * ∑ x1 : Fin (k.1 + 1),
          pathTridiagonalMatrix (Nat.succPNat k.1) x x1 * y x1 := rfl
    _ = ∑ x : Fin (k.1 + 1), y x *
          ∑ x1 : Fin (k.1 + 1),
            ((if x = x1 then 2 * y x1 else 0) -
              (if (x : ℕ) + 1 = (x1 : ℕ) then y x1 else 0) -
              (if (x1 : ℕ) + 1 = (x : ℕ) then y x1 else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          congr 1
          refine Finset.sum_congr rfl ?_
          intro x1 hx1
          rw [pathTridiagonal_entry_mul_eq_diag_sub_neighbors y x x1]
    _ = ∑ x : Fin (k.1 + 1),
          ((y x * ∑ x1 : Fin (k.1 + 1), if x = x1 then 2 * y x1 else 0) -
            (y x * ∑ x1 : Fin (k.1 + 1), if (x : ℕ) + 1 = (x1 : ℕ) then y x1 else 0) -
            (y x * ∑ x1 : Fin (k.1 + 1), if (x1 : ℕ) + 1 = (x : ℕ) then y x1 else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
          ring
    _ = (∑ x : Fin (k.1 + 1), y x * ∑ x1 : Fin (k.1 + 1), if x = x1 then 2 * y x1 else 0) -
          (∑ x : Fin (k.1 + 1), y x * ∑ x1 : Fin (k.1 + 1),
            if (x : ℕ) + 1 = (x1 : ℕ) then y x1 else 0) -
          (∑ x : Fin (k.1 + 1), y x * ∑ x1 : Fin (k.1 + 1),
            if (x1 : ℕ) + 1 = (x : ℕ) then y x1 else 0) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ = 2 * (∑ i : Fin (k.1 + 1), y i ^ 2) -
          2 * ∑ i : Fin k.1, y (Fin.castLE (Nat.le_succ k.1) i) * y i.succ := by
          rw [pathTridiagonal_diag_sum, pathTridiagonal_forward_sum, pathTridiagonal_backward_sum]
          ring

/-- Helper for Text 2.11: the endpoint-plus-edge chain expression has the same normal form
`2 * ∑ y_i^2 - 2 * ∑ y_i y_{i+1}`. -/
private theorem chain_expression_eq_normal_form
    (k : Fin n) (y : EuclideanSpace ℝ (Fin (k.1 + 1))) :
    y 0 ^ 2 +
      (∑ i : Fin k.1, (y (Fin.castLE (Nat.le_succ k.1) i) - y i.succ) ^ 2) +
      y (Fin.last k.1) ^ 2 =
        2 * (∑ i : Fin (k.1 + 1), y i ^ 2) -
          2 * ∑ i : Fin k.1, y (Fin.castLE (Nat.le_succ k.1) i) * y i.succ := by
  -- Expand the edge squares, then rewrite the full prefix square sum once from the left endpoint
  -- and once from the right endpoint.
  have hcast_eq :
      (∑ i : Fin (k.1 + 1), y i ^ 2) =
        (∑ i : Fin k.1, (y (Fin.castLE (Nat.le_succ k.1) i)) ^ 2) + (y (Fin.last k.1)) ^ 2 := by
    calc
      (∑ i : Fin (k.1 + 1), y i ^ 2) =
          (∑ i : Fin k.1, y i.castSucc ^ 2) + (y (Fin.last k.1)) ^ 2 := by
            rw [Fin.sum_univ_castSucc]
      _ = (∑ i : Fin k.1, (y (Fin.castLE (Nat.le_succ k.1) i)) ^ 2) +
            (y (Fin.last k.1)) ^ 2 := by
            congr 1
  have hsucc_eq :
      (∑ i : Fin (k.1 + 1), y i ^ 2) =
        (y 0) ^ 2 + (∑ i : Fin k.1, (y i.succ) ^ 2) := by
    rw [Fin.sum_univ_succ]
  have hexpand :
      (∑ i : Fin k.1, (y (Fin.castLE (Nat.le_succ k.1) i) - y i.succ) ^ 2) =
        (∑ i : Fin k.1, ((y (Fin.castLE (Nat.le_succ k.1) i)) ^ 2 -
          2 * (y (Fin.castLE (Nat.le_succ k.1) i) * y i.succ) + (y i.succ) ^ 2)) := by
    -- Rewrite each edge square into the standard quadratic normal form.
    refine Finset.sum_congr rfl ?_
    intro i hi
    ring
  have hsum_expand :
      (∑ i : Fin k.1, ((y (Fin.castLE (Nat.le_succ k.1) i)) ^ 2 -
        2 * (y (Fin.castLE (Nat.le_succ k.1) i) * y i.succ) + (y i.succ) ^ 2)) =
        (∑ i : Fin k.1, (y (Fin.castLE (Nat.le_succ k.1) i)) ^ 2) -
          2 * (∑ i : Fin k.1, y (Fin.castLE (Nat.le_succ k.1) i) * y i.succ) +
          (∑ i : Fin k.1, (y i.succ) ^ 2) := by
    -- Separate the square, cross, and successor-square sums before the final algebra step.
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  nlinarith [hcast_eq, hsucc_eq, hexpand, hsum_expand]

/-- Helper for Text 2.11: on the active prefix coordinates, the path tridiagonal quadratic form is
exactly the endpoint-plus-edge chain expression from LecturesConvexOptimization_Nesterov_2018's proof. -/
private theorem pathTridiagonal_quadratic_form_eq_chain_prefix
    (k : Fin n) (y : EuclideanSpace ℝ (Fin (k.1 + 1))) :
    inner ℝ (((pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin y)) y =
      y 0 ^ 2 +
        (∑ i : Fin k.1, (y (Fin.castLE (Nat.le_succ k.1) i) - y i.succ) ^ 2) +
        y (Fin.last k.1) ^ 2 := by
  -- Route correction: move the algebraic core to the native prefix space, where both sides share
  -- the same normal form.
  calc
    inner ℝ (((pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin y)) y =
        dotProduct y (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k.1)) y) := by
          rw [pathTridiagonal_inner_eq_dotProduct_mulVec_prefix]
    _ = 2 * (∑ i : Fin (k.1 + 1), y i ^ 2) -
          2 * ∑ i : Fin k.1, y (Fin.castLE (Nat.le_succ k.1) i) * y i.succ := by
          rw [pathTridiagonal_dotProduct_eq_normal_form]
    _ = y 0 ^ 2 +
          (∑ i : Fin k.1, (y (Fin.castLE (Nat.le_succ k.1) i) - y i.succ) ^ 2) +
          y (Fin.last k.1) ^ 2 := by
          symm
          rw [chain_expression_eq_normal_form]

/-- Helper for Text 2.11: the quadratic form of the path tridiagonal matrix on the prefix
coordinates is exactly LecturesConvexOptimization_Nesterov_2018's endpoint-plus-edge chain form. -/
private theorem pathTridiagonal_quadratic_form_eq_chain
    (k : Fin n) (h : E) :
    inner ℝ
      (((pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin (hardInstancePrefix k h)))
      (hardInstancePrefix k h) =
        nesterovChainQuadraticForm k h := by
  -- Instantiate the native-prefix identity at the restricted vector `hardInstancePrefix k h`.
  simpa [nesterovChainQuadraticForm, hardInstancePrefix] using
    pathTridiagonal_quadratic_form_eq_chain_prefix k (hardInstancePrefix k h)

/-- Helper for Text 2.11: the Hessian quadratic form of the hard instance is the source-facing
chain expression from the textbook proof. -/
private theorem quadraticHardInstanceFamily_hessian_chain_formula
    (L : NNReal) (k : Fin n) (x h : E) :
    inner ℝ (hessian (quadraticHardInstanceFamily (L : ℝ) k) x h) h =
      ((L : ℝ) / 4) * nesterovChainQuadraticForm k h := by
  -- Route correction: Proposition 2.2 now exports the owner bridge only after the explicit chain
  -- formula is supplied, so Text 2.11 has to establish that source-facing identity first.
  have hcomp :=
    hessian_quadratic_form_comp_continuousLinearMap
      (hardInstancePrefixLinear k)
      (smoothLowerBoundFunction_contDiff (L : ℝ) (Nat.succPNat k.1))
      x h
  have hhess :
      (hessian (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat k.1))
          (hardInstancePrefix k x) : _ →ₗ[ℝ] _) =
        (((((L : ℝ) / 4) • pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin) :
          _ →ₗ[ℝ] _) := by
    calc
      (hessian (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat k.1))
          (hardInstancePrefix k x) : _ →ₗ[ℝ] _) =
          (∇² (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat k.1))
            (hardInstancePrefix k x)).toEuclideanLin := by
              symm
              simpa using
                hessianMatrix_toEuclideanLin
                  (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat k.1))
                  (hardInstancePrefix k x)
      _ = (((((L : ℝ) / 4) • pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin) :
            _ →ₗ[ℝ] _) := by
              rw [smoothLowerBoundFunction_hessian_eq_tridiagonal]
  have hhess_apply :
      hessian (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat k.1))
          (hardInstancePrefix k x) (hardInstancePrefixLinear k h) =
        ((((L : ℝ) / 4) • pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin)
          (hardInstancePrefixLinear k h) := by
    exact
      congrArg
        (fun T :
          EuclideanSpace ℝ (Fin (k.1 + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (k.1 + 1)) ↦
            T (hardInstancePrefixLinear k h))
        hhess
  have hscale :
      ((((L : ℝ) / 4) • pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin
        (hardInstancePrefixLinear k h)) =
          ((L : ℝ) / 4) •
            (((pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin)
              (hardInstancePrefixLinear k h)) := by
    rw [Matrix.toEuclideanLin_apply, Matrix.toEuclideanLin_apply, Matrix.smul_mulVec,
      WithLp.toLp_smul]
  -- First transport the Hessian quadratic form through the prefix map, then identify the constant
  -- tridiagonal Hessian operator and finally rewrite it into the chain expression.
  calc
    inner ℝ (hessian (quadraticHardInstanceFamily (L : ℝ) k) x h) h =
        inner ℝ
          (hessian (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat k.1))
            (hardInstancePrefix k x) (hardInstancePrefixLinear k h))
          (hardInstancePrefixLinear k h) := by
            simpa [quadraticHardInstanceFamily, hardInstancePrefix_eq_linear_apply] using hcomp
    _ = inner ℝ
          ((((L : ℝ) / 4) • pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin
            (hardInstancePrefixLinear k h))
          (hardInstancePrefixLinear k h) := by
            rw [hhess_apply]
    _ = ((L : ℝ) / 4) * inner ℝ
          (((pathTridiagonalMatrix (Nat.succPNat k.1)).toEuclideanLin)
            (hardInstancePrefixLinear k h))
          (hardInstancePrefixLinear k h) := by
            rw [hscale]
            rw [real_inner_smul_left]
    _ = ((L : ℝ) / 4) * nesterovChainQuadraticForm k h := by
            simpa [hardInstancePrefix_eq_linear_apply] using
              congrArg (((L : ℝ) / 4) * ·) (pathTridiagonal_quadratic_form_eq_chain k h)

/-- Companion quadratic-form version of Text 2.11: the hard instance Hessian is nonnegative and
bounded above by `L` in every Euclidean direction. -/
theorem quadraticHardInstanceFamily_hessian_quadratic_form_bounded
    (L : NNReal) (k : Fin n) (x h : E) :
    0 ≤ inner ℝ (hessian (quadraticHardInstanceFamily (L : ℝ) k) x h) h ∧
      inner ℝ (hessian (quadraticHardInstanceFamily (L : ℝ) k) x h) h ≤
        (L : ℝ) * ‖h‖ ^ (2 : ℕ) := by
  have hEq := quadraticHardInstanceFamily_hessian_chain_formula L k x h
  constructor
  · -- The chain quadratic form is a sum of squares.
    nlinarith [L.2, hEq, nesterovChainQuadraticForm_nonneg k h]
  · -- Proposition 2.2 bounds the chain form by `4 ‖h‖²`, which matches the Hessian scaling.
    nlinarith [L.2, hEq, nesterovChainQuadraticForm_le_four_mul_norm_sq k h]

/-- Text 2.11: for every `k : Fin n`, representing the textbook index
`k.1 + 1 ∈ {1, ..., n}`, the Hessian matrix of the hard instance `f_k` satisfies
`0 ≤ ∇² f_k(x) ≤ L I_n` for every `x ∈ ℝⁿ`. -/
theorem quadraticHardInstanceFamily_hessian_loewner_bounds
    (L : NNReal) (k : Fin n) (x : E) :
    0 ≤ ∇² (quadraticHardInstanceFamily (L : ℝ) k) x ∧
      ∇² (quadraticHardInstanceFamily (L : ℝ) k) x ≤ (L : ℝ) • (1 : Mat) := by
  let f : E → ℝ := quadraticHardInstanceFamily (L : ℝ) k
  have hcont : ContDiff ℝ 2 f := by
    simpa [f] using quadraticHardInstanceFamily_contDiff L k
  have hquad :
      ∀ h : E,
        0 ≤ inner ℝ (hessian f x h) h ∧
          inner ℝ (hessian f x h) h ≤ (L : ℝ) * ‖h‖ ^ (2 : ℕ) := by
    intro h
    simpa [f] using quadraticHardInstanceFamily_hessian_quadratic_form_bounded L k x h
  constructor
  · rw [Matrix.nonneg_iff_posSemidef, ← Matrix.isPositive_toEuclideanLin_iff]
    rw [LinearMap.isPositive_iff, hessianMatrix_toEuclideanLin]
    constructor
    · simpa [f] using fderiv_gradient_isSymmetric_of_contDiffAt hcont.contDiffAt
    · intro h
      exact (hquad h).1
  · refine sub_nonneg.mp ?_
    rw [Matrix.nonneg_iff_posSemidef, ← Matrix.isPositive_toEuclideanLin_iff]
    have hpos :
        (((L : ℝ) • (1 : E →L[ℝ] E) - hessian f x) : E →ₗ[ℝ] E).IsPositive := by
      rw [LinearMap.isPositive_iff]
      constructor
      · exact
          (LinearMap.isPositive_one.smul_of_nonneg L.2).isSymmetric.sub
            (fderiv_gradient_isSymmetric_of_contDiffAt hcont.contDiffAt)
      · intro h
        have hh' : 0 ≤ (L : ℝ) * ‖h‖ ^ (2 : ℕ) - inner ℝ (hessian f x h) h := by
          linarith [(hquad h).2]
        simpa [inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K] using hh'
    have hbridge :
        (((L : ℝ) • (1 : Mat) - ∇² f x).toEuclideanLin : E →ₗ[ℝ] E) =
          (((L : ℝ) • (1 : E →L[ℝ] E) - hessian f x) : E →ₗ[ℝ] E) := by
      calc
        (((L : ℝ) • (1 : Mat) - ∇² f x).toEuclideanLin : E →ₗ[ℝ] E) =
            (L : ℝ) • LinearMap.id - ((∇² f x).toEuclideanLin : E →ₗ[ℝ] E) := by
              simp
        _ = (L : ℝ) • LinearMap.id - (hessian f x : E →ₗ[ℝ] E) := by
              rw [hessianMatrix_toEuclideanLin]
        _ = (((L : ℝ) • (1 : E →L[ℝ] E) - hessian f x) : E →ₗ[ℝ] E) := by
              ext z
              simp
    rw [hbridge]
    exact hpos

/-- Text 2.11 in canonical owner form: the hard instance `f_k` satisfies the chapter owner
predicate `𝓕_L^{1,1}(ℝⁿ)`, so its convexity and Euclidean `L`-Lipschitz gradient are available
from the canonical smooth-convex API. -/
theorem quadraticHardInstanceFamily_mem_smooth_convex_objective
    (L : NNReal) (k : Fin n) :
    quadraticHardInstanceFamily (L : ℝ) k ∈ 𝓕[L, p]¹¹ := by
  let f : E → ℝ := quadraticHardInstanceFamily (L : ℝ) k
  have hcont : ContDiff ℝ 2 f := by
    simpa [f] using quadraticHardInstanceFamily_contDiff L k
  refine (convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded hcont).2 ?_
  intro x h
  simpa [f] using quadraticHardInstanceFamily_hessian_quadratic_form_bounded L k x h

/-! ### Theorem_2_11 (from Chap02) -/
open scoped Gradient SeminormDualNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Primary domain: first-order consequences of strong convexity on real inner-product spaces, with
the later dual-norm bounds living on the finite-dimensional separated-seminorm layer.

Sampled owner-style declarations before refining this file:
* mathlib `StrongConvexOn`
* project `StrongConvexOnWith` in `Definition_2_14`
* project `StrongConvexOnWith.lower_tangent_quadratic_of_hasGradientAt` in `Definition_2_14`
* project `Seminorm.inner_le_dualNorm_mul` in `Definition_2_5`

Source/core/bridge triage:
* source-facing: the three displayed inequalities of Theorem 2.11
* core/canonical: `StrongConvexOnWith p μ Set.univ f`
* bridge/view: `StrongConvexOnWith.lower_tangent_quadratic_of_hasGradientAt` and the
  finite-dimensional dual pairing estimate `Seminorm.inner_le_dualNorm_mul`

Primitive data:
* `hf_strong : StrongConvexOnWith p μ Set.univ f`
* local pointwise differentiability / gradient witnesses at the evaluation points `x` and `y`
* only for the later dual-norm inequalities: the finite-dimensional real inner-product-space
  structure and the separation hypothesis `[Seminorm.IsNorm p]`

Derived API:
* `hf_strong.lower_tangent_quadratic_of_hasGradientAt`
* `DifferentiableAt.hasGradientAt`
* the strong-monotonicity pairing estimate obtained by adding the lower-tangent inequalities at
  `(x, y)` and `(y, x)`
* `Seminorm.inner_le_dualNorm_mul` for the later dual-norm comparisons
-/

namespace StrongConvexOnWith

section Pairing

variable [CompleteSpace E]

variable {p : Seminorm ℝ E} {μ : ℝ} {f : E → ℝ}

/-- Strong convexity with respect to `p` forces the gradient pairing to dominate `μ` times the
squared `p`-distance. This is the core bridge behind the displayed dual-norm consequences below.
-/
-- Proof sketch: apply `lower_tangent_quadratic_of_hasGradientAt` at `(x, y)` and `(y, x)`, add the
-- two inequalities, and simplify the linear terms.
theorem pairing_lower_bound
    (hf_strong : StrongConvexOnWith p μ Set.univ f)
    (x y : E) (hx : DifferentiableAt ℝ f x) (hy : DifferentiableAt ℝ f y) :
    μ * (p (x - y)) ^ 2 ≤ inner ℝ (∇ f x - ∇ f y) (x - y) := by
  -- Apply the lower tangent inequality at both endpoint orders.
  have hxy :=
    StrongConvexOnWith.lower_tangent_quadratic_of_hasGradientAt (hf := hf_strong)
      (x := x) (y := y) (g := ∇ f x) (by trivial) (by trivial) hx.hasGradientAt
  have hyx :=
    StrongConvexOnWith.lower_tangent_quadratic_of_hasGradientAt (hf := hf_strong)
      (x := y) (y := x) (g := ∇ f y) (by trivial) (by trivial) hy.hasGradientAt
  -- Rewrite the seminorm term from `p (y - x)` back to `p (x - y)` before adding.
  have hp_rev : p (y - x) = p (x - y) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (map_neg_eq_map p (x - y))
  rw [hp_rev] at hxy
  have hsum :
      μ * (p (x - y)) ^ 2 ≤
        -(inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f y) (x - y)) := by
    nlinarith [hxy, hyx]
  -- Rewrite the sum of the two linear terms as the single gradient pairing.
  have hpair :
      -(inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f y) (x - y)) =
        inner ℝ (∇ f x - ∇ f y) (x - y) := by
    calc
      -(inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f y) (x - y))
          = inner ℝ (∇ f x) (x - y) - inner ℝ (∇ f y) (x - y) := by
              have hxswap : inner ℝ (∇ f x) (y - x) = -inner ℝ (∇ f x) (x - y) := by
                have hvec : y - x = -(x - y) := by
                  abel
                rw [hvec, inner_neg_right]
              rw [hxswap]
              ring
      _ = inner ℝ (∇ f x - ∇ f y) (x - y) := by
            rw [inner_sub_left]
  -- The linear terms collapse to the single gradient pairing.
  rwa [hpair] at hsum

end Pairing

section DualNorm

variable [FiniteDimensional ℝ E]

local instance finiteDimensionalComplete : CompleteSpace E := FiniteDimensional.complete ℝ E

variable {p : Seminorm ℝ E} [Seminorm.IsNorm p] {μ : ℝ} {f : E → ℝ}

/-- Theorem 2.11 (1): if a `μ`-strongly convex function has gradients at `x` and `y`, then its
value at `y` is bounded above by the tangent model at `x` plus a quadratic term in the dual norm
of the gradient difference. Here strong convexity is the whole-space specialization
`StrongConvexOnWith p μ Set.univ f`. -/
-- Proof sketch: apply strong convexity to the translated function
-- `v ↦ f v - ⟪∇ f x, v⟫`, observe that `x` is its minimizer, and compute the optimal value of the
-- resulting quadratic lower bound using the dual norm.
theorem tangent_upper_bound_by_dualNorm
    (hf_strong : StrongConvexOnWith p μ Set.univ f)
    (x y : E) (_hx : DifferentiableAt ℝ f x) (hy : DifferentiableAt ℝ f y) :
    f y ≤ f x + inner ℝ (∇ f x) (y - x) +
      (1 / (2 * μ)) * ‖∇ f x - ∇ f y‖[p,*] ^ 2 := by
  have hμ : 0 < μ := hf_strong.2.1
  -- Start from the lower tangent inequality at base point `y`.
  have hlower :=
    StrongConvexOnWith.lower_tangent_quadratic_of_hasGradientAt (hf := hf_strong)
      (x := y) (y := x) (g := ∇ f y) (by trivial) (by trivial) hy.hasGradientAt
  -- Control the residual pairing by dual Cauchy.
  have hinner :
      inner ℝ (∇ f x - ∇ f y) (x - y) ≤
        ‖∇ f x - ∇ f y‖[p,*] * p (x - y) :=
    Seminorm.inner_le_dualNorm_mul p (x - y) (∇ f x - ∇ f y)
  let a : ℝ := ‖∇ f x - ∇ f y‖[p,*]
  let s : ℝ := p (x - y)
  -- Complete the square in the scalar variables `a` and `s`.
  have hsquare : 0 ≤ (a - μ * s) ^ 2 := sq_nonneg (a - μ * s)
  have htwoμ_pos : 0 < 2 * μ := by
    positivity
  have hscaled : (2 * μ) * (a * s - (μ / 2) * s ^ 2) ≤ a ^ 2 := by
    nlinarith [hsquare]
  have hscalar :
      a * s - (μ / 2) * s ^ 2 ≤ (1 / (2 * μ)) * a ^ 2 := by
    have htmp : a * s - (μ / 2) * s ^ 2 ≤ (2 * μ)⁻¹ * a ^ 2 :=
      (le_inv_mul_iff₀ htwoμ_pos).2 hscaled
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using htmp
  have hestimate :
      inner ℝ (∇ f x - ∇ f y) (x - y) - (μ / 2) * (p (x - y)) ^ 2 ≤
        (1 / (2 * μ)) * ‖∇ f x - ∇ f y‖[p,*] ^ 2 := by
    calc
      inner ℝ (∇ f x - ∇ f y) (x - y) - (μ / 2) * (p (x - y)) ^ 2
          ≤ ‖∇ f x - ∇ f y‖[p,*] * p (x - y) - (μ / 2) * (p (x - y)) ^ 2 := by
            linarith
      _ ≤ (1 / (2 * μ)) * ‖∇ f x - ∇ f y‖[p,*] ^ 2 := by
            simpa [a, s] using hscalar
  have hxswap : inner ℝ (∇ f x) (y - x) = -inner ℝ (∇ f x) (x - y) := by
    have hvec : y - x = -(x - y) := by
      abel
    rw [hvec, inner_neg_right]
  have hlin :
      inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f x - ∇ f y) (x - y) =
        -inner ℝ (∇ f y) (x - y) := by
    rw [inner_sub_left, hxswap]
    ring
  have hrew :
      f y ≤ f x + inner ℝ (∇ f x) (y - x) +
        (inner ℝ (∇ f x - ∇ f y) (x - y) - (μ / 2) * (p (x - y)) ^ 2) := by
    -- Rewrite the base-point gradient term from `∇ f y` to `∇ f x`.
    nlinarith [hlower, hlin]
  exact hrew.trans <| by
    gcongr

/-- Theorem 2.11 (2): the gradient pairing is bounded above by `μ⁻¹` times the squared dual norm
of the gradient difference. -/
-- Proof sketch: add the inequality from `tangent_upper_bound_by_dualNorm` to the same inequality
-- with `x` and `y` interchanged, then simplify the linear terms.
theorem gradient_pairing_le_dualNorm_sq
    (hf_strong : StrongConvexOnWith p μ Set.univ f)
    (x y : E) (hx : DifferentiableAt ℝ f x) (hy : DifferentiableAt ℝ f y) :
    inner ℝ (∇ f x - ∇ f y) (x - y) ≤
      (1 / μ) * ‖∇ f x - ∇ f y‖[p,*] ^ 2 := by
  have hμ : 0 < μ := hf_strong.2.1
  -- Combine the strong lower pairing bound with dual Cauchy.
  have hlower := StrongConvexOnWith.pairing_lower_bound hf_strong x y hx hy
  have hupper :
      inner ℝ (∇ f x - ∇ f y) (x - y) ≤
        ‖∇ f x - ∇ f y‖[p,*] * p (x - y) :=
    Seminorm.inner_le_dualNorm_mul p (x - y) (∇ f x - ∇ f y)
  by_cases hxy : x = y
  · subst hxy
    have hzero : ‖(0 : E)‖[p,*] = 0 := by
      rw [Seminorm.dualNorm_apply]
      have himage :
          (fun a : E ↦ inner ℝ (0 : E) a) '' {x : E | p x ≤ 1} = ({0} : Set ℝ) := by
        ext t
        constructor
        · rintro ⟨z, -, rfl⟩
          simp
        · rintro rfl
          refine ⟨0, ?_, by simp⟩
          simp
      rw [himage]
      simp
    simp [hzero]
  · have hsub_ne : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hp_pos : 0 < p (x - y) := Seminorm.map_pos_of_ne_zero p hsub_ne
    have hsandwich :
        μ * (p (x - y)) ^ 2 ≤ ‖∇ f x - ∇ f y‖[p,*] * p (x - y) :=
      hlower.trans hupper
    have hgrad : μ * p (x - y) ≤ ‖∇ f x - ∇ f y‖[p,*] := by
      nlinarith [hsandwich, hp_pos]
    have hdual_nonneg : 0 ≤ ‖∇ f x - ∇ f y‖[p,*] := by
      nlinarith [hgrad, hμ, hp_pos]
    have hp_le :
        p (x - y) ≤ ‖∇ f x - ∇ f y‖[p,*] / μ := by
      refine (le_div_iff₀ hμ).2 ?_
      simpa [mul_comm] using hgrad
    have hnorm_mul :
        ‖∇ f x - ∇ f y‖[p,*] * p (x - y) ≤
          (1 / μ) * ‖∇ f x - ∇ f y‖[p,*] ^ 2 := by
      calc
        ‖∇ f x - ∇ f y‖[p,*] * p (x - y) ≤
            ‖∇ f x - ∇ f y‖[p,*] * (‖∇ f x - ∇ f y‖[p,*] / μ) := by
              exact mul_le_mul_of_nonneg_left hp_le hdual_nonneg
        _ = (1 / μ) * ‖∇ f x - ∇ f y‖[p,*] ^ 2 := by
              ring_nf
    -- Substitute the gradient-difference norm bound back into the upper pairing estimate.
    exact hupper.trans hnorm_mul

/-- Theorem 2.11 (3): the dual norm of the gradient difference dominates `μ` times the primal norm
of the displacement. -/
-- Proof sketch: combine `pairing_lower_bound` with the dual Cauchy--Schwarz inequality
-- `⟪g, z⟫ ≤ ‖g‖_* ‖z‖`, then cancel the common factor `p (x - y)`.
theorem le_dualNorm_gradient_sub
    (hf_strong : StrongConvexOnWith p μ Set.univ f)
    (x y : E) (hx : DifferentiableAt ℝ f x) (hy : DifferentiableAt ℝ f y) :
    μ * p (x - y) ≤ ‖∇ f x - ∇ f y‖[p,*] := by
  -- Sandwich the gradient pairing between the strong lower bound and dual Cauchy.
  have hlower := StrongConvexOnWith.pairing_lower_bound (hf_strong := hf_strong) x y hx hy
  have hupper :
      inner ℝ (∇ f x - ∇ f y) (x - y) ≤
        ‖∇ f x - ∇ f y‖[p,*] * p (x - y) :=
    Seminorm.inner_le_dualNorm_mul p (x - y) (∇ f x - ∇ f y)
  by_cases hxy : x = y
  · subst hxy
    have hzero : ‖(0 : E)‖[p,*] = 0 := by
      rw [Seminorm.dualNorm_apply]
      have himage :
          (fun a : E ↦ inner ℝ (0 : E) a) '' {x : E | p x ≤ 1} = ({0} : Set ℝ) := by
        ext t
        constructor
        · rintro ⟨z, -, rfl⟩
          simp
        · rintro rfl
          refine ⟨0, ?_, by simp⟩
          simp
      rw [himage]
      simp
    simp [hzero]
  · have hsub_ne : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hp_pos : 0 < p (x - y) := Seminorm.map_pos_of_ne_zero p hsub_ne
    have hsandwich :
        μ * (p (x - y)) ^ 2 ≤ ‖∇ f x - ∇ f y‖[p,*] * p (x - y) :=
      hlower.trans hupper
    -- Cancel the positive factor `p (x - y)` on both sides.
    nlinarith [hsandwich, hp_pos]

end DualNorm

end StrongConvexOnWith

end
