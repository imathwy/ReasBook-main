import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_20 (from Chap07) -/
noncomputable section

open Matrix
open scoped BigOperators RealSymmetricMatrixSpace

/- Definition 7.20 is a recall/bridge item in the symmetric-matrix Frobenius domain.

Layer targeted by this refinement:
- source-facing recall of the Chapter 5 Frobenius geometry on `𝕊^n`.

Primary domain:
- the Frobenius inner product and Frobenius norm on real symmetric matrices.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` in `Definition_5_4_4_1`, the project owner for real symmetric matrices;
- Chapter 5 `RealSymmetricMatrixSpace.frobeniusInner` in `Definition_5_4_4_2`, the project owner
  for the Frobenius pairing on `𝕊^n`;
- Chapter 5 `RealSymmetricMatrixSpace.norm_eq_sqrt_frobeniusInner`, the owner-level norm bridge;
- mathlib `Matrix.frobenius_norm_def`, the ambient matrix Frobenius norm formula.

Best owner abstraction:
- source-facing: the Frobenius inner product and associated norm on `𝕊^n`;
- core/canonical: the Chapter 5 owner `RealSymmetricMatrixSpace.frobeniusInner` together with the
  inherited norm `‖·‖` on `𝕊^n`;
- bridge/view: the entrywise double-sum realization of the Frobenius pairing.

Primitive data:
- `n : ℕ`
- `X Y : 𝕊^n`

Derived API:
- the owner pairing `⟪X, Y⟫_F`
- the inherited Frobenius norm `‖X‖`
- the owner theorem `RealSymmetricMatrixSpace.norm_eq_sqrt_frobeniusInner`

Source/core/bridge triage:
- source-facing: Definition 7.20's Frobenius geometry on symmetric matrices;
- core/canonical: `𝕊^n`, `⟪·, ·⟫_F`, and `‖·‖`;
- bridge/view: the entrywise-sum formula below.

This file removes the duplicate Chapter 7 wrapper names and reuses the existing Chapter 5 owner
directly. The only local theorem kept here is the source-facing entrywise realization of the
owner pairing. -/

section

variable (n : ℕ)

/- Definition 7.20: on `𝕊^n`, the Frobenius inner product is the Chapter 5 owner
`RealSymmetricMatrixSpace.frobeniusInner`. -/
#check (RealSymmetricMatrixSpace.frobeniusInner : 𝕊^n → 𝕊^n → ℝ)

/- The associated Frobenius norm on `𝕊^n` is the inherited norm, with source formula
`‖X‖ = sqrt ⟪X, X⟫_F` given by the Chapter 5 owner theorem. -/
#check (RealSymmetricMatrixSpace.norm_eq_sqrt_frobeniusInner :
  ∀ X : 𝕊^n, ‖X‖ = Real.sqrt ⟪X, X⟫_F)

end

/-- Expanding the Chapter 5 Frobenius pairing on `𝕊^n` gives the textbook entrywise double sum. -/
theorem frobeniusInner_eq_entrywise_sum
    {n : ℕ} (X Y : 𝕊^n) :
    ⟪X, Y⟫_F =
      ∑ i : Fin n, ∑ j : Fin n,
        ((X : Matrix (Fin n) (Fin n) ℝ) i j) * ((Y : Matrix (Fin n) (Fin n) ℝ) i j) := by
  rw [RealSymmetricMatrixSpace.frobeniusInner_def]
  calc
    Matrix.trace ((X : Matrix (Fin n) (Fin n) ℝ)ᵀ * (Y : Matrix (Fin n) (Fin n) ℝ)) =
        ∑ i : Fin n, (((X : Matrix (Fin n) (Fin n) ℝ)ᵀ * (Y : Matrix (Fin n) (Fin n) ℝ)) i i) := by
      rfl
    _ =
        ∑ i : Fin n, ∑ j : Fin n,
          ((X : Matrix (Fin n) (Fin n) ℝ) j i) * ((Y : Matrix (Fin n) (Fin n) ℝ) j i) := by
      simp [Matrix.mul_apply]
    _ = ∑ j : Fin n, ∑ i : Fin n,
          ((X : Matrix (Fin n) (Fin n) ℝ) j i) * ((Y : Matrix (Fin n) (Fin n) ℝ) j i) := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin n, ∑ j : Fin n,
          ((X : Matrix (Fin n) (Fin n) ℝ) i j) * ((Y : Matrix (Fin n) (Fin n) ℝ) i j) := by
      rfl

/-! ### Lemma_7_20 (from Chap07) -/
noncomputable section

open scoped WithTopConvexAnalysis

universe u

/-
Lemma 7.20 lies in the chapter's relative-scale subgradient-transform domain.

Sampled owner-style declarations:
- `StrictlyPositiveOn` and `StrictlyPositiveOn.inequality` in `Chap07/Definition_7_81`, the
  chapter's source-facing positivity owner and its atomic projection lemma;
- `subdifferentialWithin` and the notation `∂[Set.univ] f(x)` in `Chap03/Theorem_3_44`, the
  canonical real-valued whole-space subdifferential surface used by `StrictlyPositiveOn`;
- `IsSubgradientAt` in `Chap03/Definition_3_1_5`, the underlying extended-valued owner reused by
  that real-valued subdifferential surface.

Best owner abstraction:
- source-facing: the relative-scale transformed objective and transformed subgradient;
- core/canonical: the Chapter 7 positivity owner `StrictlyPositiveOn`, written on the whole-space
  subdifferential surface `g ∈ ∂[Set.univ] f(x)`;
- bridge/view: the nonlinear lower-support inequality below for the transformed objective.

Primitive data:
- a real-valued objective `f : X → ℝ` for the transformed objective owner, and
  `f : V → ℝ` for the subgradient theorem;
- a base point `x` and a vector `g`.

Derived API:
- the textbook notation `f̂` for the transformed objective `x ↦ (1 / 2) * f(x)^2`;
- the textbook notation `ĝ[f; x] g` for the transformed subgradient `f x • g`;
- the nonlinear lower-support inequality obtained from `StrictlyPositiveOn Q f`.

Source/core/bridge triage:
- source-facing: `relativeScaleTransformedObjective`,
  `relativeScaleTransformedSubgradient`, and the displayed lower-support theorem;
- core/canonical: `StrictlyPositiveOn` and `∂[Set.univ] f(x)`;
- bridge/view: the lower-support inequality specialized to the transformed objective.

This file is the Chapter 7 owner for the relative-scale transform itself. The transformed
objective lives on the weakest ambient layer `X → ℝ`, the transformed subgradient only uses scalar
multiplication, and the nonlinear lower-support theorem adds the inner-product structure.
Downstream files should reuse these owners directly rather than rebuilding local copies of the
transformed objective or of its subgradient interface.
-/
variable {X : Type u}

/-- The transformed objective associated to `f` is `x ↦ (1 / 2) * f(x)^2`. -/
def relativeScaleTransformedObjective (f : X → ℝ) : X → ℝ :=
  fun x ↦ (1 / 2 : ℝ) * (f x) ^ 2

/- Source-facing Lean notation for the textbook transformed objective `f̂`. -/
scoped[RelativeScaleTransformNotation] postfix:max "̂" => relativeScaleTransformedObjective

open scoped RelativeScaleTransformNotation

/-- Evaluating the transformed objective notation `f̂` recovers the formula `(1 / 2) * f(x)^2`. -/
-- Proof sketch: unfold `f̂`.
theorem relativeScaleTransformedObjective_apply (f : X → ℝ) (x : X) :
    f̂ x = (1 / 2 : ℝ) * (f x) ^ 2 :=
  rfl

section Smul

variable {V : Type u} [SMul ℝ V]

/-- The pointwise transformed subgradient value attached to `g ∈ ∂f(x)` is `f(x) • g`. -/
def relativeScaleTransformedSubgradient (f : V → ℝ) (x g : V) : V :=
  f x • g

/- Source-facing Lean notation for the textbook transformed subgradient `ĝ[f; x] g`. -/
scoped[RelativeScaleTransformNotation] notation:max "ĝ[" f:arg "; " x:arg "]" =>
  relativeScaleTransformedSubgradient f x

/-- Evaluating the transformed subgradient notation gives the scaled vector `f(x) • g`. -/
-- Proof sketch: unfold `ĝ[f; x] g`.
theorem relativeScaleTransformedSubgradient_def (f : V → ℝ) (x g : V) :
    ĝ[f; x] g = f x • g :=
  rfl

end Smul

section InnerProduct

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- Proof sketch: rewrite `f̂` as `(1 / 2) * f^2` and
-- `ĝ[f; x] g` as `f(x) • g`, then apply
-- `StrictlyPositiveOn.inequality` to get `f y ≥ -(f x + ⟪g, y - x⟫)`. Squaring the resulting
-- lower bound and expanding the square yields the displayed estimate.
/-- Lemma 7.20: if `f` is strictly positive on `Q`, then for every `x, y ∈ Q` and every
whole-space subgradient `g ∈ ∂[Set.univ] f(x)`, the
transformed objective satisfies the nonlinear lower-support inequality
`f̂ y ≥ f̂ x + ⟪ĝ[f; x] g, y - x⟫ + (1 / 2) * ⟪g, y - x⟫^2`. -/
theorem relativeScaleTransformedObjective_nonlinear_lower_support
    {Q : Set V} {f : V → ℝ}
    (hstrict : StrictlyPositiveOn Q f)
    {x y g : V} (hx : x ∈ Q) (hy : y ∈ Q)
    (hg : g ∈ ∂[Set.univ] f(x)) :
    f̂ y ≥
      f̂ x +
        inner ℝ (ĝ[f; x] g) (y - x) +
        (1 / 2 : ℝ) * (inner ℝ g (y - x)) ^ 2 := sorry

end InnerProduct

end

/-! ### Proposition_7_20 (from Chap07) -/
noncomputable section

open EuclideanSpace (nonnegativeOrthant)
open scoped SymmetricBox WithTopConvexAnalysis

variable {n : ℕ} {m : ℕ+}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 7.20 lies in the Chapter 7 weighted max-absolute-coordinate / subdifferential
domain.

Sampled owner-style declarations:
- `IsSubgradientAt`, `subdifferential`, and the notation `∂ f(x)` in
  `Chap03/Definition_3_1_5`, the chapter owners for subgradients;
- `symmetricBox`, the notation `B(g)`, and `signSymmetricConvexHull` in
  `Chap07/Definition_7_35`, the chapter owners for the boxes `B(a)` and their convex hull;
- `maxWeightedAbsoluteCoordinateSum` and the orthant bridge
  `maxWeightedAbsoluteCoordinateSumOfOrthant` in `Chap07/Definition_7_43`, the Chapter 7 owner
  surface for the objective `x ↦ maxᵢ ∑ⱼ aᵢⱼ |xⱼ|`.

Best owner abstraction:
- source-facing: Proposition 7.20 itself, stated for `maxWeightedAbsoluteCoordinateSum`;
- core/canonical: the Chapter 3 owner subdifferential `∂`;
- bridge/view: the Chapter 7 box notation `B(a)` and the hull owner
  `signSymmetricConvexHull`.

Primitive data:
- a positive number of branches `m`;
- a family `a : Fin (m : ℕ) → E` in the nonnegative orthant.

Derived API:
- the origin-subdifferential identity below.

This refinement deletes the duplicate local real-valued subgradient/subdifferential and box
wrappers. The proposition is now stated directly through the existing chapter owners `∂`,
`signSymmetricConvexHull`, and the orthant bridge to `maxWeightedAbsoluteCoordinateSum`, while
keeping the same mathematical content as the textbook statement.
-/

-- Proof sketch: for each index `i`, compute `∂fᵢ(0)` for `fᵢ(x) = ∑ⱼ aᵢⱼ |xⱼ|` as the box
-- `B(a i)` by checking the subgradient inequality coordinate-wise. Since all
-- `fᵢ(0) = 0`, every branch is active in the pointwise maximum at the origin, and the standard
-- subdifferential formula for a finite maximum gives the convex hull of the union of these boxes.
/-- Proposition 7.20: if `a₁, …, aₘ ∈ ℝⁿ₊` and
`hat f(x) = maxᵢ ∑ⱼ aᵢⱼ |xⱼ|`, then `∂ hat f(0)` is the sign-symmetric convex hull
`Conv (⋃ i, B(aᵢ))`. -/
theorem subdifferential_zero_maxWeightedAbsoluteCoordinateSum_eq_signSymmetricConvexHull
    {a : Fin (m : ℕ) → E} (ha : ∀ i : Fin (m : ℕ), a i ∈ nonnegativeOrthant n) :
    ∂ (fun x : E ↦
        (maxWeightedAbsoluteCoordinateSumOfOrthant a ha x : WithTop ℝ))(0) =
      signSymmetricConvexHull a := sorry

/-! ### Theorem_7_20 (from Chap07) -/
noncomputable section

universe u

open scoped ConstrainedArgmin

variable {E : Type u} [SeminormedAddCommGroup E]

/- Theorem 7.20 lies in the localized strictly-positive-objective / constrained minimization
domain.

Sampled owner-style declarations:
- `boundedFeasibleSet` in `Chap07/Definition_7_13`, the chapter owner for the localized feasible
  set `Q ∩ closedBall x₀ R`;
- `argmin[Q] f` in `Chap01/Definition_1_3_3`, the project owner for a constrained minimizer,
  packaging feasibility together with `IsMinOn`;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  real-valued objective on a feasible set;
- `SetConstrainedMinimizationProblem.optimalValue` and
  `SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image` in `Chap01/Definition_1_3_7`,
  the canonical constrained optimal-value owner and its bridge back to the feasible-value infimum;
- mathlib `LipschitzOnWith`, the canonical owner for a set-restricted Lipschitz bound;
- mathlib `IsMinOn`, the underlying setwise minimality predicate used inside `argmin[Q] f`.

Best owner abstraction:
- source-facing: the localized max objective
  `x ↦ max (shiftedObjective φ x₀ L R x) (L * ‖x - x₀‖)`;
- core/canonical: `boundedFeasibleSet Q x₀ R`,
  `x ∈ argmin[boundedFeasibleSet Q x₀ R] f`,
  `(.mk (boundedFeasibleSet Q x₀ R) (localStrictlyPositiveObjective φ x₀ L R))`,
  `LipschitzOnWith (Real.toNNReal L) φ Q`, and `IsMinOn`;
- bridge/view: the evaluation lemma for the max formula, the in-ball branch equality with
  `shiftedObjective`, and
  `optimalValue_eq_sInf_image`.

Primitive data:
- the feasible set `Q`, objective `φ`, base point `x₀`, and radii constants `L`, `R`;
- the canonical Lipschitz owner `LipschitzOnWith (Real.toNNReal L) φ Q`;
- the constrained problem data `Q` together with the local objective
  `localStrictlyPositiveObjective φ x₀ L R`.

Derived API:
- pointwise lower and positivity bounds for the localized max objective;
- the in-ball identification with the shifted branch `shiftedObjective φ x₀ L R`;
- optimization consequences organized on the localized feasible slice `boundedFeasibleSet Q x₀ R`
  and its Chapter 1 owner optimal value.
-/

/-- The max-type objective obtained from the local minimization model around `x₀`. -/
def localStrictlyPositiveObjective
    (φ : E → ℝ) (x₀ : E) (L R : ℝ) : E → ℝ :=
  fun x ↦ max (shiftedObjective φ x₀ L R x) (L * ‖x - x₀‖)

/-- Evaluating `localStrictlyPositiveObjective φ x₀ L R` at `x` recovers the textbook formula
`max {φ(x) - φ(x₀) + 2LR, L ‖x - x₀‖}`. -/
@[simp]
theorem localStrictlyPositiveObjective_apply
    (φ : E → ℝ) (x₀ x : E) (L R : ℝ) :
    localStrictlyPositiveObjective φ x₀ L R x =
      max (shiftedObjective φ x₀ L R x) (L * ‖x - x₀‖) := by
  simp [localStrictlyPositiveObjective]

/-- If `L * R ≥ 0`, then the value of the local strictly positive objective at the base point `x₀`
is `2LR`. -/
-- Proof sketch: unfold the definition at `x₀`; the norm term vanishes and the remaining maximum is
-- `max (shiftedObjective φ x₀ L R x₀) 0 = 2 * L * R`, using
-- `shiftedObjective_basePoint` and `0 ≤ L * R`.
theorem localStrictlyPositiveObjective_at_basePoint
    (φ : E → ℝ) (x₀ : E) {L R : ℝ} (hLR : 0 ≤ L * R) :
    localStrictlyPositiveObjective φ x₀ L R x₀ = 2 * L * R := sorry

section LocalStrictlyPositiveObjective

variable {Q : Set E} {φ : E → ℝ} {x₀ : E} {L R : ℝ}

/-- A uniform Lipschitz bound on `φ` over `Q` forces the local objective to be bounded below by
`LR` at every feasible point. -/
-- Proof sketch: use the Lipschitz inequality with `y = x₀` to get
-- `shiftedObjective φ x₀ L R x ≥ 2 * L * R - L * ‖x - x₀‖`, then compare the two arguments of the
-- maximum against the midpoint value `L * R`.
theorem localStrictlyPositiveObjective_lower_bound
    (hx₀ : x₀ ∈ Q) (hL_nonneg : 0 ≤ L)
    (hφ_lipschitz : LipschitzOnWith (Real.toNNReal L) φ Q)
    {x : E} (hx : x ∈ Q) :
    L * R ≤ localStrictlyPositiveObjective φ x₀ L R x := sorry

/-- On the radius-`R` ball around `x₀`, the first branch of the max formula for the local strictly
positive objective dominates the norm branch. -/
-- Proof sketch: use the same Lipschitz lower estimate with `y = x₀`; when `‖x - x₀‖ ≤ R`, the
-- shifted value `shiftedObjective φ x₀ L R x` is at least `L * R`, hence at least
-- `L * ‖x - x₀‖`.
theorem localStrictlyPositiveObjective_eq_shift_of_norm_le
    (hx₀ : x₀ ∈ Q) (hL_nonneg : 0 ≤ L)
    (hφ_lipschitz : LipschitzOnWith (Real.toNNReal L) φ Q)
    {x : E} (hx : x ∈ Q) (hxR : ‖x - x₀‖ ≤ R) :
    localStrictlyPositiveObjective φ x₀ L R x = shiftedObjective φ x₀ L R x := sorry

-- Proof sketch: apply `localStrictlyPositiveObjective_lower_bound` to the feasible point `x`,
-- then combine `0 < L` and `0 < R` to deduce `0 < L * R`.
/-- Theorem 7.20: if `φ` satisfies the uniform Lipschitz bound
`|φ x - φ y| ≤ L ‖x - y‖` on `Q`, with `x₀ ∈ Q` and `L, R > 0`, then the local objective
`x ↦ max {φ(x) - φ(x₀) + 2LR, L ‖x - x₀‖}` is strictly positive at every feasible point of `Q`. -/
theorem localStrictlyPositiveObjective_strictlyPositive
    (hx₀ : x₀ ∈ Q) (hL : 0 < L) (hR : 0 < R)
    (hφ_lipschitz : LipschitzOnWith (Real.toNNReal L) φ Q)
    {x : E} (hx : x ∈ Q) :
    0 < localStrictlyPositiveObjective φ x₀ L R x := sorry

/-- A constrained minimizer of `φ` on the bounded feasible set
`Q₁(R) = Q ∩ closedBall x₀ R` is also a constrained minimizer of the local strictly positive
objective on the same bounded feasible set. -/
-- Proof sketch: on `boundedFeasibleSet Q x₀ R`, replace the local objective by
-- `shiftedObjective φ x₀ L R x` using `localStrictlyPositiveObjective_eq_shift_of_norm_le`, so
-- the local minimizer of `φ` also minimizes the shifted objective there.
theorem mem_argmin_localStrictlyPositiveObjective_of_mem_argmin_boundedFeasibleSet
    (hx₀ : x₀ ∈ Q) (hL_nonneg : 0 ≤ L)
    (hφ_lipschitz : LipschitzOnWith (Real.toNNReal L) φ Q)
    {xStar : E} (hxStar : xStar ∈ argmin[boundedFeasibleSet Q x₀ R] φ) :
    xStar ∈ argmin[boundedFeasibleSet Q x₀ R] (localStrictlyPositiveObjective φ x₀ L R) := sorry

/-- The Chapter 1 optimal value of the localized constrained local-objective problem on
`Q₁(R) = boundedFeasibleSet Q x₀ R` is bounded below by `LR`. -/
-- Proof sketch: package `boundedFeasibleSet Q x₀ R` together with the local objective as a
-- `SetConstrainedMinimizationProblem`; then use `optimalValue_eq_sInf_image` to rewrite the owner
-- value as the infimum of the feasible objective image, where
-- `localStrictlyPositiveObjective_lower_bound` gives the needed pointwise lower bound.
theorem localStrictlyPositiveObjective_boundedFeasibleSet_optimalValue_lower_bound
    (hx₀ : x₀ ∈ Q) (hL_nonneg : 0 ≤ L)
    (hφ_lipschitz : LipschitzOnWith (Real.toNNReal L) φ Q) :
    (L * R : EReal) ≤
      (SetConstrainedMinimizationProblem.mk (boundedFeasibleSet Q x₀ R)
        (localStrictlyPositiveObjective φ x₀ L R)).optimalValue := sorry

/-- If `R ≥ 0` and `L * R ≥ 0`, the Chapter 1 optimal value of the localized constrained
local-objective problem on `Q₁(R) = boundedFeasibleSet Q x₀ R` is bounded above by `2LR`. -/
-- Proof sketch: `x₀ ∈ boundedFeasibleSet Q x₀ R` follows from `x₀ ∈ Q` and `0 ≤ R`, so the owner
-- theorem `optimalValue_le_of_mem_feasibleSet` bounds the optimal value by the objective at `x₀`;
-- then
-- `localStrictlyPositiveObjective_at_basePoint` identifies that value with `2 * L * R`.
theorem localStrictlyPositiveObjective_boundedFeasibleSet_optimalValue_upper_bound
    (hx₀ : x₀ ∈ Q) (hR : 0 ≤ R) (hLR : 0 ≤ L * R) :
    ((SetConstrainedMinimizationProblem.mk (boundedFeasibleSet Q x₀ R)
        (localStrictlyPositiveObjective φ x₀ L R)).optimalValue) ≤
      (2 * L * R : EReal) := sorry

end LocalStrictlyPositiveObjective
