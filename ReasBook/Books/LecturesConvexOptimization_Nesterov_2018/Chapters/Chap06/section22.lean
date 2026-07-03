import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_22 (from Chap06) -/
noncomputable section

open scoped BigOperators

universe u v

/-
Definition 6.22 lies in the finite max-absolute-value / log-sum-exp smoothing domain.

Sampled owner-style declarations:
- `maxTypeObjective` in `Chap02/Lemma_2_18`, the project owner for pointwise maxima of a nonempty
  finite family;
- `maxAbsoluteValueOptimizationObjective` in `Chap06/Definition_6_21`, the nearby chapter owner
  fixing the source-facing absolute-affine family `i ↦ |a i x| - b i`;
- `η` together with the positive-parameter recall surface in `Chap06/Definition_6_27`, the
  chapter's log-sum-exp owner pattern;
- `logSumExpMaxEigenvalueSmoothing` in `Chap06/Definition_6_47`, another Chapter 6 smoothing
  owner whose public surface uses a positive smoothing parameter subtype.

Best owner abstraction:
- source-facing: `logSumExpAbsoluteValueSmoothing`, since this item introduces the smoothed
  absolute-affine objective itself;
- core/canonical: the chapter/project finite-family owner pattern
  `[Fintype ι] [Nonempty ι]` together with the Chapter 6 positive-parameter smoothing surface;
- bridge/view: `logSumExpAbsoluteValueSmoothing_apply`, the direct expansion to the textbook
  formula.

Primitive data:
- a nonempty finite index family `ι`;
- linear functionals `a : ι → Module.Dual ℝ E`;
- offsets `b : ι → ℝ`, used through the same shifted absolute values `|a i x| - b i` as in
  `maxAbsoluteValueOptimizationObjective a b`;
- the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`.

Derived API:
- the source-facing smoothing function below;
- its evaluation theorem.

This file therefore stays at the source-facing layer: there is no upstream chapter owner for this
exact log-sum-exp smoothing, so the refinement is to keep the single owner declaration while
reusing the Chapter 6 absolute-affine family from `maxAbsoluteValueOptimizationObjective` instead
of introducing a parallel residual convention.
-/
variable {ι : Type v} [Fintype ι]
variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Definition 6.22: for linear functionals `a₁, …, aₘ ∈ E*`, offsets `b ∈ ℝᵐ`, and smoothing
parameter `μ > 0`, the log-sum-exp smoothing of the Chapter 6 objective
`x ↦ max_i (|a_i(x)| - bⁱ)` from Definition 6.21 is the function
`x ↦ μ log (((card ι)⁻¹) ∑ᵢ exp ((|aᵢ(x)| - bᵢ) / μ))`. The nonempty finite-family assumptions are
part of the mathematics here because the normalization factor is the average over the index
family. -/
def logSumExpAbsoluteValueSmoothing
    [Nonempty ι] (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (μ : {μ : ℝ // 0 < μ}) : E → ℝ :=
  fun x ↦
    μ.1 * Real.log (((Fintype.card ι : ℝ)⁻¹) *
      ∑ i : ι, Real.exp ((|a i x| - b i) / μ.1))

-- Proof sketch: unfold `logSumExpAbsoluteValueSmoothing`; the displayed formula is exactly the
-- normalized log-sum-exp smoothing of the same family `i ↦ |a i x| - b i` used in
-- `maxAbsoluteValueOptimizationObjective`.
/-- Evaluating `logSumExpAbsoluteValueSmoothing a b μ` gives the defining averaged logarithmic
smoothing formula built from the shifted absolute values `|aᵢ(x)| - bᵢ`. -/
@[simp] theorem logSumExpAbsoluteValueSmoothing_apply
    [Nonempty ι] (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (μ : {μ : ℝ // 0 < μ}) (x : E) :
    logSumExpAbsoluteValueSmoothing a b μ x =
      μ.1 * Real.log (((Fintype.card ι : ℝ)⁻¹) *
        ∑ i : ι, Real.exp ((|a i x| - b i) / μ.1)) :=
  rfl

-- Proof sketch: apply `eta_apply` to the score vector
-- `i ↦ |a i x| - b i`, then separate the normalization factor `(card ι : ℝ)⁻¹`
-- from the logarithm using the standard `Real.log_mul` identity.
/-- Definition 6.22 is the Chapter 6 log-sum-exp potential `η` applied to the shifted
absolute-value score vector, together with the additive normalization term coming from averaging
over the finite index family. -/
theorem logSumExpAbsoluteValueSmoothing_eq_eta_add_log_card_inv
    [Nonempty ι] (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (μ : {μ : ℝ // 0 < μ}) (x : E) :
    logSumExpAbsoluteValueSmoothing a b μ x =
      η μ (WithLp.toLp 2 fun i : ι ↦ |a i x| - b i) +
        μ.1 * Real.log ((Fintype.card ι : ℝ)⁻¹) := sorry

end

/-! ### Proposition_6_22 (from Chap06) -/
noncomputable section

open scoped BigOperators

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type v} [Fintype ι]

local notation "E₂" => EuclideanSpace ℝ ι

/- Proposition 6.22 lies in the finite-index operator-norm / weighted-Euclidean domain.

Sampled owner declarations:
* `Seminorm.comp`, the canonical owner for transporting a seminorm along a linear map;
* `normSeminorm`, the ambient seminorm owner whose pullback gives the weighted geometry;
* `ContinuousLinearMap.opNorm`, the canonical ambient operator norm on continuous linear maps;
* `ContinuousLinearMap.pi`, the canonical owner for assembling a finite row family into a map to
  `EuclideanSpace ℝ ι`;
* `EuclideanSpace.equiv`, the canonical equivalence between `EuclideanSpace ℝ ι` and coordinate
  functions on `ι`;
* `EuclideanSpace.proj`, the canonical coordinate projections used to build the weighted scaling
  map;
* `operatorNorm_eq_sSup_dualPairing_unitSpheres` in `Chap06/Definition_6_3`, the chapter bridge
  from the canonical operator norm to a source-facing dual-pairing supremum.

Best owner abstraction:
* source-facing: the textbook supremum of `∑ⱼ u_j a_j(x)` over the ambient unit ball in `E` and
  the unit ball of the weighted Euclidean seminorm on `EuclideanSpace ℝ ι`;
* core/canonical: `‖normalizedRowMap a‖`;
* bridge/view: the weighted scaling map `weightedRowScale a`, which transports the weighted
  Euclidean seminorm to the ambient Euclidean norm.

Primitive data:
* the finite row family `a : ι → StrongDual ℝ E`.

Derived API:
* the weighted scaling map on `EuclideanSpace ℝ ι`;
* the normalized row map into `EuclideanSpace ℝ ι`;
* the source-facing weighted Euclidean seminorm, recovered as the pullback of the ambient
  seminorm after weighting;
* the source-facing bridge from the textbook supremum to the canonical operator norm.

Source/core/bridge triage:
* source-facing: `weightedRowEuclideanSeminorm` and Proposition 6.22's weighted-pairing
  supremum;
* core/canonical: `‖normalizedRowMap a‖`;
* bridge/view: `weightedRowScale`, which rewrites the weighted unit ball as an ordinary Euclidean
  unit ball.

The previous `weightedRowOperatorNorm` was a duplicate owner of this bound: it only repackaged the
same supremum into a local `def`. This refinement deletes that duplicate owner, keeps the weighted
seminorm as the source-facing bridge object, routes the inequality through the canonical operator
norm of the normalized row map, and promotes the public finite-family surface from the coordinate
owner `Fin m` to the chapter's canonical owner `[Fintype ι]`.
-/

/-- The diagonal scaling `u_j ↦ √‖a_j‖ u_j` transporting the weighted finite-family geometry to
the ambient Euclidean norm. -/
def weightedRowScale
    (a : ι → StrongDual ℝ E) : E₂ →L[ℝ] E₂ :=
  ((EuclideanSpace.equiv ι ℝ).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun j ↦
      Real.sqrt ‖a j‖ • EuclideanSpace.proj j)

omit [Fintype ι] in
/-- The `j`-th coordinate of `weightedRowScale a u` is `√‖a_j‖ u_j`. -/
theorem weightedRowScale_apply
    (a : ι → StrongDual ℝ E) (u : E₂) (j : ι) :
    weightedRowScale a u j = Real.sqrt ‖a j‖ * u j := by
  sorry

/-- The normalized row operator with coordinates
`x ↦ a_j(x) / √‖a_j‖`, interpreted as `0` on zero rows. -/
def normalizedRowMap
    (a : ι → StrongDual ℝ E) : E →L[ℝ] E₂ :=
  ((EuclideanSpace.equiv ι ℝ).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun j ↦
      (if ‖a j‖ = 0 then 0 else (Real.sqrt ‖a j‖)⁻¹) • a j)

omit [Fintype ι] in
/-- The `j`-th coordinate of `normalizedRowMap a x` is the normalized row value. -/
theorem normalizedRowMap_apply
    (a : ι → StrongDual ℝ E) (x : E) (j : ι) :
    normalizedRowMap a x j =
      (if ‖a j‖ = 0 then 0 else (Real.sqrt ‖a j‖)⁻¹) * a j x := by
  sorry

/-- The weighted Euclidean seminorm on `EuclideanSpace ℝ ι` whose weights are the dual norms of
the rows `a_j`, expressed canonically as the pullback of the ambient seminorm along
`weightedRowScale a`. Zero rows produce zero weights, so the source-facing geometry is generally a
seminorm rather than a norm. -/
def weightedRowEuclideanSeminorm
    (a : ι → StrongDual ℝ E) : Seminorm ℝ E₂ :=
  Seminorm.comp (normSeminorm ℝ E₂) (weightedRowScale a).toLinearMap

/-- Evaluating `weightedRowEuclideanSeminorm a` gives the ambient norm of `weightedRowScale a u`.
-/
theorem weightedRowEuclideanSeminorm_eq_norm_weightedRowScale
    (a : ι → StrongDual ℝ E) (u : E₂) :
    weightedRowEuclideanSeminorm a u = ‖weightedRowScale a u‖ :=
  rfl

-- Proof sketch: expand `weightedRowEuclideanSeminorm` via `weightedRowScale_apply` and then use
-- `EuclideanSpace.norm_eq`.
/-- Applying `weightedRowEuclideanSeminorm a` gives the square root of the weighted quadratic form
`∑ⱼ ‖a_j‖ (u_j)^2`. -/
theorem weightedRowEuclideanSeminorm_apply
    (a : ι → StrongDual ℝ E) (u : E₂) :
    weightedRowEuclideanSeminorm a u =
      Real.sqrt (∑ j : ι, ‖a j‖ * (u j) ^ (2 : ℕ)) := by
  sorry

-- Proof sketch: write the source supremum as the Euclidean dual pairing between
-- `normalizedRowMap a x` and `weightedRowScale a u`, then identify the supremum over the weighted
-- unit ball with the ordinary operator norm of `normalizedRowMap a`; this is the source-facing
-- specialization of the chapter bridge `operatorNorm_eq_sSup_dualPairing_unitSpheres`.
/-- The textbook weighted-pairing supremum equals the ordinary operator norm of
`normalizedRowMap a`. -/
theorem normalizedRowMap_opNorm_eq_weightedRowPairing_sSup
    (a : ι → StrongDual ℝ E) :
    ‖normalizedRowMap a‖ =
      sSup ((fun xu : E × E₂ ↦ ∑ j : ι, xu.2 j * a j xu.1) ''
        Set.prod {x : E | ‖x‖ ≤ 1}
          {u : E₂ | weightedRowEuclideanSeminorm a u ≤ 1}) := by
  sorry

-- Proof sketch: for `‖x‖ ≤ 1`, estimate each coordinate of `normalizedRowMap a x` using
-- `|a_j x| ≤ ‖a_j‖ ‖x‖`; after squaring and summing, the Euclidean norm is bounded by
-- `(∑ⱼ ‖a_j‖)^(1/2)`, and `opNorm_le_bound` finishes.
/-- The canonical operator norm of the normalized row map is bounded by
`(∑ⱼ ‖a_j‖)^(1/2)`. -/
theorem normalizedRowMap_opNorm_le_sqrt_sum_rowNorms
    (a : ι → StrongDual ℝ E) :
    ‖normalizedRowMap a‖ ≤ Real.sqrt (∑ j : ι, ‖a j‖) := by
  sorry

/-- Proposition 6.22: for the row map with coordinates `x ↦ a_j(x)`, the supremum of
`∑ⱼ u_j a_j(x)` over the ambient unit ball of `E` and the weighted unit ball
of `weightedRowEuclideanSeminorm a` in `EuclideanSpace ℝ ι` is bounded above by
`(∑ⱼ ‖a_j‖)^(1/2)`. -/
theorem weightedRowPairing_sSup_le_sqrt_sum_rowNorms
    (a : ι → StrongDual ℝ E) :
    sSup ((fun xu : E × E₂ ↦ ∑ j : ι, xu.2 j * a j xu.1) ''
      Set.prod {x : E | ‖x‖ ≤ 1}
        {u : E₂ | weightedRowEuclideanSeminorm a u ≤ 1}) ≤
      Real.sqrt (∑ j : ι, ‖a j‖) := by
  rw [← normalizedRowMap_opNorm_eq_weightedRowPairing_sSup a]
  exact normalizedRowMap_opNorm_le_sqrt_sum_rowNorms a

end
