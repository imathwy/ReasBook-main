import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
