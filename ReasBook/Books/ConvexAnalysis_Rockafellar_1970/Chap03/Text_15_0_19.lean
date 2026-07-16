import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_3
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_18

open scoped Pointwise Rockafellar

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.19 compares the Minkowski metric attached in Text 15.0.18 to the
  ambient norm metric. The textbook specialization is recovered by taking
  `E = EuclideanSpace ℝ (Fin n)`.
- `core/canonical`: the owner abstractions are the ambient norm metric on `E`, the Chapter 2
  unit-ball owner `B = Metric.closedBall (0 : E) 1`, the set-level predicates
  `Bornology.IsBounded K` and `(0 : E) ∈ interior K`, and the metric owner pair
  `ρ : MetricSpace E` together with `MetricSpace.IsMinkowskiMetric`.
- `bridge/view`: the quantitative comparison is expressed by explicit constants `α, β > 0`,
  inclusions `α • B ⊆ K ⊆ β • B`, and the resulting two-sided distance comparison.

Domain-style sampling used here:
- the boundedness owner theorem `Bornology.IsBounded.subset_closedBall`;
- `Metric.mem_interior_iff_exists_pos_closedBall_subset`;
- `Metric.closedBall` for the ambient unit ball and for the closed balls of the Minkowski metric;
- `LipschitzWith` and `AntilipschitzWith` as the canonical route from two-sided metric comparison
  to equality of topologies and Cauchy sequences.

Primitive data vs derived API:
- primitive inputs: a set `K : Set E`, the boundedness hypothesis `IsBounded K` needed for the
  outer ambient closed ball, the interior-origin hypothesis `(0 : E) ∈ interior K` needed for the
  inner ambient closed ball, and the specific closed-ball bridge data from Text 15.0.18 for a
  metric owner `ρ : MetricSpace E`;
- derived API: the ambient comparison constants `α, β`, the two-sided norm/metric inequality, the
  neighborhood-basis comparison with ambient closed balls, and the corresponding
  `CauchySeq` equivalence.

Layer target: `bridge/view`, because this item relates the metric coming from Text 15.0.18 to
the ambient norm metric while isolating the set-level bridge data actually used by the comparison
arguments.
-/

-- Proof sketch: boundedness of the set `K` gives an ambient closed ball about `0`
-- containing `K`, hence a positive dilation `β • B` of the unit ball `B`.
/-- Text 15.0.19 (1): every bounded set in a real normed space is contained in a positive
ambient dilation `β • B` of the unit ball `B`. Applied to the body from Text 15.0.18, this
supplies the outer comparison constant. -/
theorem exists_pos_subset_smul_unitClosedBall_of_isBounded
    {K : Set E} (hK_bounded : Bornology.IsBounded K) :
    ∃ β : ℝ, 0 < β ∧ K ⊆ β • B := sorry

-- Proof sketch: the hypothesis `0 ∈ interior K` provides an ambient closed ball about `0`
-- contained in `K`, hence some positive dilation `α • B` lies inside `K`.
/-- Text 15.0.19 (2): if `0 ∈ interior K`, then `K` contains a positive ambient dilation
`α • B` of the unit ball `B`. -/
theorem exists_pos_smul_unitClosedBall_subset_of_zero_mem_interior
    {K : Set E} (hK_int : (0 : E) ∈ interior K) :
    ∃ α : ℝ, 0 < α ∧ α • B ⊆ K := sorry

section MinkowskiComparison

variable {K : Set E} {ρ : MetricSpace E} [ρ.IsMinkowskiMetric]

variable (hball : letI := ρ.toPseudoMetricSpace
  ∀ x : E, ∀ ε : ℝ, 0 < ε →
    Metric.closedBall x ε = ({x} : Set E) + ε • K)

-- Proof sketch: if `C ⊆ β • B`, then the closed-ball formula from Text 15.0.18 yields
-- `closedBallₚ x ε ⊆ closedBall x (β ε)`. Evaluating this inclusion on `y` gives the lower
-- comparison `β⁻¹ dist x y ≤ ρ(x,y)`.
/-- Text 15.0.19 (3): any positive constant `β` with `K ⊆ β • B` yields the lower comparison
`β⁻¹ dist x y ≤ ρ(x,y)` between the ambient norm metric and the Minkowski metric. -/
theorem inv_mul_dist_le_minkowskiDist_of_subset_smul_unitClosedBall
    {β : ℝ} (hβ : 0 < β) (hβK : K ⊆ β • B) (x y : E) :
    β⁻¹ * dist x y ≤ ρ.dist x y := sorry

-- Proof sketch: if `α • B ⊆ C`, then the closed-ball formula gives
-- `closedBall x (α ε) ⊆ closedBallₚ x ε`. Testing membership of `y` in these balls yields the
-- upper comparison `ρ(x,y) ≤ α⁻¹ dist x y`.
/-- Text 15.0.19 (4): any positive constant `α` with `α • B ⊆ K` yields the upper comparison
`ρ(x,y) ≤ α⁻¹ dist x y` between the Minkowski metric and the ambient norm metric. -/
theorem minkowskiDist_le_inv_mul_dist_of_smul_unitClosedBall_subset
    {α : ℝ} (hα : 0 < α) (hαK : α • B ⊆ K) (x y : E) :
    ρ.dist x y ≤ α⁻¹ * dist x y := sorry

-- Proof sketch: the positive comparison constants `α, β` and clauses (3) and (4) give the
-- required two-sided distance comparison. The identity map on `E`, viewed from the
-- ambient norm metric to `ρ` and back, is Lipschitz in both directions, so the two metric
-- neighborhood filters coincide.
/-- Text 15.0.19 (5): if `α • B ⊆ K ⊆ β • B` for some positive `α, β` and the positive
`ρ`-closed balls are the sets `x + ε K`, then `ρ` and the ambient norm metric induce the same
neighborhood filter at every point `x`; equivalently, they define the same topology. For the
convex-body metric of Text 15.0.18, clauses (1) and (2) provide such `α` and `β`. -/
theorem minkowskiMetric_nhds_eq_norm_of_closedBall_eq_translate_smul
    {α β : ℝ}
    (hα : 0 < α) (hαK : α • B ⊆ K)
    (hβ : 0 < β) (hβK : K ⊆ β • B) (x : E) :
    (letI := ρ.toPseudoMetricSpace; nhds x) = nhds x := sorry

-- Proof sketch: the previous theorem makes the identity map bilipschitz between the ambient norm
-- metric and `ρ`, so it is a uniform embedding in both directions. Bilipschitz equivalent metrics
-- therefore have the same `CauchySeq` predicate.
/-- Text 15.0.19 (6): if `α • B ⊆ K ⊆ β • B` for some positive `α, β` and the positive
`ρ`-closed balls are the sets `x + ε K`, then a sequence in `E` is Cauchy for `ρ` exactly when it
is Cauchy for the ambient norm metric, formalized with the canonical owner predicate `CauchySeq`.
For the convex-body metric of Text 15.0.18, clauses (1) and (2) provide the needed comparison
constants. -/
theorem minkowskiMetric_cauchySeq_iff_norm_of_closedBall_eq_translate_smul
    {α β : ℝ}
    (hα : 0 < α) (hαK : α • B ⊆ K)
    (hβ : 0 < β) (hβK : K ⊆ β • B)
    (u : ℕ → E) :
    (letI := ρ.toPseudoMetricSpace.toUniformSpace; CauchySeq u) ↔
      CauchySeq u := sorry

end MinkowskiComparison

end
