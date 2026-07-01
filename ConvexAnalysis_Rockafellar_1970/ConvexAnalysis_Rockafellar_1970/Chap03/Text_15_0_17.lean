import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_16
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_12

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage:
- `source-facing`: Text 15.0.17 states a bijective correspondence between norms and Minkowski
  metrics. The source specialization to `R^n` is recovered by taking
  `E = EuclideanSpace ℝ (Fin n)`.
- `core/canonical`: on the norm side, the Chapter 15 owner abstraction is `IsGaugeNorm`; on the
  metric side, the owner is the source-facing class `MetricSpace.IsMinkowskiMetric` from
  `Text_15_0_16`.
- `bridge/view`: the two source formulas `ρ(x,y) = k(x - y)` and `k(x) = ρ(x,0)` are the bridge
  maps between these owner abstractions.

Domain-style sampling used here:
- the Chapter 15 owner `IsGaugeNorm` from `Text_15_0_12`;
- `IsGaugeNorm.subadditive`, `IsGaugeNorm.map_smul_eq_abs`, and
  `IsGaugeNorm.toReal_eq_zero_iff` as the canonical derived API for
  norm-gauges;
- `MetricSpace` as the ambient owner of the metric data;
- the Chapter 15 metric owner `MetricSpace.IsMinkowskiMetric`.

Primitive data vs derived API:
- primitive norm-side data: a `WithBotTop ℝ`-valued function on `E`
  together with the owner predicate
  `IsGaugeNorm`;
- primitive metric-side data: a metric structure together with `MetricSpace.IsMinkowskiMetric`;
- derived API: the concrete maps `k ↦ ρ_k`, `ρ ↦ k_ρ`, and the inverse laws.

Layer target: `bridge/view`, because this item compares two already existing owner abstractions via
canonical constructions in each direction.
-/

noncomputable section

section

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private def gaugeNormDist (k : E → WithBotTop ℝ) (hk : IsGaugeNorm k) (x y : E) : ℝ :=
  letI : IsGaugeNorm k := hk
  EReal.toReal (k (x - y))

/-- The metric structure induced by a norm-gauge on a real vector space. -/
@[reducible] def minkowskiMetricOfNorm
    (k : E → WithBotTop ℝ) (hk : IsGaugeNorm k) :
    MetricSpace E where
  dist := gaugeNormDist k hk
  dist_self x := by
    have hk0 : k 0 = 0 := hk.toIsGauge.map_zero
    change EReal.toReal (k (x - x)) = 0
    calc
      EReal.toReal (k (x - x)) = EReal.toReal (k 0) := by simp
      _ = 0 := by
        rw [hk0]
        exact EReal.toReal_zero
  dist_comm x y := by
    simpa [gaugeNormDist, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (congrArg EReal.toReal (hk.symmetric (x - y))).symm
  dist_triangle x y z := by
    have hsub : k (x - z) ≤ k (x - y) + k (y - z) := by
      simpa [sub_eq_add_neg, add_assoc] using
        (show k ((x - y) + (y - z)) ≤ k (x - y) + k (y - z) from
          IsGaugeNorm.subadditive (hk := hk) (x - y) (y - z))
    have hsub' :
        (((EReal.toReal (k (x - z)) : ℝ)) : EReal) ≤
          (((EReal.toReal (k (x - y)) : ℝ)) : EReal) +
            (((EReal.toReal (k (y - z)) : ℝ)) : EReal) := by
      rw [EReal.coe_toReal (IsGaugeNorm.ne_top (hk := hk) (x - z))
          (IsGaugeNorm.ne_bot (hk := hk) (x - z))]
      rw [EReal.coe_toReal (IsGaugeNorm.ne_top (hk := hk) (x - y))
          (IsGaugeNorm.ne_bot (hk := hk) (x - y))]
      rw [EReal.coe_toReal (IsGaugeNorm.ne_top (hk := hk) (y - z))
          (IsGaugeNorm.ne_bot (hk := hk) (y - z))]
      exact hsub
    have hsub'' :
        (((gaugeNormDist k hk x z : ℝ)) : EReal) ≤
          (((gaugeNormDist k hk x y + gaugeNormDist k hk y z : ℝ)) : EReal) := by
      simpa [gaugeNormDist] using hsub'
    exact EReal.coe_le_coe_iff.mp hsub''
  eq_of_dist_eq_zero := by
    intro x y hxy
    have hxy' : EReal.toReal (k (x - y)) = 0 := by
      simpa [gaugeNormDist] using hxy
    exact sub_eq_zero.mp ((IsGaugeNorm.toReal_eq_zero_iff (hk := hk)).1 hxy')

/-- The metric induced by a norm-gauge has distance `ρ(x,y) = k(x - y)`, with the norm-gauge
value read as a real number. -/
@[simp] theorem minkowskiMetricOfNorm_dist_eq (k : E → WithBotTop ℝ) (hk : IsGaugeNorm k)
    (x y : E) :
    (minkowskiMetricOfNorm k hk).dist x y = EReal.toReal (k (x - y)) :=
  rfl

-- Proof sketch: translation invariance follows from the difference formula
-- `ρ(x,y) = k(x - y)`. For the affine-segment axiom, rewrite the difference to the segment point as
-- `t • (x - y)` and use the absolute homogeneity of `k` together with `0 ≤ t ≤ 1`.
/-- The metric induced by a norm-gauge is a Minkowski metric. -/
theorem minkowskiMetricOfNorm_isMinkowski (k : E → WithBotTop ℝ) (hk : IsGaugeNorm k) :
    (minkowskiMetricOfNorm k hk).IsMinkowskiMetric := sorry

instance (k : E → WithBotTop ℝ) [hk : IsGaugeNorm k] :
    (minkowskiMetricOfNorm k hk).IsMinkowskiMetric :=
  minkowskiMetricOfNorm_isMinkowski k hk

end

section

variable {E : Type*} [Zero E]

namespace MetricSpace

/-- A Minkowski metric recovers its canonical norm by the formula `k(x) = ρ(x,0)`. -/
def normGauge (ρ : MetricSpace E) : E → WithBotTop ℝ :=
  fun x ↦ (ρ.dist x 0 : WithBotTop ℝ)

@[simp] theorem normGauge_apply (ρ : MetricSpace E) (x : E) :
    ρ.normGauge x = (ρ.dist x 0 : WithBotTop ℝ) :=
  rfl

end MetricSpace

end

section

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

namespace MetricSpace

-- Proof sketch: the function `x ↦ ρ(x,0)` is nonnegative and finite because it is a metric
-- distance. Symmetry follows from metric symmetry, positive homogeneity from the affine-segment
-- axiom and translation invariance, subadditivity from the metric triangle inequality, and
-- strict positivity away from `0` from the metric separation axiom.
/-- A Minkowski metric recovers its canonical norm-gauge by the formula `k(x) = ρ(x,0)`. -/
theorem normGauge_isGaugeNorm (ρ : MetricSpace E)
    (hρ : ρ.IsMinkowskiMetric) :
    IsGaugeNorm ρ.normGauge := sorry

instance (ρ : MetricSpace E) [hρ : ρ.IsMinkowskiMetric] :
    IsGaugeNorm ρ.normGauge :=
  normGauge_isGaugeNorm ρ hρ

end MetricSpace

-- Proof sketch: compare both norm-gauges pointwise using the distance formula
-- `ρ_k(x,0) = k(x - 0) = k x`, then use subtype extensionality.
/-- Recovering the norm from the metric induced by that norm returns the original norm. -/
@[simp] theorem MetricSpace.normGauge_minkowskiMetricOfNorm (k : E → WithBotTop ℝ)
    (hk : IsGaugeNorm k) :
    (minkowskiMetricOfNorm k hk).normGauge = k := sorry

-- Proof sketch: a Minkowski metric is determined by its values `ρ(x,0)` together with translation
-- invariance, since `ρ(x,y) = ρ(x - y, 0)`. Apply this to the recovered norm to identify every
-- distance value and then use extensionality of metric structures.
/-- Rebuilding a Minkowski metric from its recovered norm returns the original metric. -/
@[simp] theorem minkowskiMetricOfNorm_normGauge (ρ : MetricSpace E)
    (hρ : ρ.IsMinkowskiMetric) :
    minkowskiMetricOfNorm ρ.normGauge (MetricSpace.normGauge_isGaugeNorm ρ hρ) = ρ := sorry

/-- Text 15.0.17: the assignments `k ↦ ρ` with `ρ(x,y) = k(x - y)` and `ρ ↦ k` with
`k(x) = ρ(x,0)` define a canonical one-to-one correspondence between norms and Minkowski metrics on
the ambient real vector space. Specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers `R^n`. -/
def minkowskiMetricNormEquiv :
    { k : E → WithBotTop ℝ // IsGaugeNorm k } ≃ { ρ : MetricSpace E // ρ.IsMinkowskiMetric } where
  toFun := fun k ↦ by
    exact ⟨minkowskiMetricOfNorm k.1 k.2, minkowskiMetricOfNorm_isMinkowski k.1 k.2⟩
  invFun := fun ρ ↦ by
    exact ⟨ρ.1.normGauge, MetricSpace.normGauge_isGaugeNorm ρ.1 ρ.2⟩
  left_inv := fun k ↦ by
    apply Subtype.ext
    exact MetricSpace.normGauge_minkowskiMetricOfNorm k.1 k.2
  right_inv := fun ρ ↦ by
    apply Subtype.ext
    exact minkowskiMetricOfNorm_normGauge ρ.1 ρ.2

end

end
