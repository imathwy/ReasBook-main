import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter
open scoped Topology Manifold ContDiff

universe uM

variable {n : ℕ}
variable {M : Type uM} [TopologicalSpace M]

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The radial power map `x ↦ ‖x‖^(s - 1) • x` on `ℝ^n`, used to twist local smooth
structures. -/
noncomputable def radialPowerMap
    (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  Real.rpow ‖x‖ (s - 1) • x

/-- Helper for Problem 1-6: the radial power map fixes the origin. -/
lemma radialPowerMap_zero (s : ℝ) :
    radialPowerMap s (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
  -- The vector factor vanishes at the origin.
  simp [radialPowerMap]

/-- Helper for Problem 1-6: the radial power map fixes every point on the unit sphere. -/
lemma radialPowerMap_eq_self_of_norm_eq_one
    (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1) :
    radialPowerMap s x = x := by
  -- On `‖x‖ = 1`, the scalar factor is `1`.
  simp [radialPowerMap, hx]

/-- Helper for Problem 1-6: exponent `1` gives the identity radial map. -/
lemma radialPowerMap_one (x : EuclideanSpace ℝ (Fin n)) :
    radialPowerMap 1 x = x := by
  -- The scalar factor becomes `‖x‖^0 = 1`.
  simp [radialPowerMap]

/-- Helper for Problem 1-6: for positive exponent, the radial power map sends `‖x‖` to `‖x‖^s`. -/
lemma norm_radialPowerMap (s : ℝ) (hs : 0 < s) (x : EuclideanSpace ℝ (Fin n)) :
    ‖radialPowerMap s x‖ = ‖x‖ ^ s := by
  by_cases hx : x = 0
  · -- At the origin both sides vanish, because `s > 0`.
    simp [hx, radialPowerMap, hs.ne']
  · have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    -- Away from the origin, multiplicativity of `Real.rpow` combines the two norm factors.
    calc
      ‖radialPowerMap s x‖ = ‖Real.rpow ‖x‖ (s - 1)‖ * ‖x‖ := by
        simp [radialPowerMap, norm_smul]
      _ = Real.rpow ‖x‖ (s - 1) * ‖x‖ := by
        simp [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
      _ = ‖x‖ ^ (s - 1) * ‖x‖ ^ (1 : ℝ) := by
        simp [Real.rpow_one]
      _ = ‖x‖ ^ ((s - 1) + 1) := by
        symm
        exact Real.rpow_add hxnorm (s - 1) 1
      _ = ‖x‖ ^ s := by ring_nf

/-- Helper for Problem 1-6: positive radial powers preserve the unit ball. -/
lemma radialPowerMap_mem_unit_ball
    (s : ℝ) (hs : 0 < s) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.ball 0 1) :
    radialPowerMap s x ∈ Metric.ball 0 1 := by
  -- The norm formula reduces this to the standard scalar inequality `r^s < 1` on `0 ≤ r < 1`.
  have hx_norm : ‖x‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  have hnorm := norm_radialPowerMap s hs x
  simpa [Metric.mem_ball, dist_eq_norm, hnorm] using
    (Real.rpow_lt_one (norm_nonneg x) hx_norm hs)

/-- Helper for Problem 1-6: composing radial power maps multiplies the exponents. -/
lemma radialPowerMap_mul
    (s t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    radialPowerMap s (radialPowerMap t x) = radialPowerMap (s * t) x := by
  by_cases hx : x = 0
  · -- Both compositions fix the origin.
    simp [hx, radialPowerMap_zero]
  · have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    -- After rewriting the inner norm, the exponents add up to `s * t - 1`.
    calc
      radialPowerMap s (radialPowerMap t x)
          = Real.rpow ‖radialPowerMap t x‖ (s - 1) • (radialPowerMap t x) := by
            rfl
      _ = Real.rpow (‖x‖ ^ t) (s - 1) • (Real.rpow ‖x‖ (t - 1) • x) := by
            rw [norm_radialPowerMap t ht]
            rfl
      _ = (((‖x‖ ^ t) ^ (s - 1)) * ‖x‖ ^ (t - 1)) • x := by
            simp [smul_smul]
      _ = (‖x‖ ^ (t * (s - 1)) * ‖x‖ ^ (t - 1)) • x := by
            rw [Real.rpow_mul (norm_nonneg x)]
      _ = ‖x‖ ^ (s * t - 1) • x := by
            congr 1
            rw [← Real.rpow_add hxnorm]
            ring_nf
      _ = radialPowerMap (s * t) x := by
            rfl

/-- Helper for Problem 1-6: exponent `s⁻¹` is a left inverse to exponent `s` when `s > 0`. -/
lemma radialPowerMap_inv_left
    (s : ℝ) (hs : 0 < s) (x : EuclideanSpace ℝ (Fin n)) :
    radialPowerMap s (radialPowerMap s⁻¹ x) = x := by
  have hs_inv : 0 < s⁻¹ := by positivity
  -- The composition law collapses the exponents to `1`.
  calc
    radialPowerMap s (radialPowerMap s⁻¹ x) = radialPowerMap (s * s⁻¹) x := by
      simpa using radialPowerMap_mul s s⁻¹ hs_inv x
    _ = radialPowerMap 1 x := by rw [mul_inv_cancel₀ hs.ne']
    _ = x := radialPowerMap_one x

/-- Helper for Problem 1-6: exponent `s⁻¹` is also a right inverse to exponent `s` when `s > 0`. -/
lemma radialPowerMap_inv_right
    (s : ℝ) (hs : 0 < s) (x : EuclideanSpace ℝ (Fin n)) :
    radialPowerMap s⁻¹ (radialPowerMap s x) = x := by
  -- The same exponent product computation works in the opposite order.
  calc
    radialPowerMap s⁻¹ (radialPowerMap s x) = radialPowerMap (s⁻¹ * s) x := by
      simpa using radialPowerMap_mul s⁻¹ s hs x
    _ = radialPowerMap 1 x := by rw [inv_mul_cancel₀ hs.ne']
    _ = x := radialPowerMap_one x

/-- Helper for Problem 1-6: positive exponents make the radial power map continuous on all of
Euclidean space. -/
lemma continuous_radialPowerMap
    (s : Set.Ioi (0 : ℝ)) :
    Continuous (radialPowerMap (s : ℝ) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
  refine continuous_iff_continuousAt.2 ?_
  intro x
  by_cases hx : x = 0
  · subst hx
    -- At the origin, `‖radialPowerMap s x‖ = ‖x‖^s` tends to `0` because `s > 0`.
    have hpow :
        Continuous (fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y‖ ^ (s : ℝ)) := by
      exact (Real.continuous_rpow_const s.2.le).comp continuous_norm
    have hzero :
        Filter.Tendsto (radialPowerMap (s : ℝ))
          (nhds (0 : EuclideanSpace ℝ (Fin n))) (nhds 0) := by
      have hpow0 :
          Filter.Tendsto (fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y‖ ^ (s : ℝ))
            (nhds (0 : EuclideanSpace ℝ (Fin n))) (nhds 0) := by
        simpa [Real.zero_rpow s.2.ne'] using
          ((hpow.continuousAt : ContinuousAt
            (fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y‖ ^ (s : ℝ))
            (0 : EuclideanSpace ℝ (Fin n))).tendsto)
      refine squeeze_zero_norm (fun y : EuclideanSpace ℝ (Fin n) ↦ ?_) hpow0
      rw [norm_radialPowerMap (s : ℝ) s.2 y]
    simpa [ContinuousAt, radialPowerMap_zero] using hzero
  · -- Away from the origin, the scalar factor is a continuous `rpow`, hence so is the product.
    have hscalar :
        ContinuousAt
          (fun y : EuclideanSpace ℝ (Fin n) ↦ Real.rpow ‖y‖ ((s : ℝ) - 1)) x := by
      exact (Real.continuousAt_rpow_const ‖x‖ ((s : ℝ) - 1)
        (Or.inl (norm_pos_iff.mpr hx).ne')).comp continuousAt_id.norm
    simpa [radialPowerMap] using hscalar.smul continuousAt_id

/-- Helper for Problem 1-6: the positive radial map gives a canonical homeomorphism of the open
unit ball. -/
noncomputable def radial_power_unit_ball_homeomorph
    (s : Set.Ioi (0 : ℝ)) :
    Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  have hs_inv : 0 < ((s : ℝ)⁻¹) := by
    exact inv_pos.mpr s.2
  { toFun := fun x ↦
      ⟨radialPowerMap (s : ℝ) (x : EuclideanSpace ℝ (Fin n)),
        radialPowerMap_mem_unit_ball (s : ℝ) s.2 x.2⟩
    invFun := fun x ↦
      ⟨radialPowerMap ((s : ℝ)⁻¹) (x : EuclideanSpace ℝ (Fin n)),
        radialPowerMap_mem_unit_ball ((s : ℝ)⁻¹) hs_inv x.2⟩
    left_inv := by
      intro x
      -- The inverse branch with exponent `s⁻¹` cancels the forward branch with exponent `s`.
      apply Subtype.ext
      simpa using radialPowerMap_inv_right (s : ℝ) s.2 (x : EuclideanSpace ℝ (Fin n))
    right_inv := by
      intro x
      -- The forward branch likewise cancels the inverse branch on the unit ball.
      apply Subtype.ext
      simpa using radialPowerMap_inv_left (s : ℝ) s.2 (x : EuclideanSpace ℝ (Fin n))
    continuous_toFun := by
      -- Continuity on the subtype is inherited from the ambient radial map.
      exact Continuous.subtype_mk
        ((continuous_radialPowerMap s).comp continuous_subtype_val)
        (fun x ↦ radialPowerMap_mem_unit_ball (s : ℝ) s.2 x.2)
    continuous_invFun := by
      -- The same argument applies to the inverse exponent `s⁻¹`.
      exact Continuous.subtype_mk
        ((continuous_radialPowerMap ⟨(s : ℝ)⁻¹, hs_inv⟩).comp continuous_subtype_val)
        (fun x ↦ radialPowerMap_mem_unit_ball ((s : ℝ)⁻¹) hs_inv x.2) }

/-- Helper for Problem 1-6: the frontier of the unit ball sits inside the larger ball of radius
`2`. This is the set-theoretic input for the model-space piecewise extension. -/
lemma frontier_unit_ball_subset_ball_two :
    frontier (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ⊆ Metric.ball 0 2 := by
  intro x hx
  have hx_sphere : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    -- Rewrite the frontier of the open ball as the unit sphere.
    simpa [frontier_ball (0 : EuclideanSpace ℝ (Fin n)) (show (1 : ℝ) ≠ 0 by exact one_ne_zero)]
      using hx
  have hnorm : ‖x‖ = 1 := by
    -- On the sphere centered at the origin, distance to `0` is exactly the norm.
    simpa [Metric.sphere, dist_eq_norm] using hx_sphere
  -- The unit sphere is certainly contained in the open ball of radius `2`.
  simpa [Metric.mem_ball, dist_eq_norm, hnorm] using (show (1 : ℝ) < 2 by norm_num)

/-- Helper for Problem 1-6: the radial power map agrees with the identity on the frontier of the
unit ball. This is the boundary compatibility needed for the first `piecewise` construction. -/
lemma radialPowerMap_eqOn_frontier_unit_ball
    (s : ℝ) :
    Set.EqOn (radialPowerMap s) (fun x : EuclideanSpace ℝ (Fin n) ↦ x)
      (frontier (Metric.ball 0 1)) := by
  intro x hx
  have hx_sphere : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    -- Convert the frontier condition to the norm-one sphere.
    simpa [frontier_ball (0 : EuclideanSpace ℝ (Fin n)) (show (1 : ℝ) ≠ 0 by exact one_ne_zero)]
      using hx
  have hnorm : ‖x‖ = 1 := by
    -- The origin-centered sphere is the locus `‖x‖ = 1`.
    simpa [Metric.sphere, dist_eq_norm] using hx_sphere
  -- On `‖x‖ = 1`, the radial factor is `1`, so the map is the identity.
  simpa using radialPowerMap_eq_self_of_norm_eq_one s x hnorm

/-- Helper for Problem 1-6: positive radial powers preserve the closed unit ball. This is the
closed-set version needed for the supported piecewise extension on `Metric.ball 0 2`. -/
lemma radialPowerMap_mem_closed_unit_ball
    (s : ℝ) (hs : 0 < s) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.closedBall 0 1) :
    radialPowerMap s x ∈ Metric.closedBall 0 1 := by
  have hx_norm : ‖x‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  -- The norm formula reduces the closed-ball preservation claim to `r^s ≤ 1`.
  rw [Metric.mem_closedBall, dist_eq_norm]
  simpa [radialPowerMap_zero, sub_eq_add_neg, norm_radialPowerMap s hs x] using
    (Real.rpow_le_one (norm_nonneg x) hx_norm hs.le)

/-- Helper for Problem 1-6: the radial power map also agrees with the identity on the frontier of
the closed unit ball. This is the boundary compatibility for the closed-ball `piecewise`
homeomorphism on `Metric.ball 0 2`. -/
lemma radialPowerMap_eqOn_frontier_closed_unit_ball
    (s : ℝ) :
    Set.EqOn (radialPowerMap s) (fun x : EuclideanSpace ℝ (Fin n) ↦ x)
      (frontier (Metric.closedBall 0 1)) := by
  intro x hx
  have hx_sphere : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    -- Rewrite the frontier of the closed unit ball as the unit sphere.
    simpa [frontier_closedBall (0 : EuclideanSpace ℝ (Fin n))
      (show (1 : ℝ) ≠ 0 by exact one_ne_zero)] using hx
  have hnorm : ‖x‖ = 1 := by
    -- On the sphere centered at the origin, distance to `0` is the norm.
    simpa [Metric.sphere, dist_eq_norm] using hx_sphere
  -- The same unit-sphere computation gives the identity.
  simpa using radialPowerMap_eq_self_of_norm_eq_one s x hnorm

/-- Helper for Problem 1-6: postcomposing a chart in the maximal smooth atlas with a smooth local
self-diffeomorphism of the model space stays in the maximal smooth atlas. -/
lemma trans_mem_maximalAtlas_of_mem_groupoid
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M)
    {f : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (hf : f ∈ contDiffGroupoid ∞ (𝓡 n)) :
    e.trans f ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M := by
  -- Membership in the maximal atlas is tested by compatibility with the original atlas.
  rw [IsManifold.mem_maximalAtlas_iff]
  intro e' he'
  have he'max : e' ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M := by
    exact IsManifold.subset_maximalAtlas he'
  have hleft : e.symm.trans e' ∈ contDiffGroupoid ∞ (𝓡 n) := by
    exact IsManifold.compatible_of_mem_maximalAtlas he he'max
  have hright : e'.symm.trans e ∈ contDiffGroupoid ∞ (𝓡 n) := by
    exact IsManifold.compatible_of_mem_maximalAtlas he'max he
  constructor
  · -- The left transition factors as `f.symm` followed by the old transition from `e` to `e'`.
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid ∞ (𝓡 n)).trans ((contDiffGroupoid ∞ (𝓡 n)).symm hf) hleft
  · -- The right transition factors as the old transition from `e'` to `e`, followed by `f`.
    have hright' : (e'.symm.trans e).trans f ∈ contDiffGroupoid ∞ (𝓡 n) := by
      exact (contDiffGroupoid ∞ (𝓡 n)).trans hright hf
    simpa [OpenPartialHomeomorph.trans_assoc] using hright'

/-- Helper for Problem 1-6: the affine normalization from `Metric.ball c r` to `Metric.ball 0 2`
is a smooth coordinate change of the Euclidean model. -/
lemma ball_target_normalization_mem_contDiffGroupoid
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    ((OpenPartialHomeomorph.unitBallBall c r hr).symm.trans
      (OpenPartialHomeomorph.unitBallBall 0 2 (by positivity))) ∈ contDiffGroupoid ∞ (𝓡 n) := by
  -- The normalization is the composition of two smooth Euclidean ball charts.
  refine (contDiffGroupoid ∞ (𝓡 n)).trans ?_ ?_
  · exact (contDiffGroupoid ∞ (𝓡 n)).symm <| by
      rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
      constructor
      · simpa using
          ((OpenPartialHomeomorph.contDiff_unitBallBall hr :
            ContDiff ℝ (⊤ : ℕ∞) _).contDiffOn)
      · simpa using
          ((OpenPartialHomeomorph.contDiff_unitBallBall_symm hr :
            ContDiff ℝ (⊤ : ℕ∞) _).contDiffOn)
  · rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
    constructor
    · simpa using
        ((OpenPartialHomeomorph.contDiff_unitBallBall (show (0 : ℝ) < 2 by positivity) :
          ContDiff ℝ (⊤ : ℕ∞) _).contDiffOn)
    · simpa using
        ((OpenPartialHomeomorph.contDiff_unitBallBall_symm (show (0 : ℝ) < 2 by positivity) :
          ContDiff ℝ (⊤ : ℕ∞) _).contDiffOn)

/-- Helper for Problem 1-6: after shrinking `chartAt x0` to a small coordinate ball, one can
renormalize that ball to `Metric.ball 0 2` and stay inside the maximal smooth atlas. -/
lemma chart_at_point_with_ball_target
    [T2Space M] [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] (x0 : M) :
    ∃ chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      x0 ∈ chi.source ∧
      chi x0 = 0 ∧
      chi ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M ∧
      chi.target = Metric.ball 0 2 := by
  let e := chartAt (EuclideanSpace ℝ (Fin n)) x0
  let y0 : EuclideanSpace ℝ (Fin n) := e x0
  have hy0 : y0 ∈ e.target := by
    simpa [y0, e] using mem_chart_target (EuclideanSpace ℝ (Fin n)) x0
  rcases Metric.mem_nhds_iff.mp (chart_target_mem_nhds (EuclideanSpace ℝ (Fin n)) x0) with
    ⟨r, hrpos, hrsub⟩
  let s : Set M := e.source ∩ e ⁻¹' Metric.ball y0 r
  have hsopen : IsOpen s := by
    -- Restrict to the smaller coordinate ball around the chart center.
    exact e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball
  have hs_subset : s ⊆ e.source := by
    intro x hx
    exact hx.1
  let er : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) := e.restr s
  have her_source : er.source = s := by
    -- No extra source points are lost because `s` already lies in `e.source`.
    calc
      er.source = e.source ∩ s := by
        simp [er, hsopen.interior_eq]
      _ = s := Set.inter_eq_right.mpr hs_subset
  have her_target : er.target = Metric.ball y0 r := by
    -- The restricted chart lands exactly in the chosen Euclidean ball.
    calc
      er.target = e.target ∩ e.symm ⁻¹' interior s := by
        simp [er, PartialEquiv.restr_target]
      _ = e.target ∩ e.symm ⁻¹' s := by
        rw [hsopen.interior_eq]
      _ = e.target ∩ Metric.ball y0 r := by
        ext z
        constructor
        · intro hz
          have hz_target : z ∈ e.target := hz.1
          have hz_mem : e.symm z ∈ s := hz.2
          have hright : e (e.symm z) = z := e.right_inv hz_target
          have hball : z ∈ Metric.ball y0 r := by
            simpa [s, hright] using hz_mem.2
          exact ⟨hz_target, hball⟩
        · intro hz
          have hz_target : z ∈ e.target := hz.1
          have hz_mem : e.symm z ∈ s := by
            refine ⟨e.map_target hz_target, ?_⟩
            simpa [s, e.right_inv hz_target] using hz.2
          exact ⟨hz.1, hz_mem⟩
      _ = Metric.ball y0 r := Set.inter_eq_right.mpr hrsub
  let f : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
    (OpenPartialHomeomorph.unitBallBall y0 r hrpos).symm.trans
      (OpenPartialHomeomorph.unitBallBall 0 2 (by positivity))
  let chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) := er.trans f
  have he_max : e ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M := IsManifold.chart_mem_maximalAtlas x0
  have her_max : er ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M := by
    simpa [er] using restr_mem_maximalAtlas (contDiffGroupoid ∞ (𝓡 n)) he_max hsopen
  have hx0_source : x0 ∈ e.source := mem_chart_source (EuclideanSpace ℝ (Fin n)) x0
  have hx0_ball : e x0 ∈ Metric.ball y0 r := by
    simpa [y0] using hrpos
  have hx0_s : x0 ∈ s := ⟨hx0_source, hx0_ball⟩
  have hx0_er : er x0 = y0 := by
    simp [er, s, y0]
  have hf_source : f.source = Metric.ball y0 r := by
    -- The first Euclidean chart already maps `Metric.ball y0 r` into `Metric.ball 0 1`.
    calc
      f.source = Metric.ball y0 r ∩
          (OpenPartialHomeomorph.unitBallBall y0 r hrpos).symm ⁻¹' Metric.ball 0 1 := by
        simp [f, OpenPartialHomeomorph.trans_source]
      _ = Metric.ball y0 r := by
        refine Set.inter_eq_left.mpr ?_
        intro z hz
        exact (OpenPartialHomeomorph.unitBallBall y0 r hrpos).map_target hz
  have hy0_f_source : y0 ∈ f.source := by
    simpa [hf_source, y0] using hrpos
  have hy0_f : f y0 = 0 := by
    have hy0_source : (0 : EuclideanSpace ℝ (Fin n)) ∈
        (OpenPartialHomeomorph.unitBallBall y0 r hrpos).source := by
      simpa using (show (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 1 by simpa using zero_lt_one)
    have hy0_symm : (OpenPartialHomeomorph.unitBallBall y0 r hrpos).symm y0 =
        (0 : EuclideanSpace ℝ (Fin n)) := by
      simpa using (OpenPartialHomeomorph.unitBallBall y0 r hrpos).left_inv hy0_source
    simp [f, hy0_symm]
  refine ⟨chi, ?_, ?_, ?_, ?_⟩
  · -- The chosen point remains in the source after the Euclidean renormalization.
    simpa [chi, OpenPartialHomeomorph.trans_source, her_source, hx0_er] using ⟨hx0_s, hy0_f_source⟩
  · -- The renormalized chart sends `x0` to the origin.
    simp [chi, hx0_s, hx0_er, hy0_f]
  · -- Restriction and smooth postcomposition keep the chart in the maximal atlas.
    exact trans_mem_maximalAtlas_of_mem_groupoid her_max
      (ball_target_normalization_mem_contDiffGroupoid y0 hrpos)
  · -- The target has been normalized to the standard ball of radius `2`.
    calc
      chi.target = f.target ∩ f.symm ⁻¹' er.target := by
        simp [chi, OpenPartialHomeomorph.trans_target]
      _ = f.target := by
        refine Set.inter_eq_left.mpr ?_
        intro z hz
        have hz_source : f.symm z ∈ f.source := f.map_target hz
        simpa [hf_source, her_target]
          using hz_source
      _ = Metric.ball 0 2 := by
        calc
          f.target = Metric.ball 0 2 ∩
              (OpenPartialHomeomorph.unitBallBall 0 2 (by positivity)).symm ⁻¹'
                Metric.ball 0 1 := by
            simp [f, OpenPartialHomeomorph.trans_target]
          _ = Metric.ball 0 2 := by
            refine Set.inter_eq_left.mpr ?_
            intro z hz
            exact (OpenPartialHomeomorph.unitBallBall 0 2 (by positivity)).map_target hz

private def unitBallOpens :
    TopologicalSpace.Opens E :=
  ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

private lemma unitBallOpens_nonempty :
    Nonempty (unitBallOpens : TopologicalSpace.Opens E) := by
  refine ⟨(⟨(0 : E), ?_⟩ : (unitBallOpens : TopologicalSpace.Opens E))⟩
  change (0 : E) ∈ Metric.ball (0 : E) 1
  simpa [Metric.mem_ball, dist_eq_norm] using (show (0 : ℝ) < 1 by norm_num)

private noncomputable def unitBallSubtypeCoe :
    OpenPartialHomeomorph (unitBallOpens : TopologicalSpace.Opens E) E :=
  (unitBallOpens : TopologicalSpace.Opens E).openPartialHomeomorphSubtypeCoe unitBallOpens_nonempty

/-- Helper for Problem 1-6: the canonical ambient unit-ball radial branch. -/
noncomputable def radial_power_unit_ball_openPartialHomeomorph
    (s : Set.Ioi (0 : ℝ)) :
    OpenPartialHomeomorph E E :=
  let U : TopologicalSpace.Opens E := unitBallOpens
  let h : U ≃ₜ U := radial_power_unit_ball_homeomorph s
  let i : OpenPartialHomeomorph U E := unitBallSubtypeCoe
  (i.symm.trans h.toOpenPartialHomeomorph).trans i

/-- Helper for Problem 1-6: the ambient unit-ball radial branch has source exactly the unit ball. -/
lemma radial_power_unit_ball_openPartialHomeomorph_source
    (s : Set.Ioi (0 : ℝ)) :
    ((radial_power_unit_ball_openPartialHomeomorph s : OpenPartialHomeomorph E E)).source =
      Metric.ball 0 1 := by
  let U : TopologicalSpace.Opens E := unitBallOpens
  let i : OpenPartialHomeomorph U E := unitBallSubtypeCoe
  ext x
  simp [radial_power_unit_ball_openPartialHomeomorph, i, U, unitBallSubtypeCoe, unitBallOpens,
    OpenPartialHomeomorph.trans_source]

/-- Helper for Problem 1-6: the ambient unit-ball radial branch has target exactly the unit ball. -/
lemma radial_power_unit_ball_openPartialHomeomorph_target
    (s : Set.Ioi (0 : ℝ)) :
    ((radial_power_unit_ball_openPartialHomeomorph s : OpenPartialHomeomorph E E)).target =
      Metric.ball 0 1 := by
  let U : TopologicalSpace.Opens E := unitBallOpens
  let i : OpenPartialHomeomorph U E := unitBallSubtypeCoe
  ext x
  simp [radial_power_unit_ball_openPartialHomeomorph, i, U, unitBallSubtypeCoe, unitBallOpens,
    OpenPartialHomeomorph.trans_target]

/-- Helper for Problem 1-6: on the unit ball, the ambient branch is the radial power map. -/
lemma radial_power_unit_ball_openPartialHomeomorph_eqOn
    (s : Set.Ioi (0 : ℝ)) :
    Set.EqOn (radial_power_unit_ball_openPartialHomeomorph s : E → E)
      (radialPowerMap (s : ℝ)) (Metric.ball 0 1) := by
  let U : TopologicalSpace.Opens E := unitBallOpens
  let h : U ≃ₜ U := radial_power_unit_ball_homeomorph s
  let i : OpenPartialHomeomorph U E := unitBallSubtypeCoe
  intro x hx
  have hx_target' : x ∈ (unitBallSubtypeCoe).target := by
    simpa [unitBallSubtypeCoe, unitBallOpens] using hx
  have hx_target : x ∈ i.target := by
    simpa [i] using hx_target'
  have hi_symm : ((i.symm x : U) : EuclideanSpace ℝ (Fin n)) = x := by
    -- The subtype inclusion chart is the identity after applying its inverse on the target.
    simpa [i] using (unitBallSubtypeCoe).right_inv hx_target'
  -- Unfold the conjugation: move into the subtype, apply the explicit radial branch, and return.
  calc
    radial_power_unit_ball_openPartialHomeomorph s x = i (h (i.symm x)) := by
      simp [radial_power_unit_ball_openPartialHomeomorph, i, h, OpenPartialHomeomorph.trans_apply]
    _ = radialPowerMap (s : ℝ) (((i.symm x : U) : EuclideanSpace ℝ (Fin n))) := by
      rfl
    _ = radialPowerMap (s : ℝ) x := by
      rw [hi_symm]

/-- Helper for Problem 1-6: on the unit ball, the inverse ambient branch is the inverse radial
power map. -/
lemma radial_power_unit_ball_openPartialHomeomorph_symm_eqOn
    (s : Set.Ioi (0 : ℝ)) :
    Set.EqOn
      (((radial_power_unit_ball_openPartialHomeomorph s : OpenPartialHomeomorph E E)).symm : E → E)
      (radialPowerMap ((s : ℝ)⁻¹)) (Metric.ball 0 1) := by
  let U : TopologicalSpace.Opens E := unitBallOpens
  let h : U ≃ₜ U := radial_power_unit_ball_homeomorph s
  let i : OpenPartialHomeomorph U E := unitBallSubtypeCoe
  intro x hx
  have hx_target' : x ∈ (unitBallSubtypeCoe).target := by
    simpa [unitBallSubtypeCoe, unitBallOpens] using hx
  have hx_target : x ∈ i.target := by
    simpa [i] using hx_target'
  have hi_symm : ((i.symm x : U) : EuclideanSpace ℝ (Fin n)) = x := by
    -- The inverse ambient branch starts from the same subtype representative.
    simpa [i] using (unitBallSubtypeCoe).right_inv hx_target'
  -- The inverse conjugation uses the inverse exponent on the subtype chart.
  calc
    (radial_power_unit_ball_openPartialHomeomorph s).symm x = i (h.symm (i.symm x)) := by
      simp [radial_power_unit_ball_openPartialHomeomorph, i, h, OpenPartialHomeomorph.trans_apply,
        OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    _ = radialPowerMap ((s : ℝ)⁻¹) (((i.symm x : U) : EuclideanSpace ℝ (Fin n))) := by
      rfl
    _ = radialPowerMap ((s : ℝ)⁻¹) x := by
      rw [hi_symm]

/-- Helper for Problem 1-6: the closed unit ball is contained in the open ball of radius `2`. -/
lemma mem_ball_two_of_mem_closed_unit_ball
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.closedBall 0 1) :
    x ∈ Metric.ball 0 2 := by
  have hx_norm : ‖x‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  -- The norm bound `‖x‖ ≤ 1` is stronger than the radius-`2` ball condition.
  simpa [Metric.mem_ball, dist_eq_norm] using (show ‖x‖ < 2 by linarith)

/-- Helper for Problem 1-6: positive radial powers send the closed unit ball into the ambient
ball of radius `2`. -/
lemma radialPowerMap_mem_ball_two_of_mem_closed_unit_ball
    (s : ℝ) (hs : 0 < s) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.closedBall 0 1) :
    radialPowerMap s x ∈ Metric.ball 0 2 := by
  -- First stay inside the closed unit ball, then use the fixed inclusion into `Metric.ball 0 2`.
  exact mem_ball_two_of_mem_closed_unit_ball
    (radialPowerMap_mem_closed_unit_ball s hs hx)

/-- Helper for Problem 1-6: the supported twist applies the radial branch on the closed unit ball
and is the identity outside. -/
noncomputable def supportedRadialTwist
    (s : Set.Ioi (0 : ℝ)) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  @Set.piecewise (EuclideanSpace ℝ (Fin n)) (fun _ ↦ EuclideanSpace ℝ (Fin n))
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (radialPowerMap (s : ℝ)) (fun x ↦ x) (Classical.decPred _)

/-- Helper for Problem 1-6: the inverse supported twist uses the reciprocal exponent on the closed
unit ball and is the identity outside. -/
noncomputable def supportedRadialTwistInv
    (s : Set.Ioi (0 : ℝ)) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  @Set.piecewise (EuclideanSpace ℝ (Fin n)) (fun _ ↦ EuclideanSpace ℝ (Fin n))
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (radialPowerMap ((s : ℝ)⁻¹)) (fun x ↦ x) (Classical.decPred _)

/-- Helper for Problem 1-6: on the closed unit ball, the supported twist is the radial power map.
-/
lemma supportedRadialTwist_apply_of_mem_closedBall
    (s : Set.Ioi (0 : ℝ)) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.closedBall 0 1) :
    supportedRadialTwist s x = radialPowerMap (s : ℝ) x := by
  classical
  -- Inside the support, the `piecewise` definition chooses the radial branch.
  simp [supportedRadialTwist, hx]

/-- Helper for Problem 1-6: outside the closed unit ball, the supported twist is the identity. -/
lemma supportedRadialTwist_apply_of_notMem_closedBall
    (s : Set.Ioi (0 : ℝ)) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∉ Metric.closedBall 0 1) :
    supportedRadialTwist s x = x := by
  classical
  -- Off the support, the `piecewise` definition keeps the point fixed.
  simp [supportedRadialTwist, hx]

/-- Helper for Problem 1-6: on the closed unit ball, the inverse supported twist is the inverse
radial power map. -/
lemma supportedRadialTwistInv_apply_of_mem_closedBall
    (s : Set.Ioi (0 : ℝ)) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.closedBall 0 1) :
    supportedRadialTwistInv s x = radialPowerMap ((s : ℝ)⁻¹) x := by
  classical
  -- Inside the support, the inverse `piecewise` definition chooses the reciprocal exponent.
  simp [supportedRadialTwistInv, hx]

/-- Helper for Problem 1-6: outside the closed unit ball, the inverse supported twist is also the
identity. -/
lemma supportedRadialTwistInv_apply_of_notMem_closedBall
    (s : Set.Ioi (0 : ℝ)) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∉ Metric.closedBall 0 1) :
    supportedRadialTwistInv s x = x := by
  classical
  -- Away from the support, the inverse branch is trivial.
  simp [supportedRadialTwistInv, hx]

/-- Helper for Problem 1-6: the reciprocal supported twist is a left inverse to the supported
twist. -/
lemma supportedRadialTwist_leftInverse
    (s : Set.Ioi (0 : ℝ)) :
    Function.LeftInverse (supportedRadialTwistInv s : E → E)
      (supportedRadialTwist s) := by
  intro x
  by_cases hx : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
  · have hfx : radialPowerMap (s : ℝ) x ∈ Metric.closedBall 0 1 := by
      exact radialPowerMap_mem_closed_unit_ball (s : ℝ) s.2 hx
    -- On the support, the two radial exponents cancel each other.
    rw [supportedRadialTwist_apply_of_mem_closedBall s hx]
    rw [supportedRadialTwistInv_apply_of_mem_closedBall s hfx]
    simpa using radialPowerMap_inv_right (s : ℝ) s.2 x
  · -- Outside the support, both piecewise maps are the identity.
    rw [supportedRadialTwist_apply_of_notMem_closedBall s hx]
    rw [supportedRadialTwistInv_apply_of_notMem_closedBall s hx]

/-- Helper for Problem 1-6: the reciprocal supported twist is also a right inverse to the
supported twist. -/
lemma supportedRadialTwist_rightInverse
    (s : Set.Ioi (0 : ℝ)) :
    Function.RightInverse (supportedRadialTwistInv s : E → E)
      (supportedRadialTwist s) := by
  intro x
  by_cases hx : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
  · have hfx : radialPowerMap ((s : ℝ)⁻¹) x ∈ Metric.closedBall 0 1 := by
      have hs_inv : 0 < ((s : ℝ)⁻¹) := by
        exact inv_pos.mpr s.2
      exact radialPowerMap_mem_closed_unit_ball ((s : ℝ)⁻¹) hs_inv hx
    -- On the support, composing in the other order still cancels the exponents.
    rw [supportedRadialTwistInv_apply_of_mem_closedBall s hx]
    rw [supportedRadialTwist_apply_of_mem_closedBall s hfx]
    simpa using radialPowerMap_inv_left (s : ℝ) s.2 x
  · -- Outside the support, the forward and inverse maps are both the identity.
    rw [supportedRadialTwistInv_apply_of_notMem_closedBall s hx]
    rw [supportedRadialTwist_apply_of_notMem_closedBall s hx]

/-- Helper for Problem 1-6: the supported twist is continuous because the radial branch agrees
with the identity on the frontier of the closed unit ball. -/
lemma continuous_supportedRadialTwist
    (s : Set.Ioi (0 : ℝ)) :
    Continuous (supportedRadialTwist s : E → E) := by
  classical
  -- The only gluing input is the boundary identity on the unit sphere.
  refine (continuous_radialPowerMap s).piecewise ?_ continuous_id
  intro x hx
  exact radialPowerMap_eqOn_frontier_closed_unit_ball (s : ℝ) hx

/-- Helper for Problem 1-6: the inverse supported twist is continuous by the same frontier
compatibility. -/
lemma continuous_supportedRadialTwistInv
    (s : Set.Ioi (0 : ℝ)) :
    Continuous (supportedRadialTwistInv s : E → E) := by
  classical
  have hs_inv : 0 < ((s : ℝ)⁻¹) := by
    exact inv_pos.mpr s.2
  -- The reciprocal exponent fixes the unit sphere as well, so the same gluing argument works.
  refine (continuous_radialPowerMap ⟨(s : ℝ)⁻¹, hs_inv⟩).piecewise ?_ continuous_id
  intro x hx
  exact radialPowerMap_eqOn_frontier_closed_unit_ball ((s : ℝ)⁻¹) hx

/-- Helper for Problem 1-6: the supported twist is a global homeomorphism of the Euclidean model
space. -/
noncomputable def supportedRadialTwistHomeomorph
    (s : Set.Ioi (0 : ℝ)) :
    EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) where
  toEquiv :=
    { toFun := supportedRadialTwist s
      invFun := supportedRadialTwistInv s
      left_inv := supportedRadialTwist_leftInverse s
      right_inv := supportedRadialTwist_rightInverse s }
  continuous_toFun := continuous_supportedRadialTwist s
  continuous_invFun := continuous_supportedRadialTwistInv s

/-- Helper for Problem 1-6: the supported twist preserves the ambient ball of radius `2`. -/
lemma supportedRadialTwist_mapsTo_ball_two
    (s : Set.Ioi (0 : ℝ)) :
    Set.MapsTo (supportedRadialTwist s : E → E) (Metric.ball 0 2) (Metric.ball 0 2) := by
  intro x hx
  by_cases hclosed : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
  · -- Inside the support, the radial branch stays in the larger ambient ball.
    rw [supportedRadialTwist_apply_of_mem_closedBall s hclosed]
    exact radialPowerMap_mem_ball_two_of_mem_closed_unit_ball (s : ℝ) s.2 hclosed
  · -- Outside the support, the supported twist is the identity.
    rw [supportedRadialTwist_apply_of_notMem_closedBall s hclosed]
    exact hx

/-- Helper for Problem 1-6: the inverse supported twist also preserves the ambient ball of radius
`2`. -/
lemma supportedRadialTwistInv_mapsTo_ball_two
    (s : Set.Ioi (0 : ℝ)) :
    Set.MapsTo (supportedRadialTwistInv s : E → E) (Metric.ball 0 2) (Metric.ball 0 2) := by
  have hs_inv : 0 < ((s : ℝ)⁻¹) := by
    exact inv_pos.mpr s.2
  intro x hx
  by_cases hclosed : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
  · -- On the support, use the same norm control for the reciprocal exponent.
    rw [supportedRadialTwistInv_apply_of_mem_closedBall s hclosed]
    exact radialPowerMap_mem_ball_two_of_mem_closed_unit_ball ((s : ℝ)⁻¹) hs_inv hclosed
  · -- Off the support, the inverse supported twist is the identity.
    rw [supportedRadialTwistInv_apply_of_notMem_closedBall s hclosed]
    exact hx

/-- Helper for Problem 1-6: the supported twist maps `Metric.ball 0 2` onto itself. -/
lemma supportedRadialTwist_image_ball_two
    (s : Set.Ioi (0 : ℝ)) :
    (supportedRadialTwist s : E → E) '' Metric.ball 0 2 = Metric.ball 0 2 := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    exact supportedRadialTwist_mapsTo_ball_two s hx
  · intro y hy
    -- Surjectivity on the ball follows by pulling back with the explicit inverse branch.
    refine ⟨supportedRadialTwistInv s y,
      supportedRadialTwistInv_mapsTo_ball_two s hy, ?_⟩
    exact supportedRadialTwist_rightInverse s y

/-- Helper for Problem 1-6: the supported radial branch on `Metric.ball 0 2`. -/
noncomputable def supported_radial_ball_two_openPartialHomeomorph
    (s : Set.Ioi (0 : ℝ)) :
    OpenPartialHomeomorph E E :=
  let h : E ≃ₜ E :=
    supportedRadialTwistHomeomorph s
  h.toOpenPartialHomeomorphOfImageEq (Metric.ball 0 2) Metric.isOpen_ball
    (Metric.ball 0 2) (supportedRadialTwist_image_ball_two s)

/-- Helper for Problem 1-6: the supported radial branch has source exactly `Metric.ball 0 2`. -/
lemma supported_radial_ball_two_openPartialHomeomorph_source
    (s : Set.Ioi (0 : ℝ)) :
    ((supported_radial_ball_two_openPartialHomeomorph s : OpenPartialHomeomorph E E)).source =
      Metric.ball 0 2 := by
  simp [supported_radial_ball_two_openPartialHomeomorph]

/-- Helper for Problem 1-6: the supported radial branch has target exactly `Metric.ball 0 2`. -/
lemma supported_radial_ball_two_openPartialHomeomorph_target
    (s : Set.Ioi (0 : ℝ)) :
    ((supported_radial_ball_two_openPartialHomeomorph s : OpenPartialHomeomorph E E)).target =
      Metric.ball 0 2 := by
  simp [supported_radial_ball_two_openPartialHomeomorph]

/-- Helper for Problem 1-6: on the closed unit ball, the supported branch is the radial twist. -/
lemma supported_radial_ball_two_openPartialHomeomorph_eqOn_closedBall
    (s : Set.Ioi (0 : ℝ)) :
    Set.EqOn (supported_radial_ball_two_openPartialHomeomorph s : E → E)
      (radialPowerMap (s : ℝ)) (Metric.closedBall 0 1) := by
  intro x hx
  change supportedRadialTwist s x = radialPowerMap (s : ℝ) x
  exact supportedRadialTwist_apply_of_mem_closedBall s hx

/-- Helper for Problem 1-6: on the annulus between radii `1` and `2`, the supported branch is the
identity. -/
lemma supported_radial_ball_two_openPartialHomeomorph_eqOn_annulus
    (s : Set.Ioi (0 : ℝ)) :
    Set.EqOn (supported_radial_ball_two_openPartialHomeomorph s : E → E)
      (fun x ↦ x) (Metric.ball 0 2 \ Metric.closedBall 0 1) := by
  intro x hx
  change supportedRadialTwist s x = x
  exact supportedRadialTwist_apply_of_notMem_closedBall s hx.2

/-- Helper for Problem 1-6: on the closed unit ball, the inverse supported branch is the inverse
radial twist. -/
lemma supported_radial_ball_two_openPartialHomeomorph_symm_eqOn_closedBall
    (s : Set.Ioi (0 : ℝ)) :
    Set.EqOn
      (((supported_radial_ball_two_openPartialHomeomorph s : OpenPartialHomeomorph E E)).symm :
        E → E)
      (radialPowerMap ((s : ℝ)⁻¹)) (Metric.closedBall 0 1) := by
  intro x hx
  change supportedRadialTwistInv s x = radialPowerMap ((s : ℝ)⁻¹) x
  exact supportedRadialTwistInv_apply_of_mem_closedBall s hx

/-- Helper for Problem 1-6: on the annulus between radii `1` and `2`, the inverse supported
branch is the identity. -/
lemma supported_radial_ball_two_openPartialHomeomorph_symm_eqOn_annulus
    (s : Set.Ioi (0 : ℝ)) :
    Set.EqOn
      (((supported_radial_ball_two_openPartialHomeomorph s : OpenPartialHomeomorph E E)).symm :
        E → E)
      (fun x ↦ x) (Metric.ball 0 2 \ Metric.closedBall 0 1) := by
  intro x hx
  change supportedRadialTwistInv s x = x
  exact supportedRadialTwistInv_apply_of_notMem_closedBall s hx.2

/-- Helper for Problem 1-6: conjugate the supported `Metric.ball 0 2` model-space twist through a
chart whose target is exactly that Euclidean ball. -/
noncomputable def chart_conjugated_supported_twist
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (s : Set.Ioi (0 : ℝ)) :
    OpenPartialHomeomorph M M :=
  (chi.trans (supported_radial_ball_two_openPartialHomeomorph s)).trans chi.symm

/-- Helper for Problem 1-6: the chart-conjugated supported twist is defined on the whole chart
source. -/
lemma chart_conjugated_supported_twist_source
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hchi_target : chi.target = Metric.ball 0 2)
    (s : Set.Ioi (0 : ℝ)) :
    (chart_conjugated_supported_twist chi s).source = chi.source := by
  have hinner_source :
      (chi.trans (supported_radial_ball_two_openPartialHomeomorph s)).source =
        chi.source := by
    -- The inner composition is defined everywhere on `chi.source` because `chi.target` is exactly
    -- the ambient ball where the supported branch lives.
    calc
      (chi.trans (supported_radial_ball_two_openPartialHomeomorph s)).source
          = chi.source ∩
              chi ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2 := by
            rw [OpenPartialHomeomorph.trans_source,
              supported_radial_ball_two_openPartialHomeomorph_source]
      _ = chi.source := by
            refine Set.inter_eq_left.mpr ?_
            intro x hx
            simpa [hchi_target] using chi.map_source hx
  have hinner_target :
      (chi.trans (supported_radial_ball_two_openPartialHomeomorph s)).target =
        Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2 := by
    -- Likewise, the inner composition still lands in the same ambient Euclidean ball.
    calc
      (chi.trans (supported_radial_ball_two_openPartialHomeomorph s)).target
          = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2 ∩
              (supported_radial_ball_two_openPartialHomeomorph s).symm ⁻¹' chi.target := by
            rw [OpenPartialHomeomorph.trans_target,
              supported_radial_ball_two_openPartialHomeomorph_target]
      _ = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2 := by
            refine Set.inter_eq_left.mpr ?_
            intro y hy
            have hy_target :
                y ∈ (supported_radial_ball_two_openPartialHomeomorph s).target := by
              simpa [supported_radial_ball_two_openPartialHomeomorph_target] using hy
            have hy_source :
                (supported_radial_ball_two_openPartialHomeomorph s).symm y ∈
                  (supported_radial_ball_two_openPartialHomeomorph s).source := by
              exact
                (supported_radial_ball_two_openPartialHomeomorph s).map_target hy_target
            rw [supported_radial_ball_two_openPartialHomeomorph_source] at hy_source
            simpa [hchi_target] using hy_source
  -- The outer postcomposition by `chi.symm` is therefore defined on the same chart source.
  calc
    (chart_conjugated_supported_twist chi s).source
        = (chi.trans (supported_radial_ball_two_openPartialHomeomorph s)).source ∩
            (chi.trans (supported_radial_ball_two_openPartialHomeomorph s)) ⁻¹'
              chi.target := by
          rw [chart_conjugated_supported_twist, OpenPartialHomeomorph.trans_source]
          simp
    _ = chi.source ∩
          (chi.trans (supported_radial_ball_two_openPartialHomeomorph s)) ⁻¹' chi.target := by
          rw [hinner_source]
    _ = chi.source := by
          refine Set.inter_eq_left.mpr ?_
          intro x hx
          have hx_inner :
              x ∈ (chi.trans (supported_radial_ball_two_openPartialHomeomorph s)).source := by
            rw [hinner_source]
            exact hx
          have hx_inner_target :
              (chi.trans (supported_radial_ball_two_openPartialHomeomorph s)) x ∈
                (chi.trans (supported_radial_ball_two_openPartialHomeomorph s)).target := by
            exact
              (chi.trans (supported_radial_ball_two_openPartialHomeomorph s)).map_source
                hx_inner
          rw [hinner_target] at hx_inner_target
          simpa [hchi_target] using hx_inner_target

/-- Helper for Problem 1-6: the chart-conjugated supported twist also lands in the whole chart
source. -/
lemma chart_conjugated_supported_twist_target
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hchi_target : chi.target = Metric.ball 0 2)
    (s : Set.Ioi (0 : ℝ)) :
    (chart_conjugated_supported_twist chi s).target = chi.source := by
  have hinner_target :
      (chi.trans (supported_radial_ball_two_openPartialHomeomorph s)).target =
        Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2 := by
    -- The conjugated branch still has Euclidean target `Metric.ball 0 2` before returning by
    -- `chi.symm`.
    calc
      (chi.trans (supported_radial_ball_two_openPartialHomeomorph s)).target
          = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2 ∩
              (supported_radial_ball_two_openPartialHomeomorph s).symm ⁻¹' chi.target := by
            rw [OpenPartialHomeomorph.trans_target,
              supported_radial_ball_two_openPartialHomeomorph_target]
      _ = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2 := by
            refine Set.inter_eq_left.mpr ?_
            intro y hy
            have hy_target :
                y ∈ (supported_radial_ball_two_openPartialHomeomorph s).target := by
              simpa [supported_radial_ball_two_openPartialHomeomorph_target] using hy
            have hy_source :
                (supported_radial_ball_two_openPartialHomeomorph s).symm y ∈
                  (supported_radial_ball_two_openPartialHomeomorph s).source := by
              exact
                (supported_radial_ball_two_openPartialHomeomorph s).map_target hy_target
            rw [supported_radial_ball_two_openPartialHomeomorph_source] at hy_source
            simpa [hchi_target] using hy_source
  -- After composing with `chi.symm`, the target becomes the original chart source.
  calc
    (chart_conjugated_supported_twist chi s).target
        = chi.source ∩
            chi ⁻¹' (chi.trans (supported_radial_ball_two_openPartialHomeomorph s)).target := by
          rw [chart_conjugated_supported_twist, OpenPartialHomeomorph.trans_target]
          simp
    _ = chi.source ∩ chi ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2 := by
          rw [hinner_target]
    _ = chi.source := by
          refine Set.inter_eq_left.mpr ?_
          intro x hx
          simpa [hchi_target] using chi.map_source hx

/-- Helper for Problem 1-6: on the pulled-back closed unit ball, the chart-conjugated twist is
the conjugated radial power map. -/
lemma chart_conjugated_supported_twist_eqOn_closed_unit_ball
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (s : Set.Ioi (0 : ℝ)) :
    Set.EqOn (chart_conjugated_supported_twist chi s)
      (fun x ↦ chi.symm (radialPowerMap (s : ℝ) (chi x)))
      (chi.source ∩ chi ⁻¹' Metric.closedBall 0 1) := by
  intro x hx
  -- Inside the pulled-back closed unit ball, the supported Euclidean branch is exactly the radial
  -- power map.
  calc
    chart_conjugated_supported_twist chi s x
        = chi.symm
            ((supported_radial_ball_two_openPartialHomeomorph s) (chi x)) := by
              rfl
    _ = chi.symm (radialPowerMap (s : ℝ) (chi x)) := by
          rw [supported_radial_ball_two_openPartialHomeomorph_eqOn_closedBall s hx.2]

/-- Helper for Problem 1-6: outside the pulled-back closed unit ball but still in the chart
source, the chart-conjugated twist is the identity. -/
lemma chart_conjugated_supported_twist_eqOn_annulus
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hchi_target : chi.target = Metric.ball 0 2)
    (s : Set.Ioi (0 : ℝ)) :
    Set.EqOn (chart_conjugated_supported_twist chi s)
      (fun x ↦ x) (chi.source \ chi ⁻¹' Metric.closedBall 0 1) := by
  intro x hx
  have hx_ball_two : chi x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2 := by
    simpa [hchi_target] using chi.map_source hx.1
  have hx_annulus : chi x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2 \ Metric.closedBall 0 1 := by
    exact ⟨hx_ball_two, hx.2⟩
  -- On the annulus where the Euclidean supported twist is trivial, the conjugated map is also
  -- trivial after cancelling `chi.symm` against `chi`.
  calc
    chart_conjugated_supported_twist chi s x
        = chi.symm
            ((supported_radial_ball_two_openPartialHomeomorph s) (chi x)) := by
              rfl
    _ = chi.symm (chi x) := by
          rw [supported_radial_ball_two_openPartialHomeomorph_eqOn_annulus s hx_annulus]
    _ = x := chi.left_inv hx.1

/-- Helper for Problem 1-6: on the pulled-back closed unit ball, the inverse chart-conjugated
twist uses the reciprocal radial exponent. -/
lemma chart_conjugated_supported_twist_symm_eqOn_closed_unit_ball
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (s : Set.Ioi (0 : ℝ)) :
    Set.EqOn (chart_conjugated_supported_twist chi s).symm
      (fun x ↦ chi.symm (radialPowerMap ((s : ℝ)⁻¹) (chi x)))
      (chi.source ∩ chi ⁻¹' Metric.closedBall 0 1) := by
  intro x hx
  -- The inverse local branch is the reciprocal supported twist, so on the same pulled-back closed
  -- unit ball it becomes the reciprocal radial power map.
  calc
    (chart_conjugated_supported_twist chi s).symm x
        = chi.symm
            ((supported_radial_ball_two_openPartialHomeomorph s).symm (chi x)) := by
              rfl
    _ = chi.symm (radialPowerMap ((s : ℝ)⁻¹) (chi x)) := by
          rw [supported_radial_ball_two_openPartialHomeomorph_symm_eqOn_closedBall s hx.2]

/-- Helper for Problem 1-6: the compact support set obtained by pulling the closed unit ball back
through the distinguished chart. -/
def pulledBackClosedUnitBall
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) : Set M :=
  chi.source ∩ chi ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1

/-- Helper for Problem 1-6: the pulled-back closed unit ball is compact in the ambient manifold.
-/
lemma pulledBackClosedUnitBall_isCompact
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
    (chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hchi_target : chi.target = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2) :
    IsCompact (pulledBackClosedUnitBall chi) := by
  let f : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 → M := fun y ↦ chi.symm y
  have hcont_f : Continuous f := by
    -- The inverse chart is continuous on the whole closed unit ball because that ball sits inside
    -- the chart target `Metric.ball 0 2`.
    refine chi.continuousOn_symm.comp_continuous continuous_subtype_val ?_
    intro y
    have hy_ball_two : (y : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 2 := by
      exact mem_ball_two_of_mem_closed_unit_ball y.2
    simpa [hchi_target] using hy_ball_two
  have himage :
      Set.range f = pulledBackClosedUnitBall chi := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      have hy_target : ((y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
          EuclideanSpace ℝ (Fin n)) ∈ chi.target := by
        have hy_ball_two : ((y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
            EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 2 := by
          exact mem_ball_two_of_mem_closed_unit_ball y.2
        simpa [hchi_target] using hy_ball_two
      -- On the compact model ball, `chi.symm` lands in the pulled-back compact support.
      refine ⟨chi.map_target hy_target, ?_⟩
      show chi (f y) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
      simpa [f, chi.right_inv hy_target] using
        (show ((y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
          EuclideanSpace ℝ (Fin n)) ∈ Metric.closedBall 0 1 from y.2)
    · intro hx
      -- Every point of the pulled-back support comes from its chart coordinate in the closed ball.
      refine ⟨⟨chi x, hx.2⟩, ?_⟩
      exact chi.left_inv hx.1
  letI : CompactSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
  -- The compact support is the range of the continuous inverse chart on the compact closed ball.
  rw [← himage]
  exact isCompact_range hcont_f

/-- Helper for Problem 1-6: the pulled-back closed unit ball is closed in the ambient manifold.
-/
lemma pulledBackClosedUnitBall_isClosed
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
    (chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hchi_target : chi.target = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2) :
    IsClosed (pulledBackClosedUnitBall chi) := by
  -- Compact subsets of the Hausdorff manifold are closed.
  exact (pulledBackClosedUnitBall_isCompact chi hchi_target).isClosed

/-- Helper for Problem 1-6: boundary points of the pulled-back closed unit ball stay in the chart
source and map to the unit sphere. -/
lemma frontier_pulledBackClosedUnitBall_subset
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
    (chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hchi_target : chi.target = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2) :
    frontier (pulledBackClosedUnitBall chi) ⊆
      chi.source ∩ chi ⁻¹' Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  intro x hx
  have hK_closed : IsClosed (pulledBackClosedUnitBall chi) :=
    pulledBackClosedUnitBall_isClosed chi hchi_target
  have hxK : x ∈ pulledBackClosedUnitBall chi := hK_closed.frontier_subset hx
  refine ⟨hxK.1, ?_⟩
  have hnotInterior : x ∉ interior (pulledBackClosedUnitBall chi) := by
    exact (mem_frontier_iff_notMem_interior hxK).1 hx
  have hnotBall : chi x ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro hxball
    have hball_open : IsOpen (chi.source ∩ chi ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
      chi.continuousOn.isOpen_inter_preimage chi.open_source Metric.isOpen_ball
    have hxInterior : x ∈ interior (pulledBackClosedUnitBall chi) := by
      -- Points whose chart coordinate lies in the open unit ball are interior to the pulled-back
      -- closed ball support.
      rw [mem_interior]
      refine ⟨chi.source ∩ chi ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1, ?_, hball_open,
        ⟨hxK.1, hxball⟩⟩
      intro y hy
      exact ⟨hy.1, Metric.ball_subset_closedBall hy.2⟩
    exact hnotInterior hxInterior
  have hnorm_le : ‖chi x‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hxK.2
  have hnorm_not_lt : ¬ ‖chi x‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hnotBall
  have hnorm_eq : ‖chi x‖ = 1 := le_antisymm hnorm_le (le_of_not_gt hnorm_not_lt)
  -- Boundary points therefore land exactly on the unit sphere in the chart coordinates.
  simpa [Metric.sphere, dist_eq_norm, hnorm_eq]

/-- Helper for Problem 1-6: the chart-conjugated twist preserves the pulled-back closed unit ball.
-/
lemma chart_conjugated_supported_twist_mapsTo_pulledBackClosedUnitBall
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hchi_target : chi.target = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2)
    (s : Set.Ioi (0 : ℝ)) :
    Set.MapsTo (chart_conjugated_supported_twist chi s)
      (pulledBackClosedUnitBall chi) (pulledBackClosedUnitBall chi) := by
  intro x hx
  let e := chart_conjugated_supported_twist chi s
  have hsource : e.source = chi.source :=
    chart_conjugated_supported_twist_source chi hchi_target s
  have htarget : e.target = chi.source :=
    chart_conjugated_supported_twist_target chi hchi_target s
  have hx_source_e : x ∈ e.source := by
    rw [hsource]
    exact hx.1
  have hradial_closed :
      radialPowerMap (s : ℝ) (chi x) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    exact radialPowerMap_mem_closed_unit_ball (s : ℝ) s.2 hx.2
  have hradial_target :
      radialPowerMap (s : ℝ) (chi x) ∈ chi.target := by
    have hradial_ball_two :
        radialPowerMap (s : ℝ) (chi x) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2 := by
      exact mem_ball_two_of_mem_closed_unit_ball hradial_closed
    simpa [hchi_target] using hradial_ball_two
  refine ⟨?_, ?_⟩
  · -- The local twist still lands in the chart source after conjugation.
    simpa [htarget] using e.map_source hx_source_e
  · -- In chart coordinates, the image still lies in the closed unit ball.
    have hchi_image :
        chi (e x) = radialPowerMap (s : ℝ) (chi x) := by
      rw [chart_conjugated_supported_twist_eqOn_closed_unit_ball chi s hx]
      simpa using chi.right_inv hradial_target
    show chi (e x) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
    simpa [hchi_image] using hradial_closed

/-- Helper for Problem 1-6: the inverse chart-conjugated twist also preserves the pulled-back
closed unit ball. -/
lemma chart_conjugated_supported_twist_symm_mapsTo_pulledBackClosedUnitBall
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hchi_target : chi.target = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2)
    (s : Set.Ioi (0 : ℝ)) :
    Set.MapsTo (chart_conjugated_supported_twist chi s).symm
      (pulledBackClosedUnitBall chi) (pulledBackClosedUnitBall chi) := by
  intro x hx
  let e := chart_conjugated_supported_twist chi s
  have hsource : e.source = chi.source :=
    chart_conjugated_supported_twist_source chi hchi_target s
  have htarget : e.target = chi.source :=
    chart_conjugated_supported_twist_target chi hchi_target s
  have hx_target_e : x ∈ e.target := by
    rw [htarget]
    exact hx.1
  have hs_inv : 0 < ((s : ℝ)⁻¹) := by
    exact inv_pos.mpr s.2
  have hradial_closed :
      radialPowerMap ((s : ℝ)⁻¹) (chi x) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    exact radialPowerMap_mem_closed_unit_ball ((s : ℝ)⁻¹) hs_inv hx.2
  have hradial_target :
      radialPowerMap ((s : ℝ)⁻¹) (chi x) ∈ chi.target := by
    have hradial_ball_two :
        radialPowerMap ((s : ℝ)⁻¹) (chi x) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2 := by
      exact mem_ball_two_of_mem_closed_unit_ball hradial_closed
    simpa [hchi_target] using hradial_ball_two
  refine ⟨?_, ?_⟩
  · -- The inverse local twist stays inside the same chart source.
    simpa [hsource] using e.map_target hx_target_e
  · -- In chart coordinates, the inverse branch also stays inside the closed unit ball.
    have hchi_image :
        chi (e.symm x) = radialPowerMap ((s : ℝ)⁻¹) (chi x) := by
      rw [chart_conjugated_supported_twist_symm_eqOn_closed_unit_ball chi s hx]
      simpa using chi.right_inv hradial_target
    show chi (e.symm x) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
    simpa [hchi_image] using hradial_closed

/-- Helper for Problem 1-6: along the frontier of the pulled-back support, the chart-conjugated
twist agrees with the identity. -/
lemma chart_conjugated_supported_twist_eqOn_frontier_pulledBackClosedUnitBall
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
    (chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hchi_target : chi.target = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2)
    (s : Set.Ioi (0 : ℝ)) :
    Set.EqOn (chart_conjugated_supported_twist chi s) (fun x ↦ x)
      (frontier (pulledBackClosedUnitBall chi)) := by
  intro x hx
  have hxfront :
      x ∈ chi.source ∩ chi ⁻¹' Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    frontier_pulledBackClosedUnitBall_subset chi hchi_target hx
  have hnorm : ‖chi x‖ = 1 := by
    simpa [Metric.sphere, dist_eq_norm] using hxfront.2
  -- On the frontier, the conjugated radial map fixes the point because the radial factor is `1`.
  calc
    chart_conjugated_supported_twist chi s x
        = chi.symm (radialPowerMap (s : ℝ) (chi x)) := by
          apply chart_conjugated_supported_twist_eqOn_closed_unit_ball chi s
          exact ⟨hxfront.1, Metric.sphere_subset_closedBall hxfront.2⟩
    _ = chi.symm (chi x) := by
          rw [radialPowerMap_eq_self_of_norm_eq_one (s : ℝ) (chi x) hnorm]
    _ = x := chi.left_inv hxfront.1

/-- Helper for Problem 1-6: along the frontier of the pulled-back support, the inverse
chart-conjugated twist also agrees with the identity. -/
lemma chart_conjugated_supported_twist_symm_eqOn_frontier_pulledBackClosedUnitBall
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
    (chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hchi_target : chi.target = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2)
    (s : Set.Ioi (0 : ℝ)) :
    Set.EqOn (chart_conjugated_supported_twist chi s).symm (fun x ↦ x)
      (frontier (pulledBackClosedUnitBall chi)) := by
  intro x hx
  have hxfront :
      x ∈ chi.source ∩ chi ⁻¹' Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    frontier_pulledBackClosedUnitBall_subset chi hchi_target hx
  have hnorm : ‖chi x‖ = 1 := by
    simpa [Metric.sphere, dist_eq_norm] using hxfront.2
  -- The reciprocal exponent likewise fixes unit-sphere points, so the inverse branch is trivial
  -- on the support frontier.
  calc
    (chart_conjugated_supported_twist chi s).symm x
        = chi.symm (radialPowerMap ((s : ℝ)⁻¹) (chi x)) := by
          apply chart_conjugated_supported_twist_symm_eqOn_closed_unit_ball chi s
          exact ⟨hxfront.1, Metric.sphere_subset_closedBall hxfront.2⟩
    _ = chi.symm (chi x) := by
          rw [radialPowerMap_eq_self_of_norm_eq_one ((s : ℝ)⁻¹) (chi x) hnorm]
    _ = x := chi.left_inv hxfront.1

/-- Helper for Problem 1-6: when `0 < p < 1`, the radial power map cannot be differentiable at
the origin. The proof restricts to a coordinate ray and contradicts the growth bound forced by
differentiability. -/
lemma radialPowerMap_not_differentiableAt_zero_of_lt_one
    (hn : 0 < n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ¬ DifferentiableAt ℝ
      (radialPowerMap p : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (0 : EuclideanSpace ℝ (Fin n)) := by
  intro hdiff
  let i : Fin n := ⟨0, hn⟩
  let v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1 : ℝ)
  have hv_norm : ‖v‖ = 1 := by
    -- The chosen coordinate vector has unit norm.
    simpa [v] using EuclideanSpace.norm_single i (1 : ℝ)
  have hbigO :
      (radialPowerMap p : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =O[𝓝 0]
        (fun x : EuclideanSpace ℝ (Fin n) ↦ x) := by
    -- Differentiability at `0` forces at most linear growth near `0`.
    simpa [radialPowerMap_zero, sub_eq_add_neg] using hdiff.isBigO_sub
  rw [Asymptotics.isBigO_iff] at hbigO
  rcases hbigO with ⟨C, hC⟩
  have hCabs :
      ∀ᶠ x : EuclideanSpace ℝ (Fin n) in 𝓝 0,
        ‖radialPowerMap p x‖ ≤ |C| * ‖x‖ := by
    filter_upwards [hC] with x hx
    have hmul : C * ‖x‖ ≤ |C| * ‖x‖ := by
      gcongr
      exact le_abs_self C
    exact hx.trans hmul
  have hline_tendsto :
      Tendsto (fun t : ℝ ↦ t • v) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (0 : EuclideanSpace ℝ (Fin n))) := by
    -- Approach the origin along the positive ray generated by `v`.
    have hcont_line : Continuous fun t : ℝ ↦ t • v := by
      exact (continuous_id.smul continuous_const)
    simpa using
      tendsto_nhdsWithin_of_tendsto_nhds
        ((hcont_line.continuousAt : ContinuousAt (fun t : ℝ ↦ t • v) 0).tendsto)
  have hbound :
      ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ‖radialPowerMap p (t • v)‖ ≤ |C| * ‖t • v‖ := by
    exact hline_tendsto.eventually hCabs
  have hpow_bound :
      ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        t ^ (p - 1) ≤ |C| := by
    filter_upwards [hbound, self_mem_nhdsWithin] with t ht ht_pos
    have hnorm_line : ‖t • v‖ = t := by
      rw [norm_smul, Real.norm_of_nonneg ht_pos.le, hv_norm, mul_one]
    have hnorm_radial : ‖radialPowerMap p (t • v)‖ = t ^ p := by
      simpa [hnorm_line] using norm_radialPowerMap p hp0 (t • v)
    have hsub : t ^ (p - 1) = t ^ p / t := by
      simpa using Real.rpow_sub_natCast (ne_of_gt ht_pos) p 1
    -- Divide the eventual linear bound by the positive parameter `t`.
    rw [hsub]
    exact (div_le_iff₀ ht_pos).2 (by simpa [hnorm_line, hnorm_radial, mul_comm] using ht)
  have htop :
      Tendsto (fun t : ℝ ↦ t ^ (p - 1))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) atTop := by
    -- Since `p - 1 < 0`, the power `t^(p-1)` blows up along `t → 0+`.
    exact tendsto_rpow_neg_nhdsGT_zero (by linarith)
  have hlarge :
      ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), |C| + 1 ≤ t ^ (p - 1) := by
    exact (tendsto_atTop.1 htop) (|C| + 1)
  have hfalse : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), False := by
    filter_upwards [hpow_bound, hlarge] with t ht_small ht_large
    linarith
  have hne : Filter.NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    infer_instance
  exact hne.ne (Filter.eventually_false_iff_eq_bot.mp hfalse)

/-- Helper for Problem 1-6: a chart point sent to `0` is recovered by applying the inverse chart
to `0`. -/
lemma chart_symm_zero_eq_of_apply_eq_zero
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) {x : M}
    (hx : x ∈ e.source) (hz : e x = 0) :
    e.symm 0 = x := by
  -- Rewrite the standard left-inverse identity at `x` using the hypothesis `e x = 0`.
  simpa [hz] using e.left_inv hx

/-- Helper for Problem 1-6: the singleton-chart transport of a smooth structure along a
self-homeomorphism is again a smooth structure. -/
lemma transported_self_isManifold
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [Nonempty M]
    (Φ : M ≃ₜ M) :
    let _ : ChartedSpace M M :=
      Φ.symm.toOpenPartialHomeomorph.singletonChartedSpace
        (Homeomorph.toOpenPartialHomeomorph_source Φ.symm)
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M :=
      ChartedSpace.comp (EuclideanSpace ℝ (Fin n)) M M
    IsManifold (𝓡 n) ∞ M := by
  let eS : OpenPartialHomeomorph M M := Φ.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace M M := eS.singletonChartedSpace
    (Homeomorph.toOpenPartialHomeomorph_source Φ.symm)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M :=
    ChartedSpace.comp (EuclideanSpace ℝ (Fin n)) M M
  have hGroupoid : HasGroupoid M (contDiffGroupoid ∞ (𝓡 n)) := by
    refine ⟨?_⟩
    rintro _ _ ⟨f, hf, c, hc, rfl⟩ ⟨f', hf', c', hc', rfl⟩
    have hfEq : f = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq
        (Homeomorph.toOpenPartialHomeomorph_source Φ.symm) f hf
    have hf'Eq : f' = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq
        (Homeomorph.toOpenPartialHomeomorph_source Φ.symm) f' hf'
    subst f
    subst f'
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl M := by
      simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph Φ Φ.symm).symm
    -- The transported charts differ only by the original source charts on `M`.
    have hcompat :
        ((c.symm.trans (eS.symm.trans eS)).trans c') ∈ contDiffGroupoid ∞ (𝓡 n) := by
      rw [hmid, OpenPartialHomeomorph.trans_refl]
      exact HasGroupoid.compatible hc hc'
    simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using hcompat
  -- Once compatibility is re-established for the transported atlas, `IsManifold.mk'` packages it.
  exact IsManifold.mk' (𝓡 n) ∞ M

/-- Helper for Problem 1-6: precomposing two charts by the same self-homeomorphism cancels in
their transition map. -/
lemma transported_transition_eq
    (eS : OpenPartialHomeomorph M M)
    {e c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl M) :
    (eS.trans e).symm.trans (eS.trans c) = e.symm.trans c := by
  -- Reassociate until the middle factor `eS.symm.trans eS` appears, then collapse it.
  calc
    (eS.trans e).symm.trans (eS.trans c)
        = ((e.symm.trans eS.symm).trans eS).trans c := by
            simp [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
              OpenPartialHomeomorph.trans_assoc]
    _ = (e.symm.trans (eS.symm.trans eS)).trans c := by
          rw [← OpenPartialHomeomorph.trans_assoc]
    _ = (e.symm.trans (OpenPartialHomeomorph.refl M)).trans c := by
          rw [hmid]
    _ = e.symm.trans c := by
          simp [OpenPartialHomeomorph.trans_assoc, OpenPartialHomeomorph.trans_refl,
            OpenPartialHomeomorph.refl_trans]

/-- Helper for Problem 1-6: a chart from the original maximal smooth atlas stays in the maximal
atlas after transport by a self-homeomorphism. -/
lemma transported_chart_mem_maximalAtlas
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [Nonempty M]
    (Φ : M ≃ₜ M) {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M) :
    let _ : ChartedSpace M M :=
      Φ.symm.toOpenPartialHomeomorph.singletonChartedSpace
        (Homeomorph.toOpenPartialHomeomorph_source Φ.symm)
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M :=
      ChartedSpace.comp (EuclideanSpace ℝ (Fin n)) M M
    Φ.symm.toOpenPartialHomeomorph.trans e ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M := by
  have hcompat_old :
      ∀ {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))},
        c ∈ atlas (EuclideanSpace ℝ (Fin n)) M →
          e.symm.trans c ∈ contDiffGroupoid ∞ (𝓡 n) ∧
            c.symm.trans e ∈ contDiffGroupoid ∞ (𝓡 n) := by
    intro c hc
    exact IsManifold.mem_maximalAtlas_iff.1 he c hc
  let eS : OpenPartialHomeomorph M M := Φ.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace M M := eS.singletonChartedSpace
    (Homeomorph.toOpenPartialHomeomorph_source Φ.symm)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M :=
    ChartedSpace.comp (EuclideanSpace ℝ (Fin n)) M M
  rw [IsManifold.mem_maximalAtlas_iff]
  intro e' he'
  rcases he' with ⟨f, hf, c, hc, rfl⟩
  have hfEq : f = eS := by
    simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq
      (Homeomorph.toOpenPartialHomeomorph_source Φ.symm) f hf
  subst f
  have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl M := by
    simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph Φ Φ.symm).symm
  constructor
  · -- After collapsing the singleton middle chart, compatibility reduces to the original atlas.
    have hleft : e.symm.trans c ∈ contDiffGroupoid ∞ (𝓡 n) := (hcompat_old hc).1
    change (eS.trans e).symm.trans (eS.trans c) ∈ contDiffGroupoid ∞ (𝓡 n)
    rw [transported_transition_eq eS hmid]
    exact hleft
  · -- The reverse transition reduces in the same way.
    have hright : c.symm.trans e ∈ contDiffGroupoid ∞ (𝓡 n) := (hcompat_old hc).2
    change (eS.trans c).symm.trans (eS.trans e) ∈ contDiffGroupoid ∞ (𝓡 n)
    rw [transported_transition_eq eS hmid]
    exact hright

private noncomputable def chartSupportedTwistForward
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
    (chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (s : Set.Ioi (0 : ℝ)) :
    M → M :=
  @Set.piecewise M (fun _ ↦ M) (pulledBackClosedUnitBall chi)
    (chart_conjugated_supported_twist chi s) (fun x ↦ x) (Classical.decPred _)

private noncomputable def chartSupportedTwistInverse
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
    (chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (s : Set.Ioi (0 : ℝ)) :
    M → M :=
  @Set.piecewise M (fun _ ↦ M) (pulledBackClosedUnitBall chi)
    (chart_conjugated_supported_twist chi s).symm (fun x ↦ x) (Classical.decPred _)

/-- Helper for Problem 1-6: the globalization of the supported chart twist. -/
noncomputable def chart_supported_twist_homeomorph
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
    (chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hchi_target : chi.target = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2)
    (s : Set.Ioi (0 : ℝ)) :
    M ≃ₜ M :=
  let K := pulledBackClosedUnitBall chi
  let e := chart_conjugated_supported_twist chi s
  let f := chartSupportedTwistForward chi s
  let g := chartSupportedTwistInverse chi s
  have hK_closed : IsClosed K := pulledBackClosedUnitBall_isClosed chi hchi_target
  have he_maps : Set.MapsTo e K K :=
    chart_conjugated_supported_twist_mapsTo_pulledBackClosedUnitBall chi hchi_target s
  have he_symm_maps : Set.MapsTo e.symm K K :=
    chart_conjugated_supported_twist_symm_mapsTo_pulledBackClosedUnitBall
      chi hchi_target s
  have he_frontier : Set.EqOn e (fun x ↦ x) (frontier K) :=
    chart_conjugated_supported_twist_eqOn_frontier_pulledBackClosedUnitBall
      chi hchi_target s
  have he_symm_frontier : Set.EqOn e.symm (fun x ↦ x) (frontier K) :=
    chart_conjugated_supported_twist_symm_eqOn_frontier_pulledBackClosedUnitBall
      chi hchi_target s
  have hleft : Function.LeftInverse g f := by
    classical
    intro x
    by_cases hx : x ∈ K
    · have hx_source : x ∈ e.source := by
        rw [chart_conjugated_supported_twist_source chi hchi_target s]
        exact hx.1
      have hfx : e x ∈ K := he_maps hx
      have hf_eq : f x = e x := by
        simpa [f, chartSupportedTwistForward] using
          Set.piecewise_eq_of_mem K e (fun x ↦ x) hx
      have hg_eq : g (e x) = e.symm (e x) := by
        simpa [g, chartSupportedTwistInverse] using
          Set.piecewise_eq_of_mem K e.symm (fun x ↦ x) hfx
      rw [hf_eq, hg_eq]
      exact e.left_inv hx_source
    · have hf_eq : f x = x := by
        simpa [f, chartSupportedTwistForward] using
          Set.piecewise_eq_of_notMem K e (fun x ↦ x) hx
      have hg_eq : g x = x := by
        simpa [g, chartSupportedTwistInverse] using
          Set.piecewise_eq_of_notMem K e.symm (fun x ↦ x) hx
      rw [hf_eq, hg_eq]
  have hright : Function.RightInverse g f := by
    classical
    intro x
    by_cases hx : x ∈ K
    · have hx_target : x ∈ e.target := by
        rw [chart_conjugated_supported_twist_target chi hchi_target s]
        exact hx.1
      have hgx : e.symm x ∈ K := he_symm_maps hx
      have hg_eq : g x = e.symm x := by
        simpa [g, chartSupportedTwistInverse] using
          Set.piecewise_eq_of_mem K e.symm (fun x ↦ x) hx
      have hf_eq : f (e.symm x) = e (e.symm x) := by
        simpa [f, chartSupportedTwistForward] using
          Set.piecewise_eq_of_mem K e (fun x ↦ x) hgx
      rw [hg_eq, hf_eq]
      exact e.right_inv hx_target
    · have hg_eq : g x = x := by
        simpa [g, chartSupportedTwistInverse] using
          Set.piecewise_eq_of_notMem K e.symm (fun x ↦ x) hx
      have hf_eq : f x = x := by
        simpa [f, chartSupportedTwistForward] using
          Set.piecewise_eq_of_notMem K e (fun x ↦ x) hx
      rw [hg_eq, hf_eq]
  have hcont_f : Continuous f := by
    classical
    rw [← continuousOn_univ]
    have hcont_local : ContinuousOn e K := by
      refine e.continuousOn.mono ?_
      intro x hx
      rw [chart_conjugated_supported_twist_source chi hchi_target s]
      exact hx.1
    have hcont_local' : ContinuousOn e ((Set.univ : Set M) ∩ closure K) := by
      simpa [hK_closed.closure_eq] using hcont_local
    have hcont_id : ContinuousOn (fun x : M ↦ x) ((Set.univ : Set M) ∩ closure Kᶜ) :=
      continuous_id.continuousOn
    simpa [f, chartSupportedTwistForward] using
      hcont_local'.piecewise (fun x hx ↦ he_frontier hx.2) hcont_id
  have hcont_g : Continuous g := by
    classical
    rw [← continuousOn_univ]
    have hcont_local : ContinuousOn e.symm K := by
      refine e.continuousOn_symm.mono ?_
      intro x hx
      rw [chart_conjugated_supported_twist_target chi hchi_target s]
      exact hx.1
    have hcont_local' : ContinuousOn e.symm ((Set.univ : Set M) ∩ closure K) := by
      simpa [hK_closed.closure_eq] using hcont_local
    have hcont_id : ContinuousOn (fun x : M ↦ x) ((Set.univ : Set M) ∩ closure Kᶜ) :=
      continuous_id.continuousOn
    simpa [g, chartSupportedTwistInverse] using
      hcont_local'.piecewise (fun x hx ↦ he_symm_frontier hx.2) hcont_id
  { toEquiv :=
      { toFun := f
        invFun := g
        left_inv := hleft
        right_inv := hright }
    continuous_toFun := hcont_f
    continuous_invFun := hcont_g }

/-- Helper for Problem 1-6: the globalization agrees with the local supported twist on the
pulled-back closed unit ball. -/
lemma chart_supported_twist_homeomorph_eqOn_closed_support
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
    (chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hchi_target : chi.target = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2)
    (s : Set.Ioi (0 : ℝ)) :
    Set.EqOn (chart_supported_twist_homeomorph chi hchi_target s)
      (chart_conjugated_supported_twist chi s)
      (pulledBackClosedUnitBall chi) := by
  classical
  intro x hx
  simpa [chart_supported_twist_homeomorph, chartSupportedTwistForward] using
    Set.piecewise_eq_of_mem
      (pulledBackClosedUnitBall chi) (chart_conjugated_supported_twist chi s) (fun x ↦ x) hx

/-- Helper for Problem 1-6: the inverse globalization agrees with the inverse local
supported twist on the pulled-back closed unit ball. -/
lemma chart_supported_twist_homeomorph_symm_eqOn_closed_support
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
    (chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hchi_target : chi.target = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2)
    (s : Set.Ioi (0 : ℝ)) :
    Set.EqOn (chart_supported_twist_homeomorph chi hchi_target s).symm
      (chart_conjugated_supported_twist chi s).symm
      (pulledBackClosedUnitBall chi) := by
  classical
  intro x hx
  simpa [chart_supported_twist_homeomorph, chartSupportedTwistInverse] using
    Set.piecewise_eq_of_mem
      (pulledBackClosedUnitBall chi) (chart_conjugated_supported_twist chi s).symm
      (fun x ↦ x) hx

/-- Helper for Problem 1-6: the transition between the distinguished transported charts agrees
with the radial exponent-ratio map on the Euclidean unit ball. -/
lemma center_transition_chart_image_eq
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
    (chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hchi_target : chi.target = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2)
    (s t : Set.Ioi (0 : ℝ))
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ Metric.ball 0 1) :
    chi (((chart_conjugated_supported_twist chi t).symm)
        ((chart_conjugated_supported_twist chi s) (chi.symm y))) =
      radialPowerMap ((t : ℝ)⁻¹) (radialPowerMap (s : ℝ) y) := by
  have hy_target : y ∈ chi.target := by
    simpa [hchi_target] using
      (show y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2 by
        simpa [Metric.mem_ball, dist_eq_norm] using
          (show ‖y‖ < 2 by
            have hy_norm : ‖y‖ < 1 := by
              simpa [Metric.mem_ball, dist_eq_norm] using hy
            linarith))
  have hy_closed : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    exact Metric.ball_subset_closedBall hy
  have hyK : chi.symm y ∈ pulledBackClosedUnitBall chi := by
    refine ⟨chi.map_target hy_target, ?_⟩
    simpa [chi.right_inv hy_target] using hy_closed
  have hforwardK :
      chart_conjugated_supported_twist chi s (chi.symm y) ∈
        pulledBackClosedUnitBall chi := by
    exact chart_conjugated_supported_twist_mapsTo_pulledBackClosedUnitBall
      chi hchi_target s hyK
  have hforward_eq :
      chart_conjugated_supported_twist chi s (chi.symm y) =
        chi.symm (radialPowerMap (s : ℝ) y) := by
    -- On the pulled-back support, the forward conjugated twist is just the forward radial branch.
    calc
      chart_conjugated_supported_twist chi s (chi.symm y)
          = chi.symm (radialPowerMap (s : ℝ) (chi (chi.symm y))) := by
              exact chart_conjugated_supported_twist_eqOn_closed_unit_ball
                chi s hyK
      _ = chi.symm (radialPowerMap (s : ℝ) y) := by
            rw [chi.right_inv hy_target]
  have hforward_target :
      radialPowerMap (s : ℝ) y ∈ chi.target := by
    have hball_two :
        radialPowerMap (s : ℝ) y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2 := by
      exact radialPowerMap_mem_ball_two_of_mem_closed_unit_ball (s : ℝ) s.2 hy_closed
    simpa [hchi_target] using hball_two
  have hforward_image :
      chi (chart_conjugated_supported_twist chi s (chi.symm y)) =
        radialPowerMap (s : ℝ) y := by
    -- Applying `chi` cancels the inverse chart in the explicit forward formula.
    rw [hforward_eq]
    exact chi.right_inv hforward_target
  have houter_target :
      radialPowerMap ((t : ℝ)⁻¹)
          (chi (chart_conjugated_supported_twist chi s (chi.symm y))) ∈
        chi.target := by
    rw [hforward_image]
    have hs_inv : 0 < ((t : ℝ)⁻¹) := by
      exact inv_pos.mpr t.2
    have hclosed :
        radialPowerMap ((t : ℝ)⁻¹) (radialPowerMap (s : ℝ) y) ∈
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      exact radialPowerMap_mem_closed_unit_ball ((t : ℝ)⁻¹) hs_inv
        (radialPowerMap_mem_closed_unit_ball (s : ℝ) s.2 hy_closed)
    have hball_two :
        radialPowerMap ((t : ℝ)⁻¹) (radialPowerMap (s : ℝ) y) ∈
          Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2 := by
      exact mem_ball_two_of_mem_closed_unit_ball hclosed
    simpa [hchi_target] using hball_two
  -- The inverse conjugated twist gives the reciprocal radial exponent on the same support.
  calc
    chi (((chart_conjugated_supported_twist chi t).symm)
        ((chart_conjugated_supported_twist chi s) (chi.symm y)))
        =
          chi (chi.symm
            (radialPowerMap ((t : ℝ)⁻¹)
              (chi (chart_conjugated_supported_twist chi s (chi.symm y))))) := by
            rw [chart_conjugated_supported_twist_symm_eqOn_closed_unit_ball
              chi t hforwardK]
    _ = radialPowerMap ((t : ℝ)⁻¹)
          (chi (chart_conjugated_supported_twist chi s (chi.symm y))) := by
          rw [chi.right_inv houter_target]
    _ = radialPowerMap ((t : ℝ)⁻¹) (radialPowerMap (s : ℝ) y) := by
          rw [hforward_image]

/-- Helper for Problem 1-6: the transition between the distinguished transported charts agrees
with the radial exponent-ratio map on the Euclidean unit ball. -/
lemma center_chart_transition_eqOn_unit_ball
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
    (chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hchi_target : chi.target = Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2)
    (Φ : Set.Ioi (0 : ℝ) → M ≃ₜ M)
    (hΦ : ∀ s,
      Set.EqOn (Φ s) (chart_conjugated_supported_twist chi s)
        (pulledBackClosedUnitBall chi) ∧
      Set.EqOn (Φ s).symm (chart_conjugated_supported_twist chi s).symm
        (pulledBackClosedUnitBall chi))
    (s t : Set.Ioi (0 : ℝ)) :
    Set.EqOn (((Φ s).symm.toOpenPartialHomeomorph.trans chi).symm.trans
        ((Φ t).symm.toOpenPartialHomeomorph.trans chi))
      (radialPowerMap ((s : ℝ) / t))
      (Metric.ball 0 1) := by
  intro y hy
  have hy_target : y ∈ chi.target := by
    simpa [hchi_target] using
      (show y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2 by
        simpa [Metric.mem_ball, dist_eq_norm] using
          (show ‖y‖ < 2 by
            have hy_norm : ‖y‖ < 1 := by
              simpa [Metric.mem_ball, dist_eq_norm] using hy
            linarith))
  have hyK : chi.symm y ∈ pulledBackClosedUnitBall chi := by
    refine ⟨chi.map_target hy_target, ?_⟩
    simpa [chi.right_inv hy_target] using Metric.ball_subset_closedBall hy
  have hs_eq :
      Φ s (chi.symm y) =
        chart_conjugated_supported_twist chi s (chi.symm y) := by
    -- The chosen globalization and the local twist agree on the pulled-back support.
    exact (hΦ s).1 hyK
  have hs_imageK :
      Φ s (chi.symm y) ∈ pulledBackClosedUnitBall chi := by
    rw [hs_eq]
    exact chart_conjugated_supported_twist_mapsTo_pulledBackClosedUnitBall
      chi hchi_target s hyK
  have hs_twist_imageK :
      chart_conjugated_supported_twist chi s (chi.symm y) ∈
        pulledBackClosedUnitBall chi := by
    exact chart_conjugated_supported_twist_mapsTo_pulledBackClosedUnitBall
      chi hchi_target s hyK
  have ht_eq :
      (Φ t).symm (Φ s (chi.symm y)) =
        (chart_conjugated_supported_twist chi t).symm
          ((chart_conjugated_supported_twist chi s) (chi.symm y)) := by
    -- After the forward branch stays in the same support, the inverse globalization also reduces
    -- to the local inverse twist.
    rw [hs_eq]
    exact (hΦ t).2 hs_twist_imageK
  -- Compute the transported chart transition in local coordinates and collapse the exponents.
  calc
    (((Φ s).symm.toOpenPartialHomeomorph.trans chi).symm.trans
        ((Φ t).symm.toOpenPartialHomeomorph.trans chi)) y
        = chi ((Φ t).symm (Φ s (chi.symm y))) := by
            rfl
    _ = chi
          ((chart_conjugated_supported_twist chi t).symm
            ((chart_conjugated_supported_twist chi s) (chi.symm y))) := by
          rw [ht_eq]
    _ = radialPowerMap ((t : ℝ)⁻¹) (radialPowerMap (s : ℝ) y) := by
          exact center_transition_chart_image_eq
            chi hchi_target s t hy
    _ = radialPowerMap (((t : ℝ)⁻¹) * s) y := by
          simpa using radialPowerMap_mul ((t : ℝ)⁻¹) (s : ℝ) s.2 y
    _ = radialPowerMap ((s : ℝ) / t) y := by
          rw [div_eq_mul_inv, mul_comm]

/-- Problem 1-6: every nonempty smooth `n`-manifold with `n ≥ 1` admits an `ℝ_{>0}`-indexed
family of smooth charted-space structures on the same underlying topological manifold whose
associated maximal smooth atlases are pairwise distinct. -/
-- Proof sketch: choose one smooth atlas on `M`, modify a single chart by conjugating it with the
-- radial homeomorphisms `x ↦ ‖x‖^(s - 1) • x` on the unit ball, and keep the rest of the atlas
-- fixed. For `s > 0` this still yields a smooth atlas on the same topological manifold, while the
-- transition map between the original and modified chart fails to be a diffeomorphism unless the
-- exponents agree; Proposition 1.17 then turns this into pairwise distinct maximal smooth atlases.
theorem exists_uncountably_many_distinct_smooth_structures
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M] [SecondCountableTopology M]
    [IsManifold (𝓡 n) ∞ M] [Nonempty M] (hn : 0 < n) :
    ∃ c : Set.Ioi (0 : ℝ) → ChartedSpace (EuclideanSpace ℝ (Fin n)) M,
      (∀ s,
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M := c s
        IsManifold (𝓡 n) ∞ M) ∧
      Function.Injective (fun s ↦
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M := c s
        IsManifold.maximalAtlas (𝓡 n) ∞ M) := by
  classical
  -- Choose a base point; the final construction twists a single coordinate ball around this point.
  let x0 : M := Classical.choice ‹Nonempty M›
  obtain ⟨chi, hx0_chi, hchi_zero, hchi_max, hchi_target⟩ :
      ∃ chi : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
        x0 ∈ chi.source ∧
        chi x0 = 0 ∧
        chi ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M ∧
        chi.target = Metric.ball 0 2 := by
    exact chart_at_point_with_ball_target x0
  -- Route correction: use an ambient chart with target `Metric.ball 0 2`, so any later radial
  -- twist supported in `Metric.ball 0 1` is already trivial near the chart frontier.
  have hfix_boundary :
      ∀ s : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 → radialPowerMap s x = x := by
    intro s x hx
    exact radialPowerMap_eq_self_of_norm_eq_one s x hx
  have hn' : n ≠ 0 := by
    omega
  let Φ : Set.Ioi (0 : ℝ) → M ≃ₜ M := fun s ↦
    chart_supported_twist_homeomorph chi hchi_target s
  let c : Set.Ioi (0 : ℝ) → ChartedSpace (EuclideanSpace ℝ (Fin n)) M := fun s ↦
    let _ : ChartedSpace M M :=
      (Φ s).symm.toOpenPartialHomeomorph.singletonChartedSpace
        (Homeomorph.toOpenPartialHomeomorph_source (Φ s).symm)
    ChartedSpace.comp (EuclideanSpace ℝ (Fin n)) M M
  have hc_manifold : ∀ s,
      let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M := c s
      IsManifold (𝓡 n) ∞ M := by
    intro s
    -- The singleton-chart transport along `Φ s` preserves smooth compatibility.
    change
      let _ : ChartedSpace M M :=
        (Φ s).symm.toOpenPartialHomeomorph.singletonChartedSpace
          (Homeomorph.toOpenPartialHomeomorph_source (Φ s).symm)
      let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M :=
        ChartedSpace.comp (EuclideanSpace ℝ (Fin n)) M M
      IsManifold (𝓡 n) ∞ M
    exact transported_self_isManifold (Φ s)
  have hcenter_mem : ∀ s,
      let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M := c s
      (Φ s).symm.toOpenPartialHomeomorph.trans chi ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M := by
    intro s
    -- The distinguished center chart survives in the transported maximal atlas.
    change
      let _ : ChartedSpace M M :=
        (Φ s).symm.toOpenPartialHomeomorph.singletonChartedSpace
          (Homeomorph.toOpenPartialHomeomorph_source (Φ s).symm)
      let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M :=
        ChartedSpace.comp (EuclideanSpace ℝ (Fin n)) M M
      (Φ s).symm.toOpenPartialHomeomorph.trans chi ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M
    exact transported_chart_mem_maximalAtlas (Φ s) hchi_max
  have hΦ :
      ∀ s,
        Set.EqOn (Φ s) (chart_conjugated_supported_twist chi s)
          (pulledBackClosedUnitBall chi) ∧
        Set.EqOn (Φ s).symm (chart_conjugated_supported_twist chi s).symm
          (pulledBackClosedUnitBall chi) := by
    intro s
    constructor
    · -- The globalized homeomorphism agrees with the local twist on the compact support.
      exact chart_supported_twist_homeomorph_eqOn_closed_support
        chi hchi_target s
    · -- The globalized inverse homeomorphism agrees with the inverse local twist there as well.
      exact chart_supported_twist_homeomorph_symm_eqOn_closed_support
        chi hchi_target s
  let centerChart : Set.Ioi (0 : ℝ) → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    fun s ↦ (Φ s).symm.toOpenPartialHomeomorph.trans chi
  have hzero_target : (0 : EuclideanSpace ℝ (Fin n)) ∈ chi.target := by
    -- The chart target is the Euclidean ball of radius `2`, which contains the origin.
    have hzero_ball : (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 2 := by
      simpa [Metric.mem_ball, dist_eq_norm]
    simpa [hchi_target] using hzero_ball
  have hx0_support : x0 ∈ pulledBackClosedUnitBall chi := by
    -- The chart center lands at the origin, so it lies in the pulled-back closed unit ball.
    refine ⟨hx0_chi, ?_⟩
    simpa [Metric.mem_closedBall, dist_eq_norm, hchi_zero]
  have hΦ_fix : ∀ s, Φ s x0 = x0 ∧ (Φ s).symm x0 = x0 := by
    intro s
    constructor
    · -- The forward globalization fixes the chart center because the radial map fixes `0`.
      calc
        Φ s x0 = chart_conjugated_supported_twist chi s x0 := by
          exact (hΦ s).1 hx0_support
        _ = chi.symm (radialPowerMap (s : ℝ) (chi x0)) := by
              exact chart_conjugated_supported_twist_eqOn_closed_unit_ball
                chi s hx0_support
        _ = chi.symm 0 := by
              rw [hchi_zero, radialPowerMap_zero]
        _ = x0 := chart_symm_zero_eq_of_apply_eq_zero chi hx0_chi hchi_zero
    · -- The inverse globalization fixes the chart center for the same reason.
      calc
        (Φ s).symm x0 = (chart_conjugated_supported_twist chi s).symm x0 := by
          exact (hΦ s).2 hx0_support
        _ = chi.symm (radialPowerMap ((s : ℝ)⁻¹) (chi x0)) := by
              exact chart_conjugated_supported_twist_symm_eqOn_closed_unit_ball
                chi s hx0_support
        _ = chi.symm 0 := by
              rw [hchi_zero, radialPowerMap_zero]
        _ = x0 := chart_symm_zero_eq_of_apply_eq_zero chi hx0_chi hchi_zero
  have hx0_center_source : ∀ s, x0 ∈ (centerChart s).source := by
    intro s
    -- The center point stays in the distinguished chart source because the globalization fixes it.
    change x0 ∈ ((Φ s).symm.toOpenPartialHomeomorph.trans chi).source
    rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]
    simp [(hΦ_fix s).2, hx0_chi]
  have hcenter_zero : ∀ s, centerChart s x0 = 0 := by
    intro s
    -- Evaluating the distinguished chart at the fixed center reproduces the original chart value.
    calc
      centerChart s x0 = chi ((Φ s).symm x0) := by
        rfl
      _ = chi x0 := by
            rw [(hΦ_fix s).2]
      _ = 0 := hchi_zero
  have hzero_center_target :
      ∀ s, (0 : EuclideanSpace ℝ (Fin n)) ∈ (centerChart s).target := by
    intro s
    -- The center point maps to the origin in every distinguished chart.
    simpa [hcenter_zero s] using (centerChart s).map_source (hx0_center_source s)
  have hcenter_symm_zero : ∀ s, (centerChart s).symm 0 = x0 := by
    intro s
    -- The origin in the distinguished chart comes from the common center point.
    exact chart_symm_zero_eq_of_apply_eq_zero (centerChart s)
      (hx0_center_source s) (hcenter_zero s)
  let maximalAtlasFamily :
      Set.Ioi (0 : ℝ) → Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) := fun s ↦
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M := c s
    IsManifold.maximalAtlas (𝓡 n) ∞ M
  have hratio_contDiff :
      ∀ {u v : Set.Ioi (0 : ℝ)},
        maximalAtlasFamily u = maximalAtlasFamily v →
        ContDiffAt ℝ ∞ (radialPowerMap ((u : ℝ) / v))
          (0 : EuclideanSpace ℝ (Fin n)) := by
    intro u v huv
    have htransition :
        ContDiffAt ℝ ∞
          ((((centerChart u).symm.trans (centerChart v)) :
            OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n))
              (EuclideanSpace ℝ (Fin n))) :
            EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
          (0 : EuclideanSpace ℝ (Fin n)) := by
      let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M := c v
      have hu_mem : centerChart u ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M := by
        -- Atlas equality moves the `u`-center chart into the `v`-transported maximal atlas.
        have hu_mem_family : centerChart u ∈ maximalAtlasFamily v := by
          rw [← huv]
          simpa [maximalAtlasFamily] using hcenter_mem u
        simpa [maximalAtlasFamily] using hu_mem_family
      have hv_mem : centerChart v ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M := by
        simpa [maximalAtlasFamily] using hcenter_mem v
      have hzero_source :
          (0 : EuclideanSpace ℝ (Fin n)) ∈ ((centerChart u).symm.trans (centerChart v)).source := by
        -- The common center point `x0` shows that the distinguished transition is defined at `0`.
        rw [OpenPartialHomeomorph.trans_source]
        refine ⟨hzero_center_target u, ?_⟩
        simpa [hcenter_symm_zero u] using hx0_center_source v
      have hcompat :
          ((centerChart u).symm.trans (centerChart v)) ∈ contDiffGroupoid ∞ (𝓡 n) := by
        exact IsManifold.compatible_of_mem_maximalAtlas hu_mem hv_mem
      rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid] at hcompat
      have hcompatOn :
          ContDiffOn ℝ ∞
            ((((centerChart u).symm.trans (centerChart v)) :
              OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n))
                (EuclideanSpace ℝ (Fin n))) :
              EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
            (((centerChart u).symm.trans (centerChart v)).source) := by
        simpa using hcompat.1
      -- Groupoid membership gives smoothness on the transition source; openness upgrades this to
      -- `ContDiffAt` at the distinguished origin.
      exact hcompatOn.contDiffAt
        (((centerChart u).symm.trans (centerChart v)).open_source.mem_nhds hzero_source)
    have hevent :
        (radialPowerMap ((u : ℝ) / v)) =ᶠ[nhds (0 : EuclideanSpace ℝ (Fin n))]
          ((((centerChart u).symm.trans (centerChart v)) :
            OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n))
              (EuclideanSpace ℝ (Fin n))) :
            EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
      -- Near `0`, the distinguished transition is exactly the radial exponent-ratio map.
      filter_upwards [Metric.isOpen_ball.mem_nhds (show
        (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 1 by
          simpa [Metric.mem_ball, dist_eq_norm] using (show (0 : ℝ) < 1 by norm_num))] with y hy
      exact (center_chart_transition_eqOn_unit_ball
        chi hchi_target Φ hΦ u v hy).symm
    exact htransition.congr_of_eventuallyEq hevent
  refine ⟨c, hc_manifold, ?_⟩
  intro s t hst
  apply Subtype.ext
  by_contra hne
  have hlt_or_gt : (s : ℝ) < t ∨ t < s := lt_or_gt_of_ne hne
  cases hlt_or_gt with
  | inl hlt =>
      -- Route correction: compare the two distinguished transported charts in the common atlas of
      -- `c t`, so the transition exponent is `(s : ℝ) / t`.
      have hcont :
          ContDiffAt ℝ ∞ (radialPowerMap ((s : ℝ) / t))
            (0 : EuclideanSpace ℝ (Fin n)) := by
        exact hratio_contDiff hst
      have hdiff :
          DifferentiableAt ℝ (radialPowerMap ((s : ℝ) / t))
            (0 : EuclideanSpace ℝ (Fin n)) := by
        exact hcont.differentiableAt (by simp)
      have hratio_pos : 0 < (s : ℝ) / t := by
        exact div_pos s.2 t.2
      have hratio_lt_one : (s : ℝ) / t < 1 := by
        exact (div_lt_one t.2).2 hlt
      exact (radialPowerMap_not_differentiableAt_zero_of_lt_one
        hn hratio_pos hratio_lt_one) hdiff
  | inr hgt =>
      -- Swapping the roles of `s` and `t` gives the reciprocal exponent ratio in `(0, 1)`.
      have hcont :
          ContDiffAt ℝ ∞ (radialPowerMap ((t : ℝ) / s))
            (0 : EuclideanSpace ℝ (Fin n)) := by
        exact hratio_contDiff hst.symm
      have hdiff :
          DifferentiableAt ℝ (radialPowerMap ((t : ℝ) / s))
            (0 : EuclideanSpace ℝ (Fin n)) := by
        exact hcont.differentiableAt (by simp)
      have hratio_pos : 0 < (t : ℝ) / s := by
        exact div_pos t.2 s.2
      have hratio_lt_one : (t : ℝ) / s < 1 := by
        exact (div_lt_one s.2).2 hgt
      exact (radialPowerMap_not_differentiableAt_zero_of_lt_one
        hn hratio_pos hratio_lt_one) hdiff
