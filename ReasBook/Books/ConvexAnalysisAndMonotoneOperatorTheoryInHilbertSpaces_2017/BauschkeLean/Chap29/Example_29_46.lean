import BauschkeLean.Chap02.Example_2_60
import BauschkeLean.Chap10.Example_10_4
import BauschkeLean.Chap29.Definition_29_40

open ERealFunction
open SetValuedOperator
open scoped Topology

universe u v

/- Source/core/bridge triage for Example 29.46:
- `source-facing`: the displayed least-squares projector formula `(29.76)`.
- `core/canonical`: `continuousConvexSubgradientProjector`.
- `bridge/view`: this file specializes the Chapter 29 owner to `leastSquaresResidual L r` and
  rewrites its differentiable branch using the gradient formula from Example 2.60. -/

section

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The least-squares residual is continuous. -/
theorem leastSquaresResidual_continuous (L : H →L[ℝ] K) (r : K) :
    Continuous (leastSquaresResidual L r) :=
  (leastSquaresResidual_contDiff L r).continuous

/-- The least-squares residual is convex on the whole space. -/
theorem leastSquaresResidual_convexOn (L : H →L[ℝ] K) (r : K) :
    ConvexOn ℝ Set.univ (leastSquaresResidual L r) := by
  have hnorm_sq : ConvexOn ℝ Set.univ (fun z : K ↦ ‖z‖ ^ 2) := norm_sq_convexOn_univ
  have hshift : ConvexOn ℝ Set.univ (fun z : K ↦ ‖z - r‖ ^ 2) := by
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      hnorm_sq.translate_right (-r)
  simpa [leastSquaresResidual] using hshift.comp_linearMap L.toLinearMap

end

section

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The least-squares residual is Gâteaux differentiable on the whole space with gradient field
`x ↦ 2 L† (L x - r)`. -/
theorem leastSquaresResidual_hasGateauxDerivativeOn
    (L : H →L[ℝ] K) (r : K) :
    HasGateauxDerivativeOn
      (fun x ↦ ((leastSquaresResidual L r) x : EReal).toReal)
      (fun x ↦ InnerProductSpace.toDualMap ℝ H ((2 : ℝ) • L.adjoint (L x - r)))
      Set.univ := by
  intro x hx
  simpa [Function.toEReal_apply, InnerProductSpace.toDual_apply_eq_toDualMap_apply] using
    (leastSquaresResidual_hasFDerivAt L r x).hasGateauxDerivativeAt

private theorem leastSquaresResidual_hasGateauxDerivativeOn_active
    (L : H →L[ℝ] K) (r : K) (ξ : ℝ) :
    HasGateauxDerivativeOn
      (fun x ↦ ((leastSquaresResidual L r) x : EReal).toReal)
      (fun x ↦ InnerProductSpace.toDualMap ℝ H ((2 : ℝ) • L.adjoint (L x - r)))
      {x | ξ < leastSquaresResidual L r x} := by
  intro x hx
  have hnhds : {y | ξ < leastSquaresResidual L r y} ∈ 𝓝 x := by
    have hcont : ContinuousAt (leastSquaresResidual L r) x :=
      (leastSquaresResidual_continuous L r).continuousAt
    have hmem : leastSquaresResidual L r x ∈ Set.Ioi ξ := hx
    change leastSquaresResidual L r ⁻¹' Set.Ioi ξ ∈ 𝓝 x
    simpa using hcont.preimage_mem_nhds (IsOpen.mem_nhds isOpen_Ioi hmem)
  simpa [Function.toEReal_apply, InnerProductSpace.toDual_apply_eq_toDualMap_apply] using
    (leastSquaresResidual_hasFDerivAt L r x).hasFDerivWithinAt.hasGateauxDerivativeWithinAt hnhds

omit [CompleteSpace H] [CompleteSpace K] in
private theorem div_norm_two_smul_smul
    (t : ℝ) (u : H) :
    (t / ‖(2 : ℝ) • u‖ ^ 2) • ((2 : ℝ) • u) = (t / (2 * ‖u‖ ^ 2)) • u := by
  by_cases hu : u = 0
  · simp [hu]
  · have hu_sq : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hu)
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)), smul_smul]
    have hpow : (2 * ‖u‖) ^ 2 = 4 * ‖u‖ ^ 2 := by ring
    rw [hpow]
    congr 1
    field_simp [hu_sq]
    ring

/-- Example 29.46: the Chapter 29 subgradient projector specialized to the least-squares residual
recovers the displayed formula `(29.76)`. -/
theorem leastSquaresResidual_subgradientProjector_apply
    (L : H →L[ℝ] K) (r : K) (ξ : ℝ)
    (hC : (lowerLevelSet (leastSquaresResidual L r).toEReal.asEReal ξ).Nonempty)
    (s : Selection (∂ (leastSquaresResidual L r).toEReal)) (x : H) :
    continuousConvexSubgradientProjector
      (leastSquaresResidual L r) ξ
      (leastSquaresResidual_continuous L r)
      (leastSquaresResidual_convexOn L r)
      hC s x =
      if ξ < ‖L x - r‖ ^ 2 then
        x +
          (((ξ - ‖L x - r‖ ^ 2) / (2 * ‖L.adjoint (L x - r)‖ ^ 2)) •
            L.adjoint (L x - r))
      else
        x := by
  have hgrad := leastSquaresResidual_hasGateauxDerivativeOn_active L r ξ
  by_cases hx : ξ < ‖L x - r‖ ^ 2
  · have hactive :
        continuousConvexSubgradientProjector
            (leastSquaresResidual L r) ξ
            (leastSquaresResidual_continuous L r)
            (leastSquaresResidual_convexOn L r)
            hC s x =
          x +
            (((ξ - leastSquaresResidual L r x) /
                ‖(2 : ℝ) • L.adjoint (L x - r)‖ ^ 2) •
              ((2 : ℝ) • L.adjoint (L x - r))) := by
      simpa [leastSquaresResidual_apply] using
        (continuousConvexSubgradientProjector_apply_of_lt_of_hasGateauxDerivativeOn
          (leastSquaresResidual L r) ξ
          (leastSquaresResidual_continuous L r)
          (leastSquaresResidual_convexOn L r)
          hC s
          (fun z ↦ (2 : ℝ) • L.adjoint (L z - r))
          hgrad
          hx)
    rw [if_pos hx]
    calc
      continuousConvexSubgradientProjector
          (leastSquaresResidual L r) ξ
          (leastSquaresResidual_continuous L r)
          (leastSquaresResidual_convexOn L r)
          hC s x
        =
          x +
            (((ξ - leastSquaresResidual L r x) /
                ‖(2 : ℝ) • L.adjoint (L x - r)‖ ^ 2) •
              ((2 : ℝ) • L.adjoint (L x - r))) := hactive
      _ =
          x +
            (((ξ - ‖L x - r‖ ^ 2) / (2 * ‖L.adjoint (L x - r)‖ ^ 2)) •
              L.adjoint (L x - r)) := by
          rw [leastSquaresResidual_apply, div_norm_two_smul_smul]
  · have hx_mem : x ∈ lowerLevelSet (leastSquaresResidual L r).toEReal.asEReal ξ := by
      rw [mem_lowerLevelSet_iff]
      change ((‖L x - r‖ ^ 2 : ℝ) : EReal) ≤ ((ξ : ℝ) : EReal)
      exact_mod_cast (not_lt.mp hx : ‖L x - r‖ ^ 2 ≤ ξ)
    have hinactive :
        continuousConvexSubgradientProjector
            (leastSquaresResidual L r) ξ
            (leastSquaresResidual_continuous L r)
            (leastSquaresResidual_convexOn L r)
            hC s x = x := by
      exact continuousConvexSubgradientProjector_apply_of_mem_lowerLevelSet
        (leastSquaresResidual L r) ξ
        (leastSquaresResidual_continuous L r)
        (leastSquaresResidual_convexOn L r)
        hC s hx_mem
    simpa [if_neg hx] using hinactive

/-- On the active branch `ξ < ‖L x - r‖ ^ 2`,
the least-squares specialization of the Chapter 29 subgradient projector is exactly the displayed
formula `(29.76)`. -/
theorem leastSquaresResidual_subgradientProjector_apply_of_lt
    (L : H →L[ℝ] K) (r : K) (ξ : ℝ)
    (hC : (lowerLevelSet (leastSquaresResidual L r).toEReal.asEReal ξ).Nonempty)
    (s : Selection (∂ (leastSquaresResidual L r).toEReal))
    {x : H} (hx : ξ < ‖L x - r‖ ^ 2) :
    continuousConvexSubgradientProjector
      (leastSquaresResidual L r) ξ
      (leastSquaresResidual_continuous L r)
      (leastSquaresResidual_convexOn L r)
      hC s x =
      x +
        (((ξ - ‖L x - r‖ ^ 2) / (2 * ‖L.adjoint (L x - r)‖ ^ 2)) •
          L.adjoint (L x - r)) := by
  simpa [hx] using leastSquaresResidual_subgradientProjector_apply L r ξ hC s x

/-- On the branch `‖L x - r‖ ^ 2 ≤ ξ`, the least-squares specialization of the Chapter 29
subgradient projector fixes `x`. -/
theorem leastSquaresResidual_subgradientProjector_apply_of_le
    (L : H →L[ℝ] K) (r : K) (ξ : ℝ)
    (hC : (lowerLevelSet (leastSquaresResidual L r).toEReal.asEReal ξ).Nonempty)
    (s : Selection (∂ (leastSquaresResidual L r).toEReal))
    {x : H} (hx : ‖L x - r‖ ^ 2 ≤ ξ) :
    continuousConvexSubgradientProjector
      (leastSquaresResidual L r) ξ
      (leastSquaresResidual_continuous L r)
      (leastSquaresResidual_convexOn L r)
      hC s x = x := by
  simpa [if_neg (not_lt.mpr hx)] using leastSquaresResidual_subgradientProjector_apply L r ξ hC s x

end
