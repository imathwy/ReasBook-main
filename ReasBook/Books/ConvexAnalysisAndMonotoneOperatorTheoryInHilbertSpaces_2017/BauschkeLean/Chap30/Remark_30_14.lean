import BauschkeLean.Chap30.Corollary_30_10

open Filter
open scoped Topology

universe u v

noncomputable section

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {I : Type v}

-- Source/core/bridge triage:
-- `source-facing`: Remark 30.14 packages the half-averaged family
-- `T_i = (1 / 2) (Id + R_i)` attached to a finite nonexpansive family.
-- `core/canonical`: Chapter 4 expresses the same object through
-- `FirmlyNonexpansiveOn (Set.univ : Set H)` and the Chapter 30 common-fixed-point owner.
-- `bridge/view`: the fixed-point and Haugazeau statements transport Corollary 30.10 across this
-- half-averaging construction.

/-- The half-averaged family `T_i = (1 / 2) (R_i + Id)` attached to a family `R_i`. -/
def halfIdAddOperatorFamily (R : I → H → H) : I → H → H :=
  fun i x ↦ (1 / 2 : ℝ) • (x + R i x)

@[simp] theorem halfIdAddOperatorFamily_apply (R : I → H → H) (i : I) (x : H) :
    halfIdAddOperatorFamily R i x = (1 / 2 : ℝ) • (x + R i x) :=
  rfl

/-- Remark 30.14 (1): for the half-averaged family `T_i = (1 / 2) (R_i + Id)`, the common
fixed-point set of `T_i` coincides with the common fixed-point set of `R_i`. -/
@[simp] theorem iInter_fixedPoints_halfIdAddOperatorFamily_eq
    (R : I → H → H) :
    commonFixedPointSet (halfIdAddOperatorFamily R) = commonFixedPointSet R := by
  ext x
  rw [mem_commonFixedPointSet_iff, mem_commonFixedPointSet_iff]
  constructor
  · intro hx i
    have hdouble := congrArg (fun z : H ↦ (2 : ℝ) • z) (hx i)
    have hsum : x + R i x = x + x := by
      simpa [halfIdAddOperatorFamily, two_smul, smul_add, add_comm, add_left_comm, add_assoc]
        using hdouble
    exact add_left_cancel hsum
  · intro hx i
    calc
      halfIdAddOperatorFamily R i x = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • x := by
        simp [halfIdAddOperatorFamily, hx i, smul_add, add_smul]
      _ = (1 : ℝ) • x := by norm_num
      _ = x := by simp

/-- Remark 30.14 (2): if each `R_i` is nonexpansive, then each half-averaged companion
`T_i = (1 / 2) (R_i + Id)` is firmly nonexpansive. -/
theorem halfIdAddOperatorFamily_firmlyNonexpansive
    (R : I → H → H) (hR : ∀ i, LipschitzWith 1 (R i)) :
    ∀ i, FirmlyNonexpansiveOn (Set.univ : Set H) (halfIdAddOperatorFamily R i) := by
  intro i
  rw [firmlyNonexpansiveOn_iff]
  intro x _ y _
  let a : H := x - y
  let b : H := R i x - R i y
  have hRxy : ‖b‖ ≤ ‖a‖ := by
    simpa [a, b, dist_eq_norm] using (hR i).dist_le_mul x y
  have hRxy_sq : ‖b‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    nlinarith [hRxy, norm_nonneg a, norm_nonneg b]
  have hnorm_add :
      ‖halfIdAddOperatorFamily R i x - halfIdAddOperatorFamily R i y‖ ^ 2 =
        (1 / 4 : ℝ) * ‖a + b‖ ^ 2 := by
    have hdiff :
        halfIdAddOperatorFamily R i x - halfIdAddOperatorFamily R i y = (1 / 2 : ℝ) • (a + b) := by
      dsimp [a, b]
      calc
        halfIdAddOperatorFamily R i x - halfIdAddOperatorFamily R i y
            = (1 / 2 : ℝ) • (x + R i x) - (1 / 2 : ℝ) • (y + R i y) := by rfl
        _ = (1 / 2 : ℝ) • ((x + R i x) - (y + R i y)) := by rw [smul_sub]
        _ = (1 / 2 : ℝ) • ((x - y) + (R i x - R i y)) := by
              congr 1
              abel_nf
        _ = (1 / 2 : ℝ) • (a + b) := by rfl
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (1 / 2 : ℝ) by norm_num)]
    ring
  have hnorm_sub :
      ‖(x - halfIdAddOperatorFamily R i x) - (y - halfIdAddOperatorFamily R i y)‖ ^ 2 =
        (1 / 4 : ℝ) * ‖a - b‖ ^ 2 := by
    have hxres : x - halfIdAddOperatorFamily R i x = (1 / 2 : ℝ) • (x - R i x) := by
      have hxhalf : x - (1 / 2 : ℝ) • x = (1 / 2 : ℝ) • x := by
        calc
          x - (1 / 2 : ℝ) • x = (1 : ℝ) • x - (1 / 2 : ℝ) • x := by simp
          _ = (1 - (1 / 2 : ℝ)) • x := by rw [sub_smul]
          _ = (1 / 2 : ℝ) • x := by norm_num
      calc
        x - halfIdAddOperatorFamily R i x = x - (1 / 2 : ℝ) • (x + R i x) := by rfl
        _ = x - ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • R i x) := by rw [smul_add]
        _ = (x - (1 / 2 : ℝ) • x) - (1 / 2 : ℝ) • R i x := by abel_nf
        _ = (1 / 2 : ℝ) • x - (1 / 2 : ℝ) • R i x := by rw [hxhalf]
        _ = (1 / 2 : ℝ) • (x - R i x) := by rw [smul_sub]
    have hyres : y - halfIdAddOperatorFamily R i y = (1 / 2 : ℝ) • (y - R i y) := by
      have hyhalf : y - (1 / 2 : ℝ) • y = (1 / 2 : ℝ) • y := by
        calc
          y - (1 / 2 : ℝ) • y = (1 : ℝ) • y - (1 / 2 : ℝ) • y := by simp
          _ = (1 - (1 / 2 : ℝ)) • y := by rw [sub_smul]
          _ = (1 / 2 : ℝ) • y := by norm_num
      calc
        y - halfIdAddOperatorFamily R i y = y - (1 / 2 : ℝ) • (y + R i y) := by rfl
        _ = y - ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • R i y) := by rw [smul_add]
        _ = (y - (1 / 2 : ℝ) • y) - (1 / 2 : ℝ) • R i y := by abel_nf
        _ = (1 / 2 : ℝ) • y - (1 / 2 : ℝ) • R i y := by rw [hyhalf]
        _ = (1 / 2 : ℝ) • (y - R i y) := by rw [smul_sub]
    have hdiff :
        (x - halfIdAddOperatorFamily R i x) - (y - halfIdAddOperatorFamily R i y) =
          (1 / 2 : ℝ) • (a - b) := by
      dsimp [a, b]
      calc
        (x - halfIdAddOperatorFamily R i x) - (y - halfIdAddOperatorFamily R i y)
            = (1 / 2 : ℝ) • (x - R i x) - (1 / 2 : ℝ) • (y - R i y) := by
                rw [hxres, hyres]
        _ = (1 / 2 : ℝ) • ((x - R i x) - (y - R i y)) := by rw [← smul_sub]
        _ = (1 / 2 : ℝ) • ((x - y) - (R i x - R i y)) := by
              congr 1
              abel_nf
        _ = (1 / 2 : ℝ) • (a - b) := by rfl
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (1 / 2 : ℝ) by norm_num)]
    ring
  have hadd :
      ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * inner ℝ a b + ‖b‖ ^ 2 := by
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using norm_add_sq_real a b
  have hsub :
      ‖a - b‖ ^ 2 = ‖a‖ ^ 2 - 2 * inner ℝ a b + ‖b‖ ^ 2 := by
    simpa [two_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using norm_sub_sq_real a b
  rw [hnorm_add, hnorm_sub, hadd, hsub]
  nlinarith

variable [CompleteSpace H]

/-- The common fixed-point set of a finite nonexpansive family is Chebyshev after replacing the
family by its half-averaged companions. -/
theorem iInter_fixedPoints_isChebyshev_of_halfIdAddOperatorFamily
    (R : I → H → H) (hR : ∀ i, LipschitzWith 1 (R i))
    (hFix_nonempty : (commonFixedPointSet R).Nonempty) :
    IsChebyshev (commonFixedPointSet R) := by
  have hT : ∀ i, FirmlyNonexpansiveOn (Set.univ : Set H) (halfIdAddOperatorFamily R i) :=
    halfIdAddOperatorFamily_firmlyNonexpansive R hR
  have hHalfFix_nonempty : (commonFixedPointSet (halfIdAddOperatorFamily R)).Nonempty := by
    rw [iInter_fixedPoints_halfIdAddOperatorFamily_eq R]
    exact hFix_nonempty
  have hHalfCheb :
      IsChebyshev (commonFixedPointSet (halfIdAddOperatorFamily R)) :=
    iInter_fixedPoints_isChebyshev_of_firmlyQuasinonexpansive
      (halfIdAddOperatorFamily R)
      (fun i ↦ firmlyQuasinonexpansive_of_firmlyNonexpansive (hT i))
      hHalfFix_nonempty
  rw [iInter_fixedPoints_halfIdAddOperatorFamily_eq R] at hHalfCheb
  exact hHalfCheb

/-- Remark 30.14 (3): applying Haugazeau's algorithm to the half-averaged family
`T_i = (1 / 2) (R_i + Id)` yields the best approximation of `x₀` from the common fixed-point set
`commonFixedPointSet R`. -/
theorem haugazeau_iteration_tendsto_projection_iInter_fixedPoints_of_halfIdAddOperatorFamily
    (R : I → H → H) (hR : ∀ i, LipschitzWith 1 (R i))
    (hFix_nonempty : (commonFixedPointSet R).Nonempty)
    {m : ℕ} (control : ℕ → I)
    (hcontrol : VisitsEveryIndexInEachBlock control m)
    (x0 : H) :
    Tendsto (haugazeauIteration (halfIdAddOperatorFamily R) control x0) atTop
      (𝓝 (P[commonFixedPointSet R,
        iInter_fixedPoints_isChebyshev_of_halfIdAddOperatorFamily R hR hFix_nonempty] x0)) :=
    by
  have hT : ∀ i, FirmlyNonexpansiveOn (Set.univ : Set H) (halfIdAddOperatorFamily R i) :=
    halfIdAddOperatorFamily_firmlyNonexpansive R hR
  have hHalfFix_nonempty : (commonFixedPointSet (halfIdAddOperatorFamily R)).Nonempty := by
    rw [iInter_fixedPoints_halfIdAddOperatorFamily_eq R]
    exact hFix_nonempty
  have hlimit :
      Tendsto (haugazeauIteration (halfIdAddOperatorFamily R) control x0) atTop
        (𝓝 (P[commonFixedPointSet (halfIdAddOperatorFamily R),
          iInter_fixedPoints_isChebyshev_of_firmlyQuasinonexpansive
            (halfIdAddOperatorFamily R)
            (fun i ↦ firmlyQuasinonexpansive_of_firmlyNonexpansive (hT i))
            hHalfFix_nonempty] x0)) :=
    haugazeau_iteration_tendsto_projection_iInter_fixedPoints_of_firmlyNonexpansive
      (halfIdAddOperatorFamily R) hT hHalfFix_nonempty control hcontrol x0
  have hbest :
      IsBestApproximation x0 (commonFixedPointSet R)
        (P[commonFixedPointSet (halfIdAddOperatorFamily R),
          iInter_fixedPoints_isChebyshev_of_firmlyQuasinonexpansive
            (halfIdAddOperatorFamily R)
            (fun i ↦ firmlyQuasinonexpansive_of_firmlyNonexpansive (hT i))
            hHalfFix_nonempty] x0) := by
    rw [← iInter_fixedPoints_halfIdAddOperatorFamily_eq R]
    exact
      projectionPoint_isBestApproximation (commonFixedPointSet (halfIdAddOperatorFamily R))
        (iInter_fixedPoints_isChebyshev_of_firmlyQuasinonexpansive
          (halfIdAddOperatorFamily R)
          (fun i ↦ firmlyQuasinonexpansive_of_firmlyNonexpansive (hT i))
          hHalfFix_nonempty)
        x0
  have hproj_eq :
      P[commonFixedPointSet (halfIdAddOperatorFamily R),
        iInter_fixedPoints_isChebyshev_of_firmlyQuasinonexpansive
          (halfIdAddOperatorFamily R)
          (fun i ↦ firmlyQuasinonexpansive_of_firmlyNonexpansive (hT i))
          hHalfFix_nonempty] x0 =
        P[commonFixedPointSet R,
          iInter_fixedPoints_isChebyshev_of_halfIdAddOperatorFamily R hR hFix_nonempty] x0 := by
    exact
      eq_projectionPoint_of_isBestApproximation (commonFixedPointSet R)
        (iInter_fixedPoints_isChebyshev_of_halfIdAddOperatorFamily R hR hFix_nonempty) hbest
  rw [hproj_eq] at hlimit
  exact hlimit

end
