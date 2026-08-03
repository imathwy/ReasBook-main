import BauschkeLean.Chap20.Corollary_20_28
import BauschkeLean.Chap23.Theorem_23_44

/- Source/core/bridge triage:
- `source-facing`: the current corollary studies the affine curve `γ ↦ x_γ` satisfying
  `x_γ = γ x + (1 - γ) T x_γ` for a nonexpansive self-map `T`.
- `core/canonical`: the repository already owns this approximating-curve construction in
  Chapter 4 as `approximatingCurvePoint` on closed convex sets, and Chapter 23 already owns the
  inverse-parameter resolvent curve `SetValuedOperator.inverseParameterResolventCurve`.
- `bridge/view`: this file specializes the Chapter 4 approximating-curve API to `D = Set.univ`
  and identifies that source-facing curve with the Chapter 23 resolvent curve for
  `((id - T).toSetValuedOperator : SetValuedOperator H H)`. -/

open scoped InnerProductSpace Pointwise SetValuedOperator
open ERealFunction

universe u

namespace Function

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem id_sub_toSetValuedOperator_isMaximallyMonotone_of_nonexpansive
    (T : H → H) (hT : LipschitzWith 1 T) :
    Maximal IsMonotone (((id - T).toSetValuedOperator : SetValuedOperator H H)) := by
  let S : H → H := fun z ↦ z - T z
  have hmono : (S.toSetValuedOperator : SetValuedOperator H H).IsMonotone := by
    rw [SetValuedOperator.isMonotone_iff]
    intro x u y v hu hv
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hu hv
    subst u v
    -- Nonexpansiveness bounds the defect term `T x - T y` by the source difference `x - y`.
    have hnorm_le : ‖T x - T y‖ ≤ ‖x - y‖ := by
      simpa [dist_eq_norm] using hT.dist_le_mul x y
    have hsq_le : ‖T x - T y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      nlinarith [hnorm_le, norm_nonneg (T x - T y), norm_nonneg (x - y)]
    have hinner_le : ⟪x - y, T x - T y⟫_ℝ ≤ ‖x - y‖ ^ 2 := by
      have hnonneg : 0 ≤ ‖(x - y) - (T x - T y)‖ ^ 2 := by positivity
      nlinarith [norm_sub_sq_real (x - y) (T x - T y), hsq_le]
    have hrewrite :
        ⟪x - y, (x - T x) - (y - T y)⟫_ℝ =
          ‖x - y‖ ^ 2 - ⟪x - y, T x - T y⟫_ℝ := by
      calc
        ⟪x - y, (x - T x) - (y - T y)⟫_ℝ
            = ⟪x - y, (x - y) - (T x - T y)⟫_ℝ := by
                abel_nf
        _ = ⟪x - y, x - y⟫_ℝ - ⟪x - y, T x - T y⟫_ℝ := by
              rw [inner_sub_right]
        _ = ‖x - y‖ ^ 2 - ⟪x - y, T x - T y⟫_ℝ := by
              rw [real_inner_self_eq_norm_sq]
    change 0 ≤ ⟪x - y, (x - T x) - (y - T y)⟫_ℝ
    rw [hrewrite]
    linarith
  -- Corollary 20.28 upgrades monotone continuous single-valued operators to maximal monotone.
  exact Function.toSetValuedOperator_isMaximallyMonotone_of_monotone_continuous
    S hmono (continuous_id.sub hT.continuous)

/-- The fixed-point set of `T` is the zero set of the singleton-valued operator `Id - T`. -/
theorem fixedPoints_eq_zeros_id_sub_toSetValuedOperator
    {H : Type u} [NormedAddCommGroup H] (T : H → H) :
    Function.fixedPoints T =
      (((id - T).toSetValuedOperator : SetValuedOperator H H)).zeros := by
  -- Unfold both surfaces until the fixed-point equation and the zero residual coincide.
  ext x
  rw [Function.mem_fixedPoints_iff, SetValuedOperator.mem_zeros_iff,
    Function.toSetValuedOperator_apply, Set.mem_singleton_iff]
  constructor
  · intro hx
    simp [hx]
  · intro hx
    exact (sub_eq_zero.mp hx.symm).symm

/-- A nonexpansive self-map on a real Hilbert space has a Chebyshev fixed-point set whenever that
set is nonempty. -/
theorem fixedPoints_isChebyshev_of_nonexpansive (T : H → H) (hT : LipschitzWith 1 T)
    (hfix : (Function.fixedPoints T).Nonempty) :
    IsChebyshev (Function.fixedPoints T) := by
  let A : SetValuedOperator H H := ((id - T).toSetValuedOperator : SetValuedOperator H H)
  let hA : Maximal IsMonotone A :=
    id_sub_toSetValuedOperator_isMaximallyMonotone_of_nonexpansive T hT
  have hzero : A.zeros.Nonempty := by
    -- Transport fixed-point nonemptiness through the `Fix T = zer(Id - T)` bridge.
    simpa [A, fixedPoints_eq_zeros_id_sub_toSetValuedOperator T] using hfix
  -- Proposition 23.39 packages nonempty zero sets of maximal monotone operators as Chebyshev.
  simpa [A, fixedPoints_eq_zeros_id_sub_toSetValuedOperator T] using
    (SetValuedOperator.Maximal.zeros_isChebyshev hA hzero)

/-- The Chapter 23 inverse-parameter resolvent curve for `Id - T` is exactly the source-facing
affine approximating curve from the present corollary. -/
theorem inverseParameterResolventCurve_eq_affine_combination_of_nonexpansive
    (T : H → H) (hT : LipschitzWith 1 T) (γ : Set.Ioo (0 : ℝ) 1) (x : H) :
    ((id - T).toSetValuedOperator).inverseParameterResolventCurve
        (id_sub_toSetValuedOperator_isMaximallyMonotone_of_nonexpansive T hT) x
        ⟨(γ : ℝ) / (1 - (γ : ℝ)), div_pos γ.2.1 (sub_pos.mpr γ.2.2)⟩ =
      (γ : ℝ) • x + (1 - (γ : ℝ)) •
        T
          (((id - T).toSetValuedOperator).inverseParameterResolventCurve
            (id_sub_toSetValuedOperator_isMaximallyMonotone_of_nonexpansive T hT) x
            ⟨(γ : ℝ) / (1 - (γ : ℝ)), div_pos γ.2.1 (sub_pos.mpr γ.2.2)⟩) := by
  let A : SetValuedOperator H H := ((id - T).toSetValuedOperator : SetValuedOperator H H)
  let hA : Maximal IsMonotone A :=
    id_sub_toSetValuedOperator_isMaximallyMonotone_of_nonexpansive T hT
  let δ : PosReal := ⟨(γ : ℝ) / (1 - (γ : ℝ)), div_pos γ.2.1 (sub_pos.mpr γ.2.2)⟩
  let p := A.inverseParameterResolventCurve hA x δ
  have hp_mem :
      A.inverseParameterResolventCurve hA x δ ∈ J[(((δ⁻¹ : PosReal) : ℝ) • A)] x := by
    -- The inverse-parameter curve is the resolvent point evaluated at the reciprocal parameter.
    rw [SetValuedOperator.inverseParameterResolventCurve_apply,
      SetValuedOperator.resolvent_smul_eq_singleton_resolventMap_of_maximal A hA δ⁻¹ x]
    simp
  have hp_graph : (p, (δ : ℝ) • (x - p)) ∈ gra A := by
    -- Convert the resolvent characterization into the graph relation used by the source proof.
    simpa [p, SetValuedOperator.inverseParameterResolventCurve_apply] using
      (SetValuedOperator.mem_resolvent_smul_iff_mem_graph A δ⁻¹ x p).1 hp_mem
  have hresidual : (δ : ℝ) • (x - p) = p - T p := by
    -- For the singleton-valued operator `Id - T`, the graph value is exactly `p - T p`.
    simpa [A, SetValuedOperator.mem_graph, Function.toSetValuedOperator_apply] using hp_graph
  have hcoef : (1 - (γ : ℝ)) * (δ : ℝ) = (γ : ℝ) := by
    -- The source parameter change `δ = γ / (1 - γ)` clears denominators linearly.
    have hden_ne : (1 - (γ : ℝ)) ≠ 0 := sub_ne_zero.mpr (ne_of_gt γ.2.2)
    dsimp [δ]
    field_simp [hden_ne]
  have hscaled :
      (γ : ℝ) • (x - p) = (1 - (γ : ℝ)) • (p - T p) := by
    -- Multiply the residual identity by `1 - γ` to recover the affine-curve coefficients.
    have hmul := congrArg (fun z : H ↦ (1 - (γ : ℝ)) • z) hresidual
    simpa [smul_smul, hcoef, mul_assoc, mul_comm, mul_left_comm] using hmul
  have hcombine :
      (γ : ℝ) • x + (1 - (γ : ℝ)) • T p =
        (γ : ℝ) • p + (1 - (γ : ℝ)) • p := by
    -- Move the two residual terms to opposite sides so the right-hand side becomes `1 • p`.
    have hrewrite :
        (γ : ℝ) • x - (γ : ℝ) • p =
          (1 - (γ : ℝ)) • p - (1 - (γ : ℝ)) • T p := by
      simpa [smul_sub] using hscaled
    have hsum :=
      congrArg (fun z : H ↦ z + (γ : ℝ) • p + (1 - (γ : ℝ)) • T p) hrewrite
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum
  -- Assemble the affine fixed-point equation from the coefficient identity `γ + (1 - γ) = 1`.
  calc
    p = (γ : ℝ) • p + (1 - (γ : ℝ)) • p := by
      rw [← add_smul]
      simp
    _ = (γ : ℝ) • x + (1 - (γ : ℝ)) • T p := by
      simpa [p] using hcombine.symm

/-- The source parameter change `γ ↦ γ / (1 - γ)` sends
`γ ↓ 0` through `]0,1[` to the Chapter 23 filter `SetValuedOperator.atZeroRightWithinUnitInterval`.
-/
theorem tendstoPosRealRatioAtZeroRightWithinUnitInterval :
    Filter.Tendsto
      (fun γ : Set.Ioo (0 : ℝ) 1 ↦
        (⟨(γ : ℝ) / (1 - (γ : ℝ)), div_pos γ.2.1 (sub_pos.mpr γ.2.2)⟩ : PosReal))
      (Filter.comap (fun γ : Set.Ioo (0 : ℝ) 1 ↦ (γ : ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)))
      SetValuedOperator.atZeroRightWithinUnitInterval := by
  have hratioSubtype :
      Filter.Tendsto
        (fun γ : Set.Ioo (0 : ℝ) 1 ↦ (γ : ℝ) / (1 - (γ : ℝ)))
        (Filter.comap (fun γ : Set.Ioo (0 : ℝ) 1 ↦ (γ : ℝ))
          (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) := by
    -- The ratio tends to `0`, and positivity is automatic because the source parameter stays in
    -- `]0,1[`.
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hsubtype :
          Filter.Tendsto
            (fun γ : Set.Ioo (0 : ℝ) 1 ↦ (γ : ℝ))
            (Filter.comap (fun γ : Set.Ioo (0 : ℝ) 1 ↦ (γ : ℝ))
              (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)))
            (nhds (0 : ℝ)) :=
        (Filter.map_comap_le : Filter.Tendsto (fun γ : Set.Ioo (0 : ℝ) 1 ↦ (γ : ℝ))
          (Filter.comap (fun γ : Set.Ioo (0 : ℝ) 1 ↦ (γ : ℝ))
            (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)))
          (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1))).trans nhdsWithin_le_nhds
      have hcont : ContinuousAt (fun t : ℝ ↦ t / (1 - t)) 0 := by
        refine ContinuousAt.div continuousAt_id ?_ ?_
        · exact continuousAt_const.sub continuousAt_id
        · norm_num
      simpa using hcont.tendsto.comp hsubtype
    · exact Filter.Eventually.of_forall fun γ ↦ div_pos γ.2.1 (sub_pos.mpr γ.2.2)
  simpa [SetValuedOperator.atZeroRightWithinUnitInterval, nhdsWithin_Ioo_eq_nhdsGT zero_lt_one]
    using hratioSubtype

/-- Existence-and-uniqueness for the affine curve used in the current corollary: if `T : H → H`
is nonexpansive and
`x ∈ H`, then the equations
`x_γ = γ x + (1 - γ) T x_γ` for `γ ∈ ]0,1[` define a unique curve on `]0,1[`. -/
theorem existsUnique_curve_eq_affine_combination_of_nonexpansive
    (T : H → H) (hT : LipschitzWith 1 T) (x : H) :
    ∃! curve : Set.Ioo (0 : ℝ) 1 → H,
      ∀ γ : Set.Ioo (0 : ℝ) 1,
        curve γ = (γ : ℝ) • x + (1 - (γ : ℝ)) • T (curve γ) := by
  let canonicalCurve : Set.Ioo (0 : ℝ) 1 → H := fun γ ↦
    ((id - T).toSetValuedOperator).inverseParameterResolventCurve
      (id_sub_toSetValuedOperator_isMaximallyMonotone_of_nonexpansive T hT) x
      ⟨(γ : ℝ) / (1 - (γ : ℝ)), div_pos γ.2.1 (sub_pos.mpr γ.2.2)⟩
  refine ⟨canonicalCurve, ?_, ?_⟩
  · intro γ
    -- The Chapter 23 curve already satisfies the source affine equation pointwise.
    simpa [canonicalCurve] using
      inverseParameterResolventCurve_eq_affine_combination_of_nonexpansive T hT γ x
  intro curve hcurve
  funext γ
  have hcanonical :
      canonicalCurve γ =
        (γ : ℝ) • x + (1 - (γ : ℝ)) • T (canonicalCurve γ) := by
    simpa [canonicalCurve] using
      inverseParameterResolventCurve_eq_affine_combination_of_nonexpansive T hT γ x
  have hdiff :
      canonicalCurve γ - curve γ =
        (1 - (γ : ℝ)) • (T (canonicalCurve γ) - T (curve γ)) := by
    -- Subtract the two affine fixed-point equations to isolate the contraction defect.
    have hleft :
        canonicalCurve γ - curve γ =
          canonicalCurve γ - ((γ : ℝ) • x + (1 - (γ : ℝ)) • T (curve γ)) := by
      exact congrArg (fun z : H ↦ canonicalCurve γ - z) (hcurve γ)
    have hboth :
        canonicalCurve γ - ((γ : ℝ) • x + (1 - (γ : ℝ)) • T (curve γ)) =
          ((γ : ℝ) • x + (1 - (γ : ℝ)) • T (canonicalCurve γ)) -
            ((γ : ℝ) • x + (1 - (γ : ℝ)) • T (curve γ)) := by
      exact congrArg
        (fun z : H ↦ z - ((γ : ℝ) • x + (1 - (γ : ℝ)) • T (curve γ)))
        hcanonical
    have hsub := hleft.trans hboth
    simpa [sub_eq_add_neg, smul_sub, add_assoc, add_left_comm, add_comm] using hsub
  have hnorm :
      ‖canonicalCurve γ - curve γ‖ ≤
        (1 - (γ : ℝ)) * ‖canonicalCurve γ - curve γ‖ := by
    have hγ_nonneg : 0 ≤ 1 - (γ : ℝ) := by linarith [γ.2.2]
    calc
      ‖canonicalCurve γ - curve γ‖
        = ‖(1 - (γ : ℝ)) • (T (canonicalCurve γ) - T (curve γ))‖ := by
            rw [hdiff]
      _ = |1 - (γ : ℝ)| * ‖T (canonicalCurve γ) - T (curve γ)‖ := norm_smul _ _
      _ = (1 - (γ : ℝ)) * ‖T (canonicalCurve γ) - T (curve γ)‖ := by
            rw [abs_of_nonneg hγ_nonneg]
      _ ≤ (1 - (γ : ℝ)) * ‖canonicalCurve γ - curve γ‖ := by
            gcongr
            simpa [dist_eq_norm] using hT.dist_le_mul (canonicalCurve γ) (curve γ)
  have hnorm_eq_zero : ‖canonicalCurve γ - curve γ‖ = 0 := by
    have hγ_lt_one : 1 - (γ : ℝ) < 1 := by linarith [γ.2.1]
    nlinarith [norm_nonneg (canonicalCurve γ - curve γ), hnorm, hγ_lt_one]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm_eq_zero)).symm

/-- Corollary 23.45. If `T : H → H` is nonexpansive, if `Fix T ≠ ∅`, and if
`x ∈ H`, then
the source-facing curve `γ ↦ x_γ`, equivalently the inverse-parameter resolvent curve for
`Id - T`, converges to the metric projection of `x` onto `Fix T` as `γ ↓ 0` through `]0,1[`. -/
theorem tendsto_inverseParameterResolventCurve_projection_of_fixedPoints_nonempty
    (T : H → H) (hT : LipschitzWith 1 T) (x : H) (hfix : (Function.fixedPoints T).Nonempty) :
    Filter.Tendsto
      (fun γ : Set.Ioo (0 : ℝ) 1 ↦
        ((id - T).toSetValuedOperator).inverseParameterResolventCurve
          (id_sub_toSetValuedOperator_isMaximallyMonotone_of_nonexpansive T hT) x
          ⟨(γ : ℝ) / (1 - (γ : ℝ)), div_pos γ.2.1 (sub_pos.mpr γ.2.2)⟩)
      (Filter.comap (fun γ : Set.Ioo (0 : ℝ) 1 ↦ (γ : ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)))
      (nhds
        (projectionPoint (Function.fixedPoints T)
          (fixedPoints_isChebyshev_of_nonexpansive T hT hfix) x)) := by
  let A : SetValuedOperator H H := ((id - T).toSetValuedOperator : SetValuedOperator H H)
  let hA : Maximal IsMonotone A :=
    id_sub_toSetValuedOperator_isMaximallyMonotone_of_nonexpansive T hT
  have hzero : A.zeros.Nonempty := by
    -- Repackage the fixed-point hypothesis into the Chapter 23 zero-set hypothesis.
    simpa [A, fixedPoints_eq_zeros_id_sub_toSetValuedOperator T] using hfix
  have hresolvent :
      Filter.Tendsto (A.inverseParameterResolventCurve hA x)
        SetValuedOperator.atZeroRightWithinUnitInterval
        (nhds (P[A.zeros, SetValuedOperator.Maximal.zeros_isChebyshev hA hzero] x)) :=
    SetValuedOperator.tendsto_resolventMap_atZeroRight_of_zeros_nonempty A hA x hzero
  have hproj_best :
      IsBestApproximation x (Function.fixedPoints T)
        (P[A.zeros, SetValuedOperator.Maximal.zeros_isChebyshev hA hzero] x) := by
    -- Transport the Chapter 23 projection certificate across `Fix T = zer(Id - T)`.
    simpa [A, fixedPoints_eq_zeros_id_sub_toSetValuedOperator T] using
      projectionPoint_isBestApproximation A.zeros
        (SetValuedOperator.Maximal.zeros_isChebyshev hA hzero) x
  have hproj_eq :
      P[A.zeros, SetValuedOperator.Maximal.zeros_isChebyshev hA hzero] x =
        projectionPoint (Function.fixedPoints T)
          (fixedPoints_isChebyshev_of_nonexpansive T hT hfix) x :=
    eq_projectionPoint_of_isBestApproximation
      (Function.fixedPoints T) (fixedPoints_isChebyshev_of_nonexpansive T hT hfix) hproj_best
  -- Compose Theorem 23.44 with the source parameter change and rewrite the projection target.
  simpa [A, hproj_eq] using hresolvent.comp tendstoPosRealRatioAtZeroRightWithinUnitInterval

/-- Divergence alternative for the current corollary: if `T : H → H` is nonexpansive, if
`Fix T = ∅`, and if `x ∈ H`, then
the norms of the source-facing curve `γ ↦ x_γ`, equivalently the inverse-parameter resolvent
curve for `Id - T`, satisfy `‖x_γ‖ → +∞` as `γ ↓ 0` through `]0,1[`. -/
theorem norm_inverseParameterResolventCurve_tendsto_atTop_of_fixedPoints_eq_empty
    (T : H → H) (hT : LipschitzWith 1 T) (x : H) (hfix : Function.fixedPoints T = ∅) :
    Filter.Tendsto
      (fun γ : Set.Ioo (0 : ℝ) 1 ↦
        ‖((id - T).toSetValuedOperator).inverseParameterResolventCurve
            (id_sub_toSetValuedOperator_isMaximallyMonotone_of_nonexpansive T hT) x
            ⟨(γ : ℝ) / (1 - (γ : ℝ)), div_pos γ.2.1 (sub_pos.mpr γ.2.2)⟩‖)
      (Filter.comap (fun γ : Set.Ioo (0 : ℝ) 1 ↦ (γ : ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)))
      Filter.atTop := by
  let A : SetValuedOperator H H := ((id - T).toSetValuedOperator : SetValuedOperator H H)
  let hA : Maximal IsMonotone A :=
    id_sub_toSetValuedOperator_isMaximallyMonotone_of_nonexpansive T hT
  have hzero : A.zeros = ∅ := by
    -- The empty fixed-point hypothesis is exactly the empty-zero-set hypothesis for `Id - T`.
    simpa [A, fixedPoints_eq_zeros_id_sub_toSetValuedOperator T] using hfix
  have hresolvent :
      Filter.Tendsto (fun γ : PosReal ↦ ‖A.inverseParameterResolventCurve hA x γ‖)
        SetValuedOperator.atZeroRightWithinUnitInterval
        Filter.atTop :=
    SetValuedOperator.norm_resolventMap_tendsto_atTop_atZeroRight_of_zeros_eq_empty A hA x hzero
  have hcomp :
      Filter.Tendsto
        (fun γ : Set.Ioo (0 : ℝ) 1 ↦
          ‖A.inverseParameterResolventCurve hA x
              (⟨(γ : ℝ) / (1 - (γ : ℝ)), div_pos γ.2.1 (sub_pos.mpr γ.2.2)⟩ : PosReal)‖)
        (Filter.comap (fun γ : Set.Ioo (0 : ℝ) 1 ↦ (γ : ℝ))
          (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)))
        Filter.atTop :=
    hresolvent.comp tendstoPosRealRatioAtZeroRightWithinUnitInterval
  -- Compose Theorem 23.44 with the same parameter change used in the source statement.
  simpa [A] using hcomp

end Function
