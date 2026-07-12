import Mathlib
import DifferentialForms_Cartan_1970.I.section04.«0013_Proposition_4_1»
import DifferentialForms_Cartan_1970.III.section11.«0008_Proposition_4_1»
import DifferentialForms_Cartan_1970.III.section11.«0013_Proposition_5_2»
import DifferentialForms_Cartan_1970.V.section21.«0012_Exercise_3».Index

-- Semantic Lean search tool `lean_leansearch` was unavailable in this session; the statement shape
-- below was chosen from local mathlib and repository inspection.

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Topology
open MeromorphicOn

noncomputable section

open scoped JacobiTheta

/-- Helper for Cartan section21 0012_Exercise_3: continuity of a scalar coefficient along a line
segment is enough to make the associated scalar `1`-form curve-integrable on that segment. -/
private lemma curveIntegrableScalarOneFormOnSegment
    {D : Set ℂ} {φ : ℂ → ℂ} {a b : ℂ}
    (hφ : ContinuousOn φ D) (hseg : Set.range (Path.segment a b) ⊆ D) :
    CurveIntegrable (fun z ↦ ((φ dz) z)) (Path.segment a b) := by
  rw [curveIntegrable_segment]
  have hline :
      ContinuousOn (fun t : ℝ ↦ φ (AffineMap.lineMap a b t)) (Set.Icc (0 : ℝ) 1) := by
    refine hφ.comp (by fun_prop) ?_
    intro t ht
    exact hseg ⟨⟨t, ht⟩, by simp [Path.segment_apply]⟩
  have hcont :
      ContinuousOn (fun t : ℝ ↦ φ (AffineMap.lineMap a b t) * (b - a)) (Set.Icc (0 : ℝ) 1) :=
    hline.mul continuousOn_const
  have hInt :
      IntervalIntegrable (fun t : ℝ ↦ φ (AffineMap.lineMap a b t) * (b - a))
        MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable_of_Icc zero_le_one
  simpa [Complex.scalarOneForm_apply, mul_comm] using hInt

/-- Helper for Cartan section21 0012_Exercise_3: the canonical singleton family coming from the
period-parallelogram boundary path is an oriented boundary. -/
lemma thetaOnePeriodParallelogramSingletonBoundary
    (τ : ℂ) (hτ : 0 < τ.im) (z₀ : ℂ) :
    IsOrientedBoundaryOf ((theta_one_period_pair τ hτ).periodParallelogram z₀)
      (fun _ : Unit ↦
        (periodParallelogramBoundaryPath (L := theta_one_period_pair τ hτ) z₀).toClosedPath) := by
  -- Proposition 5.2 already packages the canonical period-cell loop as an oriented boundary.
  simpa using
    periodParallelogramBoundary_isOrientedBoundaryOf (L := theta_one_period_pair τ hτ) z₀

/-- Helper for Cartan section21 0012_Exercise_3: boundary nonvanishing makes the logarithmic
derivative of `θ₁` continuous along the period-parallelogram frontier. -/
lemma thetaOneLogDerivContinuousOnBoundary
    (τ : ℂ) (hτ : 0 < τ.im) (z₀ : ℂ)
    (hboundary :
      ∀ z ∈ frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀), (θ₁[τ]) z ≠ 0) :
    ContinuousOn (logDeriv (θ₁[τ]))
      (frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀)) := by
  intro z hz
  -- Away from zeros, entire holomorphy of `θ₁` upgrades `logDeriv θ₁` to a continuous function.
  have hdiff :
      DifferentiableAt ℂ (logDeriv (θ₁[τ])) z :=
    differentiableAt_logDeriv_of_analyticAt_nonzero
      ((exercise_3_theta_one_differentiable τ hτ).analyticAt z) (hboundary z hz)
  exact ContinuousAt.continuousWithinAt hdiff.continuousAt

/-- Helper for Cartan section21 0012_Exercise_3: the scalar one-form built from `logDeriv θ₁` is
continuous on the boundary frontier once `θ₁` has no boundary zeros. -/
lemma thetaOneLogDerivOneFormContinuousOnBoundary
    (τ : ℂ) (hτ : 0 < τ.im) (z₀ : ℂ)
    (hboundary :
      ∀ z ∈ frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀), (θ₁[τ]) z ≠ 0) :
    ContinuousOn (fun z ↦ ((logDeriv (θ₁[τ]) dz) z))
      (frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀)) := by
  -- Repackage scalar continuity as continuity of the associated scalar one-form.
  simpa [Complex.scalarOneForm] using
    (ContinuousLinearMap.smulRightL ℂ ℂ ℂ).continuous₂.comp_continuousOn
      ((continuousOn_const :
          ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ))
            (frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀))).prodMk
        (thetaOneLogDerivContinuousOnBoundary τ hτ z₀ hboundary))

/-- Helper for Cartan section21 0012_Exercise_3: the right boundary edge is the `+1` translate of
the forward left base edge, so the `θ₁` logarithmic-derivative integral matches exactly. -/
lemma thetaOneRightEdgeIntegral_eq_leftBase
    (τ : ℂ) (hτ : 0 < τ.im) (z₀ : ℂ) :
    ∫ᶜ z in Path.segment (z₀ + 1) (z₀ + 1 + τ), ((logDeriv (θ₁[τ]) dz) z) =
      ∫ᶜ z in Path.segment z₀ (z₀ + τ), ((logDeriv (θ₁[τ]) dz) z) := by
  have hper1 : Function.Periodic (logDeriv (θ₁[τ])) 1 := by
    -- The `+1` translation law for `θ₁` has no additive defect on the logarithmic derivative.
    intro z
    simpa using theta_one_logDeriv_add_one τ z hτ
  have hz₂ : z₀ + τ + 1 = z₀ + 1 + τ := by
    ring
  -- The public segment-translation lemma applies directly in the concrete `1, τ` coordinates.
  calc
    ∫ᶜ z in Path.segment (z₀ + 1) (z₀ + 1 + τ), ((logDeriv (θ₁[τ]) dz) z) =
        ∫ᶜ z in Path.segment (z₀ + 1) (z₀ + τ + 1), ((logDeriv (θ₁[τ]) dz) z) := by
          rw [hz₂]
    _ = ∫ᶜ z in Path.segment z₀ (z₀ + τ), ((logDeriv (θ₁[τ]) dz) z) := by
          simpa using
            (curveIntegral_segment_translate_eq_of_periodic
              (φ := logDeriv (θ₁[τ])) (a := z₀) (b := z₀ + τ) (ω := 1) hper1)

/-- Helper for Cartan section21 0012_Exercise_3: translating the reversed bottom edge by `τ`
rewrites the top edge to the negative bottom contribution plus the expected `2π i` defect. -/
lemma thetaOneTopEdgeIntegral_eq_neg_bottom_add_twoPiI
    (τ : ℂ) (hτ : 0 < τ.im) (z₀ : ℂ)
    (hboundary :
      ∀ z ∈ frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀), (θ₁[τ]) z ≠ 0) :
    ∫ᶜ z in Path.segment (z₀ + 1 + τ) (z₀ + τ), ((logDeriv (θ₁[τ]) dz) z) =
      -∫ᶜ z in Path.segment z₀ (z₀ + 1), ((logDeriv (θ₁[τ]) dz) z) +
        (2 * Real.pi : ℂ) * Complex.I := by
  let z₁ : ℂ := z₀ + 1
  let z₂ : ℂ := z₀ + 1 + τ
  let z₃ : ℂ := z₀ + τ
  have hlog_coeff_cont :
      ContinuousOn (logDeriv (θ₁[τ]))
        (frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀)) :=
    thetaOneLogDerivContinuousOnBoundary τ hτ z₀ hboundary
  have hbottomRev_frontier :
      Set.range (Path.segment z₁ z₀) ⊆
        frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀) := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    have ht0 : 0 ≤ 1 - (t : ℝ) := by
      linarith [t.2.2]
    have ht1 : 1 - (t : ℝ) ≤ 1 := by
      linarith [t.2.1]
    have hpoint :
        Path.segment z₁ z₀ t =
          z₀ + (1 - (t : ℝ)) • (1 : ℂ) + (0 : ℝ) • τ := by
      simp [z₁, Path.segment_apply, AffineMap.lineMap_apply, add_assoc, add_left_comm, add_comm,
        sub_eq_add_neg]
    rw [hpoint]
    exact
      mem_frontier_periodParallelogram_of_coord_eq_zero_or_one
        (L := theta_one_period_pair τ hτ) (z₀ := z₀) ht0 ht1 (by norm_num) (by norm_num)
        (Or.inr <| Or.inr <| Or.inl rfl)
  have hbottomRevInt :
      CurveIntegrable (fun z ↦ ((logDeriv (θ₁[τ]) dz) z)) (Path.segment z₁ z₀) := by
    -- Boundary continuity supplies curve integrability on the reversed bottom edge.
    exact
      curveIntegrableScalarOneFormOnSegment
        (a := z₁) (b := z₀) hlog_coeff_cont
        hbottomRev_frontier
  have hconstInt :
      CurveIntegrable
        (fun z ↦ (((fun _ : ℂ ↦ -((2 * Real.pi : ℂ) * Complex.I)) dz) z))
        (Path.segment z₁ z₀) := by
    -- The constant defect one-form is trivially integrable on the same segment.
    exact
      curveIntegrableScalarOneFormOnSegment
        (a := z₁) (b := z₀)
        (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ -((2 * Real.pi : ℂ) * Complex.I)) Set.univ)
        (by intro z hz; simp)
  have htranslate :
      ∫ᶜ z in Path.segment z₂ z₃, ((logDeriv (θ₁[τ]) dz) z) =
        ∫ᶜ z in Path.segment z₁ z₀,
          (((fun w ↦ logDeriv (θ₁[τ]) (w + τ)) dz) z) := by
    -- Parameterize the top edge as the `+τ` translate of the reversed bottom edge.
    rw [curveIntegral_segment, curveIntegral_segment]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro t _
    have hline :
        AffineMap.lineMap z₂ z₃ t = AffineMap.lineMap z₁ z₀ t + τ := by
      simp [z₁, z₂, z₃, AffineMap.lineMap_apply, add_assoc, add_left_comm, add_comm]
    have hdir : z₃ - z₂ = z₀ - z₁ := by
      simp [z₁, z₂, z₃, add_assoc, add_left_comm, add_comm]
    simp [Complex.scalarOneForm_apply, hline, hdir]
  have hadd_form :
      (fun z ↦ (((fun w ↦ logDeriv (θ₁[τ]) w - (2 * Real.pi : ℂ) * Complex.I) dz) z)) =
        (fun z ↦ ((logDeriv (θ₁[τ]) dz) z)) +
          (fun z ↦ (((fun _ : ℂ ↦ -((2 * Real.pi : ℂ) * Complex.I)) dz) z)) := by
    -- Split the translated logarithmic derivative into the original part and the constant defect.
    funext z
    ext v
    simp [Complex.scalarOneForm_apply, sub_eq_add_neg, add_mul]
  have hdefect :
      ∫ᶜ z in Path.segment z₂ z₃, ((logDeriv (θ₁[τ]) dz) z) =
        ∫ᶜ z in Path.segment z₁ z₀, ((logDeriv (θ₁[τ]) dz) z) +
          ∫ᶜ z in Path.segment z₁ z₀,
            (((fun _ : ℂ ↦ -((2 * Real.pi : ℂ) * Complex.I)) dz) z) := by
    -- Route correction: apply the `+τ` defect pointwise only on the bottom boundary segment.
    calc
      ∫ᶜ z in Path.segment z₂ z₃, ((logDeriv (θ₁[τ]) dz) z) =
          ∫ᶜ z in Path.segment z₁ z₀,
            (((fun w ↦ logDeriv (θ₁[τ]) (w + τ)) dz) z) := htranslate
      _ =
          ∫ᶜ z in Path.segment z₁ z₀,
            (((fun w ↦ logDeriv (θ₁[τ]) w - (2 * Real.pi : ℂ) * Complex.I) dz) z) := by
              rw [curveIntegral_segment, curveIntegral_segment]
              refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
              intro t ht
              have hz_frontier :
                  AffineMap.lineMap z₁ z₀ t ∈
                    frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀) := by
                refine hbottomRev_frontier ?_
                refine ⟨⟨t, ?_⟩, by simp [Path.segment_apply]⟩
                refine ⟨le_of_lt ?_, ?_⟩
                · simpa using ht.1
                · simpa using ht.2
              have hz_nonzero : (θ₁[τ]) (AffineMap.lineMap z₁ z₀ t) ≠ 0 :=
                hboundary _ hz_frontier
              have hshift :
                  logDeriv (θ₁[τ]) (AffineMap.lineMap z₁ z₀ t + τ) =
                    logDeriv (θ₁[τ]) (AffineMap.lineMap z₁ z₀ t) -
                      (2 * Real.pi : ℂ) * Complex.I :=
                theta_one_logDeriv_add_tau τ (AffineMap.lineMap z₁ z₀ t) hτ hz_nonzero
              simpa [Complex.scalarOneForm_apply, hshift]
      _ =
          ∫ᶜ z in Path.segment z₁ z₀, ((logDeriv (θ₁[τ]) dz) z) +
            ∫ᶜ z in Path.segment z₁ z₀,
              (((fun _ : ℂ ↦ -((2 * Real.pi : ℂ) * Complex.I)) dz) z) := by
              simpa [hadd_form] using curveIntegral_add hbottomRevInt hconstInt
  have hconst_eval :
      ∫ᶜ z in Path.segment z₁ z₀,
          (((fun _ : ℂ ↦ -((2 * Real.pi : ℂ) * Complex.I)) dz) z) =
        (2 * Real.pi : ℂ) * Complex.I := by
    -- The constant defect integrates to `2π i` because the reversed bottom edge has length `-1`.
    rw [curveIntegral_segment]
    simp [z₁, Complex.scalarOneForm_apply]
  have hbottomRev_symm :
      ∫ᶜ z in Path.segment z₁ z₀, ((logDeriv (θ₁[τ]) dz) z) =
        -∫ᶜ z in Path.segment z₀ z₁, ((logDeriv (θ₁[τ]) dz) z) := by
    -- Reversing the bottom edge flips the sign of the integral.
    simpa using
      curveIntegral_symm (ω := fun z ↦ ((logDeriv (θ₁[τ]) dz) z)) (γ := Path.segment z₀ z₁)
  -- Substitute the constant correction and then rewrite the reversed bottom edge by symmetry.
  calc
    ∫ᶜ z in Path.segment (z₀ + 1 + τ) (z₀ + τ), ((logDeriv (θ₁[τ]) dz) z) =
        ∫ᶜ z in Path.segment z₁ z₀, ((logDeriv (θ₁[τ]) dz) z) +
          (2 * Real.pi : ℂ) * Complex.I := by
            simpa [z₁, z₂, z₃] using hdefect.trans (by rw [hconst_eval])
    _ =
        -∫ᶜ z in Path.segment z₀ (z₀ + 1), ((logDeriv (θ₁[τ]) dz) z) +
          (2 * Real.pi : ℂ) * Complex.I := by
            simpa [z₁] using congrArg (fun w : ℂ ↦ w + (2 * Real.pi : ℂ) * Complex.I)
              hbottomRev_symm

/-- Helper for Cartan section21 0012_Exercise_3: the canonical period-parallelogram boundary path
has normalized `θ₁` logarithmic-derivative integral equal to `1`. -/
lemma thetaOnePeriodParallelogramBoundaryIntegralDivTwoPiI
    (τ : ℂ) (hτ : 0 < τ.im) (z₀ : ℂ)
    (hboundary :
      ∀ z ∈ frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀), (θ₁[τ]) z ≠ 0) :
    (∫ᶜ z in (periodParallelogramBoundaryPath (L := theta_one_period_pair τ hτ) z₀).toClosedPath.toPath,
        ((logDeriv (θ₁[τ]) dz) z)) /
      (2 * Real.pi * Complex.I : ℂ) = 1 := by
  let z₁ : ℂ := z₀ + 1
  let z₂ : ℂ := z₀ + 1 + τ
  let z₃ : ℂ := z₀ + τ
  have hlog_coeff_cont :
      ContinuousOn (logDeriv (θ₁[τ]))
        (frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀)) :=
    thetaOneLogDerivContinuousOnBoundary τ hτ z₀ hboundary
  have hbottom_frontier :
      Set.range (Path.segment z₀ z₁) ⊆
        frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀) := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    have hpoint :
        Path.segment z₀ z₁ t = z₀ + (t : ℝ) • (1 : ℂ) + (0 : ℝ) • τ := by
      simp [z₁, Path.segment_apply, AffineMap.lineMap_apply, add_assoc, add_left_comm, add_comm]
    rw [hpoint]
    exact
      mem_frontier_periodParallelogram_of_coord_eq_zero_or_one
        (L := theta_one_period_pair τ hτ) (z₀ := z₀) t.2.1 t.2.2 (by norm_num) (by norm_num)
        (Or.inr <| Or.inr <| Or.inl rfl)
  have hright_frontier :
      Set.range (Path.segment z₁ z₂) ⊆
        frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀) := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    have hpoint :
        Path.segment z₁ z₂ t = z₀ + (1 : ℝ) • (1 : ℂ) + (t : ℝ) • τ := by
      simp [z₁, z₂, Path.segment_apply, AffineMap.lineMap_apply, add_assoc, add_left_comm,
        add_comm]
    rw [hpoint]
    exact
      mem_frontier_periodParallelogram_of_coord_eq_zero_or_one
        (L := theta_one_period_pair τ hτ) (z₀ := z₀)
        (by norm_num) (by norm_num) t.2.1 t.2.2
        (Or.inr <| Or.inl rfl)
  have htop_frontier :
      Set.range (Path.segment z₂ z₃) ⊆
        frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀) := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    have ht0 : 0 ≤ 1 - (t : ℝ) := by
      linarith [t.2.2]
    have ht1 : 1 - (t : ℝ) ≤ 1 := by
      linarith [t.2.1]
    have hpoint :
        Path.segment z₂ z₃ t = z₀ + (1 - (t : ℝ)) • (1 : ℂ) + (1 : ℝ) • τ := by
      simp [z₂, z₃, Path.segment_apply, AffineMap.lineMap_apply, add_assoc, add_left_comm,
        add_comm, sub_eq_add_neg]
      ring
    rw [hpoint]
    exact
      mem_frontier_periodParallelogram_of_coord_eq_zero_or_one
        (L := theta_one_period_pair τ hτ) (z₀ := z₀) ht0 ht1 (by norm_num) (by norm_num)
        (Or.inr <| Or.inr <| Or.inr rfl)
  have hleft_frontier :
      Set.range (Path.segment z₃ z₀) ⊆
        frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀) := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    have ht0 : 0 ≤ 1 - (t : ℝ) := by
      linarith [t.2.2]
    have ht1 : 1 - (t : ℝ) ≤ 1 := by
      linarith [t.2.1]
    have hpoint :
        Path.segment z₃ z₀ t = z₀ + (0 : ℝ) • (1 : ℂ) + (1 - (t : ℝ)) • τ := by
      simp [z₃, Path.segment_apply, AffineMap.lineMap_apply, add_assoc, add_left_comm, add_comm,
        sub_eq_add_neg]
      ring
    rw [hpoint]
    exact
      mem_frontier_periodParallelogram_of_coord_eq_zero_or_one
        (L := theta_one_period_pair τ hτ) (z₀ := z₀)
        (by norm_num) (by norm_num) ht0 ht1
        (Or.inl rfl)
  have hsegmentIntegrable {a b : ℂ}
      (hfrontier :
        Set.range (Path.segment a b) ⊆
          frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀)) :
      CurveIntegrable (fun z ↦ ((logDeriv (θ₁[τ]) dz) z)) (Path.segment a b) := by
    -- Boundary continuity makes each straight edge curve-integrable.
    exact
      curveIntegrableScalarOneFormOnSegment
        (a := a) (b := b) hlog_coeff_cont
        hfrontier
  have hbottomInt :
      CurveIntegrable (fun z ↦ ((logDeriv (θ₁[τ]) dz) z)) (Path.segment z₀ z₁) :=
    hsegmentIntegrable hbottom_frontier
  have hrightInt :
      CurveIntegrable (fun z ↦ ((logDeriv (θ₁[τ]) dz) z)) (Path.segment z₁ z₂) :=
    hsegmentIntegrable hright_frontier
  have htopInt :
      CurveIntegrable (fun z ↦ ((logDeriv (θ₁[τ]) dz) z)) (Path.segment z₂ z₃) :=
    hsegmentIntegrable htop_frontier
  have hleftInt :
      CurveIntegrable (fun z ↦ ((logDeriv (θ₁[τ]) dz) z)) (Path.segment z₃ z₀) :=
    hsegmentIntegrable hleft_frontier
  have hleft_symm :
      ∫ᶜ z in Path.segment z₃ z₀, ((logDeriv (θ₁[τ]) dz) z) =
        -∫ᶜ z in Path.segment z₀ z₃, ((logDeriv (θ₁[τ]) dz) z) := by
    -- Reversing the left edge flips the sign of the integral.
    simpa using
      curveIntegral_symm (ω := fun z ↦ ((logDeriv (θ₁[τ]) dz) z)) (γ := Path.segment z₀ z₃)
  have hboundary_four_segments :
      ∫ᶜ z in (periodParallelogramBoundaryPath (L := theta_one_period_pair τ hτ) z₀).toClosedPath.toPath,
          ((logDeriv (θ₁[τ]) dz) z) =
        ∫ᶜ z in Path.segment z₀ z₁, ((logDeriv (θ₁[τ]) dz) z) +
          ∫ᶜ z in Path.segment z₁ z₂, ((logDeriv (θ₁[τ]) dz) z) +
            ∫ᶜ z in Path.segment z₂ z₃, ((logDeriv (θ₁[τ]) dz) z) +
              ∫ᶜ z in Path.segment z₃ z₀, ((logDeriv (θ₁[τ]) dz) z) := by
    -- Route correction: expand the canonical loop first, then rewrite the opposite edges.
    calc
      ∫ᶜ z in (periodParallelogramBoundaryPath (L := theta_one_period_pair τ hτ) z₀).toClosedPath.toPath,
          ((logDeriv (θ₁[τ]) dz) z) =
        ∫ᶜ z in periodParallelogramBoundaryPath (L := theta_one_period_pair τ hτ) z₀,
          ((logDeriv (θ₁[τ]) dz) z) := by
            rw [loopToClosedPathToPathEqCast]
            simp [curveIntegral_cast]
      _ =
          ∫ᶜ z in Path.segment z₀ z₁, ((logDeriv (θ₁[τ]) dz) z) +
            ∫ᶜ z in Path.segment z₁ z₂, ((logDeriv (θ₁[τ]) dz) z) +
              ∫ᶜ z in Path.segment z₂ z₃, ((logDeriv (θ₁[τ]) dz) z) +
                ∫ᶜ z in Path.segment z₃ z₀, ((logDeriv (θ₁[τ]) dz) z) := by
              change
                ∫ᶜ z in
                    (Path.segment z₀ z₁).trans
                      ((Path.segment z₁ z₂).trans
                        ((Path.segment z₂ z₃).trans (Path.segment z₃ z₀))),
                    ((logDeriv (θ₁[τ]) dz) z) =
                  ∫ᶜ z in Path.segment z₀ z₁, ((logDeriv (θ₁[τ]) dz) z) +
                    ∫ᶜ z in Path.segment z₁ z₂, ((logDeriv (θ₁[τ]) dz) z) +
                      ∫ᶜ z in Path.segment z₂ z₃, ((logDeriv (θ₁[τ]) dz) z) +
                        ∫ᶜ z in Path.segment z₃ z₀, ((logDeriv (θ₁[τ]) dz) z)
              rw [curveIntegral_trans hbottomInt
                (CurveIntegrable.trans hrightInt (CurveIntegrable.trans htopInt hleftInt))]
              rw [curveIntegral_trans hrightInt (CurveIntegrable.trans htopInt hleftInt)]
              rw [curveIntegral_trans htopInt hleftInt]
              ring
  have hboundary_integral :
      ∫ᶜ z in (periodParallelogramBoundaryPath (L := theta_one_period_pair τ hτ) z₀).toClosedPath.toPath,
          ((logDeriv (θ₁[τ]) dz) z) =
        (2 * Real.pi * Complex.I : ℂ) := by
    -- Substitute the two concrete edge identities and cancel the opposite edges.
    calc
      ∫ᶜ z in (periodParallelogramBoundaryPath (L := theta_one_period_pair τ hτ) z₀).toClosedPath.toPath,
          ((logDeriv (θ₁[τ]) dz) z) =
        ∫ᶜ z in Path.segment z₀ z₁, ((logDeriv (θ₁[τ]) dz) z) +
          ∫ᶜ z in Path.segment z₁ z₂, ((logDeriv (θ₁[τ]) dz) z) +
            ∫ᶜ z in Path.segment z₂ z₃, ((logDeriv (θ₁[τ]) dz) z) +
              ∫ᶜ z in Path.segment z₃ z₀, ((logDeriv (θ₁[τ]) dz) z) :=
            hboundary_four_segments
      _ =
          ∫ᶜ z in Path.segment z₀ z₁, ((logDeriv (θ₁[τ]) dz) z) +
            ∫ᶜ z in Path.segment z₀ z₃, ((logDeriv (θ₁[τ]) dz) z) +
              (-∫ᶜ z in Path.segment z₀ z₁, ((logDeriv (θ₁[τ]) dz) z) +
                  (2 * Real.pi : ℂ) * Complex.I) +
                ∫ᶜ z in Path.segment z₃ z₀, ((logDeriv (θ₁[τ]) dz) z) := by
              rw [thetaOneRightEdgeIntegral_eq_leftBase τ hτ z₀,
                thetaOneTopEdgeIntegral_eq_neg_bottom_add_twoPiI τ hτ z₀ hboundary]
      _ =
          ∫ᶜ z in Path.segment z₀ z₁, ((logDeriv (θ₁[τ]) dz) z) +
            ∫ᶜ z in Path.segment z₀ z₃, ((logDeriv (θ₁[τ]) dz) z) +
              (-∫ᶜ z in Path.segment z₀ z₁, ((logDeriv (θ₁[τ]) dz) z) +
                  (2 * Real.pi : ℂ) * Complex.I) +
                (-∫ᶜ z in Path.segment z₀ z₃, ((logDeriv (θ₁[τ]) dz) z)) := by
              rw [hleft_symm]
      _ = (2 * Real.pi * Complex.I : ℂ) := by
              ring
  have htwo_pi_real : (2 * Real.pi : ℝ) ≠ 0 := by
    nlinarith [Real.pi_pos]
  have hpiI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero ?_ Complex.I_ne_zero
    exact_mod_cast htwo_pi_real
  -- Normalize the explicit boundary integral by the standard `2π i` denominator.
  calc
    (∫ᶜ z in (periodParallelogramBoundaryPath (L := theta_one_period_pair τ hτ) z₀).toClosedPath.toPath,
        ((logDeriv (θ₁[τ]) dz) z)) /
      (2 * Real.pi * Complex.I : ℂ) =
        (2 * Real.pi * Complex.I : ℂ) / (2 * Real.pi * Complex.I : ℂ) := by
          rw [hboundary_integral]
    _ = 1 := div_self hpiI

/-- Cartan section21 0012_Exercise_3. A boundary-regular period parallelogram admits a singleton
oriented boundary family whose normalized `θ₁` logarithmic-derivative integral is `1`. -/
theorem theta_one_periodParallelogram_boundary_data
    (τ : ℂ) (hτ : 0 < τ.im) (z₀ : ℂ)
    (hboundary :
      ∀ z ∈ frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀), (θ₁[τ]) z ≠ 0) :
    ∃ Γ : Unit → ClosedPath ℂ,
      IsOrientedBoundaryOf ((theta_one_period_pair τ hτ).periodParallelogram z₀) Γ ∧
      (∑ i, ∫ᶜ z in (Γ i).toPath, ((logDeriv (θ₁[τ]) dz) z)) /
        (2 * Real.pi * Complex.I : ℂ) = 1 := by
  let Γ : Unit → ClosedPath ℂ := fun _ ↦
    (periodParallelogramBoundaryPath (L := theta_one_period_pair τ hτ) z₀).toClosedPath
  have hΓ :
      IsOrientedBoundaryOf ((theta_one_period_pair τ hτ).periodParallelogram z₀) Γ := by
    -- The geometric part is now reduced to the canonical singleton boundary family.
    simpa [Γ] using thetaOnePeriodParallelogramSingletonBoundary τ hτ z₀
  -- Route correction: the contour computation is now isolated in the explicit boundary-integral
  -- lemma, so the main theorem only packages the geometric boundary family.
  refine ⟨Γ, hΓ, ?_⟩
  simpa [Γ] using thetaOnePeriodParallelogramBoundaryIntegralDivTwoPiI τ hτ z₀ hboundary

/-- Helper for Exercise 3: the source contour argument on a boundary-regular period parallelogram
should package the total divisor mass of `θ₁` on that cell as `1`. -/
theorem theta_one_zero_mass_in_boundary_regular_periodParallelogram_eq_one
    (τ : ℂ) (hτ : 0 < τ.im) (z₀ : ℂ)
    (hboundary :
      ∀ z ∈ frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀), (θ₁[τ]) z ≠ 0) :
    let P : Set ℂ := (theta_one_period_pair τ hτ).periodParallelogram z₀
    let s : Finset ℂ :=
      (divisor_support_finite_of_isCompact (K := P) (g := θ₁[τ])
        (isCompact_periodParallelogram (L := theta_one_period_pair τ hτ) z₀)).toFinset
    Finset.sum s (fun z ↦ (MeromorphicOn.divisor (θ₁[τ]) P z : ℂ)) = 1 := by
  classical
  let P : Set ℂ := (theta_one_period_pair τ hτ).periodParallelogram z₀
  let s : Finset ℂ :=
    (divisor_support_finite_of_isCompact (K := P) (g := θ₁[τ])
      (isCompact_periodParallelogram (L := theta_one_period_pair τ hτ) z₀)).toFinset
  have hboundary_divisor_zero :
      ∀ z ∈ frontier P, MeromorphicOn.divisor (θ₁[τ]) P z = 0 := by
    -- Boundary nonvanishing removes every frontier point from the divisor support.
    simpa [P] using theta_one_boundary_divisor_zero_of_nonvanishing τ hτ hboundary
  have hmeromorphic : MeromorphicOn (θ₁[τ]) Set.univ := by
    -- Entire holomorphy of `θ₁` upgrades directly to a meromorphic owner on `ℂ`.
    have hanalytic_univ : AnalyticOnNhd ℂ (θ₁[τ]) Set.univ := by
      exact (exercise_3_theta_one_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ
    exact hanalytic_univ.meromorphicOn
  obtain ⟨Γ, hΓ, hΓint⟩ :=
    theta_one_periodParallelogram_boundary_data τ hτ z₀ hboundary
  have hfinsum :
      ∑ᶠ z, (MeromorphicOn.divisor (θ₁[τ]) P z : ℂ) = 1 := by
    have harg :
        (∑ i, ∫ᶜ z in (Γ i).toPath, ((logDeriv (θ₁[τ]) dz) z)) /
            (2 * Real.pi * Complex.I : ℂ) =
          ∑ᶠ z, (MeromorphicOn.divisor (θ₁[τ]) P z : ℂ) := by
      -- Apply the argument principle to the singleton oriented boundary family from the contour
      -- package and simplify the trivial shift by `a = 0`.
      simpa [P] using
        argument_principle_on_oriented_boundary
          (Γ := Γ) (D := Set.univ) (K := P) (f := θ₁[τ]) (a := 0)
          hmeromorphic isOpen_univ (by intro z hz; simp) hΓ
          (by
            intro z hz
            simpa using hboundary_divisor_zero z hz)
    calc
      ∑ᶠ z, (MeromorphicOn.divisor (θ₁[τ]) P z : ℂ) =
          (∑ i, ∫ᶜ z in (Γ i).toPath, ((logDeriv (θ₁[τ]) dz) z)) /
            (2 * Real.pi * Complex.I : ℂ) := harg.symm
      _ = 1 := hΓint
  -- Convert the ambient `finsum` from the argument principle back to the exact finite-support sum
  -- shape used by the later uniqueness argument.
  calc
    Finset.sum s (fun z ↦ (MeromorphicOn.divisor (θ₁[τ]) P z : ℂ)) =
        ∑ᶠ z, (MeromorphicOn.divisor (θ₁[τ]) P z : ℂ) := by
          simpa [P, s] using
            finset_sum_divisor_eq_finsum_support
              (K := P) (g := θ₁[τ])
              (isCompact_periodParallelogram (L := theta_one_period_pair τ hτ) z₀)
    _ = 1 := hfinsum

/-- Helper for Exercise 3: on a boundary-regular slanted fundamental cell, the source `h'/h`
count should force every zero of `θ₁` in that cell to be the origin. -/
theorem theta_one_zero_eq_zero_of_mem_boundary_regular_slanted_cell
    (τ : ℂ) (hτ : 0 < τ.im) {t : ℝ}
    (hzero_mem :
      0 ∈ (theta_one_period_pair τ hτ).periodParallelogram
        (-(t : ℝ) • (1 : ℂ) - (t / 2 : ℝ) • τ))
    (hboundary :
      ∀ z ∈ frontier ((theta_one_period_pair τ hτ).periodParallelogram
        (-(t : ℝ) • (1 : ℂ) - (t / 2 : ℝ) • τ)), (θ₁[τ]) z ≠ 0)
    {w : ℂ}
    (hwP :
      w ∈ (theta_one_period_pair τ hτ).periodParallelogram
        (-(t : ℝ) • (1 : ℂ) - (t / 2 : ℝ) • τ))
    (hwzero : (θ₁[τ]) w = 0) :
    w = 0 := by
  let L : PeriodPair := theta_one_period_pair τ hτ
  let z₀ : ℂ := -(t : ℝ) • (1 : ℂ) - (t / 2 : ℝ) • τ
  let P : Set ℂ := L.periodParallelogram z₀
  let d : ℂ → ℤ := MeromorphicOn.divisor (θ₁[τ]) P
  have hcompact : IsCompact P := by
    simpa [L, P, z₀] using isCompact_periodParallelogram (L := L) z₀
  have hzero_div : 0 < d 0 := by
    -- The origin is a known zero of `θ₁`, so its divisor contribution is positive.
    simpa [d, P] using
      (theta_one_divisor_pos_iff_eq_zero_on_set τ hτ (P := P)
        (by simpa [L, P, z₀] using hzero_mem)).2 (jacobi_theta_one_zero_at_zero τ)
  have hw_div : 0 < d w := by
    -- The candidate zero `w` contributes positive divisor mass inside the same cell.
    simpa [d, P] using
      (theta_one_divisor_pos_iff_eq_zero_on_set τ hτ (P := P)
        (by simpa [L, P, z₀] using hwP)).2 hwzero
  have hsupport_sum :
      let s : Finset ℂ := (divisor_support_finite_of_isCompact (K := P) (g := θ₁[τ]) hcompact).toFinset
      Finset.sum s (fun z ↦ (d z : ℂ)) = 1 := by
    -- Apply the packaged source-faithful contour count to the chosen slanted cell.
    simpa [L, z₀, P, d] using
      theta_one_zero_mass_in_boundary_regular_periodParallelogram_eq_one τ hτ z₀
        (by simpa [L, z₀, P] using hboundary)
  by_contra hw_ne
  let s : Finset ℂ := (divisor_support_finite_of_isCompact (K := P) (g := θ₁[τ]) hcompact).toFinset
  have hsum_int : s.sum d = 1 := by
    have hsum_cast : ((s.sum d : ℤ) : ℂ) = 1 := by
      simpa [s, d] using hsupport_sum
    exact_mod_cast hsum_cast
  have hzero_mem_support : 0 ∈ s := by
    -- Positive divisor mass puts the origin into the finite support finset.
    have hzero_ne : d 0 ≠ 0 := (ne_of_gt hzero_div)
    exact by
      simpa [s, d, Function.mem_support] using hzero_ne
  have hw_mem_support : w ∈ s := by
    have hw_ne_div : d w ≠ 0 := (ne_of_gt hw_div)
    exact by
      simpa [s, d, Function.mem_support] using hw_ne_div
  have hnonneg : ∀ z ∈ s, 0 ≤ d z := by
    intro z hz
    have hzsupport : z ∈ (MeromorphicOn.divisor (θ₁[τ]) P).support := by
      simpa [s] using hz
    have hzP : z ∈ P := (MeromorphicOn.divisor (θ₁[τ]) P).supportWithinDomain hzsupport
    by_cases hzzero : (θ₁[τ]) z = 0
    · exact le_of_lt ((theta_one_divisor_pos_iff_eq_zero_on_set τ hτ (P := P) hzP).2 hzzero)
    · have hzdiv_zero : d z = 0 := by
        -- Nonvanishing at an interior point forces divisor value `0`.
        have hanalytic_univ : AnalyticOnNhd ℂ (θ₁[τ]) Set.univ := by
          exact (exercise_3_theta_one_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ
        have hanalyticP : AnalyticOnNhd ℂ (θ₁[τ]) P := hanalytic_univ.mono (by
          intro u hu
          simp)
        simpa [d] using divisor_eq_zero_of_analyticOnNhd_nonvanishing hanalyticP hzP hzzero
      simpa [hzdiv_zero]
  have hzero_ge_one : 1 ≤ d 0 := by omega
  have hw_ge_one : 1 ≤ d w := by omega
  have hw_mem_erase : w ∈ s.erase 0 := by simp [hw_mem_support, hw_ne]
  have hw_le_erase : d w ≤ (s.erase 0).sum d := by
    exact Finset.single_le_sum
      (fun z hz ↦ hnonneg z (Finset.mem_of_mem_erase hz)) hw_mem_erase
  have hsplit : d 0 + (s.erase 0).sum d = s.sum d := by
    simpa [add_comm] using s.sum_erase_add d hzero_mem_support
  have hsum_lower : d 0 + d w ≤ s.sum d := by
    rw [← hsplit]
    linarith
  have hsum_two : 2 ≤ s.sum d := by
    linarith
  omega

/-- Helper for Exercise 3: the remaining source-faithful contour argument should produce a
translated period parallelogram for periods `1` and `τ` that contains `0` and has no other zero of
`θ₁` inside it. -/
theorem exists_theta_one_unique_zero_periodParallelogram
    (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ z₀ : ℂ,
      0 ∈ (theta_one_period_pair τ hτ).periodParallelogram z₀ ∧
      ∀ w ∈ (theta_one_period_pair τ hτ).periodParallelogram z₀,
        (θ₁[τ]) w = 0 → w = 0 := by
  obtain ⟨t, ht0, ht1, hcell, hboundary, _hlattice⟩ :=
    exists_theta_one_boundary_regular_slanted_periodParallelogram τ hτ
  let z₀ : ℂ := -(t : ℝ) • (1 : ℂ) - (t / 2 : ℝ) • τ
  refine ⟨z₀, by simpa [z₀] using hcell, ?_⟩
  intro w hwP hwzero
  -- Route correction: the main theorem now factors through the slanted boundary-regular cell
  -- chooser, leaving only the source contour-count uniqueness step unresolved.
  exact theta_one_zero_eq_zero_of_mem_boundary_regular_slanted_cell τ hτ
    (t := t) (by simpa [z₀] using hcell) (by simpa [z₀] using hboundary)
    (by simpa [z₀] using hwP) hwzero

/-- Exercise 3 (12) for Cartan section21 0012_Exercise_3: for `Im τ > 0`, the zeros of `θ₁` are
exactly the lattice points `m + nτ` with `m, n ∈ ℤ`. -/
theorem exercise_3_theta_one_zero_iff (τ u : ℂ) (hτ : 0 < τ.im) :
    (θ₁[τ]) u = 0 ↔ ∃ m n : ℤ, u = m + n * τ :=
by
  constructor
  · intro hzero
    let L : PeriodPair := theta_one_period_pair τ hτ
    obtain ⟨z₀, hz₀, hunique⟩ := exists_theta_one_unique_zero_periodParallelogram τ hτ
    obtain ⟨w, hwP, hwzero, hwsub⟩ :=
      theta_one_zero_exists_periodParallelogram_representative τ u z₀ hτ hzero
    have hw_eq_zero : w = 0 := hunique w hwP hwzero
    have hu_mem : u ∈ L.lattice := by
      have hneg : -u ∈ L.lattice := by
        simpa [hw_eq_zero] using hwsub
      simpa using L.lattice.neg_mem hneg
    rcases L.mem_lattice.mp hu_mem with ⟨m, n, hmn_raw⟩
    have hmn : ((m : ℤ) : ℂ) + ((n : ℤ) : ℂ) * τ = u := by
      simpa [L, theta_one_period_pair, mul_comm, add_assoc, add_left_comm, add_comm] using hmn_raw
    refine ⟨m, n, ?_⟩
    -- The representative reduction leaves exactly the lattice relation `u = m + nτ`.
    simpa [mul_comm, add_assoc, add_left_comm, add_comm] using hmn.symm
  · rintro ⟨m, n, rfl⟩
    -- The reverse implication is already controlled by the two translation formulas.
    exact theta_one_zero_at_lattice_point τ m n

/-- Exercise 3 (13): for `Im τ > 0`, the zeros of `θ₀` are exactly the shifted lattice points
`m + (n + 1 / 2)τ` with `m, n ∈ ℤ`. -/
theorem exercise_3_theta_zero_zero_iff (τ u : ℂ) (hτ : 0 < τ.im) :
    (θ₀[τ]) u = 0 ↔
      ∃ m n : ℤ, u = m + ((n : ℂ) + (1 / 2 : ℂ)) * τ :=
by
  constructor
  · intro hzero
    have hshift_eq :
        (θ₀[τ]) u =
          Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (u - τ / 2 + τ / 4)) *
            (θ₁[τ]) (u - τ / 2) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        exercise_3_theta_zero_add_half_tau τ (u - τ / 2)
    have hshift :
        Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (u - τ / 2 + τ / 4)) *
            (θ₁[τ]) (u - τ / 2) = 0 := by
      rw [← hshift_eq]
      exact hzero
    have hscalar_ne :
        Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (u - τ / 2 + τ / 4)) ≠ 0 := by
      exact mul_ne_zero Complex.I_ne_zero (Complex.exp_ne_zero _)
    have htheta :
        (θ₁[τ]) (u - τ / 2) = 0 :=
      (mul_eq_zero.mp hshift).resolve_left hscalar_ne
    rcases (exercise_3_theta_one_zero_iff τ (u - τ / 2) hτ).mp htheta with ⟨m, n, hu⟩
    refine ⟨m, n, ?_⟩
    calc
      u = (u - τ / 2) + τ / 2 := by ring
      _ = m + n * τ + τ / 2 := by rw [hu]
      _ = m + ((n : ℂ) + (1 / 2 : ℂ)) * τ := by ring
  · rintro ⟨m, n, rfl⟩
    have htheta :
        (θ₁[τ]) (m + n * τ) = 0 :=
      (exercise_3_theta_one_zero_iff τ (m + n * τ) hτ).mpr ⟨m, n, rfl⟩
    -- Evaluate the half-`τ` shift formula at the lattice zero of `θ₁`.
    have hshift :
        (θ₀[τ]) (m + ((n : ℂ) + (1 / 2 : ℂ)) * τ) =
          Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (m + n * τ + τ / 4)) *
            (θ₁[τ]) (m + n * τ) := by
      calc
        (θ₀[τ]) (m + ((n : ℂ) + (1 / 2 : ℂ)) * τ) = (θ₀[τ]) (m + n * τ + τ / 2) := by
          ring
        _ =
            Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (m + n * τ + τ / 4)) *
              (θ₁[τ]) (m + n * τ) := by
                simpa [add_assoc, add_left_comm, add_comm] using
                  exercise_3_theta_zero_add_half_tau τ (m + n * τ)
    rw [hshift, htheta]
    simp
