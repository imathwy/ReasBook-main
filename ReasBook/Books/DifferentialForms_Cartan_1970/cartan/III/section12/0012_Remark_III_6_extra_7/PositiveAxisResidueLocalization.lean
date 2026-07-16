import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0003_Lemma_II_1_extra_3»
import DifferentialForms_Cartan_1970.cartan.III.section11.frozen_0003_Theorem_III_5_extra_2
import DifferentialForms_Cartan_1970.cartan.III.section11.«0003_Theorem_III_5_extra_2».BoundaryCircleIntegrals
import DifferentialForms_Cartan_1970.cartan.III.section11.«0003_Theorem_III_5_extra_2».FiniteExcisionBoundary
import DifferentialForms_Cartan_1970.cartan.III.section11.«0003_Theorem_III_5_extra_2».LocalResidueExcision
import DifferentialForms_Cartan_1970.cartan.III.section12.«0012_Remark_III_6_extra_7».ShiftedLogResidueData
import DifferentialForms_Cartan_1970.cartan.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisWedgeAnnulus
import DifferentialForms_Cartan_1970.cartan.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisKeyholeSimplicity
import DifferentialForms_Cartan_1970.cartan.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisKeyholeBoundaryStraightening
import DifferentialForms_Cartan_1970.cartan.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisKeyholeCircleBoundaryStraightening

open Filter MeasureTheory Bornology
open scoped unitInterval

noncomputable section

universe u

/-- Helper for Remark III.6-extra-7: the `III.5` oriented-boundary residue theorem specialized to
the stable support API, so the positive-axis keyhole argument can avoid importing the full
`III.5` top-level file. -/
private theorem positiveAxisOrientedBoundary_sum_curveIntegral_eq_two_pi_I_mul_sum_residue
    {ι : Type u} [Fintype ι] {K D : Set ℂ} (Γ : ι → ClosedPath ℂ) {f : ℂ → ℂ}
    (s : Finset ℂ) (residue : ℂ → ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD : IsOpen D)
    (hhol : DifferentiableOn ℂ f (D \ (↑s : Set ℂ)))
    (hres : ∀ z ∈ s, IsolatedLocalResidueCircle K D s f z (residue z)) :
    ∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z =
      (2 * Real.pi * Complex.I : ℂ) * Finset.sum s residue := by
  classical
  let _ := hKD
  choose ρ₀ hρ₀pos hρ₀K hρ₀D hρ₀avoid hρ₀diff hρ₀sep hρ₀circle using
    fun z : s ↦
      exists_half_radius_isolated_local_residue_circle hD hhol z.2 (hres z.1 z.2)
  let ρ : ℂ → ℝ := fun z ↦ if hz : z ∈ s then ρ₀ ⟨z, hz⟩ else 0
  have hρpos : ∀ z ∈ s, 0 < ρ z := by
    intro z hz
    simp [ρ, hz, hρ₀pos]
  have hρK : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ interior K := by
    intro z hz
    simpa [ρ, hz] using hρ₀K ⟨z, hz⟩
  have hρD : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ D := by
    intro z hz
    simpa [ρ, hz] using hρ₀D ⟨z, hz⟩
  have hρsep :
      ∀ z ∈ s, ∀ w ∈ s, w ≠ z -> ρ z + ρ w < dist z w := by
    intro z hz w hw hwz
    have hzlt : 2 * ρ z < dist z w := by
      simpa [ρ, hz] using hρ₀sep ⟨z, hz⟩ w hw hwz
    have hwlt : 2 * ρ w < dist z w := by
      have hwlt' : 2 * ρ₀ ⟨w, hw⟩ < dist w z :=
        hρ₀sep ⟨w, hw⟩ z hz hwz.symm
      simpa [ρ, hw, dist_comm] using hwlt'
    linarith
  have hpair :
      ∀ z ∈ s, ∀ w ∈ s, z ≠ w →
        Disjoint (Metric.closedBall z (ρ z)) (Metric.closedBall w (ρ w)) :=
    pairwise_disjoint_closedBall_of_radius_separation
      (fun z hz ↦ (hρpos z hz).le) hρsep
  have hboundary :
      ∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z =
        Finset.sum s (fun z ↦ ∮ w in C(z, ρ z), f w) :=
    orientedBoundary_sum_curveIntegral_eq_sum_small_circle_integrals
      Γ s ρ hΓ hKD hD hρpos hρK hρD hpair hhol
  calc
    ∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z = Finset.sum s (fun z ↦ ∮ w in C(z, ρ z), f w) :=
      hboundary
    _ = Finset.sum s (fun z ↦ (2 * Real.pi * Complex.I : ℂ) * residue z) := by
      refine Finset.sum_congr rfl ?_
      intro z hz
      simpa [ρ, hz] using hρ₀circle ⟨z, hz⟩
    _ = (2 * Real.pi * Complex.I : ℂ) * Finset.sum s residue := by
      simpa using (Finset.mul_sum s residue (2 * Real.pi * Complex.I : ℂ)).symm

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: the slit-annulus frontier for the
positive-axis keyhole is exactly the range of the repaired contour. -/
theorem positiveAxisWedgeAnnulus_frontier_eq_range
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    frontier (positiveAxisWedgeAnnulus R ε) = Set.range (positiveAxisKeyhole R ε) := by
  -- Split the slit annulus into the closed annulus minus the open wedge before comparing the four
  -- geometric boundary pieces with the four contour branches.
  rw [show positiveAxisWedgeAnnulus R ε =
      ({z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} \ positiveAxisWedge R ε) by
        rfl]
  rw [frontier_diff_open_of_isClosed
      (A := {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R}) (W := positiveAxisWedge R ε)
      (by
        simpa [Set.setOf_and] using
          (isClosed_le continuous_const continuous_norm).inter
            (isClosed_le continuous_norm continuous_const))
      (isOpen_positiveAxisWedge R ε)]
  -- Rewrite the surviving circle part and the wedge-frontier part into the exact geometric pieces
  -- already used by the contour range decomposition.
  rw [positiveAxisClosedAnnulus_frontier_eq R ε hε hεR,
    positiveAxisWedgeAnnulus_surviving_circles_eq_majorArc_images R ε hε hεR,
    positiveAxisWedgeAnnulus_annulusInter_frontier_wedge_eq_lip_union R ε hε hεR,
    positiveAxisKeyhole_range_eq_geometric_piece_union R ε]
  simp [Set.union_assoc, Set.union_left_comm, Set.union_comm]

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: the repaired positive-axis keyhole is
the oriented boundary of the slit annulus it parametrizes. -/
theorem positiveAxisKeyhole_isOrientedBoundaryOf
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    IsOrientedBoundaryOf
      (positiveAxisWedgeAnnulus R ε)
      (fun _ : Unit ↦ (positiveAxisKeyhole R ε).toClosedPath) := by
  classical
  let K : Set ℂ := positiveAxisWedgeAnnulus R ε
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (positiveAxisKeyhole R ε).toClosedPath
  change IsOrientedBoundaryOf K Γ
  refine
    { isCompact := ?_
      piecewiseDifferentiable := ?_
      simple_loops := ?_
      pairwiseDisjoint_ranges := ?_
      iUnion_range_eq_frontier := ?_
      exists_boundary_chart_at_regular_point := ?_ }
  · -- Compactness is already packaged at the slit-annulus level.
    simpa [K] using isCompact_positiveAxisWedgeAnnulus R ε
  · rintro ⟨⟩
    -- The singleton boundary family inherits the explicit keyhole regularity.
    simpa [Γ, Path.toClosedPath] using positiveAxisKeyhole_isPiecewiseDifferentiable R ε
  · rintro ⟨⟩ s t hst
    -- Simplicity has already been reduced to the four branch injectivity statements.
    simpa [Γ, Path.toClosedPath] using positiveAxisKeyhole_simple_eq_or_endpoints hε hεR hst
  · intro i j hij
    -- A singleton family is pairwise disjoint for the trivial reason.
    exact (hij rfl).elim
  · -- Collapse the singleton family back to the explicit contour range before comparing it with
    -- the slit-annulus frontier.
    calc
      (⋃ i : Unit, Set.range (Γ i).toPath) = Set.range (positiveAxisKeyhole R ε) := by
          simpa [Γ] using positiveAxisKeyhole_singleton_iUnion_range R ε
      _ = frontier K := by
          simpa [K] using (positiveAxisWedgeAnnulus_frontier_eq_range R ε hε hεR).symm
  · rintro ⟨⟩ t₀ ht₀ hdiff hderiv
    let _ := hderiv
    -- Every regular interior parameter lies on exactly one source branch, so one of the two
    -- branch-specific boundary-straightening packages applies immediately.
    let t : I := ⟨t₀, ⟨ht₀.1.le, ht₀.2.le⟩⟩
    have hdiff' :
        DifferentiableWithinAt ℝ
          (positiveAxisKeyhole R ε).toClosedPath.realCurve
          (Set.Icc 0 1) t₀ := by
      simpa [Γ] using hdiff
    rcases positiveAxisKeyhole_regular_parameter_mem_open_branch
        (t := t) hε hεR ht₀ (by simpa [t] using hdiff') with
      htupper | htinner | htlower | htouter
    · simpa [K, Γ] using
        positiveAxisKeyhole_ray_branch_exists_boundary_chart
          R ε hε hεR ht₀ (Or.inl htupper)
    · simpa [K, Γ] using
        positiveAxisKeyhole_circle_branch_exists_boundary_chart
          R ε hε hεR ht₀ (Or.inl htinner)
    · simpa [K, Γ] using
        positiveAxisKeyhole_ray_branch_exists_boundary_chart
          R ε hε hεR ht₀ (Or.inr htlower)
    · simpa [K, Γ] using
        positiveAxisKeyhole_circle_branch_exists_boundary_chart
          R ε hε hεR ht₀ (Or.inr htouter)

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: a fixed closed residue circle inside
`shiftedLogDomain` eventually lies in the interior of the large positive-axis slit annuli
`positiveAxisWedgeAnnulus R (1 / R)`. -/
lemma eventually_closedBall_subset_interior_positiveAxisWedgeAnnulus
    (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hsubset : Metric.closedBall c ρ ⊆ shiftedLogDomain) :
    ∀ᶠ R : ℝ in atTop,
      let ε := 1 / R
      1 < R ∧ Metric.closedBall c ρ ⊆ interior (positiveAxisWedgeAnnulus R ε) := by
  let K : Set ℂ := Metric.closedBall c ρ
  have hKcompact : IsCompact K := by
    simpa [K] using isCompact_closedBall c ρ
  obtain ⟨δ, hδpos, hδsub⟩ :=
    hKcompact.exists_thickening_subset_open isOpen_shiftedLogDomain hsubset
  let B : ℝ := ‖c‖ + ρ + 1
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  let A : ℝ := max (max 1 B) (max (1 / δ) (2 / δ))
  filter_upwards [Filter.eventually_gt_atTop A] with R hR
  let ε : ℝ := 1 / R
  have hRgtLeft : max 1 B < R := lt_of_le_of_lt (le_max_left _ _) hR
  have hRgtRight : max (1 / δ) (2 / δ) < R := lt_of_le_of_lt (le_max_right _ _) hR
  have hRgt1 : 1 < R := lt_of_le_of_lt (le_max_left _ _) hRgtLeft
  have hRgtB : B < R := lt_of_le_of_lt (le_max_right _ _) hRgtLeft
  have hRgtInv : 1 / δ < R := lt_of_le_of_lt (le_max_left _ _) hRgtRight
  have hRgtHalfInv : 2 / δ < R := lt_of_le_of_lt (le_max_right _ _) hRgtRight
  have hRpos : 0 < R := lt_trans zero_lt_one hRgt1
  have hInv : 1 / R < δ := by
    have hmul : 1 < R * δ := by
      exact (div_lt_iff₀ hδpos).1 hRgtInv
    exact (div_lt_iff₀ hRpos).2 (by simpa [mul_comm] using hmul)
  have hInvHalf : 1 / R < δ / 2 := by
    have hmul : 2 < R * δ := by
      exact (div_lt_iff₀ hδpos).1 hRgtHalfInv
    have hmul' : 1 < R * (δ / 2) := by
      nlinarith
    exact (div_lt_iff₀ hRpos).2 (by simpa [mul_comm] using hmul')
  let U : Set ℂ :=
    {w : ℂ | 1 / R < ‖w‖ ∧ ‖w‖ < R} ∩
      ({w : ℂ | w.re < 0} ∪ {w : ℂ | δ / 2 < |w.im|})
  have hGapOpen : IsOpen ({w : ℂ | w.re < 0} ∪ {w : ℂ | δ / 2 < |w.im|}) := by
    refine (isOpen_lt Complex.continuous_re continuous_const).union ?_
    simpa using isOpen_lt continuous_const (continuous_abs.comp Complex.continuous_im)
  have hUopen : IsOpen U := by
    -- The eventual owner is described by strict annulus inequalities together with a strict
    -- distance-from-cut condition, so it is visibly open.
    simpa [U, Set.setOf_and, Set.inter_assoc] using
      (isOpen_lt continuous_const continuous_norm).inter
        ((isOpen_lt continuous_norm continuous_const).inter hGapOpen)
  have hUsubset : U ⊆ positiveAxisWedgeAnnulus R ε := by
    intro w hw
    rcases hw with ⟨⟨hwNormLower, hwNormUpper⟩, hwGap⟩
    refine ⟨⟨le_of_lt hwNormLower, le_of_lt hwNormUpper⟩, ?_⟩
    intro hwWedge
    rcases hwGap with hwNeg | hwIm
    · exact (not_lt_of_ge hwNeg.le hwWedge.1).elim
    · have hwReLt : w.re < R := by
        exact lt_of_le_of_lt
          (le_trans (le_abs_self _) (Complex.abs_re_le_norm w)) hwNormUpper
      have hwSlope :
          ((1 / R) / R) * w.re < 1 / R := by
        field_simp [hRpos.ne']
        nlinarith
      have hwImLt : |w.im| < 1 / R := lt_trans hwWedge.2 hwSlope
      exact (not_lt_of_ge hwIm.le) (lt_trans hwImLt hInvHalf)
  have hKU : Metric.closedBall c ρ ⊆ U := by
    intro w hw
    have hwDist : dist w c ≤ ρ := by
      simpa [Metric.mem_closedBall] using hw
    have hwNormUpper : ‖w‖ ≤ ‖c‖ + ρ := by
      calc
        ‖w‖ = ‖(w - c) + c‖ := by ring_nf
        _ ≤ ‖w - c‖ + ‖c‖ := norm_add_le _ _
        _ = dist w c + ‖c‖ := by rw [dist_eq_norm]
        _ ≤ ρ + ‖c‖ := by linarith
        _ = ‖c‖ + ρ := by ring
    have hwNormLarge : δ ≤ ‖w‖ := by
      by_contra hlt
      have hzeroThick : (0 : ℂ) ∈ Metric.thickening δ K := by
        rw [Metric.mem_thickening_iff]
        refine ⟨w, ?_, ?_⟩
        · simpa [K] using hw
        · simpa [dist_eq_norm] using hlt
      have hzeroMem : (0 : ℂ) ∈ shiftedLogDomain := hδsub hzeroThick
      have hzeroNotMem : (0 : ℂ) ∉ shiftedLogDomain := by
        simpa [shiftedLogDomain, Complex.mem_slitPlane_iff]
      exact hzeroNotMem hzeroMem
    have hwGap :
        w.re < 0 ∨ δ ≤ |w.im| := by
      by_cases hwNeg : w.re < 0
      · exact Or.inl hwNeg
      · have hwReNonneg : 0 ≤ w.re := le_of_not_gt hwNeg
        have hwRealNotMem : ((w.re : ℂ)) ∉ shiftedLogDomain := by
          intro hwRealMem
          change -((w.re : ℂ)) ∈ Complex.slitPlane at hwRealMem
          rw [Complex.mem_slitPlane_iff] at hwRealMem
          rcases hwRealMem with hpos | him
          · have hpos' : 0 < -w.re := by simpa using hpos
            linarith
          · simp at him
        by_cases hIm : δ ≤ |w.im|
        · exact Or.inr hIm
        exfalso
        have hwRealThick : ((w.re : ℂ)) ∈ Metric.thickening δ K := by
          rw [Metric.mem_thickening_iff]
          refine ⟨w, ?_, ?_⟩
          · simpa [K] using hw
          · have hdist :
              dist ((w.re : ℂ)) w = |w.im| := by
              rw [dist_eq_norm]
              calc
                ‖((w.re : ℂ) - w)‖ = ‖((-w.im : ℂ) * Complex.I)‖ := by
                    apply congrArg norm
                    apply Complex.ext <;> simp
                _ = |w.im| := by
                    simp
            have hImLt : |w.im| < δ := lt_of_not_ge hIm
            exact lt_of_eq_of_lt hdist hImLt
        exact hwRealNotMem (hδsub hwRealThick)
    have hRgtNorm : ‖c‖ + ρ < R := by
      dsimp [B] at hRgtB
      linarith
    refine ⟨⟨lt_of_lt_of_le hInv hwNormLarge, lt_of_le_of_lt hwNormUpper hRgtNorm⟩, ?_⟩
    rcases hwGap with hwNeg | hwIm
    · exact Or.inl hwNeg
    · exact Or.inr (lt_of_lt_of_le (by nlinarith [hδpos]) hwIm)
  -- The open neighborhood `U` contains the whole fixed closed ball and already sits in the
  -- desired slit annulus, so every point of the ball lies in the eventual interior.
  refine ⟨hRgt1, ?_⟩
  intro w hw
  exact ((IsOpen.subset_interior_iff hUopen).2 hUsubset) (hKU hw)

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: once the source-side isolated residue
circles have been transferred to the shifted normal form, all sufficiently large positive-axis
keyholes carry the oriented-boundary and interior residue data needed for the residue theorem. -/
lemma eventually_large_keyhole_parameters_with_isolated_residue_data_generic
    {G : ℂ → ℂ} {s : Finset ℂ} (residue : ℂ → ℂ)
    (hresidueG :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          shiftedLogDomain
          shiftedLogDomain
          s
          G
          z
          (residue z)) :
    ∀ᶠ R : ℝ in atTop,
      let ε := 1 / R
      1 < R ∧
        IsOrientedBoundaryOf
          (positiveAxisWedgeAnnulus R ε)
          (fun _ : Unit ↦ (positiveAxisKeyhole R ε).toClosedPath) ∧
        positiveAxisWedgeAnnulus R ε ⊆ shiftedLogDomain ∧
        ∀ z ∈ s,
          IsolatedLocalResidueCircle
            (positiveAxisWedgeAnnulus R ε)
            shiftedLogDomain
            s
            G
            z
            (residue z) := by
  classical
  let radius : ℂ → ℝ := fun z ↦
    if hz : z ∈ s then Classical.choose (hresidueG z hz) else 1
  have hradius_pos : ∀ z ∈ s, 0 < radius z := by
    intro z hz
    dsimp [radius]
    rw [dif_pos hz]
    exact (Classical.choose_spec (hresidueG z hz)).1
  have hradius_D : ∀ z ∈ s, Metric.closedBall z (radius z) ⊆ shiftedLogDomain := by
    intro z hz
    dsimp [radius]
    rw [dif_pos hz]
    exact (Classical.choose_spec (hresidueG z hz)).2.2.1
  have hradius_sep :
      ∀ z ∈ s, ∀ w ∈ s, w ≠ z → w ∉ Metric.closedBall z (radius z) := by
    intro z hz w hw hwz
    dsimp [radius]
    rw [dif_pos hz]
    exact (Classical.choose_spec (hresidueG z hz)).2.2.2.1 w hw hwz
  have hradius_diff :
      ∀ z ∈ s,
        DifferentiableOn ℂ G (Metric.ball z (radius z) \ ({z} : Set ℂ)) := by
    intro z hz
    dsimp [radius]
    rw [dif_pos hz]
    exact (Classical.choose_spec (hresidueG z hz)).2.2.2.2.1
  have hradius_circle :
      ∀ z ∈ s,
        (∮ w in C(z, radius z), G w) = (2 * Real.pi * Complex.I : ℂ) * residue z := by
    intro z hz
    dsimp [radius]
    rw [dif_pos hz]
    exact (Classical.choose_spec (hresidueG z hz)).2.2.2.2.2
  have hEventuallyInterior :
      ∀ᶠ R : ℝ in atTop,
        ∀ z ∈ s,
          Metric.closedBall z (radius z) ⊆ interior (positiveAxisWedgeAnnulus R (1 / R)) := by
    rw [Filter.eventually_all_finset]
    intro z hz
    filter_upwards
      [eventually_closedBall_subset_interior_positiveAxisWedgeAnnulus
        z (hρ := hradius_pos z hz) (hsubset := hradius_D z hz)]
      with R hR
    exact hR.2
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), hEventuallyInterior] with R hRgt1 hInterior
  let ε : ℝ := 1 / R
  have hRpos : 0 < R := lt_trans zero_lt_one hRgt1
  have hε : 0 < ε := by
    dsimp [ε]
    exact one_div_pos.mpr hRpos
  have hεR : ε < R := by
    dsimp [ε]
    exact (div_lt_iff₀ hRpos).2 (by nlinarith [hRgt1])
  refine ⟨hRgt1, positiveAxisKeyhole_isOrientedBoundaryOf hε hεR,
    positiveAxisWedgeAnnulus_subset_shiftedLogDomain hε hεR, ?_⟩
  intro z hz
  -- Keep the original residue-circle radius and all punctured-holomorphic data; only the owner
  -- inclusion changes after the eventual compact-exhaustion step.
  refine ⟨radius z, hradius_pos z hz, hInterior z hz, hradius_D z hz,
    hradius_sep z hz, hradius_diff z hz, hradius_circle z hz⟩

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: the shifted-log normal form is one
instance of the generic eventual keyhole residue package above. -/
lemma eventually_large_keyhole_parameters_with_isolated_residue_data
    (P Q : Polynomial ℂ) {s : Finset ℂ} (residue : ℂ → ℂ)
    (hresidueG :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          shiftedLogDomain
          shiftedLogDomain
          s
          (shiftedLogRationalNormalForm P Q)
          z
          (residue z)) :
    ∀ᶠ R : ℝ in atTop,
      let ε := 1 / R
      1 < R ∧
        IsOrientedBoundaryOf
          (positiveAxisWedgeAnnulus R ε)
          (fun _ : Unit ↦ (positiveAxisKeyhole R ε).toClosedPath) ∧
        positiveAxisWedgeAnnulus R ε ⊆ shiftedLogDomain ∧
        ∀ z ∈ s,
          IsolatedLocalResidueCircle
            (positiveAxisWedgeAnnulus R ε)
            shiftedLogDomain
            s
            (shiftedLogRationalNormalForm P Q)
            z
            (residue z) := by
  -- The geometry is integrand-independent; only the residue-circle payload specializes here.
  simpa using
    eventually_large_keyhole_parameters_with_isolated_residue_data_generic
      (G := shiftedLogRationalNormalForm P Q) residue hresidueG

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: once the isolated residue circles and
holomorphy away from the pole finset are available, sufficiently large positive-axis keyholes have
the expected constant contour integral `2π i * ∑ residue`. -/
lemma eventually_positiveAxisKeyhole_curveIntegral_eq_two_pi_I_mul_sum_residue
    {G : ℂ → ℂ} {s : Finset ℂ} (residue : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ G (shiftedLogDomain \ (↑s : Set ℂ)))
    (hresidueG :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          shiftedLogDomain
          shiftedLogDomain
          s
          G
          z
          (residue z)) :
    ∀ᶠ R : ℝ in atTop,
      ∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath,
        ((G dz) z) =
          (2 * Real.pi * Complex.I : ℂ) * Finset.sum s residue := by
  filter_upwards
    [eventually_large_keyhole_parameters_with_isolated_residue_data_generic
      (G := G) residue hresidueG]
    with R hR
  dsimp only at hR
  rcases hR with ⟨hRgt1, hΓ, hKD, hresidueK⟩
  have hboundary :
      ∑ i : Unit,
        ∫ᶜ z in ((fun _ : Unit ↦ (positiveAxisKeyhole R (1 / R)).toClosedPath) i).toPath,
          ((G dz) z) =
        (2 * Real.pi * Complex.I : ℂ) * Finset.sum s residue := by
    -- The generic oriented-boundary residue theorem now applies directly to the large keyhole.
    exact positiveAxisOrientedBoundary_sum_curveIntegral_eq_two_pi_I_mul_sum_residue
      (Γ := fun _ : Unit ↦ (positiveAxisKeyhole R (1 / R)).toClosedPath)
      (K := positiveAxisWedgeAnnulus R (1 / R)) (D := shiftedLogDomain)
      (f := G) (s := s) (residue := residue)
      hΓ hKD isOpen_shiftedLogDomain hhol hresidueK
  -- Collapse the singleton boundary family back to the explicit keyhole contour integral.
  simpa using hboundary
