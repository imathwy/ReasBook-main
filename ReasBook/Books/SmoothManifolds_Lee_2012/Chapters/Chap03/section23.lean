import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_3_23 (from Chap03/Sec03_17) -/
open scoped Manifold ContDiff

noncomputable section

universe uM

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}

/-- Helper for Proposition 3.23: the affine model-space curve `t ↦ x₀ + t • w` has within-velocity
`w` at `0` on any parameter set with unique differential there. -/
lemma affine_model_curve_velocity_within (x₀ w : E) {J : Set ℝ}
    (hJ : UniqueMDiffWithinAt 𝓘(ℝ) J 0) :
    curve_velocityWithin (𝓘(ℝ, E)) (fun t : ℝ ↦ x₀ + t • w) J 0 = w := by
  -- Compute the derivative of the affine model curve directly in the vector-space model.
  have hη : HasDerivWithinAt (fun t : ℝ ↦ x₀ + t • w) w J 0 := by
    simpa [one_smul] using
      (((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x₀).hasDerivWithinAt
  -- Then rewrite the manifold velocity in the vector-space model to the ordinary derivative.
  simpa [curve_velocityWithin, mfderivWithin_eq_fderivWithin, ← fderivWithin_derivWithin] using
    hη.derivWithin hJ.uniqueDiffWithinAt

/-- Helper for Proposition 3.23: if a tangent vector in the Euclidean model is viewed as an
ordinary vector in the model space, the affine model curve with that direction has the same
within-velocity at `0`. -/
lemma affine_model_curve_velocity_within_tangent {x₀ : E}
    (w : TangentSpace (𝓘(ℝ, E)) x₀) {J : Set ℝ}
    (hJ : UniqueMDiffWithinAt 𝓘(ℝ) J 0) :
    letI W : E := w
    curve_velocityWithin (𝓘(ℝ, E)) (fun t : ℝ ↦ x₀ + t • W) J 0 = w := by
  -- The Euclidean-model tangent space is definitionally the model vector space itself.
  simpa using affine_model_curve_velocity_within x₀ (w : E) hJ

/-- Helper for Proposition 3.23: the right half-interval `[0, ε)` has unique manifold
differentential at `0`. -/
lemma uniqueMDiffWithinAt_Ico_zero {ε : ℝ} (hε : 0 < ε) :
    UniqueMDiffWithinAt 𝓘(ℝ) (Set.Ico 0 ε) 0 := by
  -- Near `0`, the set `Ico 0 ε` agrees with the one-sided model domain `Ici 0`.
  have hIci : UniqueMDiffWithinAt 𝓘(ℝ) (Set.Ici (0 : ℝ)) (0 : ℝ) :=
    (uniqueDiffWithinAt_Ici (0 : ℝ)).uniqueMDiffWithinAt
  -- Intersect `Ici 0` with the ordinary neighborhood `(-∞, ε)`.
  simpa [Set.Ico, Set.Ici, Set.Iio, and_left_comm, and_assoc] using
    (hIci.inter (Iio_mem_nhds hε) :
      UniqueMDiffWithinAt 𝓘(ℝ) ((Set.Ici (0 : ℝ)) ∩ Set.Iio ε) (0 : ℝ))

/-- Helper for Proposition 3.23: the left half-interval `(-ε, 0]` has unique manifold
differentential at `0`. -/
lemma uniqueMDiffWithinAt_Ioc_zero {ε : ℝ} (hε : 0 < ε) :
    UniqueMDiffWithinAt 𝓘(ℝ) (Set.Ioc (-ε) 0) 0 := by
  -- Near `0`, the set `Ioc (-ε) 0` agrees with the one-sided model domain `Iic 0`.
  have hIic : UniqueMDiffWithinAt 𝓘(ℝ) (Set.Iic (0 : ℝ)) (0 : ℝ) :=
    (uniqueDiffWithinAt_Iic (0 : ℝ)).uniqueMDiffWithinAt
  -- Intersect `Iic 0` with the ordinary neighborhood `(-ε, ∞)`.
  simpa [Set.Ioc, Set.Ioi, Set.Iic, Set.inter_comm, and_comm, and_left_comm, and_assoc] using
    (hIic.inter (Ioi_mem_nhds (by linarith : (-ε : ℝ) < 0)) :
      UniqueMDiffWithinAt 𝓘(ℝ) ((Set.Iic (0 : ℝ)) ∩ Set.Ioi (-ε)) (0 : ℝ))

/-- Helper for Proposition 3.23: a neighborhood of `x₀` contains the affine line
`t ↦ x₀ + t • w` on some symmetric interval around `0`. -/
lemma affine_line_mapsTo_symmetric_interval_of_mem_nhds (x₀ w : E) {s : Set E}
    (hs : s ∈ nhds x₀) :
    ∃ ε : Set.Ioi (0 : ℝ), Set.MapsTo (fun t : ℝ ↦ x₀ + t • w) (Set.Ioo (-ε) ε) s := by
  let η : ℝ → E := fun t ↦ x₀ + t • w
  -- Pull the target neighborhood back along the affine line to get a neighborhood of `0`.
  have hη_cont : Continuous η := by
    simpa [η] using continuous_const.add (continuous_id.smul continuous_const)
  have hs0 : s ∈ nhds (η 0) := by
    simpa [η] using hs
  have hpre : η ⁻¹' s ∈ nhds (0 : ℝ) := by
    simpa [η] using hη_cont.continuousAt.preimage_mem_nhds hs0
  -- Extract an interval around `0` in the parameter line and then symmetrize it.
  rcases mem_nhds_iff_exists_Ioo_subset.mp hpre with ⟨a, b, hab, hIab⟩
  let ε : ℝ := min (-a) b
  have hεpos : 0 < ε := by
    have hna : 0 < -a := by linarith [hab.1]
    exact lt_min hna hab.2
  refine ⟨⟨ε, hεpos⟩, ?_⟩
  -- Any `t` in the symmetric interval still lies in the extracted interval `(a, b)`.
  intro t ht
  apply hIab
  constructor
  · by_contra hta
    have hat : t ≤ a := le_of_not_gt hta
    have ha_neg : a ≤ -ε := by
      have hε_le : ε ≤ -a := min_le_left _ _
      linarith
    exact (not_le_of_gt ht.1) (hat.trans ha_neg)
  · by_contra htb
    have hbt : b ≤ t := le_of_not_gt htb
    have hε_b : ε ≤ b := min_le_right _ _
    exact (not_le_of_gt ht.2) (hε_b.trans hbt)

section GeneralManifold

variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Helper for Proposition 3.23: after pushing a chart-lifted curve forward by the same extended
chart, its within-velocity agrees with the model-space within-velocity of the original coordinate
curve. -/
lemma extChartAt_velocity_after_chart
    (p : M) {J : Set ℝ} (η : ℝ → E) (h0 : (0 : ℝ) ∈ J)
    (hJ : UniqueMDiffWithinAt 𝓘(ℝ) J 0)
    (hη0 : η 0 = extChartAt I p p)
    (hη_target : Set.MapsTo η J (extChartAt I p).target)
    (hη_smooth : ContMDiffOn 𝓘(ℝ) (𝓘(ℝ, E)) ∞ η J) :
    let γ : ℝ → M := (extChartAt I p).symm ∘ η
    γ 0 = p ∧
      mfderiv I (𝓘(ℝ, E)) (extChartAt I p) (γ 0) (curve_velocityWithin I γ J 0) =
        curve_velocityWithin (𝓘(ℝ, E)) η J 0 := by
  let γ : ℝ → M := (extChartAt I p).symm ∘ η
  -- First build the lifted manifold curve by composing the inverse chart with the model curve.
  have hγ_smooth : ContMDiffOn 𝓘(ℝ) I ∞ γ J := by
    simpa [γ, Function.comp] using
      (contMDiffOn_extChartAt_symm (I := I) (n := ∞) p).comp hη_smooth hη_target
  -- The lift passes through `p` because `η 0` is the chart center.
  have hγ0 : γ 0 = p := by
    dsimp [γ]
    rw [hη0]
    exact (extChartAt I p).left_inv (mem_extChartAt_source p)
  -- Route correction: compare velocities after applying the forward chart, where the composition
  -- is literally `η` on `J`, instead of rewriting directly through the inverse-chart derivative.
  have hchart_md : MDifferentiableAt I (𝓘(ℝ, E)) (extChartAt I p) (γ 0) := by
    simpa [hγ0] using
      (mdifferentiableAt_extChartAt (I := I) (x := p) (y := p) (mem_chart_source H p))
  have hγ_md : MDifferentiableWithinAt 𝓘(ℝ) I γ J 0 := by
    exact hγ_smooth.mdifferentiableOn (by simp) 0 h0
  have hvelocity_after_chart :
      curve_velocityWithin (𝓘(ℝ, E)) ((extChartAt I p) ∘ γ) J 0 =
        mfderiv I (𝓘(ℝ, E)) (extChartAt I p) (γ 0) (curve_velocityWithin I γ J 0) := by
    simpa [curve_velocityWithin] using
      DFunLike.congr_fun (mfderiv_comp_mfderivWithin (x := 0) hchart_md hγ_md hJ)
        (show TangentSpace (𝓘(ℝ, ℝ)) (0 : ℝ) from (1 : ℝ))
  -- On the parameter set `J`, applying the chart to the lifted curve gives back `η`.
  have hchart_eq_eta :
      curve_velocityWithin (𝓘(ℝ, E)) ((extChartAt I p) ∘ γ) J 0 =
        curve_velocityWithin (𝓘(ℝ, E)) η J 0 := by
    simpa [curve_velocityWithin] using
      DFunLike.congr_fun
        (mfderivWithin_congr_of_mem
          (I := 𝓘(ℝ)) (I' := 𝓘(ℝ, E)) (s := J) (x := 0)
          (f₁ := (extChartAt I p) ∘ γ) (f := η)
          (fun t ht ↦ by
            dsimp [γ, Function.comp]
            exact (extChartAt I p).right_inv (hη_target ht))
          h0)
        (show TangentSpace (𝓘(ℝ, ℝ)) (0 : ℝ) from (1 : ℝ))
  have hfinal :
      mfderiv I (𝓘(ℝ, E)) (extChartAt I p) (γ 0) (curve_velocityWithin I γ J 0) =
        curve_velocityWithin (𝓘(ℝ, E)) η J 0 := by
    exact hvelocity_after_chart.symm.trans hchart_eq_eta
  exact ⟨hγ0, hfinal⟩

/-- Helper for Proposition 3.23: transport a tangent vector equality from `γ 0` back to the fixed
basepoint `p` before applying the chart derivative. -/
lemma tangent_transport_mfderiv_extChartAt_eq
    (p : M) {γ : ℝ → M} (hγ : γ 0 = p) (ξ : TangentSpace I (γ 0)) :
    mfderiv I (𝓘(ℝ, E)) (extChartAt I p) p (hγ ▸ ξ) =
      mfderiv I (𝓘(ℝ, E)) (extChartAt I p) (γ 0) ξ := by
  -- Quarantine the dependent-cast normalization in a one-line proof.
  cases hγ
  rfl

/-- Helper for Proposition 3.23: if a model-space curve starts at the chart center, stays in the
chart target, and has the correct model velocity, then pushing it through the inverse extended
chart realizes the desired tangent vector on the manifold. -/
lemma extChartAt_symm_velocity_of_model_curve
    (p : M) (v : TangentSpace I p) {J : Set ℝ} (η : ℝ → E) (h0 : (0 : ℝ) ∈ J)
    (hJ : UniqueMDiffWithinAt 𝓘(ℝ) J 0)
    (hη0 : η 0 = extChartAt I p p)
    (hη_target : Set.MapsTo η J (extChartAt I p).target)
    (hη_smooth : ContMDiffOn 𝓘(ℝ) (𝓘(ℝ, E)) ∞ η J)
    (hη_velocity :
      curve_velocityWithin (𝓘(ℝ, E)) η J 0 =
        mfderiv I (𝓘(ℝ, E)) (extChartAt I p) p v) :
    let γ : ℝ → M := (extChartAt I p).symm ∘ η
    ContMDiffOn 𝓘(ℝ) I ∞ γ J ∧
      ∃ hγ : γ 0 = p, hγ ▸ curve_velocityWithin I γ J 0 = v := by
  let γ : ℝ → M := (extChartAt I p).symm ∘ η
  -- First record smoothness of the lifted curve coming from the smooth inverse chart.
  have hγ_smooth : ContMDiffOn 𝓘(ℝ) I ∞ γ J := by
    simpa [γ, Function.comp] using
      (contMDiffOn_extChartAt_symm (I := I) (n := ∞) p).comp hη_smooth hη_target
  -- Then use the forward-chart computation to reduce the velocity statement to a fixed basepoint.
  rcases extChartAt_velocity_after_chart
      (I := I) (p := p) (J := J) η h0 hJ hη0 hη_target hη_smooth with
    ⟨hγ0, hchart⟩
  -- Route correction: rewrite the transported tangent vector at `γ 0` back to `p` before
  -- applying injectivity of the chart derivative, instead of unfolding the cast in place.
  have hfixed :
      mfderiv I (𝓘(ℝ, E)) (extChartAt I p) p (hγ0 ▸ curve_velocityWithin I γ J 0) =
        mfderiv I (𝓘(ℝ, E)) (extChartAt I p) p v := by
    exact
      (tangent_transport_mfderiv_extChartAt_eq (I := I) (p := p) (γ := γ) hγ0
        (curve_velocityWithin I γ J 0)).trans <|
        hchart.trans hη_velocity
  -- Finally cancel the chart derivative at the common basepoint `p`.
  have hvelocity :
      hγ0 ▸ curve_velocityWithin I γ J 0 = v :=
    (isInvertible_mfderiv_extChartAt (I := I) (x := p) (y := p) (mem_extChartAt_source p)).injective
      hfixed
  exact ⟨hγ_smooth, ⟨hγ0, hvelocity⟩⟩

/-- Helper for Proposition 3.23: at an interior point, a tangent vector is realized by an open
interval curve obtained from an affine line in extended-chart coordinates. -/
lemma exists_open_interval_curve_with_velocity_of_isInteriorPoint
    (p : M) (v : TangentSpace I p) (hpi : I.IsInteriorPoint p) :
    ∃ ε : Set.Ioi (0 : ℝ), ∃ γ : ℝ → M,
      ContMDiffOn 𝓘(ℝ) I ∞ γ (Set.Ioo (-ε) ε) ∧
        ∃ hγ : γ 0 = p, hγ ▸ curve_velocityWithin I γ (Set.Ioo (-ε) ε) 0 = v := by
  let x₀ : E := extChartAt I p p
  let wt : TangentSpace (𝓘(ℝ, E)) x₀ := mfderiv I (𝓘(ℝ, E)) (extChartAt I p) p v
  let w : E := wt
  let η : ℝ → E := fun t ↦ x₀ + t • w
  -- First combine interiority with the chart target to get one chart-safe neighborhood of `x₀`.
  have hrange : Set.range I ∈ nhds x₀ := by
    simpa [x₀] using range_mem_nhds_isInteriorPoint hpi
  have htarget_within : (extChartAt I p).target ∈ nhdsWithin x₀ (Set.range I) := by
    simpa [x₀] using extChartAt_target_mem_nhdsWithin (I := I) p
  have htarget : (extChartAt I p).target ∈ nhds x₀ := by
    rwa [nhdsWithin_eq_nhds.2 hrange] at htarget_within
  have hsafe : Set.range I ∩ (extChartAt I p).target ∈ nhds x₀ := by
    exact Filter.inter_mem hrange htarget
  -- Then shrink Lee's affine coordinate line into that neighborhood on a symmetric interval.
  rcases affine_line_mapsTo_symmetric_interval_of_mem_nhds x₀ w hsafe with ⟨ε, hη_safe⟩
  let J : Set ℝ := Set.Ioo (-(ε : ℝ)) (ε : ℝ)
  have h0 : (0 : ℝ) ∈ J := by
    have hε : 0 < (ε : ℝ) := ε.2
    have hneg : -(ε : ℝ) < 0 := by linarith
    exact ⟨hneg, by simpa using hε⟩
  have hJ : UniqueMDiffWithinAt 𝓘(ℝ) J 0 := by
    exact (uniqueDiffWithinAt_Ioo h0).uniqueMDiffWithinAt
  have hη_target : Set.MapsTo η J (extChartAt I p).target := by
    intro t ht
    exact (hη_safe ht).2
  have hη0 : η 0 = extChartAt I p p := by
    simp [η, x₀]
  have hη_smooth :
      ContMDiffOn 𝓘(ℝ) (𝓘(ℝ, E)) ∞ η J := by
    -- The coordinate curve is the affine line from Lee's proof, so it is smooth on every set.
    simpa [η, x₀, J] using
      ((contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff.contMDiffOn :
        ContMDiffOn 𝓘(ℝ) (𝓘(ℝ, E)) ∞
          (fun t : ℝ ↦ x₀ + t • w) J)
  have hη_velocity :
      curve_velocityWithin (𝓘(ℝ, E)) η J 0 =
        mfderiv I (𝓘(ℝ, E)) (extChartAt I p) p v := by
    simpa [η, w, wt, J] using affine_model_curve_velocity_within_tangent (x₀ := x₀) wt hJ
  -- Finally lift the model-space curve back through the inverse chart.
  rcases extChartAt_symm_velocity_of_model_curve
      (I := I) (p := p) (v := v) (J := J) η h0 hJ hη0 hη_target hη_smooth
      hη_velocity with
    ⟨hγ_smooth, hγ_velocity⟩
  exact ⟨ε, (extChartAt I p).symm ∘ η, by simpa [J] using hγ_smooth, by simpa [J] using hγ_velocity⟩

end GeneralManifold

variable {n : ℕ}
variable {M : Type uM} [TopologicalSpace M] [SmoothManifoldWithBoundary n M]

/-- Helper for Proposition 3.23: at a boundary point of the positive-dimensional half-space model,
the extended chart sends the basepoint to the boundary hyperplane, so the distinguished boundary
coordinate is `0`. -/
lemma boundary_chart_first_coordinate_eq_zero
    {k : ℕ} {M : Type uM} [TopologicalSpace M] [SmoothManifoldWithBoundary (k + 1) M]
    {p : M} (hpb : (𝓡∂ (k + 1)).IsBoundaryPoint p) :
    extChartAt (𝓡∂ (k + 1)) p p 0 = 0 := by
  -- Rewrite the boundary-point condition in Lee's chart as membership in the model frontier.
  rw [(𝓡∂ (k + 1)).isBoundaryPoint_iff,
    frontier_range_modelWithCornersEuclideanHalfSpace (k + 1)] at hpb
  simpa [eq_comm] using hpb

/-- Helper for Proposition 3.23: if an affine line in the Euclidean model starts on the boundary
hyperplane `x 0 = 0`, then restricting the parameter interval by the sign of the boundary
coordinate velocity keeps the line inside Lee's half-space model. -/
lemma affine_half_space_mapsTo_signed_interval {k : ℕ}
    (x₀ w : EuclideanSpace ℝ (Fin (k + 1))) (hx₀ : x₀ 0 = 0) (ε : Set.Ioi (0 : ℝ)) :
    (w 0 = 0 →
        Set.MapsTo (fun t : ℝ ↦ x₀ + t • w) (Set.Ioo (-(ε : ℝ)) (ε : ℝ))
          (Set.range (𝓡∂ (k + 1)))) ∧
      (0 < w 0 →
        Set.MapsTo (fun t : ℝ ↦ x₀ + t • w) (Set.Ico 0 (ε : ℝ))
          (Set.range (𝓡∂ (k + 1)))) ∧
      (w 0 < 0 →
        Set.MapsTo (fun t : ℝ ↦ x₀ + t • w) (Set.Ioc (-(ε : ℝ)) 0)
          (Set.range (𝓡∂ (k + 1)))) := by
  constructor
  · intro hw0 t ht
    -- On the symmetric interval, zero normal velocity keeps the affine line in the boundary
    -- hyperplane, hence in the half-space range.
    rw [range_modelWithCornersEuclideanHalfSpace (k + 1)]
    change 0 ≤ (x₀ + t • w) 0
    simpa [Pi.add_apply, Pi.smul_apply, hx₀, hw0]
  constructor
  · intro hwpos t ht
    -- Positive normal velocity stays in the half-space on `[0, ε)`.
    rw [range_modelWithCornersEuclideanHalfSpace (k + 1)]
    change 0 ≤ (x₀ + t • w) 0
    simpa [Pi.add_apply, Pi.smul_apply, hx₀] using mul_nonneg ht.1 hwpos.le
  · intro hwneg t ht
    -- Negative normal velocity stays in the half-space on `(-ε, 0]`.
    rw [range_modelWithCornersEuclideanHalfSpace (k + 1)]
    change 0 ≤ (x₀ + t • w) 0
    simpa [Pi.add_apply, Pi.smul_apply, hx₀] using
      mul_nonneg_of_nonpos_of_nonpos ht.2 hwneg.le

/-- Helper for Proposition 3.23: at a boundary point of Lee's positive-dimensional model, the
affine chart line realizing a tangent vector can be restricted to a symmetric or one-sided
interval according to the sign of its boundary coordinate velocity. -/
lemma exists_one_sided_curve_with_velocity_of_isBoundaryPoint
    {k : ℕ} {M : Type uM} [TopologicalSpace M] [SmoothManifoldWithBoundary (k + 1) M]
    (p : M) (v : TangentSpace (𝓡∂ (k + 1)) p) (hpb : (𝓡∂ (k + 1)).IsBoundaryPoint p) :
    ∃ ε : Set.Ioi (0 : ℝ), ∃ γ : ℝ → M,
      (ContMDiffOn 𝓘(ℝ) (𝓡∂ (k + 1)) ∞ γ (Set.Ioo (-ε) ε) ∧
        ∃ hγ : γ 0 = p,
          hγ ▸ curve_velocityWithin (𝓡∂ (k + 1)) γ (Set.Ioo (-ε) ε) 0 = v) ∨
      (ContMDiffOn 𝓘(ℝ) (𝓡∂ (k + 1)) ∞ γ (Set.Ico 0 ε) ∧
        ∃ hγ : γ 0 = p,
          hγ ▸ curve_velocityWithin (𝓡∂ (k + 1)) γ (Set.Ico 0 ε) 0 = v) ∨
      (ContMDiffOn 𝓘(ℝ) (𝓡∂ (k + 1)) ∞ γ (Set.Ioc (-ε) 0) ∧
        ∃ hγ : γ 0 = p,
          hγ ▸ curve_velocityWithin (𝓡∂ (k + 1)) γ (Set.Ioc (-ε) 0) 0 = v) := by
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (k + 1))) (EuclideanHalfSpace (k + 1)) :=
    𝓡∂ (k + 1)
  let x₀ : EuclideanSpace ℝ (Fin (k + 1)) := extChartAt I p p
  let wt : TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1)))) x₀ :=
    mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1)))) (extChartAt I p) p v
  let w : EuclideanSpace ℝ (Fin (k + 1)) := wt
  let η : ℝ → EuclideanSpace ℝ (Fin (k + 1)) := fun t ↦ x₀ + t • w
  -- Boundary points land on the model hyperplane, which is the source normalization in Lee's
  -- boundary construction.
  have hx₀ : x₀ 0 = 0 := by
    simpa [I, x₀] using boundary_chart_first_coordinate_eq_zero (k := k) (p := p) hpb
  -- Use a neighborhood that agrees with the chart target on points already known to lie in the
  -- model range; the affine-line shrinking lemma can then stay in the ambient Euclidean space.
  have hsafe :
      (extChartAt I p).target ∪ (Set.range I)ᶜ ∈ nhds x₀ := by
    simpa [I, x₀] using
      (extChartAt_target_union_compl_range_mem_nhds_of_mem (I := I)
        (x := p) (hy := mem_extChartAt_target p))
  rcases affine_line_mapsTo_symmetric_interval_of_mem_nhds x₀ w hsafe with ⟨ε, hη_safe⟩
  have hε : 0 < (ε : ℝ) := by
    exact ε.2
  have hη0 : η 0 = extChartAt I p p := by
    simp [η, x₀]
  have hη_smooth (J : Set ℝ) :
      ContMDiffOn 𝓘(ℝ) (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1)))) ∞ η J := by
    -- Lee's coordinate curve is the same affine line as in the interior case, hence smooth on
    -- every interval choice used below.
    simpa [η, x₀] using
      ((contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff.contMDiffOn :
        ContMDiffOn 𝓘(ℝ) (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1)))) ∞
          (fun t : ℝ ↦ x₀ + t • w) J)
  have htarget_of_safe {y : EuclideanSpace ℝ (Fin (k + 1))}
      (hy_safe : y ∈ (extChartAt I p).target ∪ (Set.range I)ᶜ)
      (hy_range : y ∈ Set.range I) :
      y ∈ (extChartAt I p).target := by
    -- Membership in the model range rules out the complement branch of the ambient neighborhood.
    rcases hy_safe with hy_target | hy_out
    · exact hy_target
    · exact False.elim (hy_out hy_range)
  have hnegε : (-(ε : ℝ)) < 0 := by
    linarith
  have h0_Ioo : (0 : ℝ) ∈ Set.Ioo (-(ε : ℝ)) (ε : ℝ) := by
    exact ⟨hnegε, hε⟩
  have h0_Ico : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (ε : ℝ) := by
    exact ⟨le_rfl, hε⟩
  have h0_Ioc : (0 : ℝ) ∈ Set.Ioc (-(ε : ℝ)) (0 : ℝ) := by
    exact ⟨hnegε, le_rfl⟩
  have hIoo : UniqueMDiffWithinAt 𝓘(ℝ) (Set.Ioo (-(ε : ℝ)) (ε : ℝ)) 0 := by
    exact (uniqueDiffWithinAt_Ioo h0_Ioo).uniqueMDiffWithinAt
  have hIco : UniqueMDiffWithinAt 𝓘(ℝ) (Set.Ico (0 : ℝ) (ε : ℝ)) 0 := by
    exact uniqueMDiffWithinAt_Ico_zero hε
  have hIoc : UniqueMDiffWithinAt 𝓘(ℝ) (Set.Ioc (-(ε : ℝ)) (0 : ℝ)) 0 := by
    exact uniqueMDiffWithinAt_Ioc_zero hε
  have hIco_subset : Set.Ico (0 : ℝ) (ε : ℝ) ⊆ Set.Ioo (-(ε : ℝ)) (ε : ℝ) := by
    exact Set.Ico_subset_Ioo_left hnegε
  have hIoc_subset : Set.Ioc (-(ε : ℝ)) (0 : ℝ) ⊆ Set.Ioo (-(ε : ℝ)) (ε : ℝ) := by
    exact Set.Ioc_subset_Ioo_right hε
  have hsigned := affine_half_space_mapsTo_signed_interval x₀ w hx₀ ε
  -- Route correction: split Lee's boundary construction by the sign of the boundary coordinate
  -- of the chart velocity before lifting through `extChartAt.symm`.
  by_cases hw0 : w 0 = 0
  · have hη_range :
        Set.MapsTo η (Set.Ioo (-(ε : ℝ)) (ε : ℝ)) (Set.range I) :=
      (hsigned.1 hw0)
    have hη_target :
        Set.MapsTo η (Set.Ioo (-(ε : ℝ)) (ε : ℝ)) (extChartAt I p).target := by
      intro t ht
      exact htarget_of_safe (hη_safe ht) (hη_range ht)
    have hη_velocity :
        curve_velocityWithin (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1)))) η
            (Set.Ioo (-(ε : ℝ)) (ε : ℝ)) 0 =
          mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1)))) (extChartAt I p) p v := by
      simpa [η, w, wt] using affine_model_curve_velocity_within_tangent (x₀ := x₀) wt hIoo
    rcases extChartAt_symm_velocity_of_model_curve
        (I := I) (p := p) (v := v) (J := Set.Ioo (-(ε : ℝ)) (ε : ℝ)) η h0_Ioo hIoo
        hη0 hη_target (hη_smooth _) hη_velocity with
      ⟨hγ_smooth, hγ_velocity⟩
    exact ⟨ε, (extChartAt I p).symm ∘ η, Or.inl ⟨hγ_smooth, hγ_velocity⟩⟩
  · by_cases hwpos : 0 < w 0
    · have hη_range :
          Set.MapsTo η (Set.Ico (0 : ℝ) (ε : ℝ)) (Set.range I) :=
        (hsigned.2.1 hwpos)
      have hη_target :
          Set.MapsTo η (Set.Ico (0 : ℝ) (ε : ℝ)) (extChartAt I p).target := by
        intro t ht
        exact htarget_of_safe (hη_safe (hIco_subset ht)) (hη_range ht)
      have hη_velocity :
          curve_velocityWithin (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1)))) η
              (Set.Ico (0 : ℝ) (ε : ℝ)) 0 =
            mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1)))) (extChartAt I p) p v := by
        simpa [η, w, wt] using affine_model_curve_velocity_within_tangent (x₀ := x₀) wt hIco
      rcases extChartAt_symm_velocity_of_model_curve
          (I := I) (p := p) (v := v) (J := Set.Ico (0 : ℝ) (ε : ℝ)) η h0_Ico hIco
          hη0 hη_target (hη_smooth _) hη_velocity with
        ⟨hγ_smooth, hγ_velocity⟩
      exact ⟨ε, (extChartAt I p).symm ∘ η, Or.inr <| Or.inl ⟨hγ_smooth, hγ_velocity⟩⟩
    · have hwneg : w 0 < 0 := by
        exact lt_of_le_of_ne (not_lt.mp hwpos) hw0
      have hη_range :
          Set.MapsTo η (Set.Ioc (-(ε : ℝ)) (0 : ℝ)) (Set.range I) :=
        (hsigned.2.2 hwneg)
      have hη_target :
          Set.MapsTo η (Set.Ioc (-(ε : ℝ)) (0 : ℝ)) (extChartAt I p).target := by
        intro t ht
        exact htarget_of_safe (hη_safe (hIoc_subset ht)) (hη_range ht)
      have hη_velocity :
          curve_velocityWithin (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1)))) η
              (Set.Ioc (-(ε : ℝ)) (0 : ℝ)) 0 =
            mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1)))) (extChartAt I p) p v := by
        simpa [η, w, wt] using affine_model_curve_velocity_within_tangent (x₀ := x₀) wt hIoc
      rcases extChartAt_symm_velocity_of_model_curve
          (I := I) (p := p) (v := v) (J := Set.Ioc (-(ε : ℝ)) (0 : ℝ)) η h0_Ioc hIoc
          hη0 hη_target (hη_smooth _) hη_velocity with
        ⟨hγ_smooth, hγ_velocity⟩
      exact ⟨ε, (extChartAt I p).symm ∘ η, Or.inr <| Or.inr ⟨hγ_smooth, hγ_velocity⟩⟩

-- Proof sketch: choose a smooth chart centered at `p`; in the interior case use the inverse chart
-- on a small open interval around the line `t ↦ t • w` representing `v` in Lee's model `H^n`, and
-- in the boundary case use the same coordinate formula on a suitable one-sided interval so the
-- image stays in the model half-space. The statement keeps the interval witness explicit rather
-- than hiding it behind an arbitrary parameter set with `UniqueMDiffWithinAt`.
/-- Proposition 3.23 (`source-facing`): on an `n`-dimensional smooth manifold with boundary in
Lee's sense, every
tangent vector at `p` is realized as the velocity at `0` of a smooth curve through `p`, either on
an open interval around `0` or on a one-sided interval when the curve must remain in the boundary
model. -/
theorem exists_smooth_curve_with_velocity
    (p : M) (v : TangentSpace (leeBoundaryModelWithCorners n) p) :
    ∃ ε : Set.Ioi (0 : ℝ), ∃ γ : ℝ → M,
      (ContMDiffOn 𝓘(ℝ) (leeBoundaryModelWithCorners n) ∞ γ (Set.Ioo (-ε) ε) ∧
        ∃ hγ : γ 0 = p,
          hγ ▸ curve_velocityWithin (leeBoundaryModelWithCorners n) γ (Set.Ioo (-ε) ε) 0 = v) ∨
      (ContMDiffOn 𝓘(ℝ) (leeBoundaryModelWithCorners n) ∞ γ (Set.Ico 0 ε) ∧
        ∃ hγ : γ 0 = p,
          hγ ▸ curve_velocityWithin (leeBoundaryModelWithCorners n) γ (Set.Ico 0 ε) 0 = v) ∨
      (ContMDiffOn 𝓘(ℝ) (leeBoundaryModelWithCorners n) ∞ γ (Set.Ioc (-ε) 0) ∧
        ∃ hγ : γ 0 = p,
          hγ ▸ curve_velocityWithin (leeBoundaryModelWithCorners n) γ (Set.Ioc (-ε) 0) 0 = v) :=
  by
  by_cases hpi : (leeBoundaryModelWithCorners n).IsInteriorPoint p
  · -- The interior branch is exactly the open-interval construction from the source proof.
    rcases exists_open_interval_curve_with_velocity_of_isInteriorPoint p v hpi with
      ⟨ε, γ, hγsmooth, hγvel⟩
    exact ⟨ε, γ, Or.inl ⟨hγsmooth, hγvel⟩⟩
  · -- TODO: source-faithful boundary branch.
    -- Route correction: split on the model dimension. In dimension `0` the model is already
    -- boundaryless, and in positive dimension Lee's one-sided boundary chart construction applies.
    cases n with
    | zero =>
        exfalso
        exact hpi <| by
          simpa [leeBoundaryModelWithCorners] using
            (BoundarylessManifold.isInteriorPoint (I := 𝓡 0) (M := M) (x := p))
    | succ k =>
        have hpb : (𝓡∂ (k + 1)).IsBoundaryPoint p := by
          refine ((𝓡∂ (k + 1)).isBoundaryPoint_iff_not_isInteriorPoint p).2 ?_
          simpa [leeBoundaryModelWithCorners] using hpi
        simpa [leeBoundaryModelWithCorners] using
          exists_one_sided_curve_with_velocity_of_isBoundaryPoint (k := k) (p := p) (v := v) hpb

end

section Boundaryless

variable {n : ℕ}
variable {M : Type uM} [TopologicalSpace M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [IsManifold (𝓡 n) ∞ M] [BoundarylessManifold (𝓡 n) M]

/-- Proposition 3.23 (`bridge/view`): on a boundaryless smooth `n`-manifold modeled on `𝓡 n`,
every tangent vector at `p` is realized as the velocity at `0` of a smooth curve through `p`
defined on an open interval around `0`. -/
theorem exists_smooth_curve_with_velocity_boundaryless
    (p : M) (v : TangentSpace (𝓡 n) p) :
    ∃ ε : Set.Ioi (0 : ℝ), ∃ γ : ℝ → M,
      ContMDiffOn 𝓘(ℝ) (𝓡 n) ∞ γ (Set.Ioo (-ε) ε) ∧
        ∃ hγ : γ 0 = p,
          hγ ▸ curve_velocityWithin (𝓡 n) γ (Set.Ioo (-ε) ε) 0 = v :=
  by
  -- On a boundaryless manifold every point is interior, so the interior helper applies directly.
  simpa using
    exists_open_interval_curve_with_velocity_of_isInteriorPoint
      (I := 𝓡 n) p v BoundarylessManifold.isInteriorPoint

end Boundaryless
