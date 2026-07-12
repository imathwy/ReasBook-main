import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0017_Definition_II_1_extra_10»
import DifferentialForms_Cartan_1970.II.section05.«0026_Definition_II_1_extra_16»
import DifferentialForms_Cartan_1970.II.section05.«0028_Proposition_8_1»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval

noncomputable section

namespace Path

theorem not_mem_range_of_range_subset {z : ℂ} (γ : Path z z) {D : Set ℂ} {a : ℂ}
    (hγD : Set.range γ ⊆ D) (haD : a ∉ D) :
    a ∉ Set.range γ :=
  fun haγ ↦ haD (hγD haγ)

end Path

theorem not_mem_range_left_of_closedPathHomotopicIn_compl_singleton
    {z₀ z₁ a : ℂ} {γ₀ : Path z₀ z₀} {γ₁ : Path z₁ z₁}
    (hγ : ClosedPathHomotopicIn ({a} : Set ℂ)ᶜ γ₀ γ₁) :
    a ∉ Set.range γ₀ := by
  have hγ₀ : IsClosedPathIn ({a} : Set ℂ)ᶜ (γ₀ : C(I, ℂ)) := by
    simpa using hγ.some.prop 0
  rintro ⟨t, rfl⟩
  exact (isClosedPathIn_compl_iff.mp hγ₀).2 t (by simp)

theorem not_mem_range_right_of_closedPathHomotopicIn_compl_singleton
    {z₀ z₁ a : ℂ} {γ₀ : Path z₀ z₀} {γ₁ : Path z₁ z₁}
    (hγ : ClosedPathHomotopicIn ({a} : Set ℂ)ᶜ γ₀ γ₁) :
    a ∉ Set.range γ₁ := by
  have hγ₁ : IsClosedPathIn ({a} : Set ℂ)ᶜ (γ₁ : C(I, ℂ)) := by
    simpa using hγ.some.prop 1
  rintro ⟨t, rfl⟩
  exact (isClosedPathIn_compl_iff.mp hγ₁).2 t (by simp)

/-- Helper for Cartan section05 0027_Remark_II_1_extra_17: a continuous logarithm branch whose
exponential is constantly `1` is locally constant. -/
theorem isLocallyConstant_of_continuous_exp_eq_one {X : Type*} [TopologicalSpace X]
    (f : C(X, ℂ)) (hf : ∀ x : X, Complex.exp (f x) = 1) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨f ⁻¹' Metric.ball (f x) 1, f.continuous.isOpen_preimage _ Metric.isOpen_ball, ?_, ?_⟩
  · simp [Metric.mem_ball, zero_lt_one]
  · intro y hy
    have hEqExp : Complex.exp (f y) = Complex.exp (f x) := by
      rw [hf y, hf x]
    rcases Complex.exp_eq_exp_iff_exists_int.mp hEqExp with ⟨n, hn⟩
    by_cases hn0 : n = 0
    · simpa [hn0] using hn
    · have hdist_lt : ‖f y - f x‖ < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hy
      have hnorm_n : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by
        have : (1 : ℝ) ≤ |(n : ℝ)| := by
          exact_mod_cast Int.one_le_abs hn0
        simpa [Complex.norm_intCast] using this
      have hnorm_ge : 2 * Real.pi ≤ ‖f y - f x‖ := by
        calc
          2 * Real.pi = 1 * ‖(2 * Real.pi : ℂ) * Complex.I‖ := by
            simp [abs_of_nonneg Real.pi_pos.le]
          _ ≤ ‖(n : ℂ)‖ * ‖(2 * Real.pi : ℂ) * Complex.I‖ := by
            gcongr
          _ = ‖(n : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)‖ := by
            simp
          _ = ‖f y - f x‖ := by
            simp [hn, sub_eq_add_neg, add_assoc, add_comm]
      have hlt : (1 : ℝ) < 2 * Real.pi := by
        nlinarith [Real.pi_gt_three]
      linarith

/-- Helper for Cartan section05 0027_Remark_II_1_extra_17: for a lift of a punctured-plane square
whose horizontal slices are closed loops, the logarithmic endpoint jump is independent of the
vertical parameter. -/
theorem liftEndpointDifference_eq_of_closedSquare
    (H : C(I × I, {z : ℂ // z ≠ 0})) (hclosed : ∀ s : I, H (1, s) = H (0, s))
    (W : C(I × I, ℂ))
    (hW :
      (fun z : ℂ ↦ (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘ W = H) :
    ∀ s : I, W (1, s) - W (0, s) = W (1, 0) - W (0, 0) := by
  let Δ : C(I, ℂ) :=
    ⟨fun s ↦ W (1, s) - W (0, s), by
      fun_prop⟩
  have hΔexp : ∀ s : I, Complex.exp (Δ s) = 1 := by
    intro s
    have htop : Complex.exp (W (1, s)) = (H (1, s)).1 := by
      simpa using congrArg Subtype.val (congr_fun hW (1, s))
    have hbot : Complex.exp (W (0, s)) = (H (0, s)).1 := by
      simpa using congrArg Subtype.val (congr_fun hW (0, s))
    calc
      Complex.exp (Δ s) = Complex.exp (W (1, s)) / Complex.exp (W (0, s)) := by
        simp [Δ, Complex.exp_sub]
      _ = (H (1, s)).1 / (H (0, s)).1 := by
        rw [htop, hbot]
      _ = 1 := by
        rw [hclosed s]
        exact div_self (H (0, s)).2
  have hΔ_loc : IsLocallyConstant Δ := isLocallyConstant_of_continuous_exp_eq_one Δ hΔexp
  intro s
  exact hΔ_loc.apply_eq_of_preconnectedSpace s 0

/-- Helper for Cartan section05 0027_Remark_II_1_extra_17: if the straight segment joining two
punctures avoids the image of a closed path, then the path has the same index at those punctures.
-/
theorem closedPathIndex_eq_of_segment_subset_compl_range {z : ℂ} (γ : Path z z)
    (a b : {w : ℂ // w ∉ Set.range γ})
    (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hγ_integrable_a : CurveIntegrable (indexForm a.1) γ)
    (hγ_integrable_b : CurveIntegrable (indexForm b.1) γ)
    (hseg : segment ℝ a.1 b.1 ⊆ (Set.range γ)ᶜ) :
    closedPathIndex γ a = closedPathIndex γ b := by
  let H : C(I × I, {w : ℂ // w ≠ 0}) :=
    ⟨fun p ↦
      ⟨γ p.1 - AffineMap.lineMap a.1 b.1 (p.2 : ℝ), by
        intro hEq
        exact hseg (lineMap_mem_segment ℝ a.1 b.1 p.2.2) ⟨p.1, sub_eq_zero.mp hEq⟩⟩,
      by
        apply Continuous.subtype_mk
        fun_prop⟩
  have hclosed : ∀ s : I, H (1, s) = H (0, s) := by
    intro s
    apply Subtype.ext
    change γ 1 - AffineMap.lineMap a.1 b.1 (s : ℝ) =
      γ 0 - AffineMap.lineMap a.1 b.1 (s : ℝ)
    rw [γ.target, γ.source]
  let leftEdge : C(I, {w : ℂ // w ≠ 0}) :=
    ⟨fun s ↦ H (0, s), by
      fun_prop⟩
  have hleft_zero :
      leftEdge 0 =
        (⟨Complex.exp (Complex.log (γ 0 - a.1)),
          Complex.exp_ne_zero (Complex.log (γ 0 - a.1))⟩ : {w : ℂ // w ≠ 0}) := by
    have hγ0a : γ 0 - a.1 ≠ 0 := by
      intro hEq
      exact a.2 ⟨0, sub_eq_zero.mp hEq ▸ by simp⟩
    apply Subtype.ext
    simpa [leftEdge, H, γ.source] using (Complex.exp_log hγ0a).symm
  let leftLift : C(I, ℂ) :=
    Complex.isCoveringMap_exp.liftPath leftEdge (Complex.log (γ 0 - a.1)) hleft_zero
  have hleftLift :
      (fun z : ℂ ↦ (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {w : ℂ // w ≠ 0})) ∘ leftLift =
        leftEdge :=
    Complex.isCoveringMap_exp.liftPath_lifts leftEdge _ hleft_zero
  let W : C(I × I, ℂ) := Complex.isCoveringMap_exp.liftHomotopy H leftLift (by
    intro s
    simpa [leftEdge] using (congr_fun hleftLift s).symm)
  have hW :
      (fun z : ℂ ↦ (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {w : ℂ // w ≠ 0})) ∘ W = H :=
    Complex.isCoveringMap_exp.liftHomotopy_lifts H leftLift (by
      intro s
      simpa [leftEdge] using (congr_fun hleftLift s).symm)
  have hjump :
      W (1, 1) - W (0, 1) = W (1, 0) - W (0, 0) :=
    liftEndpointDifference_eq_of_closedSquare H hclosed W hW 1
  let bottomLift : C(I, ℂ) :=
    ⟨fun t ↦ W (t, 0), by
      fun_prop⟩
  let topLift : C(I, ℂ) :=
    ⟨fun t ↦ W (t, 1), by
      fun_prop⟩
  have hbottom_exp : ∀ t : I, Complex.exp (bottomLift t) = γ t - a.1 := by
    intro t
    have ht : Complex.exp (W (t, 0)) = (H (t, 0)).1 := by
      simpa using congrArg Subtype.val (congr_fun hW (t, 0))
    simpa [bottomLift, H] using ht
  have htop_exp : ∀ t : I, Complex.exp (topLift t) = γ t - b.1 := by
    intro t
    have ht : Complex.exp (W (t, 1)) = (H (t, 1)).1 := by
      simpa using congrArg Subtype.val (congr_fun hW (t, 1))
    simpa [topLift, H] using ht
  have hindex_bottom :
      closedPathIndex γ a =
        (bottomLift 1 - bottomLift 0) / (((2 * Real.pi : ℂ) * Complex.I)) :=
    closedPathIndex_eq_endpoint_log_lift_difference γ a bottomLift hγ_piecewise
      hγ_integrable_a hbottom_exp
  have hindex_top :
      closedPathIndex γ b =
        (topLift 1 - topLift 0) / (((2 * Real.pi : ℂ) * Complex.I)) :=
    closedPathIndex_eq_endpoint_log_lift_difference γ b topLift hγ_piecewise
      hγ_integrable_b htop_exp
  calc
    closedPathIndex γ a =
      (bottomLift 1 - bottomLift 0) / (((2 * Real.pi : ℂ) * Complex.I)) := hindex_bottom
    _ = (topLift 1 - topLift 0) / (((2 * Real.pi : ℂ) * Complex.I)) := by
      simp [bottomLift, topLift, hjump]
    _ = closedPathIndex γ b := hindex_top.symm

-- Proof sketch: apply Theorem `2'` to the closed logarithmic form `z ↦ dz / (z - a)` on
-- `ℂ \ {a}`; the homotopy keeps every intermediate closed path in the punctured plane, so the
-- normalized contour integral defining the index is unchanged.
/-- Cartan section05 0027_Remark_II_1_extra_17 (Remark II.1-extra-17, clause (1)): for a fixed
point `a`, the index of a closed path is invariant under continuous deformation through closed
paths that avoid `a`. -/
theorem closedPathIndex_eq_of_homotopic_avoiding_point
    {z₀ z₁ a : ℂ} {γ₀ : Path z₀ z₀} {γ₁ : Path z₁ z₁}
    (hγ : ClosedPathHomotopicIn ({a} : Set ℂ)ᶜ γ₀ γ₁)
    (hγ₀_piecewise : γ₀.IsPiecewiseDifferentiable)
    (hγ₁_piecewise : γ₁.IsPiecewiseDifferentiable)
    (hγ₀_integrable : CurveIntegrable (indexForm a) γ₀)
    (hγ₁_integrable : CurveIntegrable (indexForm a) γ₁) :
    γ₀.closedPathIndexAt a (not_mem_range_left_of_closedPathHomotopicIn_compl_singleton hγ) =
      γ₁.closedPathIndexAt a (not_mem_range_right_of_closedPathHomotopicIn_compl_singleton hγ) :=
  by
  let F := hγ.some
  have hF_closed : ∀ s : I, IsClosedPathIn ({a} : Set ℂ)ᶜ (F.curry s) := by
    intro s
    simpa using F.prop s
  let H : C(I × I, {w : ℂ // w ≠ 0}) :=
    ⟨fun p ↦
      ⟨F (p.2, p.1) - a, by
        exact sub_ne_zero.mpr ((isClosedPathIn_compl_iff.mp (hF_closed p.2)).2 p.1)⟩,
      by
        apply Continuous.subtype_mk
        fun_prop⟩
  have hclosed : ∀ s : I, H (1, s) = H (0, s) := by
    intro s
    have hs_closed : (F.curry s) 0 = (F.curry s) 1 := (hF_closed s).1
    apply Subtype.ext
    simpa [H] using congrArg (fun z : ℂ ↦ z - a) hs_closed.symm
  let leftEdge : C(I, {w : ℂ // w ≠ 0}) :=
    ⟨fun s ↦ H (0, s), by
      fun_prop⟩
  have hleft_zero :
      leftEdge 0 =
        (⟨Complex.exp (Complex.log (γ₀ 0 - a)),
          Complex.exp_ne_zero (Complex.log (γ₀ 0 - a))⟩ : {w : ℂ // w ≠ 0}) := by
    have hγ0a : γ₀ 0 - a ≠ 0 := by
      intro hEq
      exact (not_mem_range_left_of_closedPathHomotopicIn_compl_singleton hγ)
        ⟨0, sub_eq_zero.mp hEq ▸ by simp⟩
    apply Subtype.ext
    simpa [leftEdge, H, F.apply_zero, γ₀.source] using (Complex.exp_log hγ0a).symm
  let leftLift : C(I, ℂ) :=
    Complex.isCoveringMap_exp.liftPath leftEdge (Complex.log (γ₀ 0 - a)) hleft_zero
  have hleftLift :
      (fun z : ℂ ↦ (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {w : ℂ // w ≠ 0})) ∘ leftLift =
        leftEdge :=
    Complex.isCoveringMap_exp.liftPath_lifts leftEdge _ hleft_zero
  let W : C(I × I, ℂ) := Complex.isCoveringMap_exp.liftHomotopy H leftLift (by
    intro s
    simpa [leftEdge] using (congr_fun hleftLift s).symm)
  have hW :
      (fun z : ℂ ↦ (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {w : ℂ // w ≠ 0})) ∘ W = H :=
    Complex.isCoveringMap_exp.liftHomotopy_lifts H leftLift (by
      intro s
      simpa [leftEdge] using (congr_fun hleftLift s).symm)
  have hjump :
      W (1, 1) - W (0, 1) = W (1, 0) - W (0, 0) :=
    liftEndpointDifference_eq_of_closedSquare H hclosed W hW 1
  let bottomLift : C(I, ℂ) :=
    ⟨fun t ↦ W (t, 0), by
      fun_prop⟩
  let topLift : C(I, ℂ) :=
    ⟨fun t ↦ W (t, 1), by
      fun_prop⟩
  have hbottom_exp : ∀ t : I, Complex.exp (bottomLift t) = γ₀ t - a := by
    intro t
    have ht : Complex.exp (W (t, 0)) = (H (t, 0)).1 := by
      simpa using congrArg Subtype.val (congr_fun hW (t, 0))
    simpa [bottomLift, H, F.apply_zero t] using ht
  have htop_exp : ∀ t : I, Complex.exp (topLift t) = γ₁ t - a := by
    intro t
    have ht : Complex.exp (W (t, 1)) = (H (t, 1)).1 := by
      simpa using congrArg Subtype.val (congr_fun hW (t, 1))
    simpa [topLift, H, F.apply_one t] using ht
  have hindex_bottom :
      γ₀.closedPathIndexAt a (not_mem_range_left_of_closedPathHomotopicIn_compl_singleton hγ) =
        (bottomLift 1 - bottomLift 0) / (((2 * Real.pi : ℂ) * Complex.I)) := by
    simpa [Path.closedPathIndexAt_def] using
      closedPathIndex_eq_endpoint_log_lift_difference γ₀
        ⟨a, not_mem_range_left_of_closedPathHomotopicIn_compl_singleton hγ⟩ bottomLift
        hγ₀_piecewise hγ₀_integrable hbottom_exp
  have hindex_top :
      γ₁.closedPathIndexAt a (not_mem_range_right_of_closedPathHomotopicIn_compl_singleton hγ) =
        (topLift 1 - topLift 0) / (((2 * Real.pi : ℂ) * Complex.I)) := by
    simpa [Path.closedPathIndexAt_def] using
      closedPathIndex_eq_endpoint_log_lift_difference γ₁
        ⟨a, not_mem_range_right_of_closedPathHomotopicIn_compl_singleton hγ⟩ topLift
        hγ₁_piecewise hγ₁_integrable htop_exp
  -- The lifted-square helper shows that the logarithmic endpoint jump is the same on the two
  -- horizontal edges, so the normalized index values agree.
  calc
    γ₀.closedPathIndexAt a (not_mem_range_left_of_closedPathHomotopicIn_compl_singleton hγ) =
      (bottomLift 1 - bottomLift 0) / (((2 * Real.pi : ℂ) * Complex.I)) := hindex_bottom
    _ = (topLift 1 - topLift 0) / (((2 * Real.pi : ℂ) * Complex.I)) := by
      simp [bottomLift, topLift, hjump]
    _ = γ₁.closedPathIndexAt a (not_mem_range_right_of_closedPathHomotopicIn_compl_singleton hγ) :=
      hindex_top.symm

-- Proof sketch: for each puncture `a` off the image of `γ`, choose a small open disc disjoint from
-- `Set.range γ`; any other puncture in that disc is joined to `a` by a straight-line homotopy that
-- keeps the path away from the varying center, so clause (1) gives local constancy.
/-- Remark II.1-extra-17 (2): for a fixed closed path, the index is a locally constant function of
the puncture on the complement of the image. -/
theorem isLocallyConstant_closedPathIndex {z : ℂ} (γ : Path z z)
    (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hγ_integrable : ∀ a : {w : ℂ // w ∉ Set.range γ},
      CurveIntegrable (indexForm a.1) γ) :
    IsLocallyConstant (fun a : {w : ℂ // w ∉ Set.range γ} ↦ closedPathIndex γ a) := by
  have hclosed_range : IsClosed (Set.range γ) :=
    (isCompact_range γ.continuous).isClosed
  rw [IsLocallyConstant.iff_exists_open]
  intro a
  rcases Metric.isOpen_iff.mp hclosed_range.isOpen_compl a.1 a.2 with ⟨r, hr_pos, hr_subset⟩
  refine ⟨Subtype.val ⁻¹' Metric.ball a.1 r,
    continuous_subtype_val.isOpen_preimage _ Metric.isOpen_ball, ?_, ?_⟩
  · simpa using hr_pos
  · intro b hb
    have hb_ball : b.1 ∈ Metric.ball a.1 r := hb
    have hseg :
        segment ℝ a.1 b.1 ⊆ (Set.range γ)ᶜ := by
      refine Set.Subset.trans ?_ hr_subset
      exact (convex_ball a.1 r).segment_subset (Metric.mem_ball_self hr_pos) hb_ball
    -- The segment between nearby punctures stays in the range complement, so the center-variation
    -- helper identifies their indices.
    exact (closedPathIndex_eq_of_segment_subset_compl_range γ a b hγ_piecewise
      (hγ_integrable a) (hγ_integrable b) hseg).symm

-- Proof sketch: apply the locally constant result from clause (2) to the connected component of
-- `a`; locally constant functions are constant on connected components.
/-- Remark II.1-extra-17 (3): for a fixed closed path, the index is constant on each connected
component of the complement of the image. -/
theorem closedPathIndex_eq_of_mem_connectedComponent {z : ℂ} (γ : Path z z)
    (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hγ_integrable : ∀ a : {w : ℂ // w ∉ Set.range γ},
      CurveIntegrable (indexForm a.1) γ)
    {a b : {w : ℂ // w ∉ Set.range γ}} (hb : b ∈ connectedComponent a) :
    closedPathIndex γ b = closedPathIndex γ a := by
  -- Clause (2) makes the index locally constant on the puncture complement, hence constant on
  -- every connected component.
  exact (isLocallyConstant_closedPathIndex γ hγ_piecewise hγ_integrable).apply_eq_of_isPreconnected
    isPreconnected_connectedComponent hb mem_connectedComponent

-- Proof sketch: the simply connectedness of `D` makes `γ` null-homotopic within `D`; since
-- `a ∉ D`, that homotopy avoids `a`, so clause (1) reduces the index to the constant loop, whose
-- logarithmic integral is zero.
/-- Remark II.1-extra-17 (4): if the image of a closed path is contained in a simply connected set
avoiding `a`, then the index with respect to `a` is zero. -/
theorem closedPathIndex_eq_zero_of_range_subset_isSimplyConnected
    {z : ℂ} {γ : Path z z} {D : Set ℂ} (hD : IsSimplyConnected D)
    (hγD : Set.range γ ⊆ D) (a : ℂ) (haD : a ∉ D)
    (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hγ_integrable : CurveIntegrable (indexForm a) γ) :
    γ.closedPathIndexAt a (γ.not_mem_range_of_range_subset hγD haD) = 0 := by
  have hzD : z ∈ D := hγD ⟨0, by simp⟩
  obtain ⟨F, hF⟩ :=
    (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hD).2 z γ
      (fun t ↦ hγD ⟨t, rfl⟩)
  have hγ_homotopic : ClosedPathHomotopicIn ({a} : Set ℂ)ᶜ γ (Path.refl z) := by
    refine ⟨{ toHomotopy := F.toHomotopy, prop' := ?_ }⟩
    intro t
    rw [isClosedPathIn_compl_iff]
    constructor
    · exact (F.eval t).isClosedPath
    · intro s
      change F (t, s) ≠ a
      intro hEq
      exact haD (hEq ▸ hF (t, s))
  have hrefl_not_mem : a ∉ Set.range (Path.refl z) := by
    rintro ⟨t, ht⟩
    exact haD (by simpa [Path.refl] using ht.symm ▸ hzD)
  have hindex :=
    closedPathIndex_eq_of_homotopic_avoiding_point hγ_homotopic
      hγ_piecewise (Path.isPiecewiseDifferentiable_refl z) hγ_integrable
      (CurveIntegrable.refl (indexForm a) z)
  -- The null-homotopy reduces the loop to the constant loop, whose index integral is zero.
  calc
    γ.closedPathIndexAt a (γ.not_mem_range_of_range_subset hγD haD) =
      (Path.refl z).closedPathIndexAt a hrefl_not_mem := hindex
    _ = 0 := by
      simp [closedPathIndex_def]

-- Proof sketch: choose an open disc centered at the origin whose radius is strictly between `r`
-- and `‖a‖`; it is simply connected, contains the image of the standard circle, and avoids `a`, so
-- clause (4) gives index `0`.
/-- Remark II.1-extra-17 (5): the positively oriented standard circle has index `0` at every point
outside the closed disc that it bounds. -/
theorem closedPathIndex_standardCircle_eq_zero_of_not_mem_closedBall
    (r : NNReal)
    (a : ℂ) (ha : a ∉ Metric.closedBall (0 : ℂ) (r : ℝ))
    (hcircle_piecewise : (standardCirclePath r).IsPiecewiseDifferentiable)
    (hcircle_integrable : CurveIntegrable (indexForm a) (standardCirclePath r)) :
    (standardCirclePath r).closedPathIndexAt a
      (standardCirclePath_not_mem_range_of_not_mem_closedBall r ha) = 0 :=
  by
  have hr_lt : (r : ℝ) < ‖a‖ := by
    by_contra hle
    exact ha (by simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hle)
  have hnorm_pos : 0 < ‖a‖ := lt_of_le_of_lt r.2 hr_lt
  let D : Set ℂ := Metric.ball (0 : ℂ) ‖a‖
  have hzero_mem : (0 : ℂ) ∈ D := by
    simpa [D, Metric.mem_ball] using hnorm_pos
  have hD_sc : IsSimplyConnected D := by
    letI : ContractibleSpace D := (convex_ball (0 : ℂ) ‖a‖).contractibleSpace ⟨0, hzero_mem⟩
    exact (inferInstance : SimplyConnectedSpace D)
  have hcircleD : Set.range (standardCirclePath r) ⊆ D := by
    rintro _ ⟨t, rfl⟩
    simp [D, Metric.mem_ball, dist_eq_norm, sub_zero, standardCirclePath_apply,
      norm_circleMap_zero, hr_lt]
  have haD : a ∉ D := by
    simp [D, Metric.mem_ball, dist_eq_norm, sub_zero]
  -- The standard circle lies in a simply connected ball that still omits the exterior point `a`.
  exact closedPathIndex_eq_zero_of_range_subset_isSimplyConnected hD_sc hcircleD a haD
    hcircle_piecewise hcircle_integrable

/-- Helper for Cartan section05 0027_Remark_II_1_extra_17: the positively oriented standard circle
has winding index `1` about the origin when its radius is positive. -/
theorem standardCirclePath_hasIndexAt_zero_one (r : NNReal) (hr : 0 < (r : ℝ)) :
    (standardCirclePath r).HasIndexAt 0 1 := by
  let w : C(I, ℂ) :=
    ⟨fun t ↦ Complex.log (r : ℂ) + ((2 * Real.pi * (t : ℝ)) : ℂ) * Complex.I, by
      fun_prop⟩
  refine ⟨w, ?_, ?_⟩
  · intro t
    -- The explicit logarithm branch follows the standard circle parametrization.
    calc
      Complex.exp (w t) =
        Complex.exp (Complex.log (r : ℂ)) *
          Complex.exp (((2 * Real.pi * (t : ℝ)) : ℂ) * Complex.I) := by
            simp [w, Complex.exp_add]
      _ = (r : ℂ) * Complex.exp (((2 * Real.pi * (t : ℝ)) : ℂ) * Complex.I) := by
            rw [Complex.exp_log]
            exact_mod_cast ne_of_gt hr
      _ = standardCirclePath r t := by
            simp [standardCirclePath_apply, circleMap]
      _ = standardCirclePath r t - 0 := by
            ring
  · -- The logarithm branch accumulates one period `2π i` over the full traversal.
    calc
      w 1 = Complex.log (r : ℂ) + ((2 * Real.pi : ℂ) * Complex.I) := by
        simp [w]
      _ =
          (Complex.log (r : ℂ) + ((0 : ℂ) * Complex.I)) +
            ((2 * Real.pi : ℂ) * (1 : ℂ)) * Complex.I := by
              ring
      _ = w 0 + ((2 * Real.pi : ℂ) * ((1 : ℤ) : ℂ)) * Complex.I := by
        simp [w]

-- Proof sketch: the open disc bounded by the standard circle is connected, and clause (2) makes
-- the index locally constant there; it therefore suffices to evaluate at the center `0`, where the
-- direct circle computation gives the value `1`.
/-- Remark II.1-extra-17 (6): the positively oriented standard circle has index `1` at every point
inside the open disc that it bounds. -/
theorem closedPathIndex_standardCircle_eq_one_of_mem_ball
    (r : NNReal)
    (a : ℂ) (ha : a ∈ Metric.ball (0 : ℂ) (r : ℝ))
    (hcircle_piecewise : (standardCirclePath r).IsPiecewiseDifferentiable)
    (hcircle_integrable_center : CurveIntegrable (indexForm 0) (standardCirclePath r))
    (hcircle_integrable_a : CurveIntegrable (indexForm a) (standardCirclePath r)) :
    (standardCirclePath r).closedPathIndexAt a
      (standardCirclePath_not_mem_range_of_mem_ball r ha) = 1 :=
  by
  have hr_pos : 0 < (r : ℝ) := by
    have ha_norm : ‖a‖ < (r : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using ha
    exact lt_of_le_of_lt (norm_nonneg a) ha_norm
  have hzero_mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (r : ℝ) := by
    simpa [Metric.mem_ball] using hr_pos
  let center : {w : ℂ // w ∉ Set.range (standardCirclePath r)} :=
    ⟨0, standardCirclePath_not_mem_range_of_mem_ball r hzero_mem⟩
  let centerToA : {w : ℂ // w ∉ Set.range (standardCirclePath r)} :=
    ⟨a, standardCirclePath_not_mem_range_of_mem_ball r ha⟩
  have hball_subset :
      Metric.ball (0 : ℂ) (r : ℝ) ⊆ (Set.range (standardCirclePath r))ᶜ := by
    intro z hz
    exact standardCirclePath_not_mem_range_of_mem_ball r hz
  have hseg :
      segment ℝ center.1 centerToA.1 ⊆ (Set.range (standardCirclePath r))ᶜ := by
    refine Set.Subset.trans ?_ hball_subset
    exact (convex_ball (0 : ℂ) (r : ℝ)).segment_subset hzero_mem ha
  have hcenter_eq :
      closedPathIndex (standardCirclePath r) center =
        closedPathIndex (standardCirclePath r) centerToA :=
    closedPathIndex_eq_of_segment_subset_compl_range (standardCirclePath r) center centerToA
      hcircle_piecewise hcircle_integrable_center hcircle_integrable_a hseg
  have hcenter_index :
      closedPathIndex (standardCirclePath r) center = 1 := by
    have hHasIndex : (standardCirclePath r).HasIndexAt 0 1 :=
      standardCirclePath_hasIndexAt_zero_one r hr_pos
    simpa [center, Path.closedPathIndexAt_def] using
      hHasIndex.closedPathIndex_eq hcircle_piecewise hcircle_integrable_center
  -- Move the puncture from the center to `a` inside the disc, then use the explicit center value.
  simpa [centerToA, Path.closedPathIndexAt_def] using hcenter_eq.symm.trans hcenter_index

/-- Summary of Remark II.1-extra-17: the index is invariant
under homotopies through closed paths avoiding the puncture, locally constant on the puncture
complement, constant on each connected component of that complement, zero on loops contained in a
simply connected domain avoiding the puncture, and for the positively oriented standard circle it
is `0` outside the bounded closed disc and `1` inside the bounded open disc. -/
theorem closedPathIndex_basicProperties :
    (∀ {z₀ z₁ a : ℂ} {γ₀ : Path z₀ z₀} {γ₁ : Path z₁ z₁},
      ∀ hγ : ClosedPathHomotopicIn ({a} : Set ℂ)ᶜ γ₀ γ₁,
        γ₀.IsPiecewiseDifferentiable →
          γ₁.IsPiecewiseDifferentiable →
            CurveIntegrable (indexForm a) γ₀ →
              CurveIntegrable (indexForm a) γ₁ →
                γ₀.closedPathIndexAt a
                    (not_mem_range_left_of_closedPathHomotopicIn_compl_singleton hγ) =
                  γ₁.closedPathIndexAt a
                    (not_mem_range_right_of_closedPathHomotopicIn_compl_singleton hγ)) ∧
    (∀ {z : ℂ} (γ : Path z z),
      γ.IsPiecewiseDifferentiable →
        (∀ a : {w : ℂ // w ∉ Set.range γ}, CurveIntegrable (indexForm a.1) γ) →
          IsLocallyConstant (fun a : {w : ℂ // w ∉ Set.range γ} ↦ closedPathIndex γ a)) ∧
    (∀ {z : ℂ} (γ : Path z z),
      γ.IsPiecewiseDifferentiable →
        (∀ a : {w : ℂ // w ∉ Set.range γ}, CurveIntegrable (indexForm a.1) γ) →
          ∀ {a b : {w : ℂ // w ∉ Set.range γ}},
            b ∈ connectedComponent a → closedPathIndex γ b = closedPathIndex γ a) ∧
    (∀ {z : ℂ} {γ : Path z z} {D : Set ℂ}, IsSimplyConnected D →
      ∀ hγD : Set.range γ ⊆ D, ∀ a : ℂ, ∀ haD : a ∉ D,
        γ.IsPiecewiseDifferentiable →
          CurveIntegrable (indexForm a) γ →
            γ.closedPathIndexAt a (γ.not_mem_range_of_range_subset hγD haD) = 0) ∧
    (∀ (r : NNReal) (a : ℂ), ∀ ha : a ∉ Metric.closedBall (0 : ℂ) (r : ℝ),
      (standardCirclePath r).IsPiecewiseDifferentiable →
        CurveIntegrable (indexForm a) (standardCirclePath r) →
          (standardCirclePath r).closedPathIndexAt a
            (standardCirclePath_not_mem_range_of_not_mem_closedBall r ha) = 0) ∧
    (∀ (r : NNReal) (a : ℂ), ∀ ha : a ∈ Metric.ball (0 : ℂ) (r : ℝ),
      (standardCirclePath r).IsPiecewiseDifferentiable →
        CurveIntegrable (indexForm 0) (standardCirclePath r) →
          CurveIntegrable (indexForm a) (standardCirclePath r) →
            (standardCirclePath r).closedPathIndexAt a
              (standardCirclePath_not_mem_range_of_mem_ball r ha) = 1) := by
  -- Package the clause-level proofs under the exact item label expected by the item pipeline.
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩⟩⟩
  · intro z₀ z₁ a γ₀ γ₁ hγ hγ₀_piecewise hγ₁_piecewise hγ₀_integrable hγ₁_integrable
    exact closedPathIndex_eq_of_homotopic_avoiding_point hγ hγ₀_piecewise hγ₁_piecewise
      hγ₀_integrable hγ₁_integrable
  · intro z γ hγ_piecewise hγ_integrable
    exact isLocallyConstant_closedPathIndex γ hγ_piecewise hγ_integrable
  · intro z γ hγ_piecewise hγ_integrable a b hb
    exact closedPathIndex_eq_of_mem_connectedComponent γ hγ_piecewise hγ_integrable hb
  · intro z γ D hD hγD a haD hγ_piecewise hγ_integrable
    exact closedPathIndex_eq_zero_of_range_subset_isSimplyConnected hD hγD a haD
      hγ_piecewise hγ_integrable
  · intro r a ha hcircle_piecewise hcircle_integrable
    exact closedPathIndex_standardCircle_eq_zero_of_not_mem_closedBall r a ha hcircle_piecewise
      hcircle_integrable
  · intro r a ha hcircle_piecewise hcircle_integrable_center hcircle_integrable_a
    exact closedPathIndex_standardCircle_eq_one_of_mem_ball r a ha hcircle_piecewise
      hcircle_integrable_center hcircle_integrable_a
