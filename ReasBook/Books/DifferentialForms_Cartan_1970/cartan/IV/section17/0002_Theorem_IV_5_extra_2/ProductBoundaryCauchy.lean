import DifferentialForms_Cartan_1970.cartan.IV.section17.«0002_Theorem_IV_5_extra_2».LocalSeriesBounds

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: on a fixed boundary circle in the last
coordinate, the lower-dimensional induction hypothesis already gives joint analyticity of the
corresponding block slice on the interior block ball. -/
lemma prodBoundaryBlockSlices_analyticOnNhd_ball
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {ρ : ℝ}
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2) :
    ∀ ζ ∈ Metric.sphere p.2 (ρ / 2),
      AnalyticOnNhd ℂ (fun x ↦ G (x, ζ)) (Metric.ball p.1 (ρ / 2)) := by
  intro ζ hζ
  -- Freeze the boundary value `ζ` and apply the induction hypothesis on the block ball.
  refine ih Metric.isOpen_ball ?_
  intro x hx i
  have hq : (x, ζ) ∈ D := hcyl ⟨hx, Metric.sphere_subset_closedBall hζ⟩
  have hBlockAt : AnalyticAt ℂ (fun y : Fin (m + 1) → ℂ ↦ G (y, ζ)) x := (hsep (x, ζ) hq).1
  have hUpdateAt : AnalyticAt ℂ (fun w : ℂ ↦ Function.update x i w) (x i) := by
    simpa [Function.update] using (analyticAt_update_coordinate x i)
  have hUpdateCenter : (fun w : ℂ ↦ Function.update x i w) (x i) = x := by
    simp
  -- Compose the block germ with the coordinate insertion once, so `ih` sees the expected slice.
  simpa using
    hBlockAt.comp_of_eq (f := fun w : ℂ ↦ Function.update x i w) (x := x i)
      hUpdateAt hUpdateCenter

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: on the smaller closed block ball, the
last-variable boundary slices are continuous on the distinguished boundary circle. -/
lemma prodBoundarySlice_continuousOn_sphere_closedBall
    {m : ℕ}
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D) :
    ∀ x ∈ Metric.closedBall p.1 (ρ / 8),
      ContinuousOn (fun ζ ↦ G (x, ζ)) (Metric.sphere p.2 (ρ / 2)) := by
  intro x hx
  have hρeighth_lt_half : ρ / 8 < ρ / 2 := by
    linarith
  have hxBall : x ∈ Metric.ball p.1 (ρ / 2) := Metric.closedBall_subset_ball hρeighth_lt_half hx
  -- Pointwise analyticity on the boundary circle immediately gives the continuity owner there.
  refine continuousOn_of_forall_analyticAt ?_
  intro ζ hζ
  have hq : (x, ζ) ∈ D := hcyl ⟨hxBall, Metric.sphere_subset_closedBall hζ⟩
  exact (hsep (x, ζ) hq).2

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: on the smaller closed block ball,
every fixed boundary value in the last coordinate gives a continuous block slice. -/
lemma prodBoundaryBlockSlice_continuousOn_closedBall
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2) :
    ∀ ζ ∈ Metric.sphere p.2 (ρ / 2),
      ContinuousOn (fun x ↦ G (x, ζ)) (Metric.closedBall p.1 (ρ / 8)) := by
  intro ζ hζ
  have hρeighth_lt_half : ρ / 8 < ρ / 2 := by
    linarith
  have hSliceOn :
      AnalyticOnNhd ℂ (fun x ↦ G (x, ζ)) (Metric.ball p.1 (ρ / 2)) := by
    -- Freeze the boundary value `ζ` and reuse the lower-dimensional analytic owner on the block
    -- ball before restricting to the smaller compact closed ball.
    exact prodBoundaryBlockSlices_analyticOnNhd_ball
      (m := m) ih (D := D) (G := G) (p := p) (ρ := ρ) hcyl hsep ζ hζ
  -- Restrict the analytic block slice to the fixed compact closed ball used later in the Cauchy
  -- package.
  exact hSliceOn.continuousOn.mono (Metric.closedBall_subset_ball hρeighth_lt_half)

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: each fixed boundary value in the last
coordinate already gives one scalar bound on the compact closed block ball. This is the true
fiberwise boundedness owner available before any separate-to-uniform upgrade on the whole torus. -/
lemma prodBoundaryBlockSlice_norm_bounded_on_closedBall_local
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2) :
    ∀ ζ ∈ Metric.sphere p.2 (ρ / 2),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ Metric.closedBall p.1 (ρ / 8), ‖G (x, ζ)‖ ≤ C := by
  intro ζ hζ
  have hcont :
      ContinuousOn (fun x ↦ G (x, ζ)) (Metric.closedBall p.1 (ρ / 8)) :=
    prodBoundaryBlockSlice_continuousOn_closedBall
      (m := m) ih (D := D) (G := G) (p := p) (ρ := ρ) hρpos hcyl hsep ζ hζ
  obtain ⟨C, hCbound⟩ :=
    (isCompact_closedBall p.1 (ρ / 8)).exists_bound_of_continuousOn
      (f := fun x ↦ G (x, ζ)) hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  -- Restrict the compact closed-ball bound to the chosen block point and discard negative slack.
  exact le_trans (hCbound x hx) (le_max_left _ _)

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: each fixed block point on the compact
closed ball already gives one scalar bound on the distinguished boundary circle in the last
coordinate. -/
lemma prodBoundaryLastSlice_norm_bounded_on_sphere_local
    {m : ℕ}
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2) :
    ∀ x ∈ Metric.closedBall p.1 (ρ / 8),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ ζ ∈ Metric.sphere p.2 (ρ / 2), ‖G (x, ζ)‖ ≤ C := by
  intro x hx
  have hcont :
      ContinuousOn (fun ζ ↦ G (x, ζ)) (Metric.sphere p.2 (ρ / 2)) :=
    prodBoundarySlice_continuousOn_sphere_closedBall
      (m := m) (D := D) (G := G) (p := p) (ρ := ρ) hρpos hsep hcyl x hx
  obtain ⟨C, hCbound⟩ :=
    (isCompact_sphere p.2 (ρ / 2)).exists_bound_of_continuousOn
      (f := fun ζ ↦ G (x, ζ)) hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro ζ hζ
  -- Restrict the compact circle bound to the chosen boundary value and discard negative slack.
  exact le_trans (hCbound ζ hζ) (le_max_left _ _)

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: on the compact torus used by the local
Cauchy package, both families of boundary sections are already continuous without invoking the
blocked joint-continuity theorem. -/
lemma prodBoundarySlices_separatelyContinuousOn_torus_local
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2) :
    (∀ ζ ∈ Metric.sphere p.2 (ρ / 2),
        ContinuousOn (fun x ↦ G (x, ζ)) (Metric.closedBall p.1 (ρ / 8))) ∧
      ∀ x ∈ Metric.closedBall p.1 (ρ / 8),
        ContinuousOn (fun ζ ↦ G (x, ζ)) (Metric.sphere p.2 (ρ / 2)) := by
  constructor
  · intro ζ hζ
    -- The block sections are continuous on the compact block closed ball because the induction
    -- hypothesis already gives analyticity on the larger open block ball.
    exact prodBoundaryBlockSlice_continuousOn_closedBall
      (m := m) ih (D := D) (G := G) (p := p) (ρ := ρ) hρpos hcyl hsep ζ hζ
  · intro x hx
    -- The last-variable sections are continuous on the boundary circle by one-variable
    -- analyticity on the enclosing cylinder.
    exact prodBoundarySlice_continuousOn_sphere_closedBall
      (m := m) (D := D) (G := G) (p := p) (ρ := ρ) hρpos hsep hcyl x hx

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: the block-coordinate members of the
compact torus continuity package can be consumed directly without unpacking the paired statement
by hand. -/
lemma prodBoundaryBlockSlices_continuousOn_torus_local
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2) :
    ∀ ζ ∈ Metric.sphere p.2 (ρ / 2),
      ContinuousOn (fun x ↦ G (x, ζ)) (Metric.closedBall p.1 (ρ / 8)) := by
  -- Read off the block-slice half of the paired torus continuity package.
  exact
    (prodBoundarySlices_separatelyContinuousOn_torus_local
      (m := m) ih (D := D) (G := G) (p := p) (ρ := ρ) hρpos hcyl hsep).1

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: the last-coordinate members of the
compact torus continuity package can likewise be consumed directly when the proof only needs the
circle slices. -/
lemma prodBoundaryLastSlices_continuousOn_torus_local
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2) :
    ∀ x ∈ Metric.closedBall p.1 (ρ / 8),
      ContinuousOn (fun ζ ↦ G (x, ζ)) (Metric.sphere p.2 (ρ / 2)) := by
  -- Read off the last-slice half of the paired torus continuity package.
  exact
    (prodBoundarySlices_separatelyContinuousOn_torus_local
      (m := m) ih (D := D) (G := G) (p := p) (ρ := ρ) hρpos hcyl hsep).2

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: the actual boundary family on
`Metric.closedBall p.1 (ρ / 8) ×ˢ Metric.sphere p.2 (ρ / 2)` needs only one compact scalar norm
budget for the later Cauchy coefficient package. -/
lemma prodBoundarySlices_norm_bounded_on_closedBallSphere_of_continuousOn_local
    {m : ℕ}
    {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {ρ : ℝ}
    (hcont :
      ContinuousOn (Function.uncurry fun x ζ ↦ G (x, ζ))
        (Metric.closedBall p.1 (ρ / 8) ×ˢ Metric.sphere p.2 (ρ / 2))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Metric.closedBall p.1 (ρ / 8),
        ∀ ζ ∈ Metric.sphere p.2 (ρ / 2), ‖G (x, ζ)‖ ≤ C := by
  let K : Set ((Fin (m + 1) → ℂ) × ℂ) :=
    Metric.closedBall p.1 (ρ / 8) ×ˢ Metric.sphere p.2 (ρ / 2)
  have hK : IsCompact K := by
    -- The boundary torus is compact because both the closed block ball and the boundary circle are.
    exact (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hnormCont : ContinuousOn (fun q : ((Fin (m + 1) → ℂ) × ℂ) ↦ ‖G q‖) K := by
    -- Convert the joint continuity owner for `G` into the corresponding norm-continuity owner on
    -- the same compact torus.
    have hGCont : ContinuousOn (fun q : ((Fin (m + 1) → ℂ) × ℂ) ↦ G q) K := by
      simpa [Function.uncurry, K] using hcont
    exact continuous_norm.continuousOn.comp hGCont (by
      intro q hq
      exact Set.mem_univ _)
  have hImageCompact :
      IsCompact ((fun q : ((Fin (m + 1) → ℂ) × ℂ) ↦ ‖G q‖) '' K) :=
    hK.image_of_continuousOn hnormCont
  rcases hImageCompact.bddAbove with ⟨C, hCbound⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx ζ hζ
  -- Evaluate the compact sup bound at the chosen torus point and discard any negative slack.
  have hmem :
      ‖G (x, ζ)‖ ∈ (fun q : ((Fin (m + 1) → ℂ) × ℂ) ↦ ‖G q‖) '' K := by
    refine ⟨(x, ζ), ?_, rfl⟩
    simpa [K] using And.intro hx hζ
  exact le_trans (hCbound hmem) (le_max_left _ _)

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: the actual boundary family on
`Metric.closedBall p.1 (ρ / 8) ×ˢ Metric.sphere p.2 (ρ / 2)` needs only one compact scalar norm
budget for the later Cauchy coefficient package. -/
lemma prodBoundarySlices_norm_bounded_on_closedBallSphere_local
    {m : ℕ} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {ρ : ℝ}
    (hcont :
      ContinuousOn (Function.uncurry fun x ζ ↦ G (x, ζ))
        (Metric.closedBall p.1 (ρ / 8) ×ˢ Metric.sphere p.2 (ρ / 2))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Metric.closedBall p.1 (ρ / 8),
        ∀ ζ ∈ Metric.sphere p.2 (ρ / 2), ‖G (x, ζ)‖ ≤ C := by
  -- Route correction: the dead separate-continuity upgrade has been deleted. This helper now
  -- consumes the explicit compact-torus continuity package that the actual coefficient estimate
  -- needs.
  exact
    prodBoundarySlices_norm_bounded_on_closedBallSphere_of_continuousOn_local
      (m := m) (G := G) (p := p) (ρ := ρ) hcont

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: once the actual boundary family has a
single scalar norm budget on the compact torus
`Metric.closedBall p.1 (ρ / 8) ×ˢ Metric.sphere p.2 (ρ / 2)`, the corresponding last-variable
`cauchyPowerSeries` coefficients satisfy the expected geometric bound uniformly on the smaller
closed block ball. -/
lemma prodBoundaryCoeffBound_of_boundaryNormBound_local
    {m : ℕ}
    {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {ρ C : ℝ}
    (hρpos : 0 < ρ)
    (hbound :
      ∀ x ∈ Metric.closedBall p.1 (ρ / 8),
        ∀ ζ ∈ Metric.sphere p.2 (ρ / 2), ‖G (x, ζ)‖ ≤ C) :
    ∀ x ∈ Metric.closedBall p.1 (ρ / 8), ∀ n : ℕ,
      ‖(cauchyPowerSeries (fun ζ ↦ G (x, ζ)) p.2 (ρ / 2)).coeff n‖ ≤
        C / (ρ / 2 : ℝ) ^ n := by
  intro x hx n
  -- Freeze the block point `x` and feed the torus norm budget directly into the scalar Cauchy
  -- coefficient estimate on the boundary circle of radius `ρ / 2`.
  exact
    cauchyPowerSeries_coeff_norm_le_div_pow_of_bound_on_circle
      (u0 := p.2) (R := ρ / 2) (M := C) (F := fun ζ ↦ G (x, ζ))
      (by positivity) (fun ζ hζ ↦ hbound x hx ζ hζ) n

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: the remaining product-coordinate
coefficient package only needs one compact-torus norm bound; once that bound is available, the
uniform geometric Cauchy estimate is immediate. -/
lemma prodBoundaryCoeff_uniformBoundOnClosedBall_local
    {m : ℕ}
    {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hbound :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ Metric.closedBall p.1 (ρ / 8),
          ∀ ζ ∈ Metric.sphere p.2 (ρ / 2), ‖G (x, ζ)‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Metric.closedBall p.1 (ρ / 8), ∀ n : ℕ,
        ‖(cauchyPowerSeries (fun ζ ↦ G (x, ζ)) p.2 (ρ / 2)).coeff n‖ ≤
          C / (ρ / 2 : ℝ) ^ n := by
  rcases hbound with ⟨C, hCnonneg, hCbound⟩
  refine ⟨C, hCnonneg, ?_⟩
  -- Reuse the fixed-budget coefficient estimate pointwise on the smaller closed block ball.
  exact prodBoundaryCoeffBound_of_boundaryNormBound_local
    (m := m) (G := G) (p := p) (ρ := ρ) (C := C) hρpos hCbound

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: once the boundary family is jointly
continuous on the compact torus, the last-variable `cauchyPowerSeries` coefficients inherit one
uniform geometric bound on the smaller closed block ball. -/
lemma prodBoundaryCoeff_uniformBound_of_continuousOn_local
    {m : ℕ}
    {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcont :
      ContinuousOn (Function.uncurry fun x ζ ↦ G (x, ζ))
        (Metric.closedBall p.1 (ρ / 8) ×ˢ Metric.sphere p.2 (ρ / 2))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Metric.closedBall p.1 (ρ / 8), ∀ n : ℕ,
        ‖(cauchyPowerSeries (fun ζ ↦ G (x, ζ)) p.2 (ρ / 2)).coeff n‖ ≤
          C / (ρ / 2 : ℝ) ^ n := by
  rcases prodBoundarySlices_norm_bounded_on_closedBallSphere_of_continuousOn_local
      (m := m) (G := G) (p := p) (ρ := ρ) hcont with
    ⟨C, hCnonneg, hCbound⟩
  -- Freeze the compact torus norm budget and feed it into the existing scalar Cauchy adapter.
  exact prodBoundaryCoeff_uniformBoundOnClosedBall_local
    (m := m) (G := G) (p := p) (ρ := ρ) hρpos ⟨C, hCnonneg, hCbound⟩

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: despite the historical name, this
coefficient package now takes the explicit compact-torus continuity owner directly; once that
continuity is available, the scalar Cauchy estimate applies unchanged. -/
lemma prodBoundaryCoeff_uniformBound_of_separateContinuity_local
    {m : ℕ} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcont :
      ContinuousOn (Function.uncurry fun x ζ ↦ G (x, ζ))
        (Metric.closedBall p.1 (ρ / 8) ×ˢ Metric.sphere p.2 (ρ / 2))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Metric.closedBall p.1 (ρ / 8), ∀ n : ℕ,
        ‖(cauchyPowerSeries (fun ζ ↦ G (x, ζ)) p.2 (ρ / 2)).coeff n‖ ≤
          C / (ρ / 2 : ℝ) ^ n := by
  -- The compact torus continuity owner already packages exactly the boundary norm budget needed
  -- by the scalar Cauchy coefficient estimate.
  exact
    prodBoundaryCoeff_uniformBound_of_continuousOn_local
      (m := m) (G := G) (p := p) (ρ := ρ) hρpos hcont

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: the product-boundary coefficient
budget produced on the `ρ / 8` block closed ball restricts unchanged to the smaller `ρ / 16`
closed ball used by the normalized-series closeout. The compact-torus continuity owner is passed
explicitly to avoid reopening the dead separate-continuity route. -/
lemma prodBoundaryCoeff_uniformBoundOnClosedSmallBall_local
    {m : ℕ} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcont :
      ContinuousOn (Function.uncurry fun x ζ ↦ G (x, ζ))
        (Metric.closedBall p.1 (ρ / 8) ×ˢ Metric.sphere p.2 (ρ / 2))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Metric.closedBall p.1 ((ρ / 8) / 2), ∀ n : ℕ,
        ‖(cauchyPowerSeries (fun ζ ↦ G (x, ζ)) p.2 (ρ / 2)).coeff n‖ ≤
          C / (ρ / 2 : ℝ) ^ n := by
  rcases prodBoundaryCoeff_uniformBound_of_separateContinuity_local
      (m := m) (G := G) (p := p) (ρ := ρ) hρpos hcont with
    ⟨C, hCnonneg, hCbound⟩
  refine ⟨C, hCnonneg, ?_⟩
  intro x hx n
  have hxLarge : x ∈ Metric.closedBall p.1 (ρ / 8) := by
    -- The normalized-series closeout only shrinks the block closed ball, so the larger product
    -- boundary coefficient budget applies without any further analytic work.
    have hxle : dist x p.1 ≤ (ρ / 8) / 2 := by
      simpa [Metric.mem_closedBall] using hx
    have hxle' : dist x p.1 ≤ ρ / 8 := by
      linarith
    simpa [Metric.mem_closedBall] using hxle'
  exact hCbound x hxLarge n

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: the compact torus used for the local
boundary Cauchy package sits inside the ambient product cylinder supplied by `hcyl`. -/
lemma prodBoundaryTorus_subset_domain_local
    {m : ℕ}
    {Dprod : Set ((Fin (m + 1) → ℂ) × ℂ)}
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ Dprod) :
    Metric.closedBall p.1 (ρ / 8) ×ˢ Metric.sphere p.2 (ρ / 2) ⊆ Dprod := by
  have hsmall_lt : ρ / 8 < ρ / 2 := by
    linarith
  intro q hq
  -- Shrink the block closed ball into the cylinder ball and use that every sphere point lies in
  -- the corresponding closed ball.
  exact hcyl ⟨Metric.closedBall_subset_ball hsmall_lt hq.1, Metric.sphere_subset_closedBall hq.2⟩

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: every torus point already carries the
separate analyticity package inherited from the ambient product domain. -/
lemma prodBoundarySeparateAnalyticityOnTorus_local
    {m : ℕ}
    {Dprod : Set ((Fin (m + 1) → ℂ) × ℂ)} {Gprod : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ Dprod)
    (hsepProd :
      ∀ q ∈ Dprod,
        AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ Gprod (x, q.2)) q.1 ∧
          AnalyticAt ℂ (fun w ↦ Gprod (q.1, w)) q.2) :
    ∀ q ∈ Metric.closedBall p.1 (ρ / 8) ×ˢ Metric.sphere p.2 (ρ / 2),
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ Gprod (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun w ↦ Gprod (q.1, w)) q.2 := by
  intro q hq
  -- Restrict the ambient separate analyticity package to the compact torus.
  exact hsepProd q (prodBoundaryTorus_subset_domain_local (m := m) hρpos hcyl hq)

/-- Helper for Theorem IV.5-extra-2: once the product family is already analytic on the ambient
open set, the compact-torus continuity and the uniform Cauchy coefficient bound follow by simple
restriction to the smaller closed block ball and boundary circle. -/
lemma prodBoundaryCoeff_uniformBound_of_analyticOnNhd_local
    {m : ℕ}
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    (hGOn : AnalyticOnNhd ℂ G D)
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D) :
    let w0 : ℂ := p.2
    let r0 : ℝ := ρ / 8
    let r1 : ℝ := r0 / 2
    let A : ℕ → (Fin (m + 1) → ℂ) → ℂ := fun n x ↦
      (cauchyPowerSeries (fun ζ ↦ G (x, ζ)) w0 (ρ / 2)).coeff n
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Metric.closedBall p.1 r1, ∀ n : ℕ, ‖A n x‖ ≤ C / (ρ / 2 : ℝ) ^ n := by
  let w0 : ℂ := p.2
  let r0 : ℝ := ρ / 8
  let r1 : ℝ := r0 / 2
  let A : ℕ → (Fin (m + 1) → ℂ) → ℂ := fun n x ↦
    (cauchyPowerSeries (fun ζ ↦ G (x, ζ)) w0 (ρ / 2)).coeff n
  have hr1_lt_half : r1 < ρ / 2 := by
    -- The closed block ball used by the normalized-series closeout is strictly smaller than the
    -- cylinder radius provided by the product-domain hypothesis.
    dsimp [r1, r0]
    linarith
  have hcont :
      ContinuousOn (Function.uncurry fun x ζ ↦ G (x, ζ))
        (Metric.closedBall p.1 r1 ×ˢ Metric.sphere p.2 (ρ / 2)) := by
    have hsubset :
        Metric.closedBall p.1 r1 ×ˢ Metric.sphere p.2 (ρ / 2) ⊆ D := by
      intro q hq
      refine hcyl ?_
      constructor
      · exact Metric.closedBall_subset_ball hr1_lt_half hq.1
      · exact Metric.sphere_subset_closedBall hq.2
    -- Restrict the ambient analytic owner to the compact torus used by the scalar Cauchy bound.
    simpa [Function.uncurry] using hGOn.continuousOn.mono hsubset
  obtain ⟨C, hCnonneg, hCbound⟩ :=
    cauchyPowerSeries_coeff_uniformBound_of_continuousOn_closedBall
      (x0 := p.1) (r := r1) (u0 := w0) (R := ρ / 2)
      (F := fun x ζ ↦ G (x, ζ)) (by positivity) hcont
  refine ⟨C, hCnonneg, ?_⟩
  intro x hx n
  -- Re-express the generic closed-ball Cauchy package in the local coefficient notation.
  simpa [A, w0] using hCbound x hx n

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: once the normalized product-coordinate
`cauchyPowerSeries` model is analytic at the center, the common-ball identity transfers that
analyticity back to the explicit Cauchy transform. -/
lemma prodLastCauchyTransform_jointAnalyticAt_center_ofCommonBall
    {m : ℕ} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hSeriesAt :
      AnalyticAt ℂ
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
          (cauchyPowerSeries (fun ζ ↦ G (q.1, ζ)) p.2 (ρ / 2)).sum (q.2 - p.2))
        p)
    (hSeriesEq :
      ∀ q ∈ Metric.ball p (ρ / 8),
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ ζ in C(p.2, ρ / 2), (ζ - q.2)⁻¹ • G (q.1, ζ)) =
        (cauchyPowerSeries (fun ζ ↦ G (q.1, ζ)) p.2 (ρ / 2)).sum (q.2 - p.2)) :
    AnalyticAt ℂ
      (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ ζ in C(p.2, ρ / 2), (ζ - q.2)⁻¹ • G (q.1, ζ)))
      p := by
  let normalized : (Fin (m + 1) → ℂ) × ℂ → ℂ := fun q ↦
    (cauchyPowerSeries (fun ζ ↦ G (q.1, ζ)) p.2 (ρ / 2)).sum (q.2 - p.2)
  let r0 : ℝ := ρ / 8
  have hr0pos : 0 < r0 := by
    -- Keep the common-ball radius normalized once so the congruence step uses one fixed ball.
    dsimp [r0]
    positivity
  have hNormalizedAt : AnalyticAt ℂ normalized p := by
    -- Repackage the normalized-series analyticity with the local name used in the congruence.
    simpa [normalized] using hSeriesAt
  have hpCommonBall : p ∈ Metric.ball p r0 := by
    -- The center belongs to every positive-radius ball around itself.
    simpa [Metric.mem_ball] using hr0pos
  have hEventuallyEq :
      normalized =ᶠ[nhds p]
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
          ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
            ∮ ζ in C(p.2, ρ / 2), (ζ - q.2)⁻¹ • G (q.1, ζ))) := by
    -- Route correction: the explicit transform is recovered from the normalized series by the
    -- already-proved common-ball equality, so no new transport or integral interchange is needed.
    filter_upwards [Metric.isOpen_ball.mem_nhds hpCommonBall] with q hq
    symm
    exact hSeriesEq q hq
  -- Transfer analyticity from the normalized `cauchyPowerSeries` model to the explicit integral.
  exact hNormalizedAt.congr hEventuallyEq
