import DifferentialForms_Cartan_1970.IV.section14.«0002_Definition_IV_2_extra_2»
import DifferentialForms_Cartan_1970.IV.section17.«0001_Definition_IV_5_extra_1»
import DifferentialForms_Cartan_1970.IV.section17.«0002_Theorem_IV_5_extra_2».TransportedSlices

/-- Helper for Theorem IV.5-extra-2: on a transported cylinder, the explicit last-variable Cauchy
transform agrees with the original function throughout the interior last disc. -/
lemma transportedLastCauchyTransform_eqOn_ball
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i))
    {z : Fin (m + 2) → ℂ} {r R : ℝ}
    (hcyl :
      Metric.ball ((Fin.succFunEquiv ℂ (m + 1) z).1) r ×ˢ
          Metric.closedBall ((Fin.succFunEquiv ℂ (m + 1) z).2) R ⊆
        {p | (Fin.succFunEquiv ℂ (m + 1)).symm p ∈ D}) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    let U := Metric.ball (e z).1 r
    let w0 := (e z).2
    let G : (Fin (m + 1) → ℂ) × ℂ → ℂ := fun p ↦
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ ζ in C(w0, R), (ζ - p.2)⁻¹ • g (p.1, ζ))
    ∀ x ∈ U, Set.EqOn (fun w ↦ g (x, w)) (fun w ↦ G (x, w)) (Metric.ball w0 R) := by
  dsimp
  intro x hx w hw
  have hslice :
      AnalyticOnNhd ℂ
        (fun u ↦ f ((Fin.succFunEquiv ℂ (m + 1)).symm (x, u)))
        (Metric.closedBall ((Fin.succFunEquiv ℂ (m + 1) z).2) R) :=
    transportedLastSlices_analyticOnNhd_closedBall (m := m) (D := D) (f := f) hsep hcyl x hx
  have hdiff :
      DifferentiableOn ℂ (fun u ↦ f ((Fin.succFunEquiv ℂ (m + 1)).symm (x, u)))
        (Metric.closedBall ((Fin.succFunEquiv ℂ (m + 1) z).2) R) :=
    hslice.differentiableOn
  have hdiffCl :
      DiffContOnCl ℂ (fun u ↦ f ((Fin.succFunEquiv ℂ (m + 1)).symm (x, u)))
        (Metric.ball ((Fin.succFunEquiv ℂ (m + 1) z).2) R) :=
    hdiff.diffContOnCl_ball (by intro u hu; exact hu)
  -- Evaluate the fixed-`x` last slice by the one-variable Cauchy formula on the chosen disc.
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (hdiffCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw).symm

/-- Helper for Theorem IV.5-extra-2: for each transported block point in the inner cylinder, the
explicit last-variable Cauchy transform is analytic on the whole inner last disc. -/
lemma transportedLastCauchyTransform_lastSlice_analyticOnNhd_ball
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i))
    {z : Fin (m + 2) → ℂ} {r R : ℝ}
    (hcyl :
      Metric.ball ((Fin.succFunEquiv ℂ (m + 1) z).1) r ×ˢ
          Metric.closedBall ((Fin.succFunEquiv ℂ (m + 1) z).2) R ⊆
        {p | (Fin.succFunEquiv ℂ (m + 1)).symm p ∈ D}) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    let U := Metric.ball (e z).1 r
    let w0 := (e z).2
    let G : (Fin (m + 1) → ℂ) × ℂ → ℂ := fun p ↦
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ ζ in C(w0, R), (ζ - p.2)⁻¹ • g (p.1, ζ))
    ∀ x ∈ U, AnalyticOnNhd ℂ (fun w ↦ G (x, w)) (Metric.ball w0 R) := by
  dsimp
  intro x hx w hw
  have hgAt :
      AnalyticAt ℂ (fun u ↦ f ((Fin.succFunEquiv ℂ (m + 1)).symm (x, u))) w := by
    have hslice :
        AnalyticOnNhd ℂ
          (fun u ↦ f ((Fin.succFunEquiv ℂ (m + 1)).symm (x, u)))
          (Metric.closedBall ((Fin.succFunEquiv ℂ (m + 1) z).2) R) :=
      transportedLastSlices_analyticOnNhd_closedBall
        (m := m) (D := D) (f := f) hsep hcyl x hx
    -- The transported last slice is already analytic on the whole closed disc.
    exact hslice w (Metric.mem_closedBall.mpr (le_of_lt hw))
  have hEqOn :
      Set.EqOn
        (fun u ↦ f ((Fin.succFunEquiv ℂ (m + 1)).symm (x, u)))
        (fun u ↦
          ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
            ∮ ζ in C((Fin.succFunEquiv ℂ (m + 1) z).2, R),
              (ζ - u)⁻¹ • f ((Fin.succFunEquiv ℂ (m + 1)).symm (x, ζ))))
        (Metric.ball ((Fin.succFunEquiv ℂ (m + 1) z).2) R) :=
    transportedLastCauchyTransform_eqOn_ball
      (m := m) (D := D) (f := f) hsep hcyl x hx
  -- Transfer analyticity from the transported last slice to its explicit Cauchy representation.
  exact hgAt.congr <| hEqOn.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hw)

/-- Helper for Theorem IV.5-extra-2: for each last-variable point in the inner disc, the explicit
transported Cauchy transform is analytic in the transported block variables on the inner block
ball. -/
lemma transportedLastCauchyTransform_blockSlice_analyticOnNhd_ball
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (ih :
      ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
        IsOpen D' →
        (∀ z ∈ D', ∀ i : Fin (m + 1),
          AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
        AnalyticOnNhd ℂ f' D')
    (hD : IsOpen D)
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i))
    {z : Fin (m + 2) → ℂ} {r R : ℝ}
    (hcyl :
      Metric.ball ((Fin.succFunEquiv ℂ (m + 1) z).1) r ×ˢ
          Metric.closedBall ((Fin.succFunEquiv ℂ (m + 1) z).2) R ⊆
        {p | (Fin.succFunEquiv ℂ (m + 1)).symm p ∈ D}) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    let U := Metric.ball (e z).1 r
    let w0 := (e z).2
    let G : (Fin (m + 1) → ℂ) × ℂ → ℂ := fun p ↦
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ ζ in C(w0, R), (ζ - p.2)⁻¹ • g (p.1, ζ))
    ∀ w ∈ Metric.ball w0 R, AnalyticOnNhd ℂ (fun x ↦ G (x, w)) U := by
  dsimp
  intro w hw x hx
  have hxDw : (Fin.succFunEquiv ℂ (m + 1)).symm (x, w) ∈ D := by
    refine hcyl ?_
    constructor
    · exact hx
    · exact Metric.mem_closedBall.mpr (le_of_lt hw)
  have hgAt :
      AnalyticAt ℂ (fun y : Fin (m + 1) → ℂ ↦ f ((Fin.succFunEquiv ℂ (m + 1)).symm (y, w))) x := by
    -- The lower-dimensional induction hypothesis already gives joint block analyticity at `x`.
    exact
      transportedFixedLastSlice_analyticOnNhd
        (m := m) (D := D) (f := f) ih hD hsep w x hxDw
  have hEqOn :
      Set.EqOn
        (fun y : Fin (m + 1) → ℂ ↦ f ((Fin.succFunEquiv ℂ (m + 1)).symm (y, w)))
        (fun y ↦
          ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
            ∮ ζ in C((Fin.succFunEquiv ℂ (m + 1) z).2, R),
              (ζ - w)⁻¹ • f ((Fin.succFunEquiv ℂ (m + 1)).symm (y, ζ))))
        (Metric.ball (fun i ↦ z (Fin.castAdd 1 i)) r) := by
    intro y hy
    -- On the whole inner cylinder, the explicit Cauchy transform agrees with the original
    -- transported function.
    simpa using
      ((transportedLastCauchyTransform_eqOn_ball
        (m := m) (D := D) (f := f) hsep hcyl) y hy hw)
  -- Transfer block analyticity from the transported slice to the explicit Cauchy transform.
  exact hgAt.congr <| hEqOn.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hx)

/-- Helper for Theorem IV.5-extra-2: on the smaller last-variable cylinder, the boundary Cauchy
kernel never hits its pole. -/
lemma transportedLastCauchyKernel_nonzero_smallCylinder
    {m : ℕ} {z : Fin (m + 2) → ℂ} {r ρ : ℝ}
    {ζ : ℂ} (hζ : ζ ∈ Metric.sphere ((Fin.succFunEquiv ℂ (m + 1) z).2) (ρ / 2))
    {p : (Fin (m + 1) → ℂ) × ℂ}
    (hp : p ∈ Metric.ball ((Fin.succFunEquiv ℂ (m + 1) z).1) r ×ˢ
      Metric.ball ((Fin.succFunEquiv ℂ (m + 1) z).2) (ρ / 4))
    (hρpos : 0 < ρ) :
    ζ - p.2 ≠ 0 := by
  -- The boundary point stays at radius `ρ / 2`, while the cylinder keeps `p.2` strictly inside
  -- the smaller `ρ / 4` ball around the same center.
  have hζdist : dist ζ ((Fin.succFunEquiv ℂ (m + 1) z).2) = ρ / 2 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hζ
  have hpdist : dist p.2 ((Fin.succFunEquiv ℂ (m + 1) z).2) < ρ / 4 := by
    simpa [Metric.mem_ball] using hp.2
  intro hzero
  have hpEq : ζ = p.2 := sub_eq_zero.mp hzero
  have : ρ / 2 < ρ / 4 := by
    calc
      ρ / 2 = dist ζ ((Fin.succFunEquiv ℂ (m + 1) z).2) := hζdist.symm
      _ = dist p.2 ((Fin.succFunEquiv ℂ (m + 1) z).2) := by rw [hpEq]
      _ < ρ / 4 := hpdist
  linarith

/-- Helper for Theorem IV.5-extra-2: each boundary Cauchy integrand is jointly analytic on the
smaller transported cylinder. -/
lemma transportedLastCauchyBoundaryIntegrand_analyticOnNhd_smallCylinder
    {m : ℕ} {f : (Fin (m + 2) → ℂ) → ℂ}
    {z : Fin (m + 2) → ℂ} {r ρ : ℝ}
    (hboundary :
      let e := Fin.succFunEquiv ℂ (m + 1)
      let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
      let U := Metric.ball (e z).1 r
      ∀ ζ ∈ Metric.sphere (e z).2 (ρ / 2),
        AnalyticOnNhd ℂ (fun x ↦ g (x, ζ)) U)
    (hρpos : 0 < ρ) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    let U := Metric.ball (e z).1 r
    ∀ ζ ∈ Metric.sphere (e z).2 (ρ / 2),
      AnalyticOnNhd ℂ
        (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ (ζ - p.2)⁻¹ * g (p.1, ζ))
        (U ×ˢ Metric.ball (e z).2 (ρ / 4)) := by
  dsimp at hboundary ⊢
  intro ζ hζ
  have hg :
      AnalyticOnNhd ℂ
        (fun p : (Fin (m + 1) → ℂ) × ℂ ↦
          f ((Fin.succFunEquiv ℂ (m + 1)).symm (p.1, ζ)))
        (Metric.ball (fun i ↦ z (Fin.castAdd 1 i)) r ×ˢ
          Metric.ball (z (Fin.natAdd (m + 1) (0 : Fin 1))) (ρ / 4)) := by
    -- Pull the boundary analytic family back along the product projection `p ↦ p.1`.
    refine (hboundary ζ hζ).comp (analyticOnNhd_fst (𝕜 := ℂ)
      (t := Metric.ball (fun i ↦ z (Fin.castAdd 1 i)) r ×ˢ
        Metric.ball (z (Fin.natAdd (m + 1) (0 : Fin 1))) (ρ / 4))) ?_
    intro p hp
    exact hp.1
  have hkernel :
      AnalyticOnNhd ℂ
        (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ (ζ - p.2)⁻¹)
        (Metric.ball (fun i ↦ z (Fin.castAdd 1 i)) r ×ˢ
          Metric.ball (z (Fin.natAdd (m + 1) (0 : Fin 1))) (ρ / 4)) := by
    have hsub :
        AnalyticOnNhd ℂ
          (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ ζ - p.2)
          (Metric.ball (fun i ↦ z (Fin.castAdd 1 i)) r ×ˢ
            Metric.ball (z (Fin.natAdd (m + 1) (0 : Fin 1))) (ρ / 4)) :=
      analyticOnNhd_const.sub (analyticOnNhd_snd (𝕜 := ℂ)
        (t := Metric.ball (fun i ↦ z (Fin.castAdd 1 i)) r ×ˢ
          Metric.ball (z (Fin.natAdd (m + 1) (0 : Fin 1))) (ρ / 4)))
    -- The smaller-radius gap keeps the pole outside the working cylinder.
    refine hsub.inv ?_
    intro p hp
    exact transportedLastCauchyKernel_nonzero_smallCylinder
      (m := m) (z := z) (r := r) (ρ := ρ) hζ hp hρpos
  -- Multiply the analytic kernel by the transported analytic boundary value.
  exact hkernel.mul hg

/-- Helper for Theorem IV.5-extra-2: once the explicit transported Cauchy transform is analytic at
the transported center, the slice-wise Cauchy identity upgrades the original transported function
to joint analyticity at that center. -/
lemma transportedLastCauchyTransform_eqAt_center
    {m : ℕ} {f : (Fin (m + 2) → ℂ) → ℂ}
    {z : Fin (m + 2) → ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hEq :
      let e := Fin.succFunEquiv ℂ (m + 1)
      let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
      let U := Metric.ball (e z).1 (ρ / 2)
      let G : (Fin (m + 1) → ℂ) × ℂ → ℂ := fun p ↦
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ ζ in C((e z).2, ρ / 2), (ζ - p.2)⁻¹ • g (p.1, ζ))
      ∀ x ∈ U, Set.EqOn (fun w ↦ g (x, w)) (fun w ↦ G (x, w)) (Metric.ball (e z).2 (ρ / 2)))
    (hGAt :
      let e := Fin.succFunEquiv ℂ (m + 1)
      let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
      let G : (Fin (m + 1) → ℂ) × ℂ → ℂ := fun p ↦
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ ζ in C((e z).2, ρ / 2), (ζ - p.2)⁻¹ • g (p.1, ζ))
      AnalyticAt ℂ G (e z)) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    AnalyticAt ℂ g (e z) := by
  let e := Fin.succFunEquiv ℂ (m + 1)
  let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
  let G : (Fin (m + 1) → ℂ) × ℂ → ℂ := fun p ↦
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ ζ in C((e z).2, ρ / 2), (ζ - p.2)⁻¹ • g (p.1, ζ))
  have hGAt' : AnalyticAt ℂ G (e z) := by
    -- Repackage the analytic explicit transform with the local names used below.
    simpa [e, g, G] using hGAt
  change AnalyticAt ℂ g (e z)
  have hzBlock : (e z).1 ∈ Metric.ball (e z).1 (ρ / 2) := by
    -- The transported block center lies in every positive-radius ball around itself.
    simpa [Metric.mem_ball] using show 0 < ρ / 2 by positivity
  have hzLast : (e z).2 ∈ Metric.ball (e z).2 (ρ / 2) := by
    -- The transported last coordinate lies in the same positive-radius scalar ball.
    simpa [Metric.mem_ball] using show 0 < ρ / 2 by positivity
  have hEq' :
      ∀ x ∈ Metric.ball (e z).1 (ρ / 2),
        Set.EqOn (fun w ↦ g (x, w)) (fun w ↦ G (x, w)) (Metric.ball (e z).2 (ρ / 2)) := by
    -- Normalize the slice-wise equality into the local names used in this helper.
    simpa [e, g, G] using hEq
  have hEqOn :
      Set.EqOn
        g
        G
        (Metric.ball (e z).1 (ρ / 2) ×ˢ Metric.ball (e z).2 (ρ / 2)) := by
    intro p hp
    -- The slice-wise identity is pointwise on the full product neighborhood around `e z`.
    exact (hEq' p.1 hp.1) hp.2
  have hNhds :
      Metric.ball (e z).1 (ρ / 2) ×ˢ Metric.ball (e z).2 (ρ / 2) ∈ nhds (e z) := by
    -- Use the product of the two positive-radius balls as the common neighborhood for congruence.
    exact (Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds ⟨hzBlock, hzLast⟩
  exact hGAt'.congr (hEqOn.eventuallyEq_of_mem hNhds).symm

/-- Helper for Theorem IV.5-extra-2: once the normalized `cauchyPowerSeries` model is analytic at
the transported center, the already-established small-ball identity transfers that analyticity
back to the explicit Cauchy integral. -/
lemma transportedLastCauchyTransform_jointAnalyticAt_center_ofCommonBall
    {m : ℕ} {f : (Fin (m + 2) → ℂ) → ℂ}
    {z : Fin (m + 2) → ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hSeriesAt :
      let e := Fin.succFunEquiv ℂ (m + 1)
      let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
      AnalyticAt ℂ
        (fun p : (Fin (m + 1) → ℂ) × ℂ ↦
          (cauchyPowerSeries (fun ζ ↦ g (p.1, ζ)) (e z).2 (ρ / 2)).sum (p.2 - (e z).2))
        (e z))
    (hSeriesEq :
      let e := Fin.succFunEquiv ℂ (m + 1)
      let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
      let r0 : ℝ := ρ / 8
      ∀ p ∈ Metric.ball (e z) r0,
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ ζ in C((e z).2, ρ / 2), (ζ - p.2)⁻¹ • g (p.1, ζ)) =
        (cauchyPowerSeries (fun ζ ↦ g (p.1, ζ)) (e z).2 (ρ / 2)).sum (p.2 - (e z).2)) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    AnalyticAt ℂ
      (fun p : (Fin (m + 1) → ℂ) × ℂ ↦
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ ζ in C((e z).2, ρ / 2), (ζ - p.2)⁻¹ • g (p.1, ζ)))
      (e z) := by
  let e := Fin.succFunEquiv ℂ (m + 1)
  let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
  let r0 : ℝ := ρ / 8
  let normalized :
      (Fin (m + 1) → ℂ) × ℂ → ℂ := fun p ↦
    (cauchyPowerSeries (fun ζ ↦ g (p.1, ζ)) (e z).2 (ρ / 2)).sum (p.2 - (e z).2)
  have hr0pos : 0 < r0 := by
    -- Keep the common-ball radius normalized once so the congruence step works on one fixed ball.
    dsimp [r0]
    positivity
  have hNormalizedAt : AnalyticAt ℂ normalized (e z) := by
    -- Repackage the normalized-series analyticity with the local names used in the congruence.
    simpa [e, g, normalized] using hSeriesAt
  have hzCommonBall : e z ∈ Metric.ball (e z) r0 := by
    -- The transported center belongs to every positive-radius ball around itself.
    simpa [Metric.mem_ball] using hr0pos
  have hEventuallyEq :
      normalized =ᶠ[nhds (e z)]
        (fun p : (Fin (m + 1) → ℂ) × ℂ ↦
          ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
            ∮ ζ in C((e z).2, ρ / 2), (ζ - p.2)⁻¹ • g (p.1, ζ))) := by
    -- Route correction: the explicit transform is recovered from the normalized series by the
    -- already-proved common-ball equality, so no new transport or integral interchange is needed.
    filter_upwards [Metric.isOpen_ball.mem_nhds hzCommonBall] with p hp
    symm
    exact hSeriesEq p hp
  -- Transfer analyticity from the normalized `cauchyPowerSeries` model to the explicit integral.
  exact hNormalizedAt.congr hEventuallyEq
