import DifferentialForms_Cartan_1970.cartan.IV.section14.«0002_Definition_IV_2_extra_2»
import DifferentialForms_Cartan_1970.cartan.IV.section17.«0001_Definition_IV_5_extra_1»
import DifferentialForms_Cartan_1970.cartan.IV.section17.«0002_Theorem_IV_5_extra_2».TransportedCauchyTransform

/-- Helper for Theorem IV.5-extra-2: the fixed closed ball of radius `ρ / 8` around the
transported center stays inside the smaller boundary cylinder. -/
lemma smallClosedBall_subset_boundaryCylinder
    {m : ℕ} {z : Fin (m + 2) → ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    Metric.closedBall (e z) (ρ / 8) ⊆
      Metric.ball (e z).1 (ρ / 2) ×ˢ Metric.ball (e z).2 (ρ / 4) := by
  dsimp
  intro p hp
  have hpdist :
      dist p ((Fin.succFunEquiv ℂ (m + 1)) z) ≤ ρ / 8 := by
    simpa [Metric.mem_closedBall] using hp
  have hprod :
      max
          (dist p.1 (((Fin.succFunEquiv ℂ (m + 1)) z).1))
          (dist p.2 (((Fin.succFunEquiv ℂ (m + 1)) z).2)) ≤
        ρ / 8 := by
    simpa [Prod.dist_eq] using hpdist
  have hblock :
      dist p.1 (((Fin.succFunEquiv ℂ (m + 1)) z).1) < ρ / 2 := by
    -- The product-ball bound controls the block coordinate by the same fixed radius.
    have hblock_le :
        dist p.1 (((Fin.succFunEquiv ℂ (m + 1)) z).1) ≤ ρ / 8 :=
      le_trans (le_max_left _ _) hprod
    linarith
  have hlast :
      dist p.2 (((Fin.succFunEquiv ℂ (m + 1)) z).2) < ρ / 4 := by
    -- The last coordinate gets the sharper `ρ / 4` bound from the same fixed closed ball.
    have hlast_le :
        dist p.2 (((Fin.succFunEquiv ℂ (m + 1)) z).2) ≤ ρ / 8 :=
      le_trans (le_max_right _ _) hprod
    linarith
  exact ⟨by simpa [Metric.mem_ball] using hblock, by simpa [Metric.mem_ball] using hlast⟩

/-- Helper for Theorem IV.5-extra-2: uniform convergence of a countable family on a circle allows
termwise circle integration. This is the generic exchange step needed when the fixed-ball Cauchy
series for the boundary integrand is integrated coefficientwise. -/
lemma circleIntegral_tsum_of_summableUniformlyOn_sphere_center_countable
    {ι : Type*} [Countable ι] {F : ι → ℂ → ℂ} {c : ℂ} {R : NNReal}
    (hcont : ∀ i, ContinuousOn (F i) (Metric.sphere c (R : ℝ)))
    (hsum : SummableUniformlyOn F (Metric.sphere c (R : ℝ))) :
    (∮ z in C(c, (R : ℝ)), ∑' i : ι, F i z) = ∑' i : ι, ∮ z in C(c, (R : ℝ)), F i z := by
  classical
  have hhas :
      HasSumUniformlyOn F (fun z ↦ ∑' i : ι, F i z) (Metric.sphere c (R : ℝ)) :=
    hsum.hasSumUniformlyOn
  have hcont_partial :
      ∀ s : Finset ι,
        ContinuousOn (fun z : ℂ ↦ ∑ i ∈ s, F i z) (Metric.sphere c (R : ℝ)) := by
    -- Finite partial sums preserve continuity on the chosen boundary circle.
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (0 : ℂ)) _)
    · intro i s hi hs
      simpa [Finset.sum_insert, hi] using (hcont i).add hs
  have htendsto :
      Filter.Tendsto (fun s : Finset ι ↦ ∮ z in C(c, (R : ℝ)), ∑ i ∈ s, F i z) Filter.atTop
        (nhds (∮ z in C(c, (R : ℝ)), ∑' i : ι, F i z)) :=
    hhas.tendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn R.2
      (Filter.Eventually.of_forall hcont_partial)
  have hsum_int :
      HasSum (fun i : ι ↦ ∮ z in C(c, (R : ℝ)), F i z)
        (∮ z in C(c, (R : ℝ)), ∑' i : ι, F i z) := by
    rw [HasSum]
    convert htendsto using 1
    ext s
    symm
    exact circleIntegral.integral_fun_sum fun i _ ↦ (hcont i).circleIntegrable R.2
  exact hsum_int.tsum_eq.symm

/-- Helper for Theorem IV.5-extra-2: uniform convergence of a countable family on a circle allows
termwise circle integration. This is the generic exchange step needed when the fixed-ball Cauchy
series for the boundary integrand is integrated coefficientwise. -/
lemma circleIntegral_tsum_of_summableUniformlyOn_sphere_countable
    {ι : Type*} [Countable ι] {F : ι → ℂ → ℂ} {R : NNReal}
    (hcont : ∀ i, ContinuousOn (F i) (Metric.sphere (0 : ℂ) (R : ℝ)))
    (hsum : SummableUniformlyOn F (Metric.sphere (0 : ℂ) (R : ℝ))) :
    (∮ z in C(0, (R : ℝ)), ∑' i : ι, F i z) = ∑' i : ι, ∮ z in C(0, (R : ℝ)), F i z := by
  -- Specialize the centered interchange lemma to the origin-centered circle used elsewhere.
  exact
    circleIntegral_tsum_of_summableUniformlyOn_sphere_center_countable
      (c := 0) (R := R) hcont hsum

/-- Helper for Theorem IV.5-extra-2: if the circle-integrand kernel is jointly continuous in a
parameter and the angular variable, then the resulting circle integral depends continuously on the
parameter. -/
lemma continuous_parametric_circleIntegral
    {S : Type*} [TopologicalSpace S] {c : ℂ} {R : ℝ} {K : S → ℂ → ℂ}
    (hK : Continuous fun p : S × ℝ ↦ deriv (circleMap c R) p.2 * K p.1 (circleMap c R p.2)) :
    Continuous fun x : S ↦ ∮ z in C(c, R), K x z := by
  let K' : S → ℝ → ℂ := fun x θ ↦ deriv (circleMap c R) θ * K x (circleMap c R θ)
  have hK' : Continuous (Function.uncurry K') := by
    simpa [K'] using hK
  -- Re-express the circle integral as an interval integral over the angular parameter once.
  simpa [circleIntegral, K'] using
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hK' (0 : ℝ) (2 * Real.pi))

/-- Helper for Theorem IV.5-extra-2: integrating a torus-continuous kernel over the second
boundary circle yields a continuous function of the first boundary variable, even for arbitrary
centers. -/
lemma continuousOn_second_circleIntegral_of_continuousOn_torus_center
    {c₁ c₂ : ℂ} {R₁ R₂ : ℝ} (hR₂ : 0 ≤ R₂) {Φ : ℂ × ℂ → ℂ}
    (hΦ :
      ContinuousOn Φ (Metric.sphere c₁ R₁ ×ˢ Metric.sphere c₂ R₂)) :
    ContinuousOn (fun ζ₁ : ℂ ↦ ∮ ζ₂ in C(c₂, R₂), Φ (ζ₁, ζ₂)) (Metric.sphere c₁ R₁) := by
  rw [continuousOn_iff_continuous_restrict]
  let S : Set ℂ := Metric.sphere c₁ R₁
  let ΦS : S → ℂ → ℂ := fun x ζ₂ ↦ Φ (x.1, ζ₂)
  have hparam :
      Continuous fun p : S × ℝ ↦
        deriv (circleMap c₂ R₂) p.2 * ΦS p.1 (circleMap c₂ R₂ p.2) := by
    have hfst : Continuous fun p : S × ℝ ↦ (p.1 : ℂ) :=
      continuous_subtype_val.comp continuous_fst
    have hsnd : Continuous fun p : S × ℝ ↦ circleMap c₂ R₂ p.2 :=
      (continuous_circleMap c₂ R₂).comp continuous_snd
    have hpair :
        Continuous fun p : S × ℝ ↦ ((p.1 : ℂ), circleMap c₂ R₂ p.2) :=
      hfst.prodMk hsnd
    have hpair_mem :
        ∀ p : S × ℝ,
          ((p.1 : ℂ), circleMap c₂ R₂ p.2) ∈
            Metric.sphere c₁ R₁ ×ˢ Metric.sphere c₂ R₂ := by
      intro p
      exact ⟨p.1.2, circleMap_mem_sphere c₂ hR₂ p.2⟩
    have hcomp :
        Continuous fun p : S × ℝ ↦ Φ ((p.1 : ℂ), circleMap c₂ R₂ p.2) :=
      hΦ.comp_continuous hpair hpair_mem
    have hderiv :
        Continuous fun p : S × ℝ ↦ deriv (circleMap c₂ R₂) p.2 := by
      simpa [deriv_circleMap] using
        (((continuous_circleMap 0 R₂).comp continuous_snd).mul
          (continuous_const : Continuous fun _ : S × ℝ ↦ (Complex.I : ℂ)))
    -- Compose the torus-continuous kernel with the parametrized circle and multiply by the
    -- circle-map derivative before integrating.
    simpa [ΦS] using hderiv.mul hcomp
  -- The parameterized circle-integral theorem now gives continuity on the outer boundary circle.
  simpa [S, ΦS] using continuous_parametric_circleIntegral (S := S) hparam

/-- Helper for Theorem IV.5-extra-2: restricting the transported boundary integrand from the
smaller boundary cylinder to the fixed common ball of radius `ρ / 8` preserves analyticity. -/
lemma transportedBoundaryIntegrand_analyticOnNhd_commonBall
    {m : ℕ} {f : (Fin (m + 2) → ℂ) → ℂ}
    {z : Fin (m + 2) → ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hBoundaryIntegrand :
      let e := Fin.succFunEquiv ℂ (m + 1)
      let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
      let U := Metric.ball (e z).1 (ρ / 2)
      ∀ ζ ∈ Metric.sphere (e z).2 (ρ / 2),
        AnalyticOnNhd ℂ
          (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ (ζ - p.2)⁻¹ * g (p.1, ζ))
          (U ×ˢ Metric.ball (e z).2 (ρ / 4))) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    let r0 : ℝ := ρ / 8
    ∀ ζ ∈ Metric.sphere (e z).2 (ρ / 2),
      AnalyticOnNhd ℂ
        (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ (ζ - p.2)⁻¹ * g (p.1, ζ))
        (Metric.ball (e z) r0) := by
  let e := Fin.succFunEquiv ℂ (m + 1)
  let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
  let r0 : ℝ := ρ / 8
  dsimp [e, g] at hBoundaryIntegrand ⊢
  intro ζ hζ
  have hsmallClosed :
      Metric.closedBall (e z) r0 ⊆
        Metric.ball (e z).1 (ρ / 2) ×ˢ Metric.ball (e z).2 (ρ / 4) := by
    -- Freeze the same inner radius used later in the Cauchy packaging, so all boundary slices
    -- work over one common ball.
    simpa [e, r0] using
      smallClosedBall_subset_boundaryCylinder (m := m) (z := z) (ρ := ρ) hρpos
  have hsubset :
      Metric.ball (e z) r0 ⊆
        Metric.ball (e z).1 (ρ / 2) ×ˢ Metric.ball (e z).2 (ρ / 4) := by
    intro p hp
    -- Pass from the open inner ball to the closed ball once, then reuse the cylinder containment.
    exact hsmallClosed (Metric.ball_subset_closedBall hp)
  -- Restrict the given boundary-cylinder analyticity to the fixed common ball.
  exact (hBoundaryIntegrand ζ hζ).mono hsubset

/-- Helper for Theorem IV.5-extra-2: every explicit boundary integrand attached to a point of the
fixed inner closed ball is continuous on the distinguished boundary circle. -/
lemma transportedBoundaryIntegrand_continuousOn_sphere_closedBall
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i))
    {z : Fin (m + 2) → ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcyl :
      Metric.ball ((Fin.succFunEquiv ℂ (m + 1) z).1) (ρ / 2) ×ˢ
          Metric.closedBall ((Fin.succFunEquiv ℂ (m + 1) z).2) (ρ / 2) ⊆
        {p | (Fin.succFunEquiv ℂ (m + 1)).symm p ∈ D}) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    let r0 : ℝ := ρ / 8
    ∀ p ∈ Metric.closedBall (e z) r0,
      ContinuousOn (fun ζ ↦ (ζ - p.2)⁻¹ * g (p.1, ζ))
        (Metric.sphere (e z).2 (ρ / 2)) := by
  let e := Fin.succFunEquiv ℂ (m + 1)
  let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
  let r0 : ℝ := ρ / 8
  dsimp
  intro p hp
  have hsmallClosed :
      Metric.closedBall (e z) r0 ⊆
        Metric.ball (e z).1 (ρ / 2) ×ˢ Metric.ball (e z).2 (ρ / 4) := by
    -- Freeze the same inner closed ball used by the Cauchy package, so the pole-free gap is
    -- available uniformly on the boundary circle.
    simpa [e, r0] using
      smallClosedBall_subset_boundaryCylinder (m := m) (z := z) (ρ := ρ) hρpos
  have hpSmall :
      p ∈ Metric.ball (e z).1 (ρ / 2) ×ˢ Metric.ball (e z).2 (ρ / 4) :=
    hsmallClosed hp
  have hslice :
      AnalyticOnNhd ℂ (fun w ↦ g (p.1, w)) (Metric.closedBall (e z).2 (ρ / 2)) := by
    -- The fixed-block last slice is analytic on the whole closed disc coming from the original
    -- separate analyticity hypothesis on the transported cylinder.
    simpa [e, g] using
      transportedLastSlices_analyticOnNhd_closedBall
        (m := m) (D := D) (f := f) hsep (z := z) (r := ρ / 2) (R := ρ / 2) hcyl p.1 hpSmall.1
  have hvalueCont :
      ContinuousOn (fun ζ ↦ g (p.1, ζ)) (Metric.sphere (e z).2 (ρ / 2)) := by
    -- Restrict the analytic last slice to the boundary circle once, so the remaining factor is
    -- the elementary pole-free scalar kernel.
    exact hslice.continuousOn.mono Metric.sphere_subset_closedBall
  have hdenCont :
      ContinuousOn (fun ζ : ℂ ↦ ζ - p.2) (Metric.sphere (e z).2 (ρ / 2)) :=
    continuousOn_id.sub continuousOn_const
  have hdenNe :
      ∀ ζ ∈ Metric.sphere (e z).2 (ρ / 2), ζ - p.2 ≠ 0 := by
    intro ζ hζ
    -- The smaller inner closed ball keeps the last coordinate strictly away from the boundary
    -- circle, so the Cauchy kernel has no pole there.
    exact
      transportedLastCauchyKernel_nonzero_smallCylinder
        (m := m) (z := z) (r := ρ / 2) (ρ := ρ) hζ hpSmall hρpos
  have hkernelCont :
      ContinuousOn (fun ζ : ℂ ↦ (ζ - p.2)⁻¹) (Metric.sphere (e z).2 (ρ / 2)) :=
    hdenCont.inv₀ hdenNe
  -- Multiply the pole-free kernel by the continuous boundary values on the distinguished circle.
  exact hkernelCont.mul hvalueCont

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: on the fixed inner closed block ball,
the transported boundary slice itself is continuous on the distinguished boundary circle. -/
lemma transportedBoundarySlice_continuousOn_sphere_closedBall
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i))
    {z : Fin (m + 2) → ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcyl :
      Metric.ball ((Fin.succFunEquiv ℂ (m + 1) z).1) (ρ / 2) ×ˢ
          Metric.closedBall ((Fin.succFunEquiv ℂ (m + 1) z).2) (ρ / 2) ⊆
        {p | (Fin.succFunEquiv ℂ (m + 1)).symm p ∈ D}) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    let r0 : ℝ := ρ / 8
    ∀ x ∈ Metric.closedBall (e z).1 r0,
      ContinuousOn (fun ζ ↦ g (x, ζ)) (Metric.sphere (e z).2 (ρ / 2)) := by
  let e := Fin.succFunEquiv ℂ (m + 1)
  let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
  let r0 : ℝ := ρ / 8
  dsimp
  intro x hx
  have hr0nonneg : 0 ≤ r0 := by
    dsimp [r0]
    linarith
  have hxPair :
      (x, (e z).2) ∈ Metric.closedBall (e z) r0 := by
    -- Insert the fixed center in the last coordinate so the product distance reduces to the
    -- closed-ball constraint already available on the block variable.
    have hxdist : dist x (e z).1 ≤ r0 := by
      simpa [Metric.mem_closedBall] using hx
    have hpairDist :
        dist (x, (e z).2) (e z) ≤ r0 := by
      simpa [Prod.dist_eq] using
        (show max (dist x (e z).1) (dist (e z).2 (e z).2) ≤ r0 by
          exact max_le hxdist (by simpa using hr0nonneg))
    simpa [Metric.mem_closedBall] using hpairDist
  have hIntegrandCont :
      ContinuousOn (fun ζ ↦ (ζ - (e z).2)⁻¹ * g (x, ζ))
        (Metric.sphere (e z).2 (ρ / 2)) := by
    -- Reuse the existing continuity owner for the boundary Cauchy integrand at the inserted
    -- point `(x, (e z).2)`.
    simpa [e, g] using
      transportedBoundaryIntegrand_continuousOn_sphere_closedBall
        (m := m) (D := D) (f := f) hsep (z := z) (ρ := ρ) hρpos hcyl
        (x, (e z).2) hxPair
  have hFactorCont :
      ContinuousOn (fun ζ : ℂ ↦ ζ - (e z).2) (Metric.sphere (e z).2 (ρ / 2)) :=
    continuousOn_id.sub continuousOn_const
  have hRecover :
      Set.EqOn
        (fun ζ ↦ (ζ - (e z).2) * ((ζ - (e z).2)⁻¹ * g (x, ζ)))
        (fun ζ ↦ g (x, ζ))
        (Metric.sphere (e z).2 (ρ / 2)) := by
    intro ζ hζ
    have hne : ζ - (e z).2 ≠ 0 := by
      intro hzero
      have hdist : dist ζ (e z).2 = ρ / 2 := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hζ
      have : dist ζ (e z).2 = 0 := by
        simpa [dist_eq_norm, hzero]
      linarith
    -- Multiply the integrand back by the nonvanishing scalar factor on the boundary sphere.
    field_simp [hne]
  have hProductCont :
      ContinuousOn
        (fun ζ ↦ (ζ - (e z).2) * ((ζ - (e z).2)⁻¹ * g (x, ζ)))
        (Metric.sphere (e z).2 (ρ / 2)) := by
    simpa [mul_assoc] using hFactorCont.mul hIntegrandCont
  -- Recover the raw boundary slice by multiplying away the fixed nonzero boundary kernel.
  exact hProductCont.congr hRecover.symm

/-- Helper for Theorem IV.5-extra-2: the explicit boundary integrand on the fixed inner closed
ball is circle-integrable on the distinguished boundary circle. -/
lemma transportedBoundaryIntegrand_circleIntegrable_closedBall
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i))
    {z : Fin (m + 2) → ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcyl :
      Metric.ball ((Fin.succFunEquiv ℂ (m + 1) z).1) (ρ / 2) ×ˢ
          Metric.closedBall ((Fin.succFunEquiv ℂ (m + 1) z).2) (ρ / 2) ⊆
        {p | (Fin.succFunEquiv ℂ (m + 1)).symm p ∈ D}) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    let r0 : ℝ := ρ / 8
    ∀ p ∈ Metric.closedBall (e z) r0,
      CircleIntegrable (fun ζ ↦ (ζ - p.2)⁻¹ * g (p.1, ζ)) (e z).2 (ρ / 2) := by
  let e := Fin.succFunEquiv ℂ (m + 1)
  let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
  let r0 : ℝ := ρ / 8
  dsimp
  intro p hp
  have hcont :
      ContinuousOn (fun ζ ↦ (ζ - p.2)⁻¹ * g (p.1, ζ))
        (Metric.sphere (e z).2 (ρ / 2)) := by
    -- Package the boundary continuity once; the remaining analytic work should not revisit these
    -- integrability side conditions.
    exact
      transportedBoundaryIntegrand_continuousOn_sphere_closedBall
        (m := m) (D := D) (f := f) hsep (z := z) (ρ := ρ) hρpos hcyl p hp
  have hρhalf_nonneg : 0 ≤ ρ / 2 := by positivity
  exact hcont.circleIntegrable hρhalf_nonneg

/-- Helper for Theorem IV.5-extra-2: each fixed transported block point gives a boundary function
that is circle-integrable on the working last-variable circle. -/
lemma transportedLastSlice_circleIntegrable_boundary
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i))
    {z : Fin (m + 2) → ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcyl :
      Metric.ball ((Fin.succFunEquiv ℂ (m + 1) z).1) (ρ / 2) ×ˢ
          Metric.closedBall ((Fin.succFunEquiv ℂ (m + 1) z).2) (ρ / 2) ⊆
        {p | (Fin.succFunEquiv ℂ (m + 1)).symm p ∈ D}) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    let U := Metric.ball (e z).1 (ρ / 2)
    ∀ x ∈ U,
      CircleIntegrable (fun ζ ↦ g (x, ζ)) (e z).2 (ρ / 2) := by
  dsimp
  intro x hx
  have hslice :
      AnalyticOnNhd ℂ
        (fun w ↦ f ((Fin.succFunEquiv ℂ (m + 1)).symm (x, w)))
        (Metric.closedBall ((Fin.succFunEquiv ℂ (m + 1) z).2) (ρ / 2)) := by
    -- The transported last slice is analytic on the whole working closed disc.
    simpa using
      transportedLastSlices_analyticOnNhd_closedBall
        (m := m) (D := D) (f := f) hsep (z := z) (r := ρ / 2) (R := ρ / 2) hcyl x hx
  have hcont :
      ContinuousOn
        (fun ζ ↦ f ((Fin.succFunEquiv ℂ (m + 1)).symm (x, ζ)))
        (Metric.sphere ((Fin.succFunEquiv ℂ (m + 1) z).2) (ρ / 2)) := by
    -- Restrict the analytic last slice once to the boundary circle to obtain integrability data.
    exact hslice.continuousOn.mono Metric.sphere_subset_closedBall
  have hCircle :
      CircleIntegrable
        (fun ζ ↦ f ((Fin.succFunEquiv ℂ (m + 1)).symm (x, ζ)))
        ((Fin.succFunEquiv ℂ (m + 1) z).2) (ρ / 2) := by
    -- The canonical Cauchy power series only needs boundary-circle integrability of the slice.
    exact hcont.circleIntegrable (by positivity)
  exact hCircle

/-- Helper for Theorem IV.5-extra-2: the `n`th coefficient of the transported last-variable
`cauchyPowerSeries` is already the centered boundary circle integral with kernel
`(ζ - (e z).2)⁻¹ ^ n * (ζ - (e z).2)⁻¹`. -/
lemma transportedLastCauchyCoeff_eq_centeredIntegral
    {m : ℕ} {f : (Fin (m + 2) → ℂ) → ℂ}
    {z : Fin (m + 2) → ℂ} {ρ : ℝ}
    (n : ℕ) (x : Fin (m + 1) → ℂ) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    (cauchyPowerSeries (fun ζ ↦ g (x, ζ)) (e z).2 (ρ / 2)).coeff n =
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ ζ in C((e z).2, ρ / 2), ((ζ - (e z).2)⁻¹) ^ n • (ζ - (e z).2)⁻¹ • g (x, ζ)) := by
  dsimp
  -- Rewrite the coefficient as the value of the multilinear term on the all-ones vector.
  rw [FormalMultilinearSeries.coeff]
  change
    (cauchyPowerSeries
      (fun ζ ↦ f ((Fin.succFunEquiv ℂ (m + 1)).symm (x, ζ)))
      (z (Fin.natAdd (m + 1) (0 : Fin 1)))
      (ρ / 2) n fun _ ↦ (1 : ℂ)) =
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∮ ζ in C(z (Fin.natAdd (m + 1) (0 : Fin 1)), ρ / 2),
          (ζ - z (Fin.natAdd (m + 1) (0 : Fin 1)))⁻¹ ^ n *
            ((ζ - z (Fin.natAdd (m + 1) (0 : Fin 1)))⁻¹ *
              f ((Fin.succFunEquiv ℂ (m + 1)).symm (x, ζ))))
  rw [cauchyPowerSeries_apply]
  simp only [one_div, smul_eq_mul]

/-- Helper for Theorem IV.5-extra-2: on the fixed common ball, the explicit transported Cauchy
transform is already equal to the canonical one-variable Cauchy power series in the last
coordinate. -/
lemma transportedLastCauchySeries_eq_on_smallBall
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i))
    {z : Fin (m + 2) → ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcyl :
      Metric.ball ((Fin.succFunEquiv ℂ (m + 1) z).1) (ρ / 2) ×ˢ
          Metric.closedBall ((Fin.succFunEquiv ℂ (m + 1) z).2) (ρ / 2) ⊆
        {p | (Fin.succFunEquiv ℂ (m + 1)).symm p ∈ D}) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    let r0 : ℝ := ρ / 8
    ∀ p ∈ Metric.ball (e z) r0,
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ ζ in C((e z).2, ρ / 2), (ζ - p.2)⁻¹ • g (p.1, ζ)) =
      (cauchyPowerSeries (fun ζ ↦ g (p.1, ζ)) (e z).2 (ρ / 2)).sum (p.2 - (e z).2) := by
  dsimp
  intro p hp
  have hsmallClosed :
      Metric.closedBall ((Fin.succFunEquiv ℂ (m + 1)) z) (ρ / 8) ⊆
        Metric.ball ((Fin.succFunEquiv ℂ (m + 1)) z).1 (ρ / 2) ×ˢ
          Metric.ball ((Fin.succFunEquiv ℂ (m + 1)) z).2 (ρ / 4) := by
    -- The fixed common ball sits inside the cylinder where the last-slice power series is valid.
    simpa using smallClosedBall_subset_boundaryCylinder (m := m) (z := z) (ρ := ρ) hρpos
  have hpSmall :
      p ∈ Metric.ball ((Fin.succFunEquiv ℂ (m + 1)) z).1 (ρ / 2) ×ˢ
        Metric.ball ((Fin.succFunEquiv ℂ (m + 1)) z).2 (ρ / 4) := by
    exact hsmallClosed (Metric.ball_subset_closedBall hp)
  have hCircle :
      CircleIntegrable
        (fun ζ ↦ f ((Fin.succFunEquiv ℂ (m + 1)).symm (p.1, ζ)))
        ((Fin.succFunEquiv ℂ (m + 1)) z).2 (ρ / 2) := by
    -- Freeze the block point and reuse the boundary integrability of the transported last slice.
    simpa using
      transportedLastSlice_circleIntegrable_boundary
        (m := m) (D := D) (f := f) hsep (z := z) (ρ := ρ) hρpos hcyl p.1 hpSmall.1
  have hpLast :
      ‖p.2 - ((Fin.succFunEquiv ℂ (m + 1)) z).2‖ < ρ / 2 := by
    have hpQuarter : dist p.2 ((Fin.succFunEquiv ℂ (m + 1)) z).2 < ρ / 4 := by
      simpa [Metric.mem_ball] using hpSmall.2
    -- The smaller `ρ / 4` last ball is strictly contained in the radius `ρ / 2` disc used by the
    -- Cauchy power series.
    have hquarter_lt_half : ρ / 4 < ρ / 2 := by
      linarith
    simpa [dist_eq_norm] using lt_trans hpQuarter hquarter_lt_half
  -- Evaluate the canonical last-variable power series at the actual displacement `p.2 - (e z).2`.
  simpa [smul_eq_mul, FormalMultilinearSeries.sum, add_sub_cancel] using
    (sum_cauchyPowerSeries_eq_integral
      (f := fun ζ ↦ f ((Fin.succFunEquiv ℂ (m + 1)).symm (p.1, ζ)))
      (c := ((Fin.succFunEquiv ℂ (m + 1)) z).2)
      (R := ρ / 2)
      (w := p.2 - ((Fin.succFunEquiv ℂ (m + 1)) z).2)
      hCircle
      hpLast).symm

/-- Helper for Theorem IV.5-extra-2: updating one coordinate of a finite block vector is an
analytic one-variable map at the original coordinate value. -/
lemma analyticAt_update_coordinate
    {m : ℕ} (x : Fin (m + 1) → ℂ) (i : Fin (m + 1)) :
    AnalyticAt ℂ (fun u : ℂ ↦ Function.update x i u) (x i) := by
  -- Check each target coordinate separately: the updated coordinate is the identity and every
  -- other coordinate is constant.
  refine AnalyticAt.pi fun j ↦ ?_
  by_cases hji : j = i
  · subst hji
    simpa using (analyticAt_id : AnalyticAt ℂ (fun u : ℂ ↦ u) (x j))
  · have hconst : (fun u : ℂ ↦ Function.update x i u j) = fun _ ↦ x j := by
      funext u
      simp [Function.update, hji]
    rw [hconst]
    exact analyticAt_const

/-- Helper for Theorem IV.5-extra-2: pairing the analytic block-coordinate update with a fixed last
coordinate gives an analytic map into the transported product space. -/
lemma analyticAt_update_coordinate_prod_const
    {m : ℕ} (x : Fin (m + 1) → ℂ) (i : Fin (m + 1)) (w : ℂ) :
    AnalyticAt ℂ (fun u : ℂ ↦ (Function.update x i u, w)) (x i) := by
  -- Combine the block update map with the constant last coordinate by the product constructor.
  exact (analyticAt_update_coordinate x i).prod analyticAt_const

/-- Helper for Theorem IV.5-extra-2: if a coordinate-insertion map lands in a target ball on an
open scalar neighborhood, then the same conclusion already holds on the half-radius closed ball. -/
lemma updateCoordinateProdConst_mapsTo_ball_closedBall_half
    {m : ℕ} {x : Fin (m + 1) → ℂ} {i : Fin (m + 1)} {w : ℂ}
    {y : (Fin (m + 1) → ℂ) × ℂ} {r s : ℝ}
    (hspos : 0 < s)
    (hMaps :
      Set.MapsTo (fun u : ℂ ↦ (Function.update x i u, w))
        (Metric.ball (x i) s) (Metric.ball y r)) :
    Set.MapsTo (fun u : ℂ ↦ (Function.update x i u, w))
      (Metric.closedBall (x i) (s / 2)) (Metric.ball y r) := by
  intro u hu
  -- Shrink the scalar neighborhood once so later compactness arguments can work on a closed ball.
  apply hMaps
  have hu_le : dist u (x i) ≤ s / 2 := by
    simpa [Metric.mem_closedBall] using hu
  have hu_lt : dist u (x i) < s := by
    have hs_half_lt : s / 2 < s := by linarith
    exact lt_of_le_of_lt hu_le hs_half_lt
  simpa [Metric.mem_ball] using hu_lt

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: once the weighted boundary integrand is
analytic on one common product ball, every coordinate-inserted slice admits one closed scalar ball
on which the weighted slice has its canonical one-variable power series and remains continuous. -/
lemma weightedBoundarySlice_hasFPowerSeriesOnBall_of_commonBall
    {m : ℕ} {g : (Fin (m + 1) → ℂ) × ℂ → ℂ}
    {center : (Fin (m + 1) → ℂ) × ℂ} {r0 outerR : ℝ}
    (hBoundaryCommonBall :
      ∀ ζ ∈ Metric.sphere center.2 outerR,
        AnalyticOnNhd ℂ
          (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ (ζ - p.2)⁻¹ * g (p.1, ζ))
          (Metric.ball center r0))
    (n : ℕ) (x : Fin (m + 1) → ℂ) (hx : x ∈ Metric.ball center.1 r0) (i : Fin (m + 1)) :
    ∃ R : NNReal, 0 < R ∧
      Set.MapsTo (fun u : ℂ ↦ (Function.update x i u, center.2))
        (Metric.closedBall (x i) (R : ℝ)) (Metric.ball center r0) ∧
      ∀ ζ ∈ Metric.sphere center.2 outerR,
        HasFPowerSeriesOnBall
          (fun u ↦
            ((ζ - center.2)⁻¹) ^ n * ((ζ - center.2)⁻¹ * g (Function.update x i u, ζ)))
          (cauchyPowerSeries
            (fun u ↦
              ((ζ - center.2)⁻¹) ^ n * ((ζ - center.2)⁻¹ * g (Function.update x i u, ζ)))
            (x i) R)
          (x i) R ∧
        ContinuousOn
          (fun u ↦
            ((ζ - center.2)⁻¹) ^ n * ((ζ - center.2)⁻¹ * g (Function.update x i u, ζ)))
          (Metric.closedBall (x i) (R : ℝ)) := by
  let ins : ℂ → (Fin (m + 1) → ℂ) × ℂ := fun u ↦ (Function.update x i u, center.2)
  have hinsCont : ContinuousAt ins (x i) := by
    -- The coordinate-insertion map is analytic, hence continuous, at the original coordinate.
    simpa [ins] using (analyticAt_update_coordinate_prod_const x i center.2).continuousAt
  have hins_mem : ins (x i) ∈ Metric.ball center r0 := by
    -- Inserting the unchanged center value in the last coordinate reduces the product-ball check
    -- to the given block-ball hypothesis.
    have hr0pos : 0 < r0 := by
      exact lt_of_le_of_lt (dist_nonneg : 0 ≤ dist x center.1) (by simpa [Metric.mem_ball] using hx)
    have hdist : dist (x, center.2) center < r0 := by
      rw [Prod.dist_eq]
      exact max_lt_iff.mpr ⟨hx, by simpa [Metric.mem_ball] using hr0pos⟩
    simpa [ins, Metric.mem_ball] using hdist
  have hpre :
      ins ⁻¹' Metric.ball center r0 ∈ nhds (x i) := by
    exact hinsCont.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hins_mem)
  rcases Metric.mem_nhds_iff.mp hpre with ⟨s, hspos, hsMaps⟩
  let R : NNReal := ⟨s / 2, by positivity⟩
  have hRpos : 0 < R := by
    change 0 < s / 2
    positivity
  have hInsertMaps :
      Set.MapsTo ins (Metric.closedBall (x i) (R : ℝ)) (Metric.ball center r0) := by
    -- Shrink the scalar neighborhood once so the later coefficient package can work on a closed
    -- ball.
    simpa [ins, R] using updateCoordinateProdConst_mapsTo_ball_closedBall_half hspos hsMaps
  refine ⟨R, hRpos, hInsertMaps, ?_⟩
  intro ζ hζ
  have hAnalyticOn :
      AnalyticOnNhd ℂ
        (fun u ↦
          ((ζ - center.2)⁻¹) ^ n * ((ζ - center.2)⁻¹ * g (Function.update x i u, ζ)))
        (Metric.ball (x i) s) := by
    intro u hu
    have hBoundaryAt :
        AnalyticAt ℂ
          (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ (ζ - p.2)⁻¹ * g (p.1, ζ))
          (Function.update x i u, center.2) := by
      exact hBoundaryCommonBall ζ hζ _ (hsMaps hu)
    have hInsertAnalytic :
        AnalyticAt ℂ (fun v : ℂ ↦ (Function.update x i v, center.2)) u := by
      simpa [Function.update] using
        (analyticAt_update_coordinate_prod_const (Function.update x i u) i center.2)
    have hInsertCenter :
        (fun v : ℂ ↦ (Function.update x i v, center.2)) u =
          (Function.update x i u, center.2) := by
      simp
    have hSliceAt :
        AnalyticAt ℂ (fun v ↦ (ζ - center.2)⁻¹ * g (Function.update x i v, ζ)) u := by
      simpa using hBoundaryAt.comp_of_eq
        (f := fun v : ℂ ↦ (Function.update x i v, center.2))
        (x := u) hInsertAnalytic hInsertCenter
    -- Multiply by the fixed scalar weight only after composing the common-ball germ with the
    -- coordinate insertion map.
    simpa [mul_assoc] using (analyticAt_const.mul hSliceAt)
  have hDiff :
      DifferentiableOn ℂ
        (fun u ↦
          ((ζ - center.2)⁻¹) ^ n * ((ζ - center.2)⁻¹ * g (Function.update x i u, ζ)))
        (Metric.ball (x i) s) := by
    exact (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).mp hAnalyticOn
  have hDiffContOnCl :
      DiffContOnCl ℂ
        (fun u ↦
          ((ζ - center.2)⁻¹) ^ n * ((ζ - center.2)⁻¹ * g (Function.update x i u, ζ)))
        (Metric.ball (x i) (R : ℝ)) := by
    apply DifferentiableOn.diffContOnCl_ball (U := Metric.ball (x i) s)
    · simpa [R] using hDiff
    · intro u hu
      have hR_lt_s : (R : ℝ) < s := by
        change s / 2 < s
        linarith
      exact Metric.closedBall_subset_ball hR_lt_s hu
  refine ⟨?_, ?_⟩
  · -- Convert the differentiable-on-ball package into the canonical power-series owner.
    simpa [R] using (hDiffContOnCl.hasFPowerSeriesOnBall (c := x i) hRpos)
  · -- The same closed-ball differentiability package also records continuity on that closed ball.
    simpa [R] using hDiffContOnCl.continuousOn_ball

/-- Helper for Theorem IV.5-extra-2: each coefficient of a scalar `cauchyPowerSeries` has the
standard interval-integral normal form coming from `circleIntegral_def_Icc`. -/
lemma cauchyPowerSeries_coeff_eq_intervalIntegral
    (φ : ℂ → ℂ) (w0 : ℂ) (R : ℝ) (n : ℕ) :
    (cauchyPowerSeries φ w0 R).coeff n =
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∫ θ in Set.Icc 0 (2 * Real.pi),
          deriv (circleMap w0 R) θ *
            (((circleMap w0 R θ - w0)⁻¹) ^ n *
              ((circleMap w0 R θ - w0)⁻¹ * φ (circleMap w0 R θ)))) := by
  -- Expand the `n`th coefficient into the circle-integral formula before switching to the scalar
  -- interval parameter used by derivative-under-the-integral arguments.
  rw [FormalMultilinearSeries.coeff]
  change cauchyPowerSeries φ w0 R n (fun _ ↦ (1 : ℂ)) = _
  rw [cauchyPowerSeries_apply]
  rw [circleIntegral_def_Icc]
  simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Theorem IV.5-extra-2: each coefficient of a scalar `cauchyPowerSeries` is the
centered boundary circle integral with kernel `((u - u0)⁻¹)^q * (u - u0)⁻¹`. -/
lemma cauchyPowerSeries_coeff_eq_centeredIntegral
    {u0 : ℂ} {R : ℝ} {F : ℂ → ℂ} (q : ℕ) :
    (cauchyPowerSeries F u0 R).coeff q =
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ u in C(u0, R), ((u - u0)⁻¹) ^ q • (u - u0)⁻¹ • F u) := by
  -- Rewrite the coefficient as the value of the multilinear term on the all-ones vector once.
  rw [FormalMultilinearSeries.coeff]
  change (cauchyPowerSeries F u0 R q) (fun _ ↦ (1 : ℂ)) = _
  rw [cauchyPowerSeries_apply]
  simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Theorem IV.5-extra-2: once the weighted boundary family is jointly continuous on the
outer sphere and inner closed disc, every scalar coefficient row is continuous on the outer sphere
and satisfies one uniform geometric Cauchy bound. -/
lemma weightedBoundarySliceCoeffRow_package_of_jointTorusContinuous_local
    {u0 c : ℂ} {innerR outerR : NNReal} {n : ℕ} {g : ℂ → ℂ → ℂ}
    (hinner : 0 < innerR)
    (hjoint :
      ContinuousOn
        (Function.uncurry fun ζ u ↦
          ((ζ - c)⁻¹) ^ n * ((ζ - c)⁻¹ * g u ζ))
        (Metric.sphere c (outerR : ℝ) ×ˢ Metric.closedBall u0 (innerR : ℝ))) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ q : ℕ,
        ContinuousOn
          (fun ζ : ℂ ↦
            (cauchyPowerSeries
              (fun u ↦ ((ζ - c)⁻¹) ^ n * ((ζ - c)⁻¹ * g u ζ))
              u0 innerR).coeff q)
          (Metric.sphere c (outerR : ℝ)) ∧
        ∀ ζ ∈ Metric.sphere c (outerR : ℝ),
          ‖(cauchyPowerSeries
              (fun u ↦ ((ζ - c)⁻¹) ^ n * ((ζ - c)⁻¹ * g u ζ))
              u0 innerR).coeff q‖ ≤
            M / (innerR : ℝ) ^ q := by
  let sOuter : Set ℂ := Metric.sphere c (outerR : ℝ)
  let sInner : Set ℂ := Metric.sphere u0 (innerR : ℝ)
  let F : ℂ → ℂ → ℂ := fun ζ u ↦ ((ζ - c)⁻¹) ^ n * ((ζ - c)⁻¹ * g u ζ)
  have hinnerReal : 0 < (innerR : ℝ) := by
    exact_mod_cast hinner
  have hFtorus :
      ContinuousOn (Function.uncurry F) (sOuter ×ˢ sInner) := by
    -- Restrict the given joint continuity from the inner closed disc to the inner boundary circle.
    refine hjoint.mono ?_
    intro p hp
    exact ⟨hp.1, Metric.sphere_subset_closedBall hp.2⟩
  have htorusCompact : IsCompact (sOuter ×ˢ sInner) :=
    (isCompact_sphere c (outerR : ℝ)).prod (isCompact_sphere u0 (innerR : ℝ))
  obtain ⟨M, hMbound⟩ :=
    htorusCompact.exists_bound_of_continuousOn (f := Function.uncurry F) hFtorus
  have hMnonneg : 0 ≤ M := by
    have hOuterPoint : c + (outerR : ℂ) ∈ sOuter := by
      simp [sOuter, Complex.norm_real, Real.norm_eq_abs]
    have hInnerPoint : u0 + (innerR : ℂ) ∈ sInner := by
      simp [sInner, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hinnerReal]
    -- Evaluate the compact bound at one explicit torus point to record the sign of `M`.
    exact le_trans (norm_nonneg _) (hMbound (c + (outerR : ℂ), u0 + (innerR : ℂ))
      ⟨hOuterPoint, hInnerPoint⟩)
  refine ⟨M, hMnonneg, ?_⟩
  intro q
  have hrowCont :
      ContinuousOn
        (fun ζ : ℂ ↦
          ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
            ∮ u in C(u0, (innerR : ℝ)), ((u - u0)⁻¹) ^ q • (u - u0)⁻¹ • F ζ u))
        sOuter := by
    have hkernelNe :
        ∀ p ∈ sOuter ×ˢ sInner, p.2 - u0 ≠ 0 := by
      intro p hp hzero
      have hpdist : dist p.2 u0 = (innerR : ℝ) := by
        simpa [sInner, Metric.mem_sphere, dist_eq_norm] using hp.2
      have : (innerR : ℝ) = 0 := by
        calc
          (innerR : ℝ) = dist p.2 u0 := hpdist.symm
          _ = 0 := by simp [dist_eq_norm, hzero]
      exact hinnerReal.ne' this
    have hkernelCont :
        ContinuousOn (fun p : ℂ × ℂ ↦ (p.2 - u0)⁻¹) (sOuter ×ˢ sInner) := by
      -- The inner boundary circle stays away from the center, so the inverse kernel is continuous.
      exact ((continuous_snd.continuousOn.sub continuousOn_const).inv₀ hkernelNe)
    have hIntegrandCont :
        ContinuousOn
          (fun p : ℂ × ℂ ↦ ((p.2 - u0)⁻¹) ^ q * ((p.2 - u0)⁻¹ * F p.1 p.2))
          (sOuter ×ˢ sInner) := by
      have hFcont : ContinuousOn (fun p : ℂ × ℂ ↦ F p.1 p.2) (sOuter ×ˢ sInner) := by
        simpa [Function.uncurry, F] using hFtorus
      -- Multiply the inner Cauchy kernel by the jointly continuous weighted boundary family.
      exact (hkernelCont.pow q).mul (hkernelCont.mul hFcont)
    have hCircleCont :
        ContinuousOn
          (fun ζ : ℂ ↦
            ∮ u in C(u0, (innerR : ℝ)), ((u - u0)⁻¹) ^ q * ((u - u0)⁻¹ * F ζ u))
          sOuter := by
      -- Integrate the torus-continuous kernel over the inner boundary circle.
      simpa [sOuter, sInner, F] using
        continuousOn_second_circleIntegral_of_continuousOn_torus_center
          (c₁ := c) (c₂ := u0) (R₁ := (outerR : ℝ)) (R₂ := (innerR : ℝ)) innerR.2
          hIntegrandCont
    -- Multiply the integrated row by the fixed scalar normalization factor `(2π i)⁻¹`.
    exact continuousOn_const.mul hCircleCont
  refine ⟨?_, ?_⟩
  · have hrowEq :
        (fun ζ : ℂ ↦
          (cauchyPowerSeries
            (fun u ↦ F ζ u) u0 innerR).coeff q) =
          (fun ζ : ℂ ↦
            ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
              ∮ u in C(u0, (innerR : ℝ)), ((u - u0)⁻¹) ^ q • (u - u0)⁻¹ • F ζ u)) := by
        funext ζ
        -- Re-express each coefficient row by the centered inner-circle Cauchy formula once.
        simpa [F, smul_eq_mul, mul_assoc] using
          (cauchyPowerSeries_coeff_eq_centeredIntegral
            (u0 := u0) (R := (innerR : ℝ)) (F := fun u ↦ F ζ u) q)
    -- Rewrite the coefficient row to the continuous centered integral model.
    change ContinuousOn (fun ζ : ℂ ↦ (cauchyPowerSeries (fun u ↦ F ζ u) u0 innerR).coeff q) sOuter
    rw [hrowEq]
    exact hrowCont
  · intro ζ hζ
    -- The compact torus bound now feeds directly into the scalar Cauchy coefficient estimate.
    change ‖(cauchyPowerSeries (fun u ↦ F ζ u) u0 innerR).coeff q‖ ≤ M / (innerR : ℝ) ^ q
    have hcoeffEq :
        (cauchyPowerSeries (fun u ↦ F ζ u) u0 (innerR : ℝ)).coeff q =
          ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
            ∮ u in C(u0, (innerR : ℝ)), ((u - u0)⁻¹) ^ q • (u - u0)⁻¹ • F ζ u) := by
      -- Normalize this coefficient once before applying the uniform circle bound.
      exact cauchyPowerSeries_coeff_eq_centeredIntegral
        (u0 := u0) (R := (innerR : ℝ)) (F := fun u ↦ F ζ u) q
    calc
      ‖(cauchyPowerSeries (fun u ↦ F ζ u) u0 (innerR : ℝ)).coeff q‖
          =
            ‖((2 * Real.pi * Complex.I : ℂ)⁻¹ •
              ∮ u in C(u0, (innerR : ℝ)), ((u - u0)⁻¹) ^ q • (u - u0)⁻¹ • F ζ u)‖ := by
                rw [hcoeffEq]
      _ ≤ (innerR : ℝ) * (M / (innerR : ℝ) ^ (q + 1)) := by
            apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const innerR.2
            intro u hu
            have hu_norm : ‖u - u0‖ = (innerR : ℝ) := by
              simpa [Metric.mem_sphere, dist_eq_norm] using hu
            calc
              ‖((u - u0)⁻¹) ^ q • (u - u0)⁻¹ • F ζ u‖
                  = ‖(u - u0)⁻¹ ^ q * ((u - u0)⁻¹ * F ζ u)‖ := by
                      simp [smul_eq_mul]
              _ = ‖(u - u0)⁻¹‖ ^ q * (‖(u - u0)⁻¹‖ * ‖F ζ u‖) := by
                    simp [norm_pow]
              _ = (innerR : ℝ)⁻¹ ^ q * ((innerR : ℝ)⁻¹ * ‖F ζ u‖) := by
                    simp [norm_inv, hu_norm]
              _ = (innerR : ℝ)⁻¹ ^ (q + 1) * ‖F ζ u‖ := by
                    rw [← mul_assoc, ← pow_succ]
              _ ≤ (innerR : ℝ)⁻¹ ^ (q + 1) * M := by
                    gcongr
                    exact hMbound (ζ, u) ⟨hζ, hu⟩
              _ = M / (innerR : ℝ) ^ (q + 1) := by
                    rw [div_eq_mul_inv, mul_comm, inv_pow]
      _ = M / (innerR : ℝ) ^ q := by
            have hRne : (innerR : ℝ) ≠ 0 := ne_of_gt hinnerReal
            rw [pow_succ, div_eq_mul_inv]
            field_simp [hRne]



/-- Helper for Theorem IV.5-extra-2: on the transported cylinder, each coefficient of the
last-variable `cauchyPowerSeries` is the normalized iterated derivative of the corresponding last
slice at the transported center. -/
lemma transportedLastCauchyCoeff_eq_invFactorial_iteratedDeriv
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i))
    {z : Fin (m + 2) → ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcyl :
      Metric.ball ((Fin.succFunEquiv ℂ (m + 1) z).1) (ρ / 2) ×ˢ
          Metric.closedBall ((Fin.succFunEquiv ℂ (m + 1) z).2) (ρ / 2) ⊆
        {p | (Fin.succFunEquiv ℂ (m + 1)).symm p ∈ D})
    (n : ℕ) (x : Fin (m + 1) → ℂ)
    (hx : x ∈ Metric.ball ((Fin.succFunEquiv ℂ (m + 1) z).1) (ρ / 2)) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    (cauchyPowerSeries (fun ζ ↦ g (x, ζ)) (e z).2 (ρ / 2)).coeff n =
      (n.factorial : ℂ)⁻¹ * iteratedDeriv n (fun w ↦ g (x, w)) (e z).2 := by
  let e := Fin.succFunEquiv ℂ (m + 1)
  let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
  have hslice :
      AnalyticOnNhd ℂ (fun w ↦ g (x, w)) (Metric.closedBall (e z).2 (ρ / 2)) := by
    -- Restrict the transported last slice to the working closed disc once, so the coefficient
    -- formula can use the standard Cauchy derivative owner directly.
    simpa [e, g] using
      transportedLastSlices_analyticOnNhd_closedBall
        (m := m) (D := D) (f := f) hsep (z := z) (r := ρ / 2) (R := ρ / 2) hcyl x hx
  have hdiff :
      DifferentiableOn ℂ (fun w ↦ g (x, w)) (Metric.closedBall (e z).2 (ρ / 2)) := by
    -- Convert the analytic owner into the differentiable closed-ball hypothesis required by the
    -- Cauchy iterated-derivative formula.
    exact hslice.differentiableOn
  have hcoeff :
      (cauchyPowerSeries (fun ζ ↦ g (x, ζ)) (e z).2 (ρ / 2)).coeff n =
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          ∮ ζ in C((e z).2, ρ / 2), (1 / (ζ - (e z).2) ^ (n + 1)) * g (x, ζ)) := by
    -- Rewrite the coefficient into the exact `1 / (ζ - c)^(n+1)` kernel expected by the Cauchy
    -- derivative formula.
    calc
      (cauchyPowerSeries (fun ζ ↦ g (x, ζ)) (e z).2 (ρ / 2)).coeff n
          = ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
              ∮ ζ in C((e z).2, ρ / 2),
                ((ζ - (e z).2)⁻¹) ^ n * ((ζ - (e z).2)⁻¹ * g (x, ζ))) := by
              simpa [e, g, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
                transportedLastCauchyCoeff_eq_centeredIntegral
                  (m := m) (f := f) (z := z) (ρ := ρ) n x
      _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
            ∮ ζ in C((e z).2, ρ / 2), (1 / (ζ - (e z).2) ^ (n + 1)) * g (x, ζ)) := by
            congr 1
            apply circleIntegral.integral_congr (by positivity)
            intro ζ hζ
            calc
              ((ζ - (e z).2)⁻¹) ^ n * ((ζ - (e z).2)⁻¹ * g (x, ζ))
                  = ((((ζ - (e z).2)⁻¹) ^ n) * (ζ - (e z).2)⁻¹) * g (x, ζ) := by
                      ring_nf
              _ = ((ζ - (e z).2)⁻¹) ^ (n + 1) * g (x, ζ) := by
                    rw [pow_succ]
              _ = (1 / (ζ - (e z).2) ^ (n + 1)) * g (x, ζ) := by
                    simp [one_div]
  have hderiv :
      ∮ ζ in C((e z).2, ρ / 2), (1 / (ζ - (e z).2) ^ (n + 1)) * g (x, ζ) =
        (2 * Real.pi * Complex.I / (n.factorial : ℂ)) *
          iteratedDeriv n (fun w ↦ g (x, w)) (e z).2 := by
    -- Apply the standard Cauchy formula for iterated derivatives on the fixed closed disc.
    simpa [smul_eq_mul] using
      (hdiff.circleIntegral_one_div_sub_center_pow_smul
        (c := (e z).2) (R := ρ / 2) (h0 := by positivity) n)
  -- Collapse the front scalar factor `(2πi)⁻¹` against the Cauchy derivative constant.
  calc
    (cauchyPowerSeries (fun ζ ↦ g (x, ζ)) (e z).2 (ρ / 2)).coeff n
        = ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
            ((2 * Real.pi * Complex.I / (n.factorial : ℂ)) *
              iteratedDeriv n (fun w ↦ g (x, w)) (e z).2)) := by
            rw [hcoeff, hderiv]
    _ = (n.factorial : ℂ)⁻¹ * iteratedDeriv n (fun w ↦ g (x, w)) (e z).2 := by
          field_simp [Complex.I_ne_zero, Real.pi_ne_zero]
