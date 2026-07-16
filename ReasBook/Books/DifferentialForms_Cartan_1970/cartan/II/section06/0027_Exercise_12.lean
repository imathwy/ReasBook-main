import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0001_Definition_II_1_extra_1»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0005_Proposition_2_1»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0017_Definition_II_1_extra_10»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0026_Definition_II_1_extra_16»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0033_Definition_II_1_extra_20»

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open scoped BigOperators unitInterval

noncomputable section

universe u

section

variable {ι : Type u} [Fintype ι]

attribute [local instance] Classical.propDecidable

/-- The ambient scalar field extending the boundary datum `φ` by `0` away from `frontier K`. -/
def boundaryDatum {K : Set ℂ} (φ : C(frontier K, ℂ)) : ℂ → ℂ :=
  fun z ↦ if hz : z ∈ frontier K then φ ⟨z, hz⟩ else 0

@[simp]
theorem boundaryDatum_of_mem {K : Set ℂ} (φ : C(frontier K, ℂ)) {z : ℂ} (hz : z ∈ frontier K) :
    boundaryDatum φ z = φ ⟨z, hz⟩ := by
  simp [boundaryDatum, hz]

@[simp]
theorem boundaryDatum_of_not_mem {K : Set ℂ} (φ : C(frontier K, ℂ)) {z : ℂ}
    (hz : z ∉ frontier K) :
    boundaryDatum φ z = 0 := by
  simp [boundaryDatum, hz]

/-- The scalar Cauchy density determined by `φ`, with pole of order `n + 1` at `z`. -/
def boundaryCauchyDensity {K : Set ℂ} (φ : C(frontier K, ℂ)) (z : ℂ) (n : ℕ) : ℂ → ℂ :=
  fun ζ ↦ boundaryDatum φ ζ / (ζ - z) ^ (n + 1)

/-- The boundary Cauchy transform attached to boundary datum `φ`, obtained by integrating the
canonical Cauchy density of `φ` along the closed paths of `Γ`. -/
def boundaryCauchyTransform {K : Set ℂ}
    (Γ : ι → ClosedPath ℂ)
    (φ : C(frontier K, ℂ)) : ℂ → ℂ :=
  fun z ↦
    ∑ i, ∫ᶜ ζ in (Γ i).toPath, (boundaryCauchyDensity φ z 0 dz) ζ

variable {K : Set ℂ} {Γ : ι → ClosedPath ℂ}
variable {φ : C(frontier K, ℂ)}

/-- Helper for Cartan section06 0027_Exercise_12: a continuous scalar coefficient field induces a
continuous real-linear `1`-form after restricting scalars. -/
private lemma scalarOneFormRestrictScalars_continuousOn {D : Set ℂ} {ψ : ℂ → ℂ}
    (hψ : ContinuousOn ψ D) :
    ContinuousOn (fun z : ℂ ↦ ((ψ dz) z).restrictScalars ℝ) D := by
  -- Rewrite the restricted scalar form as a scalar multiple of the real identity form.
  have hsmul : ContinuousOn (fun z : ℂ ↦ ψ z • (1 : ℂ →L[ℝ] ℂ)) D := by
    exact hψ.smul (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℝ] ℂ)) D)
  simpa using hsmul

/-- Helper for Cartan section06 0027_Exercise_12: a continuous scalar coefficient on the image of a
piecewise differentiable path gives an interval-integrable pullback on `[0,1]`. -/
private lemma boundaryScalarPullback_intervalIntegrable
    {z₀ z₁ : ℂ} {γ : Path z₀ z₁} (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    {ψ : ℂ → ℂ} (hψ : ContinuousOn ψ (Set.range γ)) :
    IntervalIntegrable (fun t ↦ deriv γ.extend t * ψ (γ.extend t)) MeasureTheory.volume 0 1 := by
  rcases hγ_piecewise with ⟨m, subdiv, hsubdiv, h0, h1, hpieces⟩
  have hCoeff :
      ∀ i : Fin (m + 1),
        ContinuousOn (fun z : ℂ ↦ ((ψ dz) z).restrictScalars ℝ)
          (γ.extend '' Set.Icc (subdiv i.castSucc) (subdiv i.succ)) := by
    intro i
    have hψpiece :
        ContinuousOn ψ (γ.extend '' Set.Icc (subdiv i.castSucc) (subdiv i.succ)) := by
      refine hψ.mono ?_
      rintro z ⟨t, ht, rfl⟩
      have htI : t ∈ Set.Icc (0 : ℝ) 1 :=
        Path.subdivision_piece_subset_unitInterval hsubdiv h0 h1 i ht
      exact ⟨⟨t, htI⟩, by simp [Path.extend_apply, htI]⟩
    exact scalarOneFormRestrictScalars_continuousOn hψpiece
  let a : ℕ → ℝ := fun k ↦ if hk : k ≤ m + 1 then subdiv ⟨k, Nat.lt_succ_of_le hk⟩ else 1
  have hInt :
      IntervalIntegrable
        (fun t ↦ (((ψ dz) (γ.extend t)).restrictScalars ℝ) (deriv γ.extend t))
        MeasureTheory.volume (a 0) (a (m + 1)) := by
    -- Reassemble the interval-integrable pullbacks from the finitely many `C¹` pieces.
    refine IntervalIntegrable.trans_iterate ?_
    intro k hk
    let i : Fin (m + 1) := ⟨k, hk⟩
    have hk0 : k ≤ m + 1 := Nat.le_of_lt hk
    have hk1 : k + 1 ≤ m + 1 := Nat.succ_le_of_lt hk
    have hlt : subdiv i.castSucc < subdiv i.succ := hsubdiv i.castSucc_lt_succ
    simpa [a, i, hk0, hk1] using
      Path.curveIntegral_intervalIntegrable_on_piece (γ := γ) hlt (hpieces i) (hCoeff i)
  have h0' : a 0 = 0 := by
    simp [a, h0]
  have h1' : a (m + 1) = 1 := by
    simpa [a] using h1
  simpa [h0', h1', mul_comm] using hInt

omit [Fintype ι] in
/-- Helper for Cartan section06 0027_Exercise_12: on each boundary path, the zero extension
`boundaryDatum φ` agrees continuously with `φ`. -/
private lemma boundaryDatum_continuousOn_pathRange
    (hΓ_frontier : ∀ i, Set.range (Γ i).toPath ⊆ frontier K)
    (i : ι) :
    ContinuousOn (boundaryDatum φ) (Set.range (Γ i).toPath) := by
  rw [continuousOn_iff_continuous_restrict]
  change Continuous fun p : Set.range (Γ i).toPath ↦ boundaryDatum φ p.1
  let e : Set.range (Γ i).toPath → frontier K := fun p ↦ ⟨p.1, hΓ_frontier i p.2⟩
  have he : Continuous e := by
    exact Continuous.subtype_mk continuous_subtype_val (fun p ↦ hΓ_frontier i p.2)
  -- Along the path image, the extension never uses the zero branch.
  have hphi : Continuous fun p : Set.range (Γ i).toPath ↦ φ (e p) := φ.continuous.comp he
  convert hphi using 1
  funext p
  simp [e, boundaryDatum, hΓ_frontier i p.2]

omit [Fintype ι] in
/-- Helper for Cartan section06 0027_Exercise_12: off the boundary, the Cauchy density is
continuous along each boundary path image. -/
private lemma boundaryCauchyDensity_continuousOn_pathRange
    (hΓ_frontier : ∀ i, Set.range (Γ i).toPath ⊆ frontier K)
    (i : ι) (n : ℕ) {z : ℂ} (hz : z ∈ (frontier K)ᶜ) :
    ContinuousOn (boundaryCauchyDensity φ z n) (Set.range (Γ i).toPath) := by
  have hnum : ContinuousOn (boundaryDatum φ) (Set.range (Γ i).toPath) :=
    boundaryDatum_continuousOn_pathRange (φ := φ) hΓ_frontier i
  have hden :
      ContinuousOn (fun ζ : ℂ ↦ (ζ - z) ^ (n + 1)) (Set.range (Γ i).toPath) :=
    (continuousOn_id.sub continuousOn_const).pow (n + 1)
  have hden_ne : ∀ ζ ∈ Set.range (Γ i).toPath, (ζ - z) ^ (n + 1) ≠ 0 := by
    intro ζ hζ
    apply pow_ne_zero _
    apply sub_ne_zero.mpr
    intro hEq
    have hz_frontier : z ∈ frontier K := hEq ▸ hΓ_frontier i hζ
    exact hz hz_frontier
  -- The denominator never vanishes because the whole path image lies on `frontier K`.
  simpa [boundaryCauchyDensity] using hnum.div hden hden_ne

/-- Helper for Cartan section06 0027_Exercise_12: the scalar kernel
`ζ ↦ boundaryDatum φ ζ / (ζ - z)^(n+1)` has the expected derivative in the parameter `z`. -/
private lemma boundaryCauchyKernelOrder_hasDerivAt
    {n : ℕ} {ζ x : ℂ} (hζx : ζ ≠ x) :
    HasDerivAt (fun z : ℂ ↦ boundaryDatum φ ζ / (ζ - z) ^ (n + 1))
      (((n + 1 : ℂ) * boundaryDatum φ ζ) / (ζ - x) ^ (n + 2)) x := by
  -- Differentiate `(ζ - z)⁻¹`, then raise it to the `(n + 1)`st power.
  have hsub : HasDerivAt (fun z : ℂ ↦ ζ - z) (-1) x := by
    simpa using (HasDerivAt.const_sub ζ (hasDerivAt_id x))
  have hinv : HasDerivAt (fun z : ℂ ↦ (ζ - z)⁻¹) ((ζ - x)⁻¹ ^ (2 : ℕ)) x := by
    simpa [div_eq_mul_inv, pow_two, mul_assoc] using hsub.inv (sub_ne_zero.mpr hζx)
  have hpow := hinv.pow (n + 1)
  simpa [div_eq_mul_inv, inv_pow, pow_succ, pow_two, mul_assoc, mul_left_comm, mul_comm] using
    hpow.const_mul (boundaryDatum φ ζ)

omit [Fintype ι] in
/-- Helper for Cartan section06 0027_Exercise_12: differentiating one contour component inserts
the next Cauchy-kernel power. -/
private lemma boundaryCauchyComponentOrder_hasDerivAt
    (hΓ_frontier : ∀ i, Set.range (Γ i).toPath ⊆ frontier K)
    (hΓ_piecewise : ∀ i, (Γ i).toPath.IsPiecewiseDifferentiable)
    (i : ι) (n : ℕ) {x : ℂ} (hx : x ∈ (frontier K)ᶜ) :
    HasDerivAt
      (fun z ↦ ∫ᶜ ζ in (Γ i).toPath, (boundaryCauchyDensity φ z n dz) ζ)
      ((n + 1 : ℂ) * ∫ᶜ ζ in (Γ i).toPath, (boundaryCauchyDensity φ x (n + 1) dz) ζ) x := by
  let γ := (Γ i).toPath
  let F : ℂ → ℝ → ℂ := fun z t ↦
    deriv γ.extend t * boundaryCauchyDensity φ z n (γ.extend t)
  let F' : ℂ → ℝ → ℂ := fun z t ↦
    deriv γ.extend t * ((n + 1 : ℂ) * boundaryCauchyDensity φ z (n + 1) (γ.extend t))
  obtain ⟨ρ, hρ, hρball⟩ := Metric.isOpen_iff.mp isClosed_frontier.isOpen_compl x hx
  have hhalfρ : 0 < ρ / 2 := half_pos hρ
  have hclosedBall : Metric.closedBall x (ρ / 2) ⊆ (frontier K)ᶜ := by
    exact (Metric.closedBall_subset_ball (half_lt_self hρ)).trans hρball
  have hF_meas :
      ∀ᶠ z in nhds x,
        MeasureTheory.AEStronglyMeasurable (F z)
          (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    filter_upwards [Metric.ball_mem_nhds x hhalfρ] with z hz
    have hz' : z ∈ (frontier K)ᶜ := by
      exact hρball (Metric.mem_ball.2 (lt_trans (Metric.mem_ball.1 hz) (half_lt_self hρ)))
    have hInt :
        IntervalIntegrable (F z) MeasureTheory.volume 0 1 := by
      -- Keep the contour component in the interval-pullback spelling required by dominated
      -- differentiation.
      simpa [F, γ] using
        boundaryScalarPullback_intervalIntegrable (γ := γ) (hγ_piecewise := hΓ_piecewise i)
          (ψ := boundaryCauchyDensity φ z n)
          (boundaryCauchyDensity_continuousOn_pathRange (φ := φ) hΓ_frontier i n hz')
    exact hInt.aestronglyMeasurable_restrict_uIoc
  have hF_int : IntervalIntegrable (F x) MeasureTheory.volume 0 1 := by
    -- At the base point `x`, the same pullback integrability gives the interval integral model of
    -- the contour integral.
    simpa [F, γ] using
      boundaryScalarPullback_intervalIntegrable (γ := γ) (hγ_piecewise := hΓ_piecewise i)
        (ψ := boundaryCauchyDensity φ x n)
        (boundaryCauchyDensity_continuousOn_pathRange (φ := φ) hΓ_frontier i n hx)
  have hF'_meas :
      MeasureTheory.AEStronglyMeasurable (F' x)
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    have hCoeff :
        ContinuousOn (fun ζ ↦ (n + 1 : ℂ) * boundaryCauchyDensity φ x (n + 1) ζ) (Set.range γ) := by
      exact
        continuousOn_const.mul
          (boundaryCauchyDensity_continuousOn_pathRange (φ := φ) hΓ_frontier i (n + 1) hx)
    have hInt : IntervalIntegrable (F' x) MeasureTheory.volume 0 1 := by
      -- Match the interval theorem's differentiated coefficient exactly, so no extra transport is
      -- needed inside the `HasDerivAt` proof.
      simpa [F', γ, mul_assoc, mul_left_comm, mul_comm] using
        boundaryScalarPullback_intervalIntegrable (γ := γ) (hγ_piecewise := hΓ_piecewise i)
          (ψ := fun ζ ↦ (n + 1 : ℂ) * boundaryCauchyDensity φ x (n + 1) ζ) hCoeff
    exact hInt.aestronglyMeasurable_restrict_uIoc
  let B : Set (ℂ × ℂ) := Set.range γ ×ˢ Metric.closedBall x (ρ / 2)
  let G : ℂ × ℂ → ℂ := fun p ↦
    ((n + 1 : ℂ) * boundaryDatum φ p.1) / (p.1 - p.2) ^ (n + 1 + 1)
  have hB : IsCompact B := (isCompact_range γ.continuous).prod (isCompact_closedBall x (ρ / 2))
  have hGcont : ContinuousOn G B := by
    have hNum :
        ContinuousOn (fun p : ℂ × ℂ ↦ (n + 1 : ℂ) * boundaryDatum φ p.1) B := by
      have hDatum :
          ContinuousOn (fun p : ℂ × ℂ ↦ boundaryDatum φ p.1) B := by
        exact
          (boundaryDatum_continuousOn_pathRange (φ := φ) hΓ_frontier i).comp
            continuous_fst.continuousOn (fun p hp ↦ hp.1)
      exact continuousOn_const.mul hDatum
    have hDen :
        ContinuousOn (fun p : ℂ × ℂ ↦ (p.1 - p.2) ^ (n + 1 + 1)) B := by
      exact (continuous_fst.continuousOn.sub continuous_snd.continuousOn).pow (n + 1 + 1)
    have hDen_ne : ∀ p ∈ B, (p.1 - p.2) ^ (n + 1 + 1) ≠ 0 := by
      intro p hp
      apply pow_ne_zero _
      apply sub_ne_zero.mpr
      intro hpEq
      have hpFrontier : p.1 ∈ frontier K := hΓ_frontier i hp.1
      have hpCompl : p.2 ∈ (frontier K)ᶜ := hclosedBall hp.2
      exact hpCompl (hpEq ▸ hpFrontier)
    simpa [G] using hNum.div hDen hDen_ne
  obtain ⟨M, hM⟩ := hB.exists_bound_of_continuousOn (f := G) hGcont
  have h_bound :
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIoc (0 : ℝ) 1 →
          ∀ z ∈ Metric.ball x (ρ / 2), ‖F' z t‖ ≤ M * ‖deriv γ.extend t‖ := by
    filter_upwards with t
    intro ht z hz
    have hz' : z ∈ Metric.closedBall x (ρ / 2) := by
      exact Metric.mem_closedBall.2 (le_of_lt (Metric.mem_ball.1 hz))
    have htI : t ∈ I := by
      have ht01 : t ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le zero_le_one] using ht
      exact ⟨le_of_lt ht01.1, ht01.2⟩
    have hpair : (γ.extend t, z) ∈ B := by
      refine ⟨?_, hz'⟩
      refine ⟨⟨t, htI⟩, ?_⟩
      simp [γ, Path.extend_apply, htI]
    have hGval :
        G (γ.extend t, z) = (n + 1 : ℂ) * boundaryCauchyDensity φ z (n + 1) (γ.extend t) := by
      simp [G, boundaryCauchyDensity, div_eq_mul_inv, mul_assoc]
    calc
      ‖F' z t‖ = ‖deriv γ.extend t * G (γ.extend t, z)‖ := by
        simp [F', hGval]
      _ = ‖deriv γ.extend t‖ * ‖G (γ.extend t, z)‖ := by
        simp
      _ ≤ ‖deriv γ.extend t‖ * M := by
        gcongr
        exact hM _ hpair
      _ = M * ‖deriv γ.extend t‖ := by ring
  have hDerivInt :
      IntervalIntegrable (fun t ↦ deriv γ.extend t) MeasureTheory.volume 0 1 := by
    have hConst :
        IntervalIntegrable (fun t ↦ deriv γ.extend t * (1 : ℂ)) MeasureTheory.volume 0 1 := by
      -- The unit coefficient recovers the raw derivative pullback needed for the domination bound.
      simpa [γ] using
        boundaryScalarPullback_intervalIntegrable (γ := γ) (hγ_piecewise := hΓ_piecewise i)
          (ψ := fun _ ↦ (1 : ℂ)) (by
            simpa using
              (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (1 : ℂ)) (Set.range γ)))
    simpa using hConst
  have hBoundInt :
      IntervalIntegrable (fun t ↦ M * ‖deriv γ.extend t‖) MeasureTheory.volume 0 1 :=
    hDerivInt.norm.const_mul M
  have h_diff :
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIoc (0 : ℝ) 1 →
          ∀ z ∈ Metric.ball x (ρ / 2), HasDerivAt (fun z' ↦ F z' t) (F' z t) z := by
    filter_upwards with t
    intro ht z hz
    have htI : t ∈ I := by
      have ht01 : t ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le zero_le_one] using ht
      exact ⟨le_of_lt ht01.1, ht01.2⟩
    have hz' : z ∈ (frontier K)ᶜ := by
      exact hρball (Metric.mem_ball.2 (lt_trans (Metric.mem_ball.1 hz) (half_lt_self hρ)))
    have hζz : γ.extend t ≠ z := by
      intro hEq
      have hRange : γ.extend t ∈ Set.range γ := by
        refine ⟨⟨t, htI⟩, ?_⟩
        simp [γ, Path.extend_apply, htI]
      have hzFrontier : z ∈ frontier K := hEq ▸ hΓ_frontier i hRange
      exact hz' hzFrontier
    -- Differentiate the scalar kernel in `z`, then multiply by the fixed path derivative.
    simpa [F, F', γ, boundaryCauchyDensity, div_eq_mul_inv, mul_assoc] using
      (boundaryCauchyKernelOrder_hasDerivAt (φ := φ) (n := n) (ζ := γ.extend t) (x := z)
        hζz).const_mul (deriv γ.extend t)
  -- Route correction: prove the derivative theorem entirely in interval-integral normal form, and
  -- only then transport back to the contour integral statement.
  simpa [curveIntegral_eq_intervalIntegral_deriv, F, F', γ, Complex.scalarOneForm_apply,
    intervalIntegral.integral_const_mul, mul_assoc, mul_left_comm, mul_comm] using
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds x hhalfρ) hF_meas hF_int hF'_meas h_bound hBoundInt h_diff).2

/-- Helper for Cartan section06 0027_Exercise_12: summing the componentwise derivative formulas
gives the derivative of the full boundary transform with the `n`th Cauchy kernel. -/
private lemma boundaryCauchyOrder_hasDerivAt
    (hΓ_frontier : ∀ i, Set.range (Γ i).toPath ⊆ frontier K)
    (hΓ_piecewise : ∀ i, (Γ i).toPath.IsPiecewiseDifferentiable)
    (n : ℕ) {x : ℂ} (hx : x ∈ (frontier K)ᶜ) :
    HasDerivAt
      (fun z ↦ ∑ i, ∫ᶜ ζ in (Γ i).toPath, (boundaryCauchyDensity φ z n dz) ζ)
      ((n + 1 : ℂ) * ∑ i, ∫ᶜ ζ in (Γ i).toPath, (boundaryCauchyDensity φ x (n + 1) dz) ζ) x := by
  have hsum :
      HasDerivAt
        (fun z ↦ ∑ i, ∫ᶜ ζ in (Γ i).toPath, (boundaryCauchyDensity φ z n dz) ζ)
        (∑ i, (n + 1 : ℂ) * ∫ᶜ ζ in (Γ i).toPath, (boundaryCauchyDensity φ x (n + 1) dz) ζ)
        x := by
    -- Package the componentwise derivative formulas first, then normalize the outer scalar once.
    exact HasDerivAt.fun_sum (u := Finset.univ) fun j _ ↦
      boundaryCauchyComponentOrder_hasDerivAt (φ := φ) hΓ_frontier hΓ_piecewise j n hx
  simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hsum

/-- Helper for Cartan section06 0027_Exercise_12: an identity on the open complement of the
boundary transports directly to an equality of ordinary derivatives there. -/
private lemma eqOn_deriv_eq_of_boundaryCompl {f g : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ (frontier K)ᶜ) (hEq : Set.EqOn f g ((frontier K)ᶜ)) :
    deriv f z = deriv g z := by
  -- Turn the complement-wide equality into eventual equality in `𝓝 z`, then use the canonical
  -- derivative congruence theorem.
  exact Filter.EventuallyEq.deriv_eq
    (Set.EqOn.eventuallyEq_of_mem hEq (isClosed_frontier.isOpen_compl.mem_nhds hz))

/-- Helper for Cartan section06 0027_Exercise_12: on the whole complement of `frontier K`, the
iterated derivatives of the boundary transform are given by the expected higher-order Cauchy
integrals. -/
private lemma boundaryCauchyTransform_iteratedDeriv_eq_on_compl
    (hΓ_frontier : ∀ i, Set.range (Γ i).toPath ⊆ frontier K)
    (hΓ_piecewise : ∀ i, (Γ i).toPath.IsPiecewiseDifferentiable) :
    ∀ n : ℕ,
      Set.EqOn
        (fun z ↦ iteratedDeriv n (boundaryCauchyTransform Γ φ) z)
        (fun z ↦ (n.factorial : ℂ) *
          ∑ i, ∫ᶜ ζ in (Γ i).toPath, (boundaryCauchyDensity φ z n dz) ζ)
        ((frontier K)ᶜ)
  | 0 => by
      intro z hz
      -- At order `0`, this is just the definition of the boundary transform.
      simp [boundaryCauchyTransform]
  | n + 1 => by
      intro z hz
      have ih := boundaryCauchyTransform_iteratedDeriv_eq_on_compl hΓ_frontier hΓ_piecewise n
      have hderivEq :
          deriv (iteratedDeriv n (boundaryCauchyTransform Γ φ)) z =
            deriv
              (fun w ↦
                (n.factorial : ℂ) *
                  ∑ i, ∫ᶜ ζ in (Γ i).toPath, (boundaryCauchyDensity φ w n dz) ζ) z :=
        eqOn_deriv_eq_of_boundaryCompl (K := K) (hz := hz) ih
      have hstep :
          HasDerivAt
            (fun w ↦ ∑ i, ∫ᶜ ζ in (Γ i).toPath, (boundaryCauchyDensity φ w n dz) ζ)
            ((n + 1 : ℂ) *
              ∑ i, ∫ᶜ ζ in (Γ i).toPath, (boundaryCauchyDensity φ z (n + 1) dz) ζ) z :=
        boundaryCauchyOrder_hasDerivAt (φ := φ) hΓ_frontier hΓ_piecewise n hz
      -- Differentiate the induction formula once more on the open complement and collapse the
      -- factorial normalization at the end.
      calc
        iteratedDeriv (n + 1) (boundaryCauchyTransform Γ φ) z =
            deriv (iteratedDeriv n (boundaryCauchyTransform Γ φ)) z := by
              simp [iteratedDeriv_succ]
        _ =
            deriv
              (fun w ↦
                (n.factorial : ℂ) *
                  ∑ i, ∫ᶜ ζ in (Γ i).toPath, (boundaryCauchyDensity φ w n dz) ζ) z := hderivEq
        _ =
            (n.factorial : ℂ) *
              ((n + 1 : ℂ) *
                ∑ i, ∫ᶜ ζ in (Γ i).toPath, (boundaryCauchyDensity φ z (n + 1) dz) ζ) := by
              simpa using (hstep.const_mul (n.factorial : ℂ)).deriv
        _ =
            ((n + 1).factorial : ℂ) *
              ∑ i, ∫ᶜ ζ in (Γ i).toPath, (boundaryCauchyDensity φ z (n + 1) dz) ζ := by
              simp [Nat.factorial_succ, Nat.cast_mul, mul_assoc, mul_comm]

-- Proof sketch: on any closed ball avoiding the boundary image, expand
-- `(ζ - z)⁻¹ = (ζ - a)⁻¹ * (1 - (z - a) / (ζ - a))⁻¹` into the normally convergent geometric series
-- from Theorem 3, interchange the finite sum and the resulting path-parameter integrals with the
-- series, and read off the coefficients of the power series centered at `a`.
/-- Part (1) of Cartan section06 0027_Exercise_12: if each closed path of `Γ` is piecewise
differentiable, lies in `frontier K`,
and the closed ball `|z - a| ≤ r` avoids `frontier K`, then the boundary Cauchy transform admits a
normally convergent power series expansion on that ball, hence on a neighborhood of `a`. -/
theorem boundaryCauchyTransform_hasFPowerSeriesOnBall
    (hΓ_frontier : ∀ i, Set.range (Γ i).toPath ⊆ frontier K)
    (hΓ_piecewise : ∀ i, (Γ i).toPath.IsPiecewiseDifferentiable)
    {a : ℂ} {r : ℝ}
    (hr : 0 < r) (hball : Metric.closedBall a r ⊆ (frontier K)ᶜ) :
    ∃ c : ℕ → ℂ,
      HasFPowerSeriesOnBall (boundaryCauchyTransform Γ φ) (ofScalars ℂ c) a
        (ENNReal.ofReal r) := by
  let R : NNReal := Real.toNNReal r
  have hR : 0 < R := by
    simp [R, hr]
  have hDiffOn : DifferentiableOn ℂ (boundaryCauchyTransform Γ φ) (Metric.closedBall a R) := by
    intro z hz
    have hz' : z ∈ (frontier K)ᶜ := by
      exact hball (by simpa [R, Real.toNNReal_of_nonneg hr.le] using hz)
    -- Holomorphy on the closed ball comes from differentiating each contour component.
    have hdiff : DifferentiableAt ℂ (fun z ↦
        ∑ i, ∫ᶜ ζ in (Γ i).toPath, (boundaryCauchyDensity φ z 0 dz) ζ) z :=
      (boundaryCauchyOrder_hasDerivAt (φ := φ) hΓ_frontier hΓ_piecewise 0 hz').differentiableAt
    simpa [boundaryCauchyTransform] using hdiff.differentiableWithinAt
  have hp : HasFPowerSeriesOnBall (boundaryCauchyTransform Γ φ)
      (cauchyPowerSeries (boundaryCauchyTransform Γ φ) a R) a R :=
    hDiffOn.hasFPowerSeriesOnBall hR
  let c : ℕ → ℂ := fun n ↦ cauchyPowerSeries (boundaryCauchyTransform Γ φ) a R n (fun _ ↦ (1 : ℂ))
  have hseries :
      cauchyPowerSeries (boundaryCauchyTransform Γ φ) a R = ofScalars ℂ c := by
    funext n
    calc
      cauchyPowerSeries (boundaryCauchyTransform Γ φ) a R n =
          ContinuousMultilinearMap.mkPiRing ℂ (Fin n)
            (cauchyPowerSeries (boundaryCauchyTransform Γ φ) a R n (fun _ ↦ (1 : ℂ))) := by
        symm
        exact ContinuousMultilinearMap.mkPiRing_apply_one_eq_self _
      _ = ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (c n) := by
        rfl
      _ = ofScalars ℂ c n := by
        ext
        simp [c, FormalMultilinearSeries.ofScalars, ContinuousMultilinearMap.mkPiRing_apply,
          ContinuousMultilinearMap.mkPiAlgebraFin_apply, mul_comm]
  have hRenn : (R : ENNReal) = ENNReal.ofReal r := by
    rw [show R = Real.toNNReal r by rfl, ENNReal.ofReal_eq_coe_nnreal,
      Real.toNNReal_of_nonneg hr.le]
  exact ⟨c, by simpa [hRenn, hseries] using hp⟩

-- Proof sketch: apply the previous power-series theorem on some closed ball around `a` contained
-- in the boundary complement, then pass from a convergent local power series representation to
-- analyticity at `a`.
/-- If each closed path of `Γ` is piecewise differentiable and lies in `frontier K`, then the
boundary Cauchy transform is analytic at every point of the complement of `frontier K`. -/
theorem boundaryCauchyTransform_analyticAt
    (hΓ_frontier : ∀ i, Set.range (Γ i).toPath ⊆ frontier K)
    (hΓ_piecewise : ∀ i, (Γ i).toPath.IsPiecewiseDifferentiable)
    {a : ℂ}
    (ha : a ∈ (frontier K)ᶜ) :
    AnalyticAt ℂ (boundaryCauchyTransform Γ φ) a := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isClosed_frontier.isOpen_compl a ha
  have hseries :
      ∃ c : ℕ → ℂ,
        HasFPowerSeriesOnBall (boundaryCauchyTransform Γ φ) (ofScalars ℂ c) a
          (ENNReal.ofReal (r / 2)) :=
    boundaryCauchyTransform_hasFPowerSeriesOnBall hΓ_frontier hΓ_piecewise (half_pos hr)
      ((Metric.closedBall_subset_ball (half_lt_self hr)).trans hball)
  rcases hseries with ⟨c, hc⟩
  exact hc.analyticAt

-- Proof sketch: use the local power-series expansion from part (1) on a ball around `a` disjoint
-- from the boundary, differentiate the geometric series termwise, and keep the resulting boundary
-- integrals on the direct path-pullback surface.
/-- Cartan section06 0027_Exercise_12: Exercise 12 (2): for every natural number `n` and every
point `a` off `frontier K`, the
`n`-th complex derivative of the boundary Cauchy transform is `n!` times the boundary integral
with kernel `(ζ - a)^(-(n + 1))` over the piecewise differentiable paths of `Γ` lying in
`frontier K`. -/
theorem boundaryCauchyTransform_iteratedDeriv_eq
    (hΓ_frontier : ∀ i, Set.range (Γ i).toPath ⊆ frontier K)
    (hΓ_piecewise : ∀ i, (Γ i).toPath.IsPiecewiseDifferentiable)
    {n : ℕ} {a : ℂ}
    (ha : a ∈ (frontier K)ᶜ) :
    iteratedDeriv n (boundaryCauchyTransform Γ φ) a =
      (n.factorial : ℂ) *
        ∑ i, ∫ᶜ ζ in (Γ i).toPath, (boundaryCauchyDensity φ a n dz) ζ := by
  -- Specialize the complement-wide iterated-derivative formula at the chosen point `a`.
  exact boundaryCauchyTransform_iteratedDeriv_eq_on_compl
    (φ := φ) hΓ_frontier hΓ_piecewise n ha

end
