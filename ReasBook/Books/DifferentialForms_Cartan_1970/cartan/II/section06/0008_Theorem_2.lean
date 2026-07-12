import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0001_Definition_II_1_extra_1»
import DifferentialForms_Cartan_1970.II.section05.«0005_Proposition_2_1»
import DifferentialForms_Cartan_1970.II.section05.«0004_Definition_II_1_extra_4»
import DifferentialForms_Cartan_1970.II.section05.«0017_Definition_II_1_extra_10»
import DifferentialForms_Cartan_1970.II.section05.«0019_Theorem_2»
import DifferentialForms_Cartan_1970.II.section05.«0026_Definition_II_1_extra_16»
import DifferentialForms_Cartan_1970.II.section06.«0005_Corollary_1»

open scoped unitInterval

-- Declarations for this item will be appended below by the statement pipeline.

namespace Path

open Complex

/-- Helper for Theorem 2: away from the center `a`, the singular kernel splits into the removable
difference quotient plus the pure logarithmic form with coefficient `f a`. -/
private lemma dslope_indexForm_decomposition {a z : ℂ} {f : ℂ → ℂ} (hz : z ≠ a) :
    f z • indexForm a z = (dslope f a dz) z + f a • indexForm a z := by
  -- Expand both `1`-forms and simplify the difference quotient using `dslope_of_ne`.
  ext
  have hz' : z - a ≠ 0 := sub_ne_zero.mpr hz
  simp [Complex.scalarOneForm, indexForm, dslope_of_ne f hz, slope]
  field_simp [hz']
  ring

/-- Helper for Theorem 2: the removable difference quotient is holomorphic on `D`, so its contour
integral over a null-homotopic closed path in `D` vanishes. -/
private theorem removable_dslope_curveIntegral_eq_zero
    {D : Set ℂ} (hD : IsOpen D) {a z₀ : ℂ} (ha : a ∈ D) {γ : Path z₀ z₀}
    (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hγ_null : IsNullHomotopicClosedPathIn D γ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D) :
    ∫ᶜ z in γ, (dslope f a dz) z = 0 := by
  -- Route correction: use the removable-singularity owner for `dslope f a`, then replay the
  -- earlier closed-form homotopy argument locally so no later section06 import is needed.
  have hdslope : DifferentiableOn ℂ (dslope f a) D := by
    exact (Complex.differentiableOn_dslope (hD.mem_nhds ha)).2 hf
  have hω_closed : IsClosedOn (Complex.realScalarOneForm (dslope f a)) D := by
    -- Every point of `D` has a small disc on which the regularized quotient admits a primitive.
    intro w hw
    rcases holomorphic_has_local_primitive hD hdslope hw with ⟨r, hr, hball, hExact⟩
    refine ⟨Metric.ball w r, Metric.isOpen_ball, Metric.mem_ball_self hr, hball, ?_⟩
    simpa [Complex.realScalarOneForm] using hExact.hasPrimitiveOn
  have hω_cont : ContinuousOn (Complex.realScalarOneForm (dslope f a)) D := by
    rw [show Complex.realScalarOneForm (dslope f a) =
        fun z ↦ dslope f a z • (1 : ℂ →L[ℝ] ℂ) by
          funext z
          exact Complex.realScalarOneForm_eq_smul _ z]
    exact hdslope.continuousOn.smul
      (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℝ] ℂ)) D)
  rcases hγ_null with ⟨x, _, hγx⟩
  have hγD : Set.range γ ⊆ D := by
    have hγ_in : IsClosedPathIn D (γ : C(I, ℂ)) := by
      simpa using hγx.some.prop 0
    exact hγ_in.2
  have hγ_integrable : CurveIntegrable (Complex.realScalarOneForm (dslope f a)) γ :=
    Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
      hω_cont hγ_piecewise hγD
  have hEq :
      ∫ᶜ z in γ, (((dslope f a) dz) z).restrictScalars ℝ =
        ∫ᶜ z in Path.refl x, (((dslope f a) dz) z).restrictScalars ℝ := by
    -- Homotopy invariance of closed forms compares the loop with the constant path.
    simpa [Complex.realScalarOneForm] using
      (curveIntegral_eq_of_homotopic_closed_paths_of_closed_form hγx hγ_piecewise
        (isPiecewiseDifferentiable_refl x) hγ_integrable
        (CurveIntegrable.refl (Complex.realScalarOneForm (dslope f a)) x) hω_closed :
        ∫ᶜ z in γ, Complex.realScalarOneForm (dslope f a) z =
          ∫ᶜ z in Path.refl x, Complex.realScalarOneForm (dslope f a) z)
  rw [curveIntegral_restrictScalars, curveIntegral_restrictScalars] at hEq
  simpa using hEq

/-- Helper for Theorem 2: on one `C¹` subdivision piece, a continuous scalar coefficient gives an
interval-integrable pullback integrand. -/
private lemma pullback_scalar_intervalIntegrable_on_piece {z₀ z₁ : ℂ} {γ : Path z₀ z₁}
    {l u : ℝ} (hlt : l < u) (hγ : ContDiffOn ℝ 1 γ.extend (Set.Icc l u)) {φ : ℂ → ℂ}
    (hφ : ContinuousOn φ (γ.extend '' Set.Icc l u)) :
    IntervalIntegrable (fun t ↦ deriv γ.extend t * φ (γ.extend t)) MeasureTheory.volume l u := by
  -- Replace the ambient derivative by the continuous within-derivative on the closed piece.
  have hDerivWithin :
      ContinuousOn (fun t ↦ derivWithin γ.extend (Set.Icc l u) t) (Set.Icc l u) := by
    exact (hγ.derivWithin (m := 0) (uniqueDiffOn_Icc hlt) (by simp)).continuousOn
  have hCoeff : ContinuousOn (fun t ↦ φ (γ.extend t)) (Set.Icc l u) := by
    refine hφ.comp (by fun_prop) ?_
    intro t ht
    exact ⟨t, ht, rfl⟩
  have hIntWithin :
      IntervalIntegrable
        (fun t ↦ derivWithin γ.extend (Set.Icc l u) t * φ (γ.extend t)) MeasureTheory.volume l u :=
    (hDerivWithin.mul hCoeff).intervalIntegrable_of_Icc hlt.le
  -- On the interior of the piece, the within-derivative agrees with the ordinary derivative.
  refine hIntWithin.congr_ae ?_
  rw [Set.uIoc_of_le hlt.le, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
  exact by simp [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

/-- Helper for Theorem 2: interval-integrability on each `C¹` subdivision piece upgrades to
interval-integrability on `[0,1]`. -/
private lemma pullback_scalar_intervalIntegrable_of_subdivision {z₀ z₁ : ℂ} {γ : Path z₀ z₁}
    {n : ℕ} {subdiv : Fin (n + 2) → ℝ} (hsubdiv : StrictMono subdiv) (h0 : subdiv 0 = 0)
    (h1 : subdiv (Fin.last (n + 1)) = 1)
    (hpieces : ∀ i : Fin (n + 1),
      ContDiffOn ℝ 1 γ.extend (Set.Icc (subdiv i.castSucc) (subdiv i.succ))) {φ : ℂ → ℂ}
    (hφ : ∀ i : Fin (n + 1),
      ContinuousOn φ (γ.extend '' Set.Icc (subdiv i.castSucc) (subdiv i.succ))) :
    IntervalIntegrable (fun t ↦ deriv γ.extend t * φ (γ.extend t)) MeasureTheory.volume 0 1 := by
  let a : ℕ → ℝ := fun k ↦
    if hk : k ≤ n + 1 then subdiv ⟨k, Nat.lt_succ_of_le hk⟩ else 1
  have hInt :
      IntervalIntegrable (fun t ↦ deriv γ.extend t * φ (γ.extend t)) MeasureTheory.volume
        (a 0) (a (n + 1)) := by
    refine IntervalIntegrable.trans_iterate ?_
    intro k hk
    let i : Fin (n + 1) := ⟨k, hk⟩
    have hk0 : k ≤ n + 1 := Nat.le_of_lt hk
    have hk1 : k + 1 ≤ n + 1 := Nat.succ_le_of_lt hk
    have hlt : subdiv i.castSucc < subdiv i.succ := hsubdiv i.castSucc_lt_succ
    simpa [a, i, hk0, hk1] using
      pullback_scalar_intervalIntegrable_on_piece (γ := γ) hlt (hpieces i) (hφ i)
  have h0' : a 0 = 0 := by simp [a, h0]
  have h1' : a (n + 1) = 1 := by
    simpa [a] using h1
  simpa [h0', h1'] using hInt

/-- Helper for Theorem 2: the contour integral of the singular kernel splits into the removable
part and the pure index term once the coefficient is holomorphic on a neighborhood of the loop. -/
private theorem curveIntegral_div_sub_split {D : Set ℂ} (hD : IsOpen D) {a z₀ : ℂ} (ha : a ∈ D)
    {γ : Path z₀ z₀} (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hγ_null : IsNullHomotopicClosedPathIn D γ) {n : ℤ} (hγ_index : γ.HasIndexAt a n)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) :
    ∫ᶜ w in γ, f w • indexForm a w =
      ∫ᶜ w in γ, (dslope f a dz) w + f a * ∫ᶜ w in γ, indexForm a w := by
  rcases hγ_piecewise with ⟨m, subdiv, hsubdiv, h0, h1, hpieces⟩
  have hγD : ∀ t : I, γ t ∈ D := by
    -- The null-homotopy witness records that the initial loop lies in `D`.
    rcases hγ_null with ⟨x, _, hγx⟩
    rcases hγx with ⟨hγx⟩
    have hclosedIn : IsClosedPathIn D γ := by
      simpa using hγx.prop 0
    exact (isClosedPathIn_iff_forall.mp hclosedIn).2
  have hdslope :
      DifferentiableOn ℂ (dslope f a) D := by
    exact (Complex.differentiableOn_dslope (hD.mem_nhds ha)).2 hf
  have hpiece_subset_I :
      ∀ i : Fin (m + 1), Set.Icc (subdiv i.castSucc) (subdiv i.succ) ⊆ I := by
    intro i t ht
    constructor
    · calc
        0 = subdiv 0 := by symm; exact h0
        _ ≤ subdiv i.castSucc := hsubdiv.monotone (Fin.zero_le _)
        _ ≤ t := ht.1
    · calc
        t ≤ subdiv i.succ := ht.2
        _ ≤ subdiv (Fin.last (m + 1)) := hsubdiv.monotone i.succ.le_last
        _ = 1 := h1
  have hindexCoeff :
      ∀ i : Fin (m + 1),
        ContinuousOn (fun z : ℂ ↦ (z - a)⁻¹)
          (γ.extend '' Set.Icc (subdiv i.castSucc) (subdiv i.succ)) := by
    intro i
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    rintro z ⟨t, ht, rfl⟩
    have htI : t ∈ I := hpiece_subset_I i ht
    exact sub_ne_zero.mpr <| by
      simpa [Path.extend_apply γ htI] using hγ_index.ne_center ⟨t, htI⟩
  have hdslopeCoeff :
      ∀ i : Fin (m + 1),
        ContinuousOn (dslope f a)
          (γ.extend '' Set.Icc (subdiv i.castSucc) (subdiv i.succ)) := by
    intro i
    refine hdslope.continuousOn.mono ?_
    rintro z ⟨t, ht, rfl⟩
    have htI : t ∈ I := hpiece_subset_I i ht
    simpa [Path.extend_apply γ htI] using hγD ⟨t, htI⟩
  have hInt_dslope :
      IntervalIntegrable
        (fun t ↦ deriv γ.extend t * dslope f a (γ.extend t)) MeasureTheory.volume 0 1 := by
    -- Assemble the per-piece `C¹` integrability of the removable quotient.
    exact pullback_scalar_intervalIntegrable_of_subdivision hsubdiv h0 h1 hpieces hdslopeCoeff
  have hInt_index :
      IntervalIntegrable
        (fun t ↦ deriv γ.extend t * ((γ.extend t - a)⁻¹)) MeasureTheory.volume 0 1 := by
    -- The logarithmic coefficient stays continuous because the path avoids `a`.
    exact pullback_scalar_intervalIntegrable_of_subdivision hsubdiv h0 h1 hpieces hindexCoeff
  have hInt_dslope_form :
      IntervalIntegrable
        (fun t ↦ ((dslope f a dz) (γ.extend t)) (deriv γ.extend t)) MeasureTheory.volume 0 1 := by
    refine hInt_dslope.congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro t
    simp [Complex.scalarOneForm]
  have hInt_index_form :
      IntervalIntegrable
        (fun t ↦ (indexForm a (γ.extend t)) (deriv γ.extend t)) MeasureTheory.volume 0 1 := by
    refine hInt_index.congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro t
    simp [indexForm]
  have hInt_index_smul_form :
      IntervalIntegrable
        (fun t ↦ (f a • indexForm a (γ.extend t)) (deriv γ.extend t)) MeasureTheory.volume 0 1 := by
    refine (hInt_index_form.smul (f a)).congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro t
    simp [indexForm]
  have hsplit_ae :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)),
        (f (γ.extend t) • indexForm a (γ.extend t)) (deriv γ.extend t) =
          ((dslope f a dz) (γ.extend t)) (deriv γ.extend t) +
            (f a • indexForm a (γ.extend t)) (deriv γ.extend t) := by
    -- Away from `a`, the source identity is purely algebraic, so evaluate it along the path.
    rw [Set.uIoc_of_le zero_le_one]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have htI : t ∈ I := ⟨ht.1.le, ht.2⟩
    have hz : γ.extend t ≠ a := by
      simpa [Path.extend_apply γ htI] using hγ_index.ne_center ⟨t, htI⟩
    simpa using congrArg (fun ω ↦ ω (deriv γ.extend t))
      (dslope_indexForm_decomposition (a := a) (f := f) hz)
  have hsmul :
      ∫ t in 0..1, (f a • indexForm a (γ.extend t)) (deriv γ.extend t) =
        f a * ∫ t in 0..1, (indexForm a (γ.extend t)) (deriv γ.extend t) := by
    -- Pull the constant coefficient `f a` outside the interval integral of the index form.
    rw [← smul_eq_mul]
    exact hInt_index_form.integral_smul (f a)
  -- Rewrite the curve integrals as interval integrals, then integrate the pointwise splitting.
  rw [curveIntegral_eq_intervalIntegral_deriv, curveIntegral_eq_intervalIntegral_deriv,
    curveIntegral_eq_intervalIntegral_deriv]
  calc
    ∫ t in 0..1, (f (γ.extend t) • indexForm a (γ.extend t)) (deriv γ.extend t) =
        ∫ t in 0..1,
          ((dslope f a dz) (γ.extend t)) (deriv γ.extend t) +
            (f a • indexForm a (γ.extend t)) (deriv γ.extend t) := by
      exact intervalIntegral.integral_congr_ae_restrict hsplit_ae
    _ =
        (∫ t in 0..1, ((dslope f a dz) (γ.extend t)) (deriv γ.extend t)) +
          ∫ t in 0..1, (f a • indexForm a (γ.extend t)) (deriv γ.extend t) := by
      rw [intervalIntegral.integral_add hInt_dslope_form hInt_index_smul_form]
    _ =
        (∫ t in 0..1, ((dslope f a dz) (γ.extend t)) (deriv γ.extend t)) +
          f a * ∫ t in 0..1, (indexForm a (γ.extend t)) (deriv γ.extend t) := by
      rw [hsmul]

-- Proof sketch: rewrite the integrand as
-- `fun z ↦ (f z - f a) • indexForm a z + f a • indexForm a z`; the first term extends
-- holomorphically across `a`, so its integral vanishes by Theorem I', while the second is computed
-- by the canonical index owner `Path.HasIndexAt.closedPathIndex_eq`.
/-- Helper for Cartan section06 0008_Theorem_2: after restricting scalars to `ℝ`, the logarithmic
form `indexForm a` is continuous on every set that avoids the pole `a`. -/
private lemma indexForm_restrictScalars_continuousOn
    {a : ℂ} {s : Set ℂ} (hs : s ⊆ ({a} : Set ℂ)ᶜ) :
    ContinuousOn (fun z : ℂ ↦ (indexForm a z).restrictScalars ℝ) s := by
  -- The coefficient `z ↦ (z - a)⁻¹` is continuous away from its pole.
  have hInv : ContinuousOn (fun z : ℂ ↦ (z - a)⁻¹) s := by
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro z hz
    have hz_ne : z ≠ a := by
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hs hz
    exact sub_ne_zero.mpr hz_ne
  have hsmul : ContinuousOn (fun z : ℂ ↦ (z - a)⁻¹ • (1 : ℂ →L[ℝ] ℂ)) s := by
    exact hInv.smul (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℝ] ℂ)) s)
  -- Rewrite the form into the scalar-one-form spelling used by the continuity argument.
  simpa [indexForm] using hsmul

/-- Helper for Cartan section06 0008_Theorem_2: a piecewise differentiable loop with winding index
about `a` is curve-integrable against the logarithmic form `indexForm a`. -/
private lemma curveIntegrableIndexForm_of_hasIndexAt
    {z : ℂ} {γ : Path z z} {a : ℂ} {n : ℤ}
    (hγ_piecewise : γ.IsPiecewiseDifferentiable) (hγ_index : γ.HasIndexAt a n) :
    CurveIntegrable (indexForm a) γ := by
  have hRange : Set.range γ ⊆ ({a} : Set ℂ)ᶜ := by
    -- The winding-index witness already records that the loop never hits the center.
    rintro _ ⟨t, rfl⟩
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hγ_index.ne_center t
  have hInt :
      CurveIntegrable (fun z : ℂ ↦ (indexForm a z).restrictScalars ℝ) γ :=
    Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
      (D := ({a} : Set ℂ)ᶜ)
      (ω := fun z : ℂ ↦ (indexForm a z).restrictScalars ℝ)
      (indexForm_restrictScalars_continuousOn (s := ({a} : Set ℂ)ᶜ) subset_rfl)
      hγ_piecewise hRange
  -- Restricting scalars does not change curve integrability of the logarithmic form.
  simpa using hInt

/-- Cartan section06 0008_Theorem_2: if `f` is holomorphic on an open set `D`, `γ` is a piecewise
differentiable loop in `D` homotopic through closed paths in `D` to a constant loop, and `γ` has
winding index `n` about `a ∈ D`, then the Cauchy integral of `f(z) / (z - a)` along `γ` is
`(2π i) n f(a)`. -/
theorem curveIntegral_div_sub_eq_two_pi_I_mul_index
    {D : Set ℂ} (hD : IsOpen D) {a z₀ : ℂ} (ha : a ∈ D) {γ : Path z₀ z₀}
    (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hγ_null : IsNullHomotopicClosedPathIn D γ)
    {n : ℤ} (hγ_index : γ.HasIndexAt a n) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D) :
    ∫ᶜ w in γ, f w • indexForm a w =
      ((2 * Real.pi : ℂ) * Complex.I) * (n : ℂ) * f a := by
  -- First kill the removable quotient using the earlier null-homotopic vanishing theorem.
  have hremovable :
      ∫ᶜ z in γ, (dslope f a dz) z = 0 :=
    removable_dslope_curveIntegral_eq_zero hD ha hγ_piecewise hγ_null hf
  -- Next isolate the pure logarithmic term carrying the winding number.
  have hsplit :
      ∫ᶜ w in γ, f w • indexForm a w =
        ∫ᶜ w in γ, (dslope f a dz) w + f a * ∫ᶜ w in γ, indexForm a w :=
    curveIntegral_div_sub_split hD ha hγ_piecewise hγ_null hγ_index hf
  have hindex_div :
      (∫ᶜ w in γ, indexForm a w) / (((2 * Real.pi : ℂ) * Complex.I)) = (n : ℂ) := by
    -- The remaining side condition is exactly the standard integrability of `indexForm a`.
    simpa [Path.closedPathIndexAt_def, closedPathIndex_def] using
      hγ_index.closedPathIndex_eq hγ_piecewise
        (curveIntegrableIndexForm_of_hasIndexAt hγ_piecewise hγ_index)
  have hindex :
      ∫ᶜ w in γ, indexForm a w = ((2 * Real.pi : ℂ) * Complex.I) * (n : ℂ) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (div_eq_iff Complex.two_pi_I_ne_zero).1 hindex_div
  -- Substitute the vanishing removable term and the standard index integral.
  calc
    ∫ᶜ w in γ, f w • indexForm a w =
        ∫ᶜ w in γ, (dslope f a dz) w + f a * ∫ᶜ w in γ, indexForm a w := hsplit
    _ = f a * ∫ᶜ w in γ, indexForm a w := by simp [hremovable]
    _ = f a * (((2 * Real.pi : ℂ) * Complex.I) * (n : ℂ)) := by rw [hindex]
    _ = ((2 * Real.pi : ℂ) * Complex.I) * (n : ℂ) * f a := by ring

end Path
