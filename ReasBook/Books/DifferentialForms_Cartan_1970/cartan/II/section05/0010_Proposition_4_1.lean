import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0005_Proposition_2_1»
import DifferentialForms_Cartan_1970.II.section05.«0008_Proposition_3_1»
import DifferentialForms_Cartan_1970.II.section05.«0009_Definition_II_1_extra_6»
import DifferentialForms_Cartan_1970.II.section05.«0014_Remark_II_1_extra_8»

-- `lean_leansearch` is unavailable in this environment; the statement surface was matched against
-- the local `IsClosedOn` / `HasPrimitiveOn` API, Proposition 3.1, and the existing rectangle
-- boundary path precedent.

noncomputable section

open Complex MeasureTheory Metric Set Topology
open scoped unitInterval Interval

namespace Path

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for Cartan section05 0010_Proposition_4_1: reversing a piecewise differentiable path
preserves piecewise differentiability. -/
lemma IsPiecewiseDifferentiable.reverse {x y : E} {γ : Path x y}
    (hγ : γ.IsPiecewiseDifferentiable) :
    γ.symm.IsPiecewiseDifferentiable := by
  simpa using Path.IsPiecewiseDifferentiable.symm hγ

end

end Path

/-- Helper for Cartan section05 0010_Proposition_4_1: the rectangle boundary path is piecewise
differentiable because it is a concatenation of four affine segments. -/
theorem axisParallelRectangleBoundaryPath_isPiecewiseDifferentiable (z w : ℂ) :
    (axisParallelRectangleBoundaryPath z w).IsPiecewiseDifferentiable := by
  let zw : ℂ := Complex.mk w.re z.im
  let wz : ℂ := Complex.mk z.re w.im
  have hreverse :
      ((((Path.segment z wz).trans (Path.segment wz w)).trans
          (Path.segment w zw)).trans
        (Path.segment zw z)).IsPiecewiseDifferentiable := by
    -- The reversed boundary path is left-associated, so the concatenation API applies directly.
    exact (((Path.segment_isPiecewiseDifferentiable z wz).trans_of_isDifferentiable
        (Path.segment_isDifferentiable wz w)).trans_of_isDifferentiable
        (Path.segment_isDifferentiable w zw)).trans_of_isDifferentiable
        (Path.segment_isDifferentiable zw z)
  have hsymm :
      (axisParallelRectangleBoundaryPath z w).symm.IsPiecewiseDifferentiable := by
    simpa [axisParallelRectangleBoundaryPath, zw, wz, Path.segment_symm, Path.trans_symm] using
      hreverse
  simpa using hsymm.reverse

/-- Helper for Cartan section05 0010_Proposition_4_1: the canonical boundary path of an
axis-parallel rectangle stays inside that rectangle. -/
lemma axisParallelRectangleBoundaryPath_range_subset_rectangle (z w : ℂ) :
    Set.range (axisParallelRectangleBoundaryPath z w) ⊆ Complex.Rectangle z w := by
  let zw : ℂ := Complex.mk w.re z.im
  let wz : ℂ := Complex.mk z.re w.im
  have hbottom_mem : ∀ t : I, Path.segment z zw t ∈ Complex.Rectangle z w := by
    intro t
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    constructor
    · simpa [zw, Path.segment, AffineMap.lineMap_apply, segment_eq_uIcc, sub_eq_add_neg,
        mul_add, add_mul, Set.uIcc] using (lineMap_mem_segment ℝ z.re w.re t.2)
    · simp [zw, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, Set.uIcc]
  have hright_mem : ∀ t : I, Path.segment zw w t ∈ Complex.Rectangle z w := by
    intro t
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    constructor
    · simp [zw, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, Set.uIcc]
    · simpa [zw, Path.segment, AffineMap.lineMap_apply, segment_eq_uIcc, sub_eq_add_neg,
        mul_add, add_mul, Set.uIcc] using (lineMap_mem_segment ℝ z.im w.im t.2)
  have htop_mem : ∀ t : I, Path.segment w wz t ∈ Complex.Rectangle z w := by
    intro t
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    constructor
    · simpa [wz, Path.segment, AffineMap.lineMap_apply, Set.uIcc] using
        lineMap_mem_uIcc_swap (a := z.re) (b := w.re) t
    · simp [wz, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, Set.uIcc]
  have hleft_mem : ∀ t : I, Path.segment wz z t ∈ Complex.Rectangle z w := by
    intro t
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    constructor
    · simp [wz, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, Set.uIcc]
    · simpa [wz, Path.segment, AffineMap.lineMap_apply, Set.uIcc] using
        lineMap_mem_uIcc_swap (a := z.im) (b := w.im) t
  rw [axisParallelRectangleBoundaryPath, Path.trans_range, Path.trans_range, Path.trans_range]
  intro x hx
  rcases hx with hx | hx
  · rcases hx with ⟨t, rfl⟩
    exact hbottom_mem t
  · rcases hx with hx | hx
    · rcases hx with ⟨t, rfl⟩
      exact hright_mem t
    · rcases hx with hx | hx
      · rcases hx with ⟨t, rfl⟩
        exact htop_mem t
      · rcases hx with ⟨t, rfl⟩
        exact hleft_mem t

/-- Helper for Cartan section05 0010_Proposition_4_1: a complex-valued real-linear one-form is the
planar form built from its values on the real basis vectors `1` and `I`. -/
lemma complexOneForm_eq_planarDifferentialForm (ω : ℂ → ℂ →L[ℝ] ℂ) :
    ω = Complex.planarDifferentialForm (fun z ↦ ω z 1) (fun z ↦ ω z Complex.I) := by
  -- Decompose each tangent vector in the real basis `1, I` and use real linearity.
  ext z v
  rw [Complex.planarDifferentialForm_apply]
  calc
    ω z v = ω z (v.re • (1 : ℂ) + v.im • Complex.I) := by
      exact congrArg (ω z) (complex_eq_re_smul_one_add_im_smul_I v)
    _ = v.re • ω z 1 + v.im • ω z Complex.I := by
      rw [map_add, map_smul, map_smul]

/-- Cartan section05 0010_Proposition_4_1 (Proposition 4.1, first clause): a continuous
complex-valued differential form on `D` is closed if and only if, around every point of `D`,
every sufficiently small axis-parallel rectangle contained in `D` has vanishing boundary
integral. -/
theorem isClosedOn_iff_zero_rectangle_boundary_integral_locally
    {D : Set ℂ} {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : ContinuousOn ω D) :
    IsClosedOn ω D ↔
      ∀ z ∈ D, ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ D ∧
        ∀ w₀ w₁ : ℂ,
          Complex.Rectangle w₀ w₁ ⊆ Metric.ball z r →
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath w₀ w₁, ω ζ = 0 := by
  constructor
  · intro hclosed z hz
    obtain ⟨r, hr, hballD, hprimitive⟩ := IsClosedOn.exists_ball_primitive hclosed hz
    rcases hprimitive with ⟨primitive, hprimitive⟩
    refine ⟨r, hr, hballD, ?_⟩
    intro w₀ w₁ hrect
    have hrange :
        Set.range (axisParallelRectangleBoundaryPath w₀ w₁) ⊆ Metric.ball z r := by
      -- The rectangle containment hypothesis controls the whole boundary path.
      exact Set.Subset.trans
        (axisParallelRectangleBoundaryPath_range_subset_rectangle w₀ w₁) hrect
    have hpathPrimitive :=
      hprimitive.isPrimitiveAlongPath Metric.isOpen_ball
        (axisParallelRectangleBoundaryPath w₀ w₁) hrange
    have hpiecewise :
        (axisParallelRectangleBoundaryPath w₀ w₁).IsPiecewiseDifferentiable :=
      axisParallelRectangleBoundaryPath_isPiecewiseDifferentiable w₀ w₁
    -- Restrict the ambient continuity hypothesis to the chosen ball before proving integrability.
    have hωball : ContinuousOn ω (Metric.ball z r) := hω.mono hballD
    -- The rectangle boundary path is piecewise differentiable and remains inside the ball.
    have hcurveInt :
        CurveIntegrable ω (axisParallelRectangleBoundaryPath w₀ w₁) :=
      Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn hωball hpiecewise hrange
    -- Evaluate the boundary integral through the primitive and collapse the endpoint difference.
    calc
      ∫ᶜ ζ in axisParallelRectangleBoundaryPath w₀ w₁, ω ζ =
          hprimitive.alongPath (axisParallelRectangleBoundaryPath w₀ w₁) hrange 1 -
            hprimitive.alongPath (axisParallelRectangleBoundaryPath w₀ w₁) hrange 0 := by
        simpa using hpathPrimitive.curveIntegral_eq_endpoint_sub hpiecewise hcurveInt
      _ = primitive w₀ - primitive w₀ := by
        simp [IsPrimitiveOn.alongPath_apply]
      _ = 0 := sub_self _
  · intro hrectangle z hz
    -- Route correction: reuse the already proved ball primitive from Proposition 3.1 after
    -- rewriting the real-linear one-form in planar coordinates.
    obtain ⟨r, hr, hballD, hrectzero⟩ := hrectangle z hz
    let P : ℂ → ℂ := fun w ↦ ω w 1
    let Q : ℂ → ℂ := fun w ↦ ω w Complex.I
    have hform : ω = Complex.planarDifferentialForm P Q := by
      simpa [P, Q] using complexOneForm_eq_planarDifferentialForm ω
    have hωball : ContinuousOn ω (Metric.ball z r) := hω.mono hballD
    have hP_cont : ContinuousOn P (Metric.ball z r) := by
      simpa [P] using hωball.clm_apply
        (continuousOn_const : ContinuousOn (fun _ : ℂ => (1 : ℂ)) (Metric.ball z r))
    have hQ_cont : ContinuousOn Q (Metric.ball z r) := by
      simpa [Q] using hωball.clm_apply
        (continuousOn_const : ContinuousOn (fun _ : ℂ => Complex.I) (Metric.ball z r))
    have hrect_planar :
        ∀ w₀ w₁ : ℂ,
          Complex.Rectangle w₀ w₁ ⊆ Metric.ball z r →
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath w₀ w₁,
              Complex.planarDifferentialForm P Q ζ = 0 := by
      intro w₀ w₁ hsub
      -- Rewrite the given vanishing integral in planar coordinates before invoking the ball
      -- primitive criterion.
      rw [← hform]
      exact hrectzero w₀ w₁ hsub
    refine ⟨Metric.ball z r, Metric.isOpen_ball, Metric.mem_ball_self hr, hballD, ?_⟩
    refine ⟨ballPrimitive z P Q, ?_⟩
    intro w hw
    -- Proposition 3.1 already proves that the explicit ball primitive differentiates to the
    -- planar form, so only the coordinate rewrite remains here.
    rw [hform]
    exact hasFDerivAt_ballPrimitive_of_zeroRectangleBoundary (c := z) (z := w) (r := r)
      hP_cont hQ_cont hw hrect_planar

/-- For Cartan section05 0010_Proposition_4_1, if `ω = P dx + Q dy` has continuous coefficients on
the open set `D` and `∂P/∂y` is continuous on `D`, then the condition `∂P/∂y = ∂Q/∂x` is
necessary and sufficient for `ω` to be closed. -/
theorem isClosedOn_planarDifferentialForm_iff_partialDeriv_eq
    {D : Set ℂ} (hD : IsOpen D) {P Q dPdy dQdx : ℂ → ℂ}
    (hP : ContinuousOn P D) (hQ : ContinuousOn Q D)
    (hdPdy : ContinuousOn dPdy D)
    (hP_dy : ∀ z ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ D, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re) :
    IsClosedOn (P dx + Q dy) D ↔
      ∀ z ∈ D, dPdy z = dQdx z := by
  constructor
  · intro hclosed z hz
    obtain ⟨r, hr, hballD, hprimitive⟩ := IsClosedOn.exists_ball_primitive hclosed hz
    have hz_ball : z ∈ Metric.ball z r := Metric.mem_ball_self hr
    have hpartial_ball :=
      hasPrimitiveOn_imp_partialDeriv_eq (D := Metric.ball z r) Metric.isOpen_ball
        (hdPdy.mono hballD)
        (fun w hw ↦ hP_dy w (hballD hw))
        (fun w hw ↦ hQ_dx w (hballD hw))
        hprimitive
    -- Read the equality off the primitive witness on the chosen ball.
    exact hpartial_ball z hz_ball
  · intro hpartial z hz
    obtain ⟨r, hr, hballD⟩ := Metric.isOpen_iff.mp hD z hz
    have hprimitive :=
      partialDeriv_eq_imp_hasPrimitiveOn_ball z r
        (hP.mono hballD)
        (hQ.mono hballD)
        (hdPdy.mono hballD)
        (fun w hw ↦ hP_dy w (hballD hw))
        (fun w hw ↦ hQ_dx w (hballD hw))
        (fun w hw ↦ hpartial w (hballD hw))
    -- Package the ball primitive as the local closedness witness at `z`.
    exact ⟨Metric.ball z r, Metric.isOpen_ball, Metric.mem_ball_self hr, hballD, hprimitive⟩
