import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0003_Lemma_II_1_extra_3»
import DifferentialForms_Cartan_1970.II.section05.«0004_Definition_II_1_extra_4»
import DifferentialForms_Cartan_1970.II.section05.«0007_Theorem_II_1_extra_5»
import DifferentialForms_Cartan_1970.II.section05.«0014_Remark_II_1_extra_8»

noncomputable section

open Complex MeasureTheory Metric Set Topology
open scoped unitInterval
open scoped Interval

/-- Helper for Cartan section05 0008_Proposition_3_1: the `dx` contribution along a horizontal
segment is exactly the interval integral of `P`. -/
lemma horizontal_segment_planarIntegral_eq_intervalIntegral
    (P Q : ℂ → ℂ) (x₀ x₁ b : ℝ) :
    (∫ᶜ ζ in Path.segment (Complex.mk x₀ b) (Complex.mk x₁ b),
        Complex.planarDifferentialForm P Q ζ) =
      ∫ x in x₀..x₁, P (Complex.mk x b) := by
  -- Rewrite the segment integral to the affine parameter interval `[0, 1]`.
  rw [curveIntegral_segment]
  have hline : ∀ t : ℝ,
      AffineMap.lineMap (Complex.mk x₀ b) (Complex.mk x₁ b) t =
        Complex.mk ((x₁ - x₀) * t + x₀) b := by
    intro t
    apply Complex.ext <;> simp [AffineMap.lineMap_apply, sub_eq_add_neg]
    ring
  simp [hline]
  -- The remaining affine change of variables is the standard interval-integral identity.
  simpa [sub_eq_add_neg, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using
    (intervalIntegral.smul_integral_comp_mul_add
      (f := fun x ↦ P (Complex.mk x b)) (a := (0 : ℝ)) (b := 1) (c := x₁ - x₀) (d := x₀))

/-- Helper for Cartan section05 0008_Proposition_3_1: the `dy` contribution along a vertical
segment is exactly the interval integral of `Q`. -/
lemma vertical_segment_planarIntegral_eq_intervalIntegral
    (P Q : ℂ → ℂ) (a y₀ y₁ : ℝ) :
    (∫ᶜ ζ in Path.segment (Complex.mk a y₀) (Complex.mk a y₁),
        Complex.planarDifferentialForm P Q ζ) =
      ∫ y in y₀..y₁, Q (Complex.mk a y) := by
  -- Rewrite the segment integral to the affine parameter interval `[0, 1]`.
  rw [curveIntegral_segment]
  have hline : ∀ t : ℝ,
      AffineMap.lineMap (Complex.mk a y₀) (Complex.mk a y₁) t =
        Complex.mk a ((y₁ - y₀) * t + y₀) := by
    intro t
    apply Complex.ext <;> simp [AffineMap.lineMap_apply, sub_eq_add_neg]
    ring
  simp [hline]
  -- The remaining affine change of variables is the standard interval-integral identity.
  simpa [sub_eq_add_neg, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using
    (intervalIntegral.smul_integral_comp_mul_add
      (f := fun y ↦ Q (Complex.mk a y)) (a := (0 : ℝ)) (b := 1) (c := y₁ - y₀) (d := y₀))

/-- Helper for Cartan section05 0008_Proposition_3_1: along a horizontal segment contained in `D`
where the planar form is curve integrable, the primitive changes by the interval integral of the
`dx` coefficient. -/
lemma primitive_horizontal_difference_eq_integral
    {D : Set ℂ} (hD : IsOpen D) {P Q primitive : ℂ → ℂ}
    (hprimitive : IsPrimitiveOn D (Complex.planarDifferentialForm P Q) primitive)
    {x₀ x₁ y : ℝ} (hseg : Set.uIcc x₀ x₁ ⊆ {x | Complex.mk x y ∈ D})
    (hγ_int :
      CurveIntegrable (Complex.planarDifferentialForm P Q)
        (Path.segment (Complex.mk x₀ y) (Complex.mk x₁ y))) :
    primitive (Complex.mk x₁ y) - primitive (Complex.mk x₀ y) =
      ∫ x in x₀..x₁, P (Complex.mk x y) := by
  let γ : Path (Complex.mk x₀ y) (Complex.mk x₁ y) :=
    Path.segment (Complex.mk x₀ y) (Complex.mk x₁ y)
  have hγ_apply (t : I) :
      γ t = Complex.mk (AffineMap.lineMap x₀ x₁ (t : ℝ)) y := by
    apply Complex.ext <;> simp [γ, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg]
    ring_nf
  have hγD : Set.range γ ⊆ D := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    have hx : AffineMap.lineMap x₀ x₁ (t : ℝ) ∈ Set.uIcc x₀ x₁ := by
      simpa [segment_eq_uIcc] using (lineMap_mem_segment ℝ x₀ x₁ t.2)
    rw [hγ_apply t]
    exact hseg hx
  have hγprimitive := hprimitive.isPrimitiveAlongPath hD γ hγD
  -- Route correction: the endpoint formula also needs curve integrability of the segment path.
  have hγintegral :=
    hγprimitive.curveIntegral_eq_endpoint_sub (Path.segment_isPiecewiseDifferentiable _ _) <| by
      simpa [γ] using hγ_int
  -- Rewrite the segment integral to the horizontal interval integral used in the source proof.
  rw [horizontal_segment_planarIntegral_eq_intervalIntegral (P := P) (Q := Q) (x₀ := x₀)
    (x₁ := x₁) (b := y)] at hγintegral
  simpa [γ] using hγintegral.symm

/-- Helper for Cartan section05 0008_Proposition_3_1: along a vertical segment contained in `D`
where the planar form is curve integrable, the primitive changes by the interval integral of the
`dy` coefficient. -/
lemma primitive_vertical_difference_eq_integral
    {D : Set ℂ} (hD : IsOpen D) {P Q primitive : ℂ → ℂ}
    (hprimitive : IsPrimitiveOn D (Complex.planarDifferentialForm P Q) primitive)
    {x y₀ y₁ : ℝ} (hseg : Set.uIcc y₀ y₁ ⊆ {y | Complex.mk x y ∈ D})
    (hγ_int :
      CurveIntegrable (Complex.planarDifferentialForm P Q)
        (Path.segment (Complex.mk x y₀) (Complex.mk x y₁))) :
    primitive (Complex.mk x y₁) - primitive (Complex.mk x y₀) =
      ∫ y in y₀..y₁, Q (Complex.mk x y) := by
  let γ : Path (Complex.mk x y₀) (Complex.mk x y₁) :=
    Path.segment (Complex.mk x y₀) (Complex.mk x y₁)
  have hγ_apply (t : I) :
      γ t = Complex.mk x (AffineMap.lineMap y₀ y₁ (t : ℝ)) := by
    apply Complex.ext <;> simp [γ, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg]
    ring_nf
  have hγD : Set.range γ ⊆ D := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    have hy : AffineMap.lineMap y₀ y₁ (t : ℝ) ∈ Set.uIcc y₀ y₁ := by
      simpa [segment_eq_uIcc] using (lineMap_mem_segment ℝ y₀ y₁ t.2)
    rw [hγ_apply t]
    exact hseg hy
  have hγprimitive := hprimitive.isPrimitiveAlongPath hD γ hγD
  -- Route correction: the endpoint formula also needs curve integrability of the segment path.
  have hγintegral :=
    hγprimitive.curveIntegral_eq_endpoint_sub (Path.segment_isPiecewiseDifferentiable _ _) <| by
      simpa [γ] using hγ_int
  -- Rewrite the segment integral to the vertical interval integral used in the source proof.
  rw [vertical_segment_planarIntegral_eq_intervalIntegral (P := P) (Q := Q) (a := x) (y₀ := y₀)
    (y₁ := y₁)] at hγintegral
  simpa [γ] using hγintegral.symm

/-- Helper for Cartan section05 0008_Proposition_3_1: a primitive of `P dx + Q dy` has the
expected horizontal coordinate derivative. -/
lemma primitive_hasDerivAt_horizontal
    {D : Set ℂ} {P Q primitive : ℂ → ℂ}
    (hprimitive : IsPrimitiveOn D (Complex.planarDifferentialForm P Q) primitive)
    {w : ℂ} (hw : w ∈ D) :
    HasDerivAt (fun x : ℝ ↦ primitive (Complex.mk x w.im)) (P w) w.re := by
  have hAffine :
      HasDerivAt (fun x : ℝ ↦ (x : ℂ) + (w.im : ℂ) * Complex.I) 1 w.re := by
    simpa [one_mul] using
      (HasDerivAt.ofReal_comp (hasDerivAt_id w.re)).add_const ((w.im : ℂ) * Complex.I)
  have hcomp : HasDerivAt (fun x : ℝ ↦ Complex.mk x w.im) 1 w.re := by
    convert hAffine using 1
    funext x
    apply Complex.ext <;> simp
  have h := (hprimitive w hw).comp w.re hcomp.hasFDerivAt
  simpa using h.hasDerivAt

/-- Helper for Cartan section05 0008_Proposition_3_1: a primitive of `P dx + Q dy` has the
expected vertical coordinate derivative. -/
lemma primitive_hasDerivAt_vertical
    {D : Set ℂ} {P Q primitive : ℂ → ℂ}
    (hprimitive : IsPrimitiveOn D (Complex.planarDifferentialForm P Q) primitive)
    {w : ℂ} (hw : w ∈ D) :
    HasDerivAt (fun y : ℝ ↦ primitive (Complex.mk w.re y)) (Q w) w.im := by
  have hAffine :
      HasDerivAt (fun y : ℝ ↦ (w.re : ℂ) + (y : ℂ) * Complex.I) Complex.I w.im := by
    simpa [one_mul] using
      ((HasDerivAt.ofReal_comp (hasDerivAt_id w.im)).mul_const Complex.I).const_add (w.re : ℂ)
  have hcomp : HasDerivAt (fun y : ℝ ↦ Complex.mk w.re y) Complex.I w.im := by
    convert hAffine using 1
    funext y
    apply Complex.ext <;> simp
  have h := (hprimitive w hw).comp w.im hcomp.hasFDerivAt
  simpa using h.hasDerivAt

/-- Helper for Cartan section05 0008_Proposition_3_1: the standard horizontal-then-vertical
primitive candidate on the ball centered at `c`. -/
def ballPrimitive (c : ℂ) (P Q : ℂ → ℂ) (z : ℂ) : ℂ :=
  (∫ x in c.re..z.re, P (Complex.mk x c.im)) + ∫ y in c.im..z.im, Q (Complex.mk z.re y)
