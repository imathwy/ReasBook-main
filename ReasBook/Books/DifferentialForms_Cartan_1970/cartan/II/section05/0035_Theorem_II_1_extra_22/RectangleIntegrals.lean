import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0007_Theorem_II_1_extra_5»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0033_Definition_II_1_extra_20»

open MeasureTheory
open scoped BigOperators

universe u

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: pulling back a complex rectangle along
`Complex.measurableEquivRealProd.symm` identifies it with the corresponding real product box. -/
lemma realProdSymm_preimage_rectangle (z w : ℂ) :
    Complex.measurableEquivRealProd.symm ⁻¹' Complex.Rectangle z w =
      Set.uIcc z.re w.re ×ˢ Set.uIcc z.im w.im := by
  -- Unfold the rectangle and read membership through the real and imaginary coordinates.
  ext p
  change (Complex.measurableEquivRealProd.symm p ∈ Complex.Rectangle z w) ↔
    p.1 ∈ Set.uIcc z.re w.re ∧ p.2 ∈ Set.uIcc z.im w.im
  simp [Complex.Rectangle, Complex.mem_reProdIm]

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: on a positively ordered rectangle, the
set integral over `Complex.Rectangle z w` agrees with the iterated interval integral in Cartesian
coordinates. -/
lemma rectangleSetIntegral_eq_iteratedIntegral
    {f : ℂ → ℝ} {z w : ℂ} (hRe : z.re < w.re) (hIm : z.im < w.im)
    (hcont : ContinuousOn f (Complex.Rectangle z w)) :
    ∫ ζ in Complex.Rectangle z w, f ζ =
      ∫ x in z.re..w.re, ∫ y in z.im..w.im, f (Complex.mk x y) := by
  have hpre :
      Complex.measurableEquivRealProd.symm ⁻¹' Complex.Rectangle z w =
        Set.uIcc z.re w.re ×ˢ Set.uIcc z.im w.im :=
    realProdSymm_preimage_rectangle z w
  have hcontProd :
      ContinuousOn (fun p : ℝ × ℝ ↦ f (Complex.measurableEquivRealProd.symm p))
        (Set.uIcc z.re w.re ×ˢ Set.uIcc z.im w.im) := by
    -- Transport continuity across the real-product coordinates.
    refine hcont.comp Complex.equivRealProdCLM.symm.continuous.continuousOn ?_
    intro p hp
    have hp' : p ∈ Complex.measurableEquivRealProd.symm ⁻¹' Complex.Rectangle z w := by
      rwa [hpre]
    exact hp'
  have hcompactProd : IsCompact (Set.uIcc z.re w.re ×ˢ Set.uIcc z.im w.im : Set (ℝ × ℝ)) := by
    -- The real box is compact as a product of compact intervals.
    simpa [Set.uIcc_prod_uIcc] using
      (isCompact_uIcc : IsCompact (Set.uIcc z.re w.re)).prod
        (isCompact_uIcc : IsCompact (Set.uIcc z.im w.im))
  have hIntProd :
      IntegrableOn (fun p : ℝ × ℝ ↦ f (Complex.measurableEquivRealProd.symm p))
        (Set.uIcc z.re w.re ×ˢ Set.uIcc z.im w.im) :=
    hcontProd.integrableOn_compact hcompactProd
  have hpreimageIntegral :
      ∫ p in Complex.measurableEquivRealProd.symm ⁻¹' Complex.Rectangle z w,
          f (Complex.measurableEquivRealProd.symm p) =
        ∫ ζ in Complex.Rectangle z w, f ζ := by
    -- The real-product parametrization preserves volume, so the rectangle set integral is the
    -- pulled-back box integral.
    simpa using
      (Complex.volume_preserving_equiv_real_prod.symm.setIntegral_preimage_emb
        Complex.measurableEquivRealProd.symm.measurableEmbedding f (Complex.Rectangle z w))
  calc
    ∫ ζ in Complex.Rectangle z w, f ζ =
        ∫ p in Set.uIcc z.re w.re ×ˢ Set.uIcc z.im w.im,
          f (Complex.measurableEquivRealProd.symm p) := by
      rw [← hpreimageIntegral, hpre]
    _ = ∫ x in Set.uIcc z.re w.re, ∫ y in Set.uIcc z.im w.im, f (Complex.mk x y) := by
      -- Apply Fubini on the real box.
      simpa using
        (MeasureTheory.setIntegral_prod (μ := volume) (ν := volume)
          (f := fun p : ℝ × ℝ ↦ f (Complex.measurableEquivRealProd.symm p)) hIntProd)
    _ = ∫ x in Set.Icc z.re w.re, ∫ y in Set.Icc z.im w.im, f (Complex.mk x y) := by
      rw [Set.uIcc_of_lt hRe, Set.uIcc_of_lt hIm]
    _ = ∫ x in Set.Icc z.re w.re, ∫ y in z.im..w.im, f (Complex.mk x y) := by
      -- Replace the inner set integral over `Icc` with the interval integral over `z.im..w.im`.
      refine setIntegral_congr_fun measurableSet_Icc ?_
      intro x hx
      calc
        ∫ y in Set.Icc z.im w.im, f (Complex.mk x y) =
            ∫ y in Set.Ioc z.im w.im, f (Complex.mk x y) := by
          exact (setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))).symm
        _ = ∫ y in z.im..w.im, f (Complex.mk x y) := by
          rw [intervalIntegral.integral_of_le hIm.le]
    _ = ∫ x in z.re..w.re, ∫ y in z.im..w.im, f (Complex.mk x y) := by
      -- Perform the same `Icc` to interval-integral conversion in the outer variable.
      calc
        ∫ x in Set.Icc z.re w.re, ∫ y in z.im..w.im, f (Complex.mk x y) =
            ∫ x in Set.Ioc z.re w.re, ∫ y in z.im..w.im, f (Complex.mk x y) := by
          exact (setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))).symm
        _ = ∫ x in z.re..w.re, ∫ y in z.im..w.im, f (Complex.mk x y) := by
          rw [intervalIntegral.integral_of_le hRe.le]

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the rectangle Green-Riemann formula
from `0007` matches the set-integral normalization needed in this item. -/
lemma rectangleGreenRiemannSetIntegralOrdered
    {D : Set ℂ} {P Q dPdy dQdx : ℂ → ℝ} {z w : ℂ}
    (hRe : z.re < w.re) (hIm : z.im < w.im) (hRectD : Complex.Rectangle z w ⊆ D)
    (hP_cont : ContinuousOn P D) (hQ_cont : ContinuousOn Q D)
    (hdPdy_cont : ContinuousOn dPdy D) (hdQdx_cont : ContinuousOn dQdx D)
    (hP_dy : ∀ ζ ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk ζ.re y)) (dPdy ζ) ζ.im)
    (hQ_dx : ∀ ζ ∈ D, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x ζ.im)) (dQdx ζ) ζ.re) :
    (∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, (P dx + Q dy) ζ) =
      ∫ ζ in Complex.Rectangle z w, (dQdx ζ - dPdy ζ) := by
  have hP_cont_rect : ContinuousOn P (Complex.Rectangle z w) := hP_cont.mono hRectD
  have hQ_cont_rect : ContinuousOn Q (Complex.Rectangle z w) := hQ_cont.mono hRectD
  have hdPdy_cont_rect : ContinuousOn dPdy (Complex.Rectangle z w) := hdPdy_cont.mono hRectD
  have hdQdx_cont_rect : ContinuousOn dQdx (Complex.Rectangle z w) := hdQdx_cont.mono hRectD
  have hSub_cont_rect : ContinuousOn (fun ζ ↦ dQdx ζ - dPdy ζ) (Complex.Rectangle z w) :=
    hdQdx_cont_rect.sub hdPdy_cont_rect
  have hP_dy_rect :
      ∀ ζ ∈ interior (Complex.Rectangle z w),
        HasDerivAt (fun y : ℝ ↦ P (Complex.mk ζ.re y)) (dPdy ζ) ζ.im := by
    -- Interior points of the rectangle stay in `D`, so the global derivative hypothesis applies.
    intro ζ hζ
    exact hP_dy ζ (hRectD (interior_subset hζ))
  have hQ_dx_rect :
      ∀ ζ ∈ interior (Complex.Rectangle z w),
        HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x ζ.im)) (dQdx ζ) ζ.re := by
    -- The same restriction argument works for the `x`-derivative hypothesis.
    intro ζ hζ
    exact hQ_dx ζ (hRectD (interior_subset hζ))
  calc
    (∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, (P dx + Q dy) ζ) =
        ∫ x in z.re..w.re, ∫ y in z.im..w.im,
          (dQdx (Complex.mk x y) - dPdy (Complex.mk x y)) := by
      -- Use the rectangle formula from its canonical owner file `0007`.
      simpa using
        (green_riemann_formula (P := P) (Q := Q) (dPdy := dPdy) (dQdx := dQdx)
          (z := z) (w := w) hP_cont_rect hQ_cont_rect hdPdy_cont_rect hdQdx_cont_rect
          hP_dy_rect hQ_dx_rect)
    _ = ∫ ζ in Complex.Rectangle z w, (dQdx ζ - dPdy ζ) := by
      -- Convert the iterated integral into the set integral over the rectangle.
      symm
      exact rectangleSetIntegral_eq_iteratedIntegral (f := fun ζ ↦ dQdx ζ - dPdy ζ)
        hRe hIm hSub_cont_rect

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: on an ordered rectangle, the `Q dy`
half of Green's formula already matches the target set-integral normalization. -/
lemma rectangleQdy_eq_setIntegral_dQdxOrdered
    {D : Set ℂ} {Q dQdx : ℂ → ℝ} {z w : ℂ}
    (hRe : z.re < w.re) (hIm : z.im < w.im) (hRectD : Complex.Rectangle z w ⊆ D)
    (hQ_cont : ContinuousOn Q D) (hdQdx_cont : ContinuousOn dQdx D)
    (hQ_dx : ∀ ζ ∈ D, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x ζ.im)) (dQdx ζ) ζ.re) :
    (∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, (((0 : ℂ → ℝ) dx + Q dy)) ζ) =
      ∫ ζ in Complex.Rectangle z w, dQdx ζ := by
  have hzero_dy :
      ∀ ζ ∈ D, HasDerivAt (fun y : ℝ ↦ (0 : ℂ → ℝ) (Complex.mk ζ.re y)) (0 : ℝ) ζ.im := by
    -- The unused horizontal coefficient is constant, so its transverse derivative vanishes.
    intro ζ hζ
    simpa using (hasDerivAt_const ζ.im (c := (0 : ℝ)))
  calc
    (∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, (((0 : ℂ → ℝ) dx + Q dy)) ζ) =
        ∫ ζ in Complex.Rectangle z w, (dQdx ζ - (0 : ℝ)) := by
      -- Specialize the full rectangle formula with vanishing `P` and `∂P/∂y`.
      simpa using
        (rectangleGreenRiemannSetIntegralOrdered
          (P := (0 : ℂ → ℝ)) (Q := Q) (dPdy := (0 : ℂ → ℝ)) (dQdx := dQdx)
          hRe hIm hRectD continuousOn_const hQ_cont continuousOn_const hdQdx_cont
          hzero_dy hQ_dx)
    _ = ∫ ζ in Complex.Rectangle z w, dQdx ζ := by
      -- Normalize the density after removing the zero horizontal contribution.
      simp

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: on an ordered rectangle, the `P dx`
half of Green's formula already matches the target set-integral normalization. -/
lemma rectanglePdx_eq_neg_setIntegral_dPdyOrdered
    {D : Set ℂ} {P dPdy : ℂ → ℝ} {z w : ℂ}
    (hRe : z.re < w.re) (hIm : z.im < w.im) (hRectD : Complex.Rectangle z w ⊆ D)
    (hP_cont : ContinuousOn P D) (hdPdy_cont : ContinuousOn dPdy D)
    (hP_dy : ∀ ζ ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk ζ.re y)) (dPdy ζ) ζ.im) :
    (∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, (P dx + (0 : ℂ → ℝ) dy) ζ) =
      - ∫ ζ in Complex.Rectangle z w, dPdy ζ := by
  have hzero_dx :
      ∀ ζ ∈ D, HasDerivAt (fun x : ℝ ↦ (0 : ℂ → ℝ) (Complex.mk x ζ.im)) (0 : ℝ) ζ.re := by
    -- The unused vertical coefficient is constant, so its horizontal derivative vanishes.
    intro ζ hζ
    simpa using (hasDerivAt_const ζ.re (c := (0 : ℝ)))
  have hRectCompact : IsCompact (Complex.Rectangle z w) := by
    -- The rectangle is the product of two compact real intervals.
    simpa [Complex.Rectangle] using isCompact_uIcc.reProdIm isCompact_uIcc
  have hdPdy_int_rect : IntegrableOn dPdy (Complex.Rectangle z w) := by
    -- Continuous functions are integrable on the compact rectangle.
    exact (hdPdy_cont.mono hRectD).integrableOn_compact hRectCompact
  calc
    (∫ᶜ ζ in axisParallelRectangleBoundaryPath z w, (P dx + (0 : ℂ → ℝ) dy) ζ) =
        ∫ ζ in Complex.Rectangle z w, ((0 : ℝ) - dPdy ζ) := by
      -- Specialize the full rectangle formula with vanishing `Q` and `∂Q/∂x`.
      simpa using
        (rectangleGreenRiemannSetIntegralOrdered
          (P := P) (Q := (0 : ℂ → ℝ)) (dPdy := dPdy) (dQdx := (0 : ℂ → ℝ))
          hRe hIm hRectD hP_cont continuousOn_const hdPdy_cont continuousOn_const
          hP_dy hzero_dx)
    _ = ∫ ζ in Complex.Rectangle z w, -dPdy ζ := by
      -- Normalize the density after removing the zero vertical contribution.
      simp
    _ = - ∫ ζ in Complex.Rectangle z w, dPdy ζ := by
      -- Pull the minus sign outside the set integral.
      rw [integral_neg]

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the set integral over a finite union
of pairwise disjoint ordered rectangles is the sum of the rectangle set integrals. -/
theorem setIntegral_biUnion_finiteOrderedRectangles
    {σ : Type*} (s : Finset σ) {f : ℂ → ℝ} {z w : σ → ℂ}
    (hMeas : ∀ i ∈ s, MeasurableSet (Complex.Rectangle (z i) (w i)))
    (hDisj :
      Set.Pairwise (↑s) fun i j ↦
        Disjoint (Complex.Rectangle (z i) (w i)) (Complex.Rectangle (z j) (w j)))
    (hInt : ∀ i ∈ s, IntegrableOn f (Complex.Rectangle (z i) (w i))) :
    ∫ ζ in ⋃ i ∈ s, Complex.Rectangle (z i) (w i), f ζ =
      ∑ i ∈ s, ∫ ζ in Complex.Rectangle (z i) (w i), f ζ := by
  -- Package the finite-union algebra once so later geometric lemmas can reason on rectangle
  -- families without repeatedly rebuilding the same measure-theoretic induction.
  simpa using
    (MeasureTheory.integral_biUnion_finset (μ := volume) (f := f) s hMeas hDisj hInt)
