import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0034_Example_II_1_extra_21».BoundaryParameters

open scoped unitInterval

noncomputable section

/-- Helper for Example II.1-extra-21: an interval point admits a symmetric open strip still
contained in the same interval. -/
lemma symmetricIntervalStrip_subset {a b t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b) :
    let eps_t := min (t₀ - a) (b - t₀) / 2
    0 < eps_t ∧ Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo a b := by
  dsimp
  constructor
  · have hleft : 0 < t₀ - a := sub_pos.mpr ht₀.1
    have hright : 0 < b - t₀ := sub_pos.mpr ht₀.2
    have hmin : 0 < min (t₀ - a) (b - t₀) := lt_min hleft hright
    linarith
  · intro t ht
    have hleft : 0 < t₀ - a := sub_pos.mpr ht₀.1
    have hright : 0 < b - t₀ := sub_pos.mpr ht₀.2
    have hmin_left : min (t₀ - a) (b - t₀) / 2 < t₀ - a := by
      have hmin_le : min (t₀ - a) (b - t₀) ≤ t₀ - a := min_le_left _ _
      linarith
    have hmin_right : min (t₀ - a) (b - t₀) / 2 < b - t₀ := by
      have hmin_le : min (t₀ - a) (b - t₀) ≤ b - t₀ := min_le_right _ _
      linarith
    constructor
    · have ha : a < t₀ - min (t₀ - a) (b - t₀) / 2 := by
        linarith
      exact lt_trans ha ht.1
    · have hb : t₀ + min (t₀ - a) (b - t₀) / 2 < b := by
        linarith
      exact lt_trans ht.2 hb

/-- Helper for Example II.1-extra-21: a global affine chart becomes a boundary-straightening
chart after restricting to a small strip and checking the signed side estimates. -/
lemma affineBoundaryStripChartExists
    {K : Set ℂ} {γ : ℝ → Plane} {t₀ eps_t eps_u : ℝ}
    (e : Plane ≃ᴬ[ℝ] Plane)
    (hεt_pos : 0 < eps_t) (hεu_pos : 0 < eps_u)
    (hstrip_param :
      Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo (0 : ℝ) 1)
    (hmap_axis :
      ∀ {t : ℝ}, t ∈ Set.Ioo (t₀ - eps_t) (t₀ + eps_t) → e (t, 0) = γ t)
    (hstrip_side :
      ∀ {t u : ℝ},
        t ∈ Set.Ioo (t₀ - eps_t) (t₀ + eps_t) →
        u ∈ Set.Ioo (-eps_u) eps_u →
        (u < 0 → Complex.equivRealProdCLM.symm (e (t, u)) ∉ K) ∧
        (0 < u → Complex.equivRealProdCLM.symm (e (t, u)) ∈ interior K)) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt K γ t₀ δ := by
  let δ₀ : OpenPartialHomeomorph Plane Plane := e.toHomeomorph.toOpenPartialHomeomorph
  let strip : Set Plane := Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ×ˢ Set.Ioo (-eps_u) eps_u
  let δ : OpenPartialHomeomorph Plane Plane := δ₀.restrOpen strip (isOpen_Ioo.prod isOpen_Ioo)
  refine ⟨δ, ?_⟩
  refine
    { basePoint_mem_source := ?_
      source_subset := ?_
      contDiffOn := ?_
      contDiffOn_symm := ?_
      map_horizontal_axis := ?_
      isImage_horizontalAxis := ?_
      exterior_on_right := ?_
      interior_on_left := ?_ }
  · -- The centered strip always contains `(t₀, 0)`.
    have hstrip : (t₀, 0) ∈ strip := by
      constructor
      · constructor <;> linarith
      · constructor <;> linarith
    simpa [δ, δ₀, strip] using hstrip
  · intro p hp
    -- The source restriction keeps the parameter inside the ambient unit interval.
    have hpStrip : p ∈ strip := by
      simpa [δ, δ₀, strip] using hp
    exact ⟨hstrip_param hpStrip.1, Set.mem_univ _⟩
  · -- The forward map is globally affine, hence `C¹` on the restricted source.
    simpa [δ, δ₀, strip] using e.toContinuousAffineMap.contDiff.contDiffOn
  · -- The inverse map is affine as well, so the restricted inverse stays `C¹`.
    simpa [δ, δ₀, strip] using e.symm.toContinuousAffineMap.contDiff.contDiffOn
  · intro t ht
    -- On the restricted source, the horizontal axis is exactly the chosen branch of `γ`.
    have htStrip : (t, 0) ∈ strip := by
      simpa [OpenPartialHomeomorph.horizontalAxisDomain, δ, δ₀, strip] using ht
    simpa [δ, δ₀] using hmap_axis htStrip.1
  · -- The horizontal-axis image is determined by the forward chart formula.
    apply curve_image_is_horizontal_axis
    intro t ht
    have htStrip : (t, 0) ∈ strip := by
      simpa [OpenPartialHomeomorph.horizontalAxisDomain, δ, δ₀, strip] using ht
    simpa [δ, δ₀] using hmap_axis htStrip.1
  · rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    rcases hz.1 with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hpStrip : p ∈ strip := by
      simpa [δ, δ₀, strip] using hp.1
    exact (hstrip_side hpStrip.1 hpStrip.2).1 hp.2 hz.2
  · intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hpStrip : p ∈ strip := by
      simpa [δ, δ₀, strip] using hp.1
    exact (hstrip_side hpStrip.1 hpStrip.2).2 hp.2

/-- Helper for Example II.1-extra-21: every regular point on the bottom edge admits an explicit
affine boundary-straightening chart. -/
lemma axis_parallel_rectangle_boundary_bottom_branch_exists_boundary_chart
    (z w : ℂ) (hRe : z.re < w.re) (hIm : z.im < w.im) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (Complex.Rectangle z w)
        ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t₀ δ := by
  obtain ⟨hεt_pos, hstrip_param_side⟩ := symmetricIntervalStrip_subset ht₀
  let eps_t : ℝ := min (t₀ - 0) (1 / 2 - t₀) / 2
  let eps_u : ℝ := (w.im - z.im) / 2
  have hεt_pos' : 0 < eps_t := by simpa [eps_t] using hεt_pos
  have hεu_pos : 0 < eps_u := by
    dsimp [eps_u]
    linarith
  have hslope_ne : (2 * (w.re - z.re) : ℝ) ≠ 0 := by
    linarith
  have hslope_mul_inv : (2 * (w.re - z.re) : ℝ) * (2 * (w.re - z.re))⁻¹ = 1 := by
    exact mul_inv_cancel₀ hslope_ne
  have hslope_inv_mul : (2 * (w.re - z.re) : ℝ)⁻¹ * (2 * (w.re - z.re)) = 1 := by
    exact inv_mul_cancel₀ hslope_ne
  let m : ℝˣ :=
    ⟨2 * (w.re - z.re), (2 * (w.re - z.re))⁻¹, hslope_mul_inv, hslope_inv_mul⟩
  let ex : ℝ ≃ᴬ[ℝ] ℝ :=
    ((ContinuousLinearEquiv.unitsEquivAut ℝ m).toContinuousAffineEquiv).trans
      (ContinuousAffineEquiv.constVAdd ℝ ℝ z.re)
  let ey : ℝ ≃ᴬ[ℝ] ℝ := ContinuousAffineEquiv.constVAdd ℝ ℝ z.im
  let e : Plane ≃ᴬ[ℝ] Plane := ex.prodCongr ey
  have hex_apply (x : ℝ) : ex x = 2 * (w.re - z.re) * x + z.re := by
    change (ContinuousAffineEquiv.constVAdd ℝ ℝ z.re) ((ContinuousLinearEquiv.unitsEquivAut ℝ m) x) =
      2 * (w.re - z.re) * x + z.re
    rw [ContinuousLinearEquiv.unitsEquivAut_apply]
    change z.re + x * (2 * (w.re - z.re)) = 2 * (w.re - z.re) * x + z.re
    ring
  have hey_apply (y : ℝ) : ey y = z.im + y := by
    change z.im + y = z.im + y
    rfl
  have hstrip_param :
      Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro t ht
    have htSide : t ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ) := by
      simpa [eps_t] using hstrip_param_side ht
    exact ⟨htSide.1, lt_trans htSide.2 (by norm_num)⟩
  refine affineBoundaryStripChartExists e hεt_pos' hεu_pos hstrip_param ?_ ?_
  · intro t ht
    have htSide : t ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ) := by
      simpa [eps_t] using hstrip_param_side ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ) := ⟨htSide.1.le, htSide.2.le⟩
    have hside :
        (axisParallelRectangleBoundaryPath z w).toClosedPath.toPath.extend t =
          AffineMap.lineMap z (Complex.mk w.re z.im) (2 * t) := by
      simpa [Path.toClosedPath] using axisParallelRectangleBoundaryPath_eqOn_bottom_side z w htIcc
    have hreal :
        (((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t).1 =
          AffineMap.lineMap z.re w.re (2 * t) := by
      simpa [ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    have himag :
        (((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t).2 = z.im := by
      simpa [ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
    apply Prod.ext
    · calc
        (e (t, 0)).1 = ex t := by
          simp [e]
        _ = 2 * (w.re - z.re) * t + z.re := hex_apply t
        _ = AffineMap.lineMap z.re w.re (2 * t) := by
          simp [AffineMap.lineMap_apply]
          ring
        _ = (((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t).1 := hreal.symm
    · calc
        (e (t, 0)).2 = ey 0 := by
          simp [e]
        _ = z.im := by simpa [hey_apply]
        _ = (((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t).2 := himag.symm
  · intro t u ht hu
    have hcomplex :
        Complex.equivRealProdCLM.symm (e (t, u)) =
          Complex.mk (AffineMap.lineMap z.re w.re (2 * t)) (z.im + u) := by
      apply Complex.ext
      · simp [Complex.equivRealProdCLM_symm_apply, e, hex_apply, hey_apply, AffineMap.lineMap_apply]
        ring
      · simp [Complex.equivRealProdCLM_symm_apply, e, hex_apply, hey_apply]
    constructor
    · intro hneg
      intro hz
      rw [hcomplex, Complex.Rectangle, Complex.mem_reProdIm] at hz
      have hzIm : 0 ≤ u := by
        have : z.im + u ∈ Set.uIcc z.im w.im := hz.2
        have hzIcc : 0 ≤ u ∧ z.im + u ≤ w.im := by
          simpa [Set.uIcc, hIm.le] using this
        exact hzIcc.1
      linarith
    · intro hu_pos
      rw [hcomplex, Complex.Rectangle, Complex.interior_reProdIm, Complex.mem_reProdIm]
      have htSide : t ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ) := hstrip_param_side ht
      have htUnit : 2 * t ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [htSide.1, htSide.2]
      have hre :
          AffineMap.lineMap z.re w.re (2 * t) ∈ Set.Ioo z.re w.re := by
        simpa [openSegment_eq_Ioo hRe] using
          (lineMap_mem_openSegment ℝ z.re w.re htUnit)
      have him :
          z.im + u ∈ Set.Ioo z.im w.im := by
        constructor
        · linarith
        · have hupper : u < w.im - z.im := by
            calc
              u < eps_u := hu.2
              _ = (w.im - z.im) / 2 := by rfl
              _ < w.im - z.im := by linarith
          linarith
      have hre' : AffineMap.lineMap z.re w.re (2 * t) ∈ interior (Set.uIcc z.re w.re) := by
        simpa [Set.uIcc, le_of_lt hRe, interior_Icc] using hre
      have him' : z.im + u ∈ interior (Set.uIcc z.im w.im) := by
        simpa [Set.uIcc, le_of_lt hIm, interior_Icc] using him
      exact And.intro hre' him'

/-- Helper for Example II.1-extra-21: every regular point on the right edge admits an explicit
affine boundary-straightening chart. -/
lemma axis_parallel_rectangle_boundary_right_branch_exists_boundary_chart
    (z w : ℂ) (hRe : z.re < w.re) (hIm : z.im < w.im) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4 : ℝ)) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (Complex.Rectangle z w)
        ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t₀ δ := by
  obtain ⟨hεt_pos, hstrip_param_side⟩ := symmetricIntervalStrip_subset ht₀
  let eps_t : ℝ := min (t₀ - 1 / 2) (3 / 4 - t₀) / 2
  let eps_u : ℝ := (w.re - z.re) / 2
  have hεt_pos' : 0 < eps_t := by simpa [eps_t] using hεt_pos
  have hεu_pos : 0 < eps_u := by
    dsimp [eps_u]
    linarith
  have hslope_ne : (4 * (w.im - z.im) : ℝ) ≠ 0 := by
    linarith
  have hslope_mul_inv : (4 * (w.im - z.im) : ℝ) * (4 * (w.im - z.im))⁻¹ = 1 := by
    exact mul_inv_cancel₀ hslope_ne
  have hslope_inv_mul : (4 * (w.im - z.im) : ℝ)⁻¹ * (4 * (w.im - z.im)) = 1 := by
    exact inv_mul_cancel₀ hslope_ne
  let m : ℝˣ :=
    ⟨4 * (w.im - z.im), (4 * (w.im - z.im))⁻¹, hslope_mul_inv, hslope_inv_mul⟩
  let et : ℝ ≃ᴬ[ℝ] ℝ :=
    ((ContinuousLinearEquiv.unitsEquivAut ℝ m).toContinuousAffineEquiv).trans
      (ContinuousAffineEquiv.constVAdd ℝ ℝ (3 * z.im - 2 * w.im))
  let eu : ℝ ≃ᴬ[ℝ] ℝ :=
    (ContinuousLinearEquiv.neg ℝ).toContinuousAffineEquiv.trans
      (ContinuousAffineEquiv.constVAdd ℝ ℝ w.re)
  let e : Plane ≃ᴬ[ℝ] Plane :=
    (et.prodCongr eu).trans (ContinuousAffineEquiv.prodComm ℝ ℝ ℝ)
  have het_apply (t : ℝ) : et t = AffineMap.lineMap z.im w.im (4 * t - 2) := by
    calc
      et t = 4 * (w.im - z.im) * t + (3 * z.im - 2 * w.im) := by
        change
          (ContinuousAffineEquiv.constVAdd ℝ ℝ (3 * z.im - 2 * w.im))
              ((ContinuousLinearEquiv.unitsEquivAut ℝ m) t) =
            4 * (w.im - z.im) * t + (3 * z.im - 2 * w.im)
        rw [ContinuousLinearEquiv.unitsEquivAut_apply]
        change
          (3 * z.im - 2 * w.im) + t * (4 * (w.im - z.im)) =
            4 * (w.im - z.im) * t + (3 * z.im - 2 * w.im)
        ring
      _ = AffineMap.lineMap z.im w.im (4 * t - 2) := by
        simp [AffineMap.lineMap_apply]
        ring
  have heu_apply (u : ℝ) : eu u = w.re - u := by
    change (ContinuousAffineEquiv.constVAdd ℝ ℝ w.re) (-u) = w.re - u
    change w.re + (-u) = w.re - u
    ring
  have hstrip_param :
      Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro t ht
    have htSide : t ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4 : ℝ) := by
      simpa [eps_t] using hstrip_param_side ht
    exact ⟨lt_trans (by norm_num) htSide.1, lt_trans htSide.2 (by norm_num)⟩
  refine affineBoundaryStripChartExists e hεt_pos' hεu_pos hstrip_param ?_ ?_
  · intro t ht
    have htSide : t ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4 : ℝ) := by
      simpa [eps_t] using hstrip_param_side ht
    have htIcc : t ∈ Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ) := ⟨htSide.1.le, htSide.2.le⟩
    have hside :
        (axisParallelRectangleBoundaryPath z w).toClosedPath.toPath.extend t =
          AffineMap.lineMap (Complex.mk w.re z.im) w (4 * t - 2) := by
      simpa [Path.toClosedPath] using axisParallelRectangleBoundaryPath_eqOn_right_side z w htIcc
    have hreal :
        (((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t).1 = w.re := by
      simpa [ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    have himag :
        (((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t).2 =
          AffineMap.lineMap z.im w.im (4 * t - 2) := by
      simpa [ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
    apply Prod.ext
    · calc
        (e (t, 0)).1 = eu 0 := by
          simp [e, ContinuousAffineEquiv.trans_apply]
        _ = w.re := by simpa [heu_apply]
        _ = (((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t).1 := hreal.symm
    · calc
        (e (t, 0)).2 = et t := by
          simp [e, ContinuousAffineEquiv.trans_apply]
        _ = AffineMap.lineMap z.im w.im (4 * t - 2) := het_apply t
        _ = (((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t).2 := himag.symm
  · intro t u ht hu
    have hcomplex :
        Complex.equivRealProdCLM.symm (e (t, u)) =
          Complex.mk (w.re - u) (AffineMap.lineMap z.im w.im (4 * t - 2)) := by
      apply Complex.ext
      · simp [Complex.equivRealProdCLM_symm_apply, e, het_apply, heu_apply,
          ContinuousAffineEquiv.trans_apply]
      · simp [Complex.equivRealProdCLM_symm_apply, e, het_apply, heu_apply,
          ContinuousAffineEquiv.trans_apply]
    constructor
    · intro hneg
      intro hz
      rw [hcomplex, Complex.Rectangle, Complex.mem_reProdIm] at hz
      have hzRe : w.re - u ≤ w.re := by
        have : w.re - u ∈ Set.uIcc z.re w.re := hz.1
        have hzIcc : z.re ≤ w.re - u ∧ w.re - u ≤ w.re := by
          simpa [Set.uIcc, hRe.le] using this
        exact hzIcc.2
      linarith
    · intro hu_pos
      rw [hcomplex, Complex.Rectangle, Complex.interior_reProdIm, Complex.mem_reProdIm]
      have htSide : t ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4 : ℝ) := hstrip_param_side ht
      have htUnit : 4 * t - 2 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [htSide.1, htSide.2]
      have him :
          AffineMap.lineMap z.im w.im (4 * t - 2) ∈ Set.Ioo z.im w.im := by
        simpa [openSegment_eq_Ioo hIm] using
          (lineMap_mem_openSegment ℝ z.im w.im htUnit)
      have hre :
          w.re - u ∈ Set.Ioo z.re w.re := by
        constructor
        · have hupper : u < w.re - z.re := by
            calc
              u < eps_u := hu.2
              _ = (w.re - z.re) / 2 := by rfl
              _ < w.re - z.re := by linarith
          linarith
        · linarith
      have hre' : w.re - u ∈ interior (Set.uIcc z.re w.re) := by
        simpa [Set.uIcc, le_of_lt hRe, interior_Icc] using hre
      have him' : AffineMap.lineMap z.im w.im (4 * t - 2) ∈ interior (Set.uIcc z.im w.im) := by
        simpa [Set.uIcc, le_of_lt hIm, interior_Icc] using him
      exact And.intro hre' him'

/-- Helper for Example II.1-extra-21: every regular point on the top edge admits an explicit
affine boundary-straightening chart. -/
lemma axis_parallel_rectangle_boundary_top_branch_exists_boundary_chart
    (z w : ℂ) (hRe : z.re < w.re) (hIm : z.im < w.im) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (3 / 4 : ℝ) (7 / 8 : ℝ)) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (Complex.Rectangle z w)
        ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t₀ δ := by
  obtain ⟨hεt_pos, hstrip_param_side⟩ := symmetricIntervalStrip_subset ht₀
  let eps_t : ℝ := min (t₀ - 3 / 4) (7 / 8 - t₀) / 2
  let eps_u : ℝ := (w.im - z.im) / 2
  have hεt_pos' : 0 < eps_t := by simpa [eps_t] using hεt_pos
  have hεu_pos : 0 < eps_u := by
    dsimp [eps_u]
    linarith
  have hslope_ne : (8 * (z.re - w.re) : ℝ) ≠ 0 := by
    linarith
  have hslope_mul_inv : (8 * (z.re - w.re) : ℝ) * (8 * (z.re - w.re))⁻¹ = 1 := by
    exact mul_inv_cancel₀ hslope_ne
  have hslope_inv_mul : (8 * (z.re - w.re) : ℝ)⁻¹ * (8 * (z.re - w.re)) = 1 := by
    exact inv_mul_cancel₀ hslope_ne
  let m : ℝˣ :=
    ⟨8 * (z.re - w.re), (8 * (z.re - w.re))⁻¹, hslope_mul_inv, hslope_inv_mul⟩
  let et : ℝ ≃ᴬ[ℝ] ℝ :=
    ((ContinuousLinearEquiv.unitsEquivAut ℝ m).toContinuousAffineEquiv).trans
      (ContinuousAffineEquiv.constVAdd ℝ ℝ (7 * w.re - 6 * z.re))
  let eu : ℝ ≃ᴬ[ℝ] ℝ :=
    (ContinuousLinearEquiv.neg ℝ).toContinuousAffineEquiv.trans
      (ContinuousAffineEquiv.constVAdd ℝ ℝ w.im)
  let e : Plane ≃ᴬ[ℝ] Plane := et.prodCongr eu
  have het_apply (t : ℝ) : et t = AffineMap.lineMap w.re z.re (8 * t - 6) := by
    calc
      et t = 8 * (z.re - w.re) * t + (7 * w.re - 6 * z.re) := by
        change
          (ContinuousAffineEquiv.constVAdd ℝ ℝ (7 * w.re - 6 * z.re))
              ((ContinuousLinearEquiv.unitsEquivAut ℝ m) t) =
            8 * (z.re - w.re) * t + (7 * w.re - 6 * z.re)
        rw [ContinuousLinearEquiv.unitsEquivAut_apply]
        change
          (7 * w.re - 6 * z.re) + t * (8 * (z.re - w.re)) =
            8 * (z.re - w.re) * t + (7 * w.re - 6 * z.re)
        ring
      _ = AffineMap.lineMap w.re z.re (8 * t - 6) := by
        simp [AffineMap.lineMap_apply]
        ring
  have heu_apply (u : ℝ) : eu u = w.im - u := by
    change (ContinuousAffineEquiv.constVAdd ℝ ℝ w.im) (-u) = w.im - u
    change w.im + (-u) = w.im - u
    ring
  have hstrip_param :
      Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro t ht
    have htSide : t ∈ Set.Ioo (3 / 4 : ℝ) (7 / 8 : ℝ) := by
      simpa [eps_t] using hstrip_param_side ht
    exact ⟨lt_trans (by norm_num) htSide.1, lt_trans htSide.2 (by norm_num)⟩
  refine affineBoundaryStripChartExists e hεt_pos' hεu_pos hstrip_param ?_ ?_
  · intro t ht
    have htSide : t ∈ Set.Ioo (3 / 4 : ℝ) (7 / 8 : ℝ) := by
      simpa [eps_t] using hstrip_param_side ht
    have htIcc : t ∈ Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ) := ⟨htSide.1.le, htSide.2.le⟩
    have hside :
        (axisParallelRectangleBoundaryPath z w).toClosedPath.toPath.extend t =
          AffineMap.lineMap w (Complex.mk z.re w.im) (8 * t - 6) := by
      simpa [Path.toClosedPath] using axisParallelRectangleBoundaryPath_eqOn_top_side z w htIcc
    have hreal :
        (((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t).1 =
          AffineMap.lineMap w.re z.re (8 * t - 6) := by
      simpa [ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    have himag :
        (((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t).2 = w.im := by
      simpa [ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
    apply Prod.ext
    · calc
        (e (t, 0)).1 = et t := by
          simp [e]
        _ = AffineMap.lineMap w.re z.re (8 * t - 6) := het_apply t
        _ = (((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t).1 := hreal.symm
    · calc
        (e (t, 0)).2 = eu 0 := by
          simp [e]
        _ = w.im := by simpa [heu_apply]
        _ = (((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t).2 := himag.symm
  · intro t u ht hu
    have hcomplex :
        Complex.equivRealProdCLM.symm (e (t, u)) =
          Complex.mk (AffineMap.lineMap w.re z.re (8 * t - 6)) (w.im - u) := by
      apply Complex.ext
      · simp [Complex.equivRealProdCLM_symm_apply, e, het_apply, heu_apply, AffineMap.lineMap_apply]
      · simp [Complex.equivRealProdCLM_symm_apply, e, het_apply, heu_apply]
    constructor
    · intro hneg
      intro hz
      rw [hcomplex, Complex.Rectangle, Complex.mem_reProdIm] at hz
      have hzIm : w.im - u ≤ w.im := by
        have : w.im - u ∈ Set.uIcc z.im w.im := hz.2
        have hzIcc : z.im ≤ w.im - u ∧ w.im - u ≤ w.im := by
          simpa [Set.uIcc, hIm.le] using this
        exact hzIcc.2
      linarith
    · intro hu_pos
      rw [hcomplex, Complex.Rectangle, Complex.interior_reProdIm, Complex.mem_reProdIm]
      have htSide : t ∈ Set.Ioo (3 / 4 : ℝ) (7 / 8 : ℝ) := hstrip_param_side ht
      have htUnit : 8 * t - 6 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [htSide.1, htSide.2]
      have hre :
          AffineMap.lineMap w.re z.re (8 * t - 6) ∈ Set.Ioo z.re w.re := by
        simpa [openSegment_eq_Ioo hRe, openSegment_symm ℝ w.re z.re] using
          (lineMap_mem_openSegment ℝ w.re z.re htUnit)
      have him :
          w.im - u ∈ Set.Ioo z.im w.im := by
        constructor
        · have hupper : u < w.im - z.im := by
            calc
              u < eps_u := hu.2
              _ = (w.im - z.im) / 2 := by rfl
              _ < w.im - z.im := by linarith
          linarith
        · linarith
      have hre' : AffineMap.lineMap w.re z.re (8 * t - 6) ∈ interior (Set.uIcc z.re w.re) := by
        simpa [Set.uIcc, le_of_lt hRe, interior_Icc] using hre
      have him' : w.im - u ∈ interior (Set.uIcc z.im w.im) := by
        simpa [Set.uIcc, le_of_lt hIm, interior_Icc] using him
      exact And.intro hre' him'

/-- Helper for Example II.1-extra-21: every regular point on the left edge admits an explicit
affine boundary-straightening chart. -/
lemma axis_parallel_rectangle_boundary_left_branch_exists_boundary_chart
    (z w : ℂ) (hRe : z.re < w.re) (hIm : z.im < w.im) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (7 / 8 : ℝ) (1 : ℝ)) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (Complex.Rectangle z w)
        ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t₀ δ := by
  obtain ⟨hεt_pos, hstrip_param_side⟩ := symmetricIntervalStrip_subset ht₀
  let eps_t : ℝ := min (t₀ - 7 / 8) (1 - t₀) / 2
  let eps_u : ℝ := (w.re - z.re) / 2
  have hεt_pos' : 0 < eps_t := by simpa [eps_t] using hεt_pos
  have hεu_pos : 0 < eps_u := by
    dsimp [eps_u]
    linarith
  have hslope_ne : (8 * (z.im - w.im) : ℝ) ≠ 0 := by
    linarith
  have hslope_mul_inv : (8 * (z.im - w.im) : ℝ) * (8 * (z.im - w.im))⁻¹ = 1 := by
    exact mul_inv_cancel₀ hslope_ne
  have hslope_inv_mul : (8 * (z.im - w.im) : ℝ)⁻¹ * (8 * (z.im - w.im)) = 1 := by
    exact inv_mul_cancel₀ hslope_ne
  let m : ℝˣ :=
    ⟨8 * (z.im - w.im), (8 * (z.im - w.im))⁻¹, hslope_mul_inv, hslope_inv_mul⟩
  let et : ℝ ≃ᴬ[ℝ] ℝ :=
    ((ContinuousLinearEquiv.unitsEquivAut ℝ m).toContinuousAffineEquiv).trans
      (ContinuousAffineEquiv.constVAdd ℝ ℝ (8 * w.im - 7 * z.im))
  let eu : ℝ ≃ᴬ[ℝ] ℝ := ContinuousAffineEquiv.constVAdd ℝ ℝ z.re
  let e : Plane ≃ᴬ[ℝ] Plane :=
    (et.prodCongr eu).trans (ContinuousAffineEquiv.prodComm ℝ ℝ ℝ)
  have het_apply (t : ℝ) : et t = AffineMap.lineMap w.im z.im (8 * t - 7) := by
    calc
      et t = 8 * (z.im - w.im) * t + (8 * w.im - 7 * z.im) := by
        change
          (ContinuousAffineEquiv.constVAdd ℝ ℝ (8 * w.im - 7 * z.im))
              ((ContinuousLinearEquiv.unitsEquivAut ℝ m) t) =
            8 * (z.im - w.im) * t + (8 * w.im - 7 * z.im)
        rw [ContinuousLinearEquiv.unitsEquivAut_apply]
        change
          (8 * w.im - 7 * z.im) + t * (8 * (z.im - w.im)) =
            8 * (z.im - w.im) * t + (8 * w.im - 7 * z.im)
        ring
      _ = AffineMap.lineMap w.im z.im (8 * t - 7) := by
        simp [AffineMap.lineMap_apply]
        ring
  have heu_apply (u : ℝ) : eu u = z.re + u := by
    change z.re + u = z.re + u
    rfl
  have hstrip_param :
      Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro t ht
    have htSide : t ∈ Set.Ioo (7 / 8 : ℝ) (1 : ℝ) := by
      simpa [eps_t] using hstrip_param_side ht
    exact ⟨lt_trans (by norm_num) htSide.1, htSide.2⟩
  refine affineBoundaryStripChartExists e hεt_pos' hεu_pos hstrip_param ?_ ?_
  · intro t ht
    have htSide : t ∈ Set.Ioo (7 / 8 : ℝ) (1 : ℝ) := by
      simpa [eps_t] using hstrip_param_side ht
    have htIcc : t ∈ Set.Icc (7 / 8 : ℝ) (1 : ℝ) := ⟨htSide.1.le, htSide.2.le⟩
    have hside :
        (axisParallelRectangleBoundaryPath z w).toClosedPath.toPath.extend t =
          AffineMap.lineMap (Complex.mk z.re w.im) z (8 * t - 7) := by
      simpa [Path.toClosedPath] using axisParallelRectangleBoundaryPath_eqOn_left_side z w htIcc
    have hreal :
        (((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t).1 = z.re := by
      simpa [ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    have himag :
        (((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t).2 =
          AffineMap.lineMap w.im z.im (8 * t - 7) := by
      simpa [ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
    apply Prod.ext
    · calc
        (e (t, 0)).1 = eu 0 := by
          simp [e, ContinuousAffineEquiv.trans_apply]
        _ = z.re := by simpa [heu_apply]
        _ = (((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t).1 := hreal.symm
    · calc
        (e (t, 0)).2 = et t := by
          simp [e, ContinuousAffineEquiv.trans_apply]
        _ = AffineMap.lineMap w.im z.im (8 * t - 7) := het_apply t
        _ = (((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t).2 := himag.symm
  · intro t u ht hu
    have hcomplex :
        Complex.equivRealProdCLM.symm (e (t, u)) =
          Complex.mk (z.re + u) (AffineMap.lineMap w.im z.im (8 * t - 7)) := by
      apply Complex.ext
      · simp [Complex.equivRealProdCLM_symm_apply, e, het_apply, heu_apply,
          ContinuousAffineEquiv.trans_apply]
      · simp [Complex.equivRealProdCLM_symm_apply, e, het_apply, heu_apply,
          ContinuousAffineEquiv.trans_apply]
    constructor
    · intro hneg
      intro hz
      rw [hcomplex, Complex.Rectangle, Complex.mem_reProdIm] at hz
      have hzRe : z.re ≤ z.re + u := by
        have : z.re + u ∈ Set.uIcc z.re w.re := hz.1
        have hzIcc : z.re ≤ z.re + u ∧ z.re + u ≤ w.re := by
          simpa [Set.uIcc, hRe.le] using this
        exact hzIcc.1
      linarith
    · intro hu_pos
      rw [hcomplex, Complex.Rectangle, Complex.interior_reProdIm, Complex.mem_reProdIm]
      have htSide : t ∈ Set.Ioo (7 / 8 : ℝ) (1 : ℝ) := hstrip_param_side ht
      have htUnit : 8 * t - 7 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [htSide.1, htSide.2]
      have him :
          AffineMap.lineMap w.im z.im (8 * t - 7) ∈ Set.Ioo z.im w.im := by
        simpa [openSegment_eq_Ioo hIm, openSegment_symm ℝ w.im z.im] using
          (lineMap_mem_openSegment ℝ w.im z.im htUnit)
      have hre :
          z.re + u ∈ Set.Ioo z.re w.re := by
        constructor
        · linarith
        · have hupper : u < w.re - z.re := by
            calc
              u < eps_u := hu.2
              _ = (w.re - z.re) / 2 := by rfl
              _ < w.re - z.re := by linarith
          linarith
      have hre' : z.re + u ∈ interior (Set.uIcc z.re w.re) := by
        simpa [Set.uIcc, le_of_lt hRe, interior_Icc] using hre
      have him' : AffineMap.lineMap w.im z.im (8 * t - 7) ∈ interior (Set.uIcc z.im w.im) := by
        simpa [Set.uIcc, le_of_lt hIm, interior_Icc] using him
      exact And.intro hre' him'
