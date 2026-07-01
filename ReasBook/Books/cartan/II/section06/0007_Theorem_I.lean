import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Topology

/-- Helper for Theorem I’: the explicit boundary integral of the rectangle with corners `z` and `w`. -/
private noncomputable def boundaryIntegralExpr (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * Complex.I)) -
    (∫ x : ℝ in z.re..w.re, f (x + w.im * Complex.I)) +
      Complex.I • (∫ y : ℝ in z.im..w.im, f (w.re + y * Complex.I)) -
        Complex.I • (∫ y : ℝ in z.im..w.im, f (z.re + y * Complex.I))

/-- Helper for Theorem I’: every closed complex rectangle is compact. -/
private lemma isCompact_rectangle (z w : ℂ) : IsCompact (Complex.Rectangle z w) := by
  simpa [Complex.Rectangle] using isCompact_uIcc.reProdIm isCompact_uIcc

/-- Helper for Theorem I’: a point in the open rectangle also lies in the closed rectangle. -/
private lemma mem_rectangle_of_mem_openRectangle {z w x : ℂ}
    (hx :
      x ∈ Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
        Set.Ioo (min z.im w.im) (max z.im w.im)) :
    x ∈ Complex.Rectangle z w := by
  rcases Complex.mem_reProdIm.1 hx with ⟨hxre, hxim⟩
  simpa [Complex.Rectangle, Complex.mem_reProdIm, Set.uIcc] using
    (show x.re ∈ Set.Icc (min z.re w.re) (max z.re w.re) ∧
        x.im ∈ Set.Icc (min z.im w.im) (max z.im w.im) from
      ⟨Ioo_subset_Icc_self hxre, Ioo_subset_Icc_self hxim⟩)

/-- Theorem I’ (1): a continuous complex function on `D` that is holomorphic away from a horizontal
line is conservative on `D`, i.e. the form `f(z) dz` is closed in Cartan's rectangle-integral
sense. -/
-- Proof sketch: Split any rectangle along the horizontal line of possible singularities; on the
-- resulting subrectangles apply the holomorphic rectangle-integral theorem, and when the line
-- coincides with a horizontal edge pass to the limit using continuity of `f`.
theorem continuous_holomorphic_off_horizontal_line_isConservativeOn
    {D : Set ℂ} {f : ℂ → ℂ} {y : ℝ} (hf_cont : ContinuousOn f D)
    (hf_diff : DifferentiableOn ℂ f (D \ {z : ℂ | z.im = y})) :
    Complex.IsConservativeOn f D := by
  -- Rewrite the conservative-on goal as the vanishing of the rectangle boundary integral.
  intro z w hzw
  rw [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq]
  change boundaryIntegralExpr f z w = 0
  let Rint : Set ℂ :=
    Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ Set.Ioo (min z.im w.im) (max z.im w.im)
  have hcont_rect : ContinuousOn f (Complex.Rectangle z w) := hf_cont.mono hzw
  by_cases hy : y ∈ Set.Ioo (min z.im w.im) (max z.im w.im)
  · let z' : ℂ := z.re + y * Complex.I
    let w' : ℂ := w.re + y * Complex.I
    -- When the horizontal line meets the interior, split the rectangle into lower and upper pieces.
    have hy_uIcc : y ∈ Set.uIcc z.im w.im := by
      simpa [Set.uIcc] using show y ∈ Set.Icc (min z.im w.im) (max z.im w.im) from
        ⟨hy.1.le, hy.2.le⟩
    have hsub_lower : Complex.Rectangle z w' ⊆ Complex.Rectangle z w := by
      intro u hu
      rcases Complex.mem_reProdIm.1 (by simpa [Complex.Rectangle, w'] using hu) with
        ⟨hure, huim⟩
      have huim' : u.im ∈ Set.uIcc z.im w.im :=
        (Set.uIcc_subset_uIcc left_mem_uIcc hy_uIcc) huim
      simpa [Complex.Rectangle, Complex.mem_reProdIm, w', Set.uIcc] using
        (show u.re ∈ Set.uIcc z.re w.re ∧ u.im ∈ Set.uIcc z.im w.im from ⟨hure, huim'⟩)
    have hsub_upper : Complex.Rectangle z' w ⊆ Complex.Rectangle z w := by
      intro u hu
      rcases Complex.mem_reProdIm.1 (by simpa [Complex.Rectangle, z'] using hu) with
        ⟨hure, huim⟩
      have huim' : u.im ∈ Set.uIcc z.im w.im :=
        (Set.uIcc_subset_uIcc hy_uIcc right_mem_uIcc) huim
      simpa [Complex.Rectangle, Complex.mem_reProdIm, z', Set.uIcc] using
        (show u.re ∈ Set.uIcc z.re w.re ∧ u.im ∈ Set.uIcc z.im w.im from ⟨hure, huim'⟩)
    have hd_lower :
        DifferentiableOn ℂ f
          (Set.Ioo (min z.re w'.re) (max z.re w'.re) ×ℂ
            Set.Ioo (min z.im w'.im) (max z.im w'.im)) := by
      intro x hx
      have hx_rect : x ∈ Complex.Rectangle z w' := by
        exact mem_rectangle_of_mem_openRectangle (by simpa [w'] using hx)
      have hx_mem : x ∈ D \ {u : ℂ | u.im = y} := by
        refine ⟨hzw (hsub_lower hx_rect), ?_⟩
        rcases Complex.mem_reProdIm.1 hx with
          ⟨_, hxim⟩
        exact fun hxy ↦ by
          rw [hxy] at hxim
          have hmem : y ∈ Set.Ioo (min z.im y) (max z.im y) := by
            simpa [w'] using hxim
          by_cases hzy : z.im < y
          · rw [min_eq_left hzy.le, max_eq_right hzy.le] at hmem
            exact hmem.2.ne rfl
          · have hyz : y ≤ z.im := le_of_not_gt hzy
            rw [min_eq_right hyz, max_eq_left hyz] at hmem
            exact hmem.1.ne rfl
      have hnhds : D \ {u : ℂ | u.im = y} ∈ 𝓝 x := by
        refine Filter.mem_of_superset ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hx) ?_
        intro u hu
        have hu_rect : u ∈ Complex.Rectangle z w' := by
          exact mem_rectangle_of_mem_openRectangle (by simpa [w'] using hu)
        refine ⟨hzw (hsub_lower hu_rect), ?_⟩
        rcases Complex.mem_reProdIm.1 hu with
          ⟨_, huim⟩
        exact fun huy ↦ by
          rw [huy] at huim
          have hmem : y ∈ Set.Ioo (min z.im y) (max z.im y) := by
            simpa [w'] using huim
          by_cases hzy : z.im < y
          · rw [min_eq_left hzy.le, max_eq_right hzy.le] at hmem
            exact hmem.2.ne rfl
          · have hyz : y ≤ z.im := le_of_not_gt hzy
            rw [min_eq_right hyz, max_eq_left hyz] at hmem
            exact hmem.1.ne rfl
      exact ((hf_diff x hx_mem).differentiableAt hnhds).differentiableWithinAt
    have hd_upper :
        DifferentiableOn ℂ f
          (Set.Ioo (min z'.re w.re) (max z'.re w.re) ×ℂ
            Set.Ioo (min z'.im w.im) (max z'.im w.im)) := by
      intro x hx
      have hx_rect : x ∈ Complex.Rectangle z' w := by
        exact mem_rectangle_of_mem_openRectangle (by simpa [z'] using hx)
      have hx_mem : x ∈ D \ {u : ℂ | u.im = y} := by
        refine ⟨hzw (hsub_upper hx_rect), ?_⟩
        rcases Complex.mem_reProdIm.1 hx with
          ⟨_, hxim⟩
        exact fun hxy ↦ by
          rw [hxy] at hxim
          have hmem : y ∈ Set.Ioo (min y w.im) (max y w.im) := by
            simpa [z'] using hxim
          by_cases hyw : y < w.im
          · rw [min_eq_left hyw.le, max_eq_right hyw.le] at hmem
            exact hmem.1.ne rfl
          · have hwy : w.im ≤ y := le_of_not_gt hyw
            rw [min_eq_right hwy, max_eq_left hwy] at hmem
            exact hmem.2.ne rfl
      have hnhds : D \ {u : ℂ | u.im = y} ∈ 𝓝 x := by
        refine Filter.mem_of_superset ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hx) ?_
        intro u hu
        have hu_rect : u ∈ Complex.Rectangle z' w := by
          exact mem_rectangle_of_mem_openRectangle (by simpa [z'] using hu)
        refine ⟨hzw (hsub_upper hu_rect), ?_⟩
        rcases Complex.mem_reProdIm.1 hu with
          ⟨_, huim⟩
        exact fun huy ↦ by
          rw [huy] at huim
          have hmem : y ∈ Set.Ioo (min y w.im) (max y w.im) := by
            simpa [z'] using huim
          by_cases hyw : y < w.im
          · rw [min_eq_left hyw.le, max_eq_right hyw.le] at hmem
            exact hmem.1.ne rfl
          · have hwy : w.im ≤ y := le_of_not_gt hyw
            rw [min_eq_right hwy, max_eq_left hwy] at hmem
            exact hmem.2.ne rfl
      exact ((hf_diff x hx_mem).differentiableAt hnhds).differentiableWithinAt
    have hlower :
        boundaryIntegralExpr f z w' = 0 := by
      simpa [boundaryIntegralExpr, w'] using
        Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w'
          (hcont_rect.mono hsub_lower) hd_lower
    have hupper :
        boundaryIntegralExpr f z' w = 0 := by
      simpa [boundaryIntegralExpr, z'] using
        Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z' w
          (hcont_rect.mono hsub_upper) hd_upper
    have hvert_integrable {a b c : ℝ} (ha : a ∈ Set.uIcc z.re w.re)
        (hbc : Set.uIcc b c ⊆ Set.uIcc z.im w.im) :
        IntervalIntegrable (fun t : ℝ ↦ f (a + t * Complex.I)) MeasureTheory.volume b c := by
      refine ((hcont_rect.mono ?_).comp (by fun_prop) (mapsTo_image _ _)).intervalIntegrable
      rintro _ ⟨t, ht, rfl⟩
      have ht' : t ∈ Set.uIcc z.im w.im := hbc ht
      simpa [Complex.Rectangle, Complex.mem_reProdIm, Set.uIcc] using
        (show a ∈ Set.uIcc z.re w.re ∧ t ∈ Set.uIcc z.im w.im from ⟨ha, ht'⟩)
    have hsplit :
      boundaryIntegralExpr f z w =
          boundaryIntegralExpr f z w' + boundaryIntegralExpr f z' w := by
      have hright₁ :
          IntervalIntegrable (fun t : ℝ ↦ f (w.re + t * Complex.I)) MeasureTheory.volume z.im y :=
        hvert_integrable (show w.re ∈ Set.uIcc z.re w.re from right_mem_uIcc)
          (Set.uIcc_subset_uIcc left_mem_uIcc hy_uIcc)
      have hright₂ :
          IntervalIntegrable (fun t : ℝ ↦ f (w.re + t * Complex.I)) MeasureTheory.volume y w.im :=
        hvert_integrable (show w.re ∈ Set.uIcc z.re w.re from right_mem_uIcc)
          (Set.uIcc_subset_uIcc hy_uIcc right_mem_uIcc)
      have hleft₁ :
          IntervalIntegrable (fun t : ℝ ↦ f (z.re + t * Complex.I)) MeasureTheory.volume z.im y :=
        hvert_integrable (show z.re ∈ Set.uIcc z.re w.re from left_mem_uIcc)
          (Set.uIcc_subset_uIcc left_mem_uIcc hy_uIcc)
      have hleft₂ :
          IntervalIntegrable (fun t : ℝ ↦ f (z.re + t * Complex.I)) MeasureTheory.volume y w.im :=
        hvert_integrable (show z.re ∈ Set.uIcc z.re w.re from left_mem_uIcc)
          (Set.uIcc_subset_uIcc hy_uIcc right_mem_uIcc)
      rw [boundaryIntegralExpr, boundaryIntegralExpr, boundaryIntegralExpr]
      rw [← intervalIntegral.integral_add_adjacent_intervals hright₁ hright₂,
        ← intervalIntegral.integral_add_adjacent_intervals hleft₁ hleft₂]
      simp [z', w', add_comm, sub_eq_add_neg, mul_add]
      ring_nf
    calc
      boundaryIntegralExpr f z w =
          boundaryIntegralExpr f z w' + boundaryIntegralExpr f z' w := hsplit
      _ = 0 := by rw [hlower, hupper]; simp
  · refine Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w
      hcont_rect ?_
    -- If the line misses the open rectangle, the standard rectangle theorem applies directly.
    intro x hx
    have hx_mem : x ∈ D \ {u : ℂ | u.im = y} := by
      refine ⟨hzw (mem_rectangle_of_mem_openRectangle hx), ?_⟩
      rcases Complex.mem_reProdIm.1 hx with ⟨_, hxim⟩
      exact fun hxy ↦ by
        rw [hxy] at hxim
        exact hy hxim
    have hnhds : D \ {u : ℂ | u.im = y} ∈ 𝓝 x := by
      refine Filter.mem_of_superset ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hx) ?_
      intro u hu
      refine ⟨hzw (mem_rectangle_of_mem_openRectangle hu), ?_⟩
      rcases Complex.mem_reProdIm.1 hu with ⟨_, huim⟩
      exact fun huy ↦ by
        rw [huy] at huim
        exact hy huim
    exact ((hf_diff x hx_mem).differentiableAt hnhds).differentiableWithinAt

/-- Theorem I’ (2): a continuous complex function on `D` that is holomorphic away from a set of
isolated exceptional points in `D` is conservative on `D`, i.e. the form `f(z) dz` is closed. -/
-- Proof sketch: A compact rectangle in `D` meets the exceptional set in only finitely many points
-- by the `codiscreteWithin` hypothesis, so mathlib's rectangle theorem off a countable set applies.
theorem continuous_holomorphic_off_isolated_points_isConservativeOn
    {D E : Set ℂ} {f : ℂ → ℂ} (hf_cont : ContinuousOn f D)
    (hE : D \ E ∈ Filter.codiscreteWithin D) (hf_diff : DifferentiableOn ℂ f (D \ E)) :
    Complex.IsConservativeOn f D := by
  -- Again reduce the closedness claim to the vanishing of every rectangle boundary integral.
  intro z w hzw
  rw [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq]
  change boundaryIntegralExpr f z w = 0
  let R : Set ℂ := Complex.Rectangle z w
  let Rint : Set ℂ :=
    Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ Set.Ioo (min z.im w.im) (max z.im w.im)
  -- Restrict the codiscrete-within hypothesis from `D` to the chosen rectangle.
  have hcodR : D \ E ∈ Filter.codiscreteWithin R := by
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hE ⊢
    intro x hxR
    have hxD : x ∈ D := hzw (by simpa [R] using hxR)
    refine Filter.mem_of_superset (hE x hxD) ?_
    intro u hu
    rcases hu with hu | hu
    · exact Or.inl hu
    · exact Or.inr fun hxR' ↦ hu (hzw (by simpa [R] using hxR'))
  have hExceptional_countable : (R ∩ E).Countable := by
    have hfinite : (R ∩ E).Finite :=
      (isCompact_rectangle z w).finite_diff_of_mem_codiscreteWithin hcodR |>.subset fun x hx ↦
        ⟨hx.1, by simp [hx.2]⟩
    exact hfinite.countable
  refine Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w (R ∩ E)
    hExceptional_countable (hf_cont.mono (by simpa [R] using hzw)) ?_
  -- Points in the open rectangle away from `R ∩ E` admit a neighborhood inside `D \ E`.
  intro x hx
  rcases hx with ⟨hxRint, hxExceptional⟩
  have hxR : x ∈ R := mem_rectangle_of_mem_openRectangle (by simpa [Rint] using hxRint)
  have hxD : x ∈ D := hzw (by simpa [R] using hxR)
  have hxE : x ∉ E := by
    intro hxE'
    exact hxExceptional ⟨by simpa [R] using hxR, hxE'⟩
  have hDE_inter : D \ (D \ E) = D ∩ E := by
    ext u
    simp
  obtain ⟨t, htx, htfinite⟩ :=
    (codiscreteWithin_iff_locallyFiniteComplementWithin.1 hE) x hxD
  have htfinite' : (t ∩ (D ∩ E)).Finite := by
    simpa [hDE_inter, Set.inter_assoc] using htfinite
  have hnhds : D \ E ∈ 𝓝 x := by
    have hx_not_mem : x ∉ t ∩ (D ∩ E) := by
      intro hx_mem
      exact hxE hx_mem.2.2
    refine Filter.mem_of_superset
      (Filter.inter_mem
        (Filter.inter_mem ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hxRint) htx)
        (htfinite'.isClosed.compl_mem_nhds hx_not_mem)) ?_
    intro u hu
    rcases hu with ⟨hu₁, hucompl⟩
    rcases hu₁ with ⟨huRint, hut⟩
    have huR : u ∈ R := mem_rectangle_of_mem_openRectangle (by simpa [Rint] using huRint)
    have huD : u ∈ D := hzw (by simpa [R] using huR)
    refine ⟨huD, ?_⟩
    intro huE
    exact hucompl ⟨hut, huD, huE⟩
  exact (hf_diff x ⟨hxD, hxE⟩).differentiableAt hnhds
