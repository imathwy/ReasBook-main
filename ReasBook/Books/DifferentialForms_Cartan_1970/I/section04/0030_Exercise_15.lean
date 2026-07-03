import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` is unavailable in this environment, so the statement
-- surface was chosen by checking Mathlib's `AnalyticOnNhd` owner together with the canonical
-- interval hypothesis `Set.OrdConnected`, the standard embedding `Complex.ofReal`, and the
-- canonical restriction predicate `Set.EqOn`.

open scoped Topology

/-- Helper for Exercise 15: the complexification of a real scalar power series agrees with the
original real scalar series on the real axis whenever both sums converge. -/
lemma ofScalars_complex_sum_ofReal_eq
    {c : ℕ → ℝ} {y : ℝ}
    (hyR :
      y ∈ Metric.eball (0 : ℝ) (FormalMultilinearSeries.ofScalars ℝ c).radius)
    (hyC :
      (Complex.ofReal y : ℂ) ∈
        Metric.eball (0 : ℂ) (FormalMultilinearSeries.ofScalars ℂ fun n ↦ (c n : ℂ)).radius) :
    Complex.ofReal ((FormalMultilinearSeries.ofScalars ℝ c).sum y) =
      (FormalMultilinearSeries.ofScalars ℂ fun n ↦ (c n : ℂ)).sum (Complex.ofReal y) := by
  let pR : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ c
  let pC : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ fun n ↦ (c n : ℂ)
  -- Compare the real series and its complexification term-by-term.
  have hsR : HasSum (fun n : ℕ ↦ (c n * y ^ n : ℝ)) (pR.sum y) := by
    simpa [pR, FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using pR.hasSum hyR
  have hsR' : HasSum (fun n : ℕ ↦ ((c n * y ^ n : ℝ) : ℂ)) (Complex.ofReal (pR.sum y)) := by
    simpa [Complex.ofReal_mul, Complex.ofReal_pow] using
      (Complex.hasSum_ofReal (f := fun n : ℕ ↦ c n * y ^ n) (x := pR.sum y)).2 hsR
  have hsR'' :
      HasSum (fun n : ℕ ↦ ((c n : ℂ) * (Complex.ofReal y) ^ n)) (Complex.ofReal (pR.sum y)) := by
    simpa [Complex.ofReal_mul, Complex.ofReal_pow] using hsR'
  have hsC : HasSum (fun n : ℕ ↦ ((c n : ℂ) * (Complex.ofReal y) ^ n))
      (pC.sum (Complex.ofReal y)) := by
    simpa [pC, FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using pC.hasSum hyC
  -- Uniqueness of sums identifies the two evaluations.
  exact hsR''.unique hsC

/-- Helper for Exercise 15: a real-analytic germ has a holomorphic extension to a small complex
ball centered at the same real point. -/
lemma real_analyticAt_exists_complex_eball_extension
    {u : ℝ → ℝ} {x : ℝ} (hu : AnalyticAt ℝ u x) :
    ∃ r : NNReal, 0 < r ∧ ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.eball (Complex.ofReal x) r) ∧
      Set.EqOn (fun t : ℝ ↦ g (Complex.ofReal t)) (fun t ↦ (u t : ℂ)) (Metric.eball x r) := by
  let c : ℕ → ℝ := fun n ↦ iteratedDeriv n u x / n.factorial
  let pR : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ c
  let pC : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ fun n ↦ (c n : ℂ)
  obtain ⟨R, hR⟩ : HasFPowerSeriesAt u pR x := hu.hasFPowerSeriesAt
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hR.r_pos with ⟨r, hr0, hrR⟩
  have hr0' : 0 < r := by
    exact_mod_cast hr0
  -- The complexified scalar series has positive radius because the same coefficient norms give
  -- summability on the smaller real radius `r`.
  have hrRad : (r : ENNReal) < pR.radius := lt_of_lt_of_le hrR hR.r_le
  have hSummable : Summable fun n : ℕ => ‖pC n‖ * (r : ℝ) ^ n := by
    simpa [pC, pR, c, FormalMultilinearSeries.ofScalars_norm] using
      pR.summable_norm_mul_pow hrRad
  have hrC : (r : ENNReal) ≤ pC.radius := pC.le_radius_of_summable hSummable
  have hpCpos : 0 < pC.radius := lt_of_lt_of_le (show (0 : ENNReal) < (r : ENNReal) by
    exact_mod_cast hr0) hrC
  let g : ℂ → ℂ := fun z ↦ pC.sum (z - Complex.ofReal x)
  have hgSeries : HasFPowerSeriesOnBall g pC (Complex.ofReal x) pC.radius := by
    simpa [g] using (pC.hasFPowerSeriesOnBall hpCpos).comp_sub (Complex.ofReal x)
  have hg : AnalyticOnNhd ℂ g (Metric.eball (Complex.ofReal x) r) := by
    -- Restrict the complex Taylor expansion to the smaller ball `eball (ofReal x) r`.
    exact (hgSeries.mono hr0 hrC).analyticOnNhd
  refine ⟨r, hr0', g, hg, ?_⟩
  intro t ht
  have htR : t ∈ Metric.eball x R := Metric.eball_subset_eball (le_of_lt hrR) ht
  have htNorm : ‖t - x‖ < r := by
    simpa [Metric.mem_eball, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using ht
  have hsubR : t - x ∈ Metric.eball (0 : ℝ) R := by
    -- The smaller real ball sits inside the original Taylor ball of `u`.
    simpa [Metric.mem_eball, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using htR
  have hsubPR : t - x ∈ Metric.eball (0 : ℝ) pR.radius := by
    -- The same point is also inside the convergence ball of the scalar series.
    simpa [Metric.mem_eball, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using (Metric.eball_subset_eball hR.r_le hsubR)
  have hsubPC : (Complex.ofReal (t - x) : ℂ) ∈ Metric.eball (0 : ℂ) pC.radius := by
    -- The complexified series converges on the chosen complex ball.
    have htComplexNorm : ‖(Complex.ofReal t : ℂ) - Complex.ofReal x‖ < r := by
      calc
        ‖(Complex.ofReal t : ℂ) - Complex.ofReal x‖
            = ‖Complex.ofReal (t - x)‖ := by rw [Complex.ofReal_sub]
        _ = ‖t - x‖ := Complex.norm_real (t - x)
        _ < r := htNorm
    have htComplexCenter : (Complex.ofReal t : ℂ) ∈ Metric.eball (Complex.ofReal x) r := by
      simpa [Metric.mem_eball, dist_eq_norm] using htComplexNorm
    have htComplex : (Complex.ofReal (t - x) : ℂ) ∈ Metric.eball (0 : ℂ) r := by
      simpa [Metric.mem_eball, dist_eq_norm, Complex.ofReal_sub] using htComplexCenter
    exact Metric.eball_subset_eball hrC htComplex
  have huEval : u t = pR.sum (t - x) := by
    -- Evaluate the real Taylor expansion at the translated real point.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hR.sum hsubR
  -- Evaluate the complex series on the real axis and compare it to the real series.
  calc
    g (Complex.ofReal t)
        = pC.sum (Complex.ofReal (t - x)) := by
            simp [g, Complex.ofReal_sub]
    _ = Complex.ofReal (pR.sum (t - x)) := by
          symm
          exact ofScalars_complex_sum_ofReal_eq (c := c) hsubPR hsubPC
    _ = (u t : ℂ) := by
          simpa [huEval]

/-- Helper for Exercise 15: a complex-valued real-analytic germ has a holomorphic extension to a
small complex ball centered at the same real point. -/
lemma analyticAt_exists_complex_eball_extension
    {f : ℝ → ℂ} {x : ℝ} (hf : AnalyticAt ℝ f x) :
    ∃ r : NNReal, 0 < r ∧ ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.eball (Complex.ofReal x) r) ∧
      Set.EqOn (fun t : ℝ ↦ g (Complex.ofReal t)) f (Metric.eball x r) := by
  have hRe : AnalyticAt ℝ (fun t : ℝ ↦ (f t).re) x := (Complex.reCLM.analyticAt _).comp hf
  have hIm : AnalyticAt ℝ (fun t : ℝ ↦ (f t).im) x := (Complex.imCLM.analyticAt _).comp hf
  obtain ⟨rRe, hrRe, gRe, hgRe, hEqRe⟩ := real_analyticAt_exists_complex_eball_extension hRe
  obtain ⟨rIm, hrIm, gIm, hgIm, hEqIm⟩ := real_analyticAt_exists_complex_eball_extension hIm
  let r : NNReal := min rRe rIm
  let g : ℂ → ℂ := fun z ↦ gRe z + Complex.I * gIm z
  have hrleRe : (r : ENNReal) ≤ rRe := by
    exact_mod_cast min_le_left rRe rIm
  have hrleIm : (r : ENNReal) ≤ rIm := by
    exact_mod_cast min_le_right rRe rIm
  have hgReSmall : AnalyticOnNhd ℂ gRe (Metric.eball (Complex.ofReal x) r) := by
    -- Restrict the real-part extension to the common smaller ball.
    exact hgRe.mono (Metric.eball_subset_eball hrleRe)
  have hgImSmall : AnalyticOnNhd ℂ gIm (Metric.eball (Complex.ofReal x) r) := by
    -- Restrict the imaginary-part extension to the common smaller ball.
    exact hgIm.mono (Metric.eball_subset_eball hrleIm)
  have hg : AnalyticOnNhd ℂ g (Metric.eball (Complex.ofReal x) r) := by
    -- Recombine the two scalar extensions into a single complex-valued extension.
    exact hgReSmall.add ((analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ ↦ Complex.I)
      (Metric.eball (Complex.ofReal x) r)).mul hgImSmall)
  refine ⟨r, lt_min hrRe hrIm, g, hg, ?_⟩
  intro t ht
  have htRe : t ∈ Metric.eball x rRe := Metric.eball_subset_eball hrleRe ht
  have htIm : t ∈ Metric.eball x rIm := Metric.eball_subset_eball hrleIm ht
  -- On the real axis, the recombined extension recovers the original complex value.
  calc
    g (Complex.ofReal t)
        = gRe (Complex.ofReal t) + Complex.I * gIm (Complex.ofReal t) := by
            simp [g]
    _ = Complex.ofReal ((f t).re) + Complex.I * Complex.ofReal ((f t).im) := by
          simp [hEqRe htRe, hEqIm htIm]
    _ = f t := by
          simpa [mul_comm] using Complex.re_add_im (f t)

/-- Helper for Exercise 15: the real part of a point in an overlap of two complex balls centered
on the real axis lies in the overlap of the corresponding real balls. -/
lemma exists_real_point_mem_two_eballs_of_complex_overlap
    {x y : ℝ} {r s : NNReal}
    (hxy : (Metric.eball (Complex.ofReal x) r ∩ Metric.eball (Complex.ofReal y) s).Nonempty) :
    ∃ t : ℝ, t ∈ Metric.eball x r ∧ t ∈ Metric.eball y s := by
  rcases hxy with ⟨z, hz₁, hz₂⟩
  refine ⟨z.re, ?_, ?_⟩
  · have hz₁' : ‖z - Complex.ofReal x‖ < r := by
      simpa [Metric.mem_eball, dist_eq_norm] using hz₁
    have hre : |z.re - x| ≤ ‖z - Complex.ofReal x‖ := by
      simpa [Complex.sub_re] using
        (Complex.abs_re_le_norm (z - Complex.ofReal x))
    have : |z.re - x| < r := lt_of_le_of_lt hre hz₁'
    simpa [Metric.mem_eball, Real.dist_eq, abs_sub_comm] using this
  · have hz₂' : ‖z - Complex.ofReal y‖ < s := by
      simpa [Metric.mem_eball, dist_eq_norm] using hz₂
    have hre : |z.re - y| ≤ ‖z - Complex.ofReal y‖ := by
      simpa [Complex.sub_re] using
        (Complex.abs_re_le_norm (z - Complex.ofReal y))
    have : |z.re - y| < s := lt_of_le_of_lt hre hz₂'
    simpa [Metric.mem_eball, Real.dist_eq, abs_sub_comm] using this

/-- Helper for Exercise 15: the real axis accumulates at every point of a punctured real ball even
after embedding that ball into `ℂ`. -/
lemma ofReal_mem_closure_image_punctured_eball
    {t : ℝ} {ρ : NNReal} (hρ : 0 < ρ) :
    Complex.ofReal t ∈ closure (Complex.ofReal '' ((Metric.eball t ρ : Set ℝ) \ {t})) := by
  apply mem_closure_image Complex.continuous_ofReal.continuousAt
  rw [Real.mem_closure_iff]
  intro ε hε
  let δ : ℝ := min (ε / 2) (ρ / 2)
  have hρ' : 0 < (ρ : ℝ) := by
    exact_mod_cast hρ
  have hδpos : 0 < δ := by
    positivity
  have hδltρ : δ < ρ := by
    have hδle : δ ≤ ρ / 2 := min_le_right _ _
    linarith
  have hδltε : δ < ε := by
    have hδle : δ ≤ ε / 2 := min_le_left _ _
    linarith
  refine ⟨t + δ, ?_, ?_⟩
  · constructor
    · have hmem : |(t + δ) - t| < ρ := by
        simpa [abs_of_nonneg hδpos.le] using hδltρ
      simpa [Metric.mem_eball, Real.dist_eq] using hmem
    · have hneq : t + δ ≠ t := by
        linarith
      simpa [Set.mem_singleton_iff] using hneq
  · simpa [abs_of_nonneg hδpos.le] using hδltε

/-- Helper for Exercise 15: two holomorphic charts that both extend the same real-analytic
function along overlapping real balls must coincide on the whole complex overlap. -/
lemma local_extensions_eqOn_overlap
    {f : ℝ → ℂ} {x y : ℝ} {rx ry : NNReal} {gx gy : ℂ → ℂ}
    (hxA : AnalyticOnNhd ℂ gx (Metric.eball (Complex.ofReal x) rx))
    (hyA : AnalyticOnNhd ℂ gy (Metric.eball (Complex.ofReal y) ry))
    (hxEq : Set.EqOn (fun t : ℝ ↦ gx (Complex.ofReal t)) f (Metric.eball x rx))
    (hyEq : Set.EqOn (fun t : ℝ ↦ gy (Complex.ofReal t)) f (Metric.eball y ry)) :
    Set.EqOn gx gy (Metric.eball (Complex.ofReal x) rx ∩ Metric.eball (Complex.ofReal y) ry) := by
  let U : Set ℂ := Metric.eball (Complex.ofReal x) rx ∩ Metric.eball (Complex.ofReal y) ry
  by_cases hU : U = ∅
  · intro z hz
    have : z ∈ U := hz
    simpa [U, hU] using this
  · have hU_nonempty : U.Nonempty := Set.nonempty_iff_ne_empty.mpr hU
    obtain ⟨t, htx, hty⟩ := exists_real_point_mem_two_eballs_of_complex_overlap hU_nonempty
    have htx' : |t - x| < rx := by
      simpa [Metric.mem_eball, Real.dist_eq, abs_sub_comm] using htx
    have hty' : |t - y| < ry := by
      simpa [Metric.mem_eball, Real.dist_eq, abs_sub_comm] using hty
    let ρReal : ℝ := min ((rx : ℝ) - |t - x|) ((ry : ℝ) - |t - y|)
    have hρpos : 0 < ρReal := by
      have hxmargin : 0 < (rx : ℝ) - |t - x| := by
        linarith
      have hymargin : 0 < (ry : ℝ) - |t - y| := by
        linarith
      exact lt_min hxmargin hymargin
    have hρnonneg : 0 ≤ ρReal := le_of_lt hρpos
    let ρ : NNReal := ⟨ρReal, hρnonneg⟩
    have hρle₁ : (ρ : ℝ) ≤ (rx : ℝ) - |t - x| := by
      exact min_le_left _ _
    have hρle₂ : (ρ : ℝ) ≤ (ry : ℝ) - |t - y| := by
      exact min_le_right _ _
    have hsmall₁ : ∀ s : ℝ, s ∈ Metric.eball t ρ → s ∈ Metric.eball x rx := by
      intro s hs
      have hs' : |s - t| < ρ := by
        simpa [Metric.mem_eball, Real.dist_eq, abs_sub_comm] using hs
      have habs : |s - x| ≤ |s - t| + |t - x| := by
        simpa [Real.norm_eq_abs, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (norm_add_le (s - t) (t - x))
      have hsx : |s - x| < rx := by
        apply lt_of_le_of_lt habs
        linarith
      simpa [Metric.mem_eball, Real.dist_eq, abs_sub_comm] using hsx
    have hsmall₂ : ∀ s : ℝ, s ∈ Metric.eball t ρ → s ∈ Metric.eball y ry := by
      intro s hs
      have hs' : |s - t| < ρ := by
        simpa [Metric.mem_eball, Real.dist_eq, abs_sub_comm] using hs
      have habs : |s - y| ≤ |s - t| + |t - y| := by
        simpa [Real.norm_eq_abs, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (norm_add_le (s - t) (t - y))
      have hsy : |s - y| < ry := by
        apply lt_of_le_of_lt habs
        linarith
      simpa [Metric.mem_eball, Real.dist_eq, abs_sub_comm] using hsy
    have htU₁ : Complex.ofReal t ∈ Metric.eball (Complex.ofReal x) rx := by
      have hedist : edist (Complex.ofReal t) (Complex.ofReal x) = edist t x := by
        simpa using (Complex.edist_of_im_eq (z := Complex.ofReal t) (w := Complex.ofReal x)
          (by simp))
      rw [Metric.mem_eball, hedist]
      simpa [Metric.mem_eball] using htx
    have htU₂ : Complex.ofReal t ∈ Metric.eball (Complex.ofReal y) ry := by
      have hedist : edist (Complex.ofReal t) (Complex.ofReal y) = edist t y := by
        simpa using (Complex.edist_of_im_eq (z := Complex.ofReal t) (w := Complex.ofReal y)
          (by simp))
      rw [Metric.mem_eball, hedist]
      simpa [Metric.mem_eball] using hty
    have hU_preconnected : IsPreconnected U := by
      simpa [U] using
        ((convex_eball (Complex.ofReal x) rx).inter (convex_eball (Complex.ofReal y) ry)).isPreconnected
    have hsubset :
        Complex.ofReal '' ((Metric.eball t ρ : Set ℝ) \ {t}) ⊆
          {z | gx z = gy z} \ {Complex.ofReal t} := by
      intro z hz
      rcases hz with ⟨s, hs, rfl⟩
      rcases hs with ⟨hsρ, hsne⟩
      have hsx : s ∈ Metric.eball x rx := hsmall₁ s hsρ
      have hsy : s ∈ Metric.eball y ry := hsmall₂ s hsρ
      constructor
      · change gx (Complex.ofReal s) = gy (Complex.ofReal s)
        exact (hxEq hsx).trans (hyEq hsy).symm
      · simpa using hsne
    have hclosure :
        Complex.ofReal t ∈ closure ({z | gx z = gy z} \ {Complex.ofReal t}) := by
      refine closure_mono hsubset ?_
      have hρpos' : 0 < ρ := hρpos
      exact ofReal_mem_closure_image_punctured_eball hρpos'
    have hxA' : AnalyticOnNhd ℂ gx U := by
      exact hxA.mono fun z hz ↦ hz.1
    have hyA' : AnalyticOnNhd ℂ gy U := by
      exact hyA.mono fun z hz ↦ hz.2
    have htU : Complex.ofReal t ∈ U := ⟨htU₁, htU₂⟩
    exact hxA'.eqOn_of_preconnected_of_mem_closure hyA' hU_preconnected htU hclosure

/-- Exercise 15: a complex-valued real-analytic function on an interval of `ℝ` extends to a
complex-analytic function on some connected open subset of `ℂ` containing that interval. -/
theorem exists_complex_analytic_extension_on_interval
    {I : Set ℝ} (hI : I.OrdConnected) {f : ℝ → ℂ} (hf : AnalyticOnNhd ℝ f I) :
    ∃ (D : Set ℂ) (g : ℂ → ℂ),
      IsOpen D ∧
      IsConnected D ∧
      Complex.ofReal '' I ⊆ D ∧
      AnalyticOnNhd ℂ g D ∧
      Set.EqOn (g ∘ Complex.ofReal) f I := by
  by_cases hI_empty : I = ∅
  · -- The empty interval case is immediate.
    refine ⟨Set.univ, fun _ ↦ 0, isOpen_univ, isConnected_univ, ?_, analyticOnNhd_const, ?_⟩
    · simp [hI_empty]
    · simpa [hI_empty]
  · -- Build the local holomorphic charts that will later be glued along the interval.
    have hcharts :
        ∀ x ∈ I, ∃ r : NNReal, 0 < r ∧ ∃ g : ℂ → ℂ,
          AnalyticOnNhd ℂ g (Metric.eball (Complex.ofReal x) r) ∧
          Set.EqOn (fun t : ℝ ↦ g (Complex.ofReal t)) f (Metric.eball x r) := by
      intro x hx
      exact analyticAt_exists_complex_eball_extension (hf x hx)
    classical
    let r : I → NNReal := fun x ↦ Classical.choose (hcharts x x.2)
    let chart : I → ℂ → ℂ := fun x ↦
      Classical.choose ((Classical.choose_spec (hcharts x x.2)).2)
    have hr : ∀ x : I, 0 < r x := by
      intro x
      exact (Classical.choose_spec (hcharts x x.2)).1
    have hchart_analytic :
        ∀ x : I, AnalyticOnNhd ℂ (chart x) (Metric.eball (Complex.ofReal x.1) (r x)) := by
      intro x
      exact (Classical.choose_spec ((Classical.choose_spec (hcharts x x.2)).2)).1
    have hchart_real :
        ∀ x : I, Set.EqOn (fun t : ℝ ↦ chart x (Complex.ofReal t)) f (Metric.eball x.1 (r x)) := by
      intro x
      exact (Classical.choose_spec ((Classical.choose_spec (hcharts x x.2)).2)).2
    let U : Set ℂ := ⋃ x : I, Metric.eball (Complex.ofReal x.1) (r x)
    have hU_open : IsOpen U := by
      dsimp [U]
      exact isOpen_iUnion fun x : I ↦
        (Metric.isOpen_eball : IsOpen (Metric.eball (Complex.ofReal x.1) (r x)))
    have himage_subset_U : Complex.ofReal '' I ⊆ U := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      refine Set.mem_iUnion_of_mem ⟨x, hx⟩ ?_
      -- Each real point sits at the center of its own local complex ball.
      simpa [Metric.mem_eball] using hr ⟨x, hx⟩
    have hcover : ∀ z ∈ U, ∃ x : I, z ∈ Metric.eball (Complex.ofReal x.1) (r x) := by
      intro z hz
      simpa [U] using hz
    let pickedChart : ∀ z : ℂ, z ∈ U → I := fun z hz ↦ Classical.choose (hcover z hz)
    let G : ℂ → ℂ := fun z ↦ if hz : z ∈ U then chart (pickedChart z hz) z else 0
    have hG_eq_local :
        ∀ x : I, Set.EqOn G (chart x) (Metric.eball (Complex.ofReal x.1) (r x)) := by
      intro x z hz
      have hzU : z ∈ U := Set.mem_iUnion_of_mem x hz
      have hpicked :
          z ∈ Metric.eball (Complex.ofReal (pickedChart z hzU).1) (r (pickedChart z hzU)) := by
        simpa [pickedChart] using Classical.choose_spec (hcover z hzU)
      -- The overlap uniqueness step makes the choice defining `G` independent of the chosen chart.
      have hEq :
          chart x z = chart (pickedChart z hzU) z := by
        exact local_extensions_eqOn_overlap
          (hchart_analytic x)
          (hchart_analytic (pickedChart z hzU))
          (hchart_real x)
          (hchart_real (pickedChart z hzU))
          ⟨hz, hpicked⟩
      simpa [G, hzU] using hEq.symm
    have hG_analytic : AnalyticOnNhd ℂ G U := by
      intro z hz
      let x : I := pickedChart z hz
      have hzx : z ∈ Metric.eball (Complex.ofReal x.1) (r x) := by
        simpa [x, pickedChart] using Classical.choose_spec (hcover z hz)
      have hEqNear : chart x =ᶠ[𝓝 z] G := by
        refine Filter.mem_of_superset (Metric.isOpen_eball.mem_nhds hzx) ?_
        intro w hw
        change chart x w = G w
        symm
        exact hG_eq_local x hw
      -- Near each point of `U`, the glued function agrees with one analytic chart.
      exact (hchart_analytic x z hzx).congr hEqNear
    have hI_nonempty : I.Nonempty := Set.nonempty_iff_ne_empty.mpr hI_empty
    obtain ⟨x₀, hx₀⟩ := hI_nonempty
    let D : Set ℂ := connectedComponentIn U (Complex.ofReal x₀)
    have hx₀U : Complex.ofReal x₀ ∈ U := by
      exact himage_subset_U (by exact ⟨x₀, hx₀, rfl⟩)
    have hD_open : IsOpen D := by
      simpa [D] using hU_open.connectedComponentIn (x := Complex.ofReal x₀)
    have hD_connected : IsConnected D := by
      simpa [D] using (isConnected_connectedComponentIn_iff (x := Complex.ofReal x₀) (F := U)).2 hx₀U
    have himage_preconnected : IsPreconnected (Complex.ofReal '' I) := by
      exact hI.isPreconnected.image (fun x : ℝ ↦ Complex.ofReal x)
        Complex.continuous_ofReal.continuousOn
    have himage_subset_D : Complex.ofReal '' I ⊆ D := by
      have hx₀image : Complex.ofReal x₀ ∈ Complex.ofReal '' I := by
        exact ⟨x₀, hx₀, rfl⟩
      simpa [D] using himage_preconnected.subset_connectedComponentIn hx₀image himage_subset_U
    have hG_analytic_D : AnalyticOnNhd ℂ G D := by
      exact hG_analytic.mono (connectedComponentIn_subset U (Complex.ofReal x₀))
    have hG_real : Set.EqOn (G ∘ Complex.ofReal) f I := by
      intro x hx
      have hxBallReal : x ∈ Metric.eball x (r ⟨x, hx⟩) := by
        simpa [Metric.mem_eball] using hr ⟨x, hx⟩
      have hxBallComplex :
          Complex.ofReal x ∈ Metric.eball (Complex.ofReal x) (r ⟨x, hx⟩) := by
        simpa [Metric.mem_eball] using hr ⟨x, hx⟩
      -- Evaluate the glued chart at the center point to recover the original real function.
      calc
        (G ∘ Complex.ofReal) x = chart ⟨x, hx⟩ (Complex.ofReal x) := by
          exact hG_eq_local ⟨x, hx⟩ hxBallComplex
        _ = f x := hchart_real ⟨x, hx⟩ hxBallReal
    refine ⟨D, G, hD_open, hD_connected, himage_subset_D, hG_analytic_D, hG_real⟩
