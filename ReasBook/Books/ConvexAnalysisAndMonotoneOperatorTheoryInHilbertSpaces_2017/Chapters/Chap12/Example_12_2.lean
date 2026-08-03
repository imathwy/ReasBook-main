import Mathlib
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Definition_12_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

open ERealFunction

variable {H : Type u} [NormedAddCommGroup H]

namespace ERealFunction

/-- Helper for Example 12 2: at a fixed point, the extended distance to `C` is the infimum of the
translated norm values over `C`. -/
private theorem infEDist_eq_sInf_norm_image_pointwise (C : Set H) (x : H) :
    (Metric.infEDist x C : EReal) =
      sInf ((fun y : H ↦ (‖x - y‖ : EReal)) '' C) := by
  by_cases hC : C.Nonempty
  · -- For a nonempty set, compare both sides via the same greatest-lower-bound description.
    let S : Set EReal := (fun y : H ↦ (‖x - y‖ : EReal)) '' C
    have hglbReal : IsGLB ((fun y : H ↦ dist x y) '' C) (Metric.infDist x C) :=
      Metric.isGLB_infDist hC
    have hglbEReal : IsGLB S (Metric.infDist x C : EReal) := by
      refine ⟨?_, ?_⟩
      · intro a ha
        rcases ha with ⟨y, hy, rfl⟩
        have hle : Metric.infDist x C ≤ dist x y :=
          hglbReal.1 ⟨y, hy, rfl⟩
        simpa [S, dist_eq_norm] using hle
      · intro b hb
        by_cases hb_bot : b = ⊥
        · simp [hb_bot]
        by_cases hb_top : b = ⊤
        · rcases hC with ⟨y, hy⟩
          have hle : (⊤ : EReal) ≤ (‖x - y‖ : EReal) := by
            simpa [S, hb_top] using hb ⟨y, hy, rfl⟩
          have : False := by
            simp at hle
          exact False.elim this
        have hcoe : ((b.toReal : ℝ) : EReal) = b :=
          EReal.coe_toReal hb_top hb_bot
        have hbReal : b.toReal ∈ lowerBounds ((fun y : H ↦ dist x y) '' C) := by
          intro r hr
          rcases hr with ⟨y, hy, rfl⟩
          have hle : b ≤ (‖x - y‖ : EReal) := hb ⟨y, hy, rfl⟩
          have hle' : ((b.toReal : ℝ) : EReal) ≤ (dist x y : EReal) := by
            simpa [hcoe, dist_eq_norm] using hle
          simpa using hle'
        have hle : b.toReal ≤ Metric.infDist x C :=
          hglbReal.2 hbReal
        have hle' : ((b.toReal : ℝ) : EReal) ≤ (Metric.infDist x C : EReal) := by
          exact_mod_cast hle
        simpa [hcoe] using hle'
    have hdist : (Metric.infEDist x C : EReal) = (Metric.infDist x C : EReal) := by
      rw [Metric.infDist]
      symm
      exact EReal.coe_ennreal_toReal (Metric.infEDist_ne_top (x := x) hC)
    calc
      (Metric.infEDist x C : EReal) = (Metric.infDist x C : EReal) := hdist
      _ = sInf S := hglbEReal.sInf_eq.symm
      _ = sInf ((fun y : H ↦ (‖x - y‖ : EReal)) '' C) := rfl
  · -- For the empty set, both sides are the top element.
    simp [Set.not_nonempty_iff_eq_empty.mp hC, Metric.infEDist_empty]

-- Proof sketch: compare the source-faithful `EReal` infimum over `C` with the canonical
-- extended distance `Metric.infEDist`.
/-- The source-facing extended-real distance to `C` is the `EReal` infimum of the translated
norm over `C`. -/
theorem distanceToSet_eq_sInf_norm_image (C : Set H) :
    (fun x ↦ (Metric.infEDist x C : EReal)) =
      fun x ↦ sInf ((fun y : H ↦ (‖x - y‖ : EReal)) '' C) := by
  -- The global function equality follows by evaluating the pointwise infimum formula at each `x`.
  funext x
  exact infEDist_eq_sInf_norm_image_pointwise C x

/-- Helper for Example 12 2: evaluating the indicator-plus-norm infimal convolution at `x`
reduces to the same infimum of translated norms over `C`. -/
private theorem indicator_infimalConvolution_norm_apply (C : Set H) (x : H) :
    (ι[C] □ scaledNormKernel (1 : NNReal)) x =
      sInf ((fun y : H ↦ (‖x - y‖ : EReal)) '' C) := by
  rw [infimalConvolution_apply]
  -- Restrict the infimum to points of `C`; outside `C`, the indicator contributes `⊤`.
  calc
    (⨅ y : H, (ι[C] y : EReal) + (scaledNormKernel (1 : NNReal) (x - y) : EReal))
      = ⨅ y : C, (‖x - (y : H)‖ : EReal) := by
          apply le_antisymm
          · refine le_iInf ?_
            intro y
            have hle :
                (⨅ z : H, (ι[C] z : EReal) +
                    (scaledNormKernel (1 : NNReal) (x - z) : EReal)) ≤
                  (ι[C] (y : H) : EReal) +
                    (scaledNormKernel (1 : NNReal) (x - (y : H)) : EReal) :=
              iInf_le _ (y : H)
            simpa [indicator_apply, scaledNormKernel_apply, y.property, one_mul] using hle
          · refine le_iInf ?_
            intro y
            by_cases hy : y ∈ C
            · have hle :
                  (⨅ z : C, (‖x - (z : H)‖ : EReal)) ≤
                    (‖x - ((⟨y, hy⟩ : C) : H)‖ : EReal) :=
                iInf_le (fun z : C ↦ (‖x - (z : H)‖ : EReal)) ⟨y, hy⟩
              simpa [indicator_apply, scaledNormKernel_apply, hy, one_mul] using hle
            · have hle : (⨅ z : C, (‖x - (z : H)‖ : EReal)) ≤ ⊤ := le_top
              have hle' :
                  (⨅ z : C, (‖x - (z : H)‖ : EReal)) ≤
                    (ι[C] y : EReal) + (scaledNormKernel (1 : NNReal) (x - y) : EReal) := by
                convert hle using 1
                simp [indicator_apply, hy]
              exact hle'
    _ = sInf ((fun y : H ↦ (‖x - y‖ : EReal)) '' C) := by
      symm
      rw [Set.image_eq_range, sInf_range]

-- Proof sketch: unfold the infimal convolution of `ι[C]` and `(fun x ↦ ‖x‖).toEReal`; points
-- outside `C` contribute `⊤`, while points in `C` contribute exactly `‖x - y‖`, so the defining
-- infimum reduces to the extended-real distance to `C`.
/-- Example 12 2: the distance to `C` is the infimal convolution of the indicator of `C` with the
norm. -/
theorem distanceToSet_eq_indicator_infimalConvolution_norm (C : Set H) :
    (fun x ↦ (Metric.infEDist x C : EReal)) = ι[C] □ scaledNormKernel (1 : NNReal) := by
  -- Both sides are identified with the same pointwise infimum over `C`.
  funext x
  rw [indicator_infimalConvolution_norm_apply]
  exact infEDist_eq_sInf_norm_image_pointwise C x

section

variable [NormedSpace ℝ H]

/-- Helper for Example 12 2: from a point `y` of an open set and a point `x` outside that set,
one can move slightly from `y` toward `x` while staying inside the set and strictly reducing the
distance to `x`. -/
private theorem exists_mem_and_norm_sub_lt_of_isOpen_of_not_mem
    {C : Set H} {x y : H} (hy : y ∈ C) (hx : x ∉ C) (hopen : IsOpen C) :
    ∃ z : H, z ∈ C ∧ ‖x - z‖ < ‖x - y‖ := by
  -- Move a short distance along the segment from `y` to `x` inside an open ball contained in `C`.
  have hxy : x ≠ y := by
    intro hxy
    exact hx (hxy ▸ hy)
  rcases Metric.isOpen_iff.mp hopen y hy with ⟨r, hrpos, hball⟩
  have hnorm_pos : 0 < ‖x - y‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let ε : ℝ := min (1 / 2) (r / (2 * ‖x - y‖))
  let z : H := y + ε • (x - y)
  have hε_pos : 0 < ε := by
    apply lt_min
    · norm_num
    · have hden_pos : 0 < 2 * ‖x - y‖ := by positivity
      exact div_pos hrpos hden_pos
  have hε_lt_one : ε < 1 := by
    calc
      ε ≤ 1 / 2 := min_le_left _ _
      _ < 1 := by norm_num
  have hε_mul_lt_r : ε * ‖x - y‖ < r := by
    have hε_le : ε ≤ r / (2 * ‖x - y‖) := min_le_right _ _
    have hmul_le : ε * ‖x - y‖ ≤ (r / (2 * ‖x - y‖)) * ‖x - y‖ := by
      exact mul_le_mul_of_nonneg_right hε_le (norm_nonneg _)
    have hcalc : (r / (2 * ‖x - y‖)) * ‖x - y‖ = r / 2 := by
      have hnorm_ne : ‖x - y‖ ≠ 0 := ne_of_gt hnorm_pos
      field_simp [hnorm_ne]
    have hlt : (r / (2 * ‖x - y‖)) * ‖x - y‖ < r := by
      rw [hcalc]
      nlinarith
    exact lt_of_le_of_lt hmul_le hlt
  have hz_mem_ball : z ∈ Metric.ball y r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hz_sub : z - y = ε • (x - y) := by
      simp [z, sub_eq_add_neg, add_comm, add_left_comm]
    rw [hz_sub, norm_smul, Real.norm_of_nonneg hε_pos.le]
    exact hε_mul_lt_r
  have hzC : z ∈ C := hball hz_mem_ball
  have hxz_eq : x - z = (1 - ε) • (x - y) := by
    -- Rewrite the translated point so the norm scales by the remaining segment factor.
    calc
      x - z = (x - y) - ε • (x - y) := by
        simp [z, sub_eq_add_neg, add_comm, add_assoc]
      _ = (1 : ℝ) • (x - y) - ε • (x - y) := by rw [one_smul]
      _ = (1 - ε) • (x - y) := by rw [sub_smul]
  have hone_sub_pos : 0 < 1 - ε := sub_pos.mpr hε_lt_one
  have hnorm_lt : ‖x - z‖ < ‖x - y‖ := by
    rw [hxz_eq, norm_smul, Real.norm_of_nonneg hone_sub_pos.le]
    have hcoef_lt : 1 - ε < 1 := by linarith
    nlinarith [norm_nonneg (x - y), hnorm_pos]
  exact ⟨z, hzC, hnorm_lt⟩

-- Proof sketch: exactness at `x` would produce some `y ∈ C` that attains the distance from `x` to
-- `C`. In a real normed vector space, every point of an open set can be moved slightly along the
-- segment toward an exterior point `x` while staying in `C`, which strictly decreases the norm;
-- hence no minimizer exists outside `C` when `C` is nonempty.
/-- In a real normed vector space, if `C` is nonempty and open, then the infimal convolution of
its indicator with the norm is never exact at points outside `C`. -/
theorem indicator_infimalConvolution_norm_not_exact_of_nonempty_isOpen
    (C : Set H) (hC : C.Nonempty) (hopen : IsOpen C) {x : H} (hx : x ∉ C) :
    ¬ infimalConvolution.ExactAt (ι[C]) (scaledNormKernel (1 : NNReal)) x := by
  intro hexact
  rcases hexact with ⟨y, hyExact⟩
  have hvalue :
      (Metric.infEDist x C : EReal) =
        (ι[C] □ scaledNormKernel (1 : NNReal)) x := by
    simpa using congrFun (distanceToSet_eq_indicator_infimalConvolution_norm C) x
  have hfinite : (Metric.infEDist x C : EReal) ≠ ⊤ := by
    simpa [EReal.coe_ennreal_eq_top_iff] using (Metric.infEDist_ne_top (x := x) hC)
  have hy_mem : y ∈ C := by
    by_contra hy_mem
    have htop :
        (ι[C] □ scaledNormKernel (1 : NNReal)) x = ⊤ := by
      rw [hyExact]
      simp [indicator_apply, hy_mem, scaledNormKernel_apply, one_mul]
    exact hfinite (hvalue.trans htop)
  have hdist_eq : (Metric.infEDist x C : EReal) = ‖x - y‖ := by
    calc
      (Metric.infEDist x C : EReal) = (ι[C] □ scaledNormKernel (1 : NNReal)) x := hvalue
      _ = (ι[C] y : EReal) + (scaledNormKernel (1 : NNReal) (x - y) : EReal) := hyExact
      _ = ‖x - y‖ := by
        simp [indicator_apply, hy_mem, scaledNormKernel_apply, one_mul]
  rcases exists_mem_and_norm_sub_lt_of_isOpen_of_not_mem hy_mem hx hopen with ⟨z, hzC, hzlt⟩
  have hle : (‖x - y‖ : EReal) ≤ ‖x - z‖ := by
    rw [← hdist_eq]
    calc
      ((Metric.infEDist x C : ENNReal) : EReal) ≤ (edist x z : EReal) := by
        exact (EReal.coe_ennreal_le_coe_ennreal_iff).2 (Metric.infEDist_le_edist_of_mem hzC)
      _ = ‖x - z‖ := by
        rw [edist_dist, dist_eq_norm, EReal.coe_ennreal_ofReal, max_eq_left (norm_nonneg _)]
  have hzlt' : (‖x - z‖ : EReal) < ‖x - y‖ := by
    exact_mod_cast hzlt
  exact (not_lt_of_ge hle) hzlt'

end

-- Proof sketch: choose any point `c ∈ C`; then the admissible decomposition through `c` gives a
-- finite upper bound on the infimal convolution at every `x`, so every point lies in the domain.
/-- For a nonempty set, the infimal convolution of its indicator with the norm has full domain. -/
theorem dom_indicator_infimalConvolution_norm_eq_univ_of_nonempty
    (C : Set H) (hC : C.Nonempty) :
    dom (ι[C] □ scaledNormKernel (1 : NNReal)) = Set.univ := by
  -- Rewriting by Example 12.2 reduces the domain statement to finiteness of `Metric.infEDist`.
  ext x
  rw [mem_dom_iff]
  change (ι[C] □ scaledNormKernel (1 : NNReal)) x < ⊤ ↔ x ∈ Set.univ
  have hxeq :
      (ι[C] □ scaledNormKernel (1 : NNReal)) x = (Metric.infEDist x C : EReal) := by
    simpa using congrFun (distanceToSet_eq_indicator_infimalConvolution_norm C).symm x
  rw [hxeq]
  have hfinite : (Metric.infEDist x C : EReal) ≠ ⊤ := by
    simpa [EReal.coe_ennreal_eq_top_iff] using (Metric.infEDist_ne_top (x := x) hC)
  simpa [Set.mem_univ] using lt_top_iff_ne_top.mpr hfinite

end ERealFunction
