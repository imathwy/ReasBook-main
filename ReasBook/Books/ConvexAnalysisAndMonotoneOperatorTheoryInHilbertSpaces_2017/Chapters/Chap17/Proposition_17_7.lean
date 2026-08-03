import Mathlib
import BauschkeLean.Chap02.Definition_2_54
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap08.Proposition_8_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The first-order lower-support inequality on the effective domain associated to a Gâteaux
derivative field `DT`. -/
def GateauxSupportInequalityOn
    (f : H → Set.Ioi (⊥ : EReal)) (DT : H → H →L[ℝ] ℝ) : Prop :=
  ∀ x ∈ effectiveDomain f, ∀ y ∈ effectiveDomain f,
    DT y (x - y) + (f y : EReal).toReal ≤ (f x : EReal).toReal

/-- The derivative field `DT` is monotone on `U` when every pair of points of `U` has
nonnegative monotonicity pairing. -/
def GateauxDerivativeMonotoneOn
    (DT : H → H →L[ℝ] ℝ) (U : Set H) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, 0 ≤ (DT x - DT y) (x - y)

/-- The second derivative field `A₂` is nonnegative on `U` when each of its quadratic forms is
nonnegative on every direction at every point of `U`. -/
def GateauxSecondDerivativeNonnegativeOn
    (A₂ : H → H →L[ℝ] H →L[ℝ] ℝ) (U : Set H) : Prop :=
  ∀ x ∈ U, ∀ z : H, 0 ≤ A₂ x z z

/-- Helper for Proposition 17 7: subtracting two points on the same affine segment factors through
the segment direction. -/
private lemma lineMap_sub_lineMap_eq_smul_sub
    (x y : H) (s t : ℝ) :
    AffineMap.lineMap y x s - AffineMap.lineMap y x t = (s - t) • (x - y) := by
  -- Expand both affine-segment points around the same base point and collect terms.
  calc
    AffineMap.lineMap y x s - AffineMap.lineMap y x t
        = (s • (x - y) + y) - (t • (x - y) + y) := by
            rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module']
    _ = s • (x - y) - t • (x - y) := by
          simp
    _ = (s - t) • (x - y) := by
          rw [sub_smul]

/-- Helper for Proposition 17 7: a Gâteaux derivative field differentiates every translated segment
trace at an arbitrary parameter. -/
private lemma segment_curve_hasDerivAt
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    {T : H → K} {DT : H → H →L[ℝ] K} {U : Set H} {x h : H} {t : ℝ}
    (hGateaux : HasGateauxDerivativeOn T DT U) (ht : x + t • h ∈ U) :
    HasDerivAt (fun s : ℝ ↦ T (x + s • h)) (DT (x + t • h) h) t := by
  let path : ℝ → K := fun s ↦ T ((x + t • h) + s • h)
  have hline : HasDerivAt path (DT (x + t • h) h) 0 := by
    -- Recenter the line derivative at time `t` and use the Gâteaux hypothesis
    -- at the recentered point.
    simpa [HasLineDerivAt, path] using
      (HasGateauxDerivativeWithinAt.hasLineDerivAt (hGateaux (x + t • h) ht) h)
  have hline_shift : HasDerivAt path (DT (x + t • h) h) (-t + t) := by
    simpa using hline
  -- Shift the recentered derivative statement back to parameter `t`.
  simpa [path, add_assoc, add_left_comm, add_comm, add_smul, smul_add, mul_comm,
    mul_left_comm, mul_assoc, one_smul] using
    HasDerivAt.comp_const_add (-t) t hline_shift

/-- Helper for Proposition 17 7: the real-valued trace of `f` along a segment has derivative given
by the Gâteaux derivative field applied to the segment direction. -/
private lemma line_trace_hasDerivAt_toReal
    (f : H → Set.Ioi (⊥ : EReal)) (DT : H → H →L[ℝ] ℝ)
    (hDT : HasGateauxDerivativeOn (fun x ↦ (f x : EReal).toReal) DT (effectiveDomain f))
    {x y : H} {t : ℝ} (ht : AffineMap.lineMap y x t ∈ effectiveDomain f) :
    HasDerivAt (fun s : ℝ ↦ (f (AffineMap.lineMap y x s) : EReal).toReal)
      (DT (AffineMap.lineMap y x t) (x - y)) t := by
  have ht' : y + t • (x - y) ∈ effectiveDomain f := by
    simpa [AffineMap.lineMap_apply_module', add_comm] using ht
  -- Rewrite the affine segment as a translated line with base point `y` and direction `x - y`.
  simpa [AffineMap.lineMap_apply_module', sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (segment_curve_hasDerivAt
      (T := fun z ↦ (f z : EReal).toReal) (DT := DT) (U := effectiveDomain f)
      (x := y) (h := x - y) hDT ht')

/-- Helper for Proposition 17 7: the scalar trace of the derivative field along a segment has the
expected second-derivative formula. -/
private lemma line_derivative_trace_hasDerivAt
    (DT : H → H →L[ℝ] ℝ) (A₂ : H → H →L[ℝ] H →L[ℝ] ℝ)
    {U : Set H} (hA₂ : HasGateauxDerivativeOn DT A₂ U)
    {x y : H} {t : ℝ} (ht : AffineMap.lineMap y x t ∈ U) :
    HasDerivAt (fun s : ℝ ↦ DT (AffineMap.lineMap y x s) (x - y))
      (A₂ (AffineMap.lineMap y x t) (x - y) (x - y)) t := by
  have ht' : y + t • (x - y) ∈ U := by
    simpa [AffineMap.lineMap_apply_module', add_comm] using ht
  have hop :
      HasDerivAt (fun s : ℝ ↦ DT (AffineMap.lineMap y x s))
        (A₂ (AffineMap.lineMap y x t) (x - y)) t := by
    -- Differentiate the operator-valued segment trace before evaluating it at the fixed chord.
    simpa [AffineMap.lineMap_apply_module', sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using (segment_curve_hasDerivAt (T := DT) (DT := A₂) (U := U)
        (x := y) (h := x - y) hA₂ ht')
  -- Apply the differentiated operator trace to the fixed segment direction.
  simpa using hop.clm_apply (hasDerivAt_const t (x - y))

/-- Helper for Proposition 17 7: convexity on the effective domain yields the first-order support
inequality attached to the derivative field `DT`. -/
private lemma gateaux_supportInequalityOn_of_convexOn
    (f : H → Set.Ioi (⊥ : EReal)) (DT : H → H →L[ℝ] ℝ)
    (hDT : HasGateauxDerivativeOn (fun x ↦ (f x : EReal).toReal) DT (effectiveDomain f))
    (hconvf : ConvexOn f (effectiveDomain f)) :
    GateauxSupportInequalityOn f DT := by
  intro x hx y hy
  let φ : ℝ → ℝ := fun t ↦ (f (AffineMap.lineMap y x t) : EReal).toReal
  have hφ_conv :
      _root_.ConvexOn ℝ ((AffineMap.lineMap y x) ⁻¹' effectiveDomain f) φ := by
    -- Restrict the real-valued convex representative of `f` to the affine segment through `y,x`.
    simpa [φ, Function.comp] using
      (ConvexOn.toReal_convexOn_effectiveDomain hconvf).comp_affineMap (AffineMap.lineMap y x)
  have hzero : (0 : ℝ) ∈ (AffineMap.lineMap y x) ⁻¹' effectiveDomain f := by
    -- The left endpoint of the segment is `y`.
    simpa [AffineMap.lineMap_apply_zero] using hy
  have hone : (1 : ℝ) ∈ (AffineMap.lineMap y x) ⁻¹' effectiveDomain f := by
    -- The right endpoint of the segment is `x`.
    simpa [AffineMap.lineMap_apply_one] using hx
  have hφ_deriv0 : HasDerivAt φ (DT y (x - y)) 0 := by
    -- Differentiate the scalar trace at the left endpoint.
    simpa [φ, AffineMap.lineMap_apply_zero] using
      (line_trace_hasDerivAt_toReal (f := f) (DT := DT) hDT (x := x) (y := y) (t := 0) (by
        simpa [AffineMap.lineMap_apply_zero] using hy))
  have hslope : deriv φ 0 ≤ slope φ 0 1 := by
    -- Convexity bounds the endpoint secant slope below by the derivative at `0`.
    exact hφ_conv.deriv_le_slope hzero hone zero_lt_one hφ_deriv0.differentiableAt
  have hineq_real : DT y (x - y) ≤ (f x : EReal).toReal - (f y : EReal).toReal := by
    rw [hφ_deriv0.deriv] at hslope
    simpa [φ, slope_def_field, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using
      hslope
  linarith

/-- Helper for Proposition 17 7: monotonicity of the Gâteaux derivative field implies convexity on
the open convex effective domain by applying the one-variable derivative criterion on each
segment. -/
private lemma convexOn_effectiveDomain_of_gateauxDerivativeMonotoneOn
    (f : H → Set.Ioi (⊥ : EReal)) (DT : H → H →L[ℝ] ℝ)
    (hdom : (effectiveDomain f).Nonempty) (hopen : IsOpen (effectiveDomain f))
    (hconv : Convex ℝ (effectiveDomain f))
    (hDT : HasGateauxDerivativeOn (fun x ↦ (f x : EReal).toReal) DT (effectiveDomain f))
    (hmono : GateauxDerivativeMonotoneOn DT (effectiveDomain f)) :
    ConvexOn f (effectiveDomain f) := by
  refine ⟨hdom, fun x hx ↦ hx, ?_⟩
  intro x hx y hy α hα0 hα1
  let I : Set ℝ := (AffineMap.lineMap y x) ⁻¹' effectiveDomain f
  let φ : ℝ → ℝ := fun t ↦ (f (AffineMap.lineMap y x t) : EReal).toReal
  have hI_convex : Convex ℝ I := by
    -- Pull back the convex effective domain to the scalar parameter interval.
    simpa [I] using hconv.affine_preimage (AffineMap.lineMap y x)
  have hI_open : IsOpen I := by
    -- Openness is preserved by the affine trace map.
    simpa [I] using hopen.preimage AffineMap.lineMap_continuous
  have hφ_diff : DifferentiableOn ℝ φ I := by
    intro t ht
    -- Every point of the parameter domain differentiates by the segment trace formula.
    exact (line_trace_hasDerivAt_toReal f DT hDT ht).differentiableAt.differentiableWithinAt
  have hφ'_mono : MonotoneOn (deriv φ) I := by
    intro s hs t ht hst
    have hs_deriv : deriv φ s = DT (AffineMap.lineMap y x s) (x - y) := by
      simpa [φ, ContinuousLinearMap.sub_apply, sub_eq_add_neg] using
        (line_trace_hasDerivAt_toReal (f := f) (DT := DT) hDT (x := x) (y := y) (t := s) hs).deriv
    have ht_deriv : deriv φ t = DT (AffineMap.lineMap y x t) (x - y) := by
      simpa [φ, ContinuousLinearMap.sub_apply, sub_eq_add_neg] using
        (line_trace_hasDerivAt_toReal (f := f) (DT := DT) hDT (x := x) (y := y) (t := t) ht).deriv
    have hs_dom : AffineMap.lineMap y x s ∈ effectiveDomain f := hs
    have ht_dom : AffineMap.lineMap y x t ∈ effectiveDomain f := ht
    have hsub :
        AffineMap.lineMap y x t - AffineMap.lineMap y x s = (t - s) • (x - y) := by
      simpa using lineMap_sub_lineMap_eq_smul_sub x y t s
    have hpair :
        0 ≤ (t - s) * ((DT (AffineMap.lineMap y x t) - DT (AffineMap.lineMap y x s)) (x - y)) := by
      simpa [hsub, ContinuousLinearMap.sub_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
        using hmono (AffineMap.lineMap y x t) ht_dom (AffineMap.lineMap y x s) hs_dom
    rcases eq_or_lt_of_le hst with rfl | hst'
    · exact le_rfl
    have hpair' :
        0 ≤ (DT (AffineMap.lineMap y x t) - DT (AffineMap.lineMap y x s)) (x - y) := by
      exact (mul_nonneg_iff_of_pos_left (sub_pos.mpr hst')).mp hpair
    rw [hs_deriv, ht_deriv]
    exact sub_nonneg.mp <| by
      simpa [ContinuousLinearMap.sub_apply, sub_eq_add_neg] using hpair'
  have hφ_conv : _root_.ConvexOn ℝ I φ :=
    convexOn_of_monotoneOn_deriv_openInterval I φ hI_convex hI_open hφ_diff hφ'_mono
  have hone : (1 : ℝ) ∈ I := by
    -- The parameter `1` corresponds to `x`.
    simpa [I, AffineMap.lineMap_apply_one] using hx
  have hzero : (0 : ℝ) ∈ I := by
    -- The parameter `0` corresponds to `y`.
    simpa [I, AffineMap.lineMap_apply_zero] using hy
  have hα_mem : α ∈ I := by
    -- Convexity of the effective domain keeps the interior point of the segment finite.
    simpa [I, AffineMap.lineMap_apply_module'] using
      hconv.lineMap_mem hy hx ⟨hα0.le, hα1.le⟩
  have hineq_real :
      φ α ≤ α * φ 1 + (1 - α) * φ 0 := by
    -- Apply Jensen's inequality to the scalar trace on the pulled-back interval.
    simpa [smul_eq_mul] using
      (hφ_conv.2 hone hzero hα0.le (sub_nonneg.mpr hα1.le) (by ring))
  have hineq_real_explicit :
      (f (AffineMap.lineMap y x α) : EReal).toReal ≤
        α * (f x : EReal).toReal + (1 - α) * (f y : EReal).toReal := by
    simpa [φ, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using hineq_real
  have hz_dom : AffineMap.lineMap y x α ∈ effectiveDomain f := hα_mem
  have hz_top : (f (AffineMap.lineMap y x α) : EReal) ≠ ⊤ :=
    ne_of_lt (mem_effectiveDomain_iff.mp hz_dom)
  have hz_bot : (f (AffineMap.lineMap y x α) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (AffineMap.lineMap y x α) : EReal) from
      (f (AffineMap.lineMap y x α)).2)
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hineq_ereal :
      (f (AffineMap.lineMap y x α) : EReal) ≤
        (((α * (f x : EReal).toReal + (1 - α) * (f y : EReal).toReal : ℝ)) : EReal) := by
    -- Cast the real Jensen inequality back to `EReal`.
    calc
      (f (AffineMap.lineMap y x α) : EReal)
          = (((f (AffineMap.lineMap y x α) : EReal).toReal : ℝ) : EReal) := by
            symm
            exact EReal.coe_toReal hz_top hz_bot
      _ ≤ (((α * (f x : EReal).toReal + (1 - α) * (f y : EReal).toReal : ℝ)) : EReal) := by
            exact_mod_cast hineq_real_explicit
  have hsub_cast : (((1 - α : ℝ) : EReal)) = 1 - (α : EReal) := by
    rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
  have hcombo : α • x + (1 - α) • y = AffineMap.lineMap y x α := by
    rw [AffineMap.lineMap_apply_module']
    rw [sub_smul, smul_sub, one_smul]
    abel_nf
  -- Rewrite the scalar inequality back to the original `EReal` Jensen inequality.
  calc
    (f (α • x + (1 - α) • y) : EReal)
        = (f (AffineMap.lineMap y x α) : EReal) := by rw [hcombo]
    _ ≤ (((α * (f x : EReal).toReal + (1 - α) * (f y : EReal).toReal : ℝ)) : EReal) := hineq_ereal
    _ = (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := by
          rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul, EReal.coe_toReal hx_top hx_bot,
            EReal.coe_toReal hy_top hy_bot]
          simp [hsub_cast]

/-- Helper for Proposition 17 7: nonnegativity of a second derivative field forces monotonicity of
the first derivative field by applying the one-dimensional monotonicity criterion on each
segment. -/
private lemma gateaux_derivativeMonotoneOn_of_secondDerivativeNonnegative
    (DT : H → H →L[ℝ] ℝ) (A₂ : H → H →L[ℝ] H →L[ℝ] ℝ)
    {U : Set H} (hconv : Convex ℝ U)
    (hA₂ : HasGateauxDerivativeOn DT A₂ U)
    (hnonneg : GateauxSecondDerivativeNonnegativeOn A₂ U) :
    GateauxDerivativeMonotoneOn DT U := by
  intro x hx y hy
  let k : ℝ → ℝ := fun t ↦ DT (AffineMap.lineMap y x t) (x - y)
  have hk_cont : ContinuousOn k (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    -- The derivative formula gives continuity of the scalar trace on the whole segment.
    exact
      (HasDerivAt.continuousAt
        (line_derivative_trace_hasDerivAt (DT := DT) (A₂ := A₂) hA₂
          (x := x) (y := y) (t := t) (hconv.lineMap_mem hy hx ht))).continuousWithinAt
  have hk_diff : DifferentiableOn ℝ k (interior (Set.Icc (0 : ℝ) 1)) := by
    intro t ht
    -- Differentiate the trace at every interior parameter.
    exact
      (HasDerivAt.differentiableAt
        (line_derivative_trace_hasDerivAt (DT := DT) (A₂ := A₂) hA₂
          (x := x) (y := y) (t := t)
          (hconv.lineMap_mem hy hx (interior_subset ht)))).differentiableWithinAt
  have hk_nonneg : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), 0 ≤ deriv k t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
    have hk_deriv :
        deriv k t = A₂ (AffineMap.lineMap y x t) (x - y) (x - y) := by
      simpa [k, ContinuousLinearMap.sub_apply, sub_eq_add_neg] using
        (line_derivative_trace_hasDerivAt (DT := DT) (A₂ := A₂) hA₂
          (x := x) (y := y) (t := t) (hconv.lineMap_mem hy hx ht')).deriv
    rw [hk_deriv]
    exact hnonneg _ (hconv.lineMap_mem hy hx ht') _
  have hk_mono : MonotoneOn k (Set.Icc (0 : ℝ) 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1) hk_cont hk_diff hk_nonneg
  have h01 : k 0 ≤ k 1 := hk_mono (by simp) (by simp) zero_le_one
  simpa [k, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    ContinuousLinearMap.sub_apply, sub_eq_add_neg] using sub_nonneg.mpr h01

/-- Helper for Proposition 17 7: monotonicity of the derivative field forces every available
second directional derivative to be nonnegative. -/
private lemma gateauxSecondDerivativeNonnegativeOn_of_gateauxDerivativeMonotoneOn
    (DT : H → H →L[ℝ] ℝ) (A₂ : H → H →L[ℝ] H →L[ℝ] ℝ)
    {U : Set H} (hA₂ : HasGateauxDerivativeOn DT A₂ U)
    (hmono : GateauxDerivativeMonotoneOn DT U) :
    GateauxSecondDerivativeNonnegativeOn A₂ U := by
  intro x hx z
  rcases (hA₂ x hx).1 z with ⟨α, hαpos, hseg⟩
  let g : ℝ → ℝ := fun t ↦ DT (x + t • z) z
  have hg_deriv :
      HasDerivWithinAt g (A₂ x z z) (Set.Ioi (0 : ℝ)) 0 := by
    -- Differentiate the operator-valued radial trace and then evaluate it at `z`.
    simpa [g] using
      ((hA₂ x hx).2 z).clm_apply (hasDerivWithinAt_const 0 (Set.Ioi (0 : ℝ)) z)
  have hg_deriv_Ioo :
      HasDerivWithinAt g (A₂ x z z) (Set.Ioo (0 : ℝ) α) 0 := by
    -- Restrict the one-sided derivative to the short interval supplied by the radial segment.
    exact hg_deriv.mono Set.Ioo_subset_Ioi_self
  have hg_mono : MonotoneOn g (Set.Ioo (0 : ℝ) α) := by
    intro s hs t ht hst
    have hsU : x + s • z ∈ U := hseg s ⟨hs.1.le, hs.2.le⟩
    have htU : x + t • z ∈ U := hseg t ⟨ht.1.le, ht.2.le⟩
    have hsub : (x + t • z) - (x + s • z) = (t - s) • z := by
      calc
        (x + t • z) - (x + s • z) = t • z - s • z := by abel_nf
        _ = (t - s) • z := by rw [sub_smul]
    have hpair : 0 ≤ (t - s) * (g t - g s) := by
      simpa [g, hsub, ContinuousLinearMap.sub_apply, smul_eq_mul, mul_comm, mul_left_comm,
        mul_assoc] using hmono (x + t • z) htU (x + s • z) hsU
    rcases eq_or_lt_of_le hst with rfl | hst'
    · exact le_rfl
    have hpair' : 0 ≤ g t - g s := by
      exact (mul_nonneg_iff_of_pos_left (sub_pos.mpr hst')).mp hpair
    exact sub_nonneg.mp hpair'
  have hacc :
      AccPt (0 : ℝ) (Filter.principal (Set.Ioo (0 : ℝ) α)) := by
    rw [accPt_principal_iff_nhdsWithin]
    have hne : (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) α)).NeBot := by
      rw [nhdsWithin_Ioo_eq_nhdsGT hαpos]
      exact nhdsGT_neBot_of_exists_gt ⟨α / 2, by positivity⟩
    simpa using hne
  -- A monotone right trace has nonnegative derivative at the left endpoint.
  exact hg_deriv_Ioo.nonneg_of_monotoneOn hacc hg_mono

-- Proof sketch: use the standard segment reduction to a one-variable function on an open interval.
-- The effective-domain nonemptiness hypothesis matches the project owner `ConvexOn`, which stores
-- properness as part of convexity on a set. Proposition 17.6 gives clause (ii) from convexity,
-- adding the two support inequalities yields clause (iii), and monotonicity of the derivative
-- along every segment gives convexity via Proposition 8.14. If a second derivative field is given
-- on the effective domain, then nonnegativity of its quadratic form is equivalent to monotonicity
-- of the first derivative field along line segments, so clause (iv) joins the same TFAE list. The
-- second-derivative field is recorded through the canonical owner `HasGateauxDerivativeOn` applied
-- to `DT`.
/-- Proposition 17 7: on a nonempty open convex effective domain, convexity of `f` is equivalent
to the first-order lower-support inequality and to monotonicity of a Gâteaux derivative field for
the finite representative `x ↦ (f x : EReal).toReal`; moreover, for any second Gâteaux derivative
field on the effective domain, these conditions are also equivalent to nonnegativity of its
quadratic form. -/
theorem convex_tfae_of_open_convex_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (DT : H → H →L[ℝ] ℝ)
    (hdom : (effectiveDomain f).Nonempty) (hopen : IsOpen (effectiveDomain f))
    (hconv : Convex ℝ (effectiveDomain f))
    (hDT : HasGateauxDerivativeOn (fun x ↦ (f x : EReal).toReal) DT (effectiveDomain f)) :
    List.TFAE
        [ConvexOn f (effectiveDomain f),
          GateauxSupportInequalityOn f DT,
          GateauxDerivativeMonotoneOn DT (effectiveDomain f)] ∧
      (∀ A₂ : H → H →L[ℝ] H →L[ℝ] ℝ,
        HasGateauxDerivativeOn DT A₂ (effectiveDomain f) →
          List.TFAE
            [ConvexOn f (effectiveDomain f),
              GateauxSupportInequalityOn f DT,
              GateauxDerivativeMonotoneOn DT (effectiveDomain f),
              GateauxSecondDerivativeNonnegativeOn A₂ (effectiveDomain f)]) := by
  have htfae :
      List.TFAE
        [ConvexOn f (effectiveDomain f),
          GateauxSupportInequalityOn f DT,
          GateauxDerivativeMonotoneOn DT (effectiveDomain f)] := by
    -- The first-order part follows the textbook cycle `(i) → (ii) → (iii) → (i)`.
    tfae_have 1 → 2 := by
      intro hconvf
      exact gateaux_supportInequalityOn_of_convexOn f DT hDT hconvf
    tfae_have 2 → 3 := by
      intro hsupport x hx y hy
      -- Add the two support inequalities and cancel the function values.
      have hxy_support := hsupport x hx y hy
      have hyx_support := hsupport y hy x hx
      have hsum : DT y (x - y) + DT x (y - x) ≤ 0 := by
        linarith
      have hneg : DT y (x - y) - DT x (x - y) ≤ 0 := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum
      simpa [ContinuousLinearMap.sub_apply, sub_eq_add_neg] using neg_nonneg.mpr hneg
    tfae_have 3 → 1 := by
      intro hmono
      exact convexOn_effectiveDomain_of_gateauxDerivativeMonotoneOn
        f DT hdom hopen hconv hDT hmono
    tfae_finish
  refine ⟨htfae, ?_⟩
  intro A₂ hA₂
  -- Reuse the first-order equivalences, then add the two second-derivative bridge implications.
  tfae_have 1 ↔ 2 := by
    exact List.TFAE.out htfae 0 1
  tfae_have 2 ↔ 3 := by
    exact List.TFAE.out htfae 1 2
  tfae_have 3 → 4 := by
    intro hmono
    exact gateauxSecondDerivativeNonnegativeOn_of_gateauxDerivativeMonotoneOn DT A₂ hA₂ hmono
  tfae_have 4 → 3 := by
    intro hnonneg
    exact gateaux_derivativeMonotoneOn_of_secondDerivativeNonnegative
      DT A₂ hconv hA₂ hnonneg
  tfae_finish

end DifferentiabilityOfConvexFunctions

end ERealFunction
