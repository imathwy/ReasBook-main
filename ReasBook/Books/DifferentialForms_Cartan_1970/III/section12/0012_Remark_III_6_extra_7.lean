import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0003_Lemma_II_1_extra_3»
import DifferentialForms_Cartan_1970.III.section11.«0003_Theorem_III_5_extra_2»

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Bornology
open scoped unitInterval

noncomputable section

-- Semantic search tool `lean_leansearch` was unavailable in this environment, so the keyhole-
-- contour residue API in this file was checked directly against nearby section precedent:
-- `LocalResidueCircle` in Section III.5, the upper-half-plane residue
-- theorems in Proposition 3.1, and the chapter's later rational-function contour estimates.

/-
This is a `source-facing` keyhole-contour specialization. The primitive data is a rational
function `P / Q`; the residue data is carried by the chapter's local contour owner
`LocalResidueCircle`, not by the leading meromorphic coefficient. Since mathlib's principal
`Complex.log` is holomorphic on
`Complex.slitPlane`, its branch cut is `(-∞, 0]`; to state the textbook keyhole formula for
`∫_0^∞`, the source-facing branch is therefore the shifted principal branch
`z ↦ Complex.log (-z)`, whose cut is `[0, ∞)`.

The earlier over-general meromorphic statement was false: the contour argument also needs the outer
and inner circular contributions to vanish. For rational functions, the standard degree-gap and
no-pole-on-`[0, ∞)` hypotheses are the source-faithful way to encode those contour conditions.
-/
/-- Helper for Remark III.6-extra-7: the rational function whose real-axis integral is evaluated by
the keyhole contour argument. -/
abbrev rationalEval (P Q : Polynomial ℂ) : ℂ → ℂ :=
  fun z ↦ P.eval z / Q.eval z

/-- Helper for Remark III.6-extra-7: the shifted-log integrand whose residues appear in the final
formula. -/
abbrev shiftedLogRationalEval (P Q : Polynomial ℂ) : ℂ → ℂ :=
  fun z ↦ rationalEval P Q z * Complex.log (-z)

/-- Helper for Remark III.6-extra-7: the shifted slit-plane domain on which the branch
`z ↦ Complex.log (-z)` is holomorphic. -/
abbrev shiftedLogDomain : Set ℂ :=
  {z : ℂ | -z ∈ Complex.slitPlane}

/-- Helper for Remark III.6-extra-7: the meromorphic normal-form replacement of the rational
factor on the shifted slit domain, multiplied by the shifted logarithm branch. -/
abbrev shiftedLogRationalNormalForm (P Q : Polynomial ℂ) : ℂ → ℂ :=
  fun z ↦ toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z * Complex.log (-z)

/-- Helper for Remark III.6-extra-7: the finite pole set hypothesis rewritten through the local
abbreviation `rationalEval`. -/
lemma rationalEval_pole_iff_mem
    (P Q : Polynomial ℂ) {s : Finset ℂ}
    (hpoles :
      ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s) :
    ∀ z : ℂ, meromorphicOrderAt (rationalEval P Q) z < 0 ↔ z ∈ s := by
  -- This is only a notational repackaging of the pole data from the theorem statement.
  intro z
  simpa [rationalEval] using hpoles z

/-- Helper for Remark III.6-extra-7: the positive real axis is free of poles for the locally named
rational integrand. -/
lemma rationalEval_not_pole_of_nonneg_real
    (P Q : Polynomial ℂ)
    (hcut :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) (x : ℂ) < 0) :
    ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0 := by
  -- The no-pole-on-the-cut hypothesis is unchanged after introducing `rationalEval`.
  intro x hx
  simpa [rationalEval] using hcut x hx

/-- Helper for Remark III.6-extra-7: on the lower side of the shifted branch cut, `log (-z)`
approaches `log x - π i` at a positive real point `x`. -/
lemma tendsto_shiftedLog_boundary_from_below {x : ℝ} (hx : 0 < x) :
    Filter.Tendsto Complex.log (nhdsWithin (-(x : ℂ)) {z : ℂ | z.im < 0})
      (nhds ((Real.log x : ℂ) - Real.pi * Complex.I)) := by
  -- This is the standard one-sided boundary value of `Complex.log` on the negative real axis.
  simpa [Complex.norm_real, abs_of_pos hx, sub_eq_add_neg] using
    (Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
      (z := -(x : ℂ)) (by simpa using neg_lt_zero.mpr hx) (by simp))

/-- Helper for Remark III.6-extra-7: on the upper side of the shifted branch cut, `log (-z)`
approaches `log x + π i` at a positive real point `x`. -/
lemma tendsto_shiftedLog_boundary_from_above {x : ℝ} (hx : 0 < x) :
    Filter.Tendsto Complex.log (nhdsWithin (-(x : ℂ)) {z : ℂ | 0 ≤ z.im})
      (nhds ((Real.log x : ℂ) + Real.pi * Complex.I)) := by
  -- This is the companion one-sided boundary value on the other side of the slit.
  simpa [Complex.norm_real, abs_of_pos hx] using
    (Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
      (z := -(x : ℂ)) (by simpa using neg_lt_zero.mpr hx) (by simp))

/-- Helper for Remark III.6-extra-7: the positive-axis keyhole opening angle used to keep the two
boundary values of `Complex.log (-z)` distinct. -/
abbrev positiveAxisKeyholeAngle (R ε : ℝ) : ℝ :=
  Real.arctan (ε / R)

/-- Helper for Remark III.6-extra-7: the source-faithful keyhole contour for the shifted branch
`z ↦ Complex.log (-z)`. It runs down the upper lip of the positive-axis slit, once around the
small circle clockwise, back along the lower lip, and then around the large circle
anticlockwise. -/
def positiveAxisKeyhole (R ε : ℝ) :
    Path (circleMap 0 R (positiveAxisKeyholeAngle R ε))
      (circleMap 0 R (positiveAxisKeyholeAngle R ε)) :=
  let θ := positiveAxisKeyholeAngle R ε
  let upper : Path (circleMap 0 R θ) (circleMap 0 ε θ) :=
    Path.segment (circleMap 0 R θ) (circleMap 0 ε θ)
  let inner : Path (circleMap 0 ε θ) (circleMap 0 ε (-θ)) :=
    (Path.segment θ (-θ)).map (continuous_circleMap 0 ε)
  let lower : Path (circleMap 0 ε (-θ))
      (circleMap 0 R (-θ)) :=
    Path.segment (circleMap 0 ε (-θ)) (circleMap 0 R (-θ))
  let outer : Path (circleMap 0 R (-θ)) (circleMap 0 R θ) :=
    (Path.segment (-θ) θ).map (continuous_circleMap 0 R)
  ((upper.trans inner).trans lower).trans outer

/-- Helper for Remark III.6-extra-7: unfold the explicit upper lip, inner arc, lower lip, and
outer arc that make up `positiveAxisKeyhole`. -/
theorem positiveAxisKeyhole_def (R ε : ℝ) :
    positiveAxisKeyhole R ε =
      let θ := positiveAxisKeyholeAngle R ε
      let upper : Path (circleMap 0 R θ) (circleMap 0 ε θ) :=
        Path.segment (circleMap 0 R θ) (circleMap 0 ε θ)
      let inner : Path (circleMap 0 ε θ) (circleMap 0 ε (-θ)) :=
        (Path.segment θ (-θ)).map (continuous_circleMap 0 ε)
      let lower : Path (circleMap 0 ε (-θ))
          (circleMap 0 R (-θ)) :=
        Path.segment (circleMap 0 ε (-θ)) (circleMap 0 R (-θ))
      let outer : Path (circleMap 0 R (-θ)) (circleMap 0 R θ) :=
        (Path.segment (-θ) θ).map (continuous_circleMap 0 R)
      ((upper.trans inner).trans lower).trans outer := rfl

/-- Helper for Remark III.6-extra-7: on the first quarter-break interval, the explicit keyhole
path follows the upper slit lip with the affine reparametrization `t ↦ 8 t`. -/
lemma positive_axis_keyhole_eq_on_upper_lip (R ε : ℝ) :
    Set.EqOn (positiveAxisKeyhole R ε).extend
      (fun t ↦
        AffineMap.lineMap
          (circleMap 0 R (positiveAxisKeyholeAngle R ε))
          (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
          (8 * t))
      (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) := by
  intro t ht
  let θ := positiveAxisKeyholeAngle R ε
  let upper : Path (circleMap 0 R θ) (circleMap 0 ε θ) :=
    Path.segment (circleMap 0 R θ) (circleMap 0 ε θ)
  let inner : Path (circleMap 0 ε θ) (circleMap 0 ε (-θ)) :=
    (Path.segment θ (-θ)).map (continuous_circleMap 0 ε)
  let lower : Path (circleMap 0 ε (-θ))
      (circleMap 0 R (-θ)) :=
    Path.segment (circleMap 0 ε (-θ)) (circleMap 0 R (-θ))
  let outer : Path (circleMap 0 R (-θ)) (circleMap 0 R θ) :=
    (Path.segment (-θ) θ).map (continuous_circleMap 0 R)
  let γ₂ : Path (circleMap 0 R θ) (circleMap 0 R (-θ)) :=
    (upper.trans inner).trans lower
  -- Peel off the three concatenations until only the upper segment remains.
  have houter :
      (positiveAxisKeyhole R ε).extend t = γ₂.extend (2 * t) := by
    dsimp [positiveAxisKeyhole, θ, upper, inner, lower, outer, γ₂]
    exact Path.extend_trans_of_le_half
      (γ₁ := (upper.trans inner).trans lower) (γ₂ := outer) (by linarith [ht.2])
  have hmid :
      γ₂.extend (2 * t) = (upper.trans inner).extend (2 * (2 * t)) := by
    dsimp [γ₂]
    exact Path.extend_trans_of_le_half (γ₁ := upper.trans inner) (γ₂ := lower)
      (by linarith [ht.2])
  have hinner :
      (upper.trans inner).extend (2 * (2 * t)) = upper.extend (2 * (2 * (2 * t))) := by
    exact Path.extend_trans_of_le_half (γ₁ := upper) (γ₂ := inner) (by linarith [ht.2])
  have hI : 8 * t ∈ I := by
    constructor <;> linarith [ht.1, ht.2]
  rw [houter, hmid, hinner]
  -- Once the path is reduced to a single segment, use the standard segment-extension formula.
  calc
    upper.extend (2 * (2 * (2 * t)))
        = upper.extend (8 * t) := by
            congr 1
            ring
    _ = AffineMap.lineMap (circleMap 0 R θ) (circleMap 0 ε θ) (8 * t) := by
            simpa [upper] using Path.eqOn_extend_segment (circleMap 0 R θ) (circleMap 0 ε θ) hI

/-- Helper for Remark III.6-extra-7: on the second interval, the explicit keyhole path follows the
clockwise inner circle with the affine angle parameter `t ↦ 8 t - 1`. -/
lemma positive_axis_keyhole_eq_on_inner_arc (R ε : ℝ) :
    Set.EqOn (positiveAxisKeyhole R ε).extend
      (fun t ↦
        circleMap 0 ε
          (AffineMap.lineMap
            (positiveAxisKeyholeAngle R ε)
            (-positiveAxisKeyholeAngle R ε)
            (8 * t - 1)))
      (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) := by
  intro t ht
  let θ := positiveAxisKeyholeAngle R ε
  let upper : Path (circleMap 0 R θ) (circleMap 0 ε θ) :=
    Path.segment (circleMap 0 R θ) (circleMap 0 ε θ)
  let inner : Path (circleMap 0 ε θ) (circleMap 0 ε (-θ)) :=
    (Path.segment θ (-θ)).map (continuous_circleMap 0 ε)
  let lower : Path (circleMap 0 ε (-θ))
      (circleMap 0 R (-θ)) :=
    Path.segment (circleMap 0 ε (-θ)) (circleMap 0 R (-θ))
  let outer : Path (circleMap 0 R (-θ)) (circleMap 0 R θ) :=
    (Path.segment (-θ) θ).map (continuous_circleMap 0 R)
  let γ₂ : Path (circleMap 0 R θ) (circleMap 0 R (-θ)) :=
    (upper.trans inner).trans lower
  -- Peel off the outer concatenations, then switch to the second half of `upper.trans inner`.
  have houter :
      (positiveAxisKeyhole R ε).extend t = γ₂.extend (2 * t) := by
    dsimp [positiveAxisKeyhole, θ, upper, inner, lower, outer, γ₂]
    exact Path.extend_trans_of_le_half
      (γ₁ := (upper.trans inner).trans lower) (γ₂ := outer) (by linarith [ht.2])
  have hmid :
      γ₂.extend (2 * t) = (upper.trans inner).extend (2 * (2 * t)) := by
    dsimp [γ₂]
    exact Path.extend_trans_of_le_half (γ₁ := upper.trans inner) (γ₂ := lower)
      (by linarith [ht.2])
  have hinner :
      (upper.trans inner).extend (2 * (2 * t)) = inner.extend (2 * (2 * (2 * t)) - 1) := by
    exact Path.extend_trans_of_half_le (γ₁ := upper) (γ₂ := inner) (by linarith [ht.1])
  have hI : 8 * t - 1 ∈ I := by
    constructor <;> linarith [ht.1, ht.2]
  have hI' : 2 * (2 * (2 * t)) - 1 ∈ I := by
    constructor <;> linarith [ht.1, ht.2]
  rw [houter, hmid, hinner]
  -- Rewrite the mapped angular segment, then identify the inner parameter by the segment formula.
  calc
    inner.extend (2 * (2 * (2 * t)) - 1)
        = inner ⟨2 * (2 * (2 * t)) - 1, hI'⟩ := by
            rw [Path.extend_apply]
    _ = circleMap 0 ε
          ((Path.segment θ (-θ)) ⟨2 * (2 * (2 * t)) - 1, hI'⟩) := by
          simp [inner, Path.map_coe]
    _ = circleMap 0 ε ((Path.segment θ (-θ)).extend (2 * (2 * (2 * t)) - 1)) := by
          rw [Path.extend_apply]
    _ = circleMap 0 ε ((Path.segment θ (-θ)).extend (8 * t - 1)) := by
          congr 1
          ring
    _ = circleMap 0 ε (AffineMap.lineMap θ (-θ) (8 * t - 1)) := by
          exact congrArg (circleMap 0 ε) (Path.eqOn_extend_segment θ (-θ) hI)

/-- Helper for Remark III.6-extra-7: on the third interval, the explicit keyhole path follows the
lower slit lip with the affine reparametrization `t ↦ 4 t - 1`. -/
lemma positive_axis_keyhole_eq_on_lower_lip (R ε : ℝ) :
    Set.EqOn (positiveAxisKeyhole R ε).extend
      (fun t ↦
        AffineMap.lineMap
          (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
          (4 * t - 1))
      (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) := by
  intro t ht
  let θ := positiveAxisKeyholeAngle R ε
  let upper : Path (circleMap 0 R θ) (circleMap 0 ε θ) :=
    Path.segment (circleMap 0 R θ) (circleMap 0 ε θ)
  let inner : Path (circleMap 0 ε θ) (circleMap 0 ε (-θ)) :=
    (Path.segment θ (-θ)).map (continuous_circleMap 0 ε)
  let lower : Path (circleMap 0 ε (-θ))
      (circleMap 0 R (-θ)) :=
    Path.segment (circleMap 0 ε (-θ)) (circleMap 0 R (-θ))
  let outer : Path (circleMap 0 R (-θ)) (circleMap 0 R θ) :=
    (Path.segment (-θ) θ).map (continuous_circleMap 0 R)
  let γ₂ : Path (circleMap 0 R θ) (circleMap 0 R (-θ)) :=
    (upper.trans inner).trans lower
  -- After the first break point of the outer concatenation, the motion is already on the lower lip.
  have houter :
      (positiveAxisKeyhole R ε).extend t = γ₂.extend (2 * t) := by
    dsimp [positiveAxisKeyhole, θ, upper, inner, lower, outer, γ₂]
    exact Path.extend_trans_of_le_half
      (γ₁ := (upper.trans inner).trans lower) (γ₂ := outer) ht.2
  have hmid :
      γ₂.extend (2 * t) = lower.extend (2 * (2 * t) - 1) := by
    dsimp [γ₂]
    exact Path.extend_trans_of_half_le (γ₁ := upper.trans inner) (γ₂ := lower)
      (by linarith [ht.1])
  have hI : 4 * t - 1 ∈ I := by
    constructor <;> linarith [ht.1, ht.2]
  rw [houter, hmid]
  -- Reduce again to the explicit segment-extension formula.
  calc
    lower.extend (2 * (2 * t) - 1)
        = lower.extend (4 * t - 1) := by
              congr 1
              ring
    _ = AffineMap.lineMap
            (circleMap 0 ε (-θ))
            (circleMap 0 R (-θ))
            (4 * t - 1) := by
              simpa [lower] using
                Path.eqOn_extend_segment
                  (circleMap 0 ε (-θ))
                  (circleMap 0 R (-θ))
                  hI

/-- Helper for Remark III.6-extra-7: on the final interval, the explicit keyhole path follows the
outer circle with the affine angle parameter `t ↦ 2 t - 1`. -/
lemma positive_axis_keyhole_eq_on_outer_arc (R ε : ℝ) :
    Set.EqOn (positiveAxisKeyhole R ε).extend
      (fun t ↦
        circleMap 0 R
          (AffineMap.lineMap
            (-positiveAxisKeyholeAngle R ε)
            (positiveAxisKeyholeAngle R ε)
            (2 * t - 1)))
      (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) := by
  intro t ht
  let θ := positiveAxisKeyholeAngle R ε
  let upper : Path (circleMap 0 R θ) (circleMap 0 ε θ) :=
    Path.segment (circleMap 0 R θ) (circleMap 0 ε θ)
  let inner : Path (circleMap 0 ε θ) (circleMap 0 ε (-θ)) :=
    (Path.segment θ (-θ)).map (continuous_circleMap 0 ε)
  let lower : Path (circleMap 0 ε (-θ))
      (circleMap 0 R (-θ)) :=
    Path.segment (circleMap 0 ε (-θ)) (circleMap 0 R (-θ))
  let outer : Path (circleMap 0 R (-θ)) (circleMap 0 R θ) :=
    (Path.segment (-θ) θ).map (continuous_circleMap 0 R)
  -- Route correction: isolate the outer arc directly from the last concatenation instead of
  -- forcing later chart proofs to keep unfolding the whole nested keyhole path.
  have houter :
      (positiveAxisKeyhole R ε).extend t = outer.extend (2 * t - 1) := by
    dsimp [positiveAxisKeyhole, θ, upper, inner, lower, outer]
    exact Path.extend_trans_of_half_le
      (γ₁ := (upper.trans inner).trans lower) (γ₂ := outer) ht.1
  have hI : 2 * t - 1 ∈ I := by
    constructor <;> linarith [ht.1, ht.2]
  rw [houter]
  -- The mapped angular segment is again reduced to the standard segment-extension formula.
  calc
    outer.extend (2 * t - 1)
        = outer ⟨2 * t - 1, hI⟩ := by
            rw [Path.extend_apply]
    _ = circleMap 0 R ((Path.segment (-θ) θ) ⟨2 * t - 1, hI⟩) := by
          simp [outer, Path.map_coe]
    _ = circleMap 0 R ((Path.segment (-θ) θ).extend (2 * t - 1)) := by
          rw [Path.extend_apply]
    _ = circleMap 0 R (AffineMap.lineMap (-θ) θ (2 * t - 1)) := by
          exact congrArg (circleMap 0 R) (Path.eqOn_extend_segment (-θ) θ hI)

/-- Helper for Remark III.6-extra-7: on the first interval, the real-plane closed-curve model is
the upper slit lip written in explicit coordinates. -/
lemma positive_axis_keyhole_realCurve_eq_on_upper_lip (R ε : ℝ) :
    Set.EqOn ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
      (fun t ↦
        Complex.equivRealProd
          (AffineMap.lineMap
            (circleMap 0 R (positiveAxisKeyholeAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
            (8 * t)))
      (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) := by
  intro t ht
  -- Pass from the complex-valued path formula to the real-plane parametrization by `equivRealProd`.
  simpa [ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
    congrArg Complex.equivRealProd (positive_axis_keyhole_eq_on_upper_lip R ε ht)

/-- Helper for Remark III.6-extra-7: on the second interval, the real-plane closed-curve model is
the clockwise inner circular arc written in explicit coordinates. -/
lemma positive_axis_keyhole_realCurve_eq_on_inner_arc (R ε : ℝ) :
    Set.EqOn ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
      (fun t ↦
        Complex.equivRealProd
          (circleMap 0 ε
            (AffineMap.lineMap
              (positiveAxisKeyholeAngle R ε)
              (-positiveAxisKeyholeAngle R ε)
              (8 * t - 1))))
      (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) := by
  intro t ht
  -- The real-curve owner is just the complex formula viewed in `Plane`.
  simpa [ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
    congrArg Complex.equivRealProd (positive_axis_keyhole_eq_on_inner_arc R ε ht)

/-- Helper for Remark III.6-extra-7: on the third interval, the real-plane closed-curve model is
the lower slit lip written in explicit coordinates. -/
lemma positive_axis_keyhole_realCurve_eq_on_lower_lip (R ε : ℝ) :
    Set.EqOn ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
      (fun t ↦
        Complex.equivRealProd
          (AffineMap.lineMap
            (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
            (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
            (4 * t - 1)))
      (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) := by
  intro t ht
  -- The lower lip uses the same `equivRealProd` bridge from the complex path formula.
  simpa [ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
    congrArg Complex.equivRealProd (positive_axis_keyhole_eq_on_lower_lip R ε ht)

/-- Helper for Remark III.6-extra-7: on the final interval, the real-plane closed-curve model is
the outer circular arc written in explicit coordinates. -/
lemma positive_axis_keyhole_realCurve_eq_on_outer_arc (R ε : ℝ) :
    Set.EqOn ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
      (fun t ↦
        Complex.equivRealProd
          (circleMap 0 R
            (AffineMap.lineMap
              (-positiveAxisKeyholeAngle R ε)
              (positiveAxisKeyholeAngle R ε)
              (2 * t - 1))))
      (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) := by
  intro t ht
  -- The final branch is again the complex outer-arc formula viewed in `Plane`.
  simpa [ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
    congrArg Complex.equivRealProd (positive_axis_keyhole_eq_on_outer_arc R ε ht)

/-- Helper for Remark III.6-extra-7: package the four closed-interval formulas for the real-plane
parametrization of the positive-axis keyhole contour. These closed-interval owners are stronger
than the open-interval adapters needed later for regular-point arguments. -/
lemma positive_axis_keyhole_realCurve_eqOn_piece_intervals (R ε : ℝ) :
    Set.EqOn ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
        (fun t ↦
          Complex.equivRealProd
            (AffineMap.lineMap
              (circleMap 0 R (positiveAxisKeyholeAngle R ε))
              (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
              (8 * t)))
        (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) ∧
      Set.EqOn ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
        (fun t ↦
          Complex.equivRealProd
            (circleMap 0 ε
              (AffineMap.lineMap
                (positiveAxisKeyholeAngle R ε)
                (-positiveAxisKeyholeAngle R ε)
                (8 * t - 1))))
        (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) ∧
      Set.EqOn ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
        (fun t ↦
          Complex.equivRealProd
            (AffineMap.lineMap
              (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
              (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
              (4 * t - 1)))
        (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) ∧
      Set.EqOn ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
        (fun t ↦
          Complex.equivRealProd
            (circleMap 0 R
              (AffineMap.lineMap
                (-positiveAxisKeyholeAngle R ε)
                (positiveAxisKeyholeAngle R ε)
                (2 * t - 1))))
        (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) := by
  -- Bundle the four branch formulas so later geometric arguments can case-split once and then
  -- work with concrete branch models instead of the full nested concatenation.
  refine ⟨positive_axis_keyhole_realCurve_eq_on_upper_lip R ε,
    positive_axis_keyhole_realCurve_eq_on_inner_arc R ε,
    positive_axis_keyhole_realCurve_eq_on_lower_lip R ε,
    positive_axis_keyhole_realCurve_eq_on_outer_arc R ε⟩

/-- Helper for Remark III.6-extra-7: every parameter in `I` lies either on one of the four open
branches of the positive-axis keyhole contour or at one of the five distinguished breakpoints
`0`, `1/8`, `1/4`, `1/2`, `1`. This is the stable interval splitter for the later boundary-owner
arguments. -/
lemma positive_axis_keyhole_parameter_cases (t : I) :
    t.1 = 0 ∨
      t.1 ∈ Set.Ioo (0 : ℝ) (1 / 8) ∨
      t.1 = 1 / 8 ∨
      t.1 ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4) ∨
      t.1 = 1 / 4 ∨
      t.1 ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∨
      t.1 = 1 / 2 ∨
      t.1 ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ) ∨
      t.1 = 1 := by
  -- Split first into the global endpoints `0`, `1`, or the interior interval `(0, 1)`.
  rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc t.2 with ht0 | ht1 | ht
  · exact Or.inl ht0
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ht1
  · by_cases h18 : t.1 < 1 / 8
    · exact Or.inr <| Or.inl ⟨ht.1, h18⟩
    · have h18' : 1 / 8 ≤ t.1 := le_of_not_gt h18
      by_cases h14 : t.1 < 1 / 4
      · -- The next split isolates `1/8` from the open inner-circle interval.
        rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc ⟨h18', le_of_lt h14⟩ with hEq | hEq | hmem
        · exact Or.inr <| Or.inr <| Or.inl hEq
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hEq
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inl hmem
      · have h14' : 1 / 4 ≤ t.1 := le_of_not_gt h14
        by_cases h12 : t.1 < 1 / 2
        · -- The third split isolates `1/4` from the open lower-lip interval.
          rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc ⟨h14', le_of_lt h12⟩ with
              hEq | hEq | hmem
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hEq
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hEq
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hmem
        · have h12' : 1 / 2 ≤ t.1 := le_of_not_gt h12
          -- The final split isolates `1/2` from the open outer-circle interval and the endpoint
          -- `1`.
          rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc ⟨h12', ht.2.le⟩ with
              hEq | hEq | hmem
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hEq
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr hEq
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hmem

/-- Helper for Remark III.6-extra-7: the five distinguished parameters `0`, `1/8`, `1/4`, `1/2`,
and `1` hit the four geometric corners of the positive-axis keyhole contour in source order. This
packages the endpoint evaluations before the later branchwise injectivity arguments. -/
lemma positive_axis_keyhole_breakpoint_values (R ε : ℝ) :
    positiveAxisKeyhole R ε (0 : I) =
        circleMap 0 R (positiveAxisKeyholeAngle R ε) ∧
      positiveAxisKeyhole R ε (⟨(1 / 8 : ℝ), by norm_num⟩ : I) =
        circleMap 0 ε (positiveAxisKeyholeAngle R ε) ∧
      positiveAxisKeyhole R ε (⟨(1 / 4 : ℝ), by norm_num⟩ : I) =
        circleMap 0 ε (-positiveAxisKeyholeAngle R ε) ∧
      positiveAxisKeyhole R ε (⟨(1 / 2 : ℝ), by norm_num⟩ : I) =
        circleMap 0 R (-positiveAxisKeyholeAngle R ε) ∧
      positiveAxisKeyhole R ε (1 : I) =
        circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
  have h0_segment :
      (positiveAxisKeyhole R ε).extend 0 =
        AffineMap.lineMap
          (circleMap 0 R (positiveAxisKeyholeAngle R ε))
          (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
          (8 * (0 : ℝ)) := by
    -- Evaluate the upper-lip branch at the initial parameter.
    simpa using
      (positive_axis_keyhole_eq_on_upper_lip R ε
        (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 8 : ℝ)))
  have h18_segment :
      (positiveAxisKeyhole R ε).extend (1 / 8 : ℝ) =
        AffineMap.lineMap
          (circleMap 0 R (positiveAxisKeyholeAngle R ε))
          (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
          (8 * (1 / 8 : ℝ)) := by
    -- The endpoint of the upper lip is the first contour corner.
    simpa using
      (positive_axis_keyhole_eq_on_upper_lip R ε
        (by norm_num : (1 / 8 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 8 : ℝ)))
  have h14_arc :
      (positiveAxisKeyhole R ε).extend (1 / 4 : ℝ) =
        circleMap 0 ε
          (AffineMap.lineMap
            (positiveAxisKeyholeAngle R ε)
            (-positiveAxisKeyholeAngle R ε)
            (8 * (1 / 4 : ℝ) - 1)) := by
    -- Evaluating the inner arc at its terminal parameter reaches the lower inner corner.
    simpa using
      (positive_axis_keyhole_eq_on_inner_arc R ε
        (by norm_num : (1 / 4 : ℝ) ∈ Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)))
  have h12_segment :
      (positiveAxisKeyhole R ε).extend (1 / 2 : ℝ) =
        AffineMap.lineMap
          (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
          (4 * (1 / 2 : ℝ) - 1) := by
    -- The lower lip ends at the outer lower corner.
    simpa using
      (positive_axis_keyhole_eq_on_lower_lip R ε
        (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)))
  have h1_arc :
      (positiveAxisKeyhole R ε).extend (1 : ℝ) =
        circleMap 0 R
          (AffineMap.lineMap
            (-positiveAxisKeyholeAngle R ε)
            (positiveAxisKeyholeAngle R ε)
            (2 * (1 : ℝ) - 1)) := by
    -- The outer arc closes the contour back to the starting point.
    simpa using
      (positive_axis_keyhole_eq_on_outer_arc R ε
        (by norm_num : (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) (1 : ℝ)))
  have h0_path :
      positiveAxisKeyhole R ε (0 : I) =
        AffineMap.lineMap
          (circleMap 0 R (positiveAxisKeyholeAngle R ε))
          (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
          (8 * (0 : ℝ)) := by
    -- Convert the endpoint evaluation from `extend` back to the subtype parameter.
    exact
      (Path.extend_apply (positiveAxisKeyhole R ε)
        (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)).symm.trans h0_segment
  have h18_path :
      positiveAxisKeyhole R ε (⟨(1 / 8 : ℝ), by norm_num⟩ : I) =
        AffineMap.lineMap
          (circleMap 0 R (positiveAxisKeyholeAngle R ε))
          (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
          (8 * (1 / 8 : ℝ)) := by
    -- The same bridge is needed at the first interior breakpoint.
    exact
      (Path.extend_apply (positiveAxisKeyhole R ε)
        (by norm_num : (1 / 8 : ℝ) ∈ Set.Icc (0 : ℝ) 1)).symm.trans h18_segment
  have h14_path :
      positiveAxisKeyhole R ε (⟨(1 / 4 : ℝ), by norm_num⟩ : I) =
        circleMap 0 ε
          (AffineMap.lineMap
            (positiveAxisKeyholeAngle R ε)
            (-positiveAxisKeyholeAngle R ε)
            (8 * (1 / 4 : ℝ) - 1)) := by
    -- Likewise for the lower endpoint of the inner circular arc.
    exact
      (Path.extend_apply (positiveAxisKeyhole R ε)
        (by norm_num : (1 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1)).symm.trans h14_arc
  have h12_path :
      positiveAxisKeyhole R ε (⟨(1 / 2 : ℝ), by norm_num⟩ : I) =
        AffineMap.lineMap
          (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
          (4 * (1 / 2 : ℝ) - 1) := by
    -- And again at the endpoint of the lower slit lip.
    exact
      (Path.extend_apply (positiveAxisKeyhole R ε)
        (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)).symm.trans h12_segment
  have h1_path :
      positiveAxisKeyhole R ε (1 : I) =
        circleMap 0 R
          (AffineMap.lineMap
            (-positiveAxisKeyholeAngle R ε)
            (positiveAxisKeyholeAngle R ε)
            (2 * (1 : ℝ) - 1)) := by
    -- The final bridge closes the loop at the path endpoint.
    exact
      (Path.extend_apply (positiveAxisKeyhole R ε)
        (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)).symm.trans h1_arc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- The affine upper-lip segment starts at the outer upper corner.
    simpa [AffineMap.lineMap_apply_zero] using h0_path
  · -- The affine upper-lip segment ends at the inner upper corner.
    simpa [AffineMap.lineMap_apply_one] using h18_path
  · -- The clockwise inner arc ends at angle `-2π - θ`.
    have h14_param : (8 * (1 / 4 : ℝ) - 1) = 1 := by norm_num
    rw [h14_param, AffineMap.lineMap_apply_one] at h14_path
    exact h14_path
  · -- The affine lower-lip segment ends at the outer lower corner.
    have h12_param : (4 * (1 / 2 : ℝ) - 1) = 1 := by norm_num
    rw [h12_param, AffineMap.lineMap_apply_one] at h12_path
    exact h12_path
  · -- The outer arc returns to the initial angle `θ`.
    have h1_param : (2 * (1 : ℝ) - 1) = 1 := by norm_num
    rw [h1_param, AffineMap.lineMap_apply_one] at h1_path
    exact h1_path

/-- Helper for Remark III.6-extra-7: affine interpolation between two points on the same ray only
changes the radius, so the angular coordinate stays fixed. This is the transport-stable
normalization used when a branch proof should reason by radius and angle rather than by raw
complex affine formulas. -/
lemma positiveAxisKeyhole_lineMap_circleMap_same_angle (ρ₀ ρ₁ φ c : ℝ) :
    AffineMap.lineMap (circleMap 0 ρ₀ φ) (circleMap 0 ρ₁ φ) c =
      circleMap 0 (AffineMap.lineMap ρ₀ ρ₁ c) φ := by
  -- Compare real and imaginary parts separately; on a fixed ray, affine interpolation is purely
  -- radial.
  rw [Complex.ext_iff]
  constructor <;>
    simp [circleMap_zero_re, circleMap_zero_im, AffineMap.lineMap_apply_module, smul_eq_mul,
      add_mul] <;>
    ring

/-- Helper for Remark III.6-extra-7: the opening angle `θ = arctan (ε / R)` of the positive-axis
keyhole contour lies in `(0, π / 2)` whenever `0 < ε < R`. -/
lemma positiveAxisKeyhole_angle_bounds {R ε : ℝ}
    (hε : 0 < ε) (hεR : ε < R) :
    0 < positiveAxisKeyholeAngle R ε ∧ positiveAxisKeyholeAngle R ε < Real.pi / 2 := by
  have hR : 0 < R := lt_trans hε hεR
  -- The keyhole opening is acute because the slope `ε / R` is positive.
  constructor
  · simpa [positiveAxisKeyholeAngle] using Real.arctan_pos.mpr (div_pos hε hR)
  · simpa [positiveAxisKeyholeAngle] using Real.arctan_lt_pi_div_two (ε / R)

/-- Helper for Remark III.6-extra-7: an interior point of the upper slit lip is a point on the
upper boundary ray with radius strictly between `ε` and `R`. -/
lemma positive_axis_keyhole_eq_upper_lip_circleMap_of_mem_Ioo
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t : I}
    (ht : t.1 ∈ Set.Ioo (0 : ℝ) (1 / 8)) :
    ∃ ρ ∈ Set.Ioo ε R,
      positiveAxisKeyhole R ε t =
        circleMap 0 ρ (positiveAxisKeyholeAngle R ε) := by
  let ρ : ℝ := AffineMap.lineMap R ε (8 * (t : ℝ))
  have hparam : 8 * (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hρopen : ρ ∈ Set.Ioo ε R := by
    have hseg : ρ ∈ openSegment ℝ R ε := by
      simpa [ρ] using lineMap_mem_openSegment (𝕜 := ℝ) R ε hparam
    have hRe : (R : ℝ) ≠ ε := by linarith
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hRe] at hseg
    simpa [ρ, min_eq_right (le_of_lt hεR), max_eq_left (le_of_lt hεR)] using hseg
  refine ⟨ρ, hρopen, ?_⟩
  -- Rewrite the open upper branch using the radial parameter supplied by `lineMap`.
  calc
    positiveAxisKeyhole R ε t =
        AffineMap.lineMap
          (circleMap 0 R (positiveAxisKeyholeAngle R ε))
          (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
          (8 * (t : ℝ)) := by
            exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
              positive_axis_keyhole_eq_on_upper_lip R ε (Set.Ioo_subset_Icc_self ht)
    _ = circleMap 0 ρ (positiveAxisKeyholeAngle R ε) := by
          rw [positiveAxisKeyhole_lineMap_circleMap_same_angle]

/-- Helper for Remark III.6-extra-7: an interior point of the inner arc stays on the circle of
radius `ε` with angle strictly between the two slit-boundary angles. -/
lemma positive_axis_keyhole_eq_inner_arc_circleMap_of_mem_Ioo
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t : I}
    (ht : t.1 ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4)) :
    ∃ α ∈ Set.Ioo (-positiveAxisKeyholeAngle R ε) (positiveAxisKeyholeAngle R ε),
      positiveAxisKeyhole R ε t = circleMap 0 ε α := by
  let α : ℝ :=
    AffineMap.lineMap
      (positiveAxisKeyholeAngle R ε)
      (-positiveAxisKeyholeAngle R ε)
      (8 * (t : ℝ) - 1)
  have hθ : 0 < positiveAxisKeyholeAngle R ε ∧ positiveAxisKeyholeAngle R ε < Real.pi / 2 :=
    positiveAxisKeyhole_angle_bounds (R := R) (ε := ε) hε hεR
  have hparam : 8 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hαopen :
      α ∈ Set.Ioo (-positiveAxisKeyholeAngle R ε) (positiveAxisKeyholeAngle R ε) := by
    have hseg :
        α ∈ openSegment ℝ
          (positiveAxisKeyholeAngle R ε)
          (-positiveAxisKeyholeAngle R ε) := by
      simpa [α] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (positiveAxisKeyholeAngle R ε)
          (-positiveAxisKeyholeAngle R ε)
          hparam
    have hneq :
        positiveAxisKeyholeAngle R ε ≠ -positiveAxisKeyholeAngle R ε := by
      nlinarith [hθ.1, Real.pi_pos]
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hneq] at hseg
    have horder :
        (-positiveAxisKeyholeAngle R ε) < positiveAxisKeyholeAngle R ε := by
      nlinarith [hθ.1, Real.pi_pos]
    have horder_le :
        (-positiveAxisKeyholeAngle R ε) ≤ positiveAxisKeyholeAngle R ε :=
      le_of_lt horder
    have hleft : (-positiveAxisKeyholeAngle R ε) < α := by
      simpa [min_eq_right horder_le] using hseg.left
    have hright : α < positiveAxisKeyholeAngle R ε := by
      simpa [max_eq_left horder_le] using hseg.right
    refine ⟨?_, hright⟩
    simpa using hleft
  refine ⟨α, hαopen, ?_⟩
  -- Reduce the open inner branch to its explicit angular parameter.
  exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
    positive_axis_keyhole_eq_on_inner_arc R ε (Set.Ioo_subset_Icc_self ht)

/-- Helper for Remark III.6-extra-7: an interior point of the lower slit lip is a point on the
lower boundary ray with radius strictly between `ε` and `R`. -/
lemma positive_axis_keyhole_eq_lower_lip_circleMap_of_mem_Ioo
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t : I}
    (ht : t.1 ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)) :
    ∃ ρ ∈ Set.Ioo ε R,
      positiveAxisKeyhole R ε t =
        circleMap 0 ρ (-positiveAxisKeyholeAngle R ε) := by
  let ρ : ℝ := AffineMap.lineMap ε R (4 * (t : ℝ) - 1)
  have hparam : 4 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hρopen : ρ ∈ Set.Ioo ε R := by
    have hseg : ρ ∈ openSegment ℝ ε R := by
      simpa [ρ] using lineMap_mem_openSegment (𝕜 := ℝ) ε R hparam
    have hRe : (ε : ℝ) ≠ R := by linarith
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hRe] at hseg
    simpa [ρ, min_eq_left (le_of_lt hεR), max_eq_right (le_of_lt hεR)] using hseg
  refine ⟨ρ, hρopen, ?_⟩
  -- Rewrite the open lower branch using the corresponding radial parameter.
  calc
    positiveAxisKeyhole R ε t =
        AffineMap.lineMap
          (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
          (4 * (t : ℝ) - 1) := by
            exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
              positive_axis_keyhole_eq_on_lower_lip R ε (Set.Ioo_subset_Icc_self ht)
    _ = circleMap 0 ρ (-positiveAxisKeyholeAngle R ε) := by
          rw [positiveAxisKeyhole_lineMap_circleMap_same_angle]

/-- Helper for Remark III.6-extra-7: an interior point of the outer arc stays on the circle of
radius `R` with angle strictly between the two slit-boundary angles. -/
lemma positive_axis_keyhole_eq_outer_arc_circleMap_of_mem_Ioo
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t : I}
    (ht : t.1 ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ)) :
    ∃ α ∈ Set.Ioo (-positiveAxisKeyholeAngle R ε) (positiveAxisKeyholeAngle R ε),
      positiveAxisKeyhole R ε t = circleMap 0 R α := by
  let α : ℝ :=
    AffineMap.lineMap
      (-positiveAxisKeyholeAngle R ε)
      (positiveAxisKeyholeAngle R ε)
      (2 * (t : ℝ) - 1)
  have hθ : 0 < positiveAxisKeyholeAngle R ε ∧ positiveAxisKeyholeAngle R ε < Real.pi / 2 :=
    positiveAxisKeyhole_angle_bounds (R := R) (ε := ε) hε hεR
  have hparam : 2 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hαopen :
      α ∈ Set.Ioo (-positiveAxisKeyholeAngle R ε) (positiveAxisKeyholeAngle R ε) := by
    have hseg :
        α ∈ openSegment ℝ
          (-positiveAxisKeyholeAngle R ε)
          (positiveAxisKeyholeAngle R ε) := by
      simpa [α] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (-positiveAxisKeyholeAngle R ε)
          (positiveAxisKeyholeAngle R ε)
          hparam
    have hneq :
        -positiveAxisKeyholeAngle R ε ≠ positiveAxisKeyholeAngle R ε := by
      nlinarith [hθ.1, Real.pi_pos]
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hneq] at hseg
    have horder :
        (-positiveAxisKeyholeAngle R ε) < positiveAxisKeyholeAngle R ε := by
      nlinarith [hθ.1, Real.pi_pos]
    have horder_le :
        (-positiveAxisKeyholeAngle R ε) ≤ positiveAxisKeyholeAngle R ε :=
      le_of_lt horder
    have hleft : (-positiveAxisKeyholeAngle R ε) < α := by
      simpa [min_eq_left horder_le] using hseg.left
    have hright : α < positiveAxisKeyholeAngle R ε := by
      simpa [max_eq_right horder_le] using hseg.right
    refine ⟨?_, hright⟩
    simpa using hleft
  refine ⟨α, hαopen, ?_⟩
  -- Reduce the open outer branch to its explicit angular parameter.
  exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
    positive_axis_keyhole_eq_on_outer_arc R ε (Set.Ioo_subset_Icc_self ht)

/-- Helper for Remark III.6-extra-7: after correcting the source-facing keyhole contour, the inner
arc runs only through the angle window from `θ` to `-θ`. This records the non-overwinding geometry
needed by the simple-loop/oriented-boundary package. -/
lemma positiveAxisKeyhole_inner_arc_angle_window
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    ∀ {t : I}, t.1 ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4) →
      ∃ α ∈ Set.Ioo (-positiveAxisKeyholeAngle R ε) (positiveAxisKeyholeAngle R ε),
        positiveAxisKeyhole R ε t = circleMap 0 ε α := by
  intro t ht
  exact positive_axis_keyhole_eq_inner_arc_circleMap_of_mem_Ioo R ε hε hεR ht

/-- Helper for Remark III.6-extra-7: the first keyhole breakpoint is a genuine corner where the
upper slit lip meets the clockwise inner arc, so the real-plane parametrization is not
differentiable there within `[0, 1]`. -/
lemma positive_axis_keyhole_not_differentiable_at_one_eighth
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    ¬ DifferentiableWithinAt ℝ ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (1 / 8 : ℝ) := by
  -- Route correction: compare the upper-lip and inner-arc tangent vectors on their closed branch
  -- intervals, then use uniqueness of within-derivatives at the shared breakpoint.
  intro hdiff
  let θ : ℝ := positiveAxisKeyholeAngle R ε
  let γ : ℝ → ℂ := (positiveAxisKeyhole R ε).extend
  let d : ℂ := derivWithin γ (Set.Icc (0 : ℝ) 1) (1 / 8 : ℝ)
  let upper : ℝ → ℂ := fun t ↦
    AffineMap.lineMap (circleMap 0 R θ) (circleMap 0 ε θ) (8 * t)
  let inner : ℝ → ℂ := fun t ↦
    circleMap 0 ε (AffineMap.lineMap θ (-θ) (8 * t - 1))
  have hγdiff : DifferentiableWithinAt ℝ γ (Set.Icc (0 : ℝ) 1) (1 / 8 : ℝ) := by
    -- Undo the `Complex.equivRealProd` wrapper so the tangent comparison happens in `ℂ`.
    simpa [γ, ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
      (Complex.equivRealProdCLM.comp_differentiableWithinAt_iff.mp hdiff)
  have hmain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) 1) (1 / 8 : ℝ) := by
    simpa [d, γ] using hγdiff.hasDerivWithinAt
  have hupperMain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) (1 / 8 : ℝ) := by
    -- Restrict the ambient within-derivative to the upper-lip branch interval.
    apply hmain.mono
    intro t ht
    constructor
    · exact ht.1
    · linarith [ht.2]
  have hinnerMain : HasDerivWithinAt γ d (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 8 : ℝ) := by
    -- Restrict the same ambient derivative to the inner-arc branch interval.
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hupperγ :
      HasDerivWithinAt γ ((8 : ℝ) • (circleMap 0 ε θ - circleMap 0 R θ))
        (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) (1 / 8 : ℝ) := by
    -- Differentiate the affine upper-lip model and transfer it back to the explicit keyhole.
    have hmodel :
        HasDerivAt upper ((8 : ℝ) • (circleMap 0 ε θ - circleMap 0 R θ)) (1 / 8 : ℝ) := by
      have hmodel' :
          HasDerivAt
            (fun t : ℝ ↦ AffineMap.lineMap (circleMap 0 R θ) (circleMap 0 ε θ) (t * 8))
            ((8 : ℝ) • (circleMap 0 ε θ - circleMap 0 R θ)) (1 / 8 : ℝ) := by
        simpa [smul_eq_mul, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
          (AffineMap.hasDerivAt_lineMap
            (a := circleMap 0 R θ) (b := circleMap 0 ε θ) (x := (1 / 8 : ℝ) * 8)).scomp
            (1 / 8 : ℝ) ((hasDerivAt_id (1 / 8 : ℝ)).mul_const 8)
      simpa [upper, mul_comm] using hmodel'
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, upper] using positive_axis_keyhole_eq_on_upper_lip R ε ht)
      (by constructor <;> norm_num)
  have hinnerγ :
      HasDerivWithinAt γ
        (((8 * ((-θ) - θ)) : ℝ) • (circleMap 0 ε θ * Complex.I))
        (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 8 : ℝ) := by
    -- Differentiate the angular affine parameter first, then the clockwise inner circle.
    have hparam :
        HasDerivAt (fun t : ℝ ↦ AffineMap.lineMap θ (-θ) (8 * t - 1))
          (8 * ((-θ) - θ)) (1 / 8 : ℝ) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul, two_mul,
        mul_assoc, mul_left_comm, mul_comm] using
        (AffineMap.hasDerivAt_lineMap
          (a := θ) (b := -θ) (x := (8 : ℝ) * (1 / 8 : ℝ) - 1)).comp
          (1 / 8 : ℝ) (((hasDerivAt_id (1 / 8 : ℝ)).const_mul 8).sub_const 1)
    have hmodel :
        HasDerivAt inner
          (((8 * ((-θ) - θ)) : ℝ) • (circleMap 0 ε θ * Complex.I))
          (1 / 8 : ℝ) := by
      simpa [inner, smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add,
        add_mul, two_mul, mul_assoc, mul_left_comm, mul_comm] using
        (hasDerivAt_circleMap 0 ε
          (AffineMap.lineMap θ (-θ) ((8 : ℝ) * (1 / 8 : ℝ) - 1))).scomp
          (1 / 8 : ℝ) hparam
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, inner] using positive_axis_keyhole_eq_on_inner_arc R ε ht)
      (by constructor <;> norm_num)
  have hupperUD :
      UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) (1 / 8 : ℝ) :=
    (uniqueDiffOn_Icc (show (0 : ℝ) < 1 / 8 by norm_num)).uniqueDiffWithinAt
      (by constructor <;> norm_num)
  have hinnerUD :
      UniqueDiffWithinAt ℝ (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 8 : ℝ) :=
    (uniqueDiffOn_Icc (show (1 / 8 : ℝ) < 1 / 4 by norm_num)).uniqueDiffWithinAt
      (by constructor <;> norm_num)
  have hcompare :
      ((8 : ℝ) • (circleMap 0 ε θ - circleMap 0 R θ)) =
        (((8 * ((-θ) - θ)) : ℝ) • (circleMap 0 ε θ * Complex.I)) := by
    -- Uniqueness of within-derivatives on the two closed branch intervals forces the two tangents
    -- at the breakpoint to agree.
    calc
      ((8 : ℝ) • (circleMap 0 ε θ - circleMap 0 R θ))
          = derivWithin γ (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) (1 / 8 : ℝ) := by
              symm
              exact hupperγ.derivWithin hupperUD
      _ = d := hupperMain.derivWithin hupperUD
      _ = derivWithin γ (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 8 : ℝ) := by
            symm
            exact hinnerMain.derivWithin hinnerUD
      _ =
          (((8 * ((-θ) - θ)) : ℝ) • (circleMap 0 ε θ * Complex.I)) :=
            hinnerγ.derivWithin hinnerUD
  have hR : 0 < R := lt_trans hε hεR
  have hθ_pos : 0 < θ := by
    simpa [θ, positiveAxisKeyholeAngle] using
      (Real.arctan_pos.mpr (div_pos hε hR))
  have hupper_re_neg :
      ((((8 : ℝ) • (circleMap 0 ε θ - circleMap 0 R θ)) : ℂ)).re < 0 := by
    have hcos_pos : 0 < Real.cos θ := by
      simpa [θ, positiveAxisKeyholeAngle] using Real.cos_arctan_pos (ε / R)
    have hdiff_neg : ε - R < 0 := sub_neg.mpr hεR
    have hcore : (ε - R) * Real.cos θ < 0 := mul_neg_of_neg_of_pos hdiff_neg hcos_pos
    rw [show ((((8 : ℝ) • (circleMap 0 ε θ - circleMap 0 R θ)) : ℂ)).re =
        8 * ((ε - R) * Real.cos θ) by
          simp [θ, circleMap_zero_re, sub_eq_add_neg, mul_left_comm]
          ring_nf]
    exact mul_neg_of_pos_of_neg (by norm_num) hcore
  have hinner_re_pos :
      0 <
        ((((8 * ((-θ) - θ)) : ℝ) • (circleMap 0 ε θ * Complex.I)) : ℂ).re := by
    have hfactor_neg : 8 * ((-θ) - θ) < 0 := by
      nlinarith [Real.pi_pos, hθ_pos]
    have hsin_pos : 0 < Real.sin θ := by
      simpa [θ, positiveAxisKeyholeAngle] using
        (Real.sin_arctan_pos.mpr (div_pos hε hR))
    have him_pos : 0 < (circleMap 0 ε θ).im := by
      rw [circleMap_zero_im]
      exact mul_pos hε hsin_pos
    have hneg_im : -(circleMap 0 ε θ).im < 0 := by
      linarith
    rw [show
      ((((8 * ((-θ) - θ)) : ℝ) • (circleMap 0 ε θ * Complex.I)) : ℂ).re =
        (8 * ((-θ) - θ)) * (-(circleMap 0 ε θ).im) by
          simp [Complex.mul_re, Complex.mul_im, mul_assoc, mul_left_comm, mul_comm]]
    exact mul_pos_of_neg_of_neg hfactor_neg hneg_im
  have hre_eq :
      ((((8 : ℝ) • (circleMap 0 ε θ - circleMap 0 R θ)) : ℂ)).re =
        ((((8 * ((-θ) - θ)) : ℝ) • (circleMap 0 ε θ * Complex.I)) : ℂ).re := by
    simpa using congrArg Complex.re hcompare
  linarith

/-- Helper for Remark III.6-extra-7: the explicit clockwise inner-arc model has the expected
one-sided tangent at the quarter breakpoint. -/
lemma positiveAxisKeyhole_inner_arc_hasDerivWithinAt_one_quarter
    (R ε : ℝ) :
    HasDerivWithinAt
      (fun t : ℝ ↦
        circleMap 0 ε
          (AffineMap.lineMap
            (positiveAxisKeyholeAngle R ε)
            (-positiveAxisKeyholeAngle R ε)
            (8 * t - 1)))
      (((8 * ((-positiveAxisKeyholeAngle R ε) -
            positiveAxisKeyholeAngle R ε)) : ℝ) •
        (circleMap 0 ε (-positiveAxisKeyholeAngle R ε) * Complex.I))
      (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 4 : ℝ) := by
  let θ : ℝ := positiveAxisKeyholeAngle R ε
  have hparam :
      HasDerivAt
        (fun t : ℝ ↦ AffineMap.lineMap θ (-θ) (8 * t - 1))
        (8 * ((-θ) - θ)) (1 / 4 : ℝ) := by
    -- Differentiate the affine angle parameter before composing with `circleMap`.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul, two_mul,
      mul_assoc, mul_left_comm, mul_comm] using
      (AffineMap.hasDerivAt_lineMap
        (a := θ) (b := -θ) (x := (8 : ℝ) * (1 / 4 : ℝ) - 1)).comp
        (1 / 4 : ℝ) (((hasDerivAt_id (1 / 4 : ℝ)).const_mul 8).sub_const 1)
  have hmodel_raw :
      HasDerivAt
        (fun t : ℝ ↦ circleMap 0 ε (AffineMap.lineMap θ (-θ) (8 * t - 1)))
        (((8 * ((-θ) - θ)) : ℝ) •
          (circleMap 0 ε
            (AffineMap.lineMap θ (-θ) ((8 : ℝ) * (1 / 4 : ℝ) - 1)) *
            Complex.I))
        (1 / 4 : ℝ) := by
    -- The circular arc derivative is the usual `circleMap * I` tangent multiplied by the angular
    -- speed.
    simpa [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul,
      two_mul, mul_assoc, mul_left_comm, mul_comm] using
      (hasDerivAt_circleMap 0 ε
        (AffineMap.lineMap θ (-θ) ((8 : ℝ) * (1 / 4 : ℝ) - 1))).scomp
        (1 / 4 : ℝ) hparam
  have hquarter_param : (8 : ℝ) * (1 / 4 : ℝ) - 1 = 1 := by
    norm_num
  have hmodel :
      HasDerivAt
        (fun t : ℝ ↦ circleMap 0 ε (AffineMap.lineMap θ (-θ) (8 * t - 1)))
        (((8 * ((-θ) - θ)) : ℝ) •
          (circleMap 0 ε (-θ) * Complex.I))
        (1 / 4 : ℝ) := by
    -- At `t = 1/4`, the affine parameter lands at the endpoint angle `-2π - θ`.
    convert hmodel_raw using 1
    rw [hquarter_param, AffineMap.lineMap_apply_one]
  simpa [θ] using hmodel.hasDerivWithinAt

/-- Helper for Remark III.6-extra-7: the explicit lower-lip model has the expected one-sided
tangent at the quarter breakpoint. -/
lemma positiveAxisKeyhole_lower_lip_hasDerivWithinAt_one_quarter
    (R ε : ℝ) :
    HasDerivWithinAt
      (fun t : ℝ ↦
        AffineMap.lineMap
          (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
          (4 * t - 1))
      ((4 : ℝ) •
        (circleMap 0 R (-positiveAxisKeyholeAngle R ε) -
          circleMap 0 ε (-positiveAxisKeyholeAngle R ε)))
      (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 4 : ℝ) := by
  let θ : ℝ := positiveAxisKeyholeAngle R ε
  have hmodel :
      HasDerivAt
        (fun t : ℝ ↦
          AffineMap.lineMap
            (circleMap 0 ε (-θ))
            (circleMap 0 R (-θ))
            (4 * t - 1))
        ((4 : ℝ) •
          (circleMap 0 R (-θ) - circleMap 0 ε (-θ)))
        (1 / 4 : ℝ) := by
    have hmodel' :
        HasDerivAt
          (fun t : ℝ ↦
            AffineMap.lineMap
              (circleMap 0 ε (-θ))
              (circleMap 0 R (-θ))
              (t * 4 - 1))
          ((4 : ℝ) •
            (circleMap 0 R (-θ) - circleMap 0 ε (-θ)))
          (1 / 4 : ℝ) := by
      -- The lower lip is an affine segment, so only the scalar speed `4` matters.
      simpa [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul,
        two_mul, mul_assoc, mul_left_comm, mul_comm] using
        (AffineMap.hasDerivAt_lineMap
          (a := circleMap 0 ε (-θ))
          (b := circleMap 0 R (-θ))
          (x := (1 / 4 : ℝ) * 4 - 1)).scomp
          (1 / 4 : ℝ) (((hasDerivAt_id (1 / 4 : ℝ)).mul_const 4).sub_const 1)
    simpa [mul_comm] using hmodel'
  simpa [θ] using hmodel.hasDerivWithinAt

/-- Helper for Remark III.6-extra-7: the second keyhole breakpoint is a genuine corner where the
clockwise inner arc meets the lower slit lip, so the real-plane parametrization is not
differentiable there within `[0, 1]`. -/
lemma positive_axis_keyhole_not_differentiable_at_one_quarter
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    ¬ DifferentiableWithinAt ℝ ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (1 / 4 : ℝ) := by
  -- Route correction: compare the inner-arc and lower-lip tangents at the shared breakpoint,
  -- then separate them by the sign of their real parts.
  intro hdiff
  let θ : ℝ := positiveAxisKeyholeAngle R ε
  let γ : ℝ → ℂ := (positiveAxisKeyhole R ε).extend
  let d : ℂ := derivWithin γ (Set.Icc (0 : ℝ) 1) (1 / 4 : ℝ)
  let inner : ℝ → ℂ := fun t ↦
    circleMap 0 ε (AffineMap.lineMap θ (-θ) (8 * t - 1))
  let lower : ℝ → ℂ := fun t ↦
    AffineMap.lineMap
      (circleMap 0 ε (-θ))
      (circleMap 0 R (-θ))
      (4 * t - 1)
  have hγdiff : DifferentiableWithinAt ℝ γ (Set.Icc (0 : ℝ) 1) (1 / 4 : ℝ) := by
    -- Move from the real-plane curve back to the complex-valued contour.
    simpa [γ, ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
      (Complex.equivRealProdCLM.comp_differentiableWithinAt_iff.mp hdiff)
  have hmain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) 1) (1 / 4 : ℝ) := by
    simpa [d, γ] using hγdiff.hasDerivWithinAt
  have hinnerMain : HasDerivWithinAt γ d (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 4 : ℝ) := by
    -- Restrict the ambient derivative to the inner-arc interval.
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hlowerMain : HasDerivWithinAt γ d (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 4 : ℝ) := by
    -- Restrict the same derivative to the lower-lip interval.
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hinnerγ :
      HasDerivWithinAt γ
        (((8 * ((-θ) - θ)) : ℝ) •
          (circleMap 0 ε (-θ) * Complex.I))
        (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 4 : ℝ) := by
    -- Use the dedicated branch derivative so the main corner proof only does derivative
    -- uniqueness, not repeated elaboration of the branch model.
    exact (positiveAxisKeyhole_inner_arc_hasDerivWithinAt_one_quarter R ε).congr_of_mem
      (fun t ht ↦ by simpa [γ, inner, θ] using positive_axis_keyhole_eq_on_inner_arc R ε ht)
      (by constructor <;> norm_num)
  have hlowerγ :
      HasDerivWithinAt γ
        ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ)))
        (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 4 : ℝ) := by
    -- The lower lip uses the matching affine-segment derivative helper.
    exact (positiveAxisKeyhole_lower_lip_hasDerivWithinAt_one_quarter R ε).congr_of_mem
      (fun t ht ↦ by simpa [γ, lower, θ] using positive_axis_keyhole_eq_on_lower_lip R ε ht)
      (by constructor <;> norm_num)
  have hinnerUD :
      UniqueDiffWithinAt ℝ (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 4 : ℝ) :=
    (uniqueDiffOn_Icc (show (1 / 8 : ℝ) < 1 / 4 by norm_num)).uniqueDiffWithinAt
      (by constructor <;> norm_num)
  have hlowerUD :
      UniqueDiffWithinAt ℝ (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 4 : ℝ) :=
    (uniqueDiffOn_Icc (show (1 / 4 : ℝ) < 1 / 2 by norm_num)).uniqueDiffWithinAt
      (by constructor <;> norm_num)
  have hcompare :
      (((8 * ((-θ) - θ)) : ℝ) •
        (circleMap 0 ε (-θ) * Complex.I)) =
        ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) := by
    -- Uniqueness of within-derivatives forces the two one-sided tangents to agree.
    calc
      (((8 * ((-θ) - θ)) : ℝ) •
          (circleMap 0 ε (-θ) * Complex.I))
          = derivWithin γ (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 4 : ℝ) := by
              symm
              exact hinnerγ.derivWithin hinnerUD
      _ = d := hinnerMain.derivWithin hinnerUD
      _ = derivWithin γ (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 4 : ℝ) := by
            symm
            exact hlowerMain.derivWithin hlowerUD
      _ = ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) :=
            hlowerγ.derivWithin hlowerUD
  have hR : 0 < R := lt_trans hε hεR
  have hθ_pos : 0 < θ := by
    simpa [θ, positiveAxisKeyholeAngle] using Real.arctan_pos.mpr (div_pos hε hR)
  have hinner_re_neg :
      ((((8 * ((-θ) - θ)) : ℝ) •
          (circleMap 0 ε (-θ) * Complex.I)) : ℂ).re < 0 := by
    have hfactor_neg : 8 * ((-θ) - θ) < 0 := by
      nlinarith [Real.pi_pos, hθ_pos]
    have hsin_pos : 0 < Real.sin θ := by
      simpa [θ, positiveAxisKeyholeAngle] using Real.sin_arctan_pos.mpr (div_pos hε hR)
    have hcore : 0 < ε * Real.sin θ := by
      exact mul_pos hε hsin_pos
    have hsin :
        Real.sin (-θ) = -Real.sin θ := by
      simpa using Real.sin_neg θ
    have him :
        (circleMap 0 ε (-θ)).im = -(ε * Real.sin θ) := by
      rw [circleMap_zero_im, hsin]
      ring
    rw [show
      ((((8 * ((-θ) - θ)) : ℝ) •
          (circleMap 0 ε (-θ) * Complex.I)) : ℂ).re =
        (8 * ((-θ) - θ)) * (-(circleMap 0 ε (-θ)).im) by
          simp [Complex.mul_re, Complex.mul_im, mul_assoc, mul_left_comm, mul_comm]]
    rw [him]
    nlinarith
  have hlower_re_pos :
      0 <
        ((((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) :
            ℂ)).re := by
    have hcos_pos : 0 < Real.cos θ := by
      simpa [θ, positiveAxisKeyholeAngle] using Real.cos_arctan_pos (ε / R)
    have hcore : 0 < (R - ε) * Real.cos θ := by
      exact mul_pos (sub_pos.mpr hεR) hcos_pos
    have hcos :
        Real.cos (-θ) = Real.cos θ := by
      simpa using Real.cos_neg θ
    have hcos' :
        Real.cos (-θ) = Real.cos θ := hcos
    have hre_diff :
        (circleMap 0 R (-θ) - circleMap 0 ε (-θ)).re =
          (R - ε) * Real.cos θ := by
      simp [sub_eq_add_neg, circleMap_zero_re, hcos']
      ring
    rw [show
      ((((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) :
          ℂ)).re =
        4 * (circleMap 0 R (-θ) - circleMap 0 ε (-θ)).re by
          simp [mul_assoc, mul_left_comm, mul_comm]]
    rw [hre_diff]
    nlinarith
  have hre_eq :
      ((((8 * ((-θ) - θ)) : ℝ) •
          (circleMap 0 ε (-θ) * Complex.I)) : ℂ).re =
        ((((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) :
            ℂ)).re := by
    simpa using congrArg Complex.re hcompare
  linarith

/-- Helper for Remark III.6-extra-7: the third keyhole breakpoint is a genuine corner where the
lower slit lip meets the outer arc, so the real-plane parametrization is not differentiable there
within `[0, 1]`. -/
lemma positive_axis_keyhole_not_differentiable_at_one_half
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    ¬ DifferentiableWithinAt ℝ ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
  -- Route correction: compare the lower-lip and outer-arc tangents at the shared corner, then
  -- separate them by the sign of their imaginary parts.
  intro hdiff
  let θ : ℝ := positiveAxisKeyholeAngle R ε
  let γ : ℝ → ℂ := (positiveAxisKeyhole R ε).extend
  let d : ℂ := derivWithin γ (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ)
  let lower : ℝ → ℂ := fun t ↦
    AffineMap.lineMap
      (circleMap 0 ε (-θ))
      (circleMap 0 R (-θ))
      (4 * t - 1)
  let outer : ℝ → ℂ := fun t ↦
    circleMap 0 R
      (AffineMap.lineMap (-θ) θ (2 * t - 1))
  have hγdiff : DifferentiableWithinAt ℝ γ (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
    -- Move from the real-plane curve back to the complex-valued contour.
    simpa [γ, ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
      (Complex.equivRealProdCLM.comp_differentiableWithinAt_iff.mp hdiff)
  have hmain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
    simpa [d, γ] using hγdiff.hasDerivWithinAt
  have hlowerMain : HasDerivWithinAt γ d (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    -- Restrict the ambient derivative to the lower-lip interval.
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have houterMain : HasDerivWithinAt γ d (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) := by
    -- Restrict the same derivative to the outer-arc interval.
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hlowerγ :
      HasDerivWithinAt γ
        ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ)))
        (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    -- Differentiate the affine lower-lip model and transfer it back to the explicit contour.
    have hmodel :
        HasDerivAt lower
          ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ)))
          (1 / 2 : ℝ) := by
      have hmodel' :
          HasDerivAt
            (fun t : ℝ ↦
              AffineMap.lineMap
                (circleMap 0 ε (-θ))
                (circleMap 0 R (-θ))
                (t * 4 - 1))
            ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ)))
            (1 / 2 : ℝ) := by
        simpa [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul,
          two_mul, mul_assoc, mul_left_comm, mul_comm] using
          (AffineMap.hasDerivAt_lineMap
            (a := circleMap 0 ε (-θ))
            (b := circleMap 0 R (-θ))
            (x := (1 / 2 : ℝ) * 4 - 1)).scomp
            (1 / 2 : ℝ) (((hasDerivAt_id (1 / 2 : ℝ)).mul_const 4).sub_const 1)
      simpa [lower, mul_comm] using hmodel'
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, lower] using positive_axis_keyhole_eq_on_lower_lip R ε ht)
      (by constructor <;> norm_num)
  have houterγ :
      HasDerivWithinAt γ
        (((2 * (θ - (-θ))) : ℝ) •
          (circleMap 0 R (-θ) * Complex.I))
        (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) := by
    -- Differentiate the outer circular arc through its affine angle parameter.
    have hparam :
        HasDerivAt
          (fun t : ℝ ↦ AffineMap.lineMap (-θ) θ (2 * t - 1))
          (2 * (θ - (-θ))) (1 / 2 : ℝ) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul, two_mul,
        mul_assoc, mul_left_comm, mul_comm] using
        (AffineMap.hasDerivAt_lineMap
          (a := -θ) (b := θ) (x := (2 : ℝ) * (1 / 2 : ℝ) - 1)).comp
          (1 / 2 : ℝ) (((hasDerivAt_id (1 / 2 : ℝ)).const_mul 2).sub_const 1)
    have hmodel :
        HasDerivAt outer
          (((2 * (θ - (-θ))) : ℝ) •
            (circleMap 0 R (-θ) * Complex.I))
          (1 / 2 : ℝ) := by
      simpa [outer, smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add,
        add_mul, two_mul, mul_assoc, mul_left_comm, mul_comm] using
        (hasDerivAt_circleMap 0 R
          (AffineMap.lineMap (-θ) θ ((2 : ℝ) * (1 / 2 : ℝ) - 1))).scomp
          (1 / 2 : ℝ) hparam
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, outer] using positive_axis_keyhole_eq_on_outer_arc R ε ht)
      (by constructor <;> norm_num)
  have hlowerUD :
      UniqueDiffWithinAt ℝ (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) :=
    (uniqueDiffOn_Icc (show (1 / 4 : ℝ) < 1 / 2 by norm_num)).uniqueDiffWithinAt
      (by constructor <;> norm_num)
  have houterUD :
      UniqueDiffWithinAt ℝ (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) :=
    (uniqueDiffOn_Icc (show (1 / 2 : ℝ) < 1 by norm_num)).uniqueDiffWithinAt
      (by constructor <;> norm_num)
  have hcompare :
      ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) =
        (((2 * (θ - (-θ))) : ℝ) •
          (circleMap 0 R (-θ) * Complex.I)) := by
    -- Uniqueness of within-derivatives forces the two one-sided tangents to agree.
    calc
      ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ)))
          = derivWithin γ (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
              symm
              exact hlowerγ.derivWithin hlowerUD
      _ = d := hlowerMain.derivWithin hlowerUD
      _ = derivWithin γ (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) := by
            symm
            exact houterMain.derivWithin houterUD
      _ =
          (((2 * (θ - (-θ))) : ℝ) •
            (circleMap 0 R (-θ) * Complex.I)) :=
            houterγ.derivWithin houterUD
  have hR : 0 < R := lt_trans hε hεR
  have hθ_pos : 0 < θ := by
    simpa [θ, positiveAxisKeyholeAngle] using Real.arctan_pos.mpr (div_pos hε hR)
  have hlower_im_neg :
      ((((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) :
          ℂ)).im < 0 := by
    have hsin_pos : 0 < Real.sin θ := by
      simpa [θ, positiveAxisKeyholeAngle] using Real.sin_arctan_pos.mpr (div_pos hε hR)
    have hcore : (R - ε) * (-Real.sin θ) < 0 := by
      exact mul_neg_of_pos_of_neg (sub_pos.mpr hεR) (by linarith)
    have hsin :
        Real.sin (-θ) = -Real.sin θ := by
      simpa using Real.sin_neg θ
    have hsin' :
        Real.sin (-θ) = -Real.sin θ := hsin
    rw [show
      ((((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) :
          ℂ)).im =
        4 * ((R - ε) * (-Real.sin θ)) by
          simp [circleMap_zero_im, sub_eq_add_neg, hsin']
          ring]
    exact mul_neg_of_pos_of_neg (by norm_num) hcore
  have houter_im_pos :
      0 <
        ((((2 * (θ - (-θ))) : ℝ) •
            (circleMap 0 R (-θ) * Complex.I)) : ℂ).im := by
    have hfactor_pos : 0 < 2 * (θ - (-θ)) := by
      nlinarith [Real.pi_pos, hθ_pos]
    have hcos_pos : 0 < Real.cos θ := by
      simpa [θ, positiveAxisKeyholeAngle] using Real.cos_arctan_pos (ε / R)
    have hre_pos : 0 < (circleMap 0 R (-θ)).re := by
      have hcos :
          Real.cos (-θ) = Real.cos θ := by
        simpa using Real.cos_neg θ
      rw [circleMap_zero_re, hcos]
      exact mul_pos hR hcos_pos
    rw [show
      ((((2 * (θ - (-θ))) : ℝ) •
          (circleMap 0 R (-θ) * Complex.I)) : ℂ).im =
        (2 * (θ - (-θ))) * (circleMap 0 R (-θ)).re by
          simp [Complex.mul_re, Complex.mul_im, mul_assoc, mul_left_comm, mul_comm]]
    exact mul_pos hfactor_pos hre_pos
  have him_eq :
      ((((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) :
          ℂ)).im =
        ((((2 * (θ - (-θ))) : ℝ) •
            (circleMap 0 R (-θ) * Complex.I)) : ℂ).im := by
    simpa using congrArg Complex.im hcompare
  linarith

/-- Helper for Remark III.6-extra-7: every interior regular parameter of the keyhole contour lies
on exactly one of the four open source branches. This is the branch dispatcher needed before the
later boundary-straightening proof can case-split cleanly. -/
lemma positiveAxisKeyhole_regular_parameter_mem_open_branch
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) {t : I}
    (ht : t.1 ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t.1) :
    t.1 ∈ Set.Ioo (0 : ℝ) (1 / 8) ∨
      t.1 ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4) ∨
      t.1 ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∨
      t.1 ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ) := by
  -- Route correction: reuse the stable interval dispatcher, then exclude the three interior
  -- breakpoints by the corner nondifferentiability lemmas.
  rcases positive_axis_keyhole_parameter_cases t with
    ht0 | htupper | ht18 | htinner | ht14 | htlower | ht12 | htouter | ht1
  · exfalso
    simpa [ht0] using ht.1
  · exact Or.inl htupper
  · exfalso
    exact
      (positive_axis_keyhole_not_differentiable_at_one_eighth hε hεR)
        (by simpa [ht18] using hdiff)
  · exact Or.inr <| Or.inl htinner
  · exfalso
    exact
      (positive_axis_keyhole_not_differentiable_at_one_quarter hε hεR)
        (by simpa [ht14] using hdiff)
  · exact Or.inr <| Or.inr <| Or.inl htlower
  · exfalso
    exact
      (positive_axis_keyhole_not_differentiable_at_one_half hε hεR)
        (by simpa [ht12] using hdiff)
  · exact Or.inr <| Or.inr <| Or.inr htouter
  · exfalso
    simpa [ht1] using ht.2

/-- Helper for Remark III.6-extra-7: the image of the explicit keyhole contour is the union of
its four source-facing pieces. This isolates the `Path.trans_range` bookkeeping needed later for
the wedge-annulus frontier comparison. -/
theorem positiveAxisKeyhole_range_eq_four_piece_union (R ε : ℝ) :
    Set.range (positiveAxisKeyhole R ε) =
      let θ := positiveAxisKeyholeAngle R ε
      let upper : Path (circleMap 0 R θ) (circleMap 0 ε θ) :=
        Path.segment (circleMap 0 R θ) (circleMap 0 ε θ)
      let inner : Path (circleMap 0 ε θ) (circleMap 0 ε (-θ)) :=
        (Path.segment θ (-θ)).map (continuous_circleMap 0 ε)
      let lower : Path (circleMap 0 ε (-θ))
          (circleMap 0 R (-θ)) :=
        Path.segment (circleMap 0 ε (-θ)) (circleMap 0 R (-θ))
      let outer : Path (circleMap 0 R (-θ)) (circleMap 0 R θ) :=
        (Path.segment (-θ) θ).map (continuous_circleMap 0 R)
      Set.range upper ∪ Set.range inner ∪ Set.range lower ∪ Set.range outer := by
  -- Expand the keyhole contour into its four explicit pieces before comparing images.
  rw [positiveAxisKeyhole_def]
  simp only [Path.trans_range]

/-- Helper for Remark III.6-extra-7: the upper slit lip is exactly the geometric image of the
radius interval `Set.uIcc R ε` under the fixed-angle circle map. -/
lemma positiveAxisKeyhole_upper_lip_range_eq_geometric
    (R ε : ℝ) :
    Set.range
        (Path.segment
          (circleMap 0 R (positiveAxisKeyholeAngle R ε))
          (circleMap 0 ε (positiveAxisKeyholeAngle R ε))) =
      (fun ρ : ℝ ↦ circleMap 0 ρ (positiveAxisKeyholeAngle R ε)) '' Set.uIcc R ε := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨AffineMap.lineMap R ε (t : ℝ), ?_, ?_⟩
    · -- The segment parameter determines a radius in the closed interval between `R` and `ε`.
      simpa [segment_eq_uIcc] using lineMap_mem_segment ℝ R ε t.2
    · -- Along the upper lip only the radius changes, not the angle.
      simpa [Path.segment_apply] using
        (positiveAxisKeyhole_lineMap_circleMap_same_angle
          R ε (positiveAxisKeyholeAngle R ε) (t : ℝ)).symm
  · rintro ⟨ρ, hρ, rfl⟩
    have hseg : ρ ∈ segment ℝ R ε := by
      -- Reinterpret the closed radius interval as the corresponding real segment.
      simpa [segment_eq_uIcc] using hρ
    rw [segment_eq_image_lineMap] at hseg
    rcases hseg with ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    -- Repackage the geometric radius parameter back through the path parameter.
    simpa [Path.segment_apply] using
      positiveAxisKeyhole_lineMap_circleMap_same_angle
        R ε (positiveAxisKeyholeAngle R ε) t

/-- Helper for Remark III.6-extra-7: the clockwise inner arc is exactly the image of the angular
interval between the two slit-boundary angles under `circleMap 0 ε`. -/
lemma positiveAxisKeyhole_inner_arc_range_eq_geometric
    (R ε : ℝ) :
    Set.range
        (((Path.segment
            (positiveAxisKeyholeAngle R ε)
            (-positiveAxisKeyholeAngle R ε)).map
              (continuous_circleMap 0 ε))) =
      (fun φ : ℝ ↦ circleMap 0 ε φ) ''
        Set.uIcc (positiveAxisKeyholeAngle R ε) (-positiveAxisKeyholeAngle R ε) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨AffineMap.lineMap
        (positiveAxisKeyholeAngle R ε)
        (-positiveAxisKeyholeAngle R ε)
        (t : ℝ), ?_, ?_⟩
    · -- The segment parameter determines an angle between the two slit-boundary angles.
      simpa [segment_eq_uIcc] using
        lineMap_mem_segment ℝ
          (positiveAxisKeyholeAngle R ε)
          (-positiveAxisKeyholeAngle R ε)
          t.2
    · -- The mapped segment is exactly the circle image of that affine angle parameter.
      simp [Path.map_coe, Function.comp_apply, Path.segment_apply]
  · rintro ⟨φ, hφ, rfl⟩
    have hseg :
        φ ∈ segment ℝ
          (positiveAxisKeyholeAngle R ε)
          (-positiveAxisKeyholeAngle R ε) := by
      -- Reinterpret the closed angle interval as the corresponding real segment.
      simpa [segment_eq_uIcc] using hφ
    rw [segment_eq_image_lineMap] at hseg
    rcases hseg with ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    -- Repackage the geometric angle parameter through the mapped path.
    simp [Path.map_coe, Function.comp_apply, Path.segment_apply]

/-- Helper for Remark III.6-extra-7: the lower slit lip is exactly the geometric image of the
radius interval `Set.uIcc ε R` under the lower boundary angle. -/
lemma positiveAxisKeyhole_lower_lip_range_eq_geometric
    (R ε : ℝ) :
    Set.range
        (Path.segment
          (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε))) =
      (fun ρ : ℝ ↦ circleMap 0 ρ (-positiveAxisKeyholeAngle R ε)) '' Set.uIcc ε R := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨AffineMap.lineMap ε R (t : ℝ), ?_, ?_⟩
    · -- The segment parameter determines a radius in the closed interval between `ε` and `R`.
      simpa [segment_eq_uIcc] using lineMap_mem_segment ℝ ε R t.2
    · -- Along the lower lip only the radius changes, not the angle.
      simpa [Path.segment_apply] using
        (positiveAxisKeyhole_lineMap_circleMap_same_angle
          ε R (-positiveAxisKeyholeAngle R ε) (t : ℝ)).symm
  · rintro ⟨ρ, hρ, rfl⟩
    have hseg : ρ ∈ segment ℝ ε R := by
      -- Reinterpret the closed radius interval as the corresponding real segment.
      simpa [segment_eq_uIcc] using hρ
    rw [segment_eq_image_lineMap] at hseg
    rcases hseg with ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    -- Repackage the geometric radius parameter back through the path parameter.
    simpa [Path.segment_apply] using
      positiveAxisKeyhole_lineMap_circleMap_same_angle
        ε R (-positiveAxisKeyholeAngle R ε) t

/-- Helper for Remark III.6-extra-7: the outer arc is exactly the image of the angular interval
between the lower and upper slit-boundary angles under `circleMap 0 R`. -/
lemma positiveAxisKeyhole_outer_arc_range_eq_geometric
    (R ε : ℝ) :
    Set.range
        (((Path.segment
            (-positiveAxisKeyholeAngle R ε)
            (positiveAxisKeyholeAngle R ε)).map
              (continuous_circleMap 0 R))) =
      (fun φ : ℝ ↦ circleMap 0 R φ) ''
        Set.uIcc (-positiveAxisKeyholeAngle R ε) (positiveAxisKeyholeAngle R ε) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨AffineMap.lineMap
        (-positiveAxisKeyholeAngle R ε)
        (positiveAxisKeyholeAngle R ε)
        (t : ℝ), ?_, ?_⟩
    · -- The segment parameter determines an angle between the two slit-boundary angles.
      simpa [segment_eq_uIcc] using
        lineMap_mem_segment ℝ
          (-positiveAxisKeyholeAngle R ε)
          (positiveAxisKeyholeAngle R ε)
          t.2
    · -- The mapped segment is exactly the circle image of that affine angle parameter.
      simp [Path.map_coe, Function.comp_apply, Path.segment_apply]
  · rintro ⟨φ, hφ, rfl⟩
    have hseg :
        φ ∈ segment ℝ
          (-positiveAxisKeyholeAngle R ε)
          (positiveAxisKeyholeAngle R ε) := by
      -- Reinterpret the closed angle interval as the corresponding real segment.
      simpa [segment_eq_uIcc] using hφ
    rw [segment_eq_image_lineMap] at hseg
    rcases hseg with ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    -- Repackage the geometric angle parameter through the mapped outer path.
    simp [Path.map_coe, Function.comp_apply, Path.segment_apply]

/-- Helper for Remark III.6-extra-7: the range of the positive-axis keyhole contour is the union
of the four geometric pieces from the source proof: upper lip, inner circle, lower lip, and outer
circle. -/
theorem positiveAxisKeyhole_range_eq_geometric_piece_union
    (R ε : ℝ) :
    Set.range (positiveAxisKeyhole R ε) =
      (fun ρ : ℝ ↦ circleMap 0 ρ (positiveAxisKeyholeAngle R ε)) '' Set.uIcc R ε ∪
        (fun φ : ℝ ↦ circleMap 0 ε φ) ''
          Set.uIcc (positiveAxisKeyholeAngle R ε) (-positiveAxisKeyholeAngle R ε) ∪
        (fun ρ : ℝ ↦ circleMap 0 ρ (-positiveAxisKeyholeAngle R ε)) '' Set.uIcc ε R ∪
        (fun φ : ℝ ↦ circleMap 0 R φ) ''
          Set.uIcc (-positiveAxisKeyholeAngle R ε) (positiveAxisKeyholeAngle R ε) := by
  -- Rewrite the contour range into the four canonical path pieces before converting each one to
  -- its radius/angle image.
  rw [positiveAxisKeyhole_range_eq_four_piece_union]
  dsimp
  -- Route correction: normalize the contour image to the source geometric pieces before any
  -- frontier or simplicity argument.
  rw [positiveAxisKeyhole_upper_lip_range_eq_geometric,
    positiveAxisKeyhole_inner_arc_range_eq_geometric,
    positiveAxisKeyhole_lower_lip_range_eq_geometric,
    positiveAxisKeyhole_outer_arc_range_eq_geometric]

/-- Helper for Remark III.6-extra-7: a radial segment along a fixed argument stays inside the
closed annulus `{z | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R}` once both endpoint radii lie in `[ε, R]`. -/
lemma positiveAxisKeyhole_radial_segment_range_subset_closed_annulus_of_angle
    {ρ₀ ρ₁ φ R ε : ℝ}
    (hε : 0 ≤ ε)
    (hρ₀ : ρ₀ ∈ Set.Icc ε R) (hρ₁ : ρ₁ ∈ Set.Icc ε R) :
    Set.range (Path.segment (circleMap 0 ρ₀ φ) (circleMap 0 ρ₁ φ)) ⊆
      {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
  rintro z ⟨t, rfl⟩
  have hρt : AffineMap.lineMap ρ₀ ρ₁ (t : ℝ) ∈ Set.Icc ε R := by
    -- Convexity of the closed interval keeps the interpolated radius between `ε` and `R`.
    exact (convex_Icc ε R).lineMap_mem hρ₀ hρ₁ t.2
  have hsegment_eq :
      (Path.segment (circleMap 0 ρ₀ φ) (circleMap 0 ρ₁ φ)) t =
        circleMap 0 (AffineMap.lineMap ρ₀ ρ₁ (t : ℝ)) φ := by
    -- A straight interpolation between two points on the same ray only changes the radius.
    rw [Complex.ext_iff]
    constructor <;>
      simp [Path.segment_apply, circleMap_zero_re, circleMap_zero_im,
        AffineMap.lineMap_apply_module, smul_eq_mul, add_mul] <;>
      ring
  have hnorm :
      ‖(Path.segment (circleMap 0 ρ₀ φ) (circleMap 0 ρ₁ φ)) t‖ =
        AffineMap.lineMap ρ₀ ρ₁ (t : ℝ) := by
    rw [hsegment_eq, norm_circleMap_zero, abs_of_nonneg (le_trans hε hρt.1)]
  refine ⟨?_, ?_⟩
  · rw [hnorm]
    exact hρt.1
  · rw [hnorm]
    exact hρt.2

/-- Helper for Remark III.6-extra-7: a circular arc with fixed radius in `[ε, R]` stays inside the
same closed annulus. -/
lemma positiveAxisKeyhole_circle_arc_range_subset_closed_annulus_of_radius_bounds
    {ρ α β R ε : ℝ}
    (hε : 0 ≤ ε)
    (hρ : ρ ∈ Set.Icc ε R) :
    Set.range (((Path.segment α β).map (continuous_circleMap 0 ρ))) ⊆
      {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
  rintro z ⟨t, rfl⟩
  have hnorm :
      ‖(((Path.segment α β).map (continuous_circleMap 0 ρ)) t)‖ = ρ := by
    -- The circle map has constant norm equal to its radius.
    rw [Path.map_coe, Function.comp_apply, norm_circleMap_zero, abs_of_nonneg (le_trans hε hρ.1)]
  refine ⟨?_, ?_⟩
  · rw [hnorm]
    exact hρ.1
  · rw [hnorm]
    exact hρ.2

/-- Helper for Remark III.6-extra-7: every point of the explicit positive-axis keyhole contour
stays in the closed annulus `{z | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R}`. This isolates the radial control before the
later wedge-frontier comparison. -/
lemma positiveAxisKeyhole_range_subset_closed_annulus
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    Set.range (positiveAxisKeyhole R ε) ⊆ {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
  have hε_nonneg : 0 ≤ ε := le_of_lt hε
  have hupper :
      Set.range
          (Path.segment
            (circleMap 0 R (positiveAxisKeyholeAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeAngle R ε))) ⊆
        {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
    -- The upper slit lip interpolates between the two allowed radii `R` and `ε`.
    exact positiveAxisKeyhole_radial_segment_range_subset_closed_annulus_of_angle
      hε_nonneg
      (ρ₀ := R) (ρ₁ := ε)
      (φ := positiveAxisKeyholeAngle R ε)
      (R := R) (ε := ε)
      ⟨le_of_lt hεR, le_rfl⟩
      ⟨le_rfl, le_of_lt hεR⟩
  have hinner :
      Set.range
          (((Path.segment
              (positiveAxisKeyholeAngle R ε)
              (-positiveAxisKeyholeAngle R ε)).map
                (continuous_circleMap 0 ε))) ⊆
        {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
    -- The inner arc has constant radius exactly `ε`.
    exact positiveAxisKeyhole_circle_arc_range_subset_closed_annulus_of_radius_bounds
      hε_nonneg
      (ρ := ε)
      (α := positiveAxisKeyholeAngle R ε)
      (β := -positiveAxisKeyholeAngle R ε)
      (R := R) (ε := ε)
      ⟨le_rfl, le_of_lt hεR⟩
  have hlower :
      Set.range
          (Path.segment
            (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
            (circleMap 0 R (-positiveAxisKeyholeAngle R ε))) ⊆
        {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
    -- The lower slit lip uses the same two radii with the opposite orientation.
    exact positiveAxisKeyhole_radial_segment_range_subset_closed_annulus_of_angle
      hε_nonneg
      (ρ₀ := ε) (ρ₁ := R)
      (φ := -positiveAxisKeyholeAngle R ε)
      (R := R) (ε := ε)
      ⟨le_rfl, le_of_lt hεR⟩
      ⟨le_of_lt hεR, le_rfl⟩
  have houter :
      Set.range
          (((Path.segment
              (-positiveAxisKeyholeAngle R ε)
              (positiveAxisKeyholeAngle R ε)).map
                (continuous_circleMap 0 R))) ⊆
        {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
    -- The outer arc has constant radius exactly `R`.
    exact positiveAxisKeyhole_circle_arc_range_subset_closed_annulus_of_radius_bounds
      hε_nonneg
      (ρ := R)
      (α := -positiveAxisKeyholeAngle R ε)
      (β := positiveAxisKeyholeAngle R ε)
      (R := R) (ε := ε)
      ⟨le_of_lt hεR, le_rfl⟩
  -- Decompose the contour into its four canonical pieces and apply the corresponding annulus
  -- bound piecewise.
  rw [positiveAxisKeyhole_range_eq_four_piece_union]
  intro z hz
  rcases hz with hz | hz
  · rcases hz with hz | hz
    · rcases hz with hz | hz
      · exact hupper hz
      · exact hinner hz
    · exact hlower hz
  · exact houter hz

/-- Helper for Remark III.6-extra-7: the singleton closed-path family attached to
`positiveAxisKeyhole` has union equal to the actual contour range. This is the stable interface
between the explicit path formula and the later `IsOrientedBoundaryOf` family API. -/
lemma positiveAxisKeyhole_singleton_iUnion_range (R ε : ℝ) :
    (⋃ i : Unit,
        Set.range ((((fun _ : Unit ↦ (positiveAxisKeyhole R ε).toClosedPath) i).toPath))) =
      Set.range (positiveAxisKeyhole R ε) := by
  ext z
  constructor
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨i, hi⟩
    cases i
    simpa [Path.toClosedPath] using hi
  · intro hz
    refine Set.mem_iUnion.mpr ?_
    refine ⟨(), ?_⟩
    simpa [Path.toClosedPath] using hz

/-- Helper for Remark III.6-extra-7: the open positive wedge removed from the annulus in the
source-faithful fixed-parameter model of the keyhole contour. -/
abbrev positiveAxisWedge (R ε : ℝ) : Set ℂ :=
  {z : ℂ | 0 < z.re ∧ |z.im| < (ε / R) * z.re}

/-- Helper for Remark III.6-extra-7: the compact wedge-annulus whose frontier should match
`positiveAxisKeyhole R ε`. -/
abbrev positiveAxisWedgeAnnulus (R ε : ℝ) : Set ℂ :=
  {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} \ positiveAxisWedge R ε

/-- Helper for Remark III.6-extra-7: the removed positive wedge is open because it is cut out by
two strict inequalities in the real and imaginary coordinates. -/
lemma isOpen_positiveAxisWedge (R ε : ℝ) :
    IsOpen (positiveAxisWedge R ε) := by
  have hre : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have him : IsOpen {z : ℂ | |z.im| < (ε / R) * z.re} := by
    simpa using
      isOpen_lt (continuous_abs.comp Complex.continuous_im)
        (continuous_const.mul Complex.continuous_re)
  -- The slit wedge is exactly the intersection of the positive-real half-space with the
  -- strict slope inequality.
  simpa [positiveAxisWedge, Set.setOf_and] using hre.inter him

/-- Helper for Remark III.6-extra-7: the slit wedge-annulus is closed because it is a closed
annulus with the open positive wedge removed. -/
lemma isClosed_positiveAxisWedgeAnnulus (R ε : ℝ) :
    IsClosed (positiveAxisWedgeAnnulus R ε) := by
  have hclosed_annulus : IsClosed {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
    simpa [Set.setOf_and] using
      (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
  -- Rewrite the set difference as an intersection with the wedge complement.
  simpa [positiveAxisWedgeAnnulus, Set.diff_eq, Set.setOf_and] using
    hclosed_annulus.inter (isOpen_positiveAxisWedge R ε).isClosed_compl

/-- Helper for Remark III.6-extra-7: every point of the slit wedge-annulus has norm at most `R`,
so the whole region lies in the closed ball centered at `0` with radius `R`. -/
lemma positiveAxisWedgeAnnulus_subset_closedBall (R ε : ℝ) :
    positiveAxisWedgeAnnulus R ε ⊆ Metric.closedBall (0 : ℂ) R := by
  intro z hz
  -- The outer annulus inequality is exactly the closed-ball bound.
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact hz.1.2

/-- Helper for Remark III.6-extra-7: the slit wedge-annulus is compact as a closed subset of the
closed ball of radius `R`. -/
lemma isCompact_positiveAxisWedgeAnnulus (R ε : ℝ) :
    IsCompact (positiveAxisWedgeAnnulus R ε) := by
  -- The closed-ball owner keeps the compactness proof independent of the slit geometry details.
  refine (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
    (isClosed_positiveAxisWedgeAnnulus R ε) ?_
  exact positiveAxisWedgeAnnulus_subset_closedBall R ε

/-- Helper for Remark III.6-extra-7: once the positive wedge is removed from the annulus, every
remaining point avoids the shifted branch cut `[0, ∞)`, so the whole wedge-annulus lies in the
domain of `z ↦ Complex.log (-z)`. -/
lemma positiveAxisWedgeAnnulus_subset_shiftedLogDomain
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    positiveAxisWedgeAnnulus R ε ⊆ shiftedLogDomain := by
  intro z hz
  rcases hz with ⟨hzAnnulus, hzNotWedge⟩
  have hR : 0 < R := lt_trans hε hεR
  have hz_ne_zero : z ≠ 0 := by
    -- The annulus constraints force `‖z‖ ≥ ε > 0`, so the center is excluded.
    intro hz0
    have hnorm_nonpos : ε ≤ 0 := by
      simpa [hz0] using hzAnnulus.1
    linarith
  change -z ∈ Complex.slitPlane
  rw [Complex.mem_slitPlane_iff]
  by_cases hz_im : z.im = 0
  · -- On the real axis, being outside the removed positive wedge forces the real part to be
    -- negative, which exactly means `-z` lies in the principal slit plane.
    by_cases hz_re_pos : 0 < z.re
    · have hz_mem_wedge : z ∈ positiveAxisWedge R ε := by
        refine ⟨hz_re_pos, ?_⟩
        have hslope : 0 < (ε / R) * z.re := by
          exact mul_pos (div_pos hε hR) hz_re_pos
        simpa [positiveAxisWedge, hz_im, abs_zero] using hslope
      exact (hzNotWedge hz_mem_wedge).elim
    · have hz_re_ne : z.re ≠ 0 := by
        intro hz_re
        apply hz_ne_zero
        apply Complex.ext <;> simp [hz_re, hz_im]
      have hz_re_neg : z.re < 0 := by
        exact lt_of_le_of_ne (le_of_not_gt hz_re_pos) (by simpa [eq_comm] using hz_re_ne)
      exact Or.inl (by simpa using neg_pos.mpr hz_re_neg)
  · -- Away from the real axis, the shifted branch is already regular because `-z` is not on the
    -- slit.
    exact Or.inr (by simpa using hz_im)

/-- Helper for Remark III.6-extra-7: points on the upper lip of the keyhole lie on the line of
slope `ε / R`. This is the first concrete bridge from the explicit contour parametrization to the
wedge-annulus boundary geometry. -/
lemma positiveAxisKeyhole_upper_lip_line
    (R ε ρ : ℝ) :
    (circleMap 0 ρ (positiveAxisKeyholeAngle R ε)).im =
      (ε / R) * (circleMap 0 ρ (positiveAxisKeyholeAngle R ε)).re := by
  -- Unfold the circle coordinates at the keyhole angle and use the standard arctangent formulas.
  rw [circleMap_zero_im, circleMap_zero_re, positiveAxisKeyholeAngle,
    Real.sin_arctan, Real.cos_arctan]
  ring_nf

/-- Helper for Remark III.6-extra-7: points on the lower lip of the keyhole lie on the line of
slope `-(ε / R)`. This is the companion boundary equation for the lower slit edge. -/
lemma positiveAxisKeyhole_lower_lip_line
    (R ε ρ : ℝ) :
    (circleMap 0 ρ (-positiveAxisKeyholeAngle R ε)).im =
      -((ε / R) * (circleMap 0 ρ (-positiveAxisKeyholeAngle R ε)).re) := by
  -- Normalize the angle by one full turn, then reduce again to the arctangent identities.
  have hsin :
      Real.sin (-positiveAxisKeyholeAngle R ε) =
        -Real.sin (positiveAxisKeyholeAngle R ε) := by
    simpa using Real.sin_neg (positiveAxisKeyholeAngle R ε)
  have hcos :
      Real.cos (-positiveAxisKeyholeAngle R ε) =
        Real.cos (positiveAxisKeyholeAngle R ε) := by
    simpa using Real.cos_neg (positiveAxisKeyholeAngle R ε)
  rw [circleMap_zero_im, circleMap_zero_re, hsin, hcos, positiveAxisKeyholeAngle,
    Real.sin_arctan, Real.cos_arctan]
  ring_nf

/-- Helper for Remark III.6-extra-7: every nonzero point on the upper lip has positive real part,
so it belongs to the positive-axis side of the wedge model. -/
lemma positiveAxisKeyhole_upper_lip_re_pos
    {R ε ρ : ℝ} (hρ : 0 < ρ) :
    0 < (circleMap 0 ρ (positiveAxisKeyholeAngle R ε)).re := by
  -- The opening angle is an arctangent, so its cosine is always positive.
  rw [circleMap_zero_re, positiveAxisKeyholeAngle]
  exact mul_pos hρ (Real.cos_arctan_pos (ε / R))

/-- Helper for Remark III.6-extra-7: every nonzero point on the lower lip also has positive real
part, which is the remaining sign condition in the wedge-annulus geometry. -/
lemma positiveAxisKeyhole_lower_lip_re_pos
    {R ε ρ : ℝ} (hρ : 0 < ρ) :
    0 < (circleMap 0 ρ (-positiveAxisKeyholeAngle R ε)).re := by
  -- The lower-lip angle differs from the upper one by a full turn and a sign change.
  have hcos :
      Real.cos (-positiveAxisKeyholeAngle R ε) =
        Real.cos (positiveAxisKeyholeAngle R ε) := by
    simpa using Real.cos_neg (positiveAxisKeyholeAngle R ε)
  rw [circleMap_zero_re, hcos, positiveAxisKeyholeAngle]
  exact mul_pos hρ (Real.cos_arctan_pos (ε / R))

/-- Helper for Remark III.6-extra-7: a circular arc obtained by mapping an affine angle segment
through `circleMap` is differentiable as a path. -/
lemma positiveAxisKeyhole_circle_segment_isDifferentiable (ρ α β : ℝ) :
    ((Path.segment α β).map (continuous_circleMap 0 ρ)).IsDifferentiable := by
  -- The angular parameter is affine on `[0, 1]`, so composing it with `circleMap` stays `C¹`.
  rw [Path.IsDifferentiable]
  have hcontDiff :
      ContDiffOn ℝ 1
        (fun t : ℝ ↦ circleMap 0 ρ ((ContinuousAffineMap.lineMap (R := ℝ) α β) t))
        (Set.Icc (0 : ℝ) 1) := by
    simpa [Function.comp] using
      ((contDiff_circleMap 0 ρ).comp
        (ContinuousAffineMap.contDiff (ContinuousAffineMap.lineMap (R := ℝ) α β))).contDiffOn
  refine hcontDiff.congr ?_
  intro t ht
  rw [Path.extend_apply _ ht]
  simp [ContinuousAffineMap.coe_lineMap_eq, Path.map_coe, Path.segment_apply,
    AffineMap.lineMap_apply_module]

/-- Helper for Remark III.6-extra-7: the positive-axis keyhole contour is piecewise
differentiable because it is built from two straight segments and two smooth circular arcs. -/
lemma positiveAxisKeyhole_isPiecewiseDifferentiable (R ε : ℝ) :
    (positiveAxisKeyhole R ε).IsPiecewiseDifferentiable := by
  let θ : ℝ := positiveAxisKeyholeAngle R ε
  have hupper :
      (Path.segment (circleMap 0 R θ) (circleMap 0 ε θ)).IsPiecewiseDifferentiable :=
    Path.segment_isPiecewiseDifferentiable _ _
  have hinner :
      ((Path.segment θ (-θ)).map (continuous_circleMap 0 ε)).IsDifferentiable :=
    positiveAxisKeyhole_circle_segment_isDifferentiable ε θ (-θ)
  have hlower :
      (Path.segment (circleMap 0 ε (-θ))
        (circleMap 0 R (-θ))).IsDifferentiable :=
    Path.segment_isDifferentiable _ _
  have houter :
      ((Path.segment (-θ) θ).map (continuous_circleMap 0 R)).IsDifferentiable :=
    positiveAxisKeyhole_circle_segment_isDifferentiable R (-θ) θ
  -- Append the four smooth pieces in the same source order used to define the keyhole contour.
  have hupper_inner := hupper.trans_of_isDifferentiable hinner
  have hupper_inner_lower := hupper_inner.trans_of_isDifferentiable hlower
  have hall := hupper_inner_lower.trans_of_isDifferentiable houter
  simpa [positiveAxisKeyhole, θ] using hall

/-- Helper for Remark III.6-extra-7: the shifted slit-plane domain is open because it is the
preimage of `Complex.slitPlane` under negation. -/
lemma isOpen_shiftedLogDomain :
    IsOpen shiftedLogDomain := by
  -- Rewrite the shifted branch domain as a preimage so the openness of `Complex.slitPlane`
  -- transfers directly.
  simpa [shiftedLogDomain] using Complex.isOpen_slitPlane.preimage continuous_neg

/-- Helper for Remark III.6-extra-7: every pole recorded by the finite pole set `s` already lies
in the shifted logarithm domain, because the no-pole-on-`[0, ∞)` hypothesis excludes poles on the
shifted branch cut. -/
lemma mem_shiftedLogDomain_of_mem_pole_finset
    {f : ℂ → ℂ} {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ↔ z ∈ s)
    (hcut : ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt f (x : ℂ) < 0)
    {z : ℂ} (hz : z ∈ s) :
    z ∈ shiftedLogDomain := by
  change -z ∈ Complex.slitPlane
  rw [Complex.mem_slitPlane_iff]
  by_cases hz_im : z.im = 0
  · -- On the real axis, the cut hypothesis forces the pole to lie strictly on the negative side.
    have hz_not_nonneg : ¬ 0 ≤ z.re := by
      intro hz_re_nonneg
      have hpole : meromorphicOrderAt f z < 0 := (hpoles z).2 hz
      have hnot_pole : ¬ meromorphicOrderAt f ((z.re : ℂ)) < 0 := hcut z.re hz_re_nonneg
      have hz_eq : z = (z.re : ℂ) := by
        apply Complex.ext <;> simp [hz_im]
      have hpole_real : meromorphicOrderAt f ((z.re : ℂ)) < 0 := by
        rwa [hz_eq] at hpole
      exact hnot_pole hpole_real
    left
    simpa using neg_pos.mpr (lt_of_not_ge hz_not_nonneg)
  · -- Off the real axis, the shifted branch is already regular.
    right
    simpa using hz_im

/-- Helper for Remark III.6-extra-7: the whole pole finset lies in the shifted logarithm domain. -/
lemma pole_finset_subset_shiftedLogDomain
    {f : ℂ → ℂ} {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ↔ z ∈ s)
    (hcut : ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt f (x : ℂ) < 0) :
    (↑s : Set ℂ) ⊆ shiftedLogDomain := by
  intro z hz
  -- Apply the pointwise cut-avoidance lemma pole-by-pole.
  exact mem_shiftedLogDomain_of_mem_pole_finset hpoles hcut hz

/-- Helper for Remark III.6-extra-7: the rational function `P / Q` is meromorphic on the shifted
slit domain because polynomial evaluations are entire and meromorphicity is stable under
division. -/
lemma rationalEval_meromorphicOn_shiftedLogDomain
    (P Q : Polynomial ℂ) :
    MeromorphicOn (rationalEval P Q) shiftedLogDomain := by
  have hPmer_univ : MeromorphicOn (fun w : ℂ ↦ P.eval w) Set.univ := by
    -- Polynomial evaluation is entire, hence meromorphic, on the whole plane.
    simpa [Polynomial.coe_aeval_eq_eval] using
      (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (A := ℂ) P).meromorphicOn
  have hQmer_univ : MeromorphicOn (fun w : ℂ ↦ Q.eval w) Set.univ := by
    -- The same entire-function bridge applies to the denominator polynomial.
    simpa [Polynomial.coe_aeval_eq_eval] using
      (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (A := ℂ) Q).meromorphicOn
  have hrat_univ : MeromorphicOn (rationalEval P Q) Set.univ := by
    -- Meromorphicity is stable under pointwise division.
    simpa [rationalEval] using hPmer_univ.div hQmer_univ
  -- Restrict the global meromorphic statement to the shifted slit domain.
  exact hrat_univ.mono_set (by intro z hz; simp)

/-- Helper for Remark III.6-extra-7: replacing the rational factor by its meromorphic normal form
does not change the local trailing coefficient of the shifted-log integrand at points of the
shifted slit domain. -/
lemma meromorphicTrailingCoeffAt_shiftedLogRationalNormalForm_eq
    (P Q : Polynomial ℂ) {z : ℂ} (hz : z ∈ shiftedLogDomain) :
    meromorphicTrailingCoeffAt (shiftedLogRationalNormalForm P Q) z =
      meromorphicTrailingCoeffAt (shiftedLogRationalEval P Q) z := by
  let f : ℂ → ℂ := rationalEval P Q
  have hmeromorphic : MeromorphicOn f shiftedLogDomain :=
    rationalEval_meromorphicOn_shiftedLogDomain P Q
  apply meromorphicTrailingCoeffAt_congr_nhdsNE
  have hEqNF := hmeromorphic.toMeromorphicNFOn_eq_self_on_nhdsNE hz
  -- Multiplying by the same shifted logarithm preserves punctured-neighborhood equality.
  filter_upwards [hEqNF] with w hw
  rw [shiftedLogRationalNormalForm, shiftedLogRationalEval, hw]

/-- Helper for Remark III.6-extra-7: one isolated source-side local residue circle for the literal
shifted logarithmic integrand transfers unchanged to the shifted meromorphic normal form, because
the two integrands differ only on a codiscrete subset of the admissible circle. The isolation is
part of the input so the source residue really is the residue at the listed pole, not the integral
around a larger circle containing additional poles. -/
lemma shiftedLogRationalNormalForm_localResidueCircle_at
    (P Q : Polynomial ℂ) {s : Finset ℂ} {z residue_z : ℂ}
    (hres :
      IsolatedLocalResidueCircle
        shiftedLogDomain
        shiftedLogDomain
        s
        (shiftedLogRationalEval P Q)
        z
        residue_z) :
    LocalResidueCircle
      shiftedLogDomain
      shiftedLogDomain
      (shiftedLogRationalNormalForm P Q)
      z
      residue_z := by
  let U : Set ℂ := shiftedLogDomain
  have hmeromorphic : MeromorphicOn (rationalEval P Q) U :=
    rationalEval_meromorphicOn_shiftedLogDomain P Q
  rcases hres with ⟨R, hR, hRK, hRD, havoid, hdiff, hcircleR⟩
  refine ⟨R, hR, hRK, hRD, ?_⟩
  let _ := havoid
  let _ := hdiff
  have hsphere_subset : Metric.sphere z |R| ⊆ U := by
    -- The owner closed ball from the source residue circle already contains the boundary sphere.
    intro w hw
    have hw_le : dist w z ≤ R := by
      have hw_eq : dist w z = |R| := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hw
      rw [abs_of_pos hR] at hw_eq
      exact le_of_eq hw_eq
    exact hRD (by simpa [Metric.mem_closedBall] using hw_le)
  have hEq :
      shiftedLogRationalNormalForm P Q =ᶠ[Filter.codiscreteWithin (Metric.sphere z |R|)]
        shiftedLogRationalEval P Q := by
    have hEqNF :
        (fun w ↦ toMeromorphicNFOn (rationalEval P Q) U w)
          =ᶠ[Filter.codiscreteWithin (Metric.sphere z |R|)]
        rationalEval P Q := by
      exact
        (toMeromorphicNFOn_eqOn_codiscrete (U := U) hmeromorphic).symm.filter_mono
          (Filter.codiscreteWithin_mono hsphere_subset)
    -- Multiply the codiscrete equality for the rational factor by the common shifted logarithm.
    filter_upwards [hEqNF] with w hw
    rw [shiftedLogRationalNormalForm, shiftedLogRationalEval, hw]
  -- The circle integral does not see codiscrete modifications of the integrand.
  calc
    (∮ w in C(z, R), shiftedLogRationalNormalForm P Q w) =
        ∮ w in C(z, R), shiftedLogRationalEval P Q w := by
          exact circleIntegral.circleIntegral_congr_codiscreteWithin hEq hR.ne'
    _ = (2 * Real.pi * Complex.I : ℂ) * residue_z := hcircleR

/-- Helper for Remark III.6-extra-7: the full finite family of isolated source-side local residue
circles transfers pointwise to the shifted meromorphic normal form. -/
lemma shiftedLogRationalNormalForm_localResidueCircle
    (P Q : Polynomial ℂ) {s : Finset ℂ} (residue : ℂ → ℂ)
    (hresidue :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          shiftedLogDomain
          shiftedLogDomain
          s
          (shiftedLogRationalEval P Q)
          z
          (residue z)) :
    ∀ z ∈ s,
      LocalResidueCircle
        shiftedLogDomain
        shiftedLogDomain
        (shiftedLogRationalNormalForm P Q)
        z
        (residue z) := by
  intro z hz
  -- Reduce the family statement to the pointwise codiscrete-transfer lemma.
  exact shiftedLogRationalNormalForm_localResidueCircle_at P Q (hresidue z hz)

/-- Helper for Remark III.6-extra-7: at any point of the shifted slit domain away from the pole
finset `s`, the shifted logarithmic meromorphic normal form is differentiable on the punctured
domain `shiftedLogDomain \ s`. This isolates the pointwise holomorphy input needed by the
isolated-residue transfer before the later global `DifferentiableOn` packaging. -/
lemma shiftedLogRationalNF_differentiableWithinAt_shiftedLogDomain_off_poles
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0) {s : Finset ℂ}
    (hpoles' : ∀ z : ℂ, meromorphicOrderAt (rationalEval P Q) z < 0 ↔ z ∈ s)
    {z : ℂ} (hz : z ∈ shiftedLogDomain \ (↑s : Set ℂ)) :
    DifferentiableWithinAt ℂ
      (shiftedLogRationalNormalForm P Q)
      (shiftedLogDomain \ (↑s : Set ℂ))
      z := by
  let f : ℂ → ℂ := rationalEval P Q
  let _ := hQ
  have hmeromorphic : MeromorphicOn f shiftedLogDomain :=
    rationalEval_meromorphicOn_shiftedLogDomain P Q
  have horder_nonneg_f : 0 ≤ meromorphicOrderAt f z := by
    -- Outside the pole finset, the local meromorphic order cannot be negative.
    by_contra hneg
    exact hz.2 ((hpoles' z).1 (lt_of_not_ge hneg))
  have horder_nonneg_nf :
      0 ≤ meromorphicOrderAt (toMeromorphicNFOn f shiftedLogDomain) z := by
    -- Passing to normal form preserves the local meromorphic order on the domain.
    rw [meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := shiftedLogDomain) hmeromorphic hz.1]
    exact horder_nonneg_f
  have hNF : MeromorphicNFAt (toMeromorphicNFOn f shiftedLogDomain) z :=
    (meromorphicNFOn_toMeromorphicNFOn f shiftedLogDomain) hz.1
  have hnf_diff : DifferentiableAt ℂ (fun w ↦ toMeromorphicNFOn f shiftedLogDomain w) z := by
    -- The normal-form factor is analytic, hence differentiable, at every non-pole point.
    exact
      (hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 horder_nonneg_nf).differentiableAt
  have hlog_diff : DifferentiableAt ℂ (fun w : ℂ ↦ Complex.log (-w)) z := by
    -- The shifted branch of the logarithm is holomorphic on `shiftedLogDomain`.
    simpa using (differentiableAt_id.neg.clog hz.1)
  -- Multiply the two holomorphic factors to recover the corrected integrand.
  simpa [shiftedLogRationalNormalForm, f] using
    (hnf_diff.mul hlog_diff).differentiableWithinAt

/-- Helper for Remark III.6-extra-7: one isolated source-side local residue circle for the literal
shifted logarithmic integrand stays isolated after replacing the rational factor by its
meromorphic normal form. The owner and separation data are unchanged; only the circle integral
uses the codiscrete normal-form comparison. -/
lemma shiftedLogRationalNormalForm_isolatedLocalResidueCircle_at
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0) {s : Finset ℂ}
    (hpoles' : ∀ w : ℂ, meromorphicOrderAt (rationalEval P Q) w < 0 ↔ w ∈ s)
    {z residue_z : ℂ}
    (hres :
      IsolatedLocalResidueCircle
        shiftedLogDomain
        shiftedLogDomain
        s
        (shiftedLogRationalEval P Q)
        z
        residue_z) :
    IsolatedLocalResidueCircle
      shiftedLogDomain
      shiftedLogDomain
      s
      (shiftedLogRationalNormalForm P Q)
      z
      residue_z := by
  let U : Set ℂ := shiftedLogDomain
  let f : ℂ → ℂ := rationalEval P Q
  have hmeromorphic : MeromorphicOn f U :=
    rationalEval_meromorphicOn_shiftedLogDomain P Q
  rcases hres with ⟨R, hR, hRK, hRD, havoid, hdiff, hcircleR⟩
  refine ⟨R, hR, hRK, hRD, havoid, ?_, ?_⟩
  · have hNFdiff :
        DifferentiableOn ℂ (shiftedLogRationalNormalForm P Q) (U \ (↑s : Set ℂ)) :=
      fun w hw ↦
        shiftedLogRationalNF_differentiableWithinAt_shiftedLogDomain_off_poles
          P Q hQ hpoles' hw
    -- Rebuild the punctured-ball holomorphy field by showing the source punctured ball avoids
    -- every pole in `s` except the center `z`, which has already been removed.
    refine hNFdiff.mono ?_
    intro w hw
    refine ⟨hRD ?_, ?_⟩
    · rw [Metric.mem_closedBall]
      exact le_of_lt <| by simpa [Metric.mem_ball] using hw.1
    · intro hwS
      have hwne : w ≠ z := by
        simpa using hw.2
      have hwBall : w ∈ Metric.closedBall z R := by
        rw [Metric.mem_closedBall]
        exact le_of_lt <| by simpa [Metric.mem_ball] using hw.1
      exact havoid w hwS hwne hwBall
  · have hsphere_subset : Metric.sphere z |R| ⊆ U := by
      -- The owner closed ball from the source residue circle already contains the boundary sphere.
      intro w hw
      have hw_le : dist w z ≤ R := by
        have hw_eq : dist w z = |R| := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hw
        rw [abs_of_pos hR] at hw_eq
        exact le_of_eq hw_eq
      exact hRD (by simpa [Metric.mem_closedBall] using hw_le)
    have hEq :
        shiftedLogRationalNormalForm P Q =ᶠ[Filter.codiscreteWithin (Metric.sphere z |R|)]
          shiftedLogRationalEval P Q := by
      have hEqNF :
          (fun w ↦ toMeromorphicNFOn f U w)
            =ᶠ[Filter.codiscreteWithin (Metric.sphere z |R|)]
          f := by
        exact
          (toMeromorphicNFOn_eqOn_codiscrete (U := U) hmeromorphic).symm.filter_mono
            (Filter.codiscreteWithin_mono hsphere_subset)
      -- Multiply the codiscrete equality for the rational factor by the common shifted logarithm.
      filter_upwards [hEqNF] with w hw
      rw [shiftedLogRationalNormalForm, shiftedLogRationalEval, hw]
    -- The same codiscrete comparison transfers the exact residue-circle integral.
    calc
      (∮ w in C(z, R), shiftedLogRationalNormalForm P Q w) =
          ∮ w in C(z, R), shiftedLogRationalEval P Q w := by
            exact circleIntegral.circleIntegral_congr_codiscreteWithin hEq hR.ne'
      _ = (2 * Real.pi * Complex.I : ℂ) * residue_z := hcircleR

/-- Helper for Remark III.6-extra-7: the full finite family of isolated source-side local residue
circles transfers pointwise to the shifted meromorphic normal form without changing the owner or
the finite singular set. -/
lemma shiftedLogRationalNormalForm_isolatedLocalResidueCircle
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0) {s : Finset ℂ}
    (hpoles' : ∀ w : ℂ, meromorphicOrderAt (rationalEval P Q) w < 0 ↔ w ∈ s)
    (residue : ℂ → ℂ)
    (hresidue :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          shiftedLogDomain
          shiftedLogDomain
          s
          (shiftedLogRationalEval P Q)
          z
          (residue z)) :
    ∀ z ∈ s,
      IsolatedLocalResidueCircle
        shiftedLogDomain
        shiftedLogDomain
        s
      (shiftedLogRationalNormalForm P Q)
      z
      (residue z) := by
  intro z hz
  -- Reduce the family statement to the pointwise isolated transfer lemma with the global pole API.
  exact
    shiftedLogRationalNormalForm_isolatedLocalResidueCircle_at
      P Q hQ hpoles' (hresidue z hz)

/-- Helper for Remark III.6-extra-7: away from the denominator roots, the rational factor and the
shifted logarithm are both holomorphic on the shifted slit plane, hence so is their product. -/
lemma shiftedLogRationalEval_differentiableOn_shiftedLogDomain_off_roots
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    DifferentiableOn ℂ (shiftedLogRationalEval P Q)
      (shiftedLogDomain \ (↑(Q.roots.toFinset) : Set ℂ)) := by
  intro z hz
  -- Excluding denominator roots gives a genuine quotient-holomorphy statement for
  -- `P.eval / Q.eval`.
  have hQeval : Q.eval z ≠ 0 := by
    intro hzero
    exact hz.2 (Multiset.mem_toFinset.2 ((Polynomial.mem_roots hQ).2 hzero))
  have hrat : DifferentiableAt ℂ (rationalEval P Q) z := by
    simpa [rationalEval] using (P.differentiableAt.div Q.differentiableAt hQeval)
  have hlog : DifferentiableAt ℂ (fun w : ℂ ↦ Complex.log (-w)) z := by
    -- The shifted branch is just `Complex.log` composed with negation.
    simpa using (differentiableAt_id.neg.clog hz.1)
  exact (hrat.mul hlog).differentiableWithinAt

/-- Helper for Remark III.6-extra-7: removing the pole set `s` in addition to the denominator roots
only shrinks the holomorphy domain, so the shifted-log rational integrand remains differentiable on
that smaller set. -/
lemma shiftedLogRationalEval_differentiableOn_shiftedLogDomain_off_poles_and_roots
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0) (s : Finset ℂ) :
    DifferentiableOn ℂ (shiftedLogRationalEval P Q)
      (shiftedLogDomain \ (↑(s ∪ Q.roots.toFinset) : Set ℂ)) := by
  have hbase :
      DifferentiableOn ℂ (shiftedLogRationalEval P Q)
        (shiftedLogDomain \ (↑(Q.roots.toFinset) : Set ℂ)) :=
    shiftedLogRationalEval_differentiableOn_shiftedLogDomain_off_roots P Q hQ
  -- The residue theorem later works on the smaller excision set `s ∪ Q.roots.toFinset`.
  refine hbase.mono ?_
  intro z hz
  refine ⟨hz.1, ?_⟩
  intro hzroot
  exact hz.2 (Finset.mem_union.mpr (Or.inr hzroot))

/-- Helper for Remark III.6-extra-7: after replacing the raw rational factor by its meromorphic
normal form on the shifted slit domain, the shifted-log integrand is holomorphic away from the
pole finset `s`. This is the source-faithful correction for removable denominator roots. -/
lemma shiftedLogRationalNF_differentiableOn_shiftedLogDomain_off_poles
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0) {s : Finset ℂ}
    (hpoles' : ∀ z : ℂ, meromorphicOrderAt (rationalEval P Q) z < 0 ↔ z ∈ s) :
    DifferentiableOn ℂ
      (shiftedLogRationalNormalForm P Q)
      (shiftedLogDomain \ (↑s : Set ℂ)) := by
  intro z hz
  -- Package the earlier pointwise holomorphy bridge as the requested `DifferentiableOn` fact.
  exact
    shiftedLogRationalNF_differentiableWithinAt_shiftedLogDomain_off_poles
      P Q hQ hpoles' hz

/-- Helper for Remark III.6-extra-7: the degree-gap hypothesis already rules out the zero
denominator polynomial. -/
lemma denominator_ne_zero_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    Q ≠ 0 := by
  -- If `Q = 0`, then `Q.natDegree = 0`, contradicting `P.natDegree + 2 ≤ Q.natDegree`.
  intro hQ
  subst hQ
  simp at hdeg

/-- Helper for Remark III.6-extra-7: multiplying the denominator by `X^2` keeps it nonzero, which
is the algebraic input for the later asymptotic comparison. -/
lemma denominator_mul_X_sq_ne_zero_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    Q * Polynomial.X ^ 2 ≠ 0 := by
  -- The degree-gap step first produces `Q ≠ 0`; the polynomial `X^2` is nonzero as well.
  exact mul_ne_zero
    (denominator_ne_zero_of_degree_gap_two P Q hdeg)
    (pow_ne_zero 2 Polynomial.X_ne_zero)

/-- Helper for Remark III.6-extra-7: multiplying the numerator by `X^2` matches the source outer-
arc quantity `z^2 * (P(z) / Q(z))`, and the degree-gap hypothesis says that this corrected
numerator has degree at most the denominator degree. -/
lemma numerator_mul_X_sq_natDegree_le_denominator_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    (P * Polynomial.X ^ 2).natDegree ≤ Q.natDegree := by
  by_cases hP : P = 0
  · -- If the numerator is zero, the corrected numerator is zero as well, so the bound is trivial.
    subst hP
    simp
  · -- Otherwise `natDegree_mul_X_pow` turns the claim into the given arithmetic degree gap.
    simpa [Polynomial.natDegree_mul_X_pow (n := 2) hP] using hdeg

/-- Helper for Remark III.6-extra-7: the corrected cobounded polynomial comparison is between
`(P * X^2).eval` and `Q.eval`, because this is the algebraic form of bounding `z^2 * R(z)` on the
outer circle. -/
lemma numerator_mul_X_sq_isBigO_denominator_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    (fun z ↦ (P * Polynomial.X ^ 2).eval z) =O[cobounded ℂ] Q.eval := by
  by_cases hP : P = 0
  · -- The zero numerator is bounded by everything, so the Big-O statement is immediate.
    simpa [hP] using Asymptotics.isBigO_zero Q.eval (cobounded ℂ)
  · -- Convert the corrected nat-degree comparison into the degree inequality required by mathlib.
    have hQ : Q ≠ 0 := denominator_ne_zero_of_degree_gap_two P Q hdeg
    have hdeg' : (P * Polynomial.X ^ 2).degree ≤ Q.degree := by
      rw [Polynomial.degree_eq_natDegree (mul_ne_zero hP (pow_ne_zero 2 Polynomial.X_ne_zero)),
        Polynomial.degree_eq_natDegree hQ]
      exact_mod_cast numerator_mul_X_sq_natDegree_le_denominator_of_degree_gap_two P Q hdeg
    simpa using
      (Polynomial.isBigO_cobounded_of_degree_le
        (P := P * Polynomial.X ^ 2) (Q := Q) hdeg')

/-- Helper for Remark III.6-extra-7: a bound of the form `‖a‖ ≤ K * ‖b‖` gives the corresponding
uniform estimate `‖a / b‖ ≤ K`. -/
lemma norm_div_le_of_norm_le_mul {a b : ℂ} {K : ℝ}
    (hK : 0 ≤ K) (hab : ‖a‖ ≤ K * ‖b‖) :
    ‖a / b‖ ≤ K := by
  by_cases hb : b = 0
  · -- If the denominator vanishes, complex division is defined as `0`, so only `0 ≤ K` remains.
    subst hb
    simpa using hK
  · -- Otherwise divide the norm inequality by the positive scalar `‖b‖`.
    rw [norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr hb)).2 <| by simpa [mul_comm] using hab

/-- Helper for Remark III.6-extra-7: the corrected rational quantity `z^2 * R(z)` stays uniformly
bounded outside a sufficiently large disk when `deg Q ≥ deg P + 2`. -/
lemma rationalEval_mul_sq_eventually_bounded
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ K R : ℝ, 0 < min K R ∧
      ∀ z : ℂ, R ≤ ‖z‖ → ‖(z ^ 2 : ℂ) * rationalEval P Q z‖ ≤ K := by
  obtain ⟨K, hKpos, hKbound⟩ :=
    Asymptotics.isBigO_iff'.mp
      (numerator_mul_X_sq_isBigO_denominator_of_degree_gap_two P Q hdeg)
  have hbounded :
      ∀ᶠ z in cobounded ℂ, ‖(z ^ 2 : ℂ) * rationalEval P Q z‖ ≤ K := by
    -- Route correction: bound the source-faithful object `z^2 * R(z)` directly, rather than a
    -- later outer-arc specialization.
    filter_upwards [hKbound] with z hz
    have hquot :
        ‖((P * Polynomial.X ^ 2).eval z) / Q.eval z‖ ≤ K :=
      norm_div_le_of_norm_le_mul hKpos.le hz
    have hnorm :
        ‖z‖ ^ (2 : ℕ) * (‖P.eval z‖ / ‖Q.eval z‖) ≤ K := by
      calc
        ‖z‖ ^ (2 : ℕ) * (‖P.eval z‖ / ‖Q.eval z‖)
            = ‖P.eval z‖ * ‖z‖ ^ (2 : ℕ) / ‖Q.eval z‖ := by
                rw [div_eq_mul_inv, div_eq_mul_inv]
                ring_nf
        _ ≤ K := by
              simpa [rationalEval, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
                norm_div, norm_mul, norm_pow, mul_comm, mul_left_comm, mul_assoc] using hquot
    calc
      ‖(z ^ 2 : ℂ) * rationalEval P Q z‖
          = ‖z‖ ^ (2 : ℕ) * (‖P.eval z‖ / ‖Q.eval z‖) := by
              rw [rationalEval, norm_mul, norm_div, norm_pow]
      _ ≤ K := hnorm
  rcases Filter.hasBasis_cobounded_norm.eventually_iff.mp hbounded with ⟨R₀, -, hR₀⟩
  refine ⟨K, max R₀ 1, ?_, ?_⟩
  · -- Enlarge the eventual radius so the final decay estimate stays away from `0`.
    refine lt_min hKpos ?_
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  · intro z hz
    -- Any point outside the larger radius still lies in the original eventual region.
    exact hR₀ <| by
      simpa using (le_trans (le_max_left _ _) hz)

/-- Helper for Remark III.6-extra-7: once `‖z‖` is bounded away from `0`, a bound on
`‖z^2 * R(z)‖` converts into the expected `‖R(z)‖ ≤ K / ‖z‖^2` decay. -/
lemma decay_of_mul_sq_bound {R K : ℝ} {z w : ℂ}
    (hR : 0 < R) (hz : R ≤ ‖z‖) (hbound : ‖(z ^ 2 : ℂ) * w‖ ≤ K) :
    ‖w‖ ≤ K / ‖z‖ ^ (2 : ℕ) := by
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hR hz
  have hzsqpos : 0 < ‖z‖ ^ (2 : ℕ) := by
    exact pow_pos hzpos 2
  -- Rewrite the corrected norm as `‖w‖ * ‖z‖^2` and divide by the positive square norm.
  refine (le_div_iff₀ hzsqpos).2 ?_
  calc
    ‖w‖ * ‖z‖ ^ (2 : ℕ) = ‖(z ^ 2 : ℂ) * w‖ := by
      rw [norm_mul, norm_pow, mul_comm]
    _ ≤ K := hbound

/-- Helper for Remark III.6-extra-7: the degree-gap hypothesis gives the standard quadratic decay
estimate `‖R(z)‖ = O(‖z‖⁻²)` for the rational function `R(z) = P(z) / Q(z)`. -/
lemma rationalEval_decay_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ K R : ℝ, 0 < min K R ∧
      ∀ z : ℂ, R ≤ ‖z‖ → ‖rationalEval P Q z‖ ≤ K / ‖z‖ ^ (2 : ℕ) := by
  obtain ⟨K, R, hKR, hbounded⟩ := rationalEval_mul_sq_eventually_bounded P Q hdeg
  refine ⟨K, R, hKR, ?_⟩
  intro z hz
  have hR : 0 < R := (lt_min_iff.mp hKR).2
  -- First bound `z^2 * R(z)` uniformly, then divide by `‖z‖^2`.
  exact decay_of_mul_sq_bound hR hz (hbounded z hz)

/-- Helper for Remark III.6-extra-7: the degree gap is exactly the strict inequality needed to
compare `P` with `Q * X^2` in the cobounded polynomial asymptotics route. -/
lemma natDegree_lt_denominator_mul_X_sq_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    P.natDegree < (Q * Polynomial.X ^ 2).natDegree := by
  -- Rewrite the target degree through `natDegree_mul_X_pow` and discharge the arithmetic gap.
  have hQne : Q ≠ 0 := denominator_ne_zero_of_degree_gap_two P Q hdeg
  have hlt : P.natDegree < Q.natDegree + 2 := by
    omega
  simpa [Polynomial.natDegree_mul_X_pow (n := 2) hQne] using hlt

/-- Helper for Remark III.6-extra-7: the negative real point on the outer circle survives the
positive-axis slit and therefore still lies on the frontier of the slit annulus. This is the
geometric witness that the owner frontier contains the major arc around angle `π`. -/
lemma positiveAxisWedgeAnnulus_negative_real_frontier_point
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    circleMap 0 R Real.pi ∈ frontier (positiveAxisWedgeAnnulus R ε) := by
  have hR : 0 < R := lt_trans hε hεR
  have hclosedAnnulusEq :
      {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} =
        Metric.closedBall (0 : ℂ) R \ Metric.ball (0 : ℂ) ε := by
    -- Rewrite the closed annulus in the metric `closedBall \ ball` form used by the frontier API.
    ext z
    simp [Metric.mem_closedBall, Metric.mem_ball, dist_eq_norm, sub_zero, not_lt, and_comm,
      and_left_comm, and_assoc]
  have hball :
      Metric.closedBall (0 : ℂ) ε ⊆ interior (Metric.closedBall (0 : ℂ) R) := by
    intro z hz
    have hz_norm : ‖z‖ ≤ ε := by
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz
    -- Every point with norm at most `ε` lies strictly inside the larger closed ball of radius `R`.
    refine Metric.ball_subset_interior_closedBall ?_
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact lt_of_le_of_lt hz_norm hεR
  have hfrontierAnnulus :
      circleMap 0 R Real.pi ∈ frontier ({z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R}) := by
    rw [hclosedAnnulusEq]
    -- The negative real point lies on the outer boundary sphere of the annulus.
    rw [frontier_diff_ball_eq_of_closedBall_subset_interior
      (a := (0 : ℂ)) (r := ε) hε Metric.isClosed_closedBall hball]
    left
    rw [frontier_closedBall' (0 : ℂ) R]
    simpa [Metric.mem_sphere, dist_eq_norm, norm_circleMap_zero, abs_of_pos hR]
  have hwedge :
      circleMap 0 R Real.pi ∉ positiveAxisWedge R ε := by
    intro hwedge
    rw [positiveAxisWedge] at hwedge
    have hre_nonpos : (circleMap 0 R Real.pi).re ≤ 0 := by
      simp [circleMap_zero_re, Real.cos_pi, hR.le]
    -- The removed wedge only lives on the positive-real side, so the negative-real point survives.
    exact (not_lt_of_ge hre_nonpos hwedge.1).elim
  -- Split the slit-annulus frontier into the surviving annulus frontier and the slit-boundary
  -- frontier, then place the negative-real point in the surviving outer-circle branch.
  rw [positiveAxisWedgeAnnulus,
    frontier_diff_open_of_isClosed
      (A := {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R})
      (W := positiveAxisWedge R ε)
      (by
        simpa [Set.setOf_and] using
          (isClosed_le continuous_const continuous_norm).inter
            (isClosed_le continuous_norm continuous_const))
      (isOpen_positiveAxisWedge R ε)]
  exact Or.inl ⟨hfrontierAnnulus, hwedge⟩

/-- Helper for Remark III.6-extra-7: the current local `positiveAxisKeyhole` does not pass
through the negative-real outer point. This records in Lean the contour/API drift that blocks the
frontier owner theorem until the major-arc contour is repaired. -/
lemma positiveAxisKeyhole_negative_real_point_not_mem_range
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    circleMap 0 R Real.pi ∉ Set.range (positiveAxisKeyhole R ε) := by
  have hR : 0 < R := lt_trans hε hεR
  have hθ :
      0 < positiveAxisKeyholeAngle R ε ∧ positiveAxisKeyholeAngle R ε < Real.pi / 2 :=
    positiveAxisKeyhole_angle_bounds (R := R) (ε := ε) hε hεR
  rw [positiveAxisKeyhole_range_eq_geometric_piece_union]
  intro hz
  simp only [Set.mem_union, Set.mem_image] at hz
  rcases hz with hz | hz
  · rcases hz with hz | hz
    · rcases hz with hz | hz
      · rcases hz with ⟨ρ, hρ, hEq⟩
        have hρIcc : ρ ∈ Set.Icc ε R := by
          simpa [Set.uIcc, min_eq_right (le_of_lt hεR), max_eq_left (le_of_lt hεR)] using hρ
        have hρpos : 0 < ρ := lt_of_lt_of_le hε hρIcc.1
        have hre_pos : 0 < (circleMap 0 ρ (positiveAxisKeyholeAngle R ε)).re :=
          positiveAxisKeyhole_upper_lip_re_pos (R := R) (ε := ε) (ρ := ρ) hρpos
        have hre_target : (circleMap 0 R Real.pi).re < 0 := by
          simp [circleMap_zero_re, Real.cos_pi, hR]
        have hre_eq :
            (circleMap 0 ρ (positiveAxisKeyholeAngle R ε)).re =
              (circleMap 0 R Real.pi).re := congrArg Complex.re hEq
        linarith
      · rcases hz with ⟨α, hα, hEq⟩
        have hnorm : ε = R := by
          have := congrArg norm hEq
          have hnorm_eq : ε = |R| := by
            simpa [norm_circleMap_zero, abs_of_pos hε] using this
          rwa [abs_of_pos hR] at hnorm_eq
        linarith
    · rcases hz with ⟨ρ, hρ, hEq⟩
      have hρIcc : ρ ∈ Set.Icc ε R := by
        simpa [Set.uIcc, min_eq_left (le_of_lt hεR), max_eq_right (le_of_lt hεR)] using hρ
      have hρpos : 0 < ρ := lt_of_lt_of_le hε hρIcc.1
      have hre_pos : 0 < (circleMap 0 ρ (-positiveAxisKeyholeAngle R ε)).re :=
        positiveAxisKeyhole_lower_lip_re_pos (R := R) (ε := ε) (ρ := ρ) hρpos
      have hre_target : (circleMap 0 R Real.pi).re < 0 := by
        simp [circleMap_zero_re, Real.cos_pi, hR]
      have hre_eq :
          (circleMap 0 ρ (-positiveAxisKeyholeAngle R ε)).re =
            (circleMap 0 R Real.pi).re := congrArg Complex.re hEq
      linarith
  · rcases hz with ⟨α, hα, hEq⟩
    have hφIcc :
        α ∈ Set.Icc (-positiveAxisKeyholeAngle R ε) (positiveAxisKeyholeAngle R ε) := by
      have hθle : -positiveAxisKeyholeAngle R ε ≤ positiveAxisKeyholeAngle R ε := by
        linarith [hθ.1]
      simpa [Set.uIcc, min_eq_left hθle, max_eq_right hθle] using hα
    have hφIoo : α ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      -- The short outer arc only sees angles strictly between `-π/2` and `π/2`, so its real
      -- part stays positive and cannot reach the negative real axis.
      refine ⟨?_, ?_⟩ <;> linarith [hφIcc.1, hφIcc.2, hθ.2]
    have hcos_pos : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo hφIoo
    have hre_pos : 0 < (circleMap 0 R α).re := by
      rw [circleMap_zero_re]
      exact mul_pos hR hcos_pos
    have hre_target : (circleMap 0 R Real.pi).re < 0 := by
      simp [circleMap_zero_re, Real.cos_pi, hR]
    have hre_eq :
        (circleMap 0 R α).re = (circleMap 0 R Real.pi).re := congrArg Complex.re hEq
    linarith

/-- Helper for Remark III.6-extra-7: the present contour and owner APIs do not yet match. The
frontier contains a negative-real outer point that the current short-arc keyhole misses, so the
frontier theorem must wait for the major-arc contour repair from the source proof. -/
lemma positiveAxisWedgeAnnulus_frontier_range_mismatch
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    frontier (positiveAxisWedgeAnnulus R ε) ≠ Set.range (positiveAxisKeyhole R ε) := by
  intro hEq
  have hfront :
      circleMap 0 R Real.pi ∈ frontier (positiveAxisWedgeAnnulus R ε) :=
    positiveAxisWedgeAnnulus_negative_real_frontier_point hε hεR
  have hrange :
      circleMap 0 R Real.pi ∈ Set.range (positiveAxisKeyhole R ε) := by
    simpa [hEq] using hfront
  exact positiveAxisKeyhole_negative_real_point_not_mem_range hε hεR hrange

/-- Helper for Remark III.6-extra-7: the frontier of the positive-axis slit annulus is exactly
the range of the explicit positive-axis keyhole contour. This is the source-faithful rewrite
bridge from the geometric owner to the contour owner. -/
theorem positiveAxisWedgeAnnulus_frontier_eq_range
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    frontier (positiveAxisWedgeAnnulus R ε) = Set.range (positiveAxisKeyhole R ε) := by
  -- Route correction: the current contour still follows the short inner/outer arcs through angle
  -- `0`, so the stated equality is false for the present local API; see
  -- `positiveAxisWedgeAnnulus_frontier_range_mismatch`. The next proof step is to repair
  -- `positiveAxisKeyhole` to the surviving major-arc contour from the source proof, then rerun the
  -- frontier split against the corrected geometric range lemma.
  -- TODO: after the contour repair, split the positive-axis slit annulus frontier into the
  -- surviving circles and the two slit lips, then identify that union with the repaired
  -- `positiveAxisKeyhole_range_eq_geometric_piece_union`.
  sorry

/-- Helper for Remark III.6-extra-7: equality on one open branch of the positive-axis keyhole
forces equality of the corresponding parameters. This isolates the branchwise injectivity package
needed later by the simple-loop proof from the breakpoint bookkeeping. -/
lemma positiveAxisKeyhole_same_branch_injective
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {s t : I}
    (hbranch :
      (s.1 ∈ Set.Ioo (0 : ℝ) (1 / 8) ∧ t.1 ∈ Set.Ioo (0 : ℝ) (1 / 8)) ∨
        (s.1 ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4) ∧ t.1 ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4)) ∨
        (s.1 ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∧ t.1 ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)) ∨
        (s.1 ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ) ∧ t.1 ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ)))
    (hst : positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t) :
    s = t := by
  have hR : 0 < R := lt_trans hε hεR
  have hθ := positiveAxisKeyhole_angle_bounds (R := R) (ε := ε) hε hεR
  rcases hbranch with hupper | hinner | hlower | houter
  · rcases hupper with ⟨hs, ht⟩
    -- On the upper lip, the keyhole is a nonconstant affine interpolation in the radius.
    have hsPath :
        positiveAxisKeyhole R ε s =
          AffineMap.lineMap
            (circleMap 0 R (positiveAxisKeyholeAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
            (8 * (s : ℝ)) := by
      exact (Path.extend_apply (positiveAxisKeyhole R ε) s.2).symm.trans <|
        positive_axis_keyhole_eq_on_upper_lip R ε (Set.Ioo_subset_Icc_self hs)
    have htPath :
        positiveAxisKeyhole R ε t =
          AffineMap.lineMap
            (circleMap 0 R (positiveAxisKeyholeAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
            (8 * (t : ℝ)) := by
      exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
        positive_axis_keyhole_eq_on_upper_lip R ε (Set.Ioo_subset_Icc_self ht)
    have hparam :
        AffineMap.lineMap
            (circleMap 0 R (positiveAxisKeyholeAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
            (8 * (s : ℝ)) =
          AffineMap.lineMap
            (circleMap 0 R (positiveAxisKeyholeAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
            (8 * (t : ℝ)) := by
      calc
        AffineMap.lineMap
            (circleMap 0 R (positiveAxisKeyholeAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
            (8 * (s : ℝ)) =
            positiveAxisKeyhole R ε s := hsPath.symm
        _ = positiveAxisKeyhole R ε t := hst
        _ =
            AffineMap.lineMap
              (circleMap 0 R (positiveAxisKeyholeAngle R ε))
              (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
              (8 * (t : ℝ)) := htPath
    have hEndsNe :
        circleMap 0 R (positiveAxisKeyholeAngle R ε) ≠
          circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
      intro hEq
      have hnorm := congrArg norm hEq
      simp [norm_circleMap_zero, abs_of_pos hR, abs_of_pos hε] at hnorm
      linarith
    have hst' : 8 * (s : ℝ) = 8 * (t : ℝ) := by
      rcases (AffineMap.lineMap_eq_lineMap_iff
        (p₀ := circleMap 0 R (positiveAxisKeyholeAngle R ε))
        (p₁ := circleMap 0 ε (positiveAxisKeyholeAngle R ε))
        (c₁ := 8 * (s : ℝ)) (c₂ := 8 * (t : ℝ))).mp hparam with hEq | hEq
      · exact (hEndsNe hEq).elim
      · exact hEq
    -- Recover the subtype equality from the affine radial parameter.
    exact Subtype.ext (by linarith)
  · rcases hinner with ⟨hs, ht⟩
    let α : ℝ :=
      AffineMap.lineMap
        (positiveAxisKeyholeAngle R ε)
        (-positiveAxisKeyholeAngle R ε)
        (8 * (s : ℝ) - 1)
    let β : ℝ :=
      AffineMap.lineMap
        (positiveAxisKeyholeAngle R ε)
        (-positiveAxisKeyholeAngle R ε)
        (8 * (t : ℝ) - 1)
    -- On the inner circle, injectivity comes from the angular window of length `< 2π`.
    have hsPath : positiveAxisKeyhole R ε s = circleMap 0 ε α := by
      exact (Path.extend_apply (positiveAxisKeyhole R ε) s.2).symm.trans <|
        positive_axis_keyhole_eq_on_inner_arc R ε (Set.Ioo_subset_Icc_self hs)
    have htPath : positiveAxisKeyhole R ε t = circleMap 0 ε β := by
      exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
        positive_axis_keyhole_eq_on_inner_arc R ε (Set.Ioo_subset_Icc_self ht)
    have hcircle : circleMap 0 ε α = circleMap 0 ε β := by
      calc
        circleMap 0 ε α = positiveAxisKeyhole R ε s := hsPath.symm
        _ = positiveAxisKeyhole R ε t := hst
        _ = circleMap 0 ε β := htPath
    have hsParam : 8 * (s : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hs.1, hs.2]
    have htParam : 8 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have hAngleOrder :
        -positiveAxisKeyholeAngle R ε < positiveAxisKeyholeAngle R ε := by
      nlinarith [hθ.1, Real.pi_pos]
    have hAnglesNe :
        positiveAxisKeyholeAngle R ε ≠ -positiveAxisKeyholeAngle R ε := by
      nlinarith [hθ.1, Real.pi_pos]
    have hαmemOpen :
        α ∈ openSegment ℝ
          (positiveAxisKeyholeAngle R ε)
          (-positiveAxisKeyholeAngle R ε) := by
      simpa [α] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (positiveAxisKeyholeAngle R ε)
          (-positiveAxisKeyholeAngle R ε)
          hsParam
    have hβmemOpen :
        β ∈ openSegment ℝ
          (positiveAxisKeyholeAngle R ε)
          (-positiveAxisKeyholeAngle R ε) := by
      simpa [β] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (positiveAxisKeyholeAngle R ε)
          (-positiveAxisKeyholeAngle R ε)
          htParam
    have hαmemIoo :
        α ∈ Set.Ioo
          (-positiveAxisKeyholeAngle R ε)
          (positiveAxisKeyholeAngle R ε) := by
      rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hαmemOpen
      simpa [min_eq_right hAngleOrder.le, max_eq_left hAngleOrder.le] using hαmemOpen
    have hβmemIoo :
        β ∈ Set.Ioo
          (-positiveAxisKeyholeAngle R ε)
          (positiveAxisKeyholeAngle R ε) := by
      rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hβmemOpen
      simpa [min_eq_right hAngleOrder.le, max_eq_left hAngleOrder.le] using hβmemOpen
    have hαmem :
        α ∈ Set.uIoc
          (positiveAxisKeyholeAngle R ε)
          (-positiveAxisKeyholeAngle R ε) := by
      rw [Set.uIoc_of_ge hAngleOrder.le]
      exact Set.Ioo_subset_Ioc_self hαmemIoo
    have hβmem :
        β ∈ Set.uIoc
          (positiveAxisKeyholeAngle R ε)
          (-positiveAxisKeyholeAngle R ε) := by
      rw [Set.uIoc_of_ge hAngleOrder.le]
      exact Set.Ioo_subset_Ioc_self hβmemIoo
    have hlen :
        |positiveAxisKeyholeAngle R ε - (-positiveAxisKeyholeAngle R ε)| ≤ 2 * Real.pi := by
      have hnonneg :
          0 ≤ positiveAxisKeyholeAngle R ε - (-positiveAxisKeyholeAngle R ε) := by
        nlinarith [hθ.1, Real.pi_pos]
      rw [abs_of_nonneg hnonneg]
      nlinarith [hθ.2, Real.pi_pos]
    have hinj :=
      injOn_circleMap_of_abs_sub_le
        (c := 0) (R := ε)
        (a := positiveAxisKeyholeAngle R ε)
        (b := -positiveAxisKeyholeAngle R ε)
        (by linarith : ε ≠ 0) hlen
    have hαβ : α = β := hinj hαmem hβmem hcircle
    have hαβ_explicit :
        AffineMap.lineMap
            (positiveAxisKeyholeAngle R ε)
            (-positiveAxisKeyholeAngle R ε)
            (8 * (s : ℝ) - 1) =
          AffineMap.lineMap
            (positiveAxisKeyholeAngle R ε)
            (-positiveAxisKeyholeAngle R ε)
            (8 * (t : ℝ) - 1) := by
      simpa [α, β] using hαβ
    have hst' : 8 * (s : ℝ) - 1 = 8 * (t : ℝ) - 1 := by
      rcases (AffineMap.lineMap_eq_lineMap_iff
        (p₀ := positiveAxisKeyholeAngle R ε)
        (p₁ := -positiveAxisKeyholeAngle R ε)
        (c₁ := 8 * (s : ℝ) - 1) (c₂ := 8 * (t : ℝ) - 1)).mp hαβ_explicit with hEq | hEq
      · have : False := by
          nlinarith [hEq, hθ.1, Real.pi_pos]
        exact this.elim
      · exact hEq
    -- The affine angle parameter is injective because the two angular endpoints differ.
    exact Subtype.ext (by linarith)
  · rcases hlower with ⟨hs, ht⟩
    -- The lower lip is the same affine radial model, with the opposite orientation.
    have hsPath :
        positiveAxisKeyhole R ε s =
          AffineMap.lineMap
            (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
            (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
            (4 * (s : ℝ) - 1) := by
      exact (Path.extend_apply (positiveAxisKeyhole R ε) s.2).symm.trans <|
        positive_axis_keyhole_eq_on_lower_lip R ε (Set.Ioo_subset_Icc_self hs)
    have htPath :
        positiveAxisKeyhole R ε t =
          AffineMap.lineMap
            (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
            (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
            (4 * (t : ℝ) - 1) := by
      exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
        positive_axis_keyhole_eq_on_lower_lip R ε (Set.Ioo_subset_Icc_self ht)
    have hparam :
        AffineMap.lineMap
            (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
            (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
            (4 * (s : ℝ) - 1) =
          AffineMap.lineMap
            (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
            (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
            (4 * (t : ℝ) - 1) := by
      calc
        AffineMap.lineMap
            (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
            (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
            (4 * (s : ℝ) - 1) =
            positiveAxisKeyhole R ε s := hsPath.symm
        _ = positiveAxisKeyhole R ε t := hst
        _ =
            AffineMap.lineMap
              (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
              (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
              (4 * (t : ℝ) - 1) := htPath
    have hEndsNe :
        circleMap 0 ε (-positiveAxisKeyholeAngle R ε) ≠
          circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
      intro hEq
      have hnorm := congrArg norm hEq
      simp [norm_circleMap_zero, abs_of_pos hR, abs_of_pos hε] at hnorm
      linarith
    have hst' : 4 * (s : ℝ) - 1 = 4 * (t : ℝ) - 1 := by
      rcases (AffineMap.lineMap_eq_lineMap_iff
        (p₀ := circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
        (p₁ := circleMap 0 R (-positiveAxisKeyholeAngle R ε))
        (c₁ := 4 * (s : ℝ) - 1) (c₂ := 4 * (t : ℝ) - 1)).mp hparam with hEq | hEq
      · exact (hEndsNe hEq).elim
      · exact hEq
    -- Again the subtype equality is read off from the affine radial coordinate.
    exact Subtype.ext (by linarith)
  · rcases houter with ⟨hs, ht⟩
    let α : ℝ :=
      AffineMap.lineMap
        (-positiveAxisKeyholeAngle R ε)
        (positiveAxisKeyholeAngle R ε)
        (2 * (s : ℝ) - 1)
    let β : ℝ :=
      AffineMap.lineMap
        (-positiveAxisKeyholeAngle R ε)
        (positiveAxisKeyholeAngle R ε)
        (2 * (t : ℝ) - 1)
    -- The outer circle uses the same injective angular strip as the inner arc.
    have hsPath : positiveAxisKeyhole R ε s = circleMap 0 R α := by
      exact (Path.extend_apply (positiveAxisKeyhole R ε) s.2).symm.trans <|
        positive_axis_keyhole_eq_on_outer_arc R ε (Set.Ioo_subset_Icc_self hs)
    have htPath : positiveAxisKeyhole R ε t = circleMap 0 R β := by
      exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
        positive_axis_keyhole_eq_on_outer_arc R ε (Set.Ioo_subset_Icc_self ht)
    have hcircle : circleMap 0 R α = circleMap 0 R β := by
      calc
        circleMap 0 R α = positiveAxisKeyhole R ε s := hsPath.symm
        _ = positiveAxisKeyhole R ε t := hst
        _ = circleMap 0 R β := htPath
    have hsParam : 2 * (s : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hs.1, hs.2]
    have htParam : 2 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have hAngleOrder :
        -positiveAxisKeyholeAngle R ε < positiveAxisKeyholeAngle R ε := by
      nlinarith [hθ.1, Real.pi_pos]
    have hAnglesNe :
        -positiveAxisKeyholeAngle R ε ≠ positiveAxisKeyholeAngle R ε := by
      nlinarith [hθ.1, Real.pi_pos]
    have hαmemOpen :
        α ∈ openSegment ℝ
          (-positiveAxisKeyholeAngle R ε)
          (positiveAxisKeyholeAngle R ε) := by
      simpa [α] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (-positiveAxisKeyholeAngle R ε)
          (positiveAxisKeyholeAngle R ε)
          hsParam
    have hβmemOpen :
        β ∈ openSegment ℝ
          (-positiveAxisKeyholeAngle R ε)
          (positiveAxisKeyholeAngle R ε) := by
      simpa [β] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (-positiveAxisKeyholeAngle R ε)
          (positiveAxisKeyholeAngle R ε)
          htParam
    have hαmemIoo :
        α ∈ Set.Ioo
          (-positiveAxisKeyholeAngle R ε)
          (positiveAxisKeyholeAngle R ε) := by
      rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hαmemOpen
      simpa [min_eq_left hAngleOrder.le, max_eq_right hAngleOrder.le] using hαmemOpen
    have hβmemIoo :
        β ∈ Set.Ioo
          (-positiveAxisKeyholeAngle R ε)
          (positiveAxisKeyholeAngle R ε) := by
      rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hβmemOpen
      simpa [min_eq_left hAngleOrder.le, max_eq_right hAngleOrder.le] using hβmemOpen
    have hαmem :
        α ∈ Set.uIoc
          (-positiveAxisKeyholeAngle R ε)
          (positiveAxisKeyholeAngle R ε) := by
      rw [Set.uIoc_of_le hAngleOrder.le]
      exact Set.Ioo_subset_Ioc_self hαmemIoo
    have hβmem :
        β ∈ Set.uIoc
          (-positiveAxisKeyholeAngle R ε)
          (positiveAxisKeyholeAngle R ε) := by
      rw [Set.uIoc_of_le hAngleOrder.le]
      exact Set.Ioo_subset_Ioc_self hβmemIoo
    have hlen :
        |(-positiveAxisKeyholeAngle R ε) - positiveAxisKeyholeAngle R ε| ≤ 2 * Real.pi := by
      have hnonpos :
          (-positiveAxisKeyholeAngle R ε) - positiveAxisKeyholeAngle R ε ≤ 0 := by
        nlinarith [hθ.1, Real.pi_pos]
      rw [abs_of_nonpos hnonpos]
      nlinarith [hθ.2, Real.pi_pos]
    have hinj :=
      injOn_circleMap_of_abs_sub_le
        (c := 0) (R := R)
        (a := -positiveAxisKeyholeAngle R ε)
        (b := positiveAxisKeyholeAngle R ε)
        (by linarith : R ≠ 0) hlen
    have hαβ : α = β := hinj hαmem hβmem hcircle
    have hαβ_explicit :
        AffineMap.lineMap
            (-positiveAxisKeyholeAngle R ε)
            (positiveAxisKeyholeAngle R ε)
            (2 * (s : ℝ) - 1) =
          AffineMap.lineMap
            (-positiveAxisKeyholeAngle R ε)
            (positiveAxisKeyholeAngle R ε)
            (2 * (t : ℝ) - 1) := by
      simpa [α, β] using hαβ
    have hst' : 2 * (s : ℝ) - 1 = 2 * (t : ℝ) - 1 := by
      rcases (AffineMap.lineMap_eq_lineMap_iff
        (p₀ := -positiveAxisKeyholeAngle R ε)
        (p₁ := positiveAxisKeyholeAngle R ε)
        (c₁ := 2 * (s : ℝ) - 1) (c₂ := 2 * (t : ℝ) - 1)).mp hαβ_explicit with hEq | hEq
      · have : False := by
          nlinarith [hEq, hθ.1, Real.pi_pos]
        exact this.elim
      · exact hEq
    -- The outer-arc affine angle parameter is likewise injective.
    exact Subtype.ext (by linarith)

/-- Helper for Remark III.6-extra-7: the upper outer corner of the positive-axis keyhole contour
is hit exactly at the two loop endpoints `0` and `1`. This is the first exact corner fiber needed
for the simple-loop proof. -/
lemma positiveAxisKeyhole_eq_upper_outer_corner_iff
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t : I} :
    positiveAxisKeyhole R ε t = circleMap 0 R (positiveAxisKeyholeAngle R ε) ↔
      t = (0 : I) ∨ t = (1 : I) := by
  have hR : 0 < R := lt_trans hε hεR
  have hθ := positiveAxisKeyhole_angle_bounds (R := R) (ε := ε) hε hεR
  have hEndsNe :
      circleMap 0 R (positiveAxisKeyholeAngle R ε) ≠
        circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
    intro hEq
    have hnorm := congrArg norm hEq
    simp [norm_circleMap_zero, abs_of_pos hR, abs_of_pos hε] at hnorm
    linarith
  constructor
  · intro ht
    rcases positive_axis_keyhole_parameter_cases t with
      hzero | hupper | honeEight | hinner | honeQuarter | hlower | hhalf | houter | hone
    · -- The initial parameter is one endpoint of the closed loop.
      exact Or.inl (Subtype.ext hzero)
    · have hparam : 8 * (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hupper.1, hupper.2]
      have hpath :
          positiveAxisKeyhole R ε t =
            AffineMap.lineMap
              (circleMap 0 R (positiveAxisKeyholeAngle R ε))
              (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
              (8 * (t : ℝ)) := by
        -- On the open upper lip, the contour is the radial segment parameterized by `8 t`.
        exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
          positive_axis_keyhole_eq_on_upper_lip R ε (Set.Ioo_subset_Icc_self hupper)
      have hopen :
          positiveAxisKeyhole R ε t ∈
            openSegment ℝ
              (circleMap 0 R (positiveAxisKeyholeAngle R ε))
              (circleMap 0 ε (positiveAxisKeyholeAngle R ε)) := by
        -- Interior upper-lip parameters land in the open segment, so they cannot be the corner.
        simpa [hpath] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (circleMap 0 R (positiveAxisKeyholeAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
            hparam)
      have hcorner :
          circleMap 0 R (positiveAxisKeyholeAngle R ε) ∈
            openSegment ℝ
              (circleMap 0 R (positiveAxisKeyholeAngle R ε))
              (circleMap 0 ε (positiveAxisKeyholeAngle R ε)) := by
        simpa [ht] using hopen
      exact False.elim <| hEndsNe <|
        (left_mem_openSegment_iff
          (𝕜 := ℝ)
          (x := circleMap 0 R (positiveAxisKeyholeAngle R ε))
          (y := circleMap 0 ε (positiveAxisKeyholeAngle R ε))).mp hcorner
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext honeEight
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hR, abs_of_pos hε] at hnorm
      exact (hεR.ne hnorm.symm).elim
    · have hpath :
          positiveAxisKeyhole R ε t =
            circleMap 0 ε
              (AffineMap.lineMap
                (positiveAxisKeyholeAngle R ε)
                (-positiveAxisKeyholeAngle R ε)
                (8 * (t : ℝ) - 1)) := by
        -- The inner arc has constant radius `ε`, so it cannot hit the outer corner.
        exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
          positive_axis_keyhole_eq_on_inner_arc R ε (Set.Ioo_subset_Icc_self hinner)
      have hnorm := congrArg norm (ht.symm.trans hpath)
      simp [norm_circleMap_zero, abs_of_pos hR, abs_of_pos hε] at hnorm
      exact (hεR.ne hnorm.symm).elim
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext honeQuarter
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.2.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hR, abs_of_pos hε] at hnorm
      linarith
    · rcases positive_axis_keyhole_eq_lower_lip_circleMap_of_mem_Ioo R ε hε hεR hlower with
        ⟨ρ, hρ, hpath⟩
      have hlower_im : (positiveAxisKeyhole R ε t).im < 0 := by
        -- The lower lip lies strictly below the real axis on the positive side.
        rw [hpath]
        have hline := positiveAxisKeyhole_lower_lip_line R ε ρ
        have hre := positiveAxisKeyhole_lower_lip_re_pos
          (R := R) (ε := ε) (ρ := ρ) (lt_trans hε hρ.1)
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have hupper_im :
          0 < (circleMap 0 R (positiveAxisKeyholeAngle R ε)).im := by
        -- The target upper corner lies strictly above the real axis.
        have hline := positiveAxisKeyhole_upper_lip_line R ε R
        have hre := positiveAxisKeyhole_upper_lip_re_pos (R := R) (ε := ε) (ρ := R) hR
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have him := congrArg Complex.im ht
      linarith
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have hupper_im :
          0 < (circleMap 0 R (positiveAxisKeyholeAngle R ε)).im := by
        -- The upper outer corner lies above the real axis.
        have hline := positiveAxisKeyhole_upper_lip_line R ε R
        have hre := positiveAxisKeyhole_upper_lip_re_pos (R := R) (ε := ε) (ρ := R) hR
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε)).im < 0 := by
        -- The lower outer corner lies below the real axis.
        have hline := positiveAxisKeyhole_lower_lip_line R ε R
        have hre := positiveAxisKeyhole_lower_lip_re_pos (R := R) (ε := ε) (ρ := R) hR
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext hhalf
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.2.2.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · rcases positive_axis_keyhole_eq_outer_arc_circleMap_of_mem_Ioo R ε hε hεR houter with
        ⟨α, hα, hpath⟩
      have hAngleOrder :
          -positiveAxisKeyholeAngle R ε < positiveAxisKeyholeAngle R ε := by
        nlinarith [hθ.1, Real.pi_pos]
      have hαmem :
          α ∈ Set.uIoc
            (-positiveAxisKeyholeAngle R ε)
            (positiveAxisKeyholeAngle R ε) := by
        rw [Set.uIoc_of_le hAngleOrder.le]
        exact Set.Ioo_subset_Ioc_self hα
      have hendmem :
          positiveAxisKeyholeAngle R ε ∈
            Set.uIoc
              (-positiveAxisKeyholeAngle R ε)
              (positiveAxisKeyholeAngle R ε) := by
        rw [Set.uIoc_of_le hAngleOrder.le]
        exact Set.mem_Ioc.mpr ⟨hAngleOrder, le_rfl⟩
      have hlen :
          |(-positiveAxisKeyholeAngle R ε) - positiveAxisKeyholeAngle R ε| ≤ 2 * Real.pi := by
        have hnonpos :
            (-positiveAxisKeyholeAngle R ε) - positiveAxisKeyholeAngle R ε ≤ 0 := by
          nlinarith [hθ.1, Real.pi_pos]
        rw [abs_of_nonpos hnonpos]
        nlinarith [hθ.2, Real.pi_pos]
      have hinj :=
        injOn_circleMap_of_abs_sub_le
          (c := 0) (R := R)
          (a := -positiveAxisKeyholeAngle R ε)
          (b := positiveAxisKeyholeAngle R ε)
          (by linarith : R ≠ 0) hlen
      have hcircle : circleMap 0 R α = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        calc
          circleMap 0 R α = positiveAxisKeyhole R ε t := hpath.symm
          _ = circleMap 0 R (positiveAxisKeyholeAngle R ε) := ht
      have hαeq : α = positiveAxisKeyholeAngle R ε := hinj hαmem hendmem hcircle
      exact False.elim ((ne_of_lt hα.2) hαeq)
    · -- The terminal parameter is the other endpoint of the closed loop.
      exact Or.inr (Subtype.ext hone)
  · rintro (rfl | rfl)
    · exact (positive_axis_keyhole_breakpoint_values R ε).1
    · exact (positive_axis_keyhole_breakpoint_values R ε).2.2.2.2

/-- Helper for Remark III.6-extra-7: the upper inner corner of the positive-axis keyhole contour
is hit exactly at the first interior breakpoint `t = 1/8`. -/
lemma positiveAxisKeyhole_eq_upper_inner_corner_iff
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t : I} :
    positiveAxisKeyhole R ε t = circleMap 0 ε (positiveAxisKeyholeAngle R ε) ↔
      t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := by
  have hR : 0 < R := lt_trans hε hεR
  have hθ := positiveAxisKeyhole_angle_bounds (R := R) (ε := ε) hε hεR
  have hEndsNe :
      circleMap 0 R (positiveAxisKeyholeAngle R ε) ≠
        circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
    intro hEq
    have hnorm := congrArg norm hEq
    simp [norm_circleMap_zero, abs_of_pos hR, abs_of_pos hε] at hnorm
    linarith
  constructor
  · intro ht
    rcases positive_axis_keyhole_parameter_cases t with
      hzero | hupper | honeEight | hinner | honeQuarter | hlower | hhalf | houter | hone
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have htEq : t = (0 : I) := Subtype.ext hzero
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hR, abs_of_pos hε] at hnorm
      linarith
    · have hparam : 8 * (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hupper.1, hupper.2]
      have hpath :
          positiveAxisKeyhole R ε t =
            AffineMap.lineMap
              (circleMap 0 R (positiveAxisKeyholeAngle R ε))
              (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
              (8 * (t : ℝ)) := by
        -- The open upper lip is the radial segment ending at the upper inner corner.
        exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
          positive_axis_keyhole_eq_on_upper_lip R ε (Set.Ioo_subset_Icc_self hupper)
      have hopen :
          positiveAxisKeyhole R ε t ∈
            openSegment ℝ
              (circleMap 0 R (positiveAxisKeyholeAngle R ε))
              (circleMap 0 ε (positiveAxisKeyholeAngle R ε)) := by
        simpa [hpath] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (circleMap 0 R (positiveAxisKeyholeAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
            hparam)
      have hcorner :
          circleMap 0 ε (positiveAxisKeyholeAngle R ε) ∈
            openSegment ℝ
              (circleMap 0 R (positiveAxisKeyholeAngle R ε))
              (circleMap 0 ε (positiveAxisKeyholeAngle R ε)) := by
        simpa [ht] using hopen
      exact False.elim <| hEndsNe <|
        (right_mem_openSegment_iff
          (𝕜 := ℝ)
          (x := circleMap 0 R (positiveAxisKeyholeAngle R ε))
          (y := circleMap 0 ε (positiveAxisKeyholeAngle R ε))).mp hcorner
    · exact Subtype.ext honeEight
    · rcases positive_axis_keyhole_eq_inner_arc_circleMap_of_mem_Ioo R ε hε hεR hinner with
        ⟨α, hα, hpath⟩
      have hAngleOrder :
          -positiveAxisKeyholeAngle R ε < positiveAxisKeyholeAngle R ε := by
        nlinarith [hθ.1, Real.pi_pos]
      have hαmem :
          α ∈ Set.uIoc
            (positiveAxisKeyholeAngle R ε)
            (-positiveAxisKeyholeAngle R ε) := by
        rw [Set.uIoc_of_ge hAngleOrder.le]
        exact Set.Ioo_subset_Ioc_self hα
      have htargetmem :
          positiveAxisKeyholeAngle R ε ∈
            Set.uIoc
              (positiveAxisKeyholeAngle R ε)
              (-positiveAxisKeyholeAngle R ε) := by
        rw [Set.uIoc_of_ge hAngleOrder.le]
        exact Set.mem_Ioc.mpr ⟨hAngleOrder, le_rfl⟩
      have hlen :
          |positiveAxisKeyholeAngle R ε - (-positiveAxisKeyholeAngle R ε)| ≤ 2 * Real.pi := by
        have hnonneg :
            0 ≤ positiveAxisKeyholeAngle R ε - (-positiveAxisKeyholeAngle R ε) := by
          nlinarith [hθ.1, Real.pi_pos]
        rw [abs_of_nonneg hnonneg]
        nlinarith [hθ.2, Real.pi_pos]
      have hinj :=
        injOn_circleMap_of_abs_sub_le
          (c := 0) (R := ε)
          (a := positiveAxisKeyholeAngle R ε)
          (b := -positiveAxisKeyholeAngle R ε)
          (by linarith : ε ≠ 0) hlen
      have hcircle : circleMap 0 ε α = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
        calc
          circleMap 0 ε α = positiveAxisKeyhole R ε t := hpath.symm
          _ = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := ht
      have hαeq : α = positiveAxisKeyholeAngle R ε := hinj hαmem htargetmem hcircle
      exact False.elim ((ne_of_lt hα.2) hαeq)
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have hupper_im :
          0 < (circleMap 0 ε (positiveAxisKeyholeAngle R ε)).im := by
        -- The upper inner corner lies above the real axis.
        have hline := positiveAxisKeyhole_upper_lip_line R ε ε
        have hre := positiveAxisKeyhole_upper_lip_re_pos (R := R) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 ε (-positiveAxisKeyholeAngle R ε)).im < 0 := by
        -- The lower inner corner lies below the real axis.
        have hline := positiveAxisKeyhole_lower_lip_line R ε ε
        have hre := positiveAxisKeyhole_lower_lip_re_pos (R := R) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext honeQuarter
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.2.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · rcases positive_axis_keyhole_eq_lower_lip_circleMap_of_mem_Ioo R ε hε hεR hlower with
        ⟨ρ, hρ, hpath⟩
      have hnorm :
          ε = ρ := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ε (positiveAxisKeyholeAngle R ε) = positiveAxisKeyhole R ε t := ht.symm
          _ = circleMap 0 ρ (-positiveAxisKeyholeAngle R ε) := hpath
        simpa [norm_circleMap_zero, abs_of_pos hε, abs_of_pos (lt_trans hε hρ.1)] using hnorm'
      have : False := by
        linarith [hρ.1, hnorm]
      exact this.elim
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have hupper_im :
          0 < (circleMap 0 ε (positiveAxisKeyholeAngle R ε)).im := by
        -- The upper inner corner lies above the real axis.
        have hline := positiveAxisKeyhole_upper_lip_line R ε ε
        have hre := positiveAxisKeyhole_upper_lip_re_pos (R := R) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε)).im < 0 := by
        -- The lower outer corner also lies below the real axis.
        have hline := positiveAxisKeyhole_lower_lip_line R ε R
        have hre := positiveAxisKeyhole_lower_lip_re_pos (R := R) (ε := ε) (ρ := R) hR
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext hhalf
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.2.2.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · rcases positive_axis_keyhole_eq_outer_arc_circleMap_of_mem_Ioo R ε hε hεR houter with
        ⟨α, hα, hpath⟩
      have hnorm :
          ε = R := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ε (positiveAxisKeyholeAngle R ε) = positiveAxisKeyhole R ε t := ht.symm
          _ = circleMap 0 R α := hpath
        simpa [norm_circleMap_zero, abs_of_pos hε, abs_of_pos hR] using hnorm'
      have : False := by
        linarith [hεR, hnorm]
      exact this.elim
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have htEq : t = (1 : I) := Subtype.ext hone
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.2.2.2
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hR, abs_of_pos hε] at hnorm
      linarith
  · rintro rfl
    exact (positive_axis_keyhole_breakpoint_values R ε).2.1

/-- Helper for Remark III.6-extra-7: the lower inner corner of the positive-axis keyhole contour
is hit exactly at the second interior breakpoint `t = 1/4`. -/
lemma positiveAxisKeyhole_eq_lower_inner_corner_iff
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t : I} :
    positiveAxisKeyhole R ε t = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) ↔
      t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := by
  have hR : 0 < R := lt_trans hε hεR
  have hθ := positiveAxisKeyhole_angle_bounds (R := R) (ε := ε) hε hεR
  have hEndsNe :
      circleMap 0 ε (-positiveAxisKeyholeAngle R ε) ≠
        circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
    intro hEq
    have hnorm := congrArg norm hEq
    simp [norm_circleMap_zero, abs_of_pos hR, abs_of_pos hε] at hnorm
    linarith
  constructor
  · intro ht
    rcases positive_axis_keyhole_parameter_cases t with
      hzero | hupper | honeEight | hinner | honeQuarter | hlower | hhalf | houter | hone
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have htEq : t = (0 : I) := Subtype.ext hzero
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hR, abs_of_pos hε] at hnorm
      linarith
    · rcases positive_axis_keyhole_eq_upper_lip_circleMap_of_mem_Ioo R ε hε hεR hupper with
        ⟨ρ, hρ, hpath⟩
      have hupper_im : 0 < (positiveAxisKeyhole R ε t).im := by
        -- The upper lip lies strictly above the real axis.
        rw [hpath]
        have hline := positiveAxisKeyhole_upper_lip_line R ε ρ
        have hre := positiveAxisKeyhole_upper_lip_re_pos
          (R := R) (ε := ε) (ρ := ρ) (lt_trans hε hρ.1)
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 ε (-positiveAxisKeyholeAngle R ε)).im < 0 := by
        -- The lower inner corner lies below the real axis.
        have hline := positiveAxisKeyhole_lower_lip_line R ε ε
        have hre := positiveAxisKeyhole_lower_lip_re_pos (R := R) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have him := congrArg Complex.im ht
      linarith
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have hupper_im :
          0 < (circleMap 0 ε (positiveAxisKeyholeAngle R ε)).im := by
        -- The upper inner corner lies above the real axis.
        have hline := positiveAxisKeyhole_upper_lip_line R ε ε
        have hre := positiveAxisKeyhole_upper_lip_re_pos (R := R) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 ε (-positiveAxisKeyholeAngle R ε)).im < 0 := by
        -- The target lower inner corner lies below the real axis.
        have hline := positiveAxisKeyhole_lower_lip_line R ε ε
        have hre := positiveAxisKeyhole_lower_lip_re_pos (R := R) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext honeEight
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · rcases positive_axis_keyhole_eq_inner_arc_circleMap_of_mem_Ioo R ε hε hεR hinner with
        ⟨α, hα, hpath⟩
      have hAngleOrder :
          -positiveAxisKeyholeAngle R ε < positiveAxisKeyholeAngle R ε := by
        nlinarith [hθ.1, Real.pi_pos]
      have hαmem :
          α ∈ Set.Ico
            (-positiveAxisKeyholeAngle R ε)
            (positiveAxisKeyholeAngle R ε) := by
        exact Set.Ioo_subset_Ico_self hα
      have htargetmem :
          -positiveAxisKeyholeAngle R ε ∈
            Set.Ico
              (-positiveAxisKeyholeAngle R ε)
              (positiveAxisKeyholeAngle R ε) := by
        exact Set.mem_Ico.mpr ⟨le_rfl, hAngleOrder⟩
      have hlen :
          positiveAxisKeyholeAngle R ε - (-positiveAxisKeyholeAngle R ε) ≤ 2 * Real.pi := by
        nlinarith [hθ.2, Real.pi_pos]
      have hinj :=
        injOn_circleMap_of_abs_sub_le'
          (c := 0) (R := ε)
          (a := -positiveAxisKeyholeAngle R ε)
          (b := positiveAxisKeyholeAngle R ε)
          (by linarith : ε ≠ 0) hlen
      have hcircle : circleMap 0 ε α = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
        calc
          circleMap 0 ε α = positiveAxisKeyhole R ε t := hpath.symm
          _ = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := ht
      have hαeq : α = -positiveAxisKeyholeAngle R ε := hinj hαmem htargetmem hcircle
      exact False.elim ((ne_of_gt hα.1) hαeq)
    · exact Subtype.ext honeQuarter
    · have hparam : 4 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hlower.1, hlower.2]
      have hpath :
          positiveAxisKeyhole R ε t =
            AffineMap.lineMap
              (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
              (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
              (4 * (t : ℝ) - 1) := by
        -- The lower lip is the radial segment beginning at the lower inner corner.
        exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
          positive_axis_keyhole_eq_on_lower_lip R ε (Set.Ioo_subset_Icc_self hlower)
      have hopen :
          positiveAxisKeyhole R ε t ∈
            openSegment ℝ
              (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
              (circleMap 0 R (-positiveAxisKeyholeAngle R ε)) := by
        simpa [hpath] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
            (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
            hparam)
      have hcorner :
          circleMap 0 ε (-positiveAxisKeyholeAngle R ε) ∈
            openSegment ℝ
              (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
              (circleMap 0 R (-positiveAxisKeyholeAngle R ε)) := by
        simpa [ht] using hopen
      exact False.elim <| hEndsNe <|
        (left_mem_openSegment_iff
          (𝕜 := ℝ)
          (x := circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
          (y := circleMap 0 R (-positiveAxisKeyholeAngle R ε))).mp hcorner
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext hhalf
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.2.2.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hR, abs_of_pos hε] at hnorm
      linarith
    · rcases positive_axis_keyhole_eq_outer_arc_circleMap_of_mem_Ioo R ε hε hεR houter with
        ⟨α, hα, hpath⟩
      have hnorm :
          ε = R := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ε (-positiveAxisKeyholeAngle R ε) = positiveAxisKeyhole R ε t := ht.symm
          _ = circleMap 0 R α := hpath
        simpa [norm_circleMap_zero, abs_of_pos hε, abs_of_pos hR] using hnorm'
      have : False := by
        linarith [hεR, hnorm]
      exact this.elim
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have htEq : t = (1 : I) := Subtype.ext hone
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.2.2.2
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hR, abs_of_pos hε] at hnorm
      linarith
  · rintro rfl
    exact (positive_axis_keyhole_breakpoint_values R ε).2.2.1

/-- Helper for Remark III.6-extra-7: the lower outer corner of the positive-axis keyhole contour
is hit exactly at the third interior breakpoint `t = 1/2`. -/
lemma positiveAxisKeyhole_eq_lower_outer_corner_iff
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t : I} :
    positiveAxisKeyhole R ε t = circleMap 0 R (-positiveAxisKeyholeAngle R ε) ↔
      t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := by
  have hR : 0 < R := lt_trans hε hεR
  have hθ := positiveAxisKeyhole_angle_bounds (R := R) (ε := ε) hε hεR
  have hEndsNe :
      circleMap 0 ε (-positiveAxisKeyholeAngle R ε) ≠
        circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
    intro hEq
    have hnorm := congrArg norm hEq
    simp [norm_circleMap_zero, abs_of_pos hR, abs_of_pos hε] at hnorm
    linarith
  constructor
  · intro ht
    rcases positive_axis_keyhole_parameter_cases t with
      hzero | hupper | honeEight | hinner | honeQuarter | hlower | hhalf | houter | hone
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have hupper_im :
          0 < (circleMap 0 R (positiveAxisKeyholeAngle R ε)).im := by
        -- The initial upper outer corner lies above the real axis.
        have hline := positiveAxisKeyhole_upper_lip_line R ε R
        have hre := positiveAxisKeyhole_upper_lip_re_pos (R := R) (ε := ε) (ρ := R) hR
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε)).im < 0 := by
        -- The target lower outer corner lies below the real axis.
        have hline := positiveAxisKeyhole_lower_lip_line R ε R
        have hre := positiveAxisKeyhole_lower_lip_re_pos (R := R) (ε := ε) (ρ := R) hR
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have htEq : t = (0 : I) := Subtype.ext hzero
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · rcases positive_axis_keyhole_eq_upper_lip_circleMap_of_mem_Ioo R ε hε hεR hupper with
        ⟨ρ, hρ, hpath⟩
      have hnorm :
          R = ρ := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 R (-positiveAxisKeyholeAngle R ε) = positiveAxisKeyhole R ε t := ht.symm
          _ = circleMap 0 ρ (positiveAxisKeyholeAngle R ε) := hpath
        simpa [norm_circleMap_zero, abs_of_pos hR, abs_of_pos (lt_trans hε hρ.1)] using hnorm'
      have : False := by
        linarith [hρ.2, hnorm]
      exact this.elim
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have hupper_im :
          0 < (circleMap 0 ε (positiveAxisKeyholeAngle R ε)).im := by
        -- The upper inner corner lies above the real axis.
        have hline := positiveAxisKeyhole_upper_lip_line R ε ε
        have hre := positiveAxisKeyhole_upper_lip_re_pos (R := R) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε)).im < 0 := by
        -- The target corner lies below the real axis.
        have hline := positiveAxisKeyhole_lower_lip_line R ε R
        have hre := positiveAxisKeyhole_lower_lip_re_pos (R := R) (ε := ε) (ρ := R) hR
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext honeEight
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · rcases positive_axis_keyhole_eq_inner_arc_circleMap_of_mem_Ioo R ε hε hεR hinner with
        ⟨α, hα, hpath⟩
      have hnorm :
          R = ε := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 R (-positiveAxisKeyholeAngle R ε) = positiveAxisKeyhole R ε t := ht.symm
          _ = circleMap 0 ε α := hpath
        simpa [norm_circleMap_zero, abs_of_pos hR, abs_of_pos hε] using hnorm'
      have : False := by
        linarith [hεR, hnorm]
      exact this.elim
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext honeQuarter
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.2.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hR, abs_of_pos hε] at hnorm
      linarith
    · have hparam : 4 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hlower.1, hlower.2]
      have hpath :
          positiveAxisKeyhole R ε t =
            AffineMap.lineMap
              (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
              (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
              (4 * (t : ℝ) - 1) := by
        -- The open lower lip is the radial segment ending at the lower outer corner.
        exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
          positive_axis_keyhole_eq_on_lower_lip R ε (Set.Ioo_subset_Icc_self hlower)
      have hopen :
          positiveAxisKeyhole R ε t ∈
            openSegment ℝ
              (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
              (circleMap 0 R (-positiveAxisKeyholeAngle R ε)) := by
        simpa [hpath] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
            (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
            hparam)
      have hcorner :
          circleMap 0 R (-positiveAxisKeyholeAngle R ε) ∈
            openSegment ℝ
              (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
              (circleMap 0 R (-positiveAxisKeyholeAngle R ε)) := by
        simpa [ht] using hopen
      exact False.elim <| hEndsNe <|
        (right_mem_openSegment_iff
          (𝕜 := ℝ)
          (x := circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
          (y := circleMap 0 R (-positiveAxisKeyholeAngle R ε))).mp hcorner
    · exact Subtype.ext hhalf
    · rcases positive_axis_keyhole_eq_outer_arc_circleMap_of_mem_Ioo R ε hε hεR houter with
        ⟨α, hα, hpath⟩
      have hAngleOrder :
          -positiveAxisKeyholeAngle R ε < positiveAxisKeyholeAngle R ε := by
        nlinarith [hθ.1, Real.pi_pos]
      have hαmem :
          α ∈ Set.Ico
            (-positiveAxisKeyholeAngle R ε)
            (positiveAxisKeyholeAngle R ε) := by
        exact Set.Ioo_subset_Ico_self hα
      have htargetmem :
          -positiveAxisKeyholeAngle R ε ∈
            Set.Ico
              (-positiveAxisKeyholeAngle R ε)
              (positiveAxisKeyholeAngle R ε) := by
        exact Set.mem_Ico.mpr ⟨le_rfl, hAngleOrder⟩
      have hlen :
          positiveAxisKeyholeAngle R ε - (-positiveAxisKeyholeAngle R ε) ≤ 2 * Real.pi := by
        nlinarith [hθ.2, Real.pi_pos]
      have hinj :=
        injOn_circleMap_of_abs_sub_le'
          (c := 0) (R := R)
          (a := -positiveAxisKeyholeAngle R ε)
          (b := positiveAxisKeyholeAngle R ε)
          (by linarith : R ≠ 0) hlen
      have hcircle : circleMap 0 R α = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
        calc
          circleMap 0 R α = positiveAxisKeyhole R ε t := hpath.symm
          _ = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := ht
      have hαeq : α = -positiveAxisKeyholeAngle R ε := hinj hαmem htargetmem hcircle
      exact False.elim ((ne_of_gt hα.1) hαeq)
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have hupper_im :
          0 < (circleMap 0 R (positiveAxisKeyholeAngle R ε)).im := by
        -- The terminal upper outer corner lies above the real axis.
        have hline := positiveAxisKeyhole_upper_lip_line R ε R
        have hre := positiveAxisKeyhole_upper_lip_re_pos (R := R) (ε := ε) (ρ := R) hR
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε)).im < 0 := by
        -- The target lower outer corner stays below the real axis.
        have hline := positiveAxisKeyhole_lower_lip_line R ε R
        have hre := positiveAxisKeyhole_lower_lip_re_pos (R := R) (ε := ε) (ρ := R) hR
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have htEq : t = (1 : I) := Subtype.ext hone
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.2.2.2
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
  · rintro rfl
    exact (positive_axis_keyhole_breakpoint_values R ε).2.2.2.1

/-- Helper for Remark III.6-extra-7: package the four exact corner fibers of the positive-axis
keyhole contour so later proofs can dispatch only on branch geometry. -/
lemma positiveAxisKeyhole_corner_fiber_classifier
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t : I} :
    (positiveAxisKeyhole R ε t = circleMap 0 R (positiveAxisKeyholeAngle R ε) ↔
        t = (0 : I) ∨ t = (1 : I)) ∧
      (positiveAxisKeyhole R ε t = circleMap 0 ε (positiveAxisKeyholeAngle R ε) ↔
        t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I)) ∧
      (positiveAxisKeyhole R ε t = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) ↔
        t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I)) ∧
      (positiveAxisKeyhole R ε t = circleMap 0 R (-positiveAxisKeyholeAngle R ε) ↔
        t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I)) := by
  -- Bundle the four exact breakpoint fibers so later case splits can stay on the source geometry.
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using positiveAxisKeyhole_eq_upper_outer_corner_iff R ε hε hεR (t := t)
  · simpa using positiveAxisKeyhole_eq_upper_inner_corner_iff R ε hε hεR (t := t)
  · simpa using positiveAxisKeyhole_eq_lower_inner_corner_iff R ε hε hεR (t := t)
  · simpa using positiveAxisKeyhole_eq_lower_outer_corner_iff R ε hε hεR (t := t)

/-- Helper for Remark III.6-extra-7: equality on the positive-axis keyhole contour can only occur
at the same parameter, or at the two loop endpoints. This is the simple-loop input for the later
oriented-boundary packaging. -/
theorem positiveAxisKeyhole_simple_eq_or_endpoints
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) {s t : I}
    (hst : positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  -- Route correction: keep contour simplicity separate from the final owner theorem so the main
  -- proof only consumes the branch geometry and exact corner fibers proved above.
  have hbreak := positive_axis_keyhole_breakpoint_values R ε
  rcases positive_axis_keyhole_parameter_cases s with
    hs0 | hsupper | hs18 | hsinner | hs14 | hslower | hs12 | hsouter | hs1
  · have hsEq : s = (0 : I) := Subtype.ext hs0
    -- If `s` is the initial endpoint, `t` must be one of the two parameters for the same corner.
    have htCorner :
        positiveAxisKeyhole R ε t = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
      calc
        positiveAxisKeyhole R ε t = positiveAxisKeyhole R ε s := hst.symm
        _ = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by simpa [hsEq] using hbreak.1
    rcases (positiveAxisKeyhole_eq_upper_outer_corner_iff R ε hε hεR).1 htCorner with ht0 | ht1
    · left
      simpa [hsEq, ht0]
    · right
      left
      simpa [hsEq, ht1]
  · -- Use the already-isolated branch geometry instead of unfolding the concatenated contour again.
    rcases positive_axis_keyhole_eq_upper_lip_circleMap_of_mem_Ioo R ε hε hεR hsupper with
      ⟨ρs, hρs, hsPath⟩
    rcases positive_axis_keyhole_parameter_cases t with
      ht0 | htupper | ht18 | htinner | ht14 | htlower | ht12 | htouter | ht1
    · have htEq : t = (0 : I) := Subtype.ext ht0
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by simpa [htEq] using hbreak.1
      have : False := by
        rcases (positiveAxisKeyhole_eq_upper_outer_corner_iff R ε hε hεR).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsupper.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsupper.2]
      exact this.elim
    · left
      exact positiveAxisKeyhole_same_branch_injective R ε hε hεR (Or.inl ⟨hsupper, htupper⟩) hst
    · have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext ht18
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_upper_inner_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 8 := by simpa using congrArg Subtype.val hsEq
        linarith [hsupper.2]
      exact this.elim
    · rcases positive_axis_keyhole_eq_inner_arc_circleMap_of_mem_Ioo R ε hε hεR htinner with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          ρs = ε := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ρs (positiveAxisKeyholeAngle R ε) = positiveAxisKeyhole R ε s := hsPath.symm
          _ = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos (lt_trans hε hρs.1), abs_of_pos hε] using hnorm'
      have : False := by
        linarith [hρs.1, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext ht14
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_lower_inner_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 4 := by simpa using congrArg Subtype.val hsEq
        linarith [hsupper.2]
      exact this.elim
    · rcases positive_axis_keyhole_eq_lower_lip_circleMap_of_mem_Ioo R ε hε hεR htlower with
        ⟨ρt, hρt, htPath⟩
      have hR : 0 < R := lt_trans hε hεR
      have hsIm : 0 < (positiveAxisKeyhole R ε s).im := by
        rw [hsPath]
        have hline := positiveAxisKeyhole_upper_lip_line R ε ρs
        have hre :=
          positiveAxisKeyhole_upper_lip_re_pos
            (R := R) (ε := ε) (ρ := ρs) (lt_trans hε hρs.1)
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have htIm : (positiveAxisKeyhole R ε t).im < 0 := by
        rw [htPath]
        have hline := positiveAxisKeyhole_lower_lip_line R ε ρt
        have hre :=
          positiveAxisKeyhole_lower_lip_re_pos
            (R := R) (ε := ε) (ρ := ρt) (lt_trans hε hρt.1)
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have him : (positiveAxisKeyhole R ε s).im = (positiveAxisKeyhole R ε t).im := congrArg Complex.im hst
      have : False := by
        linarith [hsIm, htIm, him]
      exact this.elim
    · have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext ht12
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_lower_outer_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 2 := by simpa using congrArg Subtype.val hsEq
        linarith [hsupper.2]
      exact this.elim
    · rcases positive_axis_keyhole_eq_outer_arc_circleMap_of_mem_Ioo R ε hε hεR htouter with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          ρs = R := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ρs (positiveAxisKeyholeAngle R ε) = positiveAxisKeyhole R ε s := hsPath.symm
          _ = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos (lt_trans hε hρs.1), abs_of_pos (lt_trans hε hεR)] using hnorm'
      have : False := by
        linarith [hρs.2, hnorm]
      exact this.elim
    · have htEq : t = (1 : I) := Subtype.ext ht1
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.2.2
      have : False := by
        rcases (positiveAxisKeyhole_eq_upper_outer_corner_iff R ε hε hεR).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsupper.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsupper.2]
      exact this.elim
  · have hsEq : s = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext hs18
    -- The first interior corner has a singleton fiber.
    have htCorner :
        positiveAxisKeyhole R ε t = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
      calc
        positiveAxisKeyhole R ε t = positiveAxisKeyhole R ε s := hst.symm
        _ = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by simpa [hsEq] using hbreak.2.1
    have htEq := (positiveAxisKeyhole_eq_upper_inner_corner_iff R ε hε hεR).1 htCorner
    left
    simpa [hsEq, htEq]
  · rcases positive_axis_keyhole_eq_inner_arc_circleMap_of_mem_Ioo R ε hε hεR hsinner with
      ⟨αs, hαs, hsPath⟩
    rcases positive_axis_keyhole_parameter_cases t with
      ht0 | htupper | ht18 | htinner | ht14 | htlower | ht12 | htouter | ht1
    · have htEq : t = (0 : I) := Subtype.ext ht0
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by simpa [htEq] using hbreak.1
      have : False := by
        rcases (positiveAxisKeyhole_eq_upper_outer_corner_iff R ε hε hεR).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsinner.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsinner.2]
      exact this.elim
    · rcases positive_axis_keyhole_eq_upper_lip_circleMap_of_mem_Ioo R ε hε hεR htupper with
        ⟨ρt, hρt, htPath⟩
      have hnorm :
          ε = ρt := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ε αs = positiveAxisKeyhole R ε s := hsPath.symm
          _ = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ρt (positiveAxisKeyholeAngle R ε) := htPath
        simpa [norm_circleMap_zero, abs_of_pos hε, abs_of_pos (lt_trans hε hρt.1)] using hnorm'
      have : False := by
        linarith [hρt.1, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext ht18
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_upper_inner_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 8 := by simpa using congrArg Subtype.val hsEq
        linarith [hsinner.1]
      exact this.elim
    · left
      exact positiveAxisKeyhole_same_branch_injective R ε hε hεR
        (Or.inr <| Or.inl ⟨hsinner, htinner⟩) hst
    · have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext ht14
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_lower_inner_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 4 := by simpa using congrArg Subtype.val hsEq
        linarith [hsinner.2]
      exact this.elim
    · rcases positive_axis_keyhole_eq_lower_lip_circleMap_of_mem_Ioo R ε hε hεR htlower with
        ⟨ρt, hρt, htPath⟩
      have hnorm :
          ε = ρt := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ε αs = positiveAxisKeyhole R ε s := hsPath.symm
          _ = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ρt (-positiveAxisKeyholeAngle R ε) := htPath
        simpa [norm_circleMap_zero, abs_of_pos hε, abs_of_pos (lt_trans hε hρt.1)] using hnorm'
      have : False := by
        linarith [hρt.1, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext ht12
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_lower_outer_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 2 := by simpa using congrArg Subtype.val hsEq
        linarith [hsinner.2]
      exact this.elim
    · rcases positive_axis_keyhole_eq_outer_arc_circleMap_of_mem_Ioo R ε hε hεR htouter with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          ε = R := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ε αs = positiveAxisKeyhole R ε s := hsPath.symm
          _ = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos hε, abs_of_pos (lt_trans hε hεR)] using hnorm'
      have : False := by
        linarith [hεR, hnorm]
      exact this.elim
    · have htEq : t = (1 : I) := Subtype.ext ht1
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.2.2
      have : False := by
        rcases (positiveAxisKeyhole_eq_upper_outer_corner_iff R ε hε hεR).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsinner.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsinner.2]
      exact this.elim
  · have hsEq : s = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext hs14
    -- The lower inner corner also has a singleton fiber.
    have htCorner :
        positiveAxisKeyhole R ε t = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
      calc
        positiveAxisKeyhole R ε t = positiveAxisKeyhole R ε s := hst.symm
        _ = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
            simpa [hsEq] using hbreak.2.2.1
    have htEq := (positiveAxisKeyhole_eq_lower_inner_corner_iff R ε hε hεR).1 htCorner
    left
    simpa [hsEq, htEq]
  · rcases positive_axis_keyhole_eq_lower_lip_circleMap_of_mem_Ioo R ε hε hεR hslower with
      ⟨ρs, hρs, hsPath⟩
    rcases positive_axis_keyhole_parameter_cases t with
      ht0 | htupper | ht18 | htinner | ht14 | htlower | ht12 | htouter | ht1
    · have htEq : t = (0 : I) := Subtype.ext ht0
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by simpa [htEq] using hbreak.1
      have : False := by
        rcases (positiveAxisKeyhole_eq_upper_outer_corner_iff R ε hε hεR).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hslower.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hslower.2]
      exact this.elim
    · rcases positive_axis_keyhole_eq_upper_lip_circleMap_of_mem_Ioo R ε hε hεR htupper with
        ⟨ρt, hρt, htPath⟩
      have hR : 0 < R := lt_trans hε hεR
      have hsIm : (positiveAxisKeyhole R ε s).im < 0 := by
        rw [hsPath]
        have hline := positiveAxisKeyhole_lower_lip_line R ε ρs
        have hre :=
          positiveAxisKeyhole_lower_lip_re_pos
            (R := R) (ε := ε) (ρ := ρs) (lt_trans hε hρs.1)
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have htIm : 0 < (positiveAxisKeyhole R ε t).im := by
        rw [htPath]
        have hline := positiveAxisKeyhole_upper_lip_line R ε ρt
        have hre :=
          positiveAxisKeyhole_upper_lip_re_pos
            (R := R) (ε := ε) (ρ := ρt) (lt_trans hε hρt.1)
        have hratio : 0 < ε / R := div_pos hε hR
        rw [hline]
        nlinarith
      have him : (positiveAxisKeyhole R ε s).im = (positiveAxisKeyhole R ε t).im := congrArg Complex.im hst
      have : False := by
        linarith [hsIm, htIm, him]
      exact this.elim
    · have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext ht18
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_upper_inner_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 8 := by simpa using congrArg Subtype.val hsEq
        linarith [hslower.1]
      exact this.elim
    · rcases positive_axis_keyhole_eq_inner_arc_circleMap_of_mem_Ioo R ε hε hεR htinner with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          ρs = ε := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ρs (-positiveAxisKeyholeAngle R ε) = positiveAxisKeyhole R ε s := hsPath.symm
          _ = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos (lt_trans hε hρs.1), abs_of_pos hε] using hnorm'
      have : False := by
        linarith [hρs.1, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext ht14
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_lower_inner_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 4 := by simpa using congrArg Subtype.val hsEq
        linarith [hslower.1]
      exact this.elim
    · left
      exact positiveAxisKeyhole_same_branch_injective R ε hε hεR
        (Or.inr <| Or.inr <| Or.inl ⟨hslower, htlower⟩) hst
    · have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext ht12
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_lower_outer_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 2 := by simpa using congrArg Subtype.val hsEq
        linarith [hslower.2]
      exact this.elim
    · rcases positive_axis_keyhole_eq_outer_arc_circleMap_of_mem_Ioo R ε hε hεR htouter with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          ρs = R := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ρs (-positiveAxisKeyholeAngle R ε) = positiveAxisKeyhole R ε s := hsPath.symm
          _ = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos (lt_trans hε hρs.1), abs_of_pos (lt_trans hε hεR)] using hnorm'
      have : False := by
        linarith [hρs.2, hnorm]
      exact this.elim
    · have htEq : t = (1 : I) := Subtype.ext ht1
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.2.2
      have : False := by
        rcases (positiveAxisKeyhole_eq_upper_outer_corner_iff R ε hε hεR).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hslower.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hslower.2]
      exact this.elim
  · have hsEq : s = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext hs12
    -- The lower outer corner also has a singleton fiber.
    have htCorner :
        positiveAxisKeyhole R ε t = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
      calc
        positiveAxisKeyhole R ε t = positiveAxisKeyhole R ε s := hst.symm
        _ = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
            simpa [hsEq] using hbreak.2.2.2.1
    have htEq := (positiveAxisKeyhole_eq_lower_outer_corner_iff R ε hε hεR).1 htCorner
    left
    simpa [hsEq, htEq]
  · rcases positive_axis_keyhole_eq_outer_arc_circleMap_of_mem_Ioo R ε hε hεR hsouter with
      ⟨αs, hαs, hsPath⟩
    rcases positive_axis_keyhole_parameter_cases t with
      ht0 | htupper | ht18 | htinner | ht14 | htlower | ht12 | htouter | ht1
    · have htEq : t = (0 : I) := Subtype.ext ht0
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by simpa [htEq] using hbreak.1
      have : False := by
        rcases (positiveAxisKeyhole_eq_upper_outer_corner_iff R ε hε hεR).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsouter.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsouter.2]
      exact this.elim
    · rcases positive_axis_keyhole_eq_upper_lip_circleMap_of_mem_Ioo R ε hε hεR htupper with
        ⟨ρt, hρt, htPath⟩
      have hnorm :
          R = ρt := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 R αs = positiveAxisKeyhole R ε s := hsPath.symm
          _ = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ρt (positiveAxisKeyholeAngle R ε) := htPath
        simpa [norm_circleMap_zero, abs_of_pos (lt_trans hε hεR), abs_of_pos (lt_trans hε hρt.1)] using hnorm'
      have : False := by
        linarith [hρt.2, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext ht18
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_upper_inner_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 8 := by simpa using congrArg Subtype.val hsEq
        linarith [hsouter.1]
      exact this.elim
    · rcases positive_axis_keyhole_eq_inner_arc_circleMap_of_mem_Ioo R ε hε hεR htinner with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          R = ε := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 R αs = positiveAxisKeyhole R ε s := hsPath.symm
          _ = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos (lt_trans hε hεR), abs_of_pos hε] using hnorm'
      have : False := by
        linarith [hεR, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext ht14
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_lower_inner_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 4 := by simpa using congrArg Subtype.val hsEq
        linarith [hsouter.1]
      exact this.elim
    · rcases positive_axis_keyhole_eq_lower_lip_circleMap_of_mem_Ioo R ε hε hεR htlower with
        ⟨ρt, hρt, htPath⟩
      have hnorm :
          R = ρt := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 R αs = positiveAxisKeyhole R ε s := hsPath.symm
          _ = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ρt (-positiveAxisKeyholeAngle R ε) := htPath
        simpa [norm_circleMap_zero, abs_of_pos (lt_trans hε hεR), abs_of_pos (lt_trans hε hρt.1)] using hnorm'
      have : False := by
        linarith [hρt.2, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext ht12
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_lower_outer_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 2 := by simpa using congrArg Subtype.val hsEq
        linarith [hsouter.1]
      exact this.elim
    · left
      exact positiveAxisKeyhole_same_branch_injective R ε hε hεR
        (Or.inr <| Or.inr <| Or.inr ⟨hsouter, htouter⟩) hst
    · have htEq : t = (1 : I) := Subtype.ext ht1
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.2.2
      have : False := by
        rcases (positiveAxisKeyhole_eq_upper_outer_corner_iff R ε hε hεR).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsouter.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsouter.2]
      exact this.elim
  · have hsEq : s = (1 : I) := Subtype.ext hs1
    -- The terminal endpoint is the second parameter for the same upper outer corner.
    have htCorner :
        positiveAxisKeyhole R ε t = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
      calc
        positiveAxisKeyhole R ε t = positiveAxisKeyhole R ε s := hst.symm
        _ = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
            simpa [hsEq] using hbreak.2.2.2.2
    rcases (positiveAxisKeyhole_eq_upper_outer_corner_iff R ε hε hεR).1 htCorner with ht0 | ht1
    · right
      right
      simpa [hsEq, ht0]
    · left
      simpa [hsEq, ht1]

/-- Helper for Remark III.6-extra-7: every regular interior parameter of the positive-axis
keyhole contour admits a local boundary-straightening chart for the wedge-annulus it bounds. -/
theorem positiveAxisKeyhole_exists_boundary_straightening_at_regular_point
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀)
    (hderiv :
      derivWithin ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ ≠ 0) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (positiveAxisWedgeAnnulus R ε)
        ((positiveAxisKeyhole R ε).toClosedPath.realCurve) t₀ δ := by
  -- Route correction: dispatch first to the open branch containing the regular parameter, then
  -- use the matching slit-lip or circular-arc chart package.
  -- TODO: apply `positiveAxisKeyhole_regular_parameter_mem_open_branch` and build the explicit
  -- ray-strip and radial-strip charts for the four source branches.
  let _ := ht₀
  let _ := hdiff
  let _ := hderiv
  sorry

/-- Helper for Remark III.6-extra-7: for fixed `0 < ε < R`, the positive-axis keyhole contour is
the oriented boundary of the explicit slit wedge-annulus. -/
theorem positiveAxisKeyhole_isOrientedBoundaryOf_positiveAxisWedgeAnnulus
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    IsOrientedBoundaryOf (positiveAxisWedgeAnnulus R ε)
      (fun _ : Unit ↦ (positiveAxisKeyhole R ε).toClosedPath) := by
  classical
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (positiveAxisKeyhole R ε).toClosedPath
  change IsOrientedBoundaryOf (positiveAxisWedgeAnnulus R ε) Γ
  -- Route correction: once the frontier, simplicity, and local-chart packages are isolated, the
  -- owner theorem is just the singleton-family `IsOrientedBoundaryOf` constructor.
  refine
    { isCompact := ?_
      piecewiseDifferentiable := ?_
      simple_loops := ?_
      pairwiseDisjoint_ranges := ?_
      iUnion_range_eq_frontier := ?_
      exists_boundary_chart_at_regular_point := ?_ }
  · -- The wedge-annulus owner is already packaged as a compact set.
    simpa using isCompact_positiveAxisWedgeAnnulus R ε
  · rintro ⟨⟩
    -- The singleton loop inherits the explicit piecewise differentiability of the keyhole path.
    simpa [Γ, Path.toClosedPath] using positiveAxisKeyhole_isPiecewiseDifferentiable R ε
  · rintro ⟨⟩ s t hst
    -- Delegate contour simplicity to the standalone branchwise equality dispatcher.
    rcases positiveAxisKeyhole_simple_eq_or_endpoints hε hεR hst with hEq | hst01 | hst10
    · exact Or.inl hEq
    · exact Or.inr <| Or.inl <| by
        rcases hst01 with ⟨hs, ht⟩
        simpa [hs, ht]
    · exact Or.inr <| Or.inr <| by
        rcases hst10 with ⟨hs, ht⟩
        simpa [hs, ht]
  · intro i j hij
    -- A singleton family is pairwise disjoint for the trivial reason.
    exact (hij rfl).elim
  · have hboundary :
        (⋃ i : Unit, Set.range ((Γ i).toPath)) = Set.range (positiveAxisKeyhole R ε) := by
      -- Collapse the singleton family range back to the explicit keyhole contour range.
      simpa [Γ] using positiveAxisKeyhole_singleton_iUnion_range R ε
    -- Rewrite the explicit contour range as the frontier of the wedge-annulus owner.
    simpa [positiveAxisWedgeAnnulus_frontier_eq_range R ε hε hεR] using hboundary
  · rintro ⟨⟩ t₀ ht₀ hdiff hderiv
    -- Delegate the regular-point chart to the branchwise boundary-straightening theorem.
    exact positiveAxisKeyhole_exists_boundary_straightening_at_regular_point
      R ε hε hεR ht₀ hdiff hderiv

/-- Helper for Remark III.6-extra-7: after choosing the source-faithful scale `ε = 1 / R`, the
positive-axis keyhole eventually carries both the boundary-owner data and the isolated residue
circles needed for the residue theorem. -/
lemma eventually_large_keyhole_parameters_with_isolated_residue_data
    (P Q : Polynomial ℂ) {s : Finset ℂ} (residue : ℂ → ℂ)
    (hresidueG :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          shiftedLogDomain
          shiftedLogDomain
          s
          (shiftedLogRationalNormalForm P Q)
          z
          (residue z)) :
    ∀ᶠ R : ℝ in atTop,
      let ε := 1 / R
      1 < R ∧
        IsOrientedBoundaryOf
          (positiveAxisWedgeAnnulus R ε)
          (fun _ : Unit ↦ (positiveAxisKeyhole R ε).toClosedPath) ∧
        positiveAxisWedgeAnnulus R ε ⊆ shiftedLogDomain ∧
        ∀ z ∈ s,
          IsolatedLocalResidueCircle
            (positiveAxisWedgeAnnulus R ε)
            shiftedLogDomain
            s
            (shiftedLogRationalNormalForm P Q)
            z
            (residue z) := by
  -- TODO: shrink the source residue circles once, then choose `R` large enough that the fixed
  -- circles lie inside `positiveAxisWedgeAnnulus R (1 / R)` and stay away from the slit wedge.
  let _ := hresidueG
  sorry

/-- Helper for Remark III.6-extra-7: the contour integral of the shifted-log normal form over the
keyhole family with `ε = 1 / R` tends to `-(2π i)` times the improper positive-axis integral of
the rational factor. -/
lemma positiveAxisKeyhole_curveIntegral_tendsto_neg_two_pi_I_integral
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    Tendsto
      (fun R : ℝ ↦
        ∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath,
          (((shiftedLogRationalNormalForm P Q) dz) z))
      atTop
      (nhds
        (-(2 * Real.pi * Complex.I : ℂ) *
          ∫ x in Set.Ioi (0 : ℝ), rationalEval P Q (x : ℂ) ∂volume)) := by
  -- TODO: split the keyhole contour into lips and arcs, pair the two lips through the boundary
  -- values of `Complex.log (-z)`, and show the circular contributions vanish from the degree-gap
  -- decay estimate.
  let _ := hdeg
  let _ := hcut'
  sorry

/-- Remark III.6-extra-7: for a rational function `R(z) = P(z) / Q(z)` with `deg Q ≥ deg P + 2`
and no poles on the nonnegative real axis, the keyhole-contour argument gives
`∫_0^∞ R(x) dx = -∑ Res (R(z) log (-z))`, expressed here with the shifted principal branch
`z ↦ Complex.log (-z)` and explicit isolated local residue data for the residue terms. -/
theorem integral_eq_neg_sum_residues_mul_log
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    {s : Finset ℂ}
    (hpoles :
      ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hcut :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) (x : ℂ) < 0)
    (residue : ℂ → ℂ)
    (hresidue :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          shiftedLogDomain
          shiftedLogDomain
          s
          (shiftedLogRationalEval P Q)
          z
          (residue z)) :
    ∫ x in Set.Ioi (0 : ℝ), P.eval (x : ℂ) / Q.eval (x : ℂ) ∂volume =
      -s.sum residue := by
  have hpoles' : ∀ z : ℂ, meromorphicOrderAt (rationalEval P Q) z < 0 ↔ z ∈ s :=
    rationalEval_pole_iff_mem P Q hpoles
  have hcut' : ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0 :=
    rationalEval_not_pole_of_nonneg_real P Q hcut
  have hQ : Q ≠ 0 := denominator_ne_zero_of_degree_gap_two P Q hdeg
  let G : ℂ → ℂ := shiftedLogRationalNormalForm P Q
  have hsDomain : (↑s : Set ℂ) ⊆ shiftedLogDomain :=
    pole_finset_subset_shiftedLogDomain hpoles' hcut'
  have hhol : DifferentiableOn ℂ G (shiftedLogDomain \ (↑s : Set ℂ)) := by
    -- The normal-form correction removes the removable denominator-root obstruction on the slit
    -- domain, leaving a punctured-holomorphic integrand for the residue theorem.
    simpa [G] using shiftedLogRationalNF_differentiableOn_shiftedLogDomain_off_poles P Q hQ hpoles'
  have htrailing :
      ∀ z ∈ s,
        meromorphicTrailingCoeffAt G z =
          meromorphicTrailingCoeffAt (shiftedLogRationalEval P Q) z := by
    intro z hz
    exact meromorphicTrailingCoeffAt_shiftedLogRationalNormalForm_eq P Q (hsDomain hz)
  have hresidueG :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          shiftedLogDomain
          shiftedLogDomain
          s
          G
          z
          (residue z) := by
    -- Transfer the given source-side residue circles to the meromorphic normal form before any
    -- contour geometry or limiting argument is invoked.
    simpa [G] using
      shiftedLogRationalNormalForm_isolatedLocalResidueCircle
        P Q hQ hpoles' residue hresidue
  let F : ℝ → ℂ := fun R ↦
    ∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath,
      ((G dz) z)
  have hresidue_tendsto :
      Tendsto F atTop (nhds ((2 * Real.pi * Complex.I : ℂ) * s.sum residue)) := by
    have hEventuallyEq :
        F =ᶠ[atTop] fun _ : ℝ ↦ (2 * Real.pi * Complex.I : ℂ) * s.sum residue := by
      -- Route correction: keep the contour parameter `R` alive until the end, so the residue
      -- identity is an eventual constant family rather than a frozen one-contour statement.
      filter_upwards
        [eventually_large_keyhole_parameters_with_isolated_residue_data P Q residue hresidueG]
        with R hR
      dsimp only at hR
      rcases hR with ⟨hRgt1, hΓ, hKD, hresidueK⟩
      have hboundary :
          ∑ i : Unit,
            ∫ᶜ z in ((fun _ : Unit ↦ (positiveAxisKeyhole R (1 / R)).toClosedPath) i).toPath,
              ((G dz) z) =
            (2 * Real.pi * Complex.I : ℂ) * Finset.sum s residue := by
        -- For each sufficiently large keyhole, the imported residue theorem identifies the
        -- boundary integral with the finite residue sum.
        exact orientedBoundary_sum_curveIntegral_eq_two_pi_I_mul_sum_residue
          (Γ := fun _ : Unit ↦ (positiveAxisKeyhole R (1 / R)).toClosedPath)
          (K := positiveAxisWedgeAnnulus R (1 / R)) (D := shiftedLogDomain)
          (f := G) (s := s) (residue := residue)
          hΓ hKD isOpen_shiftedLogDomain hhol hresidueK
      -- Collapse the singleton boundary family back to the explicit keyhole curve integral.
      simpa [F] using hboundary
    -- An eventually constant function converges to its eventual value.
    exact Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds
  have hcontour_tendsto :
      Tendsto F atTop
        (nhds (-(2 * Real.pi * Complex.I : ℂ) *
          ∫ x in Set.Ioi (0 : ℝ), rationalEval P Q (x : ℂ) ∂volume)) := by
    -- The remaining analytic input is the keyhole limit computation for the explicit contour.
    simpa [F, G] using
      positiveAxisKeyhole_curveIntegral_tendsto_neg_two_pi_I_integral P Q hdeg hcut'
  have hlimit_eq :
      (-(2 * Real.pi * Complex.I : ℂ)) *
          ∫ x in Set.Ioi (0 : ℝ), rationalEval P Q (x : ℂ) ∂volume =
        (2 * Real.pi * Complex.I : ℂ) * s.sum residue := by
    -- The explicit contour family has both the residue-theorem limit and the source contour limit.
    exact tendsto_nhds_unique hcontour_tendsto hresidue_tendsto
  let c : ℂ := 2 * Real.pi * Complex.I
  have hc_ne : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hcancel :
      -(∫ x in Set.Ioi (0 : ℝ), rationalEval P Q (x : ℂ) ∂volume) = s.sum residue := by
    -- Rewrite the left-hand side as `c * (-I)` and cancel the common nonzero factor `c`.
    have hrewrite :
        c * (-(∫ x in Set.Ioi (0 : ℝ), rationalEval P Q (x : ℂ) ∂volume)) =
          c * s.sum residue := by
      simpa [c, neg_mul, mul_assoc] using hlimit_eq
    exact mul_left_cancel₀ hc_ne hrewrite
  have htarget :
      ∫ x in Set.Ioi (0 : ℝ), rationalEval P Q (x : ℂ) ∂volume = -s.sum residue := by
    -- Negate the already-cancelled equality to put the conclusion in the textbook form.
    simpa using congrArg Neg.neg hcancel
  -- Unfold `rationalEval` once more to recover the theorem statement verbatim.
  simpa [rationalEval] using htarget
