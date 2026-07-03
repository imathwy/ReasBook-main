import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0001_Definition_II_1_extra_1»
import DifferentialForms_Cartan_1970.II.section05.«0003_Lemma_II_1_extra_3»
import DifferentialForms_Cartan_1970.III.section11.«0003_Theorem_III_5_extra_2»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Complex MeasureTheory
open scoped Real unitInterval

-- Semantic recall note: `lean_leansearch` is unavailable in this environment, so the path and
-- contour-integral API choices were checked against local `Path`/`circleMap` precedent,
-- mathlib's `curveIntegral`/`dz` notation, and the principal-branch `Complex.log` slit-plane API.

/-- The keyhole contour `δ(r, ε)` from Exercise 21, modeled as the boundary of a slit annulus for
the principal branch of `Complex.log`: it runs down the upper lip of the negative-axis slit, once
around the circle of radius `ε` clockwise, back along the lower lip, and finally once around the
circle of radius `r` anticlockwise. The lips lie at arguments `±(π - θ)` with
`θ = arctan (ε / r)`, so the contour keeps the two boundary values of `Complex.log` distinct
instead of retracing the branch cut itself. -/
def exercise21Delta (r ε : ℝ) :
    let θ := Real.arctan (ε / r)
    Path (circleMap 0 r (Real.pi - θ)) (circleMap 0 r (Real.pi - θ)) :=
  let θ := Real.arctan (ε / r)
  let upper : Path (circleMap 0 r (Real.pi - θ)) (circleMap 0 ε (Real.pi - θ)) :=
    Path.segment (circleMap 0 r (Real.pi - θ)) (circleMap 0 ε (Real.pi - θ))
  let inner : Path (circleMap 0 ε (Real.pi - θ)) (circleMap 0 ε (-Real.pi + θ)) :=
    (Path.segment (Real.pi - θ) (-Real.pi + θ)).map (continuous_circleMap 0 ε)
  let lower : Path (circleMap 0 ε (-Real.pi + θ)) (circleMap 0 r (-Real.pi + θ)) :=
    Path.segment (circleMap 0 ε (-Real.pi + θ)) (circleMap 0 r (-Real.pi + θ))
  let outer : Path (circleMap 0 r (-Real.pi + θ)) (circleMap 0 r (Real.pi - θ)) :=
    (Path.segment (-Real.pi + θ) (Real.pi - θ)).map (continuous_circleMap 0 r)
  ((upper.trans inner).trans lower).trans outer

/-- Helper for `exercise21Delta`: unfold the explicit concatenation of the two slit-lip segments
and the two circular arcs making up the keyhole contour. -/
theorem exercise21Delta_def (r ε : ℝ) :
    exercise21Delta r ε =
      let θ := Real.arctan (ε / r)
      let upper : Path (circleMap 0 r (Real.pi - θ)) (circleMap 0 ε (Real.pi - θ)) :=
        Path.segment (circleMap 0 r (Real.pi - θ)) (circleMap 0 ε (Real.pi - θ))
      let inner : Path (circleMap 0 ε (Real.pi - θ)) (circleMap 0 ε (-Real.pi + θ)) :=
        (Path.segment (Real.pi - θ) (-Real.pi + θ)).map (continuous_circleMap 0 ε)
      let lower : Path (circleMap 0 ε (-Real.pi + θ)) (circleMap 0 r (-Real.pi + θ)) :=
        Path.segment (circleMap 0 ε (-Real.pi + θ)) (circleMap 0 r (-Real.pi + θ))
      let outer : Path (circleMap 0 r (-Real.pi + θ)) (circleMap 0 r (Real.pi - θ)) :=
        (Path.segment (-Real.pi + θ) (Real.pi - θ)).map (continuous_circleMap 0 r)
      ((upper.trans inner).trans lower).trans outer := rfl

/-- Helper for Exercise 21: on the first quarter-break interval, the explicit keyhole path follows
the upper slit lip with the affine reparametrization `t ↦ 8 t`. -/
lemma exercise21Delta_eq_on_upper_lip (r ε : ℝ) :
    Set.EqOn (exercise21Delta r ε).extend
      (fun t ↦
        AffineMap.lineMap
          (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
          (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
          (8 * t))
      (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) := by
  intro t ht
  let θ := Real.arctan (ε / r)
  let upper : Path (circleMap 0 r (Real.pi - θ)) (circleMap 0 ε (Real.pi - θ)) :=
    Path.segment (circleMap 0 r (Real.pi - θ)) (circleMap 0 ε (Real.pi - θ))
  let inner : Path (circleMap 0 ε (Real.pi - θ)) (circleMap 0 ε (-Real.pi + θ)) :=
    (Path.segment (Real.pi - θ) (-Real.pi + θ)).map (continuous_circleMap 0 ε)
  let lower : Path (circleMap 0 ε (-Real.pi + θ)) (circleMap 0 r (-Real.pi + θ)) :=
    Path.segment (circleMap 0 ε (-Real.pi + θ)) (circleMap 0 r (-Real.pi + θ))
  let outer : Path (circleMap 0 r (-Real.pi + θ)) (circleMap 0 r (Real.pi - θ)) :=
    (Path.segment (-Real.pi + θ) (Real.pi - θ)).map (continuous_circleMap 0 r)
  let γ₂ : Path (circleMap 0 r (Real.pi - θ)) (circleMap 0 r (-Real.pi + θ)) :=
    (upper.trans inner).trans lower
  -- Peel off the three concatenations until only the upper radial segment remains.
  have houter :
      (exercise21Delta r ε).extend t = γ₂.extend (2 * t) := by
    dsimp [exercise21Delta, θ, upper, inner, lower, outer, γ₂]
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
    _ = AffineMap.lineMap (circleMap 0 r (Real.pi - θ)) (circleMap 0 ε (Real.pi - θ)) (8 * t) := by
          simpa [upper] using
            Path.eqOn_extend_segment (circleMap 0 r (Real.pi - θ))
              (circleMap 0 ε (Real.pi - θ)) hI

/-- Helper for Exercise 21: on the second interval, the explicit keyhole path follows the
clockwise inner circle with the affine angle parameter `t ↦ 8 t - 1`. -/
lemma exercise21Delta_eq_on_inner_arc (r ε : ℝ) :
    Set.EqOn (exercise21Delta r ε).extend
      (fun t ↦
        circleMap 0 ε
          (AffineMap.lineMap
            (Real.pi - Real.arctan (ε / r))
            (-Real.pi + Real.arctan (ε / r))
            (8 * t - 1)))
      (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) := by
  intro t ht
  let θ := Real.arctan (ε / r)
  let upper : Path (circleMap 0 r (Real.pi - θ)) (circleMap 0 ε (Real.pi - θ)) :=
    Path.segment (circleMap 0 r (Real.pi - θ)) (circleMap 0 ε (Real.pi - θ))
  let inner : Path (circleMap 0 ε (Real.pi - θ)) (circleMap 0 ε (-Real.pi + θ)) :=
    (Path.segment (Real.pi - θ) (-Real.pi + θ)).map (continuous_circleMap 0 ε)
  let lower : Path (circleMap 0 ε (-Real.pi + θ)) (circleMap 0 r (-Real.pi + θ)) :=
    Path.segment (circleMap 0 ε (-Real.pi + θ)) (circleMap 0 r (-Real.pi + θ))
  let outer : Path (circleMap 0 r (-Real.pi + θ)) (circleMap 0 r (Real.pi - θ)) :=
    (Path.segment (-Real.pi + θ) (Real.pi - θ)).map (continuous_circleMap 0 r)
  let γ₂ : Path (circleMap 0 r (Real.pi - θ)) (circleMap 0 r (-Real.pi + θ)) :=
    (upper.trans inner).trans lower
  -- Peel off the outer concatenations, then switch to the second half of `upper.trans inner`.
  have houter :
      (exercise21Delta r ε).extend t = γ₂.extend (2 * t) := by
    dsimp [exercise21Delta, θ, upper, inner, lower, outer, γ₂]
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
          ((Path.segment (Real.pi - θ) (-Real.pi + θ)) ⟨2 * (2 * (2 * t)) - 1, hI'⟩) := by
          simp [inner, Path.map_coe]
    _ = circleMap 0 ε
          ((Path.segment (Real.pi - θ) (-Real.pi + θ)).extend (2 * (2 * (2 * t)) - 1)) := by
          rw [Path.extend_apply]
    _ = circleMap 0 ε
          ((Path.segment (Real.pi - θ) (-Real.pi + θ)).extend (8 * t - 1)) := by
          congr 1
          ring
    _ = circleMap 0 ε (AffineMap.lineMap (Real.pi - θ) (-Real.pi + θ) (8 * t - 1)) := by
          exact congrArg (circleMap 0 ε)
            (Path.eqOn_extend_segment (Real.pi - θ) (-Real.pi + θ) hI)

/-- Helper for Exercise 21: on the third interval, the explicit keyhole path follows the lower
slit lip with the affine reparametrization `t ↦ 4 t - 1`. -/
lemma exercise21Delta_eq_on_lower_lip (r ε : ℝ) :
    Set.EqOn (exercise21Delta r ε).extend
      (fun t ↦
        AffineMap.lineMap
          (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
          (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
          (4 * t - 1))
      (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) := by
  intro t ht
  let θ := Real.arctan (ε / r)
  let upper : Path (circleMap 0 r (Real.pi - θ)) (circleMap 0 ε (Real.pi - θ)) :=
    Path.segment (circleMap 0 r (Real.pi - θ)) (circleMap 0 ε (Real.pi - θ))
  let inner : Path (circleMap 0 ε (Real.pi - θ)) (circleMap 0 ε (-Real.pi + θ)) :=
    (Path.segment (Real.pi - θ) (-Real.pi + θ)).map (continuous_circleMap 0 ε)
  let lower : Path (circleMap 0 ε (-Real.pi + θ)) (circleMap 0 r (-Real.pi + θ)) :=
    Path.segment (circleMap 0 ε (-Real.pi + θ)) (circleMap 0 r (-Real.pi + θ))
  let outer : Path (circleMap 0 r (-Real.pi + θ)) (circleMap 0 r (Real.pi - θ)) :=
    (Path.segment (-Real.pi + θ) (Real.pi - θ)).map (continuous_circleMap 0 r)
  let γ₂ : Path (circleMap 0 r (Real.pi - θ)) (circleMap 0 r (-Real.pi + θ)) :=
    (upper.trans inner).trans lower
  -- After the first break point of the outer concatenation, the motion is already on the lower lip.
  have houter :
      (exercise21Delta r ε).extend t = γ₂.extend (2 * t) := by
    dsimp [exercise21Delta, θ, upper, inner, lower, outer, γ₂]
    exact Path.extend_trans_of_le_half
      (γ₁ := (upper.trans inner).trans lower) (γ₂ := outer) ht.2
  have hmid :
      γ₂.extend (2 * t) = lower.extend (2 * (2 * t) - 1) := by
    dsimp [γ₂]
    exact Path.extend_trans_of_half_le (γ₁ := upper.trans inner) (γ₂ := lower)
      (by linarith [ht.1])
  have hI : 4 * t - 1 ∈ I := by
    constructor <;> linarith [ht.1, ht.2]
  have hI' : 2 * (2 * t) - 1 ∈ I := by
    constructor <;> linarith [ht.1, ht.2]
  rw [houter, hmid]
  -- Reduce again to the explicit segment-extension formula.
  calc
    lower.extend (2 * (2 * t) - 1)
        = lower.extend (4 * t - 1) := by
            congr 1
            ring
    _ = AffineMap.lineMap
          (circleMap 0 ε (-Real.pi + θ))
          (circleMap 0 r (-Real.pi + θ))
          (4 * t - 1) := by
            simpa [lower] using
              Path.eqOn_extend_segment
                (circleMap 0 ε (-Real.pi + θ))
                (circleMap 0 r (-Real.pi + θ))
                hI

/-- Helper for Exercise 21: on the final interval, the explicit keyhole path follows the outer
circle with the affine angle parameter `t ↦ 2 t - 1`. -/
lemma exercise21Delta_eq_on_outer_arc (r ε : ℝ) :
    Set.EqOn (exercise21Delta r ε).extend
      (fun t ↦
        circleMap 0 r
          (AffineMap.lineMap
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r))
            (2 * t - 1)))
      (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) := by
  intro t ht
  let θ := Real.arctan (ε / r)
  let upper : Path (circleMap 0 r (Real.pi - θ)) (circleMap 0 ε (Real.pi - θ)) :=
    Path.segment (circleMap 0 r (Real.pi - θ)) (circleMap 0 ε (Real.pi - θ))
  let inner : Path (circleMap 0 ε (Real.pi - θ)) (circleMap 0 ε (-Real.pi + θ)) :=
    (Path.segment (Real.pi - θ) (-Real.pi + θ)).map (continuous_circleMap 0 ε)
  let lower : Path (circleMap 0 ε (-Real.pi + θ)) (circleMap 0 r (-Real.pi + θ)) :=
    Path.segment (circleMap 0 ε (-Real.pi + θ)) (circleMap 0 r (-Real.pi + θ))
  let outer : Path (circleMap 0 r (-Real.pi + θ)) (circleMap 0 r (Real.pi - θ)) :=
    (Path.segment (-Real.pi + θ) (Real.pi - θ)).map (continuous_circleMap 0 r)
  -- Route correction: isolate the outer arc directly from the last concatenation instead of
  -- forcing later chart proofs to keep unfolding the whole nested keyhole path.
  have houter :
      (exercise21Delta r ε).extend t = outer.extend (2 * t - 1) := by
    dsimp [exercise21Delta, θ, upper, inner, lower, outer]
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
    _ = circleMap 0 r ((Path.segment (-Real.pi + θ) (Real.pi - θ)) ⟨2 * t - 1, hI⟩) := by
          simp [outer, Path.map_coe]
    _ = circleMap 0 r ((Path.segment (-Real.pi + θ) (Real.pi - θ)).extend (2 * t - 1)) := by
          rw [Path.extend_apply]
    _ = circleMap 0 r (AffineMap.lineMap (-Real.pi + θ) (Real.pi - θ) (2 * t - 1)) := by
          exact congrArg (circleMap 0 r)
            (Path.eqOn_extend_segment (-Real.pi + θ) (Real.pi - θ) hI)

/-- Helper for Exercise 21: on the first interval, the real-plane closed-curve model is the upper
slit lip written in explicit coordinates. -/
lemma exercise21Delta_realCurve_eq_on_upper_lip (r ε : ℝ) :
    Set.EqOn ((exercise21Delta r ε).toClosedPath.realCurve)
      (fun t ↦
        Complex.equivRealProd
          (AffineMap.lineMap
            (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
            (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
            (8 * t)))
      (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) := by
  intro t ht
  -- Pass from the complex-valued path formula to the real-plane parametrization by `equivRealProd`.
  simpa [ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
    congrArg Complex.equivRealProd (exercise21Delta_eq_on_upper_lip r ε ht)

/-- Helper for Exercise 21: undoing `Complex.equivRealProd` on the upper-lip branch exposes the
fixed-angle radial formula needed by the later strip chart. -/
lemma exercise21Delta_realCurve_symm_eq_on_upper_lip (r ε : ℝ) :
    Set.EqOn
      (fun t ↦ Complex.equivRealProdCLM.symm (((exercise21Delta r ε).toClosedPath.realCurve) t))
      (fun t ↦
        circleMap 0 (AffineMap.lineMap r ε (8 * t))
          (Real.pi - Real.arctan (ε / r)))
      (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) := by
  intro t ht
  -- Strip off the real-plane identification first, then rewrite interpolation on a fixed ray as
  -- pure radius interpolation.
  have hcurve := exercise21Delta_realCurve_eq_on_upper_lip r ε ht
  have hray :
      AffineMap.lineMap
          (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
          (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
          (8 * t) =
        circleMap 0 (AffineMap.lineMap r ε (8 * t))
          (Real.pi - Real.arctan (ε / r)) := by
    -- On a fixed ray, affine interpolation between the endpoints only changes the radius.
    rw [Complex.ext_iff]
    constructor <;>
      simp [circleMap_zero_re, circleMap_zero_im, AffineMap.lineMap_apply_module, smul_eq_mul,
        add_mul] <;>
      ring
  calc
    Complex.equivRealProdCLM.symm (((exercise21Delta r ε).toClosedPath.realCurve) t)
        = AffineMap.lineMap
            (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
            (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
            (8 * t) := by
              simpa using congrArg Complex.equivRealProdCLM.symm hcurve
    _ = circleMap 0 (AffineMap.lineMap r ε (8 * t))
          (Real.pi - Real.arctan (ε / r)) := hray

/-- Helper for Exercise 21: on the second interval, the real-plane closed-curve model is the
clockwise inner circular arc written in explicit coordinates. -/
lemma exercise21Delta_realCurve_eq_on_inner_arc (r ε : ℝ) :
    Set.EqOn ((exercise21Delta r ε).toClosedPath.realCurve)
      (fun t ↦
        Complex.equivRealProd
          (circleMap 0 ε
            (AffineMap.lineMap
              (Real.pi - Real.arctan (ε / r))
              (-Real.pi + Real.arctan (ε / r))
              (8 * t - 1))))
      (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) := by
  intro t ht
  -- The real-curve owner is just the complex formula viewed in `Plane`.
  simpa [ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
    congrArg Complex.equivRealProd (exercise21Delta_eq_on_inner_arc r ε ht)

/-- Helper for Exercise 21: undoing `Complex.equivRealProd` on the inner arc exposes the explicit
angle interpolation that later radial charts use directly. -/
lemma exercise21Delta_realCurve_symm_eq_on_inner_arc (r ε : ℝ) :
    Set.EqOn
      (fun t ↦ Complex.equivRealProdCLM.symm (((exercise21Delta r ε).toClosedPath.realCurve) t))
      (fun t ↦
        circleMap 0 ε
          (AffineMap.lineMap
            (Real.pi - Real.arctan (ε / r))
            (-Real.pi + Real.arctan (ε / r))
            (8 * t - 1)))
      (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) := by
  intro t ht
  -- On the circular branch, the only transport to remove is the `Complex.equivRealProd` wrapper.
  simpa using
    congrArg Complex.equivRealProdCLM.symm (exercise21Delta_realCurve_eq_on_inner_arc r ε ht)

/-- Helper for Exercise 21: on the third interval, the real-plane closed-curve model is the lower
slit lip written in explicit coordinates. -/
lemma exercise21Delta_realCurve_eq_on_lower_lip (r ε : ℝ) :
    Set.EqOn ((exercise21Delta r ε).toClosedPath.realCurve)
      (fun t ↦
        Complex.equivRealProd
          (AffineMap.lineMap
            (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
            (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
            (4 * t - 1)))
      (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) := by
  intro t ht
  -- The lower lip uses the same `equivRealProd` bridge from the complex path formula.
  simpa [ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
    congrArg Complex.equivRealProd (exercise21Delta_eq_on_lower_lip r ε ht)

/-- Helper for Exercise 21: undoing `Complex.equivRealProd` on the lower-lip branch again
reduces the branch formula to a fixed-angle radial interpolation. -/
lemma exercise21Delta_realCurve_symm_eq_on_lower_lip (r ε : ℝ) :
    Set.EqOn
      (fun t ↦ Complex.equivRealProdCLM.symm (((exercise21Delta r ε).toClosedPath.realCurve) t))
      (fun t ↦
        circleMap 0 (AffineMap.lineMap ε r (4 * t - 1))
          (-Real.pi + Real.arctan (ε / r)))
      (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) := by
  intro t ht
  -- As on the upper lip, fixed-angle affine interpolation is equivalent to radius interpolation.
  have hcurve := exercise21Delta_realCurve_eq_on_lower_lip r ε ht
  have hray :
      AffineMap.lineMap
          (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
          (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
          (4 * t - 1) =
        circleMap 0 (AffineMap.lineMap ε r (4 * t - 1))
          (-Real.pi + Real.arctan (ε / r)) := by
    -- The reflected lower-lip branch has the same fixed-angle radial interpolation shape.
    rw [Complex.ext_iff]
    constructor <;>
      simp [circleMap_zero_re, circleMap_zero_im, AffineMap.lineMap_apply_module, smul_eq_mul,
        add_mul] <;>
      ring
  calc
    Complex.equivRealProdCLM.symm (((exercise21Delta r ε).toClosedPath.realCurve) t)
        = AffineMap.lineMap
            (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
            (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
            (4 * t - 1) := by
              simpa using congrArg Complex.equivRealProdCLM.symm hcurve
    _ = circleMap 0 (AffineMap.lineMap ε r (4 * t - 1))
          (-Real.pi + Real.arctan (ε / r)) := hray

/-- Helper for Exercise 21: on the final interval, the real-plane closed-curve model is the outer
circular arc written in explicit coordinates. -/
lemma exercise21Delta_realCurve_eq_on_outer_arc (r ε : ℝ) :
    Set.EqOn ((exercise21Delta r ε).toClosedPath.realCurve)
      (fun t ↦
        Complex.equivRealProd
          (circleMap 0 r
            (AffineMap.lineMap
              (-Real.pi + Real.arctan (ε / r))
              (Real.pi - Real.arctan (ε / r))
              (2 * t - 1))))
      (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) := by
  intro t ht
  -- The final branch is again the complex outer-arc formula viewed in `Plane`.
  simpa [ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
    congrArg Complex.equivRealProd (exercise21Delta_eq_on_outer_arc r ε ht)

/-- Helper for Exercise 21: undoing `Complex.equivRealProd` on the outer arc leaves the explicit
angle interpolation used by the radial boundary charts. -/
lemma exercise21Delta_realCurve_symm_eq_on_outer_arc (r ε : ℝ) :
    Set.EqOn
      (fun t ↦ Complex.equivRealProdCLM.symm (((exercise21Delta r ε).toClosedPath.realCurve) t))
      (fun t ↦
        circleMap 0 r
          (AffineMap.lineMap
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r))
            (2 * t - 1)))
      (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) := by
  intro t ht
  -- The outer circular branch needs only the same removal of the real-plane wrapper.
  simpa using
    congrArg Complex.equivRealProdCLM.symm (exercise21Delta_realCurve_eq_on_outer_arc r ε ht)

/-- Helper for Exercise 21: package the four closed-interval formulas for the real-plane
parametrization of `exercise21Delta`. These explicit branch owners are the stable interface for
the later slit-annulus geometry, so downstream proofs do not keep unfolding `Path.trans`. -/
lemma exercise21Delta_realCurve_eqOn_piece_intervals (r ε : ℝ) :
    Set.EqOn ((exercise21Delta r ε).toClosedPath.realCurve)
        (fun t ↦
          Complex.equivRealProd
            (AffineMap.lineMap
              (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
              (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
              (8 * t)))
        (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) ∧
      Set.EqOn ((exercise21Delta r ε).toClosedPath.realCurve)
        (fun t ↦
          Complex.equivRealProd
            (circleMap 0 ε
              (AffineMap.lineMap
                (Real.pi - Real.arctan (ε / r))
                (-Real.pi + Real.arctan (ε / r))
                (8 * t - 1))))
        (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) ∧
      Set.EqOn ((exercise21Delta r ε).toClosedPath.realCurve)
        (fun t ↦
          Complex.equivRealProd
            (AffineMap.lineMap
              (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
              (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
              (4 * t - 1)))
        (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) ∧
      Set.EqOn ((exercise21Delta r ε).toClosedPath.realCurve)
        (fun t ↦
          Complex.equivRealProd
            (circleMap 0 r
              (AffineMap.lineMap
                (-Real.pi + Real.arctan (ε / r))
                (Real.pi - Real.arctan (ε / r))
                (2 * t - 1))))
        (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) := by
  -- Bundle the four branch formulas so later geometry can case-split once and work with concrete
  -- branch models instead of the full nested keyhole expression.
  refine ⟨exercise21Delta_realCurve_eq_on_upper_lip r ε,
    exercise21Delta_realCurve_eq_on_inner_arc r ε,
    exercise21Delta_realCurve_eq_on_lower_lip r ε,
    exercise21Delta_realCurve_eq_on_outer_arc r ε⟩

/-- Helper for Exercise 21: every parameter in `I` lies on exactly one open branch interval of the
keyhole contour or is one of the five distinguished breakpoint parameters `0`, `1/8`, `1/4`,
`1/2`, `1`. This is the stable interval-splitting interface for the later simple-loop and
boundary-chart arguments. -/
lemma exercise21Delta_parameter_cases (t : I) :
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
      · -- The next breakpoint split isolates `1/8` from the open inner-circle interval.
        rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc ⟨h18', le_of_lt h14⟩ with hEq | hEq | hmem
        · exact Or.inr <| Or.inr <| Or.inl hEq
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hEq
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inl hmem
      · have h14' : 1 / 4 ≤ t.1 := le_of_not_gt h14
        by_cases h12 : t.1 < 1 / 2
        · -- The third split isolates `1/4` from the open lower-lip interval.
          rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc ⟨h14', le_of_lt h12⟩ with hEq | hEq | hmem
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hEq
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hEq
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hmem
        · have h12' : 1 / 2 ≤ t.1 := le_of_not_gt h12
          -- The final split isolates `1/2` from the open outer-circle interval and the endpoint `1`.
          rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc ⟨h12', ht.2.le⟩ with hEq | hEq | hmem
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hEq
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr hEq
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hmem

/-- Helper for Exercise 21: the five distinguished parameters `0`, `1/8`, `1/4`, `1/2`, and `1`
hit exactly the four geometric corners of the keyhole contour in the source order. This packages
the easy endpoint evaluations before the harder converse fiber classification. -/
lemma exercise21Delta_breakpoint_values (r ε : ℝ) :
    exercise21Delta r ε (0 : I) =
        circleMap 0 r (Real.pi - Real.arctan (ε / r)) ∧
      exercise21Delta r ε (⟨(1 / 8 : ℝ), by norm_num⟩ : I) =
        circleMap 0 ε (Real.pi - Real.arctan (ε / r)) ∧
      exercise21Delta r ε (⟨(1 / 4 : ℝ), by norm_num⟩ : I) =
        circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) ∧
      exercise21Delta r ε (⟨(1 / 2 : ℝ), by norm_num⟩ : I) =
        circleMap 0 r (-Real.pi + Real.arctan (ε / r)) ∧
      exercise21Delta r ε (1 : I) =
        circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
  have h0_segment :
      (exercise21Delta r ε).extend 0 =
        AffineMap.lineMap
          (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
          (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
          (8 * (0 : ℝ)) := by
    -- Evaluate the explicit upper-lip formula at the initial parameter.
    simpa using
      (exercise21Delta_eq_on_upper_lip r ε (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 8 : ℝ)))
  have h18_segment :
      (exercise21Delta r ε).extend (1 / 8 : ℝ) =
        AffineMap.lineMap
          (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
          (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
          (8 * (1 / 8 : ℝ)) := by
    -- The end of the upper lip is the first contour corner.
    simpa using
      (exercise21Delta_eq_on_upper_lip r ε
        (by norm_num : (1 / 8 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 8 : ℝ)))
  have h14_arc :
      (exercise21Delta r ε).extend (1 / 4 : ℝ) =
        circleMap 0 ε
          (AffineMap.lineMap
            (Real.pi - Real.arctan (ε / r))
            (-Real.pi + Real.arctan (ε / r))
            (8 * (1 / 4 : ℝ) - 1)) := by
    -- Evaluating the inner arc at its terminal parameter reaches the lower inner corner.
    simpa using
      (exercise21Delta_eq_on_inner_arc r ε
        (by norm_num : (1 / 4 : ℝ) ∈ Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)))
  have h12_segment :
      (exercise21Delta r ε).extend (1 / 2 : ℝ) =
        AffineMap.lineMap
          (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
          (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
          (4 * (1 / 2 : ℝ) - 1) := by
    -- The lower lip ends at the outer lower corner.
    simpa using
      (exercise21Delta_eq_on_lower_lip r ε
        (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)))
  have h1_arc :
      (exercise21Delta r ε).extend (1 : ℝ) =
        circleMap 0 r
          (AffineMap.lineMap
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r))
            (2 * (1 : ℝ) - 1)) := by
    -- The outer arc closes the contour back at its starting point.
    simpa using
      (exercise21Delta_eq_on_outer_arc r ε
        (by norm_num : (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) (1 : ℝ)))
  have h0_path :
      exercise21Delta r ε (0 : I) =
        AffineMap.lineMap
          (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
          (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
          (8 * (0 : ℝ)) := by
    -- Convert the endpoint evaluation from `extend` back to the subtype parameter.
    exact
      (Path.extend_apply (exercise21Delta r ε)
        (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)).symm.trans h0_segment
  have h18_path :
      exercise21Delta r ε (⟨(1 / 8 : ℝ), by norm_num⟩ : I) =
        AffineMap.lineMap
          (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
          (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
          (8 * (1 / 8 : ℝ)) := by
    -- The same bridge is needed at the first interior breakpoint.
    exact
      (Path.extend_apply (exercise21Delta r ε)
        (by norm_num : (1 / 8 : ℝ) ∈ Set.Icc (0 : ℝ) 1)).symm.trans h18_segment
  have h14_path :
      exercise21Delta r ε (⟨(1 / 4 : ℝ), by norm_num⟩ : I) =
        circleMap 0 ε
          (AffineMap.lineMap
            (Real.pi - Real.arctan (ε / r))
            (-Real.pi + Real.arctan (ε / r))
            (8 * (1 / 4 : ℝ) - 1)) := by
    -- Likewise for the lower endpoint of the inner circular arc.
    exact
      (Path.extend_apply (exercise21Delta r ε)
        (by norm_num : (1 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1)).symm.trans h14_arc
  have h12_path :
      exercise21Delta r ε (⟨(1 / 2 : ℝ), by norm_num⟩ : I) =
        AffineMap.lineMap
          (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
          (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
          (4 * (1 / 2 : ℝ) - 1) := by
    -- And again at the endpoint of the lower slit lip.
    exact
      (Path.extend_apply (exercise21Delta r ε)
        (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)).symm.trans h12_segment
  have h1_path :
      exercise21Delta r ε (1 : I) =
        circleMap 0 r
          (AffineMap.lineMap
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r))
            (2 * (1 : ℝ) - 1)) := by
    -- The final bridge closes the loop at the path endpoint.
    exact
      (Path.extend_apply (exercise21Delta r ε)
        (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)).symm.trans h1_arc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- The affine upper-lip segment starts at the outer upper corner.
    simpa [AffineMap.lineMap_apply_zero] using h0_path
  · -- The affine upper-lip segment ends at the inner upper corner.
    simpa [AffineMap.lineMap_apply_one] using h18_path
  · -- The clockwise inner arc ends at angle `-π + θ`.
    have h14_param : (8 * (1 / 4 : ℝ) - 1) = 1 := by norm_num
    rw [h14_param, AffineMap.lineMap_apply_one] at h14_path
    exact h14_path
  · -- The affine lower-lip segment ends at the outer lower corner.
    have h12_param : (4 * (1 / 2 : ℝ) - 1) = 1 := by norm_num
    rw [h12_param, AffineMap.lineMap_apply_one] at h12_path
    exact h12_path
  · -- The outer arc returns to the initial angle `π - θ`.
    have h1_param : (2 * (1 : ℝ) - 1) = 1 := by norm_num
    rw [h1_param, AffineMap.lineMap_apply_one] at h1_path
    exact h1_path

/-- Helper for Exercise 21: points on the upper lip of the negative-axis keyhole lie on the line
`im z = (ε / r) * (-re z)`. This is the first branch invariant used to separate the slit lips from
the circular arcs. -/
lemma exercise21Delta_upper_lip_line (r ε ρ : ℝ) :
    (circleMap 0 ρ (Real.pi - Real.arctan (ε / r))).im =
      -((ε / r) * (circleMap 0 ρ (Real.pi - Real.arctan (ε / r))).re) := by
  -- Unfold the circle coordinates at the upper-lip angle and use the standard arctangent formulas.
  rw [circleMap_zero_im, circleMap_zero_re]
  rw [Real.sin_pi_sub, Real.cos_pi_sub, Real.sin_arctan, Real.cos_arctan]
  ring

/-- Helper for Exercise 21: points on the lower lip of the negative-axis keyhole lie on the line
`im z = (ε / r) * re z`. This is the companion line equation for the lower slit edge. -/
lemma exercise21Delta_lower_lip_line (r ε ρ : ℝ) :
    (circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))).im =
      (ε / r) * (circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))).re := by
  -- Normalize the lower-lip angle to `arctan (ε / r) - π`, then reduce again to the
  -- arctangent identities.
  have hsin :
      Real.sin (-Real.pi + Real.arctan (ε / r)) = -Real.sin (Real.arctan (ε / r)) := by
    rw [show -Real.pi + Real.arctan (ε / r) = Real.arctan (ε / r) - Real.pi by ring]
    simp [Real.sin_sub]
  have hcos :
      Real.cos (-Real.pi + Real.arctan (ε / r)) = -Real.cos (Real.arctan (ε / r)) := by
    rw [show -Real.pi + Real.arctan (ε / r) = Real.arctan (ε / r) - Real.pi by ring]
    simp [Real.cos_sub]
  rw [circleMap_zero_im, circleMap_zero_re, hsin, hcos, Real.sin_arctan, Real.cos_arctan]
  ring

/-- Helper for Exercise 21: every nonzero point on the upper lip has negative real part, so it
lies on the negative-real side of the slit model. -/
lemma exercise21Delta_upper_lip_re_neg
    {r ε ρ : ℝ} (hρ : 0 < ρ) :
    (circleMap 0 ρ (Real.pi - Real.arctan (ε / r))).re < 0 := by
  -- The upper-lip angle differs from `arctan (ε / r)` by `π`, so the cosine changes sign.
  rw [circleMap_zero_re, Real.cos_pi_sub]
  have hpos : 0 < ρ * Real.cos (Real.arctan (ε / r)) := by
    exact mul_pos hρ (Real.cos_arctan_pos (ε / r))
  linarith

/-- Helper for Exercise 21: every nonzero point on the lower lip also has negative real part,
which is the remaining sign condition in the negative-wedge geometry. -/
lemma exercise21Delta_lower_lip_re_neg
    {r ε ρ : ℝ} (hρ : 0 < ρ) :
    (circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))).re < 0 := by
  -- The lower-lip angle is `arctan (ε / r) - π`, so the cosine is the negative of
  -- `cos (arctan (ε / r))`.
  have hcos :
      Real.cos (-Real.pi + Real.arctan (ε / r)) = -Real.cos (Real.arctan (ε / r)) := by
    rw [show -Real.pi + Real.arctan (ε / r) = Real.arctan (ε / r) - Real.pi by ring]
    simp [Real.cos_sub]
  rw [circleMap_zero_re, hcos]
  have hpos : 0 < ρ * Real.cos (Real.arctan (ε / r)) := by
    exact mul_pos hρ (Real.cos_arctan_pos (ε / r))
  linarith

/-- Helper for Exercise 21: the transverse coefficient in the slit-lip normal coordinates is
strictly positive, so the sign of the transverse parameter agrees with the side of the slit. -/
lemma exercise21_lip_transverse_coefficient_pos
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    0 <
      Real.cos (Real.arctan (ε / r)) +
        (ε / r) * Real.sin (Real.arctan (ε / r)) := by
  have hr : 0 < r := lt_trans hε hεr
  have hcos : 0 < Real.cos (Real.arctan (ε / r)) :=
    Real.cos_arctan_pos (ε / r)
  have hratio_nonneg : 0 ≤ ε / r := by
    exact le_of_lt (div_pos hε hr)
  have hsin_nonneg : 0 ≤ Real.sin (Real.arctan (ε / r)) := by
    rw [Real.sin_arctan]
    positivity
  -- The coefficient is the sum of a positive cosine term and a nonnegative slope correction.
  exact add_pos_of_pos_of_nonneg hcos (mul_nonneg hratio_nonneg hsin_nonneg)

/-- Helper for Exercise 21: in the explicit upper-lip normal coordinates, the signed height above
the slit line is a positive multiple of the transverse parameter. This is the core sign identity
for the upper branch chart. -/
lemma exercise21_upper_lip_normal_signed_height
    (r ε ρ s : ℝ) :
    let φ := Real.pi - Real.arctan (ε / r)
    let z := circleMap 0 ρ φ + (s : ℂ) * circleMap 0 1 (φ - Real.pi / 2)
    z.im + (ε / r) * z.re =
      s *
        (Real.cos (Real.arctan (ε / r)) +
          (ε / r) * Real.sin (Real.arctan (ε / r))) := by
  let φ := Real.pi - Real.arctan (ε / r)
  let w : ℂ := circleMap 0 ρ φ
  let n : ℂ := circleMap 0 1 (φ - Real.pi / 2)
  have hw :
      w.im + (ε / r) * w.re = 0 := by
    -- The upper lip itself lies on the boundary line `im z = -(ε / r) re z`.
    have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := ρ)
    simpa [w, φ] using eq_neg_iff_add_eq_zero.mp hline
  have hn :
      n.im + (ε / r) * n.re =
        Real.cos (Real.arctan (ε / r)) +
          (ε / r) * Real.sin (Real.arctan (ε / r)) := by
    -- The chosen upper-lip normal is the `-π/2` rotation of the lip direction.
    dsimp [n, φ]
    rw [circleMap_zero_im, circleMap_zero_re, Real.sin_sub_pi_div_two,
      Real.cos_sub_pi_div_two, Real.sin_pi_sub, Real.cos_pi_sub]
    ring
  -- Split the signed height into the lip contribution, which vanishes, and the normal
  -- contribution, which is exactly the positive transverse coefficient.
  calc
    (w + (s : ℂ) * n).im + (ε / r) * (w + (s : ℂ) * n).re
        = (w.im + (ε / r) * w.re) + s * (n.im + (ε / r) * n.re) := by
            simp [Complex.add_re, Complex.add_im, mul_re, mul_im, Complex.ofReal_re,
              Complex.ofReal_im]
            ring
    _ = s *
        (Real.cos (Real.arctan (ε / r)) +
          (ε / r) * Real.sin (Real.arctan (ε / r))) := by
          rw [hw, hn]
          ring

/-- Helper for Exercise 21: in the explicit lower-lip normal coordinates, the signed height below
the slit line is again a positive multiple of the transverse parameter. This is the matching sign
identity for the lower branch chart. -/
lemma exercise21_lower_lip_normal_signed_height
    (r ε ρ s : ℝ) :
    let φ := -Real.pi + Real.arctan (ε / r)
    let z := circleMap 0 ρ φ + (s : ℂ) * circleMap 0 1 (φ + Real.pi / 2)
    -z.im + (ε / r) * z.re =
      s *
        (Real.cos (Real.arctan (ε / r)) +
          (ε / r) * Real.sin (Real.arctan (ε / r))) := by
  let φ := -Real.pi + Real.arctan (ε / r)
  let w : ℂ := circleMap 0 ρ φ
  let n : ℂ := circleMap 0 1 (φ + Real.pi / 2)
  have hw :
      -w.im + (ε / r) * w.re = 0 := by
    -- The lower lip lies on the companion boundary line `im z = (ε / r) re z`.
    have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := ρ)
    linarith
  have hsin :
      Real.sin (-Real.pi + Real.arctan (ε / r)) =
        -Real.sin (Real.arctan (ε / r)) := by
    rw [show -Real.pi + Real.arctan (ε / r) = Real.arctan (ε / r) - Real.pi by ring]
    simp [Real.sin_sub]
  have hcos :
      Real.cos (-Real.pi + Real.arctan (ε / r)) =
        -Real.cos (Real.arctan (ε / r)) := by
    rw [show -Real.pi + Real.arctan (ε / r) = Real.arctan (ε / r) - Real.pi by ring]
    simp [Real.cos_sub]
  have hn :
      -n.im + (ε / r) * n.re =
        Real.cos (Real.arctan (ε / r)) +
          (ε / r) * Real.sin (Real.arctan (ε / r)) := by
    -- The lower-lip inward normal is the `+π/2` rotation of the lower radial direction.
    dsimp [n, φ]
    rw [circleMap_zero_im, circleMap_zero_re, Real.sin_add_pi_div_two,
      Real.cos_add_pi_div_two, hsin, hcos]
    ring
  -- As on the upper lip, the line contribution vanishes and only the normal coefficient remains.
  calc
    -(w + (s : ℂ) * n).im + (ε / r) * (w + (s : ℂ) * n).re
        = (-w.im + (ε / r) * w.re) + s * (-n.im + (ε / r) * n.re) := by
            simp [Complex.add_re, Complex.add_im, mul_re, mul_im, Complex.ofReal_re,
              Complex.ofReal_im]
            ring
    _ = s *
        (Real.cos (Real.arctan (ε / r)) +
          (ε / r) * Real.sin (Real.arctan (ε / r))) := by
          rw [hw, hn]
          ring

/-- Helper for Exercise 21: affine interpolation between two points on the same ray only changes
the radius, so the angular coordinate stays fixed. This is the transport-stable normalization used
when a branch proof should reason by radius and angle rather than by raw complex affine formulas. -/
lemma exercise21_lineMap_circleMap_same_angle (ρ₀ ρ₁ φ c : ℝ) :
    AffineMap.lineMap (circleMap 0 ρ₀ φ) (circleMap 0 ρ₁ φ) c =
      circleMap 0 (AffineMap.lineMap ρ₀ ρ₁ c) φ := by
  -- Compare real and imaginary parts separately; on a fixed ray, affine interpolation is purely
  -- radial.
  rw [Complex.ext_iff]
  constructor <;>
    simp [circleMap_zero_re, circleMap_zero_im, AffineMap.lineMap_apply_module, smul_eq_mul,
      add_mul] <;>
    ring

/-- Helper for Exercise 21: the opening angle `θ = arctan (ε / r)` of the keyhole contour lies in
`(0, π / 2)` whenever `0 < ε < r`. -/
lemma exercise21_keyhole_angle_bounds {r ε : ℝ}
    (hε : 0 < ε) (hεr : ε < r) :
    0 < Real.arctan (ε / r) ∧ Real.arctan (ε / r) < Real.pi / 2 := by
  -- The keyhole opening is acute because the slope `ε / r` is positive.
  have hr : 0 < r := lt_trans hε hεr
  constructor
  · exact Real.arctan_pos.mpr (div_pos hε hr)
  · exact Real.arctan_lt_pi_div_two (ε / r)

/-- Helper for Exercise 21: an interior point of the upper slit lip is a point on the upper
boundary ray with radius strictly between `ε` and `r`. -/
lemma exercise21Delta_eq_upper_lip_circleMap_of_mem_Ioo
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t : I}
    (ht : t.1 ∈ Set.Ioo (0 : ℝ) (1 / 8)) :
    ∃ ρ ∈ Set.Ioo ε r,
      exercise21Delta r ε t =
        circleMap 0 ρ (Real.pi - Real.arctan (ε / r)) := by
  let ρ : ℝ := AffineMap.lineMap r ε (8 * (t : ℝ))
  have hparam : 8 * (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hρopen : ρ ∈ Set.Ioo ε r := by
    have hseg : ρ ∈ openSegment ℝ r ε := by
      simpa [ρ] using lineMap_mem_openSegment (𝕜 := ℝ) r ε hparam
    have hre : (r : ℝ) ≠ ε := by linarith
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hre] at hseg
    simpa [ρ, min_eq_right (le_of_lt hεr), max_eq_left (le_of_lt hεr)] using hseg
  refine ⟨ρ, hρopen, ?_⟩
  -- Rewrite the open upper branch using the radial parameter supplied by `lineMap`.
  calc
    exercise21Delta r ε t =
        AffineMap.lineMap
          (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
          (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
          (8 * (t : ℝ)) := by
            exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
              exercise21Delta_eq_on_upper_lip r ε (Set.Ioo_subset_Icc_self ht)
    _ = circleMap 0 ρ (Real.pi - Real.arctan (ε / r)) := by
          rw [exercise21_lineMap_circleMap_same_angle]

/-- Helper for Exercise 21: an interior point of the inner arc stays on the circle of radius `ε`
with angle strictly between the two slit-boundary angles. -/
lemma exercise21Delta_eq_inner_arc_circleMap_of_mem_Ioo
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t : I}
    (ht : t.1 ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4)) :
    ∃ α ∈ Set.Ioo (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)),
      exercise21Delta r ε t = circleMap 0 ε α := by
  let α : ℝ :=
    AffineMap.lineMap
      (Real.pi - Real.arctan (ε / r))
      (-Real.pi + Real.arctan (ε / r))
      (8 * (t : ℝ) - 1)
  have hr : 0 < r := lt_trans hε hεr
  have hθ : 0 < Real.arctan (ε / r) ∧ Real.arctan (ε / r) < Real.pi / 2 :=
    exercise21_keyhole_angle_bounds (r := r) (ε := ε) hε hεr
  have hparam : 8 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hαopen :
      α ∈ Set.Ioo (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)) := by
    have hseg :
        α ∈ openSegment ℝ
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r)) := by
      simpa [α] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r))
          hparam
    have hneq :
        Real.pi - Real.arctan (ε / r) ≠ -Real.pi + Real.arctan (ε / r) := by
      nlinarith [hθ.2, Real.pi_pos]
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hneq] at hseg
    have horder :
        -Real.pi + Real.arctan (ε / r) ≤ Real.pi - Real.arctan (ε / r) := by
      nlinarith [hθ.2, Real.pi_pos]
    simpa [α, min_eq_right horder, max_eq_left horder] using hseg
  refine ⟨α, hαopen, ?_⟩
  -- Reduce the open inner branch to its explicit angular parameter.
  exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
    exercise21Delta_eq_on_inner_arc r ε (Set.Ioo_subset_Icc_self ht)

/-- Helper for Exercise 21: an interior point of the lower slit lip is a point on the lower
boundary ray with radius strictly between `ε` and `r`. -/
lemma exercise21Delta_eq_lower_lip_circleMap_of_mem_Ioo
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t : I}
    (ht : t.1 ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)) :
    ∃ ρ ∈ Set.Ioo ε r,
      exercise21Delta r ε t =
        circleMap 0 ρ (-Real.pi + Real.arctan (ε / r)) := by
  let ρ : ℝ := AffineMap.lineMap ε r (4 * (t : ℝ) - 1)
  have hparam : 4 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hρopen : ρ ∈ Set.Ioo ε r := by
    have hseg : ρ ∈ openSegment ℝ ε r := by
      simpa [ρ] using lineMap_mem_openSegment (𝕜 := ℝ) ε r hparam
    have hre : (ε : ℝ) ≠ r := by linarith
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hre] at hseg
    simpa [ρ, min_eq_left (le_of_lt hεr), max_eq_right (le_of_lt hεr)] using hseg
  refine ⟨ρ, hρopen, ?_⟩
  -- Rewrite the open lower branch using the corresponding radial parameter.
  calc
    exercise21Delta r ε t =
        AffineMap.lineMap
          (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
          (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
          (4 * (t : ℝ) - 1) := by
            exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
              exercise21Delta_eq_on_lower_lip r ε (Set.Ioo_subset_Icc_self ht)
    _ = circleMap 0 ρ (-Real.pi + Real.arctan (ε / r)) := by
          rw [exercise21_lineMap_circleMap_same_angle]

/-- Helper for Exercise 21: an interior point of the outer arc stays on the circle of radius `r`
with angle strictly between the two slit-boundary angles. -/
lemma exercise21Delta_eq_outer_arc_circleMap_of_mem_Ioo
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t : I}
    (ht : t.1 ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ)) :
    ∃ α ∈ Set.Ioo (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)),
      exercise21Delta r ε t = circleMap 0 r α := by
  let α : ℝ :=
    AffineMap.lineMap
      (-Real.pi + Real.arctan (ε / r))
      (Real.pi - Real.arctan (ε / r))
      (2 * (t : ℝ) - 1)
  have hr : 0 < r := lt_trans hε hεr
  have hθ : 0 < Real.arctan (ε / r) ∧ Real.arctan (ε / r) < Real.pi / 2 :=
    exercise21_keyhole_angle_bounds (r := r) (ε := ε) hε hεr
  have hparam : 2 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hαopen :
      α ∈ Set.Ioo (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)) := by
    have hseg :
        α ∈ openSegment ℝ
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r)) := by
      simpa [α] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r))
          hparam
    have hneq :
        -Real.pi + Real.arctan (ε / r) ≠ Real.pi - Real.arctan (ε / r) := by
      nlinarith [hθ.2, Real.pi_pos]
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hneq] at hseg
    have horder :
        -Real.pi + Real.arctan (ε / r) ≤ Real.pi - Real.arctan (ε / r) := by
      nlinarith [hθ.2, Real.pi_pos]
    simpa [α, min_eq_left horder, max_eq_right horder] using hseg
  refine ⟨α, hαopen, ?_⟩
  -- Reduce the open outer branch to its explicit angular parameter.
  exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
    exercise21Delta_eq_on_outer_arc r ε (Set.Ioo_subset_Icc_self ht)

/-- Helper for Exercise 21: the upper outer corner of the keyhole contour is hit only at the two
identified endpoint parameters `0` and `1`. This is the first exact breakpoint fiber needed for
the later simple-loop proof. -/
lemma exercise21Delta_eq_upper_outer_corner_iff
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t : I} :
    exercise21Delta r ε t = circleMap 0 r (Real.pi - Real.arctan (ε / r)) ↔
      t = (0 : I) ∨ t = (1 : I) := by
  have hr : 0 < r := lt_trans hε hεr
  have hθpos : 0 < Real.arctan (ε / r) := Real.arctan_pos.mpr (div_pos hε hr)
  have hθlt : Real.arctan (ε / r) < Real.pi / 2 := Real.arctan_lt_pi_div_two (ε / r)
  have hEndsNe :
      circleMap 0 r (Real.pi - Real.arctan (ε / r)) ≠
        circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
    intro hEq
    have hnorm := congrArg norm hEq
    simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
    linarith
  constructor
  · intro ht
    rcases exercise21Delta_parameter_cases t with
      hzero | hupper | honeEight | hinner | honeQuarter | hlower | hhalf | houter | hone
    · -- The initial parameter is one endpoint of the closed loop.
      exact Or.inl (Subtype.ext hzero)
    · have hparam : 8 * (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hupper.1, hupper.2]
      have hpath :
          exercise21Delta r ε t =
            AffineMap.lineMap
              (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
              (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
              (8 * (t : ℝ)) := by
        -- On the open upper lip, the contour is the radial segment parameterized by `8 t`.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_upper_lip r ε (Set.Ioo_subset_Icc_self hupper)
      have hopen :
          exercise21Delta r ε t ∈
            openSegment ℝ
              (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
              (circleMap 0 ε (Real.pi - Real.arctan (ε / r))) := by
        -- Interior upper-lip parameters land in the open segment, so they cannot be a corner.
        simpa [hpath] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
            (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
            hparam)
      have hcorner :
          circleMap 0 r (Real.pi - Real.arctan (ε / r)) ∈
            openSegment ℝ
              (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
              (circleMap 0 ε (Real.pi - Real.arctan (ε / r))) := by
        simpa [ht] using hopen
      exact False.elim <| hEndsNe <|
        (left_mem_openSegment_iff
          (𝕜 := ℝ)
          (x := circleMap 0 r (Real.pi - Real.arctan (ε / r)))
          (y := circleMap 0 ε (Real.pi - Real.arctan (ε / r)))).mp hcorner
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext honeEight
      have hcorner :
          exercise21Delta r ε t = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      exact (hεr.ne hnorm.symm).elim
    · have hpath :
          exercise21Delta r ε t =
            circleMap 0 ε
              (AffineMap.lineMap
                (Real.pi - Real.arctan (ε / r))
                (-Real.pi + Real.arctan (ε / r))
                (8 * (t : ℝ) - 1)) := by
        -- The inner arc has constant radius `ε`, so it cannot hit the outer corner.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_inner_arc r ε (Set.Ioo_subset_Icc_self hinner)
      have hnorm := congrArg norm (ht.symm.trans hpath)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      exact (hεr.ne hnorm.symm).elim
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext honeQuarter
      have hcorner :
          exercise21Delta r ε t = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.2.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hparam : 4 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hlower.1, hlower.2]
      have hpath :
          exercise21Delta r ε t =
            AffineMap.lineMap
              (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
              (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
              (4 * (t : ℝ) - 1) := by
        -- The open lower lip is the radial segment on the lower boundary ray.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_lower_lip r ε (Set.Ioo_subset_Icc_self hlower)
      have hρ :
          0 <
            AffineMap.lineMap ε r (4 * (t : ℝ) - 1) := by
        -- The lower-lip radius stays in the closed interval `[ε, r]`, hence remains positive.
        have hparamI : 4 * (t : ℝ) - 1 ∈ I := ⟨le_of_lt hparam.1, le_of_lt hparam.2⟩
        have hρmem :
            AffineMap.lineMap ε r (4 * (t : ℝ) - 1) ∈ Set.Icc ε r := by
          exact (convex_Icc ε r).lineMap_mem
            ⟨le_rfl, le_of_lt hεr⟩
            ⟨le_of_lt hεr, le_rfl⟩
            hparamI
        exact lt_of_lt_of_le hε hρmem.1
      have hlower_im :
          (exercise21Delta r ε t).im < 0 := by
        -- Rewrite the lower lip as a fixed-angle circle point, then use the lower-ray sign.
        rw [hpath, exercise21_lineMap_circleMap_same_angle]
        have hline :=
          exercise21Delta_lower_lip_line
            (r := r) (ε := ε)
            (ρ := AffineMap.lineMap ε r (4 * (t : ℝ) - 1))
        have hre :=
          exercise21Delta_lower_lip_re_neg
            (r := r) (ε := ε)
            (ρ := AffineMap.lineMap ε r (4 * (t : ℝ) - 1))
            hρ
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hupper_im :
          0 < (circleMap 0 r (Real.pi - Real.arctan (ε / r))).im := by
        -- The target corner lies on the upper lip, hence above the real axis.
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := r)
        have hre := exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := r) hr
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have him := congrArg Complex.im ht
      linarith
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have hupper_im :
          0 < (circleMap 0 r (Real.pi - Real.arctan (ε / r))).im := by
        -- The upper outer corner lies above the real axis.
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := r)
        have hre := exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := r) hr
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 r (-Real.pi + Real.arctan (ε / r))).im < 0 := by
        -- The lower outer corner lies below the real axis.
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := r)
        have hre := exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := r) hr
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext hhalf
      have hcorner :
          exercise21Delta r ε t = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.2.2.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · let α : ℝ :=
        AffineMap.lineMap
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r))
          (2 * (t : ℝ) - 1)
      have hpath : exercise21Delta r ε t = circleMap 0 r α := by
        -- The outer arc uses the admissible angular window `(-π + θ, π - θ)`.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_outer_arc r ε (Set.Ioo_subset_Icc_self houter)
      have hparam : 2 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [houter.1, houter.2]
      have hAngleOrder :
          -Real.pi + Real.arctan (ε / r) < Real.pi - Real.arctan (ε / r) := by
        nlinarith [hθlt, Real.pi_pos]
      have hAnglesNe :
          -Real.pi + Real.arctan (ε / r) ≠ Real.pi - Real.arctan (ε / r) := by
        nlinarith [hθlt, Real.pi_pos]
      have hαmemOpen :
          α ∈ openSegment ℝ
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r)) := by
        -- The branch parameter stays strictly inside the outer-arc angle window.
        simpa [α] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r))
            hparam)
      have hαmemIoo :
          α ∈ Set.Ioo
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r)) := by
        rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hαmemOpen
        simpa [min_eq_left hAngleOrder.le, max_eq_right hAngleOrder.le] using hαmemOpen
      have hαmem :
          α ∈ Set.uIoc
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r)) := by
        rw [Set.uIoc_of_le hAngleOrder.le]
        exact Set.Ioo_subset_Ioc_self hαmemIoo
      have hendmem :
          Real.pi - Real.arctan (ε / r) ∈
            Set.uIoc
              (-Real.pi + Real.arctan (ε / r))
              (Real.pi - Real.arctan (ε / r)) := by
        rw [Set.uIoc_of_le hAngleOrder.le]
        exact Set.mem_Ioc.mpr ⟨hAngleOrder, le_rfl⟩
      have hlen :
          |(-Real.pi + Real.arctan (ε / r)) - (Real.pi - Real.arctan (ε / r))| ≤
            2 * Real.pi := by
        have hnonpos :
            (-Real.pi + Real.arctan (ε / r)) - (Real.pi - Real.arctan (ε / r)) ≤ 0 := by
          nlinarith [hθlt, Real.pi_pos]
        rw [abs_of_nonpos hnonpos]
        nlinarith [hθpos, Real.pi_pos]
      have hinj :=
        injOn_circleMap_of_abs_sub_le
          (c := 0) (R := r)
          (a := -Real.pi + Real.arctan (ε / r))
          (b := Real.pi - Real.arctan (ε / r))
          (by linarith : r ≠ 0) hlen
      have hcircle : circleMap 0 r α = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        calc
          circleMap 0 r α = exercise21Delta r ε t := hpath.symm
          _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := ht
      have hαeq : α = Real.pi - Real.arctan (ε / r) := hinj hαmem hendmem hcircle
      exact False.elim ((ne_of_lt hαmemIoo.2) hαeq)
    · -- The terminal parameter is the second endpoint of the closed loop.
      exact Or.inr (Subtype.ext hone)
  · rintro (rfl | rfl)
    · exact (exercise21Delta_breakpoint_values r ε).1
    · exact (exercise21Delta_breakpoint_values r ε).2.2.2.2

/-- Helper for Exercise 21: the upper inner corner of the keyhole contour is hit exactly at the
first interior breakpoint `t = 1/8`. This is the second exact breakpoint fiber needed for the
later simple-loop proof. -/
lemma exercise21Delta_eq_upper_inner_corner_iff
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t : I} :
    exercise21Delta r ε t = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) ↔
      t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := by
  have hr : 0 < r := lt_trans hε hεr
  have hθpos : 0 < Real.arctan (ε / r) := Real.arctan_pos.mpr (div_pos hε hr)
  have hθlt : Real.arctan (ε / r) < Real.pi / 2 := Real.arctan_lt_pi_div_two (ε / r)
  have hEndsNe :
      circleMap 0 r (Real.pi - Real.arctan (ε / r)) ≠
        circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
    intro hEq
    have hnorm := congrArg norm hEq
    simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
    linarith
  constructor
  · intro ht
    rcases exercise21Delta_parameter_cases t with
      hzero | hupper | honeEight | hinner | honeQuarter | hlower | hhalf | houter | hone
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have htEq : t = (0 : I) := Subtype.ext hzero
      have hcorner :
          exercise21Delta r ε t = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hparam : 8 * (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hupper.1, hupper.2]
      have hpath :
          exercise21Delta r ε t =
            AffineMap.lineMap
              (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
              (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
              (8 * (t : ℝ)) := by
        -- On the open upper lip, the contour is the open radial segment between the two corners.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_upper_lip r ε (Set.Ioo_subset_Icc_self hupper)
      have hopen :
          exercise21Delta r ε t ∈
            openSegment ℝ
              (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
              (circleMap 0 ε (Real.pi - Real.arctan (ε / r))) := by
        -- Interior upper-lip parameters cannot land on either endpoint of the segment.
        simpa [hpath] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
            (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
            hparam)
      have hcorner :
          circleMap 0 ε (Real.pi - Real.arctan (ε / r)) ∈
            openSegment ℝ
              (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
              (circleMap 0 ε (Real.pi - Real.arctan (ε / r))) := by
        simpa [ht] using hopen
      exact False.elim <| hEndsNe <|
        (right_mem_openSegment_iff
          (𝕜 := ℝ)
          (x := circleMap 0 r (Real.pi - Real.arctan (ε / r)))
          (y := circleMap 0 ε (Real.pi - Real.arctan (ε / r)))).mp hcorner
    · exact Subtype.ext honeEight
    · let α : ℝ :=
        AffineMap.lineMap
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r))
          (8 * (t : ℝ) - 1)
      have hpath :
          exercise21Delta r ε t = circleMap 0 ε α := by
        -- On the inner arc, only the initial angle can hit the upper inner corner.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_inner_arc r ε (Set.Ioo_subset_Icc_self hinner)
      have hparam : 8 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hinner.1, hinner.2]
      have hAngleOrder :
          -Real.pi + Real.arctan (ε / r) < Real.pi - Real.arctan (ε / r) := by
        nlinarith [hθlt, Real.pi_pos]
      have hAnglesNe :
          Real.pi - Real.arctan (ε / r) ≠ -Real.pi + Real.arctan (ε / r) := by
        nlinarith [hθlt, Real.pi_pos]
      have hαmemOpen :
          α ∈ openSegment ℝ
            (Real.pi - Real.arctan (ε / r))
            (-Real.pi + Real.arctan (ε / r)) := by
        simpa [α] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (Real.pi - Real.arctan (ε / r))
            (-Real.pi + Real.arctan (ε / r))
            hparam)
      have hαmemIoo :
          α ∈ Set.Ioo
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r)) := by
        rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hαmemOpen
        simpa [min_eq_right hAngleOrder.le, max_eq_left hAngleOrder.le] using hαmemOpen
      have hαmem :
          α ∈ Set.uIoc
            (Real.pi - Real.arctan (ε / r))
            (-Real.pi + Real.arctan (ε / r)) := by
        rw [Set.uIoc_of_ge hAngleOrder.le]
        exact Set.Ioo_subset_Ioc_self hαmemIoo
      have htargetmem :
          Real.pi - Real.arctan (ε / r) ∈
            Set.uIoc
              (Real.pi - Real.arctan (ε / r))
              (-Real.pi + Real.arctan (ε / r)) := by
        rw [Set.uIoc_of_ge hAngleOrder.le]
        exact Set.mem_Ioc.mpr ⟨hAngleOrder, le_rfl⟩
      have hlen :
          |(Real.pi - Real.arctan (ε / r)) - (-Real.pi + Real.arctan (ε / r))| ≤
            2 * Real.pi := by
        have hnonneg :
            0 ≤ (Real.pi - Real.arctan (ε / r)) - (-Real.pi + Real.arctan (ε / r)) := by
          nlinarith [hθlt, Real.pi_pos]
        rw [abs_of_nonneg hnonneg]
        nlinarith [hθpos, Real.pi_pos]
      have hinj :=
        injOn_circleMap_of_abs_sub_le
          (c := 0) (R := ε)
          (a := Real.pi - Real.arctan (ε / r))
          (b := -Real.pi + Real.arctan (ε / r))
          (by linarith : ε ≠ 0) hlen
      have hcircle : circleMap 0 ε α = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
        calc
          circleMap 0 ε α = exercise21Delta r ε t := hpath.symm
          _ = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := ht
      have hαeq : α = Real.pi - Real.arctan (ε / r) := hinj hαmem htargetmem hcircle
      exact False.elim ((ne_of_lt hαmemIoo.2) hαeq)
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have hupper_im :
          0 < (circleMap 0 ε (Real.pi - Real.arctan (ε / r))).im := by
        -- The upper inner corner lies above the real axis on the upper slit boundary.
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := ε)
        have hre := exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 ε (-Real.pi + Real.arctan (ε / r))).im < 0 := by
        -- The lower inner corner is on the opposite slit lip, hence below the axis.
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := ε)
        have hre := exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext honeQuarter
      have hcorner :
          exercise21Delta r ε t = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.2.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · have hparam : 4 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hlower.1, hlower.2]
      have hpath :
          exercise21Delta r ε t =
            AffineMap.lineMap
              (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
              (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
              (4 * (t : ℝ) - 1) := by
        -- Lower-lip interior points stay strictly below the real axis.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_lower_lip r ε (Set.Ioo_subset_Icc_self hlower)
      have hρ :
          0 <
            AffineMap.lineMap ε r (4 * (t : ℝ) - 1) := by
        have hparamI : 4 * (t : ℝ) - 1 ∈ I := ⟨le_of_lt hparam.1, le_of_lt hparam.2⟩
        have hρmem :
            AffineMap.lineMap ε r (4 * (t : ℝ) - 1) ∈ Set.Icc ε r := by
          exact (convex_Icc ε r).lineMap_mem
            ⟨le_rfl, le_of_lt hεr⟩
            ⟨le_of_lt hεr, le_rfl⟩
            hparamI
        exact lt_of_lt_of_le hε hρmem.1
      have hlower_im :
          (exercise21Delta r ε t).im < 0 := by
        -- Convert the affine lower-lip point back to a fixed-angle circle point.
        rw [hpath, exercise21_lineMap_circleMap_same_angle]
        have hline :=
          exercise21Delta_lower_lip_line
            (r := r) (ε := ε)
            (ρ := AffineMap.lineMap ε r (4 * (t : ℝ) - 1))
        have hre :=
          exercise21Delta_lower_lip_re_neg
            (r := r) (ε := ε)
            (ρ := AffineMap.lineMap ε r (4 * (t : ℝ) - 1))
            hρ
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hupper_im :
          0 < (circleMap 0 ε (Real.pi - Real.arctan (ε / r))).im := by
        -- The target corner lies on the upper slit boundary.
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := ε)
        have hre := exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have him := congrArg Complex.im ht
      linarith
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have hupper_im :
          0 < (circleMap 0 ε (Real.pi - Real.arctan (ε / r))).im := by
        -- The target corner lies above the real axis.
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := ε)
        have hre := exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 r (-Real.pi + Real.arctan (ε / r))).im < 0 := by
        -- The lower outer corner still lies below the real axis.
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := r)
        have hre := exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := r) hr
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext hhalf
      have hcorner :
          exercise21Delta r ε t = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.2.2.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · have hpath :
          exercise21Delta r ε t =
            circleMap 0 r
              (AffineMap.lineMap
                (-Real.pi + Real.arctan (ε / r))
                (Real.pi - Real.arctan (ε / r))
                (2 * (t : ℝ) - 1)) := by
        -- The outer arc has radius `r`, so it cannot hit a corner on the inner circle.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_outer_arc r ε (Set.Ioo_subset_Icc_self houter)
      have hnorm := congrArg norm (ht.symm.trans hpath)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have htEq : t = (1 : I) := Subtype.ext hone
      have hcorner :
          exercise21Delta r ε t = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.2.2.2
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
  · rintro rfl
    exact (exercise21Delta_breakpoint_values r ε).2.1

/-- Helper for Exercise 21: the lower inner corner of the keyhole contour is hit exactly at the
second interior breakpoint `t = 1/4`. This closes the third exact breakpoint fiber needed for
the later simple-loop proof. -/
lemma exercise21Delta_eq_lower_inner_corner_iff
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t : I} :
    exercise21Delta r ε t = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) ↔
      t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := by
  have hr : 0 < r := lt_trans hε hεr
  have hθpos : 0 < Real.arctan (ε / r) := Real.arctan_pos.mpr (div_pos hε hr)
  have hθlt : Real.arctan (ε / r) < Real.pi / 2 := Real.arctan_lt_pi_div_two (ε / r)
  have hEndsNe :
      circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) ≠
        circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
    intro hEq
    have hnorm := congrArg norm hEq
    simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
    linarith
  constructor
  · intro ht
    rcases exercise21Delta_parameter_cases t with
      hzero | hupper | honeEight | hinner | honeQuarter | hlower | hhalf | houter | hone
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have htEq : t = (0 : I) := Subtype.ext hzero
      have hcorner :
          exercise21Delta r ε t = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hparam : 8 * (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hupper.1, hupper.2]
      have hpath :
          exercise21Delta r ε t =
            AffineMap.lineMap
              (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
              (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
              (8 * (t : ℝ)) := by
        -- Upper-lip interior points stay above the real axis, unlike the lower inner corner.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_upper_lip r ε (Set.Ioo_subset_Icc_self hupper)
      have hρ :
          0 <
            AffineMap.lineMap r ε (8 * (t : ℝ)) := by
        have hparamI : 8 * (t : ℝ) ∈ I := ⟨le_of_lt hparam.1, le_of_lt hparam.2⟩
        have hρmem :
            AffineMap.lineMap r ε (8 * (t : ℝ)) ∈ Set.Icc ε r := by
          exact (convex_Icc ε r).lineMap_mem
            ⟨le_of_lt hεr, le_rfl⟩
            ⟨le_rfl, le_of_lt hεr⟩
            hparamI
        exact lt_of_lt_of_le hε hρmem.1
      have hupper_im :
          0 < (exercise21Delta r ε t).im := by
        -- Convert the affine upper-lip point back to a fixed-angle circle point.
        rw [hpath, exercise21_lineMap_circleMap_same_angle]
        have hline :=
          exercise21Delta_upper_lip_line
            (r := r) (ε := ε)
            (ρ := AffineMap.lineMap r ε (8 * (t : ℝ)))
        have hre :=
          exercise21Delta_upper_lip_re_neg
            (r := r) (ε := ε)
            (ρ := AffineMap.lineMap r ε (8 * (t : ℝ)))
            hρ
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 ε (-Real.pi + Real.arctan (ε / r))).im < 0 := by
        -- The target corner lies on the lower slit boundary.
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := ε)
        have hre := exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have him := congrArg Complex.im ht
      linarith
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have hupper_im :
          0 < (circleMap 0 ε (Real.pi - Real.arctan (ε / r))).im := by
        -- The upper inner corner is above the real axis.
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := ε)
        have hre := exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 ε (-Real.pi + Real.arctan (ε / r))).im < 0 := by
        -- The target corner is below the real axis.
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := ε)
        have hre := exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext honeEight
      have hcorner :
          exercise21Delta r ε t = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · let α : ℝ :=
        AffineMap.lineMap
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r))
          (8 * (t : ℝ) - 1)
      have hpath :
          exercise21Delta r ε t = circleMap 0 ε α := by
        -- The inner arc reaches the lower inner corner only at its terminal parameter.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_inner_arc r ε (Set.Ioo_subset_Icc_self hinner)
      have hparam : 8 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hinner.1, hinner.2]
      have hAngleOrder :
          -Real.pi + Real.arctan (ε / r) < Real.pi - Real.arctan (ε / r) := by
        nlinarith [hθlt, Real.pi_pos]
      have hAnglesNe :
          Real.pi - Real.arctan (ε / r) ≠ -Real.pi + Real.arctan (ε / r) := by
        nlinarith [hθlt, Real.pi_pos]
      have hαmemOpen :
          α ∈ openSegment ℝ
            (Real.pi - Real.arctan (ε / r))
            (-Real.pi + Real.arctan (ε / r)) := by
        simpa [α] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (Real.pi - Real.arctan (ε / r))
            (-Real.pi + Real.arctan (ε / r))
            hparam)
      have hαmemIoo :
          α ∈ Set.Ioo
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r)) := by
        rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hαmemOpen
        simpa [min_eq_right hAngleOrder.le, max_eq_left hAngleOrder.le] using hαmemOpen
      have hαmem :
          α ∈ Set.Ico
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r)) := by
        exact Set.Ioo_subset_Ico_self hαmemIoo
      have htargetmem :
          -Real.pi + Real.arctan (ε / r) ∈
            Set.Ico
              (-Real.pi + Real.arctan (ε / r))
              (Real.pi - Real.arctan (ε / r)) := by
        exact Set.mem_Ico.mpr ⟨le_rfl, hAngleOrder⟩
      have hlen :
          (Real.pi - Real.arctan (ε / r)) - (-Real.pi + Real.arctan (ε / r)) ≤
            2 * Real.pi := by
        nlinarith [hθpos, Real.pi_pos]
      have hinj :=
        injOn_circleMap_of_abs_sub_le'
          (c := 0) (R := ε)
          (a := -Real.pi + Real.arctan (ε / r))
          (b := Real.pi - Real.arctan (ε / r))
          (by linarith : ε ≠ 0) hlen
      have hcircle : circleMap 0 ε α = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
        calc
          circleMap 0 ε α = exercise21Delta r ε t := hpath.symm
          _ = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := ht
      have hαeq : α = -Real.pi + Real.arctan (ε / r) := hinj hαmem htargetmem hcircle
      exact False.elim ((ne_of_gt hαmemIoo.1) hαeq)
    · exact Subtype.ext honeQuarter
    · have hparam : 4 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hlower.1, hlower.2]
      have hpath :
          exercise21Delta r ε t =
            AffineMap.lineMap
              (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
              (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
              (4 * (t : ℝ) - 1) := by
        -- On the open lower lip, the target is the excluded left endpoint.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_lower_lip r ε (Set.Ioo_subset_Icc_self hlower)
      have hopen :
          exercise21Delta r ε t ∈
            openSegment ℝ
              (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
              (circleMap 0 r (-Real.pi + Real.arctan (ε / r))) := by
        simpa [hpath] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
            (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
            hparam)
      have hcorner :
          circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) ∈
            openSegment ℝ
              (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
              (circleMap 0 r (-Real.pi + Real.arctan (ε / r))) := by
        simpa [ht] using hopen
      exact False.elim <| hEndsNe <|
        (left_mem_openSegment_iff
          (𝕜 := ℝ)
          (x := circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
          (y := circleMap 0 r (-Real.pi + Real.arctan (ε / r)))).mp hcorner
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext hhalf
      have hcorner :
          exercise21Delta r ε t = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.2.2.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hpath :
          exercise21Delta r ε t =
            circleMap 0 r
              (AffineMap.lineMap
                (-Real.pi + Real.arctan (ε / r))
                (Real.pi - Real.arctan (ε / r))
                (2 * (t : ℝ) - 1)) := by
        -- The outer arc has radius `r`, so it cannot hit the inner lower corner.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_outer_arc r ε (Set.Ioo_subset_Icc_self houter)
      have hnorm := congrArg norm (ht.symm.trans hpath)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have htEq : t = (1 : I) := Subtype.ext hone
      have hcorner :
          exercise21Delta r ε t = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.2.2.2
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
  · rintro rfl
    exact (exercise21Delta_breakpoint_values r ε).2.2.1

/-- Helper for Exercise 21: the lower outer corner of the keyhole contour is hit exactly at the
third interior breakpoint `t = 1/2`. This is the last exact breakpoint fiber needed before the
simple-loop dispatcher can close. -/
lemma exercise21Delta_eq_lower_outer_corner_iff
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t : I} :
    exercise21Delta r ε t = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) ↔
      t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := by
  have hr : 0 < r := lt_trans hε hεr
  have hθpos : 0 < Real.arctan (ε / r) := Real.arctan_pos.mpr (div_pos hε hr)
  have hθlt : Real.arctan (ε / r) < Real.pi / 2 := Real.arctan_lt_pi_div_two (ε / r)
  have hEndsNe :
      circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) ≠
        circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
    intro hEq
    have hnorm := congrArg norm hEq
    simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
    linarith
  constructor
  · intro ht
    rcases exercise21Delta_parameter_cases t with
      hzero | hupper | honeEight | hinner | honeQuarter | hlower | hhalf | houter | hone
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have hupper_im :
          0 < (circleMap 0 r (Real.pi - Real.arctan (ε / r))).im := by
        -- The initial upper outer corner lies above the real axis.
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := r)
        have hre := exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := r) hr
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 r (-Real.pi + Real.arctan (ε / r))).im < 0 := by
        -- The target corner is below the real axis on the lower slit boundary.
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := r)
        have hre := exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := r) hr
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have htEq : t = (0 : I) := Subtype.ext hzero
      have hcorner :
          exercise21Delta r ε t = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · have hparam : 8 * (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hupper.1, hupper.2]
      have hpath :
          exercise21Delta r ε t =
            AffineMap.lineMap
              (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
              (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
              (8 * (t : ℝ)) := by
        -- Upper-lip interior points stay above the real axis, unlike the target corner.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_upper_lip r ε (Set.Ioo_subset_Icc_self hupper)
      have hρ :
          0 <
            AffineMap.lineMap r ε (8 * (t : ℝ)) := by
        have hparamI : 8 * (t : ℝ) ∈ I := ⟨le_of_lt hparam.1, le_of_lt hparam.2⟩
        have hρmem :
            AffineMap.lineMap r ε (8 * (t : ℝ)) ∈ Set.Icc ε r := by
          exact (convex_Icc ε r).lineMap_mem
            ⟨le_of_lt hεr, le_rfl⟩
            ⟨le_rfl, le_of_lt hεr⟩
            hparamI
        exact lt_of_lt_of_le hε hρmem.1
      have hupper_im :
          0 < (exercise21Delta r ε t).im := by
        -- Convert the affine upper-lip point to a fixed-angle circle point.
        rw [hpath, exercise21_lineMap_circleMap_same_angle]
        have hline :=
          exercise21Delta_upper_lip_line
            (r := r) (ε := ε)
            (ρ := AffineMap.lineMap r ε (8 * (t : ℝ)))
        have hre :=
          exercise21Delta_upper_lip_re_neg
            (r := r) (ε := ε)
            (ρ := AffineMap.lineMap r ε (8 * (t : ℝ)))
            hρ
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 r (-Real.pi + Real.arctan (ε / r))).im < 0 := by
        -- The lower outer corner lies below the axis.
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := r)
        have hre := exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := r) hr
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have him := congrArg Complex.im ht
      linarith
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have hupper_im :
          0 < (circleMap 0 ε (Real.pi - Real.arctan (ε / r))).im := by
        -- The upper inner corner is still above the real axis.
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := ε)
        have hre := exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 r (-Real.pi + Real.arctan (ε / r))).im < 0 := by
        -- The target corner is below the real axis.
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := r)
        have hre := exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := r) hr
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext honeEight
      have hcorner :
          exercise21Delta r ε t = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · have hpath :
          exercise21Delta r ε t =
            circleMap 0 ε
              (AffineMap.lineMap
                (Real.pi - Real.arctan (ε / r))
                (-Real.pi + Real.arctan (ε / r))
                (8 * (t : ℝ) - 1)) := by
        -- The inner arc has radius `ε`, so it cannot hit a corner on the outer circle.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_inner_arc r ε (Set.Ioo_subset_Icc_self hinner)
      have hnorm := congrArg norm (ht.symm.trans hpath)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext honeQuarter
      have hcorner :
          exercise21Delta r ε t = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.2.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hparam : 4 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hlower.1, hlower.2]
      have hpath :
          exercise21Delta r ε t =
            AffineMap.lineMap
              (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
              (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
              (4 * (t : ℝ) - 1) := by
        -- On the open lower lip, the target is the excluded right endpoint.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_lower_lip r ε (Set.Ioo_subset_Icc_self hlower)
      have hopen :
          exercise21Delta r ε t ∈
            openSegment ℝ
              (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
              (circleMap 0 r (-Real.pi + Real.arctan (ε / r))) := by
        simpa [hpath] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
            (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
            hparam)
      have hcorner :
          circleMap 0 r (-Real.pi + Real.arctan (ε / r)) ∈
            openSegment ℝ
              (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
              (circleMap 0 r (-Real.pi + Real.arctan (ε / r))) := by
        simpa [ht] using hopen
      exact False.elim <| hEndsNe <|
        (right_mem_openSegment_iff
          (𝕜 := ℝ)
          (x := circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
          (y := circleMap 0 r (-Real.pi + Real.arctan (ε / r)))).mp hcorner
    · exact Subtype.ext hhalf
    · let α : ℝ :=
        AffineMap.lineMap
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r))
          (2 * (t : ℝ) - 1)
      have hpath :
          exercise21Delta r ε t = circleMap 0 r α := by
        -- The outer arc hits the lower outer corner only at its initial angle.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_outer_arc r ε (Set.Ioo_subset_Icc_self houter)
      have hparam : 2 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [houter.1, houter.2]
      have hAngleOrder :
          -Real.pi + Real.arctan (ε / r) < Real.pi - Real.arctan (ε / r) := by
        nlinarith [hθlt, Real.pi_pos]
      have hAnglesNe :
          -Real.pi + Real.arctan (ε / r) ≠ Real.pi - Real.arctan (ε / r) := by
        nlinarith [hθlt, Real.pi_pos]
      have hαmemOpen :
          α ∈ openSegment ℝ
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r)) := by
        simpa [α] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r))
            hparam)
      have hαmemIoo :
          α ∈ Set.Ioo
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r)) := by
        rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hαmemOpen
        simpa [min_eq_left hAngleOrder.le, max_eq_right hAngleOrder.le] using hαmemOpen
      have hαmem :
          α ∈ Set.Ico
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r)) := by
        exact Set.Ioo_subset_Ico_self hαmemIoo
      have htargetmem :
          -Real.pi + Real.arctan (ε / r) ∈
            Set.Ico
              (-Real.pi + Real.arctan (ε / r))
              (Real.pi - Real.arctan (ε / r)) := by
        exact Set.mem_Ico.mpr ⟨le_rfl, hAngleOrder⟩
      have hlen :
          (Real.pi - Real.arctan (ε / r)) - (-Real.pi + Real.arctan (ε / r)) ≤
            2 * Real.pi := by
        nlinarith [hθpos, Real.pi_pos]
      have hinj :=
        injOn_circleMap_of_abs_sub_le'
          (c := 0) (R := r)
          (a := -Real.pi + Real.arctan (ε / r))
          (b := Real.pi - Real.arctan (ε / r))
          (by linarith : r ≠ 0) hlen
      have hcircle : circleMap 0 r α = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
        calc
          circleMap 0 r α = exercise21Delta r ε t := hpath.symm
          _ = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := ht
      have hαeq : α = -Real.pi + Real.arctan (ε / r) := hinj hαmem htargetmem hcircle
      exact False.elim ((ne_of_gt hαmemIoo.1) hαeq)
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have hupper_im :
          0 < (circleMap 0 r (Real.pi - Real.arctan (ε / r))).im := by
        -- The terminal upper outer corner lies above the axis.
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := r)
        have hre := exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := r) hr
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 r (-Real.pi + Real.arctan (ε / r))).im < 0 := by
        -- The target corner remains below the axis.
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := r)
        have hre := exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := r) hr
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have htEq : t = (1 : I) := Subtype.ext hone
      have hcorner :
          exercise21Delta r ε t = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.2.2.2
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
  · rintro rfl
    exact (exercise21Delta_breakpoint_values r ε).2.2.2.1

/-- Helper for Exercise 21: a circular arc obtained by mapping an affine angle segment through
`circleMap` is differentiable as a path. -/
lemma exercise21_circle_segment_isDifferentiable (ρ α β : ℝ) :
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

/-- Helper for Exercise 21: the keyhole contour `δ(r, ε)` is piecewise differentiable because it
is built from two straight segments and two smooth circular arcs. -/
lemma exercise21Delta_isPiecewiseDifferentiable (r ε : ℝ) :
    (exercise21Delta r ε).IsPiecewiseDifferentiable := by
  let θ : ℝ := Real.arctan (ε / r)
  have hupper :
      (Path.segment (circleMap 0 r (Real.pi - θ)) (circleMap 0 ε (Real.pi - θ))).IsPiecewiseDifferentiable :=
    Path.segment_isPiecewiseDifferentiable _ _
  have hinner :
      ((Path.segment (Real.pi - θ) (-Real.pi + θ)).map (continuous_circleMap 0 ε)).IsDifferentiable :=
    exercise21_circle_segment_isDifferentiable ε (Real.pi - θ) (-Real.pi + θ)
  have hlower :
      (Path.segment (circleMap 0 ε (-Real.pi + θ)) (circleMap 0 r (-Real.pi + θ))).IsDifferentiable :=
    Path.segment_isDifferentiable _ _
  have houter :
      ((Path.segment (-Real.pi + θ) (Real.pi - θ)).map (continuous_circleMap 0 r)).IsDifferentiable :=
    exercise21_circle_segment_isDifferentiable r (-Real.pi + θ) (Real.pi - θ)
  -- Append the four smooth pieces in the source order used to define the keyhole contour.
  have hupper_inner := hupper.trans_of_isDifferentiable hinner
  have hupper_inner_lower := hupper_inner.trans_of_isDifferentiable hlower
  have hall := hupper_inner_lower.trans_of_isDifferentiable houter
  simpa [exercise21Delta, θ] using hall

/-- Helper for Exercise 21: a positive-radius point `circleMap 0 ρ φ` belongs to the principal
slit plane whenever its angle stays strictly between `-π` and `π`. -/
lemma exercise21_mem_slitPlane_circleMap_of_angle {ρ φ : ℝ}
    (hρ : 0 < ρ) (hφ_lower : -Real.pi < φ) (hφ_upper : φ < Real.pi) :
    circleMap 0 ρ φ ∈ Complex.slitPlane := by
  -- If the imaginary part vanishes, the angle must be `0`; otherwise `im ≠ 0` puts the point
  -- in the slit plane immediately.
  by_cases hsin : Real.sin φ = 0
  · have hφ_zero : φ = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt hφ_lower hφ_upper).mp hsin
    rw [Complex.mem_slitPlane_iff]
    left
    rw [circleMap_zero_re, hφ_zero, Real.cos_zero]
    simpa using hρ
  · rw [Complex.mem_slitPlane_iff]
    right
    rw [circleMap_zero_im]
    exact mul_ne_zero hρ.ne' hsin

/-- Helper for Exercise 21: equality on one open branch of the keyhole contour forces equality of
the corresponding parameters. This isolates the source-faithful injectivity package needed for the
later simple-loop proof from the breakpoint bookkeeping. -/
lemma exercise21Delta_same_branch_injective
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {s t : I}
    (hbranch :
      (s.1 ∈ Set.Ioo (0 : ℝ) (1 / 8) ∧ t.1 ∈ Set.Ioo (0 : ℝ) (1 / 8)) ∨
        (s.1 ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4) ∧ t.1 ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4)) ∨
        (s.1 ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∧ t.1 ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)) ∨
        (s.1 ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ) ∧ t.1 ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ)))
    (hst : exercise21Delta r ε s = exercise21Delta r ε t) :
    s = t := by
  have hr : 0 < r := lt_trans hε hεr
  have hθ := exercise21_keyhole_angle_bounds (r := r) (ε := ε) hε hεr
  rcases hbranch with hupper | hinner | hlower | houter
  · rcases hupper with ⟨hs, ht⟩
    -- On the upper lip, the keyhole is a nonconstant affine interpolation in the radius.
    have hsPath :
        exercise21Delta r ε s =
          AffineMap.lineMap
            (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
            (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
            (8 * (s : ℝ)) := by
      exact (Path.extend_apply (exercise21Delta r ε) s.2).symm.trans <|
        exercise21Delta_eq_on_upper_lip r ε (Set.Ioo_subset_Icc_self hs)
    have htPath :
        exercise21Delta r ε t =
          AffineMap.lineMap
            (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
            (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
            (8 * (t : ℝ)) := by
      exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
        exercise21Delta_eq_on_upper_lip r ε (Set.Ioo_subset_Icc_self ht)
    have hparam :
        AffineMap.lineMap
            (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
            (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
            (8 * (s : ℝ)) =
          AffineMap.lineMap
            (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
            (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
            (8 * (t : ℝ)) := by
      calc
        AffineMap.lineMap
            (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
            (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
            (8 * (s : ℝ)) =
            exercise21Delta r ε s := hsPath.symm
        _ = exercise21Delta r ε t := hst
        _ =
            AffineMap.lineMap
              (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
              (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
              (8 * (t : ℝ)) := htPath
    have hEndsNe :
        circleMap 0 r (Real.pi - Real.arctan (ε / r)) ≠
          circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
      intro hEq
      have hnorm := congrArg norm hEq
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    have hst' : 8 * (s : ℝ) = 8 * (t : ℝ) := by
      rcases (AffineMap.lineMap_eq_lineMap_iff
        (p₀ := circleMap 0 r (Real.pi - Real.arctan (ε / r)))
        (p₁ := circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
        (c₁ := 8 * (s : ℝ)) (c₂ := 8 * (t : ℝ))).mp hparam with hEq | hEq
      · exact (hEndsNe hEq).elim
      · exact hEq
    -- Recover the subtype equality from the affine radial parameter.
    exact Subtype.ext (by linarith)
  · rcases hinner with ⟨hs, ht⟩
    let α : ℝ :=
      AffineMap.lineMap
        (Real.pi - Real.arctan (ε / r))
        (-Real.pi + Real.arctan (ε / r))
        (8 * (s : ℝ) - 1)
    let β : ℝ :=
      AffineMap.lineMap
        (Real.pi - Real.arctan (ε / r))
        (-Real.pi + Real.arctan (ε / r))
        (8 * (t : ℝ) - 1)
    -- On the inner circle, injectivity comes from the angular window of length `< 2π`.
    have hsPath : exercise21Delta r ε s = circleMap 0 ε α := by
      exact (Path.extend_apply (exercise21Delta r ε) s.2).symm.trans <|
        exercise21Delta_eq_on_inner_arc r ε (Set.Ioo_subset_Icc_self hs)
    have htPath : exercise21Delta r ε t = circleMap 0 ε β := by
      exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
        exercise21Delta_eq_on_inner_arc r ε (Set.Ioo_subset_Icc_self ht)
    have hcircle : circleMap 0 ε α = circleMap 0 ε β := by
      calc
        circleMap 0 ε α = exercise21Delta r ε s := hsPath.symm
        _ = exercise21Delta r ε t := hst
        _ = circleMap 0 ε β := htPath
    have hsParam : 8 * (s : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hs.1, hs.2]
    have htParam : 8 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have hAngleOrder :
        -Real.pi + Real.arctan (ε / r) < Real.pi - Real.arctan (ε / r) := by
      nlinarith [hθ.2, Real.pi_pos]
    have hAnglesNe :
        Real.pi - Real.arctan (ε / r) ≠ -Real.pi + Real.arctan (ε / r) := by
      nlinarith [hθ.2, Real.pi_pos]
    have hαmemOpen :
        α ∈ openSegment ℝ
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r)) := by
      simpa [α] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r))
          hsParam
    have hβmemOpen :
        β ∈ openSegment ℝ
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r)) := by
      simpa [β] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r))
          htParam
    have hαmemIoo :
        α ∈ Set.Ioo
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r)) := by
      rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hαmemOpen
      simpa [min_eq_right hAngleOrder.le, max_eq_left hAngleOrder.le] using hαmemOpen
    have hβmemIoo :
        β ∈ Set.Ioo
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r)) := by
      rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hβmemOpen
      simpa [min_eq_right hAngleOrder.le, max_eq_left hAngleOrder.le] using hβmemOpen
    have hαmem :
        α ∈ Set.uIoc
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r)) := by
      rw [Set.uIoc_of_ge hAngleOrder.le]
      exact Set.Ioo_subset_Ioc_self hαmemIoo
    have hβmem :
        β ∈ Set.uIoc
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r)) := by
      rw [Set.uIoc_of_ge hAngleOrder.le]
      exact Set.Ioo_subset_Ioc_self hβmemIoo
    have hlen :
        |(Real.pi - Real.arctan (ε / r)) - (-Real.pi + Real.arctan (ε / r))| ≤ 2 * Real.pi := by
      have hnonneg :
          0 ≤ (Real.pi - Real.arctan (ε / r)) - (-Real.pi + Real.arctan (ε / r)) := by
        nlinarith [hθ.2, Real.pi_pos]
      rw [abs_of_nonneg hnonneg]
      nlinarith [hθ.1, Real.pi_pos]
    have hinj :=
      injOn_circleMap_of_abs_sub_le
        (c := 0) (R := ε)
        (a := Real.pi - Real.arctan (ε / r))
        (b := -Real.pi + Real.arctan (ε / r))
        (by linarith : ε ≠ 0) hlen
    have hαβ : α = β := hinj hαmem hβmem hcircle
    have hαβ_explicit :
        AffineMap.lineMap
            (Real.pi - Real.arctan (ε / r))
            (-Real.pi + Real.arctan (ε / r))
            (8 * (s : ℝ) - 1) =
          AffineMap.lineMap
            (Real.pi - Real.arctan (ε / r))
            (-Real.pi + Real.arctan (ε / r))
            (8 * (t : ℝ) - 1) := by
      simpa [α, β] using hαβ
    have hst' : 8 * (s : ℝ) - 1 = 8 * (t : ℝ) - 1 := by
      rcases (AffineMap.lineMap_eq_lineMap_iff
        (p₀ := Real.pi - Real.arctan (ε / r))
        (p₁ := -Real.pi + Real.arctan (ε / r))
        (c₁ := 8 * (s : ℝ) - 1) (c₂ := 8 * (t : ℝ) - 1)).mp hαβ_explicit with hEq | hEq
      · have : False := by
          nlinarith [hEq, hθ.2, Real.pi_pos]
        exact this.elim
      · exact hEq
    -- The affine angle parameter is injective because the two angular endpoints differ.
    exact Subtype.ext (by linarith)
  · rcases hlower with ⟨hs, ht⟩
    -- The lower lip is the same affine radial model, with the opposite orientation.
    have hsPath :
        exercise21Delta r ε s =
          AffineMap.lineMap
            (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
            (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
            (4 * (s : ℝ) - 1) := by
      exact (Path.extend_apply (exercise21Delta r ε) s.2).symm.trans <|
        exercise21Delta_eq_on_lower_lip r ε (Set.Ioo_subset_Icc_self hs)
    have htPath :
        exercise21Delta r ε t =
          AffineMap.lineMap
            (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
            (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
            (4 * (t : ℝ) - 1) := by
      exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
        exercise21Delta_eq_on_lower_lip r ε (Set.Ioo_subset_Icc_self ht)
    have hparam :
        AffineMap.lineMap
            (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
            (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
            (4 * (s : ℝ) - 1) =
          AffineMap.lineMap
            (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
            (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
            (4 * (t : ℝ) - 1) := by
      calc
        AffineMap.lineMap
            (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
            (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
            (4 * (s : ℝ) - 1) =
            exercise21Delta r ε s := hsPath.symm
        _ = exercise21Delta r ε t := hst
        _ =
            AffineMap.lineMap
              (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
              (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
              (4 * (t : ℝ) - 1) := htPath
    have hEndsNe :
        circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) ≠
          circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
      intro hEq
      have hnorm := congrArg norm hEq
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    have hst' : 4 * (s : ℝ) - 1 = 4 * (t : ℝ) - 1 := by
      rcases (AffineMap.lineMap_eq_lineMap_iff
        (p₀ := circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
        (p₁ := circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
        (c₁ := 4 * (s : ℝ) - 1) (c₂ := 4 * (t : ℝ) - 1)).mp hparam with hEq | hEq
      · exact (hEndsNe hEq).elim
      · exact hEq
    -- Again the subtype equality is read off from the affine radial coordinate.
    exact Subtype.ext (by linarith)
  · rcases houter with ⟨hs, ht⟩
    let α : ℝ :=
      AffineMap.lineMap
        (-Real.pi + Real.arctan (ε / r))
        (Real.pi - Real.arctan (ε / r))
        (2 * (s : ℝ) - 1)
    let β : ℝ :=
      AffineMap.lineMap
        (-Real.pi + Real.arctan (ε / r))
        (Real.pi - Real.arctan (ε / r))
        (2 * (t : ℝ) - 1)
    -- The outer circle uses the same injective angular strip as the inner arc.
    have hsPath : exercise21Delta r ε s = circleMap 0 r α := by
      exact (Path.extend_apply (exercise21Delta r ε) s.2).symm.trans <|
        exercise21Delta_eq_on_outer_arc r ε (Set.Ioo_subset_Icc_self hs)
    have htPath : exercise21Delta r ε t = circleMap 0 r β := by
      exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
        exercise21Delta_eq_on_outer_arc r ε (Set.Ioo_subset_Icc_self ht)
    have hcircle : circleMap 0 r α = circleMap 0 r β := by
      calc
        circleMap 0 r α = exercise21Delta r ε s := hsPath.symm
        _ = exercise21Delta r ε t := hst
        _ = circleMap 0 r β := htPath
    have hsParam : 2 * (s : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hs.1, hs.2]
    have htParam : 2 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have hAngleOrder :
        -Real.pi + Real.arctan (ε / r) < Real.pi - Real.arctan (ε / r) := by
      nlinarith [hθ.2, Real.pi_pos]
    have hAnglesNe :
        -Real.pi + Real.arctan (ε / r) ≠ Real.pi - Real.arctan (ε / r) := by
      nlinarith [hθ.2, Real.pi_pos]
    have hαmemOpen :
        α ∈ openSegment ℝ
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r)) := by
      simpa [α] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r))
          hsParam
    have hβmemOpen :
        β ∈ openSegment ℝ
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r)) := by
      simpa [β] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r))
          htParam
    have hαmemIoo :
        α ∈ Set.Ioo
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r)) := by
      rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hαmemOpen
      simpa [min_eq_left hAngleOrder.le, max_eq_right hAngleOrder.le] using hαmemOpen
    have hβmemIoo :
        β ∈ Set.Ioo
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r)) := by
      rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hβmemOpen
      simpa [min_eq_left hAngleOrder.le, max_eq_right hAngleOrder.le] using hβmemOpen
    have hαmem :
        α ∈ Set.uIoc
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r)) := by
      rw [Set.uIoc_of_le hAngleOrder.le]
      exact Set.Ioo_subset_Ioc_self hαmemIoo
    have hβmem :
        β ∈ Set.uIoc
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r)) := by
      rw [Set.uIoc_of_le hAngleOrder.le]
      exact Set.Ioo_subset_Ioc_self hβmemIoo
    have hlen :
        |(-Real.pi + Real.arctan (ε / r)) - (Real.pi - Real.arctan (ε / r))| ≤ 2 * Real.pi := by
      have hnonpos :
          (-Real.pi + Real.arctan (ε / r)) - (Real.pi - Real.arctan (ε / r)) ≤ 0 := by
        nlinarith [hθ.2, Real.pi_pos]
      rw [abs_of_nonpos hnonpos]
      nlinarith [hθ.1, Real.pi_pos]
    have hinj :=
      injOn_circleMap_of_abs_sub_le
        (c := 0) (R := r)
        (a := -Real.pi + Real.arctan (ε / r))
        (b := Real.pi - Real.arctan (ε / r))
        (by linarith : r ≠ 0) hlen
    have hαβ : α = β := hinj hαmem hβmem hcircle
    have hαβ_explicit :
        AffineMap.lineMap
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r))
            (2 * (s : ℝ) - 1) =
          AffineMap.lineMap
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r))
            (2 * (t : ℝ) - 1) := by
      simpa [α, β] using hαβ
    have hst' : 2 * (s : ℝ) - 1 = 2 * (t : ℝ) - 1 := by
      rcases (AffineMap.lineMap_eq_lineMap_iff
        (p₀ := -Real.pi + Real.arctan (ε / r))
        (p₁ := Real.pi - Real.arctan (ε / r))
        (c₁ := 2 * (s : ℝ) - 1) (c₂ := 2 * (t : ℝ) - 1)).mp hαβ_explicit with hEq | hEq
      · have : False := by
          nlinarith [hEq, hθ.2, Real.pi_pos]
        exact this.elim
      · exact hEq
    -- The outer-arc affine angle parameter is likewise injective.
    exact Subtype.ext (by linarith)

/-- Helper for Exercise 21: equality on the keyhole contour can only occur at the same parameter
or at the identified endpoint pair `(0, 1)` / `(1, 0)`. -/
lemma exercise21Delta_simple_eq_or_endpoints
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {s t : I}
    (hst : exercise21Delta r ε s = exercise21Delta r ε t) :
    s = t ∨ (s, t) = ((0 : I), (1 : I)) ∨ (s, t) = ((1 : I), (0 : I)) := by
  have hr : 0 < r := lt_trans hε hεr
  have hbreak := exercise21Delta_breakpoint_values r ε
  rcases exercise21Delta_parameter_cases s with
    hs0 | hsupper | hs18 | hsinner | hs14 | hslower | hs12 | hsouter | hs1
  · have hsEq : s = (0 : I) := Subtype.ext hs0
    -- If `s` is the initial endpoint, `t` must be one of the two parameters for the same corner.
    have htCorner :
        exercise21Delta r ε t = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
      calc
        exercise21Delta r ε t = exercise21Delta r ε s := hst.symm
        _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by simpa [hsEq] using hbreak.1
    rcases (exercise21Delta_eq_upper_outer_corner_iff r ε hε hεr).1 htCorner with ht0 | ht1
    · left
      simpa [hsEq, ht0]
    · right
      left
      simpa [hsEq, ht1]
  · -- Route correction: use the branch geometry already proved for the four open pieces instead of
    -- trying to recurse on the concatenated path itself.
    rcases exercise21Delta_eq_upper_lip_circleMap_of_mem_Ioo r ε hε hεr hsupper with
      ⟨ρs, hρs, hsPath⟩
    rcases exercise21Delta_parameter_cases t with
      ht0 | htupper | ht18 | htinner | ht14 | htlower | ht12 | htouter | ht1
    · have htEq : t = (0 : I) := Subtype.ext ht0
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by simpa [htEq] using hbreak.1
      have : False := by
        rcases (exercise21Delta_eq_upper_outer_corner_iff r ε hε hεr).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsupper.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsupper.2]
      exact this.elim
    · left
      exact exercise21Delta_same_branch_injective r ε hε hεr (Or.inl ⟨hsupper, htupper⟩) hst
    · have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext ht18
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_upper_inner_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 8 := by simpa using congrArg Subtype.val hsEq
        linarith [hsupper.2]
      exact this.elim
    · rcases exercise21Delta_eq_inner_arc_circleMap_of_mem_Ioo r ε hε hεr htinner with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          ρs = ε := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ρs (Real.pi - Real.arctan (ε / r)) = exercise21Delta r ε s := hsPath.symm
          _ = exercise21Delta r ε t := hst
          _ = circleMap 0 ε αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos (lt_trans hε hρs.1), abs_of_pos hε] using hnorm'
      have : False := by
        linarith [hρs.1, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext ht14
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_lower_inner_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 4 := by simpa using congrArg Subtype.val hsEq
        linarith [hsupper.2]
      exact this.elim
    · rcases exercise21Delta_eq_lower_lip_circleMap_of_mem_Ioo r ε hε hεr htlower with
        ⟨ρt, hρt, htPath⟩
      have hsIm : 0 < (exercise21Delta r ε s).im := by
        rw [hsPath]
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := ρs)
        have hre :=
          exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := ρs) (lt_trans hε hρs.1)
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have htIm : (exercise21Delta r ε t).im < 0 := by
        rw [htPath]
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := ρt)
        have hre :=
          exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := ρt) (lt_trans hε hρt.1)
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have him : (exercise21Delta r ε s).im = (exercise21Delta r ε t).im := congrArg Complex.im hst
      have : False := by
        linarith [hsIm, htIm, him]
      exact this.elim
    · have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext ht12
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_lower_outer_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 2 := by simpa using congrArg Subtype.val hsEq
        linarith [hsupper.2]
      exact this.elim
    · rcases exercise21Delta_eq_outer_arc_circleMap_of_mem_Ioo r ε hε hεr htouter with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          ρs = r := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ρs (Real.pi - Real.arctan (ε / r)) = exercise21Delta r ε s := hsPath.symm
          _ = exercise21Delta r ε t := hst
          _ = circleMap 0 r αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos (lt_trans hε hρs.1), abs_of_pos hr] using hnorm'
      have : False := by
        linarith [hρs.2, hnorm]
      exact this.elim
    · have htEq : t = (1 : I) := Subtype.ext ht1
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.2.2
      have : False := by
        rcases (exercise21Delta_eq_upper_outer_corner_iff r ε hε hεr).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsupper.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsupper.2]
      exact this.elim
  · have hsEq : s = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext hs18
    -- The first interior corner has a singleton fiber.
    have htCorner :
        exercise21Delta r ε t = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
      calc
        exercise21Delta r ε t = exercise21Delta r ε s := hst.symm
        _ = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by simpa [hsEq] using hbreak.2.1
    have htEq := (exercise21Delta_eq_upper_inner_corner_iff r ε hε hεr).1 htCorner
    left
    simpa [hsEq, htEq]
  · rcases exercise21Delta_eq_inner_arc_circleMap_of_mem_Ioo r ε hε hεr hsinner with
      ⟨αs, hαs, hsPath⟩
    rcases exercise21Delta_parameter_cases t with
      ht0 | htupper | ht18 | htinner | ht14 | htlower | ht12 | htouter | ht1
    · have htEq : t = (0 : I) := Subtype.ext ht0
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by simpa [htEq] using hbreak.1
      have : False := by
        rcases (exercise21Delta_eq_upper_outer_corner_iff r ε hε hεr).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsinner.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsinner.2]
      exact this.elim
    · rcases exercise21Delta_eq_upper_lip_circleMap_of_mem_Ioo r ε hε hεr htupper with
        ⟨ρt, hρt, htPath⟩
      have hnorm :
          ε = ρt := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ε αs = exercise21Delta r ε s := hsPath.symm
          _ = exercise21Delta r ε t := hst
          _ = circleMap 0 ρt (Real.pi - Real.arctan (ε / r)) := htPath
        simpa [norm_circleMap_zero, abs_of_pos hε, abs_of_pos (lt_trans hε hρt.1)] using hnorm'
      have : False := by
        linarith [hρt.1, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext ht18
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_upper_inner_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 8 := by simpa using congrArg Subtype.val hsEq
        linarith [hsinner.1]
      exact this.elim
    · left
      exact exercise21Delta_same_branch_injective r ε hε hεr
        (Or.inr <| Or.inl ⟨hsinner, htinner⟩) hst
    · have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext ht14
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_lower_inner_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 4 := by simpa using congrArg Subtype.val hsEq
        linarith [hsinner.2]
      exact this.elim
    · rcases exercise21Delta_eq_lower_lip_circleMap_of_mem_Ioo r ε hε hεr htlower with
        ⟨ρt, hρt, htPath⟩
      have hnorm :
          ε = ρt := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ε αs = exercise21Delta r ε s := hsPath.symm
          _ = exercise21Delta r ε t := hst
          _ = circleMap 0 ρt (-Real.pi + Real.arctan (ε / r)) := htPath
        simpa [norm_circleMap_zero, abs_of_pos hε, abs_of_pos (lt_trans hε hρt.1)] using hnorm'
      have : False := by
        linarith [hρt.1, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext ht12
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_lower_outer_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 2 := by simpa using congrArg Subtype.val hsEq
        linarith [hsinner.2]
      exact this.elim
    · rcases exercise21Delta_eq_outer_arc_circleMap_of_mem_Ioo r ε hε hεr htouter with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          ε = r := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ε αs = exercise21Delta r ε s := hsPath.symm
          _ = exercise21Delta r ε t := hst
          _ = circleMap 0 r αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos hε, abs_of_pos hr] using hnorm'
      have : False := by
        linarith [hεr, hnorm]
      exact this.elim
    · have htEq : t = (1 : I) := Subtype.ext ht1
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.2.2
      have : False := by
        rcases (exercise21Delta_eq_upper_outer_corner_iff r ε hε hεr).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsinner.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsinner.2]
      exact this.elim
  · have hsEq : s = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext hs14
    -- The lower inner corner also has a singleton fiber.
    have htCorner :
        exercise21Delta r ε t = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
      calc
        exercise21Delta r ε t = exercise21Delta r ε s := hst.symm
        _ = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
            simpa [hsEq] using hbreak.2.2.1
    have htEq := (exercise21Delta_eq_lower_inner_corner_iff r ε hε hεr).1 htCorner
    left
    simpa [hsEq, htEq]
  · rcases exercise21Delta_eq_lower_lip_circleMap_of_mem_Ioo r ε hε hεr hslower with
      ⟨ρs, hρs, hsPath⟩
    rcases exercise21Delta_parameter_cases t with
      ht0 | htupper | ht18 | htinner | ht14 | htlower | ht12 | htouter | ht1
    · have htEq : t = (0 : I) := Subtype.ext ht0
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by simpa [htEq] using hbreak.1
      have : False := by
        rcases (exercise21Delta_eq_upper_outer_corner_iff r ε hε hεr).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hslower.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hslower.2]
      exact this.elim
    · rcases exercise21Delta_eq_upper_lip_circleMap_of_mem_Ioo r ε hε hεr htupper with
        ⟨ρt, hρt, htPath⟩
      have hsIm : (exercise21Delta r ε s).im < 0 := by
        rw [hsPath]
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := ρs)
        have hre :=
          exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := ρs) (lt_trans hε hρs.1)
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have htIm : 0 < (exercise21Delta r ε t).im := by
        rw [htPath]
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := ρt)
        have hre :=
          exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := ρt) (lt_trans hε hρt.1)
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have him : (exercise21Delta r ε s).im = (exercise21Delta r ε t).im := congrArg Complex.im hst
      have : False := by
        linarith [hsIm, htIm, him]
      exact this.elim
    · have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext ht18
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_upper_inner_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 8 := by simpa using congrArg Subtype.val hsEq
        linarith [hslower.1]
      exact this.elim
    · rcases exercise21Delta_eq_inner_arc_circleMap_of_mem_Ioo r ε hε hεr htinner with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          ρs = ε := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ρs (-Real.pi + Real.arctan (ε / r)) = exercise21Delta r ε s := hsPath.symm
          _ = exercise21Delta r ε t := hst
          _ = circleMap 0 ε αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos (lt_trans hε hρs.1), abs_of_pos hε] using hnorm'
      have : False := by
        linarith [hρs.1, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext ht14
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_lower_inner_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 4 := by simpa using congrArg Subtype.val hsEq
        linarith [hslower.1]
      exact this.elim
    · left
      exact exercise21Delta_same_branch_injective r ε hε hεr
        (Or.inr <| Or.inr <| Or.inl ⟨hslower, htlower⟩) hst
    · have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext ht12
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_lower_outer_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 2 := by simpa using congrArg Subtype.val hsEq
        linarith [hslower.2]
      exact this.elim
    · rcases exercise21Delta_eq_outer_arc_circleMap_of_mem_Ioo r ε hε hεr htouter with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          ρs = r := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ρs (-Real.pi + Real.arctan (ε / r)) = exercise21Delta r ε s := hsPath.symm
          _ = exercise21Delta r ε t := hst
          _ = circleMap 0 r αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos (lt_trans hε hρs.1), abs_of_pos hr] using hnorm'
      have : False := by
        linarith [hρs.2, hnorm]
      exact this.elim
    · have htEq : t = (1 : I) := Subtype.ext ht1
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.2.2
      have : False := by
        rcases (exercise21Delta_eq_upper_outer_corner_iff r ε hε hεr).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hslower.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hslower.2]
      exact this.elim
  · have hsEq : s = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext hs12
    -- The lower outer corner has a singleton fiber as well.
    have htCorner :
        exercise21Delta r ε t = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
      calc
        exercise21Delta r ε t = exercise21Delta r ε s := hst.symm
        _ = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
            simpa [hsEq] using hbreak.2.2.2.1
    have htEq := (exercise21Delta_eq_lower_outer_corner_iff r ε hε hεr).1 htCorner
    left
    simpa [hsEq, htEq]
  · rcases exercise21Delta_eq_outer_arc_circleMap_of_mem_Ioo r ε hε hεr hsouter with
      ⟨αs, hαs, hsPath⟩
    rcases exercise21Delta_parameter_cases t with
      ht0 | htupper | ht18 | htinner | ht14 | htlower | ht12 | htouter | ht1
    · have htEq : t = (0 : I) := Subtype.ext ht0
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by simpa [htEq] using hbreak.1
      have : False := by
        rcases (exercise21Delta_eq_upper_outer_corner_iff r ε hε hεr).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsouter.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsouter.2]
      exact this.elim
    · rcases exercise21Delta_eq_upper_lip_circleMap_of_mem_Ioo r ε hε hεr htupper with
        ⟨ρt, hρt, htPath⟩
      have hnorm :
          r = ρt := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 r αs = exercise21Delta r ε s := hsPath.symm
          _ = exercise21Delta r ε t := hst
          _ = circleMap 0 ρt (Real.pi - Real.arctan (ε / r)) := htPath
        simpa [norm_circleMap_zero, abs_of_pos hr, abs_of_pos (lt_trans hε hρt.1)] using hnorm'
      have : False := by
        linarith [hρt.2, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext ht18
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_upper_inner_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 8 := by simpa using congrArg Subtype.val hsEq
        linarith [hsouter.1]
      exact this.elim
    · rcases exercise21Delta_eq_inner_arc_circleMap_of_mem_Ioo r ε hε hεr htinner with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          r = ε := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 r αs = exercise21Delta r ε s := hsPath.symm
          _ = exercise21Delta r ε t := hst
          _ = circleMap 0 ε αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] using hnorm'
      have : False := by
        linarith [hεr, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext ht14
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_lower_inner_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 4 := by simpa using congrArg Subtype.val hsEq
        linarith [hsouter.1]
      exact this.elim
    · rcases exercise21Delta_eq_lower_lip_circleMap_of_mem_Ioo r ε hε hεr htlower with
        ⟨ρt, hρt, htPath⟩
      have hnorm :
          r = ρt := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 r αs = exercise21Delta r ε s := hsPath.symm
          _ = exercise21Delta r ε t := hst
          _ = circleMap 0 ρt (-Real.pi + Real.arctan (ε / r)) := htPath
        simpa [norm_circleMap_zero, abs_of_pos hr, abs_of_pos (lt_trans hε hρt.1)] using hnorm'
      have : False := by
        linarith [hρt.2, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext ht12
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.2.1
      have : False := by
        have hsEq := (exercise21Delta_eq_lower_outer_corner_iff r ε hε hεr).1 hsCorner
        have hsval : (s : ℝ) = 1 / 2 := by simpa using congrArg Subtype.val hsEq
        linarith [hsouter.1]
      exact this.elim
    · left
      exact exercise21Delta_same_branch_injective r ε hε hεr
        (Or.inr <| Or.inr <| Or.inr ⟨hsouter, htouter⟩) hst
    · have htEq : t = (1 : I) := Subtype.ext ht1
      have hsCorner :
          exercise21Delta r ε s = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        calc
          exercise21Delta r ε s = exercise21Delta r ε t := hst
          _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
              simpa [htEq] using hbreak.2.2.2.2
      have : False := by
        rcases (exercise21Delta_eq_upper_outer_corner_iff r ε hε hεr).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsouter.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsouter.2]
      exact this.elim
  · have hsEq : s = (1 : I) := Subtype.ext hs1
    -- The terminal endpoint is the second parameter for the same upper outer corner.
    have htCorner :
        exercise21Delta r ε t = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
      calc
        exercise21Delta r ε t = exercise21Delta r ε s := hst.symm
        _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
            simpa [hsEq] using hbreak.2.2.2.2
    rcases (exercise21Delta_eq_upper_outer_corner_iff r ε hε hεr).1 htCorner with ht0 | ht1
    · right
      right
      simpa [hsEq, ht0]
    · left
      simpa [hsEq, ht1]

lemma exercise21Delta_not_differentiable_at_one_eighth
    {r ε : ℝ} (hε : 0 < ε) (hεr : ε < r) :
    ¬ DifferentiableWithinAt ℝ ((exercise21Delta r ε).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (1 / 8 : ℝ) := by
  -- Route correction: compare the upper-lip and inner-arc tangents on their own closed branch
  -- intervals, then use uniqueness of within-derivatives at the shared breakpoint.
  intro hdiff
  let θ : ℝ := Real.arctan (ε / r)
  let γ : ℝ → ℂ := (exercise21Delta r ε).extend
  let d : ℂ := derivWithin γ (Set.Icc (0 : ℝ) 1) (1 / 8 : ℝ)
  let upper : ℝ → ℂ := fun t ↦
    AffineMap.lineMap (circleMap 0 r (Real.pi - θ)) (circleMap 0 ε (Real.pi - θ)) (8 * t)
  let inner : ℝ → ℂ := fun t ↦
    circleMap 0 ε
      (AffineMap.lineMap (Real.pi - θ) (-Real.pi + θ) (8 * t - 1))
  have hγdiff : DifferentiableWithinAt ℝ γ (Set.Icc (0 : ℝ) 1) (1 / 8 : ℝ) := by
    -- Undo the `Complex.equivRealProd` wrapper so the tangent comparison happens in `ℂ`.
    simpa [γ, ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
      (Complex.equivRealProdCLM.comp_differentiableWithinAt_iff.mp hdiff)
  have hmain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) 1) (1 / 8 : ℝ) := by
    simpa [d, γ] using hγdiff.hasDerivWithinAt
  have hupperMain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) (1 / 8 : ℝ) := by
    -- Restrict the ambient derivative to the upper-lip branch interval.
    apply hmain.mono
    intro t ht
    constructor
    · exact ht.1
    · linarith [ht.2]
  have hinnerMain : HasDerivWithinAt γ d (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 8 : ℝ) := by
    -- Restrict the same derivative to the inner-arc branch interval.
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hupperγ :
      HasDerivWithinAt γ ((8 : ℝ) • (circleMap 0 ε (Real.pi - θ) - circleMap 0 r (Real.pi - θ)))
        (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) (1 / 8 : ℝ) := by
    -- Differentiate the affine upper-lip model and transfer it back to the explicit contour.
    have hmodel :
        HasDerivAt upper
          ((8 : ℝ) • (circleMap 0 ε (Real.pi - θ) - circleMap 0 r (Real.pi - θ))) (1 / 8 : ℝ) := by
      have hmodel' :
          HasDerivAt
            (fun t : ℝ ↦
              AffineMap.lineMap
                (circleMap 0 r (Real.pi - θ))
                (circleMap 0 ε (Real.pi - θ))
                (t * 8))
            ((8 : ℝ) • (circleMap 0 ε (Real.pi - θ) - circleMap 0 r (Real.pi - θ)))
            (1 / 8 : ℝ) := by
        simpa [smul_eq_mul, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
          (AffineMap.hasDerivAt_lineMap
            (a := circleMap 0 r (Real.pi - θ))
            (b := circleMap 0 ε (Real.pi - θ))
            (x := (1 / 8 : ℝ) * 8)).scomp
            (1 / 8 : ℝ) ((hasDerivAt_id (1 / 8 : ℝ)).mul_const 8)
      simpa [upper, mul_comm] using hmodel'
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, upper] using exercise21Delta_eq_on_upper_lip r ε ht)
      (by constructor <;> norm_num)
  have hinnerγ :
      HasDerivWithinAt γ
        (((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
          (circleMap 0 ε (Real.pi - θ) * Complex.I))
        (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 8 : ℝ) := by
    -- Differentiate the affine angle parameter first, then the clockwise inner circle.
    have hparam :
        HasDerivAt
          (fun t : ℝ ↦ AffineMap.lineMap (Real.pi - θ) (-Real.pi + θ) (8 * t - 1))
          (8 * ((-Real.pi + θ) - (Real.pi - θ))) (1 / 8 : ℝ) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul, two_mul,
        mul_assoc, mul_left_comm, mul_comm] using
        (AffineMap.hasDerivAt_lineMap
          (a := Real.pi - θ) (b := -Real.pi + θ) (x := (8 : ℝ) * (1 / 8 : ℝ) - 1)).comp
          (1 / 8 : ℝ) (((hasDerivAt_id (1 / 8 : ℝ)).const_mul 8).sub_const 1)
    have hmodel :
        HasDerivAt inner
          (((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
            (circleMap 0 ε (Real.pi - θ) * Complex.I))
          (1 / 8 : ℝ) := by
      simpa [inner, smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add,
        add_mul, two_mul, mul_assoc, mul_left_comm, mul_comm] using
        (hasDerivAt_circleMap 0 ε
          (AffineMap.lineMap (Real.pi - θ) (-Real.pi + θ) ((8 : ℝ) * (1 / 8 : ℝ) - 1))).scomp
          (1 / 8 : ℝ) hparam
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, inner] using exercise21Delta_eq_on_inner_arc r ε ht)
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
      ((8 : ℝ) • (circleMap 0 ε (Real.pi - θ) - circleMap 0 r (Real.pi - θ))) =
        (((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
          (circleMap 0 ε (Real.pi - θ) * Complex.I)) := by
    -- Uniqueness of within-derivatives on the two branch intervals forces the tangents to agree.
    calc
      ((8 : ℝ) • (circleMap 0 ε (Real.pi - θ) - circleMap 0 r (Real.pi - θ)))
          = derivWithin γ (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) (1 / 8 : ℝ) := by
              symm
              exact hupperγ.derivWithin hupperUD
      _ = d := hupperMain.derivWithin hupperUD
      _ = derivWithin γ (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 8 : ℝ) := by
            symm
            exact hinnerMain.derivWithin hinnerUD
      _ =
          (((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
            (circleMap 0 ε (Real.pi - θ) * Complex.I)) :=
            hinnerγ.derivWithin hinnerUD
  have hr : 0 < r := lt_trans hε hεr
  have hθ_pos : 0 < θ := by
    simpa [θ] using Real.arctan_pos.mpr (div_pos hε hr)
  have hupper_im_neg :
      ((((8 : ℝ) • (circleMap 0 ε (Real.pi - θ) - circleMap 0 r (Real.pi - θ))) : ℂ)).im < 0 := by
    have hsin_pos : 0 < Real.sin θ := by
      simpa [θ] using (Real.sin_arctan_pos.mpr (div_pos hε hr))
    have hcore : (ε - r) * Real.sin θ < 0 := by
      exact mul_neg_of_neg_of_pos (sub_neg.mpr hεr) hsin_pos
    have him_formula :
        ((((8 : ℝ) • (circleMap 0 ε (Real.pi - θ) - circleMap 0 r (Real.pi - θ))) : ℂ)).im =
          8 * ((ε - r) * Real.sin θ) := by
      have hsin : Real.sin (Real.pi + -θ) = Real.sin θ := by
        have hangle : Real.pi + -θ = Real.pi - θ := by
          ring
        rw [hangle, Real.sin_pi_sub]
      simp [smul_eq_mul, circleMap_zero_im, sub_eq_add_neg]
      rw [hsin]
      ring_nf
    rw [him_formula]
    exact mul_neg_of_pos_of_neg (by norm_num) hcore
  have hinner_im_pos :
      0 <
        ((((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
            (circleMap 0 ε (Real.pi - θ) * Complex.I)) : ℂ).im := by
    have hθ_bounds := exercise21_keyhole_angle_bounds (r := r) (ε := ε) hε hεr
    have hpi_sub_pos : 0 < Real.pi - θ := by
      have hθ_lt_pi : θ < Real.pi := by
        linarith [hθ_bounds.2, Real.pi_pos]
      linarith
    have hfactor_neg : 8 * ((-Real.pi + θ) - (Real.pi - θ)) < 0 := by
      have hfactor_eq : 8 * ((-Real.pi + θ) - (Real.pi - θ)) = -16 * (Real.pi - θ) := by
        ring
      rw [hfactor_eq]
      nlinarith
    have hre_neg : (circleMap 0 ε (Real.pi - θ)).re < 0 := by
      simpa [θ] using
        (exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := ε) hε)
    rw [show
      ((((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
          (circleMap 0 ε (Real.pi - θ) * Complex.I)) : ℂ).im =
        (8 * ((-Real.pi + θ) - (Real.pi - θ))) *
          (circleMap 0 ε (Real.pi - θ)).re by
          simp [Complex.mul_re, Complex.mul_im, mul_assoc, mul_left_comm, mul_comm]]
    exact mul_pos_of_neg_of_neg hfactor_neg hre_neg
  have him_eq :
      ((((8 : ℝ) • (circleMap 0 ε (Real.pi - θ) - circleMap 0 r (Real.pi - θ))) : ℂ)).im =
        ((((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
            (circleMap 0 ε (Real.pi - θ) * Complex.I)) : ℂ).im := by
    simpa using congrArg Complex.im hcompare
  linarith

lemma exercise21Delta_not_differentiable_at_one_quarter
    {r ε : ℝ} (hε : 0 < ε) (hεr : ε < r) :
    ¬ DifferentiableWithinAt ℝ ((exercise21Delta r ε).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (1 / 4 : ℝ) := by
  -- Compare the inner-arc and lower-lip tangents at the second corner of the keyhole contour.
  intro hdiff
  let θ : ℝ := Real.arctan (ε / r)
  let γ : ℝ → ℂ := (exercise21Delta r ε).extend
  let d : ℂ := derivWithin γ (Set.Icc (0 : ℝ) 1) (1 / 4 : ℝ)
  let inner : ℝ → ℂ := fun t ↦
    circleMap 0 ε
      (AffineMap.lineMap (Real.pi - θ) (-Real.pi + θ) (8 * t - 1))
  let lower : ℝ → ℂ := fun t ↦
    AffineMap.lineMap
      (circleMap 0 ε (-Real.pi + θ))
      (circleMap 0 r (-Real.pi + θ))
      (4 * t - 1)
  have hγdiff : DifferentiableWithinAt ℝ γ (Set.Icc (0 : ℝ) 1) (1 / 4 : ℝ) := by
    -- Move from the real-plane curve back to the complex-valued path.
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
        (((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
          (circleMap 0 ε (-Real.pi + θ) * Complex.I))
        (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 4 : ℝ) := by
    -- Differentiate the angular branch model and transfer it back to the explicit contour.
    have hparam :
        HasDerivAt
          (fun t : ℝ ↦ AffineMap.lineMap (Real.pi - θ) (-Real.pi + θ) (8 * t - 1))
          (8 * ((-Real.pi + θ) - (Real.pi - θ))) (1 / 4 : ℝ) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul, two_mul,
        mul_assoc, mul_left_comm, mul_comm] using
        (AffineMap.hasDerivAt_lineMap
          (a := Real.pi - θ) (b := -Real.pi + θ) (x := (8 : ℝ) * (1 / 4 : ℝ) - 1)).comp
          (1 / 4 : ℝ) (((hasDerivAt_id (1 / 4 : ℝ)).const_mul 8).sub_const 1)
    have hmodel :
        HasDerivAt inner
          (((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
            (circleMap 0 ε (-Real.pi + θ) * Complex.I))
          (1 / 4 : ℝ) := by
      have hmodel_raw :
          HasDerivAt inner
            (((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
              (circleMap 0 ε
                (AffineMap.lineMap (Real.pi - θ) (-Real.pi + θ) ((8 : ℝ) * (1 / 4 : ℝ) - 1)) *
                Complex.I))
            (1 / 4 : ℝ) := by
        simpa [inner, smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add,
          add_mul, two_mul, mul_assoc, mul_left_comm, mul_comm] using
          (hasDerivAt_circleMap 0 ε
            (AffineMap.lineMap (Real.pi - θ) (-Real.pi + θ) ((8 : ℝ) * (1 / 4 : ℝ) - 1))).scomp
            (1 / 4 : ℝ) hparam
      have hquarter_param : (8 : ℝ) * (1 / 4 : ℝ) - 1 = 1 := by
        norm_num
      convert hmodel_raw using 1
      rw [hquarter_param, AffineMap.lineMap_apply_one]
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, inner] using exercise21Delta_eq_on_inner_arc r ε ht)
      (by constructor <;> norm_num)
  have hlowerγ :
      HasDerivWithinAt γ
        ((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ)))
        (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 4 : ℝ) := by
    -- Differentiate the affine lower-lip model and transfer it back to the explicit contour.
    have hmodel :
        HasDerivAt lower
          ((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ)))
          (1 / 4 : ℝ) := by
      have hmodel' :
          HasDerivAt
            (fun t : ℝ ↦
              AffineMap.lineMap
                (circleMap 0 ε (-Real.pi + θ))
                (circleMap 0 r (-Real.pi + θ))
                (t * 4 - 1))
            ((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ)))
            (1 / 4 : ℝ) := by
        simpa [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul,
          two_mul, mul_assoc, mul_left_comm, mul_comm] using
          (AffineMap.hasDerivAt_lineMap
            (a := circleMap 0 ε (-Real.pi + θ))
            (b := circleMap 0 r (-Real.pi + θ))
            (x := (1 / 4 : ℝ) * 4 - 1)).scomp
            (1 / 4 : ℝ) (((hasDerivAt_id (1 / 4 : ℝ)).mul_const 4).sub_const 1)
      simpa [lower, mul_comm] using hmodel'
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, lower] using exercise21Delta_eq_on_lower_lip r ε ht)
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
      (((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
        (circleMap 0 ε (-Real.pi + θ) * Complex.I)) =
        ((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ))) := by
    -- Uniqueness of within-derivatives forces the two one-sided tangents to agree.
    calc
      (((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
          (circleMap 0 ε (-Real.pi + θ) * Complex.I))
          = derivWithin γ (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 4 : ℝ) := by
              symm
              exact hinnerγ.derivWithin hinnerUD
      _ = d := hinnerMain.derivWithin hinnerUD
      _ = derivWithin γ (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 4 : ℝ) := by
            symm
            exact hlowerMain.derivWithin hlowerUD
      _ = ((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ))) :=
            hlowerγ.derivWithin hlowerUD
  have hr : 0 < r := lt_trans hε hεr
  have hθ_pos : 0 < θ := by
    simpa [θ] using Real.arctan_pos.mpr (div_pos hε hr)
  have hinner_im_pos :
      0 <
        ((((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
            (circleMap 0 ε (-Real.pi + θ) * Complex.I)) : ℂ).im := by
    have hθ_bounds := exercise21_keyhole_angle_bounds (r := r) (ε := ε) hε hεr
    have hpi_sub_pos : 0 < Real.pi - θ := by
      have hθ_lt_pi : θ < Real.pi := by
        linarith [hθ_bounds.2, Real.pi_pos]
      linarith
    have hfactor_neg : 8 * ((-Real.pi + θ) - (Real.pi - θ)) < 0 := by
      have hfactor_eq : 8 * ((-Real.pi + θ) - (Real.pi - θ)) = -16 * (Real.pi - θ) := by
        ring
      rw [hfactor_eq]
      nlinarith
    have hre_neg : (circleMap 0 ε (-Real.pi + θ)).re < 0 := by
      simpa [θ] using
        (exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := ε) hε)
    rw [show
      ((((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
          (circleMap 0 ε (-Real.pi + θ) * Complex.I)) : ℂ).im =
        (8 * ((-Real.pi + θ) - (Real.pi - θ))) *
          (circleMap 0 ε (-Real.pi + θ)).re by
          simp [Complex.mul_re, Complex.mul_im, mul_assoc, mul_left_comm, mul_comm]]
    exact mul_pos_of_neg_of_neg hfactor_neg hre_neg
  have hlower_im_neg :
      ((((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ))) : ℂ)).im < 0 := by
    have hsin_pos : 0 < Real.sin θ := by
      simpa [θ] using (Real.sin_arctan_pos.mpr (div_pos hε hr))
    have hsin_neg : -Real.sin θ < 0 := by
      linarith
    have hcore : (r - ε) * (-Real.sin θ) < 0 := by
      exact mul_neg_of_pos_of_neg (sub_pos.mpr hεr) hsin_neg
    rw [show
      ((((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ))) : ℂ)).im =
        4 * ((r - ε) * (-Real.sin θ)) by
          simp [circleMap_zero_im, sub_eq_add_neg]
          have hsin :
              Real.sin (-Real.pi + θ) = -Real.sin θ := by
            rw [show -Real.pi + θ = θ - Real.pi by ring]
            simp [Real.sin_sub]
          rw [hsin]
          ring]
    exact mul_neg_of_pos_of_neg (by norm_num) hcore
  have him_eq :
      ((((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
          (circleMap 0 ε (-Real.pi + θ) * Complex.I)) : ℂ).im =
        ((((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ))) : ℂ)).im := by
    simpa using congrArg Complex.im hcompare
  linarith

lemma exercise21Delta_not_differentiable_at_one_half
    {r ε : ℝ} (hε : 0 < ε) (hεr : ε < r) :
    ¬ DifferentiableWithinAt ℝ ((exercise21Delta r ε).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
  -- Compare the lower-lip and outer-arc tangents at the third corner of the keyhole contour.
  intro hdiff
  let θ : ℝ := Real.arctan (ε / r)
  let γ : ℝ → ℂ := (exercise21Delta r ε).extend
  let d : ℂ := derivWithin γ (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ)
  let lower : ℝ → ℂ := fun t ↦
    AffineMap.lineMap
      (circleMap 0 ε (-Real.pi + θ))
      (circleMap 0 r (-Real.pi + θ))
      (4 * t - 1)
  let outer : ℝ → ℂ := fun t ↦
    circleMap 0 r
      (AffineMap.lineMap (-Real.pi + θ) (Real.pi - θ) (2 * t - 1))
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
        ((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ)))
        (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    -- Differentiate the affine lower-lip model and transfer it back to the explicit contour.
    have hmodel :
        HasDerivAt lower
          ((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ)))
          (1 / 2 : ℝ) := by
      have hmodel' :
          HasDerivAt
            (fun t : ℝ ↦
              AffineMap.lineMap
                (circleMap 0 ε (-Real.pi + θ))
                (circleMap 0 r (-Real.pi + θ))
                (t * 4 - 1))
            ((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ)))
            (1 / 2 : ℝ) := by
        simpa [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul,
          two_mul, mul_assoc, mul_left_comm, mul_comm] using
          (AffineMap.hasDerivAt_lineMap
            (a := circleMap 0 ε (-Real.pi + θ))
            (b := circleMap 0 r (-Real.pi + θ))
            (x := (1 / 2 : ℝ) * 4 - 1)).scomp
            (1 / 2 : ℝ) (((hasDerivAt_id (1 / 2 : ℝ)).mul_const 4).sub_const 1)
      simpa [lower, mul_comm] using hmodel'
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, lower] using exercise21Delta_eq_on_lower_lip r ε ht)
      (by constructor <;> norm_num)
  have houterγ :
      HasDerivWithinAt γ
        (((2 * ((Real.pi - θ) - (-Real.pi + θ))) : ℝ) •
          (circleMap 0 r (-Real.pi + θ) * Complex.I))
        (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) := by
    -- Differentiate the outer circular arc through its affine angle parameter.
    have hparam :
        HasDerivAt
          (fun t : ℝ ↦ AffineMap.lineMap (-Real.pi + θ) (Real.pi - θ) (2 * t - 1))
          (2 * ((Real.pi - θ) - (-Real.pi + θ))) (1 / 2 : ℝ) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul, two_mul,
        mul_assoc, mul_left_comm, mul_comm] using
        (AffineMap.hasDerivAt_lineMap
          (a := -Real.pi + θ) (b := Real.pi - θ) (x := (2 : ℝ) * (1 / 2 : ℝ) - 1)).comp
          (1 / 2 : ℝ) (((hasDerivAt_id (1 / 2 : ℝ)).const_mul 2).sub_const 1)
    have hmodel :
        HasDerivAt outer
          (((2 * ((Real.pi - θ) - (-Real.pi + θ))) : ℝ) •
            (circleMap 0 r (-Real.pi + θ) * Complex.I))
          (1 / 2 : ℝ) := by
      simpa [outer, smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add,
        add_mul, two_mul, mul_assoc, mul_left_comm, mul_comm] using
        (hasDerivAt_circleMap 0 r
          (AffineMap.lineMap (-Real.pi + θ) (Real.pi - θ) ((2 : ℝ) * (1 / 2 : ℝ) - 1))).scomp
          (1 / 2 : ℝ) hparam
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, outer] using exercise21Delta_eq_on_outer_arc r ε ht)
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
      ((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ))) =
        (((2 * ((Real.pi - θ) - (-Real.pi + θ))) : ℝ) •
          (circleMap 0 r (-Real.pi + θ) * Complex.I)) := by
    -- Uniqueness of within-derivatives forces the two one-sided tangents to agree.
    calc
      ((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ)))
          = derivWithin γ (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
              symm
              exact hlowerγ.derivWithin hlowerUD
      _ = d := hlowerMain.derivWithin hlowerUD
      _ = derivWithin γ (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) := by
            symm
            exact houterMain.derivWithin houterUD
      _ =
          (((2 * ((Real.pi - θ) - (-Real.pi + θ))) : ℝ) •
            (circleMap 0 r (-Real.pi + θ) * Complex.I)) :=
            houterγ.derivWithin houterUD
  have hr : 0 < r := lt_trans hε hεr
  have hθ_pos : 0 < θ := by
    simpa [θ] using Real.arctan_pos.mpr (div_pos hε hr)
  have hlower_re_neg :
      ((((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ))) : ℂ)).re < 0 := by
    have hcos_pos : 0 < Real.cos θ := by
      simpa [θ] using Real.cos_arctan_pos (ε / r)
    have hcos_neg : -Real.cos θ < 0 := by
      linarith
    have hcore : (r - ε) * (-Real.cos θ) < 0 := by
      exact mul_neg_of_pos_of_neg (sub_pos.mpr hεr) hcos_neg
    rw [show
      ((((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ))) : ℂ)).re =
        4 * ((r - ε) * (-Real.cos θ)) by
          simp [circleMap_zero_re, sub_eq_add_neg]
          have hcos :
              Real.cos (-Real.pi + θ) = -Real.cos θ := by
            rw [show -Real.pi + θ = θ - Real.pi by ring]
            simp [Real.cos_sub]
          rw [hcos]
          ring]
    exact mul_neg_of_pos_of_neg (by norm_num) hcore
  have houter_re_pos :
      0 <
        ((((2 * ((Real.pi - θ) - (-Real.pi + θ))) : ℝ) •
            (circleMap 0 r (-Real.pi + θ) * Complex.I)) : ℂ).re := by
    have hθ_bounds := exercise21_keyhole_angle_bounds (r := r) (ε := ε) hε hεr
    have hpi_sub_pos : 0 < Real.pi - θ := by
      have hθ_lt_pi : θ < Real.pi := by
        linarith [hθ_bounds.2, Real.pi_pos]
      linarith
    have hfactor_pos : 0 < 2 * ((Real.pi - θ) - (-Real.pi + θ)) := by
      have hfactor_eq : 2 * ((Real.pi - θ) - (-Real.pi + θ)) = 4 * (Real.pi - θ) := by
        ring
      rw [hfactor_eq]
      nlinarith
    have hre_neg : (circleMap 0 r (-Real.pi + θ)).re < 0 := by
      simpa [θ] using
        (exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := r) hr)
    have him_neg : (circleMap 0 r (-Real.pi + θ)).im < 0 := by
      have hline :
          (circleMap 0 r (-Real.pi + θ)).im =
            (ε / r) * (circleMap 0 r (-Real.pi + θ)).re := by
        simpa [θ] using exercise21Delta_lower_lip_line r ε r
      rw [hline]
      exact mul_neg_of_pos_of_neg (div_pos hε hr) hre_neg
    rw [show
      ((((2 * ((Real.pi - θ) - (-Real.pi + θ))) : ℝ) •
          (circleMap 0 r (-Real.pi + θ) * Complex.I)) : ℂ).re =
        (2 * ((Real.pi - θ) - (-Real.pi + θ))) *
          (-(circleMap 0 r (-Real.pi + θ)).im) by
          simp [Complex.mul_re, Complex.mul_im, mul_assoc, mul_left_comm, mul_comm]]
    exact mul_pos hfactor_pos (by linarith)
  have hre_eq :
      ((((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ))) : ℂ)).re =
        ((((2 * ((Real.pi - θ) - (-Real.pi + θ))) : ℝ) •
            (circleMap 0 r (-Real.pi + θ) * Complex.I)) : ℂ).re := by
    simpa using congrArg Complex.re hcompare
  linarith

lemma exercise21Delta_regular_parameter_mem_open_branch
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ ((exercise21Delta r ε).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀) :
    t₀ ∈ Set.Ioo (0 : ℝ) (1 / 8) ∨
      t₀ ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4) ∨
      t₀ ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∨
      t₀ ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ) := by
  let t : I := ⟨t₀, ⟨ht₀.1.le, ht₀.2.le⟩⟩
  -- The interval dispatcher leaves only the four open branches and the three genuine corners.
  rcases exercise21Delta_parameter_cases t with
    ht0 | htupper | ht18 | htinner | ht14 | htlower | ht12 | htouter | ht1
  · exfalso
    have ht0' : t₀ = 0 := by
      simpa [t] using ht0
    linarith [ht₀.1, ht0']
  · exact Or.inl htupper
  · exfalso
    have ht18' : t₀ = 1 / 8 := by
      simpa [t] using ht18
    exact
      (exercise21Delta_not_differentiable_at_one_eighth hε hεr)
        (by simpa [ht18'] using hdiff)
  · exact Or.inr <| Or.inl htinner
  · exfalso
    have ht14' : t₀ = 1 / 4 := by
      simpa [t] using ht14
    exact
      (exercise21Delta_not_differentiable_at_one_quarter hε hεr)
        (by simpa [ht14'] using hdiff)
  · exact Or.inr <| Or.inr <| Or.inl htlower
  · exfalso
    have ht12' : t₀ = 1 / 2 := by
      simpa [t] using ht12
    exact
      (exercise21Delta_not_differentiable_at_one_half hε hεr)
        (by simpa [ht12'] using hdiff)
  · exact Or.inr <| Or.inr <| Or.inr htouter
  · exfalso
    have ht1' : t₀ = 1 := by
      simpa [t] using ht1
    linarith [ht₀.2, ht1']

lemma exercise21_radial_segment_range_subset_slitPlane_of_angle
    {ρ₀ ρ₁ φ : ℝ}
    (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁) (hφ : φ ∈ Set.Ioo (-Real.pi) Real.pi) :
    Set.range (Path.segment (circleMap 0 ρ₀ φ) (circleMap 0 ρ₁ φ)) ⊆ Complex.slitPlane := by
  rintro z ⟨t, rfl⟩
  -- The segment only changes the radius, and the interpolated radius stays positive.
  have hρt : 0 < AffineMap.lineMap ρ₀ ρ₁ (t : ℝ) := by
    exact (convex_Ioi (0 : ℝ)).lineMap_mem hρ₀ hρ₁ t.2
  have hsegment_eq :
      (Path.segment (circleMap 0 ρ₀ φ) (circleMap 0 ρ₁ φ)) t =
        circleMap 0 (AffineMap.lineMap ρ₀ ρ₁ (t : ℝ)) φ := by
    -- A straight interpolation along a fixed ray only interpolates the radius.
    rw [Complex.ext_iff]
    constructor <;>
      simp [Path.segment_apply, circleMap_zero_re, circleMap_zero_im,
        AffineMap.lineMap_apply_module, smul_eq_mul, add_mul] <;>
      ring
  simpa [hsegment_eq] using
    (exercise21_mem_slitPlane_circleMap_of_angle
      (ρ := AffineMap.lineMap ρ₀ ρ₁ (t : ℝ)) (φ := φ) hρt hφ.1 hφ.2)

/-- Helper for Exercise 21: a circular arc obtained by varying the angle between two admissible
endpoints stays inside `Complex.slitPlane`. -/
lemma exercise21_circle_arc_range_subset_slitPlane_of_endpoints
    {ρ α β : ℝ}
    (hρ : 0 < ρ) (hα : α ∈ Set.Ioo (-Real.pi) Real.pi) (hβ : β ∈ Set.Ioo (-Real.pi) Real.pi) :
    Set.range (((Path.segment α β).map (continuous_circleMap 0 ρ))) ⊆ Complex.slitPlane := by
  rintro z ⟨t, rfl⟩
  -- The affine angle parameter stays in `(-π, π)` because both endpoints do.
  have hangle : AffineMap.lineMap α β (t : ℝ) ∈ Set.Ioo (-Real.pi) Real.pi := by
    exact (convex_Ioo (-Real.pi) Real.pi).lineMap_mem hα hβ t.2
  simpa only [Path.map_coe, Function.comp_apply, Path.segment_apply] using
    (exercise21_mem_slitPlane_circleMap_of_angle
      (ρ := ρ) (φ := AffineMap.lineMap α β (t : ℝ)) hρ hangle.1 hangle.2)

/-- Helper for Exercise 21: the image of `exercise21Delta` is the union of its upper lip, inner
arc, lower lip, and outer arc. -/
theorem exercise21Delta_range_eq_four_piece_union (r ε : ℝ) :
    Set.range (exercise21Delta r ε) =
      let θ := Real.arctan (ε / r)
      let upper : Path (circleMap 0 r (Real.pi - θ)) (circleMap 0 ε (Real.pi - θ)) :=
        Path.segment (circleMap 0 r (Real.pi - θ)) (circleMap 0 ε (Real.pi - θ))
      let inner : Path (circleMap 0 ε (Real.pi - θ)) (circleMap 0 ε (-Real.pi + θ)) :=
        (Path.segment (Real.pi - θ) (-Real.pi + θ)).map (continuous_circleMap 0 ε)
      let lower : Path (circleMap 0 ε (-Real.pi + θ)) (circleMap 0 r (-Real.pi + θ)) :=
        Path.segment (circleMap 0 ε (-Real.pi + θ)) (circleMap 0 r (-Real.pi + θ))
      let outer : Path (circleMap 0 r (-Real.pi + θ)) (circleMap 0 r (Real.pi - θ)) :=
        (Path.segment (-Real.pi + θ) (Real.pi - θ)).map (continuous_circleMap 0 r)
      Set.range upper ∪ Set.range inner ∪ Set.range lower ∪ Set.range outer := by
  -- Expand the concatenation once so later proofs can work with the four canonical pieces.
  rw [exercise21Delta_def]
  simp [Path.trans_range]

/-- Helper for Exercise 21: a radial segment along a fixed argument stays inside the closed annulus
`{z | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r}` as soon as both endpoint radii lie in `[ε, r]`. -/
lemma exercise21_radial_segment_range_subset_closed_annulus_of_angle
    {ρ₀ ρ₁ φ r ε : ℝ}
    (hε : 0 ≤ ε)
    (hρ₀ : ρ₀ ∈ Set.Icc ε r) (hρ₁ : ρ₁ ∈ Set.Icc ε r) :
    Set.range (Path.segment (circleMap 0 ρ₀ φ) (circleMap 0 ρ₁ φ)) ⊆
      {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} := by
  rintro z ⟨t, rfl⟩
  have hρt : AffineMap.lineMap ρ₀ ρ₁ (t : ℝ) ∈ Set.Icc ε r := by
    -- Convexity of the closed interval keeps the interpolated radius between `ε` and `r`.
    exact (convex_Icc ε r).lineMap_mem hρ₀ hρ₁ t.2
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

/-- Helper for Exercise 21: a circular arc with fixed radius inside `[ε, r]` stays in the same
closed annulus. -/
lemma exercise21_circle_arc_range_subset_closed_annulus_of_radius_bounds
    {ρ α β r ε : ℝ}
    (hε : 0 ≤ ε)
    (hρ : ρ ∈ Set.Icc ε r) :
    Set.range (((Path.segment α β).map (continuous_circleMap 0 ρ))) ⊆
      {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} := by
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

/-- Helper for Exercise 21: every point of the textbook keyhole contour stays in the closed annulus
`{z | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r}`. This isolates the radial control from the later slit-boundary
arguments. -/
lemma exercise21Delta_range_subset_closed_annulus
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    Set.range (exercise21Delta r ε) ⊆ {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} := by
  have hε_nonneg : 0 ≤ ε := le_of_lt hε
  have hupper :
      Set.range
          (Path.segment (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
            (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))) ⊆
        {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} := by
    -- The upper slit lip interpolates between the two allowed radii `r` and `ε`.
    exact exercise21_radial_segment_range_subset_closed_annulus_of_angle
      hε_nonneg
      (ρ₀ := r) (ρ₁ := ε)
      (φ := Real.pi - Real.arctan (ε / r))
      (r := r) (ε := ε)
      ⟨le_of_lt hεr, le_rfl⟩
      ⟨le_rfl, le_of_lt hεr⟩
  have hinner :
      Set.range
          (((Path.segment (Real.pi - Real.arctan (ε / r))
              (-Real.pi + Real.arctan (ε / r))).map (continuous_circleMap 0 ε))) ⊆
        {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} := by
    -- The inner arc has constant radius exactly `ε`.
    exact exercise21_circle_arc_range_subset_closed_annulus_of_radius_bounds
      hε_nonneg
      (ρ := ε) (α := Real.pi - Real.arctan (ε / r))
      (β := -Real.pi + Real.arctan (ε / r))
      (r := r) (ε := ε)
      ⟨le_rfl, le_of_lt hεr⟩
  have hlower :
      Set.range
          (Path.segment (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
            (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))) ⊆
        {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} := by
    -- The lower slit lip uses the same two radii with the opposite orientation.
    exact exercise21_radial_segment_range_subset_closed_annulus_of_angle
      hε_nonneg
      (ρ₀ := ε) (ρ₁ := r)
      (φ := -Real.pi + Real.arctan (ε / r))
      (r := r) (ε := ε)
      ⟨le_rfl, le_of_lt hεr⟩
      ⟨le_of_lt hεr, le_rfl⟩
  have houter :
      Set.range
          (((Path.segment (-Real.pi + Real.arctan (ε / r))
              (Real.pi - Real.arctan (ε / r))).map (continuous_circleMap 0 r))) ⊆
        {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} := by
    -- The outer arc has constant radius exactly `r`.
    exact exercise21_circle_arc_range_subset_closed_annulus_of_radius_bounds
      hε_nonneg
      (ρ := r) (α := -Real.pi + Real.arctan (ε / r))
      (β := Real.pi - Real.arctan (ε / r))
      (r := r) (ε := ε)
      ⟨le_of_lt hεr, le_rfl⟩
  -- Decompose the contour into its four canonical pieces and apply the corresponding annulus bound.
  rw [exercise21Delta_range_eq_four_piece_union]
  intro z hz
  rcases hz with hz | hz
  · rcases hz with hz | hz
    · rcases hz with hz | hz
      · exact hupper hz
      · exact hinner hz
    · exact hlower hz
  · exact houter hz

/-- Helper for Exercise 21: every point of the textbook keyhole contour `δ(r, ε)` stays in
`Complex.slitPlane`, so the principal branch of `Complex.log` is available all along the contour. -/
lemma exercise21Delta_range_subset_slitPlane
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    Set.range (exercise21Delta r ε) ⊆ Complex.slitPlane := by
  -- Route correction: the stable Lean interface is `Set.range`, not path-extension formulas.
  -- Decompose the contour once, then prove each of the four canonical pieces stays in the slit.
  have hr : 0 < r := lt_trans hε hεr
  have hθ :
      0 < Real.arctan (ε / r) ∧ Real.arctan (ε / r) < Real.pi / 2 :=
    exercise21_keyhole_angle_bounds (r := r) (ε := ε) hε hεr
  have hupperAngle : Real.pi - Real.arctan (ε / r) ∈ Set.Ioo (-Real.pi) Real.pi := by
    constructor
    · nlinarith [hθ.2, Real.pi_pos]
    · nlinarith [hθ.1]
  have hlowerAngle : -Real.pi + Real.arctan (ε / r) ∈ Set.Ioo (-Real.pi) Real.pi := by
    constructor
    · nlinarith [hθ.1]
    · nlinarith [hθ.2, Real.pi_pos]
  have hupper :
      Set.range
          (Path.segment (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
            (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))) ⊆ Complex.slitPlane := by
    -- The upper slit lip is a radial segment on the admissible ray `arg = π - θ`.
    exact exercise21_radial_segment_range_subset_slitPlane_of_angle hr hε hupperAngle
  have hinner :
      Set.range
          (((Path.segment (Real.pi - Real.arctan (ε / r))
              (-Real.pi + Real.arctan (ε / r))).map (continuous_circleMap 0 ε))) ⊆
        Complex.slitPlane := by
    -- The inner circular arc keeps its angle strictly between `-π` and `π`.
    exact exercise21_circle_arc_range_subset_slitPlane_of_endpoints hε hupperAngle hlowerAngle
  have hlower :
      Set.range
          (Path.segment (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
            (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))) ⊆ Complex.slitPlane := by
    -- The lower slit lip is the same radial argument with the opposite orientation.
    exact exercise21_radial_segment_range_subset_slitPlane_of_angle hε hr hlowerAngle
  have houter :
      Set.range
          (((Path.segment (-Real.pi + Real.arctan (ε / r))
              (Real.pi - Real.arctan (ε / r))).map (continuous_circleMap 0 r))) ⊆
        Complex.slitPlane := by
    -- The outer circular arc also stays away from the forbidden angle `π`.
    exact exercise21_circle_arc_range_subset_slitPlane_of_endpoints hr hlowerAngle hupperAngle
  rw [exercise21Delta_range_eq_four_piece_union]
  intro z hz
  rcases hz with hz | hz
  · rcases hz with hz | hz
    · rcases hz with hz | hz
      · exact hupper hz
      · exact hinner hz
    · exact hlower hz
  · exact houter hz

/-- Helper for Exercise 21: the singleton closed-path family attached to `exercise21Delta` has
union equal to the actual contour range. This is the stable interface between the explicit path
formula and the `IsOrientedBoundaryOf` family API. -/
lemma exercise21Delta_singleton_iUnion_range (r ε : ℝ) :
    (⋃ i : Unit,
        Set.range ((((fun _ : Unit ↦ (exercise21Delta r ε).toClosedPath) i).toPath))) =
      Set.range (exercise21Delta r ε) := by
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

/-- Helper for Exercise 21: a holomorphic kernel of the form `g(z) / (z - a)` realizes its
residue `g(a)` on every positively oriented small circle that stays inside both `interior K` and
`D`. -/
lemma localResidueCircle_div_sub_of_differentiableOn
    {K D : Set ℂ} {g : ℂ → ℂ} {a : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hK : Metric.closedBall a r ⊆ interior K)
    (hD : Metric.closedBall a r ⊆ D)
    (hg : DifferentiableOn ℂ g D) :
    LocalResidueCircle K D (fun z ↦ g z / (z - a)) a (g a) := by
  -- Choose the given circle and evaluate its Cauchy kernel integral by the disc Cauchy formula.
  refine ⟨r, hr, hK, hD, ?_⟩
  have hg_ball : DifferentiableOn ℂ g (Metric.closedBall a r) := hg.mono hD
  have ha_ball : a ∈ Metric.ball a r := by
    exact (Metric.mem_ball_self hr : a ∈ Metric.ball a r)
  simpa [div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    hg_ball.circleIntegral_sub_inv_smul ha_ball

/-- Helper for Exercise 21: the principal logarithm factors as `(z - 1)` times the first divided
difference `dslope log 1 z`. -/
lemma exercise21_log_eq_sub_one_mul_dslope (z : ℂ) :
    Complex.log z = (z - 1) * dslope Complex.log 1 z := by
  -- This is the standard divided-difference identity specialized at the simple zero of `log`.
  simpa [Complex.log_one] using (sub_smul_dslope Complex.log 1 z).symm

/-- Helper for Exercise 21: the factor `log z` can be rewritten through `dslope log 1 z`, so the
integrand takes the standard `/(z - 1)` kernel form. -/
lemma exercise21_integrand_eq_real_pole_kernel (a : ℝ) {z : ℂ} :
    (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) =
      (((z ^ 2 + (a : ℂ) ^ 2) * dslope Complex.log 1 z)⁻¹) / (z - 1) := by
  -- Rewrite `log z` by its divided-difference factor and normalize the resulting reciprocal.
  rw [exercise21_log_eq_sub_one_mul_dslope]
  field_simp

/-- Helper for Exercise 21: away from `z = a i`, the integrand is a standard simple-pole kernel
with coefficient `(((z + a i) * log z)⁻¹)`. -/
lemma exercise21_integrand_eq_pos_imag_pole_kernel (a : ℝ) {z : ℂ}
    (hz : z ≠ (a : ℂ) * Complex.I) :
    (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) =
      ((((z + (a : ℂ) * Complex.I) * Complex.log z)⁻¹) / (z - (a : ℂ) * Complex.I)) := by
  -- Factor `z² + a²` as `(z - ai)(z + ai)` and isolate the simple pole at `z = ai`.
  have hz' : z - (a : ℂ) * Complex.I ≠ 0 := sub_ne_zero.mpr hz
  calc
    (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹)
        = ((((z - (a : ℂ) * Complex.I) * (z + (a : ℂ) * Complex.I)) * Complex.log z)⁻¹) := by
            congr 1
            ring_nf
            simp [pow_two]
    _ = ((((z + (a : ℂ) * Complex.I) * Complex.log z)⁻¹) / (z - (a : ℂ) * Complex.I)) := by
          field_simp [hz']

/-- Helper for Exercise 21: away from `z = -a i`, the integrand is a standard simple-pole kernel
with coefficient `(((z - a i) * log z)⁻¹)`. -/
lemma exercise21_integrand_eq_neg_imag_pole_kernel (a : ℝ) {z : ℂ}
    (hz : z ≠ -((a : ℂ) * Complex.I)) :
    (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) =
      ((((z - (a : ℂ) * Complex.I) * Complex.log z)⁻¹) / (z + (a : ℂ) * Complex.I)) := by
  -- Factor `z² + a²` as `(z + ai)(z - ai)` and isolate the simple pole at `z = -ai`.
  have hz' : z + (a : ℂ) * Complex.I ≠ 0 := by
    simpa [eq_neg_iff_add_eq_zero] using hz
  calc
    (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹)
        = ((((z + (a : ℂ) * Complex.I) * (z - (a : ℂ) * Complex.I)) * Complex.log z)⁻¹) := by
            congr 1
            ring_nf
            simp [pow_two]
    _ = ((((z - (a : ℂ) * Complex.I) * Complex.log z)⁻¹) / (z + (a : ℂ) * Complex.I)) := by
          field_simp [hz']

/-- Helper for Exercise 21: on the principal branch, `log (a i)` is `log a + π i / 2` for
positive real `a`. -/
lemma exercise21_log_mul_I_of_pos (a : ℝ) (ha : 0 < a) :
    Complex.log ((a : ℂ) * Complex.I) = Real.log a + (Real.pi / 2 : ℝ) * Complex.I := by
  -- Factor out the positive real scalar so that the branch value reduces to `log I`.
  simpa [Complex.log_I, add_comm] using
    (Complex.log_ofReal_mul (x := Complex.I) ha Complex.I_ne_zero)

/-- Helper for Exercise 21: on the principal branch, `log (-a i)` is `log a - π i / 2` for
positive real `a`. -/
lemma exercise21_log_neg_mul_I_of_pos (a : ℝ) (ha : 0 < a) :
    Complex.log (-((a : ℂ) * Complex.I)) = Real.log a - (Real.pi / 2 : ℝ) * Complex.I := by
  -- Rewrite `-a i` as the positive real `a` times `-I`, then use the principal-branch value of
  -- `log (-I)`.
  rw [show -((a : ℂ) * Complex.I) = (a : ℂ) * (-Complex.I) by ring]
  simpa [Complex.log_neg_I, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (Complex.log_ofReal_mul (x := -Complex.I) ha (by simp : (-Complex.I) ≠ 0))

/-- Helper for Exercise 21: the pole at `z = 1` already contributes a real-valued term. -/
lemma exercise21_real_pole_term (a : ℝ) :
    1 / ((1 : ℂ) + (a : ℂ) ^ 2) = (1 / (1 + a ^ 2) : ℂ) := by
  -- The denominator is a real scalar, so the complex reciprocal is just the coerced real one.
  simp [pow_two]

/-- Helper for Exercise 21: expand the denominator at `z = a i` into explicit real and imaginary
parts. -/
lemma exercise21_term2_rewrite (a : ℝ) :
    ((2 * (a : ℂ) * Complex.I) * (Real.log a + (Real.pi / 2 : ℝ) * Complex.I)) =
      (-(a * Real.pi) : ℝ) + ((2 * a * Real.log a : ℝ) : ℂ) * Complex.I := by
  -- This is the direct multiplication needed before taking reciprocals.
  rw [Complex.ext_iff]
  constructor
  · simp [mul_add, mul_assoc]
    ring
  · simp [mul_add, mul_assoc]

/-- Helper for Exercise 21: expand the denominator at `z = -a i` into explicit real and imaginary
parts. -/
lemma exercise21_term3_rewrite (a : ℝ) :
    ((2 * (a : ℂ) * Complex.I) * (Real.log a - (Real.pi / 2 : ℝ) * Complex.I)) =
      ((a * Real.pi : ℝ) : ℂ) + ((2 * a * Real.log a : ℝ) : ℂ) * Complex.I := by
  -- The same expansion with the opposite branch value flips the real part.
  rw [Complex.ext_iff]
  constructor
  · simp [sub_eq_add_neg, mul_add, mul_assoc]
    ring
  · simp [sub_eq_add_neg, mul_add, mul_assoc]

/-- Helper for Exercise 21: after substituting the principal-branch values of
`log (± a i)`, the two nonreal residue terms combine to a single real correction. -/
lemma exercise21_reciprocal_difference (a : ℝ) (ha : 0 < a) :
    1 / (((-(a * Real.pi) : ℝ) : ℂ) + ((2 * a * Real.log a : ℝ) : ℂ) * Complex.I) -
      1 / (((a * Real.pi : ℝ) : ℂ) + ((2 * a * Real.log a : ℝ) : ℂ) * Complex.I) =
        (-Real.pi / (2 * a * ((Real.log a) ^ 2 + Real.pi ^ 2 / 4)) : ℝ) := by
  -- Separate real and imaginary parts of the reciprocal difference; the imaginary part cancels.
  rw [Complex.ext_iff]
  constructor
  · simp [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.normSq, pow_two]
    field_simp [ha.ne', Real.pi_ne_zero]
    ring
  · simp [Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_im, Complex.normSq, pow_two]

/-- Helper for Exercise 21: the explicit residue sum in the contour identity simplifies to the
real quantity that appears in the final integral formula. -/
lemma exercise21_residue_sum_eval (a : ℝ) (ha : 0 < a) :
    1 / ((1 : ℂ) + (a : ℂ) ^ 2) +
      1 / ((2 * (a : ℂ) * Complex.I) * Complex.log ((a : ℂ) * Complex.I)) -
      1 / ((2 * (a : ℂ) * Complex.I) * Complex.log (-((a : ℂ) * Complex.I))) =
        (1 / (1 + a ^ 2) - Real.pi / (2 * a * ((Real.log a) ^ 2 + Real.pi ^ 2 / 4)) : ℝ) := by
  -- Substitute the principal-branch logarithms and rewrite the two reciprocal denominators.
  rw [exercise21_log_mul_I_of_pos a ha, exercise21_log_neg_mul_I_of_pos a ha]
  rw [exercise21_term2_rewrite, exercise21_term3_rewrite, exercise21_real_pole_term]
  have hrec := exercise21_reciprocal_difference a ha
  -- Regroup the sum so the reciprocal-difference helper applies directly.
  calc
    (1 / (1 + a ^ 2) : ℂ) +
        1 / (((-(a * Real.pi) : ℝ) : ℂ) + ((2 * a * Real.log a : ℝ) : ℂ) * Complex.I) -
        1 / (((a * Real.pi : ℝ) : ℂ) + ((2 * a * Real.log a : ℝ) : ℂ) * Complex.I) =
          (1 / (1 + a ^ 2) : ℂ) +
            (1 / (((-(a * Real.pi) : ℝ) : ℂ) + ((2 * a * Real.log a : ℝ) : ℂ) * Complex.I) -
              1 / (((a * Real.pi : ℝ) : ℂ) + ((2 * a * Real.log a : ℝ) : ℂ) * Complex.I)) := by
            simp [sub_eq_add_neg, add_assoc]
    _ = (1 / (1 + a ^ 2) : ℂ) +
          (-Real.pi / (2 * a * ((Real.log a) ^ 2 + Real.pi ^ 2 / 4)) : ℝ) := by
            exact congrArg (fun z : ℂ => (1 / (1 + a ^ 2) : ℂ) + z) hrec
    _ = (1 / (1 + a ^ 2) - Real.pi / (2 * a * ((Real.log a) ^ 2 + Real.pi ^ 2 / 4)) : ℝ) := by
          simp [sub_eq_add_neg]
          ring_nf

/-- Helper for Exercise 21: the three poles of the slit-plane contour integrand are `1` and
`± a i`. -/
abbrev exercise21PoleSet (a : ℝ) : Set ℂ :=
  ({(1 : ℂ), (a : ℂ) * Complex.I, -((a : ℂ) * Complex.I)} : Set ℂ)

/-- Helper for Exercise 21: the same finite pole set, packaged as a `Finset` for the residue
theorem. -/
abbrev exercise21PoleFinset (a : ℝ) : Finset ℂ :=
  {(1 : ℂ), (a : ℂ) * Complex.I, -((a : ℂ) * Complex.I)}

/-- Helper for Exercise 21: coercing the pole `Finset` back to a set recovers the textbook pole
set. -/
lemma exercise21PoleFinset_coe (a : ℝ) :
    (↑(exercise21PoleFinset a) : Set ℂ) = exercise21PoleSet a := by
  ext z
  simp [exercise21PoleFinset, exercise21PoleSet]

/-- Helper for Exercise 21: the residue coefficient of the real pole at `z = 1`. -/
abbrev exercise21RealPoleCoeff (a : ℝ) : ℂ :=
  1 / ((1 : ℂ) + (a : ℂ) ^ 2)

/-- Helper for Exercise 21: the residue coefficient of the pole at `z = a i`. -/
abbrev exercise21PosImagPoleCoeff (a : ℝ) : ℂ :=
  1 / ((2 * (a : ℂ) * Complex.I) * Complex.log ((a : ℂ) * Complex.I))

/-- Helper for Exercise 21: the residue coefficient of the pole at `z = -a i`. -/
abbrev exercise21NegImagPoleCoeff (a : ℝ) : ℂ :=
  -1 / ((2 * (a : ℂ) * Complex.I) * Complex.log (-((a : ℂ) * Complex.I)))

/-- Helper for Exercise 21: the residue function on the three poles `1`, `a i`, and `-a i`. -/
abbrev exercise21Residue (a : ℝ) (z : ℂ) : ℂ :=
  if z = (1 : ℂ) then exercise21RealPoleCoeff a
  else if z = (a : ℂ) * Complex.I then exercise21PosImagPoleCoeff a
  else exercise21NegImagPoleCoeff a

/-- Helper for Exercise 21: the raw integrand after subtracting the three principal-part kernels.
This keeps the source contour decomposition explicit while separating the remaining
removable-singularity work from the already solved residue algebra. -/
abbrev exercise21RegularPart (a : ℝ) (z : ℂ) : ℂ :=
  (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) -
    exercise21RealPoleCoeff a / (z - 1) -
      exercise21PosImagPoleCoeff a / (z - (a : ℂ) * Complex.I) -
        exercise21NegImagPoleCoeff a / (z + (a : ℂ) * Complex.I)

/-- Helper for Exercise 21: on `Complex.slitPlane`, the principal logarithm vanishes only at `1`.
This is the bridge from the slit-plane branch choice to the nonvanishing denominator needed for
the punctured holomorphy statements below. -/
lemma exercise21_log_ne_zero_of_mem_slitPlane_ne_one {z : ℂ}
    (hz_slit : z ∈ Complex.slitPlane) (hz1 : z ≠ (1 : ℂ)) :
    Complex.log z ≠ 0 := by
  -- Exponentiating `log z = 0` on the slit plane would force `z = 1`.
  intro hz_log
  have hz_exp : Complex.exp (Complex.log z) = z :=
    Complex.exp_log (Complex.slitPlane_ne_zero hz_slit)
  rw [hz_log, Complex.exp_zero] at hz_exp
  exact hz1 hz_exp.symm

/-- Helper for Exercise 21: once the two imaginary poles are excluded, the quadratic factor
`z^2 + a^2` is nonzero. -/
lemma exercise21_quadratic_ne_zero_of_off_imag_poles (a : ℝ) {z : ℂ}
    (hz_ai : z ≠ (a : ℂ) * Complex.I) (hz_neg_ai : z ≠ -((a : ℂ) * Complex.I)) :
    z ^ 2 + (a : ℂ) ^ 2 ≠ 0 := by
  -- Factor the quadratic as `(z - a i) (z + a i)` and use the excluded-pole hypotheses.
  intro hquad
  have hfactor : z ^ 2 + (a : ℂ) ^ 2 =
      (z - (a : ℂ) * Complex.I) * (z + (a : ℂ) * Complex.I) := by
    ring_nf
    simp [pow_two]
  rw [hfactor] at hquad
  rcases mul_eq_zero.mp hquad with hleft | hright
  · exact hz_ai (sub_eq_zero.mp hleft)
  · exact hz_neg_ai (eq_neg_iff_add_eq_zero.mpr hright)

/-- Helper for Exercise 21: `Complex.log` is holomorphic on the principal slit plane. -/
lemma exercise21_log_differentiableOn_slitPlane :
    DifferentiableOn ℂ Complex.log Complex.slitPlane := by
  -- This is the standard holomorphy statement for the principal branch.
  intro z hz
  simpa using (Complex.hasDerivAt_log hz).differentiableAt.differentiableWithinAt

/-- Helper for Exercise 21: the divided difference `dslope log 1` never vanishes on
`Complex.slitPlane`. -/
lemma exercise21_dslope_log_ne_zero_of_mem_slitPlane {z : ℂ}
    (hz : z ∈ Complex.slitPlane) :
    dslope Complex.log 1 z ≠ 0 := by
  -- Away from `1`, vanishing of the divided difference would force `log z = 0`; at `1`, the
  -- value is the derivative `log'(1) = 1`.
  by_cases hz1 : z = (1 : ℂ)
  · subst hz1
    have hderiv : deriv Complex.log (1 : ℂ) = 1 := by
      simpa using
        (Complex.hasDerivAt_log
          (by simp [Complex.mem_slitPlane_iff] : (1 : ℂ) ∈ Complex.slitPlane)).deriv
    simpa [dslope_same, hderiv]
  · intro hdslope
    have hlog_ne : Complex.log z ≠ 0 :=
      exercise21_log_ne_zero_of_mem_slitPlane_ne_one hz hz1
    have hlog_zero : Complex.log z = 0 := by
      rw [exercise21_log_eq_sub_one_mul_dslope, hdslope]
      simp
    exact hlog_ne hlog_zero

/-- Helper for Exercise 21: the contour integrand is holomorphic at every slit-plane point away
from the three poles `1`, `± a i`. -/
lemma exercise21_integrand_differentiableAt_of_mem_slitPlane_off_poles
    (a : ℝ) {z : ℂ} (hz_slit : z ∈ Complex.slitPlane) (hz_off : z ∉ exercise21PoleSet a) :
    DifferentiableAt ℂ (fun w ↦ (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹)) z := by
  -- Excluding the three poles makes each denominator factor nonzero, so the inverse is holomorphic.
  have hz1 : z ≠ (1 : ℂ) := by
    intro hz1
    exact hz_off (by simp [exercise21PoleSet, hz1])
  have hz_ai : z ≠ (a : ℂ) * Complex.I := by
    intro hz_ai
    exact hz_off (by simp [exercise21PoleSet, hz_ai])
  have hz_neg_ai : z ≠ -((a : ℂ) * Complex.I) := by
    intro hz_neg_ai
    exact hz_off (by simp [exercise21PoleSet, hz_neg_ai])
  have hlog_ne : Complex.log z ≠ 0 :=
    exercise21_log_ne_zero_of_mem_slitPlane_ne_one hz_slit hz1
  have hquad_ne : z ^ 2 + (a : ℂ) ^ 2 ≠ 0 :=
    exercise21_quadratic_ne_zero_of_off_imag_poles a hz_ai hz_neg_ai
  have hdenom_ne : ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z) ≠ 0 :=
    mul_ne_zero hquad_ne hlog_ne
  have hquad : DifferentiableAt ℂ (fun w : ℂ ↦ w ^ 2 + (a : ℂ) ^ 2) z := by
    fun_prop
  have hlog : DifferentiableAt ℂ Complex.log z := by
    simpa using (Complex.hasDerivAt_log hz_slit).differentiableAt
  -- The inverse of the nonvanishing denominator carries the final differentiability step.
  simpa using (hquad.mul hlog).inv hdenom_ne

/-- Helper for Exercise 21: the contour integrand is holomorphic on the slit plane once the three
actual poles are removed. -/
lemma exercise21_integrand_differentiableOn_slitPlane_off_poles
    (a : ℝ) :
    DifferentiableOn ℂ
      (fun z ↦ (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹))
      (Complex.slitPlane \ exercise21PoleSet a) := by
  -- Unpack the punctured-slit condition and reuse the pointwise differentiability bridge.
  intro z hz
  have hdiff :
      DifferentiableAt ℂ (fun w ↦ (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹)) z :=
    exercise21_integrand_differentiableAt_of_mem_slitPlane_off_poles a hz.1 hz.2
  exact hdiff.differentiableWithinAt

/-- Helper for Exercise 21: the punctured-slit holomorphy statement can be restated with the
`Finset` pole package used by the residue theorem. -/
lemma exercise21_integrand_differentiableOn_slitPlane_off_poles_finset
    (a : ℝ) :
    DifferentiableOn ℂ
      (fun z ↦ (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹))
      (Complex.slitPlane \ (↑(exercise21PoleFinset a) : Set ℂ)) := by
  -- This is just the set-level pole description rewritten through `exercise21PoleFinset`.
  simpa [exercise21PoleFinset_coe] using
    exercise21_integrand_differentiableOn_slitPlane_off_poles a

/-- Helper for Exercise 21: after subtracting the three residue kernels, the remaining raw term is
holomorphic on the punctured slit plane. Because Lean totalizes `inv 0 = 0`, extending this raw
expression across the poles is the separate remaining blocker rather than part of this lemma. -/
lemma exercise21_regularPart_differentiableOn_slitPlane_off_poles
    (a : ℝ) :
    DifferentiableOn ℂ (exercise21RegularPart a) (Complex.slitPlane \ exercise21PoleSet a) := by
  intro z hz
  have hz_slit : z ∈ Complex.slitPlane := hz.1
  have hz_off : z ∉ exercise21PoleSet a := hz.2
  have hz1 : z ≠ (1 : ℂ) := by
    intro hz1
    exact hz_off (by simp [exercise21PoleSet, hz1])
  have hz_ai : z ≠ (a : ℂ) * Complex.I := by
    intro hz_ai
    exact hz_off (by simp [exercise21PoleSet, hz_ai])
  have hz_neg_ai : z ≠ -((a : ℂ) * Complex.I) := by
    intro hz_neg_ai
    exact hz_off (by simp [exercise21PoleSet, hz_neg_ai])
  have hintegrand :
      DifferentiableAt ℂ (fun w ↦ (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹)) z :=
    exercise21_integrand_differentiableAt_of_mem_slitPlane_off_poles a hz_slit hz_off
  have hrealPole :
      DifferentiableAt ℂ
        (fun w ↦ exercise21RealPoleCoeff a / (w - 1)) z := by
    -- The real-pole term is a constant multiple of the holomorphic reciprocal kernel off `z = 1`.
    have hkernel : DifferentiableAt ℂ (fun w : ℂ ↦ (w - 1)⁻¹) z := by
      exact (differentiableAt_id.sub_const (1 : ℂ)).inv (sub_ne_zero.mpr hz1)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hkernel.const_mul (exercise21RealPoleCoeff a)
  have hposImagPole :
      DifferentiableAt ℂ
        (fun w ↦
          exercise21PosImagPoleCoeff a /
            (w - (a : ℂ) * Complex.I)) z := by
    -- The same reciprocal-kernel argument works at the pole `a i`.
    have hkernel : DifferentiableAt ℂ (fun w : ℂ ↦ (w - (a : ℂ) * Complex.I)⁻¹) z := by
      exact (differentiableAt_id.sub_const ((a : ℂ) * Complex.I)).inv (sub_ne_zero.mpr hz_ai)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hkernel.const_mul (exercise21PosImagPoleCoeff a)
  have hnegImagPole :
      DifferentiableAt ℂ
        (fun w ↦
          exercise21NegImagPoleCoeff a /
            (w + (a : ℂ) * Complex.I)) z := by
    -- Rewrite the denominator as `w - (-a i)` so the off-pole reciprocal lemma applies unchanged.
    have hkernel : DifferentiableAt ℂ (fun w : ℂ ↦ (w - (-((a : ℂ) * Complex.I)))⁻¹) z := by
      exact (differentiableAt_id.sub_const (-((a : ℂ) * Complex.I))).inv
        (sub_ne_zero.mpr hz_neg_ai)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hkernel.const_mul (exercise21NegImagPoleCoeff a)
  have hregular :
      DifferentiableAt ℂ (exercise21RegularPart a) z := by
    -- Combine the punctured holomorphy of the integrand with the three holomorphic kernel terms.
    have hsub1 :
        DifferentiableAt ℂ
          (fun w ↦
            (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹) -
              exercise21RealPoleCoeff a / (w - 1)) z :=
      hintegrand.sub hrealPole
    have hsub2 :
        DifferentiableAt ℂ
          (fun w ↦
            (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹) -
              exercise21RealPoleCoeff a / (w - 1) -
                exercise21PosImagPoleCoeff a / (w - (a : ℂ) * Complex.I)) z :=
      hsub1.sub hposImagPole
    have hsub3 :
        DifferentiableAt ℂ (exercise21RegularPart a) z := by
      change DifferentiableAt ℂ
        (fun w ↦
          (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹) -
            exercise21RealPoleCoeff a / (w - 1) -
              exercise21PosImagPoleCoeff a / (w - (a : ℂ) * Complex.I) -
                exercise21NegImagPoleCoeff a / (w + (a : ℂ) * Complex.I)) z
      exact hsub2.sub hnegImagPole
    exact hsub3
  exact hregular.differentiableWithinAt

/-- Helper for Exercise 21: a sufficiently small circle around `1` realizes the residue
coefficient `1 / (1 + a^2)` while staying away from the imaginary poles. -/
lemma exercise21_real_pole_localResidueCircle
    {K : Set ℂ} {ρ : ℝ} (a : ℝ)
    (hρ : 0 < ρ)
    (hK : Metric.closedBall (1 : ℂ) ρ ⊆ interior K)
    (hD :
      Metric.closedBall (1 : ℂ) ρ ⊆
        Complex.slitPlane \ ({(a : ℂ) * Complex.I, -((a : ℂ) * Complex.I)} : Set ℂ)) :
    LocalResidueCircle
      K
      Complex.slitPlane
      (fun z ↦ (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹))
      (1 : ℂ)
      (exercise21RealPoleCoeff a) := by
  let D : Set ℂ := Complex.slitPlane \ ({(a : ℂ) * Complex.I, -((a : ℂ) * Complex.I)} : Set ℂ)
  let g : ℂ → ℂ := fun z ↦ (((z ^ 2 + (a : ℂ) ^ 2) * dslope Complex.log 1 z)⁻¹)
  have hdslope :
      DifferentiableOn ℂ (dslope Complex.log 1) Complex.slitPlane := by
    -- The removable singularity theorem turns the principal logarithm into a holomorphic divided
    -- difference on the whole slit plane.
    exact
      (Complex.differentiableOn_dslope
        ((Complex.isOpen_slitPlane.mem_nhds
          (by simp [Complex.mem_slitPlane_iff] : (1 : ℂ) ∈ Complex.slitPlane)))).2
        exercise21_log_differentiableOn_slitPlane
  have hg : DifferentiableOn ℂ g D := by
    intro z hz
    have hz_slit : z ∈ Complex.slitPlane := hz.1
    have hz_ai : z ≠ (a : ℂ) * Complex.I := by
      intro h
      exact hz.2 (by simp [h])
    have hz_neg_ai : z ≠ -((a : ℂ) * Complex.I) := by
      intro h
      exact hz.2 (by simp [h])
    have hquad_ne : z ^ 2 + (a : ℂ) ^ 2 ≠ 0 :=
      exercise21_quadratic_ne_zero_of_off_imag_poles a hz_ai hz_neg_ai
    have hdslope_ne : dslope Complex.log 1 z ≠ 0 :=
      exercise21_dslope_log_ne_zero_of_mem_slitPlane hz_slit
    have hdenom_ne : ((z ^ 2 + (a : ℂ) ^ 2) * dslope Complex.log 1 z) ≠ 0 :=
      mul_ne_zero hquad_ne hdslope_ne
    have hquad : DifferentiableAt ℂ (fun w : ℂ ↦ w ^ 2 + (a : ℂ) ^ 2) z := by
      fun_prop
    have hdiff :
        DifferentiableAt ℂ (dslope Complex.log 1) z := by
      exact (hdslope z hz_slit).differentiableAt (Complex.isOpen_slitPlane.mem_nhds hz_slit)
    -- The reciprocal is holomorphic because both factors stay nonzero on the punctured domain.
    simpa [g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      ((hquad.mul hdiff).inv hdenom_ne).differentiableWithinAt
  have hlocal :
      LocalResidueCircle K D (fun z ↦ g z / (z - (1 : ℂ))) (1 : ℂ) (g 1) :=
    localResidueCircle_div_sub_of_differentiableOn
      (K := K) (D := D) (g := g) (a := (1 : ℂ)) (r := ρ) hρ hK hD hg
  rcases hlocal with ⟨radius, hradius, hballK, hballD, hcircle⟩
  refine ⟨radius, hradius, hballK, ?_, ?_⟩
  · intro z hz
    exact (hballD hz).1
  · have hcongr :
        (∮ z in C((1 : ℂ), radius), (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹)) =
          ∮ z in C((1 : ℂ), radius), g z / (z - (1 : ℂ)) := by
      -- On the whole small circle, the original integrand is already in the standard `/(z-1)`
      -- kernel form.
      refine circleIntegral.integral_congr hradius.le ?_
      intro z hz
      simpa [g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        exercise21_integrand_eq_real_pole_kernel a (z := z)
    have hg_one : g 1 = exercise21RealPoleCoeff a := by
      -- Evaluating the divided difference at the center reduces to `log'(1) = 1`.
      have hderiv : deriv Complex.log (1 : ℂ) = 1 := by
        simpa using
          (Complex.hasDerivAt_log
            (by simp [Complex.mem_slitPlane_iff] : (1 : ℂ) ∈ Complex.slitPlane)).deriv
      simp [g, exercise21RealPoleCoeff, dslope_same, hderiv]
    rw [hcongr, hcircle, hg_one]

/-- Helper for Exercise 21: a sufficiently small circle around `a i` realizes the positive
imaginary residue while staying away from the other two poles. -/
lemma exercise21_pos_imag_pole_localResidueCircle
    {K : Set ℂ} {ρ : ℝ} (a : ℝ)
    (hρ : 0 < ρ)
    (hK : Metric.closedBall ((a : ℂ) * Complex.I) ρ ⊆ interior K)
    (hD :
      Metric.closedBall ((a : ℂ) * Complex.I) ρ ⊆
        Complex.slitPlane \ ({(1 : ℂ), -((a : ℂ) * Complex.I)} : Set ℂ)) :
    LocalResidueCircle
      K
      Complex.slitPlane
      (fun z ↦ (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹))
      ((a : ℂ) * Complex.I)
      (exercise21PosImagPoleCoeff a) := by
  let D : Set ℂ := Complex.slitPlane \ ({(1 : ℂ), -((a : ℂ) * Complex.I)} : Set ℂ)
  let g : ℂ → ℂ := fun z ↦ ((((z + (a : ℂ) * Complex.I) * Complex.log z)⁻¹))
  have hg : DifferentiableOn ℂ g D := by
    intro z hz
    have hz_slit : z ∈ Complex.slitPlane := hz.1
    have hz_one : z ≠ (1 : ℂ) := by
      intro h
      exact hz.2 (by simp [h])
    have hz_neg_ai : z ≠ -((a : ℂ) * Complex.I) := by
      intro h
      exact hz.2 (by simp [h])
    have hlog_ne : Complex.log z ≠ 0 :=
      exercise21_log_ne_zero_of_mem_slitPlane_ne_one hz_slit hz_one
    have hfactor_ne : z + (a : ℂ) * Complex.I ≠ 0 := by
      simpa [eq_neg_iff_add_eq_zero] using hz_neg_ai
    have hdenom_ne : ((z + (a : ℂ) * Complex.I) * Complex.log z) ≠ 0 :=
      mul_ne_zero hfactor_ne hlog_ne
    have hfactor : DifferentiableAt ℂ (fun w : ℂ ↦ w + (a : ℂ) * Complex.I) z := by
      fun_prop
    have hlog : DifferentiableAt ℂ Complex.log z := by
      simpa using (Complex.hasDerivAt_log hz_slit).differentiableAt
    -- The pole factor `z - a i` has been split off, leaving a holomorphic coefficient.
    simpa [g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      ((hfactor.mul hlog).inv hdenom_ne).differentiableWithinAt
  have hlocal :
      LocalResidueCircle
        K D (fun z ↦ g z / (z - (a : ℂ) * Complex.I))
        ((a : ℂ) * Complex.I) (g ((a : ℂ) * Complex.I)) :=
    localResidueCircle_div_sub_of_differentiableOn
      (K := K) (D := D) (g := g) (a := (a : ℂ) * Complex.I) (r := ρ) hρ hK hD hg
  rcases hlocal with ⟨radius, hradius, hballK, hballD, hcircle⟩
  refine ⟨radius, hradius, hballK, ?_, ?_⟩
  · intro z hz
    exact (hballD hz).1
  · have hcongr :
        (∮ z in C((a : ℂ) * Complex.I, radius),
            (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹)) =
          ∮ z in C((a : ℂ) * Complex.I, radius), g z / (z - (a : ℂ) * Complex.I) := by
      -- On the punctured circle, the original integrand is the simple-pole kernel at `a i`.
      refine circleIntegral.integral_congr hradius.le ?_
      intro z hz
      have hz_ne : z ≠ (a : ℂ) * Complex.I := by
        intro h
        have : (0 : ℝ) = radius := by
          simpa [Metric.mem_sphere, Complex.dist_eq, h] using hz
        exact hradius.ne' this.symm
      simpa [g] using exercise21_integrand_eq_pos_imag_pole_kernel a hz_ne
    have hg_ai : g ((a : ℂ) * Complex.I) = exercise21PosImagPoleCoeff a := by
      -- Evaluating the holomorphic coefficient at the pole gives the stated residue.
      have htwo :
          (a : ℂ) * Complex.I + (a : ℂ) * Complex.I = 2 * (a : ℂ) * Complex.I := by
        ring
      simpa [g, exercise21PosImagPoleCoeff, div_eq_mul_inv, htwo]
    rw [hcongr, hcircle, hg_ai]

/-- Helper for Exercise 21: a sufficiently small circle around `-a i` realizes the negative
imaginary residue while staying away from the other two poles. -/
lemma exercise21_neg_imag_pole_localResidueCircle
    {K : Set ℂ} {ρ : ℝ} (a : ℝ)
    (hρ : 0 < ρ)
    (hK : Metric.closedBall (-((a : ℂ) * Complex.I)) ρ ⊆ interior K)
    (hD :
      Metric.closedBall (-((a : ℂ) * Complex.I)) ρ ⊆
        Complex.slitPlane \ ({(1 : ℂ), (a : ℂ) * Complex.I} : Set ℂ)) :
    LocalResidueCircle
      K
      Complex.slitPlane
      (fun z ↦ (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹))
      (-((a : ℂ) * Complex.I))
      (exercise21NegImagPoleCoeff a) := by
  let D : Set ℂ := Complex.slitPlane \ ({(1 : ℂ), (a : ℂ) * Complex.I} : Set ℂ)
  let g : ℂ → ℂ := fun z ↦ ((((z - (a : ℂ) * Complex.I) * Complex.log z)⁻¹))
  have hg : DifferentiableOn ℂ g D := by
    intro z hz
    have hz_slit : z ∈ Complex.slitPlane := hz.1
    have hz_one : z ≠ (1 : ℂ) := by
      intro h
      exact hz.2 (by simp [h])
    have hz_ai : z ≠ (a : ℂ) * Complex.I := by
      intro h
      exact hz.2 (by simp [h])
    have hlog_ne : Complex.log z ≠ 0 :=
      exercise21_log_ne_zero_of_mem_slitPlane_ne_one hz_slit hz_one
    have hfactor_ne : z - (a : ℂ) * Complex.I ≠ 0 := sub_ne_zero.mpr hz_ai
    have hdenom_ne : ((z - (a : ℂ) * Complex.I) * Complex.log z) ≠ 0 :=
      mul_ne_zero hfactor_ne hlog_ne
    have hfactor : DifferentiableAt ℂ (fun w : ℂ ↦ w - (a : ℂ) * Complex.I) z := by
      fun_prop
    have hlog : DifferentiableAt ℂ Complex.log z := by
      simpa using (Complex.hasDerivAt_log hz_slit).differentiableAt
    -- After factoring out `z + a i`, only a holomorphic coefficient remains.
    simpa [g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      ((hfactor.mul hlog).inv hdenom_ne).differentiableWithinAt
  have hlocal :
      LocalResidueCircle
        K D (fun z ↦ g z / (z + (a : ℂ) * Complex.I))
        (-((a : ℂ) * Complex.I)) (g (-((a : ℂ) * Complex.I))) :=
    by
      simpa [sub_eq_add_neg] using
        (localResidueCircle_div_sub_of_differentiableOn
          (K := K) (D := D) (g := g) (a := -((a : ℂ) * Complex.I)) (r := ρ) hρ hK hD hg)
  rcases hlocal with ⟨radius, hradius, hballK, hballD, hcircle⟩
  refine ⟨radius, hradius, hballK, ?_, ?_⟩
  · intro z hz
    exact (hballD hz).1
  · have hcongr :
        (∮ z in C(-((a : ℂ) * Complex.I), radius),
            (((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹)) =
          ∮ z in C(-((a : ℂ) * Complex.I), radius), g z / (z + (a : ℂ) * Complex.I) := by
      -- On the punctured circle, the original integrand is the simple-pole kernel at `-a i`.
      refine circleIntegral.integral_congr hradius.le ?_
      intro z hz
      have hz_ne : z ≠ -((a : ℂ) * Complex.I) := by
        intro h
        have : (0 : ℝ) = radius := by
          simpa [Metric.mem_sphere, Complex.dist_eq, h] using hz
        exact hradius.ne' this.symm
      simpa [g] using exercise21_integrand_eq_neg_imag_pole_kernel a hz_ne
    have hg_neg_ai : g (-((a : ℂ) * Complex.I)) = exercise21NegImagPoleCoeff a := by
      -- The remaining coefficient evaluates to the stated negative residue.
      have htwo :
          -((a : ℂ) * Complex.I) - (a : ℂ) * Complex.I = -(2 * (a : ℂ) * Complex.I) := by
        ring
      simpa [g, exercise21NegImagPoleCoeff, div_eq_mul_inv, htwo, inv_neg]
    rw [hcongr, hcircle, hg_neg_ai]

/-- Helper for Exercise 21: once three small residue circles are chosen around `1`, `a i`, and
`-a i`, the residue theorem hypotheses at all poles can be bundled uniformly. -/
lemma exercise21_localResidueCircle_data
    {K : Set ℂ} (a : ℝ) (ha : 0 < a) {ρ₁ ρ₂ ρ₃ : ℝ}
    (hρ₁ : 0 < ρ₁)
    (hK₁ : Metric.closedBall (1 : ℂ) ρ₁ ⊆ interior K)
    (hD₁ :
      Metric.closedBall (1 : ℂ) ρ₁ ⊆
        Complex.slitPlane \ ({(a : ℂ) * Complex.I, -((a : ℂ) * Complex.I)} : Set ℂ))
    (hρ₂ : 0 < ρ₂)
    (hK₂ : Metric.closedBall ((a : ℂ) * Complex.I) ρ₂ ⊆ interior K)
    (hD₂ :
      Metric.closedBall ((a : ℂ) * Complex.I) ρ₂ ⊆
        Complex.slitPlane \ ({(1 : ℂ), -((a : ℂ) * Complex.I)} : Set ℂ))
    (hρ₃ : 0 < ρ₃)
    (hK₃ : Metric.closedBall (-((a : ℂ) * Complex.I)) ρ₃ ⊆ interior K)
    (hD₃ :
      Metric.closedBall (-((a : ℂ) * Complex.I)) ρ₃ ⊆
        Complex.slitPlane \ ({(1 : ℂ), (a : ℂ) * Complex.I} : Set ℂ)) :
    ∀ z ∈ exercise21PoleFinset a,
      LocalResidueCircle
        K
        Complex.slitPlane
        (fun w ↦ (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹))
        z
        (exercise21Residue a z) := by
  have h_ai_ne_one : (a : ℂ) * Complex.I ≠ (1 : ℂ) := by
    intro h
    have him := congrArg Complex.im h
    simpa [ha.ne'] using him
  have h_neg_ai_ne_one : -((a : ℂ) * Complex.I) ≠ (1 : ℂ) := by
    intro h
    have him := congrArg Complex.im h
    simpa [ha.ne'] using him
  have h_ai_ne_neg_ai : (a : ℂ) * Complex.I ≠ -((a : ℂ) * Complex.I) := by
    intro h
    have him := congrArg Complex.im h
    have : a = -a := by simpa using him
    linarith
  have h_neg_ai_ne_ai : -((a : ℂ) * Complex.I) ≠ (a : ℂ) * Complex.I := by
    intro h
    exact h_ai_ne_neg_ai h.symm
  intro z hz
  -- The pole set is exactly the three simple poles handled above.
  simp [exercise21PoleFinset] at hz
  rcases hz with rfl | rfl | rfl
  · simpa [exercise21Residue, h_ai_ne_one, h_neg_ai_ne_one] using
      exercise21_real_pole_localResidueCircle (K := K) (ρ := ρ₁) a hρ₁ hK₁ hD₁
  · simpa [exercise21Residue, h_ai_ne_one, h_ai_ne_neg_ai] using
      exercise21_pos_imag_pole_localResidueCircle (K := K) (ρ := ρ₂) a hρ₂ hK₂ hD₂
  · simpa [exercise21Residue, h_neg_ai_ne_one, h_neg_ai_ne_ai] using
      exercise21_neg_imag_pole_localResidueCircle (K := K) (ρ := ρ₃) a hρ₃ hK₃ hD₃

/-- Helper for Exercise 21: the slit around the negative real axis that separates the two
boundary values of the principal logarithm. -/
abbrev exercise21NegativeWedge (r ε : ℝ) : Set ℂ :=
  {z : ℂ | z.re < 0 ∧ |z.im| < (ε / r) * (-z.re)}

/-- Helper for Exercise 21: the compact slit annulus bounded by the keyhole contour `δ(r, ε)`. -/
abbrev exercise21NegativeWedgeAnnulus (r ε : ℝ) : Set ℂ :=
  {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} \ exercise21NegativeWedge r ε

/-- Helper for Exercise 21: the explicit slit annulus lies in `Complex.slitPlane`. -/
lemma exercise21NegativeWedgeAnnulus_subset_slitPlane
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    exercise21NegativeWedgeAnnulus r ε ⊆ Complex.slitPlane := by
  intro z hz
  have hr : 0 < r := lt_trans hε hεr
  have hnorm_pos : 0 < ‖z‖ := lt_of_lt_of_le hε hz.1.1
  by_cases him : z.im = 0
  · have hre_nonneg : 0 ≤ z.re := by
      by_contra hre_neg
      have hwedge : z ∈ exercise21NegativeWedge r ε := by
        constructor
        · exact lt_of_not_ge hre_neg
        · rw [him, abs_zero]
          have hratio_pos : 0 < ε / r := div_pos hε hr
          have hre_pos : 0 < -z.re := by
            linarith
          have : 0 < (ε / r) * (-z.re) := mul_pos hratio_pos hre_pos
          simpa using this
      exact hz.2 hwedge
    rw [Complex.mem_slitPlane_iff]
    left
    have hz_ne : z ≠ 0 := by
      intro hz0
      simpa [hz0] using hnorm_pos.ne'
    have hre_ne : z.re ≠ 0 := by
      intro hre_zero
      apply hz_ne
      apply Complex.ext <;> simp [hre_zero, him]
    exact lt_of_le_of_ne hre_nonneg (Ne.symm hre_ne)
  · rw [Complex.mem_slitPlane_iff]
    exact Or.inr him

/-- Helper for Exercise 21: the removed negative wedge is open because it is cut out by two strict
inequalities in the real and imaginary coordinates. -/
lemma isOpen_exercise21NegativeWedge (r ε : ℝ) :
    IsOpen (exercise21NegativeWedge r ε) := by
  have hre : IsOpen {z : ℂ | z.re < 0} :=
    isOpen_lt continuous_re continuous_const
  have him :
      IsOpen {z : ℂ | |z.im| < (ε / r) * (-z.re)} := by
    simpa using
      isOpen_lt (continuous_abs.comp continuous_im) (continuous_const.mul continuous_re.neg)
  -- The slit wedge is exactly the intersection of those two open half-space conditions.
  simpa [exercise21NegativeWedge, Set.setOf_and] using hre.inter him

/-- Helper for Exercise 21: the radial constraints alone define a closed annulus. -/
lemma isClosed_exercise21ClosedAnnulus (r ε : ℝ) :
    IsClosed {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} := by
  -- Both radius inequalities are closed conditions, so their intersection is closed as well.
  simpa [Set.setOf_and] using
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)

lemma isClosed_exercise21NegativeWedgeAnnulus (r ε : ℝ) :
    IsClosed (exercise21NegativeWedgeAnnulus r ε) := by
  -- Rewrite the set difference as an intersection with the wedge complement.
  simpa [exercise21NegativeWedgeAnnulus, Set.diff_eq, Set.setOf_and] using
    (isClosed_exercise21ClosedAnnulus r ε).inter
      (isOpen_exercise21NegativeWedge r ε).isClosed_compl

/-- Helper for Exercise 21: every point of the slit annulus has norm at most `r`, so the whole
region lies in the closed ball centered at `0` with radius `r`. -/
lemma exercise21NegativeWedgeAnnulus_subset_closedBall (r ε : ℝ) :
    exercise21NegativeWedgeAnnulus r ε ⊆ Metric.closedBall (0 : ℂ) r := by
  intro z hz
  -- The outer annulus inequality is exactly the closed-ball bound.
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact hz.1.2

/-- Helper for Exercise 21: the slit annulus is compact as a closed subset of the closed ball of
radius `r`. -/
lemma isCompact_exercise21NegativeWedgeAnnulus (r ε : ℝ) :
    IsCompact (exercise21NegativeWedgeAnnulus r ε) := by
  -- The closed-ball owner keeps the compactness proof independent of the slit geometry details.
  refine (isCompact_closedBall (0 : ℂ) r).of_isClosed_subset
    (isClosed_exercise21NegativeWedgeAnnulus r ε) ?_
  exact exercise21NegativeWedgeAnnulus_subset_closedBall r ε

/-- Helper for Exercise 21: the closed annulus owner has frontier exactly the inner and outer
boundary circles. This isolates the radial part of the slit-annulus frontier before the wedge
geometry is reintroduced. -/
lemma exercise21ClosedAnnulus_frontier_eq
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    frontier {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} =
      Metric.sphere (0 : ℂ) r ∪ Metric.sphere (0 : ℂ) ε := by
  have hannulus :
      {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} =
        Metric.closedBall (0 : ℂ) r \ Metric.ball (0 : ℂ) ε := by
    ext z
    -- The annulus is the outer closed ball with the inner open ball removed.
    simp [Metric.mem_closedBall, Metric.mem_ball, dist_eq_norm, sub_zero, not_lt, and_comm]
  rw [hannulus]
  rw [frontier_diff_open_of_isClosed Metric.isClosed_closedBall Metric.isOpen_ball]
  rw [frontier_closedBall', frontier_ball (0 : ℂ) hε.ne']
  have hsphere_outer :
      Metric.sphere (0 : ℂ) r \ Metric.ball (0 : ℂ) ε = Metric.sphere (0 : ℂ) r := by
    ext z
    constructor
    · intro hz
      exact hz.1
    · intro hz
      refine ⟨hz, ?_⟩
      intro hzball
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hzball
      linarith
  have hsphere_inner :
      Metric.closedBall (0 : ℂ) r ∩ Metric.sphere (0 : ℂ) ε = Metric.sphere (0 : ℂ) ε := by
    ext z
    constructor
    · intro hz
      exact hz.2
    · intro hz
      refine ⟨?_, hz⟩
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      linarith
  -- The surviving pieces are exactly the outer and inner boundary circles.
  rw [hsphere_outer, hsphere_inner]

lemma exercise21_upper_lip_range_eq_geometric
    (r ε : ℝ) :
    Set.range
        (Path.segment
          (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
          (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))) =
      (fun ρ : ℝ ↦ circleMap 0 ρ (Real.pi - Real.arctan (ε / r))) '' Set.uIcc r ε := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨AffineMap.lineMap r ε (t : ℝ), ?_, ?_⟩
    · simpa [segment_eq_uIcc] using lineMap_mem_segment ℝ r ε t.2
    · -- The upper radial segment only changes the radius.
      simpa [Path.segment_apply] using
        (exercise21_lineMap_circleMap_same_angle
          r ε (Real.pi - Real.arctan (ε / r)) (t : ℝ)).symm
  · rintro ⟨ρ, hρ, rfl⟩
    have hseg : ρ ∈ segment ℝ r ε := by
      simpa [segment_eq_uIcc] using hρ
    rw [segment_eq_image_lineMap] at hseg
    rcases hseg with ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    -- Repackage the geometric radius parameter back into the segment path parameter.
    simpa [Path.segment_apply] using
      exercise21_lineMap_circleMap_same_angle
        r ε (Real.pi - Real.arctan (ε / r)) t

lemma exercise21_inner_arc_range_eq_geometric
    (r ε : ℝ) :
    Set.range
        (((Path.segment (Real.pi - Real.arctan (ε / r))
            (-Real.pi + Real.arctan (ε / r))).map (continuous_circleMap 0 ε))) =
      (fun φ : ℝ ↦ circleMap 0 ε φ) ''
        Set.uIcc (Real.pi - Real.arctan (ε / r)) (-Real.pi + Real.arctan (ε / r)) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨AffineMap.lineMap
        (Real.pi - Real.arctan (ε / r))
        (-Real.pi + Real.arctan (ε / r))
        (t : ℝ), ?_, ?_⟩
    · simpa [segment_eq_uIcc] using
        lineMap_mem_segment ℝ
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r))
          t.2
    · -- The mapped angular segment is exactly the circle image of the affine angle parameter.
      simp [Path.map_coe, Function.comp_apply, Path.segment_apply]
  · rintro ⟨φ, hφ, rfl⟩
    have hseg :
        φ ∈ segment ℝ
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r)) := by
      simpa [segment_eq_uIcc] using hφ
    rw [segment_eq_image_lineMap] at hseg
    rcases hseg with ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    -- Repackage the angle parameter through the mapped path.
    simp [Path.map_coe, Function.comp_apply, Path.segment_apply]

lemma exercise21_lower_lip_range_eq_geometric
    (r ε : ℝ) :
    Set.range
        (Path.segment
          (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
          (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))) =
      (fun ρ : ℝ ↦ circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))) '' Set.uIcc ε r := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨AffineMap.lineMap ε r (t : ℝ), ?_, ?_⟩
    · simpa [segment_eq_uIcc] using lineMap_mem_segment ℝ ε r t.2
    · -- The lower radial segment likewise only changes the radius.
      simpa [Path.segment_apply] using
        (exercise21_lineMap_circleMap_same_angle
          ε r (-Real.pi + Real.arctan (ε / r)) (t : ℝ)).symm
  · rintro ⟨ρ, hρ, rfl⟩
    have hseg : ρ ∈ segment ℝ ε r := by
      simpa [segment_eq_uIcc] using hρ
    rw [segment_eq_image_lineMap] at hseg
    rcases hseg with ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    -- Repackage the lower-lip radius parameter back into the segment path parameter.
    simpa [Path.segment_apply] using
      exercise21_lineMap_circleMap_same_angle
        ε r (-Real.pi + Real.arctan (ε / r)) t

lemma exercise21_outer_arc_range_eq_geometric
    (r ε : ℝ) :
    Set.range
        (((Path.segment (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r))).map (continuous_circleMap 0 r))) =
      (fun φ : ℝ ↦ circleMap 0 r φ) ''
        Set.uIcc (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨AffineMap.lineMap
        (-Real.pi + Real.arctan (ε / r))
        (Real.pi - Real.arctan (ε / r))
        (t : ℝ), ?_, ?_⟩
    · simpa [segment_eq_uIcc] using
        lineMap_mem_segment ℝ
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r))
          t.2
    · -- The outer arc is the circle image of the affine angle segment.
      simp [Path.map_coe, Function.comp_apply, Path.segment_apply]
  · rintro ⟨φ, hφ, rfl⟩
    have hseg :
        φ ∈ segment ℝ
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r)) := by
      simpa [segment_eq_uIcc] using hφ
    rw [segment_eq_image_lineMap] at hseg
    rcases hseg with ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    -- Repackage the angle parameter through the mapped outer path.
    simp [Path.map_coe, Function.comp_apply, Path.segment_apply]

theorem exercise21Delta_range_eq_geometric_piece_union
    (r ε : ℝ) :
    Set.range (exercise21Delta r ε) =
      (fun ρ : ℝ ↦ circleMap 0 ρ (Real.pi - Real.arctan (ε / r))) '' Set.uIcc r ε ∪
        (fun φ : ℝ ↦ circleMap 0 ε φ) ''
          Set.uIcc (Real.pi - Real.arctan (ε / r)) (-Real.pi + Real.arctan (ε / r)) ∪
        (fun ρ : ℝ ↦ circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))) '' Set.uIcc ε r ∪
        (fun φ : ℝ ↦ circleMap 0 r φ) ''
          Set.uIcc (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)) := by
  -- Rewrite the four canonical path-piece ranges into their geometric radius/angle images.
  rw [exercise21Delta_range_eq_four_piece_union]
  dsimp
  -- Rewrite each of the four canonical pieces through its geometric radius/angle image.
  rw [exercise21_upper_lip_range_eq_geometric, exercise21_inner_arc_range_eq_geometric,
    exercise21_lower_lip_range_eq_geometric, exercise21_outer_arc_range_eq_geometric]

lemma exercise21NegativeWedge_upper_lip_mem_frontier
    (r ε ρ : ℝ) (hε : 0 < ε) (hεr : ε < r) (hρ : 0 < ρ) :
    circleMap 0 ρ (Real.pi - Real.arctan (ε / r)) ∈ frontier (exercise21NegativeWedge r ε) := by
  let z : ℂ := circleMap 0 ρ (Real.pi - Real.arctan (ε / r))
  have hr : 0 < r := lt_trans hε hεr
  have hratio_pos : 0 < ε / r := div_pos hε hr
  have hre_neg : z.re < 0 := by
    -- The upper lip lies on the negative-real side of the slit.
    simpa [z] using exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := ρ) hρ
  have hline : z.im = -((ε / r) * z.re) := by
    -- The upper lip is exactly the upper boundary line of the wedge.
    simpa [z] using exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := ρ)
  have him_pos : 0 < z.im := by
    have hneg_re_pos : 0 < -z.re := by linarith
    rw [hline]
    nlinarith
  have habs : |z.im| = (ε / r) * (-z.re) := by
    -- On the upper lip the imaginary part is positive, so the absolute value drops.
    rw [abs_of_pos him_pos, hline]
    ring
  have hz_not_mem : z ∉ exercise21NegativeWedge r ε := by
    -- The lip point satisfies the wedge inequality with equality, not strictly.
    intro hz
    have : |z.im| < (ε / r) * (-z.re) := hz.2
    rw [habs] at this
    exact lt_irrefl _ this
  have hz_closure : z ∈ closure (exercise21NegativeWedge r ε) := by
    -- Moving a tiny distance straight downward enters the open wedge.
    refine Metric.mem_closure_iff.2 ?_
    intro δ hδ
    let η : ℝ := min (δ / 2) (z.im / 2)
    have hη_pos : 0 < η := by
      refine lt_min ?_ ?_
      · linarith
      · linarith
    have hη_lt_im : η < z.im := by
      have hhalf_lt : z.im / 2 < z.im := by linarith
      exact lt_of_le_of_lt (min_le_right _ _) hhalf_lt
    let w : ℂ := z - (η : ℂ) * Complex.I
    refine ⟨w, ?_, ?_⟩
    · -- The perturbed point still has negative real part and now satisfies the wedge inequality
      -- strictly.
      refine ⟨?_, ?_⟩
      · simpa [w] using hre_neg
      · have hw_im : w.im = z.im - η := by
          simp [w]
        have hw_im_pos : 0 < w.im := by
          rw [hw_im]
          linarith
        calc
          |w.im| = z.im - η := by simpa [hw_im] using (abs_of_pos hw_im_pos)
          _ < z.im := by linarith
          _ = (ε / r) * (-z.re) := by
                rw [hline]
                ring
          _ = (ε / r) * (-w.re) := by simp [w]
    · -- The perturbation size is exactly `η`, so the point can be chosen inside any ball.
      have hη_lt_δ : η < δ := by
        have hη_le : η ≤ δ / 2 := min_le_left _ _
        linarith
      rw [dist_eq_norm]
      have hsub : z - w = (η : ℂ) * Complex.I := by
        simp [w]
      rw [hsub, norm_mul, Complex.norm_I, mul_one]
      simpa [Complex.norm_real, abs_of_nonneg hη_pos.le] using hη_lt_δ
  -- Combine the closure witness with the fact that boundary points of an open set lie outside it.
  rw [frontier_eq_closure_inter_closure]
  refine ⟨hz_closure, ?_⟩
  rw [closure_compl]
  exact fun hz_int ↦ hz_not_mem (interior_subset hz_int)

/-- Helper for Exercise 21: every point on the lower slit lip is also a boundary point of the
removed negative wedge, because moving slightly upward enters the wedge while the boundary value
itself again occurs with equality. -/
lemma exercise21NegativeWedge_lower_lip_mem_frontier
    (r ε ρ : ℝ) (hε : 0 < ε) (hεr : ε < r) (hρ : 0 < ρ) :
    circleMap 0 ρ (-Real.pi + Real.arctan (ε / r)) ∈ frontier (exercise21NegativeWedge r ε) := by
  let z : ℂ := circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))
  have hr : 0 < r := lt_trans hε hεr
  have hratio_pos : 0 < ε / r := div_pos hε hr
  have hre_neg : z.re < 0 := by
    -- The lower lip lies on the same negative-real side of the slit.
    simpa [z] using exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := ρ) hρ
  have hline : z.im = (ε / r) * z.re := by
    -- The lower lip is the lower boundary line of the wedge.
    simpa [z] using exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := ρ)
  have him_neg : z.im < 0 := by
    have hneg_re_pos : 0 < -z.re := by linarith
    rw [hline]
    nlinarith
  have habs : |z.im| = (ε / r) * (-z.re) := by
    -- On the lower lip the imaginary part is negative, so the absolute value contributes a minus.
    rw [abs_of_neg him_neg, hline]
    ring
  have hz_not_mem : z ∉ exercise21NegativeWedge r ε := by
    -- The lower lip also satisfies the wedge inequality only with equality.
    intro hz
    have : |z.im| < (ε / r) * (-z.re) := hz.2
    rw [habs] at this
    exact lt_irrefl _ this
  have hz_closure : z ∈ closure (exercise21NegativeWedge r ε) := by
    -- Moving a tiny distance straight upward enters the open wedge.
    refine Metric.mem_closure_iff.2 ?_
    intro δ hδ
    let η : ℝ := min (δ / 2) ((-z.im) / 2)
    have hη_pos : 0 < η := by
      refine lt_min ?_ ?_
      · linarith
      · linarith
    have hη_lt_neg_im : η < -z.im := by
      have hhalf_lt : (-z.im) / 2 < -z.im := by linarith
      exact lt_of_le_of_lt (min_le_right _ _) hhalf_lt
    let w : ℂ := z + (η : ℂ) * Complex.I
    refine ⟨w, ?_, ?_⟩
    · -- The perturbed point still has negative real part and now satisfies the wedge inequality
      -- strictly.
      refine ⟨?_, ?_⟩
      · simpa [w] using hre_neg
      · have hw_im : w.im = z.im + η := by
          simp [w]
        have hw_im_neg : w.im < 0 := by
          rw [hw_im]
          linarith
        calc
          |w.im| = -(z.im + η) := by simpa [hw_im] using (abs_of_neg hw_im_neg)
          _ < -z.im := by linarith
          _ = (ε / r) * (-z.re) := by
                rw [hline]
                ring
          _ = (ε / r) * (-w.re) := by simp [w]
    · -- The perturbation size is again exactly `η`.
      have hη_lt_δ : η < δ := by
        have hη_le : η ≤ δ / 2 := min_le_left _ _
        linarith
      rw [dist_eq_norm]
      have hsub : z - w = -((η : ℂ) * Complex.I) := by
        simp [w]
      rw [hsub, norm_neg, norm_mul, Complex.norm_I, mul_one]
      simpa [Complex.norm_real, abs_of_nonneg hη_pos.le] using hη_lt_δ
  -- The lower lip is likewise the meeting set of the wedge and its complement.
  rw [frontier_eq_closure_inter_closure]
  refine ⟨hz_closure, ?_⟩
  rw [closure_compl]
  exact fun hz_int ↦ hz_not_mem (interior_subset hz_int)

/-- Helper for Exercise 21: the geometric upper lip piece already lies in the closed-annulus part
of the wedge frontier. This packages the easy inclusion needed before the harder converse rewrite. -/
lemma exercise21NegativeWedge_upper_lip_image_subset_annulus_frontier
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    (fun ρ : ℝ ↦ circleMap 0 ρ (Real.pi - Real.arctan (ε / r))) '' Set.uIcc r ε ⊆
      {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} ∩ frontier (exercise21NegativeWedge r ε) := by
  rintro z ⟨ρ, hρ, rfl⟩
  have hρIcc : ρ ∈ Set.Icc ε r := by
    rcases Set.mem_uIcc.mp hρ with hρ' | hρ'
    · linarith [hρ'.1, hρ'.2, hεr]
    · exact hρ'
  refine ⟨?_, ?_⟩
  · -- The radius parameter already places the point in the closed annulus.
    show ε ≤ ‖circleMap 0 ρ (Real.pi - Real.arctan (ε / r))‖ ∧
        ‖circleMap 0 ρ (Real.pi - Real.arctan (ε / r))‖ ≤ r
    rw [norm_circleMap_zero, abs_of_nonneg (le_trans hε.le hρIcc.1)]
    exact hρIcc
  · -- Every upper-lip point is a frontier point of the removed wedge.
    exact exercise21NegativeWedge_upper_lip_mem_frontier r ε ρ hε hεr (lt_of_lt_of_le hε hρIcc.1)

/-- Helper for Exercise 21: the geometric lower lip piece also lies in the closed-annulus part of
the wedge frontier. -/
lemma exercise21NegativeWedge_lower_lip_image_subset_annulus_frontier
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    (fun ρ : ℝ ↦ circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))) '' Set.uIcc ε r ⊆
      {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} ∩ frontier (exercise21NegativeWedge r ε) := by
  rintro z ⟨ρ, hρ, rfl⟩
  have hρIcc : ρ ∈ Set.Icc ε r := by
    rcases Set.mem_uIcc.mp hρ with hρ' | hρ'
    · exact hρ'
    · linarith [hρ'.1, hρ'.2, hεr]
  refine ⟨?_, ?_⟩
  · -- The lower-lip radius parameter obeys the same annulus bounds.
    show ε ≤ ‖circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))‖ ∧
        ‖circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))‖ ≤ r
    rw [norm_circleMap_zero, abs_of_nonneg (le_trans hε.le hρIcc.1)]
    exact hρIcc
  · -- Every lower-lip point is again a wedge-frontier point.
    exact exercise21NegativeWedge_lower_lip_mem_frontier r ε ρ hε hεr (lt_of_lt_of_le hε hρIcc.1)

/-- Helper for Exercise 21: a point on the upper slit boundary line with negative real part is
the corresponding upper-lip circle point for a unique positive radius. -/
lemma exercise21_eq_circleMap_upper_of_re_neg_line
    (r ε : ℝ) {z : ℂ}
    (hre : z.re < 0) (hline : z.im = -((ε / r) * z.re)) :
    ∃ ρ > 0, z = circleMap 0 ρ (Real.pi - Real.arctan (ε / r)) := by
  let ρ : ℝ := -z.re / Real.cos (Real.arctan (ε / r))
  have hcos_pos : 0 < Real.cos (Real.arctan (ε / r)) := Real.cos_arctan_pos (ε / r)
  have hcos_ne : Real.cos (Real.arctan (ε / r)) ≠ 0 := hcos_pos.ne'
  have hρ_pos : 0 < ρ := by
    -- The boundary-line radius is positive because both `-re z` and `cos (arctan _)` are.
    dsimp [ρ]
    exact div_pos (by linarith) hcos_pos
  refine ⟨ρ, hρ_pos, ?_⟩
  -- Compare the explicit line point with the circle parametrization coordinatewise.
  rw [Complex.ext_iff]
  constructor
  · rw [circleMap_zero_re, Real.cos_pi_sub]
    dsimp [ρ]
    field_simp [hcos_ne]
  · rw [circleMap_zero_im, Real.sin_pi_sub, hline]
    dsimp [ρ]
    field_simp [hcos_ne]
    rw [Real.sin_arctan, Real.cos_arctan]
    ring

/-- Helper for Exercise 21: a point on the lower slit boundary line with negative real part is
the corresponding lower-lip circle point for a unique positive radius. -/
lemma exercise21_eq_circleMap_lower_of_re_neg_line
    (r ε : ℝ) {z : ℂ}
    (hre : z.re < 0) (hline : z.im = (ε / r) * z.re) :
    ∃ ρ > 0, z = circleMap 0 ρ (-Real.pi + Real.arctan (ε / r)) := by
  let ρ : ℝ := -z.re / Real.cos (Real.arctan (ε / r))
  have hcos_pos : 0 < Real.cos (Real.arctan (ε / r)) := Real.cos_arctan_pos (ε / r)
  have hcos_ne : Real.cos (Real.arctan (ε / r)) ≠ 0 := hcos_pos.ne'
  have hρ_pos : 0 < ρ := by
    -- The same radius formula works on the lower boundary line.
    dsimp [ρ]
    exact div_pos (by linarith) hcos_pos
  have hsin :
      Real.sin (-Real.pi + Real.arctan (ε / r)) = -Real.sin (Real.arctan (ε / r)) := by
    rw [show -Real.pi + Real.arctan (ε / r) = Real.arctan (ε / r) - Real.pi by ring]
    simp [Real.sin_sub]
  have hcos :
      Real.cos (-Real.pi + Real.arctan (ε / r)) = -Real.cos (Real.arctan (ε / r)) := by
    rw [show -Real.pi + Real.arctan (ε / r) = Real.arctan (ε / r) - Real.pi by ring]
    simp [Real.cos_sub]
  refine ⟨ρ, hρ_pos, ?_⟩
  -- The lower-lip parametrization uses the same positive radius with the opposite branch angle.
  rw [Complex.ext_iff]
  constructor
  · rw [circleMap_zero_re, hcos]
    dsimp [ρ]
    field_simp [hcos_ne]
  · rw [circleMap_zero_im, hsin, hline]
    dsimp [ρ]
    field_simp [hcos_ne]
    rw [Real.sin_arctan, Real.cos_arctan]
    ring

/-- Helper for Exercise 21: inside the closed annulus, the wedge-frontier piece is exactly the
union of the two slit lips. This is the source-faithful converse rewrite missing from the global
frontier proof. -/
lemma exercise21NegativeWedgeAnnulus_annulusFrontier_eq_lip_union
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    ({z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} ∩ frontier (exercise21NegativeWedge r ε)) =
      (fun ρ : ℝ ↦ circleMap 0 ρ (Real.pi - Real.arctan (ε / r))) '' Set.uIcc r ε ∪
        (fun ρ : ℝ ↦ circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))) '' Set.uIcc ε r := by
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    rcases hz with ⟨hzAnn, hzFront⟩
    have hr : 0 < r := lt_trans hε hεr
    have hκ_pos : 0 < ε / r := div_pos hε hr
    have hnorm_pos : 0 < ‖z‖ := lt_of_lt_of_le hε hzAnn.1
    have hzClosure : z ∈ closure (exercise21NegativeWedge r ε) := by
      rw [(isOpen_exercise21NegativeWedge r ε).frontier_eq, Set.mem_diff] at hzFront
      exact hzFront.1
    have hz_not_mem : z ∉ exercise21NegativeWedge r ε := by
      rw [(isOpen_exercise21NegativeWedge r ε).frontier_eq, Set.mem_diff] at hzFront
      exact hzFront.2
    have hz_re_nonpos : z.re ≤ 0 := by
      -- The wedge lies in the nonpositive-real half-plane, so every closure point does too.
      have hsubset :
          exercise21NegativeWedge r ε ⊆ {w : ℂ | w.re ≤ 0} := by
        intro w hw
        exact hw.1.le
      exact (closure_minimal hsubset (isClosed_le continuous_re continuous_const)) hzClosure
    have hz_abs_le : |z.im| ≤ (ε / r) * (-z.re) := by
      -- The closure also preserves the weak version of the boundary-line inequality.
      have hsubset :
          exercise21NegativeWedge r ε ⊆ {w : ℂ | |w.im| ≤ (ε / r) * (-w.re)} := by
        intro w hw
        exact hw.2.le
      exact
        (closure_minimal hsubset
          (isClosed_le (continuous_abs.comp continuous_im) (continuous_const.mul continuous_re.neg)))
          hzClosure
    have hz_re_ne : z.re ≠ 0 := by
      intro hre_zero
      have him_zero : z.im = 0 := by
        have him_abs_zero : |z.im| = 0 := by
          apply le_antisymm
          · simpa [hre_zero] using hz_abs_le
          · exact abs_nonneg _
        exact abs_eq_zero.mp him_abs_zero
      have hz_zero : z = 0 := by
        apply Complex.ext <;> simp [hre_zero, him_zero]
      exact hnorm_pos.ne' (by simpa [hz_zero])
    have hz_re_neg : z.re < 0 := lt_of_le_of_ne hz_re_nonpos hz_re_ne
    have hz_abs_ge : (ε / r) * (-z.re) ≤ |z.im| := by
      -- If the inequality were still strict, the point would lie inside the open wedge.
      by_contra hlt
      exact hz_not_mem ⟨hz_re_neg, lt_of_not_ge hlt⟩
    have hz_abs_eq : |z.im| = (ε / r) * (-z.re) := le_antisymm hz_abs_le hz_abs_ge
    by_cases him_nonneg : 0 ≤ z.im
    · have him_line : z.im = -((ε / r) * z.re) := by
        -- On the upper branch, the absolute value drops and produces the upper lip line.
        rw [abs_of_nonneg him_nonneg] at hz_abs_eq
        linarith
      rcases exercise21_eq_circleMap_upper_of_re_neg_line r ε hz_re_neg him_line with
        ⟨ρ, hρ_pos, rfl⟩
      left
      refine ⟨ρ, ?_, rfl⟩
      rw [Set.uIcc_of_gt hεr]
      simpa [norm_circleMap_zero, abs_of_nonneg hρ_pos.le] using hzAnn
    · have him_line : z.im = (ε / r) * z.re := by
        -- On the lower branch, the absolute value contributes the sign change.
        rw [abs_of_neg (lt_of_not_ge him_nonneg)] at hz_abs_eq
        linarith
      rcases exercise21_eq_circleMap_lower_of_re_neg_line r ε hz_re_neg him_line with
        ⟨ρ, hρ_pos, rfl⟩
      right
      refine ⟨ρ, ?_, rfl⟩
      rw [Set.uIcc_of_lt hεr]
      simpa [norm_circleMap_zero, abs_of_nonneg hρ_pos.le] using hzAnn
  · intro z hz
    rcases hz with hz | hz
    · exact (exercise21NegativeWedge_upper_lip_image_subset_annulus_frontier r ε hε hεr) hz
    · exact (exercise21NegativeWedge_lower_lip_image_subset_annulus_frontier r ε hε hεr) hz

/-- Helper for Exercise 21: the two slit-lip geometric images already lie in the normalized split
frontier expression for the slit annulus. This isolates the wedge-frontier half of the source
picture before the surviving-circle classification is added. -/
lemma exercise21NegativeWedgeAnnulus_frontier_split_contains_lips
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    ((fun ρ : ℝ ↦ circleMap 0 ρ (Real.pi - Real.arctan (ε / r))) '' Set.uIcc r ε ∪
        (fun ρ : ℝ ↦ circleMap 0 ρ (-Real.pi + Real.arctan (ε / r))) '' Set.uIcc ε r) ⊆
      ((Metric.sphere (0 : ℂ) r ∪ Metric.sphere (0 : ℂ) ε) \ exercise21NegativeWedge r ε) ∪
        ({z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} ∩ frontier (exercise21NegativeWedge r ε)) := by
  intro z hz
  rcases hz with hz | hz
  · -- The upper lip already lands in the wedge-frontier summand of the split frontier formula.
    exact Or.inr
      ((exercise21NegativeWedge_upper_lip_image_subset_annulus_frontier r ε hε hεr) hz)
  · -- The same packaging applies to the lower slit lip.
    exact Or.inr
      ((exercise21NegativeWedge_lower_lip_image_subset_annulus_frontier r ε hε hεr) hz)

/-- Helper for Exercise 21: on the nonnegative half of `[-π, π]`, surviving the deleted wedge is
equivalent to staying below the upper slit angle `π - arctan (ε / r)`. -/
lemma exercise21_surviving_angle_nonneg_iff
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {φ : ℝ}
    (hφ : φ ∈ Set.Icc (0 : ℝ) Real.pi) :
    (¬ (Real.cos φ < 0 ∧ |Real.sin φ| < (ε / r) * (-Real.cos φ))) ↔
      φ ≤ Real.pi - Real.arctan (ε / r) := by
  let κ : ℝ := ε / r
  let θ : ℝ := Real.arctan κ
  have hr : 0 < r := lt_trans hε hεr
  have hκ_pos : 0 < κ := by
    dsimp [κ]
    exact div_pos hε hr
  have hθ_pos : 0 < θ := by
    dsimp [θ]
    exact Real.arctan_pos.mpr hκ_pos
  have hθ_lt : θ < Real.pi / 2 := by
    dsimp [θ]
    exact Real.arctan_lt_pi_div_two κ
  by_cases hhalf : φ ≤ Real.pi / 2
  · have hcos_nonneg : 0 ≤ Real.cos φ := by
      -- On the first half of `[0, π]`, the cosine never enters the deleted wedge.
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hφ.1], hhalf⟩
    constructor
    · -- The upper slit angle is strictly larger than `π / 2`, so this branch is automatic.
      intro _
      dsimp [θ] at hθ_lt ⊢
      linarith
    · -- A nonnegative cosine rules out the wedge inequality immediately.
      intro _
      rintro ⟨hcos_neg, _⟩
      exact not_lt_of_ge hcos_nonneg hcos_neg
  · let ψ : ℝ := Real.pi - φ
    have hhalf_lt : Real.pi / 2 < φ := lt_of_not_ge hhalf
    have hψ_Ioo : ψ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      dsimp [ψ]
      constructor <;> linarith [hφ.2]
    have hsin_nonneg : 0 ≤ Real.sin φ := Real.sin_nonneg_of_mem_Icc hφ
    have habs : |Real.sin φ| = Real.sin φ := abs_of_nonneg hsin_nonneg
    have hnegcos_pos : 0 < -Real.cos φ := by
      -- On the second half of `[0, π]`, reflect across `π / 2` to recover a positive cosine.
      have hcosψ_pos : 0 < Real.cos ψ := Real.cos_pos_of_mem_Ioo hψ_Ioo
      simpa [ψ, Real.cos_pi_sub] using hcosψ_pos
    have hwedge_iff :
        (Real.cos φ < 0 ∧ |Real.sin φ| < κ * (-Real.cos φ)) ↔ Real.tan ψ < κ := by
      constructor
      · intro hbad
        have hdiv : Real.sin φ / (-Real.cos φ) < κ := by
          have hmul : Real.sin φ < κ * (-Real.cos φ) := by
            simpa [habs] using hbad.2
          exact (div_lt_iff₀ hnegcos_pos).2 <| by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
        -- Re-express the slope inequality on the reflected acute angle.
        simpa [ψ, Real.tan_eq_sin_div_cos, Real.sin_pi_sub, Real.cos_pi_sub] using hdiv
      · intro htan
        refine ⟨?_, ?_⟩
        · linarith
        have hdiv : Real.sin φ / (-Real.cos φ) < κ := by
          simpa [ψ, Real.tan_eq_sin_div_cos, Real.sin_pi_sub, Real.cos_pi_sub] using htan
        have hmul : Real.sin φ < κ * (-Real.cos φ) := (div_lt_iff₀ hnegcos_pos).1 hdiv
        simpa [habs] using hmul
    have htan_iff : Real.tan ψ < κ ↔ ψ < θ := by
      -- Both angles lie in `(-π/2, π/2)`, so `tan` is strictly monotone here.
      rw [← Real.tan_arctan κ]
      exact Real.strictMonoOn_tan.lt_iff_lt hψ_Ioo (Real.arctan_mem_Ioo κ)
    -- Convert the reflected-angle inequality back to the original angle `φ`.
    calc
      (¬ (Real.cos φ < 0 ∧ |Real.sin φ| < κ * (-Real.cos φ))) ↔ ¬ Real.tan ψ < κ := by
        rw [hwedge_iff]
      _ ↔ ¬ ψ < θ := by rw [htan_iff]
      _ ↔ θ ≤ ψ := by rw [not_lt]
      _ ↔ φ ≤ Real.pi - Real.arctan (ε / r) := by
        constructor <;> intro h
        · dsimp [ψ, θ] at h ⊢
          linarith
        · dsimp [ψ, θ] at h ⊢
          linarith

/-- Helper for Exercise 21: inside `[-π, π]`, surviving the deleted wedge is exactly membership in
the angular interval between the two slit-boundary angles. -/
lemma exercise21_surviving_angle_mem_uIcc_iff
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {φ : ℝ}
    (hφ : φ ∈ Set.Icc (-Real.pi) Real.pi) :
    (¬ (Real.cos φ < 0 ∧ |Real.sin φ| < (ε / r) * (-Real.cos φ))) ↔
      φ ∈ Set.uIcc (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)) := by
  let θ : ℝ := Real.arctan (ε / r)
  let α : ℝ := Real.pi - θ
  have hr : 0 < r := lt_trans hε hεr
  have hθ_pos : 0 < θ := by
    dsimp [θ]
    exact Real.arctan_pos.mpr (div_pos hε hr)
  have hθ_lt : θ < Real.pi / 2 := by
    dsimp [θ]
    exact Real.arctan_lt_pi_div_two (ε / r)
  have hα_pos : 0 < α := by
    dsimp [α]
    linarith
  have hlow : -Real.pi + θ < Real.pi - θ := by
    dsimp [θ]
    linarith [Real.pi_pos, hθ_lt]
  by_cases hφ_nonneg : 0 ≤ φ
  · have hφ_nonneg' : φ ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hφ_nonneg, hφ.2⟩
    have hmem :
        φ ∈ Set.uIcc (-Real.pi + θ) (Real.pi - θ) ↔ φ ≤ α := by
      rw [Set.uIcc_of_lt hlow]
      constructor
      · intro hz
        simpa [α, θ] using hz.2
      · intro hz
        refine ⟨?_, ?_⟩
        · dsimp [α, θ] at hz ⊢
          linarith
        · simpa [α, θ] using hz
    -- On the nonnegative half-line, membership in the surviving interval is exactly the upper bound.
    simpa [θ, α] using
      (exercise21_surviving_angle_nonneg_iff r ε hε hεr hφ_nonneg').trans hmem.symm
  · let ψ : ℝ := -φ
    have hφ_neg : φ < 0 := lt_of_not_ge hφ_nonneg
    have hψ_nonneg : ψ ∈ Set.Icc (0 : ℝ) Real.pi := by
      dsimp [ψ]
      constructor
      · linarith
      · have hupper : -φ ≤ Real.pi := by
          linarith [hφ.1]
        simpa using hupper
    have hsymm :
        (¬ (Real.cos φ < 0 ∧ |Real.sin φ| < (ε / r) * (-Real.cos φ))) ↔
          (¬ (Real.cos ψ < 0 ∧ |Real.sin ψ| < (ε / r) * (-Real.cos ψ))) := by
      -- The deleted wedge is symmetric with respect to reflection across the real axis.
      dsimp [ψ]
      simp [Real.cos_neg, Real.sin_neg]
    have hmem :
        φ ∈ Set.uIcc (-Real.pi + θ) (Real.pi - θ) ↔ ψ ≤ α := by
      rw [Set.uIcc_of_lt hlow]
      constructor
      · intro hz
        have hlower : -Real.pi + θ ≤ φ := hz.1
        dsimp [ψ, α, θ]
        linarith
      · intro hz
        refine ⟨?_, ?_⟩
        · dsimp [ψ, α, θ] at hz ⊢
          linarith
        · dsimp [α, θ]
          have hφα : φ < α := by
            linarith [hφ_neg, hα_pos]
          exact hφα.le
    -- Reflect negative angles to the nonnegative branch handled above.
    exact hsymm.trans <|
      (exercise21_surviving_angle_nonneg_iff r ε hε hεr hψ_nonneg).trans hmem.symm

/-- Helper for Exercise 21: a positive-radius circle point survives the deleted wedge exactly when
its angle lies in the surviving principal-argument interval. -/
lemma exercise21NegativeWedge_circleMap_not_mem_iff_angle_mem_surviving_arc
    (r ε ρ : ℝ) (hε : 0 < ε) (hεr : ε < r) (hρ : 0 < ρ) {φ : ℝ}
    (hφ : φ ∈ Set.Icc (-Real.pi) Real.pi) :
    circleMap 0 ρ φ ∉ exercise21NegativeWedge r ε ↔
      φ ∈ Set.uIcc (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)) := by
  have hmem :
      circleMap 0 ρ φ ∈ exercise21NegativeWedge r ε ↔
        (Real.cos φ < 0 ∧ |Real.sin φ| < (ε / r) * (-Real.cos φ)) := by
    constructor
    · intro hz
      refine ⟨?_, ?_⟩
      · -- Positive radius lets us divide the real-part inequality by `ρ`.
        have hre : ρ * Real.cos φ < 0 := by
          simpa [exercise21NegativeWedge, circleMap_zero_re] using hz.1
        nlinarith
      · have him :
            |ρ * Real.sin φ| < (ε / r) * (-(ρ * Real.cos φ)) := by
          simpa [exercise21NegativeWedge, circleMap_zero_re, circleMap_zero_im]
            using hz.2
        have him' : ρ * |Real.sin φ| < ρ * ((ε / r) * (-Real.cos φ)) := by
          simpa [abs_mul, abs_of_pos hρ, mul_assoc, mul_left_comm, mul_comm] using him
        nlinarith
    · intro hz
      refine ⟨?_, ?_⟩
      · -- Conversely, multiplying by the positive radius recovers the circle-point inequality.
        have hre : ρ * Real.cos φ < 0 := by
          nlinarith
        simpa [circleMap_zero_re] using hre
      · have him' : ρ * |Real.sin φ| < ρ * ((ε / r) * (-Real.cos φ)) :=
          by nlinarith
        simpa [circleMap_zero_re, circleMap_zero_im, abs_mul, abs_of_pos hρ,
          mul_assoc, mul_left_comm, mul_comm] using him'
  -- Reduce the circle-point statement to the pure angular classifier.
  rw [show circleMap 0 ρ φ ∉ exercise21NegativeWedge r ε ↔
      ¬ circleMap 0 ρ φ ∈ exercise21NegativeWedge r ε by simp]
  rw [hmem]
  exact exercise21_surviving_angle_mem_uIcc_iff r ε hε hεr hφ

/-- Helper for Exercise 21: on any positive-radius circle centered at the origin, deleting the
negative wedge leaves exactly the image of the surviving argument interval. -/
lemma exercise21NegativeWedge_sphere_diff_eq_arc_image
    (r ε ρ : ℝ) (hε : 0 < ε) (hεr : ε < r) (hρ : 0 < ρ) :
    Metric.sphere (0 : ℂ) ρ \ exercise21NegativeWedge r ε =
      (fun φ : ℝ ↦ circleMap 0 ρ φ) ''
        Set.uIcc (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)) := by
  ext z
  constructor
  · intro hz
    have hz_sphere : z ∈ Metric.sphere (0 : ℂ) ρ := hz.1
    have hnorm : ‖z‖ = ρ := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz_sphere
      simpa [abs_of_pos hρ] using hz_sphere
    have hz_eq : circleMap 0 ρ z.arg = z := by
      -- Reconstruct the sphere point from its norm and principal argument.
      apply Complex.ext_norm_arg
      · simpa [norm_circleMap_zero, abs_of_pos hρ] using hnorm.symm
      · rw [circleMap_zero, Complex.arg_real_mul _ hρ, Complex.arg_exp_mul_I, Complex.toIocMod_arg]
    have harg : z.arg ∈ Set.Icc (-Real.pi) Real.pi := ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩
    refine ⟨z.arg, ?_, hz_eq⟩
    have hz_not_mem : circleMap 0 ρ z.arg ∉ exercise21NegativeWedge r ε := by
      simpa [hz_eq] using hz.2
    exact
      (exercise21NegativeWedge_circleMap_not_mem_iff_angle_mem_surviving_arc
        r ε ρ hε hεr hρ harg).1 hz_not_mem
  · rintro ⟨φ, hφ, rfl⟩
    have hθ_pos : 0 < Real.arctan (ε / r) := by
      have hr : 0 < r := lt_trans hε hεr
      exact Real.arctan_pos.mpr (div_pos hε hr)
    have hinterval :
        -Real.pi + Real.arctan (ε / r) < Real.pi - Real.arctan (ε / r) := by
      have hlt_pi : Real.arctan (ε / r) < Real.pi := by
        linarith [Real.arctan_lt_pi_div_two (ε / r), Real.pi_pos]
      have hleft : -Real.pi + Real.arctan (ε / r) < 0 := by
        linarith
      have hright : 0 ≤ Real.pi - Real.arctan (ε / r) := by
        linarith [Real.arctan_lt_pi_div_two (ε / r)]
      exact lt_of_lt_of_le hleft hright
    have hφIcc : φ ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIcc_of_lt hinterval] at hφ
      refine ⟨?_, ?_⟩
      · exact le_trans (by linarith [hθ_pos]) hφ.1
      · exact le_trans hφ.2 (by linarith [hθ_pos])
    refine ⟨?_, ?_⟩
    · exact circleMap_mem_sphere 0 hρ.le φ
    · exact
        (exercise21NegativeWedge_circleMap_not_mem_iff_angle_mem_surviving_arc
          r ε ρ hε hεr hρ hφIcc).2 hφ

/-- Helper for Exercise 21: the surviving part of the outer boundary circle is exactly the outer
arc image used in the source contour decomposition. -/
lemma exercise21NegativeWedge_outerSphere_diff_eq_outer_arc_image
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    Metric.sphere (0 : ℂ) r \ exercise21NegativeWedge r ε =
      (fun φ : ℝ ↦ circleMap 0 r φ) ''
        Set.uIcc (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)) := by
  -- Specialize the positive-radius circle classifier to the outer radius `r`.
  exact exercise21NegativeWedge_sphere_diff_eq_arc_image r ε r hε hεr (lt_trans hε hεr)

/-- Helper for Exercise 21: the surviving part of the inner boundary circle is exactly the inner
arc image used in the source contour decomposition. -/
lemma exercise21NegativeWedge_innerSphere_diff_eq_inner_arc_image
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    Metric.sphere (0 : ℂ) ε \ exercise21NegativeWedge r ε =
      (fun φ : ℝ ↦ circleMap 0 ε φ) ''
        Set.uIcc (Real.pi - Real.arctan (ε / r)) (-Real.pi + Real.arctan (ε / r)) := by
  -- The inner arc uses the same surviving angular interval, but written in the clockwise order.
  simpa [Set.uIcc, min_comm, max_comm] using
    (exercise21NegativeWedge_sphere_diff_eq_arc_image r ε ε hε hεr hε)

/-- Helper for Exercise 21: once the two fixed-radius classifiers are available, the surviving
circle part of the slit-annulus frontier is exactly the union of the two circle-arc images. -/
lemma exercise21NegativeWedgeAnnulus_surviving_circles_eq_arc_union
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    ((Metric.sphere (0 : ℂ) r ∪ Metric.sphere (0 : ℂ) ε) \ exercise21NegativeWedge r ε) =
      (fun φ : ℝ ↦ circleMap 0 ε φ) ''
        Set.uIcc (Real.pi - Real.arctan (ε / r)) (-Real.pi + Real.arctan (ε / r)) ∪
      (fun φ : ℝ ↦ circleMap 0 r φ) ''
        Set.uIcc (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r)) := by
  ext z
  constructor
  · intro hz
    have hz_not_mem : z ∉ exercise21NegativeWedge r ε := hz.2
    rcases hz.1 with hz_outer | hz_inner
    · -- A surviving outer-circle point belongs to the outer arc image.
      right
      simpa [exercise21NegativeWedge_outerSphere_diff_eq_outer_arc_image r ε hε hεr] using
        (show z ∈ Metric.sphere (0 : ℂ) r \ exercise21NegativeWedge r ε from
          ⟨hz_outer, hz_not_mem⟩)
    · -- A surviving inner-circle point belongs to the inner arc image.
      left
      simpa [exercise21NegativeWedge_innerSphere_diff_eq_inner_arc_image r ε hε hεr] using
        (show z ∈ Metric.sphere (0 : ℂ) ε \ exercise21NegativeWedge r ε from
          ⟨hz_inner, hz_not_mem⟩)
  · rintro (hz | hz)
    · -- Repackage the inner arc image back into the surviving inner sphere.
      have hz' : z ∈ Metric.sphere (0 : ℂ) ε \ exercise21NegativeWedge r ε := by
        simpa [exercise21NegativeWedge_innerSphere_diff_eq_inner_arc_image r ε hε hεr] using hz
      exact ⟨Or.inr hz'.1, hz'.2⟩
    · -- Repackage the outer arc image back into the surviving outer sphere.
      have hz' : z ∈ Metric.sphere (0 : ℂ) r \ exercise21NegativeWedge r ε := by
        simpa [exercise21NegativeWedge_outerSphere_diff_eq_outer_arc_image r ε hε hεr] using hz
      exact ⟨Or.inl hz'.1, hz'.2⟩

/-- Helper for Exercise 21: the frontier of the slit annulus is exactly the range of the explicit
keyhole contour. -/
theorem exercise21NegativeWedgeAnnulus_frontier_eq_range
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    frontier (exercise21NegativeWedgeAnnulus r ε) = Set.range (exercise21Delta r ε) := by
  -- Split the slit-annulus frontier into the surviving circles and the wedge-frontier lips.
  rw [show exercise21NegativeWedgeAnnulus r ε =
      ({z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} \ exercise21NegativeWedge r ε) by
        rfl]
  rw [frontier_diff_open_of_isClosed
      (isClosed_exercise21ClosedAnnulus r ε) (isOpen_exercise21NegativeWedge r ε)]
  -- Rewrite the radial frontier and the slit-frontier piece into the four geometric contour parts.
  rw [exercise21ClosedAnnulus_frontier_eq r ε hε hεr,
    exercise21NegativeWedgeAnnulus_surviving_circles_eq_arc_union r ε hε hεr,
    exercise21NegativeWedgeAnnulus_annulusFrontier_eq_lip_union r ε hε hεr,
    exercise21Delta_range_eq_geometric_piece_union]
  simp [Set.union_assoc, Set.union_left_comm, Set.union_comm]

/-- Helper for Exercise 21: near an interior upper-lip point, the explicit affine normal tube
stays inside the ambient annulus and keeps the same sign pattern `re z < 0 < im z`. This is the
radius/control part of the source-faithful strip chart before converting signed height into
membership in the slit annulus. -/
lemma exercise21_upper_lip_small_strip_ambient
    {r ε ρ₀ : ℝ} (hε : 0 < ε) (hεr : ε < r) (hρ₀ : ρ₀ ∈ Set.Ioo ε r) :
    ∃ η > 0, ∀ {ρ s : ℝ},
      |ρ - ρ₀| < η → |s| < η →
      let φ := Real.pi - Real.arctan (ε / r)
      let z := circleMap 0 ρ φ + (s : ℂ) * circleMap 0 1 (φ - Real.pi / 2)
      ε < ‖z‖ ∧ ‖z‖ < r ∧ z.re < 0 ∧ 0 < z.im := by
  let θ : ℝ := Real.arctan (ε / r)
  have hr : 0 < r := lt_trans hε hεr
  have hρ₀_pos : 0 < ρ₀ := lt_trans hε hρ₀.1
  have hcos_pos : 0 < Real.cos θ := by
    simpa [θ] using Real.cos_arctan_pos (ε / r)
  have hsin_pos : 0 < Real.sin θ := by
    simpa [θ] using Real.sin_arctan_pos.mpr (div_pos hε hr)
  have hsin_nonneg : 0 ≤ Real.sin θ := hsin_pos.le
  have hcos_nonneg : 0 ≤ Real.cos θ := hcos_pos.le
  have hsin_le_one : Real.sin θ ≤ 1 := by
    nlinarith [sq_nonneg (Real.cos θ), Real.sin_sq_add_cos_sq θ]
  have hcos_le_one : Real.cos θ ≤ 1 := by
    nlinarith [sq_nonneg (Real.sin θ), Real.sin_sq_add_cos_sq θ]
  let η : ℝ :=
    min ((ρ₀ - ε) / 4)
      (min ((r - ρ₀) / 4)
        (min (ρ₀ / 4)
          (min (ρ₀ * Real.cos θ / 4) (ρ₀ * Real.sin θ / 4))))
  have hη_pos : 0 < η := by
    dsimp [η]
    refine lt_min ?_ ?_
    · positivity
    · refine lt_min ?_ ?_
      · positivity
      · refine lt_min ?_ ?_
        · positivity
        · refine lt_min ?_ ?_
          · positivity
          · positivity
  refine ⟨η, hη_pos, ?_⟩
  intro ρ s hρ hs
  let φ : ℝ := Real.pi - Real.arctan (ε / r)
  let n : ℂ := circleMap 0 1 (φ - Real.pi / 2)
  let z : ℂ := circleMap 0 ρ φ + (s : ℂ) * n
  have hη_rhoε : η ≤ (ρ₀ - ε) / 4 := by
    dsimp [η]
    exact min_le_left _ _
  have hη_rhor : η ≤ (r - ρ₀) / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hη_rho : η ≤ ρ₀ / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hη_cos : η ≤ ρ₀ * Real.cos θ / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hη_sin : η ≤ ρ₀ * Real.sin θ / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hρ_lower : ρ₀ - η < ρ := by
    have hρ' := abs_lt.mp hρ
    linarith
  have hρ_upper : ρ < ρ₀ + η := by
    have hρ' := abs_lt.mp hρ
    linarith
  have hρ_pos : 0 < ρ := by
    linarith
  have hnorm_upper :
      ‖z‖ < r := by
    have hupper :
        ‖z‖ ≤ ρ + |s| := by
      calc
        ‖z‖ = ‖circleMap 0 ρ φ + (s : ℂ) * n‖ := by rfl
        _ ≤ ‖circleMap 0 ρ φ‖ + ‖(s : ℂ) * n‖ := norm_add_le _ _
        _ = ρ + |s| := by
          rw [norm_circleMap_zero, abs_of_nonneg hρ_pos.le, norm_mul, norm_circleMap_zero]
          simp [n]
    have hρs_lt : ρ + |s| < r := by
      have hη_half : 2 * η ≤ (r - ρ₀) / 2 := by
        nlinarith
      have hstep : ρ + |s| < ρ₀ + 2 * η := by
        linarith
      linarith
    exact lt_of_le_of_lt hupper hρs_lt
  have hnorm_lower :
      ε < ‖z‖ := by
    have hlower :
        ρ - |s| ≤ ‖z‖ := by
      calc
        ρ - |s| = ‖circleMap 0 ρ φ‖ - ‖(s : ℂ) * n‖ := by
          rw [norm_circleMap_zero, abs_of_nonneg hρ_pos.le, norm_mul, norm_circleMap_zero]
          simp [n]
        _ ≤ ‖circleMap 0 ρ φ - (-((s : ℂ) * n))‖ := norm_sub_norm_le _ _
        _ = ‖z‖ := by simp [z]
    have hρs_gt : ε < ρ - |s| := by
      have hstep : ρ₀ - 2 * η < ρ - |s| := by
        linarith
      have hη_half : 2 * η ≤ (ρ₀ - ε) / 2 := by
        nlinarith
      linarith
    exact lt_of_lt_of_le hρs_gt hlower
  have hz_re_formula :
      z.re = -(ρ * Real.cos θ) + s * Real.sin θ := by
    -- Rewrite the affine tube point in explicit trigonometric coordinates.
    dsimp [z, n, φ, θ]
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      circleMap_zero_re, circleMap_zero_im, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
    ring
  have hz_im_formula :
      z.im = ρ * Real.sin θ + s * Real.cos θ := by
    -- The same explicit coordinate rewrite gives the positive imaginary part.
    dsimp [z, n, φ, θ]
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      circleMap_zero_re, circleMap_zero_im, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
    ring
  have hs_sin_le : s * Real.sin θ ≤ |s| := by
    have hs_mul :
        s * Real.sin θ ≤ |s| * Real.sin θ := by
      exact mul_le_mul_of_nonneg_right (le_abs_self s) hsin_nonneg
    have hs_mul' : |s| * Real.sin θ ≤ |s| := by
      nlinarith [abs_nonneg s, hsin_le_one]
    exact hs_mul.trans hs_mul'
  have hs_cos_ge : -|s| ≤ s * Real.cos θ := by
    have hleft : -|s| * Real.cos θ ≤ s * Real.cos θ := by
      exact mul_le_mul_of_nonneg_right (neg_abs_le_self s) hcos_nonneg
    have hright : -|s| ≤ -|s| * Real.cos θ := by
      nlinarith [abs_nonneg s, hcos_le_one]
    exact hright.trans hleft
  have hz_re_neg : z.re < 0 := by
    have hρ_big : 3 * ρ₀ / 4 < ρ := by
      linarith
    have hρcos_big : 3 * (ρ₀ * Real.cos θ) / 4 < ρ * Real.cos θ := by
      nlinarith
    have hs_small : |s| < ρ₀ * Real.cos θ / 4 := by
      exact lt_of_lt_of_le hs hη_cos
    rw [hz_re_formula]
    nlinarith
  have hz_im_pos : 0 < z.im := by
    have hρ_big : 3 * ρ₀ / 4 < ρ := by
      linarith
    have hρsin_big : 3 * (ρ₀ * Real.sin θ) / 4 < ρ * Real.sin θ := by
      nlinarith
    have hs_small : |s| < ρ₀ * Real.sin θ / 4 := by
      exact lt_of_lt_of_le hs hη_sin
    rw [hz_im_formula]
    nlinarith
  exact ⟨hnorm_lower, hnorm_upper, hz_re_neg, hz_im_pos⟩

/-- Helper for Exercise 21: near an interior lower-lip point, the explicit affine normal tube
stays inside the ambient annulus and keeps the sign pattern `re z < 0` and `im z < 0`. This is
the symmetric lower-branch radius/control lemma needed before translating signed height into slit-
annulus membership. -/
lemma exercise21_lower_lip_small_strip_ambient
    {r ε ρ₀ : ℝ} (hε : 0 < ε) (hεr : ε < r) (hρ₀ : ρ₀ ∈ Set.Ioo ε r) :
    ∃ η > 0, ∀ {ρ s : ℝ},
      |ρ - ρ₀| < η → |s| < η →
      let φ := -Real.pi + Real.arctan (ε / r)
      let z := circleMap 0 ρ φ + (s : ℂ) * circleMap 0 1 (φ + Real.pi / 2)
      ε < ‖z‖ ∧ ‖z‖ < r ∧ z.re < 0 ∧ z.im < 0 := by
  let θ : ℝ := Real.arctan (ε / r)
  have hr : 0 < r := lt_trans hε hεr
  have hρ₀_pos : 0 < ρ₀ := lt_trans hε hρ₀.1
  have hcos_pos : 0 < Real.cos θ := by
    simpa [θ] using Real.cos_arctan_pos (ε / r)
  have hsin_pos : 0 < Real.sin θ := by
    simpa [θ] using Real.sin_arctan_pos.mpr (div_pos hε hr)
  have hsin_nonneg : 0 ≤ Real.sin θ := hsin_pos.le
  have hcos_nonneg : 0 ≤ Real.cos θ := hcos_pos.le
  have hsin_le_one : Real.sin θ ≤ 1 := by
    nlinarith [sq_nonneg (Real.cos θ), Real.sin_sq_add_cos_sq θ]
  have hcos_le_one : Real.cos θ ≤ 1 := by
    nlinarith [sq_nonneg (Real.sin θ), Real.sin_sq_add_cos_sq θ]
  let η : ℝ :=
    min ((ρ₀ - ε) / 4)
      (min ((r - ρ₀) / 4)
        (min (ρ₀ / 4)
          (min (ρ₀ * Real.cos θ / 4) (ρ₀ * Real.sin θ / 4))))
  have hη_pos : 0 < η := by
    dsimp [η]
    refine lt_min ?_ ?_
    · positivity
    · refine lt_min ?_ ?_
      · positivity
      · refine lt_min ?_ ?_
        · positivity
        · refine lt_min ?_ ?_
          · positivity
          · positivity
  refine ⟨η, hη_pos, ?_⟩
  intro ρ s hρ hs
  let φ : ℝ := -Real.pi + Real.arctan (ε / r)
  let n : ℂ := circleMap 0 1 (φ + Real.pi / 2)
  let z : ℂ := circleMap 0 ρ φ + (s : ℂ) * n
  have hη_rhoε : η ≤ (ρ₀ - ε) / 4 := by
    dsimp [η]
    exact min_le_left _ _
  have hη_rhor : η ≤ (r - ρ₀) / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hη_rho : η ≤ ρ₀ / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hη_cos : η ≤ ρ₀ * Real.cos θ / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hη_sin : η ≤ ρ₀ * Real.sin θ / 4 := by
    dsimp [η]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hρ_lower : ρ₀ - η < ρ := by
    have hρ' := abs_lt.mp hρ
    linarith
  have hρ_upper : ρ < ρ₀ + η := by
    have hρ' := abs_lt.mp hρ
    linarith
  have hρ_pos : 0 < ρ := by
    linarith
  have hnorm_upper : ‖z‖ < r := by
    have hupper : ‖z‖ ≤ ρ + |s| := by
      calc
        ‖z‖ = ‖circleMap 0 ρ φ + (s : ℂ) * n‖ := by rfl
        _ ≤ ‖circleMap 0 ρ φ‖ + ‖(s : ℂ) * n‖ := norm_add_le _ _
        _ = ρ + |s| := by
          rw [norm_circleMap_zero, abs_of_nonneg hρ_pos.le, norm_mul, norm_circleMap_zero]
          simp [n]
    have hρs_lt : ρ + |s| < r := by
      have hη_half : 2 * η ≤ (r - ρ₀) / 2 := by
        nlinarith
      have hstep : ρ + |s| < ρ₀ + 2 * η := by
        linarith
      linarith
    exact lt_of_le_of_lt hupper hρs_lt
  have hnorm_lower : ε < ‖z‖ := by
    have hlower : ρ - |s| ≤ ‖z‖ := by
      calc
        ρ - |s| = ‖circleMap 0 ρ φ‖ - ‖(s : ℂ) * n‖ := by
          rw [norm_circleMap_zero, abs_of_nonneg hρ_pos.le, norm_mul, norm_circleMap_zero]
          simp [n]
        _ ≤ ‖circleMap 0 ρ φ - (-((s : ℂ) * n))‖ := norm_sub_norm_le _ _
        _ = ‖z‖ := by simp [z]
    have hρs_gt : ε < ρ - |s| := by
      have hstep : ρ₀ - 2 * η < ρ - |s| := by
        linarith
      have hη_half : 2 * η ≤ (ρ₀ - ε) / 2 := by
        nlinarith
      linarith
    exact lt_of_lt_of_le hρs_gt hlower
  have hz_re_formula :
      z.re = -(ρ * Real.cos θ) + s * Real.sin θ := by
    -- Rewrite the lower affine tube point in explicit trigonometric coordinates.
    dsimp [z, n, φ, θ]
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      circleMap_zero_re, circleMap_zero_im, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
    ring
  have hz_im_formula :
      z.im = -(ρ * Real.sin θ) - s * Real.cos θ := by
    -- The explicit imaginary-part formula shows the whole lower strip stays below the real axis.
    dsimp [z, n, φ, θ]
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      circleMap_zero_re, circleMap_zero_im, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two]
    ring
  have hs_sin_le : s * Real.sin θ ≤ |s| := by
    have hs_mul : s * Real.sin θ ≤ |s| * Real.sin θ := by
      exact mul_le_mul_of_nonneg_right (le_abs_self s) hsin_nonneg
    have hs_mul' : |s| * Real.sin θ ≤ |s| := by
      nlinarith [abs_nonneg s, hsin_le_one]
    exact hs_mul.trans hs_mul'
  have hs_cos_ge : -|s| ≤ s * Real.cos θ := by
    have hleft : -|s| * Real.cos θ ≤ s * Real.cos θ := by
      exact mul_le_mul_of_nonneg_right (neg_abs_le_self s) hcos_nonneg
    have hright : -|s| ≤ -|s| * Real.cos θ := by
      nlinarith [abs_nonneg s, hcos_le_one]
    exact hright.trans hleft
  have hz_re_neg : z.re < 0 := by
    have hρ_big : 3 * ρ₀ / 4 < ρ := by
      linarith
    have hρcos_big : 3 * (ρ₀ * Real.cos θ) / 4 < ρ * Real.cos θ := by
      nlinarith
    have hs_small : |s| < ρ₀ * Real.cos θ / 4 := by
      exact lt_of_lt_of_le hs hη_cos
    rw [hz_re_formula]
    nlinarith
  have hz_im_neg : z.im < 0 := by
    have hρ_big : 3 * ρ₀ / 4 < ρ := by
      linarith
    have hρsin_big : 3 * (ρ₀ * Real.sin θ) / 4 < ρ * Real.sin θ := by
      nlinarith
    have hs_small : |s| < ρ₀ * Real.sin θ / 4 := by
      exact lt_of_lt_of_le hs hη_sin
    rw [hz_im_formula]
    nlinarith
  exact ⟨hnorm_lower, hnorm_upper, hz_re_neg, hz_im_neg⟩

/-- Helper for Exercise 21: on the upper half-plane side of the slit, membership in the slit
annulus is equivalent to lying on or above the upper boundary line of the removed wedge. This is
the canonical rewrite that turns the affine-strip signed-height identity into a set-membership
statement. -/
lemma exercise21NegativeWedgeAnnulus_mem_iff_upper_signed_height_nonneg
    {r ε : ℝ} {z : ℂ}
    (hεz : ε < ‖z‖) (hzr : ‖z‖ < r) (hzre : z.re < 0) (hzim : 0 < z.im) :
    z ∈ exercise21NegativeWedgeAnnulus r ε ↔ 0 ≤ z.im + (ε / r) * z.re := by
  constructor
  · intro hz
    -- Under the fixed sign hypotheses, not being in the deleted wedge is exactly the negation of
    -- the strict upper-boundary inequality.
    have hnot_height : ¬ z.im < (ε / r) * (-z.re) := by
      intro hlt
      exact hz.2 ⟨hzre, by simpa [abs_of_pos hzim] using hlt⟩
    have hheight : (ε / r) * (-z.re) ≤ z.im := le_of_not_gt hnot_height
    linarith
  · intro hheight
    -- Route correction: use the source-faithful signed-height criterion directly instead of
    -- trying to prove branch membership by repeated local strip lemmas.
    refine ⟨⟨le_of_lt hεz, le_of_lt hzr⟩, ?_⟩
    intro hwedge
    have hlt : z.im < (ε / r) * (-z.re) := by
      simpa [abs_of_pos hzim] using hwedge.2
    linarith

/-- Helper for Exercise 21: on the lower half-plane side of the slit, membership in the slit
annulus is equivalent to lying on or above the lower boundary line measured by the reflected
signed height `-im z + (ε / r) re z`. -/
lemma exercise21NegativeWedgeAnnulus_mem_iff_lower_signed_height_nonneg
    {r ε : ℝ} {z : ℂ}
    (hεz : ε < ‖z‖) (hzr : ‖z‖ < r) (hzre : z.re < 0) (hzim : z.im < 0) :
    z ∈ exercise21NegativeWedgeAnnulus r ε ↔ 0 ≤ -z.im + (ε / r) * z.re := by
  constructor
  · intro hz
    -- The lower branch is the same wedge inequality after rewriting `|im z|` as `-im z`.
    have hnot_height : ¬ -z.im < (ε / r) * (-z.re) := by
      intro hlt
      exact hz.2 ⟨hzre, by simpa [abs_of_neg hzim] using hlt⟩
    have hheight : (ε / r) * (-z.re) ≤ -z.im := le_of_not_gt hnot_height
    linarith
  · intro hheight
    -- Repackage the strict annulus bounds and then exclude the deleted wedge by the signed-height
    -- inequality.
    refine ⟨⟨le_of_lt hεz, le_of_lt hzr⟩, ?_⟩
    intro hwedge
    have hlt : -z.im < (ε / r) * (-z.re) := by
      simpa [abs_of_neg hzim] using hwedge.2
    linarith

/-- Helper for Exercise 21: near an interior upper-lip point, the sign of the transverse
parameter decides whether the explicit affine strip point lies inside or outside the slit annulus.
This is the pointwise side-of-boundary statement used later to package the upper strip chart. -/
lemma exercise21_upper_lip_side_of_annulus
    {r ε ρ₀ : ℝ} (hε : 0 < ε) (hεr : ε < r) (hρ₀ : ρ₀ ∈ Set.Ioo ε r) :
    ∃ η > 0, ∀ {ρ s : ℝ},
      |ρ - ρ₀| < η → |s| < η →
      let z := circleMap 0 ρ (Real.pi - Real.arctan (ε / r)) +
        (s : ℂ) * circleMap 0 1 ((Real.pi - Real.arctan (ε / r)) - Real.pi / 2)
      (s < 0 → z ∉ exercise21NegativeWedgeAnnulus r ε) ∧
        (0 < s → z ∈ exercise21NegativeWedgeAnnulus r ε) := by
  rcases exercise21_upper_lip_small_strip_ambient hε hεr hρ₀ with ⟨η, hη, hambient⟩
  refine ⟨η, hη, ?_⟩
  intro ρ s hρ hs
  let z := circleMap 0 ρ (Real.pi - Real.arctan (ε / r)) +
    (s : ℂ) * circleMap 0 1 ((Real.pi - Real.arctan (ε / r)) - Real.pi / 2)
  have hambient' := hambient hρ hs
  have hsigned :
      z.im + (ε / r) * z.re =
        s *
          (Real.cos (Real.arctan (ε / r)) +
            (ε / r) * Real.sin (Real.arctan (ε / r))) := by
    simpa [z] using exercise21_upper_lip_normal_signed_height r ε ρ s
  have hcoeff :
      0 <
        Real.cos (Real.arctan (ε / r)) +
          (ε / r) * Real.sin (Real.arctan (ε / r)) :=
    exercise21_lip_transverse_coefficient_pos r ε hε hεr
  constructor
  · intro hsneg hzmem
    have hheight :
        0 ≤ z.im + (ε / r) * z.re :=
      (exercise21NegativeWedgeAnnulus_mem_iff_upper_signed_height_nonneg
        hambient'.1 hambient'.2.1 hambient'.2.2.1 hambient'.2.2.2).1 hzmem
    rw [hsigned] at hheight
    nlinarith
  · intro hspos
    have hheight :
        0 ≤ z.im + (ε / r) * z.re := by
      rw [hsigned]
      nlinarith
    exact
      (exercise21NegativeWedgeAnnulus_mem_iff_upper_signed_height_nonneg
        hambient'.1 hambient'.2.1 hambient'.2.2.1 hambient'.2.2.2).2 hheight

/-- Helper for Exercise 21: near an interior lower-lip point, positive transverse height moves
into the slit annulus and negative transverse height moves out of it. This is the reflected
pointwise side-of-boundary statement for the lower strip chart. -/
lemma exercise21_lower_lip_side_of_annulus
    {r ε ρ₀ : ℝ} (hε : 0 < ε) (hεr : ε < r) (hρ₀ : ρ₀ ∈ Set.Ioo ε r) :
    ∃ η > 0, ∀ {ρ s : ℝ},
      |ρ - ρ₀| < η → |s| < η →
      let z := circleMap 0 ρ (-Real.pi + Real.arctan (ε / r)) +
        (s : ℂ) * circleMap 0 1 ((-Real.pi + Real.arctan (ε / r)) + Real.pi / 2)
      (s < 0 → z ∉ exercise21NegativeWedgeAnnulus r ε) ∧
        (0 < s → z ∈ exercise21NegativeWedgeAnnulus r ε) := by
  rcases exercise21_lower_lip_small_strip_ambient hε hεr hρ₀ with ⟨η, hη, hambient⟩
  refine ⟨η, hη, ?_⟩
  intro ρ s hρ hs
  let z := circleMap 0 ρ (-Real.pi + Real.arctan (ε / r)) +
    (s : ℂ) * circleMap 0 1 ((-Real.pi + Real.arctan (ε / r)) + Real.pi / 2)
  have hambient' := hambient hρ hs
  have hsigned :
      -z.im + (ε / r) * z.re =
        s *
          (Real.cos (Real.arctan (ε / r)) +
            (ε / r) * Real.sin (Real.arctan (ε / r))) := by
    simpa [z] using exercise21_lower_lip_normal_signed_height r ε ρ s
  have hcoeff :
      0 <
        Real.cos (Real.arctan (ε / r)) +
          (ε / r) * Real.sin (Real.arctan (ε / r)) :=
    exercise21_lip_transverse_coefficient_pos r ε hε hεr
  constructor
  · intro hsneg hzmem
    have hheight :
        0 ≤ -z.im + (ε / r) * z.re :=
      (exercise21NegativeWedgeAnnulus_mem_iff_lower_signed_height_nonneg
        hambient'.1 hambient'.2.1 hambient'.2.2.1 hambient'.2.2.2).1 hzmem
    rw [hsigned] at hheight
    nlinarith
  · intro hspos
    have hheight :
        0 ≤ -z.im + (ε / r) * z.re := by
      rw [hsigned]
      nlinarith
    exact
      (exercise21NegativeWedgeAnnulus_mem_iff_lower_signed_height_nonneg
        hambient'.1 hambient'.2.1 hambient'.2.2.1 hambient'.2.2.2).2 hheight

/-- Helper for Exercise 21: once the angle stays in the surviving principal-argument interval,
membership of a circle point in the slit annulus is purely radial. This is the canonical circle
rewrite used by the inner and outer boundary charts. -/
lemma exercise21NegativeWedgeAnnulus_circleMap_mem_iff_radius_mem_Icc
    (r ε ρ : ℝ) (hε : 0 < ε) (hεr : ε < r) (hρ : 0 < ρ) {φ : ℝ}
    (hφ : φ ∈ Set.Icc (-Real.pi) Real.pi)
    (hφsurvive :
      φ ∈ Set.uIcc (-Real.pi + Real.arctan (ε / r)) (Real.pi - Real.arctan (ε / r))) :
    circleMap 0 ρ φ ∈ exercise21NegativeWedgeAnnulus r ε ↔ ρ ∈ Set.Icc ε r := by
  constructor
  · intro hz
    -- On a fixed circle point, annulus membership records exactly the radius bounds.
    simpa [norm_circleMap_zero, abs_of_pos hρ] using hz.1
  · intro hρIcc
    -- The surviving-angle rewrite removes the wedge condition, leaving only the radial interval.
    refine ⟨?_, ?_⟩
    · simpa [norm_circleMap_zero, abs_of_pos hρ] using hρIcc
    · exact
        (exercise21NegativeWedge_circleMap_not_mem_iff_angle_mem_surviving_arc
          r ε ρ hε hεr hρ hφ).2 hφsurvive

/-- Helper for Exercise 21: quarter-turning a complex tangent in real coordinates is multiplication
by `I` before converting back to `Plane`. -/
lemma exercise21_rot90_equivRealProd_eq_equivRealProd_mul_I (z : ℂ) :
    rot90 (Complex.equivRealProd z) = Complex.equivRealProd (z * Complex.I) := by
  -- `Complex.equivRealProd` identifies multiplication by `I` with the standard quarter-turn.
  ext <;> simp [rot90, Complex.equivRealProd]

/-- Helper for Exercise 21: a tube map around a `C¹` branch has the expected tangent and
transverse derivative columns at the base point. -/
lemma exercise21_radial_tube_hasFDerivAt {γ n : ℝ → ℂ} {t₀ : ℝ} {v : ℂ}
    (hγCont : ContDiffAt ℝ 1 γ t₀) (hγDeriv : HasDerivAt γ v t₀)
    (hnCont : ContDiffAt ℝ 1 n t₀) :
    ContDiffAt ℝ 1 (fun p : Plane ↦ γ p.1 + p.2 • n p.1) (t₀, 0) ∧
      HasFDerivAt (fun p : Plane ↦ γ p.1 + p.2 • n p.1)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (n t₀))
        (t₀, 0) := by
  constructor
  · -- The tube map is the sum of the branch and the varying transverse direction.
    have hγfst : ContDiffAt ℝ 1 (fun p : Plane ↦ γ p.1) (t₀, 0) := by
      simpa using hγCont.comp (x := (t₀, 0)) contDiffAt_fst
    have hnfst : ContDiffAt ℝ 1 (fun p : Plane ↦ n p.1) (t₀, 0) := by
      simpa using hnCont.comp (x := (t₀, 0)) contDiffAt_fst
    simpa using hγfst.add (contDiffAt_snd.smul hnfst)
  · -- At `p.2 = 0`, the transverse derivative contributes only the normal vector itself.
    have hγfst :
        HasFDerivAt (fun p : Plane ↦ γ p.1)
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v) (t₀, (0 : ℝ)) := by
      simpa [ContinuousLinearMap.smulRight_apply] using
        hγDeriv.hasFDerivAt.comp (t₀, (0 : ℝ))
          (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (t₀, (0 : ℝ))))
    have hnfst :
        HasFDerivAt (fun p : Plane ↦ n p.1)
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (deriv n t₀)) (t₀, (0 : ℝ)) := by
      simpa [ContinuousLinearMap.smulRight_apply] using
        (hnCont.differentiableAt one_ne_zero).hasDerivAt.hasFDerivAt.comp (t₀, (0 : ℝ))
          (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (t₀, (0 : ℝ))))
    have hsnd :
        HasFDerivAt (fun p : Plane ↦ p.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (t₀, (0 : ℝ)) := by
      simpa using
        (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (t₀, (0 : ℝ))))
    simpa [ContinuousLinearMap.smulRight_apply] using hγfst.add (hsnd.smul hnfst)

/-- Helper for Exercise 21: rescaling the second `Plane` coordinate by a nonzero real factor is
the linear equivalence used to normalize the tangent/normal frame in the strip charts. -/
noncomputable def exercise21_plane_second_rescale (c : ℝ) (hc : c ≠ 0) : Plane ≃L[ℝ] Plane :=
  { toLinearEquiv :=
      { toFun := fun p ↦ (p.1, p.2 / c)
        invFun := fun p ↦ (p.1, c * p.2)
        left_inv := by
          intro p
          ext
          · rfl
          · field_simp [hc]
        right_inv := by
          intro p
          ext
          · rfl
          · field_simp [hc]
        map_add' := by
          intro p q
          ext <;> simp [div_eq_mul_inv, add_mul]
        map_smul' := by
          intro s p
          ext <;> simp [div_eq_mul_inv, mul_assoc] }
    continuous_toFun := by
      fun_prop
    continuous_invFun := by
      fun_prop }

/-- Helper for Exercise 21: the upper slit-lip side test can be read directly in `Plane`
coordinates, so later chart proofs can use the transverse coordinate `p.2` without repackaging
back to separate `(ρ, s)` variables. -/
lemma exercise21_upper_lip_plane_side_of_annulus
    {r ε ρ₀ : ℝ} (hε : 0 < ε) (hεr : ε < r) (hρ₀ : ρ₀ ∈ Set.Ioo ε r) :
    ∃ η > 0, ∀ {p : Plane},
      |p.1 - ρ₀| < η → |p.2| < η →
      let z := circleMap 0 p.1 (Real.pi - Real.arctan (ε / r)) +
        (p.2 : ℂ) * circleMap 0 1 ((Real.pi - Real.arctan (ε / r)) - Real.pi / 2)
      (p.2 < 0 → z ∉ exercise21NegativeWedgeAnnulus r ε) ∧
        (0 < p.2 → z ∈ exercise21NegativeWedgeAnnulus r ε) := by
  rcases exercise21_upper_lip_side_of_annulus hε hεr hρ₀ with ⟨η, hη, hside⟩
  refine ⟨η, hη, ?_⟩
  intro p hpρ hp2
  -- This is exactly the earlier side-of-annulus statement after reading `(ρ, s)` as `p.1, p.2`.
  simpa using hside hpρ hp2

/-- Helper for Exercise 21: the lower slit-lip side test likewise packages cleanly in `Plane`
coordinates, which is the form needed by the later strip-chart boundary fields. -/
lemma exercise21_lower_lip_plane_side_of_annulus
    {r ε ρ₀ : ℝ} (hε : 0 < ε) (hεr : ε < r) (hρ₀ : ρ₀ ∈ Set.Ioo ε r) :
    ∃ η > 0, ∀ {p : Plane},
      |p.1 - ρ₀| < η → |p.2| < η →
      let z := circleMap 0 p.1 (-Real.pi + Real.arctan (ε / r)) +
        (p.2 : ℂ) * circleMap 0 1 ((-Real.pi + Real.arctan (ε / r)) + Real.pi / 2)
      (p.2 < 0 → z ∉ exercise21NegativeWedgeAnnulus r ε) ∧
        (0 < p.2 → z ∈ exercise21NegativeWedgeAnnulus r ε) := by
  rcases exercise21_lower_lip_side_of_annulus hε hεr hρ₀ with ⟨η, hη, hside⟩
  refine ⟨η, hη, ?_⟩
  intro p hpρ hp2
  -- This is the reflected lower-branch side test in the chart-native `Plane` coordinates.
  simpa using hside hpρ hp2

/-- Helper for Exercise 21: composing the upper-lip side test with the affine branch parameter
`t ↦ lineMap r ε (8 t)` packages the annulus-side information directly in the strip-chart
coordinates `(t, s)`. -/
lemma exercise21_upper_lip_chart_side_of_annulus
    {r ε t₀ : ℝ} (hε : 0 < ε) (hεr : ε < r) (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) (1 / 8 : ℝ)) :
    ∃ η > 0, ∀ {p : Plane},
      |p.1 - t₀| < η → |p.2| < η →
      let z := circleMap 0 (AffineMap.lineMap r ε (8 * p.1))
          (Real.pi - Real.arctan (ε / r)) +
        (p.2 : ℂ) * circleMap 0 1 ((Real.pi - Real.arctan (ε / r)) - Real.pi / 2)
      (p.2 < 0 → z ∉ exercise21NegativeWedgeAnnulus r ε) ∧
        (0 < p.2 → z ∈ exercise21NegativeWedgeAnnulus r ε) := by
  let ρ₀ : ℝ := AffineMap.lineMap r ε (8 * t₀)
  have hparam₀ : 8 * t₀ ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht₀.1, ht₀.2]
  have hρ₀ : ρ₀ ∈ Set.Ioo ε r := by
    -- The base radius lies strictly between `ε` and `r` because `t₀` is an interior upper-lip
    -- parameter.
    have hseg : ρ₀ ∈ openSegment ℝ r ε := by
      simpa [ρ₀] using lineMap_mem_openSegment (𝕜 := ℝ) r ε hparam₀
    have hre : (r : ℝ) ≠ ε := by
      linarith
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hre] at hseg
    simpa [ρ₀, min_eq_right (le_of_lt hεr), max_eq_left (le_of_lt hεr)] using hseg
  rcases exercise21_upper_lip_plane_side_of_annulus hε hεr hρ₀ with ⟨η₀, hη₀, hside⟩
  let η : ℝ := min η₀ (η₀ / (8 * (r - ε)))
  have hscale : 0 < 8 * (r - ε) := by
    nlinarith
  refine ⟨η, lt_min hη₀ (div_pos hη₀ hscale), ?_⟩
  intro p hp ht
  have hp₂ : |p.2| < η₀ := by
    exact lt_of_lt_of_le ht (min_le_left _ _)
  have hp₁ : |AffineMap.lineMap r ε (8 * p.1) - ρ₀| < η₀ := by
    have hp₁' : |p.1 - t₀| < η₀ / (8 * (r - ε)) := by
      exact lt_of_lt_of_le hp (min_le_right _ _)
    have hlin :
        AffineMap.lineMap r ε (8 * p.1) - ρ₀ = (8 * (p.1 - t₀)) * (ε - r) := by
      dsimp [ρ₀]
      simp [AffineMap.lineMap_apply_module]
      ring
    calc
      |AffineMap.lineMap r ε (8 * p.1) - ρ₀|
          = |8 * (p.1 - t₀)| * |ε - r| := by
              rw [hlin, abs_mul]
      _ = (8 * |p.1 - t₀|) * (r - ε) := by
            rw [abs_mul, abs_of_nonneg (show 0 ≤ (8 : ℝ) by norm_num),
              abs_of_neg (by linarith : ε - r < 0)]
            ring
      _ = (8 * (r - ε)) * |p.1 - t₀| := by
            ring
      _ < (8 * (r - ε)) * (η₀ / (8 * (r - ε))) := by
            gcongr
      _ = η₀ := by
            field_simp [hscale.ne']
  -- Apply the already-packaged `Plane` side test at the transported radius coordinate.
  simpa [ρ₀] using
    (hside (p := (AffineMap.lineMap r ε (8 * p.1), p.2)) hp₁ hp₂)

/-- Helper for Exercise 21: composing the reflected lower-lip side test with the affine branch
parameter `t ↦ lineMap ε r (4 t - 1)` packages the annulus-side information in the actual lower
strip-chart coordinates `(t, s)`. -/
lemma exercise21_lower_lip_chart_side_of_annulus
    {r ε t₀ : ℝ} (hε : 0 < ε) (hεr : ε < r) (ht₀ : t₀ ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2 : ℝ)) :
    ∃ η > 0, ∀ {p : Plane},
      |p.1 - t₀| < η → |p.2| < η →
      let z := circleMap 0 (AffineMap.lineMap ε r (4 * p.1 - 1))
          (-Real.pi + Real.arctan (ε / r)) +
        (p.2 : ℂ) * circleMap 0 1 ((-Real.pi + Real.arctan (ε / r)) + Real.pi / 2)
      (p.2 < 0 → z ∉ exercise21NegativeWedgeAnnulus r ε) ∧
        (0 < p.2 → z ∈ exercise21NegativeWedgeAnnulus r ε) := by
  let ρ₀ : ℝ := AffineMap.lineMap ε r (4 * t₀ - 1)
  have hparam₀ : 4 * t₀ - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht₀.1, ht₀.2]
  have hρ₀ : ρ₀ ∈ Set.Ioo ε r := by
    -- The reflected branch uses the same open-segment radius control on `(ε, r)`.
    have hseg : ρ₀ ∈ openSegment ℝ ε r := by
      simpa [ρ₀] using lineMap_mem_openSegment (𝕜 := ℝ) ε r hparam₀
    have hre : (ε : ℝ) ≠ r := by
      linarith
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hre] at hseg
    simpa [ρ₀, min_eq_left (le_of_lt hεr), max_eq_right (le_of_lt hεr)] using hseg
  rcases exercise21_lower_lip_plane_side_of_annulus hε hεr hρ₀ with ⟨η₀, hη₀, hside⟩
  let η : ℝ := min η₀ (η₀ / (4 * (r - ε)))
  have hscale : 0 < 4 * (r - ε) := by
    nlinarith
  refine ⟨η, lt_min hη₀ (div_pos hη₀ hscale), ?_⟩
  intro p hp ht
  have hp₂ : |p.2| < η₀ := by
    exact lt_of_lt_of_le ht (min_le_left _ _)
  have hp₁ : |AffineMap.lineMap ε r (4 * p.1 - 1) - ρ₀| < η₀ := by
    have hp₁' : |p.1 - t₀| < η₀ / (4 * (r - ε)) := by
      exact lt_of_lt_of_le hp (min_le_right _ _)
    have hlin :
        AffineMap.lineMap ε r (4 * p.1 - 1) - ρ₀ = (4 * (p.1 - t₀)) * (r - ε) := by
      dsimp [ρ₀]
      simp [AffineMap.lineMap_apply_module]
      ring
    calc
      |AffineMap.lineMap ε r (4 * p.1 - 1) - ρ₀|
          = |4 * (p.1 - t₀)| * |r - ε| := by
              rw [hlin, abs_mul]
      _ = (4 * |p.1 - t₀|) * (r - ε) := by
            rw [abs_mul, abs_of_nonneg (show 0 ≤ (4 : ℝ) by norm_num),
              abs_of_nonneg (show 0 ≤ r - ε by linarith)]
            ring
      _ = (4 * (r - ε)) * |p.1 - t₀| := by
            ring
      _ < (4 * (r - ε)) * (η₀ / (4 * (r - ε))) := by
            gcongr
      _ = η₀ := by
            field_simp [hscale.ne']
  -- Apply the reflected `Plane` side test after transporting the first chart coordinate.
  simpa [ρ₀] using
    (hside (p := (AffineMap.lineMap ε r (4 * p.1 - 1), p.2)) hp₁ hp₂)

/-- Helper for Exercise 21: once a regular parameter lies on one of the two slit lips, the
boundary-straightening problem is reduced to the explicit affine strip chart aligned with that
lip. -/
/-- Helper for Exercise 21: an interior point on the upper slit lip admits an explicit affine
boundary-straightening chart whose positive transverse side enters the slit annulus. -/
lemma exercise21_upper_lip_exists_boundary_chart
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) (1 / 8 : ℝ)) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (exercise21NegativeWedgeAnnulus r ε)
        ((exercise21Delta r ε).toClosedPath.realCurve) t₀ δ := by
  -- Route correction: this should follow the Proposition 3.1 strip-chart template with the
  -- explicit upper-lip branch `t ↦ lineMap (circleMap 0 r φ) (circleMap 0 ε φ) (8 t)`,
  -- the constant inward normal `circleMap 0 1 (φ - π/2)`, and the existing upper-lip ambient
  -- and signed-height lemmas to fill `exterior_on_right` and `interior_on_left`.
  -- TODO: build the restricted inverse-function chart and package the positive-side image into an
  -- explicit open subset of `exercise21NegativeWedgeAnnulus r ε`.
  let _ := hε
  let _ := hεr
  let _ := ht₀
  sorry

/-- Helper for Exercise 21: an interior point on the lower slit lip admits the reflected affine
boundary-straightening chart whose positive transverse side again enters the slit annulus. -/
lemma exercise21_lower_lip_exists_boundary_chart
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2 : ℝ)) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (exercise21NegativeWedgeAnnulus r ε)
        ((exercise21Delta r ε).toClosedPath.realCurve) t₀ δ := by
  -- Route correction: this should repeat the upper-lip strip-chart construction with the
  -- reflected branch `t ↦ lineMap (circleMap 0 ε φ) (circleMap 0 r φ) (4 t - 1)` and the normal
  -- `circleMap 0 1 (φ + π/2)`, using the lower-lip ambient and signed-height lemmas to package
  -- the side conditions.
  -- TODO: build the restricted inverse-function chart and prove the lower positive-side image
  -- lies in an explicit open subset of `exercise21NegativeWedgeAnnulus r ε`.
  let _ := hε
  let _ := hεr
  let _ := ht₀
  sorry

lemma exercise21_ray_branch_exists_boundary_chart
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hbranch :
      t₀ ∈ Set.Ioo (0 : ℝ) (1 / 8) ∨ t₀ ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2))
    (hdiff :
      DifferentiableWithinAt ℝ ((exercise21Delta r ε).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀)
    (hderiv :
      derivWithin ((exercise21Delta r ε).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ ≠ 0) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (exercise21NegativeWedgeAnnulus r ε)
        ((exercise21Delta r ε).toClosedPath.realCurve) t₀ δ := by
  -- Route correction: the ray branches are now handled by the two concrete slit-lip charts.
  let _ := hdiff
  let _ := hderiv
  rcases hbranch with htupper | htlower
  · exact exercise21_upper_lip_exists_boundary_chart r ε hε hεr htupper
  · exact exercise21_lower_lip_exists_boundary_chart r ε hε hεr htlower

/-- Helper for Exercise 21: once a regular parameter lies on one of the two circular branches, the
boundary-straightening problem is reduced to the explicit radial strip chart for that circle. -/
lemma exercise21_circle_branch_exists_boundary_chart
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hbranch :
      t₀ ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4) ∨ t₀ ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ))
    (hdiff :
      DifferentiableWithinAt ℝ ((exercise21Delta r ε).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀)
    (hderiv :
      derivWithin ((exercise21Delta r ε).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ ≠ 0) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (exercise21NegativeWedgeAnnulus r ε)
        ((exercise21Delta r ε).toClosedPath.realCurve) t₀ δ := by
  -- Route correction: the circular branches need radial normals, so isolate that chart package
  -- separately from the affine slit-lip argument.
  -- TODO: build the inner/outer radial tube charts explicitly and prove the `p.2 > 0` side moves
  -- toward the annulus interior for the corresponding circle branch.
  sorry

/-- Helper for Exercise 21: every regular interior parameter of the keyhole contour admits a local
boundary straightening chart for the slit annulus it bounds. -/
theorem exercise21Delta_exists_boundary_straightening_at_regular_point
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ ((exercise21Delta r ε).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀)
    (hderiv :
      derivWithin ((exercise21Delta r ε).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ ≠ 0) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (exercise21NegativeWedgeAnnulus r ε)
        ((exercise21Delta r ε).toClosedPath.realCurve) t₀ δ := by
  -- Route correction: the breakpoint-exclusion step is already proved, so dispatch directly to
  -- the explicit branch chart package corresponding to the regular open branch containing `t₀`.
  rcases exercise21Delta_regular_parameter_mem_open_branch r ε hε hεr ht₀ hdiff with
    htupper | htinner | htlower | htouter
  · -- The upper slit lip uses the affine strip chart for the ray branches.
    exact exercise21_ray_branch_exists_boundary_chart
      r ε hε hεr ht₀ (Or.inl htupper) hdiff hderiv
  · -- The inner circular branch uses the radial chart package.
    exact exercise21_circle_branch_exists_boundary_chart
      r ε hε hεr ht₀ (Or.inl htinner) hdiff hderiv
  · -- The lower slit lip reuses the same affine strip chart with the lower-branch data.
    exact exercise21_ray_branch_exists_boundary_chart
      r ε hε hεr ht₀ (Or.inr htlower) hdiff hderiv
  · -- The outer circular branch reuses the radial chart package for the surviving outer arc.
    exact exercise21_circle_branch_exists_boundary_chart
      r ε hε hεr ht₀ (Or.inr htouter) hdiff hderiv

/-- Helper for Exercise 21: the keyhole contour should be the oriented boundary of the explicit
slit annulus. -/
theorem exercise21Delta_isOrientedBoundaryOf_negative_wedge_annulus
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    IsOrientedBoundaryOf (exercise21NegativeWedgeAnnulus r ε)
      (fun _ : Unit ↦ (exercise21Delta r ε).toClosedPath) := by
  classical
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (exercise21Delta r ε).toClosedPath
  change IsOrientedBoundaryOf (exercise21NegativeWedgeAnnulus r ε) Γ
  -- Route correction: the remaining geometric blocker is now isolated to the actual oriented-
  -- boundary witness for the explicit slit annulus. The pole-ball geometry is proved separately.
  refine
    { isCompact := ?_
      piecewiseDifferentiable := ?_
      simple_loops := ?_
      pairwiseDisjoint_ranges := ?_
      iUnion_range_eq_frontier := ?_
      exists_boundary_chart_at_regular_point := ?_ }
  · -- The slit annulus is already packaged as a compact set.
    simpa using isCompact_exercise21NegativeWedgeAnnulus r ε
  · rintro ⟨⟩
    -- The singleton boundary loop inherits the explicit piecewise differentiability of `δ(r, ε)`.
    simpa [Γ, Path.toClosedPath] using exercise21Delta_isPiecewiseDifferentiable r ε
  · rintro ⟨⟩ s t hst
    -- Delegate loop simplicity to the explicit dispatcher proved from the four branch models.
    exact exercise21Delta_simple_eq_or_endpoints r ε hε hεr hst
  · intro i j hij
    -- A singleton family has pairwise disjoint ranges for the trivial reason.
    exact (hij rfl).elim
  · have hboundary :
        (⋃ i : Unit, Set.range ((Γ i).toPath)) = Set.range (exercise21Delta r ε) := by
      -- First collapse the singleton indexed family back to the explicit contour range.
      simpa [Γ] using exercise21Delta_singleton_iUnion_range r ε
    -- Rewrite the singleton family range back to the explicit contour frontier.
    simpa [exercise21NegativeWedgeAnnulus_frontier_eq_range r ε hε hεr] using hboundary
  · rintro ⟨⟩ t₀ ht₀ hdiff hderiv
    -- Delegate the regular-point chart to the branch-local straightening theorem.
    exact exercise21Delta_exists_boundary_straightening_at_regular_point
      r ε hε hεr ht₀ hdiff hderiv

/-- Helper for Exercise 21: an open ball contained in `K` gives a smaller concentric closed ball
contained in `interior K`. This keeps the pole-ball packaging separate from the boundary proof. -/
lemma exercise21_closedBall_subset_interior_of_ball_subset
    {K : Set ℂ} {c : ℂ} {ρ R : ℝ}
    (hρR : ρ < R) (hball : Metric.ball c R ⊆ K) :
    Metric.closedBall c ρ ⊆ interior K := by
  -- Upgrade the open-ball inclusion to an interior inclusion, then shrink the radius once.
  have hsubset : Metric.ball c R ⊆ interior K :=
    (IsOpen.subset_interior_iff Metric.isOpen_ball).2 hball
  exact (Metric.closedBall_subset_ball hρR).trans hsubset

/-- Helper for Exercise 21: a point within distance `ρ` of a center `c` has norm within `ρ` of
`‖c‖`. This is the annulus-control bridge for the explicit residue balls. -/
lemma exercise21_norm_bounds_of_dist_lt {z c : ℂ} {ρ : ℝ}
    (hz : dist z c < ρ) :
    ‖c‖ - ρ < ‖z‖ ∧ ‖z‖ < ‖c‖ + ρ := by
  -- Convert the distance estimate into the standard norm-difference estimate.
  have hdist : ‖z - c‖ < ρ := by
    simpa [dist_eq_norm] using hz
  have hclose : |‖z‖ - ‖c‖| < ρ :=
    lt_of_le_of_lt (abs_norm_sub_norm_le z c) hdist
  constructor
  · linarith [(abs_lt.mp hclose).1]
  · linarith [(abs_lt.mp hclose).2]

/-- Helper for Exercise 21: distance control implies control of the real coordinate. -/
lemma exercise21_re_close_of_dist_lt {z c : ℂ} {ρ : ℝ}
    (hz : dist z c < ρ) :
    |z.re - c.re| < ρ := by
  -- The real part is bounded by the complex norm of the displacement.
  have hdist : ‖z - c‖ < ρ := by
    simpa [dist_eq_norm] using hz
  exact lt_of_le_of_lt (by simpa [sub_re] using abs_re_le_norm (z - c)) hdist

/-- Helper for Exercise 21: distance control implies control of the imaginary coordinate. -/
lemma exercise21_im_close_of_dist_lt {z c : ℂ} {ρ : ℝ}
    (hz : dist z c < ρ) :
    |z.im - c.im| < ρ := by
  -- The imaginary part is bounded by the same displacement norm.
  have hdist : ‖z - c‖ < ρ := by
    simpa [dist_eq_norm] using hz
  exact lt_of_le_of_lt (by simpa [sub_im] using abs_im_le_norm (z - c)) hdist

/-- Helper for Exercise 21: a small ball around `1` stays inside the slit annulus because its
points keep positive real part and stay between the two radial bounds. -/
lemma exercise21_ball_one_subset_negative_wedge_annulus
    (r ε ρ : ℝ)
    (hρε : ρ ≤ 1 - ε) (hρr : ρ ≤ r - 1) (hρone : ρ ≤ 1) :
    Metric.ball (1 : ℂ) ρ ⊆ exercise21NegativeWedgeAnnulus r ε := by
  intro z hz
  have hnorm := exercise21_norm_bounds_of_dist_lt (c := (1 : ℂ)) hz
  have hre_close : |z.re - 1| < ρ :=
    exercise21_re_close_of_dist_lt (c := (1 : ℂ)) hz
  have hεnorm : ε < ‖z‖ := by
    have : 1 - ρ < ‖z‖ := by
      simpa using hnorm.1
    linarith
  have hnormr : ‖z‖ < r := by
    have : ‖z‖ < 1 + ρ := by
      simpa using hnorm.2
    linarith
  refine ⟨⟨le_of_lt hεnorm, le_of_lt hnormr⟩, ?_⟩
  -- Positive real part keeps the whole ball away from the removed negative wedge.
  intro hwedge
  have hre_pos : 0 < z.re := by
    have hre_lt : -ρ < z.re - 1 := (abs_lt.mp hre_close).1
    linarith
  linarith [hwedge.1, hre_pos]

/-- Helper for Exercise 21: a small ball around `a i` stays inside the slit annulus. The norm
bounds keep the ball in the annulus, while the positive imaginary part keeps it out of the slit. -/
lemma exercise21_ball_pos_imag_subset_negative_wedge_annulus
    (a r ε ρ : ℝ) (ha : 0 < a) (hεa : ε < a) (har : a < r)
    (hρε : ρ ≤ a - ε) (hρr : ρ ≤ r - a) (hρa : ρ ≤ a / 2) :
    Metric.ball ((a : ℂ) * Complex.I) ρ ⊆ exercise21NegativeWedgeAnnulus r ε := by
  intro z hz
  have hnorm := exercise21_norm_bounds_of_dist_lt (c := (a : ℂ) * Complex.I) hz
  have hre_close : |z.re| < ρ := by
    simpa using exercise21_re_close_of_dist_lt (c := (a : ℂ) * Complex.I) hz
  have him_close : |z.im - a| < ρ := by
    simpa using exercise21_im_close_of_dist_lt (c := (a : ℂ) * Complex.I) hz
  have hεnorm : ε < ‖z‖ := by
    have : a - ρ < ‖z‖ := by
      simpa [abs_of_nonneg ha.le, norm_mul, Complex.norm_I] using hnorm.1
    linarith
  have hnormr : ‖z‖ < r := by
    have : ‖z‖ < a + ρ := by
      simpa [abs_of_nonneg ha.le, norm_mul, Complex.norm_I] using hnorm.2
    linarith
  refine ⟨⟨le_of_lt hεnorm, le_of_lt hnormr⟩, ?_⟩
  intro hwedge
  have hr : 0 < r := lt_trans ha har
  have hεr : ε < r := lt_trans hεa har
  have hratio : ε / r < 1 := (div_lt_one hr).2 hεr
  have him_gt_half : a / 2 < z.im := by
    have hlower : -ρ < z.im - a := (abs_lt.mp him_close).1
    linarith
  have him_abs : ρ < |z.im| := by
    have hz_im_pos : 0 < z.im := lt_trans (show 0 < a / 2 by positivity) him_gt_half
    have hρlt : ρ < z.im := by
      linarith
    simpa [abs_of_pos hz_im_pos] using hρlt
  have hneg_re_nonneg : 0 ≤ -z.re := by linarith [hwedge.1]
  have hneg_re_lt : -z.re < ρ := by
    have hleft : -ρ < z.re := (abs_lt.mp hre_close).1
    linarith
  have hwedge_small : (ε / r) * (-z.re) < ρ := by
    nlinarith
  linarith [hwedge.2, him_abs, hwedge_small]

/-- Helper for Exercise 21: the companion ball around `-a i` also stays inside the slit annulus.
Here the negative imaginary part keeps the ball away from the removed wedge. -/
lemma exercise21_ball_neg_imag_subset_negative_wedge_annulus
    (a r ε ρ : ℝ) (ha : 0 < a) (hεa : ε < a) (har : a < r)
    (hρε : ρ ≤ a - ε) (hρr : ρ ≤ r - a) (hρa : ρ ≤ a / 2) :
    Metric.ball (-((a : ℂ) * Complex.I)) ρ ⊆ exercise21NegativeWedgeAnnulus r ε := by
  intro z hz
  have hnorm := exercise21_norm_bounds_of_dist_lt (c := -((a : ℂ) * Complex.I)) hz
  have hre_close : |z.re| < ρ := by
    simpa using exercise21_re_close_of_dist_lt (c := -((a : ℂ) * Complex.I)) hz
  have him_close : |z.im + a| < ρ := by
    simpa using exercise21_im_close_of_dist_lt (c := -((a : ℂ) * Complex.I)) hz
  have hεnorm : ε < ‖z‖ := by
    have : a - ρ < ‖z‖ := by
      simpa [abs_of_nonneg ha.le, norm_mul, Complex.norm_I] using hnorm.1
    linarith
  have hnormr : ‖z‖ < r := by
    have : ‖z‖ < a + ρ := by
      simpa [abs_of_nonneg ha.le, norm_mul, Complex.norm_I] using hnorm.2
    linarith
  refine ⟨⟨le_of_lt hεnorm, le_of_lt hnormr⟩, ?_⟩
  intro hwedge
  have hr : 0 < r := lt_trans ha har
  have hεr : ε < r := lt_trans hεa har
  have hratio : ε / r < 1 := (div_lt_one hr).2 hεr
  have him_lt_half : z.im < -(a / 2) := by
    have hupper : z.im + a < ρ := (abs_lt.mp him_close).2
    linarith
  have him_abs : ρ < |z.im| := by
    have hz_im_neg : z.im < 0 := lt_trans him_lt_half (by linarith)
    have : ρ < -z.im := by linarith
    simpa [abs_of_neg hz_im_neg] using this
  have hneg_re_nonneg : 0 ≤ -z.re := by linarith [hwedge.1]
  have hneg_re_lt : -z.re < ρ := by
    have hleft : -ρ < z.re := (abs_lt.mp hre_close).1
    linarith
  have hwedge_small : (ε / r) * (-z.re) < ρ := by
    nlinarith
  linarith [hwedge.2, him_abs, hwedge_small]

/-- Helper for Exercise 21: explicit residue-circle radii around `1`, `a i`, and `-a i` stay
inside the slit annulus and avoid the other poles. -/
lemma exercise21_negative_wedge_annulus_pole_ball_data
    (a r ε : ℝ) (hε : 0 < ε) (hεa : ε < a) (har : a < r) (hε1 : ε < 1) (h1r : 1 < r) :
    let K := exercise21NegativeWedgeAnnulus r ε
    ∃ ρ₁ ρ₂ ρ₃ : ℝ,
      K ⊆ Complex.slitPlane ∧
      0 < ρ₁ ∧
        Metric.closedBall (1 : ℂ) ρ₁ ⊆ interior K ∧
        Metric.closedBall (1 : ℂ) ρ₁ ⊆
          Complex.slitPlane \ ({(a : ℂ) * Complex.I, -((a : ℂ) * Complex.I)} : Set ℂ) ∧
      0 < ρ₂ ∧
        Metric.closedBall ((a : ℂ) * Complex.I) ρ₂ ⊆ interior K ∧
        Metric.closedBall ((a : ℂ) * Complex.I) ρ₂ ⊆
          Complex.slitPlane \ ({(1 : ℂ), -((a : ℂ) * Complex.I)} : Set ℂ) ∧
      0 < ρ₃ ∧
        Metric.closedBall (-((a : ℂ) * Complex.I)) ρ₃ ⊆ interior K ∧
        Metric.closedBall (-((a : ℂ) * Complex.I)) ρ₃ ⊆
          Complex.slitPlane \ ({(1 : ℂ), (a : ℂ) * Complex.I} : Set ℂ) := by
  let K := exercise21NegativeWedgeAnnulus r ε
  let ρ₁ : ℝ := min (1 - ε) (min (r - 1) 1) / 4
  let ρ₂ : ℝ := min (a - ε) (min (r - a) a) / 4
  let ρ₃ : ℝ := ρ₂
  have ha : 0 < a := lt_trans hε hεa
  have hr : 0 < r := lt_trans ha har
  have hK_subset : K ⊆ Complex.slitPlane :=
    exercise21NegativeWedgeAnnulus_subset_slitPlane r ε hε (lt_trans hεa har)
  have hρ₁_pos : 0 < ρ₁ := by
    dsimp [ρ₁]
    refine div_pos ?_ (by norm_num)
    refine lt_min (sub_pos.mpr hε1) ?_
    exact lt_min (sub_pos.mpr h1r) zero_lt_one
  have hρ₂_pos : 0 < ρ₂ := by
    dsimp [ρ₂]
    refine div_pos ?_ (by norm_num)
    refine lt_min (sub_pos.mpr hεa) ?_
    exact lt_min (sub_pos.mpr har) ha
  have hρ₁_lt : ρ₁ < min (1 - ε) (min (r - 1) 1) := by
    dsimp [ρ₁]
    have hpos : 0 < min (1 - ε) (min (r - 1) 1) := by
      refine lt_min (sub_pos.mpr hε1) ?_
      exact lt_min (sub_pos.mpr h1r) zero_lt_one
    nlinarith
  have hρ₂_lt : ρ₂ < min (a - ε) (min (r - a) a) := by
    dsimp [ρ₂]
    have hpos : 0 < min (a - ε) (min (r - a) a) := by
      refine lt_min (sub_pos.mpr hεa) ?_
      exact lt_min (sub_pos.mpr har) ha
    nlinarith
  have hρ₁_lt_one : ρ₁ < 1 := by
    have hmin : min (1 - ε) (min (r - 1) 1) ≤ 1 := by
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    exact lt_of_lt_of_le hρ₁_lt hmin
  have hρ₂_lt_a : ρ₂ < a := by
    have hmin : min (a - ε) (min (r - a) a) ≤ a := by
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    exact lt_of_lt_of_le hρ₂_lt hmin
  have hball₁ :
      Metric.ball (1 : ℂ) (2 * ρ₁) ⊆ K := by
    -- The quarter-minimum radius leaves room both for the annulus bounds and for `re > 0`.
    refine exercise21_ball_one_subset_negative_wedge_annulus r ε (2 * ρ₁) ?_ ?_ ?_
    · have hhalf : 2 * ρ₁ = min (1 - ε) (min (r - 1) 1) / 2 := by
        dsimp [ρ₁]
        ring_nf
      rw [hhalf]
      have hmin : min (1 - ε) (min (r - 1) 1) / 2 ≤ 1 - ε := by
        have := min_le_left (1 - ε) (min (r - 1) 1)
        nlinarith
      exact hmin
    · have hhalf : 2 * ρ₁ = min (1 - ε) (min (r - 1) 1) / 2 := by
        dsimp [ρ₁]
        ring_nf
      rw [hhalf]
      have hmin : min (1 - ε) (min (r - 1) 1) / 2 ≤ r - 1 := by
        have h' := min_le_right (1 - ε) (min (r - 1) 1)
        have h'' := min_le_left (r - 1) 1
        nlinarith
      exact hmin
    · have hhalf : 2 * ρ₁ = min (1 - ε) (min (r - 1) 1) / 2 := by
        dsimp [ρ₁]
        ring_nf
      rw [hhalf]
      have hmin : min (1 - ε) (min (r - 1) 1) / 2 ≤ 1 := by
        have h' := min_le_right (1 - ε) (min (r - 1) 1)
        have h'' := min_le_right (r - 1) 1
        nlinarith
      exact hmin
  have hball₂ :
      Metric.ball ((a : ℂ) * Complex.I) (2 * ρ₂) ⊆ K := by
    -- The same quarter-minimum radius keeps the imaginary poles inside the annulus and away from
    -- the slit because `|im z|` stays larger than `|re z|`.
    refine exercise21_ball_pos_imag_subset_negative_wedge_annulus a r ε (2 * ρ₂) ha hεa har ?_ ?_ ?_
    · have hhalf : 2 * ρ₂ = min (a - ε) (min (r - a) a) / 2 := by
        dsimp [ρ₂]
        ring_nf
      rw [hhalf]
      have hmin : min (a - ε) (min (r - a) a) / 2 ≤ a - ε := by
        have := min_le_left (a - ε) (min (r - a) a)
        nlinarith
      exact hmin
    · have hhalf : 2 * ρ₂ = min (a - ε) (min (r - a) a) / 2 := by
        dsimp [ρ₂]
        ring_nf
      rw [hhalf]
      have hmin : min (a - ε) (min (r - a) a) / 2 ≤ r - a := by
        have h' := min_le_right (a - ε) (min (r - a) a)
        have h'' := min_le_left (r - a) a
        nlinarith
      exact hmin
    · have hhalf : 2 * ρ₂ = min (a - ε) (min (r - a) a) / 2 := by
        dsimp [ρ₂]
        ring_nf
      rw [hhalf]
      have hmin : min (a - ε) (min (r - a) a) / 2 ≤ a / 2 := by
        have h' := min_le_right (a - ε) (min (r - a) a)
        have h'' := min_le_right (r - a) a
        nlinarith
      exact hmin
  have hball₃ :
      Metric.ball (-((a : ℂ) * Complex.I)) (2 * ρ₃) ⊆ K := by
    -- The lower imaginary pole uses the same radius and the same annulus estimate with `im < 0`.
    dsimp [ρ₃]
    refine exercise21_ball_neg_imag_subset_negative_wedge_annulus a r ε (2 * ρ₂) ha hεa har ?_ ?_ ?_
    · have hhalf : 2 * ρ₂ = min (a - ε) (min (r - a) a) / 2 := by
        dsimp [ρ₂]
        ring_nf
      rw [hhalf]
      have hmin : min (a - ε) (min (r - a) a) / 2 ≤ a - ε := by
        have := min_le_left (a - ε) (min (r - a) a)
        nlinarith
      exact hmin
    · have hhalf : 2 * ρ₂ = min (a - ε) (min (r - a) a) / 2 := by
        dsimp [ρ₂]
        ring_nf
      rw [hhalf]
      have hmin : min (a - ε) (min (r - a) a) / 2 ≤ r - a := by
        have h' := min_le_right (a - ε) (min (r - a) a)
        have h'' := min_le_left (r - a) a
        nlinarith
      exact hmin
    · have hhalf : 2 * ρ₂ = min (a - ε) (min (r - a) a) / 2 := by
        dsimp [ρ₂]
        ring_nf
      rw [hhalf]
      have hmin : min (a - ε) (min (r - a) a) / 2 ≤ a / 2 := by
        have h' := min_le_right (a - ε) (min (r - a) a)
        have h'' := min_le_right (r - a) a
        nlinarith
      exact hmin
  have hK₁ : Metric.closedBall (1 : ℂ) ρ₁ ⊆ interior K :=
    exercise21_closedBall_subset_interior_of_ball_subset
      (by nlinarith [hρ₁_pos]) hball₁
  have hK₂ : Metric.closedBall ((a : ℂ) * Complex.I) ρ₂ ⊆ interior K :=
    exercise21_closedBall_subset_interior_of_ball_subset
      (by nlinarith [hρ₂_pos]) hball₂
  have hK₃ : Metric.closedBall (-((a : ℂ) * Complex.I)) ρ₃ ⊆ interior K := by
    dsimp [ρ₃]
    exact exercise21_closedBall_subset_interior_of_ball_subset
      (by nlinarith [hρ₂_pos]) hball₃
  refine ⟨ρ₁, ρ₂, ρ₃, hK_subset, hρ₁_pos, hK₁, ?_, hρ₂_pos, hK₂, ?_, ?_, hK₃, ?_⟩
  · intro z hz
    refine ⟨hK_subset (interior_subset (hK₁ hz)), ?_⟩
    intro hzbad
    rcases hzbad with hzbad | hzbad
    · subst z
      have hdist : 1 ≤ dist (1 : ℂ) ((a : ℂ) * Complex.I) := by
        simpa [dist_eq_norm] using abs_re_le_norm ((1 : ℂ) - (a : ℂ) * Complex.I)
      have hmem : dist (1 : ℂ) ((a : ℂ) * Complex.I) ≤ ρ₁ := by
        simpa [Metric.mem_closedBall, dist_comm] using hz
      linarith
    · subst z
      have hdist : 1 ≤ dist (1 : ℂ) (-((a : ℂ) * Complex.I)) := by
        simpa [dist_eq_norm] using abs_re_le_norm ((1 : ℂ) - (-((a : ℂ) * Complex.I)))
      have hmem : dist (1 : ℂ) (-((a : ℂ) * Complex.I)) ≤ ρ₁ := by
        simpa [Metric.mem_closedBall, dist_comm] using hz
      linarith
  · intro z hz
    refine ⟨hK_subset (interior_subset (hK₂ hz)), ?_⟩
    intro hzbad
    rcases hzbad with hzbad | hzbad
    · subst z
      have hdist : a ≤ dist ((a : ℂ) * Complex.I) (1 : ℂ) := by
        simpa [dist_eq_norm, abs_of_nonneg ha.le] using
          abs_im_le_norm (((a : ℂ) * Complex.I) - (1 : ℂ))
      have hmem : dist ((a : ℂ) * Complex.I) (1 : ℂ) ≤ ρ₂ := by
        simpa [Metric.mem_closedBall, dist_comm] using hz
      linarith
    · subst z
      have hdist : a ≤ dist ((a : ℂ) * Complex.I) (-((a : ℂ) * Complex.I)) := by
        have : a + a ≤ dist ((a : ℂ) * Complex.I) (-((a : ℂ) * Complex.I)) := by
          simpa [dist_eq_norm, abs_of_nonneg (show 0 ≤ a + a by positivity)] using
            abs_im_le_norm (((a : ℂ) * Complex.I) - (-((a : ℂ) * Complex.I)))
        linarith
      have hmem : dist ((a : ℂ) * Complex.I) (-((a : ℂ) * Complex.I)) ≤ ρ₂ := by
        simpa [Metric.mem_closedBall, dist_comm] using hz
      linarith
  · simpa [ρ₃] using hρ₂_pos
  · intro z hz
    refine ⟨hK_subset (interior_subset (hK₃ hz)), ?_⟩
    intro hzbad
    rcases hzbad with hzbad | hzbad
    · subst z
      have hdist : a ≤ dist (-((a : ℂ) * Complex.I)) (1 : ℂ) := by
        simpa [dist_eq_norm, abs_of_neg (show -a < 0 by linarith)] using
          abs_im_le_norm ((-((a : ℂ) * Complex.I)) - (1 : ℂ))
      have hmem : dist (-((a : ℂ) * Complex.I)) (1 : ℂ) ≤ ρ₃ := by
        simpa [Metric.mem_closedBall, ρ₃, dist_comm] using hz
      linarith
    · subst z
      have hdist : a ≤ dist (-((a : ℂ) * Complex.I)) ((a : ℂ) * Complex.I) := by
        have : a + a ≤ dist (-((a : ℂ) * Complex.I)) ((a : ℂ) * Complex.I) := by
          have hneg : -a - a < 0 := by linarith
          simpa [dist_eq_norm, two_mul, abs_of_neg hneg] using
            abs_im_le_norm ((-((a : ℂ) * Complex.I)) - ((a : ℂ) * Complex.I))
        linarith
      have hmem : dist (-((a : ℂ) * Complex.I)) ((a : ℂ) * Complex.I) ≤ ρ₃ := by
        simpa [Metric.mem_closedBall, ρ₃, dist_comm] using hz
      linarith

/-- Helper for Exercise 21: the explicit keyhole contour bounds a compact slit-annulus region that
contains the three poles together with small residue circles around them. -/
theorem exercise21Delta_orientedBoundary_residue_data
    (a r ε : ℝ) (hε : 0 < ε) (hεa : ε < a) (har : a < r) (hε1 : ε < 1) (h1r : 1 < r) :
    ∃ K : Set ℂ, ∃ ρ₁ ρ₂ ρ₃ : ℝ,
      IsOrientedBoundaryOf K (fun _ : Unit ↦ (exercise21Delta r ε).toClosedPath) ∧
      K ⊆ Complex.slitPlane ∧
      0 < ρ₁ ∧
        Metric.closedBall (1 : ℂ) ρ₁ ⊆ interior K ∧
        Metric.closedBall (1 : ℂ) ρ₁ ⊆
          Complex.slitPlane \ ({(a : ℂ) * Complex.I, -((a : ℂ) * Complex.I)} : Set ℂ) ∧
      0 < ρ₂ ∧
        Metric.closedBall ((a : ℂ) * Complex.I) ρ₂ ⊆ interior K ∧
        Metric.closedBall ((a : ℂ) * Complex.I) ρ₂ ⊆
          Complex.slitPlane \ ({(1 : ℂ), -((a : ℂ) * Complex.I)} : Set ℂ) ∧
      0 < ρ₃ ∧
        Metric.closedBall (-((a : ℂ) * Complex.I)) ρ₃ ⊆ interior K ∧
        Metric.closedBall (-((a : ℂ) * Complex.I)) ρ₃ ⊆
          Complex.slitPlane \ ({(1 : ℂ), (a : ℂ) * Complex.I} : Set ℂ) := by
  let K : Set ℂ := exercise21NegativeWedgeAnnulus r ε
  obtain ⟨ρ₁, ρ₂, ρ₃, hK_subset, hρ₁, hK₁, hD₁, hρ₂, hK₂, hD₂, hρ₃, hK₃, hD₃⟩ :=
    exercise21_negative_wedge_annulus_pole_ball_data a r ε hε hεa har hε1 h1r
  -- The explicit residue-circle data is now packaged separately from the single remaining
  -- geometric boundary witness for the slit annulus.
  refine ⟨K, ρ₁, ρ₂, ρ₃, ?_, hK_subset, hρ₁, hK₁, hD₁, hρ₂, hK₂, hD₂, hρ₃, hK₃, hD₃⟩
  exact exercise21Delta_isOrientedBoundaryOf_negative_wedge_annulus r ε hε (lt_trans hεa har)

/-- Helper for Exercise 21: the three explicit local residue circles can be upgraded to isolated
residue circles because each owner closed ball already avoids the other two poles and the
integrand is holomorphic on the punctured slit-plane away from the pole finset. -/
lemma exercise21_isolatedLocalResidueCircle_data
    {K : Set ℂ} (a : ℝ) (ha : 0 < a) {ρ₁ ρ₂ ρ₃ : ℝ}
    (hρ₁ : 0 < ρ₁)
    (hK₁ : Metric.closedBall (1 : ℂ) ρ₁ ⊆ interior K)
    (hD₁ :
      Metric.closedBall (1 : ℂ) ρ₁ ⊆
        Complex.slitPlane \ ({(a : ℂ) * Complex.I, -((a : ℂ) * Complex.I)} : Set ℂ))
    (hρ₂ : 0 < ρ₂)
    (hK₂ : Metric.closedBall ((a : ℂ) * Complex.I) ρ₂ ⊆ interior K)
    (hD₂ :
      Metric.closedBall ((a : ℂ) * Complex.I) ρ₂ ⊆
        Complex.slitPlane \ ({(1 : ℂ), -((a : ℂ) * Complex.I)} : Set ℂ))
    (hρ₃ : 0 < ρ₃)
    (hK₃ : Metric.closedBall (-((a : ℂ) * Complex.I)) ρ₃ ⊆ interior K)
    (hD₃ :
      Metric.closedBall (-((a : ℂ) * Complex.I)) ρ₃ ⊆
        Complex.slitPlane \ ({(1 : ℂ), (a : ℂ) * Complex.I} : Set ℂ)) :
    ∀ z ∈ exercise21PoleFinset a,
      IsolatedLocalResidueCircle
        K
        Complex.slitPlane
        (exercise21PoleFinset a)
        (fun w ↦ (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹))
        z
        (exercise21Residue a z) := by
  intro z hz
  rcases
      exercise21_localResidueCircle_data
        (K := K) a ha hρ₁ hK₁ hD₁ hρ₂ hK₂ hD₂ hρ₃ hK₃ hD₃ z hz with
    ⟨ρ, hρ, hK, hD, hcircle⟩
  have havoid :
      ∀ w ∈ exercise21PoleFinset a, w ≠ z → w ∉ Metric.closedBall z ρ := by
    intro w hw hwz hwBall
    -- Route correction: reuse the exact owner ball from `LocalResidueCircle` and only add the
    -- missing finset-avoidance clause required by `IsolatedLocalResidueCircle`.
    simp [exercise21PoleFinset] at hz hw
    rcases hz with rfl | rfl | rfl
    · rcases hw with rfl | rfl | rfl
      · exact hwz rfl
      · exact (hD hwBall).2 (by simp)
      · exact (hD hwBall).2 (by simp)
    · rcases hw with rfl | rfl | rfl
      · exact (hD hwBall).2 (by simp)
      · exact hwz rfl
      · exact (hD hwBall).2 (by simp)
    · rcases hw with rfl | rfl | rfl
      · exact (hD hwBall).2 (by simp)
      · exact (hD hwBall).2 (by simp)
      · exact hwz rfl
  refine ⟨ρ, hρ, hK, hD, havoid, ?_, hcircle⟩
  -- The punctured owner ball lies in the slit plane and avoids the whole pole finset.
  refine (exercise21_integrand_differentiableOn_slitPlane_off_poles_finset a).mono ?_
  intro w hw
  have hwClosed : w ∈ Metric.closedBall z ρ := Metric.ball_subset_closedBall hw.1
  refine ⟨(hD hwClosed).1, ?_⟩
  intro hwPole
  by_cases hwz : w = z
  · exact hw.2 hwz
  · exact havoid w (by simpa using hwPole) hwz hwClosed

/-- Helper for Exercise 21: the positive-imaginary residue coefficient can be rewritten in the
normalized inverse-product form produced by the residue theorem. -/
lemma exercise21_pos_imag_coeff_normalized (a : ℝ) :
    -((Complex.log ((a : ℂ) * Complex.I))⁻¹ * (Complex.I * (((a : ℂ)⁻¹) * (2 : ℂ)⁻¹))) =
      1 / ((2 * (a : ℂ) * Complex.I) * Complex.log ((a : ℂ) * Complex.I)) := by
  -- Reverse the inverses in the commutative field `ℂ` and simplify `I⁻¹ = -I`.
  simp [div_eq_mul_inv, mul_left_comm, mul_comm, mul_inv_rev]

/-- Helper for Exercise 21: the negative-imaginary residue coefficient has the analogous
normalized inverse-product form. -/
lemma exercise21_neg_imag_coeff_normalized (a : ℝ) :
    (Complex.log (-((a : ℂ) * Complex.I)))⁻¹ * (Complex.I * (((a : ℂ)⁻¹) * (2 : ℂ)⁻¹)) =
      -1 / ((2 * (a : ℂ) * Complex.I) * Complex.log (-((a : ℂ) * Complex.I))) := by
  -- The same inverse-reversal identity applies at the pole `-a i`.
  simp [div_eq_mul_inv, mul_left_comm, mul_comm, mul_inv_rev]

/-- Helper for Exercise 21: summing the residues over the three-pole `Finset` gives the normalized
expression returned by the oriented-boundary residue theorem. -/
lemma exercise21PoleFinset_sum_residue_normalized (a : ℝ) (ha : 0 < a) :
    Finset.sum (exercise21PoleFinset a) (exercise21Residue a) =
      ((1 + (a : ℂ) ^ 2)⁻¹ +
        -((Complex.log ((a : ℂ) * Complex.I))⁻¹ *
            (Complex.I * (((a : ℂ)⁻¹) * (2 : ℂ)⁻¹))) +
        (Complex.log (-((a : ℂ) * Complex.I)))⁻¹ *
          (Complex.I * (((a : ℂ)⁻¹) * (2 : ℂ)⁻¹))) := by
  have h_ai_ne_one : (a : ℂ) * Complex.I ≠ (1 : ℂ) := by
    -- The point `a i` has nonzero imaginary part, so it cannot equal `1`.
    intro h
    have him := congrArg Complex.im h
    simpa [ha.ne'] using him
  have h_neg_ai_ne_one : -((a : ℂ) * Complex.I) ≠ (1 : ℂ) := by
    -- The point `-a i` also has nonzero imaginary part.
    intro h
    have him := congrArg Complex.im h
    simpa [ha.ne'] using him
  have h_ai_ne_neg_ai : (a : ℂ) * Complex.I ≠ -((a : ℂ) * Complex.I) := by
    -- Equality of the two imaginary poles would force `a = 0`.
    intro h
    have him := congrArg Complex.im h
    have : a = -a := by simpa using him
    linarith
  have h_neg_ai_ne_ai : -((a : ℂ) * Complex.I) ≠ (a : ℂ) * Complex.I := by
    intro h
    exact h_ai_ne_neg_ai h.symm
  rw [exercise21PoleFinset, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · -- Evaluate the residue selector at the three actual poles.
    simp [exercise21Residue, exercise21RealPoleCoeff, exercise21PosImagPoleCoeff,
      exercise21NegImagPoleCoeff, h_ai_ne_one, h_neg_ai_ne_one, h_neg_ai_ne_ai]
    rw [← exercise21_neg_imag_coeff_normalized]
    simp [add_assoc]
  · simp [h_ai_ne_neg_ai]
  · intro h
    simp at h
    rcases h with h | h
    · exact h_ai_ne_one h.symm
    · exact h_neg_ai_ne_one h.symm

/-- Exercise 21 (1): if `0 < ε < a < r` and `ε < 1 < r`, so the keyhole contour `δ(r, ε)`
encloses the poles at `z = 1` and `z = ± a i`, then the integral of
`z ↦ 1 / (((z^2 + a^2) log z))` equals the sum of those residues, using the principal branch of
`Complex.log`. -/
theorem contourIntegral_exercise21_delta
    (a r ε : ℝ) (hε : 0 < ε) (hεa : ε < a) (har : a < r) (hε1 : ε < 1) (h1r : 1 < r) :
    (∫ᶜ z in exercise21Delta r ε,
        (((fun z ↦ ((z ^ 2 + (a : ℂ) ^ 2) * Complex.log z)⁻¹) dz) z)) /
      (2 * Real.pi * Complex.I : ℂ) =
        1 / ((1 : ℂ) + (a : ℂ) ^ 2) +
          1 / ((2 * (a : ℂ) * Complex.I) * Complex.log ((a : ℂ) * Complex.I)) -
            1 / ((2 * (a : ℂ) * Complex.I) * Complex.log (-((a : ℂ) * Complex.I))) := by
  have ha : 0 < a := lt_trans hε hεa
  obtain ⟨K, ρ₁, ρ₂, ρ₃, hΓ, hKD, hρ₁, hK₁, hD₁, hρ₂, hK₂, hD₂, hρ₃, hK₃, hD₃⟩ :=
    exercise21Delta_orientedBoundary_residue_data a r ε hε hεa har hε1 h1r
  have hhol :
      DifferentiableOn ℂ
        (fun w ↦ (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹))
        (Complex.slitPlane \ (↑(exercise21PoleFinset a) : Set ℂ)) :=
    exercise21_integrand_differentiableOn_slitPlane_off_poles_finset a
  have hres :
      ∀ z ∈ exercise21PoleFinset a,
        IsolatedLocalResidueCircle
          K
          Complex.slitPlane
          (exercise21PoleFinset a)
          (fun w ↦ (((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹))
          z
          (exercise21Residue a z) :=
    exercise21_isolatedLocalResidueCircle_data
      (K := K) a ha hρ₁ hK₁ hD₁ hρ₂ hK₂ hD₂ hρ₃ hK₃ hD₃
  have hboundary :
      ∑ i : Unit,
        ∫ᶜ z in ((fun _ : Unit ↦ (exercise21Delta r ε).toClosedPath) i).toPath,
          (((fun w ↦ ((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹) dz) z) =
        (2 * Real.pi * Complex.I : ℂ) *
          Finset.sum (exercise21PoleFinset a) (exercise21Residue a) := by
    -- Apply the oriented-boundary residue theorem to the singleton family carrying `δ(r, ε)`.
    exact orientedBoundary_sum_curveIntegral_eq_two_pi_I_mul_sum_residue
      (Γ := fun _ : Unit ↦ (exercise21Delta r ε).toClosedPath)
      (K := K) (D := Complex.slitPlane)
      (f := fun w ↦ ((w ^ 2 + (a : ℂ) ^ 2) * Complex.log w)⁻¹)
      (s := exercise21PoleFinset a) (residue := exercise21Residue a)
      hΓ hKD Complex.isOpen_slitPlane hhol hres
  have htwo_pi_I_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    norm_num [Real.pi_ne_zero]
  have hnormalized :=
    congrArg (fun w : ℂ ↦ w / (2 * Real.pi * Complex.I : ℂ)) hboundary
  -- Collapse the singleton contour sum and rewrite the residue sum into the normalized formula.
  rw [exercise21PoleFinset_sum_residue_normalized a ha] at hnormalized
  simpa [div_eq_mul_inv, htwo_pi_I_ne, mul_assoc, mul_left_comm, mul_comm,
    exercise21_pos_imag_coeff_normalized, exercise21_neg_imag_coeff_normalized] using
    hnormalized

theorem integral_inv_quadratic_log_sq_add_pi_sq
    (a : ℝ) (ha : 0 < a) :
    ∫ x in Set.Ioi (0 : ℝ), 1 / ((x ^ 2 + a ^ 2) * ((Real.log x) ^ 2 + Real.pi ^ 2)) ∂volume =
      Real.pi / (2 * a * ((Real.log a) ^ 2 + Real.pi ^ 2 / 4)) - 1 / (1 + a ^ 2) := by
  -- TODO: once `contourIntegral_exercise21_delta` is available, specialize to `ε = R⁻¹`,
  -- decompose the contour into the two slit lips and the two circular arcs, rewrite the lip sum
  -- through the exact finite-`R` kernel, show the arc terms vanish, and then pass to the
  -- improper real integral using the residue simplification `exercise21_residue_sum_eval`.
  sorry
