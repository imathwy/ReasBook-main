import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0001_Definition_II_1_extra_1»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0003_Lemma_II_1_extra_3»
import DifferentialForms_Cartan_1970.cartan.III.section11.«0003_Theorem_III_5_extra_2»

noncomputable section

open Complex MeasureTheory
open scoped Real unitInterval

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
          ring_nf
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
              apply Complex.equivRealProdCLM.injective
              simpa using hcurve
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
  apply Complex.equivRealProdCLM.injective
  simpa using exercise21Delta_realCurve_eq_on_inner_arc r ε ht

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
              apply Complex.equivRealProdCLM.injective
              simpa using hcurve
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
  apply Complex.equivRealProdCLM.injective
  simpa using exercise21Delta_realCurve_eq_on_outer_arc r ε ht

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
