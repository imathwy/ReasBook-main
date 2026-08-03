module

import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Topology.Homotopy.Equiv
public import Topology_Munkres_2000.Book.Definition_53_5.FigureEight
public import Topology_Munkres_2000.Book.Example_58_3.PlaneModels

public section

noncomputable section

open scoped ContinuousMap
open scoped ComplexConjugate

/-- The loop around the left cycle of the theta space, before restricting its codomain. -/
private def leftThetaLoop (z : Circle) : ℂ :=
  let w := Complex.I * (z : ℂ)
  if w.re ≤ 0 then w else Complex.I * w.im

/-- The loop around the right cycle of the theta space, before restricting its codomain. -/
private def rightThetaLoop (z : Circle) : ℂ :=
  let w := Complex.I * (z : ℂ)
  if 0 ≤ w.re then w else Complex.I * w.im

/-- Helper for Exercise 58.4: the left cycle parameterization is continuous. -/
private theorem continuous_leftThetaLoop : Continuous leftThetaLoop := by
  -- The circular and diameter formulas agree where the rotated real part is zero.
  have hw : Continuous fun z : Circle ↦ Complex.I * (z : ℂ) := by
    fun_prop
  have him : Continuous fun z : Circle ↦
      Complex.I * (Complex.I * (z : ℂ)).im := by
    fun_prop
  exact Continuous.if_le hw him (Complex.continuous_re.comp hw) continuous_const fun z hz ↦ by
    apply Complex.ext
    · simpa using hz
    · simp

/-- Helper for Exercise 58.4: the right cycle parameterization is continuous. -/
private theorem continuous_rightThetaLoop : Continuous rightThetaLoop := by
  -- The same boundary calculation pastes the right semicircle to the diameter.
  have hw : Continuous fun z : Circle ↦ Complex.I * (z : ℂ) := by
    fun_prop
  have him : Continuous fun z : Circle ↦
      Complex.I * (Complex.I * (z : ℂ)).im := by
    fun_prop
  exact Continuous.if_le hw him continuous_const (Complex.continuous_re.comp hw) fun z hz ↦ by
    apply Complex.ext
    · simpa using hz.symm
    · simp

/-- The pointwise formula folding the two circles of the figure eight onto the two cycles of
the theta space. -/
private def figureEightToThetaRaw (p : FigureEight) : ℂ :=
  @ite ℂ (p.1.2 = 1) (Classical.propDecidable (p.1.2 = 1))
    (leftThetaLoop p.1.1) (rightThetaLoop p.1.2)

/-- The folding formula lands in the theta space. -/
private theorem figureEightToThetaRaw_mem (p : FigureEight) :
    ‖figureEightToThetaRaw p‖ = 1 ∨
      ((figureEightToThetaRaw p).re = 0 ∧
        (figureEightToThetaRaw p).im ∈ Set.Icc (-1 : ℝ) 1) := by
  -- On either coordinate circle, rotation by `I` stays on the unit circle.
  by_cases hp : p.1.2 = 1
  · have hx : ‖(p.1.1 : ℂ)‖ = 1 := by
      simp [Submonoid.unitSphere]
    have hw : ‖Complex.I * (p.1.1 : ℂ)‖ = 1 := by
      simp [hx]
    rw [figureEightToThetaRaw, if_pos hp]
    simp only [leftThetaLoop]
    by_cases hbranch : (Complex.I * (p.1.1 : ℂ)).re ≤ 0
    · rw [if_pos hbranch]
      exact Or.inl hw
    · rw [if_neg hbranch]
      right
      constructor
      · simp
      · simpa using (abs_le.mp ((Complex.abs_im_le_norm _).trans_eq hw))
  · have hy : ‖(p.1.2 : ℂ)‖ = 1 := by
      simp [Submonoid.unitSphere]
    have hw : ‖Complex.I * (p.1.2 : ℂ)‖ = 1 := by
      simp [hy]
    rw [figureEightToThetaRaw, if_neg hp]
    simp only [rightThetaLoop]
    by_cases hbranch : 0 ≤ (Complex.I * (p.1.2 : ℂ)).re
    · rw [if_pos hbranch]
      exact Or.inl hw
    · rw [if_neg hbranch]
      right
      constructor
      · simp
      · simpa using (abs_le.mp ((Complex.abs_im_le_norm _).trans_eq hw))

/-- The underlying function of the map from the figure eight to the theta space. -/
private def figureEightToThetaFunction (p : FigureEight) : PlanarTheta :=
  ⟨figureEightToThetaRaw p,
    (PlanarTheta.mem_iff (figureEightToThetaRaw p)).2 (figureEightToThetaRaw_mem p)⟩

/-- The folding map from the figure eight to the theta space is continuous. -/
private theorem continuous_figureEightToThetaFunction :
    Continuous figureEightToThetaFunction := by
  -- Paste the two loop formulas over the two closed coordinate circles.
  let leftSide : Set FigureEight := {p | p.1.2 = 1}
  let rightSide : Set FigureEight := {p | p.1.1 = 1}
  have hleftClosed : IsClosed leftSide := by
    exact isClosed_eq (continuous_snd.comp continuous_subtype_val) continuous_const
  have hrightClosed : IsClosed rightSide := by
    exact isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const
  have hleft : ContinuousOn figureEightToThetaRaw leftSide := by
    refine (continuous_leftThetaLoop.comp
      (continuous_fst.comp continuous_subtype_val)).continuousOn.congr ?_
    intro p hp
    simp [leftSide] at hp
    simp [figureEightToThetaRaw, hp]
  have hright : ContinuousOn figureEightToThetaRaw rightSide := by
    refine (continuous_rightThetaLoop.comp
      (continuous_snd.comp continuous_subtype_val)).continuousOn.congr ?_
    intro p hp
    simp [rightSide] at hp
    by_cases hsecond : p.1.2 = 1
    · simp [figureEightToThetaRaw, hsecond, hp, leftThetaLoop, rightThetaLoop]
    · simp [figureEightToThetaRaw, hsecond]
  have hcover : leftSide ∪ rightSide = Set.univ := by
    ext p
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    exact (FigureEight.mem_iff p.1).1 p.2
  have hraw : Continuous figureEightToThetaRaw := by
    rw [← continuousOn_univ, ← hcover]
    exact hleft.union_of_isClosed hright hleftClosed hrightClosed
  -- Restricting the codomain to `PlanarTheta` preserves continuity.
  have hmem (p : FigureEight) : figureEightToThetaRaw p ∈ PlanarTheta.carrier :=
    (PlanarTheta.mem_iff _).2 (figureEightToThetaRaw_mem p)
  exact hraw.subtype_mk hmem

/-- The explicit continuous map folding the two circles of the figure eight onto the two
cycles of the theta space. -/
def figureEightToTheta : C(FigureEight, PlanarTheta) :=
  ⟨figureEightToThetaFunction, continuous_figureEightToThetaFunction⟩

/-- The pointwise formula collapsing the theta diameter and wrapping each semicircle around
one circle of the figure eight. -/
private def thetaToFigureEightRaw (z : PlanarTheta) : ℂ × ℂ :=
  if z.1.re = 0 then (1, 1)
  else if z.1.re < 0 then (-z.1 ^ 2, 1)
  else (1, -z.1 ^ 2)

/-- Helper for Exercise 58.4: a purely imaginary unit complex number has negative square one. -/
private theorem neg_sq_eq_one_of_re_eq_zero_norm_eq_one (z : ℂ)
    (hre : z.re = 0) (hnorm : ‖z‖ = 1) : -z ^ 2 = 1 := by
  -- The norm equation reduces to `z.im ^ 2 = 1`, after which the components agree.
  have hnormSq : Complex.normSq z = 1 := by
    rw [← Complex.sq_norm, hnorm]
    norm_num
  rw [Complex.normSq_apply, hre] at hnormSq
  have himSq : z.im * z.im = 1 := by
    simpa using hnormSq
  apply Complex.ext
  · simp [pow_two, Complex.mul_re, hre, himSq]
  · simp [pow_two, Complex.mul_im, hre]

/-- The first coordinate of the inverse formula lies on the unit circle. -/
private theorem thetaToFigureEightRaw_fst_mem (z : PlanarTheta) :
    (thetaToFigureEightRaw z).1 ∈ Submonoid.unitSphere ℂ := by
  -- Away from the diameter, theta membership forces `z` onto the unit circle.
  by_cases hzero : z.1.re = 0
  · simp [thetaToFigureEightRaw, hzero, Submonoid.unitSphere]
  · have hnorm : ‖(z.1 : ℂ)‖ = 1 := by
      rcases (PlanarTheta.mem_iff z.1).1 z.2 with hnorm | hdiameter
      · exact hnorm
      · exact (hzero hdiameter.1).elim
    by_cases hneg : z.1.re < 0
    · simp [thetaToFigureEightRaw, hzero, hneg, Submonoid.unitSphere, hnorm]
    · simp [thetaToFigureEightRaw, hzero, hneg, Submonoid.unitSphere]

/-- The second coordinate of the inverse formula lies on the unit circle. -/
private theorem thetaToFigureEightRaw_snd_mem (z : PlanarTheta) :
    (thetaToFigureEightRaw z).2 ∈ Submonoid.unitSphere ℂ := by
  -- The right semicircle is treated symmetrically; every other branch is the basepoint.
  by_cases hzero : z.1.re = 0
  · simp [thetaToFigureEightRaw, hzero, Submonoid.unitSphere]
  · have hnorm : ‖(z.1 : ℂ)‖ = 1 := by
      rcases (PlanarTheta.mem_iff z.1).1 z.2 with hnorm | hdiameter
      · exact hnorm
      · exact (hzero hdiameter.1).elim
    by_cases hneg : z.1.re < 0
    · simp [thetaToFigureEightRaw, hzero, hneg, Submonoid.unitSphere]
    · simp [thetaToFigureEightRaw, hzero, hneg, Submonoid.unitSphere, hnorm]

/-- The inverse formula, regarded as a point of the product of two circles. -/
private def thetaToFigureEightCirclePair (z : PlanarTheta) : Circle × Circle :=
  (⟨(thetaToFigureEightRaw z).1, thetaToFigureEightRaw_fst_mem z⟩,
    ⟨(thetaToFigureEightRaw z).2, thetaToFigureEightRaw_snd_mem z⟩)

/-- The inverse formula lies in the figure eight. -/
private theorem thetaToFigureEightCirclePair_mem (z : PlanarTheta) :
    (thetaToFigureEightCirclePair z).2 = 1 ∨
      (thetaToFigureEightCirclePair z).1 = 1 := by
  -- Each branch of the collapse formula fixes the inactive circle coordinate.
  by_cases hzero : z.1.re = 0
  · left
    ext
    simp [thetaToFigureEightCirclePair, thetaToFigureEightRaw, hzero]
  · by_cases hneg : z.1.re < 0
    · left
      ext
      simp [thetaToFigureEightCirclePair, thetaToFigureEightRaw, hzero, hneg]
    · right
      ext
      simp [thetaToFigureEightCirclePair, thetaToFigureEightRaw, hzero, hneg]

/-- The underlying function of the map from the theta space to the figure eight. -/
private def thetaToFigureEightFunction (z : PlanarTheta) : FigureEight :=
  ⟨thetaToFigureEightCirclePair z,
    (FigureEight.mem_iff (thetaToFigureEightCirclePair z)).2
      (thetaToFigureEightCirclePair_mem z)⟩

/-- The map collapsing the diameter and wrapping the semicircles is continuous. -/
private theorem continuous_thetaToFigureEightFunction :
    Continuous thetaToFigureEightFunction := by
  -- The diameter and the two closed semicircles form a closed cover of the theta space.
  let diameter : Set PlanarTheta := {z | z.1.re = 0}
  let leftArc : Set PlanarTheta := {z | z.1.re ≤ 0 ∧ ‖(z.1 : ℂ)‖ = 1}
  let rightArc : Set PlanarTheta := {z | 0 ≤ z.1.re ∧ ‖(z.1 : ℂ)‖ = 1}
  have hre : Continuous fun z : PlanarTheta ↦ z.1.re :=
    Complex.continuous_re.comp continuous_subtype_val
  have hnorm : Continuous fun z : PlanarTheta ↦ ‖(z.1 : ℂ)‖ :=
    continuous_subtype_val.norm
  have hdiameterClosed : IsClosed diameter := by
    exact isClosed_eq hre continuous_const
  have hleftClosed : IsClosed leftArc := by
    exact (isClosed_le hre continuous_const).inter (isClosed_eq hnorm continuous_const)
  have hrightClosed : IsClosed rightArc := by
    exact (isClosed_le continuous_const hre).inter (isClosed_eq hnorm continuous_const)
  have hdiameter : ContinuousOn thetaToFigureEightRaw diameter := by
    have hconst : Continuous fun _ : PlanarTheta ↦ ((1 : ℂ), (1 : ℂ)) := continuous_const
    refine hconst.continuousOn.congr ?_
    intro z hz
    simp [diameter] at hz
    simp [thetaToFigureEightRaw, hz]
  have hleft : ContinuousOn thetaToFigureEightRaw leftArc := by
    have hformula : Continuous fun z : PlanarTheta ↦ (-(z.1 : ℂ) ^ 2, (1 : ℂ)) := by
      fun_prop
    refine hformula.continuousOn.congr ?_
    intro z hz
    change z.1.re ≤ 0 ∧ ‖(z.1 : ℂ)‖ = 1 at hz
    by_cases hzero : z.1.re = 0
    · have hend : -(z.1 : ℂ) ^ 2 = 1 :=
        neg_sq_eq_one_of_re_eq_zero_norm_eq_one z.1 hzero hz.2
      simp [thetaToFigureEightRaw, hzero, hend]
    · have hneg : z.1.re < 0 := lt_of_le_of_ne hz.1 hzero
      simp [thetaToFigureEightRaw, hzero, hneg]
  have hright : ContinuousOn thetaToFigureEightRaw rightArc := by
    have hformula : Continuous fun z : PlanarTheta ↦ ((1 : ℂ), -(z.1 : ℂ) ^ 2) := by
      fun_prop
    refine hformula.continuousOn.congr ?_
    intro z hz
    change 0 ≤ z.1.re ∧ ‖(z.1 : ℂ)‖ = 1 at hz
    by_cases hzero : z.1.re = 0
    · have hend : -(z.1 : ℂ) ^ 2 = 1 :=
        neg_sq_eq_one_of_re_eq_zero_norm_eq_one z.1 hzero hz.2
      simp [thetaToFigureEightRaw, hzero, hend]
    · have hnneg : ¬z.1.re < 0 := not_lt.mpr hz.1
      simp [thetaToFigureEightRaw, hzero, hnneg]
  have hcover : (diameter ∪ leftArc) ∪ rightArc = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    rcases (PlanarTheta.mem_iff z.1).1 z.2 with hcircle | hdiameter
    · rcases le_total z.1.re 0 with hle | hle
      · exact Or.inl (Or.inr ⟨hle, hcircle⟩)
      · exact Or.inr ⟨hle, hcircle⟩
    · exact Or.inl (Or.inl hdiameter.1)
  have hraw : Continuous thetaToFigureEightRaw := by
    rw [← continuousOn_univ, ← hcover]
    exact (hdiameter.union_of_isClosed hleft hdiameterClosed hleftClosed).union_of_isClosed
      hright (hdiameterClosed.union hleftClosed) hrightClosed
  -- Restrict both coordinates to `Circle`, then restrict the pair to `FigureEight`.
  have hfst : Continuous fun z : PlanarTheta ↦
      (⟨(thetaToFigureEightRaw z).1, thetaToFigureEightRaw_fst_mem z⟩ : Circle) :=
    hraw.fst.subtype_mk thetaToFigureEightRaw_fst_mem
  have hsnd : Continuous fun z : PlanarTheta ↦
      (⟨(thetaToFigureEightRaw z).2, thetaToFigureEightRaw_snd_mem z⟩ : Circle) :=
    hraw.snd.subtype_mk thetaToFigureEightRaw_snd_mem
  have hpair : Continuous thetaToFigureEightCirclePair := hfst.prodMk hsnd
  have hmem (z : PlanarTheta) : thetaToFigureEightCirclePair z ∈ FigureEight.carrier :=
    (FigureEight.mem_iff _).2 (thetaToFigureEightCirclePair_mem z)
  exact hpair.subtype_mk hmem

/-- The explicit continuous map from the theta space to the figure eight, collapsing the
vertical diameter and sending the two semicircles to the two coordinate circles. -/
def thetaToFigureEight : C(PlanarTheta, FigureEight) :=
  ⟨thetaToFigureEightFunction, continuous_thetaToFigureEightFunction⟩

/-- Helper for Exercise 58.4: squaring a real point of the unit circle gives one. -/
private theorem circle_sq_eq_one_of_im_eq_zero (z : Circle)
    (him : (z : ℂ).im = 0) : (z : ℂ) ^ 2 = 1 := by
  -- The norm equation says that the square of the real part is one.
  have hnormSq : Complex.normSq (z : ℂ) = 1 := by
    rw [← Complex.sq_norm, Circle.norm_coe]
    norm_num
  rw [Complex.normSq_apply, him] at hnormSq
  have hreSq : (z : ℂ).re * (z : ℂ).re = 1 := by
    simpa using hnormSq
  apply Complex.ext
  · simp [pow_two, Complex.mul_re, him, hreSq]
  · simp [pow_two, Complex.mul_im, him]

/-- Helper for Exercise 58.4: rotation by `I`, followed by squaring and negation,
recovers the original square. -/
private theorem neg_I_mul_sq (z : ℂ) : -(Complex.I * z) ^ 2 = z ^ 2 := by
  -- Expand the square and use `I ^ 2 = -1`.
  rw [mul_pow, Complex.I_sq]
  ring

/-- Helper for Exercise 58.4: the upper semicircle is squared and the lower semicircle
is collapsed to the basepoint. -/
private def upperCircleFoldRaw (z : Circle) : ℂ :=
  if 0 ≤ (z : ℂ).im then (z : ℂ) ^ 2 else 1

/-- Helper for Exercise 58.4: the circle fold has unit norm. -/
private theorem upperCircleFoldRaw_mem (z : Circle) :
    upperCircleFoldRaw z ∈ Submonoid.unitSphere ℂ := by
  -- Both branches lie on the unit circle.
  by_cases hupper : 0 ≤ (z : ℂ).im
  · simp [upperCircleFoldRaw, hupper, Submonoid.unitSphere]
  · simp [upperCircleFoldRaw, hupper, Submonoid.unitSphere]

/-- Helper for Exercise 58.4: the upper-circle fold as a circle-valued function. -/
private def upperCircleFoldFunction (z : Circle) : Circle :=
  ⟨upperCircleFoldRaw z, upperCircleFoldRaw_mem z⟩

/-- Helper for Exercise 58.4: the upper-circle fold is continuous. -/
private theorem continuous_upperCircleFoldFunction :
    Continuous upperCircleFoldFunction := by
  -- The squaring and constant branches agree at the two real points of the circle.
  have hraw : Continuous upperCircleFoldRaw := by
    refine Continuous.if_le (by fun_prop) continuous_const continuous_const
      (Complex.continuous_im.comp continuous_subtype_val) ?_
    intro z hz
    exact circle_sq_eq_one_of_im_eq_zero z hz.symm
  exact hraw.subtype_mk upperCircleFoldRaw_mem

/-- Helper for Exercise 58.4: the continuous upper-circle fold. -/
private def upperCircleFold : C(Circle, Circle) :=
  ⟨upperCircleFoldFunction, continuous_upperCircleFoldFunction⟩

/-- Helper for Exercise 58.4: the ratio between the folded point and the original point. -/
private def upperCircleFoldRatio (z : Circle) : ℂ :=
  upperCircleFoldRaw z / (z : ℂ)

/-- Helper for Exercise 58.4: the fold ratio lies in the closed upper half-plane. -/
private theorem upperCircleFoldRatio_im_nonneg (z : Circle) :
    0 ≤ (upperCircleFoldRatio z).im := by
  -- On the upper half it is `z`; on the lower half it is `conj z`.
  have hne : (z : ℂ) ≠ 0 := Circle.coe_ne_zero z
  by_cases hupper : 0 ≤ (z : ℂ).im
  · have hratio : upperCircleFoldRatio z = (z : ℂ) := by
      simp [upperCircleFoldRatio, upperCircleFoldRaw, hupper, pow_two, hne]
    rw [hratio]
    exact hupper
  · have hinv : (z : ℂ)⁻¹ = conj (z : ℂ) := by
      simpa using Circle.coe_inv_eq_conj z
    have hratio : upperCircleFoldRatio z = conj (z : ℂ) := by
      simp [upperCircleFoldRatio, upperCircleFoldRaw, hupper, div_eq_mul_inv, hinv]
    rw [hratio]
    simp only [Complex.conj_im]
    exact neg_nonneg.mpr (le_of_not_ge hupper)

/-- Helper for Exercise 58.4: the fold ratio has unit norm. -/
private theorem upperCircleFoldRatio_norm (z : Circle) :
    ‖upperCircleFoldRatio z‖ = 1 := by
  -- It is a quotient of two unit complex numbers.
  rw [upperCircleFoldRatio, norm_div, Circle.norm_coe]
  have hfold : ‖upperCircleFoldRaw z‖ = 1 := by
    simpa [Submonoid.unitSphere] using upperCircleFoldRaw_mem z
  simp [hfold]

/-- Helper for Exercise 58.4: the real part of the fold ratio is at most one. -/
private theorem upperCircleFoldRatio_re_le_one (z : Circle) :
    (upperCircleFoldRatio z).re ≤ 1 := by
  -- Bound the real part by the norm, which is one.
  exact le_trans (le_abs_self _) ((Complex.abs_re_le_norm _).trans_eq
    (upperCircleFoldRatio_norm z))

/-- Helper for Exercise 58.4: the fold ratio varies continuously. -/
private theorem continuous_upperCircleFoldRatio :
    Continuous upperCircleFoldRatio := by
  -- Division is harmless because a point of the circle is nonzero.
  have hfold : Continuous upperCircleFoldRaw :=
    continuous_subtype_val.comp continuous_upperCircleFoldFunction
  exact hfold.div continuous_subtype_val Circle.coe_ne_zero

/-- Helper for Exercise 58.4: the nonzero complex factor used to interpolate the fold ratio
to one. -/
private def circleFoldHomotopyFactor (t : unitInterval) (z : Circle) : ℂ :=
  ((1 - (t : ℝ) : ℝ) : ℂ) * upperCircleFoldRatio z + (t : ℝ) +
    (((t : ℝ) * (1 - (t : ℝ)) * (1 - (upperCircleFoldRatio z).re) : ℝ) : ℂ) * Complex.I

/-- Helper for Exercise 58.4: the interpolation factor never vanishes. -/
private theorem circleFoldHomotopyFactor_ne_zero (t : unitInterval) (z : Circle) :
    circleFoldHomotopyFactor t z ≠ 0 := by
  -- Its extra positive imaginary term detours around the sole antipodal obstruction.
  intro hzero
  have ht_nonneg : 0 ≤ (t : ℝ) := t.2.1
  have ht_le_one : (t : ℝ) ≤ 1 := t.2.2
  by_cases ht_zero : (t : ℝ) = 0
  · have hratio_ne : upperCircleFoldRatio z ≠ 0 := by
      intro hratio_zero
      have hnorm := upperCircleFoldRatio_norm z
      rw [hratio_zero, norm_zero] at hnorm
      norm_num at hnorm
    apply hratio_ne
    simpa [circleFoldHomotopyFactor, ht_zero] using hzero
  · by_cases ht_one : (t : ℝ) = 1
    · norm_num [circleFoldHomotopyFactor, ht_one] at hzero
    · have ht_pos : 0 < (t : ℝ) := lt_of_le_of_ne ht_nonneg (Ne.symm ht_zero)
      have ht_lt_one : (t : ℝ) < 1 := lt_of_le_of_ne ht_le_one ht_one
      have hcoeff : 0 < (t : ℝ) * (1 - (t : ℝ)) :=
        mul_pos ht_pos (sub_pos.mpr ht_lt_one)
      have hfirst : 0 ≤ (1 - (t : ℝ)) * (upperCircleFoldRatio z).im :=
        mul_nonneg (sub_nonneg.mpr ht_le_one) (upperCircleFoldRatio_im_nonneg z)
      have hsecond : 0 ≤ (t : ℝ) * (1 - (t : ℝ)) *
          (1 - (upperCircleFoldRatio z).re) :=
        mul_nonneg hcoeff.le (sub_nonneg.mpr (upperCircleFoldRatio_re_le_one z))
      have him := congrArg Complex.im hzero
      have hre := congrArg Complex.re hzero
      simp [circleFoldHomotopyFactor] at him hre
      have hratio_re : (upperCircleFoldRatio z).re = 1 := by
        nlinarith
      nlinarith

/-- Helper for Exercise 58.4: the ambient complex vector defining the circle-fold homotopy. -/
private def circleFoldHomotopyVector (t : unitInterval) (z : Circle) : ℂ :=
  (z : ℂ) * circleFoldHomotopyFactor t z

/-- Helper for Exercise 58.4: the circle-fold homotopy vector never vanishes. -/
private theorem circleFoldHomotopyVector_ne_zero (t : unitInterval) (z : Circle) :
    circleFoldHomotopyVector t z ≠ 0 := by
  -- Both the circle point and the interpolation factor are nonzero.
  exact mul_ne_zero (Circle.coe_ne_zero z) (circleFoldHomotopyFactor_ne_zero t z)

/-- Helper for Exercise 58.4: normalization of the homotopy vector lies on the unit circle. -/
private theorem circleFoldHomotopyValue_mem (t : unitInterval) (z : Circle) :
    NormedSpace.normalize (circleFoldHomotopyVector t z) ∈ Submonoid.unitSphere ℂ := by
  -- A nonzero vector normalizes to norm one.
  simpa [Submonoid.unitSphere] using
    NormedSpace.norm_normalize (circleFoldHomotopyVector_ne_zero t z)

/-- Helper for Exercise 58.4: the normalized circle-fold homotopy value. -/
private def circleFoldHomotopyValue (t : unitInterval) (z : Circle) : Circle :=
  ⟨NormedSpace.normalize (circleFoldHomotopyVector t z), circleFoldHomotopyValue_mem t z⟩

/-- Helper for Exercise 58.4: the circle-fold homotopy preserves the closed lower semicircle. -/
private theorem circleFoldHomotopyValue_im_nonpos (t : unitInterval) (z : Circle)
    (hz : (z : ℂ).im ≤ 0) : ((circleFoldHomotopyValue t z : Circle) : ℂ).im ≤ 0 := by
  -- On the lower semicircle the fold ratio is complex conjugation.
  have hinv : (z : ℂ)⁻¹ = conj (z : ℂ) := by
    simpa using Circle.coe_inv_eq_conj z
  have hratio : upperCircleFoldRatio z = conj (z : ℂ) := by
    by_cases hupper : 0 ≤ (z : ℂ).im
    · have him : (z : ℂ).im = 0 := le_antisymm hz hupper
      have hne : (z : ℂ) ≠ 0 := Circle.coe_ne_zero z
      calc
        upperCircleFoldRatio z = (z : ℂ) := by
          simp [upperCircleFoldRatio, upperCircleFoldRaw, hupper, pow_two, hne]
        _ = conj (z : ℂ) := by
          apply Complex.ext
          · simp
          · simp [him]
    · simp [upperCircleFoldRatio, upperCircleFoldRaw, hupper, div_eq_mul_inv, hinv]
  have hnormSq : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ ↦ r ^ 2) (Circle.norm_coe z)
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    simpa [pow_two] using h
  have hreBounds : -1 ≤ (z : ℂ).re ∧ (z : ℂ).re ≤ 1 := by
    constructor
    · exact neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans_eq (Circle.norm_coe z))
    · exact le_trans (le_abs_self _) ((Complex.abs_re_le_norm _).trans_eq (Circle.norm_coe z))
  -- The only nonlinear estimate is `re * (1 - re) ≤ -im` on the lower semicircle.
  have hquadratic : (z : ℂ).re * (1 - (z : ℂ).re) ≤ -(z : ℂ).im := by
    by_cases hre : (z : ℂ).re ≤ 0
    · have honeMinus : 0 ≤ 1 - (z : ℂ).re := sub_nonneg.mpr hreBounds.2
      have hproduct : (z : ℂ).re * (1 - (z : ℂ).re) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hre honeMinus
      exact hproduct.trans (neg_nonneg.mpr hz)
    · have hrePos : 0 < (z : ℂ).re := lt_of_not_ge hre
      nlinarith [sq_nonneg ((z : ℂ).re * (1 - (z : ℂ).re) + (z : ℂ).im)]
  have htBounds : 0 ≤ (t : ℝ) ∧ (t : ℝ) ≤ 1 := t.2
  have hbracket : (z : ℂ).im +
      (z : ℂ).re * (1 - (t : ℝ)) * (1 - (z : ℂ).re) ≤ 0 := by
    by_cases hre : (z : ℂ).re ≤ 0
    · have hterm : (z : ℂ).re * (1 - (t : ℝ)) *
          (1 - (z : ℂ).re) ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg hre (sub_nonneg.mpr htBounds.2))
          (sub_nonneg.mpr hreBounds.2)
      linarith
    · have hrePos : 0 < (z : ℂ).re := lt_of_not_ge hre
      have hbase : 0 ≤ (z : ℂ).re * (1 - (z : ℂ).re) :=
        mul_nonneg hrePos.le (sub_nonneg.mpr hreBounds.2)
      have hscaled : (z : ℂ).re * (1 - (t : ℝ)) *
          (1 - (z : ℂ).re) ≤ (z : ℂ).re * (1 - (z : ℂ).re) := by
        calc
          (z : ℂ).re * (1 - (t : ℝ)) * (1 - (z : ℂ).re) =
              (1 - (t : ℝ)) * ((z : ℂ).re * (1 - (z : ℂ).re)) := by ring
          _ ≤ 1 * ((z : ℂ).re * (1 - (z : ℂ).re)) :=
            mul_le_mul_of_nonneg_right (by linarith [htBounds.1]) hbase
          _ = (z : ℂ).re * (1 - (z : ℂ).re) := by ring
      linarith
  have hvectorIm : (circleFoldHomotopyVector t z).im ≤ 0 := by
    -- Expanding only the imaginary coordinate exposes the preceding semicircle estimate.
    have hcoordinate : (circleFoldHomotopyVector t z).im = (t : ℝ) *
        ((z : ℂ).im + (z : ℂ).re * (1 - (t : ℝ)) *
          (1 - (z : ℂ).re)) := by
      rw [circleFoldHomotopyVector, circleFoldHomotopyFactor, hratio]
      simp [Complex.mul_im, Complex.mul_re]
      ring
    rw [hcoordinate]
    exact mul_nonpos_of_nonneg_of_nonpos htBounds.1 hbracket
  -- Normalization multiplies the vector by a nonnegative real scalar.
  change (NormedSpace.normalize (circleFoldHomotopyVector t z)).im ≤ 0
  simp only [NormedSpace.normalize, Complex.smul_im]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _)) hvectorIm

/-- Helper for Exercise 58.4: the normalized circle-fold homotopy is continuous. -/
private theorem continuous_circleFoldHomotopyValue :
    Continuous fun p : unitInterval × Circle ↦ circleFoldHomotopyValue p.1 p.2 := by
  -- The factor is continuous, and normalization is continuous away from zero.
  apply Continuous.subtype_mk
  rw [continuous_iff_continuousAt]
  intro p
  unfold NormedSpace.normalize
  have hratio : Continuous fun q : unitInterval × Circle ↦ upperCircleFoldRatio q.2 :=
    continuous_upperCircleFoldRatio.comp continuous_snd
  have hvector : Continuous fun q : unitInterval × Circle ↦
      circleFoldHomotopyVector q.1 q.2 := by
    unfold circleFoldHomotopyVector circleFoldHomotopyFactor
    fun_prop
  have hnorm_ne : ‖circleFoldHomotopyVector p.1 p.2‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (circleFoldHomotopyVector_ne_zero p.1 p.2)
  exact (hvector.continuousAt.norm.inv₀ hnorm_ne).smul hvector.continuousAt

/-- Helper for Exercise 58.4: the circle-fold homotopy starts at the fold. -/
private theorem circleFoldHomotopyValue_zero (z : Circle) :
    circleFoldHomotopyValue 0 z = upperCircleFold z := by
  -- At time zero the factor is exactly the fold ratio.
  have hvector : circleFoldHomotopyVector 0 z = upperCircleFoldRaw z := by
    unfold circleFoldHomotopyVector circleFoldHomotopyFactor upperCircleFoldRatio
    norm_num
    field_simp
  apply Circle.ext
  have hfold : ‖upperCircleFoldRaw z‖ = 1 := by
    simpa [Submonoid.unitSphere] using upperCircleFoldRaw_mem z
  change NormedSpace.normalize (circleFoldHomotopyVector 0 z) = upperCircleFoldRaw z
  rw [hvector]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one hfold

/-- Helper for Exercise 58.4: the circle-fold homotopy ends at the identity. -/
private theorem circleFoldHomotopyValue_one (z : Circle) :
    circleFoldHomotopyValue 1 z = z := by
  -- At time one the interpolation factor is one.
  apply Circle.ext
  simp [circleFoldHomotopyValue, circleFoldHomotopyVector, circleFoldHomotopyFactor,
    NormedSpace.normalize_eq_self_of_norm_eq_one]

/-- Helper for Exercise 58.4: the circle-fold homotopy fixes the common basepoint. -/
private theorem circleFoldHomotopyValue_basepoint (t : unitInterval) :
    circleFoldHomotopyValue t 1 = 1 := by
  -- At the basepoint the fold ratio is one, so the detour term vanishes.
  apply Circle.ext
  simp [circleFoldHomotopyValue, circleFoldHomotopyVector, circleFoldHomotopyFactor,
    upperCircleFoldRatio, upperCircleFoldRaw,
    NormedSpace.normalize_eq_self_of_norm_eq_one]

/-- Helper for Exercise 58.4: the upper-circle fold is homotopic to the identity. -/
private def circleFoldHomotopy :
    ContinuousMap.Homotopy upperCircleFold (ContinuousMap.id Circle) :=
  {
    toFun := fun p ↦ circleFoldHomotopyValue p.1 p.2
    continuous_toFun := continuous_circleFoldHomotopyValue
    map_zero_left := circleFoldHomotopyValue_zero
    map_one_left := circleFoldHomotopyValue_one
  }

/-- Helper for Exercise 58.4: the lower-circle fold obtained by inversion conjugation. -/
private def lowerCircleFoldFunction (z : Circle) : Circle :=
  (upperCircleFold z⁻¹)⁻¹

/-- Helper for Exercise 58.4: the lower-circle fold is continuous. -/
private theorem continuous_lowerCircleFoldFunction :
    Continuous lowerCircleFoldFunction := by
  -- Inversion conjugates the already continuous upper-circle fold.
  exact continuous_inv.comp (continuous_upperCircleFoldFunction.comp continuous_inv)

/-- Helper for Exercise 58.4: the continuous lower-circle fold. -/
private def lowerCircleFold : C(Circle, Circle) :=
  ⟨lowerCircleFoldFunction, continuous_lowerCircleFoldFunction⟩

/-- Helper for Exercise 58.4: the lower fold squares the lower semicircle and collapses
the upper semicircle. -/
private theorem lowerCircleFold_apply (z : Circle) :
    lowerCircleFold z = if (z : ℂ).im ≤ 0 then z ^ 2 else 1 := by
  -- Inversion exchanges the upper and lower semicircles.
  by_cases hlower : (z : ℂ).im ≤ 0
  · apply Circle.ext
    simp [lowerCircleFold, lowerCircleFoldFunction, upperCircleFold,
      upperCircleFoldFunction, upperCircleFoldRaw, hlower]
  · apply Circle.ext
    simp [lowerCircleFold, lowerCircleFoldFunction, upperCircleFold,
      upperCircleFoldFunction, upperCircleFoldRaw, hlower]

/-- Helper for Exercise 58.4: the lower-circle fold homotopy value. -/
private def lowerCircleFoldHomotopyValue (t : unitInterval) (z : Circle) : Circle :=
  (circleFoldHomotopyValue t z⁻¹)⁻¹

/-- Helper for Exercise 58.4: the lower-circle fold homotopy is continuous. -/
private theorem continuous_lowerCircleFoldHomotopyValue :
    Continuous fun p : unitInterval × Circle ↦ lowerCircleFoldHomotopyValue p.1 p.2 := by
  -- Invert both the source circle coordinate and the upper-fold homotopy value.
  exact continuous_inv.comp (continuous_circleFoldHomotopyValue.comp
    (continuous_fst.prodMk (continuous_inv.comp continuous_snd)))

/-- Helper for Exercise 58.4: the lower-circle homotopy starts at its fold. -/
private theorem lowerCircleFoldHomotopyValue_zero (z : Circle) :
    lowerCircleFoldHomotopyValue 0 z = lowerCircleFold z := by
  -- This is the upper-fold endpoint transported through inversion.
  simp [lowerCircleFoldHomotopyValue, lowerCircleFold, lowerCircleFoldFunction,
    circleFoldHomotopyValue_zero]

/-- Helper for Exercise 58.4: the lower-circle homotopy ends at the identity. -/
private theorem lowerCircleFoldHomotopyValue_one (z : Circle) :
    lowerCircleFoldHomotopyValue 1 z = z := by
  -- Double inversion cancels at the identity endpoint.
  simp [lowerCircleFoldHomotopyValue, circleFoldHomotopyValue_one]

/-- Helper for Exercise 58.4: the lower-circle homotopy fixes the common basepoint. -/
private theorem lowerCircleFoldHomotopyValue_basepoint (t : unitInterval) :
    lowerCircleFoldHomotopyValue t 1 = 1 := by
  -- Inversion fixes the common basepoint.
  simp [lowerCircleFoldHomotopyValue, circleFoldHomotopyValue_basepoint]

/-- Helper for Exercise 58.4: the coordinate pair of the pasted figure-eight homotopy. -/
private def figureEightFoldHomotopyPair (t : unitInterval) (p : FigureEight) : Circle × Circle :=
  @ite (Circle × Circle) (p.1.2 = 1) (Classical.propDecidable (p.1.2 = 1))
    (circleFoldHomotopyValue t p.1.1, 1)
    (1, lowerCircleFoldHomotopyValue t p.1.2)

/-- Helper for Exercise 58.4: the pasted coordinate pair remains in the figure eight. -/
private theorem figureEightFoldHomotopyPair_mem (t : unitInterval) (p : FigureEight) :
    figureEightFoldHomotopyPair t p ∈ FigureEight.carrier := by
  -- Each branch keeps the inactive coordinate at the common basepoint.
  apply (FigureEight.mem_iff _).2
  by_cases hleft : p.1.2 = 1
  · left
    simp [figureEightFoldHomotopyPair, hleft]
  · right
    simp [figureEightFoldHomotopyPair, hleft]

/-- Helper for Exercise 58.4: the value of the pasted figure-eight homotopy. -/
private def figureEightFoldHomotopyValue (t : unitInterval) (p : FigureEight) : FigureEight :=
  ⟨figureEightFoldHomotopyPair t p, figureEightFoldHomotopyPair_mem t p⟩

/-- Helper for Exercise 58.4: the lower-circle homotopy is continuous on the second
figure-eight coordinate. -/
private theorem continuous_lowerCircleFoldHomotopyValue_snd :
    Continuous fun q : unitInterval × FigureEight ↦
      lowerCircleFoldHomotopyValue q.1 q.2.1.2 := by
  -- Compose the lower-circle homotopy with the second coordinate projection.
  change Continuous ((fun p : unitInterval × Circle ↦
    lowerCircleFoldHomotopyValue p.1 p.2) ∘
      (fun q : unitInterval × FigureEight ↦ (q.1, q.2.1.2)))
  exact continuous_lowerCircleFoldHomotopyValue.comp
    (continuous_fst.prodMk (continuous_snd.comp
      (continuous_subtype_val.comp continuous_snd)))

/-- Helper for Exercise 58.4: the pasted pair is continuous on the left coordinate circle. -/
private theorem continuousOn_figureEightFoldHomotopyPair_left :
    ContinuousOn (fun q : unitInterval × FigureEight ↦
      figureEightFoldHomotopyPair q.1 q.2) {q | q.2.1.2 = 1} := by
  -- On this closed piece the pasted pair is the upper-circle homotopy paired with one.
  have hformula : Continuous fun q : unitInterval × FigureEight ↦
      (circleFoldHomotopyValue q.1 q.2.1.1, (1 : Circle)) :=
    (continuous_circleFoldHomotopyValue.comp
      (continuous_fst.prodMk (continuous_fst.comp
        (continuous_subtype_val.comp continuous_snd)))).prodMk continuous_const
  refine hformula.continuousOn.congr ?_
  intro q hq
  change q.2.1.2 = 1 at hq
  simp only [figureEightFoldHomotopyPair, hq, if_pos]

/-- Helper for Exercise 58.4: the pasted pair is continuous on the right coordinate circle. -/
private theorem continuousOn_figureEightFoldHomotopyPair_right :
    ContinuousOn (fun q : unitInterval × FigureEight ↦
      figureEightFoldHomotopyPair q.1 q.2) {q | q.2.1.1 = 1} := by
  -- On the overlap, both circle homotopies fix the common basepoint.
  have hformula : Continuous fun q : unitInterval × FigureEight ↦
      ((1 : Circle), lowerCircleFoldHomotopyValue q.1 q.2.1.2) :=
    continuous_const.prodMk continuous_lowerCircleFoldHomotopyValue_snd
  refine hformula.continuousOn.congr ?_
  intro q hq
  change q.2.1.1 = 1 at hq
  by_cases hleftPoint : q.2.1.2 = 1
  · simp [figureEightFoldHomotopyPair, hleftPoint, hq,
      circleFoldHomotopyValue_basepoint, lowerCircleFoldHomotopyValue_basepoint]
  · simp [figureEightFoldHomotopyPair, hleftPoint]

/-- Helper for Exercise 58.4: the pasted figure-eight coordinate pair is continuous. -/
private theorem continuous_figureEightFoldHomotopyPair :
    Continuous fun q : unitInterval × FigureEight ↦
      figureEightFoldHomotopyPair q.1 q.2 := by
  -- The two coordinate circles are closed and cover the figure eight.
  let leftSide : Set (unitInterval × FigureEight) := {q | q.2.1.2 = 1}
  let rightSide : Set (unitInterval × FigureEight) := {q | q.2.1.1 = 1}
  have hleftClosed : IsClosed leftSide := by
    exact isClosed_eq (continuous_snd.comp
      (continuous_subtype_val.comp continuous_snd)) continuous_const
  have hrightClosed : IsClosed rightSide := by
    exact isClosed_eq (continuous_fst.comp
      (continuous_subtype_val.comp continuous_snd)) continuous_const
  have hcover : leftSide ∪ rightSide = Set.univ := by
    ext q
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    exact (FigureEight.mem_iff q.2.1).1 q.2.2
  rw [← continuousOn_univ, ← hcover]
  exact continuousOn_figureEightFoldHomotopyPair_left.union_of_isClosed
    continuousOn_figureEightFoldHomotopyPair_right hleftClosed hrightClosed

/-- Helper for Exercise 58.4: the pasted figure-eight homotopy is continuous. -/
private theorem continuous_figureEightFoldHomotopyValue :
    Continuous fun q : unitInterval × FigureEight ↦
      figureEightFoldHomotopyValue q.1 q.2 := by
  -- Restrict the continuous coordinate pair to the figure-eight carrier.
  have hmem (q : unitInterval × FigureEight) :
      figureEightFoldHomotopyPair q.1 q.2 ∈ FigureEight.carrier :=
    figureEightFoldHomotopyPair_mem q.1 q.2
  exact continuous_figureEightFoldHomotopyPair.subtype_mk hmem

/-- Helper for Exercise 58.4: the pasted figure-eight homotopy ends at the identity. -/
private theorem figureEightFoldHomotopyValue_one (p : FigureEight) :
    figureEightFoldHomotopyValue 1 p = p := by
  -- At time one each active coordinate is unchanged.
  apply Subtype.ext
  by_cases hleft : p.1.2 = 1
  · apply Prod.ext
    · simp [figureEightFoldHomotopyValue, figureEightFoldHomotopyPair, hleft,
        circleFoldHomotopyValue_one]
    · simp [figureEightFoldHomotopyValue, figureEightFoldHomotopyPair, hleft]
  · have hright : p.1.1 = 1 :=
      ((FigureEight.mem_iff p.1).1 p.2).resolve_left hleft
    apply Prod.ext
    · simpa [figureEightFoldHomotopyValue, figureEightFoldHomotopyPair, hleft]
        using hright.symm
    · simp [figureEightFoldHomotopyValue, figureEightFoldHomotopyPair, hleft,
        lowerCircleFoldHomotopyValue_one]

/-- Helper for Exercise 58.4: on the left coordinate circle, the composite is the upper fold. -/
private theorem thetaToFigureEight_figureEightToTheta_left (p : FigureEight)
    (hleft : p.1.2 = 1) :
    thetaToFigureEight (figureEightToTheta p) = figureEightFoldHomotopyValue 0 p := by
  -- Split according to whether the active circle point lies above, on, or below the real axis.
  apply Subtype.ext
  apply Prod.ext
  · apply Circle.ext
    by_cases hupper : 0 ≤ (p.1.1 : ℂ).im
    · by_cases him : (p.1.1 : ℂ).im = 0
      · have hsq : (p.1.1 : ℂ) ^ 2 = 1 :=
          circle_sq_eq_one_of_im_eq_zero p.1.1 him
        simp [thetaToFigureEight, thetaToFigureEightFunction,
          thetaToFigureEightCirclePair, thetaToFigureEightRaw,
          figureEightToTheta, figureEightToThetaFunction, figureEightToThetaRaw,
          leftThetaLoop, hleft, him, hsq,
          figureEightFoldHomotopyValue, figureEightFoldHomotopyPair,
          circleFoldHomotopyValue_zero, upperCircleFold,
          upperCircleFoldFunction, upperCircleFoldRaw]
      · have hpos : 0 < (p.1.1 : ℂ).im := lt_of_le_of_ne hupper (Ne.symm him)
        simpa [thetaToFigureEight, thetaToFigureEightFunction,
          thetaToFigureEightCirclePair, thetaToFigureEightRaw,
          figureEightToTheta, figureEightToThetaFunction, figureEightToThetaRaw,
          leftThetaLoop, hleft, hupper, him, hpos,
          figureEightFoldHomotopyValue, figureEightFoldHomotopyPair,
          circleFoldHomotopyValue_zero, upperCircleFold,
          upperCircleFoldFunction, upperCircleFoldRaw] using
            neg_I_mul_sq (p.1.1 : ℂ)
    · have hneg : (p.1.1 : ℂ).im < 0 := lt_of_not_ge hupper
      simp [thetaToFigureEight, thetaToFigureEightFunction,
        thetaToFigureEightCirclePair, thetaToFigureEightRaw,
        figureEightToTheta, figureEightToThetaFunction, figureEightToThetaRaw,
        leftThetaLoop, hleft, hupper,
        figureEightFoldHomotopyValue, figureEightFoldHomotopyPair,
        circleFoldHomotopyValue_zero, upperCircleFold,
        upperCircleFoldFunction, upperCircleFoldRaw]
  · apply Circle.ext
    by_cases hupper : 0 ≤ (p.1.1 : ℂ).im
    · by_cases him : (p.1.1 : ℂ).im = 0
      · simp [thetaToFigureEight, thetaToFigureEightFunction,
          thetaToFigureEightCirclePair, thetaToFigureEightRaw,
          figureEightToTheta, figureEightToThetaFunction, figureEightToThetaRaw,
          leftThetaLoop, hleft, him, figureEightFoldHomotopyValue,
          figureEightFoldHomotopyPair]
      · have hpos : 0 < (p.1.1 : ℂ).im := lt_of_le_of_ne hupper (Ne.symm him)
        simp [thetaToFigureEight, thetaToFigureEightFunction,
          thetaToFigureEightCirclePair, thetaToFigureEightRaw,
          figureEightToTheta, figureEightToThetaFunction, figureEightToThetaRaw,
          leftThetaLoop, hleft, hupper, him, hpos, figureEightFoldHomotopyValue,
          figureEightFoldHomotopyPair]
    · have hneg : (p.1.1 : ℂ).im < 0 := lt_of_not_ge hupper
      simp [thetaToFigureEight, thetaToFigureEightFunction,
        thetaToFigureEightCirclePair, thetaToFigureEightRaw,
        figureEightToTheta, figureEightToThetaFunction, figureEightToThetaRaw,
        leftThetaLoop, hleft, hupper, figureEightFoldHomotopyValue,
        figureEightFoldHomotopyPair]

/-- Helper for Exercise 58.4: on the right coordinate circle, the composite is the lower fold. -/
private theorem thetaToFigureEight_figureEightToTheta_right (p : FigureEight)
    (hright : p.1.2 ≠ 1) :
    thetaToFigureEight (figureEightToTheta p) = figureEightFoldHomotopyValue 0 p := by
  -- The right loop is the inversion-conjugate calculation on the lower semicircle.
  apply Subtype.ext
  apply Prod.ext
  · apply Circle.ext
    by_cases hlower : (p.1.2 : ℂ).im ≤ 0
    · by_cases him : (p.1.2 : ℂ).im = 0
      · simp [thetaToFigureEight, thetaToFigureEightFunction,
          thetaToFigureEightCirclePair, thetaToFigureEightRaw,
          figureEightToTheta, figureEightToThetaFunction, figureEightToThetaRaw,
          rightThetaLoop, hright, him, figureEightFoldHomotopyValue,
          figureEightFoldHomotopyPair]
      · have hneg : (p.1.2 : ℂ).im < 0 := lt_of_le_of_ne hlower him
        have hnpos : ¬0 < (p.1.2 : ℂ).im := not_lt.mpr hlower
        simp [thetaToFigureEight, thetaToFigureEightFunction,
          thetaToFigureEightCirclePair, thetaToFigureEightRaw,
          figureEightToTheta, figureEightToThetaFunction, figureEightToThetaRaw,
          rightThetaLoop, hright, hlower, him, hnpos, figureEightFoldHomotopyValue,
          figureEightFoldHomotopyPair]
    · have hpos : 0 < (p.1.2 : ℂ).im := lt_of_not_ge hlower
      simp [thetaToFigureEight, thetaToFigureEightFunction,
        thetaToFigureEightCirclePair, thetaToFigureEightRaw,
        figureEightToTheta, figureEightToThetaFunction, figureEightToThetaRaw,
        rightThetaLoop, hright, hlower, figureEightFoldHomotopyValue,
        figureEightFoldHomotopyPair]
  · apply Circle.ext
    by_cases hlower : (p.1.2 : ℂ).im ≤ 0
    · by_cases him : (p.1.2 : ℂ).im = 0
      · have hsq : (p.1.2 : ℂ) ^ 2 = 1 :=
          circle_sq_eq_one_of_im_eq_zero p.1.2 him
        simp [thetaToFigureEight, thetaToFigureEightFunction,
          thetaToFigureEightCirclePair, thetaToFigureEightRaw,
          figureEightToTheta, figureEightToThetaFunction, figureEightToThetaRaw,
          rightThetaLoop, hright, him, hsq,
          figureEightFoldHomotopyValue, figureEightFoldHomotopyPair,
          lowerCircleFoldHomotopyValue_zero, lowerCircleFold_apply]
      · have hneg : (p.1.2 : ℂ).im < 0 := lt_of_le_of_ne hlower him
        have hnpos : ¬0 < (p.1.2 : ℂ).im := not_lt.mpr hlower
        simpa [thetaToFigureEight, thetaToFigureEightFunction,
          thetaToFigureEightCirclePair, thetaToFigureEightRaw,
          figureEightToTheta, figureEightToThetaFunction, figureEightToThetaRaw,
          rightThetaLoop, hright, hlower, him, hnpos,
          figureEightFoldHomotopyValue, figureEightFoldHomotopyPair,
          lowerCircleFoldHomotopyValue_zero, lowerCircleFold_apply] using
            neg_I_mul_sq (p.1.2 : ℂ)
    · have hpos : 0 < (p.1.2 : ℂ).im := lt_of_not_ge hlower
      simp [thetaToFigureEight, thetaToFigureEightFunction,
        thetaToFigureEightCirclePair, thetaToFigureEightRaw,
        figureEightToTheta, figureEightToThetaFunction, figureEightToThetaRaw,
        rightThetaLoop, hright, hlower, figureEightFoldHomotopyValue,
        figureEightFoldHomotopyPair, lowerCircleFoldHomotopyValue_zero,
        lowerCircleFold_apply]

/-- Helper for Exercise 58.4: the pasted figure-eight homotopy starts at the stated composite. -/
private theorem figureEightFoldHomotopyValue_zero (p : FigureEight) :
    figureEightFoldHomotopyValue 0 p = thetaToFigureEight (figureEightToTheta p) := by
  -- Select the corresponding coordinate-circle computation.
  by_cases hleft : p.1.2 = 1
  · exact (thetaToFigureEight_figureEightToTheta_left p hleft).symm
  · exact (thetaToFigureEight_figureEightToTheta_right p hleft).symm

/-- Helper for Exercise 58.4: the explicit homotopy from the figure-eight composite
to the identity. -/
private def figureEightFoldHomotopy :
    ContinuousMap.Homotopy (thetaToFigureEight.comp figureEightToTheta)
      (ContinuousMap.id FigureEight) :=
  {
    toFun := fun q ↦ figureEightFoldHomotopyValue q.1 q.2
    continuous_toFun := continuous_figureEightFoldHomotopyValue
    map_zero_left := figureEightFoldHomotopyValue_zero
    map_one_left := figureEightFoldHomotopyValue_one
  }

/-- Helper for Exercise 58.4: two upper-semicircle points with the same real part coincide. -/
private theorem circle_eq_of_re_eq_of_im_nonneg (z w : Circle)
    (hre : (z : ℂ).re = (w : ℂ).re) (hz : 0 ≤ (z : ℂ).im)
    (hw : 0 ≤ (w : ℂ).im) : z = w := by
  -- Equal circle norms determine the absolute imaginary coordinate, and the sign fixes it.
  apply Circle.ext
  apply Complex.ext
  · exact hre
  · have hzNorm := congrArg (fun r : ℝ ↦ r ^ 2) (Circle.norm_coe z)
    have hwNorm := congrArg (fun r : ℝ ↦ r ^ 2) (Circle.norm_coe w)
    rw [Complex.sq_norm, Complex.normSq_apply] at hzNorm hwNorm
    rw [hre] at hzNorm
    have hsquares : (z : ℂ).im ^ 2 = (w : ℂ).im ^ 2 := by
      nlinarith
    exact (sq_eq_sq₀ hz hw).mp hsquares

/-- Helper for Exercise 58.4: two lower-semicircle points with the same real part coincide. -/
private theorem circle_eq_of_re_eq_of_im_nonpos (z w : Circle)
    (hre : (z : ℂ).re = (w : ℂ).re) (hz : (z : ℂ).im ≤ 0)
    (hw : (w : ℂ).im ≤ 0) : z = w := by
  -- Equal circle norms determine the absolute imaginary coordinate, and the sign fixes it.
  apply Circle.ext
  apply Complex.ext
  · exact hre
  · have hzNorm := congrArg (fun r : ℝ ↦ r ^ 2) (Circle.norm_coe z)
    have hwNorm := congrArg (fun r : ℝ ↦ r ^ 2) (Circle.norm_coe w)
    rw [Complex.sq_norm, Complex.normSq_apply] at hzNorm hwNorm
    rw [hre] at hzNorm
    have hsquares : (-(z : ℂ).im) ^ 2 = (-(w : ℂ).im) ^ 2 := by
      nlinarith
    have him := (sq_eq_sq₀ (neg_nonneg.mpr hz) (neg_nonneg.mpr hw)).mp hsquares
    linarith

/-- Helper for Exercise 58.4: upper and lower circle points with the same real part are inverse. -/
private theorem circle_eq_inv_of_re_eq_of_im_nonpos_nonneg (z w : Circle)
    (hre : (z : ℂ).re = (w : ℂ).re) (hz : (z : ℂ).im ≤ 0)
    (hw : 0 ≤ (w : ℂ).im) : w = z⁻¹ := by
  -- Inversion conjugates a circle point, so it reverses only the imaginary coordinate.
  apply Circle.ext
  rw [Circle.coe_inv_eq_conj]
  apply Complex.ext
  · simpa using hre.symm
  · have hzNorm := congrArg (fun r : ℝ ↦ r ^ 2) (Circle.norm_coe z)
    have hwNorm := congrArg (fun r : ℝ ↦ r ^ 2) (Circle.norm_coe w)
    rw [Complex.sq_norm, Complex.normSq_apply] at hzNorm hwNorm
    rw [hre] at hzNorm
    simp only [Complex.conj_im]
    have hsquares : (w : ℂ).im ^ 2 = (-(z : ℂ).im) ^ 2 := by
      nlinarith
    exact (sq_eq_sq₀ hw (neg_nonneg.mpr hz)).mp hsquares

/-- Helper for Exercise 58.4: the left theta-cycle parameterization is injective. -/
private theorem leftThetaLoop_injective : Function.Injective leftThetaLoop := by
  -- On each semicircle the imaginary output remembers the real circle coordinate.
  intro z w h
  by_cases hz : 0 ≤ (z : ℂ).im
  · by_cases hw : 0 ≤ (w : ℂ).im
    · have hre : (z : ℂ).re = (w : ℂ).re := by
        simpa [leftThetaLoop, hz, hw] using congrArg Complex.im h
      have him : -(z : ℂ).im = -(w : ℂ).im := by
        simpa [leftThetaLoop, hz, hw] using congrArg Complex.re h
      apply Circle.ext
      exact Complex.ext hre (by linarith)
    · have hre : (z : ℂ).re = (w : ℂ).re := by
        simpa [leftThetaLoop, hz, hw] using congrArg Complex.im h
      have him : -(z : ℂ).im = 0 := by
        simpa [leftThetaLoop, hz, hw] using congrArg Complex.re h
      have hzZero : (z : ℂ).im = 0 := by linarith
      exact circle_eq_of_re_eq_of_im_nonpos z w hre hzZero.le (le_of_not_ge hw)
  · by_cases hw : 0 ≤ (w : ℂ).im
    · have hre : (z : ℂ).re = (w : ℂ).re := by
        simpa [leftThetaLoop, hz, hw] using congrArg Complex.im h
      have him : 0 = -(w : ℂ).im := by
        simpa [leftThetaLoop, hz, hw] using congrArg Complex.re h
      have hwZero : (w : ℂ).im = 0 := by linarith
      exact circle_eq_of_re_eq_of_im_nonpos z w hre (le_of_not_ge hz) hwZero.le
    · have hre : (z : ℂ).re = (w : ℂ).re := by
        simpa [leftThetaLoop, hz, hw] using congrArg Complex.im h
      exact circle_eq_of_re_eq_of_im_nonpos z w hre (le_of_not_ge hz) (le_of_not_ge hw)

/-- Helper for Exercise 58.4: the right theta-cycle parameterization is injective. -/
private theorem rightThetaLoop_injective : Function.Injective rightThetaLoop := by
  -- The symmetric semicircle decomposition again retains the active real coordinate.
  intro z w h
  by_cases hz : (z : ℂ).im ≤ 0
  · by_cases hw : (w : ℂ).im ≤ 0
    · have hre : (z : ℂ).re = (w : ℂ).re := by
        simpa [rightThetaLoop, hz, hw] using congrArg Complex.im h
      have him : -(z : ℂ).im = -(w : ℂ).im := by
        simpa [rightThetaLoop, hz, hw] using congrArg Complex.re h
      apply Circle.ext
      exact Complex.ext hre (by linarith)
    · have hre : (z : ℂ).re = (w : ℂ).re := by
        simpa [rightThetaLoop, hz, hw] using congrArg Complex.im h
      have him : -(z : ℂ).im = 0 := by
        simpa [rightThetaLoop, hz, hw] using congrArg Complex.re h
      have hzZero : (z : ℂ).im = 0 := by linarith
      exact circle_eq_of_re_eq_of_im_nonneg z w hre hzZero.symm.le (le_of_not_ge hw)
  · by_cases hw : (w : ℂ).im ≤ 0
    · have hre : (z : ℂ).re = (w : ℂ).re := by
        simpa [rightThetaLoop, hz, hw] using congrArg Complex.im h
      have him : 0 = -(w : ℂ).im := by
        simpa [rightThetaLoop, hz, hw] using congrArg Complex.re h
      have hwZero : (w : ℂ).im = 0 := by linarith
      exact circle_eq_of_re_eq_of_im_nonneg z w hre (le_of_not_ge hz) hwZero.symm.le
    · have hre : (z : ℂ).re = (w : ℂ).re := by
        simpa [rightThetaLoop, hz, hw] using congrArg Complex.im h
      exact circle_eq_of_re_eq_of_im_nonneg z w hre (le_of_not_ge hz) (le_of_not_ge hw)

/-- Helper for Exercise 58.4: the two theta-cycle parameterizations agree exactly on the
shared diameter fibers, apart from their common basepoint. -/
private theorem leftThetaLoop_eq_rightThetaLoop_iff (z w : Circle) :
    leftThetaLoop z = rightThetaLoop w ↔
      (z = 1 ∧ w = 1) ∨
        (w = z⁻¹ ∧ z ≠ 1 ∧ (z : ℂ).im ≤ 0) := by
  constructor
  · intro h
    -- Equality of imaginary outputs gives equal real circle coordinates in every branch.
    by_cases hz : 0 ≤ (z : ℂ).im
    · by_cases hw : (w : ℂ).im ≤ 0
      · have hre : (z : ℂ).re = (w : ℂ).re := by
          simpa [leftThetaLoop, rightThetaLoop, hz, hw] using congrArg Complex.im h
        have him : -(z : ℂ).im = -(w : ℂ).im := by
          simpa [leftThetaLoop, rightThetaLoop, hz, hw] using congrArg Complex.re h
        have hzZero : (z : ℂ).im = 0 := by linarith
        have hwZero : (w : ℂ).im = 0 := by linarith
        have hinv := circle_eq_inv_of_re_eq_of_im_nonpos_nonneg z w hre
          hzZero.le hwZero.symm.le
        by_cases hone : z = 1
        · left
          exact ⟨hone, by simpa [hone] using hinv⟩
        · right
          exact ⟨hinv, hone, hzZero.le⟩
      · have hre : (z : ℂ).re = (w : ℂ).re := by
          simpa [leftThetaLoop, rightThetaLoop, hz, hw] using congrArg Complex.im h
        have him : -(z : ℂ).im = 0 := by
          simpa [leftThetaLoop, rightThetaLoop, hz, hw] using congrArg Complex.re h
        have hzZero : (z : ℂ).im = 0 := by linarith
        have hinv := circle_eq_inv_of_re_eq_of_im_nonpos_nonneg z w hre
          hzZero.le (le_of_not_ge hw)
        by_cases hone : z = 1
        · left
          exact ⟨hone, by simpa [hone] using hinv⟩
        · right
          exact ⟨hinv, hone, hzZero.le⟩
    · by_cases hw : (w : ℂ).im ≤ 0
      · have hre : (z : ℂ).re = (w : ℂ).re := by
          simpa [leftThetaLoop, rightThetaLoop, hz, hw] using congrArg Complex.im h
        have him : 0 = -(w : ℂ).im := by
          simpa [leftThetaLoop, rightThetaLoop, hz, hw] using congrArg Complex.re h
        have hwZero : (w : ℂ).im = 0 := by linarith
        have hinv := circle_eq_inv_of_re_eq_of_im_nonpos_nonneg z w hre
          (le_of_not_ge hz) hwZero.symm.le
        by_cases hone : z = 1
        · left
          exact ⟨hone, by simpa [hone] using hinv⟩
        · right
          exact ⟨hinv, hone, le_of_not_ge hz⟩
      · have hre : (z : ℂ).re = (w : ℂ).re := by
          simpa [leftThetaLoop, rightThetaLoop, hz, hw] using congrArg Complex.im h
        have hinv := circle_eq_inv_of_re_eq_of_im_nonpos_nonneg z w hre
          (le_of_not_ge hz) (le_of_not_ge hw)
        by_cases hone : z = 1
        · left
          exact ⟨hone, by simpa [hone] using hinv⟩
        · right
          exact ⟨hinv, hone, le_of_not_ge hz⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, hzOne, hz⟩)
    · simp [leftThetaLoop, rightThetaLoop]
    · by_cases hzZero : (z : ℂ).im = 0
      · have hinvSelf : z⁻¹ = z := by
          apply Circle.ext
          rw [Circle.coe_inv_eq_conj]
          apply Complex.ext
          · simp
          · simp [hzZero]
        rw [hinvSelf]
        simp [leftThetaLoop, rightThetaLoop, hzZero]
      · have hzNeg : (z : ℂ).im < 0 := lt_of_le_of_ne hz hzZero
        have hzNotUpper : ¬0 ≤ (z : ℂ).im := not_le.mpr hzNeg
        apply Complex.ext
        · simp [leftThetaLoop, rightThetaLoop, hzNotUpper]
        · simp [leftThetaLoop, rightThetaLoop, hzNotUpper]

/-- Helper for Exercise 58.4: the fibers of the folding map are equality or paired points
on the shared diameter. -/
private theorem figureEightToTheta_fiberRelation (p q : FigureEight) :
    figureEightToTheta p = figureEightToTheta q ↔
      p = q ∨
        (p.1.2 = 1 ∧ q.1.1 = 1 ∧ q.1.2 = p.1.1⁻¹ ∧
          p.1.1 ≠ 1 ∧ (p.1.1 : ℂ).im ≤ 0) ∨
        (q.1.2 = 1 ∧ p.1.1 = 1 ∧ p.1.2 = q.1.1⁻¹ ∧
          q.1.1 ≠ 1 ∧ (q.1.1 : ℂ).im ≤ 0) := by
  constructor
  · intro h
    have hraw : figureEightToThetaRaw p = figureEightToThetaRaw q :=
      congrArg Subtype.val h
    by_cases hpLeft : p.1.2 = 1
    · by_cases hqLeft : q.1.2 = 1
      · have hactive : p.1.1 = q.1.1 := by
          apply leftThetaLoop_injective
          simpa [figureEightToThetaRaw, hpLeft, hqLeft] using hraw
        left
        apply Subtype.ext
        exact Prod.ext hactive (hpLeft.trans hqLeft.symm)
      · have hqRight : q.1.1 = 1 :=
          ((FigureEight.mem_iff q.1).1 q.2).resolve_left hqLeft
        have hcross : leftThetaLoop p.1.1 = rightThetaLoop q.1.2 := by
          simpa [figureEightToThetaRaw, hpLeft, hqLeft] using hraw
        rcases (leftThetaLoop_eq_rightThetaLoop_iff p.1.1 q.1.2).1 hcross with
          hbase | hpaired
        · exact (hqLeft hbase.2).elim
        · exact Or.inr (Or.inl ⟨hpLeft, hqRight, hpaired⟩)
    · have hpRight : p.1.1 = 1 :=
        ((FigureEight.mem_iff p.1).1 p.2).resolve_left hpLeft
      by_cases hqLeft : q.1.2 = 1
      · have hcross : leftThetaLoop q.1.1 = rightThetaLoop p.1.2 := by
          symm
          simpa [figureEightToThetaRaw, hpLeft, hqLeft] using hraw
        rcases (leftThetaLoop_eq_rightThetaLoop_iff q.1.1 p.1.2).1 hcross with
          hbase | hpaired
        · exact (hpLeft hbase.2).elim
        · exact Or.inr (Or.inr ⟨hqLeft, hpRight, hpaired⟩)
      · have hactive : p.1.2 = q.1.2 := by
          apply rightThetaLoop_injective
          simpa [figureEightToThetaRaw, hpLeft, hqLeft] using hraw
        left
        apply Subtype.ext
        exact Prod.ext (hpRight.trans (((FigureEight.mem_iff q.1).1 q.2).resolve_left
          hqLeft).symm) hactive
  · rintro (rfl | hpaired | hpaired)
    · rfl
    · rcases hpaired with ⟨hpLeft, hqRight, hqInv, hpNe, hpLower⟩
      have hqNotLeft : q.1.2 ≠ 1 := by
        rw [hqInv]
        simpa using hpNe
      apply Subtype.ext
      change figureEightToThetaRaw p = figureEightToThetaRaw q
      rw [figureEightToThetaRaw, if_pos hpLeft, figureEightToThetaRaw, if_neg hqNotLeft]
      exact (leftThetaLoop_eq_rightThetaLoop_iff p.1.1 q.1.2).2
        (Or.inr ⟨hqInv, hpNe, hpLower⟩)
    · rcases hpaired with ⟨hqLeft, hpRight, hpInv, hqNe, hqLower⟩
      have hpNotLeft : p.1.2 ≠ 1 := by
        rw [hpInv]
        simpa using hqNe
      apply Subtype.ext
      change figureEightToThetaRaw p = figureEightToThetaRaw q
      rw [figureEightToThetaRaw, if_neg hpNotLeft, figureEightToThetaRaw, if_pos hqLeft]
      exact ((leftThetaLoop_eq_rightThetaLoop_iff q.1.1 p.1.2).2
        (Or.inr ⟨hpInv, hqNe, hqLower⟩)).symm

/-- Helper for Exercise 58.4: the figure-eight homotopy preserves a paired shared-diameter
fiber with the left representative listed first. -/
private theorem figureEightFoldHomotopy_preserves_pairedFiber (t : unitInterval)
    (p q : FigureEight) (hpLeft : p.1.2 = 1) (hqInv : q.1.2 = p.1.1⁻¹)
    (hpNe : p.1.1 ≠ 1) (hpLower : (p.1.1 : ℂ).im ≤ 0) :
    figureEightToTheta (figureEightFoldHomotopyValue t p) =
      figureEightToTheta (figureEightFoldHomotopyValue t q) := by
  -- The right representative remains on its branch because inversion does not send a
  -- non-basepoint to the basepoint.
  have hqNotLeft : q.1.2 ≠ 1 := by
    rw [hqInv]
    simpa using hpNe
  have hpPair : figureEightFoldHomotopyPair t p =
      (circleFoldHomotopyValue t p.1.1, 1) := by
    rw [figureEightFoldHomotopyPair, if_pos hpLeft]
  have hqPair : figureEightFoldHomotopyPair t q =
      (1, lowerCircleFoldHomotopyValue t q.1.2) := by
    rw [figureEightFoldHomotopyPair, if_neg hqNotLeft]
  by_cases hnewBasepoint : circleFoldHomotopyValue t p.1.1 = 1
  · -- If the moving point reaches the basepoint, both representatives become identical.
    apply congrArg figureEightToTheta
    apply Subtype.ext
    apply Prod.ext
    · simp [figureEightFoldHomotopyValue, hpPair, hqPair, hnewBasepoint]
    · simp [figureEightFoldHomotopyValue, hpPair, hqPair, hqInv,
        lowerCircleFoldHomotopyValue, hnewBasepoint]
  · -- Otherwise the fiber relation is preserved by inversion and the semicircle invariant.
    apply (figureEightToTheta_fiberRelation _ _).2
    right
    left
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [figureEightFoldHomotopyValue, hpPair]
    · simp [figureEightFoldHomotopyValue, hqPair]
    · simp [figureEightFoldHomotopyValue, hpPair, hqPair,
        hqInv, lowerCircleFoldHomotopyValue]
    · simpa [figureEightFoldHomotopyValue, hpPair]
        using hnewBasepoint
    · simpa [figureEightFoldHomotopyValue, hpPair]
        using circleFoldHomotopyValue_im_nonpos t p.1.1 hpLower

/-- Helper for Exercise 58.4: the figure-eight homotopy is constant on every fiber of the
folding map. -/
private theorem figureEightFoldHomotopy_fiberCompatible (t : unitInterval) (p q : FigureEight)
    (h : figureEightToTheta p = figureEightToTheta q) :
    figureEightToTheta (figureEightFoldHomotopyValue t p) =
      figureEightToTheta (figureEightFoldHomotopyValue t q) := by
  -- The canonical fiber classification reduces compatibility to one oriented paired case.
  rcases (figureEightToTheta_fiberRelation p q).1 h with rfl | hpaired | hpaired
  · rfl
  · exact figureEightFoldHomotopy_preserves_pairedFiber t p q
      hpaired.1 hpaired.2.2.1 hpaired.2.2.2.1 hpaired.2.2.2.2
  · exact (figureEightFoldHomotopy_preserves_pairedFiber t q p
      hpaired.1 hpaired.2.2.1 hpaired.2.2.2.1 hpaired.2.2.2.2).symm

/-- Helper for Exercise 58.4: rotating a unit complex number by `-I` gives a circle point. -/
private theorem neg_I_mul_mem_circle (z : ℂ) (hz : ‖z‖ = 1) :
    -Complex.I * z ∈ Submonoid.unitSphere ℂ := by
  -- Rotation has norm one and preserves the norm of `z`.
  simp [Submonoid.unitSphere, hz]

/-- Helper for Exercise 58.4: the circle point obtained by rotating a unit complex number. -/
private def rotatedCirclePoint (z : ℂ) (hz : ‖z‖ = 1) : Circle :=
  ⟨-Complex.I * z, neg_I_mul_mem_circle z hz⟩

/-- Helper for Exercise 58.4: the explicit lower-semicircle point over a real coordinate
in `Set.Icc (-1) 1` lies on the unit circle. -/
private theorem lowerSemicircleRaw_mem (s : ℝ) (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    (s : ℂ) - (Real.sqrt (1 - s ^ 2) : ℝ) * Complex.I ∈ Submonoid.unitSphere ℂ := by
  -- The square-root coordinate completes `s ^ 2` to the circle equation.
  have hradicand : 0 ≤ 1 - s ^ 2 := by
    rcases hs with ⟨hsLower, hsUpper⟩
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - s) (by linarith : 0 ≤ 1 + s)]
  have hnormSq : Complex.normSq
      ((s : ℂ) - (Real.sqrt (1 - s ^ 2) : ℝ) * Complex.I) = 1 := by
    simp only [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, sub_zero, Complex.sub_im, Complex.I_im,
      Complex.mul_im, mul_one, add_zero, zero_sub]
    nlinarith [Real.sq_sqrt hradicand]
  have hnorm : ‖(s : ℂ) - (Real.sqrt (1 - s ^ 2) : ℝ) * Complex.I‖ = 1 := by
    rw [Complex.norm_def, hnormSq]
    norm_num
  simpa [Submonoid.unitSphere] using hnorm

/-- Helper for Exercise 58.4: the lower-semicircle point with prescribed real coordinate. -/
private def lowerSemicirclePoint (s : ℝ) (hs : s ∈ Set.Icc (-1 : ℝ) 1) : Circle :=
  ⟨(s : ℂ) - (Real.sqrt (1 - s ^ 2) : ℝ) * Complex.I,
    lowerSemicircleRaw_mem s hs⟩

/-- Helper for Exercise 58.4: a circle point placed on the left coordinate circle of the
figure eight. -/
private def figureEightLeftPoint (z : Circle) : FigureEight :=
  ⟨(z, 1), (FigureEight.mem_iff (z, 1)).2 (Or.inl rfl)⟩

/-- Helper for Exercise 58.4: a circle point placed on the right coordinate circle of the
figure eight. -/
private def figureEightRightPoint (z : Circle) : FigureEight :=
  ⟨(1, z), (FigureEight.mem_iff (1, z)).2 (Or.inr rfl)⟩

/-- Helper for Exercise 58.4: folding a point on the left coordinate circle applies the
left theta-cycle parameterization. -/
private theorem figureEightToTheta_leftPoint_coe (z : Circle) :
    ((figureEightToTheta (figureEightLeftPoint z) : PlanarTheta) : ℂ) = leftThetaLoop z := by
  -- Unfold only the coordinate-circle wrapper and the folding projection.
  simp [figureEightToTheta, figureEightToThetaFunction, figureEightToThetaRaw,
    figureEightLeftPoint]

/-- Helper for Exercise 58.4: folding a non-basepoint on the right coordinate circle applies
the right theta-cycle parameterization. -/
private theorem figureEightToTheta_rightPoint_coe (z : Circle) (hz : z ≠ 1) :
    ((figureEightToTheta (figureEightRightPoint z) : PlanarTheta) : ℂ) = rightThetaLoop z := by
  -- The non-basepoint hypothesis selects the right branch of the folding formula.
  simp [figureEightToTheta, figureEightToThetaFunction, figureEightToThetaRaw,
    figureEightRightPoint, hz]

/-- Helper for Exercise 58.4: the explicit folding map onto the theta space is surjective. -/
private theorem figureEightToTheta_surjective : Function.Surjective figureEightToTheta := by
  intro y
  rcases (PlanarTheta.mem_iff y.1).1 y.2 with hcircle | hdiameter
  · let z : Circle := rotatedCirclePoint y.1 hcircle
    by_cases hyLeft : y.1.re ≤ 0
    · refine ⟨figureEightLeftPoint z, ?_⟩
      apply Subtype.ext
      rw [figureEightToTheta_leftPoint_coe]
      have hzUpper : 0 ≤ (z : ℂ).im := by
        simp [z, rotatedCirclePoint]
        linarith
      have hloop : leftThetaLoop z = Complex.I * (z : ℂ) := by
        simp [leftThetaLoop, hzUpper]
      rw [hloop]
      simp only [z, rotatedCirclePoint]
      rw [← mul_assoc, mul_neg, Complex.I_mul_I]
      simp
    · have hyRight : 0 < y.1.re := lt_of_not_ge hyLeft
      have hzLower : (z : ℂ).im ≤ 0 := by
        simp [z, rotatedCirclePoint]
        linarith
      have hzNe : z ≠ 1 := by
        intro hzOne
        have him := congrArg (fun w : Circle ↦ ((w : ℂ).im)) hzOne
        simp [z, rotatedCirclePoint] at him
        linarith
      refine ⟨figureEightRightPoint z, ?_⟩
      apply Subtype.ext
      rw [figureEightToTheta_rightPoint_coe z hzNe]
      have hloop : rightThetaLoop z = Complex.I * (z : ℂ) := by
        simp [rightThetaLoop, hzLower]
      rw [hloop]
      simp only [z, rotatedCirclePoint]
      rw [← mul_assoc, mul_neg, Complex.I_mul_I]
      simp
  · rcases hdiameter with ⟨hyRe, hyIm⟩
    let z : Circle := lowerSemicirclePoint y.1.im hyIm
    refine ⟨figureEightLeftPoint z, ?_⟩
    apply Subtype.ext
    rw [figureEightToTheta_leftPoint_coe]
    by_cases hsqrt : Real.sqrt (1 - y.1.im ^ 2) = 0
    · have hzIm : (z : ℂ).im = 0 := by
        simp [z, lowerSemicirclePoint, hsqrt]
      have hzRe : (z : ℂ).re = y.1.im := by
        simp [z, lowerSemicirclePoint]
      have hloop : leftThetaLoop z = Complex.I * (z : ℂ) := by
        simp [leftThetaLoop, hzIm]
      rw [hloop]
      apply Complex.ext
      · simp [Complex.mul_re, hzIm, hyRe]
      · simp [Complex.mul_im, hzRe]
    · have hsqrtPos : 0 < Real.sqrt (1 - y.1.im ^ 2) :=
        lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hsqrt)
      have hzIm : (z : ℂ).im = -Real.sqrt (1 - y.1.im ^ 2) := by
        simp [z, lowerSemicirclePoint]
      have hzRe : (z : ℂ).re = y.1.im := by
        simp [z, lowerSemicirclePoint]
      have hzLower : ¬0 ≤ (z : ℂ).im := by
        rw [hzIm]
        linarith
      have hloop : leftThetaLoop z = Complex.I * ((z : ℂ).re : ℂ) := by
        simp [leftThetaLoop, hzLower]
      rw [hloop]
      apply Complex.ext
      · simp [Complex.mul_re, hyRe]
      · simp [Complex.mul_im, hzRe]

/-- Helper for Exercise 58.4: the figure-eight carrier is closed in the torus. -/
private theorem isClosed_figureEight_carrier : IsClosed FigureEight.carrier := by
  -- Each coordinate circle is a closed equality locus, and the carrier is their union.
  have hsnd : Continuous fun z : Torus ↦ z.2 := continuous_snd
  have hfst : Continuous fun z : Torus ↦ z.1 := continuous_fst
  have hcarrier : FigureEight.carrier =
      {z : Torus | z.2 = 1} ∪ {z : Torus | z.1 = 1} := by
    ext z
    rw [FigureEight.mem_iff]
    simp only [Set.mem_union, Set.mem_setOf_eq]
  rw [hcarrier]
  exact (isClosed_eq hsnd continuous_const).union (isClosed_eq hfst continuous_const)

/-- Helper for Exercise 58.4: the figure eight inherits compactness from the compact torus. -/
private theorem figureEight_compactSpace : CompactSpace FigureEight := by
  -- A closed subspace of the compact torus is compact.
  exact isCompact_iff_compactSpace.mp isClosed_figureEight_carrier.isCompact

/-- Helper for Exercise 58.4: the folding map presents the theta space as a quotient of the
figure eight. -/
private theorem figureEightToTheta_isQuotientMap :
    Topology.IsQuotientMap figureEightToTheta := by
  -- Compact-to-Hausdorff continuous surjections are quotient maps.
  letI : CompactSpace FigureEight := figureEight_compactSpace
  exact Topology.IsQuotientMap.of_surjective_continuous
    figureEightToTheta_surjective figureEightToTheta.continuous

/-- Helper for Exercise 58.4: a selected figure-eight representative of each theta point. -/
private def figureEightRepresentative (y : PlanarTheta) : FigureEight :=
  Function.surjInv figureEightToTheta_surjective y

/-- Helper for Exercise 58.4: the selected figure-eight representative projects to its
original theta point. -/
private theorem figureEightRepresentative_spec (y : PlanarTheta) :
    figureEightToTheta (figureEightRepresentative y) = y := by
  -- This is the defining right-inverse property of the surjective choice.
  exact Function.surjInv_eq figureEightToTheta_surjective y

/-- Helper for Exercise 58.4: the pointwise theta homotopy obtained from a selected
figure-eight representative. -/
private def thetaFoldHomotopyValue (t : unitInterval) (y : PlanarTheta) : PlanarTheta :=
  figureEightToTheta (figureEightFoldHomotopyValue t (figureEightRepresentative y))

/-- Helper for Exercise 58.4: the descended theta homotopy agrees with the figure-eight
homotopy on every representative. -/
private theorem thetaFoldHomotopyValue_spec (t : unitInterval) (p : FigureEight) :
    thetaFoldHomotopyValue t (figureEightToTheta p) =
      figureEightToTheta (figureEightFoldHomotopyValue t p) := by
  -- Fiber compatibility removes the arbitrary representative chosen by `surjInv`.
  apply figureEightFoldHomotopy_fiberCompatible
  exact Function.surjInv_eq figureEightToTheta_surjective (figureEightToTheta p)

/-- Helper for Exercise 58.4: the quotient-descended theta homotopy is continuous. -/
private theorem continuous_thetaFoldHomotopyValue :
    Continuous fun q : unitInterval × PlanarTheta ↦ thetaFoldHomotopyValue q.1 q.2 := by
  -- Test continuity after the quotient map on the figure-eight coordinate.
  apply figureEightToTheta_isQuotientMap.continuous_lift_prod_right
  have hcontinuous : Continuous fun q : unitInterval × FigureEight ↦
      figureEightToTheta (figureEightFoldHomotopyValue q.1 q.2) :=
    figureEightToTheta.continuous.comp continuous_figureEightFoldHomotopyValue
  exact hcontinuous.congr fun q ↦ (thetaFoldHomotopyValue_spec q.1 q.2).symm

/-- Helper for Exercise 58.4: the descended theta homotopy starts at the stated composite. -/
private theorem thetaFoldHomotopyValue_zero (y : PlanarTheta) :
    thetaFoldHomotopyValue 0 y = figureEightToTheta (thetaToFigureEight y) := by
  -- The chosen representative projects to `y`, so the figure-eight zero endpoint descends.
  rw [thetaFoldHomotopyValue, figureEightFoldHomotopyValue_zero,
    figureEightRepresentative_spec]

/-- Helper for Exercise 58.4: the descended theta homotopy ends at the identity. -/
private theorem thetaFoldHomotopyValue_one (y : PlanarTheta) :
    thetaFoldHomotopyValue 1 y = y := by
  -- The figure-eight endpoint is the representative itself, which projects back to `y`.
  rw [thetaFoldHomotopyValue, figureEightFoldHomotopyValue_one,
    figureEightRepresentative_spec]

/-- Helper for Exercise 58.4: the quotient-descended homotopy from the theta composite to
the identity. -/
private def thetaFoldHomotopy :
    ContinuousMap.Homotopy (figureEightToTheta.comp thetaToFigureEight)
      (ContinuousMap.id PlanarTheta) :=
  {
    toFun := fun q ↦ thetaFoldHomotopyValue q.1 q.2
    continuous_toFun := continuous_thetaFoldHomotopyValue
    map_zero_left := thetaFoldHomotopyValue_zero
    map_one_left := thetaFoldHomotopyValue_one
  }

/-- The inverse map followed by the folding map is homotopic to the identity on the figure
eight. -/
theorem thetaToFigureEight_comp_figureEightToTheta :
    (thetaToFigureEight.comp figureEightToTheta).Homotopic
      (ContinuousMap.id FigureEight) := by
  -- Package the pasted coordinate homotopy.
  exact ⟨figureEightFoldHomotopy⟩

/-- Exercise 58.4: the folding map followed by the inverse map is homotopic to the identity
on the theta space. -/
theorem figureEightToTheta_comp_thetaToFigureEight :
    (figureEightToTheta.comp thetaToFigureEight).Homotopic
      (ContinuousMap.id PlanarTheta) := by
  -- Descend the fiber-compatible figure-eight homotopy through the quotient folding map.
  exact ⟨thetaFoldHomotopy⟩

/-- The explicit homotopy equivalence between the figure eight and the theta space. -/
def figureEightHomotopyEquiv : FigureEight ≃ₕ PlanarTheta :=
  ⟨figureEightToTheta, thetaToFigureEight,
    thetaToFigureEight_comp_figureEightToTheta,
    figureEightToTheta_comp_thetaToFigureEight⟩

/-- The forward map of `figureEightHomotopyEquiv` is the explicit folding map. -/
theorem figureEightHomotopyEquiv_toFun :
    figureEightHomotopyEquiv.toFun = figureEightToTheta := by
  -- The constructor stores the explicit folding map as its forward map.
  rfl
