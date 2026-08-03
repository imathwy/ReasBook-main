module

public import Topology_Munkres_2000.Book.Definition_61_2.Arc
public import Topology_Munkres_2000.Book.Theorem_63_5
import Topology_Munkres_2000.Book.Theorem_63_2

public section

open Set

namespace LoopWithTail

/-- The upper equatorial semicircle continued along the meridian tail. -/
def upperArcWithTail : Set (StandardSphere 2) :=
  {x | ((x : EuclideanSpace ℝ (Fin 3)) 2 = 0 ∧
      0 ≤ (x : EuclideanSpace ℝ (Fin 3)) 1) ∨
    ((x : EuclideanSpace ℝ (Fin 3)) 1 = 0 ∧
      0 ≤ (x : EuclideanSpace ℝ (Fin 3)) 0 ∧
      0 ≤ (x : EuclideanSpace ℝ (Fin 3)) 2)}

/-- The lower equatorial semicircle in Figure 63.5. -/
def lowerArc : Set (StandardSphere 2) :=
  {x | (x : EuclideanSpace ℝ (Fin 3)) 2 = 0 ∧
    (x : EuclideanSpace ℝ (Fin 3)) 1 ≤ 0}

/-- Helper for Example 63.1: the real and imaginary coordinates of a circle point,
followed by zero, form a point of the standard two-sphere. -/
private lemma equatorCoordinates_mem_standardSphere (z : Circle) :
    !₂[z.1.re, z.1.im, 0] ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  -- Square the norm and reduce it to the unit-norm identity for `z`.
  rw [Metric.mem_sphere, dist_zero_right]
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one]
  rw [PiLp.norm_sq_eq_of_L2]
  have hunit : z.1.re ^ 2 + z.1.im ^ 2 = 1 := by
    calc
      z.1.re ^ 2 + z.1.im ^ 2 = Complex.normSq z.1 := by
        rw [Complex.normSq_apply]
        ring
      _ = ‖z.1‖ ^ 2 := Complex.normSq_eq_norm_sq z.1
      _ = 1 := by rw [Circle.norm_coe]; norm_num
  simpa [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs] using hunit

/-- Helper for Example 63.1: the equatorial inclusion of the complex unit circle. -/
private def equatorMap (z : Circle) : StandardSphere 2 :=
  ⟨!₂[z.1.re, z.1.im, 0], equatorCoordinates_mem_standardSphere z⟩

/-- Helper for Example 63.1: the equatorial inclusion is continuous. -/
private lemma continuous_equatorMap : Continuous equatorMap := by
  -- Continuity is coordinatewise before passing to the sphere subtype.
  apply continuous_induced_rng.mpr
  fun_prop

/-- Helper for Example 63.1: the equatorial inclusion is injective. -/
private lemma injective_equatorMap : Function.Injective equatorMap := by
  -- Equality of the first two coordinates is equality of the underlying complex points.
  intro z w hzw
  apply Subtype.ext
  apply Complex.ext
  · exact congrArg (fun x : StandardSphere 2 ↦
      (x : EuclideanSpace ℝ (Fin 3)) 0) hzw
  · exact congrArg (fun x : StandardSphere 2 ↦
      (x : EuclideanSpace ℝ (Fin 3)) 1) hzw

/-- Helper for Example 63.1: the real and imaginary coordinates of a circle point in
the first and third positions form a point of the standard two-sphere. -/
private lemma meridianCoordinates_mem_standardSphere (z : Circle) :
    !₂[z.1.re, 0, z.1.im] ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  -- The same unit-norm identity applies after permuting the coordinates.
  rw [Metric.mem_sphere, dist_zero_right]
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one]
  rw [PiLp.norm_sq_eq_of_L2]
  have hunit : z.1.re ^ 2 + z.1.im ^ 2 = 1 := by
    calc
      z.1.re ^ 2 + z.1.im ^ 2 = Complex.normSq z.1 := by
        rw [Complex.normSq_apply]
        ring
      _ = ‖z.1‖ ^ 2 := Complex.normSq_eq_norm_sq z.1
      _ = 1 := by rw [Circle.norm_coe]; norm_num
  simpa [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, add_comm] using hunit

/-- Helper for Example 63.1: the meridian inclusion of the complex unit circle. -/
private def meridianMap (z : Circle) : StandardSphere 2 :=
  ⟨!₂[z.1.re, 0, z.1.im], meridianCoordinates_mem_standardSphere z⟩

/-- Helper for Example 63.1: the meridian inclusion is continuous. -/
private lemma continuous_meridianMap : Continuous meridianMap := by
  -- Continuity is again checked on the three ambient coordinates.
  apply continuous_induced_rng.mpr
  fun_prop

/-- Helper for Example 63.1: the meridian inclusion is injective. -/
private lemma injective_meridianMap : Function.Injective meridianMap := by
  -- The first and third coordinates recover the underlying complex point.
  intro z w hzw
  apply Subtype.ext
  apply Complex.ext
  · exact congrArg (fun x : StandardSphere 2 ↦
      (x : EuclideanSpace ℝ (Fin 3)) 0) hzw
  · exact congrArg (fun x : StandardSphere 2 ↦
      (x : EuclideanSpace ℝ (Fin 3)) 2) hzw

/-- Helper for Example 63.1: the squares of the three coordinates of a point on
the standard two-sphere sum to one. -/
private lemma coordinate_sq_sum_eq_one (x : StandardSphere 2) :
    (x : EuclideanSpace ℝ (Fin 3)) 0 ^ 2 +
      (x : EuclideanSpace ℝ (Fin 3)) 1 ^ 2 +
      (x : EuclideanSpace ℝ (Fin 3)) 2 ^ 2 = 1 := by
  -- Square the defining norm equation of the sphere and expand the finite sum.
  have hnorm : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    have hnormSphere := x.2
    rw [Metric.mem_sphere, dist_zero_right] at hnormSphere
    exact hnormSphere
  have hnormSq : ‖(x : EuclideanSpace ℝ (Fin 3))‖ ^ 2 = 1 := by
    rw [hnorm]
    norm_num
  rw [PiLp.norm_sq_eq_of_L2] at hnormSq
  simpa [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, add_assoc] using hnormSq

/-- Helper for Example 63.1: a sphere point on the equatorial plane determines a
point of the complex unit circle. -/
private lemma equatorialComplex_mem_circle (x : StandardSphere 2)
    (hx : (x : EuclideanSpace ℝ (Fin 3)) 2 = 0) :
    ((x : EuclideanSpace ℝ (Fin 3)) 0 : ℂ) +
        (x : EuclideanSpace ℝ (Fin 3)) 1 * Complex.I ∈
      Metric.sphere (0 : ℂ) 1 := by
  -- The missing third coordinate reduces the sphere equation to the complex norm.
  have hsum := coordinate_sq_sum_eq_one x
  rw [hx] at hsum
  norm_num at hsum
  rw [Metric.mem_sphere, dist_zero_right, Complex.norm_add_mul_I, hsum,
    Real.sqrt_one]

/-- Helper for Example 63.1: the circle point recovered from an equatorial sphere point. -/
private def equatorialCircle (x : StandardSphere 2)
    (hx : (x : EuclideanSpace ℝ (Fin 3)) 2 = 0) : Circle :=
  ⟨((x : EuclideanSpace ℝ (Fin 3)) 0 : ℂ) +
      (x : EuclideanSpace ℝ (Fin 3)) 1 * Complex.I,
    equatorialComplex_mem_circle x hx⟩

/-- Helper for Example 63.1: equatorial inclusion after equatorial recovery is the
original sphere point. -/
private lemma equatorMap_equatorialCircle (x : StandardSphere 2)
    (hx : (x : EuclideanSpace ℝ (Fin 3)) 2 = 0) :
    equatorMap (equatorialCircle x hx) = x := by
  -- Compare the three ambient coordinates, using `hx` in the last coordinate.
  apply Subtype.ext
  ext i
  fin_cases i
  · norm_num [equatorMap, equatorialCircle]
  · norm_num [equatorMap, equatorialCircle]
  · simpa [equatorMap, equatorialCircle] using hx.symm

/-- Helper for Example 63.1: a sphere point on the meridian plane determines a
point of the complex unit circle. -/
private lemma meridianComplex_mem_circle (x : StandardSphere 2)
    (hx : (x : EuclideanSpace ℝ (Fin 3)) 1 = 0) :
    ((x : EuclideanSpace ℝ (Fin 3)) 0 : ℂ) +
        (x : EuclideanSpace ℝ (Fin 3)) 2 * Complex.I ∈
      Metric.sphere (0 : ℂ) 1 := by
  -- The missing second coordinate reduces the sphere equation to the complex norm.
  have hsum := coordinate_sq_sum_eq_one x
  rw [hx] at hsum
  norm_num at hsum
  rw [Metric.mem_sphere, dist_zero_right, Complex.norm_add_mul_I, hsum,
    Real.sqrt_one]

/-- Helper for Example 63.1: the circle point recovered from a meridional sphere point. -/
private def meridianCircle (x : StandardSphere 2)
    (hx : (x : EuclideanSpace ℝ (Fin 3)) 1 = 0) : Circle :=
  ⟨((x : EuclideanSpace ℝ (Fin 3)) 0 : ℂ) +
      (x : EuclideanSpace ℝ (Fin 3)) 2 * Complex.I,
    meridianComplex_mem_circle x hx⟩

/-- Helper for Example 63.1: meridian inclusion after meridian recovery is the
original sphere point. -/
private lemma meridianMap_meridianCircle (x : StandardSphere 2)
    (hx : (x : EuclideanSpace ℝ (Fin 3)) 1 = 0) :
    meridianMap (meridianCircle x hx) = x := by
  -- Compare the three ambient coordinates, using `hx` in the middle coordinate.
  apply Subtype.ext
  ext i
  fin_cases i
  · norm_num [meridianMap, meridianCircle]
  · simpa [meridianMap, meridianCircle] using hx.symm
  · simp only [meridianMap, meridianCircle, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, zero_add,
      mul_one, mul_zero, add_zero]
    apply congrArg (x : EuclideanSpace ℝ (Fin 3))
    exact Fin.ext rfl

/-- Helper for Example 63.1: the complex number `I` lies on the unit circle. -/
private lemma complexI_mem_circle :
    Complex.I ∈ Metric.sphere (0 : ℂ) 1 := by
  -- Its norm is one.
  norm_num [Metric.mem_sphere, dist_zero_right]

/-- Helper for Example 63.1: the north point of the complex unit circle. -/
private def circleI : Circle :=
  ⟨Complex.I, complexI_mem_circle⟩

/-- Helper for Example 63.1: the upper semicircle is the counterclockwise circle
path from `1` to `-1`. -/
private lemma mem_range_circlePath_one_negOne_iff (z : Circle) :
    z ∈ Set.range (Circle.path 1 (-1)) ↔ 0 ≤ z.1.im := by
  -- `Circle.range_path` identifies this path with angles in `[0, π]`.
  rw [Circle.range_path]
  simp only [Circle.angleDiff, Set.mem_image, Set.mem_Icc]
  norm_num [Complex.arg_neg_one]
  rw [if_pos Real.pi_pos.le]
  constructor
  · rintro ⟨θ, ⟨hθ0, hθπ⟩, rfl⟩
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
    exact Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθπ
  · intro hz
    refine ⟨Complex.arg z.1, ⟨Complex.arg_nonneg_iff.mpr hz,
      Complex.arg_le_pi z.1⟩, ?_⟩
    exact Circle.exp_arg z

/-- Helper for Example 63.1: the lower semicircle is the counterclockwise circle
path from `-1` to `1`. -/
private lemma mem_range_circlePath_negOne_one_iff (z : Circle) :
    z ∈ Set.range (Circle.path (-1) 1) ↔ z.1.im ≤ 0 := by
  -- Use the complementary pair of semicircle paths, including both shared endpoints.
  have hupper := mem_range_circlePath_one_negOne_iff z
  constructor
  · intro hz
    by_contra hzIm
    have hzUpper : z ∈ Set.range (Circle.path 1 (-1)) :=
      hupper.mpr (le_of_not_ge hzIm)
    have hzEnds : z ∈ ({(1 : Circle), (-1 : Circle)} : Set Circle) := by
      rw [← Circle.range_path_inter_range_path (Circle.neg_ne_self 1).symm]
      exact ⟨hzUpper, hz⟩
    rcases hzEnds with hzOne | hzNegOne
    · subst z
      norm_num at hzIm
    · subst z
      norm_num at hzIm
  · intro hzIm
    have hzUnion :
        z ∈ Set.range (Circle.path 1 (-1)) ∪
          Set.range (Circle.path (-1) 1) := by
      rw [Circle.range_path_union_range_path (Circle.neg_ne_self 1).symm]
      exact Set.mem_univ z
    rcases hzUnion with hzUpper | hzLower
    · have hzImZero : z.1.im = 0 := le_antisymm hzIm (hupper.mp hzUpper)
      by_cases hzRe : 0 ≤ z.1.re
      · have hzOne : z = 1 := Circle.arg_eq_zero.mp
          (Complex.arg_eq_zero_iff.mpr ⟨hzRe, hzImZero⟩)
        rw [hzOne]
        exact Path.target_mem_range (Circle.path (-1) 1)
      · have hzArg : Complex.arg z.1 = Real.pi :=
          Complex.arg_eq_pi_iff.mpr ⟨lt_of_not_ge hzRe, hzImZero⟩
        have hnegArg : Complex.arg ((-1 : Circle).1) = Real.pi := by norm_num
        have hzNegOne : z = -1 := by
          apply Circle.injective_arg
          exact hzArg.trans hnegArg.symm
        rw [hzNegOne]
        exact Path.source_mem_range (Circle.path (-1) 1)
    · exact hzLower

/-- Helper for Example 63.1: the first-quarter circle path consists exactly of
circle points with nonnegative real and imaginary parts. -/
private lemma mem_range_circlePath_one_I_iff (z : Circle) :
    z ∈ Set.range (Circle.path 1 circleI) ↔ 0 ≤ z.1.re ∧ 0 ≤ z.1.im := by
  -- `Circle.range_path` identifies this quarter-circle with angles in `[0, π / 2]`.
  rw [Circle.range_path]
  simp only [Circle.angleDiff, Set.mem_image, Set.mem_Icc]
  norm_num [circleI, Complex.arg_I]
  have hpiHalfNonneg : 0 ≤ Real.pi / 2 := by positivity
  have hpiHalfLePi : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  rw [if_pos hpiHalfNonneg]
  constructor
  · rintro ⟨θ, ⟨hθ0, hθπ⟩, rfl⟩
    have hθLower : -(Real.pi / 2) ≤ θ := by linarith [Real.pi_pos]
    have hθLePi : θ ≤ Real.pi := hθπ.trans hpiHalfLePi
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
    constructor
    · exact Real.cos_nonneg_of_mem_Icc ⟨hθLower, hθπ⟩
    · exact Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθLePi
  · rintro ⟨hzRe, hzIm⟩
    refine ⟨Complex.arg z.1, ⟨Complex.arg_nonneg_iff.mpr hzIm, ?_⟩,
      Circle.exp_arg z⟩
    exact Complex.arg_le_pi_div_two_iff.mpr (Or.inl hzRe)

/-- Helper for Example 63.1: the mapped lower circle path has exactly the lower
equatorial semicircle as its range. -/
private lemma range_lowerEquatorPath :
    Set.range ((Circle.path (-1) 1).map continuous_equatorMap) = lowerArc := by
  -- Translate circle-path membership to the sign of the second sphere coordinate.
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨rfl, (mem_range_circlePath_negOne_one_iff _).mp
      (Set.mem_range_self t)⟩
  · rintro ⟨hxPlane, hxSign⟩
    let z := equatorialCircle x hxPlane
    have hzSign : z.1.im ≤ 0 := by
      simpa [z, equatorialCircle] using hxSign
    obtain ⟨t, ht⟩ := (mem_range_circlePath_negOne_one_iff z).mpr hzSign
    refine ⟨t, ?_⟩
    calc
      ((Circle.path (-1) 1).map continuous_equatorMap) t =
          equatorMap ((Circle.path (-1) 1) t) := rfl
      _ = equatorMap z := congrArg equatorMap ht
      _ = x := equatorMap_equatorialCircle x hxPlane

/-- Helper for Example 63.1: the mapped upper circle path has exactly the upper
equatorial semicircle as its range. -/
private lemma range_upperEquatorPath :
    Set.range ((Circle.path 1 (-1)).map continuous_equatorMap) =
      {x : StandardSphere 2 | (x : EuclideanSpace ℝ (Fin 3)) 2 = 0 ∧
        0 ≤ (x : EuclideanSpace ℝ (Fin 3)) 1} := by
  -- Translate circle-path membership to the sign of the second sphere coordinate.
  apply Set.ext
  intro x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨rfl, (mem_range_circlePath_one_negOne_iff _).mp
      (Set.mem_range_self t)⟩
  · rintro ⟨hxPlane, hxSign⟩
    let z := equatorialCircle x hxPlane
    have hzSign : 0 ≤ z.1.im := by
      simpa [z, equatorialCircle] using hxSign
    obtain ⟨t, ht⟩ := (mem_range_circlePath_one_negOne_iff z).mpr hzSign
    refine ⟨t, ?_⟩
    calc
      ((Circle.path 1 (-1)).map continuous_equatorMap) t =
          equatorMap ((Circle.path 1 (-1)) t) := rfl
      _ = equatorMap z := congrArg equatorMap ht
      _ = x := equatorMap_equatorialCircle x hxPlane

/-- Helper for Example 63.1: the mapped first-quarter circle path has exactly the
positive meridian quarter as its range. -/
private lemma range_positiveMeridianPath :
    Set.range ((Circle.path 1 circleI).map continuous_meridianMap) =
      {x : StandardSphere 2 | (x : EuclideanSpace ℝ (Fin 3)) 1 = 0 ∧
        0 ≤ (x : EuclideanSpace ℝ (Fin 3)) 0 ∧
        0 ≤ (x : EuclideanSpace ℝ (Fin 3)) 2} := by
  -- Translate quarter-circle membership to the two nonnegative sphere coordinates.
  apply Set.ext
  intro x
  constructor
  · rintro ⟨t, rfl⟩
    have ht := (mem_range_circlePath_one_I_iff _).mp (Set.mem_range_self t)
    exact ⟨rfl, ht.1, ht.2⟩
  · rintro ⟨hxPlane, hxFirst, hxThird⟩
    let z := meridianCircle x hxPlane
    have hzSigns : 0 ≤ z.1.re ∧ 0 ≤ z.1.im := by
      simpa [z, meridianCircle] using And.intro hxFirst hxThird
    obtain ⟨t, ht⟩ := (mem_range_circlePath_one_I_iff z).mpr hzSigns
    refine ⟨t, ?_⟩
    calc
      ((Circle.path 1 circleI).map continuous_meridianMap) t =
          meridianMap ((Circle.path 1 circleI) t) := rfl
      _ = meridianMap z := congrArg meridianMap ht
      _ = x := meridianMap_meridianCircle x hxPlane

/-- Helper for Example 63.1: concatenating two injective paths that meet only at
their common endpoint gives an injective path. -/
private lemma injective_pathTrans_of_range_inter_eq_singleton
    {X : Type*} [TopologicalSpace X] {a b c : X}
    (γ : Path a b) (δ : Path b c)
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hinter : Set.range γ ∩ Set.range δ = {b}) :
    Function.Injective (γ.trans δ) := by
  -- Compare the two half-interval formulas for the concatenated path.
  intro s t hst
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · by_cases ht : (t : ℝ) ≤ 1 / 2
    · rw [Path.trans_apply, dif_pos hs, Path.trans_apply, dif_pos ht] at hst
      have huv := hγ hst
      apply Subtype.ext
      have huvVal := congrArg Subtype.val huv
      norm_num at huvVal
      linarith
    · rw [Path.trans_apply, dif_pos hs, Path.trans_apply, dif_neg ht] at hst
      have hsu : 2 * (s : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · linarith [s.2.1]
        · linarith
      have htv : 2 * (t : ℝ) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · linarith
        · linarith [t.2.2]
      let su : unitInterval := ⟨2 * (s : ℝ), hsu⟩
      let tv : unitInterval := ⟨2 * (t : ℝ) - 1, htv⟩
      have hst' : γ su = δ tv := hst
      have hmem : γ su ∈ Set.range γ ∩ Set.range δ := by
        constructor
        · exact Set.mem_range_self su
        · exact ⟨tv, hst'.symm⟩
      rw [hinter] at hmem
      have hub : γ su = b :=
        Set.mem_singleton_iff.mp hmem
      have hvb : δ tv = b := hst'.symm.trans hub
      have hvZero := hδ (hvb.trans δ.source.symm)
      have hvVal := congrArg Subtype.val hvZero
      change 2 * (t : ℝ) - 1 = 0 at hvVal
      exfalso
      apply ht
      linarith
  · by_cases ht : (t : ℝ) ≤ 1 / 2
    · rw [Path.trans_apply, dif_neg hs, Path.trans_apply, dif_pos ht] at hst
      have hsu : 2 * (s : ℝ) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · linarith
        · linarith [s.2.2]
      have htv : 2 * (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · linarith [t.2.1]
        · linarith
      let su : unitInterval := ⟨2 * (s : ℝ) - 1, hsu⟩
      let tv : unitInterval := ⟨2 * (t : ℝ), htv⟩
      have hst' : δ su = γ tv := hst
      have hmem : γ tv ∈ Set.range γ ∩ Set.range δ := by
        constructor
        · exact Set.mem_range_self tv
        · exact ⟨su, hst'⟩
      rw [hinter] at hmem
      have hub : γ tv = b :=
        Set.mem_singleton_iff.mp hmem
      have hub' : δ su = b := hst'.trans hub
      have huZero := hδ (hub'.trans δ.source.symm)
      have huVal := congrArg Subtype.val huZero
      change 2 * (s : ℝ) - 1 = 0 at huVal
      exfalso
      apply hs
      linarith
    · rw [Path.trans_apply, dif_neg hs, Path.trans_apply, dif_neg ht] at hst
      have huv := hδ hst
      apply Subtype.ext
      have huvVal := congrArg Subtype.val huv
      norm_num at huvVal
      linarith

/-- Helper for Example 63.1: the equatorial and meridional parametrizations agree
at their common east endpoint. -/
private lemma equatorMap_one_eq_meridianMap_one :
    equatorMap (1 : Circle) = meridianMap (1 : Circle) := by
  -- All three ambient coordinates agree at the point `(1, 0, 0)`.
  apply Subtype.ext
  ext i
  fin_cases i
  · norm_num [equatorMap, meridianMap]
  · norm_num [equatorMap, meridianMap]
  · norm_num [equatorMap, meridianMap]

/-- Helper for Example 63.1: the upper equatorial semicircle and the positive
meridian quarter meet only at the east endpoint. -/
private lemma upperEquator_inter_positiveMeridian :
    {x : StandardSphere 2 | (x : EuclideanSpace ℝ (Fin 3)) 2 = 0 ∧
        0 ≤ (x : EuclideanSpace ℝ (Fin 3)) 1} ∩
      {x : StandardSphere 2 | (x : EuclideanSpace ℝ (Fin 3)) 1 = 0 ∧
        0 ≤ (x : EuclideanSpace ℝ (Fin 3)) 0 ∧
        0 ≤ (x : EuclideanSpace ℝ (Fin 3)) 2} =
      {equatorMap (1 : Circle)} := by
  -- The two zero-coordinate equations leave a nonnegative first coordinate of square one.
  apply Set.ext
  intro x
  constructor
  · rintro ⟨⟨hxThird, -⟩, ⟨hxSecond, hxFirst, -⟩⟩
    have hsum := coordinate_sq_sum_eq_one x
    rw [hxSecond, hxThird] at hsum
    norm_num at hsum
    have hxFirstEq : (x : EuclideanSpace ℝ (Fin 3)) 0 = 1 := by
      rcases hsum with hsum | hsum
      · exact hsum
      · nlinarith
    rw [Set.mem_singleton_iff]
    apply Subtype.ext
    ext i
    fin_cases i
    · simpa [equatorMap] using hxFirstEq
    · simpa [equatorMap] using hxSecond
    · simpa [equatorMap] using hxThird
  · rintro rfl
    have hupper : equatorMap (1 : Circle) ∈
        Set.range ((Circle.path 1 (-1)).map continuous_equatorMap) :=
      Path.source_mem_range _
    rw [range_upperEquatorPath] at hupper
    have hmeridian : meridianMap (1 : Circle) ∈
        Set.range ((Circle.path 1 circleI).map continuous_meridianMap) :=
      Path.source_mem_range _
    rw [range_positiveMeridianPath] at hmeridian
    rw [← equatorMap_one_eq_meridianMap_one] at hmeridian
    exact ⟨hupper, hmeridian⟩

/-- Helper for Example 63.1: the upper semicircle followed by the positive
meridian quarter is represented by an injective path with range `upperArcWithTail`. -/
private lemma existsInjectivePathWithRangeUpperArcWithTail :
    ∃ a b : StandardSphere 2, ∃ γ : Path a b,
      Function.Injective γ ∧ Set.range γ = upperArcWithTail := by
  -- Name the two path pieces and align their propositionally equal common endpoint.
  let γ₁ : Path (equatorMap (-1 : Circle)) (equatorMap (1 : Circle)) :=
    ((Circle.path 1 (-1)).map continuous_equatorMap).symm
  let rawδ : Path (meridianMap (1 : Circle)) (meridianMap circleI) :=
    (Circle.path 1 circleI).map continuous_meridianMap
  have htarget : meridianMap circleI = meridianMap circleI := rfl
  let δ : Path (equatorMap (1 : Circle)) (meridianMap circleI) :=
    rawδ.cast equatorMap_one_eq_meridianMap_one htarget
  let γ := γ₁.trans δ
  have hγ₁ : Function.Injective γ₁ := by
    intro s t hst
    apply unitInterval.symm_bijective.injective
    exact (injective_equatorMap.comp
      (Circle.path_injective_of_ne (Circle.neg_ne_self 1).symm)) hst
  have honeI : (1 : Circle) ≠ circleI := by
    intro hone
    have harg := congrArg (fun z : Circle ↦ Complex.arg z.1) hone
    norm_num [circleI, Complex.arg_I] at harg
    have hpiZero : Real.pi = 0 := by linarith
    exact Real.pi_ne_zero hpiZero
  have hrawδ : Function.Injective rawδ :=
    injective_meridianMap.comp (Circle.path_injective_of_ne honeI)
  have hδ : Function.Injective δ := by
    intro s t hst
    apply hrawδ
    exact hst
  have hδRange : Set.range δ = Set.range rawδ := by
    exact congrArg Set.range (Path.cast_coe rawδ
      equatorMap_one_eq_meridianMap_one htarget)
  have hinter : Set.range γ₁ ∩ Set.range δ = {equatorMap (1 : Circle)} := by
    rw [hδRange]
    change Set.range (((Circle.path 1 (-1)).map continuous_equatorMap).symm) ∩
      Set.range ((Circle.path 1 circleI).map continuous_meridianMap) = _
    rw [Path.symm_range, range_upperEquatorPath, range_positiveMeridianPath]
    exact upperEquator_inter_positiveMeridian
  have hγ : Function.Injective γ :=
    injective_pathTrans_of_range_inter_eq_singleton γ₁ δ hγ₁ hδ hinter
  have hγRange : Set.range γ = upperArcWithTail := by
    change Set.range (γ₁.trans δ) = upperArcWithTail
    rw [Path.trans_range, hδRange]
    change Set.range (((Circle.path 1 (-1)).map continuous_equatorMap).symm) ∪
      Set.range ((Circle.path 1 circleI).map continuous_meridianMap) = upperArcWithTail
    rw [Path.symm_range, range_upperEquatorPath, range_positiveMeridianPath]
    rfl
  exact ⟨equatorMap (-1 : Circle), meridianMap circleI, γ, hγ, hγRange⟩

/-- Helper for Example 63.1: an injective path in a Hausdorff space has an arc as
its range. -/
private lemma isArcRangeOfInjectivePath
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {a b : X} (γ : Path a b) (hγ : Function.Injective γ) :
    Topology.IsArc (Set.range γ) := by
  -- Compactness of the unit interval upgrades the path to an embedding onto its range.
  let hEmbedding : Topology.IsEmbedding γ :=
    γ.continuous.isClosedEmbedding hγ |>.isEmbedding
  exact ⟨⟨hEmbedding.toHomeomorph.symm⟩⟩

/-- The upper semicircle together with the tail is an arc. -/
instance upperArcWithTail.instIsArc : Topology.IsArc upperArcWithTail := by
  -- Use the injective concatenated parametrization and transport its range equality.
  obtain ⟨a, b, γ, hγ, hRange⟩ := existsInjectivePathWithRangeUpperArcWithTail
  rw [← hRange]
  exact isArcRangeOfInjectivePath γ hγ

/-- The lower semicircle is an arc. -/
instance lowerArc.instIsArc : Topology.IsArc lowerArc := by
  -- The mapped counterclockwise lower semicircle path is injective with this range.
  rw [← range_lowerEquatorPath]
  exact isArcRangeOfInjectivePath _
    (injective_equatorMap.comp
      (Circle.path_injective_of_ne (Circle.neg_ne_self 1)))

/-- The upper arc with its tail is closed in the sphere. -/
theorem isClosed_upperArcWithTail : IsClosed upperArcWithTail := by
  -- Compactness of the explicit path range gives closedness in the sphere.
  obtain ⟨a, b, γ, -, hRange⟩ := existsInjectivePathWithRangeUpperArcWithTail
  rw [← hRange]
  exact (isCompact_range γ.continuous).isClosed

/-- The lower arc is closed in the sphere. -/
theorem isClosed_lowerArc : IsClosed lowerArc := by
  -- Compactness of the explicit path range gives closedness in the sphere.
  rw [← range_lowerEquatorPath]
  exact (isCompact_range
    ((Circle.path (-1) 1).map continuous_equatorMap).continuous).isClosed

/-- The upper arc with its tail is connected. -/
theorem isConnected_upperArcWithTail : IsConnected upperArcWithTail := by
  -- The continuous image of the unit interval is connected.
  obtain ⟨a, b, γ, -, hRange⟩ := existsInjectivePathWithRangeUpperArcWithTail
  rw [← hRange]
  exact isConnected_range γ.continuous

/-- The lower arc is connected. -/
theorem isConnected_lowerArc : IsConnected lowerArc := by
  -- The continuous image of the unit interval is connected.
  rw [← range_lowerEquatorPath]
  exact isConnected_range ((Circle.path (-1) 1).map continuous_equatorMap).continuous

/-- The upper arc with its tail does not separate the sphere. -/
theorem upperArcWithTail_not_separates : ¬ upperArcWithTail.Separates :=
  arc_not_separates upperArcWithTail

/-- The lower arc does not separate the sphere. -/
theorem lowerArc_not_separates : ¬ lowerArc.Separates :=
  arc_not_separates lowerArc

/-- The loop-and-tail subset drawn in Figure 63.5, realized as the union of its two arcs. -/
def curve : Set (StandardSphere 2) :=
  upperArcWithTail ∪ lowerArc

/-- Helper for Example 63.1: a sphere point whose second and third coordinates
vanish is one of the two equatorial endpoints. -/
private lemma eq_equatorMap_one_or_negOne_of_second_third_eq_zero
    (x : StandardSphere 2)
    (hxSecond : (x : EuclideanSpace ℝ (Fin 3)) 1 = 0)
    (hxThird : (x : EuclideanSpace ℝ (Fin 3)) 2 = 0) :
    x = equatorMap (1 : Circle) ∨ x = equatorMap (-1 : Circle) := by
  -- The sphere equation reduces the first coordinate to `1` or `-1`.
  have hsum := coordinate_sq_sum_eq_one x
  rw [hxSecond, hxThird] at hsum
  norm_num at hsum
  rcases hsum with hxFirst | hxFirst
  · left
    apply Subtype.ext
    ext i
    fin_cases i
    · simpa [equatorMap] using hxFirst
    · simpa [equatorMap] using hxSecond
    · simpa [equatorMap] using hxThird
  · right
    apply Subtype.ext
    ext i
    fin_cases i
    · simpa [equatorMap] using hxFirst
    · simpa [equatorMap] using hxSecond
    · simpa [equatorMap] using hxThird

/-- The two arcs in Figure 63.5 intersect in exactly two distinct points. -/
theorem upperArcWithTail_inter_lowerArc :
    ∃ p q, p ≠ q ∧ upperArcWithTail ∩ lowerArc = {p, q} := by
  -- Choose the east and west endpoints and first record their memberships in both paths.
  let p := equatorMap (1 : Circle)
  let q := equatorMap (-1 : Circle)
  have hpUpper : p ∈ upperArcWithTail := by
    have hpRange : p ∈ Set.range
        ((Circle.path 1 (-1)).map continuous_equatorMap) :=
      Path.source_mem_range _
    rw [range_upperEquatorPath] at hpRange
    exact Or.inl hpRange
  have hqUpper : q ∈ upperArcWithTail := by
    have hqRange : q ∈ Set.range
        ((Circle.path 1 (-1)).map continuous_equatorMap) :=
      Path.target_mem_range _
    rw [range_upperEquatorPath] at hqRange
    exact Or.inl hqRange
  have hpLower : p ∈ lowerArc := by
    rw [← range_lowerEquatorPath]
    exact Path.target_mem_range _
  have hqLower : q ∈ lowerArc := by
    rw [← range_lowerEquatorPath]
    exact Path.source_mem_range _
  refine ⟨p, q, injective_equatorMap.ne (Circle.neg_ne_self 1).symm, ?_⟩
  apply Set.ext
  intro x
  constructor
  · rintro ⟨hxUpper, hxLower⟩
    rcases hxUpper with hxUpper | hxTail
    · have hxSecond := le_antisymm hxLower.2 hxUpper.2
      rcases eq_equatorMap_one_or_negOne_of_second_third_eq_zero x
          hxSecond hxLower.1 with hxp | hxq
      · exact Or.inl hxp
      · exact Or.inr hxq
    · rcases eq_equatorMap_one_or_negOne_of_second_third_eq_zero x
          hxTail.1 hxLower.1 with hxp | hxq
      · exact Or.inl hxp
      · exact Or.inr hxq
  · rintro (hxp | hxq)
    · rw [hxp]
      exact ⟨hpUpper, hpLower⟩
    · rw [hxq]
      exact ⟨hqUpper, hqLower⟩

/-- Helper for Example 63.1: the coordinate vector `(0, 0, -1)` lies on the
standard two-sphere. -/
private lemma southPole_mem_standardSphere :
    !₂[0, 0, -1] ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  -- The vector has Euclidean norm one.
  norm_num [PiLp.norm_eq_of_L2, Fin.sum_univ_succ]

/-- The south pole as a point of the standard two-sphere. -/
def southPole : StandardSphere 2 :=
  ⟨!₂[0, 0, -1], southPole_mem_standardSphere⟩

/-- Helper for Example 63.1: the third coordinate of the south pole is `-1`. -/
private lemma southPole_thirdCoordinate :
    (southPole : EuclideanSpace ℝ (Fin 3)) 2 = -1 := by
  -- Normalize the numeral index to the third entry of the coordinate vector.
  have htwo : (2 : Fin 3) = Fin.succ (Fin.succ 0) := Fin.ext rfl
  rw [htwo]
  rfl

/-- The south pole does not belong to the subset drawn in Figure 63.5. -/
theorem southPole_not_mem : southPole ∉ curve := by
  -- Its third coordinate is `-1`, so it lies in neither equatorial arc nor the tail.
  intro hsouth
  rcases hsouth with hsouthUpper | hsouthLower
  · rcases hsouthUpper with hsouthEquator | hsouthTail
    · linarith [southPole_thirdCoordinate, hsouthEquator.1]
    · linarith [southPole_thirdCoordinate, hsouthTail.2.2]
  · linarith [southPole_thirdCoordinate, hsouthLower.1]

/-- The south pole as a point of the complement of the subset in Figure 63.5. -/
def southPoleComplement : (curveᶜ : Set (StandardSphere 2)) :=
  ⟨southPole, southPole_not_mem⟩

/-- Helper for Example 63.1: the third-coordinate function on the standard
two-sphere is continuous. -/
private lemma continuous_thirdCoordinate :
    Continuous (fun x : StandardSphere 2 ↦
      (x : EuclideanSpace ℝ (Fin 3)) 2) := by
  -- Compose the subtype inclusion with continuous coordinate evaluation.
  fun_prop

/-- Helper for Example 63.1: every equatorial sphere point belongs to the
loop-with-tail curve. -/
private lemma mem_curve_of_thirdCoordinate_eq_zero (x : StandardSphere 2)
    (hx : (x : EuclideanSpace ℝ (Fin 3)) 2 = 0) : x ∈ curve := by
  -- The sign of the second coordinate chooses the upper or lower semicircle.
  by_cases hxSecond : 0 ≤ (x : EuclideanSpace ℝ (Fin 3)) 1
  · exact Or.inl (Or.inl ⟨hx, hxSecond⟩)
  · exact Or.inr ⟨hx, le_of_not_ge hxSecond⟩

/-- Helper for Example 63.1: every point in the complementary component of the
south pole has nonpositive third coordinate. -/
private lemma southPoleComponent_height_nonpos (x : StandardSphere 2)
    (hx : x ∈ connectedComponentIn curveᶜ southPoleComplement) :
    (x : EuclideanSpace ℝ (Fin 3)) 2 ≤ 0 := by
  -- A positive-height point would force a height-zero point in the same component.
  by_contra hxNonpos
  have hxPositive : 0 < (x : EuclideanSpace ℝ (Fin 3)) 2 := lt_of_not_ge hxNonpos
  have hsouthComponent :
      southPole ∈ connectedComponentIn curveᶜ southPoleComplement :=
    mem_connectedComponentIn southPole_not_mem
  have hzeroInterval : (0 : ℝ) ∈ Set.Icc
      ((southPole : EuclideanSpace ℝ (Fin 3)) 2)
      ((x : EuclideanSpace ℝ (Fin 3)) 2) := by
    constructor
    · rw [southPole_thirdCoordinate]
      norm_num
    · exact hxPositive.le
  have hzeroImage := isPreconnected_connectedComponentIn.intermediate_value
    hsouthComponent hx continuous_thirdCoordinate.continuousOn hzeroInterval
  obtain ⟨y, hyComponent, hyZero⟩ := hzeroImage
  have hyComplement := connectedComponentIn_subset curveᶜ southPoleComplement hyComponent
  exact hyComplement (mem_curve_of_thirdCoordinate_eq_zero y hyZero)

/-- Helper for Example 63.1: the endpoint of the positive meridian tail has
third coordinate one. -/
private lemma meridianMap_circleI_thirdCoordinate :
    (meridianMap circleI : EuclideanSpace ℝ (Fin 3)) 2 = 1 := by
  -- Normalize the numeral index and evaluate the explicit meridian coordinates.
  have htwo : (2 : Fin 3) = Fin.succ (Fin.succ 0) := Fin.ext rfl
  rw [htwo]
  simp only [meridianMap, circleI, Matrix.cons_val_succ,
    Matrix.cons_val_zero, Complex.I_im]

/-- The separation assertion in Example 63.1: the subset in Figure 63.5
separates the standard two-sphere into exactly two components. -/
theorem separatesInto : curve.SeparatesInto 2 := by
  exact union_separatesInto_two_of_inter_pair upperArcWithTail lowerArc
    isClosed_upperArcWithTail isClosed_lowerArc isConnected_upperArcWithTail
    isConnected_lowerArc upperArcWithTail_inter_lowerArc
    upperArcWithTail_not_separates lowerArc_not_separates

/-- The complementary component containing the south pole witnesses the failure
of the common-frontier conclusion. -/
theorem southPoleComponent_frontier_ne :
    frontier (connectedComponentIn curveᶜ southPoleComplement) ≠ curve := by
  -- The component and its closure stay in the nonpositive-height closed hemisphere.
  let north := meridianMap circleI
  have hcomponentSubset :
      connectedComponentIn curveᶜ southPoleComplement ⊆
        {x : StandardSphere 2 | (x : EuclideanSpace ℝ (Fin 3)) 2 ≤ 0} := by
    intro x hx
    exact southPoleComponent_height_nonpos x hx
  have hhalfspaceClosed : IsClosed
      {x : StandardSphere 2 | (x : EuclideanSpace ℝ (Fin 3)) 2 ≤ 0} := by
    exact isClosed_Iic.preimage continuous_thirdCoordinate
  have hclosureSubset := closure_minimal hcomponentSubset hhalfspaceClosed
  -- The positive endpoint belongs to the tail, hence to the curve, but not to that closure.
  have hnRange : north ∈ Set.range
      ((Circle.path 1 circleI).map continuous_meridianMap) :=
    Path.target_mem_range _
  rw [range_positiveMeridianPath] at hnRange
  have hnCurve : north ∈ curve := Or.inl (Or.inr hnRange)
  intro hfrontier
  have hnFrontier : north ∈
      frontier (connectedComponentIn curveᶜ southPoleComplement) := by
    rw [hfrontier]
    exact hnCurve
  have hnClosure := frontier_subset_closure hnFrontier
  have hnNonpos := hclosureSubset hnClosure
  change (north : EuclideanSpace ℝ (Fin 3)) 2 ≤ 0 at hnNonpos
  have hnPositive : (north : EuclideanSpace ℝ (Fin 3)) 2 = 1 :=
    meridianMap_circleI_thirdCoordinate
  linarith

/-- Example 63.1: Unlike a Jordan curve, the subset in Figure 63.5 is not
the frontier of every complementary component. -/
theorem not_commonFrontier :
    ∃ x : (curveᶜ : Set (StandardSphere 2)),
      frontier (connectedComponentIn curveᶜ x) ≠ curve :=
  ⟨southPoleComplement, southPoleComponent_frontier_ne⟩

end LoopWithTail
