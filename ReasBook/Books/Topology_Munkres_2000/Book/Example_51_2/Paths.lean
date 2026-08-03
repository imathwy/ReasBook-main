module

public import Topology_Munkres_2000.Book.Example_51_1.Homotopy
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

noncomputable section

open Set unitInterval

/-- The real plane with the origin removed. -/
abbrev PuncturedPlane := {p : ℝ × ℝ // p ≠ 0}

namespace PuncturedPlane

/-- The east point is not the origin. -/
theorem east_ne_zero : (1, 0) ≠ (0 : ℝ × ℝ) := by
  norm_num

/-- The common initial point of the three paths. -/
def east : PuncturedPlane := ⟨(1, 0), east_ne_zero⟩

/-- The west point is not the origin. -/
theorem west_ne_zero : (-1, 0) ≠ (0 : ℝ × ℝ) := by
  norm_num

/-- The common terminal point of the three paths. -/
def west : PuncturedPlane := ⟨(-1, 0), west_ne_zero⟩

/-- The coordinate formula for the upper semicircle. -/
def upperSemicirclePoint (s : unitInterval) : ℝ × ℝ :=
  (Real.cos (Real.pi * s), Real.sin (Real.pi * s))

/-- The upper semicircle formula never reaches the origin. -/
theorem upperSemicirclePoint_ne_zero (s : unitInterval) :
    upperSemicirclePoint s ≠ 0 := by
  -- Vanishing of both coordinates contradicts the Pythagorean identity.
  intro h
  have hcos := congrArg Prod.fst h
  have hsin := congrArg Prod.snd h
  simp only [upperSemicirclePoint, Prod.fst_zero] at hcos
  simp only [upperSemicirclePoint, Prod.snd_zero] at hsin
  have htrig := Real.sin_sq_add_cos_sq (Real.pi * (s : ℝ))
  rw [hcos, hsin] at htrig
  norm_num at htrig

/-- The upper semicircle formula is continuous. -/
theorem continuous_upperSemicirclePoint : Continuous upperSemicirclePoint := by
  -- Each trigonometric coordinate is continuous in the path parameter.
  unfold upperSemicirclePoint
  fun_prop

/-- The subtype-valued upper semicircle formula is continuous. -/
theorem continuous_upperSemicircle : Continuous fun s : unitInterval ↦
    (⟨upperSemicirclePoint s, upperSemicirclePoint_ne_zero s⟩ : PuncturedPlane) := by
  -- Lift the continuous coordinate map to the punctured-plane subtype.
  exact continuous_upperSemicirclePoint.subtype_mk _

/-- The upper semicircle formula starts at the east point. -/
theorem upperSemicirclePoint_zero :
    (⟨upperSemicirclePoint 0, upperSemicirclePoint_ne_zero 0⟩ : PuncturedPlane) = east := by
  -- Evaluate the trigonometric formula at the initial parameter.
  apply Subtype.ext
  norm_num [upperSemicirclePoint, east]

/-- The upper semicircle formula ends at the west point. -/
theorem upperSemicirclePoint_one :
    (⟨upperSemicirclePoint 1, upperSemicirclePoint_ne_zero 1⟩ : PuncturedPlane) = west := by
  -- Evaluate the trigonometric formula at the terminal parameter.
  apply Subtype.ext
  norm_num [upperSemicirclePoint, west]

/-- The path along the upper unit semicircle. -/
def upperSemicircle : Path east west where
  toFun := fun s ↦ ⟨upperSemicirclePoint s, upperSemicirclePoint_ne_zero s⟩
  continuous_toFun := continuous_upperSemicircle
  source' := upperSemicirclePoint_zero
  target' := upperSemicirclePoint_one

/-- The coordinate formula for the upper semiellipse. -/
def upperSemiellipsePoint (s : unitInterval) : ℝ × ℝ :=
  (Real.cos (Real.pi * s), 2 * Real.sin (Real.pi * s))

/-- The upper semiellipse formula never reaches the origin. -/
theorem upperSemiellipsePoint_ne_zero (s : unitInterval) :
    upperSemiellipsePoint s ≠ 0 := by
  -- A zero semiellipse point would force both sine and cosine to vanish.
  intro h
  have hcos := congrArg Prod.fst h
  have hsin := congrArg Prod.snd h
  simp only [upperSemiellipsePoint, Prod.fst_zero] at hcos
  simp only [upperSemiellipsePoint, Prod.snd_zero] at hsin
  have htrig := Real.sin_sq_add_cos_sq (Real.pi * (s : ℝ))
  rw [hcos] at htrig
  norm_num at hsin
  rw [hsin] at htrig
  norm_num at htrig

/-- The upper semiellipse formula is continuous. -/
theorem continuous_upperSemiellipsePoint : Continuous upperSemiellipsePoint := by
  -- Each coordinate of the semiellipse formula is continuous.
  unfold upperSemiellipsePoint
  fun_prop

/-- The subtype-valued upper semiellipse formula is continuous. -/
theorem continuous_upperSemiellipse : Continuous fun s : unitInterval ↦
    (⟨upperSemiellipsePoint s, upperSemiellipsePoint_ne_zero s⟩ : PuncturedPlane) := by
  -- Lift the continuous coordinate map to the punctured-plane subtype.
  exact continuous_upperSemiellipsePoint.subtype_mk _

/-- The upper semiellipse formula starts at the east point. -/
theorem upperSemiellipsePoint_zero :
    (⟨upperSemiellipsePoint 0, upperSemiellipsePoint_ne_zero 0⟩ : PuncturedPlane) = east := by
  -- Evaluate the semiellipse at its initial parameter.
  apply Subtype.ext
  norm_num [upperSemiellipsePoint, east]

/-- The upper semiellipse formula ends at the west point. -/
theorem upperSemiellipsePoint_one :
    (⟨upperSemiellipsePoint 1, upperSemiellipsePoint_ne_zero 1⟩ : PuncturedPlane) = west := by
  -- Evaluate the semiellipse at its terminal parameter.
  apply Subtype.ext
  norm_num [upperSemiellipsePoint, west]

/-- The path along the upper semiellipse with vertical semiaxis two. -/
def upperSemiellipse : Path east west where
  toFun := fun s ↦ ⟨upperSemiellipsePoint s, upperSemiellipsePoint_ne_zero s⟩
  continuous_toFun := continuous_upperSemiellipse
  source' := upperSemiellipsePoint_zero
  target' := upperSemiellipsePoint_one

/-- The coordinate formula for the lower semicircle. -/
def lowerSemicirclePoint (s : unitInterval) : ℝ × ℝ :=
  (Real.cos (Real.pi * s), -Real.sin (Real.pi * s))

/-- The lower semicircle formula never reaches the origin. -/
theorem lowerSemicirclePoint_ne_zero (s : unitInterval) :
    lowerSemicirclePoint s ≠ 0 := by
  -- Vanishing of both coordinates contradicts the Pythagorean identity.
  intro h
  have hcos := congrArg Prod.fst h
  have hsin := congrArg Prod.snd h
  simp only [lowerSemicirclePoint, Prod.fst_zero] at hcos
  simp only [lowerSemicirclePoint, Prod.snd_zero] at hsin
  have htrig := Real.sin_sq_add_cos_sq (Real.pi * (s : ℝ))
  rw [hcos] at htrig
  norm_num at hsin
  rw [hsin] at htrig
  norm_num at htrig

/-- The lower semicircle formula is continuous. -/
theorem continuous_lowerSemicirclePoint : Continuous lowerSemicirclePoint := by
  -- Each trigonometric coordinate is continuous in the path parameter.
  unfold lowerSemicirclePoint
  fun_prop

/-- The subtype-valued lower semicircle formula is continuous. -/
theorem continuous_lowerSemicircle : Continuous fun s : unitInterval ↦
    (⟨lowerSemicirclePoint s, lowerSemicirclePoint_ne_zero s⟩ : PuncturedPlane) := by
  -- Lift the continuous coordinate map to the punctured-plane subtype.
  exact continuous_lowerSemicirclePoint.subtype_mk _

/-- The lower semicircle formula starts at the east point. -/
theorem lowerSemicirclePoint_zero :
    (⟨lowerSemicirclePoint 0, lowerSemicirclePoint_ne_zero 0⟩ : PuncturedPlane) = east := by
  -- Evaluate the lower semicircle at its initial parameter.
  apply Subtype.ext
  norm_num [lowerSemicirclePoint, east]

/-- The lower semicircle formula ends at the west point. -/
theorem lowerSemicirclePoint_one :
    (⟨lowerSemicirclePoint 1, lowerSemicirclePoint_ne_zero 1⟩ : PuncturedPlane) = west := by
  -- Evaluate the lower semicircle at its terminal parameter.
  apply Subtype.ext
  norm_num [lowerSemicirclePoint, west]

/-- The path along the lower unit semicircle. -/
def lowerSemicircle : Path east west where
  toFun := fun s ↦ ⟨lowerSemicirclePoint s, lowerSemicirclePoint_ne_zero s⟩
  continuous_toFun := continuous_lowerSemicircle
  source' := lowerSemicirclePoint_zero
  target' := lowerSemicirclePoint_one

/-- The value of the upper semicircle path. -/
theorem upperSemicircle_apply (s : unitInterval) :
    (upperSemicircle s).1 = upperSemicirclePoint s := by
  -- The path constructor uses this coordinate formula definitionally.
  rfl

/-- The value of the upper semiellipse path. -/
theorem upperSemiellipse_apply (s : unitInterval) :
    (upperSemiellipse s).1 = upperSemiellipsePoint s := by
  -- The path constructor uses this coordinate formula definitionally.
  rfl

/-- The value of the lower semicircle path. -/
theorem lowerSemicircle_apply (s : unitInterval) :
    (lowerSemicircle s).1 = lowerSemicirclePoint s := by
  -- The path constructor uses this coordinate formula definitionally.
  rfl

/-- The continuous inclusion of the punctured plane into the plane. -/
def inclusion : C(PuncturedPlane, ℝ × ℝ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The upper semicircle viewed as a path in the full plane. -/
def upperSemicircleAmbient : Path (inclusion east) (inclusion west) :=
  upperSemicircle.map inclusion.continuous

/-- The lower semicircle viewed as a path in the full plane. -/
def lowerSemicircleAmbient : Path (inclusion east) (inclusion west) :=
  lowerSemicircle.map inclusion.continuous

/-- Helper for Example 51.2: the affine interpolation between the upper circle and
upper ellipse has the expected coordinate formula. -/
lemma upperAffinePoint_apply (z : unitInterval × unitInterval) :
    AffineMap.lineMap (upperSemicircle z.2).1 (upperSemiellipse z.2).1 (z.1 : ℝ) =
      (Real.cos (Real.pi * z.2), (1 + (z.1 : ℝ)) * Real.sin (Real.pi * z.2)) := by
  -- Expand the two path values and simplify the affine combination coordinatewise.
  rw [upperSemicircle_apply, upperSemiellipse_apply]
  simp only [upperSemicirclePoint, upperSemiellipsePoint,
    AffineMap.lineMap_apply_module]
  ext
  · dsimp
    ring
  · dsimp
    ring

/-- The affine interpolation from the upper semicircle to the upper semiellipse stays punctured. -/
theorem upperAffinePoint_ne_zero (z : unitInterval × unitInterval) :
    AffineMap.lineMap (upperSemicircle z.2).1 (upperSemiellipse z.2).1 (z.1 : ℝ) ≠ 0 := by
  -- The coordinate formula and the Pythagorean identity rule out the origin.
  rw [upperAffinePoint_apply]
  intro h
  have hcoords := Prod.mk_eq_zero.mp h
  have hpositive : 0 < 1 + (z.1 : ℝ) := by
    linarith [z.1.property.1]
  have hcoefficient : 1 + (z.1 : ℝ) ≠ 0 := by
    exact ne_of_gt hpositive
  have hsin : Real.sin (Real.pi * (z.2 : ℝ)) = 0 := by
    exact (mul_eq_zero.mp hcoords.2).resolve_left hcoefficient
  have htrig := Real.sin_sq_add_cos_sq (Real.pi * (z.2 : ℝ))
  rw [hcoords.1, hsin] at htrig
  norm_num at htrig

/-- The subtype-valued upper affine interpolation is continuous. -/
theorem continuous_upperAffine : Continuous fun z : unitInterval × unitInterval ↦
    (⟨AffineMap.lineMap (upperSemicircle z.2).1 (upperSemiellipse z.2).1 (z.1 : ℝ),
      upperAffinePoint_ne_zero z⟩ : PuncturedPlane) := by
  -- Lift continuity of the affine coordinate formula to the punctured subtype.
  apply Continuous.subtype_mk
  have hcoordinates : Continuous fun z : unitInterval × unitInterval ↦
      (Real.cos (Real.pi * z.2),
        (1 + (z.1 : ℝ)) * Real.sin (Real.pi * z.2)) := by
    fun_prop
  exact hcoordinates.congr fun z ↦ (upperAffinePoint_apply z).symm

/-- At time zero, the upper affine interpolation is the upper semicircle. -/
theorem upperAffine_zero (s : unitInterval) :
    (⟨AffineMap.lineMap (upperSemicircle s).1 (upperSemiellipse s).1 (0 : ℝ),
      upperAffinePoint_ne_zero (0, s)⟩ : PuncturedPlane) = upperSemicircle s := by
  -- At affine time zero, the interpolation is its first endpoint.
  apply Subtype.ext
  exact AffineMap.lineMap_apply_zero (upperSemicircle s).1 (upperSemiellipse s).1

/-- At time one, the upper affine interpolation is the upper semiellipse. -/
theorem upperAffine_one (s : unitInterval) :
    (⟨AffineMap.lineMap (upperSemicircle s).1 (upperSemiellipse s).1 (1 : ℝ),
      upperAffinePoint_ne_zero (1, s)⟩ : PuncturedPlane) = upperSemiellipse s := by
  -- At affine time one, the interpolation is its second endpoint.
  apply Subtype.ext
  exact AffineMap.lineMap_apply_one (upperSemicircle s).1 (upperSemiellipse s).1

/-- The upper affine interpolation fixes both path endpoints. -/
theorem upperAffine_fixed (t s : unitInterval) (hs : s ∈ ({0, 1} : Set unitInterval)) :
    (⟨AffineMap.lineMap (upperSemicircle s).1 (upperSemiellipse s).1 (t : ℝ),
      upperAffinePoint_ne_zero (t, s)⟩ : PuncturedPlane) = upperSemicircle s := by
  -- Both input paths agree at either distinguished path endpoint.
  rcases hs with hs | hs
  · subst s
    apply Subtype.ext
    simp only [Path.source, AffineMap.lineMap_same_apply]
  · rw [Set.mem_singleton_iff] at hs
    subst s
    apply Subtype.ext
    simp only [Path.target, AffineMap.lineMap_same_apply]

/-- The punctured-plane affine interpolation from the upper semicircle to the upper semiellipse. -/
def upperHomotopy : upperSemicircle.Homotopy upperSemiellipse where
  toHomotopy :=
    { toFun := fun z ↦
        ⟨AffineMap.lineMap (upperSemicircle z.2).1 (upperSemiellipse z.2).1 (z.1 : ℝ),
          upperAffinePoint_ne_zero z⟩
      continuous_toFun := continuous_upperAffine
      map_zero_left := upperAffine_zero
      map_one_left := upperAffine_one }
  prop' := upperAffine_fixed

/-- The ambient value of the acceptable affine path homotopy. -/
theorem upperHomotopy_apply (z : unitInterval × unitInterval) :
    (upperHomotopy z).1 =
      (Real.cos (Real.pi * z.2), (1 + (z.1 : ℝ)) * Real.sin (Real.pi * z.2)) := by
  -- Project the homotopy construction and apply its coordinate computation.
  exact upperAffinePoint_apply z

end PuncturedPlane
