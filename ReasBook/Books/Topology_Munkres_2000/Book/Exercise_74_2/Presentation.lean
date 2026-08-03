module

public import Topology_Munkres_2000.Book.Remark_74_2.Vertices
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Real.Basic

public section

namespace HeptagonFreeProduct

noncomputable section

/-- The lifted angles of a regular heptagon, including the closing angle. -/
def angles (i : Fin 8) : ℝ :=
  2 * Real.pi * i / 7

/-- Seven is at least three, as required for a cyclic polygon. -/
theorem three_le_seven : 3 ≤ 7 := by decide

/-- The chosen unit radius is positive. -/
theorem radius_pos : (0 : ℝ) < 1 := by norm_num

/-- The lifted heptagon angles are strictly increasing. -/
theorem angles_strictMono : StrictMono angles := by
  -- Positive scaling and division preserve the strict order of vertex indices.
  intro i j hij
  rw [angles, angles]
  have denominator_pos : (0 : ℝ) < 7 := by norm_num
  have coefficient_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [div_lt_div_iff_of_pos_right denominator_pos]
  exact mul_lt_mul_of_pos_left (Nat.cast_lt.2 hij) coefficient_pos

/-- The final lifted angle completes one full turn. -/
theorem angles_last : angles (Fin.last 7) = angles 0 + 2 * Real.pi := by
  -- The final index equals the denominator, so its angle is one full revolution.
  rw [angles, angles]
  norm_num [Fin.last]

/-- A regular cyclic heptagon centered at the origin. -/
def polygon : CyclicPolygon 7 where
  three_le := three_le_seven
  center := 0
  radius := 1
  radius_pos := radius_pos
  angles := angles
  angles_strictMono := angles_strictMono
  angles_last := angles_last

/-- The edge labels and orientations encoding `a b a a a b⁻¹ a⁻¹`. -/
def pasting : polygon.EdgePasting (Fin 2) :=
  .ofSigns polygon ![0, 1, 0, 0, 0, 1, 0] ![true, true, true, true, true, false, false]

/-- The heptagon quotient with boundary word `a b a a a b⁻¹ a⁻¹`. -/
abbrev Space := pasting.Realization

/-- The canonical map from the heptagon to its edge-pasting quotient. -/
abbrev quotientMap : polygon.region → Space :=
  pasting.quotientMap

/-- The image of the first heptagon vertex in the quotient space. -/
def basepoint : Space :=
  quotientMap (polygon.vertexPoint 0)


end

end HeptagonFreeProduct
