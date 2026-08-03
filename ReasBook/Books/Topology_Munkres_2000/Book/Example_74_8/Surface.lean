module

public import Topology_Munkres_2000.Book.Definition_74_3.Pasting
public import Topology_Munkres_2000.Book.Definition_60_3
public import Topology_Munkres_2000.Book.Example_22_5.Torus
public import Topology_Munkres_2000.Book.Example_74_8.CutPresentation

public section

namespace ProjectivePlaneTorus

noncomputable section

/-- The lifted angles of the vertices of a regular hexagon. -/
def angles (i : Fin 7) : ℝ :=
  2 * Real.pi * ((i : ℕ) : ℝ) / 6

/-- Six is at least three, as required for a cyclic polygon. -/
theorem three_le_six : 3 ≤ 6 := by
  -- This is the numerical side condition for a hexagon.
  norm_num

/-- The chosen unit radius is positive. -/
theorem zero_lt_one : (0 : ℝ) < 1 := by
  -- The radius is the positive real unit.
  norm_num

/-- The lifted hexagon angles are strictly increasing. -/
theorem angles_strictMono : StrictMono angles := by
  intro i j hij
  -- Multiplication by the positive angular increment preserves the index order.
  have hindices : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by
    exact_mod_cast hij
  apply (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 6)).2
  exact mul_lt_mul_of_pos_left hindices (mul_pos (by norm_num) Real.pi_pos)

/-- The final lifted angle completes one full turn. -/
theorem angles_last : angles (Fin.last 6) = angles 0 + 2 * Real.pi := by
  -- The last index is six, so the normalization by six cancels.
  norm_num [angles]

/-- A regular cyclic hexagon used to realize the connected sum `P² # T`. -/
def hexagon : CyclicPolygon 6 where
  three_le := three_le_six
  center := 0
  radius := 1
  radius_pos := zero_lt_one
  angles := angles
  angles_strictMono := angles_strictMono
  angles_last := angles_last

/-- Helper for Example 74.8: the displayed orientations agree with the signs of the hexagon
boundary word. -/
private theorem pastingOrientation_eq (i : Fin 6) :
    hexagon.signedOrientation i (![true, true, true, true, false, false] i) =
      hexagon.signedOrientation i (![true, true, true, true, false, false] i) := by
  rfl

/-- The edge pasting with boundary word `a a b c b⁻¹ c⁻¹`. -/
def pasting : hexagon.EdgePasting (Fin 3) where
  label := ![0, 0, 1, 2, 1, 2]
  orientation i := hexagon.signedOrientation i (![true, true, true, true, false, false] i)
  sign := ![true, true, true, true, false, false]
  orientation_eq := pastingOrientation_eq

/-- The first edge of the hexagonal pasting has label `a`. -/
theorem pasting_label_zero : pasting.label 0 = 0 := by
  -- The first label is the first entry of the supplied vector.
  unfold pasting
  decide

/-- The third edge of the hexagonal pasting has label `b`. -/
theorem pasting_label_two : pasting.label 2 = 1 := by
  -- The third label is the third entry of the supplied vector.
  unfold pasting
  decide

/-- The fourth edge of the hexagonal pasting has label `c`. -/
theorem pasting_label_three : pasting.label 3 = 2 := by
  -- The fourth label is the fourth entry of the supplied vector.
  unfold pasting
  decide

/-- The concrete polygonal realization of the connected sum `P² # T`. -/
abbrev Surface := pasting.Realization

/-- The canonical map from the regular hexagon to `P² # T`. -/
abbrev quotientMap : hexagon.region → Surface :=
  pasting.quotientMap

/-- The image of the first hexagon vertex, used as the basepoint of `P² # T`. -/
def basepoint : Surface :=
  quotientMap ⟨hexagon.toPolygon.vertices 0, hexagon.vertex_mem_region 0⟩

/-- The standard deleted-disc boundary gluing of `P²` and the torus agrees with the
hexagonal realization. -/
theorem homeomorphicStandardGluing :
    Nonempty (standardGluing.GluedSurface ≃ₜ Surface) := by
  -- Route correction: the former arbitrary-chart theorem had no presentation-compatible
  -- hypotheses.  The concrete proof must compare `standardGluing` and `pasting` through the
  -- common triangle-plus-pentagon cut source, using `boundaryCircleParam` on its seam.
  -- TODO: construct the two concrete complement quotient presentations and compare their
  -- kernels with the folded-hexagon quotient presentation.
  sorry


end

end ProjectivePlaneTorus
