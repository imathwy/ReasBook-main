module

public import Topology_Munkres_2000.Book.Definition_53_5.FigureEight
public import Topology_Munkres_2000.Book.Theorem_53_1.CircleMap
public import Mathlib.Topology.Constructions

public section

namespace FigureEightTangentCircleCover

/-- The nonzero integer points at which the tangent circles are attached. -/
abbrev NonzeroInt := {n : ℤ // n ≠ 0}

/-- One indexed family of circles tangent to a coordinate axis. -/
abbrev TangentCircles := NonzeroInt × Circle

/-- The disjoint union of the two axes and the two tangent-circle families before gluing. -/
abbrev Raw := ℝ ⊕ ℝ ⊕ TangentCircles ⊕ TangentCircles

/-- A point on the horizontal-axis component. -/
def xAxis (x : ℝ) : Raw :=
  Sum.inl x

/-- A point on the vertical-axis component. -/
def yAxis (y : ℝ) : Raw :=
  Sum.inr (Sum.inl y)

/-- A point on the circle tangent to the horizontal axis at a nonzero integer. -/
def xCircle (n : NonzeroInt) (z : Circle) : Raw :=
  Sum.inr (Sum.inr (Sum.inl (n, z)))

/-- A point on the circle tangent to the vertical axis at a nonzero integer. -/
def yCircle (n : NonzeroInt) (z : Circle) : Raw :=
  Sum.inr (Sum.inr (Sum.inr (n, z)))

/-- The generating identifications joining the axes at the origin and attaching every
tangent circle at its basepoint. -/
inductive Gluing : Raw → Raw → Prop
  | origin : Gluing (xAxis 0) (yAxis 0)
  | xCircle_base (n : NonzeroInt) : Gluing (xCircle n 1) (xAxis n)
  | yCircle_base (n : NonzeroInt) : Gluing (yCircle n 1) (yAxis n)

/-- The §60 total space, presented as the two axes with tangent circles attached at
the nonzero integer points. -/
abbrev Total := Quot Gluing

/-- A point on the first coordinate circle lies in the figure eight. -/
theorem firstCircle_mem (z : Circle) : (z, 1) ∈ FigureEight.carrier :=
  FigureEight.mem_iff (z, 1) |>.mpr (Or.inl rfl)

/-- A point on the first coordinate circle of the figure eight. -/
noncomputable def firstCircle (z : Circle) : FigureEight :=
  ⟨(z, 1), firstCircle_mem z⟩

/-- A point on the second coordinate circle lies in the figure eight. -/
theorem secondCircle_mem (z : Circle) : (1, z) ∈ FigureEight.carrier :=
  FigureEight.mem_iff (1, z) |>.mpr (Or.inr rfl)

/-- A point on the second coordinate circle of the figure eight. -/
noncomputable def secondCircle (z : Circle) : FigureEight :=
  ⟨(1, z), secondCircle_mem z⟩

/-- The projection before passing to the gluing quotient. -/
noncomputable def rawProjection : Raw → FigureEight
  | Sum.inl x => firstCircle (Circle.turnExp x)
  | Sum.inr (Sum.inl y) => secondCircle (Circle.turnExp y)
  | Sum.inr (Sum.inr (Sum.inl (_, z))) => secondCircle z
  | Sum.inr (Sum.inr (Sum.inr (_, z))) => firstCircle z

/-- The raw projection respects the origin and tangent-circle identifications. -/
theorem rawProjection_eq {a b : Raw} (hab : Gluing a b) :
    rawProjection a = rawProjection b := by
  cases hab <;> ext <;> simp [rawProjection, xAxis, yAxis, xCircle, yCircle,
    firstCircle, secondCircle, Circle.turnExp_zero, Circle.turnExp_int]

/-- The §60 projection from the axes-with-tangent-circles cover to the figure eight. -/
noncomputable def proj : Total → FigureEight :=
  Quot.lift rawProjection fun _ _ hab ↦ rawProjection_eq hab

/-- On the horizontal axis, the projection wraps around the first circle. -/
theorem proj_xAxis (x : ℝ) :
    proj (Quot.mk Gluing (xAxis x)) = firstCircle (Circle.turnExp x) := by
  -- The quotient lift computes to the raw projection on representatives.
  rfl

/-- On the vertical axis, the projection wraps around the second circle. -/
theorem proj_yAxis (y : ℝ) :
    proj (Quot.mk Gluing (yAxis y)) = secondCircle (Circle.turnExp y) := by
  -- The quotient lift computes to the raw projection on representatives.
  rfl

/-- Each circle tangent to the horizontal axis maps homeomorphically onto the second circle. -/
theorem proj_xCircle (n : NonzeroInt) (z : Circle) :
    proj (Quot.mk Gluing (xCircle n z)) = secondCircle z := by
  -- The quotient lift computes to the raw projection on representatives.
  rfl

/-- Each circle tangent to the vertical axis maps homeomorphically onto the first circle. -/
theorem proj_yCircle (n : NonzeroInt) (z : Circle) :
    proj (Quot.mk Gluing (yCircle n z)) = firstCircle z := by
  -- The quotient lift computes to the raw projection on representatives.
  rfl

end FigureEightTangentCircleCover
