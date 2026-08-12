import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_29

noncomputable section

namespace TwoDimensionalTV

/-- The primal matrix space `ℝ^(m × n)` used in the Chapter 12 two-dimensional TV model. -/
abbrev MatrixSpace (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- The horizontal dual block space `ℝ^(m × (n - 1))`. -/
abbrev HorizontalSpace (m n : ℕ) := MatrixSpace m (n - 1)

/-- The vertical dual block space `ℝ^((m - 1) × n)`. -/
abbrev VerticalSpace (m n : ℕ) := MatrixSpace (m - 1) n

/-- The canonical `L²` product owner for the Chapter 12 TV dual pair `(p, q)`. -/
abbrev DualSpace (m n : ℕ) := WithLp 2 (HorizontalSpace m n × VerticalSpace m n)

instance matrixSpaceNormedAddCommGroup (m n : ℕ) :
    NormedAddCommGroup (MatrixSpace m n) :=
  Matrix.frobeniusNormedAddCommGroup

instance matrixSpaceNormedSpace (m n : ℕ) :
    NormedSpace ℝ (MatrixSpace m n) :=
  Matrix.frobeniusNormedSpace

instance matrixSpaceInnerProductSpace (m n : ℕ) :
    InnerProductSpace ℝ (MatrixSpace m n) :=
  Matrix.frobeniusInnerProductSpace

end TwoDimensionalTV
