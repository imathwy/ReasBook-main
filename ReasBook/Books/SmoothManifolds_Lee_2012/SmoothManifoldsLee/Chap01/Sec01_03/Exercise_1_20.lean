import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_03.Proposition_1_19

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace
open scoped Manifold

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [T2Space M] [SecondCountableTopology M]
variable [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]

/- Exercise 1.20 in Lee asks the reader to prove Proposition 1.19, namely that every smooth
manifold has a countable basis of regular coordinate balls. The chapter owner for this statement is
the preceding theorem `exists_countable_regular_coordinate_ball_basis`. -/
recall exists_countable_regular_coordinate_ball_basis
