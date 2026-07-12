import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

-- Semantic Lean search recalled Euclidean-ball volume lemmas in the Lebesgue measure modules; local
-- verification showed this item only needs Euclidean, measurable-space, and Lebesgue basic imports.

variable {n : ℕ}

/-- The open cube in `ℝ^n` centered at `c` with radius `r`, realized as the sup-metric ball in
`Fin n → ℝ` pulled back along the canonical equivalence with `EuclideanSpace ℝ (Fin n)`. -/
def openCube (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' Metric.ball ((EuclideanSpace.equiv (Fin n) ℝ) c) r

/-- Open cubes are open subsets of `ℝ^n`. -/
theorem isOpen_openCube (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    IsOpen (openCube c r) := by
  simpa [openCube] using
    Metric.isOpen_ball.preimage (EuclideanSpace.equiv (Fin n) ℝ).continuous

/-- A sequence of open cubes covers `A` when every radius is nonnegative and their union contains
`A`; zero-radius terms serve only as padding for finite or empty countable covers. -/
def IsOpenCubeCover (A : Set (EuclideanSpace ℝ (Fin n)))
    (c : ℕ → EuclideanSpace ℝ (Fin n)) (r : ℕ → ℝ) : Prop :=
  (∀ i, 0 ≤ r i) ∧ A ⊆ ⋃ i, openCube (c i) (r i)

namespace IsOpenCubeCover

/-- Every cube radius in an open-cube cover is nonnegative. -/
theorem radius_nonneg {A : Set (EuclideanSpace ℝ (Fin n))} {c : ℕ → EuclideanSpace ℝ (Fin n)}
    {r : ℕ → ℝ} (h : IsOpenCubeCover A c r) (i : ℕ) : 0 ≤ r i :=
  h.1 i

/-- The union of an open-cube cover contains the target set. -/
theorem subset_iUnion {A : Set (EuclideanSpace ℝ (Fin n))} {c : ℕ → EuclideanSpace ℝ (Fin n)}
    {r : ℕ → ℝ} (h : IsOpenCubeCover A c r) : A ⊆ ⋃ i, openCube (c i) (r i) :=
  h.2

end IsOpenCubeCover

/-- Exercise 6.1. Open rectangles can be replaced by open cubes or open balls in the definition of
subsets of measure zero. This theorem records the open-cube formulation. -/
theorem volume_eq_zero_iff_forall_pos_exists_open_cube_cover
    {A : Set (EuclideanSpace ℝ (Fin n))} :
    volume A = 0 ↔
      ∀ ε > 0, ∃ c : ℕ → EuclideanSpace ℝ (Fin n), ∃ r : ℕ → ℝ,
        IsOpenCubeCover A c r ∧
        (∑' i, volume (openCube (c i) (r i))) < ENNReal.ofReal ε := sorry

/-- A sequence of open balls covers `A` when every radius is nonnegative and their union contains
`A`; zero-radius terms serve only as padding for finite or empty countable covers. -/
def IsOpenBallCover (A : Set (EuclideanSpace ℝ (Fin n)))
    (c : ℕ → EuclideanSpace ℝ (Fin n)) (r : ℕ → ℝ) : Prop :=
  (∀ i, 0 ≤ r i) ∧ A ⊆ ⋃ i, Metric.ball (c i) (r i)

namespace IsOpenBallCover

/-- Every ball radius in an open-ball cover is nonnegative. -/
theorem radius_nonneg {A : Set (EuclideanSpace ℝ (Fin n))} {c : ℕ → EuclideanSpace ℝ (Fin n)}
    {r : ℕ → ℝ} (h : IsOpenBallCover A c r) (i : ℕ) : 0 ≤ r i :=
  h.1 i

/-- The union of an open-ball cover contains the target set. -/
theorem subset_iUnion {A : Set (EuclideanSpace ℝ (Fin n))} {c : ℕ → EuclideanSpace ℝ (Fin n)}
    {r : ℕ → ℝ} (h : IsOpenBallCover A c r) : A ⊆ ⋃ i, Metric.ball (c i) (r i) :=
  h.2

end IsOpenBallCover

/-- Companion ball-cover formulation: a subset has measure zero if and only if it can be covered by
countably many open balls whose total volume is arbitrarily small. -/
theorem volume_eq_zero_iff_forall_pos_exists_open_ball_cover
    {A : Set (EuclideanSpace ℝ (Fin n))} :
    volume A = 0 ↔
      ∀ ε > 0, ∃ c : ℕ → EuclideanSpace ℝ (Fin n), ∃ r : ℕ → ℝ,
        IsOpenBallCover A c r ∧
        (∑' i, volume (Metric.ball (c i) (r i))) < ENNReal.ofReal ε := sorry
