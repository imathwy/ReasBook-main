import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.UnitSphereTangent

open Bundle

noncomputable section

-- Semantic recall via `lean_leansearch`: mathlib exposes the sphere manifold instances,
-- `TangentBundle`, and `Trivialization`, but no dedicated `Parallelizable` owner for spheres.
-- This file therefore records the source-facing parallelizability condition directly as the
-- existence of one global fiberwise-linear trivialization of the tangent bundle.

/-- The source-facing condition that `S^n` is parallelizable: its tangent bundle admits a single
global fiberwise `ℝ`-linear trivialization. -/
def sphereParallelizable (n : ℕ) : Prop :=
  ∃ e : Trivialization (EuclideanSpace ℝ (Fin n))
      (TotalSpace.proj : unitSphereTangentBundle n → unitSphere n),
    e.baseSet = Set.univ ∧ e.IsLinear ℝ

/-- Unfolding `sphereParallelizable` identifies parallelizability with the existence of a global
fiberwise `ℝ`-linear trivialization of the tangent bundle of `S^n`. -/
theorem sphereParallelizable_iff_exists_trivialization (n : ℕ) :
    sphereParallelizable n ↔
      ∃ e : Trivialization (EuclideanSpace ℝ (Fin n))
          (TotalSpace.proj : unitSphereTangentBundle n → unitSphere n),
        e.baseSet = Set.univ ∧ e.IsLinear ℝ :=
  Iff.rfl

/-- Theorem 24.6.8. If `S^n` is parallelizable, then `n = 0`, `n = 1`, `n = 3`, or `n = 7`. -/
theorem sphereParallelizable_possibleDimensions
    (n : ℕ) (h_parallelizable : sphereParallelizable n) :
    n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7 := sorry
