import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Problem_4_11 (from Chap04/Sec04_27) -/
-- Local API note: semantic `lean_leansearch` was unavailable in this session, so this item uses
-- the existing mathlib notions `IsCoveringMap` and `IsProperMap`; the converse-failure clause is
-- stated directly because importing the current repository example file would pull in unrelated
-- pre-existing errors.

open scoped Manifold

/-- Problem 4-11 (1): a topological covering map is proper if and only if each of its fibers is
finite. -/
theorem isProperMap_iff_finite_fibers_of_isCoveringMap
    {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X] {π : E → X}
    (hπ : IsCoveringMap π) :
    IsProperMap π ↔ ∀ x, (π ⁻¹' {x}).Finite := sorry

/-- Problem 4-11 (2): consequently, the converse of Proposition 4.46 is false; there exists a
smooth covering map that is not proper. -/
theorem exists_smoothCoveringMap_not_isProperMap :
    ∃ π : ℝ → Circle, Manifold.IsSmoothCoveringMap (𝓘(ℝ)) (𝓡 1) π ∧ ¬ IsProperMap π := sorry
