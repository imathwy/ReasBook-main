module

public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

namespace Set

/-- A set in `EuclideanSpace ℝ (Fin N)` is in general position when each of its finite
subsets containing at most `N + 1` points is affinely independent. -/
def InGeneralPosition {N : ℕ} (A : Set (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∀ s : Finset (EuclideanSpace ℝ (Fin N)),
    (s : Set (EuclideanSpace ℝ (Fin N))) ⊆ A → s.card ≤ N + 1 →
      AffineIndependent ℝ (fun x : s ↦ (x : EuclideanSpace ℝ (Fin N)))

/-- The finite-subset characterization of `Set.InGeneralPosition`. -/
theorem inGeneralPosition_iff {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin N))} :
    A.InGeneralPosition ↔
      ∀ s : Finset (EuclideanSpace ℝ (Fin N)),
        (s : Set (EuclideanSpace ℝ (Fin N))) ⊆ A → s.card ≤ N + 1 →
          AffineIndependent ℝ (fun x : s ↦ (x : EuclideanSpace ℝ (Fin N))) :=
  Iff.rfl

namespace InGeneralPosition

/-- Every sufficiently small finite subset of a set in general position is affinely
independent. -/
theorem affineIndependent {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin N))}
    (hA : A.InGeneralPosition) (s : Finset (EuclideanSpace ℝ (Fin N)))
    (hs : (s : Set (EuclideanSpace ℝ (Fin N))) ⊆ A) (hcard : s.card ≤ N + 1) :
    AffineIndependent ℝ (fun x : s ↦ (x : EuclideanSpace ℝ (Fin N))) :=
  hA s hs hcard

/-- Every subset of a set in general position is in general position. -/
theorem mono {N : ℕ} {A B : Set (EuclideanSpace ℝ (Fin N))}
    (hA : A.InGeneralPosition) (hBA : B ⊆ A) : B.InGeneralPosition := by
  intro s hs hcard
  exact hA s (hs.trans hBA) hcard

end InGeneralPosition

end Set
