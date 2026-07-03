import LecturesConvexOptimization_Nesterov_2018.Chap07.Definition_7_29
import LecturesConvexOptimization_Nesterov_2018.Chap07.Definition_7_33

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Theorem 7.8 lies in the Chapter 7 centered ellipsoid-rounding / sign-invariant convex-set
domain.

Sampled owner-style declarations:
* `IsEllipsoidalRounding` in `Chap07/Definition_7_29`, the chapter owner of centered
  `γ √n`-ellipsoidal roundings;
* `IsEllipsoidalRounding.unit_ellipsoid_subset` and
  `IsEllipsoidalRounding.subset_outer_ellipsoid` in `Chap07/Definition_7_29`, the derived inner
  and outer containment API for that owner;
* `IsSignInvariant` in `Chap07/Definition_7_33`, the chapter owner of sign-symmetry;
* `matrixEllipsoid` / `W[r](G)` in `Chap07/Definition_7_26`, reused upstream by
  `IsEllipsoidalRounding`.

Best owner abstraction:
* source-facing: the existence of a diagonal centered ellipsoidal rounding for a sign-invariant
  convex set;
* core/canonical: `IsEllipsoidalRounding C γ D`;
* bridge/view: the extra diagonality condition `D.IsDiag`.

Primitive data:
* a set `C : Set E`;
* a matrix `D : Mat`.

Derived API:
* positive definiteness and the two ellipsoid containments, all supplied by
  `IsEllipsoidalRounding C 1 D`;
* diagonality as the only additional theorem-specific datum.

This refinement deletes the duplicate local wrapper `IsDiagonalEllipsoidalRounding`. The theorem is
source-facing, but its rounding core is already owned by `IsEllipsoidalRounding`; only the extra
diagonality requirement remains outside that owner.
-/

-- Proof sketch: choose a volume-maximizing feasible diagonal matrix among those whose unit
-- ellipsoid lies in `C`, and use the sign-invariant rounding argument from Lemma 7.7 to show that
-- the optimal outer radius is at most `Real.sqrt n`.
/-- Theorem 7.8: every bounded sign-symmetric convex set in `ℝⁿ` with nonempty interior admits a
positive-definite diagonal matrix `D` such that `W_1(D) ⊆ C ⊆ W_(sqrt n)(D)`. -/
theorem exists_diagonal_rounding_of_signInvariant_convex_interior_nonempty_bounded
    {C : Set E} (h_sign : IsSignInvariant C) (h_convex : Convex ℝ C)
    (h_interior : (interior C).Nonempty) (h_bounded : Bornology.IsBounded C) :
    ∃ D : Mat, D.IsDiag ∧ IsEllipsoidalRounding C 1 D := sorry
