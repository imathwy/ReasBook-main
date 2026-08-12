import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Nesterov.Chap03.Lemma_3_2_7

-- Declarations for this item will be appended below by the statement pipeline.

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

open Matrix
open scoped EllipsoidNotation

/-
Definition 3.56 belongs to the chapter's Euclidean ellipsoid API.

Sampled owner-style declarations:
- `affineEllipsoid` in `Lemma_3_2_7`, the earlier chapter owner of the textbook ellipsoid
  `E(H, x̄)`;
- `mem_affineEllipsoid_iff` in `Lemma_3_2_7`, the exact membership companion theorem;
- `centerCutEllipsoid` in `Lemma_3_2_7`, the next ellipsoid-method construction derived from the
  same owner;
- `Matrix.toEuclideanLin`, the ambient mathlib map turning a matrix into its Euclidean linear
  action.

Best owner abstraction:
- source-facing/core owner: `affineEllipsoid`;
- bridge/view: `mem_affineEllipsoid_iff`.

Primitive data:
- a shape matrix `H : Mat`;
- a center `xBar : E`.

Derived API:
- the ellipsoid `affineEllipsoid H xBar`;
- the membership characterization `mem_affineEllipsoid_iff`.

Source/core/bridge triage:
- source-facing: `affineEllipsoid`;
- core/canonical: the existing chapter owner from `Lemma_3_2_7`;
- bridge/view: the companion membership equivalence.

This file is therefore recall-only: the chapter already owns the ellipsoid and its defining
membership theorem upstream, so no parallel local definition is kept here.
-/

recall affineEllipsoid
    (H : Mat) (xBar : E) :
    Set E

/- The defining quadratic-membership formula is already owned by the upstream companion theorem. -/
recall mem_affineEllipsoid_iff
    {H : Mat} {xBar x : E} :
    x ∈ E(H, xBar) ↔
      inner ℝ (toEuclideanLin H⁻¹ (x - xBar)) (x - xBar) ≤ 1
