import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_29
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_33

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace (positiveOrthant)
open Matrix
open scoped BigOperators EllipsoidNotation SymmetricBox

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Lemma 7.9 lies in Chapter 7's diagonal ellipsoid / symmetric-box rounding domain.

Sampled owner-style declarations:
- `symmetricBox` with notation `B(g)` in `Chap07/Definition_7_33`, the chapter owner for
  coordinate boxes;
- `mem_symmetricBox_iff_abs_le` in `Chap07/Definition_7_33`, the owner theorem for the textbook
  absolute-value membership view of `B(a)`;
- `matrixEllipsoid` with centered notation `W[r](G)` in `Chap07/Definition_7_26`, the chapter
  owner for ellipsoids;
- `IsEllipsoidalRounding` in `Chap07/Definition_7_29`, the chapter owner for centered
  `γ √n`-ellipsoidal roundings;
- `EuclideanSpace.positiveOrthant` and `EuclideanSpace.mem_positiveOrthant_iff` in
  `Chap01/Definition_1_10_2`, the canonical positivity owner for the semiaxis vector.

Best owner abstraction:
- source-facing: the symmetric-box sandwich hypothesis and the resulting diagonal ellipsoidal
  rounding;
- core/canonical: `positiveOrthant`, `B(g)`, `W[r](G)`, and `IsEllipsoidalRounding`;
- bridge/view: the coordinate membership theorems specialized to `B(a)` and
  `W[r](Matrix.diagonal fun i ↦ (a i)^2)`.

Primitive data:
- the semiaxis vector `a : E`;
- a set `C : Set E`;
- a dilation factor `m : ℝ`.

Derived API:
- the inner box `B(a)` and outer box `B(m • a)`, read through
  `mem_symmetricBox_iff_abs_le`;
- the diagonal shape matrix `Matrix.diagonal fun i ↦ (a i)^2`, whose semiaxes are `a i`;
- the centered rounding datum
  `IsEllipsoidalRounding C m (Matrix.diagonal fun i ↦ (a i)^2)`;
- the inner and outer ellipsoid containments recovered canonically from that owner.

Source/core/bridge triage:
- source-facing: the sandwich theorem below;
- core/canonical: `positiveOrthant`, `B(g)`, `mem_symmetricBox_iff_abs_le`, `W[r](G)`, and
  `IsEllipsoidalRounding`;
- bridge/view: the diagonal-square ellipsoid membership theorem specialized to
  `W[r](Matrix.diagonal fun i ↦ (a i)^2)`.

This refinement deletes the local duplicate box-membership theorem and reuses the Chapter 7 box
owner `B(·)` together with `mem_symmetricBox_iff_abs_le` directly. The main theorem is now stated
through the Chapter 7 rounding owner `IsEllipsoidalRounding` instead of exposing its positive
definiteness and ellipsoid containments as a parallel conjunction, while the ambient dimension now
matches the chapter owners at `{n : ℕ}` instead of unnecessarily strengthening to `ℕ+`.
-/

-- Proof sketch: specialize the centered ellipsoid owner `W[r](G)` to the diagonal-square matrix
-- `G = D²` with `D = diag(d)`, then expand the inverse diagonal quadratic form.
/-- Membership in the diagonal ellipsoid with shape matrix `D²`, where `D = diag(d)`, is exactly
the coordinate inequality `sqrt (∑ i, (x i / d i)^2) ≤ r` when the semiaxes `d i` are positive.
-/
theorem mem_diagonalSquareEllipsoid_iff
    (a : E) (ha : a ∈ positiveOrthant n) (r : ℝ) (x : E) :
    x ∈ W[r]((diagonal fun i ↦ (a i) ^ (2 : ℕ))) ↔
      Real.sqrt (∑ i, (x i / a i) ^ (2 : ℕ)) ≤ r := sorry

-- Proof sketch: the inner containment `W[1](D²) ⊆ B(d)` is the coordinatewise estimate
-- `|x i| / d i ≤ 1` obtained by bounding each nonnegative summand in
-- `∑ i, (x i / d i)^2 ≤ 1`. For the outer containment, `x ∈ B(m d)` gives
-- `|x i| / d i ≤ m` for each coordinate, so
-- `∑ i, (x i / d i)^2 ≤ n * m^2`, equivalently
-- `sqrt (∑ i, (x i / d i)^2) ≤ m * sqrt n`.
/-- Lemma 7.9: if a set `C` lies between the boxes `B(d)` and `B(m d)`, where the semiaxes `d i`
are positive, then `C` lies between the corresponding diagonal ellipsoids
`W₁(D²)` and `W_{m √n}(D²)`, where `D = diag(d)`. Equivalently, the diagonal-square matrix
`D²` is an ellipsoidal rounding of `C` with parameter `m`. -/
theorem symmetricBox_sandwich_implies_diagonalEllipsoid_sandwich
    (a : E) (ha : a ∈ positiveOrthant n) {m : ℝ} {C : Set E}
    (h_left : B(a) ⊆ C)
    (h_right : C ⊆ B((m • a))) :
    IsEllipsoidalRounding C m (diagonal fun i ↦ (a i) ^ (2 : ℕ)) := sorry

end
