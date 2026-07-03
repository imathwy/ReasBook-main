import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_28 (from Chap07) -/
noncomputable section

open Matrix
open scoped EllipsoidNotation PositiveDefMatrixNorm

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 7.28 lies in the positive-definite matrix norm / rank-one update domain.

Sampled owner-style declarations:
- `positiveDefMatrixNorm` in `Definition_7_23`, the chapter owner of the primal weighted norm
  `x ↦ √⟪Gx, x⟫`;
- `affineEllipsoid` in `Chap03/Lemma_3_2_7`, the chapter ellipsoid owner whose inverse-matrix
  specialization recovers the primal unit ball of `positiveDefMatrixNorm`;
- `rankOneUpdateAugmentedHull` in `Lemma_7_4`, the existing owner of the convex hull obtained by
  adjoining `±g` to a unit ellipsoid;
- `rankOneUpdatedMatrix` in `Lemma_7_4`, the existing owner of the rank-one interpolation
  `G(α) = (1 - α) G + α ggᵀ`.

Best owner abstraction:
- source-facing: the primal unit ball `{x | ‖x‖[G] ≤ 1}`, the signed hull obtained from it, and the
  rank-one interpolation;
- core/canonical: `positiveDefMatrixNorm`, `affineEllipsoid`, `rankOneUpdateAugmentedHull`, and
  `rankOneUpdatedMatrix`;
- bridge/view: the inverse-matrix identification of the primal unit ball and the subtype-parameter
  companions below.

Primitive data:
- a positive-definite matrix `G : Mat`;
- a vector `g : E`;
- an interpolation parameter `α`.

Derived API:
- the weighted unit ball is the unit ball of `positiveDefMatrixNorm`;
- equivalently it is `affineEllipsoid G⁻¹ 0`;
- the signed hull is `rankOneUpdateAugmentedHull G⁻¹ g`;
- the matrix path is `rankOneUpdatedMatrix G g α`.

Source/core/bridge triage:
- source-facing: Definition 7.28's weighted unit ball, signed hull, and interpolated matrix;
- core/canonical: the existing chapter owners above;
- bridge/view: the two theorems below.

This file is therefore recall/bridge-only: the previous `weightedUnitBall`,
`signedConvexHullOfWeightedUnitBall`, and `rankOneInterpolatedMatrix` were duplicate public shells
around existing chapter owners and are removed.
-/

/- Definition 7.28 recalls the primal weighted norm owner `positiveDefMatrixNorm`. -/
#check positiveDefMatrixNorm

/- Definition 7.28 recalls the signed hull owner `rankOneUpdateAugmentedHull`. -/
#check rankOneUpdateAugmentedHull

/- Definition 7.28 recalls the rank-one interpolation owner `rankOneUpdatedMatrix`. -/
#check rankOneUpdatedMatrix

/-- The primal `G`-unit ball from Definition 7.28 is the inverse-matrix ellipsoid
`E(G⁻¹, 0)`. -/
theorem mem_affineEllipsoid_inv_iff_norm_le_one
    (G : {G : Mat // G.PosDef}) (x : E) :
    x ∈ E(G.1⁻¹, (0 : E)) ↔ ‖x‖[G] ≤ 1 := by
  let GInv : {G : Mat // G.PosDef} := ⟨G.1⁻¹, G.2.inv⟩
  rw [← centeredMatrixEllipsoid_one_eq_affineEllipsoid G.1⁻¹]
  rw [mem_centeredMatrixEllipsoid_iff_dualNorm_le G.2.inv]
  rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv GInv x]
  rw [positiveDefMatrixNorm_def G x]
  let _ := G.2.isUnit.invertible
  simp [GInv, real_inner_comm]

/-- The signed hull from Definition 7.28 is the convex hull of the primal `G`-unit ball together
with the two points `±g`. -/
theorem rankOneUpdateAugmentedHull_inv_eq_convexHull_primalUnitBall
    (G : {G : Mat // G.PosDef}) (g : E) :
    rankOneUpdateAugmentedHull G.1⁻¹ g =
      convexHull ℝ ({x : E | ‖x‖[G] ≤ 1} ∪ ({g, -g} : Set E)) := by
  refine congrArg (convexHull ℝ) ?_
  ext x
  simp [mem_affineEllipsoid_inv_iff_norm_le_one]

end

/-! ### Proposition_7_28 (from Chap07) -/
open scoped Gradient

noncomputable section

universe u

/-
Proposition 7.28 lies in the support-function smoothing / envelope-gradient
domain.

Sampled owner-style declarations:
- `Uβ` and `Argmaxβ` in `Chap07/Definition_7_53`, the Chapter 7 source-facing
  owners of the smoothed value and its canonical argmax set;
- `smoothedObjective_hasFDerivAt` in `Chap06/Theorem_6_1`, the canonical
  Chapter 6 derivative owner for smoothed supremum problems;
- `smoothSupportFunctionApproximation_hasFDerivAt_and_omegaStar_upper_bound` in
  `Chap07/Lemma_7_10`, the source-facing derivative theorem already stated on
  the canonical dual owner `U_β`;
- mathlib `HasFDerivAt`, `DifferentiableAt`, `HasGradientAt`, and
  `HasGradientAt.gradient`, which give the dual-owner derivative API and the
  stronger Hilbert-space pullback bridge.

Best owner abstraction:
- source-facing: Proposition 7.28's differentiability theorem for the positive
  support-function approximation `U_β` on `StrongDual ℝ E`;
- core/canonical: `Uβ` and `Argmaxβ`;
- bridge/view: the pullback along `InnerProductSpace.toDual ℝ E` from the dual
  owner on `StrongDual ℝ E` to the Hilbert-space variable `s ∈ E`.

Primitive data:
- the feasible set `hatP`, barrier term `F`, center `x0`, and smoothing
  parameter `β : {β : ℝ // 0 < β}`;
- a point `s : StrongDual ℝ E` and the unique maximizer `u` of the canonical
  argmax set at `s`.

Derived API:
- the canonical support-function value owner `U_β` and argmax owner `Argmaxβ`;
- Fréchet differentiability on the dual owner, which only needs the real
  normed-space structure on `E`;
- the Hilbert-space gradient formula for the pulled-back function
  `s ↦ U_β((InnerProductSpace.toDual ℝ E) s)`, which belongs to a stronger
  bridge layer.

Source/core/bridge triage:
- source-facing: the dual-owner derivative theorem below;
- core/canonical: `Uβ` and `Argmaxβ`;
- bridge/view: the pulled-back gradient theorem on `E`.

The previous version stated the whole file under Hilbert-space /
finite-dimensional assumptions, even though the numbered Fréchet-derivative
statement only uses the Chapter 6 owner on `StrongDual ℝ E`. This refinement
keeps the main source-facing theorem on the weakest normed-space layer and
isolates the pulled-back Hilbert-space gradient results in a separate stronger
bridge section.
-/

section DualOwner

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (hatP : Set E) (F : E → ℝ) (x0 : E) (β : {β : ℝ // 0 < β})

-- Proof sketch: combine the unique-maximizer form of the owner-side Danskin
-- statement for `U_β` with the canonical pairing
-- `g ↦ g (u - x₀)` on `StrongDual ℝ E`.
/-- Proposition 7.28: for the positive support-function smoothing owner `U_β`,
if `u` is the unique maximizer in the canonical argmax set at `s`, then the
Fréchet derivative of `U_β` at `s` is evaluation at `u - x₀`. -/
theorem supportFunctionApproximation_hasFDerivAt_of_unique_argmax
    (s : StrongDual ℝ E) (u : E)
    (hu : u ∈ Argmaxβ hatP F β s)
    (hu_unique : ∀ v : E, v ∈ Argmaxβ hatP F β s → v = u) :
    HasFDerivAt (Uβ hatP F x0 β) (ContinuousLinearMap.apply ℝ ℝ (u - x0)) s := sorry

/-- The positive support-function approximation `U_β` is differentiable when
its canonical argmax set admits a unique selector. -/
-- Proof sketch: apply the pointwise owner-side derivative statement at each
-- dual point `s`.
theorem supportFunctionApproximation_differentiable_of_unique_argmax
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s) :
    Differentiable ℝ (Uβ hatP F x0 β) := by
  intro s
  exact
    (supportFunctionApproximation_hasFDerivAt_of_unique_argmax
      hatP F x0 β s (uStar s) (huStar s) (huStar_unique s)).differentiableAt

end DualOwner

section HilbertBridge

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (hatP : Set E) (F : E → ℝ) (x0 : E) (β : {β : ℝ // 0 < β})

-- Proof sketch: pull the dual-owner derivative back along
-- `InnerProductSpace.toDual ℝ E`; the representing vector remains `u - x₀`.
/-- The Hilbert-space pullback of `U_β` has gradient `u - x₀` at `s` whenever
`u` is the unique canonical argmax point over `((InnerProductSpace.toDual ℝ E) s)`. -/
theorem supportFunctionApproximation_hasGradientAt_of_unique_argmax
    (s u : E)
    (hu : u ∈ Argmaxβ hatP F β ((InnerProductSpace.toDual ℝ E) s))
    (hu_unique :
      ∀ v : E, v ∈ Argmaxβ hatP F β ((InnerProductSpace.toDual ℝ E) s) → v = u) :
    HasGradientAt
      (fun t : E ↦ Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t))
      (u - x0)
      s := sorry

/-- Under the unique-argmax hypothesis, the gradient of the pulled-back
positive support-function approximation is `u^*_β(s) - x₀`. -/
-- Proof sketch: extract the gradient from the pulled-back `HasGradientAt`
-- statement.
theorem gradient_supportFunctionApproximation_eq_of_unique_argmax
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (s : E) :
    ∇ (fun t : E ↦ Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t)) s =
      uStar ((InnerProductSpace.toDual ℝ E) s) - x0 := by
  simpa using
    (supportFunctionApproximation_hasGradientAt_of_unique_argmax
      hatP F x0 β s (uStar ((InnerProductSpace.toDual ℝ E) s))
      (huStar ((InnerProductSpace.toDual ℝ E) s))
      (huStar_unique ((InnerProductSpace.toDual ℝ E) s))).gradient

end HilbertBridge
