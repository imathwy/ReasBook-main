import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_30 (from Chap07) -/
noncomputable section

open Matrix
open scoped EllipsoidNotation PositiveDefMatrixNorm SupportFunction

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 7.30 lies in the positive-definite ellipsoid / support-function domain.

Sampled owner-style declarations:
- `supportFunction` with notation `ξ[Q]` in `Chap03/Definition_3_9`, the chapter owner of support
  functions;
- `supportFunction_convexHull_union_eq_max` in `Chap03/Lemma_3_3`, the exact upstream support
  theorem for convex hulls of two-set unions;
- `positiveDefMatrixNorm` in `Definition_7_23`, the chapter owner of the weighted norm;
- `E(H, x̄)` in `Chap03/Lemma_3_2_7` together with the Chapter 7 bridge
  `mem_affineEllipsoid_inv_iff_norm_le_one` from `Definition_7_28`.

Best owner abstraction:
- source-facing: `convexHullOfWeightedUnitBallAndPoint`, the one-sided hull `C_g(G)`;
- core/canonical: `ξ[Q]`, `E(H, x̄)`, and `positiveDefMatrixNorm`;
- bridge/view: the primal-unit-ball reformulation and the support-function theorem below.

Primitive data:
- a positive-definite matrix `G : {G : Mat // G.PosDef}`;
- a vector `g : E`.

Derived API:
- the one-sided hull `C_g(G) = convexHull ℝ (E(G⁻¹, 0) ∪ {g})`;
- the equivalent source wording with the primal unit ball `{x | ‖x‖[G] ≤ 1}`;
- the support-function identity for `C_g(G)` derived from the chapter support-function owner.

Source/core/bridge triage:
- source-facing: `convexHullOfWeightedUnitBallAndPoint`;
- core/canonical: `supportFunction`, `affineEllipsoid`, and `positiveDefMatrixNorm`;
- bridge/view: the two theorem-level restatements below.

This file keeps only the genuinely source-facing hull owner. The previous local `supportFunction`
and `weightedUnitBall` declarations were duplicate public shells around the chapter owners
`ξ[Q]` and `E(G⁻¹, 0)`, so they are removed. -/

/-- Definition 7.30: for a positive-definite matrix `G` on `ℝⁿ` and a vector `g ∈ ℝⁿ`, the set
`C_g(G)` is the convex hull of the weighted unit ball `W₁(G) = E(G⁻¹, 0)` together with the point
`g`. -/
def convexHullOfWeightedUnitBallAndPoint
    (G : {G : Mat // G.PosDef}) (g : E) : Set E :=
  convexHull ℝ (E(G.1⁻¹, 0) ∪ ({g} : Set E))

namespace OneSidedHullNotation

/- Source-facing Lean notation for the textbook weighted unit ball `W₁(G)` and one-sided hull
`C_g(G)`. -/
scoped notation:max "W₁(" G:arg ")" =>
  W[1](G.1⁻¹)

scoped notation:max "C_[" g:arg "](" G:arg ")" =>
  convexHullOfWeightedUnitBallAndPoint G g

end OneSidedHullNotation

open scoped OneSidedHullNotation

/-- Expanding `C_[g](G)` gives the convex hull of `W₁(G)` and the point `g`. -/
theorem convexHullOfWeightedUnitBallAndPoint_def
    (G : {G : Mat // G.PosDef}) (g : E) :
    C_[g](G) = convexHull ℝ (W₁(G) ∪ ({g} : Set E)) := by
  rw [show W₁(G) = E(G.1⁻¹, (0 : E)) by
    simpa using centeredMatrixEllipsoid_one_eq_affineEllipsoid G.1⁻¹]
  simp [convexHullOfWeightedUnitBallAndPoint]

/-- The weighted unit ball `W₁(G)` is exactly the primal `G`-unit ball `{x | ‖x‖[G] ≤ 1}`. -/
theorem weightedUnitBall_eq_primalUnitBall
    (G : {G : Mat // G.PosDef}) :
    W₁(G) = {x : E | ‖x‖[G] ≤ 1} := by
  rw [show W₁(G) = E(G.1⁻¹, (0 : E)) by
    simpa using centeredMatrixEllipsoid_one_eq_affineEllipsoid G.1⁻¹]
  ext x
  simp [mem_affineEllipsoid_inv_iff_norm_le_one]

/-- Expanding `C_[g](G)` gives the convex hull of the primal `G`-unit ball and the point `g`. -/
theorem convexHullOfWeightedUnitBallAndPoint_eq_convexHull_primalUnitBall
    (G : {G : Mat // G.PosDef}) (g : E) :
    C_[g](G) =
      convexHull ℝ ({x : E | ‖x‖[G] ≤ 1} ∪ ({g} : Set E)) := by
  rw [convexHullOfWeightedUnitBallAndPoint_def, weightedUnitBall_eq_primalUnitBall]

/-- The support function of `C_[g](G)` is the maximum of the support functions of `W₁(G)` and the
singleton `{g}`. Equivalently, this is the chapter-owner form of the textbook formula
`ξ[C_[g](G)] x = max (ξ[W₁(G)] x) ⟪g, x⟫`. -/
theorem supportFunction_convexHullOfWeightedUnitBallAndPoint_eq_max
    (G : {G : Mat // G.PosDef}) (g x : E) :
    ξ[C_[g](G)] x =
      max (ξ[W₁(G)] x) (inner ℝ g x : EReal) := by
  simpa [convexHullOfWeightedUnitBallAndPoint_def, supportFunction_apply] using
    supportFunction_convexHull_union_eq_max (W₁(G)) ({g} : Set E) x

end

/-! ### Proposition_7_30 (from Chap07) -/
noncomputable section

universe u v

section

variable {E : Type u} {E₁ : Type v}
variable [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup E₁] [Module ℝ E₁]

/- Proposition 7.30 lies in the finite weighted-average / logarithmic primal-dual gap domain.

Sampled owner-style declarations:
- `Finset.centerMass` in mathlib's convex-combination API, the canonical owner of weighted finite
  averages;
- `Finset.centroid` in mathlib's affine-space API, the equal-weight specialization of
  `Finset.centerMass`;
- `Finset.centroid_eq_centerMass`, the bridge identifying the arithmetic mean with the canonical
  center-of-mass owner;
- `Real.log_le_iff_le_exp`, the canonical logarithm-to-exponential comparison used in the final
  estimate.

Best owner abstraction:
- source-facing: Proposition 7.30's primal-dual efficiency estimate;
- core/canonical: `Finset.centroid` for the primal arithmetic mean and `Finset.centerMass` for the
  inverse-`ψ` weighted dual average;
- bridge/view: the logarithmic hypothesis rewritten as an exponential bound.

Primitive data:
- the iterate family `x : Fin (k + 1) → P`;
- the positive objective `ψ` and positive dual objective `ψStar`;
- the dual-point assignment `u`.

Derived API:
- the canonical primal aggregate `barx`;
- the canonical dual aggregate `barU`;
- the exponential lower bound obtained from the logarithmic gap inequality.

The previous file stored all three aggregates as separate public definitions even though they are
exact instances of the mathlib owners `Finset.centroid` and `Finset.centerMass`. This refinement
deletes those duplicate wrappers and states the proposition directly on the owner abstractions.
The auxiliary witness `barx : P` is also removed from the theorem surface: the primal aggregate is
intrinsic, so the only required source-facing input is its membership in `P`.
-/

section WeightedAverages

variable {P : Set E} {Ω : Set E₁}
variable (ψ : P → { r : ℝ // 0 < r }) (u : P → E₁) (ψStar : Ω → { r : ℝ // 0 < r })
variable {k : ℕ} (x : Fin (k + 1) → P)

local notation "barx" => Finset.univ.centroid ℝ (fun i ↦ (x i : E))
local notation "barU" =>
  Finset.univ.centerMass (fun i ↦ ((ψ (x i) : ℝ)⁻¹)) (fun i ↦ u (x i))

-- Proof sketch: the logarithmic hypothesis is `log (ψ⋆(barU) / ψ(barx)) ≤ ellStar / Sk`.
-- Apply `Real.log_le_iff_le_exp` to bound the ratio by `exp (ellStar / Sk)`, then divide by the
-- positive factor `exp (ellStar / Sk)` and rewrite with `Real.exp_neg`.
/-- Proposition 7.30: if the logarithmic primal-dual gap at the canonical weighted aggregates
`barx` and `barU` is bounded by `\ell_k^\star / S_k`, then
`ψ(barx) ≥ ψ^\star(barU) \exp(-\ell_k^\star / S_k)`. Here `barx` is the arithmetic mean of the
iterates and `barU` is their inverse-`ψ` weighted dual center of mass. -/
theorem primalDualEfficiencyEstimate_of_weightedLogarithmicGap
    (hbarx_mem : barx ∈ P)
    (hbarU_mem : barU ∈ Ω)
    {Sk ellStar : ℝ}
    (hloggap :
      ellStar / Sk ≥
        Real.log ((ψStar ⟨barU, hbarU_mem⟩ : ℝ) / (ψ ⟨barx, hbarx_mem⟩ : ℝ))) :
    (ψ ⟨barx, hbarx_mem⟩ : ℝ) ≥
      (ψStar ⟨barU, hbarU_mem⟩ : ℝ) * Real.exp (-ellStar / Sk) := by
  let a : ℝ := ψStar ⟨barU, hbarU_mem⟩
  let b : ℝ := ψ ⟨barx, hbarx_mem⟩
  have ha : 0 < a := (ψStar ⟨barU, hbarU_mem⟩).2
  have hb : 0 < b := (ψ ⟨barx, hbarx_mem⟩).2
  have hratio : a / b ≤ Real.exp (ellStar / Sk) := by
    refine (Real.log_le_iff_le_exp (show 0 < a / b by exact div_pos ha hb)).1 ?_
    simpa [a, b] using hloggap
  have hmul : a ≤ Real.exp (ellStar / Sk) * b :=
    (div_le_iff₀ hb).1 hratio
  have hexp : 0 < Real.exp (ellStar / Sk) := Real.exp_pos _
  have hdiv : a / Real.exp (ellStar / Sk) ≤ b :=
    (div_le_iff₀ hexp).2 (by simpa [mul_comm] using hmul)
  simpa [a, b, Real.exp_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

end WeightedAverages

end
