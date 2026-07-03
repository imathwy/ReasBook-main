import LecturesConvexOptimization_Nesterov_2018.Chap06.Definition_6_21
import LecturesConvexOptimization_Nesterov_2018.Chap06.Definition_6_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Metric
open scoped BigOperators

universe u

variable {ι : Type*} [Fintype ι]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "G" => ι ⊕ ι
local notation "E₂" => PiLp 1 (fun _ : G ↦ ℝ)

/- Proposition 6.21 lies in the operator-norm bridge domain for the same row data that feed the
Chapter 6 owner `maxAbsoluteValueOptimizationObjective`.

Primary domain:
- canonical operator norms of continuous linear maps `E →L[ℝ] E₂`;
- the finite `ℓ¹` norm on `PiLp 1`;
- the signed row stack `a_i, -a_i` indexed by `ι ⊕ ι`, viewed through canonical product assembly.

Sampled owner-style declarations:
- `maxAbsoluteValueOptimizationObjective` in `Definition_6_21`, the nearby source-facing Chapter 6
  owner for the max-absolute-value optimization data;
- `ContinuousLinearMap.pi`, the canonical owner assembling a finite family of continuous linear
  functionals into a product-valued continuous linear map;
- `PiLp.continuousLinearEquiv`, the canonical equivalence between a finite product and the
  corresponding `PiLp` space;
- `ContinuousLinearMap.sSup_sphere_eq_norm`, the canonical operator-norm support formula.

Best owner abstraction:
- source-facing: the signed stacking operator-norm identity attached to the row family `a`;
- core/canonical: the ambient norm `‖·‖` on the canonical stacked map expression;
- bridge/view: the pointwise `ℓ¹` norm formula for that canonical stack.

Primitive data:
- a finite row family `a : ι → StrongDual ℝ E`.

Derived API:
- the source-facing signed stack `signedRowStack a`;
- the canonical stacked-map expression implementing `signedRowStack`, built from
  `ContinuousLinearMap.pi` and `PiLp.continuousLinearEquiv`;
- its pointwise `ℓ¹` norm identity;
- the operator-norm equality and the source bounds from Proposition 6.21.

Source/core/bridge triage:
- source-facing: `signedRowStack` together with
  `signedRowStack_opNorm_eq_two_mul_sSup_abs_rowSum` and `signedRowStack_opNorm_bounds`;
- core/canonical: `ContinuousLinearMap.pi`, `PiLp.continuousLinearEquiv`, and the ambient
  operator norm;
- bridge/view: `signedRowStack_norm_eq_two_mul_sum_abs`.

This file therefore introduces the source-facing signed stack only once, as the short bridge
`signedRowStack a`, and states Proposition 6.21 on that owner surface. Its implementation remains
the canonical composition of `ContinuousLinearMap.pi` with `PiLp.continuousLinearEquiv`.
-/

/-- The canonical signed stack `Â[a]` attached to the row family `a`, with coordinates `aᵢ` and
`-aᵢ` on the signed index set `ι ⊕ ι`. -/
abbrev signedRowStack (a : ι → StrongDual ℝ E) : E →L[ℝ] E₂ :=
  (PiLp.continuousLinearEquiv 1 ℝ (fun _ : G ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (Sum.elim a (-a)))

local notation "Â[" a "]" => signedRowStack a

-- Proof sketch: expand the `ℓ¹` norm in `PiLp 1`; the signed stack has coordinates
-- `a_i x` and `-a_i x` over `ι ⊕ ι`, so the absolute values add to
-- `2 * ∑ j, |a j x|`.
/-- For the canonical signed stack attached to the row family `a`, the `ℓ¹` norm of the image of
`x` is twice the sum of the absolute row evaluations. -/
theorem signedRowStack_norm_eq_two_mul_sum_abs
    (a : ι → StrongDual ℝ E) (x : E) :
    ‖Â[a] x‖ = 2 * ∑ j, |a j x| := sorry

-- Proof sketch: combine `signedRowStack_norm_eq_two_mul_sum_abs` with
-- `ContinuousLinearMap.sSup_sphere_eq_norm` for the canonical stacked map.
/-- Proposition 6.21: the operator norm of the canonical signed stack equals twice the supremum
over the unit sphere of the sum of the absolute row evaluations. -/
theorem signedRowStack_opNorm_eq_two_mul_sSup_abs_rowSum
    (a : ι → StrongDual ℝ E) :
    ‖Â[a]‖ =
      2 * sSup ((fun x : E ↦ ∑ j, |a j x|) '' sphere (0 : E) 1) := sorry

-- Proof sketch: use Proposition 6.21 together with `∑ i |a_i x| ≥ |a_j x|` for each `j` and the
-- bound `|a_j x| ≤ ‖a_j‖` on the unit sphere.
/-- Proposition 6.21 yields the source lower and upper bounds
`2 * max_j ‖a_j‖ ≤ ‖Â‖ ≤ 2 * ∑ j ‖a_j‖` for the canonical signed stack `Â`. -/
theorem signedRowStack_opNorm_bounds
    (a : ι → StrongDual ℝ E) [Nonempty ι] :
    2 * Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ ‖a j‖) ≤ ‖Â[a]‖ ∧
      ‖Â[a]‖ ≤ 2 * ∑ j, ‖a j‖ := sorry

end
