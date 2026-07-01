import Mathlib
import Nesterov.Chap03.Lemma_3_2_7
import Nesterov.Chap07.Definition_7_23
import Nesterov.Chap07.Definition_7_26
import Nesterov.Chap07.Definition_7_34

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped EllipsoidNotation PositiveDefMatrixNorm

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Matₙ" => Matrix (Fin n) (Fin n) ℝ

/- Lemma 7.7 lies in Chapter 7's diagonal ellipsoid / dual-norm comparison domain.

Sampled owner-style declarations:
- `Matrix.IsDiag` and `Matrix.PosDef` in mathlib's diagonal / positive-definite matrix API, the
  canonical matrix-level owners for diagonal positive-definite matrices;
- `positiveDefMatrixNorm` and its dual notation `‖g‖[G,*]` in `Definition_7_23`, the core owner
  for the weighted dual norm;
- `matrixEllipsoid` with centered notation `W[r](G)` in `Definition_7_26`, the chapter owner for
  ellipsoids;
- `ellipsoidBoxGeneratedConvexSet`, `ellipsoidBoxInterpolationMatrix`, and
  `ellipsoidBoxLogVolumePotential` in `Definition_7_34`, the source-facing owners introduced for
  the present geometric construction.

Best owner abstraction:
- source-facing: `ellipsoidBoxAlphaStar` and the four theorem-level consequences of Lemma 7.7;
- core/canonical: `Matrix.PosDef`, `‖g‖[G,*]`, `W[r](G)`, and
  `ellipsoidBoxLogVolumePotential`;
- bridge/view: the explicit formula for `α*` and the scalar logarithmic comparison expression used
  in parts (3) and (4).

Primitive data:
- a matrix `D : Matₙ`;
- its positive-definiteness proof when the dual norm is used;
- a vector `g : Eₙ`;
- scalar parameters `α` and `γ`.

Derived API:
- the dual-norm square `‖g‖[⟨D, hDpos⟩,*] ^ 2` is derived from the upstream owner and is not kept
  as a separate public definition;
- the source-facing critical value `α*`;
- the theorem-level logarithmic comparison bounds used in parts (3) and (4).

Source/core/bridge triage:
- source-facing: `ellipsoidBoxAlphaStar`;
- core/canonical: `⟨D, hDpos⟩`, `W[r](G)`, `ellipsoidBoxLogVolumePotential`;
- bridge/view: the theorem-level inequalities below.

This refinement removes the duplicate public scalar wrapper for `‖g‖*_D²` and rewrites the target
file directly against the canonical dual-norm owner supplied upstream. -/

/-- The critical value `α* = (S - n) / ((2 S - n) S)` used in the sign-invariant rounding step,
where `S = ‖g‖[⟨D, hDpos⟩,*]^2`. -/
def ellipsoidBoxAlphaStar
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ) : ℝ :=
  (‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ) - (n : ℝ)) /
    ((((2 : ℝ) * (‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ))) - (n : ℝ)) *
      (‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ)))

-- Proof sketch: unfold `ellipsoidBoxAlphaStar`.
/-- Expanding `ellipsoidBoxAlphaStar d g` gives the closed formula
`(S - n) / ((2 S - n) S)` with `S = ‖g‖[⟨D, hDpos⟩,*]^2`. -/
theorem ellipsoidBoxAlphaStar_eq
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ) :
    ellipsoidBoxAlphaStar D hDpos g =
      (‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ) - (n : ℝ)) /
        ((((2 : ℝ) * (‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ))) - (n : ℝ)) *
          (‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ))) :=
  rfl

-- Proof sketch: write `S = ‖g‖[d.toPositiveDefMatrix,*]^2`. The hypothesis `S > n` gives
-- positivity of the numerator and denominator in the defining formula for `α*`; if `n = 0`, then
-- `α* = 1 / (2 S)`, while if `0 < n`, `ellipsoidBoxAlphaStar_mem_Ioc_inv_dim` yields
-- `0 < α* ≤ 1 / n ≤ 1`. In either case `α* ∈ [0, 1)`.
/-- Under `S > n`, the canonical value `α*` lies in the half-open unit interval `[0, 1)`. -/
theorem ellipsoidBoxAlphaStar_mem_halfOpenUnitInterval
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ)
    (hS : (n : ℝ) < ‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ)) :
    ellipsoidBoxAlphaStar D hDpos g ∈ Set.Ico (0 : ℝ) 1 := sorry

-- Proof sketch: compare the Minkowski functional of the centered ellipsoid with shape matrix
-- `(1 - α) D + α D²(g)` to the support function of `Conv(W₁(D) ∪ B(|g|))`, using the coordinatewise
-- bound `(∑ i (g i * |x i|)^2) ≤ (∑ i g i * |x i|)^2`.
/-- Lemma 7.7 (1): for every `α ∈ [0, 1]`, the unit ellipsoid with interpolation matrix
`G(α) = (1 - α) D + α D²(g)` is contained in `C = Conv(W₁(D) ∪ B(|g|))`. -/
theorem centeredMatrixEllipsoid_closedInterpolation_subset_ellipsoidBoxGeneratedConvexSet
    (D : Matₙ) (g : Eₙ) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    W[1]((ellipsoidBoxInterpolationMatrix D g α)) ⊆
      ellipsoidBoxGeneratedConvexSet D g := sorry

-- Proof sketch: write `S = ‖g‖[d.toPositiveDefMatrix,*]^2`; the hypothesis `S > n` gives
-- positivity of the numerator, and the algebraic inequality
-- `ellipsoidBoxAlphaStar d g ≤ 1 / n` reduces to `0 ≤ 2 S^2 - n S + n^2`.
/-- Lemma 7.7 (2): if `S = ‖g‖*_D² > n`, then the critical value
`α* = (S - n) / ((2 S - n) S)` lies in the interval `(0, 1 / n]`. -/
theorem ellipsoidBoxAlphaStar_mem_Ioc_inv_dim
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ) (hn : 0 < n)
    (hS : (n : ℝ) < ‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ)) :
    ellipsoidBoxAlphaStar D hDpos g ∈ Set.Ioc (0 : ℝ) (1 / (n : ℝ)) := sorry

-- Proof sketch: combine the self-concordant upper estimate for `V(α)` with the choice
-- `α = ellipsoidBoxAlphaStar d g`, rewrite the resulting scalar bound in terms of
-- `S = ‖g‖[d.toPositiveDefMatrix,*]^2`, and then use the interval hypothesis
-- `1 < γ ≤ ‖g‖[d.toPositiveDefMatrix,*] / √n`. Its upper bound already forces the comparison
-- regime `n < S`, so no separate nontriviality or `S > n` hypothesis is needed in the public
-- statement. This yields the comparison with
-- `log (1 + (γ² - 1) / γ²) - (γ² - 1) / γ²`.
/-- Lemma 7.7 (3): if `1 < γ ≤ ‖g‖*_D / √n`, then the logarithmic potential at `α*` is bounded
above by the scalar
comparison term `log (1 + (γ² - 1) / γ²) - (γ² - 1) / γ²`. -/
theorem ellipsoidBoxLogVolumePotential_alphaStar_le_gammaComparison
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ) (γ : ℝ)
    (hγ :
      γ ∈
        Set.Ioc
          (1 : ℝ)
          (‖g‖[⟨D, hDpos⟩,*] / Real.sqrt (n : ℝ))) :
    ellipsoidBoxLogVolumePotential D g (ellipsoidBoxAlphaStar D hDpos g) ≤
      Real.log (1 + (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ)) -
        (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) := sorry

-- Proof sketch: set `u = (γ² - 1) / γ²`; the assumption `γ > 1` gives `u > 0`, and the standard
-- inequality `log (1 + u) < u` yields the strict negativity.
/-- Lemma 7.7 (4): for every `γ > 1`, the comparison term
`log (1 + (γ² - 1) / γ²) - (γ² - 1) / γ²` is strictly negative. -/
theorem ellipsoidBoxGammaComparison_neg
    (γ : ℝ) (hγ : 1 < γ) :
    Real.log (1 + (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ)) -
        (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) < 0 := sorry

end
