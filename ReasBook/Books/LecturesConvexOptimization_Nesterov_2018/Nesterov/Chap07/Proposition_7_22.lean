import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap01.Definition_1_3_7
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_17

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped RealSymmetricMatrixSpace

universe u

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n

/- Proposition 7.22 lies in Chapter 7's symmetric-matrix spectral-radius minimization domain.

Sampled owner-style declarations:
- `ρ(X)` in `Definition_7_17`, the chapter owner for the real-valued spectral radius on `𝕊^n`;
- `𝕊^n` in Chapter 5, the chapter owner for real symmetric matrices;
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the project's
  canonical optimization-value owner for a feasible set and real-valued objective;
- `SpectralRadiusMinimizationProblem.maxRank` in `Definition_7_45`, the later chapter owner for
  `sup_y rank(A y)` in the specialized optimization problem.

Best owner abstraction:
- source-facing: Proposition 7.22's induced lower and upper bounds for `f_p*` along an arbitrary
  family `A : Q → 𝕊^n`;
- core/canonical: the chapter owners `𝕊^n` and `ρ(X)`, together with the Chapter 1 constrained
  minimization owner for the induced infima and `sSup` for the rank bound;
- bridge/view: the named source quantities `inducedRadiusInf`, `inducedRankSup`, and
  `inducedObjectiveInf`.

Primitive data:
- a feasible type `Q`;
- a family `A : Q → 𝕊^n`;
- an exponent parameter `p : ℕ+`;
- the objective `F_p : 𝕊^n → ℝ`;
- the pointwise lower and upper bounds on `F_p`.

Derived API:
- `φ*` as the canonical owner optimal value of `y ↦ ρ(A y)`;
- `r = sup_y rank(A y)`;
- `f_p*` as the canonical owner optimal value of `y ↦ F_p(A y)`.

Source/core/bridge triage:
- source-facing: the proposition below and the three named source quantities `φ*`, `r`, `f_p*`;
- core/canonical: `ρ(X)` on `𝕊^n`, `SetConstrainedMinimizationProblem.optimalValue`, and `sSup`;
- bridge/view: the explicit `EReal`-infimum formulas and the final real-valued inequality bridge.

The previous file duplicated the chapter symmetric-matrix carrier with a local subtype
`selfAdjoint (Matrix ...)`, treated the spectral radius as an arbitrary parameter `ρ`, and
totalized the source infima as plain real `sInf` values on an arbitrary type `Q`. This refinement
keeps the source-facing quantities `φ*`, `r`, and `f_p*`, but moves the two infima onto the
canonical Chapter 1 optimal-value owner so empty families no longer silently collapse to `0`. The
proposition itself is then the finite real-surface bridge for those canonical optimal values.
-/

/-- The infimum `φ*` of the spectral radii `ρ(A y)` along a family of symmetric matrices, encoded
as the canonical constrained optimal value on the feasible type `Q`. -/
def inducedRadiusInf {Q : Type u} (A : Q → SymmMat) : EReal :=
  (.mk Set.univ fun y : Q ↦ ρ(A y) : SetConstrainedMinimizationProblem Q).optimalValue

/-- Expanding `inducedRadiusInf` recovers the extended-real infimum of `ρ(A y)` over `Q`. -/
theorem inducedRadiusInf_eq_sInf_range {Q : Type u} (A : Q → SymmMat) :
    inducedRadiusInf A = sInf (Set.range fun y : Q ↦ (ρ(A y) : EReal)) := by
  let problem : SetConstrainedMinimizationProblem Q := .mk Set.univ fun y ↦ ρ(A y)
  simpa [inducedRadiusInf, problem, Set.image_univ] using problem.optimalValue_eq_sInf_image

/-- The supremum `r` of the ranks of the symmetric matrices `A y`. -/
def inducedRankSup {Q : Type u} (A : Q → SymmMat) : ℕ :=
  sSup (Set.range fun y : Q ↦ Matrix.rank (A y : Matrix (Fin n) (Fin n) ℝ))

/-- The induced objective infimum `f_p*`, encoded as the canonical constrained optimal value of
`y ↦ F_p(A y)` on the feasible type `Q`. -/
def inducedObjectiveInf {Q : Type u} (F_p : SymmMat → ℝ) (A : Q → SymmMat) : EReal :=
  (.mk Set.univ fun y : Q ↦ F_p (A y) : SetConstrainedMinimizationProblem Q).optimalValue

/-- Expanding `inducedObjectiveInf` recovers the extended-real infimum of `F_p(A y)` over `Q`. -/
theorem inducedObjectiveInf_eq_sInf_range {Q : Type u} (F_p : SymmMat → ℝ) (A : Q → SymmMat) :
    inducedObjectiveInf F_p A = sInf (Set.range fun y : Q ↦ (F_p (A y) : EReal)) := by
  let problem : SetConstrainedMinimizationProblem Q := .mk Set.univ fun y ↦ F_p (A y)
  simpa [inducedObjectiveInf, problem, Set.image_univ] using
    problem.optimalValue_eq_sInf_image

-- Proof sketch: because `Q` is nonempty, the two owner optimal values are finite and their
-- `toReal` projections recover the textbook real infima. Apply the assumed pointwise inequalities
-- to `A y`; the lower bound follows by taking infima of `(1 / 2) * ρ(A y)^2 ≤ F_p(A y)`, and the
-- upper bound uses `Matrix.rank (A y) ≤ inducedRankSup A` before taking infima.
/-- Proposition 7.22: if `F_p` satisfies the pointwise bounds
`(1 / 2) ρ(X)^2 ≤ F_p(X) ≤ (1 / 2) ρ(X)^2 (rank X)^(1 / p)` on real symmetric matrices, then the
induced infimum `f_p* = inf_y F_p(A y)`, read as the real part of the canonical owner optimal
value on a nonempty feasible type `Q`, satisfies
`(1 / 2) φ*^2 ≤ f_p* ≤ (1 / 2) φ*^2 r^(1 / p)`, where
`φ* = inf_y ρ(A y)` is read in the same way and `r = sup_y rank(A y)`. -/
theorem inducedObjectiveInf_bounds
    {Q : Type u} [Nonempty Q] (p : ℕ+) (F_p : SymmMat → ℝ) (A : Q → SymmMat)
    (h_lower : ∀ X, (1 / 2 : ℝ) * ρ(X) ^ (2 : ℕ) ≤ F_p X)
    (h_upper : ∀ X,
      F_p X ≤ (1 / 2 : ℝ) * ρ(X) ^ (2 : ℕ) *
        ((Matrix.rank (X : Matrix (Fin n) (Fin n) ℝ) : ℝ) ^ (1 / (p : ℝ)))) :
    (1 / 2 : ℝ) * (inducedRadiusInf A).toReal ^ (2 : ℕ) ≤
        (inducedObjectiveInf F_p A).toReal ∧
      (inducedObjectiveInf F_p A).toReal ≤
        (1 / 2 : ℝ) * (inducedRadiusInf A).toReal ^ (2 : ℕ) *
          ((inducedRankSup A : ℝ) ^ (1 / (p : ℝ))) :=
  sorry
