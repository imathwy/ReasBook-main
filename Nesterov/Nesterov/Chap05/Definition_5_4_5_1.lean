import Mathlib
import Nesterov.Chap01.Definition_1_3_3
import Nesterov.Chap03.Definition_3_56
import Nesterov.Chap05.Definition_5_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 5.4.5.1 lies in the minimum-volume enclosing-ellipsoid / constrained-optimization
domain.

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with a real-valued objective;
* `𝕊^n₊₊` and `strictPositiveSemidefiniteCone_posDef` in `Chap05/Definition_5_4_4_5`, the
  chapter owner and matrix-level bridge for positive-definite symmetric shapes;
* `minimumVolumeEnclosingEllipsoidBarrierDomain` in `Chap05/Definition_5_4_5_2`, the immediate
  downstream MVEE barrier domain already written on `𝕊^n₊₊ × Eₙ × ℝ`;
* `circumscribedEllipsoidBarrierDomain` in `Chap05/Definition_5_4_5_5`, the nearby ellipsoid
  barrier file that uses the same strict-cone owner level rather than a raw positive-definite
  subtype.

Best owner abstraction:
* source-facing data: the finite point family `a`, the enclosing-ellipsoid set `W(H, v)` with shape
  `H : 𝕊^n₊₊`, and the epigraph variable `τ`;
* core/canonical: `SetConstrainedMinimizationProblem` on the ambient decision-variable type
  `𝕊^n₊₊ × Eₙ × ℝ`;
* bridge/view: the canonical coercion from `H : 𝕊^n₊₊` to its ambient symmetric matrix in `𝕊^n`,
  followed by the matrix view in `Matrix (Fin n) (Fin n) ℝ`.

Primitive data:
* the feasible set of strict-cone shapes, centers, and epigraph variables satisfying the
  enclosing inequalities;
* the objective `τ`.

Derived API:
* the source-facing image-form notation `W(H, v)`;
* its bridge to the Chapter 3 ellipsoid owner `E(H, x̄)`;
* the membership and objective-expansion lemmas below.

Source/core/bridge triage:
* source-facing: the notation `W(H, v)` and the textbook feasible inequalities for
  `(H, v, τ) ∈ 𝕊^n₊₊ × Eₙ × ℝ`;
* core/canonical: `SetConstrainedMinimizationProblem`;
* bridge/view: the matrix-action coercion `H ↦ ((H : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ)`,
  followed by the Chapter 3 ellipsoid owner `E(H, x̄)`. -/

noncomputable section

open Matrix
open StrictPositiveSemidefiniteCone
open scoped EllipsoidNotation RealSymmetricMatrixSpace

variable {ι : Type*} {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/-- Definition 5.4.5.1: the source-facing image-form ellipsoid `W(H, v)` is the set of points
`x` satisfying the textbook constraint `‖H x - v‖ ≤ 1`. -/
def enclosingEllipsoid
    (H : 𝕊^n₊₊) (v : Eₙ) : Set Eₙ :=
  {x | ‖(toMatrix H).toEuclideanLin x - v‖ ≤ 1}

namespace EnclosingEllipsoidNotation

/-- The source-facing image-form ellipsoid `W(H, v)`. -/
scoped notation:max "W(" H ", " v ")" =>
  enclosingEllipsoid H v

end EnclosingEllipsoidNotation

open scoped EnclosingEllipsoidNotation

/-- The image-form ellipsoid `W(H, v)` is the Chapter 3 affine ellipsoid with shape
`(H⁻¹)^2` and center `H⁻¹ v`. -/
theorem enclosingEllipsoid_eq_affineEllipsoid
    (H : 𝕊^n₊₊) (v : Eₙ) :
    W(H, v) = E((toMatrix H)⁻¹ * (toMatrix H)⁻¹, ((toMatrix H)⁻¹).toEuclideanLin v) := by
  sorry

-- Proof sketch: rewrite `W(H, v)` through `enclosingEllipsoid_eq_affineEllipsoid`, expand
-- `mem_affineEllipsoid_iff`, and simplify the resulting quadratic form.
/-- Membership in `W(H, v)` is exactly the constraint `‖H x - v‖ ≤ 1`. -/
@[simp] theorem mem_enclosingEllipsoid_iff
    {H : 𝕊^n₊₊} {v x : Eₙ} :
    x ∈ W(H, v) ↔ ‖(toMatrix H).toEuclideanLin x - v‖ ≤ 1 :=
  Iff.rfl

/-- Definition 5.4.5.1: the minimum-volume enclosing ellipsoid problem for a finite family of
points `a i` minimizes the scalar upper bound `τ` over strict-cone shapes `H : 𝕊ⁿ₊₊`, offsets
`v`, and `τ`, subject to `logDetBarrier n H ≤ τ` and the enclosing constraints
`a_i ∈ W(H, v)` for every index `i`. The raw `-log det H ≤ τ` and `‖H a_i - v‖ ≤ 1` formulas are
companion bridge views. -/
def minimumVolumeEnclosingEllipsoidProblem
    (a : ι → Eₙ) :
    SetConstrainedMinimizationProblem
      (𝕊^n₊₊ × Eₙ × ℝ) where
  feasibleSet := {Hvτ | logDetBarrier n Hvτ.1 ≤ Hvτ.2.2 ∧
    ∀ i, a i ∈ W(Hvτ.1, Hvτ.2.1)}
  objective := Prod.snd ∘ Prod.snd

-- Proof sketch: unfold `minimumVolumeEnclosingEllipsoidProblem`; the feasible set is
-- definitionally the conjunction of the owner determinant barrier bound and the source-facing
-- enclosing-ellipsoid constraints.
/-- A triple `(H, v, τ)` is feasible for the minimum-volume enclosing ellipsoid problem exactly
when `logDetBarrier n H ≤ τ` and every point `a i` belongs to the enclosing ellipsoid
`W(H, v)`. -/
@[simp] theorem mem_minimumVolumeEnclosingEllipsoidProblem_feasibleSet_iff
    (a : ι → Eₙ)
    (H : 𝕊^n₊₊) (v : Eₙ) (τ : ℝ) :
    (H, v, τ) ∈ (minimumVolumeEnclosingEllipsoidProblem a).feasibleSet ↔
      logDetBarrier n H ≤ τ ∧
        ∀ i, a i ∈ W(H, v) :=
  Iff.rfl

-- Proof sketch: expand the owner determinant barrier with `logDetBarrier_apply` and rewrite the
-- source-facing ellipsoid constraints using `mem_enclosingEllipsoid_iff`.
/-- Expanding the owner feasible-set description rewrites MVEE feasibility back to the textbook
formula `-log det H ≤ τ` together with the norm constraints `‖H a_i - v‖ ≤ 1`. -/
theorem mem_minimumVolumeEnclosingEllipsoidProblem_feasibleSet_iff_formula
    (a : ι → Eₙ)
    (H : 𝕊^n₊₊) (v : Eₙ) (τ : ℝ) :
    (H, v, τ) ∈ (minimumVolumeEnclosingEllipsoidProblem a).feasibleSet ↔
      -Real.log (toMatrix H).det ≤ τ ∧
        ∀ i, ‖(toMatrix H).toEuclideanLin (a i) - v‖ ≤ 1 := by
  simp [mem_minimumVolumeEnclosingEllipsoidProblem_feasibleSet_iff, logDetBarrier_apply,
    mem_enclosingEllipsoid_iff]

-- Proof sketch: unfold `minimumVolumeEnclosingEllipsoidProblem`; the objective field is exactly
-- the third coordinate `τ`.
/-- Evaluating the objective of the minimum-volume enclosing ellipsoid problem returns the
auxiliary variable `τ`. -/
@[simp] theorem minimumVolumeEnclosingEllipsoidProblem_objective_apply
    (a : ι → Eₙ)
    (H : 𝕊^n₊₊) (v : Eₙ) (τ : ℝ) :
    (minimumVolumeEnclosingEllipsoidProblem a) (H, v, τ) = τ :=
  rfl

end
