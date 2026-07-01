import Mathlib
import Nesterov.Chap05.Definition_5_4_4_2
import Nesterov.Chap05.Definition_5_4_4_3
import Nesterov.Chap06.Definition_6_44
import Nesterov.Chap07.Algorithm_7_11
import Nesterov.Chap07.Definition_7_21

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Gradient
open Matrix
open RealSymmetricMatrixSpace
open scoped RealSymmetricMatrixSpace

noncomputable section

variable {m n : ℕ}

local notation "Eₘ" => EuclideanSpace ℝ (Fin m)
local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n

/- Proposition 7.27 lies in the repeated-squaring / symmetric-matrix trace-power domain.

Sampled owner-style declarations:
- Chapter 7 `repeatedSquaringX`, `repeatedSquaringY`, and their closed-form theorems in
  `Algorithm_7_11`, the canonical owner of the repeated-squaring orbit;
- Chapter 7 `linearMatrixCombination` and `linearMatrixCombination_apply` in `Definition_7_21`,
  the canonical ambient owner of the coefficient-sum matrix map `y ↦ ∑ᵢ yᵢ Aᵢ`;
- Chapter 5 `𝕊^n` and `RealSymmetricMatrixSpace.isSymm`, the chapter owner and coercion bridge
  for real symmetric matrices;
- Chapter 6 `squaredLpMatrixNormSmoothing`, the chapter owner for the half-scaled
  trace-power smoothing functional;
- Chapter 6 `RealSymmetricMatrixSpace.powerTrace`, written `π[k]`, the chapter owner for
  symmetric trace powers.

Best owner abstraction:
- source-facing: Proposition 7.27's repeated-squaring and gradient statements for the
  power-of-two specialization of the smoothing functional;
- core/canonical: `squaredLpMatrixNormSmoothing`, `π[k]` on `𝕊^n`, `repeatedSquaringX`,
  `repeatedSquaringY`, and `linearMatrixCombination`;
- bridge/view: the codomain restriction from the ambient Chapter 7 coefficient-sum map to
  `𝕊^n`, together with the power-of-two specialization of
  `squaredLpMatrixNormSmoothing_eq_half_rpow_powerTrace`.

Primitive data:
- `k : ℕ+`;
- a symmetric coefficient family `A : Fin m → SymmMat`;
- a point `y : Eₘ`.

Derived API:
- the thin bridge `symmetricLinearMatrixCombination A : Eₘ →ₗ[ℝ] SymmMat`;
- the positive smoothing order `2^(k-1)` whose Chapter 6 owner gives the `2^k` trace power;
- the proposition's specializations of the repeated-squaring closed forms to the ambient matrix
  underlying `A(y)`;
- the iterate-based rewriting and gradient formula for
  `squaredLpMatrixNormSmoothing (2^(k-1)) (A(y))`.

Source/core/bridge triage:
- source-facing: the Proposition 7.27 theorems below;
- core/canonical: `squaredLpMatrixNormSmoothing`, `π[k]`, `repeatedSquaringX`,
  `repeatedSquaringY`, and `linearMatrixCombination`;
- bridge/view: `symmetricLinearMatrixCombination` and the companion power-of-two trace formula.

This refinement moves the file from raw ambient matrices to the chapter's symmetric-matrix
surface. The only new public owner below is the thin codomain-restriction bridge from
`linearMatrixCombination` to `𝕊^n`; the smoothing objective is no longer rebuilt locally, and the
proposition is stated directly as the repeated-squaring and gradient bridge for the existing
Chapter 6 owner `squaredLpMatrixNormSmoothing`. The gradient theorem records the missing
nonzero-trace domain condition explicitly instead of relying on Lean's totalized division.
-/

private abbrev ambientLinearMatrixCombination
    (A : Fin m → SymmMat) : Eₘ →ₗ[ℝ] Mₙ :=
  linearMatrixCombination fun i ↦ (A i : Mₙ)

/-- The symmetric-matrix bridge `y ↦ A(y)` obtained by restricting the Chapter 7 ambient
coefficient-sum map to the canonical carrier `𝕊^n`. -/
abbrev symmetricLinearMatrixCombination
    (A : Fin m → SymmMat) : Eₘ →ₗ[ℝ] SymmMat :=
  LinearMap.codRestrict (𝕊^n) (ambientLinearMatrixCombination A) fun y ↦ by
    simpa [ambientLinearMatrixCombination, linearMatrixCombination_apply] using
      (show (((∑ i : Fin m, y i • A i : SymmMat) : Mₙ) ∈ 𝕊^n) from
        (∑ i : Fin m, y i • A i).2)

/-- Coercing `symmetricLinearMatrixCombination A y` to ambient matrices recovers the textbook
coefficient formula `A(y) = ∑ᵢ yᵢ Aᵢ`. -/
@[simp] theorem coe_symmetricLinearMatrixCombination_apply
    (A : Fin m → SymmMat) (y : Eₘ) :
    ((symmetricLinearMatrixCombination A y : SymmMat) : Mₙ) =
      ∑ i : Fin m, y i • (A i : Mₙ) :=
  rfl

/-- Evaluating `symmetricLinearMatrixCombination` gives the intrinsic symmetric sum
`A(y) = ∑ᵢ yᵢ Aᵢ` in `𝕊^n`. -/
@[simp] theorem symmetricLinearMatrixCombination_apply
    (A : Fin m → SymmMat) (y : Eₘ) :
    symmetricLinearMatrixCombination A y = ∑ i : Fin m, y i • A i := by
  apply Subtype.ext
  simpa using coe_symmetricLinearMatrixCombination_apply A y

/-- The positive smoothing order whose Chapter 6 owner specializes to the `2^k` trace power from
Proposition 7.27. -/
def powerOfTwoSmoothingOrder (k : ℕ+) : ℕ+ :=
  Nat.toPNat (2 ^ k.natPred) (pow_pos (by decide : 0 < 2) _)

private theorem two_mul_powerOfTwoSmoothingOrder (k : ℕ+) :
    2 * (powerOfTwoSmoothingOrder k : ℕ) = 2 ^ (k : ℕ) := by
  have hk : k.natPred + 1 = (k : ℕ) := by
    change Nat.succ k.natPred = (k : ℕ)
    exact congrArg PNat.val (PNat.succPNat_natPred k)
  change 2 * 2 ^ k.natPred = 2 ^ (k : ℕ)
  rw [← hk, Nat.pow_succ, Nat.mul_comm]

private theorem one_div_powerOfTwoSmoothingOrder (k : ℕ+) :
    1 / (powerOfTwoSmoothingOrder k : ℝ) = (2 : ℝ) / (2 ^ (k : ℕ) : ℝ) := by
  have hp : (powerOfTwoSmoothingOrder k : ℝ) ≠ 0 := by
    positivity
  have hk : (2 ^ (k : ℕ) : ℝ) = 2 * (powerOfTwoSmoothingOrder k : ℝ) := by
    exact_mod_cast (two_mul_powerOfTwoSmoothingOrder k).symm
  calc
    1 / (powerOfTwoSmoothingOrder k : ℝ) = (2 : ℝ) / (2 * (powerOfTwoSmoothingOrder k : ℝ)) := by
      field_simp [hp]
    _ = (2 : ℝ) / (2 ^ (k : ℕ) : ℝ) := by
      rw [hk]

/-- Writing Proposition 7.27's `f_{2^k}(y)` through the Chapter 6 owner expresses it as the
power-of-two specialization of `squaredLpMatrixNormSmoothing`. -/
theorem squaredLpMatrixNormSmoothing_powerOfTwo_eq_half_rpow_trace
    (k : ℕ+) (A : Fin m → SymmMat) (y : Eₘ) :
    squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
      (symmetricLinearMatrixCombination A y) =
      (1 / 2 : ℝ) *
        Real.rpow
          (Matrix.trace ((symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ (k : ℕ))))
          ((2 : ℝ) / (2 ^ (k : ℕ) : ℝ)) := by
  rw [squaredLpMatrixNormSmoothing_eq_half_rpow_powerTrace, powerTrace_def,
    two_mul_powerOfTwoSmoothingOrder, one_div_powerOfTwoSmoothingOrder]

-- Proof sketch: specialize the canonical repeated-squaring first-component formula to the matrix
-- `A(y) = symmetricLinearMatrixCombination A y`.
/-- Proposition 7.27 (1): the repeated-squaring first component `X_k` satisfies
`X_k = A(y)^(2^k)`. -/
theorem repeatedSquaringX_symmetricLinearMatrixCombination_eq_pow
    (A : Fin m → SymmMat) (y : Eₘ) (k : ℕ) :
    repeatedSquaringX (symmetricLinearMatrixCombination A y : Mₙ) k =
      (symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ k) :=
  repeatedSquaringX_eq_pow _ _

-- Proof sketch: specialize the canonical repeated-squaring second-component formula to the matrix
-- `A(y) = symmetricLinearMatrixCombination A y`.
/-- Proposition 7.27 (2): the repeated-squaring second component `Y_k` satisfies
`Y_k = A(y)^(2^k - 1)`. -/
theorem repeatedSquaringY_symmetricLinearMatrixCombination_eq_pow_pred
    (A : Fin m → SymmMat) (y : Eₘ) (k : ℕ) :
    repeatedSquaringY (symmetricLinearMatrixCombination A y : Mₙ) k =
      (symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ k - 1) :=
  repeatedSquaringY_eq_pow_pred _ _

-- Proof sketch: substitute the identity from part (1) into the definition of
-- `squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)`.
/-- Proposition 7.27 (3): for the power-of-two specialization of the Chapter 6 smoothing owner,
`f_{2^k}(y) = (1 / 2) * Trace(X_k)^(2 / 2^k)`. -/
theorem squaredLpMatrixNormSmoothing_powerOfTwo_eq_iterateX
    (k : ℕ+) (A : Fin m → SymmMat) (y : Eₘ) :
    squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
      (symmetricLinearMatrixCombination A y) =
      (1 / 2 : ℝ) *
        Real.rpow
          (Matrix.trace (repeatedSquaringX (symmetricLinearMatrixCombination A y : Mₙ) (k : ℕ)))
          ((2 : ℝ) / (2 ^ (k : ℕ) : ℝ)) := by
  rw [squaredLpMatrixNormSmoothing_powerOfTwo_eq_half_rpow_trace,
    repeatedSquaringX_symmetricLinearMatrixCombination_eq_pow]

-- Proof sketch: differentiate the affine matrix map `y ↦ A(y)` entrywise, use the trace-power
-- derivative of `M ↦ Trace(M^(2^k))` on symmetric matrices, note that the even trace power is
-- automatically nonnegative, and finish with the chain rule for the outer power
-- `t ↦ (1 / 2) * t^(2 / 2^k)`.
/- Proposition 7.27 (4): if `Trace(X_k) ≠ 0`, then the power-of-two specialization of
`squaredLpMatrixNormSmoothing` has gradient
`∇ f_{2^k}(y)^(i) = (2 f_{2^k}(y) / Trace(X_k)) * Trace(Y_k Aᵢ)`. -/
theorem squaredLpMatrixNormSmoothing_powerOfTwo_hasGradientAt
    (k : ℕ+) (A : Fin m → SymmMat) (y : Eₘ)
    (htrace :
      Matrix.trace (repeatedSquaringX (symmetricLinearMatrixCombination A y : Mₙ) (k : ℕ)) ≠ 0) :
    HasGradientAt
      (fun y' ↦
        squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
          (symmetricLinearMatrixCombination A y'))
      ((EuclideanSpace.equiv (Fin m) ℝ).symm <| fun i : Fin m ↦
        ((2 : ℝ) *
            squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
              (symmetricLinearMatrixCombination A y) /
            Matrix.trace
              (repeatedSquaringX (symmetricLinearMatrixCombination A y : Mₙ) (k : ℕ))) *
          Matrix.trace
            (repeatedSquaringY (symmetricLinearMatrixCombination A y : Mₙ) (k : ℕ) *
              (A i : Mₙ)))
      y := by
  sorry

end
