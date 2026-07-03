import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_27 (from Chap07) -/
noncomputable section

open scoped EllipsoidNotation

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 7.27 lies in the Chapter 7 ellipsoid-rounding domain.

Primary domain:
- ellipsoidal roundings of convex sets in `ℝⁿ`.

Sampled owner-style declarations:
- `matrixEllipsoid` in `Chap07/Definition_7_26`, the source-facing owner of radius-parametrized
  ellipsoids;
- `matrixEllipsoid_one_eq_affineEllipsoid` in `Chap07/Definition_7_26`, the canonical radius-`1`
  bridge;
- `affineEllipsoid` in `Chap03/Lemma_3_2_7`, the chapter owner of the unit ellipsoid;
- `IsEllipsoidalRounding` in `Chap07/Definition_7_29`, which reuses the same `W[r](G)` owner in
  the centered case.

Best owner abstraction:
- source-facing: the `β`-rounding predicate itself;
- core/canonical owners: `matrixEllipsoid` for variable radius and `affineEllipsoid` for the unit
  ellipsoid;
- bridge/view: the radius-`1` identification from `Definition_7_26`.

Primitive data:
- a set `C : Set E`;
- a rounding parameter `β : ℝ`;
- a shape matrix `G : Mat`;
- a center `v : E`.

Derived API:
- the inner unit-ellipsoid inclusion, canonically phrased with `affineEllipsoid`;
- the outer inclusion in `W[β](v, G)`;
- the derived radius-`1` `matrixEllipsoid` inclusion used for the source wording.

Source/core/bridge triage:
- source-facing: `IsBetaRounding`;
- core/canonical: `matrixEllipsoid`, `affineEllipsoid`;
- bridge/view: `IsBetaRounding.unit_matrixEllipsoid_subset`.

This item defines only the rounding predicate, not a second ellipsoid owner. The previous local
`matrixEllipsoid` duplicate is therefore deleted in favor of the Chapter 7 owner from
`Definition_7_26`, and the primitive inner field is refined to the canonical unit-ellipsoid owner
`affineEllipsoid`. -/

/-- Definition 7.27: the ellipsoid `W₁(v,G)` is a `β`-rounding of `C` when the unit ellipsoid
`W₁(v,G)` is contained in `C` and `C` is contained in the dilated ellipsoid `W_β(v,G)`. -/
structure IsBetaRounding
    (C : Set E) (β : ℝ) (G : Mat) (v : E) : Prop where
  /-- The unit ellipsoid `W₁(v,G) = E(G, v)` lies inside `C`. -/
  unit_ellipsoid_subset : E(G, v) ⊆ C
  /-- The set `C` lies inside the outer ellipsoid `W_β(v,G)`. -/
  subset_beta_ellipsoid : C ⊆ W[β](v, G)

namespace IsBetaRounding

/-- The source-facing unit-radius inclusion `W₁(v,G) ⊆ C` is the radius-`1` view of the canonical
inner field `E(G, v) ⊆ C`. -/
theorem unit_matrixEllipsoid_subset
    {C : Set E} {β : ℝ} {G : Mat} {v : E}
    (h : IsBetaRounding C β G v) :
    W[1](v, G) ⊆ C := by
  simpa [matrixEllipsoid_one_eq_affineEllipsoid] using h.unit_ellipsoid_subset

end IsBetaRounding

/-- A `β`-rounding canonically supplies the source-facing inner and outer ellipsoid containments
from the definition. -/
instance {C : Set E} {β : ℝ} {G : Mat} {v : E}
    (h : IsBetaRounding C β G v) :
    Fact (W[1](v, G) ⊆ C ∧ C ⊆ W[β](v, G)) where
  out := ⟨h.unit_matrixEllipsoid_subset, h.subset_beta_ellipsoid⟩

/-! ### Proposition_7_27 (from Chap07) -/
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
