import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_1 (from Chap01) -/
universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 1.1 is recall-only: Lean does not introduce a separate public `RealVectorSpace`
structure. The textbook notion is formalized by the owner pair `[AddCommGroup E] [Module ℝ E]`. -/

/- The additive data of a real vector space is the canonical typeclass `AddCommGroup E`. -/
#check AddCommGroup E

/- Scalar multiplication by real numbers, together with its compatibility with the additive
structure, is the canonical owner typeclass `Module ℝ E`. -/
#check Module ℝ E

end

/-! ### Lemma_1_1 (from Chap01) -/
noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The dual norm of a linear functional, realized as the operator norm of the associated
continuous linear functional. -/
def dualNorm (y : Module.Dual ℝ E) : ℝ :=
  ‖LinearMap.toContinuousLinearMap y‖

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: apply `ContinuousLinearMap.le_opNorm` to the continuous linear functional
-- `LinearMap.toContinuousLinearMap y`; the abbreviation `dualNorm y` is exactly this operator norm,
-- and because the codomain is `ℝ`, the norm of `y x` is `|y x|`.
/-- Lemma 1.1: for a linear functional `y ∈ E* = Module.Dual ℝ E` on a finite-dimensional real
normed space, the canonical dual pairing is bounded by the dual norm times the norm of the
vector. This is the chapter-facing dual-pairing inequality `|y x| ≤ ‖y‖_* ‖x‖` written using
`dualNorm`. -/
theorem abs_apply_le_dual_norm_mul_norm (y : Module.Dual ℝ E) (x : E) :
    |y x| ≤ dualNorm y * ‖x‖ := sorry

end

/-! ### Proposition_1_1 (from Chap01) -/
noncomputable section

open Matrix WithLp

section

variable {m n : ℕ}

/-- Proposition 1.1 (`source-facing`; `core/canonical` owner:
`ContinuousLinearMap.le_opNorm`; `bridge/view`: `Matrix.toLpLin`): for every real vector `x`, the
induced `(a,b)`-norm of a real matrix `A` bounds the `b`-norm of `A x` by
`‖A x‖_b ≤ ‖A‖_{a,b} ‖x‖_a`. In the project notation from Definition 1.34, this is the
source-facing `WithLp` coordinate form of the owner theorem for
`(A.toLpLin a b).toContinuousLinearMap`. -/
theorem norm_mulVec_le_opNorm_toLpLin_mul_norm
    (a b : ENNReal) [Fact (1 ≤ a)] [Fact (1 ≤ b)]
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    ‖toLp b (A *ᵥ x)‖ ≤ ‖(A.toLpLin a b).toContinuousLinearMap‖ * ‖toLp a x‖ := by
  simpa [toLpLin_toLp] using (A.toLpLin a b).toContinuousLinearMap.le_opNorm (toLp a x)

end
