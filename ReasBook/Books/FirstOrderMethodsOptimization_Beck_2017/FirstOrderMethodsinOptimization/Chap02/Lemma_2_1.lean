import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The primal-space support function of `C`, obtained by evaluating the chapter owner
`support_function` along the Riesz map `InnerProductSpace.toDualMap`. This is the textbook support
function `σ_C` in Euclidean coordinates. -/
noncomputable abbrev support_function_primal (C : Set E) : E → EReal :=
  fun x ↦ support_function C (InnerProductSpace.toDualMap ℝ E x)

/-- Textbook notation for the primal-space support function. -/
notation "σ[" C "]" => support_function_primal C

-- Proof sketch: unfold `support_function_primal`; this is exactly the specialization of
-- `support_function` along `InnerProductSpace.toDualMap`.
/-- Evaluating `σ[C]` at `x` is the same as evaluating the chapter owner `support_function C` at
the dual vector corresponding to `x`. -/
@[simp] theorem support_function_primal_apply (C : Set E) (x : E) :
    σ[C] x = support_function C (InnerProductSpace.toDualMap ℝ E x) :=
  rfl

-- Proof sketch: specialize the chapter owner `support_function` along the canonical map
-- `InnerProductSpace.toDualMap ℝ E`; the resulting evaluation is exactly the supremum of the
-- pairings `c ↦ ⟪x, c⟫` over `C`.
/-- The inner-product-space support-function formula is the specialization of the chapter owner
`support_function` along `InnerProductSpace.toDualMap`, written on the source-facing owner
`σ[C]`. -/
theorem support_function_eq_sSup (C : Set E) (x : E) :
    σ[C] x = sSup ((fun c : E ↦ (inner ℝ x c : EReal)) '' C) := by
  simpa using support_function_apply C (InnerProductSpace.toDualMap ℝ E x)

-- Proof sketch: the specialized support function is the chapter owner support function on the dual
-- space, precomposed with the continuous linear map `InnerProductSpace.toDualMap`; closedness and
-- convexity are preserved under this specialization.
/-- Lemma 2.1: the support function of a subset of a real inner product space, expressed via the
chapter owner support function on the dual space and written on the source-facing owner `σ[C]`, is
closed, i.e. lower semicontinuous, and convex in the chapter owner sense `is_convex_function`. -/
theorem support_function_closed_and_convex (C : Set E) :
    LowerSemicontinuous (σ[C]) ∧ is_convex_function (σ[C]) := sorry

end
