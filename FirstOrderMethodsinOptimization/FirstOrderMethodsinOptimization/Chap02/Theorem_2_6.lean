import FirstOrderMethodsinOptimization.Chap02.Definition_2_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u v

section

variable {E : Type u} {V : Type v}
variable [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup V] [Module ℝ V]

-- Proof sketch: the real epigraph of the pullback function is the affine preimage of the real
-- epigraph of `f`, and affine preimages preserve convexity.
/-- Theorem 2.6 (1): precomposition with an affine map preserves convexity of an
extended-real-valued function. -/
theorem is_convex_function_precompose_affineMap {f : V → EReal}
    (hf : is_convex_function f) (g : E →ᵃ[ℝ] V) :
    is_convex_function (f ∘ g) := sorry

/-- Source-facing specialization of Theorem 2.6 (1) to affine maps written as `x ↦ A x + b`. -/
theorem is_convex_function_precompose_linearMap_add {f : V → EReal}
    (hf : is_convex_function f) (A : E →ₗ[ℝ] V) (b : V) :
    is_convex_function (fun x ↦ f (A x + b)) := by
  simpa using
    is_convex_function_precompose_affineMap hf (A.toAffineMap + AffineMap.const ℝ E b)

end

section

variable {E : Type u}
variable [AddCommMonoid E] [Module ℝ E]

-- Proof sketch: combine the epigraph inequalities for each `f i` using the nonnegativity of the
-- coefficients; equivalently, build the result by iterating the two basic closure operations of
-- nonnegative scalar multiplication and addition.
/-- Theorem 2.6 (2): a finite nonnegative weighted sum of convex extended-real-valued functions is
convex. -/
theorem is_convex_function_finset_nonneg_weighted_sum {m : ℕ} {f : Fin m → E → EReal}
    (hf : ∀ i : Fin m, is_convex_function (f i)) (α : Fin m → NNReal) :
    is_convex_function (fun x ↦ ∑ i : Fin m, (((α i : ℝ) : EReal) * f i x)) := sorry

-- Proof sketch: the epigraph of the pointwise supremum is the intersection of the epigraphs of the
-- family members, and intersections of convex sets remain convex.
/-- Theorem 2.6 (3): the pointwise supremum, written in the text as a pointwise maximum over the
index set, of convex extended-real-valued functions is convex. -/
theorem is_convex_function_iSup {ι : Type v} {f : ι → E → EReal}
    (hf : ∀ i : ι, is_convex_function (f i)) :
    is_convex_function (fun x ↦ ⨆ i : ι, f i x) := sorry

end
