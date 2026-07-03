import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_6 (from Chap02) -/
universe u

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

/-- Definition 2.6: an extended-real-valued function is convex when its real epigraph
is a convex subset of `E × ℝ`. -/
def is_convex_function (f : E → EReal) : Prop :=
  Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)}

/-- The predicate `is_convex_function` is equivalent to convexity of the real epigraph
`{(x, r) | f x ≤ r}`. -/
@[simp]
lemma is_convex_function_iff_convex_real_epigraph (f : E → EReal) :
    is_convex_function f ↔ Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} :=
  Iff.rfl

end

/-! ### Example_2_6 (from Chap02) -/
universe u

noncomputable section

section

open Metric

variable {E : Type u} [NormedAddCommGroup E]

-- Proof sketch: unfold `infimal_convolution`, expand `extendedIndicator C`, and use
-- `infDist_eq_iInf` to identify the infimum over `C` of the distances `dist x y = ‖x - y‖`
-- with the pointwise infimum over all `y : E` of `δ_C y + ‖x - y‖`.
/-- Example 2.6 (1): for a nonempty set `C`, the distance to `C` is the infimal convolution of
the extended indicator `δ_C` with the norm function `h₁(z) = ‖z‖`. -/
theorem infimal_convolution_extendedIndicator_norm_eq_infDist
    (C : Set E) (hC : C.Nonempty) (x : E) :
    (extendedIndicator C □ fun z ↦ (‖z‖ : EReal)) x =
      (infDist x C : EReal) := sorry

end

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Proof sketch: rewrite `infDist · C` using
-- `infimal_convolution_extendedIndicator_norm_eq_infDist`, note that the indicator of a convex set
-- is convex and that `z ↦ ‖z‖` is convex by `convexOn_univ_norm`, then apply the convexity
-- owner theorem `infimal_convolution_is_convex` and convert back to a real-valued `ConvexOn`
-- statement on the full effective domain.
/-- Example 2.6 (2): if `C` is convex, then its distance function `x ↦ infDist x C` is
convex on the whole space. -/
theorem convexOn_infDist (C : Set E) (hC : Convex ℝ C) :
    ConvexOn ℝ Set.univ (fun x ↦ infDist x C) := sorry

end

end

/-! ### Lemma_2_6 (from Chap02) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: if `A = B`, then the specialized chapter owner support functions agree by
-- substitution. Conversely, if the support functions agree after precomposition with
-- `InnerProductSpace.toDualMap`, then completeness identifies every continuous linear functional
-- with an inner-product functional via `InnerProductSpace.toDual`. If one set is empty, the common
-- support function is constantly `⊥`, so both sets are empty. Otherwise, if `x ∈ A \ B`, apply
-- strict separation to the closed convex set `B` and the point `x`; transport the separating
-- functional across Fréchet-Riesz to get a vector representation, yielding a contradiction to
-- support-function equality. Symmetry gives the reverse inclusion.
/-- Lemma 2.6: two closed convex sets in a real inner product space are equal if and only if their
support functions agree after specializing the chapter owner support function along
`InnerProductSpace.toDualMap`; the canonical Fréchet-Riesz identification of the continuous dual
with the inner product space is used through the ambient completeness hypothesis. -/
theorem eq_iff_support_function_eq_of_closed_convex
    (A B : Set E) (hA_closed : IsClosed A) (hA_convex : Convex ℝ A)
    (hB_closed : IsClosed B) (hB_convex : Convex ℝ B) :
    A = B ↔
      (fun x ↦ support_function A (InnerProductSpace.toDualMap ℝ E x)) =
        fun x ↦ support_function B (InnerProductSpace.toDualMap ℝ E x) := sorry

end

/-! ### Theorem_2_6 (from Chap02) -/
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
