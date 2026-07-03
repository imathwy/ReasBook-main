import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_7 (from Chap02) -/
universe u

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E] {f : E → EReal}

/- Definition 2.7 reuses the chapter owner `is_convex_function` from Definition 2.6 for convexity
of an extended-real-valued function. -/
recall is_convex_function

/-- Definition 2.7: convexity is equivalent to the two-point Jensen inequality along every segment
joining two points of the effective domain, with weight in `[0, 1]`. -/
theorem is_convex_function_iff_segment_ineq :
    is_convex_function f ↔
      ∀ x ∈ effective_domain f, ∀ y ∈ effective_domain f, ∀ {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        f (t • x + (1 - t) • y) ≤ (t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y := sorry

-- Proof sketch: identify the real epigraph from Definition 2.6 with the epigraph of the finite
-- restriction `x ↦ (f x).toReal` on `effective_domain f`; the local hypothesis `h_ne_bot` rules
-- out `-∞` on the domain, and membership in `effective_domain f` rules out `∞`, so
-- `convexOn_iff_convex_epigraph` applies to a genuine real-valued restriction.
/-- Companion bridge: if an extended-real-valued function never takes the value `-∞` on its
effective domain, then the source Jensen formulation is equivalent to convexity of the finite-valued
restriction `x ↦ (f x).toReal` on that domain. -/
theorem is_convex_function_iff_convexOn_toReal
    (h_ne_bot : ∀ x ∈ effective_domain f, f x ≠ ⊥) :
    is_convex_function f ↔ ConvexOn ℝ (effective_domain f) (fun x ↦ (f x).toReal) := sorry

/-- If a convex extended-real-valued function never takes the value `-∞` on its effective domain,
then its finite-valued restriction is convex on that domain. -/
theorem convexOn_toReal_of_is_convex_function (hf : is_convex_function f)
    (h_ne_bot : ∀ x ∈ effective_domain f, f x ≠ ⊥) :
    ConvexOn ℝ (effective_domain f) (fun x ↦ (f x).toReal) :=
  (is_convex_function_iff_convexOn_toReal h_ne_bot).1 hf

-- Proof sketch: the convexity of the effective domain is the set component of
-- the real epigraph under the first-coordinate projection.
/-- If an extended-real-valued function is convex, then its effective domain is a convex set. -/
theorem effective_domain_convex_of_is_convex_function (hf : is_convex_function f) :
    Convex ℝ (effective_domain f) := sorry

-- Proof sketch: apply `effective_domain_convex_of_is_convex_function` to `hx`, `hy`, and the
-- bounds encoded by `ht`.
/-- If an extended-real-valued function is convex and finite at two points of its effective
domain, then it is also finite at every convex combination of those points with weight in `[0,
1]`. -/
theorem combo_mem_effective_domain_of_is_convex_function (hf : is_convex_function f)
    {x y : E} (hx : x ∈ effective_domain f)
    (hy : y ∈ effective_domain f) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t • x + (1 - t) • y ∈ effective_domain f := by
  exact
    effective_domain_convex_of_is_convex_function hf hx hy ht.1
      (sub_nonneg.2 ht.2) (by ring)

end

/-! ### Example_2_7 (from Chap02) -/
universe u

open Matrix
open PointedCone

noncomputable section

section

variable {m n : ℕ}

/-- The cone cut out by the coordinatewise inequalities `A *ᵥ x ≤ 0`, realized as the preimage of
the positive cone under the matrix linear map. -/
def matrix_nonpositive_cone (A : Matrix (Fin m) (Fin n) ℝ) : PointedCone ℝ (Fin n → ℝ) :=
  (positive ℝ (Fin m → ℝ)).comap (-A).mulVecLin

/-- The transpose image of the nonnegative orthant in `ℝⁿ`, realized as the image of the positive
cone under the transpose matrix linear map. -/
def transpose_nonnegative_cone (A : Matrix (Fin m) (Fin n) ℝ) : PointedCone ℝ (Fin n → ℝ) :=
  (positive ℝ (Fin m → ℝ)).map Aᵀ.mulVecLin

/-- The Euclidean-dual realization of `transpose_nonnegative_cone A`, transported along
`dotProductEquiv ℝ (Fin n)`. -/
def transpose_nonnegative_dual_cone (A : Matrix (Fin m) (Fin n) ℝ) :
    PointedCone ℝ (Module.Dual ℝ (Fin n → ℝ)) :=
  (transpose_nonnegative_cone A).map (dotProductEquiv ℝ (Fin n))

@[simp]
theorem mem_matrix_nonpositive_cone (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ∈ matrix_nonpositive_cone A ↔ A *ᵥ x ≤ (0 : Fin m → ℝ) := by
  simp [matrix_nonpositive_cone]

@[simp]
theorem mem_transpose_nonnegative_cone (A : Matrix (Fin m) (Fin n) ℝ) (y : Fin n → ℝ) :
    y ∈ transpose_nonnegative_cone A ↔
      ∃ z ∈ Set.Ici (0 : Fin m → ℝ), Aᵀ *ᵥ z = y := by
  rw [transpose_nonnegative_cone, mem_map]
  constructor
  · rintro ⟨z, hz, hzy⟩
    refine ⟨z, ?_, ?_⟩
    · simpa using hz
    have hzy' : z ᵥ* A = y := by
      simpa [Matrix.mulVecLin_apply] using hzy
    exact (Matrix.mulVec_transpose A z).trans hzy'
  · rintro ⟨z, hz, hzy⟩
    refine ⟨z, ?_, ?_⟩
    · simpa using hz
    have hzy' : z ᵥ* A = y := (Matrix.mulVec_transpose A z).symm.trans hzy
    simpa [Matrix.mulVecLin_apply] using hzy'

@[simp]
theorem mem_transpose_nonnegative_dual_cone
    (A : Matrix (Fin m) (Fin n) ℝ) (y : Module.Dual ℝ (Fin n → ℝ)) :
    y ∈ transpose_nonnegative_dual_cone A ↔
      ∃ z ∈ Set.Ici (0 : Fin m → ℝ), dotProductEquiv ℝ (Fin n) (Aᵀ *ᵥ z) = y := by
  rw [transpose_nonnegative_dual_cone, mem_map]
  constructor
  · rintro ⟨v, hv, hy⟩
    rcases (mem_transpose_nonnegative_cone A v).mp hv with ⟨z, hz, rfl⟩
    exact ⟨z, hz, hy⟩
  · rintro ⟨z, hz, hy⟩
    exact ⟨Aᵀ *ᵥ z, (mem_transpose_nonnegative_cone A _).2 ⟨z, hz, rfl⟩, hy⟩

-- Proof sketch: rewrite membership in
-- `polar_cone (matrix_nonpositive_cone A : Set (Fin n → ℝ))` as the implication
-- `A *ᵥ x ≤ 0 → dotProduct y x ≤ 0` for every `x`; then use the bridge
-- `farkas_lemma_second_formulation_iff_mem_positive_map` to identify the representing vector with
-- the owner-side image of the positive cone under `Aᵀ.mulVecLin`, and finally transport along
-- `dotProductEquiv ℝ (Fin n)`.
/-- The polar cone of the matrix inequality set consists exactly of Euclidean-dual vectors of the
form `Aᵀ *ᵥ λ` with `λ ≥ 0`. -/
theorem polar_cone_matrix_nonpositive_cone_eq_transpose_nonnegative_dual_cone
    (A : Matrix (Fin m) (Fin n) ℝ) :
    polar_cone (matrix_nonpositive_cone A : Set (Fin n → ℝ)) =
      (transpose_nonnegative_dual_cone A : Set (Module.Dual ℝ (Fin n → ℝ))) := sorry

-- Proof sketch: combine the cone-case identity `σ_K = δ_{Kᵒ}` with the explicit description of
-- `polar_cone (matrix_nonpositive_cone A : Set (Fin n → ℝ))` from
-- `polar_cone_matrix_nonpositive_cone_eq_transpose_nonnegative_dual_cone`.
/-- Example 2.7: for `S = {x : ℝ^n | A *ᵥ x ≤ 0}`, the support function `σ_S` is the indicator
function of the Euclidean-dual image `{(Aᵀ *ᵥ λ) | λ ∈ ℝ^m_+}`. -/
theorem support_function_matrix_nonpositive_cone_eq_extendedIndicator_transpose_nonnegative_dual_cone
    (A : Matrix (Fin m) (Fin n) ℝ) :
    support_function (matrix_nonpositive_cone A : Set (Fin n → ℝ)) =
      extendedIndicator (transpose_nonnegative_dual_cone A : Set (Module.Dual ℝ (Fin n → ℝ))) :=
    sorry

end

/-! ### Lemma_2_7 (from Chap02) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Proof sketch: one inequality is immediate from `A ⊆ closure A`. For the reverse inequality,
-- evaluate the chapter owner `support_function` only along the canonical continuous-dual map
-- `InnerProductSpace.toDualMap ℝ E`, whose values are continuous linear functionals, and use that
-- each such functional has the same supremum on `A` and on `closure A`.
/-- Lemma 2.7 (1): after specializing the chapter owner `support_function` along
`InnerProductSpace.toDualMap`, replacing a set by its topological closure does not change the
support function. -/
lemma support_function_eq_support_function_closure (A : Set E) :
    (fun x ↦ support_function A (InnerProductSpace.toDualMap ℝ E x)) =
      fun x ↦ support_function (closure A) (InnerProductSpace.toDualMap ℝ E x) := sorry

end

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

-- Proof sketch: one inequality is immediate from `A ⊆ convexHull ℝ A`. For the reverse
-- inequality, write a point of `convexHull ℝ A` as a convex combination of points of `A`, use the
-- linearity of the dual functional, and bound the resulting convex combination by the supremum
-- over `A`.
/-- Lemma 2.7 (2): the chapter owner `support_function` is unchanged when a set is replaced by its
convex hull. Any inner-product-space formula is obtained by specializing this owner-level equality
along `InnerProductSpace.toDualMap`. -/
lemma support_function_eq_support_function_convexHull (A : Set E) :
    support_function A = support_function (convexHull ℝ A) := sorry

end

/-! ### Theorem_2_7 (from Chap02) -/
universe u v

section

variable {E : Type u} {V : Type v}
variable [AddCommMonoid E] [Module ℝ E]
variable [AddCommMonoid V] [Module ℝ V]

-- Proof sketch: for each `x`, the value `⨅ y, f (x, y)` is the fiberwise infimum of the convex
-- function `f`. To prove convexity, compare the epigraph of this partial infimum with the image of
-- the epigraph of `f`, then apply convexity of `f` on pairs `(x₁, y₁)` and `(x₂, y₂)`. In the
-- chapter owner formulation `is_convex_function : (E → EReal) → Prop`, the textbook fiberwise
-- finiteness side condition is redundant because the target function may legitimately take the value
-- `⊤`.
/-- Theorem 2.7: convexity is preserved under partial minimization. For the chapter owner notion
`is_convex_function`, if `f : E × V → EReal` is convex, then the fiberwise infimum
`x ↦ ⨅ y : V, f (x, y)` is convex. -/
theorem partial_infimum_is_convex_function
    {f : E × V → EReal} (hf : is_convex_function f) :
    is_convex_function (fun x ↦ ⨅ y : V, f (x, y)) := sorry

end
