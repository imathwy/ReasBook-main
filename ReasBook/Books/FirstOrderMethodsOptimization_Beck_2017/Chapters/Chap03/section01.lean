

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_1 (from Chap03) -/
universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 3.1 is the `source-facing` primitive predicate for Chapter 3 subdifferential
theory. The owner set-valued abstraction appears next as `subdifferential`; any finite-valued or
topologized forms should remain derived bridge/view API rather than parallel primitive data. -/

/-- Definition 3.1: a vector `g ∈ E* = Module.Dual ℝ E` is a subgradient of
`f : E → EReal` at `x` when `x` lies in the effective domain of `f` and the
subgradient inequality `f y ≥ f x + g (y - x)` holds for every `y`. -/
def is_subgradient_at (f : E → EReal) (x : E) (g : Module.Dual ℝ E) : Prop :=
  x ∈ effective_domain f ∧ ∀ y : E, f y ≥ f x + (g (y - x) : EReal)

-- Proof sketch: one implication is immediate by restriction. For the converse, if `y` is outside
-- the effective domain then `¬ f y < ⊤`, hence `⊤ ≤ f y`; together with `f y ≤ ⊤` this gives
-- `f y = ⊤`, so the inequality is automatic there.
/-- The subgradient inequality may be checked only on the effective domain, since outside that set
`f y = ⊤` and the inequality is automatic. -/
theorem is_subgradient_at_iff_forall_mem_effective_domain
    (f : E → EReal) (x : E) (g : Module.Dual ℝ E) :
    is_subgradient_at f x g ↔
      x ∈ effective_domain f ∧
        ∀ y ∈ effective_domain f, f y ≥ f x + (g (y - x) : EReal) := by
  constructor
  · rintro ⟨hx, hg⟩
    exact ⟨hx, fun y hy ↦ hg y⟩
  · rintro ⟨hx, hg⟩
    refine ⟨hx, fun y ↦ ?_⟩
    by_cases hy : y ∈ effective_domain f
    · exact hg y hy
    · have hy' : ¬ f y < ⊤ := by
        simpa [effective_domain] using hy
      have hfy_top : f y = ⊤ := le_antisymm le_top (not_lt.mp hy')
      simp [hfy_top]

/-- For a real-valued function, every point lies in the effective domain and the chapter
subgradient predicate reduces to the usual affine lower-support inequality. -/
theorem is_subgradient_at_coe_iff (f : E → ℝ) (x : E) (g : Module.Dual ℝ E) :
    is_subgradient_at (fun y ↦ (f y : EReal)) x g ↔ ∀ y : E, f y ≥ f x + g (y - x) := by
  constructor
  · intro hg y
    have h₀ : (f x : EReal) + (g (y - x) : EReal) ≤ (f y : EReal) := by
      simpa only [ge_iff_le] using hg.2 y
    have h : (((f x + g (y - x) : ℝ) : EReal) ≤ (f y : EReal)) := by
      simpa only [EReal.coe_add] using h₀
    exact EReal.coe_le_coe_iff.mp h
  · intro hg
    refine ⟨by simp [effective_domain], fun y ↦ ?_⟩
    have h₀ : f x + g (y - x) ≤ f y := by
      simpa only [ge_iff_le] using hg y
    have h : (((f x + g (y - x) : ℝ) : EReal) ≤ (f y : EReal)) :=
      EReal.coe_le_coe h₀
    simpa only [ge_iff_le, EReal.coe_add] using h

end

/-! ### Lemma_3_1 (from Chap03) -/
universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {f : E → EReal}

/- Lemma 3.1 is a `bridge/view` item in the chapter convex-analysis API: the owner theorem is
`is_convex_function_of_subdifferentiable_on_convex_effective_domain`, whose owner hypothesis is the
inclusion `effective_domain f ⊆ subdifferential_domain f`. This file keeps the source wording
"there exists a subgradient" and rewrites it through the owner set `subdifferential f x`,
equivalently membership in the owner domain `subdifferential_domain f`. -/
recall effective_domain
recall is_convex_function
recall subdifferential
recall subdifferential_domain
recall mem_subdifferential_domain
recall is_convex_function_of_subdifferentiable_on_convex_effective_domain

-- Proof sketch: to prove convexity, fix `x, y ∈ effective_domain f` and `t ∈ [0, 1]`, and set
-- `z = t • x + (1 - t) • y`. The convexity hypothesis on `effective_domain f` gives
-- `z ∈ effective_domain f`, so `hsubgrad` yields some `g ∈ subdifferential f z`, hence
-- `z ∈ subdifferential_domain f`. Applying the resulting subgradient inequality first with `y` and
-- then with `x`, and combining the two inequalities with weights `t` and `1 - t`, gives the
-- Jensen inequality along the segment from `x` to `y`, hence `f` is convex.
/-- Lemma 3.1: if an extended-real-valued function has convex effective domain and admits a
subgradient at every point of its effective domain, then the function is convex. -/
lemma is_convex_function_of_subgradient_exists_on_effective_domain
    (hdom : Convex ℝ (effective_domain f))
    (hsubgrad : ∀ x ∈ effective_domain f, ∃ g : Module.Dual ℝ E, g ∈ subdifferential f x) :
    is_convex_function f :=
  is_convex_function_of_subdifferentiable_on_convex_effective_domain hdom
    (fun x hx ↦ by
      rw [mem_subdifferential_domain]
      simpa [Set.nonempty_def] using hsubgrad x hx)

end

/-! ### Proposition_3_1 (from Chap03) -/
universe u

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Proposition 3.1 is `source-facing` for the norm example in the chapter subdifferential theory.
Its owner stack already lives upstream: `is_subgradient_at` is the primitive predicate,
`subdifferential` is the source-facing owner set, and `strongDualSubdifferential` is the
continuous-dual `bridge/view`. The proposition should therefore stay as a direct identification of
that existing owner object, not introduce a parallel wrapper API. -/

-- Proof sketch: unfold `strongDualSubdifferential`, simplify `‖0‖ = 0`, and identify the
-- resulting inequality
-- `(‖y‖ : EReal) ≥ g y` for all `y` with the dual-unit-ball condition `‖g‖ ≤ 1`, equivalently
-- `g ∈ closedBall (0 : StrongDual ℝ E) 1`.
/-- Proposition 3.1: the subdifferential of the norm at the origin is the closed unit ball of the
dual norm on `E*`. -/
theorem subdifferentialAt_norm_zero_eq_dual_closed_unit_ball :
    strongDualSubdifferential (fun x : E ↦ (‖x‖ : EReal)) (0 : E) =
      closedBall (0 : StrongDual ℝ E) 1 := sorry

end

/-! ### Theorem_3_1 (from Chap03) -/
universe u

section

open Bornology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 3.1 is a `bridge/view` item in the chapter subdifferential API. The owner declaration
is `subdifferential : Set (Module.Dual ℝ E)` from Definition 3.2, while the closedness statement
in this theorem lives on the topologized continuous-dual view. Owner-level convexity already lives
in `convex_subdifferential`, so the only primitive
data here is the canonical preimage of `subdifferential` along
`StrongDual ℝ E → Module.Dual ℝ E`; membership lemmas are derived API. -/
recall subdifferential
recall convex_subdifferential

/-- The continuous-dual view of `subdifferential f x`, obtained by restricting the chapter's
source-facing subdifferential along the canonical coercion `StrongDual ℝ E → Module.Dual ℝ E`. -/
abbrev strongDualSubdifferential (f : E → EReal) (x : E) : Set (StrongDual ℝ E) :=
  ((↑) : StrongDual ℝ E → Module.Dual ℝ E) ⁻¹' ∂ f(x)

notation "∂ₛ" f "(" x ")" => strongDualSubdifferential f x

/-- Membership in `strongDualSubdifferential f x` means that the underlying algebraic-dual
functional belongs to the owner subdifferential `subdifferential f x`. -/
@[simp] theorem mem_strongDualSubdifferential
    {f : E → EReal} {x : E} {g : StrongDual ℝ E} :
    g ∈ ∂ₛ f(x) ↔ (g : Module.Dual ℝ E) ∈ ∂ f(x) :=
  Iff.rfl

-- Proof sketch: write `∂ₛ f(x)` as the intersection, over `y : E`, of the closed
-- half-spaces cut out by the affine functionals `g ↦ (g (y - x) : EReal)`, together
-- with the constant condition `x ∈ effective_domain f`; arbitrary intersections of closed sets are
-- closed.
/-- Theorem 3.1 (1): for an extended-real-valued function, the continuous-dual subdifferential
`∂ₛ f(x)` is a closed subset of the dual space. -/
theorem isClosed_subdifferential (f : E → EReal) (x : E) :
    IsClosed (∂ₛ f(x)) := sorry

/-- Theorem 3.1 (2): for an extended-real-valued function, the continuous-dual subdifferential
`∂ₛ f(x)` is a convex subset of the dual space. -/
theorem convex_strongDualSubdifferential (f : E → EReal) (x : E) :
    Convex ℝ (∂ₛ f(x)) := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- In finite dimensions, every algebraic functional is continuous, so the strong-dual view of
`subdifferential f x` is exactly its image under the canonical equivalence
`LinearMap.toContinuousLinearMap`. -/
theorem strongDualSubdifferential_eq_image_subdifferential
    (f : E → EReal) (x : E) :
    ∂ₛ f(x) =
      (LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E) ''
        ∂ f(x) := by
  let e : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E := LinearMap.toContinuousLinearMap
  ext g
  constructor
  · intro hg
    exact ⟨e.symm g, hg, e.apply_symm_apply g⟩
  · rintro ⟨g', hg', rfl⟩
    simpa [e] using hg'

end

section

open InnerProductSpace (toDualMap)

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Euclidean/vector-side view of `subdifferential f x`, obtained by transporting the Chapter
3 strong-dual bridge `strongDualSubdifferential f x` back to vectors through the Riesz map. This
is a `bridge/view` API; `subdifferential` remains the owner abstraction. -/
abbrev euclideanSubdifferential (f : E → EReal) (x : E) : Set E :=
  (toDualMap ℝ E) ⁻¹' strongDualSubdifferential f x

/-- Membership in `euclideanSubdifferential f x` is definitionally membership of the corresponding
Riesz functional in `strongDualSubdifferential f x`. -/
@[simp] theorem mem_euclideanSubdifferential_iff
    {f : E → EReal} {x z : E} :
    z ∈ euclideanSubdifferential f x ↔
      toDualMap ℝ E z ∈ strongDualSubdifferential f x :=
  Iff.rfl

end
