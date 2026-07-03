

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_3_6_1 (from Chap03) -/
section

/- Proposition 3.6.1 is `source-facing`: it studies one concrete extended-real-valued example.
The owner abstraction for “equal to a function on a feasible set and `⊤` outside” already exists
upstream as `constrained_problem_objective`, so the only primitive data kept here are the concrete
objective `x ↦ -√x` and the feasible set `[0, ∞)`. The proposition clauses themselves stay at the
chapter owners `is_convex_function` and `subdifferential`; no extra helper API is exposed beyond
that concrete source object. -/

/-- The extended-real function equal to `-√x` on the nonnegative ray and `∞` on the negative
half-line. -/
noncomputable def negative_sqrt_extension : ℝ → EReal :=
  constrained_problem_objective (fun x ↦ ((-Real.sqrt x : ℝ) : EReal)) (Set.Ici (0 : ℝ))

-- Proof sketch: `negative_sqrt_extension` never takes the value `⊥`, so the bridge
-- `is_convex_function_iff_convexOn_toReal` reduces the owner-level convexity claim to convexity of
-- the finite restriction on its effective domain, computed locally as `[0, ∞)`. On that ray the
-- function is `x ↦ -Real.sqrt x`, which is convex because `Real.sqrt` is concave on the
-- nonnegative ray.
/-- Proposition 3.6.1 (1): the function `negative_sqrt_extension` is convex. -/
theorem negative_sqrt_extension_is_convex_function :
    is_convex_function negative_sqrt_extension := sorry

-- Proof sketch: assume `g ∈ subdifferential negative_sqrt_extension 0`. The subgradient inequality
-- then gives `-Real.sqrt y ≥ g * y` for every `y ≥ 0`. Evaluating at `y = 1` forces `g < 0`, and
-- taking `y = 1 / (2 * g ^ 2)` yields a contradiction.
/-- Proposition 3.6.1 (2): the subdifferential of `negative_sqrt_extension` at `0` is empty, so
the function is not subdifferentiable there. -/
theorem negative_sqrt_extension_subdifferential_zero :
    subdifferential negative_sqrt_extension (0 : ℝ) = ∅ := sorry

end

/-! ### Definition_3_6 (from Chap03) -/
universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 3.6 is `source-facing` in the chapter subgradient API. The primitive owner object is
the pointwise set `subdifferential f x`; Definition 3.5 already identifies "subdifferentiable at
`x`" with the canonical proposition `(subdifferential f x).Nonempty`. This file therefore keeps
only the textbook point-domain `dom(∂ f)` together with the atomic membership and domain
consequence lemmas derived from that owner set. -/

/-- Definition 3.6: the domain of the subdifferential `dom(∂ f)` is the set of points where the
extended-real-valued function `f` is subdifferentiable, equivalently where `∂ f(x)` is nonempty. -/
def subdifferential_domain (f : E → EReal) : Set E :=
  {x | (subdifferential f x).Nonempty}

-- Proof sketch: unfold `subdifferential_domain`.
/-- Membership in `dom(∂ f)` means that the subdifferential at the point is nonempty. -/
@[simp] theorem mem_subdifferential_domain {f : E → EReal} {x : E} :
    x ∈ subdifferential_domain f ↔ (subdifferential f x).Nonempty :=
  Iff.rfl

-- Proof sketch: if `x ∉ effective_domain f`, then Definition 3.2 gives
-- `subdifferential f x = ∅`, so `x` cannot belong to `subdifferential_domain f`.
/-- Every point in the domain of the subdifferential belongs to the effective domain. -/
theorem subdifferential_domain_subset_effective_domain {f : E → EReal} :
    subdifferential_domain f ⊆ effective_domain f := by
  intro x hx
  rw [mem_subdifferential_domain] at hx
  by_contra hx_dom
  simp [subdifferential_eq_empty_of_not_mem_effective_domain hx_dom] at hx

end

/-! ### Proposition_3_6 (from Chap03) -/
universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Proposition 3.6 is `source-facing` in the chapter convex-analysis API. Its owner notions are
the Chapter 2 predicate `is_convex_function` and the Chapter 3 owner set
`subdifferential_domain`; the textbook condition "subdifferentiable at every point of dom(f)" is
therefore best recorded as the inclusion `effective_domain f ⊆ subdifferential_domain f`, with the
pointwise nonemptiness view left to `[simp]` rewrites from `mem_subdifferential_domain`. -/

-- Proof sketch: for each `x ∈ effective_domain f`, the inclusion `hsub` gives
-- `x ∈ subdifferential_domain f`, hence some `g ∈ subdifferential f x`, equivalently a
-- subgradient at `x`. Applying the resulting inequalities at a convex combination of `x₀` and
-- `x₁` yields the Jensen inequality, hence convexity.
/-- Proposition 3.6: if an extended-real-valued function is subdifferentiable at every point of
its convex effective domain, then the function is convex. -/
theorem is_convex_function_of_subdifferentiable_on_convex_effective_domain
    {f : E → EReal} (hdom : Convex ℝ (effective_domain f))
    (hsub : effective_domain f ⊆ subdifferential_domain f) :
    is_convex_function f := by
  rw [is_convex_function_iff_segment_ineq]
  intro x hx y hy t ht
  let z := t • x + (1 - t) • y
  have hz : z ∈ effective_domain f := by
    refine hdom hx hy ht.1 (sub_nonneg.2 ht.2) ?_
    ring
  rcases mem_subdifferential_domain.mp (hsub hz) with ⟨g, hg⟩
  by_cases hfz_bot : f z = ⊥
  · simp [z, hfz_bot]
  · have hgx : f x ≥ f z + (g (x - z) : EReal) := hg.2 x
    have hgy : f y ≥ f z + (g (y - z) : EReal) := hg.2 y
    have hfx_top : f x ≠ ⊤ := (mem_effective_domain.mp hx).ne
    have hfy_top : f y ≠ ⊤ := (mem_effective_domain.mp hy).ne
    have hfz_top : f z ≠ ⊤ := (mem_effective_domain.mp hz).ne
    have hfx_bot : f x ≠ ⊥ := by
      intro hfx_bot
      have hgxz_ne_bot : (g (x - z) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
      have hsum_ne_bot : f z + (g (x - z) : EReal) ≠ ⊥ := by
        rw [EReal.add_ne_bot_iff]
        exact ⟨hfz_bot, hgxz_ne_bot⟩
      have hsum_le_bot : f z + (g (x - z) : EReal) ≤ ⊥ := by
        simpa [hfx_bot] using hgx
      exact hsum_ne_bot (le_bot_iff.mp hsum_le_bot)
    have hfy_bot : f y ≠ ⊥ := by
      intro hfy_bot
      have hgyz_ne_bot : (g (y - z) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
      have hsum_ne_bot : f z + (g (y - z) : EReal) ≠ ⊥ := by
        rw [EReal.add_ne_bot_iff]
        exact ⟨hfz_bot, hgyz_ne_bot⟩
      have hsum_le_bot : f z + (g (y - z) : EReal) ≤ ⊥ := by
        simpa [hfy_bot] using hgy
      exact hsum_ne_bot (le_bot_iff.mp hsum_le_bot)
    have hgx_real : (f z).toReal + g (x - z) ≤ (f x).toReal := by
      exact EReal.coe_le_coe_iff.mp <| by
        simpa [ge_iff_le, EReal.coe_add, EReal.coe_toReal hfx_top hfx_bot,
          EReal.coe_toReal hfz_top hfz_bot] using hgx
    have hgy_real : (f z).toReal + g (y - z) ≤ (f y).toReal := by
      exact EReal.coe_le_coe_iff.mp <| by
        simpa [ge_iff_le, EReal.coe_add, EReal.coe_toReal hfy_top hfy_bot,
          EReal.coe_toReal hfz_top hfz_bot] using hgy
    have hcancel : t * g (x - z) + (1 - t) * g (y - z) = 0 := by
      have hvec : t • (x - z) + (1 - t) • (y - z) = (0 : E) := by
        calc
          t • (x - z) + (1 - t) • (y - z)
              = t • x + (1 - t) • y - (t • z + (1 - t) • z) := by
                  rw [smul_sub, smul_sub]
                  abel
          _ = t • x + (1 - t) • y - ((t + (1 - t)) • z) := by
                rw [← add_smul]
          _ = t • x + (1 - t) • y - z := by simp
          _ = 0 := by simp [z]
      have hlin := congrArg g hvec
      simpa using hlin
    have hmain : (f z).toReal ≤ t * (f x).toReal + (1 - t) * (f y).toReal := by
      nlinarith [hgx_real, hgy_real, hcancel, ht.1, sub_nonneg.2 ht.2]
    have hmain_ereal : f z ≤ ((t * (f x).toReal + (1 - t) * (f y).toReal : ℝ) : EReal) := by
      rw [← EReal.coe_toReal hfz_top hfz_bot]
      exact_mod_cast hmain
    simpa [z, EReal.coe_add, EReal.coe_mul, EReal.coe_toReal hfx_top hfx_bot,
      EReal.coe_toReal hfy_top hfy_bot] using hmain_ereal

end

/-! ### Theorem_3_6 (from Chap03) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 3.6 is a `source-facing` existence statement in the chapter convex-analysis API.
Its owner notions are already provided earlier in the project by `effective_domain`,
`is_convex_function`, `subdifferential`, and `intrinsicInterior ℝ`, so this file reuses those
declarations directly rather than restating local copies. The relative-interior hypothesis already
forces `effective_domain f` to be nonempty, and for a convex extended-real-valued function any
occurrence of `⊥` is either absent on the effective domain or makes every dual vector a
subgradient there. Thus the theorem needs only the owner convexity and relative-interior
hypotheses. -/
recall effective_domain
recall is_convex_function
recall subdifferential
recall intrinsicInterior

-- Proof sketch: translate the textbook relative-interior hypothesis on `effective_domain f` into
-- the finite-dimensional supporting-hyperplane setup for the epigraph of `f`. A supporting
-- functional at `(x, f x)` has positive vertical coefficient, and normalizing it yields a linear
-- functional satisfying the subgradient inequality at `x`. If `f` takes the value `⊥` somewhere
-- on the effective domain, convexity forces the same at every relative-interior point, and then
-- the subgradient inequality is automatic for every dual vector.
/-- Theorem 3.6: if `f` is convex and `x` lies in the relative interior of `dom(f)`, then the
subdifferential `∂ f(x)` is nonempty. -/
theorem subdifferential_nonempty_at_relativeInterior_point
    (f : E → EReal) (x : E) (hconv : is_convex_function f)
    (hx : x ∈ intrinsicInterior ℝ (effective_domain f)) :
    (subdifferential f x).Nonempty := sorry

end
