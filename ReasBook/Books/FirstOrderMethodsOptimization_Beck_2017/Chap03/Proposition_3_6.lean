import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_6

-- Declarations for this item will be appended below by the statement pipeline.

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
