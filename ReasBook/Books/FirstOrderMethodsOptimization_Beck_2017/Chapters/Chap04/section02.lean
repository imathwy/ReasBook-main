

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_2 (from Chap04) -/
universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-
Definition 4.2 is `source-facing`: it introduces the biconjugate `f**`. The `core/canonical`
owner abstraction is still the chapter Fenchel-conjugate operator `conjugate_function` from
Definition 4.1, so the only primitive data here should be the canonical double-dual evaluation
`x ↦ Module.Dual.eval ℝ E x` together with a second application of that owner. The textbook
supremum formula is derived API.
-/
/-- Definition 4.2: the biconjugate `f**` of an extended-real-valued function `f` is the
extended-real-valued function on `E` obtained by applying the Chapter 4 owner
`conjugate_function` from Definition 4.1 to `f*` on the dual space and then restricting along the
canonical double-dual evaluation map `E → E**`. Equivalently, it is the supremum over the dual
space `E* = Module.Dual ℝ E` of the values `y x - f*(y)`. -/
noncomputable def biconjugate_function (f : E → EReal) : E → EReal :=
  fun x ↦ conjugate_function (conjugate_function f) (Module.Dual.eval ℝ E x)

/-- Evaluating the biconjugate at `x` gives the supremum of `y x - f*(y)` over all dual vectors
`y`. -/
theorem biconjugate_function_apply (f : E → EReal) (x : E) :
    biconjugate_function f x =
      sSup (Set.range fun y : Module.Dual ℝ E ↦ (y x : EReal) - conjugate_function f y) :=
  by
    let g : Module.Dual ℝ E → EReal := conjugate_function f
    simpa [biconjugate_function, g] using
      conjugate_function_apply g (Module.Dual.eval ℝ E x)

end

/-! ### Proposition_4_2 (from Chap04) -/
universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Proposition 4.2 is `source-facing` in the chapter conjugacy API. The `core/canonical` owners
for properness and Fenchel conjugation are already Chapter 2's
`IsProperExtendedRealFunction` and Definition 4.1's `conjugate_function`, so this file keeps only
the source-facing inequality and reuses those owners directly. -/
recall IsProperExtendedRealFunction
recall conjugate_function
recall conjugate_function_apply

-- Proof sketch: evaluate the defining supremum of `conjugate_function f y` at `x`, then rearrange
-- the resulting inequality in `EReal`.
/-- Proposition 4.2: Fenchel's inequality. For a proper extended-real-valued function `f`, the sum
of `f x` and its conjugate at `y` dominates the dual pairing `⟨y, x⟩`, written here as `y x`. -/
theorem fenchel_inequality (f : E → EReal) (x : E) (y : Module.Dual ℝ E)
    (hproper : IsProperExtendedRealFunction f) :
    f x + conjugate_function f y ≥ (y x : EReal) := by
  have hx :
      (y x : EReal) - f x ≤ conjugate_function f y := by
    rw [conjugate_function_apply]
    exact le_sSup (Set.mem_range_self x)
  rcases hproper.effective_domain_nonempty with ⟨z, hz⟩
  lift f z to ℝ using ⟨hz.ne, hproper.ne_bot z⟩ with fz hfz
  have hconj_ne_bot : conjugate_function f y ≠ ⊥ := by
    have hz' :
        ((y z : EReal) - f z) ≤ conjugate_function f y := by
      rw [conjugate_function_apply]
      exact le_sSup (Set.mem_range_self z)
    have hterm_ne_bot : ((y z : EReal) - f z) ≠ ⊥ := by
      rw [← hfz]
      simpa [EReal.coe_sub] using EReal.coe_ne_bot (y z - fz)
    exact bot_lt_iff_ne_bot.mp <| (bot_lt_iff_ne_bot.mpr hterm_ne_bot).trans_le hz'
  have hyx :
      (y x : EReal) ≤ conjugate_function f y + f x :=
    (EReal.sub_le_iff_le_add (.inl (hproper.ne_bot x)) (.inr hconj_ne_bot)).mp hx
  simpa [add_comm] using hyx

end

/-! ### Theorem_4_2 (from Chap04) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 4.2 is `source-facing` in the chapter conjugacy API. The `core/canonical` owners are
Chapter 2's `is_convex_function` together with Mathlib's `LowerSemicontinuous` and Definition 4.2's
`biconjugate_function` (built on Definition 4.1's `conjugate_function`). This file therefore keeps
only the source-facing biconjugation theorem and reuses those owner abstractions directly. -/
recall is_convex_function
recall biconjugate_function

-- Proof sketch: combine the earlier inequality `f** ≤ f` with strict separation of the epigraph
-- of a closed convex function from any point below it. The separating functional produces a
-- dual vector contradicting Fenchel's inequality unless `f x ≤ f** x`, so pointwise equality
-- follows.
/-- Theorem 4.2: a closed convex extended-real-valued function on a finite-dimensional real normed
space coincides with its biconjugate. Here closedness is expressed by `LowerSemicontinuous` and
convexity by `is_convex_function`. -/
theorem biconjugate_function_eq_self_of_closed_convex
    (f : E → EReal) (hclosed : LowerSemicontinuous f) (hconvex : is_convex_function f) :
    biconjugate_function f = f := sorry

end
