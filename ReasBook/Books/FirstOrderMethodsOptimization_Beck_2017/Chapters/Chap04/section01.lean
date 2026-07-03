import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_1 (from Chap04) -/
universe u

open InnerProductSpace (toDualMap)

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 4.1 is `source-facing`: it introduces the Fenchel conjugate itself. In Chapter 4,
this file is also the `core/canonical` owner for that construction, so downstream files should
reuse `conjugate_function` rather than restating the same supremum formula under parallel local
names. The only primitive data here is the conjugate function; its evaluation formula is derived
API. -/

/-- Definition 4.1: the conjugate function `f*` of an extended-real-valued function `f` is the
extended-real-valued function on the dual space `E* = Module.Dual ℝ E` sending `y` to the
supremum of the values `y x - f x` over all `x : E`. This is the canonical `EReal` formulation
of the textbook formula (4.1). -/
noncomputable def conjugate_function (f : E → EReal) : Module.Dual ℝ E → EReal :=
  fun y ↦ sSup (Set.range fun x : E ↦ (y x : EReal) - f x)

/-- Evaluating the conjugate function at `y` gives the supremum of the dual pairing minus `f`
over all points of `E`. -/
theorem conjugate_function_apply (f : E → EReal) (y : Module.Dual ℝ E) :
    conjugate_function f y = sSup (Set.range fun x : E ↦ (y x : EReal) - f x) :=
  rfl

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The primal-space view of the Fenchel conjugate, obtained by evaluating the Chapter 4 owner
`conjugate_function` along the Riesz map `toDualMap ℝ E : E → E*`. -/
noncomputable abbrev conjugate_function_primal (f : E → EReal) : E → EReal :=
  fun x ↦ conjugate_function f (toDualMap ℝ E x)

end

/-- Textbook postfix notation for the primal-space Fenchel conjugate. -/
postfix:max "∗" => conjugate_function_primal

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Evaluating `f∗` at `x` is the same as evaluating `conjugate_function f` at the dual vector
corresponding to `x`. -/
theorem conjugate_function_primal_apply (f : E → EReal) (x : E) :
    (f∗) x = conjugate_function f (toDualMap ℝ E x) :=
  rfl

end

/-! ### Lemma_4_1 (from Chap04) -/
universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

-- Proof sketch: for fixed `x` and any dual vector `y`, the defining supremum formula for
-- `conjugate_function f y` gives `y x - f x ≤ conjugate_function f y`. Rearranging yields
-- `y x - conjugate_function f y ≤ f x`, and taking the supremum over `y` gives
-- `biconjugate_function f x ≤ f x`.
/-- Lemma 4.1: the biconjugate of an extended-real-valued function is pointwise bounded above by
the original function. -/
theorem biconjugate_function_apply_le (f : E → EReal) (x : E) :
    biconjugate_function f x ≤ f x := by
  cases hfx : f x with
  | bot =>
      rw [biconjugate_function_apply]
      refine sSup_le fun z hz ↦ ?_
      rcases hz with ⟨y, rfl⟩
      have hx_top : (⊤ : EReal) ∈ Set.range fun z : E ↦ (y z : EReal) - f z := by
        refine ⟨x, ?_⟩
        simp [hfx, EReal.sub_bot (EReal.coe_ne_bot (y x))]
      have hy_top : conjugate_function f y = ⊤ := by
        rw [conjugate_function_apply]
        exact top_unique <| le_sSup hx_top
      simp [hy_top]
  | coe r =>
      rw [biconjugate_function_apply]
      refine sSup_le fun z hz ↦ ?_
      rcases hz with ⟨y, rfl⟩
      change (y x : EReal) - conjugate_function f y ≤ (r : EReal)
      rw [conjugate_function_apply]
      have hxy :
          (y x : EReal) - (r : EReal) ≤
            sSup (Set.range fun z : E ↦ (y z : EReal) - f z) := by
        refine le_sSup ?_
        refine ⟨x, ?_⟩
        simp [hfx]
      have hy_le :
          (y x : EReal) ≤
            sSup (Set.range fun z : E ↦ (y z : EReal) - f z) + (r : EReal) :=
        (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot r)) (.inl (EReal.coe_ne_top r))).1 hxy
      exact EReal.sub_le_of_le_add' hy_le
  | top =>
      simp

end

/-! ### Proposition_4_1 (from Chap04) -/
universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Proposition 4.1 is `source-facing`. Its owner abstractions already exist upstream:
`extendedIndicator` in Chapter 2, `support_function` in Chapter 2, and `conjugate_function` in
Definition 4.1. This file therefore keeps only the indicator-conjugate identity itself. -/

-- Proof sketch: unfold `conjugate_function`, `extendedIndicator`, and `support_function`. If
-- `x ∈ C`, then `(extendedIndicator C) x = 0`, so the conjugate integrand is `y x`; if `x ∉ C`,
-- then `(extendedIndicator C) x = ⊤`, so the integrand is `⊥`. Thus the supremum over all `x`
-- reduces to the supremum over `C`.
/-- The pointwise indicator-conjugate identity: the Fenchel conjugate of `δ_C` at `y` is the
support function `σ_C (y)`. -/
theorem conjugate_function_extendedIndicator_apply_eq_support_function (C : Set E)
    (y : Module.Dual ℝ E) :
    conjugate_function (extendedIndicator C) y = support_function C y := sorry

-- Proof sketch: use extensionality on the dual variable and apply
-- `conjugate_function_extendedIndicator_apply_eq_support_function` pointwise.
/-- Proposition 4.1: equations (4.2) and (4.3) identify the Fenchel conjugate of the indicator
function `δ_C` with the support function `σ_C`. The textbook assumes `C` is nonempty, but this
equality remains valid for `C = ∅` because both sides are then constantly `⊥`. -/
theorem conjugate_function_extendedIndicator_eq_support_function (C : Set E) :
    conjugate_function (extendedIndicator C) = support_function C := sorry

end

/-! ### Theorem_4_1 (from Chap04) -/
universe u

open InnerProductSpace

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 4.1 is `source-facing` in the chapter conjugacy API. Its primitive notions are the
owner declarations `is_convex_function` from Definition 2.6 and `conjugate_function` from
Definition 4.1; the canonical `bridge/view` owner is `conjugate_function_primal`, which
specializes the dual-space conjugate to the primal inner-product space through `toDualMap`
without reintroducing a local lambda wrapper. -/
recall conjugate_function_primal

-- Proof sketch: for each fixed `x : E`, the map
-- `f∗` contributes the affine function
-- `y ↦ ⟪y, x⟫ - f x` in the defining supremum of `f*`. Each such affine function is continuous,
-- hence lower semicontinuous, and convex in the chapter-owner sense. Then closedness follows from
-- lower semicontinuity of pointwise suprema, and convexity follows from the chapter closure result
-- `is_convex_function_iSup` after rewriting the conjugate by its defining supremum.
/-- Theorem 4.1: the conjugate function of an extended-real-valued function on a real inner
product space, viewed on the primal space as `f∗`, is closed, i.e. lower semicontinuous, and
convex in the chapter-owner sense. -/
theorem conjugate_function_closed_and_convex (f : E → EReal) :
    LowerSemicontinuous (f∗) ∧ is_convex_function (f∗) :=
  sorry

end
