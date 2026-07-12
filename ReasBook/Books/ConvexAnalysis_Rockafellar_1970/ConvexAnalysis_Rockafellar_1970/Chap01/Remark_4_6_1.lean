import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-!
Source/core/bridge triage for this item.

-- `source-facing`: the remark rewrites properness in terms of the domain `{x | f x < ⊤}` and the
  finiteness of the restricted function.
- `core/canonical`: the owner predicate already introduced in this chapter is
  `Function.IsProper` for functions `f : E → WithBotTop α`.
- `bridge/view`: the present item is a pointwise restatement of that owner predicate using the
  textbook's domain language, not a new owner abstraction.

Mathlib/project sampling used here:
- the owner predicate `Function.IsProper` from the preceding item `Definition_4_6`;
- the bridge theorems `Function.isProper_iff` and
  `Function.isProper_iff_nonempty_dom_and_bot_lt` from the same item;
- the chapter owner bridge `mem_effectiveDomain`, which identifies `x ∈ dom(f)` with `f x < ⊤`;
- the order bridges `WithBot.bot_lt_iff_ne_bot` and `WithBotTop.bot_lt_coe`, which encode the
  textbook finiteness side as strict separation from `⊥` and `⊤`.

Primitive data vs derived API:
- primitive data: the owner predicate `Function.IsProper f`;
- derived API: the domain-language restatement `dom(f).Nonempty` together with pointwise
  finite-valuedness of `f` on `dom(f)`.

Layer target: `bridge/view`; this remark is a source-facing restatement of the chapter owner
predicate, not a second properness definition.
-/

section

variable {E : Type u}
variable {α : Type v} [Preorder α]

namespace Function

-- Proof sketch: first keep the primitive owner layer explicit:
-- `f.IsProper ↔ dom(f).Nonempty ∧ ∀ x ∈ dom(f), f x ≠ ⊥`.
-- This is equivalent to the Definition 4.6 owner because `f x = ⊥` forces `x ∈ dom(f)`.
--
-- Then move to the intrinsic order phrase on `dom(f)`:
-- `⊥ < f x`.
-- Finally recover the textbook existential finite-valued phrase by lifting each value away from
-- `⊥` and `⊤`.
/-- Helper for Remark 4.6.1: properness is equivalent to nonempty effective domain and pointwise
exclusion of `⊥` on that domain. This is the primitive domain-restricted owner bridge. -/
theorem isProper_iff_nonempty_dom_and_ne_bot_on_dom
    (f : E → WithBotTop α) :
    f.IsProper ↔ dom(f).Nonempty ∧ ∀ x ∈ dom(f), f x ≠ ⊥ := by
  rw [isProper_iff]
  constructor
  · rintro ⟨hdom, hne_bot⟩
    exact ⟨hdom, fun x _ ↦ hne_bot x⟩
  · rintro ⟨hdom, hne_bot⟩
    refine ⟨hdom, ?_⟩
    intro x
    by_cases hx : x ∈ dom(f)
    · exact hne_bot x hx
    · intro hfx_bot
      exact hx <| mem_effectiveDomain.mpr <| by
        simpa [hfx_bot] using (WithBot.bot_lt_coe (⊤ : WithTop α))

/-- Helper for Remark 4.6.1: properness is equivalent to nonempty effective domain and strict
separation from `⊥` on `dom(f)`. This is the intrinsic order form of finite-valuedness on the
restricted domain. -/
theorem isProper_iff_nonempty_dom_and_bot_lt_on_dom
    (f : E → WithBotTop α) :
    f.IsProper ↔ dom(f).Nonempty ∧ ∀ x ∈ dom(f), ⊥ < f x := by
  rw [isProper_iff_nonempty_dom_and_ne_bot_on_dom]
  constructor
  · rintro ⟨hdom, hne_bot⟩
    refine ⟨hdom, ?_⟩
    intro x hx
    exact (WithBot.bot_lt_iff_ne_bot).2 (hne_bot x hx)
  · rintro ⟨hdom, hbot_lt⟩
    refine ⟨hdom, ?_⟩
    intro x hx
    exact (WithBot.bot_lt_iff_ne_bot).1 (hbot_lt x hx)

/-- Helper for Remark 4.6.1: a `WithBotTop α`-valued function that is finite on the effective
domain and never equal to `⊥` there must actually take a finite `α`-value there. -/
private theorem finite_value_of_mem_dom_and_ne_bot_withBotTop
    {f : E → WithBotTop α} {x : E} (hx : x ∈ dom(f)) (hfx_bot : f x ≠ ⊥) :
    ∃ a : α, f x = a := by
  -- Domain membership removes the `⊤` branch, while the hypothesis removes the `⊥` branch.
  have hfx_top : f x ≠ ⊤ := (mem_effectiveDomain.mp hx).ne
  cases hfx : f x using WithBotTop.rec with
  | bot =>
      exact (hfx_bot hfx).elim
  | coe a =>
      exact ⟨a, rfl⟩
  | top =>
      exact (hfx_top hfx).elim

/-- Helper for Remark 4.6.1: properness is equivalent to nonempty effective domain and
finite-valuedness on `dom(f)`, expressed in existential finite-value form. -/
theorem isProper_iff_nonempty_dom_and_finite_restriction
    (f : E → WithBotTop α) :
    f.IsProper ↔ dom(f).Nonempty ∧ ∀ x ∈ dom(f), ∃ a : α, f x = a := by
  rw [isProper_iff_nonempty_dom_and_bot_lt_on_dom]
  constructor
  · rintro ⟨hdom, hbot_lt⟩
    refine ⟨hdom, ?_⟩
    intro x hx
    -- Route correction: the imported extractor is stated for `WithTopBot`, so we eliminate the
    -- two boundary branches directly in the `WithBotTop` nesting used by this remark.
    have hne_bot : f x ≠ ⊥ := (WithBot.bot_lt_iff_ne_bot).1 (hbot_lt x hx)
    exact finite_value_of_mem_dom_and_ne_bot_withBotTop hx hne_bot
  · rintro ⟨hdom, hfinite⟩
    refine ⟨hdom, ?_⟩
    intro x hx
    rcases hfinite x hx with ⟨a, ha⟩
    -- Convert the finite witness back into strict separation from `⊥` on the domain.
    have hne_bot : f x ≠ ⊥ := by
      intro hfx_bot
      simp [ha] at hfx_bot
    exact (WithBot.bot_lt_iff_ne_bot).2 hne_bot

/-- Remark 4.6.1: `f` is proper exactly when its domain `C = {x | f x < ⊤}` is nonempty and the
restriction of `f` to `C` is finite-valued, i.e. every `f x` with `x ∈ C` is equal to a finite
number. -/
theorem isProper_iff_nonempty_effectiveDomain_and_finite_restriction
    (f : E → WithBotTop α) :
    f.IsProper ↔ dom(f).Nonempty ∧ ∀ x ∈ dom(f), ∃ a : α, f x = a := by
  exact isProper_iff_nonempty_dom_and_finite_restriction (f := f)

end Function

end
