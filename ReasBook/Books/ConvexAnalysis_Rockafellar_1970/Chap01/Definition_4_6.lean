import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set

/-!
Source triage for this item.

- `source-facing`: the item defines properness of a convex function through its epigraph.
- `core/canonical`: the owner abstraction is properness of a codomain-agnostic function
  `f : E → β` when the codomain has ordered-top and bottom structure, using nonemptiness of the
  effective domain `dom(f)` for the finite-point part;
  convexity is separate data supplied elsewhere.
- `bridge/view`: the useful bridge is the standard pointwise reformulation saying that `f` is proper
  exactly when its effective domain is nonempty and it is nowhere `⊥`. The source epigraph
  phrasing is retained as a theorem-level characterization rather than as the primary owner.

Mathlib sampling used here:
- `ConvexOn` in `Mathlib/Analysis/Convex/Function.lean`;
- `ConvexOn.convex_epigraph` in the same file;
- `lowerSemicontinuousOn_iff_isClosed_epigraph` in
  `Mathlib/Topology/Semicontinuity/Basic.lean`.

Project sampling used here:
- `effectiveDomain`, notation `dom(·)`, and `mem_effectiveDomain` from `Definition_4_4`;
- `effectiveDomain_eq_image_fst_epi` from `Definition_4_4`, which already identifies the
  effective domain with the projection of the epigraph;
- the chapter owner pattern `Function.IsConvex` from `Theorem_4_2`, where the reusable owner stays
  concise and source phrasing is exposed through companion theorems.

The book's "contains no vertical lines" is rendered directly on the ambient height type `α`. The
vertical-line bridge uses `NoMinOrder α` (to descend strictly below a finite height) and
`Nonempty α` (to witness finite levels); for the final properness characterization, the latter is
recovered from the hypotheses on either side.
-/

namespace Function

variable {E : Type u} {α : Type v} {β : Type v}

/-- Definition 4.6: a function into a codomain with strict order, top, and bottom is proper exactly when
its effective domain is nonempty and it is nowhere equal to `⊥`. This reuses the chapter owner
`dom(·)` for finite points while keeping the textbook epigraph formulation as derived API in the
`WithTopBot` specialization below. -/
def IsProper [LT β] [Top β] [Bot β] (f : E → β) : Prop :=
  dom(f).Nonempty ∧ ∀ x, f x ≠ ⊥

/-- A function is proper exactly when it has a finite point and is nowhere equal to `⊥`. -/
theorem isProper_iff [LT β] [Top β] [Bot β] (f : E → β) :
    f.IsProper ↔ dom(f).Nonempty ∧ ∀ x, f x ≠ ⊥ :=
  Iff.rfl

/-- With a nonempty effective domain fixed, improperness is exactly existence of a point where the
function takes the value `⊥`. -/
theorem not_isProper_iff_exists_eq_bot_of_nonempty_dom [LT β] [Top β] [Bot β]
    {f : E → β} (hdom : dom(f).Nonempty) :
    ¬ f.IsProper ↔ ∃ x, f x = ⊥ := by
  constructor
  · intro hf_not_proper
    by_contra h_exists_bot
    exact hf_not_proper ⟨hdom, fun x hx_bot ↦ h_exists_bot ⟨x, hx_bot⟩⟩
  · rintro ⟨x, hx_bot⟩ hf_proper
    exact (hf_proper.2 x) hx_bot

/-- Bridge form of properness using strict inequality above `⊥`. -/
theorem isProper_iff_nonempty_dom_and_bot_lt
    [PartialOrder β] [Top β] [OrderBot β] [NoBotOrder β] (f : E → β) :
    f.IsProper ↔ dom(f).Nonempty ∧ ∀ x, ⊥ < f x := by
  rw [isProper_iff]
  constructor
  · rintro ⟨hdom, hne_bot⟩
    -- Rewrite the owner predicate pointwise into strict separation from `⊥`.
    refine ⟨hdom, ?_⟩
    intro x
    simpa using
      ((bot_lt_iff_ne_bot : (⊥ : β) < f x ↔ f x ≠ (⊥ : β)).2 (hne_bot x))
  · rintro ⟨hdom, hbot_lt⟩
    -- Conversely, `⊥ < f x` is exactly the exclusion of the bottom value.
    refine ⟨hdom, ?_⟩
    intro x
    exact
      (bot_lt_iff_ne_bot : (⊥ : β) < f x ↔ f x ≠ (⊥ : β)).1 (hbot_lt x)

/-- A proper function has a nonempty effective domain. -/
theorem IsProper.nonempty_dom [LT β] [Top β] [Bot β] {f : E → β} (hf : f.IsProper) :
    dom(f).Nonempty :=
  hf.1

/-- A proper function is nowhere equal to `⊥`. -/
theorem IsProper.ne_bot [LT β] [Top β] [Bot β] {f : E → β} (hf : f.IsProper) (x : E) :
    f x ≠ ⊥ :=
  hf.2 x

/-- A proper function is everywhere strictly above `⊥` whenever `<` is bottom-separated. -/
theorem IsProper.bot_lt [PartialOrder β] [Top β] [OrderBot β] [NoBotOrder β]
    {f : E → β} (hf : f.IsProper) (x : E) :
    ⊥ < f x :=
  by
    -- The owner already records the only pointwise obstruction to `⊥ < f x`.
    simpa using
      ((bot_lt_iff_ne_bot : (⊥ : β) < f x ↔ f x ≠ (⊥ : β)).2 (hf.ne_bot x))

/-!
The direct `WithTopBot` abbreviation in this mathlib snapshot has no dedicated namespace API.
These local bridges keep the coercion/order manipulations explicit and stable inside Definition 4.6.
-/

/-- Helper for Definition 4.6: finite values of `WithTopBot α` are strictly above `⊥`. -/
private theorem withTopBot_bot_lt_coe {δ : Type*} [LT δ] (a : δ) :
    (⊥ : WithTopBot δ) < (a : WithTopBot δ) := by
  change (((⊥ : WithBot δ) : WithTop (WithBot δ)) <
    (((a : WithBot δ) : WithTop (WithBot δ))))
  exact WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe a)

/-- Helper for Definition 4.6: finite values of `WithTopBot α` are strictly below `⊤`. -/
private theorem withTopBot_coe_lt_top {δ : Type*} [LT δ] (a : δ) :
    (a : WithTopBot δ) < (⊤ : WithTopBot δ) := by
  change (((a : WithBot δ) : WithTop (WithBot δ)) < (⊤ : WithTop (WithBot δ)))
  exact WithTop.coe_lt_top _

/-- Helper for Definition 4.6: finite values of `WithTopBot α` are never `⊥`. -/
private theorem withTopBot_coe_ne_bot {δ : Type*} (a : δ) :
    (a : WithTopBot δ) ≠ (⊥ : WithTopBot δ) := by
  intro h
  change (((a : WithBot δ) : WithTop (WithBot δ)) =
    (((⊥ : WithBot δ) : WithTop (WithBot δ)))) at h
  cases h

/-- Helper for Definition 4.6: on `WithTopBot α`, strict separation from `⊥` is exactly exclusion
of the bottom value. -/
private theorem withTopBot_bot_lt_iff_ne_bot {δ : Type*} [Preorder δ] {x : WithTopBot δ} :
    (⊥ : WithTopBot δ) < x ↔ x ≠ (⊥ : WithTopBot δ) := by
  cases x with
  | none =>
      constructor
      · intro _ h
        cases h
      · intro _
        change (((⊥ : WithBot δ) : WithTop (WithBot δ)) < (⊤ : WithTop (WithBot δ)))
        exact WithTop.coe_lt_top _
  | some y =>
      cases y with
      | bot =>
          constructor
          · intro h
            exact (lt_irrefl (⊥ : WithTopBot δ) h).elim
          · intro h
            exact False.elim (h rfl)
      | coe a =>
          constructor
          · intro _
            exact withTopBot_coe_ne_bot a
          · intro _
            exact withTopBot_bot_lt_coe a

/-- Helper for Definition 4.6: the canonical codomain lift views a finite-valued map as
`WithTopBot`-valued. -/
abbrev toWithTopBot {X : Type*} {δ : Type*} (g : X → δ) : X → WithTopBot δ :=
  fun x ↦ (g x : WithTopBot δ)

/-- Helper for Definition 4.6: `extendBotTop φ` preserves the two boundary points and applies `φ`
to finite values. -/
def extendBotTop {δ ε : Type*} [Top ε] [Bot ε] (φ : δ → ε) : WithTopBot δ → ε
  | ⊥ => ⊥
  | ⊤ => ⊤
  | (a : δ) => φ a

/-- Helper for Definition 4.6: `extendBotTop` sends `⊥` to `⊥`. -/
@[simp] theorem extendBotTop_bot {δ ε : Type*} [Top ε] [Bot ε] (φ : δ → ε) :
    φ.extendBotTop (⊥ : WithTopBot δ) = ⊥ :=
  rfl

/-- Helper for Definition 4.6: `extendBotTop` sends `⊤` to `⊤`. -/
@[simp] theorem extendBotTop_top {δ ε : Type*} [Top ε] [Bot ε] (φ : δ → ε) :
    φ.extendBotTop (⊤ : WithTopBot δ) = ⊤ :=
  rfl

/-- Helper for Definition 4.6: `extendBotTop` agrees with `φ` on finite values. -/
@[simp] theorem extendBotTop_coe {δ ε : Type*} [Top ε] [Bot ε] (φ : δ → ε) (a : δ) :
    φ.extendBotTop (a : WithTopBot δ) = φ a :=
  rfl

/-- Helper for Definition 4.6: a domain point of a `WithTopBot α`-valued function that is not
`⊥` must be represented by a finite value of `α`. -/
theorem finite_value_of_mem_dom_and_ne_bot [Preorder α] {f : E → WithTopBot α} {x : E}
    (hx : x ∈ dom(f)) (hfx_bot : f x ≠ ⊥) :
    ∃ a : α, f x = a := by
  -- Membership in the effective domain excludes `⊤`, so only the finite branch remains.
  have hfx_top : f x ≠ ⊤ := (mem_effectiveDomain.mp hx).ne
  cases hfx : f x with
  | none =>
      exact (hfx_top hfx).elim
  | some y =>
      cases y with
      | bot =>
          exact (hfx_bot hfx).elim
      | coe a =>
          exact ⟨a, rfl⟩

/-- Composing a proper `WithTopBot α`-valued function with a boundary-preserving extension
`φ.extendBotTop` preserves properness when `φ` stays strictly below `⊤` and away from `⊥` on all
finite inputs. -/
theorem IsProper.comp_extendBotTop_of_lt_top_and_ne_bot {γ : Type*} [Preorder α] [Preorder γ]
    {f : E → WithTopBot α} (hf : f.IsProper) (φ : α → WithTopBot γ)
    (hφ_lt_top : ∀ a, φ a < ⊤) (hφ_ne_bot : ∀ a, φ a ≠ ⊥) :
    (φ.extendBotTop ∘ f).IsProper := by
  refine ⟨?_, ?_⟩
  · rcases hf.nonempty_dom with ⟨x, hx⟩
    -- Start from a finite witness in the effective domain of `f`.
    rcases finite_value_of_mem_dom_and_ne_bot (f := f) hx (hf.ne_bot x) with ⟨a, ha⟩
    refine ⟨x, ?_⟩
    simpa [Function.comp, ha] using hφ_lt_top a
  · intro x
    by_cases hfx_top : f x = ⊤
    · -- The extension preserves the top boundary point.
      intro h
      have htop_bot : (⊤ : WithTopBot γ) = (⊥ : WithTopBot γ) := by
        simpa [Function.comp, hfx_top] using h
      cases htop_bot
    · -- Away from `⊤`, properness of `f` lets us descend to a finite branch of `φ`.
      have hx_dom : x ∈ dom(f) := by
        exact mem_effectiveDomain.mpr
          ((WithTop.lt_top_iff_ne_top : f x < (⊤ : WithTopBot α) ↔ f x ≠ ⊤).2 hfx_top)
      rcases finite_value_of_mem_dom_and_ne_bot (f := f) hx_dom (hf.ne_bot x) with ⟨a, ha⟩
      intro h
      have h' : φ a = ⊥ := by
        simpa [Function.comp, ha] using h
      exact hφ_ne_bot a h'

/-- Finite-branch companion of `IsProper.comp_extendBotTop_of_lt_top_and_ne_bot`: composing with
`((φ.toWithTopBot).extendBotTop)` preserves properness. -/
theorem IsProper.comp_extendBotTop {γ : Type*} [Preorder α] [Preorder γ]
    {f : E → WithTopBot α}
    (hf : f.IsProper) (φ : α → γ) :
    (((φ.toWithTopBot).extendBotTop) ∘ f).IsProper := by
  refine hf.comp_extendBotTop_of_lt_top_and_ne_bot (φ := φ.toWithTopBot) ?_ ?_
  · intro a
    -- Finite values stay finite under the canonical codomain lift.
    exact withTopBot_coe_lt_top (φ a)
  · intro a
    exact withTopBot_coe_ne_bot (φ a)

/-- A proper `WithTopBot α`-valued function has nonempty finite codomain layer `α`. -/
private theorem IsProper.nonempty_codomain [Preorder α] {f : E → WithTopBot α}
    (hf : f.IsProper) :
    Nonempty α := by
  rcases hf.nonempty_dom with ⟨x, hx⟩
  -- A proper function has a finite value somewhere in its effective domain.
  rcases finite_value_of_mem_dom_and_ne_bot (f := f) hx (hf.ne_bot x) with ⟨a, ha⟩
  exact ⟨a⟩

/-- A proper `WithTopBot α`-valued function has a nonempty epigraph. -/
private theorem IsProper.epigraph_nonempty [Preorder α] {f : E → WithTopBot α}
    (hf : f.IsProper) :
    (epi f).Nonempty := by
  rcases hf.nonempty_dom with ⟨x, hx⟩
  -- Use a finite point of `f` to produce an explicit epigraph witness.
  rcases finite_value_of_mem_dom_and_ne_bot (f := f) hx (hf.ne_bot x) with ⟨a, ha⟩
  refine ⟨(x, a), ?_⟩
  exact (mem_epi_restrict_iff).2
    ⟨by simp, by simp [ha]⟩

/-- The epigraph of a `WithTopBot α`-valued function is nonempty exactly when its effective domain
is nonempty. -/
private theorem epigraph_nonempty_iff_nonempty_dom [Preorder α] [Nonempty α]
    (f : E → WithTopBot α) :
    (epi f).Nonempty ↔ dom(f).Nonempty := by
  rw [effectiveDomain_eq_image_fst_epi]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.1, ⟨p, hp, rfl⟩⟩
  · rintro ⟨x, ⟨p, hp, rfl⟩⟩
    exact ⟨p, hp⟩

/-- The vertical line above `x` fails to lie in the epigraph exactly when `f x` is strictly above
`⊥`. -/
private theorem no_vertical_line_iff_bot_lt [Preorder α] [Nonempty α] [NoMinOrder α]
    (f : E → WithTopBot α) (x : E) :
    (¬ ∀ r : α, (x, r) ∈ epi f) ↔ ⊥ < f x := by
  constructor
  · intro hnoVertical
    by_cases hfx_top : f x = ⊤
    · rw [hfx_top]
      rcases ‹Nonempty α› with ⟨a⟩
      exact lt_trans (withTopBot_bot_lt_coe a) (withTopBot_coe_lt_top a)
    · by_cases hfx_bot : f x = (⊥ : WithTopBot α)
      · -- If `f x = ⊥`, every finite height lies above it, giving a full vertical line.
        exact False.elim <|
          hnoVertical (fun r ↦ (mem_epi_restrict_iff).2 ⟨by simp, by simp [hfx_bot]⟩)
      · -- Otherwise `f x` is finite, so strict positivity above `⊥` is immediate.
        have hx_dom : x ∈ dom(f) := by
          exact mem_effectiveDomain.mpr
            ((WithTop.lt_top_iff_ne_top : f x < (⊤ : WithTopBot α) ↔ f x ≠ ⊤).2 hfx_top)
        rcases finite_value_of_mem_dom_and_ne_bot (f := f) hx_dom hfx_bot with ⟨a, ha⟩
        simpa [ha] using withTopBot_bot_lt_coe a
  · intro hbot hx
    by_cases hfx_top : f x = ⊤
    · -- A top value cannot lie below any finite height in the epigraph.
      rcases ‹Nonempty α› with ⟨r⟩
      have htop_le : (⊤ : WithTopBot α) ≤ (r : WithTopBot α) := by
        simpa [hfx_top] using (mem_epi_restrict_iff.1 (hx r)).2
      have hr_top : ((r : α) : WithTopBot α) < (⊤ : WithTopBot α) := by
        exact withTopBot_coe_lt_top r
      exact (not_le_of_gt hr_top) htop_le
    · -- In the finite branch, move strictly below the realized height to leave the epigraph.
      have hfx_bot : f x ≠ ⊥ := by
        exact (withTopBot_bot_lt_iff_ne_bot).1 hbot
      have hx_dom : x ∈ dom(f) := by
        exact mem_effectiveDomain.mpr
          ((WithTop.lt_top_iff_ne_top : f x < (⊤ : WithTopBot α) ↔ f x ≠ ⊤).2 hfx_top)
      rcases finite_value_of_mem_dom_and_ne_bot (f := f) hx_dom hfx_bot with ⟨a, ha⟩
      obtain ⟨r, hr⟩ : ∃ r : α, r < a := exists_lt a
      have hxa : (a : WithTopBot α) ≤ r := by
        simpa [ha] using (mem_epi_restrict_iff.1 (hx r)).2
      exact (not_le_of_gt (show ((r : α) : WithTopBot α) < a by simpa using hr)) hxa

/-- The vertical line above `x` fails to lie in the epigraph exactly when `f x` is not `⊥`. -/
private theorem no_vertical_line_iff_ne_bot [Preorder α] [Nonempty α] [NoMinOrder α]
    (f : E → WithTopBot α) (x : E) :
    (¬ ∀ r : α, (x, r) ∈ epi f) ↔ f x ≠ ⊥ := by
  constructor
  · intro hnoVertical hfx_bot
    have hbot : (⊥ : WithTopBot α) < f x := (no_vertical_line_iff_bot_lt f x).1 hnoVertical
    rw [hfx_bot] at hbot
    exact lt_irrefl _ hbot
  · intro hfx_bot
    have hbot : (⊥ : WithTopBot α) < f x := by
      exact (withTopBot_bot_lt_iff_ne_bot).2 hfx_bot
    exact (no_vertical_line_iff_bot_lt f x).2 hbot

/-- Definition 4.6 in epigraph form: a `WithTopBot α`-valued function is proper exactly when its
epigraph is nonempty and contains no full vertical line. -/
theorem isProper_iff_nonempty_epigraph_and_no_vertical_line [Preorder α] [NoMinOrder α]
    (f : E → WithTopBot α) : f.IsProper ↔ (epi f).Nonempty ∧ ∀ x, ¬ ∀ r : α, (x, r) ∈ epi f := by
  rw [isProper_iff]
  constructor
  · rintro ⟨hdom, hne_bot⟩
    have hf : f.IsProper := ⟨hdom, hne_bot⟩
    letI : Nonempty α := hf.nonempty_codomain
    -- Properness supplies both a finite epigraph witness and pointwise exclusion of vertical lines.
    refine ⟨hf.epigraph_nonempty, ?_⟩
    intro x
    exact (no_vertical_line_iff_ne_bot f x).2 (hne_bot x)
  · rintro ⟨hepi, hnoVertical⟩
    rcases hepi with ⟨⟨x₀, r₀⟩, hx₀⟩
    letI : Nonempty α := ⟨r₀⟩
    -- A single epigraph point already gives a finite-domain witness for properness.
    refine ⟨⟨x₀, lt_of_le_of_lt (mem_epi_restrict_iff.1 hx₀).2
      (withTopBot_coe_lt_top r₀)⟩, ?_⟩
    intro x
    exact (no_vertical_line_iff_ne_bot f x).1 (hnoVertical x)

end Function
