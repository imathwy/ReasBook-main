import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise Rockafellar

universe u v w

section

variable {𝕜 : Type v} {E : Type u} {α : Type w}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.20 introduces a new property of a convex function
  `f : E → WithTopBot α` (specializing to `ℝ^n → (-∞, +∞]`): being gauge-like means that `f`
  never takes the value `⊥`, that `0` is a
  minimizer of `f`, and that every finite strict-upper sublevel set `f ⁻¹' Set.Iic β` is a
  positive scalar multiple of one fixed set.
- `core/canonical`: the existing owner abstractions are the chapter convexity predicate
  `Function.IsConvex 𝕜`, the function-side minimum owner
  `IsMinOn f Set.univ 0`, and the chapter's canonical sublevel-set style
  `f ⁻¹' Set.Iic α`.
- `bridge/view`: the later representation theorem pairs this source-facing predicate with
  `Function.IsClosedProperConvex`; closedness and properness belong there, while convexity already
  belongs to the present owner because the text defines gauge-like functions among convex
  functions.

Domain-style sampling used here:
- the project declaration `Function.IsConvex` from `Theorem_4_2`;
- the function owner `IsMinOn` together with its range-minimum bridge `IsLeast`;
- the chapter's canonical sublevel-set pattern `f ⁻¹' Set.Iic β`;
- mathlib's pointwise scalar action on sets `t • C`.

Primitive data vs derived API:
- primitive owner data: the function `f : E → WithTopBot α`;
- primitive conditions from the source: the codomain restriction `f(x) ∈ (-∞, +∞]`, convexity,
  the minimum condition that `0` realizes the least value of `f`, and proportionality of all
  finite strict-upper sublevel sets;
- the range-level least-element statement is derived API from the function-side minimum owner, so
  it should not remain a primitive field.

Layer target: `source-facing`.
-/

namespace Function

/-- Text 15.0.20: a convex function `f : E → WithTopBot α` (in particular
`f : ℝ^n → (-∞, +∞]`) is gauge-like if it never takes the value `⊥`, if `0` attains the infimum
of its values, and if every strict-upper sublevel set at a finite codomain level
`β : WithTopBot α` (i.e. `β < ⊤`) is a positive scalar multiple of one fixed set.
Closedness and properness are later hypotheses, not part of this source-facing predicate. -/
class IsGaugeLike
    (𝕜 : Type v) [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E]
    [AddCommMonoid α] [SMul 𝕜 α] [PartialOrder α]
    (f : E → WithTopBot α) : Prop where
  bot_lt : ∀ x : E, ⊥ < f x
  convex : f.IsConvex 𝕜
  zero_isMinOn : IsMinOn f Set.univ 0
  proportional_finite_sublevel_sets :
    ∃ C : Set E,
      ∀ {β : WithTopBot α}, f 0 < β → β < ⊤ →
        ∃ t : 𝕜, 0 < t ∧ f ⁻¹' Set.Iic β = t • C

scoped[Rockafellar] notation "IsGaugeLike[" 𝕜 "]" => Function.IsGaugeLike (𝕜 := 𝕜)

namespace IsGaugeLike

/-- In a gauge-like function, `0` attains the least value of the range. -/
theorem zero_isLeast_range
    [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E]
    [AddCommMonoid α] [SMul 𝕜 α] [PartialOrder α]
    {f : E → WithTopBot α} (hf : IsGaugeLike[𝕜] f) :
    IsLeast (Set.range f) (f 0) := by
  have hmin : ∀ x : E, f 0 ≤ f x := by
    simpa [isMinOn_univ_iff] using hf.zero_isMinOn
  refine ⟨⟨0, rfl⟩, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact hmin x

end IsGaugeLike

/-- The zero function is a canonical gauge-like function. -/
instance
    [Semiring 𝕜] [PartialOrder 𝕜] [ZeroLEOneClass 𝕜] [NeZero (1 : 𝕜)]
    [AddCommMonoid E] [MulAction 𝕜 E]
    [AddCommMonoid α] [PartialOrder α]
    [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] :
    IsGaugeLike[𝕜] (fun _ : E ↦ (0 : WithTopBot α)) where
  bot_lt _ := by
    change (((⊥ : WithBot α) : WithTop (WithBot α)) <
      (((0 : α) : WithBot α) : WithTop (WithBot α)))
    exact WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe 0)
  convex := Function.isConvex_zero (𝕜 := 𝕜) (E := E) (β := α)
  zero_isMinOn := by
    simp [isMinOn_univ_iff]
  proportional_finite_sublevel_sets := by
    refine ⟨Set.univ, ?_⟩
    intro β hβ0 _
    refine ⟨1, zero_lt_one, ?_⟩
    ext x
    simp [hβ0.le]

end Function

end
