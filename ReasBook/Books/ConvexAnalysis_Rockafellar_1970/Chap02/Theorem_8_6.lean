import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_5
import ConvexAnalysis_Rockafellar_1970.Chap02.Definiton_8_5_0

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u}

open scoped Rockafellar
open Filter

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 8.6 studies, for a fixed direction `y`, when the translate profile
  `λ ↦ f (x + λ • y)` is non-increasing, first from a one-point `liminf` hypothesis, then
  globally in terms of membership in `((f)₀⁺).recessionCone`, equivalently
  `((f)₀⁺) y ≤ 0`, and finally in the closed case from one base point in `dom(f)`.
- `core/canonical`: the owner abstraction is the canonical namespace `Function`, with the
  owner declarations `Function.IsConvex 𝕜`, `Function.IsProper`, `recessionFunction`,
  `Function.recessionCone`, and
  `recessionFunction_isLeast_translationUpperBounds`,
  `tendsto_differenceQuotient_atTop_recessionFunction`.
- `bridge/view`: Rockafellar's phrase "non-increasing in `λ`, `-∞ < λ < +∞`" is rendered directly
  by the canonical order-theoretic predicate `Antitone` on the scalar-parameterized profile.

Domain-style sampling used here:
- `Function.recessionFunction`;
- `Function.recessionFunction_isLeast_translationUpperBounds`;
- `Function.recessionFunction_eq_sSup_differenceQuotients_at_point`;
- `Function.tendsto_differenceQuotient_atTop_recessionFunction`;
- `Filter.liminf` and `Antitone`.

Primitive data vs derived API:
- primitive inputs: a `WithBotTop α`-valued function `f : E → WithBotTop α` on a `𝕜`-module `E`,
  a direction
  `y`, and the translate profiles `t ↦ f (x + t • y)`;
- owner hypotheses: the first two clauses separate ambient geometry (`𝕜`, `E`) from codomain
  order-additive data (`α`) on the same canonical layer as
  `recessionFunction_isLeast_translationUpperBounds`; `f.IsConvex 𝕜` is needed first, then the
  theorem-level primitive assumptions are local `dom`-non-`⊥` (for the cone equivalence) and
  global non-`⊥` (for closed-case propagation), while `f.IsProper` is kept as a derived wrapper
  layer; the closed-case propagation theorem keeps the current scalar-codomain owner from Theorem
  8.5 and alone upgrades to
  `[AddCommGroup E]` plus the topological hypotheses needed for the limit formula;
- derived API: the order-theoretic antitonicity statements for translate profiles and their
  canonical reformulation via membership in `((f)₀⁺).recessionCone`, with the textbook
  inequality `((f)₀⁺) y ≤ 0` recovered by `Function.mem_recessionCone_iff`.

Layer target: this item stays `source-facing`, but it is stated directly in the canonical owner
language of `Function.recessionFunction` on the intrinsic module layer rather than through a
coordinate model or a wrapper namespace.
-/

namespace Function

section

variable {𝕜 : Type*} {α : Type*}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [Module 𝕜 α]
variable (f : E → WithBotTop α)

-- Proof sketch: apply the one-variable convex analysis of the restriction
-- `λ ↦ f (x + λ • y)`. Finiteness of `liminf` at `+∞` rules out positive asymptotic slope, so the
-- convex profile must be antitone on all of the scalar line.
/-- If the liminf of `f` along the ray `x + λ • y` is finite at `+∞`, then the profile
`λ ↦ f (x + λ • y)` is non-increasing on the scalar line. -/
theorem antitone_translate_of_liminf_lt_top
    (hf_convex : f.IsConvex 𝕜)
    {x y : E}
    (hliminf : liminf (fun t : 𝕜 ↦ f (x + t • y)) atTop < ⊤) :
    Antitone (fun t : 𝕜 ↦ f (x + t • y)) := sorry

end

section

variable {𝕜 : Type*} {α : Type*}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [Module 𝕜 α]
variable (f : E → WithBotTop α)

-- Proof sketch: if every translate profile is antitone, then the constant function `0` is a
-- translation upper bound for `f`, so the leastness statement for `(f)₀⁺` gives
-- `y ∈ ((f)₀⁺).recessionCone`. Conversely, that membership rewrites to the nonpositivity
-- inequality needed to show, via positive homogeneity, that `((f)₀⁺) ((t - s) • y) ≤ 0` for
-- `s ≤ t`; applying the
-- translation-upper-bound inequality with base point `x + s • y` and displacement `(t - s) • y`
-- gives `f (x + t • y) ≤ f (x + s • y)`, i.e. antitonicity of each translate profile.
/-- Primitive-layer form of Theorem 8.6: under the local non-`⊥` condition on `dom(f)`, every
translate profile `λ ↦ f (x + λ • y)` is non-increasing in `λ` for all base points if and only if
`y` lies in `((f)₀⁺).recessionCone`. -/
theorem forall_antitone_translate_iff_mem_recessionCone_of_dom_ne_bot
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ x ∈ dom(f), f x ≠ (⊥ : WithBotTop α))
    (y : E) :
    (∀ x : E, Antitone (fun t : 𝕜 ↦ f (x + t • y))) ↔
      y ∈ ((f)₀⁺).recessionCone := sorry

/-- Theorem 8.6 (proper specialization): for a proper convex function, every translate profile
`λ ↦ f (x + λ • y)` is non-increasing in `λ` if and only if `y` lies in the recession cone
`((f)₀⁺).recessionCone`. -/
theorem forall_antitone_translate_iff_mem_recessionCone
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (y : E) :
    (∀ x : E, Antitone (fun t : 𝕜 ↦ f (x + t • y))) ↔
      y ∈ ((f)₀⁺).recessionCone :=
  forall_antitone_translate_iff_mem_recessionCone_of_dom_ne_bot (f := f) hf_convex
    (fun x _ => hf_proper.ne_bot x) y

end

section

open scoped Topology

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable (f : E → WithBotTop 𝕜)

-- Proof sketch: by the assumed antitonicity at the chosen base point `x`, every positive
-- difference quotient based at `x` is nonpositive. The closed-case limit formula from Theorem 8.5
-- gives `y ∈ ((f)₀⁺).recessionCone`, and then the preceding equivalence upgrades this to
-- antitonicity for every base point.
/-- Primitive-layer closed-case propagation: antitonicity along one translate line through a point
of `dom(f)` propagates to every parallel translate line under convexity, lower semicontinuity, and
global non-`⊥` codomain values. -/
theorem forall_antitone_translate_of_closed_of_antitone_translate_of_ne_bot
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ z : E, f z ≠ (⊥ : WithBotTop 𝕜))
    (hf_closed : LowerSemicontinuous f)
    (y : E)
    {x : E} (hx : x ∈ dom(f))
    (hmono : Antitone (fun t : 𝕜 ↦ f (x + t • y))) :
    ∀ z : E, Antitone (fun t : 𝕜 ↦ f (z + t • y)) := sorry

/-- Proper specialization of the closed-case propagation theorem. -/
theorem forall_antitone_translate_of_closed_of_antitone_translate
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f)
    (y : E)
    {x : E} (hx : x ∈ dom(f))
    (hmono : Antitone (fun t : 𝕜 ↦ f (x + t • y))) :
    ∀ z : E, Antitone (fun t : 𝕜 ↦ f (z + t • y)) :=
  forall_antitone_translate_of_closed_of_antitone_translate_of_ne_bot (f := f)
    hf_convex (fun z => hf_proper.ne_bot z) hf_closed y hx hmono

end

end Function

end
