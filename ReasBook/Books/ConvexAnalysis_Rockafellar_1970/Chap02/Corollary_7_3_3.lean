import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_7_3_2

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

universe u

variable
    {𝕜 : Type*} {E : Type u}
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 7.3.3 says that a lower bound for a convex function on `ri[𝕜](C)`
  extends to `closure C`, provided the relative interior of `C` lies in the effective domain of
  the function.
- `core/canonical`: the owner abstraction already fixed upstream is `f.IsConvex` from
  `Theorem_4_2`, together with the canonical set-theoretic notions `Convex 𝕜`,
  `intrinsicInterior 𝕜 C`, and `closure`; the chapter source-facing notation `ri[𝕜](C)` is the
  canonical surface for that relative interior in this section.
- `bridge/view`: the effective domain is expressed by the chapter owner `dom(f)`, and the lower
  bound `f(x) ≥ α` by `α ≤ f x` at the same extended-codomain layer as `f`.

Domain-style sampling used here:
- the chapter owner predicate `f.IsConvex` from `Theorem_4_2`;
- mathlib's owner predicate `Convex 𝕜 C` for convex subsets;
- mathlib's convex relative-interior API `Convex.intrinsicInterior` and
  `Convex.closure_intrinsicInterior_eq_closure`;
- mathlib's closure operator `closure`;
- the preceding intrinsic-closure-to-relative-interior bridge
  `ri_inter_nonempty_of_intrinsicClosure_inter_openSublevel_nonempty` from
  `Corollary_7_3_2`.
- Primitive data vs derived API: the primitive inputs are the convex function `f`, the convex set
  `C`, the level `α`, the owner convexity hypothesis `hf : f.IsConvex`, the effective-domain
  inclusion on `ri[𝕜](C)`, and the lower-bound hypothesis on `ri[𝕜](C)`; the lower bound on
  `closure C` is the source-facing conclusion.
- Layer target: this item remains `source-facing`, but its corollaries are attached directly to
  the upstream owner namespace `Function.IsConvex` rather than kept as parallel global wrappers.
- Ambient-space refinement: the proof is coordinate-free and uses only the Chapter 7 owner layer
  on finite-dimensional ordered normed-field spaces.
-/

-- Proof sketch: argue by contradiction and first choose a scalar level `β : 𝕜` with
-- `f x < β ≤ α`. If a point of `intrinsicClosure 𝕜 C` lies below that scalar level, Corollary
-- 7.3.2 gives a strict-sublevel point in `ri[𝕜](C)`; this contradicts the lower-bound hypothesis
-- there.
namespace Function.IsConvex

variable {f : E → WithTopBot 𝕜}

private theorem withTopBot_exists_coe_of_ne_top_ne_bot {z : WithTopBot 𝕜}
    (hz_top : z ≠ ⊤) (hz_bot : z ≠ ⊥) :
    ∃ a : 𝕜, (a : WithTopBot 𝕜) = z := by
  cases hz : z using WithTop.recTopCoe with
  | top => exact False.elim (hz_top hz)
  | coe z' =>
      cases hz' : z' using WithBot.recBotCoe with
      | bot => exact False.elim (hz_bot (by simp [hz, hz']))
      | coe a => exact ⟨a, rfl⟩

/-- Corollary 7.3.3, intrinsic-closure pointwise owner form: if a convex function on a
finite-dimensional ordered normed-field space is bounded below by the level `α : WithTopBot 𝕜` on
`ri[𝕜](C)`, and if `ri[𝕜](C)` lies in the effective domain `dom(f)`, then every point of
`intrinsicClosure 𝕜 C` also satisfies the same lower bound. -/
theorem lower_bound_of_mem_intrinsicClosure_of_lower_bound_on_ri
    (hf : f.IsConvex 𝕜) {C : Set E} (hC : Convex 𝕜 C) (α : WithTopBot 𝕜)
    (hdom : ri[𝕜](C) ⊆ dom(f))
    (hα : ri[𝕜](C) ⊆ f ⁻¹' Set.Ici α)
    {x : E} (hx : x ∈ intrinsicClosure 𝕜 C) :
    α ≤ f x := by
  by_contra hxα
  have hxα' : ¬ α ≤ f x := by
    intro hle
    exact hxα hle
  obtain ⟨β, hβx, hβα⟩ : ∃ β : 𝕜, f x < (β : WithTopBot 𝕜) ∧ (β : WithTopBot 𝕜) ≤ α := by
    cases hαval : α using WithTop.recTopCoe with
    | top =>
        have hxαtop : ¬ (⊤ : WithTopBot 𝕜) ≤ f x := by
          simpa [hαval] using hxα'
        have hfx_top : f x < (⊤ : WithTopBot 𝕜) := lt_of_not_ge hxαtop
        by_cases hfx_bot : f x = ⊥
        · refine ⟨0, ?_, le_top⟩
          rw [hfx_bot]
          exact WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe 0)
        · have hfx_ne_top : f x ≠ ⊤ := (lt_top_iff_ne_top.mp hfx_top)
          rcases withTopBot_exists_coe_of_ne_top_ne_bot hfx_ne_top hfx_bot with ⟨γ, hγ⟩
          refine ⟨γ + 1, ?_, le_top⟩
          rw [← hγ]
          exact WithTop.coe_lt_coe.mpr
            (WithBot.coe_lt_coe.mpr (lt_add_of_pos_right γ zero_lt_one))
    | coe a =>
        cases haval : a using WithBot.recBotCoe with
        | bot => exact False.elim (hxα' (by simp [hαval, haval]))
        | coe a =>
            refine ⟨a, ?_, ?_⟩
            · exact lt_of_not_ge (by simpa [hαval, haval] using hxα')
            · simp [hαval, haval]
  obtain ⟨y, hyri, hylt⟩ :=
    ri_inter_nonempty_of_intrinsicClosure_inter_openSublevel_nonempty
      (hf := hf)
      (hC := hC) (α := β) (hdom := hdom) (hα := ⟨x, hx, hβx⟩)
  have hy_ge : α ≤ f y := by
    simpa [Set.mem_Ici] using hα hyri
  exact not_lt_of_ge (hβα.trans hy_ge) hylt

/-- Corollary 7.3.3, intrinsic-closure set-theoretic bridge. -/
theorem lower_bound_on_intrinsicClosure_of_lower_bound_on_ri
    (hf : f.IsConvex 𝕜) {C : Set E} (hC : Convex 𝕜 C) (α : WithTopBot 𝕜)
    (hdom : ri[𝕜](C) ⊆ dom(f))
    (hα : ri[𝕜](C) ⊆ f ⁻¹' Set.Ici α) :
    intrinsicClosure 𝕜 C ⊆ f ⁻¹' Set.Ici α := by
  intro x hx
  exact lower_bound_of_mem_intrinsicClosure_of_lower_bound_on_ri hf hC α hdom hα hx

/-- Corollary 7.3.3, ambient-closure pointwise bridge: if a convex function is bounded below by
`α` on `ri[𝕜](C)` and `ri[𝕜](C) ⊆ dom(f)`, then every point of `closure C` satisfies the same lower
bound. -/
theorem lower_bound_of_mem_closure_of_lower_bound_on_ri
    (hf : f.IsConvex 𝕜) {C : Set E} (hC : Convex 𝕜 C) (α : WithTopBot 𝕜)
    (hdom : ri[𝕜](C) ⊆ dom(f))
    (hα : ri[𝕜](C) ⊆ f ⁻¹' Set.Ici α)
    {x : E} (hx : x ∈ closure C) :
    α ≤ f x :=
  lower_bound_of_mem_intrinsicClosure_of_lower_bound_on_ri hf hC α hdom hα <| by
    simpa [intrinsicClosure_eq_closure 𝕜 C] using hx

/-- Corollary 7.3.3, ambient-closure set-theoretic bridge. -/
theorem lower_bound_on_closure_of_lower_bound_on_ri
    (hf : f.IsConvex 𝕜) {C : Set E} (hC : Convex 𝕜 C) (α : WithTopBot 𝕜)
    (hdom : ri[𝕜](C) ⊆ dom(f))
    (hα : ri[𝕜](C) ⊆ f ⁻¹' Set.Ici α) :
    closure C ⊆ f ⁻¹' Set.Ici α := by
  intro x hx
  exact lower_bound_of_mem_closure_of_lower_bound_on_ri hf hC α hdom hα hx

end Function.IsConvex

end
