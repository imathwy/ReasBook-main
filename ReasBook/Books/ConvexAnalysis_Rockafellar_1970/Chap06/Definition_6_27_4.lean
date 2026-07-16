import ConvexAnalysis_Rockafellar_1970.Chap02.Definiton_8_5_0
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {𝕜 : Type v} {E : Type u} {β : Type w}
  [Preorder β] [Top β] [Preorder 𝕜] [Zero 𝕜] [Zero E] [Add E] [SMul 𝕜 E]

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.27.4 introduces a direction of recession of an extended-real-valued
  function `f` as a nonzero vector `y` such that every ray profile
  `λ ↦ f (x + λ • y)` is non-increasing for `λ ≥ 0`, starting from every base point
  `x ∈ dom(f)`.
- `core/canonical`: the primitive owner only needs order and top on the codomain so that
  `dom(f)` and the ray inequality are meaningful; this is kept codomain-generic as
  `f : E → β` with `[Preorder β] [Top β]`.
- `bridge/canonical`: the closest existing owner abstraction already present upstream is the
  Chapter 2 recession-cone owner `Function.recessionCone`, applied to the recession function
  `((f)₀⁺)`. However, that owner matches the present source notion canonically only
  under additional convex/proper hypotheses from Theorem 8.6.
- `bridge/view`: the file therefore keeps the textbook predicate as the primitive public owner and
  adds only a thin bridge to `((f)₀⁺).recessionCone` under the stronger
  owner hypotheses `f.IsConvex 𝕜` and `f.IsProper`.

Domain-style sampling used here:
- `Set.RecedesInDirection` from `Chap02/Definition_8_0_1`, which keeps the source-facing nonzero
  direction predicate while delegating the core geometry to `recessionCone`, and makes the scalar
  a core owner parameter because it is not recoverable from the set and the direction;
- `Function.recessionCone` and `Function.mem_recessionCone_iff` from `Chap02/Definiton_8_5_0`;
- `Function.forall_antitone_translate_iff_mem_recessionCone` from
  `Chap02/Theorem_8_6`, giving the convex/proper bridge from linewise monotonicity to
  recession-function nonpositivity.

Primitive data vs derived API:
- primitive source-facing data: the function `f`, the direction `y`, nonzeroness of `y`, and for
  each `x ∈ dom(f)` the canonical order-theoretic owner `AntitoneOn` of the forward ray profile
  `t ↦ f (x + t • y)` on `Set.Ici 0`;
- derived public API: the textbook basepoint inequality `f (x + λ • y) ≤ f x` for `λ ≥ 0`, and
  under convexity/proper hypotheses the canonical bridge to membership in
  `((f)₀⁺).recessionCone`;
- companion bridge: on additive commutative monoids, the same source-facing predicate is
  equivalent to
  antitonicity of every translate profile on the whole scalar line, which feeds directly into
  Theorem 8.6.

Layer target: `source-facing`. The source notion is more general than the Chapter 2 recession
function owner, so the refinement preserves that general source predicate and connects it to the
more specific owner abstraction only when the needed hypotheses are made explicit. As on the set
side, the scalar is a core owner parameter and stays explicit in the public API.
-/

namespace Function

variable (𝕜)

/-- Definition 6.27.4: a nonzero vector `y` is a direction of recession of `f` when every forward
ray profile `λ ↦ f (x + λ • y)` is non-increasing from every base point `x ∈ dom(f)`.

The scalar is a core owner parameter for this notion and cannot be recovered from `f` and `y`, so
the primary owner is scalar-parameterized. The textbook real statement is a specialization. -/
def RecedesInDirection (f : E → β) (y : E) : Prop :=
  y ≠ 0 ∧ ∀ x ∈ dom(f), AntitoneOn (fun t : 𝕜 ↦ f (x + t • y)) (Set.Ici 0)

variable {𝕜}

namespace RecedesInDirection

theorem ne_zero {f : E → β} {y : E} (hy : f.RecedesInDirection 𝕜 y) : y ≠ 0 :=
  hy.1

theorem antitoneOn_translate {f : E → β} {y : E} (hy : f.RecedesInDirection 𝕜 y)
    {x : E} (hx : x ∈ dom(f)) :
    AntitoneOn (fun t : 𝕜 ↦ f (x + t • y)) (Set.Ici 0) :=
  hy.2 x hx

end RecedesInDirection

end Function

end

section

variable {𝕜 : Type v} {E : Type u} {β : Type w}
  [Preorder β] [Top β] [Preorder 𝕜] [Zero 𝕜]
  [AddZeroClass E] [SMulWithZero 𝕜 E]

open scoped Rockafellar

namespace Function

namespace RecedesInDirection

theorem ray_le {f : E → β} {y : E} (hy : f.RecedesInDirection 𝕜 y)
    {x : E} (hx : x ∈ dom(f)) {t : 𝕜} (ht : 0 ≤ t) :
    f (x + t • y) ≤ f x :=
  by
    have hle : f (x + t • y) ≤ f (x + (0 : 𝕜) • y) :=
      (hy.antitoneOn_translate hx) (by simp) ht ht
    simpa [zero_smul, add_zero] using hle

end RecedesInDirection

end Function

end

section

variable {𝕜 : Type v} {E : Type u} {β : Type w}
  [Preorder β] [Top β] [Ring 𝕜] [Preorder 𝕜] [AddRightMono 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]

open scoped Rockafellar

namespace Function

/-- The source-facing recession-direction predicate is exactly nonzeroness together with the
textbook ray inequality. -/
theorem recedesInDirection_iff {f : E → β} {y : E} :
    f.RecedesInDirection 𝕜 y ↔
      y ≠ 0 ∧ ∀ x ∈ dom(f), ∀ t : 𝕜, 0 ≤ t → f (x + t • y) ≤ f x :=
  by
    constructor
    · rintro ⟨hy, hanti⟩
      refine ⟨hy, ?_⟩
      intro x hx t ht
      have hle : f (x + t • y) ≤ f (x + (0 : 𝕜) • y) := hanti x hx (by simp) ht ht
      simpa [zero_smul, add_zero] using hle
    · rintro ⟨hy, hray⟩
      refine ⟨hy, ?_⟩
      intro x hx s hs t ht hst
      have hxs : x + s • y ∈ dom(f) := by
        rw [mem_effectiveDomain]
        exact lt_of_le_of_lt (hray x hx s hs) hx
      have hle := hray (x + s • y) hxs (t - s) (sub_nonneg.mpr hst)
      have hsmul : s • y + (t - s) • y = (s + (t - s)) • y := by
        exact (add_smul s (t - s) y).symm
      have htranslate : x + (s • y + (t - s) • y) = x + t • y := by
        calc
          x + (s • y + (t - s) • y) = x + (s + (t - s)) • y := by rw [hsmul]
          _ = x + t • y := by rw [add_sub_cancel]
      simpa [add_assoc, htranslate] using hle

end Function

end

section

variable {𝕜 : Type v} {E : Type u} {α : Type w}
  [Preorder α] [Ring 𝕜] [Preorder 𝕜] [AddRightMono 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]

open scoped Rockafellar

namespace Function

-- Proof sketch: if `f` recedes in the source-facing sense, then for `s ≤ t` one applies the
-- defining ray inequality at the shifted base point `x + s • y` with step `t - s`. Conversely,
-- antitonicity of every translate profile immediately gives the source ray inequality by setting
-- `s = 0`.
/-- On additive commutative monoids, the source-facing recession-direction predicate is equivalent
to antitonicity of every translate profile on the whole scalar line. -/
theorem recedesInDirection_iff_forall_antitone_translate
    {f : E → WithTopBot α} {y : E} :
    f.RecedesInDirection 𝕜 y ↔
      y ≠ 0 ∧ ∀ x : E, Antitone (fun t : 𝕜 ↦ f (x + t • y)) := by
  constructor
  · rintro ⟨hy, hanti⟩
    refine ⟨hy, ?_⟩
    intro x s t hst
    by_cases hxs : x + s • y ∈ dom(f)
    · have hle := hanti (x + s • y) hxs (by simp) (sub_nonneg.mpr hst) (sub_nonneg.mpr hst)
      have hsmul : s • y + (t - s) • y = (s + (t - s)) • y := by
        exact (add_smul s (t - s) y).symm
      have hleft : x + (s • y + (t - s) • y) = x + t • y := by
        calc
          x + (s • y + (t - s) • y) = x + (s + (t - s)) • y := by rw [hsmul]
          _ = x + t • y := by rw [add_sub_cancel]
      have hright : x + (s • y + (0 : 𝕜) • y) = x + s • y := by simp
      simpa [add_assoc, hleft, hright] using hle
    · rw [mem_effectiveDomain] at hxs
      have hs_top : f (x + s • y) = (⊤ : WithTopBot α) := by
        by_contra hs_top
        have hlt : f (x + s • y) < (⊤ : WithTopBot α) := by
          cases hfx : f (x + s • y) using WithBotTop.rec with
          | bot =>
              simpa [hfx] using (WithBot.bot_lt_coe (⊤ : WithTop α))
          | coe a =>
              simpa [hfx] using (WithBotTop.coe_lt_top a)
          | top =>
              exact False.elim (hs_top hfx)
        exact hxs hlt
      simp [hs_top]
  · rintro ⟨hy, hanti⟩
    refine ⟨hy, ?_⟩
    intro x hx
    exact fun s hs t ht hst ↦ hanti x hst

end Function

end

section

variable {𝕜 : Type v} {E : Type u}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [AddRightMono 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

open scoped Rockafellar

namespace Function

-- Proof sketch: Theorem 8.6 identifies the antitonicity of all translate profiles directly with
-- membership in `((f)₀⁺).recessionCone`.
/-- Under the canonical convex/proper hypotheses, the source-facing recession-direction predicate
is exactly nonzeroness together with membership in the owner recession cone
`((f)₀⁺).recessionCone`. -/
@[simp] theorem recedesInDirection_iff_mem_recessionCone
    {f : E → WithTopBot 𝕜} {y : E}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    f.RecedesInDirection 𝕜 y ↔
      y ∈ ((f)₀⁺).recessionCone ∧ y ≠ 0 := by
  rw [recedesInDirection_iff_forall_antitone_translate]
  constructor
  · rintro ⟨hy, hanti⟩
    exact
      ⟨(forall_antitone_translate_iff_mem_recessionCone
        (f := f) hf_convex hf_proper y).mp hanti, hy⟩
  · rintro ⟨hy_mem, hy⟩
    exact
      ⟨hy, (forall_antitone_translate_iff_mem_recessionCone
        (f := f) hf_convex hf_proper y).mpr hy_mem⟩

namespace RecedesInDirection

/-- Under convex/proper hypotheses, a recession direction belongs to the recession cone of the
recession function. -/
theorem mem_recessionCone
    {f : E → WithTopBot 𝕜} {y : E}
    (hy : f.RecedesInDirection 𝕜 y)
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    y ∈ ((f)₀⁺).recessionCone := by
  exact ((recedesInDirection_iff_mem_recessionCone
    (f := f) (y := y) hf_convex hf_proper).mp hy).1

/-- Under convex/proper hypotheses, nonzero membership in `((f)₀⁺).recessionCone` gives a
source-facing recession direction. -/
theorem of_mem_recessionCone
    {f : E → WithTopBot 𝕜} {y : E}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hy_ne : y ≠ 0) (hy_mem : y ∈ ((f)₀⁺).recessionCone) :
    f.RecedesInDirection 𝕜 y := by
  exact (recedesInDirection_iff_mem_recessionCone
    (f := f) (y := y) hf_convex hf_proper).mpr ⟨hy_mem, hy_ne⟩

end RecedesInDirection

end Function

end
