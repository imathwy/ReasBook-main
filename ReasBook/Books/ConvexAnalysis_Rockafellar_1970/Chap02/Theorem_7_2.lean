import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_10

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 E : Type*}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 7.2 states that an improper convex function takes the value `-∞` at
  every point of the relative interior of its effective domain.
- `core/canonical`: the owner abstractions already fixed earlier in the project are
  `Function.IsConvex`, `Function.IsProper`, the chapter effective-domain owners `dom(·)` and
  `riDom[𝕜](·)`, and the canonical relative-boundary owner with chapter notation `rb[𝕜](·)`.
- `bridge/view`: Rockafellar's `ri (dom f)` and relative boundary of `dom f` are represented by
  `riDom[𝕜](f)` and `rb[𝕜](dom(f))`.

Domain-style sampling used here:
- the chapter owner predicate `Function.IsConvex` from `Theorem_4_2`;
- the chapter properness owner `Function.IsProper` from `Definition_4_6`;
- the chapter effective-domain owner `dom(·)` from `Definition_4_4`;
- the epigraph bridge `Function.isConvex_iff_convex_epigraph`;
- the relative-interior/relative-boundary theorem surface notation `riDom[𝕜](·)` and `rb[𝕜](·)`.

Primitive data vs derived API:
- primitive inputs: the function `f : E → WithTopBot 𝕜` together with the owner predicates
  `Function.IsConvex 𝕜 f` and explicit bottom-attainment data `∃ u, f u = ⊥`;
- derived conclusions: the `-∞` value on the relative interior of `dom(f)` and the resulting
  relative-boundary localization of finite domain points.
- Layer target: this item is `source-facing`, expressed through the chapter owner predicates rather
  than the raw epigraph/properness encoding or a duplicate local effective-domain presentation.
  The source-facing `¬ f.IsProper` form is retained as a thin wrapper over the primitive
  bottom-attainment layer.
-/

namespace Function.IsConvex

open AffineMap

variable {f : E → WithTopBot 𝕜}

private theorem withTopBot_eq_bot_iff_forall_lt (x : WithTopBot 𝕜) :
    x = ⊥ ↔ ∀ y : 𝕜, x < (y : WithTopBot 𝕜) := by
  induction x using WithTop.recTopCoe with
  | top =>
      constructor
      · intro h
        exact (WithTop.top_ne_coe h).elim
      · intro h
        have ht := h 0
        exact (WithTop.not_top_le_coe _ (le_of_lt ht)).elim
  | coe x =>
      induction x using WithBot.recBotCoe with
      | bot =>
          constructor
          · intro _ y
            exact WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe y)
          · intro _
            rfl
      | coe a =>
          constructor
          · intro h
            exact (WithBot.coe_ne_bot (WithTop.coe_injective h)).elim
          · intro h
            exact (lt_irrefl _ (h a)).elim

/-- Primitive-data form of Theorem 7.2: if `f` is convex and attains `⊥` somewhere, then
`f x = -∞` for every `x ∈ riDom[𝕜](f)`. -/
-- Proof sketch: the set `dom(f)` is convex because it is the strict sublevel set
-- `{y | f y < (⊤ : WithTopBot 𝕜)}` of the convex function `f`.
-- Bottom-attainment yields a point `u` in that
-- domain with `f u = ⊥`. For `x ∈ riDom[𝕜](f)`, apply Theorem 6.4 to the
-- convex domain to obtain `y` in the domain and `μ > 1` with `y = (1 - μ) • u + μ • x`. Then
-- write `x` as a strict convex combination of `u` and `y`, use convexity of the epigraph with
-- the endpoint value `f u = ⊥` to get affine upper bounds on `f x` at every scalar height, and
-- conclude `f x = ⊥`.
private theorem eq_bot_of_mem_riDom_of_exists_eq_bot_core
    {g : E → WithTopBot 𝕜}
    (hg_convex : g.IsConvex 𝕜)
    (hbot : ∃ u : E, g u = ⊥)
    {x : E} (hx : x ∈ riDom[𝕜](g)) :
    g x = ⊥ := by
  by_contra hfx
  rcases hbot with ⟨u, hu_eq_bot⟩
  have hu_dom : u ∈ dom(g) := by
    rw [mem_effectiveDomain, hu_eq_bot]
    exact bot_lt_top
  rcases Convex.forall_exists_gt_one_lineMap_mem_of_mem_intrinsicInterior hx u hu_dom with
      ⟨μ, hμ, hy_dom'⟩
  let y := lineMap u x μ
  have hy_dom : y ∈ dom(g) := by
    simpa [y] using hy_dom'
  have hβ : ∃ β : 𝕜, g y ≤ β := by
    by_cases hy_bot : g y = ⊥
    · refine ⟨0, ?_⟩
      simp [hy_bot]
    · have hy_top : g y ≠ ⊤ := (mem_effectiveDomain.mp hy_dom).ne
      induction hfy : g y using WithTop.recTopCoe with
      | top => exact (hy_top hfy).elim
      | coe z =>
          induction z using WithBot.recBotCoe with
          | bot => exact (hy_bot hfy).elim
          | coe β => exact ⟨β, by simp [hfy]⟩
  rcases hβ with ⟨β, hy_le⟩
  have hμ0 : 0 < μ := lt_trans zero_lt_one hμ
  have ht0 : 0 < μ⁻¹ := inv_pos.mpr hμ0
  have ht1 : μ⁻¹ < 1 := by
    rw [inv_lt_one₀]
    · linarith
    · linarith
  have hx_le : ∀ r : 𝕜, g x ≤ r := by
    intro r
    let α : 𝕜 := (μ * r - β) / (μ - 1)
    have hμ_ne : μ ≠ 0 := hμ0.ne'
    have hμ1 : μ - 1 ≠ 0 := sub_ne_zero.mpr hμ.ne.symm
    have hxy :
        g ((1 - μ⁻¹) • u + μ⁻¹ • y) ≤ ((1 - μ⁻¹) * α + μ⁻¹ * β : 𝕜) := by
      have hu_epi : (u, α) ∈ epi g := by
        exact mem_epi_iff.2 (by simp [hu_eq_bot])
      have hy_epi : (y, β) ∈ epi g := mem_epi_iff.2 hy_le
      have hconv : Convex 𝕜 (epi g) := by
        simpa [epi_univ_eq_setOf_le] using hg_convex.convex_epigraph
      have hmem : (1 - μ⁻¹) • (u, α) + μ⁻¹ • (y, β) ∈ epi g :=
        hconv hu_epi hy_epi (sub_nonneg.mpr ht1.le) ht0.le (by ring)
      simpa [smul_eq_mul] using (mem_epi_iff.1 hmem)
    have hx_repr : (1 - μ⁻¹) • u + μ⁻¹ • y = x := by
      calc
        (1 - μ⁻¹) • u + μ⁻¹ • y = lineMap u y μ⁻¹ := by
          simp [lineMap_apply_module]
        _ = lineMap u x (μ⁻¹ * μ) := by
          simp [y]
        _ = lineMap u x (1 : 𝕜) := by
          rw [inv_mul_cancel₀ hμ_ne]
        _ = x := lineMap_apply_one u x
    have hr : ((1 - μ⁻¹) * α + μ⁻¹ * β : 𝕜) = r := by
      dsimp [α]
      have hα_eq : (μ - 1) * ((μ * r - β) / (μ - 1)) = μ * r - β := by
        field_simp [hμ1]
      have hfac : 1 - μ⁻¹ = (μ - 1) * μ⁻¹ := by
        field_simp [hμ_ne]
      calc
        ((1 - μ⁻¹) * ((μ * r - β) / (μ - 1)) + μ⁻¹ * β : 𝕜)
            = ((μ - 1) * μ⁻¹) * ((μ * r - β) / (μ - 1)) + μ⁻¹ * β := by rw [hfac]
        _ = μ⁻¹ * ((μ - 1) * ((μ * r - β) / (μ - 1))) + μ⁻¹ * β := by ring
        _ = μ⁻¹ * (μ * r - β) + μ⁻¹ * β := by rw [hα_eq]
        _ = μ⁻¹ * (μ * r) := by ring
        _ = r := by rw [← mul_assoc, inv_mul_cancel₀ hμ_ne, one_mul]
    simpa [hx_repr, hr] using hxy
  have hx_lt : ∀ r : 𝕜, g x < r := by
    intro r
    exact lt_of_le_of_lt (hx_le (r - 1))
      (by
        change
          (((r - 1 : 𝕜) : WithBot 𝕜) : WithTop (WithBot 𝕜)) <
            (((r : 𝕜) : WithBot 𝕜) : WithTop (WithBot 𝕜))
        exact WithTop.coe_lt_coe.mpr <| WithBot.coe_lt_coe.mpr <| sub_lt_self r zero_lt_one)
  exact hfx ((withTopBot_eq_bot_iff_forall_lt (x := g x)).2 hx_lt)

theorem eq_bot_of_mem_riDom_of_exists_eq_bot
    (hf_convex : f.IsConvex 𝕜)
    (hbot : ∃ u : E, f u = ⊥)
    {x : E} (hx : x ∈ riDom[𝕜](f)) :
    f x = ⊥ := by
  exact eq_bot_of_mem_riDom_of_exists_eq_bot_core hf_convex hbot hx

/-- Theorem 7.2: if `f` is an improper convex function, then `f x = -∞` for every
`x ∈ riDom[𝕜](f)`. -/
theorem eq_bot_of_mem_riDom
    (hf_convex : f.IsConvex 𝕜)
    (hf_not_proper : ¬ f.IsProper)
    {x : E} (hx : x ∈ riDom[𝕜](f)) :
    f x = ⊥ := by
  have hdom_nonempty : dom(f).Nonempty := ⟨x, intrinsicInterior_subset hx⟩
  rcases (Function.not_isProper_iff_exists_eq_bot_of_nonempty_dom (f := f) hdom_nonempty).1
      hf_not_proper with ⟨u, hu_eq_bot⟩
  exact hf_convex.eq_bot_of_mem_riDom_of_exists_eq_bot ⟨u, hu_eq_bot⟩ hx

/-- If `f` is improper and convex, every point where `f` is not `⊥` lies outside `riDom[𝕜](f)`. -/
theorem not_mem_riDom_of_ne_bot
    (hf_convex : f.IsConvex 𝕜)
    (hf_not_proper : ¬ f.IsProper)
    {x : E} (hx_ne_bot : f x ≠ ⊥) :
    x ∉ riDom[𝕜](f) := by
  intro hx_ri
  exact hx_ne_bot (hf_convex.eq_bot_of_mem_riDom hf_not_proper hx_ri)

/-- If an improper convex function is finite at a point of its effective domain, that point lies
in `rb[𝕜](dom(f))`. -/
-- Proof sketch: a point of the effective domain is automatically in its intrinsic closure. If it
-- were in the relative interior, the main theorem would force the value there to be `⊥`,
-- contradicting the hypothesis `f x ≠ ⊥`. Hence the point lies in
-- `intrinsicClosure 𝕜 (dom f) \ intrinsicInterior 𝕜 (dom f)`, i.e. in `rb[𝕜](dom(f))`.
theorem mem_rb_dom_of_ne_bot
    (hf_convex : f.IsConvex 𝕜)
    (hf_not_proper : ¬ f.IsProper)
    {x : E} (hx_dom : x ∈ dom(f)) (hx_ne_bot : f x ≠ ⊥) :
    x ∈ rb[𝕜](dom(f)) := by
  have hx_frontier : x ∈ intrinsicClosure 𝕜 dom(f) \ riDom[𝕜](f) := by
    refine ⟨subset_intrinsicClosure hx_dom, ?_⟩
    exact hf_convex.not_mem_riDom_of_ne_bot hf_not_proper hx_ne_bot
  have hrb :
      intrinsicClosure 𝕜 dom(f) \ riDom[𝕜](f) = rb[𝕜](dom(f)) :=
    intrinsicClosure_diff_intrinsicInterior dom(f)
  exact hrb ▸ hx_frontier

end Function.IsConvex

end
