import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_7_2_1 (from Chap02) -/
section

open scoped Rockafellar

variable {𝕜 E : Type*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 7.2.1 says that a lower semicontinuous improper convex function
  cannot take any finite value.
- `core/canonical`: the owner predicates already present in the project are
  `LowerSemicontinuous`, `Function.IsConvex`, and `Function.IsProper` for `WithTopBot 𝕜`-valued
  functions, together with the effective-domain owner `dom(·)` and Theorem 7.2 for the `⊥` locus
  on `ri[𝕜](dom f)`.
  The existing owner bridge `mem_effectiveDomain` already identifies `x ∈ dom(f)` with
  `f x < ⊤`.
- `bridge/view`: this corollary closes the gap from Theorem 7.2 by extending the `⊥` conclusion
  from `ri (dom f)` to all of `dom(f)` via lower semicontinuity.
- primitive inputs: the function `f : E → WithTopBot 𝕜` with owner hypotheses
  `LowerSemicontinuous`, `Function.IsConvex 𝕜 f`, and the source-facing improperness hypothesis
  `¬ f.IsProper`.
- derived API: once the direct conclusion `f x = ⊥` is known on `dom(f)`, any reformulation using
  `mem_effectiveDomain` is companion-level API rather than the main corollary surface.
- Layer target: this item remains `source-facing`, but it is refined to a thin corollary-level
  consequence of the existing Chapter 7 owner theorem rather than an independent local owner. The
  corollary surface itself is attached to the convexity owner namespace `Function.IsConvex` as the
  direct owner theorem, rather than as a parallel `↔` wrapper around `mem_effectiveDomain`.

Mathlib/project sampling used here:
- `LowerSemicontinuous` from `Mathlib/Topology/Semicontinuity/Defs.lean`;
- the chapter owner predicate `Function.IsConvex` from `Theorem_4_2`;
- the chapter properness owner `Function.IsProper` from `Definition_4_6`;
- the chapter effective-domain owner `dom(·)` and `Function.IsConvex.convex_dom`;
- `Function.IsConvex.eq_bot_of_mem_riDom` from `Theorem_7_2`;
- `Convex.intrinsicClosure_ri_eq_intrinsicClosure` from `Theorem_6_3`;
- `LowerSemicontinuous.isClosed_preimage` from mathlib's semicontinuity API.
-/

-- Proof sketch: Theorem 7.2 gives `f = ⊥` on `riDom[𝕜](f)`. Lower semicontinuity turns this into a
-- closure theorem on `closure (riDom[𝕜](f))`: for any scalar `r` strictly below `f x`, the closed
-- sublevel set `{y | f y ≤ r}` contains `riDom[𝕜](f)` because there `f = ⊥ ≤ r`; closedness then
-- forces `f x ≤ r`, a contradiction. This yields the primitive intrinsic-closure owner theorem on
-- `intrinsicClosure 𝕜 (riDom[𝕜](f))`; the source-facing `intrinsicClosure 𝕜 dom(f)`/`dom(f)` forms
-- are then thin bridges using Theorem 6.3 and `subset_intrinsicClosure`.
namespace Function.IsConvex

variable {f : E → WithTopBot 𝕜}

section Core

variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Corollary 7.2.1, primitive intrinsic-closure form: a lower semicontinuous improper convex
function takes the value `⊥` at every point of `intrinsicClosure 𝕜 (riDom[𝕜](f))`. -/
theorem eq_bot_of_mem_intrinsicClosure_riDom_of_lowerSemicontinuous
    (hf : f.IsConvex 𝕜) (hf_lsc : LowerSemicontinuous f)
    (hf_not_proper : ¬ f.IsProper) {x : E}
    (hx : x ∈ intrinsicClosure 𝕜 (riDom[𝕜](f))) :
    f x = ⊥ := by
  have hx_closure : x ∈ closure (riDom[𝕜](f)) := intrinsicClosure_subset_closure hx
  by_contra hfx
  have hrx : ∃ r : 𝕜, (r : WithTopBot 𝕜) < f x := by
    by_cases htop : f x = ⊤
    · refine ⟨0, ?_⟩
      simpa [htop] using (WithTopBot.coe_lt_top (0 : 𝕜))
    · lift f x to 𝕜 using ⟨htop, hfx⟩ with s hs
      refine ⟨s - 1, ?_⟩
      simpa [hs] using (WithTopBot.coe_lt_coe_iff.mpr (sub_lt_self s zero_lt_one))
  rcases hrx with ⟨r, hrx⟩
  let sublevel : Set E := f ⁻¹' Set.Iic (r : WithTopBot 𝕜)
  have hri_subset : riDom[𝕜](f) ⊆ sublevel := by
    intro y hy
    have hy_bot :
        f y = ⊥ :=
      hf.eq_bot_of_mem_riDom hf_not_proper hy
    simp [sublevel, hy_bot]
  have hclosed : IsClosed sublevel := by
    simpa [sublevel] using hf_lsc.isClosed_preimage (r : WithTopBot 𝕜)
  have hfx_le : f x ≤ (r : WithTopBot 𝕜) :=
    (hclosed.closure_subset_iff.mpr hri_subset) hx_closure
  exact not_lt_of_ge hfx_le hrx

end Core

section FiniteDimensionalBridge

variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Corollary 7.2.1, intrinsic-closure form: a lower semicontinuous improper convex function takes
the value `⊥` at every point of the intrinsic closure of its effective domain, so in particular it
has no finite values on `dom(f)`. -/
theorem eq_bot_of_mem_intrinsicClosure_dom_of_lowerSemicontinuous
    (hf : f.IsConvex 𝕜) (hf_lsc : LowerSemicontinuous f)
    (hf_not_proper : ¬ f.IsProper) {x : E} (hx : x ∈ intrinsicClosure 𝕜 dom(f)) :
    f x = ⊥ := by
  have hdom_convex : Convex 𝕜 dom(f) := hf.convex_dom
  have hriClosure :
      intrinsicClosure 𝕜 (riDom[𝕜](f)) = intrinsicClosure 𝕜 dom(f) := by
    simpa [riDom_eq_intrinsicInterior_dom] using
      hdom_convex.intrinsicClosure_ri_eq_intrinsicClosure
  have hx_riClosure : x ∈ intrinsicClosure 𝕜 (riDom[𝕜](f)) := by
    exact hriClosure.symm ▸ hx
  exact hf.eq_bot_of_mem_intrinsicClosure_riDom_of_lowerSemicontinuous hf_lsc
    hf_not_proper hx_riClosure

/-- Corollary 7.2.1, `dom` bridge: a lower semicontinuous improper convex function
takes the value `⊥` at every point of its effective domain. -/
theorem eq_bot_of_mem_dom_of_lowerSemicontinuous
    (hf : f.IsConvex 𝕜) (hf_lsc : LowerSemicontinuous f)
    (hf_not_proper : ¬ f.IsProper) {x : E} (hx : x ∈ dom(f)) :
    f x = ⊥ := by
  exact hf.eq_bot_of_mem_intrinsicClosure_dom_of_lowerSemicontinuous hf_lsc
    hf_not_proper (subset_intrinsicClosure hx)

end FiniteDimensionalBridge

end Function.IsConvex

end

/-! ### Corollary_7_2_2 (from Chap02) -/
section

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 7.2.2 says that the closure of an improper convex function is again a
  closed improper convex function and agrees with the original function on `ri (dom f)`.
- `core/canonical`: the owner predicates already fixed in the chapter are `Function.IsConvex 𝕜`,
  `LowerSemicontinuous`, `Function.IsProper`, and Rockafellar's chapter closure owner `cl(·)`.
- `bridge/view`: Rockafellar's `ri (dom f)` is represented by the scalar-parameterized chapter
  notation `riDom[𝕜](f)`, and agreement there is expressed by `Set.EqOn`; Text 7.0.15 already
  supplies the owner-level `riDom` bridge for `cl(f)`.

Domain-style sampling used here:
- the lower-semicontinuous hull owner `cl(·)` and the owner theorem
  `lowerSemicontinuous_lowerSemicontinuousHull` from `Text_7_0_4`;
- `Function.isConvex_verticalInfimum` from `Theorem_5_3`, which is the owner theorem for
  convexity of functions built from epigraph sets;
- the properness owner `Function.IsProper` from `Definition_4_6`;
- `Function.not_isProper_iff` from `Definition_4_7`;
- Text 7.0.15 in the owner form
  `Function.IsConvex.cl_eqOn_riDom_of_not_isProper`.

Primitive data vs derived API:
- primitive data: an extended-codomain function `f : E → WithBotTop 𝕜`, together with the chapter
  owner `cl(f)`;
- source-facing extra hypotheses: convexity of `f` and, only where genuinely needed, the
  improperness hypothesis `¬ f.IsProper`;
- derived outputs: convexity and lower semicontinuity of `cl(f)`, failure of properness for that
  closure, and agreement with `f` on `riDom[𝕜](f)`.

Layer target: clause (1) and clause (3) are `source-facing` consequences on the chapter owner
`cl(f)`; clause (2) is `core/canonical`, since lower semicontinuity is an owner property of
`cl(f)` itself and does not use the source's extra convex/improper hypotheses; clause (4) is
`bridge/view`, and is reused directly from `Text_7_0_15` rather than restated through a duplicate
local wrapper.
-/

section Convexity

variable {𝕜 E : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [IsTopologicalAddGroup 𝕜] [ContinuousConstSMul 𝕜 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
variable {f : E → WithBotTop 𝕜}

namespace Function.IsConvex

variable {f : E → WithBotTop 𝕜}

-- Proof sketch: `cl(f)` is by definition the vertical infimum attached to `closure (epi f)`, and
-- convexity of `epi f` passes to its closure. The source's improperness hypothesis is redundant
-- for this owner-level convexity consequence and is removed from the statement.
/-- Corollary 7.2.2 (1), owner form: the chapter closure `cl(f)` of a convex function is convex. -/
theorem lowerSemicontinuousHull_isConvex
    (hf : f.IsConvex 𝕜) :
    (cl(f)).IsConvex 𝕜 := by
  simpa [lowerSemicontinuousHull] using
    Function.isConvex_verticalInfimum (hf.convex_epi.closure)

end Function.IsConvex

end Convexity

/- Corollary 7.2.2 (2): this is exactly the canonical `cl(·)` lower-semicontinuity owner theorem
from `Text_7_0_4`. -/
recall lowerSemicontinuous_lowerSemicontinuousHull

/- Corollary 7.2.2 (4): this is exactly the owner theorem from `Text_7_0_15`. -/
recall Function.IsConvex.cl_eqOn_riDom_of_not_isProper

section Properness

variable {𝕜 E : Type*}
variable [TopologicalSpace E]
variable [ConditionallyCompleteLattice 𝕜] [TopologicalSpace 𝕜] [NoBotOrder 𝕜]
variable {f : E → WithBotTop 𝕜}

namespace Function

variable {f : E → WithBotTop 𝕜}

-- Proof sketch: if `f` already attains `⊥`, then `cl(f) ≤ f` gives the same bottom value for
-- `cl(f)`. If `dom(f) = ∅`, then `epi f = ∅`, hence
-- `epi (cl(f)) = closure (epi f) = ∅`, so `dom(cl(f)) = ∅` as well.
/-- Corollary 7.2.2 (3), owner form: if `f` is improper, then `cl(f)` is improper. The source's
convexity hypothesis is redundant for this owner-level persistence statement. -/
theorem lowerSemicontinuousHull_not_isProper_of_not_isProper
    (hf_not_proper : ¬ f.IsProper) :
    ¬ (cl(f)).IsProper := by
  rw [Function.not_isProper_iff]
  rw [Function.not_isProper_iff] at hf_not_proper
  rcases hf_not_proper with hdom_not_nonempty | ⟨x, hx⟩
  · left
    have hdom_empty : dom(f) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hdom_not_nonempty
    have hepi_empty : epi f = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro ⟨y, μ⟩ hy
      have hy_dom : y ∈ dom(f) := by
        exact lt_of_le_of_lt (by simpa [mem_epi_iff] using hy) (WithBotTop.coe_lt_top μ)
      simp [hdom_empty] at hy_dom
    calc
      dom(cl(f)) = Prod.fst '' closure (epi f) := by
        simpa [lowerSemicontinuousHull] using
          Function.effectiveDomain_verticalInfimum_eq_image_fst (closure (epi f))
      _ = ∅ := by simp [hepi_empty]
  · right
    refine ⟨x, ?_⟩
    exact le_bot_iff.mp <| by
      simpa [hx] using (lowerSemicontinuousHull_le f x)

end Function

end Properness

end

/-! ### Theorem_7_2 (from Chap02) -/
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
  simpa using (WithBotTop.eq_bot_iff_forall_lt (x := x))

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
      lift g y to 𝕜 using ⟨hy_top, hy_bot⟩ with β hfy
      exact ⟨β, by simp [hfy]⟩
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
      have hconv : Convex 𝕜 (epi g) := hg_convex.convex_epi
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

/-! ### Corollary_7_2_3 (from Chap02) -/
section

open scoped Rockafellar

variable {𝕜 E : Type*}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 7.2.3 gives a dichotomy for a convex function whose effective domain
  is relatively open.
- `core/canonical`: the owner abstractions already fixed upstream in this chapter are
  `Function.IsConvex`, `Function.IsProper`, `IsRelativelyOpen`, and the effective-domain owners
  `dom(·)` / `riDom[𝕜](·)`.
- `bridge/view`: relative openness is converted to the owner equality
  `riDom[𝕜](f) = dom(f)` via `IsRelativelyOpen`, while the textbook
  phrase "f(x) is infinite" is rendered pointwise as `f x = ⊥ ∨ f x = ⊤`.

Domain-style sampling used here:
- the chapter owner predicate `Function.IsConvex`;
- the owner effective-domain notation `dom(·)`;
- the chapter relative-interior notation `riDom[𝕜](·)`;
- the chapter properness owner `Function.IsProper` and the consequence `Function.IsProper.bot_lt`;
- the chapter source-facing predicate `IsRelativelyOpen 𝕜`;
- Theorem 7.2 in its owner form
  `Function.IsConvex.eq_bot_of_mem_riDom`.

Primitive data vs derived API:
- primitive inputs: the function `f`, the owner convexity hypothesis `Function.IsConvex 𝕜 f`, and
  the owner equality `riDom[𝕜](f) = dom(f)`;
- source-facing bridge input: the relative-openness hypothesis `IsRelativelyOpen 𝕜` on `dom(f)`,
  which is definitionally this owner equality;
- canonical owner conclusion: either `f` is everywhere strictly above `⊥`, or
  `f x = ⊥ ↔ x ∈ dom(f)` pointwise on the effective-domain owner;
- derived source-style conclusion: every value is an infinite endpoint of `WithBotTop 𝕜`.
- Layer target: this item is `source-facing`, but it is expressed directly through the chapter's
  owner predicates and effective-domain notation rather than through duplicate raw
  `intrinsicInterior 𝕜 dom(f)` / `{x | f x < ⊤}` presentations.
-/

-- Proof sketch: split on properness. In the proper case, proper functions are everywhere strictly
-- above `⊥` by `Function.IsProper.bot_lt`. In the improper case, `IsRelativelyOpen` turns the
-- relative-openness hypothesis into `riDom[𝕜](f) = dom(f)`, so Theorem 7.2
-- yields `f x = ⊥` on the effective domain. Outside the effective domain one has `f x = ⊤`, since
-- nonmembership in `dom(f)` is exactly `¬ f x < ⊤`, hence every value is infinite.
namespace Function.IsConvex

variable {f : E → WithBotTop 𝕜}

-- Bridge lemma: this is the intrinsic-equality expansion of the source-facing
-- `IsRelativelyOpen 𝕜 dom(f)` hypothesis.
private theorem all_gt_bot_or_eq_bot_iff_mem_dom_of_riDom_eq_dom
    (hf_convex : f.IsConvex 𝕜) (hriDom_eq : riDom[𝕜](f) = dom(f)) :
    (∀ x, ⊥ < f x) ∨ (∀ x, f x = ⊥ ↔ x ∈ dom(f)) := by
  by_cases hproper : f.IsProper
  · exact Or.inl hproper.bot_lt
  · refine Or.inr ?_
    intro x
    constructor
    · intro hxb
      simp [mem_effectiveDomain, hxb]
    · intro hx
      exact hf_convex.eq_bot_of_mem_riDom hproper <| by
        simpa [hriDom_eq] using hx

/-! Corollary 7.2.3 in source-facing relatively-open owner form:
`IsRelativelyOpen 𝕜 dom(f)` is the public hypothesis surface, and the
`riDom[𝕜](f) = dom(f)` equality is used only as an internal bridge. -/

/-- Corollary 7.2.3, relatively-open owner form with effective-domain branch:
either `f` is everywhere strictly above `⊥`, or `f x = ⊥` holds exactly on `dom(f)`. -/
theorem all_gt_bot_or_eq_bot_iff_mem_dom
    (hf_convex : f.IsConvex 𝕜) (hdom_open : IsRelativelyOpen 𝕜 dom(f)) :
    (∀ x, ⊥ < f x) ∨ (∀ x, f x = ⊥ ↔ x ∈ dom(f)) := by
  exact all_gt_bot_or_eq_bot_iff_mem_dom_of_riDom_eq_dom hf_convex <| by
    simpa [IsRelativelyOpen] using hdom_open

/-- Corollary 7.2.3: if a convex function has relatively open effective domain, for instance if
`dom(f) = Set.univ`, then either it is everywhere strictly above `⊥` or every value is
infinite, i.e. equal to `⊥` or `⊤` in the `WithBotTop 𝕜` codomain. -/
theorem all_gt_bot_or_all_infinite
    (hf_convex : f.IsConvex 𝕜) (hdom_open : IsRelativelyOpen 𝕜 dom(f)) :
    (∀ x, ⊥ < f x) ∨ (∀ x, f x = ⊥ ∨ f x = ⊤) := by
  rcases hf_convex.all_gt_bot_or_eq_bot_iff_mem_dom hdom_open with hgt | hbot
  · exact Or.inl hgt
  · refine Or.inr ?_
    intro x
    by_cases hx : x ∈ dom(f)
    · exact Or.inl ((hbot x).2 hx)
    · refine Or.inr ?_
      exact top_unique <| not_lt.mp <| by
        simpa [mem_effectiveDomain] using hx

end Function.IsConvex

end
