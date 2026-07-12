import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Prop_4_4_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_3
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_7_2

-- Declarations for this item will be appended below by the statement pipeline.

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
