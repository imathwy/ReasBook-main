import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open Bornology Function

variable {𝕜 E : Type*}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [ClosedIicTopology 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 17.2.1 starts from a nonempty closed bounded set `S` and a
  continuous `𝕜`-valued function on `S`, extends that function by `+∞` off `S`, and asserts that
  the convex hull of the extension is a closed proper convex function.
- `core/canonical`: the owner abstractions already present upstream are `Function.convexHull` for
  Rockafellar's `conv`, the canonical extension owner `Function.toWithTopBotOn`, and the bundled
  predicate `Function.IsClosedProperConvex`.
- `bridge/view`: the source's extension by `+∞` off `S` is exactly the canonical function
  `f.toWithTopBotOn S`, so the corollary should be stated directly on that owner
  expression rather than by introducing a parallel local wrapper for the extension or for the
  closed/proper/convex package.

Domain-style sampling used here:
- `Function.convexHull` from `Chap01.Text_5_5_1`;
- `Function.toWithTopBotOn` from `Chap01.Remark_4_4_5`;
- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`;
- `Metric.isCompact_iff_isClosed_bounded` for the closed-bounded-to-compact bridge in proper
  pseudo-metric spaces.

Primitive data vs derived API:
- primitive source data: the set `S` and the `𝕜`-valued branch `f`;
- intrinsic compactness owner datum: `IsCompact S` for the relative topology of `S`;
- canonical bridge data: the ambient extension `f.toWithTopBotOn S`;
- explicit closedness bridge datum: `LowerSemicontinuous (conv(f.toWithTopBotOn S))`;
- derived API: the closed/proper/convex conclusion for the same convex-hull owner.

Layer target: `core/canonical` for the primary theorem (`IsCompact` surface), plus a thin
`source-facing` bridge theorem that recovers the closed-and-bounded hypotheses through compactness
of proper pseudo-metric spaces.
-/

-- Proof sketch: use `hS_nonempty` to get one finite value of `f.toWithTopBotOn S`, and use
-- compactness plus continuity to get a global lower bound on `f` over `S`; this lower bound
-- controls the vertical infimum defining `conv(f.toWithTopBotOn S)`, yielding non-`⊥` values.
-- Convexity comes from `Function.isConvex_conv`, and closedness is the explicit bridge hypothesis
-- `hconv_closed`.
/-- Intrinsic compact-set owner form of Corollary 17.2.1: if `S` is nonempty compact and `f` is
continuous on `S` and `conv(f.toWithTopBotOn S)` is lower semicontinuous, then the convex hull of
the canonical extension `f.toWithTopBotOn S` is a closed proper convex function. -/
theorem conv_toWithTopBotOn_isClosedProperConvex_of_nonempty_of_isCompact
    [TopologicalSpace E] [AddCommMonoid E] [Module 𝕜 E]
    {S : Set E} {f : E → 𝕜} (hS_nonempty : S.Nonempty) (hS_compact : IsCompact S)
    (hf : ContinuousOn f S)
    (hconv_closed : LowerSemicontinuous (conv(f.toWithTopBotOn S))) :
    IsClosedProperConvex[𝕜] (conv(f.toWithTopBotOn S)) := by
  let g : E → WithTopBot 𝕜 := f.toWithTopBotOn S
  refine ⟨Function.isConvex_conv g, ?_, ?_⟩
  · rw [Function.isProper_iff]
    refine ⟨?_, ?_⟩
    · rcases hS_nonempty with ⟨x0, hx0⟩
      refine ⟨x0, ?_⟩
      rw [mem_effectiveDomain]
      have hx0_epi : (x0, f x0) ∈ epi g := by
        exact (mem_epi_iff).2 (le_of_eq (by simpa [g] using Function.toWithTopBotOn_of_mem f S hx0))
      have hx0_convexEpi : (x0, f x0) ∈ _root_.convexHull 𝕜 (epi g) :=
        subset_convexHull 𝕜 (epi g) hx0_epi
      have hle : conv(g) x0 ≤ (f x0 : WithTopBot 𝕜) := by
        rw [Function.convexHull_eq_verticalInfimum_convexHull_epigraph]
        exact Function.verticalInfimum_le_of_mem hx0_convexEpi
      have hfx_lt_top : (f x0 : WithTopBot 𝕜) < ⊤ := by
        exact lt_top_iff_ne_top.2 (by simp)
      exact lt_of_le_of_lt hle hfx_lt_top
    · rcases hS_compact.exists_isMinOn hS_nonempty hf with ⟨xmin, hxminS, hxmin⟩
      let m : 𝕜 := f xmin
      have hxmin_le : ∀ y ∈ S, f xmin ≤ f y := by
        simpa [IsMinOn, IsMinFilter, Filter.Eventually, Filter.mem_principal] using hxmin
      have hsubset_const : epi g ⊆ epi (fun _ : E ↦ ((m : 𝕜) : WithTopBot 𝕜)) := by
        intro p hp
        have hp_le : g p.1 ≤ (p.2 : WithTopBot 𝕜) := (mem_epi_iff).1 hp
        have hp_mem_S : p.1 ∈ S := by
          by_contra hp_not_mem_S
          have hp_top : g p.1 = (⊤ : WithTopBot 𝕜) := by
            simpa [g] using Function.toWithTopBotOn_of_notMem f S hp_not_mem_S
          have hp_le_top : (⊤ : WithTopBot 𝕜) ≤ (p.2 : WithTopBot 𝕜) := by
            rw [← hp_top]
            exact hp_le
          have hp2_eq_top : (p.2 : WithTopBot 𝕜) = ⊤ := (top_le_iff).1 hp_le_top
          exact (WithTopBot.coe_ne_top p.2) hp2_eq_top
        have hm_le_fx : (m : WithTopBot 𝕜) ≤ (f p.1 : WithTopBot 𝕜) := by
          exact (WithTopBot.coe_le_coe).2 (by simpa [m] using hxmin_le p.1 hp_mem_S)
        have hfx_eq : (f p.1 : WithTopBot 𝕜) = g p.1 := by
          simpa [g] using (Function.toWithTopBotOn_of_mem f S hp_mem_S).symm
        exact (mem_epi_iff).2 (le_trans (hfx_eq ▸ hm_le_fx) hp_le)
      have hconst_convex : Convex 𝕜 (epi (fun _ : E ↦ ((m : 𝕜) : WithTopBot 𝕜))) := by
        have hconst_convexOn : ConvexOn 𝕜 (Set.univ : Set E) (fun _ : E ↦ m) :=
          Function.convexOn_univ_const (𝕜 := 𝕜) (E := E) m
        simpa using
          (Function.isConvex_coe_of_convexOn_univ
            (𝕜 := 𝕜) (E := E) (β := 𝕜) hconst_convexOn)
      have hsubset_convexEpi :
          _root_.convexHull 𝕜 (epi g) ⊆ epi (fun _ : E ↦ ((m : 𝕜) : WithTopBot 𝕜)) := by
        exact convexHull_min hsubset_const hconst_convex
      have hm_le_conv : (fun _ : E ↦ ((m : 𝕜) : WithTopBot 𝕜)) ≤ conv(g) := by
        intro x
        have hle_vi :
            (fun _ : E ↦ ((m : 𝕜) : WithTopBot 𝕜)) x ≤
              Function.verticalInfimum (_root_.convexHull 𝕜 (epi g)) x := by
          exact (Function.le_verticalInfimum_of_subset_epi hsubset_convexEpi) x
        rw [Function.convexHull_eq_verticalInfimum_convexHull_epigraph]
        exact hle_vi
      intro x
      have hbot_lt_m : (⊥ : WithTopBot 𝕜) < ((m : 𝕜) : WithTopBot 𝕜) := by
        exact lt_of_le_of_ne (by simp) (by simp)
      have hconv_ne_bot : conv(g) x ≠ (⊥ : WithTopBot 𝕜) :=
        ne_of_gt <| lt_of_lt_of_le hbot_lt_m (hm_le_conv x)
      simpa [g] using hconv_ne_bot
  · simpa using hconv_closed

/-- Corollary 17.2.1 in closed-and-bounded bridge form over proper pseudo-metric spaces: if `S` is
nonempty closed bounded and `f` is continuous on `S`, then the convex hull of `f.toWithTopBotOn S`
is a closed proper convex function provided the same lower-semicontinuity witness for that convex
hull. -/
theorem conv_toWithTopBotOn_isClosedProperConvex_of_nonempty_of_isClosed_of_isBounded
    [PseudoMetricSpace E] [AddCommMonoid E] [Module 𝕜 E]
    [ProperSpace E]
    {S : Set E} {f : E → 𝕜} (hS_nonempty : S.Nonempty) (hS_closed : IsClosed S)
    (hS_bounded : IsBounded S) (hf : ContinuousOn f S)
    (hconv_closed : LowerSemicontinuous (conv(f.toWithTopBotOn S))) :
    IsClosedProperConvex[𝕜] (conv(f.toWithTopBotOn S)) := by
  have hS_compact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded
  exact conv_toWithTopBotOn_isClosedProperConvex_of_nonempty_of_isCompact
    hS_nonempty hS_compact hf hconv_closed

end
