import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open Filter
open scoped Topology Rockafellar

section

variable {𝕜 : Type v} [Semiring 𝕜] [TopologicalSpace 𝕜] [LE 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

namespace Function

/-- Sequential closedness consequence for the pairing-parametric graph owner: if the graph of
the subdifferential is closed, then limits of convergent graph sequences remain in the graph. -/
theorem mem_subdifferentialAt_of_tendsto_of_isClosed_subdifferentialGraph
    {Y : Type (max u v)} [TopologicalSpace Y] [HasPairing E Y 𝕜]
    {f : E → WithBotTop 𝕜} (hclosed : IsClosed (gph∂[Y](f)))
    {xSeq : ℕ → E} {x : E}
    {xStarSeq : ℕ → Y} {xStar : Y}
    (hx : Tendsto xSeq atTop (𝓝 x))
    (hxStar : Tendsto xStarSeq atTop (𝓝 xStar))
    (hsub : ∀ n, xStarSeq n ∈ (∂[Y]f(xSeq n))) :
    xStar ∈ (∂[Y]f(x)) := by
  have hgraph : Tendsto (fun n ↦ (xSeq n, xStarSeq n)) atTop (𝓝 (x, xStar)) := by
    simpa [nhds_prod_eq] using hx.prodMk hxStar
  have hmem : ∀ n, (xSeq n, xStarSeq n) ∈ gph∂[Y](f) := by
    intro n
    simpa using hsub n
  have hlimit : (x, xStar) ∈ gph∂[Y](f) := by
    exact hclosed.mem_of_tendsto hgraph (Filter.Eventually.of_forall hmem)
  simpa using hlimit

end Function

end

section

variable {𝕜 : Type v} [Semiring 𝕜] [TopologicalSpace 𝕜] [PartialOrder 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.24.7 says that if `xᵢ → x` and `xᵢ⋆ → x⋆` with
  `xᵢ⋆ ∈ ∂f(xᵢ)` for all `i`, then `x⋆ ∈ ∂f(x)`. The source then immediately restates this as the
  closedness of the graph of `∂f`.
- `core/canonical`: the owner abstractions already present in the project are the dual-valued
  graph owner `_root_.subdifferentialGraph` from Definition 5.24.3, the dual-valued
  `_root_.subdifferentialAt` from Definition 23.0.6, the closed-proper-convex owner
  `Function.IsClosedProperConvex`, and the topological owner `IsClosed`.
- `bridge/view`: once graph closedness is available, the pairing-parametric sequential
  closedness consequence is packaged as
  `mem_subdifferentialAt_of_tendsto_of_isClosed_subdifferentialGraph`.

Domain-style sampling used here:
- `_root_.subdifferentialGraph` from
  [Definition_5_24_3](Items/Chap05/Definition_5_24_3.lean);
- `_root_.subdifferentialAt` from
  [Definition_23_0_6](Items/Chap05/Definition_23_0_6.lean);
- `Function.IsClosedProperConvex` from
  [Text_12_3_6](Items/Chap03/Text_12_3_6.lean);
- mathlib's canonical closed-set owner `IsClosed`, together with
  `IsClosed.mem_of_tendsto` and `IsClosed.isSeqClosed`.

Primitive data vs derived API:
- primitive data: the closed proper convex function `f` and its canonical dual-valued owner graph
  `subdifferentialGraph f`;
- primitive topological compatibility data: continuity of
  `(x, x⋆) ↦ ⟪z - x, x⋆⟫ₚ` for each fixed `z`;
- derived API: the pairing-parametric sequence-limit corollary obtained from closedness of the
  canonical graph owner.

Layer target: `core/canonical` for the main labeled entry
`Function.IsClosedProperConvex.isClosed_subdifferentialGraph`, because the source itself
identifies the theorem with graph closedness; the sequential statement is kept only as a
consequence on that owner.

Codomain-layer normalization:
- this file's pairing-parametric theorem surfaces are kept at the chapter owner codomain
  `WithBotTop 𝕜` (not a concrete `EReal` alias), while the strong-dual bridge below is the
  `𝕜 = ℝ` specialization.

Ambient-assumption minimization:
- no finite-dimensionality hypothesis is needed at the canonical dual-valued closed-graph layer;
- no inner-product or completeness assumption is exposed on the pairing-parametric theorem;
- the strong-dual specialization is a thin bridge theorem.
-/

-- Proof sketch: write the graph as an intersection over `z` of closed sets
-- `{(x, x⋆) | f x + ⟪z - x, x⋆⟫ ≤ f z}`. Each set is closed because
-- `x ↦ f x` is lower semicontinuous (from `hf`) and
-- `(x, x⋆) ↦ (⟪z - x, x⋆⟫ : WithBotTop 𝕜)` is continuous.
/-- Theorem 5.24.7 at the pairing-parametric owner layer: if `f` is closed proper convex and the
pairing evaluation map `(x, x⋆) ↦ ⟪z - x, x⋆⟫ₚ` is continuous for each `z`, then the canonical
subdifferential graph is closed. -/
theorem IsClosedProperConvex.isClosed_subdifferentialGraph
    {Y : Type (max u v)} [TopologicalSpace Y] [HasPairing E Y 𝕜]
    {f : E → WithBotTop 𝕜} (hf : IsClosedProperConvex[𝕜] f)
    (hpair_cont : ∀ z : E,
      Continuous (fun p : E × Y ↦ ((⟪z - p.1, p.2⟫ₚ : 𝕜) : WithBotTop 𝕜)))
    :
    IsClosed (gph∂[Y](f)) := by
  have hgraph_eq :
      gph∂[Y](f) =
        ⋂ z : E,
          {p : E × Y |
            f p.1 + ((⟪z - p.1, p.2⟫ₚ : 𝕜) : WithBotTop 𝕜) ≤ f z} := by
    ext p
    constructor
    · intro hp
      refine Set.mem_iInter.mpr ?_
      intro z
      have hp' : p.2 ∈ subdifferentialAt f p.1 Y := hp
      exact (_root_.mem_subdifferentialAt_pairing.mp hp') z
    · intro hp
      change p.2 ∈ subdifferentialAt f p.1 Y
      rw [_root_.mem_subdifferentialAt_pairing]
      intro z
      have hz :
          f p.1 + ((⟪z - p.1, p.2⟫ₚ : 𝕜) : WithBotTop 𝕜) ≤ f z :=
        (Set.mem_iInter.mp hp) z
      simpa [ge_iff_le] using hz
  rw [hgraph_eq]
  refine isClosed_iInter ?_
  intro z
  have hcont_pairing :
      Continuous (fun p : E × Y ↦
        ((⟪z - p.1, p.2⟫ₚ : 𝕜) : WithBotTop 𝕜)) := hpair_cont z
  have hlsc_fst :
      LowerSemicontinuous (fun p : E × Y ↦ f p.1) :=
    hf.closed.comp continuous_fst
  have hlsc_pairing :
      LowerSemicontinuous (fun p : E × Y ↦
        ((⟪z - p.1, p.2⟫ₚ : 𝕜) : WithBotTop 𝕜)) :=
    hcont_pairing.lowerSemicontinuous
  have hlsc_sum :
      LowerSemicontinuous (fun p : E × Y ↦
        f p.1 + ((⟪z - p.1, p.2⟫ₚ : 𝕜) : WithBotTop 𝕜)) := by
    refine hlsc_fst.add' hlsc_pairing ?_
    intro p
    have h1 :
        f p.1 ≠ (⊤ : WithBotTop 𝕜) ∨
          ((⟪z - p.1, p.2⟫ₚ : 𝕜) : WithBotTop 𝕜) ≠ ⊥ := by
      exact Or.inr (WithBotTop.coe_ne_bot (⟪z - p.1, p.2⟫ₚ : 𝕜))
    have h2 :
        f p.1 ≠ (⊥ : WithBotTop 𝕜) ∨
          ((⟪z - p.1, p.2⟫ₚ : 𝕜) : WithBotTop 𝕜) ≠ ⊤ := by
      exact Or.inr (WithBotTop.coe_ne_top (⟪z - p.1, p.2⟫ₚ : 𝕜))
    exact WithBotTop.continuousAt_add
      (p := (f p.1, ((⟪z - p.1, p.2⟫ₚ : 𝕜) : WithBotTop 𝕜))) h1 h2
  simpa [Set.preimage] using hlsc_sum.isClosed_preimage (f z)

-- Proof sketch: this is the canonical dual-valued sequential consequence of graph closedness,
-- instantiated by the pairing-parametric closed-graph theorem above.
/-- Pairing-parametric sequential form of Theorem 5.24.7: under the same hypotheses as
`Function.IsClosedProperConvex.isClosed_subdifferentialGraph`, limits of convergent subgradient
sequences remain subgradients. -/
theorem IsClosedProperConvex.mem_subdifferentialAt_of_tendsto_pairing
    {Y : Type (max u v)} [TopologicalSpace Y] [HasPairing E Y 𝕜]
    {f : E → WithBotTop 𝕜} (hf : IsClosedProperConvex[𝕜] f)
    (hpair_cont : ∀ z : E,
      Continuous (fun p : E × Y ↦ ((⟪z - p.1, p.2⟫ₚ : 𝕜) : WithBotTop 𝕜)))
    {xSeq : ℕ → E} {x : E}
    {xStarSeq : ℕ → Y} {xStar : Y}
    (hx : Tendsto xSeq atTop (𝓝 x))
    (hxStar : Tendsto xStarSeq atTop (𝓝 xStar))
    (hsub : ∀ n, xStarSeq n ∈ (∂[Y]f(xSeq n))) :
    xStar ∈ (∂[Y]f(x)) := by
  exact Function.mem_subdifferentialAt_of_tendsto_of_isClosed_subdifferentialGraph
    (hf.isClosed_subdifferentialGraph hpair_cont) hx hxStar hsub

end Function

end

section

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

namespace Function

/-- Strong-dual specialization of
`Function.IsClosedProperConvex.isClosed_subdifferentialGraph`; this is the chapter's canonical
concrete dual model bridge. -/
theorem IsClosedProperConvex.isClosed_subdifferentialGraph_strongDual
    {f : E → WithBotTop ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    IsClosed (gph∂(f)) := by
  refine hf.isClosed_subdifferentialGraph (Y := StrongDual ℝ E) ?_
  intro z
  have hcont_real : Continuous (fun p : E × StrongDual ℝ E ↦ (p.2) (z - p.1)) :=
    continuous_snd.clm_apply (continuous_const.sub continuous_fst)
  simpa using WithBotTop.continuous_coe.comp hcont_real

/-- Theorem 5.24.7, strong-dual sequential bridge: in a real seminormed space, limits of
convergent dual subgradient sequences of a closed proper convex function remain subgradients. -/
theorem IsClosedProperConvex.mem_subdifferentialAt_of_tendsto
    {f : E → WithBotTop ℝ} (hf : IsClosedProperConvex[ℝ] f)
    {xSeq : ℕ → E} {x : E}
    {xStarSeq : ℕ → StrongDual ℝ E} {xStar : StrongDual ℝ E}
    (hx : Tendsto xSeq atTop (𝓝 x))
    (hxStar : Tendsto xStarSeq atTop (𝓝 xStar))
    (hsub : ∀ n, xStarSeq n ∈ (∂ f at xSeq n)) :
    xStar ∈ (∂ f at x) := by
  exact hf.mem_subdifferentialAt_of_tendsto_pairing (Y := StrongDual ℝ E)
    (hpair_cont := by
      intro z
      have hcont_real : Continuous (fun p : E × StrongDual ℝ E ↦ (p.2) (z - p.1)) :=
        continuous_snd.clm_apply (continuous_const.sub continuous_fst)
      simpa using WithBotTop.continuous_coe.comp hcont_real)
    hx hxStar hsub

end Function

end
