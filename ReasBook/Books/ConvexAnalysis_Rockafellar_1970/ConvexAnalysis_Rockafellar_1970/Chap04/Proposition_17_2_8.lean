import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_12_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Definition_17_2_4
import ConvexAnalysis_Rockafellar_1970.Chap04.Definition_17_2_7
import ConvexAnalysis_Rockafellar_1970.Chap04.Lemma_17_2_9

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {X Y : Type*} {𝕜 : Type*}
    [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜] [IsOrderedRing 𝕜]
    [AddCommGroup Y] [Module 𝕜 Y]
    [HasPairing X Y 𝕜] [HasPairing Y X 𝕜] [HasPairingSwap X Y 𝕜]
    [HasPairingAddRight X Y 𝕜] [HasPairingSMulRight X Y 𝕜] [HasPairingZeroRight X Y 𝕜]
local notation "YStar" => Y × 𝕜

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 17.2.8 identifies, for a dual family `SStar ⊆ Y × 𝕜`, the support
  function of the inequality solution set with the function generated in Definition 17.2.7 from
  the cone of Definition 17.2.5.
- `core/canonical`: the owner abstractions are the support function `supportFunction`, the
  solution-set owner `linearInequalitySolutionSet`, and the fiber-infimum owner
  `Kinf[𝕜](SStar)`, canonically presented via `generated_cone_inf` and
  `Function.verticalInfimum`, together with the lower-semicontinuous hull owner `cl(·)`.
- `bridge/view`: this item is the closed-owner bridge from `Kinf[𝕜](SStar)` to the
  support function of `linearInequalitySolutionSet SStar`.

Domain-style sampling used here:
- `supportFunction`;
- `linearInequalitySolutionSet`;
- `Kinf[𝕜](SStar)` / `generated_cone_inf`;
- the Chapter 1 owner `Function.verticalInfimum` underlying `Kinf[𝕜](SStar)`;
- the closure owner `cl(·)`;
- `convexConjugate_indicator_eq_supportFunction`;
- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull`;
- the generated-cone owner `PointedCone.hull`.

Primitive data vs derived API:
- primitive source-facing data: the family of inequalities `SStar : Set (Y × 𝕜)`;
- owner objects derived from that data: `linearInequalitySolutionSet SStar` and
  `Kinf[𝕜](SStar)`;
- derived bridge API: the equality between the support function of the former and the
  lower-semicontinuous hull of the latter, proved through Fenchel conjugacy rather than through a
  false raw cone/epigraph identification.

Ambient-layer decision:
- `linearInequalitySolutionSet` already lives on the primal/dual pairing layer (`X` paired with
  `Y`), while `Kinf[𝕜](SStar)` only needs an ordered scalar module on `Y`. The bridge theorem
  is therefore stated with explicit primal and dual owners, with reverse-orientation pairing data
  used only for conjugacy-side steps.

Closure correction:
- the raw cone `K⋆[𝕜] SStar = PointedCone.hull 𝕜 (adjoin_vertical_unit SStar)` is not a
  priori a closed epigraph, so this file should not present a literal set equality between
  `K⋆[𝕜] SStar` and `{p | δᵛ(p.1 | linearInequalitySolutionSet SStar) ≤ p.2}` as its
  main bridge.
- instead, the proof works at the canonical function-duality layer: the conjugate of
  `Kinf[𝕜](SStar)` is the indicator of `linearInequalitySolutionSet SStar`, so
  convex biconjugacy yields
  `δᵛ(· | linearInequalitySolutionSet SStar) = cl(Kinf[𝕜](SStar))`.

Layer target: `bridge/view`. The file should expose the source theorem directly in terms of the
existing owners rather than introduce a parallel wrapper around support functions, vertical
infimum functions, or epigraph packages.
-/

private theorem pairing_le_Kinf_of_mem_linearInequalitySolutionSet
    {SStar : Set YStar} {x : X} (hx : x ∈ solutionSet[SStar]) :
    ∀ y : Y, (⟪x, y⟫ₚ : WithTopBot 𝕜) ≤ Kinf[𝕜](SStar) y := by
  sorry

private theorem convexConjugate_Kinf_eq_indicator_linearInequalitySolutionSet
    (SStar : Set YStar) :
    (Kinf[𝕜](SStar))⋆ =
      (δ[𝕜](· | solutionSet[SStar])) := by
  sorry

private theorem Kinf_isConvex (SStar : Set YStar) :
    (Kinf[𝕜](SStar)).IsConvex 𝕜 := by
  simpa [generated_cone_inf] using
    Function.isConvex_verticalInfimum
      (K⋆[𝕜] SStar).convex

/-- Proposition 17.2.8: the support function of the set cut out by the inequalities encoded in
`SStar ⊆ Y × 𝕜` is the lower-semicontinuous hull of the generated-cone infimum owner
`Kinf[𝕜](SStar)`. This source theorem is stated on the primal/dual pairing owner surface rather
than by identifying primal and dual ambient spaces. -/
theorem supportFunction_linearInequalitySolutionSet_eq_lowerSemicontinuousHull_generated_cone_inf
    [TopologicalSpace (WithTopBot 𝕜)]
    [FiniteDimensional 𝕜 Y]
    [HasContinuousPairing Y X 𝕜]
    (SStar : Set YStar) :
    δᵛ(· | solutionSet[SStar]) =
      cl(Kinf[𝕜](SStar)) := by
  sorry

end
