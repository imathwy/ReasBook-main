import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_37_1_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_3
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_4
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_6_3

noncomputable section

open scoped Rockafellar

universe u v

namespace Bifunction

section

variable {𝕜 : Type v} [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {U : Type u} {V : Type v}
variable {YU : Type u} {YV : Type v}
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U] [HasPairing U YU 𝕜]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V] [HasPairing V YV 𝕜]
variable [NormedAddCommGroup YU] [NormedSpace 𝕜 YU]
variable [NormedAddCommGroup YV] [NormedSpace 𝕜 YV]

local instance : HasPairing YU U 𝕜 := HasPairing.swap
local instance : HasPairing YV V 𝕜 := HasPairing.swap

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 37.5 is the saddle-function analogue of Fenchel subgradient inversion:
  for a closed proper concave-convex `K`, any conjugate saddle representative `KStar`, the
  saddle-subgradient relation for `K` is equivalent both to the reversed saddle-subgradient
  relation for `KStar` and to the usual convex subgradient relation of the graph function of the
  closed proper convex generator `F`.
- `core/canonical`: the owner abstractions already present in the project are
  `Bifunction.lowerConjugate`, the Chapter 34 class owner `omegaAdjoint`, the Chapter 34 equivalence
  relation `K ∼ L`, the Chapter 34 closed-convex owner `Bifunction.IsClosedConvex`, the saddle
  subdifferential owner `Bifunction.subdifferentialAt`, the Chapter 23 vector-subdifferential
  owner `_root_.subdifferentialAt` / `∂[·](·)(·)` on `Function.uncurry F`, and the Chapter 6/7
  adjoint notation surface `F⋆`.
- `bridge/view`: the source theorem's fourth displayed equality is a Fenchel-Young equality
  companion relating the same owner data through `adjoint`; it is kept inside the TFAE
  theorem below rather than promoted to a second owner.

Primary mathematical domain:
- conjugate saddle-functions, saddle subdifferentials, and graph-function Fenchel duality.

Domain-style sampling used here:
- `_root_.subdifferentialAt` from `Chap05.Definition_23_0_6`;
- `Bifunction.lowerConjugate` from `Chap07.Definition_37_1_1`;
- `Bifunction.subdifferentialAt` and the notation `d(K ; u, v)` from `Chap07.Text_35_6_3`;
- `Bifunction.adjoint` / `F⋆` from `Chap06.Definition_6_30_14`;
- `Bifunction.mem_omegaAdjoint_iff` and the Chapter 34 owner `omegaAdjoint` from
  `Chap07.Defn_34_2`.

Primitive data vs derived API:
- primitive source data for the full four-clause theorem: a closed-convex generator owner
  `hF : IsClosedConvex F`, graph properness of `Function.uncurry F`, a representative
  `K ∈ omegaAdjoint V YU F`, and a conjugate-side representative `KStar ∼ lowerConjugate K`;
- primitive owner data reused from upstream: `d(K ; u, v)`, `d(KStar ; uStar, vStar)`,
  the graph-function owner `Function.uncurry F`,
  the pairing-level subdifferential owner
  `∂[YU × V](Function.uncurry F)(·)`, and `(F⋆)`;
- derived saddle-side data: `SaddleFunction.IsProper K`, obtained from
  `Bifunction.isProper_of_mem_omega_of_uncurry_isConvex_of_uncurry_isProper`;
- derived API: the four-way `List.TFAE` formulation matching Rockafellar's theorem, and the
  shorter inversion lemma used directly by Corollary 37.5.3 and the graph corollaries.

Layer target:
- the theorem `conjugate_subdifferentialAt_tfae_of_mem_omega_and_equivalent_lowerConjugate` is
  `source-facing`;
- the theorem
  `mem_subdifferentialAt_iff_mem_subdifferentialAt_of_equivalent_lowerConjugate`
  is the `core/canonical` owner-level consequence for downstream use, but it remains on the same
  pairing-level normed ambient layer as the source-facing theorem because its only justification
  in the current chapter graph is extraction of the first two clauses of that TFAE statement.
-/

-- Proof sketch: first derive `SaddleFunction.IsProper K` from the Chapter 34 properness bridge
-- attached to `hK : K ∈ omegaAdjoint V YU F`, then use the Chapter 34 closed-convex owner `hF`
-- for the generator `F`, identify the graph-function conjugate relation by the convex theorem
-- `Function.IsClosedProperConvex.mem_subdifferentialAt_convexConjugate_iff`, and translate the
-- saddle-side clauses through the Chapter 37 conjugate owner `lowerConjugate K`. Corollary 37.4.1
-- then allows replacement of `lowerConjugate K` by any equivalent conjugate representative
-- `KStar`.
variable {F : U → YV → WithBotTop 𝕜}
variable {K : U → V → WithBotTop 𝕜}
variable {KStar : YU → YV → WithBotTop 𝕜}

local notation "F⋆" => (adjoint V YU F : V → YU → WithBotTop 𝕜)

/-- Theorem 37.5, source-facing owner form: for `K ∈ omegaAdjoint V YU F` and a conjugate saddle
representative
`KStar ∼ lowerConjugate K`, the saddle-subgradient clause for `K`, the reversed
saddle-subgradient clause for `KStar`, the graph-function subgradient clause for
`Function.uncurry F` through the pairing-level subgradient notation `∂[YU × V](·)(·)`, and the
associated Fenchel-Young equality written with `(F⋆)` all
belong to one four-condition equivalence class. Properness of `K` is derived internally from the
Chapter 34 owner hypotheses. -/
theorem conjugate_subdifferentialAt_tfae_of_mem_omega_and_equivalent_lowerConjugate
    (hF : IsClosedConvex F)
    (hF_proper : (Function.uncurry F).IsProper)
    (hK : K ∈ omegaAdjoint V YU F)
    (hKStar : KStar ∼ lowerConjugate K)
    {u : U} {uStar : YU} {v : V} {vStar : YV} :
    List.TFAE
      [ (uStar, vStar) ∈ d(K ; u, v | YU, YV),
        (u, v) ∈ d(KStar ; uStar, vStar | U, V),
        (-uStar, v) ∈ ∂[YU × V]Function.uncurry F((u, vStar)),
        F u vStar - ⟪v, vStar⟫ₚ =
          F⋆ v uStar - ⟪u, uStar⟫ₚ ] := by
  sorry

-- This owner-level inversion statement is only obtained in this file by specializing the
-- preceding TFAE theorem to its first two clauses, so it stays on the same
-- pairing-level normed ambient layer rather than being promoted to a weaker theorem unsupported
-- by the current chapter graph.
-- Proof sketch: specialize the preceding TFAE theorem to the first two clauses and read off the
-- `0 ↔ 1` equivalence.
/-- Core owner consequence of Theorem 37.5: the saddle subdifferential of a closed proper
concave-convex kernel is inverted by any conjugate saddle representative in the Chapter 37 sense
`KStar ∼ lowerConjugate K`. -/
theorem mem_subdifferentialAt_iff_mem_subdifferentialAt_of_equivalent_lowerConjugate
    (hK_shape : SaddleFunction.IsConcaveConvex 𝕜 K)
    (hK_closed : SaddleFunction.IsClosed K)
    (hK_proper : SaddleFunction.IsProper K)
    (hKStar : KStar ∼ lowerConjugate K)
    {u : U} {uStar : YU} {v : V} {vStar : YV} :
    (uStar, vStar) ∈ d(K ; u, v | YU, YV) ↔
      (u, v) ∈ d(KStar ; uStar, vStar | U, V) := by
  sorry

end

end Bifunction
