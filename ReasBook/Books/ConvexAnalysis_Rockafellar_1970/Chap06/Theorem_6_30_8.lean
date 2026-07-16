import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_5
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_12

noncomputable section

open scoped Rockafellar

universe u v w z

namespace Bifunction

section

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type z}
variable [Add 𝕜] [Neg 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [Zero U] [Sub U] [Neg UStar]
variable [HasPairing U UStar 𝕜] [HasPairingNegRight U UStar 𝕜]

variable (G : U → X → WithBotTop 𝕜)

local notation "h" => upperPerturbationFunction G

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.8 characterizes Kuhn--Tucker vectors for the concave program
  attached to `G` by a superdifferential condition on the upper perturbation function
  `h := upperPerturbationFunction G`.
- `core/canonical`: the owner declarations already present are
  `Bifunction.upperPerturbationFunction`, `Bifunction.IsConcaveKuhnTuckerVector`, and the
  Chapter 6 owner `_root_.concaveSubdifferentialAt`.
- `bridge/view`: the theorem is the direct source-facing bridge between the Chapter 6
  Kuhn--Tucker owner and the Chapter 6 concave-subdifferential condition at the origin; the
  pairing inequality from Definition 6.30.5 is a derived membership criterion rather than a
  second public owner.

Domain-style sampling used here:
- `Bifunction.upperPerturbationFunction` from Definition 6.30.11;
- `Bifunction.IsConcaveKuhnTuckerVector` and its finiteness/supporting-hyperplane API from
  Definition 6.30.12;
- `_root_.concaveSubdifferentialAt` and
  `_root_.mem_concaveSubdifferentialAt_pairing` from Definition 6.30.5;
- the primal-side Kuhn--Tucker/subdifferential bridge from Theorem 6.29.1.

Primitive data vs derived API:
- primitive inputs: a bifunction `G` and a dual vector `u⋆`;
- primitive owners already upstream: `h := upperPerturbationFunction G`,
  `IsConcaveKuhnTuckerVector G u⋆`, and `concaveSubdifferentialAt h 0`;
- derived bridge API in this file: the source iff-characterization of concave Kuhn--Tucker
  vectors by finiteness of `h 0` together with the origin supergradient condition, expressed on
  the canonical owner `concaveSubdifferentialAt h 0`.

Layer target: `source-facing`, expressed directly in the canonical owner language already present
in the project.
-/

-- Proof sketch: if `u⋆` is a concave Kuhn--Tucker vector, the theorem
-- `IsConcaveKuhnTuckerVector.upperPerturbationFunction_zero_finite` gives finiteness of `h 0`,
-- and the owner inequality
-- `⟪u, u⋆⟫ₚ + h u ≤ h 0`, together with `HasPairingNegRight.pairing_neg_right`, is exactly the
-- pairing membership criterion for `-u⋆ ∈ concaveSubdifferentialAt h 0`. Conversely, finiteness
-- of `h 0` and that supergradient condition give `h u ≤ h 0 - ⟪u, u⋆⟫ₚ` for all `u`, hence
-- `⟪u, u⋆⟫ₚ + h u ≤ h 0`; evaluating at `u = 0` forces the defining shifted supremum to equal
-- `h 0`, and the finiteness of `h 0` supplies the two finiteness fields of
-- `IsConcaveKuhnTuckerVector G u⋆`.
/-- Theorem 6.30.8: a dual vector `u⋆` is a Kuhn--Tucker vector for the concave program attached
to `G` exactly when the unperturbed upper perturbation value `h 0` is finite and `-u⋆` belongs to
the concave subdifferential of `h := upperPerturbationFunction G` at `0`, under the canonical
right-negation compatibility `⟪u, -u⋆⟫ₚ = -⟪u, u⋆⟫ₚ`. -/
theorem isConcaveKuhnTuckerVector_iff_zero_finite_and_neg_mem_concaveSubdifferentialAt_zero
    (uStar : UStar) :
    IsConcaveKuhnTuckerVector G uStar ↔
      h 0 ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤ ∧
        -uStar ∈ concaveSubdifferentialAt h 0 := sorry

end

end Bifunction
