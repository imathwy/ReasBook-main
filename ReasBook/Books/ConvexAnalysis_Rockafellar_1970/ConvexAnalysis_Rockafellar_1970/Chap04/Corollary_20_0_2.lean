import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Rockafellar

noncomputable section

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 20.0.2 asserts attainment in the finite infimal convolution of the
  conjugates under the same primitive hypotheses as Theorem 20.0.1.
- `core/canonical`: the canonical owner is the finite-family mixed-domain attainment theorem
  `exists_sum_eq_finiteInfimalConvolution_conjugates_of_mixedPolyhedralDomain` from
  `Theorem_20_1`.
- `bridge/view`: this file stays on the public finite index `ι` surface, with no `Fin` reindexing
  bridge needed.

Primitive data vs derived API:
- primitive inputs remain the polyhedral family, pointwise `⊥`-exclusion, and nonempty common
  effective domain;
- derived output is an attaining decomposition for the finite infimal convolution of the
  conjugates at `x⋆`.

Layer target: this stays `bridge/view`, but now uses the primitive mixed-domain owner route
directly instead of passing through a stronger closed-proper-convex bridge.
-/

-- Proof sketch: apply the canonical mixed-owner attainment theorem from `Theorem_20_1`.
-- Polyhedrality makes the nonpolyhedral-convex branch vacuous, and a common domain point gives
-- the mixed domain hypothesis directly.
/- Corollary 20.0.2: under the hypotheses of Theorem 20.0.1, for each `x⋆` in a finite-dimensional
topological vector space with a continuous linear self-pairing, the infimum defining the finite
infimal convolution of the conjugates is attained by some decomposition `x⋆ = ∑ i, xᵢ⋆`. -/
theorem
    exists_sum_eq_finiteInfimalConvolution_conjugates_of_polyhedral_domNonempty
    (f : ι → E → WithBotTop 𝕜)
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hf_poly : ∀ i, (f i).HasPolyhedralEpigraph)
    (hdom : (⋂ i, dom(f i)).Nonempty)
    (xStar : E) :
    ∃ xsStar : ι → E,
      (∑ i, xsStar i) = xStar ∧
        finiteInfimalConvolution (fun i ↦ (f i)⋆) xStar =
          ∑ i, (f i)⋆ (xsStar i) := by
  have hf_convex : ∀ i, ¬ (f i).HasPolyhedralEpigraph → (f i).IsConvex 𝕜 := by
    intro i hi_not_poly
    exact False.elim (hi_not_poly (hf_poly i))
  have hmixed : f.HasMixedPolyhedralDomainPoint := by
    rcases hdom with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    constructor
    · intro i _
      exact (Set.mem_iInter.mp hx) i
    · intro i hi_not_poly
      exact False.elim (hi_not_poly (hf_poly i))
  simpa using
    exists_sum_eq_finiteInfimalConvolution_conjugates_of_mixedPolyhedralDomain
      (f := f) hf_convex hf_bot hmixed xStar

end
