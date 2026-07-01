import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_20_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Rockafellar

section

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable [IsStrictOrderedRing 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
  [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 20.0.1 identifies the conjugate of the sum of a finite family
  of polyhedral convex functions with the infimal convolution of the individual conjugates,
  assuming the effective domains have nonempty intersection and the summands never take the value
  `⊥`. The source states this on `R^n`; the theorem is kept at the more canonical pairing/module
  owner layer, and the textbook properness wording is recovered below only as a thin companion.
- `core/canonical`: the project owner for finite infimal convolution is
  `finiteInfimalConvolution`, while the other owner notions here are
  `Function.HasPolyhedralEpigraph`, `Function.HasMixedPolyhedralDomainPoint`, and `dom(·)` for
  source-facing wrappers; convexity is derived owner-side from
  `Function.HasPolyhedralEpigraph.isConvex`, and the properness bridge `Function.IsProper.bot_lt`
  supplies the pointwise `⊥`-exclusion when needed.
- `bridge/view`: the textbook symbols `(f₁ + ··· + f_m)^*` and `f₁^* □ ··· □ f_m^*` are rendered
  directly by the chapter owner notation `(∑ i, f i)⋆` and
  `finiteInfimalConvolution (fun i ↦ (f i)⋆)`, while the common effective-domain hypothesis is
  expressed through the project owner notation `dom(f i)` rather than restated as a raw pointwise
  finiteness condition.

Domain-style sampling used here:
- `dom(·)` and `mem_effectiveDomain`;
- `(f i).bot_lt` via `Function.IsProper.bot_lt`;
- `finiteInfimalConvolution`;
- `(f i).HasPolyhedralEpigraph`;
- `Function.HasPolyhedralEpigraph.add`.

Primitive data vs derived API:
- primitive inputs: the finite family `f : ι → E → WithTopBot 𝕜`, together with the
  canonical owner hypothesis `(f i).HasPolyhedralEpigraph` for each member, the pointwise
  exclusion `∀ i x, ⊥ < f i x`, and the canonical mixed-domain owner witness
  `f.HasMixedPolyhedralDomainPoint`;
- owner primitives reused from `Text_19_0_8`: `Function.HasPolyhedralEpigraph` and its set-side
  bridge `Function.HasPolyhedralEpigraph.isPolyhedralConvexSet`;
- source-facing bridge witness: `(⋂ i, dom(f i)).Nonempty`;
- derived API: the mixed-owner all-polyhedral specialization, the source-facing common-domain
  wrapper, and the corresponding thin properness-form restatements.

Layer target: this item stays `source-facing`, building directly on the chapter owner epigraph API
from `Text_19_0_8` rather than duplicating those declarations locally or collapsing to the
Chapter 16 common-`riDom` owner theorem, whose hypothesis layer would be strictly stronger than
the source's common-domain assumption.
-/

-- Proof sketch: invoke the canonical mixed-owner theorem from `Theorem_20_1` directly.
-- Polyhedrality of every summand makes the nonpolyhedral-convex branch vacuous.
/-- Canonical mixed-owner all-polyhedral specialization: if every summand has polyhedral epigraph,
is pointwise strictly above `⊥`, and the family has a mixed polyhedral-domain point, then the
conjugate of the finite sum is the finite infimal convolution of the conjugates. -/
theorem convexConjugate_sum_eq_finiteInfimalConvolution_of_polyhedral_mixedDomain
    (f : ι → E → WithTopBot 𝕜)
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hf_poly : ∀ i, (f i).HasPolyhedralEpigraph)
    (hdom : f.HasMixedPolyhedralDomainPoint)
    :
    ((∑ i, f i)⋆ : E → WithTopBot 𝕜) =
      finiteInfimalConvolution (fun i ↦ (f i)⋆) := by
  have hf_convex : ∀ i, ¬ (f i).HasPolyhedralEpigraph → (f i).IsConvex 𝕜 := by
    intro i hi_not_poly
    exact False.elim (hi_not_poly (hf_poly i))
  simpa using
    convexConjugate_sum_eq_finiteInfimalConvolution_of_mixedPolyhedralDomain
      (f := f) hf_convex hf_bot hdom

/-- Properness-form restatement of the canonical mixed-owner all-polyhedral specialization. -/
theorem
    convexConjugate_sum_eq_finiteInfimalConvolution_of_proper_polyhedral_mixedDomain
    (f : ι → E → WithTopBot 𝕜)
    (hf_proper : ∀ i, (f i).IsProper)
    (hf_poly : ∀ i, (f i).HasPolyhedralEpigraph)
    (hdom : f.HasMixedPolyhedralDomainPoint)
    :
    ((∑ i, f i)⋆ : E → WithTopBot 𝕜) =
      finiteInfimalConvolution (fun i ↦ (f i)⋆) := by
  simpa using
    convexConjugate_sum_eq_finiteInfimalConvolution_of_polyhedral_mixedDomain
      f (fun i x ↦ (hf_proper i).bot_lt x) hf_poly hdom

private theorem hasMixedPolyhedralDomainPoint_of_polyhedral_domNonempty
    (f : ι → E → WithTopBot 𝕜)
    (hf_poly : ∀ i, (f i).HasPolyhedralEpigraph)
    (hdom : (⋂ i, dom(f i)).Nonempty) :
    f.HasMixedPolyhedralDomainPoint := by
    rcases hdom with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    constructor
    · intro i _
      exact (Set.mem_iInter.mp hx) i
    · intro i hi_not_poly
      exact False.elim (hi_not_poly (hf_poly i))

-- Proof sketch: this is the source-facing common-domain wrapper around the canonical mixed-owner
-- all-polyhedral theorem above.
/-- Theorem 20.0.1, source-facing common-domain form: if a finite family of polyhedral convex
functions on a finite-dimensional pairing module over `𝕜` never takes the value `⊥` and has
nonempty common effective domain, then the conjugate of the pointwise sum is the finite infimal
convolution of the individual conjugates. -/
theorem convexConjugate_sum_eq_finiteInfimalConvolution_of_polyhedral_domNonempty
    (f : ι → E → WithTopBot 𝕜)
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hf_poly : ∀ i, (f i).HasPolyhedralEpigraph)
    (hdom : (⋂ i, dom(f i)).Nonempty)
    :
    ((∑ i, f i)⋆ : E → WithTopBot 𝕜) =
      finiteInfimalConvolution (fun i ↦ (f i)⋆) := by
  have hmixed : f.HasMixedPolyhedralDomainPoint :=
    hasMixedPolyhedralDomainPoint_of_polyhedral_domNonempty f hf_poly hdom
  simpa using
    convexConjugate_sum_eq_finiteInfimalConvolution_of_polyhedral_mixedDomain
      f hf_bot hf_poly hmixed

/-- Properness-form restatement of Theorem 20.0.1. This companion adds no new mathematics: its
only use of `Function.IsProper (f i)` is to recover the pointwise `⊥`-exclusion, while the
somewhere-finite clause already follows from `hdom`. -/
theorem
    convexConjugate_sum_eq_finiteInfimalConvolution_of_proper_polyhedral_commonDomain
    (f : ι → E → WithTopBot 𝕜)
    (hf_proper : ∀ i, (f i).IsProper)
    (hf_poly : ∀ i, (f i).HasPolyhedralEpigraph)
    (hdom : (⋂ i, dom(f i)).Nonempty)
    :
    ((∑ i, f i)⋆ : E → WithTopBot 𝕜) =
      finiteInfimalConvolution (fun i ↦ (f i)⋆) := by
  have hmixed : f.HasMixedPolyhedralDomainPoint :=
    hasMixedPolyhedralDomainPoint_of_polyhedral_domNonempty f hf_poly hdom
  simpa using
    convexConjugate_sum_eq_finiteInfimalConvolution_of_proper_polyhedral_mixedDomain
      f hf_proper hf_poly hmixed

end
