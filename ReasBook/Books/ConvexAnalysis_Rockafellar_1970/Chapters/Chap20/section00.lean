import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_20_0_1 (from Chap04) -/
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

/-! ### Corollary_20_0_2 (from Chap04) -/
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

/-! ### Corollary_20_0_3 (from Chap04) -/
/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 20.0.3 packages the fully polyhedral specialization of the
  conjugate-of-sum formula together with the corresponding attainment statement.
- `core/canonical`: within Chapter 20.0, the source-facing owner declarations already exist as
  `convexConjugate_sum_eq_finiteInfimalConvolution_of_polyhedral_domNonempty`
  and
  `exists_sum_eq_finiteInfimalConvolution_conjugates_of_polyhedral_domNonempty`.
  Both owners live directly on the chapter `WithBotTop` codomain layer at the same scalar-generic
  finite-dimensional pairing-space abstraction, so this recall node does not need any
  `EReal`-bridge restatement.
  The broader Chapter 20.1 theorems remain upstream support for those owners, not the public
  declarations recalled here.
- `bridge/view`: this file is a recall node only; it introduces no second owner-level API and
  should reuse the direct Chapter 20.0 owners rather than skip to the more general 20.1 layer.

Domain-style sampling used here:
- `convexConjugate_sum_eq_finiteInfimalConvolution_of_polyhedral_domNonempty`;
- `exists_sum_eq_finiteInfimalConvolution_conjugates_of_polyhedral_domNonempty`;
- chapter-level `WithBotTop` codomain owner surfaces for conjugate-of-sum and attainment.

Primitive data vs derived API:
- no new primitive data belongs to this item;
- the source content is exactly the pair of direct Chapter 20.0 owners recalled below.

Layer target: `bridge/view`, since the mathematical content is already owned upstream in the
immediately preceding Chapter 20.0 items and this file should recall those direct owners rather
than restate them or bypass them with a more general upstream theorem pair.
-/

/- Corollary 20.0.3 recalls the direct Chapter 20.0 owner theorem for the all-polyhedral
conjugate-of-sum formula. -/
recall
  convexConjugate_sum_eq_finiteInfimalConvolution_of_polyhedral_domNonempty

/- Corollary 20.0.3 also recalls the matching Chapter 20.0 attainment statement for the finite
infimal convolution of the conjugates. -/
recall
  exists_sum_eq_finiteInfimalConvolution_conjugates_of_polyhedral_domNonempty

/-! ### Theorem_20_0_4 (from Chap04) -/
open scoped BigOperators Rockafellar

noncomputable section

universe u

section

namespace Function

variable {ι : Type u}
variable {𝕜 : Type*} [Ring 𝕜] [Preorder 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable {α : Type*} [AddCommMonoid α] [Module 𝕜 α] [Preorder α]

/-- A finite family has a common point that lies in `dom(·)` on polyhedral indices and in
`riDom[𝕜](·)` on nonpolyhedral indices. -/
abbrev mixedPolyhedralDomain (f : ι → E → WithTopBot α) : Set E := by
  classical
  exact ⋂ i, (if (f i).HasPolyhedralEpigraph then dom(f i) else riDom[𝕜](f i))

/-- A finite family has a common point in the mixed polyhedral domain intersection. -/
abbrev HasMixedPolyhedralDomainPoint (f : ι → E → WithTopBot α) : Prop :=
  (mixedPolyhedralDomain f).Nonempty

/-- Membership in the mixed polyhedral-domain set is exactly the branchwise
`dom`/`riDom[𝕜]` condition. -/
theorem mem_mixedPolyhedralDomain_iff (f : ι → E → WithTopBot α) (x : E) :
    x ∈ mixedPolyhedralDomain f ↔
      (∀ i, (f i).HasPolyhedralEpigraph → x ∈ dom(f i)) ∧
        (∀ i, ¬ (f i).HasPolyhedralEpigraph → x ∈ riDom[𝕜](f i)) := by
  classical
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · intro i hi_poly
      have hxi :
          x ∈ (if (f i).HasPolyhedralEpigraph then dom(f i) else riDom[𝕜](f i)) :=
        Set.mem_iInter.mp hx i
      simpa [hi_poly] using hxi
    · intro i hi_not_poly
      have hxi :
          x ∈ (if (f i).HasPolyhedralEpigraph then dom(f i) else riDom[𝕜](f i)) :=
        Set.mem_iInter.mp hx i
      simpa [hi_not_poly] using hxi
  · rintro ⟨hx_dom, hx_ri⟩
    refine Set.mem_iInter.mpr ?_
    intro i
    by_cases hi_poly : (f i).HasPolyhedralEpigraph
    · simpa [hi_poly] using hx_dom i hi_poly
    · simpa [hi_poly] using hx_ri i hi_poly

/-- Bridge: `HasMixedPolyhedralDomainPoint` is exactly the explicit witness form used in source
statements. -/
theorem hasMixedPolyhedralDomainPoint_iff (f : ι → E → WithTopBot α) :
    f.HasMixedPolyhedralDomainPoint ↔
      ∃ x : E,
        (∀ i, (f i).HasPolyhedralEpigraph → x ∈ dom(f i)) ∧
          ∀ i, ¬ (f i).HasPolyhedralEpigraph → x ∈ riDom[𝕜](f i) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (mem_mixedPolyhedralDomain_iff (f := f) (x := x)).1 hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (mem_mixedPolyhedralDomain_iff (f := f) (x := x)).2 hx⟩

end Function

end

section

variable {ι : Type u}
variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable [IsStrictOrderedRing 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 20.0.4 is the mixed polyhedral refinement of the conjugation formula
  for a finite sum of proper convex functions.
- `core/canonical`: the best owner abstractions already present in this chapter are
  the finite-family owners `convexConjugate`, `finiteInfimalConvolution`, `cl(·)`, `dom(·)`, and
  `riDom[𝕜](·)`, together with the chapter polyhedral-epigraph predicate
  `Function.HasPolyhedralEpigraph`.
- `bridge/view`: this item stays `source-facing` rather than collapsing to a prefix-style
  presentation, because its mixed hypothesis is indexed by the intrinsic predicate
  `Function.HasPolyhedralEpigraph (f i)` and does not choose an ordering that turns the
  polyhedral members into an initial segment. The refinement here is therefore to reuse the owner
  `lowerSemicontinuousHull` through the chapter notation `cl(·)`, together with `riDom[𝕜](·)` and
  the upstream polyhedral-epigraph owner directly, while factoring the mixed compatibility block
  into the short owner predicate `Function.HasMixedPolyhedralDomainPoint`.

Domain-style sampling used here:
- the finite-family duality owner
  `convexConjugate_sum_lowerSemicontinuousHull_eq_`
  `lowerSemicontinuousHull_finiteInfimalConvolution_of_proper_convex`
  from `Theorem_16_4_2`;
- the finite-family closure owner
  `Function.lowerSemicontinuousHull_sum_eq_sum_of_nonempty_iInter_riDom`
  from `Theorem_9_3`;
- the polyhedral special case
  `convexConjugate_sum_eq_finiteInfimalConvolution_of_proper_polyhedral_commonDomain`
  from `Theorem_20_0_1`;
- the chapter owner predicate `Function.HasPolyhedralEpigraph` from `Text_19_0_8`.

Primitive data vs derived API:
- primitive inputs: a finite family `f : ι → E → WithTopBot 𝕜`;
- owner hypotheses: pointwise exclusion of `⊥`, convexity only on the nonpolyhedral branch, and
  the mixed polyhedral/domain-relative-interior compatibility condition;
- derived API: the conjugation formula for the pointwise sum, plus the thin properness-form
  companion below. The mixed-domain compatibility condition is exposed as the short owner
  predicate `Function.HasMixedPolyhedralDomainPoint`.

Layer target: `source-facing`; the theorem is stated directly for the finite-family sum and the
finite infimal convolution of the conjugates, while reusing the canonical owner
`lowerSemicontinuousHull` through the theorem-surface notation `cl(·)` on the right-hand side and
`riDom[𝕜](·)` for the relative-interior domain condition. The source's numbered list is therefore
refined to the canonical arbitrary finite-index owner layer `[Fintype ι]`, since no order or
coordinate structure on the index type is used anywhere in the theorem surface. The public theorem
stays at the same root theorem layer as `Theorem_20_0_1` and `Theorem_20_1`, rather than
introducing a parallel namespace wrapper for another finite-family conjugacy identity.

Scalar/codomain minimization note: the mixed-domain owner declarations above are codomain-split
(`f : ι → E → WithTopBot α`), while the conjugation theorem itself remains on
`WithTopBot 𝕜` because the current finite-family conjugate API chain is pairing-valued at `𝕜`
(`Theorem_16_4_2` and `Theorem_9_3` clause (5)).
-/

variable [Fintype ι] [FiniteDimensional 𝕜 E]
  [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]

variable (f : ι → E → WithTopBot 𝕜)

-- Proof sketch: apply the general conjugation formula from Theorem 16.4.2 to the family `f`. The
-- mixed hypothesis already gives a common finite point for every summand: on the polyhedral branch
-- directly through `dom(f i)`, and on the nonpolyhedral branch because
-- `riDom[𝕜](f i) ⊆ dom(f i)`.
-- Together with the pointwise exclusion `⊥ < f i x`, this recovers the properness required by the
-- general theorem. The mixed hypothesis is stronger than the all-`riDom` hypothesis used to
-- compare lower
-- semicontinuous hulls of sums, because for polyhedral indices it gives plain domain membership
-- and polyhedrality upgrades that branch to convexity and the needed relative-interior
-- compatibility, while the nonpolyhedral branch carries its own explicit convexity hypothesis.
-- The right-hand side is then the canonical lower-semicontinuous hull of the finite infimal
-- convolution of the individual conjugates.
/-- Theorem 20.0.4: for a finite family of convex `WithTopBot 𝕜`-valued functions on a
finite-dimensional topological module over `𝕜` equipped with a continuous linear self-pairing, if
one point lies in the ordinary domain of every polyhedral member and in the relative interior
`riDom[𝕜](·)` of the domain of every nonpolyhedral member, and if every summand is pointwise
strictly above `⊥`, then the conjugate of the pointwise sum is the closure `cl(·)` of the finite
infimal convolution of the individual conjugates. Convexity is required explicitly only for the
nonpolyhedral summands, since `Function.HasPolyhedralEpigraph` already supplies convexity on the
polyhedral branch. -/
theorem convexConjugate_sum_eq_cl_finiteInfimalConvolution_of_mixedPolyhedralDomain
    (hf_convex : ∀ i, ¬ (f i).HasPolyhedralEpigraph → (f i).IsConvex 𝕜)
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hdom : f.HasMixedPolyhedralDomainPoint) :
    (∑ i, f i)⋆ =
      cl(finiteInfimalConvolution (fun i ↦ (f i)⋆)) :=
    sorry

/-- Properness-form restatement of Theorem 20.0.4. This companion adds no new mathematics: the
mixed domain hypothesis already provides the somewhere-finite part of properness for every
summand, so `Function.IsProper (f i)` is used here only through the pointwise consequence
`⊥ < f i x`. -/
theorem
    convexConjugate_sum_eq_cl_finiteInfimalConvolution_of_proper_mixedPolyhedralDomain
    (hf_convex : ∀ i, ¬ (f i).HasPolyhedralEpigraph → (f i).IsConvex 𝕜)
    (hf_proper : ∀ i, (f i).IsProper)
    (hdom : f.HasMixedPolyhedralDomainPoint) :
    (∑ i, f i)⋆ =
      cl(finiteInfimalConvolution (fun i ↦ (f i)⋆)) := by
  simpa using
    convexConjugate_sum_eq_cl_finiteInfimalConvolution_of_mixedPolyhedralDomain
      f hf_convex (fun i x ↦ (hf_proper i).bot_lt x) hdom

end
