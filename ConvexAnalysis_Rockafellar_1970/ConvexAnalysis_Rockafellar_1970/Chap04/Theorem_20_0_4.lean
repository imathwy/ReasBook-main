import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_8

-- Declarations for this item will be appended below by the statement pipeline.

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
