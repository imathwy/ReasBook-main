import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_20_0_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Rockafellar

noncomputable section

section

namespace Function

variable {𝕜 : Type*} [Semiring 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
variable {α : Type*} [AddCommMonoid α] [Module 𝕜 α] [Preorder α]
variable {m : ℕ}

/-- The first `k` summands in a finite family have polyhedral epigraphs. -/
abbrev HasPolyhedralPrefix (f : Fin m → E → WithTopBot α) (k : ℕ) : Prop :=
  ∀ i : Fin m, (i : ℕ) < k → (f i).HasPolyhedralEpigraph

end Function

end

section

namespace Function

variable {𝕜 : Type*} [Ring 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable {β : Type*} [LT β] [Top β]
variable {m : ℕ}

/-- A finite family has a point in the domains of the first `k` members and in the relative
interiors of the remaining members. -/
abbrev HasMixedPrefixDomainPoint
    (f : Fin m → E → β) (k : ℕ) : Prop :=
  ∃ x : E,
    (∀ i : Fin m, (i : ℕ) < k → x ∈ dom(f i)) ∧
      ∀ i : Fin m, k ≤ (i : ℕ) → x ∈ riDom[𝕜](f i)

end Function

end

section

variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E]
  [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable {m : ℕ}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 20.1 states the Fenchel-type formula for the conjugate of a finite sum
  of proper convex functions when a prefix of the family is polyhedral and the remaining effective
  domains have a common relative-interior point with that prefix-domain intersection.
- `core/canonical`: the upstream owner theorem for the mixed regularity hypothesis is
  `convexConjugate_sum_eq_cl_finiteInfimalConvolution_of_mixedPolyhedralDomain`
  from `Theorem_20_0_4`,
  together with the Chapter 1 owner `finiteInfimalConvolution` and its specification theorem
  `finiteInfimalConvolution_eq_sInf_decompositions`.
- `bridge/view`: this file now exposes both layers: a canonical finite-family theorem on the
  intrinsic owner hypothesis `Function.HasMixedPolyhedralDomainPoint`, and source-facing prefix
  wrappers matching Rockafellar's "first `k` polyhedral" presentation. A private helper lemma
  translates the prefix hypotheses into the intrinsic owner hypothesis.

Domain-style sampling used here:
- `convexConjugate_sum_eq_cl_finiteInfimalConvolution_of_mixedPolyhedralDomain`
  and its thin properness companion
  `convexConjugate_sum_eq_cl_finiteInfimalConvolution_of_proper_mixedPolyhedralDomain`
  from `Theorem_20_0_4`;
- `finiteInfimalConvolution` and `finiteInfimalConvolution_eq_sInf_decompositions`;
- `Function.IsConvex` and `Function.IsProper.bot_lt`;
- `convexConjugate` with the chapter notation `f⋆`;
- `Function.HasPolyhedralEpigraph`;
- the chapter domain vocabulary `dom(f)` / `riDom[𝕜](f)`;
- `Function.HasPolyhedralEpigraph.isConvex`.

Primitive data vs derived API:
- primitive inputs: a finite family `f : Fin m → E → WithTopBot 𝕜`;
- primitive owner-side exclusion of `⊥`: `∀ i x, ⊥ < f i x`;
- theorem-local source hypotheses: the explicit prefix polyhedrality condition
  `∀ i : Fin m, (i : ℕ) < k → (f i).HasPolyhedralEpigraph`, the suffix-convexity condition
  `∀ i : Fin m, k ≤ (i : ℕ) → (f i).IsConvex`, and the mixed domain condition
  `∃ x : E, (∀ i : Fin m, (i : ℕ) < k → x ∈ dom(f i)) ∧
    ∀ i : Fin m, k ≤ (i : ℕ) → x ∈ riDom[𝕜](f i)`;
- derived API: canonical mixed-owner conjugate/decomposition/attainment theorems and their
  properness companions, together with source-facing prefix wrappers for Theorem 20.1.
  `WithTopBot 𝕜`; the upstream theorem imported from `Theorem_20_0_4` is still exposed through
  the legacy alias spelling.
-/

variable (f : Fin m → E → WithTopBot 𝕜) (k : ℕ)

omit [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)] [IsStrictOrderedRing 𝕜]
  [DenselyOrdered 𝕜] [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜]
  [HasContinuousPairing E E 𝕜] in
private theorem mixedPolyhedralData_of_polyhedralPrefix
    (hf_suffixConvex : ∀ i : Fin m, k ≤ (i : ℕ) → (f i).IsConvex 𝕜)
    (hpoly : f.HasPolyhedralPrefix k)
    (hdom : f.HasMixedPrefixDomainPoint k) :
    (∀ i : Fin m, ¬ (f i).HasPolyhedralEpigraph → (f i).IsConvex 𝕜) ∧
      f.HasMixedPolyhedralDomainPoint := by
  rcases hdom with ⟨x, hx_prefix, hx_suffix⟩
  refine ⟨?_, ?_⟩
  · intro i hi_not_poly
    by_cases hik : (i : ℕ) < k
    · exact False.elim (hi_not_poly (hpoly i hik))
    · exact hf_suffixConvex i (Nat.le_of_not_gt hik)
  · refine (Function.hasMixedPolyhedralDomainPoint_iff (𝕜 := 𝕜) (f := f)).2 ?_
    refine ⟨x, ?_⟩
    constructor
    · intro i hi_poly
      by_cases hik : (i : ℕ) < k
      · exact hx_prefix i hik
      · exact intrinsicInterior_subset (hx_suffix i (Nat.le_of_not_gt hik))
    · intro i hi_not_poly
      by_cases hik : (i : ℕ) < k
      · exact False.elim (hi_not_poly (hpoly i hik))
      · exact hx_suffix i (Nat.le_of_not_gt hik)

section CanonicalMixed

variable {ι : Type*} [Fintype ι]
variable (f : ι → E → WithTopBot 𝕜)

-- Proof sketch: this is the intrinsic finite-family owner statement corresponding to Theorem
-- 20.1, with the mixed hypothesis already presented in the canonical owner language
-- `Function.HasMixedPolyhedralDomainPoint`.
/-- Canonical mixed-owner form of Theorem 20.1: for a finite family in the intrinsic
`HasMixedPolyhedralDomainPoint` presentation, if nonpolyhedral summands are convex and every
summand is pointwise strictly above `⊥`, then the conjugate of the finite sum equals the finite
infimal convolution of the conjugates. -/
theorem convexConjugate_sum_eq_finiteInfimalConvolution_of_mixedPolyhedralDomain
    (hf_convex : ∀ i, ¬ (f i).HasPolyhedralEpigraph → (f i).IsConvex 𝕜)
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hdom : f.HasMixedPolyhedralDomainPoint) :
    ((∑ i, f i)⋆ : E → WithTopBot 𝕜) =
      finiteInfimalConvolution (fun i ↦ (f i)⋆) := by
  sorry

/-- Properness-form restatement of the canonical mixed-owner theorem. -/
theorem
    convexConjugate_sum_eq_finiteInfimalConvolution_of_proper_mixedPolyhedralDomain
    (hf_convex : ∀ i, ¬ (f i).HasPolyhedralEpigraph → (f i).IsConvex 𝕜)
    (hf_proper : ∀ i, (f i).IsProper)
    (hdom : f.HasMixedPolyhedralDomainPoint) :
    ((∑ i, f i)⋆ : E → WithTopBot 𝕜) =
      finiteInfimalConvolution (fun i ↦ (f i)⋆) := by
  simpa using
    convexConjugate_sum_eq_finiteInfimalConvolution_of_mixedPolyhedralDomain
      f hf_convex (fun i x ↦ (hf_proper i).bot_lt x) hdom

/-- Canonical mixed-owner decomposition formula corresponding to Theorem 20.1. -/
theorem convexConjugate_sum_eq_sInf_decompositions_of_mixedPolyhedralDomain
    (hf_convex : ∀ i, ¬ (f i).HasPolyhedralEpigraph → (f i).IsConvex 𝕜)
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hdom : f.HasMixedPolyhedralDomainPoint)
    (xStar : E) :
    ((∑ i, f i)⋆ xStar) =
      sInf {r : WithTopBot 𝕜 | ∃ xs : ι → E, (∑ i, xs i) = xStar ∧
        r = ∑ i, (f i)⋆ (xs i)} := by
  rw [convexConjugate_sum_eq_finiteInfimalConvolution_of_mixedPolyhedralDomain
      (f := f) hf_convex hf_bot hdom]
  simpa using
    (finiteInfimalConvolution_eq_sInf_decompositions
      (f := fun i ↦ ((f i)⋆ : E → WithTopBot 𝕜)) xStar)

/-- Properness-form restatement of the canonical mixed-owner decomposition formula. -/
theorem
    convexConjugate_sum_eq_sInf_decompositions_of_proper_mixedPolyhedralDomain
    (hf_convex : ∀ i, ¬ (f i).HasPolyhedralEpigraph → (f i).IsConvex 𝕜)
    (hf_proper : ∀ i, (f i).IsProper)
    (hdom : f.HasMixedPolyhedralDomainPoint)
    (xStar : E) :
    ((∑ i, f i)⋆ xStar) =
      sInf {r : WithTopBot 𝕜 | ∃ xs : ι → E, (∑ i, xs i) = xStar ∧
        r = ∑ i, (f i)⋆ (xs i)} := by
  simpa using
    convexConjugate_sum_eq_sInf_decompositions_of_mixedPolyhedralDomain
      f hf_convex (fun i x ↦ (hf_proper i).bot_lt x) hdom xStar

section

variable [Nonempty ι]

-- Proof sketch: this is the canonical mixed-owner attainment clause corresponding to Theorem 20.1.
/-- Canonical mixed-owner attainment clause corresponding to Theorem 20.1. -/
theorem exists_sum_eq_finiteInfimalConvolution_conjugates_of_mixedPolyhedralDomain
    (hf_convex : ∀ i, ¬ (f i).HasPolyhedralEpigraph → (f i).IsConvex 𝕜)
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hdom : f.HasMixedPolyhedralDomainPoint)
    (xStar : E) :
    ∃ xsStar : ι → E,
      (∑ i, xsStar i) = xStar ∧
        finiteInfimalConvolution (fun i ↦ (f i)⋆) xStar =
          ∑ i, (f i)⋆ (xsStar i) := by
  sorry

/-- Properness-form restatement of the canonical mixed-owner attainment clause. -/
theorem
    exists_sum_eq_finiteInfimalConvolution_conjugates_of_proper_mixedPolyhedralDomain
    (hf_convex : ∀ i, ¬ (f i).HasPolyhedralEpigraph → (f i).IsConvex 𝕜)
    (hf_proper : ∀ i, (f i).IsProper)
    (hdom : f.HasMixedPolyhedralDomainPoint)
    (xStar : E) :
    ∃ xsStar : ι → E,
      (∑ i, xsStar i) = xStar ∧
        finiteInfimalConvolution (fun i ↦ (f i)⋆) xStar =
          ∑ i, (f i)⋆ (xsStar i) := by
  simpa using
    exists_sum_eq_finiteInfimalConvolution_conjugates_of_mixedPolyhedralDomain
      f hf_convex (fun i x ↦ (hf_proper i).bot_lt x) hdom xStar

end

end CanonicalMixed

-- Proof sketch: apply the theorem's Fenchel-sum formula under the mixed-domain hypothesis to the
-- finite family `f`, first using `mixedPolyhedralData_of_polyhedralPrefix` to translate the
-- source prefix presentation to the owner-side mixed hypothesis of `Theorem_20_0_4`. The mixed
-- domain hypothesis already gives a common finite point for every summand, so the only extra
-- primitive side condition needed upstream is the pointwise exclusion `⊥ < f i x`. The project
-- owner for the decomposition infimum is
-- `finiteInfimalConvolution`, which packages the textbook infimum over all decompositions
-- `x₁⋆ + ··· + x_m⋆ = x⋆`. The polyhedral-prefix hypothesis supplies convexity on the first `k`
-- summands through `HasPolyhedralEpigraph.isConvex`, so explicit convexity is needed only on
-- the remaining suffix; together with the common-domain-point assumption, these are exactly the
-- source hypotheses needed to identify the conjugate of the sum with that owner.
/-- Theorem 20.1, in canonical ambient form: for convex `f₁, …, f_m` on a
finite-dimensional topological vector space equipped with a continuous linear self-pairing,
if the first
`k` are polyhedral, the remaining
summands are convex, the family is pointwise strictly above `⊥`, and some point lies in
`dom f₁ ∩ ··· ∩ dom f_k ∩ ri(dom f_{k+1}) ∩ ··· ∩ ri(dom f_m)`, then
`(f₁ + ··· + f_m)⋆ = f₁⋆ □ ··· □ f_m⋆`, rendered by
`finiteInfimalConvolution`. The textbook properness wording is
recovered immediately below as a thin companion, since `hdom` already supplies the
somewhere-finite clause. -/
theorem convexConjugate_sum_eq_finiteInfimalConvolution_of_polyhedralPrefix_mixedDomain
    (k : ℕ)
    (hf_suffixConvex : ∀ i : Fin m, k ≤ (i : ℕ) → (f i).IsConvex 𝕜)
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hpoly : f.HasPolyhedralPrefix k)
    (hdom : f.HasMixedPrefixDomainPoint k) :
    ((∑ i, f i)⋆ : E → WithTopBot 𝕜) =
      finiteInfimalConvolution (fun i ↦ (f i)⋆) := by
  rcases
    mixedPolyhedralData_of_polyhedralPrefix (f := f) (k := k)
      hf_suffixConvex hpoly hdom with ⟨hf_convex, hmixed⟩
  simpa using
    convexConjugate_sum_eq_finiteInfimalConvolution_of_mixedPolyhedralDomain
      (f := f) hf_convex hf_bot hmixed

/-- Properness-form restatement of Theorem 20.1. This companion adds no new mathematics: the
mixed domain hypothesis already provides the somewhere-finite clause for every summand, so
`Function.IsProper (f i)` is used only to recover the pointwise exclusion `⊥ < f i x`. -/
theorem
    convexConjugate_sum_eq_finiteInfimalConvolution_of_proper_polyhedralPrefix_mixedDomain
    (k : ℕ)
    (hf_suffixConvex : ∀ i : Fin m, k ≤ (i : ℕ) → (f i).IsConvex 𝕜)
    (hf_proper : ∀ i : Fin m, (f i).IsProper)
    (hpoly : f.HasPolyhedralPrefix k)
    (hdom : f.HasMixedPrefixDomainPoint k) :
    ((∑ i, f i)⋆ : E → WithTopBot 𝕜) =
      finiteInfimalConvolution (fun i ↦ (f i)⋆) := by
  simpa using
    convexConjugate_sum_eq_finiteInfimalConvolution_of_polyhedralPrefix_mixedDomain
      f k hf_suffixConvex (fun i x ↦ (hf_proper i).bot_lt x) hpoly hdom

-- Proof sketch: combine the main theorem above with the owner-side decomposition formula
-- `finiteInfimalConvolution_eq_sInf_decompositions`. This rewrites the canonical owner
-- `finiteInfimalConvolution (fun i ↦ convexConjugate (f i)) x⋆` as the textbook infimum over all
-- decompositions `∑ i, xᵢ⋆ = x⋆` of the sum `∑ i, fᵢ⋆(xᵢ⋆)`.
/-- Under the same hypotheses, with explicit convexity assumed only on the nonpolyhedral suffix
and `⊥ < f i x` as the primitive no-bottom input,
the conjugate of the finite sum at `x⋆` is the infimum
of `∑ i, fᵢ⋆(xᵢ⋆)` over all decompositions `∑ i, xᵢ⋆ = x⋆`. -/
theorem convexConjugate_sum_eq_sInf_decompositions_of_polyhedralPrefix_mixedDomain
    (k : ℕ)
    (hf_suffixConvex : ∀ i : Fin m, k ≤ (i : ℕ) → (f i).IsConvex 𝕜)
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hpoly : f.HasPolyhedralPrefix k)
    (hdom : f.HasMixedPrefixDomainPoint k)
    (xStar : E) :
    ((∑ i, f i)⋆ xStar) =
      sInf {r : WithTopBot 𝕜 | ∃ xs : Fin m → E, (∑ i, xs i) = xStar ∧
        r = ∑ i, (f i)⋆ (xs i)} := by
  rw [convexConjugate_sum_eq_finiteInfimalConvolution_of_polyhedralPrefix_mixedDomain
      (f := f) (k := k) hf_suffixConvex hf_bot hpoly hdom]
  simpa using
    (finiteInfimalConvolution_eq_sInf_decompositions
      (f := fun i ↦ ((f i)⋆ : E → WithTopBot 𝕜)) xStar)

/-- Properness-form restatement of the decomposition formula in Theorem 20.1. -/
theorem
    convexConjugate_sum_eq_sInf_decompositions_of_proper_polyhedralPrefix_mixedDomain
    (k : ℕ)
    (hf_suffixConvex : ∀ i : Fin m, k ≤ (i : ℕ) → (f i).IsConvex 𝕜)
    (hf_proper : ∀ i : Fin m, (f i).IsProper)
    (hpoly : f.HasPolyhedralPrefix k)
    (hdom : f.HasMixedPrefixDomainPoint k)
    (xStar : E) :
    ((∑ i, f i)⋆ xStar) =
      sInf {r : WithTopBot 𝕜 | ∃ xs : Fin m → E, (∑ i, xs i) = xStar ∧
        r = ∑ i, (f i)⋆ (xs i)} := by
  simpa using
    convexConjugate_sum_eq_sInf_decompositions_of_polyhedralPrefix_mixedDomain
      f k hf_suffixConvex (fun i x ↦ (hf_proper i).bot_lt x) hpoly hdom xStar

section

variable [NeZero m]

-- Proof sketch: Theorem 20.1 identifies the target value with the finite infimal convolution of
-- the conjugates. The source theorem also states that this infimum is attained; in the owner
-- language, that means some decomposition `xsStar` realizes the value of
-- `finiteInfimalConvolution (fun i ↦ convexConjugate (f i)) xStar`. The nonempty-family
-- assumption `[NeZero m]` is needed here because otherwise no decomposition can sum to a nonzero
-- `xStar`.
/-- Under the same hypotheses, for a nonempty finite family, the infimum defining the finite
infimal convolution of the conjugates is attained at every `x⋆`. The primitive no-bottom input is
`⊥ < f i x`; the properness-form restatement follows immediately below. -/
theorem exists_sum_eq_finiteInfimalConvolution_conjugates_of_polyhedralPrefix_mixedDomain
    (k : ℕ)
    (hf_suffixConvex : ∀ i : Fin m, k ≤ (i : ℕ) → (f i).IsConvex 𝕜)
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hpoly : f.HasPolyhedralPrefix k)
    (hdom : f.HasMixedPrefixDomainPoint k)
    (xStar : E) :
    ∃ xsStar : Fin m → E,
      (∑ i, xsStar i) = xStar ∧
        finiteInfimalConvolution (fun i ↦ (f i)⋆) xStar =
          ∑ i, (f i)⋆ (xsStar i) := by
  rcases
    mixedPolyhedralData_of_polyhedralPrefix (f := f) (k := k)
      hf_suffixConvex hpoly hdom with ⟨hf_convex, hmixed⟩
  simpa using
    exists_sum_eq_finiteInfimalConvolution_conjugates_of_mixedPolyhedralDomain
      (f := f) hf_convex hf_bot hmixed xStar

/-- Properness-form restatement of the attainment clause in Theorem 20.1. -/
theorem
    exists_sum_eq_finiteInfimalConvolution_conjugates_of_proper_polyhedralPrefix_mixedDomain
    (k : ℕ)
    (hf_suffixConvex : ∀ i : Fin m, k ≤ (i : ℕ) → (f i).IsConvex 𝕜)
    (hf_proper : ∀ i : Fin m, (f i).IsProper)
    (hpoly : f.HasPolyhedralPrefix k)
    (hdom : f.HasMixedPrefixDomainPoint k)
    (xStar : E) :
    ∃ xsStar : Fin m → E,
      (∑ i, xsStar i) = xStar ∧
        finiteInfimalConvolution (fun i ↦ (f i)⋆) xStar =
          ∑ i, (f i)⋆ (xsStar i) := by
  simpa using
    exists_sum_eq_finiteInfimalConvolution_conjugates_of_polyhedralPrefix_mixedDomain
      f k hf_suffixConvex (fun i x ↦ (hf_proper i).bot_lt x) hpoly hdom xStar

end

end
