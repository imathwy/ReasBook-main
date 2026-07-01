import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_21_0_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

noncomputable section

section

variable {E : Type*}
variable {ι : Type*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 21.1 is Rockafellar's alternative for a finite system of strict convex
  inequalities on a convex set `C`: either there is a point of `C` where every inequality is
  strict, or there is a nontrivial nonnegative multiplier certificate whose weighted sum is
  nonnegative on all of `C`.
- `core/canonical`: the owner abstractions already present in the project are
  `strictConvexInequalitySolutionSet` for the strict feasible region at the primitive `<` layer,
  `ConvexOn 𝕜 C`, the pointwise `⊥`-exclusion used elsewhere in Chapter 21, the
  scalar-parameterized relative interior `ri[𝕜](C)`, the effective-domain notation `dom(f)`, and
  the logical exclusive-or `Xor'`.
- `bridge/view`: Rockafellar's strict system `fᵢ(x) < 0` is expressed by the owner feasible set
  `C ∩ strictConvexInequalitySolutionSet f`, while the textbook hypothesis
  `dom fᵢ ⊇ ri C` is stated through `ri[𝕜](C) ⊆ dom(f i)` and the multiplier conclusion is written
  as a `WithTopBot 𝕜`-valued finite sum on `C`.

Domain-style sampling used here:
- `strictConvexInequalitySolutionSet` and `mem_strictConvexInequalitySolutionSet`;
- `ConvexOn`;
- `Function.IsProper.bot_lt`;
- `dom(f)`;
- `ri[𝕜](·)`;
- `Xor'`.

Primitive data vs derived API:
- primitive inputs: a convex set `C`, an indexed family
  `f : ι → E → WithTopBot 𝕜`,
  convexity-on-`C` of each `f i`, the pointwise exclusion `∀ i x, ⊥ < f i x`, and the
  relative-interior domain inclusion;
- derived API: the owner strict-feasible region
  `C ∩ strictConvexInequalitySolutionSet f`, the source-facing bridge back
  to `∃ x ∈ C, ∀ i, f i x < 0`, and the direct multiplier-certificate clause
  `∃ w, (∀ i, 0 ≤ w i) ∧ w ≠ 0 ∧ ∀ x ∈ C, 0 ≤ ∑ i, wᵢ fᵢ(x)`.

Abstraction audit:
- codomain: this item is stated at the `WithTopBot 𝕜` layer rather than on a concrete
  `EReal`/`ℝ` specialization.
- scalar/ambient: the theorem surface is parameterized by the weaker primitive layer
  `LinearOrderedRing 𝕜` and a topological `𝕜`-module `E`; no finite-dimensional or continuity
  hypotheses are built into the owner-level statement.

Layer target: `source-facing`, with the strict system routed through the Chapter 21 owner
`C ∩ strictConvexInequalitySolutionSet f` and the textbook pointwise wording
retained only as a thin companion bridge. The multiplier side stays source-facing as the direct
existence of a nonnegative nontrivial multiplier family.
-/
theorem strict_convexInequalitySolutionSet_nonempty_iff
    {α : Type*} [LT α] [Zero α] {C : Set E} (f : ι → E → α) :
    (C ∩ strictConvexInequalitySolutionSet f).Nonempty ↔
      ∃ x : E, x ∈ C ∧ ∀ i : ι, f i x < 0 := by
  constructor
  · rintro ⟨x, hxC, hxstrict⟩
    exact ⟨x, hxC, mem_strictConvexInequalitySolutionSet.mp hxstrict⟩
  · rintro ⟨x, hxC, hxstrict⟩
    exact ⟨x, hxC, mem_strictConvexInequalitySolutionSet.mpr hxstrict⟩

/-- Whole-space companion bridge: strict-feasible-set nonemptiness is equivalent to existence of a
point satisfying all strict inequalities. -/
theorem strictConvexInequalitySolutionSet_nonempty_iff_exists
    {α : Type*} [LT α] [Zero α] (f : ι → E → α) :
    (strictConvexInequalitySolutionSet f).Nonempty ↔
      ∃ x : E, ∀ i : ι, f i x < 0 := by
  simpa using
    (strict_convexInequalitySolutionSet_nonempty_iff (C := (Set.univ : Set E)) f)

section

variable {𝕜 : Type*}
variable [Fintype ι] [Nonempty ι]
variable [LinearOrderedRing 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]

-- Proof sketch: the two alternatives are mutually exclusive because any nonzero nonnegative
-- multiplier vector evaluates negatively at a strictly feasible point. If the strict-feasibility
-- alternative fails, separate the convex image
-- `{ζ | ∃ x ∈ C, ∀ i, f i x < ζ i}` from the nonpositive orthant in the finite coordinate space
-- `ι → 𝕜` using Theorem 11.3 to
-- obtain a nonzero vector of nonnegative multipliers. The resulting weighted sum is nonnegative
-- on `C ∩ ⋂ i dom(f i)`, and Corollary 7.3.3 extends this inequality from the relative
-- interior setup to all of `C`.
/-- Theorem 21.1: for a convex set `C` in a topological `𝕜`-module and a finite nonempty family
of convex functions `fᵢ` whose effective domains contain `ri[𝕜](C)` and which never take the value
`⊥`, exactly one of the following alternatives holds: either the owner
strict-feasible set `C ∩ strictConvexInequalitySolutionSet f` is nonempty, or there is a
nonzero nonnegative multiplier vector `λ` such that `∑ i λᵢ fᵢ x ≥ 0` for every `x ∈ C`. The
owner feasible side is stated with the Chapter 21 feasible-set owner, and the multiplier side is
kept as the direct source-facing certificate existence clause. The plain pointwise wording is
recovered immediately below as a thin companion, and the properness wording is recovered after
that since the somewhere-finite part of properness is not primitive data for this alternative. -/
theorem xor_strict_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate
    {C : Set E} (f : ι → E → WithTopBot 𝕜) (hC : Convex 𝕜 C)
    (hf_convex : ∀ i, ConvexOn 𝕜 C (f i))
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hdom : ∀ i, ri[𝕜](C) ⊆ dom(f i)) :
    Xor'
      ((C ∩ strictConvexInequalitySolutionSet f).Nonempty)
      (∃ w : ι → 𝕜, w.IsNonnegativeZeroBoundCertificateOn C f) := sorry

/-- Source-facing pointwise restatement of Theorem 21.1: the owner strict-feasible-set
alternative is equivalent to existence of `x ∈ C` with `f i x < 0` for every `i`. -/
theorem xor_exists_strict_feasible_point_or_nonnegative_multiplier_certificate
    {C : Set E} (f : ι → E → WithTopBot 𝕜) (hC : Convex 𝕜 C)
    (hf_convex : ∀ i, ConvexOn 𝕜 C (f i))
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hdom : ∀ i, ri[𝕜](C) ⊆ dom(f i)) :
    Xor'
      (∃ x : E, x ∈ C ∧ ∀ i, f i x < 0)
      (∃ w : ι → 𝕜, w.IsNonnegativeZeroBoundCertificateOn C f) := by
  simpa [strict_convexInequalitySolutionSet_nonempty_iff f] using
    xor_strict_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate
      f hC hf_convex hf_bot hdom

/-- Properness-form restatement of Theorem 21.1. This companion adds no new mathematics: its only
use of `Function.IsProper (f i)` is to recover the pointwise `⊥`-exclusion needed by the main
theorem. -/
theorem
    xor_strict_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate_of_proper
    {C : Set E} (f : ι → E → WithTopBot 𝕜) (hC : Convex 𝕜 C)
    (hf_convex : ∀ i, ConvexOn 𝕜 C (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (hdom : ∀ i, ri[𝕜](C) ⊆ dom(f i)) :
    Xor'
      ((C ∩ strictConvexInequalitySolutionSet f).Nonempty)
      (∃ w : ι → 𝕜, w.IsNonnegativeZeroBoundCertificateOn C f) := by
  exact
    xor_strict_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate
      f hC hf_convex (fun i x ↦ (hf_proper i).bot_lt x) hdom

/-- Properness-form source-facing restatement of Theorem 21.1. -/
theorem xor_exists_strict_feasible_point_or_nonnegative_multiplier_certificate_of_proper
    {C : Set E} (f : ι → E → WithTopBot 𝕜) (hC : Convex 𝕜 C)
    (hf_convex : ∀ i, ConvexOn 𝕜 C (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (hdom : ∀ i, ri[𝕜](C) ⊆ dom(f i)) :
    Xor'
      (∃ x : E, x ∈ C ∧ ∀ i, f i x < 0)
      (∃ w : ι → 𝕜, w.IsNonnegativeZeroBoundCertificateOn C f) := by
  simpa [strict_convexInequalitySolutionSet_nonempty_iff f] using
    xor_strict_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate_of_proper
      f hC hf_convex hf_proper hdom

end

end
