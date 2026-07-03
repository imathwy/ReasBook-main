import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_21_1_1 (from Chap04) -/
noncomputable section

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item gives an explicit pair of convex `[-∞, +∞]`-valued functions on
  `ℝ`, packaged by the canonical two-branch family `sqrt_counterexample_family`, showing that the
  multiplier conclusion fails without the relative-interior domain hypothesis.
- `core/canonical`: the project codomain owner layer is `WithTopBot ℝ`; branch convexity is kept
  on the canonical set owner `ConvexOn ℝ (Set.univ : Set ℝ)`, together with the project owner
  `dom(·)` for the effective domain,
  mathlib's `intrinsicInterior ℝ`, and the Chapter 21 owner-side bridges
  `strictConvexInequalitySolutionSet_nonempty_iff_exists` and
  `Function.IsNonnegativeZeroBoundCertificateOn`.
- `bridge/view`: the source pair is assembled directly into the canonical two-branch family
  `sqrt_counterexample_family`; the domain-hypothesis failure is exposed first by the intrinsic
  negative-point witness `x ∉ dom(sqrt_counterexample_left_function)` for `x < 0`, and only then
  specialized to the concrete `x = -1` and to the
  textbook `ri[ℝ](C) ⊆ dom f₁` surface at `C = ℝ`.

Domain-style sampling used here:
- the canonical set owner `ConvexOn` at `Set.univ` for the branch convexity surface;
- the project owner `dom(·)` and bridge lemma `mem_effectiveDomain` from `Definition_4_4`;
- the owner-side feasible bridge `strictConvexInequalitySolutionSet_nonempty_iff_exists` and the
  direct multiplier-certificate owner
  `Function.IsNonnegativeZeroBoundCertificateOn` from `Theorem_21_1`.

Primitive data vs derived API:
- primitive data: the left branch `sqrt_counterexample_left_function` and the canonical family
  `sqrt_counterexample_family`;
- derived API: the owner-level convexity of the two branches, the absence of a strict feasible
  point for `sqrt_counterexample_family`, the
  failure of the Chapter 21 multiplier-certificate conclusion, and the failure of the
  relative-interior domain inclusion.

Abstraction audit:
- scalar/codomain: this item remains at `ℝ` / `WithTopBot ℝ` because its primitive owner data is
  the branch `x ↦ -Real.sqrt x`, and the Chapter 21 multiplier owner reused below is itself a
  real-weighted `WithTopBot ℝ` statement.
- ambient set surface: the primary non-domain statement is kept independent of `Set.univ`
  (`x < 0 → x ∉ dom(...)`), with the `x = -1` and `ri[ℝ]((Set.univ : Set ℝ))` formulations
  retained as direct Chapter 21 specializations.
-/

/-- The left function in the Chapter 21 counterexample equals `-√x` on `[0, ∞)` and `+∞` on
`(-∞, 0)`. -/
def sqrt_counterexample_left_function : ℝ → WithTopBot ℝ :=
  fun x ↦ if 0 ≤ x then ((-Real.sqrt x : ℝ) : WithTopBot ℝ) else ⊤

/-- Intrinsic two-branch index type for the Chapter 21.1.1 counterexample family. -/
inductive SqrtCounterexampleBranch where
  /-- Left branch carrying the `-√x`/`+∞` function. -/
  | left
  /-- Right branch carrying the identity function. -/
  | right
  deriving DecidableEq, Fintype

/-- The right function in the Chapter 21.1.1 counterexample is `x ↦ x`. -/
def sqrt_counterexample_right_function : ℝ → WithTopBot ℝ :=
  id.toWithTopBot

/-- The canonical two-branch family attached to the Chapter 21 counterexample. -/
def sqrt_counterexample_family : SqrtCounterexampleBranch → ℝ → WithTopBot ℝ
  | .left => sqrt_counterexample_left_function
  | .right => sqrt_counterexample_right_function

-- Proof sketch: identify the epigraph with `{(x, t) | 0 ≤ x ∧ -√x ≤ t} ∪ {x < 0} ×ˢ Set.univ`.
-- The first piece is the epigraph of the concave map `x ↦ -√x` on `[0, ∞)`, and the second piece
-- is vertically trivial because the function is `⊤` on `(-∞, 0)`. Conclude via
-- `Function.isConvex_iff_convex_epigraph`.
/-- The left example function is convex on `ℝ`. -/
theorem sqrt_counterexample_left_function_convexOn :
    ConvexOn ℝ (Set.univ : Set ℝ) sqrt_counterexample_left_function := sorry

-- Proof sketch: the epigraph is the half-space `{(x, t) | x ≤ t}`, so
-- `Function.isConvex_iff_convex_epigraph` gives the owner predicate.
/-- The right branch `x ↦ x`, viewed in `WithTopBot ℝ`, is convex on `ℝ`. -/
theorem sqrt_counterexample_right_branch_convexOn :
    ConvexOn ℝ (Set.univ : Set ℝ) sqrt_counterexample_right_function := sorry

/-- Owner-level convexity packaging for the canonical two-branch counterexample family. -/
theorem sqrt_counterexample_family_convexOn :
    ∀ i : SqrtCounterexampleBranch,
      ConvexOn ℝ (Set.univ : Set ℝ) (sqrt_counterexample_family i) := by
  intro i
  cases i
  · simpa [sqrt_counterexample_family] using sqrt_counterexample_left_function_convexOn
  · simpa [sqrt_counterexample_family, sqrt_counterexample_right_function] using
      sqrt_counterexample_right_branch_convexOn

-- Proof sketch: if `x < 0`, then the right function is strictly negative but the left one is
-- `⊤`; if `x ≥ 0`, then the left function is nonpositive while the right function is nonnegative.
/-- Owner-form strict infeasibility for the Chapter 21 counterexample family on `ℝ`. -/
theorem sqrt_counterexample_strict_convexInequalitySolutionSet_empty :
    ¬ (strictConvexInequalitySolutionSet sqrt_counterexample_family).Nonempty := sorry

/-- Source-facing strict infeasibility for the Chapter 21 counterexample family. -/
theorem no_common_strictly_negative_point_for_sqrt_counterexample :
    ¬ ∃ x : ℝ,
      ∀ i : SqrtCounterexampleBranch, sqrt_counterexample_family i x < (0 : WithTopBot ℝ) := by
  intro hstrict
  have hnonempty :
      (strictConvexInequalitySolutionSet sqrt_counterexample_family).Nonempty := by
    exact
      (strictConvexInequalitySolutionSet_nonempty_iff_exists sqrt_counterexample_family).2 hstrict
  exact sqrt_counterexample_strict_convexInequalitySolutionSet_empty hnonempty

-- Proof sketch: if `lam1 > 0`, then for sufficiently small `x > 0` one has
-- `lam2 * x < lam1 * √x`, so the value `-lam1 * √x + lam2 * x` is negative, contradicting the
-- assumed certificate inequality. Hence `lam1 = 0`. Evaluating the remaining inequality at
-- negative `x` then forces `lam2 = 0`, so the nontriviality clause in Theorem 21.1 cannot be
-- satisfied.
/-- Owner-form failure of Theorem 21.1's multiplier certificate on the canonical `...On` owner,
specialized to `C = ℝ`. -/
theorem sqrt_counterexample_no_nonnegativeZeroBoundCertificateOn :
    ¬ ∃ w : SqrtCounterexampleBranch → ℝ,
      w.IsNonnegativeZeroBoundCertificateOn (Set.univ : Set ℝ) sqrt_counterexample_family := sorry

/-- Whole-space specialization bridge from the canonical `...On` owner to the non-`On` owner. -/
theorem sqrt_counterexample_no_nonnegativeZeroBoundCertificate :
    ¬ ∃ w : SqrtCounterexampleBranch → ℝ,
      w.IsNonnegativeZeroBoundCertificate sqrt_counterexample_family := by
  simpa [Function.IsNonnegativeZeroBoundCertificate] using
    sqrt_counterexample_no_nonnegativeZeroBoundCertificateOn

/-- Text 21.1.1: the family `sqrt_counterexample_family` admits no nontrivial
nonnegative multiplier family in the sense of Theorem 21.1. -/
theorem no_nonnegative_multiplier_certificate_for_sqrt_counterexample :
    ¬ ∃ w : SqrtCounterexampleBranch → ℝ,
      (∀ i : SqrtCounterexampleBranch, 0 ≤ w i) ∧
      w ≠ 0 ∧
      ∀ x : ℝ, (0 : WithTopBot ℝ) ≤
        ∑ i, (w i : WithTopBot ℝ) * sqrt_counterexample_family i x := by
  intro hcert
  apply sqrt_counterexample_no_nonnegativeZeroBoundCertificate
  rcases hcert with ⟨w, hw_nonneg, hw_ne, hw_sum⟩
  refine ⟨w, ?_⟩
  exact
    (Function.isNonnegativeZeroBoundCertificate_iff
      (w := w) (f := sqrt_counterexample_family)).2
      ⟨hw_nonneg, hw_ne, hw_sum⟩

-- Proof sketch: by definition the left branch is `⊤` at every negative point.
/-- Any negative point lies outside the effective domain of the left branch of the Chapter 21
counterexample. -/
theorem not_mem_dom_sqrt_counterexample_left_function_of_lt_zero
    {x : ℝ} (hx : x < 0) :
    x ∉ dom(sqrt_counterexample_left_function) := by
  rw [mem_effectiveDomain, sqrt_counterexample_left_function]
  simp [if_neg (not_le.mpr hx)]

/-- Concrete specialization of
`not_mem_dom_sqrt_counterexample_left_function_of_lt_zero` at `x = -1`. -/
theorem neg_one_not_mem_dom_sqrt_counterexample_left_function :
    (-1 : ℝ) ∉ dom(sqrt_counterexample_left_function) := by
  exact
    not_mem_dom_sqrt_counterexample_left_function_of_lt_zero
      (x := (-1 : ℝ)) (by norm_num)

/-!
The domain failure can be phrased intrinsically on any ambient set whose relative interior
contains a negative point; the `x = -1` and `C = ℝ` statements are direct specializations.
-/
/-- Any set whose relative interior contains a negative point fails the domain inclusion for the
left branch. -/
theorem ri_not_subset_dom_sqrt_counterexample_left_function_of_exists_neg_mem_ri
    {C : Set ℝ} (hneg : ∃ x : ℝ, x < 0 ∧ x ∈ ri[ℝ](C)) :
    ¬ ri[ℝ](C) ⊆ dom(sqrt_counterexample_left_function) := by
  rcases hneg with ⟨x, hxneg, hxri⟩
  intro hsubset
  exact
    not_mem_dom_sqrt_counterexample_left_function_of_lt_zero hxneg
      (hsubset hxri)

/-- Any set whose relative interior contains `-1` fails the domain inclusion for the left branch. -/
theorem ri_not_subset_dom_sqrt_counterexample_left_function_of_neg_one_mem_ri
    {C : Set ℝ} (hnegOne : (-1 : ℝ) ∈ ri[ℝ](C)) :
    ¬ ri[ℝ](C) ⊆ dom(sqrt_counterexample_left_function) := by
  exact
    ri_not_subset_dom_sqrt_counterexample_left_function_of_exists_neg_mem_ri
      (C := C) ⟨-1, by norm_num, hnegOne⟩

-- Proof sketch: `ri[ℝ]((Set.univ : Set ℝ)) = Set.univ`, so `x = -1` belongs to that relative
-- interior; combine with `neg_one_not_mem_dom_sqrt_counterexample_left_function`.
/-- The relative interior of `C = ℝ` is not contained in the finite-value domain of the left
counterexample function. -/
theorem relativeInterior_not_subset_dom_sqrt_counterexample_left_function :
    ¬ ri[ℝ]((Set.univ : Set ℝ)) ⊆ dom(sqrt_counterexample_left_function) := by
  exact
    ri_not_subset_dom_sqrt_counterexample_left_function_of_neg_one_mem_ri
      (C := (Set.univ : Set ℝ)) (by simp)

/-- Any set whose relative interior contains a negative point cannot satisfy the Chapter 21 domain
hypothesis for the full two-branch counterexample family. -/
theorem sqrt_counterexample_hdom_fails_of_exists_neg_mem_ri
    {C : Set ℝ} (hneg : ∃ x : ℝ, x < 0 ∧ x ∈ ri[ℝ](C)) :
    ¬ ∀ i : SqrtCounterexampleBranch, ri[ℝ](C) ⊆ dom(sqrt_counterexample_family i) := by
  intro hdom
  exact
    ri_not_subset_dom_sqrt_counterexample_left_function_of_exists_neg_mem_ri
      (C := C) hneg
      (by simpa [sqrt_counterexample_family] using (hdom .left))

/-- Any set whose relative interior contains `-1` cannot satisfy the Chapter 21 domain
hypothesis for the full two-branch counterexample family. -/
theorem sqrt_counterexample_hdom_fails_of_neg_one_mem_ri
    {C : Set ℝ} (hnegOne : (-1 : ℝ) ∈ ri[ℝ](C)) :
    ¬ ∀ i : SqrtCounterexampleBranch, ri[ℝ](C) ⊆ dom(sqrt_counterexample_family i) := by
  exact
    sqrt_counterexample_hdom_fails_of_exists_neg_mem_ri
      (C := C) ⟨-1, by norm_num, hnegOne⟩

/-- The Chapter 21 relative-interior domain hypothesis fails for the full two-branch family. -/
theorem sqrt_counterexample_hdom_fails :
    ¬ ∀ i : SqrtCounterexampleBranch, ri[ℝ]((Set.univ : Set ℝ)) ⊆ dom(sqrt_counterexample_family i) := by
  exact
    sqrt_counterexample_hdom_fails_of_neg_one_mem_ri
      (C := (Set.univ : Set ℝ)) (by simp)

/-! ### Theorem_21_1 (from Chap04) -/
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
