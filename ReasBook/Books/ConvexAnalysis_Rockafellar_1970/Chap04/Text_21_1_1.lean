import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_21_1

-- Declarations for this item will be appended below by the statement pipeline.

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
