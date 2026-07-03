import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_10_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section
open scoped Pointwise

variable {ι : Type*}

/- Definition 7.33 lies in the sign-symmetric convex-set domain, with finiteness used only for the
convex-box characterization.

Sampled owner-style declarations:
* `EuclideanSpace.nonnegativeOrthant` and `EuclideanSpace.mem_nonnegativeOrthant_iff` from
  `Chap01/Definition_1_10_2`, the chapter owner for the orthant `ℝⁿ_+`;
* `zeroOneBox` in `Chap01/Definition_1_3_1`, the nearby project owner pattern for intrinsic
  coordinatewise boxes;
* `Pi.abs_apply`, the canonical pointwise absolute-value surface on `ι → ℝ`;
* `Pi.smul_apply`, the canonical pointwise scalar action of `ι → ℝ` on `EuclideanSpace ℝ ι`;
* the later Chapter 7 duplicate local copies in `Theorem_7_8` and `Definition_7_70`, which should
  reuse the owners introduced here rather than re-own them.

Best owner abstraction:
* source-facing: `signVectorSet`, `symmetricBox`, and `IsSignInvariant`;
* core/canonical: the ambient pointwise absolute value on `ι → ℝ`, the pointwise scalar action of
  `ι → ℝ` on `EuclideanSpace ℝ ι`, together with the chapter orthant owner `nonnegativeOrthant`
  after the textbook specialization `ι = Fin n`;
* bridge/view: the coordinatewise membership lemmas and the convex-set characterization by
  symmetric boxes.

Primitive data:
* the coordinate type `ι`;
* a coordinatewise radius function `g : ι → ℝ` for the textbook box `B(g)`;
* a subset `C : Set (EuclideanSpace ℝ ι)`.

Derived API:
* the coordinatewise membership criteria for the sign vectors and symmetric boxes;
* the closure lemma for sign-invariant sets;
* the convex equivalence with symmetric-box containment for the coordinatewise absolute values of
  points of the set.

This refinement keeps the source-facing owners introduced by Definition 7.33, but reowns the
textbook box `B(g)` by the intrinsic coordinatewise interval condition on `EuclideanSpace ℝ ι`
rather than through the implementation transport `ofLp`/`Set.pi`. The public theorem surface can
therefore use the canonical pointwise forms `σ • g` and `B(fun i ↦ |g i|)` directly. The textbook
`ℝⁿ` case is recovered by taking `ι = Fin n`. It leaves the box owner itself in this file so later
Chapter 7 files can reuse it directly instead of re-defining the same set under parallel names.
-/

/-- The sign vectors on a coordinate type `ι`, namely the functions whose coordinates are all
equal to `-1` or `1`. -/
abbrev signVectorSet (ι : Type*) : Set (ι → ℝ) :=
  Set.pi Set.univ fun _ ↦ ({(-1 : ℝ), 1} : Set ℝ)

/-- Membership in `signVectorSet ι` means that every coordinate is a sign. -/
@[simp]
theorem mem_signVectorSet_iff {σ : ι → ℝ} :
    σ ∈ signVectorSet ι ↔ ∀ i, σ i = -1 ∨ σ i = 1 :=
  by simp [signVectorSet]

local notation "E" => EuclideanSpace ℝ ι

/-- The symmetric box `B(g) = {s | -g ≤ s ≤ g}`. -/
abbrev symmetricBox (g : ι → ℝ) : Set E :=
  {s | ∀ i, s i ∈ Set.Icc (-g i) (g i)}

namespace SymmetricBox

/- Source-facing Lean notation for the textbook box `B(g)`. -/
scoped notation:max "B(" g:arg ")" => symmetricBox g

end SymmetricBox

open scoped SymmetricBox

/-- Membership in `symmetricBox g` is the coordinatewise inequality `-g ≤ s ≤ g`. -/
@[simp]
theorem mem_symmetricBox_iff {g : ι → ℝ} {s : E} :
    s ∈ B(g) ↔ ∀ i, -g i ≤ s i ∧ s i ≤ g i :=
  by
    simp [symmetricBox, Set.mem_Icc]

/-- Membership in the symmetric box `B(g)` means that every coordinate of `s` is bounded in
absolute value by the corresponding coordinate of `g`. -/
theorem mem_symmetricBox_iff_abs_le {g : ι → ℝ} {s : E} :
    s ∈ B(g) ↔ ∀ i, |s i| ≤ g i := by
  rw [mem_symmetricBox_iff]
  simp [abs_le]

/-- Definition 7.33: a set of coordinate vectors is sign-invariant when it is closed under
coordinatewise sign changes by arbitrary sign vectors. -/
def IsSignInvariant (C : Set E) : Prop :=
  ∀ g ∈ C, ∀ σ : ι → ℝ, σ ∈ signVectorSet ι → (σ • g : E) ∈ C

namespace IsSignInvariant

/-- A sign-invariant set contains every coordinatewise sign change of each of its points. -/
theorem smul_mem {C : Set E} (hC : IsSignInvariant C)
    {g : E} {σ : ι → ℝ} (hg : g ∈ C) (hσ : σ ∈ signVectorSet ι) :
    (σ • g : E) ∈ C :=
  hC g hg σ hσ

end IsSignInvariant

/-- If `C` is convex, sign-invariance is equivalent to containing the full symmetric box
`B(fun i ↦ |g i|)` for every point `g` of `C`. -/
-- Proof sketch: for the forward direction, each sign flip of `g` lies in `C`, so convexity keeps
-- the whole box `B(fun i ↦ |g i|)` inside `C` because its vertices are exactly those sign flips.
-- Conversely, every sign flip `σ ⊙ g` belongs to `B(fun i ↦ |g i|)`, so the assumed box
-- inclusion recovers sign-invariance.
theorem isSignInvariant_iff_symmetricBox_subset_of_convex
    [Finite ι] {C : Set E} (hC_convex : Convex ℝ C) :
    IsSignInvariant C ↔
      ∀ g ∈ C,
        B(fun i ↦ |g i|) ⊆ C := sorry
