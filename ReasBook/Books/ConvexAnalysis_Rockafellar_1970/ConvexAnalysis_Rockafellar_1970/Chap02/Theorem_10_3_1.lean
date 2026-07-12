import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_12
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_12
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_3

-- Declarations for this item will be appended below by the statement pipeline.

section

open Set
open scoped Rockafellar

variable {ι : Type*} [Fintype ι]

local notation "E" => (ι → ℝ)
local notation "C" => (orthant[ℝ](E))
local notation "riC" => ri[ℝ](C)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 10.3.1 is about a finite convex function on the positive orthant of
  `ℝ^ι` that is nondecreasing in each coordinate, and concludes first a bounded-above-on-bounded
  subsets property and then the canonical unique continuous convex extension to the nonnegative
  orthant.
- `core/canonical`: the owner objects already present in the project are
  `interior (orthant[ℝ](E) : Set E)`, `orthant[ℝ](E)`,
  the ambient coordinatewise order on `E`, the owner monotonicity predicate
  `MonotoneOn`, the owner extension theorem
  `Function.extensionFromIntrinsicInterior`, its owner-side derived theorems
  `Function.extensionFromIntrinsicInterior.convexOn`,
  `Function.extensionFromIntrinsicInterior.continuousOn`,
  `Function.extensionFromIntrinsicInterior.eqOn_intrinsicInterior`,
  `ConvexOn`, `Bornology.IsBounded`, `BddAbove`, `ContinuousOn`, `Set.EqOn`, and the canonical
  continuity-only uniqueness theorem `Function.extensionFromIntrinsicInterior.eqOn`.
- `bridge/view`: the source's coordinatewise monotonicity is expressed by the owner predicate
  `MonotoneOn f riC`; the textbook coordinatewise inequality formulation is already the
  ambient `Pi` order on `E`, so no parallel local wrapper is kept here.

Domain-style sampling used here:
- `interior (orthant[ℝ](E) : Set E)`;
- `orthant[ℝ](E)`;
- `MonotoneOn`;
- `Pi.le_def`;
- `intrinsicInterior_eq_interior_of_affineSpan_eq_top`;
- `IsOpen.affineSpan_eq_top`;
- `ConvexOn`;
- `Bornology.IsBounded`;
- `BddAbove`;
- `ContinuousOn`;
- `Set.EqOn`.

Primitive data vs derived API:
- primitive inputs: a codomain-preorder-valued function for part (1), and for part (2) the
  real-valued function `f : E → ℝ` with convexity and coordinatewise monotonicity on
  `riC`, kept canonically as `MonotoneOn f riC` for the ambient coordinatewise order on `E`;
- derived API: boundedness above on bounded subsets of `riC`, and the existence and uniqueness of
  the canonical continuous convex extension to `C`.

Layer target: `source-facing`, stated directly in terms of the chapter orthant sets and the
canonical setwise convexity, continuity, boundedness, orthant-order monotonicity predicates, and
the owner extension construction from Theorem 10.3.
-/

-- Proof sketch: if `B` is bounded in the positive orthant, each coordinate of points of `B` is
-- bounded above by some common real number `λ`. Coordinatewise monotonicity then gives
-- `f x ≤ f (fun _ ↦ λ)` for every `x ∈ B`, so `f '' B` has a common upper bound.
/-- Theorem 10.3.1 (1): a coordinatewise nondecreasing function on the positive orthant is bounded
above on every bounded subset of the positive orthant. -/
theorem bddAbove_image_on_bounded_subsets_of_positiveOrthant_of_coordinatewiseMonotone
    {β : Type*} [Preorder β] (f : E → β)
    (hf_monotone : MonotoneOn f riC)
    (s : Set E) (hs : s ⊆ riC) (hs_bounded : Bornology.IsBounded s) :
    BddAbove (f '' s) := sorry

/-- The nonnegative orthant `(ConvexCone.positive ℝ E : Set E)` is full-dimensional in `ℝ^ι`. -/
theorem affineSpan_nonnegativeOrthant_eq_top :
    affineSpan ℝ C = ⊤ := by
  sorry

/-- The intrinsic interior of the nonnegative orthant is the positive orthant. -/
@[simp] theorem intrinsicInterior_nonnegativeOrthant_eq_positiveOrthant :
    riC = interior C := by
  have hri : riC = interior C := by
    change ri[ℝ](C) = interior C
    simpa using
      (intrinsicInterior_eq_interior_of_affineSpan_eq_top (𝕜 := ℝ)
        affineSpan_nonnegativeOrthant_eq_top)
  exact hri

/-- The nonnegative orthant is locally simplicial. -/
theorem isLocallySimplicial_nonnegativeOrthant :
    Set.IsLocallySimplicial ℝ C := by
  sorry

variable (f : E → ℝ)

-- Proof sketch: apply part (1) to obtain the bounded-above-on-bounded-subsets hypothesis needed by
-- Theorem 10.3 for `C = (ConvexCone.positive ℝ E : Set E)`.
-- The positive orthant is the intrinsic interior of
-- the nonnegative orthant, and the nonnegative orthant is locally simplicial, so Theorem 10.3
-- yields the canonical continuous convex extension to `(ConvexCone.positive ℝ E : Set E)`;
-- uniqueness is recorded at the primitive continuity layer (hence also among continuous convex
-- extensions) via the owner-side continuity uniqueness theorem from Theorem 10.3.
/-- Theorem 10.3.1 (2): the canonical Chapter 10 extension from the positive orthant to the
nonnegative orthant is convex, continuous, agrees with `f` on the positive orthant, and is the
unique continuous extension there (hence, in particular, the unique continuous convex extension). -/
theorem continuousOnConvexOnExtensionFromPositiveOrthant_of_coordinatewiseMonotone
    (hf_monotone : MonotoneOn f riC) (hf_convex : ConvexOn ℝ riC f) :
    ConvexOn ℝ C (f.extensionFromIntrinsicInterior C) ∧
      ContinuousOn (f.extensionFromIntrinsicInterior C) C ∧
        EqOn (f.extensionFromIntrinsicInterior C) f riC ∧
      ∀ g : E → ℝ,
        ContinuousOn g C →
          EqOn g f riC →
            EqOn g (f.extensionFromIntrinsicInterior C) C :=
  sorry

-- Proof sketch: specialize the owner-side continuity uniqueness theorem from Theorem 10.3 to the
-- nonnegative orthant, using the orthant relative-interior identity and part (1) to supply the
-- bounded-above-on-bounded-subsets hypothesis.
/-- Companion to Theorem 10.3.1 (2): any continuous extension to the nonnegative orthant that
agrees with `f` on the positive orthant coincides there with the canonical Chapter 10 extension. -/
theorem eqOn_continuousOnExtensionFromPositiveOrthant_of_coordinatewiseMonotone
    (hf_monotone : MonotoneOn f riC) (hf_convex : ConvexOn ℝ riC f) {g : E → ℝ}
    (hg_cont : ContinuousOn g C) (hg_eq : EqOn g f riC) :
    EqOn g (f.extensionFromIntrinsicInterior C) C := sorry

end
