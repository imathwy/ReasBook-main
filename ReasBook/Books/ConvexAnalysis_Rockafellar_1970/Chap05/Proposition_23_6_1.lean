import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 23.6.1 translates the `ε`-subdifferential at a finite base point
  `x` into a Fenchel-conjugate sublevel condition for the translated defect function
  `h(y) = f (x + y) - f x`, and then reads off the closedness, convexity, monotonicity, and
  zero-tolerance intersection properties of `∂_ε f(x)`.
- `core/canonical`: the owner declarations already present in the project are
  `_root_.subdifferentialAt` and Fenchel conjugation `f⋆`; the approximate subdifferential of
  Definition 23.6 is kept here directly through its canonical supporting-affine inequality.
- `bridge/view`: there is no extra Euclidean bridge here; the source's `x*` naturally belongs to
  the canonical dual `StrongDual ℝ E`.

Domain-style sampling used here:
- `convexConjugate` / `f⋆` from `Chap03/Defn_12_2`;
- `_root_.subdifferentialAt` from `Chap05/Definition_23_0_6`;
- the supporting-affine inequality surface introduced by Definition 23.6;
- the set-theoretic intersection surface `⋂ (ε : ℝ) (_ : 0 < ε), ...`, already used elsewhere in
  the project for exact positive-radius limit statements.

Primitive data vs derived API:
- primitive source data: the base point `x`, the function `f`, and the translated defect
  function `h(y) = f (x + y) - f x`;
- derived API: the conjugate formula for `h⋆`, the `ε`-subdifferential membership criterion, and
  the closed/convex/monotone/intersection properties of the approximate-support set from
  Definition 23.6.

Layer target: `source-facing`, but stated directly on the canonical project owners
`_root_.subdifferentialAt` and `convexConjugate`, with the approximate-subdifferential side kept
in its direct source-facing set form.
-/

/-- The translated defect function at `x` is `y ↦ f (x + y) - f x`. -/
def translatedDefectFunction (f : E → EReal) (x : E) : E → EReal :=
  fun y ↦ f (x + y) - f x

/-- Evaluating the translated defect function at `y` subtracts the base value `f x` from the
translated value `f (x + y)`. -/
-- Proof sketch: unfold `translatedDefectFunction`; the statement is the defining formula.
@[simp] theorem translatedDefectFunction_apply (f : E → EReal) (x y : E) :
    translatedDefectFunction f x y = f (x + y) - f x := sorry

/-- The Fenchel conjugate of the translated defect function is obtained from `f⋆` by adding the
base value `f x` and subtracting the pairing with `x`. -/
-- Proof sketch: unfold `translatedDefectFunction` and `convexConjugate`; change variables
-- `z = x + y` in the defining supremum and pull the constant term `f x - ⟪x, xStar⟫ₚ` outside
-- the supremum. The finiteness hypotheses on `f x` ensure the translation defect is the intended
-- real-valued affine shift rather than a degenerate `⊥`/`⊤` arithmetic branch.
theorem convexConjugate_translatedDefectFunction_eq
    (f : E → EReal) (x : E) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (xStar : StrongDual ℝ E) :
    (translatedDefectFunction f x)⋆ xStar = f⋆ xStar + f x - ⟪x, xStar⟫ₚ := sorry

/-- Proposition 23.6.1: for the translated defect function `h(y) = f (x + y) - f x` at a finite
base point `x`, a dual vector `xStar` belongs to the `ε`-subdifferential of `f` at `x` exactly
when the Fenchel conjugate `h⋆ xStar` is at most `ε`. -/
-- Proof sketch: rewrite membership in `epsSubdifferentialAt f x ε` by
-- `mem_epsSubdifferentialAt`, then compare the resulting family of affine upper bounds with the
-- supremum formula defining `(translatedDefectFunction f x)⋆ xStar`. This is exactly the same
-- supremum/inequality conversion as Fenchel-Young, specialized to the translated defect function.
theorem mem_epsSubdifferentialAt_iff_convexConjugate_translatedDefectFunction_le
    (f : E → EReal) (x : E) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (ε : ℝ) (xStar : StrongDual ℝ E) :
    xStar ∈ {yStar : StrongDual ℝ E |
      ∀ z, f z ≥ f x + (((yStar (z - x) - ε : ℝ) : EReal))} ↔
      (translatedDefectFunction f x)⋆ xStar ≤ ε := sorry

/-- Under the finite-base hypotheses of Proposition 23.6.1, each `ε`-subdifferential is closed in
the strong dual. -/
-- Proof sketch: by Proposition 23.6.1, `epsSubdifferentialAt f x ε` is the sublevel set
-- `{xStar | (translatedDefectFunction f x)⋆ xStar ≤ ε}`. Theorem 12.2 gives lower semicontinuity
-- of Fenchel conjugates, and closed sublevel sets of lower-semicontinuous functions are closed.
theorem isClosed_epsSubdifferentialAt
    (f : E → EReal) (x : E) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥) (ε : ℝ) :
    IsClosed {xStar : StrongDual ℝ E |
      ∀ z, f z ≥ f x + (((xStar (z - x) - ε : ℝ) : EReal))} := sorry

/-- Under the finite-base hypotheses of Proposition 23.6.1, each `ε`-subdifferential is convex in
the strong dual. -/
-- Proof sketch: rewrite `epsSubdifferentialAt f x ε` as the same conjugate sublevel set from
-- Proposition 23.6.1. Fenchel conjugates are convex by Theorem 12.2, and sublevel sets of convex
-- functions are convex.
theorem convex_epsSubdifferentialAt
    (f : E → EReal) (x : E) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥) (ε : ℝ) :
    Convex ℝ {xStar : StrongDual ℝ E |
      ∀ z, f z ≥ f x + (((xStar (z - x) - ε : ℝ) : EReal))} := sorry

/-- The `ε`-subdifferential grows with the tolerance parameter: smaller tolerances give smaller
sets. -/
-- Proof sketch: compare the defining inequalities
-- `f z ≥ f x + (xStar (z - x) - εᵢ)` for `ε₁ ≤ ε₂`; any witness for the smaller tolerance is
-- automatically a witness for the larger one.
theorem epsSubdifferentialAt_mono
    (f : E → EReal) (x : E) {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    {xStar : StrongDual ℝ E |
        ∀ z, f z ≥ f x + (((xStar (z - x) - ε₁ : ℝ) : EReal))} ⊆
      {xStar : StrongDual ℝ E |
        ∀ z, f z ≥ f x + (((xStar (z - x) - ε₂ : ℝ) : EReal))} := sorry

/-- Under the finite-base hypotheses of Proposition 23.6.1, intersecting all positive-tolerance
`ε`-subdifferentials recovers the exact subdifferential. -/
-- Proof sketch: by Proposition 23.6.1, the positive-tolerance sets are the positive sublevel sets
-- of `(translatedDefectFunction f x)⋆`. Intersecting over all `ε > 0` therefore gives the zero
-- sublevel set, which is exactly the exact subdifferential at `x`.
theorem iInter_pos_epsSubdifferentialAt_eq_subdifferentialAt
    (f : E → EReal) (x : E) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥) :
    (⋂ (ε : ℝ) (_ : 0 < ε), {xStar : StrongDual ℝ E |
      ∀ z, f z ≥ f x + (((xStar (z - x) - ε : ℝ) : EReal))}) = subdifferentialAt f x := sorry

end
