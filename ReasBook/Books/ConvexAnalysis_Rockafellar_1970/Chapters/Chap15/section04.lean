import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_15_4_1 (from Chap03) -/
noncomputable section

open scoped ConvexFunctionPolar

universe u

section

variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable [HasLinearPairing E E ℝ] [HasContinuousPairing E E ℝ] [HasPairingSwap E E ℝ]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 15.4.1 says that the polarity mapping `f ↦ fᵒ` is a symmetric
  one-to-one correspondence on the class of nonnegative closed convex functions on a
  finite-dimensional real vector space with continuous linear self-pairing vanishing at the
  origin.
- `core/canonical`: the owner constructions already present in the project are
  `convex_function_polar`, `lowerSemicontinuousHull`, the standing Chapter 15 hypothesis class
  `Function.IsNonnegativeClosedConvexZero`, and mathlib's canonical set-function relation `Set.BijOn`.
- `bridge/view`: the textbook phrase "symmetric one-to-one correspondence" is rendered by the
  owner-side involution equation `fᵒᵒ = f` on the standing class, together with the induced
  bijection of that class with itself.

Domain-style sampling used here:
- `convex_function_polar`;
- the owner instance
  `instIsNonnegativeClosedConvexZeroConvexFunctionPolar`;
- `convex_function_polar_involutive`;
- the chapter-level correspondence pattern
  `convexConjugate_bijOn_closedProperConvexFunctions`.

Primitive data vs derived API:
- primitive input: a function `f : E → WithBotTop ℝ`;
- source hypotheses: nonnegativity, lower semicontinuity, convexity, and `f 0 = 0`;
- derived output: the bipolar identity `fᵒᵒ = f` on the standing class and the resulting
  bijection of `{f | f.IsNonnegativeClosedConvexZero}` with itself.

Layer target: `source-facing`; the corollary is stated directly for the canonical function polar on
the canonical class of admissible functions, with no surrogate restricted-map wrapper.
-/

-- Proof sketch: Theorem 15.4 packages closure of the class under polarity. The companion
-- bipolar identity `fᵒᵒ = f` is the owner theorem `convex_function_polar_involutive`, so polarity
-- is its own inverse on the standing class and hence defines a bijection of that class with
-- itself.
/-- Corollary 15.4.1: the polarity mapping `f ↦ fᵒ` induces a symmetric one-to-one
correspondence on the class of all nonnegative closed convex functions on a finite-dimensional
real vector space with continuous linear self-pairing that vanish at the origin, expressed here
as a bijection of that class with itself. -/
theorem convex_function_polar_bijOn_nonnegativeClosedConvexZeroFunctions :
    Set.BijOn
      (fun f : E → WithBotTop ℝ ↦ (fᵒ : E → WithBotTop ℝ))
      {f : E → WithBotTop ℝ | f.IsNonnegativeClosedConvexZero}
      {f : E → WithBotTop ℝ | f.IsNonnegativeClosedConvexZero} := by
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    exact
      isNonnegativeClosedConvexZero_convex_function_polar_of_nonnegative_convex_zero
        f hf.nonneg hf.convex hf.map_zero
  · intro f hf g hg hfg
    have hff : (((fᵒ : E → WithBotTop ℝ)ᵒ : E → WithBotTop ℝ)) = f := by
      calc
        (((fᵒ : E → WithBotTop ℝ)ᵒ : E → WithBotTop ℝ)) = lowerSemicontinuousHull f :=
          convex_function_polar_convex_function_polar_eq_lowerSemicontinuousHull_of_nonnegative_convex_zero
            f hf.nonneg hf.convex hf.map_zero
        _ = f := lowerSemicontinuousHull_eq_self hf.closed
    have hgg : (((gᵒ : E → WithBotTop ℝ)ᵒ : E → WithBotTop ℝ)) = g := by
      calc
        (((gᵒ : E → WithBotTop ℝ)ᵒ : E → WithBotTop ℝ)) = lowerSemicontinuousHull g :=
          convex_function_polar_convex_function_polar_eq_lowerSemicontinuousHull_of_nonnegative_convex_zero
            g hg.nonneg hg.convex hg.map_zero
        _ = g := lowerSemicontinuousHull_eq_self hg.closed
    have hfg' : (fᵒ : E → WithBotTop ℝ) = (gᵒ : E → WithBotTop ℝ) := by simpa using hfg
    have hbipolar_eq :
        (((fᵒ : E → WithBotTop ℝ)ᵒ : E → WithBotTop ℝ)) =
          (((gᵒ : E → WithBotTop ℝ)ᵒ : E → WithBotTop ℝ)) := by
      rw [hfg']
    exact hff.symm.trans (hbipolar_eq.trans hgg)
  · intro f hf
    have hfpolar : (fᵒ : E → WithBotTop ℝ).IsNonnegativeClosedConvexZero :=
      isNonnegativeClosedConvexZero_convex_function_polar_of_nonnegative_convex_zero
        f hf.nonneg hf.convex hf.map_zero
    have hbipolar : (((fᵒ : E → WithBotTop ℝ)ᵒ : E → WithBotTop ℝ)) = f := by
      calc
        (((fᵒ : E → WithBotTop ℝ)ᵒ : E → WithBotTop ℝ)) = lowerSemicontinuousHull f :=
          convex_function_polar_convex_function_polar_eq_lowerSemicontinuousHull_of_nonnegative_convex_zero
            f hf.nonneg hf.convex hf.map_zero
        _ = f := lowerSemicontinuousHull_eq_self hf.closed
    exact ⟨(fᵒ : E → WithBotTop ℝ), hfpolar, hbipolar⟩

end

/-! ### Theorem_15_4 (from Chap03) -/
noncomputable section

open scoped ConvexFunctionPolar Rockafellar

universe u

section

variable {E : Type u}
variable [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
variable [HasLinearPairing E E ℝ] [HasContinuousPairing E E ℝ]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 15.4 states that the polar `fᵒ` of a nonnegative convex function with
  `f 0 = 0` is again nonnegative, closed, convex, and normalized at the origin, and that the
  bipolar `fᵒᵒ` is the closure `cl f`.
- `core/canonical`: the owner constructions already present in the project are
  `convex_function_polar`, the owner fact `convex_function_polar_nonneg`, the convexity predicate
  `Function.IsConvex`, the closedness predicate `LowerSemicontinuous`, the closure operator
  `lowerSemicontinuousHull`, and the standing Chapter 15 hypothesis class
  `Function.IsNonnegativeClosedConvexZero`.
- `bridge/view`: Rockafellar's closure notation `cl f` is rendered by
  `lowerSemicontinuousHull f`, so the bipolar clause is stated directly as a function equality.

Domain-style sampling used here:
- `convex_function_polar` and `convex_function_polar_nonneg` from `Text_15_0_29`;
- `Function.IsNonnegativeClosedConvexZero` from `Text_15_0_31`;
- `lowerSemicontinuousHull` from `Text_7_0_4`;
- `LowerSemicontinuous` and `Function.IsConvex` as the canonical owner predicates for closedness
  and convexity of extended-codomain-valued functions on a real linear pairing space.

Primitive data vs derived API:
- primitive input: a function `f : E → WithBotTop ℝ`;
- source hypotheses: nonnegativity, convexity, and the normalization `f 0 = 0`;
- derived outputs: the owner-layer package `fᵒ.IsNonnegativeClosedConvexZero`, the
  source-facing bipolar identity `fᵒᵒ = cl(f)`, and the owner-facing involution theorem `fᵒᵒ = f`
  on the standing Chapter 15 class.

The source sentence is split into atomic declarations to avoid a large conjunction: clause (1) is
recalled directly, clauses (2) through (4) are packaged by the Chapter 15 owner class, clause (5)
is kept as a separate source-facing equality, and the class-level closedness hypothesis is used
only for the derived involution theorem.
-/

/- Theorem 15.4 (1): the polar `fᵒ = convex_function_polar f` is nonnegative at every dual point.
This is exactly `convex_function_polar_nonneg` from `Text_15_0_29`. -/
recall convex_function_polar_nonneg

section

variable (f : E → WithBotTop ℝ)

-- Proof sketch: clause (1) is the recalled theorem `convex_function_polar_nonneg`. For the
-- remaining clauses, identify the epigraph of `convex_function_polar f` with the image of the
-- polar of the epigraph of `f` under the vertical reflection `(xStar, μStar) ↦ (xStar, -μStar)`.
-- Since `epi f` is convex and contains `(0, 0)` under the standing hypotheses, its polar is
-- closed and convex, and the reflected epigraph inherits those properties; the value at the
-- origin is `0` because `μStar = 0` is admissible when `f` is nonnegative and the recalled
-- nonnegativity theorem supplies the reverse inequality.
/-- Theorem 15.4 clauses (1) through (4), packaged at the Chapter 15 owner layer: if `f` is a
nonnegative convex function with `f 0 = 0`, then its polar `fᵒ = convex_function_polar f` is
again nonnegative, closed, convex, and normalized at the origin. -/
theorem isNonnegativeClosedConvexZero_convex_function_polar_of_nonnegative_convex_zero
    (hf_nonneg : ∀ x : E, (0 : WithBotTop ℝ) ≤ f x) (hf_convex : f.IsConvex ℝ)
    (hf_zero : f 0 = 0) :
    (fᵒ : E → WithBotTop ℝ).IsNonnegativeClosedConvexZero := by
  have hclosed : LowerSemicontinuous (fᵒ : E → WithBotTop ℝ) := by
    sorry
  have hconvex : (fᵒ : E → WithBotTop ℝ).IsConvex ℝ := by
    sorry
  have hmap_zero : (fᵒ : E → WithBotTop ℝ) 0 = 0 := by
    sorry
  exact
    { convex := hconvex
      closed := hclosed
      nonneg := convex_function_polar_nonneg f
      map_zero := hmap_zero }

/-- Theorem 15.4 packages clauses (1) through (4) at the Chapter 15 owner layer: the polar of a
nonnegative closed convex function vanishing at the origin again belongs to the standing class. -/
instance instIsNonnegativeClosedConvexZeroConvexFunctionPolar
    (f : E → WithBotTop ℝ) [hf : f.IsNonnegativeClosedConvexZero] :
    (fᵒ : E → WithBotTop ℝ).IsNonnegativeClosedConvexZero :=
  isNonnegativeClosedConvexZero_convex_function_polar_of_nonnegative_convex_zero
    f hf.nonneg hf.convex hf.map_zero

end

section

variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable [HasLinearPairing E E ℝ] [HasContinuousPairing E E ℝ] [HasPairingSwap E E ℝ]
variable (f : E → WithBotTop ℝ)

-- Proof sketch: the previous clauses show that `convex_function_polar f` is a nonnegative closed
-- convex function with value `0` at the origin, so the same theorem applies to `convex_function_polar f`.
-- Comparing the epigraph description of the bipolar with the set bipolar theorem yields
-- `convex_function_polar (convex_function_polar f) = lowerSemicontinuousHull f`.
/-- Theorem 15.4 (5): if `f` is a nonnegative convex function with `f 0 = 0`, then the bipolar
`fᵒᵒ` equals the closure `cl f`, represented in this project by `lowerSemicontinuousHull f`.
The finite-dimensional source statement is kept at the intrinsic continuous linear self-pairing
layer rather than an inner-product specialization. -/
theorem convex_function_polar_convex_function_polar_eq_lowerSemicontinuousHull_of_nonnegative_convex_zero
    (hf_nonneg : ∀ x : E, (0 : WithBotTop ℝ) ≤ f x)
    (hf_convex : f.IsConvex ℝ) (hf_zero : f 0 = 0) :
    ((fᵒ : E → WithBotTop ℝ)ᵒ : E → WithBotTop ℝ) = cl(f) := by
  let hfpolar : (fᵒ : E → WithBotTop ℝ).IsNonnegativeClosedConvexZero :=
    isNonnegativeClosedConvexZero_convex_function_polar_of_nonnegative_convex_zero
      f hf_nonneg hf_convex hf_zero
  sorry

/-- The owner-layer involution form of Theorem 15.4 on the Chapter 15 class. -/
theorem convex_function_polar_involutive
    (hf : f.IsNonnegativeClosedConvexZero) :
    ((fᵒ : E → WithBotTop ℝ)ᵒ : E → WithBotTop ℝ) = f := by
  calc
    ((fᵒ : E → WithBotTop ℝ)ᵒ : E → WithBotTop ℝ) = cl(f) :=
      convex_function_polar_convex_function_polar_eq_lowerSemicontinuousHull_of_nonnegative_convex_zero
        f hf.nonneg hf.convex hf.map_zero
    _ = f := lowerSemicontinuousHull_eq_self hf.closed

end

end
