import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_15_4

-- Declarations for this item will be appended below by the statement pipeline.

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
