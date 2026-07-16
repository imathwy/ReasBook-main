import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_3
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_12_2_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_29

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConvexFunctionPolar Rockafellar

universe u

section

variable {E : Type u} [SMul ℝ E]

/-- The obverse of `f` sends `x` to the infimum of the positive scalars `λ` for which the scaled
perspective `f_λ x`, rendered by the positive right scalar multiple of `f`, is at most `1`.
The positive parameter is packaged canonically as `a : NNRealˣ`, so the construction lives on an
arbitrary real `ℝ`-scaled space. -/
def obverse (f : E → WithBotTop ℝ) : E → WithBotTop ℝ :=
  fun x ↦
    sInf
      (((↑) : NNRealˣ → WithBotTop ℝ) ''
        {a : NNRealˣ | ((a : NNReal) •ʳ f) x ≤ (1 : WithBotTop ℝ)})

end

section

variable {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

namespace Function

/-- The standing Chapter 15 hypothesis package keeps the primitive source data:
closedness, convexity, nonnegativity, and the normalization `f 0 = 0`.
The Chapter 12 properness clause is derived from nonnegativity together with the finite value at
the origin, so it is not stored as primitive public data. This owner already lives on the
intrinsic real topological-module layer with codomain `WithBotTop ℝ`; later source bridges may
specialize the ambient further, but this owner keeps only the primitive data. -/
class IsNonnegativeClosedConvexZero (f : E → WithBotTop ℝ) : Prop where
  convex : f.IsConvex ℝ
  closed : LowerSemicontinuous f
  nonneg : ∀ x : E, (0 : WithBotTop ℝ) ≤ f x
  map_zero : f 0 = 0

namespace IsNonnegativeClosedConvexZero

/-- Properness is derived from pointwise nonnegativity and the finite value `f 0 = 0`. -/
theorem proper {f : E → WithBotTop ℝ} (hf : f.IsNonnegativeClosedConvexZero) :
    f.IsProper := by
  rw [Function.isProper_iff_nonempty_dom_and_bot_lt]
  refine ⟨⟨0, ?_⟩, ?_⟩
  · rw [mem_effectiveDomain, hf.map_zero]
    exact show (0 : WithBotTop ℝ) < ⊤ from WithBotTop.coe_lt_top (0 : ℝ)
  · intro x
    exact
      lt_of_lt_of_le
        (show (⊥ : WithBotTop ℝ) < (0 : WithBotTop ℝ) by simp)
        (hf.nonneg x)

/-- The standing Chapter 15 owner canonically upgrades to the Chapter 12 owner
`f.IsClosedProperConvex`. -/
theorem isClosedProperConvex {f : E → WithBotTop ℝ} (hf : f.IsNonnegativeClosedConvexZero) :
    f.IsClosedProperConvex (𝕜 := ℝ) :=
  { convex := hf.convex, proper := hf.proper, closed := hf.closed }

instance instIsClosedProperConvex (f : E → WithBotTop ℝ) [hf : f.IsNonnegativeClosedConvexZero] :
    f.IsClosedProperConvex (𝕜 := ℝ) :=
  hf.isClosedProperConvex

end IsNonnegativeClosedConvexZero

end Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.31 states that for a nonnegative closed convex function `f` with
  `f 0 = 0`, the extended polar of its Fenchel conjugate `f⋆` is given pointwise by the infimum
  over the positive dilations `f_λ`.
- `core/canonical`: the existing owner constructions are `f⋆`,
  `convex_function_polar`, the earlier scaled-epigraph owner `rightScalarMul`, the
  source-facing infimum owner `obverse`, the Chapter 12 owner `Function.IsClosedProperConvex`,
  the closed-proper-convex biconjugacy theorem `Function.IsClosedProperConvex.biconjugate_eq`,
  and the standing Chapter 15 refinement `Function.IsNonnegativeClosedConvexZero`.
- `bridge/view`: the source's positive-dilation notation `f_λ` is rendered directly by the
  existing owner `rightScalarMul` with the canonical positive parameter `a : NNRealˣ`, so no
  parallel local wrapper is kept. The Chapter 12 properness owner is derived from the source data
  rather than stored primitively. The main theorem keeps the textbook's explicit infimum formula,
  and the companion theorem below identifies that formula with the existing source-facing owner
  `obverse`.

Domain-style sampling used here:
- `convex_function_polar`;
- `rightScalarMul`;
- `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos`;
- `Function.IsClosedProperConvex.biconjugate_eq`;
- `obverse`;
- `f⋆`.

Primitive data vs derived API:
- primitive inputs: a function `f : E → WithBotTop ℝ`, the source-specific fields `f.IsConvex ℝ`,
  `LowerSemicontinuous f`, `∀ x, 0 ≤ f x`, `f 0 = 0`, and a point `x : E`;
- primitive source formula: the infimum over the positive parameters `a : NNRealˣ` with
  `((a : NNReal) •ʳ f) x ≤ 1`;
- derived owner bridge: `hf.proper` and `hf.isClosedProperConvex` from the standing Chapter 15
  owner `hf : f.IsNonnegativeClosedConvexZero`;
- derived API: the bridge identifying that formula with `obverse f`.

Layer target: `source-facing` for the main labeled theorem, with a `bridge/view` companion to the
existing `obverse` abstraction. The owner `obverse` itself lives on the weaker real-scaling
layer above; the conjugate/polar comparison theorem below is stated at the finite-dimensional
real pairing layer.
-/

end

section

variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable [FiniteDimensional ℝ E]
variable [HasLinearPairing E E ℝ] [HasContinuousPairing E E ℝ]

-- Proof sketch: start from the defining infimum formula for `convex_function_polar
-- (convexConjugate f) x`. For `λ > 0`, rewrite the admissibility condition
-- `∀ y, ⟪y, x⟫ ≤ 1 + λ (convexConjugate f) y` as
-- `sup_y (⟪y, x⟫ - λ (convexConjugate f) y) ≤ 1`, identify that supremum with
-- `λ * convexConjugate (convexConjugate f) (λ⁻¹ • x)`, and then use closed-convex biconjugacy
-- through the canonical Chapter 12 owner theorem `hf.isClosedProperConvex.biconjugate_eq`,
-- together with the standing normalization hypotheses, to replace `f**` by `f`.
/-- Text 15.0.31: if `f : E → [0, +∞]` is convex, lower semicontinuous, and satisfies `f 0 = 0`
on a finite-dimensional real vector space with continuous linear self-pairing, then the polar of
its Fenchel conjugate `f*`,
rendered as `(f⋆)ᵒ`, is given at
each `x` by the infimum of the positive scalars `λ` for which the dilated perspective
`f_λ x = λ f (λ⁻¹ x)` is at most `1`. Specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers
the source statement on `R^n`. -/
theorem
    convex_function_polar_convexConjugate_eq_sInf_rightScalarMul_of_nonnegative_closed_convex_zero
    (f : E → WithBotTop ℝ) (hf : f.IsNonnegativeClosedConvexZero) (x : E) :
    ((f⋆ : E → WithBotTop ℝ)ᵒ) x =
      sInf
        (((↑) : NNRealˣ → WithBotTop ℝ) ''
          {a : NNRealˣ | ((a : NNReal) •ʳ f) x ≤ (1 : WithBotTop ℝ)}) := sorry

-- Proof sketch: unfold `obverse f x` and compare the resulting right-hand side with the main
-- theorem's infimum formula.
/-- The perspective-infimum formula from the main theorem is exactly the obverse construction
`obverse f`, under the same finite-dimensional real pairing hypotheses. -/
theorem
    convex_function_polar_convexConjugate_eq_obverse_of_nonnegative_closed_convex_zero
    (f : E → WithBotTop ℝ) (hf : f.IsNonnegativeClosedConvexZero) (x : E) :
    ((f⋆ : E → WithBotTop ℝ)ᵒ) x = obverse f x := by
  simpa [obverse] using
    convex_function_polar_convexConjugate_eq_sInf_rightScalarMul_of_nonnegative_closed_convex_zero
      f hf x

end
