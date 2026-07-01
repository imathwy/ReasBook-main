import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_11
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_0_3
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_0_5
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_1_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Rockafellar

attribute [local instance] Classical.propDecidable

section

/-!
Source/core/bridge triage for this item.

- `source-facing`: the text lists four explicit sets `C₁`, `C₂`, `C₃`, `C₄` and records their
  support-function formulas.
- `core/canonical`: the owner abstraction is the chapter support function `supportFunction C x`
  attached directly to a subset of a paired ambient space; the set owner for `C₃` is stated on
  the intrinsic planar product owner `𝕜 × 𝕜` at the primitive order/inversion layer
  (`Preorder` + `Zero` + `Inv`), and the support-function API is split into a scalar-generic
  `⊤`/non-`⊤` criterion plus a real-specialized closed form where `Real.sqrt` is canonical.
- `bridge/view`: the already formalized simplex and `ℓ¹`-ball examples are reused directly,
  `C₃` remains new in this file, and `C₄` is reused from the earlier source-facing
  formalization `quadraticOverLinearSupportSet` together with its support-function owner theorem
  `quadraticOverLinearFunction_eq_supportFunction`.

Domain-style sampling used here:
- the owner declaration `supportFunction` and its specification theorem `supportFunction_def`;
- the canonical product pairing owner on `𝕜 × 𝕜` from `instHasPairingProd` / `pairing_prod`,
  built from the scalar multiplication pairing on `𝕜`;
- the existing project source-facing examples
  `supportFunction_coordinateSimplex_eq_greatestCoordinate` and
  `supportFunction_coordinateL1Ball_eq_sup'_univ_abs`;
- the earlier Chapter 2 declarations `quadraticOverLinearSupportSet`,
  `quadraticOverLinearFunction`, and `quadraticOverLinearFunction_eq_supportFunction`;
- the standard extended-real conventions using `⊤` for `+∞` and coercions
  `𝕜 → WithTopBot 𝕜`.

Primitive data vs derived API:
- primitive data: the explicit planar set `C₃`;
- derived API: a scalar-generic support-function criterion for `C₃`, its real closed-form
  specialization, and the direct Chapter 2 owner reuse for `C₄`, together with direct recall of
  the earlier `C₁` and `C₂` computations.

Layer target: `source-facing`; the new declarations keep the textbook sets themselves explicit and
  state their support-function values directly, while the repeated `C₄` example is reused
  directly from the earlier Chapter 2 owner instead of being redefined.
-/

/- The `C₁` example in Text 13.2.6 is already the previously formalized coordinate-simplex
support-function formula. -/
recall supportFunction_coordinateSimplex_eq_greatestCoordinate

/- The `C₂` example in Text 13.2.6 is already the previously formalized `ℓ¹`-unit-ball
support-function formula. -/
recall supportFunction_coordinateL1Ball_eq_sup'_univ_abs

section

local notation "R2[" 𝕜 "]" => (𝕜 × 𝕜)

/-- The planar set `C₃ = {(ξ₁, ξ₂) | ξ₁ < 0, ξ₂ ≤ ξ₁⁻¹}` on the intrinsic product owner
`𝕜 × 𝕜`. -/
def negativeReciprocalHypograph (𝕜 : Type*) [Preorder 𝕜] [Zero 𝕜] [Inv 𝕜] :
    Set (R2[𝕜]) :=
  {x | x.1 < 0 ∧ x.2 ≤ (x.1)⁻¹}

end

scoped[Rockafellar] notation "C₃" => negativeReciprocalHypograph _
scoped[Rockafellar] notation "C₃[" 𝕜 "]" => negativeReciprocalHypograph 𝕜

section

local instance instHasPairingScalarSelf (𝕜 : Type*) [Mul 𝕜] : HasPairing 𝕜 𝕜 𝕜 where
  pairing x y := x * y

variable {𝕜 : Type*} [LinearOrderedField 𝕜]

/-- On the intrinsic product owner `𝕜 × 𝕜`, membership in the canonical nonnegative orthant is
coordinatewise nonnegativity. -/
theorem mem_orthant_prod_iff (x : R2[𝕜]) :
    x ∈ orthant[𝕜](R2[𝕜]) ↔ 0 ≤ x.1 ∧ 0 ≤ x.2 := by
  simpa using (mem_nonnegativeOrthant_iff (x := x))

theorem supportFunction_negativeReciprocalHypograph_eq
    (xStar : R2[𝕜]) :
    δᵛ(xStar | C₃[𝕜]) = (⊤ : WithTopBot 𝕜) ↔
      xStar ∉ orthant[𝕜](R2[𝕜]) := sorry

end

-- Proof sketch: maximize `ξ₁ ξ₁⋆ + ξ₂ ξ₂⋆` under the constraints `ξ₁ < 0` and `ξ₂ ≤ ξ₁⁻¹`.
-- For `xStar ∈ orthant[ℝ](ℝ × ℝ)` (equivalently coordinatewise nonnegative), the supremum occurs
-- on the boundary `ξ₂ = ξ₁⁻¹`,
-- reducing to a one-variable optimization with value `-2 * √(ξ₁⋆ ξ₂⋆)`. If one coordinate of
-- `xStar` is negative, the linear functional is unbounded above on the admissible region, so the
-- support function is `+∞`.
/-- Text 13.2.6, real closed-form specialization: for
`C₃ = {(ξ₁, ξ₂) | ξ₁ < 0, ξ₂ ≤ ξ₁⁻¹}`, the support function is
`-2 (ξ₁⋆ ξ₂⋆)^{1/2}` on `orthant[ℝ](ℝ × ℝ)` and `+∞` otherwise. -/
theorem supportFunction_negativeReciprocalHypograph_eq_real
    (xStar : R2[ℝ]) :
    δᵛ(xStar | C₃[ℝ]) =
      if xStar ∈ orthant[ℝ](R2[ℝ]) then
        (((-2 : ℝ) * Real.sqrt (xStar.1 * xStar.2)) : WithTopBot ℝ)
      else
        ⊤ := sorry

/- The `C₄` example in Text 13.2.6 is already the earlier Chapter 2 source-facing support-function
identity for `quadraticOverLinearSupportSet = {(ξ₁, ξ₂) | 2 ξ₁ + ξ₂² ≤ 0}`. -/
recall quadraticOverLinearFunction_eq_supportFunction

end
