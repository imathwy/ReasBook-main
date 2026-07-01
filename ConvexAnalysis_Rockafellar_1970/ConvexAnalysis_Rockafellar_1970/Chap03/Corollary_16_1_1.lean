import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

/-
Source/core/bridge triage:
- `source-facing`: Corollary 16.1.1 states that dilating a nonempty set by a nonnegative scalar
  scales its support function by the same scalar.
- `core/canonical`: the owner abstraction is the project support function `supportFunction`,
  together with pointwise set scaling. The generic owner theorem belongs with the existing
  support-function scaling API in `Text_13_1_3`.
- `bridge/view`: the textbook notation `δ*(x* | C)` is the chapter notation `δᵛ(xStar | C)`, and
  the pointwise textbook evaluation formula is the companion theorem
  `supportFunction_smul_set_of_nonempty_apply`.
- Primitive data vs derived API: primitive inputs are only `C`, its nonemptiness witness, and a
  scalar `c` with nonnegativity witness `0 ≤ c`; the owner equality and its pointwise
  specialization are
  derived API.

Domain-style sampling used here:
- `supportFunction` and `supportFunction_def`;
- the owner theorem `supportFunction_smul_set_of_pos`;
- the upstream owner extension `supportFunction_smul_set_of_nonempty`.

Layer target: `bridge/view`. This numbered file should be a direct recall layer, not a second
owner location for the same support-function scaling API.
-/

/- Corollary 16.1.1: for a nonempty set `C` and a nonnegative scalar `λ`, the support function of
the dilate `λ C` is `λ` times the support function of `C`. This is the canonical owner theorem
`supportFunction_smul_set_of_nonempty`, restated on the owner surface `supportFunction`. -/
recall supportFunction_smul_set_of_nonempty
  {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {X Y : Type*}
  [AddCommMonoid Y] [Module 𝕜 Y]
  [HasPairing X Y 𝕜] [HasPairingSMulRight X Y 𝕜] [HasPairingZeroRight X Y 𝕜]
  (C : Set Y) (hC : C.Nonempty) {c : 𝕜} (hc : 0 ≤ c) :
  (supportFunction (c • C) : X → WithTopBot 𝕜) =
    (c : WithTopBot 𝕜) • (supportFunction C : X → WithTopBot 𝕜)

/- Corollary 16.1.1 in pointwise form is the existing companion theorem
`supportFunction_smul_set_of_nonempty_apply`. -/
recall supportFunction_smul_set_of_nonempty_apply
  {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {X Y : Type*}
  [AddCommMonoid Y] [Module 𝕜 Y]
  [HasPairing X Y 𝕜] [HasPairingSMulRight X Y 𝕜] [HasPairingZeroRight X Y 𝕜]
  (C : Set Y) (hC : C.Nonempty) {c : 𝕜} (hc : 0 ≤ c) (xStar : X) :
  supportFunction (c • C) xStar = (c : WithTopBot 𝕜) * supportFunction C xStar
