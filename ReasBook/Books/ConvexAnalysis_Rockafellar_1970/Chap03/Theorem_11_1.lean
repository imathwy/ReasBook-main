import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Operations
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_11_0_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_11_0_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

section ProperSeparation

variable {𝕜 : Type*} [CommRing 𝕜] [ConditionallyCompletePartialOrder 𝕜]
variable {X : Type*} [AddCommGroup X] [Module 𝕜 X]
variable {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]
variable {C1 C2 : Set X}

-- The support-function side uses the same primal/dual pairing data as separation, viewed in the
-- opposite orientation and lifted to `WithTopBot`.
local instance instHasPairingDualPrimalWithTopBot : HasPairing Y X (WithTopBot 𝕜) :=
  HasPairing.swap (X := X) (Y := Y) (L := WithTopBot 𝕜)
local notation3:max "δᵛ(" x " | " C ")" => supportFunction (L := WithTopBot 𝕜) C x

/-
Source/core/bridge triage:
- `source-facing`: Theorem 11.1 gives infimum-supremum criteria for proper and strong hyperplane
  separation of two nonempty sets.
- `core/canonical`: the chapter owner abstractions are `AffineSubspace.SeparatesProperly` and
  `AffineSubspace.StronglySeparates`, together with the project owner `supportFunction`.
- `bridge/view`: the textbook projected supremum is the owner value `δᵛ(b | C)`, and
  the projected infimum is its canonical dual `-δᵛ(-b | C)`.
- Domain-style sampling used here: the project declarations `AffineSubspace.SeparatesProperly`,
  `AffineSubspace.StronglySeparates`, and `supportFunction`.
- Primitive data vs derived API: the primitive inputs are the two sets and their nonemptiness; the
  existence of a proper or strong separating hyperplane and the support-function gap conditions are
  theorem-level content.
- Layer target: `source-facing`, stated with the chapter's existing separation owners and a thin
  bridge to the textbook infimum/supremum formulas through the existing support-function owner.
  It is stated on arbitrary pairing spaces over a commutative ring. Since no inner-product-specific
  operation enters these owner statements, and the support-function side only needs the
  extended-order codomain `WithTopBot 𝕜`, the theorem is refined to that canonical pairing
  layer rather than a concrete coordinate model.
-/

/-- Theorem 11.1 (1), stated in the chapter's canonical ambient form: for nonempty sets `C1` and
`C2` in a primal/dual pairing over `𝕜`, a hyperplane separates `C1` and `C2` properly if and only
if there is a dual vector `b` such that the projected infimum on `C1` dominates the projected
supremum on `C2`, while the projected supremum on `C1` strictly exceeds the projected infimum on
`C2`.
Written through the owner notation `δᵛ(· | ·)` in codomain `WithTopBot 𝕜`, this is the source
support-function infimum/supremum criterion. -/
-- Proof sketch: if `H` separates properly, unpack `H.SeparatesProperly C1 C2` into one nonzero
-- equation `⟪x, b⟫ = β` and opposite closed-half-space containments. Those containments force the
-- support-function dual `-δᵛ(-b | C1)` to dominate `δᵛ(b | C2)`, and properness gives strict
-- inequality between `δᵛ(b | C1)` and the dual value `-δᵛ(-b | C2)`. Conversely, choose `β`
-- between these two projected ranges. Condition (b) ensures that not both sets lie in the
-- resulting hyperplane, so `affineHyperplane b β` separates properly.
theorem exists_hyperplane_separating_properly_iff_supportFunction_conditions
    (hC1_nonempty : C1.Nonempty) (hC2_nonempty : C2.Nonempty) :
    (∃ H : AffineSubspace 𝕜 X, H.SeparatesProperly Y C1 C2) ↔
      ∃ b : Y,
        (-δᵛ(-b | C1) ≥ δᵛ(b | C2)) ∧
          (δᵛ(b | C1) > -δᵛ(-b | C2)) := sorry

end ProperSeparation

section StrongSeparation

variable {𝕜 : Type*} [CommRing 𝕜] [ConditionallyCompletePartialOrder 𝕜]
variable {X : Type*} [PseudoMetricSpace X] [AddCommGroup X] [Module 𝕜 X]
variable {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]
variable {C1 C2 : Set X}

-- The support-function side uses the same primal/dual pairing data as separation, viewed in the
-- opposite orientation and lifted to `WithTopBot`.
local instance instHasPairingDualPrimalWithTopBotStrong : HasPairing Y X (WithTopBot 𝕜) :=
  HasPairing.swap (X := X) (Y := Y) (L := WithTopBot 𝕜)
local notation3:max "δᵛ(" x " | " C ")" => supportFunction (L := WithTopBot 𝕜) C x

/-- Theorem 11.1 (2), stated in the chapter's canonical ambient form: for nonempty sets `C1` and
`C2` in a primal/dual pairing pseudometric space over `𝕜`, a hyperplane separates `C1` and `C2`
strongly if and only if there is a dual vector `b` whose projected infimum on `C1` lies strictly
above the projected supremum on `C2`, i.e. Rockafellar's condition (c). Written through the owner
notation `δᵛ(· | ·)`, this is the textbook strict support-function infimum/supremum inequality.
-/
-- Proof sketch: strong separation provides one hyperplane `⟪x, b⟫ = β` and a positive margin
-- `δ`, so every point of `C1` has projection at least `β + δ` while every point of `C2` has
-- projection at most `β - δ`, yielding `-δᵛ(-b | C1) > δᵛ(b | C2)`. Conversely, if such a gap
-- exists, choose `β` strictly between these two extrema and then choose `ε > 0` small enough
-- that the `ε`-thickenings of `C1` and `C2` still stay in opposite open half-spaces, which gives
-- `H.StronglySeparates Y C1 C2`.
theorem exists_hyperplane_separating_strongly_iff_supportFunction_condition
    (hC1_nonempty : C1.Nonempty) (hC2_nonempty : C2.Nonempty) :
    (∃ H : AffineSubspace 𝕜 X, H.StronglySeparates Y C1 C2) ↔
      ∃ b : Y,
        (-δᵛ(-b | C1) > δᵛ(b | C2)) := sorry

end StrongSeparation

end
