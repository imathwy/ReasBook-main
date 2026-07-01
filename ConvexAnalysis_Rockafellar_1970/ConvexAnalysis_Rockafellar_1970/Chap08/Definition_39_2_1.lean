import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

universe u v w

/-!
Source/core/bridge triage:

- `source-facing`: Definition 39.2.1 introduces the process pairing `⟨Au, x⋆⟩`, namely the
  support value of the fiber `Au` at `x⋆`.
- `core/canonical`: the owner abstraction underneath is the support-function surface
  `δᵛ[WithBotTop 𝕜](xStar | C)`.
- `bridge/view`: the companion theorem identifies this source-facing process pairing with the
  convex pairing of the corresponding indicator slice, via
  `convexConjugate_indicatorFunction_eq_supportFunction_pointwise`.

Primary mathematical domain:
- support functions and indicator-function conjugacy on convex-process fibers.

Domain-style sampling used here:
- `supportFunction` from `Chap01.Defintion_4_8_2`;
- `convexConjugate_indicatorFunction_eq_supportFunction_pointwise` from
  `Chap03.Text_13_1_4`;
- the Chapter 33 raw owner `convexConjugate`.

Primitive data vs derived API:
- primitive source-facing owner introduced here:
  `supremumProcessPairing 𝕜 XStar A u xStar = δᵛ[WithBotTop 𝕜](xStar | A.image ({u} : Set U))`;
- primitive reused owners: the fiber set `A.image ({u} : Set U)` and the indicator
  `δ[𝕜](· | A.image ({u} : Set U))`;
- derived API: the source-facing process-pairing versus indicator-pairing identity below.

Layer target: `source-facing`.

Notation evaluation:
- the source writes contextual bracket notation `⟨Au, x⋆⟩`, but this chapter already uses bracket
  notation for conjugate pairings;
- to avoid a second overloaded bracket surface with different owners and elaboration behavior, the
  source-facing public owner here is the explicit name `supremumProcessPairing`.
-/

namespace SetRel

section Pairing

variable {U : Type u} {X : Type v} {XStar : Type w}

/-- Definition 39.2.1: the supremum-oriented Chapter 39 process pairing `⟨Au, x⋆⟩` is the
support value of the fiber `Au` at `x⋆`. The dual carrier `XStar` is part of the owner because it
is not recoverable from `A : SetRel U X` alone. -/
abbrev supremumProcessPairing (𝕜 : Type*) [ConditionallyCompleteLattice 𝕜]
    (XStar : Type w) [HasPairing XStar X 𝕜] (A : SetRel U X) :
    U → XStar → WithBotTop 𝕜 :=
  fun u xStar ↦ δᵛ[WithBotTop 𝕜](xStar | A.image ({u} : Set U))

section Bridge

variable {𝕜 : Type*}
variable [ConditionallyCompleteLattice 𝕜]
variable [AddGroup 𝕜]
variable [HasPairing XStar X 𝕜] [HasPairing X XStar 𝕜] [HasPairingSwap X XStar 𝕜]

-- Proof sketch: this is exactly
-- `convexConjugate_indicatorFunction_eq_supportFunction_pointwise` specialized to the fiber
-- `A.image ({u} : Set U)`.
/-- The Chapter 39 process pairing is the convex pairing of the indicator slice of the
corresponding fiber. -/
theorem supremumProcessPairing_eq_convexPairing_indicator
    (A : SetRel U X) (u : U) (xStar : XStar) :
    supremumProcessPairing 𝕜 XStar A u xStar =
      (δ[𝕜](· | A.image ({u} : Set U)))⋆ xStar := by
  simpa [supremumProcessPairing] using
    (convexConjugate_indicatorFunction_eq_supportFunction_pointwise
      (E := X) (EStar := XStar) (α := 𝕜)
      (C := A.image ({u} : Set U)) (xStar := xStar)).symm

end Bridge

end Pairing

end SetRel
