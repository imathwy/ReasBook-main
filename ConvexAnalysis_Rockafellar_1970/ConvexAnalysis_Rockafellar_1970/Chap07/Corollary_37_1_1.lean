import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_42
import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem_37_1

noncomputable section

universe u v

open scoped Rockafellar

namespace Bifunction

section

open SaddleFunction

variable {R : Type*} {α : Type*}
variable {U : Type u} {UStar : Type*} {X : Type v} {XStar : Type*}
variable [Ring R] [PartialOrder R]
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [AddCommGroup α]
variable [TopologicalSpace U] [AddCommGroup U] [Module R U]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module R UStar]
variable [TopologicalSpace X] [AddCommGroup X] [Module R X]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module R XStar]
variable [HasPairing U UStar (WithBotTop α)] [HasPairing X XStar (WithBotTop α)]
variable [SMul R (WithBotTop α)]

local notation "lowerConjugate" =>
  (Bifunction.lowerConjugate : (U → XStar → WithBotTop α) → UStar → X → WithBotTop α)
local notation "upperConjugate" =>
  (Bifunction.upperConjugate : (U → XStar → WithBotTop α) → UStar → X → WithBotTop α)

/-- The lower conjugate of a closed concave-convex saddle-function is itself concave-convex. -/
theorem lowerConjugate_isConcaveConvex
    {K : U → XStar → WithBotTop α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K) :
    IsConcaveConvex R (lowerConjugate K) := sorry

/-- The lower conjugate of a closed concave-convex saddle-function is lower closed. -/
theorem lowerConjugate_isLowerClosed
    {K : U → XStar → WithBotTop α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K) :
    IsLowerClosed (lowerConjugate K) := sorry

/-- The upper conjugate of a closed concave-convex saddle-function is itself concave-convex. -/
theorem upperConjugate_isConcaveConvex
    {K : U → XStar → WithBotTop α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K) :
    IsConcaveConvex R (upperConjugate K) := sorry

/-- The upper conjugate of a closed concave-convex saddle-function is upper closed. -/
theorem upperConjugate_isUpperClosed
    {K : U → XStar → WithBotTop α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K) :
    IsUpperClosed (upperConjugate K) := sorry

/-- The lower and upper conjugates of a closed concave-convex saddle-function belong to the same
Chapter 34 equivalence class. -/
theorem lowerConjugate_equivalent_upperConjugate
    {K : U → XStar → WithBotTop α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K) :
    lowerConjugate K ∼ upperConjugate K := sorry

end

section

open SaddleFunction

variable {R : Type*} {α : Type*}
variable {U : Type u} {UStar : Type*} {X : Type v} {XStar : Type*}
variable [Ring R] [PartialOrder R]
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [AddCommGroup α]
variable [TopologicalSpace U] [AddCommGroup U] [Module R U]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module R UStar]
variable [TopologicalSpace X] [AddCommGroup X] [Module R X]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module R XStar]
variable [HasPairing U UStar (WithBotTop α)] [HasPairing X XStar (WithBotTop α)]
variable [SMul R (WithBotTop α)]

local notation "lowerConjugate" =>
  (Bifunction.lowerConjugate : (U → XStar → WithBotTop α) → UStar → X → WithBotTop α)
local notation "upperConjugate" =>
  (Bifunction.upperConjugate : (U → XStar → WithBotTop α) → UStar → X → WithBotTop α)

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 37.1.1 says that conjugation sends a closed concave-convex
  saddle-function to a conjugate equivalence class whose lower and upper representatives are
  respectively lower closed and upper closed, that this conjugate class depends only on the
  original Chapter 34 equivalence class, and that conjugating again returns to the original
  equivalence class. The source surface is the paired-space one from Theorem 37.1:
  `K : U → XStar → WithBotTop α` and conjugates
  `K⋆ : UStar → X → WithBotTop α`.
- `core/canonical`: the owner layer already present in the chapter is `lowerConjugate`,
  `upperConjugate`, the equivalence relation `∼`, and the saddle-function predicates
  `IsConcaveConvex`, `IsClosed`, `IsLowerClosed`, and `IsUpperClosed`.
- `bridge/view`: Theorem 34.2 and Theorem 37.1 identify a closed concave-convex saddle-function
  with a closed convex generator `F` and then identify its conjugates with the canonical lower
  and upper representatives of the conjugate-side generator.

Domain-style sampling used here:
- `Bifunction.lowerConjugate` and `Bifunction.upperConjugate` from `Definition_37_1_1`;
- `Bifunction.lowerConjugate_eq_lowerPairing_inverse_adjointFunction_of_mem_omega` and
  `Bifunction.upperConjugate_eq_lagrangian_of_mem_omega` from `Theorem_37_1`;
- `Bifunction.mem_omega_iff_equivalent_lowerPairing`,
  `Bifunction.isConcaveConvex_of_mem_omega`, and `Bifunction.isClosed_of_mem_omega` from
  `Theorem_34_2`;
- `SaddleFunction.IsLowerClosed` and `SaddleFunction.IsUpperClosed` from
  `Definition33_0_42`.

Primitive data vs derived API:
- primitive source data: a closed concave-convex saddle-function
  `K : U → XStar → WithBotTop α`;
- primitive owner data reused here: `lowerConjugate K`, `upperConjugate K`, and `K ∼ L`;
- derived API recorded here: lower/upper closedness of the two conjugates, equivalence of the
  two conjugate representatives, invariance under passage to an equivalent representative, and
  the return to the original equivalence class after conjugating any representative of the
  conjugate class.

Layer target: `source-facing`, stated directly on the existing Chapter 34 and Chapter 37 owners.
-/

section

-- Proof sketch: use Theorem 34.2 to place `K` and `L` in the same class `Ω(F)` for the closed
-- convex generator `F` of `K`. Theorem 37.1 then identifies the lower conjugates of both
-- representatives with the same canonical lower conjugate-side representative, and likewise for
-- the upper conjugates, so both conjugate assignments are invariant on the Chapter 34
-- equivalence class.
/-- Corollary 37.1.1: the lower conjugate depends only on the Chapter 34 equivalence class of a
closed concave-convex saddle-function. -/
theorem lowerConjugate_equivalent_of_equivalent
    {K L : U → XStar → WithBotTop α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K)
    (hKL : K ∼ L) :
    lowerConjugate K ∼ lowerConjugate L := sorry

/-- Corollary 37.1.1: the upper conjugate depends only on the Chapter 34 equivalence class of a
closed concave-convex saddle-function. -/
theorem upperConjugate_equivalent_of_equivalent
    {K L : U → XStar → WithBotTop α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K)
    (hKL : K ∼ L) :
    upperConjugate K ∼ upperConjugate L := sorry

end

variable [HasPairing UStar U (WithBotTop α)] [HasPairing XStar X (WithBotTop α)]

section

local notation "lowerConjugate" =>
  (Bifunction.lowerConjugate :
    (UStar → X → WithBotTop α) → U → XStar → WithBotTop α)
local notation "upperConjugate" =>
  (Bifunction.upperConjugate :
    (UStar → X → WithBotTop α) → U → XStar → WithBotTop α)
local notation "sourceLowerConjugate" =>
  (Bifunction.lowerConjugate :
    (U → XStar → WithBotTop α) → UStar → X → WithBotTop α)

-- Proof sketch: the hypothesis places `KStar` in the same conjugate-side class as
-- `lowerConjugate K`, hence also in the class of `upperConjugate K` by the previous theorem.
-- Apply the corresponding lower/upper conjugate invariance theorem on that conjugate class, and
-- then use the converse half of Theorem 37.1 for the common closed convex generator to identify
-- each conjugate of `KStar` with the original class of `K`.
/-- Conjugating any representative of the conjugate equivalence class returns, via lower
conjugation, a representative of the original Chapter 34 equivalence class. -/
theorem lowerConjugate_equivalent_original_of_equivalent_lowerConjugate
    {K : U → XStar → WithBotTop α} {KStar : UStar → X → WithBotTop α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K)
    (hKStar : KStar ∼ sourceLowerConjugate K) :
    lowerConjugate KStar ∼ K := sorry

/-- Conjugating any representative of the conjugate equivalence class returns, via upper
conjugation, a representative of the original Chapter 34 equivalence class. -/
theorem upperConjugate_equivalent_original_of_equivalent_lowerConjugate
    {K : U → XStar → WithBotTop α} {KStar : UStar → X → WithBotTop α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K)
    (hKStar : KStar ∼ sourceLowerConjugate K) :
    upperConjugate KStar ∼ K := sorry

end

end

end Bifunction
