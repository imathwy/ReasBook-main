import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_13
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_6
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_42
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_4_1

noncomputable section

universe u v w

open scoped Rockafellar

namespace Bifunction

section Lagrangian

variable {U : Type u} {UStar : Type*} {X : Type v} {L : Type w}
variable [InfSet L] [Sub L] [Neg L] [HasPairing U UStar L]

local instance : HasPairing UStar U L := HasPairing.swap

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 36.5 characterizes which saddle functions arise as Lagrangians of
  convex programs associated with closed convex bifunctions.
- `core/canonical`: the existing owner is Chapter 6's `Bifunction.lagrangian`, now reused on the
  order-dual codomain via the canonical bifunction bridge `Bifunction.toOrderDual`. The remaining
  owner layer consists of `Bifunction.inverse`, `concaveConjugate`, `Bifunction.IsClosedConvex`,
  `SaddleFunction.IsConcaveConvex`, and `Bifunction.upperClosure`.
- `bridge/view`: the Chapter 7 source formula is the order-dual view of the Chapter 6 Lagrangian,
  and equivalently the pointwise concave conjugate of the inverse slice `(F _*) x`.

Domain-style sampling used here:
- `Bifunction.lagrangian` and `Bifunction.lagrangian_eq_iSup_pairing_add` from
  `Definition_6_30_13`;
- `concaveConjugate` and `concaveConjugate_eq_iInf_pairing_sub` from `Definition_6_30_4`;
- `Bifunction.inverse` and `Bifunction.inverse_apply` from `Definition_36_4_1`;
- `Bifunction.upperConcavePairing` and `Bifunction.upperConcavePairing_apply` from `Defn_34_6`;
- `Bifunction.upperClosure` and `Bifunction.upperClosure_isUpperClosed` from `Defn_34_1`;
- `SaddleFunction.IsConcaveConvex` and `Bifunction.IsClosedConvex` from `Defn_34_2`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → L`;
- primitive source-facing owner reused here: `lagrangian (toOrderDual F)`;
- canonical bridge owner reused here: `upperConcavePairing (F _*)`;
- bridge/view API added here: the source infimum formulas.

Layer target: `bridge/view`, reusing the Chapter 6 owner instead of introducing a second
Lagrangian root in Chapter 7.
-/

/-- Evaluating the Chapter 7 Lagrangian owner at `(u⋆, x)` gives the inverse-slice concave
conjugate `((F _*) x)∗ u⋆`. -/
@[simp] theorem lagrangian_toOrderDual_apply
    (F : U → X → L) (uStar : UStar) (x : X) :
    lagrangian (toOrderDual F) uStar x = ((F _*) x)∗ uStar :=
  rfl

/-- The Chapter 7 Lagrangian owner is exactly the Chapter 34 upper-concave representative of the
inverse bifunction `F _*`. -/
theorem lagrangian_toOrderDual_eq_upperConcavePairing_inverse
    (F : U → X → L) :
    lagrangian (toOrderDual F) =
      (upperConcavePairing (F _*) : UStar → X → L) := by
  funext uStar x
  rfl

/-- Evaluating the Chapter 7 Lagrangian bridge at `(u⋆, x)` gives the infimum formula
`inf_u (⟪u, u⋆⟫ₚ - F _* x u)`. -/
theorem lagrangian_toOrderDual_eq_iInf_pairing_sub_inverse
    (F : U → X → L) (uStar : UStar) (x : X) :
    lagrangian (toOrderDual F) uStar x =
      ⨅ u : U, (⟪u, uStar⟫ₚ - F _* x u) := by
  rw [lagrangian_toOrderDual_apply, concaveConjugate_eq_iInf_pairing_sub]

end Lagrangian

section LagrangianWithTopBot

variable {α : Type*} {U : Type u} {UStar : Type*} {X : Type v}
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α]
variable [HasPairing U UStar (WithTopBot α)]

/-- `WithTopBot` pairing specialization of the generic Lagrangian bridge:
`L(u⋆, x) = inf_u (⟪u, u⋆⟫ₚ + F u x)`. -/
theorem lagrangian_eq_iInf_pairing_add
    (F : U → X → WithTopBot α) (uStar : UStar) (x : X) :
    lagrangian (toOrderDual F) uStar x =
      ⨅ u : U, (⟪u, uStar⟫ₚ : WithTopBot α) + F u x := by
  simpa [inverse_apply, sub_eq_add_neg, add_comm] using
    lagrangian_toOrderDual_eq_iInf_pairing_sub_inverse F uStar x

end LagrangianWithTopBot

section Characterization

open SaddleFunction

variable {𝕜 : Type*} {U : Type u} {UStar : Type*} {X : Type v}
variable [Semiring 𝕜] [AddCommGroup 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [TopologicalSpace U] [AddCommMonoid U] [SMul 𝕜 U]
variable [TopologicalSpace UStar] [AddCommMonoid UStar] [SMul 𝕜 UStar]
variable [TopologicalSpace X] [AddCommMonoid X] [SMul 𝕜 X]
variable [HasPairing U UStar 𝕜]

/-!
Abstraction boundary note:

- `lagrangian (toOrderDual F)` is already codomain-generic (pairing + infimum + subtraction).
- this theorem keeps the source scalar parameter abstract at `𝕜` while presenting the codomain at
  the canonical owner level `WithTopBot 𝕜` (rather than the alias `EReal`);
- the intrinsic Chapter 34 owner for this chapter-level characterization is
  `upperConcavePairing (F _*)`;
- the Chapter 6 Lagrangian expression remains as a downstream bridge surface via
  `lagrangian_toOrderDual_eq_upperConcavePairing_inverse`;
- the source-facing closedness side is stated with the fixed-point owner `IsUpperClosed`, not a
  raw closure equation.
-/

/-- Theorem 36.5 at the intrinsic Chapter 34 owner layer: a saddle function `L` is generated by
some closed convex bifunction through `upperConcavePairing (F _*)` if and only if `L` is
concave-convex and upper closed. -/
theorem exists_isClosedConvex_eq_upperConcavePairing_inverse_iff
    (L : UStar → X → WithTopBot 𝕜) :
    (∃ F : U → X → WithTopBot 𝕜,
      IsClosedConvex F ∧
        L = (upperConcavePairing (F _*) : UStar → X → WithTopBot 𝕜)) ↔
      IsConcaveConvex 𝕜 L ∧ IsUpperClosed L := by
  sorry

/-- Source-facing bridge form of Theorem 36.5: a saddle function `L` is the Chapter 6 Lagrangian
of a convex program associated with some closed convex bifunction if and only if `L` is
concave-convex and upper closed. -/
theorem exists_isClosedConvex_eq_lagrangian_iff
    (L : UStar → X → WithTopBot 𝕜) :
    (∃ F : U → X → WithTopBot 𝕜, IsClosedConvex F ∧ L = lagrangian (toOrderDual F)) ↔
      IsConcaveConvex 𝕜 L ∧ IsUpperClosed L := by
  simpa [lagrangian_toOrderDual_eq_upperConcavePairing_inverse] using
    exists_isClosedConvex_eq_upperConcavePairing_inverse_iff L

end Characterization

end Bifunction
