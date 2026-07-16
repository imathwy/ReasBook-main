import Mathlib.Data.Setoid.Basic
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_5
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_4

noncomputable section

universe u v

open scoped Rockafellar

namespace SaddleFunction

section Equivalence

open Bifunction

variable {𝕜 : Type*}
variable {U : Type u} {X : Type v}
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace U] [TopologicalSpace X]

/-- A concave-convex saddle-function is closed when both `cl₁ K` and `cl₂ K` are equivalent to
`K`, exactly as in the opening definitions of §34. -/
def IsClosed [ConditionallyCompleteLattice 𝕜] [Neg 𝕜] (K : U → X → WithTopBot 𝕜) : Prop :=
  cl₁ K ∼ K ∧ cl₂ K ∼ K

section

variable [ConditionallyCompleteLinearOrder 𝕜]
variable [AddGroup 𝕜]
variable [NoMinOrder 𝕜] [Nonempty 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
variable [NoBotOrder 𝕜]

/-- Companion source-facing form of closedness: by idempotence of the one-variable closure
operators, `K` is closed exactly when `cl₁ (cl₂ K) = cl₁ K` and `cl₂ (cl₁ K) = cl₂ K`. -/
theorem isClosed_iff (K : U → X → WithTopBot 𝕜) :
    IsClosed K ↔ cl₁ (cl₂ K) = cl₁ K ∧ cl₂ (cl₁ K) = cl₂ K := by
  constructor
  · intro h
    rcases h with ⟨h₁, h₂⟩
    rcases (Bifunction.equivalent_iff (cl₁ K) K).1 h₁ with ⟨_, h₂₁⟩
    rcases (Bifunction.equivalent_iff (cl₂ K) K).1 h₂ with ⟨h₁₂, _⟩
    exact ⟨h₁₂, h₂₁⟩
  · rintro ⟨h₁₂, h₂₁⟩
    refine ⟨?_, ?_⟩
    · exact (Bifunction.equivalent_iff (cl₁ K) K).2 ⟨closure1_idem K, h₂₁⟩
    · exact (Bifunction.equivalent_iff (cl₂ K) K).2 ⟨h₁₂, closure2_idem K⟩

end

end Equivalence

end SaddleFunction

namespace Bifunction

section ClosedConvex

variable {𝕜 : Type*}
variable {U : Type u} {X : Type v}
variable [TopologicalSpace U] [TopologicalSpace X]
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]

/-- A closed convex bifunction is one whose uncurried graph function is convex and lower
semicontinuous. This is the exact ambient notion used in Theorem 34.2, without strengthening to
properness. -/
abbrev IsClosedConvex (F : U → X → WithTopBot 𝕜) : Prop :=
  convᵇ[𝕜](F) ∧ closedᵇ(F)

namespace IsClosedConvex

theorem convex {F : U → X → WithTopBot 𝕜}
    (hF : IsClosedConvex F) :
    convᵇ[𝕜](F) :=
  hF.1

theorem closed {F : U → X → WithTopBot 𝕜}
    (hF : IsClosedConvex F) :
    closedᵇ(F) :=
  hF.2

end IsClosedConvex

/-- The closed-convex owner unpacks to convexity and lower semicontinuity of the uncurried graph
function. -/
theorem isClosedConvex_iff (F : U → X → WithTopBot 𝕜) :
    IsClosedConvex F ↔ convᵇ[𝕜](F) ∧ closedᵇ(F) :=
  Iff.rfl

end ClosedConvex

section Pairings

variable {L : Type*}
variable {U : Type u} {X : Type v} {XStar : Type*}
variable [SupSet L] [Sub L] [HasPairing X XStar L]

variable (XStar) in
/-- Section 34's lower representative `K̲(u, x⋆) = (F u)⋆ x⋆` attached to a convex bifunction
`F`, at the primitive conjugation codomain layer `L`.

The dual ambient parameter `XStar` is part of the public owner surface because it is not
recoverable from `F : U → X → L` alone. -/
def lowerPairing (F : U → X → L) : U → XStar → L :=
  fun u xStar ↦ (F u)⋆ xStar

@[simp] theorem lowerPairing_apply
    (F : U → X → L) (u : U) (xStar : XStar) :
    lowerPairing XStar F u xStar = (F u)⋆ xStar :=
  rfl

section

variable [InfSet L] [Neg L]
variable {UStar : Type*}
variable [Neg UStar] [HasPairing U UStar L] [HasPairing (U × X) (UStar × XStar) L]

/-!
The adjoint-side representative `(u, x⋆) ↦ (adjoint F x⋆)∗ u` is the natural general-dual
bridge behind the self-dual Chapter 34 owner `upperPairing`.
Owning it once keeps later files from repeating the same raw lambda formula.
-/
/-- The general-dual upper representative attached to a convex bifunction `F`, expressed through
the adjoint bifunction and first-variable concave conjugation. The reversed pairing needed by
`concaveConjugate` is derived canonically from `HasPairing U UStar L` and is not part of the
public owner assumptions. -/
def upperAdjointPairing (XStar : Type*) (UStar : Type*)
    [Neg UStar] [HasPairing U UStar L] [HasPairing (U × X) (UStar × XStar) L]
    (F : U → X → L) : U → XStar → L :=
  fun u xStar ↦
    let _ : HasPairing UStar U L := HasPairing.swap
    concaveConjugate (adjoint XStar UStar F xStar) u

omit [HasPairing X XStar L] in
@[simp] theorem upperAdjointPairing_apply
    (F : U → X → L) (u : U) (xStar : XStar) :
    upperAdjointPairing XStar UStar F u xStar =
      (let _ : HasPairing UStar U L := HasPairing.swap
       concaveConjugate (adjoint XStar UStar F xStar) u) :=
  rfl

section

variable [Preorder L]

/-- The Chapter 34 representative class at the primitive pairing layer: for a bifunction `F`,
`ωAdj(F)` is the pointwise interval between the lower representative `lowerPairing` and the
general-dual upper representative `upperAdjointPairing`. -/
def omegaAdjoint (XStar : Type*) (UStar : Type*)
    [HasPairing X XStar L] [Neg UStar] [HasPairing U UStar L]
    [HasPairing (U × X) (UStar × XStar) L]
    (F : U → X → L) : Set (U → XStar → L) :=
  Set.Icc (lowerPairing XStar F) (upperAdjointPairing XStar UStar F)

scoped[Rockafellar] notation "ΩAdj[" UStar "](" F ")" =>
  Bifunction.omegaAdjoint _ UStar F

/-- Membership in `ωAdj(F)` is exactly the pairing-level sandwich
`lowerPairing F ≤ K ≤ upperAdjointPairing F`. -/
theorem mem_omegaAdjoint_iff
    {XStar : Type*} {UStar : Type*}
    [HasPairing X XStar L] [Neg UStar] [HasPairing U UStar L]
    [HasPairing (U × X) (UStar × XStar) L]
    (F : U → X → L) (K : U → XStar → L) :
    K ∈ ΩAdj[UStar](F) ↔
      lowerPairing XStar F ≤ K ∧ K ≤ upperAdjointPairing XStar UStar F :=
  Iff.rfl

end

section

variable [Neg U] [HasPairing U U L] [HasPairing (U × X) (U × XStar) L]

/-- Section 34's upper representative `K̅(u, x⋆) = (u, F* x⋆)` attached to a convex bifunction
`F`, written directly through the canonical adjoint-bifunction owner `adjoint`.

The dual ambient parameter `XStar` is part of the raw owner surface because it is not recoverable
from `F : U → X → L` alone. -/
def upperPairing (XStar : Type*) [HasPairing (U × X) (U × XStar) L]
    (F : U → X → L) : U → XStar → L :=
  fun u xStar ↦ concaveConjugate (adjoint XStar U F xStar) u

@[simp] theorem upperPairing_apply
    {XStar : Type*} [HasPairing (U × X) (U × XStar) L]
    (F : U → X → L) (u : U) (xStar : XStar) :
    upperPairing XStar F u xStar =
      concaveConjugate (adjoint XStar U F xStar) u :=
  rfl

section

variable [Preorder L]

/-- The class `Ω(F)` from Theorem 34.2, as the pointwise interval between the lower and upper
canonical saddle representatives generated by `F` at codomain layer `L`. -/
def omega (XStar : Type*) [HasPairing X XStar L] [HasPairing (U × X) (U × XStar) L]
    (F : U → X → L) : Set (U → XStar → L) :=
  Set.Icc (lowerPairing XStar F) (upperPairing XStar F)

scoped[Rockafellar] notation "Ω(" F ")" => Bifunction.omega _ F

/-- Membership in `Ω(F)` is exactly the source sandwich relation
`lowerPairing F ≤ K ≤ upperPairing F`. -/
theorem mem_omega_iff
    {XStar : Type*} [HasPairing X XStar L] [HasPairing (U × X) (U × XStar) L]
    (F : U → X → L) (K : U → XStar → L) :
    K ∈ Ω(F) ↔ lowerPairing XStar F ≤ K ∧ K ≤ upperPairing XStar F :=
  Iff.rfl

end

end

end

end Pairings

end Bifunction
