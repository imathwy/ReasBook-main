import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_4
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem33_1

noncomputable section

universe u v w z

open scoped Rockafellar

namespace Bifunction

section AdmissibleOwners

variable {𝕜 : Type z} {U : Type u} {X : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [TopologicalSpace X] [AddCommMonoid X] [Module 𝕜 X]

/-!
Source/core/bridge triage:

- `source-facing`: Lemma33.0.18 extracts the one-to-one correspondence promised by Theorem 33.1
  between image-closed convex bifunctions and concave-convex kernels that are closed in the second
  variable.
- `core/canonical`: the map-level owner is `Bifunction.lowerPairing` from `Defn_34_2`, together
  with graph convexity of `Function.uncurry F`, slice closedness `Bifunction.IsConvexClosed F`,
  and the saddle owner `SaddleFunction.IsConcaveConvex 𝕜 K`.
- `bridge/view`: the correspondence is the mutual inverse relation obtained by using that same
  owner once with pairing `X × XStar` and once with the swapped pairing `XStar × X`, on the direct
  admissible subclasses cut out by the earlier Chapter 33 owners.

Domain-style sampling used here:
- `Bifunction.lowerPairing` and `Bifunction.lowerPairing_apply` from `Defn_34_2`;
- `Set.InvOn` for mutually inverse maps on restricted classes;
- `Bifunction.IsConvexClosed`;
- `SaddleFunction.IsConcaveConvex`;
- `lowerPairing_isConcaveConvex_of_uncurry_isConvex`;
- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull`.

Layer target: `bridge/view`, stated directly on the admissible classes and using only earlier
Chapter 33 owners.
-/

/-- The admissible source class for the lower-pairing involution consists of bifunctions whose
uncurried graph is convex and whose second-variable slices are closed. -/
def lowerPairingSourceAdmissible (F : U → X → WithBotTop 𝕜) : Prop :=
  (Function.uncurry F).IsConvex 𝕜 ∧ IsConvexClosed F

variable {XStar : Type w}
variable [TopologicalSpace XStar] [AddCommMonoid XStar] [Module 𝕜 XStar]

/-- The admissible target class for the lower-pairing involution consists of concave-convex
kernels whose second-variable slices are closed. -/
def lowerPairingTargetAdmissible (K : U → XStar → WithBotTop 𝕜) : Prop :=
  SaddleFunction.IsConcaveConvex 𝕜 K ∧ IsConvexClosed K

end AdmissibleOwners

section

variable {𝕜 : Type z} {U : Type u} {X : Type v} {XStar : Type w}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [OrderTopology 𝕜] [NoBotOrder 𝕜] [NoMinOrder 𝕜] [Nonempty 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X] [FiniteDimensional 𝕜 X]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [FiniteDimensional 𝕜 XStar]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]
variable [HasLinearPairing XStar X 𝕜] [HasContinuousPairing XStar X 𝕜]

-- Proof sketch: Theorem 33.0.16 gives the forward and reverse reconstruction formulas by
-- partial Fenchel conjugation. Second-variable closedness on both sides then identifies each
-- slice with its biconjugate, yielding the two inverse identities on the admissible classes.
/-- Lemma33.0.18: partial Fenchel conjugation in the second variable is inverse, on the class of
convex bifunctions closed in the second variable and the class of concave-convex bifunctions
closed in the second variable, to the reverse partial conjugation. The statement is kept on the
finite-dimensional scalar-field continuous linear pairing layer actually used by the Chapter 12
reconstruction theorems behind the inverse identities. -/
theorem lowerPairing_invOn_admissibleClasses :
    Set.InvOn
      (lowerPairing X)
      (lowerPairing XStar)
      {F : U → X → WithBotTop 𝕜 | lowerPairingSourceAdmissible F}
      {K : U → XStar → WithBotTop 𝕜 | lowerPairingTargetAdmissible K} := sorry

end

end Bifunction
