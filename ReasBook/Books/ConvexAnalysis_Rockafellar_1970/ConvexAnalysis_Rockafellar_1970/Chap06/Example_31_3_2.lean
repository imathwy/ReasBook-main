import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_11
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_7_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_5

noncomputable section

open scoped Pointwise Rockafellar
attribute [local instance] Classical.propDecidable
universe u v

/-!
Source/core/bridge triage:

- `source-facing`: Example 31.3.2 computes the primal and dual Kuhn--Tucker subgradient sets at
  owner level as orthant-normal-cone translations.
- `core/canonical`: the owner abstractions used here are the dual-valued owners
  `∂[Y](·)(·)` and `∂⁺[Y](·)(·)`, together with the orthant
  owner `orthant` and the pairing-based normal-cone owner `normalCone`.

Domain-style sampling used here:
- `orthant` and `mem_orthant_iff` from `Chap01.Definition_2_5_11`;
- `normalCone` and `mem_normalCone_iff` from `Chap01.Definition_2_7_10`;
- `subdifferentialAt` notation `∂[Y]f(x)` from `Chap05.Definition_23_0_6`;
- `concaveSubdifferentialAt` notation `∂⁺[Y]g(x)` from `Chap06.Definition_6_30_5`.

Primitive data vs derived API:
- primitive source data: dual coefficients in an arbitrary paired dual carrier for the owner-level
  LP branches;
- primitive owner surface: the dual-valued owner sets `∂[Y](·)(·)` and `∂⁺[Y](·)(·)`;
- derived API: the normal-cone translation formulas.

Ambient/codomain layer notes:
- owner-level statements are pairing-based (paired dual carrier + normal cone), not hard-coded to
  vector-inner-product owners;
- primal codomain is at the weaker `WithTopBot 𝕜` layer;
- dual branch is also stated on `WithTopBot 𝕜`: this branch is an orthant-restricted affine map
  with value `⊥` outside the feasible region, so no extra `EReal` specialization is needed.

Layer target: `source-facing` owner theorems only, with no Euclidean coordinate bridge API and no
parallel LP-specific wrapper API.
-/

section PrimalOwner

variable {𝕜 : Type v} [Ring 𝕜] [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜] [AddLeftMono 𝕜]
variable {X : Type u} [AddCommGroup X] [Module 𝕜 X]
  [PartialOrder X] [IsOrderedAddMonoid X] [PosSMulMono 𝕜 X]

variable {Y : Type (max u v)} [AddCommGroup Y] [HasPairing X Y 𝕜]
  [HasPairingZeroLeft X Y 𝕜] [HasPairingAddRight X Y 𝕜]
  [HasPairingSubLeft X Y 𝕜] [HasPairingSubRight X Y 𝕜]
private def primalOwnerBranch (aStar : Y) : X → WithTopBot 𝕜 :=
  fun z : X ↦ ((⟪z, aStar⟫ₚ : 𝕜) : WithTopBot 𝕜) + δ[𝕜](z | orthant[𝕜](X))

-- Proof sketch: the primal branch is the affine functional `z ↦ ⟪z, a⋆⟫ₚ` plus the orthant
-- indicator in the canonical `WithTopBot 𝕜` codomain. Applying the Chapter 23 owner for affine
-- perturbations together with the Chapter 1 normal-cone owner for the indicator gives the
-- translated cone `{a⋆} + N[𝕜](x | orthant)`.
/-- Example 31.3.2, primal side at owner level: for
`f x = ⟪x, a⋆⟫ₚ + δ[𝕜](x | orthant[𝕜](X))`, the pairing-level
subdifferential in any paired dual carrier is the
translate of the orthant normal cone by `a⋆`. -/
theorem subdifferentialAt_apply_add_indicator_orthant
    (aStar : Y)
    (x : X) :
    ∂[Y] (primalOwnerBranch aStar : X → WithTopBot 𝕜)(x) =
      ({aStar} : Set Y) + N[𝕜](x | orthant[𝕜](X)) := by
  sorry

end PrimalOwner

section DualOwner

variable {𝕜 : Type v} [Ring 𝕜] [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜] [AddLeftMono 𝕜]
variable {U : Type u} [AddCommGroup U] [Module 𝕜 U]
  [PartialOrder U] [IsOrderedAddMonoid U] [PosSMulMono 𝕜 U]

variable {Y : Type (max u v)} [AddCommGroup Y] [HasPairing U Y 𝕜]
  [HasPairingZeroLeft U Y 𝕜] [HasPairingNegRight U Y 𝕜]
  [HasPairingAddRight U Y 𝕜] [HasPairingSubLeft U Y 𝕜]
  [HasPairingSubRight U Y 𝕜]
private def dualOwnerBranch (a : Y) : U → WithTopBot 𝕜 :=
  fun v : U ↦
    if v ∈ orthant[𝕜](U) then ((⟪v, a⟫ₚ : 𝕜) : WithTopBot 𝕜) else (⊥ : WithTopBot 𝕜)

-- Proof sketch: rewrite the dual branch as the affine functional `u⋆ ↦ ⟪u⋆, a⟫ₚ` restricted to
-- the nonnegative orthant and equal to `⊥` off the orthant, then apply the canonical concave
-- subdifferential owner formula together with the orthant normal-cone description.
/-- Example 31.3.2, dual side at owner level: for the orthant-restricted affine branch
`u⋆ ↦ if u⋆ ∈ orthant[𝕜](U) then ⟪u⋆, a⟫ₚ else ⊥`, the pairing-level
concave subdifferential in
any paired dual carrier is the translate by `a` of the negative orthant normal cone. -/
theorem concaveSubdifferentialAt_apply_on_orthant
    (a : Y)
    (uStar : U) :
    ∂⁺[Y] (dualOwnerBranch a : U → WithTopBot 𝕜)(uStar) =
      ({a} : Set Y) + (-N[𝕜](uStar | orthant[𝕜](U))) := by
  sorry

end DualOwner
