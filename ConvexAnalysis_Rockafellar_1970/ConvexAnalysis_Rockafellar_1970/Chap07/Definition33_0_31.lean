import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_28

noncomputable section

open scoped Rockafellar

universe u v u' v' w

namespace Bifunction

section PairingEquation

variable {U : Type u} {X : Type v} {XStar : Type v'} {L : Type w}
variable [Sub L] [Neg L] [SupSet L] [InfSet L]
variable [HasPairing X XStar L]
variable {UStar : Type u'} [Neg UStar] [HasPairing U UStar L]
variable [HasPairing (U × X) (UStar × XStar) L]

/-!
Source/core/bridge triage:

- `source-facing`: Definition33.0.31 introduces the pairing equation for a convex bifunction `F`,
  at a fixed primal parameter `u` and dual parameter `xStar`.
- `core/canonical`: the owner layer is the equality between the convex pairing value
  `⟪F u, xStar⟫ᶠ` and the concave pairing value `⟪u, F⋆ xStar⟫ᶜ`.
- `bridge/view`: the companion theorem below unfolds this owner into the displayed `sup = inf`
  formula.

Domain-style sampling inspected before repair:
- `Bifunction.adjoint` / `F⋆`;
- `convexConjugate_eq_iSup_pairing_sub` applied to the slice `F u`;
- `concaveConjugate_eq_iInf_pairing_sub` applied to the adjoint slice `F⋆ xStar`;
- the canonical swapped-pairing bridge `HasPairing.swap`.

Primitive vs derived API:
- primitive data: the bifunction `F : U → X → L`, together with the pairings needed to
  evaluate the primal and dual slices;
- primitive owner: `PairingEquationAt`;
- derived API: the explicit `⨆ = ⨅` formula theorem below.
-/

variable (F : U → X → L)

/-- Definition33.0.31: the pairing equation for a bifunction `F` and its adjoint asserts, at
`(u, xStar)`, that the convex pairing value of the slice `F u` at `xStar` equals the concave
pairing value of the adjoint slice `F⋆ xStar` at `u`. -/
def PairingEquationAt
    (u : U) (xStar : XStar) : Prop :=
  let _ : HasPairing UStar U L := HasPairing.swap
  ⟪F u, xStar⟫ᶠ = ⟪u, F⋆ xStar⟫ᶜ

-- Proof sketch: rewrite the two sides of `PairingEquationAt` by the canonical conjugate
-- specification theorems for the slice `F u` and the adjoint slice
-- `F⋆ xStar`.
/-- Unpack `PairingEquationAt F u xStar` as the displayed `sup = inf` formula from
Definition33.0.31, with the right side written through the canonical adjoint notation `F⋆`. -/
theorem pairingEquationAt_iff
    (u : U) (xStar : XStar) :
    PairingEquationAt F u xStar ↔
      (⨆ x : X, ⟪x, xStar⟫ₚ - F u x) =
        ⨅ uStar : UStar, ⟪u, uStar⟫ₚ - F⋆ xStar uStar := by
  let _ : HasPairing UStar U L := HasPairing.swap
  rw [PairingEquationAt, convexConjugate_eq_iSup_pairing_sub, concaveConjugate_eq_iInf_pairing_sub]

end PairingEquation

end Bifunction
