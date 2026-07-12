import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_1_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_8
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_29

noncomputable section

universe u v u' v' w

open scoped Rockafellar

namespace Bifunction

section ConvexSlice

variable {U : Type u} {X : Type v} {XStar : Type v'} {α : Type w}
variable [Add α] [Neg α] [ConditionallyCompleteLattice α]
variable [HasPairing X XStar α]

/-!
Source/core/bridge triage:

- `source-facing`: Lemma33.0.37 records the extreme inconsistent case for the two Chapter 33
  pairings attached to a bifunction `F`, namely when the primal slice `F u` is identically `+∞`
  and the adjoint slice `adjoint F xStar` is identically `-∞`.
- `core/canonical`: the stable owner layer for these domain-complement hypotheses is the Chapter 33
  pair `dom F` and `dom (-F⋆)`, together with the convex slice pairing
  `⟪F u, xStar⟫ᶠ` and the concave adjoint-slice pairing
  `⟪u, F⋆ xStar⟫ᶜ`.
- `bridge/view`: the helper lemmas below isolate each one-sided infinity separately, while the main
  labeled theorem packages the simultaneous opposite-infinity conclusion exactly as in the source.

Domain-style sampling used here:
- `Bifunction.dom` and `Bifunction.mem_dom` from `Chap06.Definition_6_29_8`;
- `Bifunction.adjoint` from `Definition_6_30_14`;
- the Chapter 33 notation owners `⟪·, ·⟫ᶠ` and `⟪·, ·⟫ᶜ`.

Abstraction checks:
- no later Chapter 38 `dom` owner is imported;
- the statement stays on the pairing-based layer rather than an inner-product specialization;
- primal/dual pairings are assumed on the finite layer `HasPairing _ _ α`, then lifted
  canonically to `WithTopBot α` for conjugacy/domain statements;
- the dual ambient parameters `XStar` and `UStar` remain explicit because they are not recoverable
  from `F` alone.
-/

-- Proof sketch: `u ∉ dom F` means the slice `F u` is constantly
-- `⊤`; the convex conjugate of the constant `⊤` function is therefore constantly `⊥`.
/-- If `u` lies outside `dom F`, then the
first Chapter 33 pairing at `u` is `-∞`. -/
theorem convex_slice_pairing_eq_bot_of_not_mem_dom
    (F : U → X → WithTopBot α) {u : U} {xStar : XStar}
    (hu : u ∉ dom F) :
    ⟪F u, xStar⟫ᶠ = (⊥ : WithTopBot α) := sorry

end ConvexSlice

section AdjointSlice

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {α : Type w}
variable [Add α] [Neg α] [ConditionallyCompleteLattice α]
variable [Neg UStar]
variable [HasPairing U UStar α] [HasPairing X XStar α]
variable (F : U → X → WithTopBot α)

local notation "F⋆" => (adjoint XStar UStar F)

/-- The reversed pairing lets an adjoint slice be viewed through the chapter's concave pairing
notation. -/
local instance : HasPairing UStar U (WithTopBot α) := HasPairing.swap

-- Proof sketch: `xStar ∉ dom (-F⋆)` means
-- `adjoint F xStar` is constantly `⊥`; the concave conjugate of the constant `⊥`
-- function is therefore constantly `⊤`.
/-- If `x⋆` lies outside `dom (-F⋆)`, then the second Chapter 33
pairing at `x⋆` is `+∞`. -/
theorem adjoint_slice_pairing_eq_top_of_not_mem_dom_neg_adjoint
    {u : U} {xStar : XStar}
    (hxStar : xStar ∉ dom (-F⋆)) :
    ⟪u, F⋆ xStar⟫ᶜ = (⊤ : WithTopBot α) := sorry

-- Proof sketch: apply the two preceding one-sided lemmas. The first uses `u ∉ dom F`, and the
-- second uses `xStar ∉ dom (-F⋆)`.
/-- Lemma33.0.37: when `u ∉ dom F` and `x⋆ ∉ dom (-F⋆)`, the two
Chapter 33 pairings are
oppositely infinite: `⟪F u, x⋆⟫ᶠ = -∞` and
`⟪u, F⋆ x⋆⟫ᶜ = +∞`. -/
theorem opposite_infinite_pairings_of_not_mem_dom_and_not_mem_dom_neg_adjoint
    {u : U} {xStar : XStar}
    (hu : u ∉ dom F)
    (hxStar : xStar ∉ dom (-F⋆)) :
    ⟪F u, xStar⟫ᶠ = (⊥ : WithTopBot α) ∧
      ⟪u, F⋆ xStar⟫ᶜ = (⊤ : WithTopBot α) := sorry

end AdjointSlice

end Bifunction
