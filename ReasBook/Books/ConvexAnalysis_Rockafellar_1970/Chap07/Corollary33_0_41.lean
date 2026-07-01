import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_31
import ConvexAnalysis_Rockafellar_1970.Chap07.Lemma33_0_37

noncomputable section

universe u v u' v' w

open scoped Rockafellar

namespace Bifunction

section

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {α : Type w}
variable [Add α] [Neg α] [ConditionallyCompleteLattice α]
variable [Neg UStar]
variable [HasPairing U UStar α] [HasPairing X XStar α]
variable (F : U → X → WithTopBot α)

local notation "F⋆" => (adjoint XStar UStar F)

/-!
Source/core/bridge triage:

- `source-facing`: Corollary33.0.41 says that if neither `dom F` nor
  `dom (-F⋆)` is the whole ambient space, then the Chapter 33 pairing equation cannot hold for
  every pair `(u, x⋆)`.
- `core/canonical`: use the established owners directly:
  `dom`, `dom (-F⋆)`, and `PairingEquationAt`.
- `bridge/view`: `Set.ne_univ_iff_exists_notMem` converts the proper-domain hypotheses into
  outside-domain witnesses, and Lemma33.0.37 turns those witnesses into the impossible equality
  `⊥ = ⊤`.

Domain-style sampling used here:

- `Bifunction.dom` and `Bifunction.mem_dom`;
- `Bifunction.PairingEquationAt`;
- `Bifunction.opposite_infinite_pairings_of_not_mem_dom_and_not_mem_dom_neg_adjoint`;
- `Set.ne_univ_iff_exists_notMem`.

Abstraction checks for this item:

- codomain/ambient layer: kept at `WithTopBot α`, because both `dom F` / `dom (-F⋆)` and the
  upstream opposite-infinity bridge lemma are
  owned on this layer;
- pairing owner layer: primal/dual pairings are taken at the finite-value layer
  `HasPairing _ _ α`, with canonical lift to `WithTopBot α`;
- scalar/linear layer: no scalar structure enters this statement directly;
- owner layer: the primitive contradiction data are outside-domain witnesses
  `∃ u, u ∉ dom F` and `∃ x⋆, x⋆ ∉ dom (-F⋆)`; the source-facing proper-domain assumptions are
  recovered canonically via `Set.ne_univ_iff_exists_notMem`;
- topology layer: this result is order/pairing-based and has no ambient/intrinsic topology owner.
-/

-- Proof sketch for the proper-domain bridge theorem below: turn each proper-domain hypothesis into
-- an outside-domain witness via
-- `Set.ne_univ_iff_exists_notMem`. Lemma33.0.37 then gives
-- `⟪F u, x⋆⟫ᶠ = ⊥` and `⟪u, F⋆ x⋆⟫ᶜ = ⊤`, contradicting
-- `PairingEquationAt F u x⋆`.
/-- If `u ∉ dom F` and `x⋆ ∉ dom (-F⋆)`, then the Chapter 33 pairing equation fails at
`(u, x⋆)`. -/
theorem not_pairingEquationAt_of_not_mem_dom_and_not_mem_dom_neg_adjoint
    {u : U} {xStar : XStar}
    (hu : u ∉ dom F)
    (hxStar : xStar ∉ dom (-F⋆)) :
    ¬ PairingEquationAt F u xStar := sorry

-- Proof sketch: choose witnesses outside `dom F` and `dom (-F⋆)`, then apply the preceding
-- pointwise contradiction theorem.
/-- If `dom F` and `dom (-F⋆)` each omit a point, then the Chapter 33 pairing equation cannot
hold at every pair `(u, x⋆)`. -/
theorem not_forall_pairingEquationAt_of_exists_not_mem_dom_and_exists_not_mem_dom_neg_adjoint
    (hDom : ∃ u : U, u ∉ dom F)
    (hAdjDom : ∃ xStar : XStar, xStar ∉ dom (-F⋆)) :
    ¬ ∀ u : U, ∀ xStar : XStar, PairingEquationAt F u xStar := sorry

-- Proof sketch: rewrite the proper-domain hypotheses with
-- `Set.ne_univ_iff_exists_notMem`, then apply the witness-based helper theorem above.
/-- Corollary33.0.41: if `dom F` and `dom (-F⋆)` are both proper subsets, then `F` cannot
satisfy Definition33.0.31 at every pair `(u, x⋆)`. -/
theorem not_forall_pairingEquationAt_of_dom_ne_univ_and_dom_neg_adjoint_ne_univ
    (hDom : dom F ≠ Set.univ)
    (hAdjDom : dom (-F⋆) ≠ Set.univ) :
    ¬ ∀ u : U, ∀ xStar : XStar, PairingEquationAt F u xStar := sorry

end

end Bifunction
