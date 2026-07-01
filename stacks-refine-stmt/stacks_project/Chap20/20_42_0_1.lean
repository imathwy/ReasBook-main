import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap20.Lemma_20_11_8

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for 20.42.0.1:
- primary domain: closed monoidal structure on the derived category `D(\mathcal O_X)` attached to
  the canonical owner category `(RingedSpace.Modules X)`;
- sampled owner API:
  `(RingedSpace.Modules X)`,
  `ihom.adjunction`,
  `MonoidalClosed.uncurry`,
  `Iso.homCongr`,
  `β_`;
- best owner abstraction: the core owner is the closed-monoidal adjunction `ihom.adjunction L` on
  `DerivedCategory (RingedSpace.Modules X)`, and the Stacks Project's factor order `K ⊗ L` is obtained by
  transporting that owner along the braiding `β_ K L`.

Source/core/bridge triage:
- `source-facing`: the textbook bijection
  `Hom(K, R\mathcal H\!\mathit{om}(L, M)) ≃ Hom(K ⊗^{\mathbf L} L, M)`;
- `core/canonical`: `(ihom.adjunction L).homEquiv K M`;
- `bridge/view`: transport across `(β_ K L).symm.homCongr (Iso.refl M)` from `L ⊗ K` to `K ⊗ L`.

Primitive data versus derived API:
- primitive data: only the owner category `(RingedSpace.Modules X)` and the monoidal closed structure and
  braiding on `DerivedCategory (RingedSpace.Modules X)`;
- derived API: the book-order Hom-bijection, obtained from the owner adjunction plus the braiding.

This numbered item is therefore recall-only: it should not keep a parallel ringed-space-specific
owner definition. -/

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]
variable [BraidedCategory (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules X))]

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

/- Core recall: the owner equivalence is `ihom.adjunction`; the Stacks Project's factor order
`K ⊗ L` is its transport across the braiding `β_ K L`. -/
recall ihom.adjunction

/- Specialized check for 20.42.0.1. -/
#check
  fun (K L M : DModX) ↦
    ((((ihom.adjunction L).homEquiv K M).symm.trans
        ((β_ K L).symm.homCongr (Iso.refl M))) :
      (K ⟶ (ihom L).obj M) ≃ (K ⊗ L ⟶ M))

-- Proof sketch: the transported equivalence applies the braiding-conjugation equivalence to
-- `MonoidalClosed.uncurry f`, and `Iso.homCongr` specializes here to left composition by
-- `(β_ K L).hom`.
/-- Applying the textbook-order tensor-internal-Hom adjunction sends a morphism
`K ⟶ R\mathcal H\!\mathit{om}(L, M)` to the corresponding morphism
`K \otimes_{\mathcal O_X}^{\mathbf L} L ⟶ M`. -/
theorem ringedSpaceDerivedInternalHomAdjunction_apply
    {K L M : DModX}
    (f : K ⟶ (ihom L).obj M) :
    ((((ihom.adjunction L).homEquiv K M).symm.trans
        ((β_ K L).symm.homCongr (Iso.refl M))) f) =
      (β_ K L).hom ≫ MonoidalClosed.uncurry f :=
  by
    change (β_ K L).hom ≫ MonoidalClosed.uncurry f ≫ (Iso.refl M).hom =
        (β_ K L).hom ≫ MonoidalClosed.uncurry f
    simp

end

end AlgebraicGeometry.RingedSpace
