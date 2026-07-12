import Mathlib.Tactic.Recall
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap18.Lemma_18_27_6

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CartesianClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The derived category `D(𝒪_X)` of sheaves of modules on a ringed space `X`. -/
abbrev RingedSpaceDerived (X : RingedSpace.{u}) :=
  DerivedCategory (Modules X)

/-
Domain-style sampling for 20.42.0.1:
- primary domain: closed monoidal structure on the derived category `D(𝒪_X)` attached to
  the canonical owner category `(RingedSpace.Modules X)`;
- sampled owner API:
  `MonoidalClosed.internalHomAdjunction₂.homEquiv`,
  `ihom.adjunction`,
  `MonoidalClosed.braidedHomEquiv_symm_apply`,
  `β_`;
- best owner abstraction: the chapter owner `MonoidalClosed.braidedHomEquiv` from
  `Lemma_18_27_6`, whose source tensor order `K ⊗ L` is obtained from
  `MonoidalClosed.internalHomAdjunction₂.homEquiv` by transport across the braiding `β_ K L`.

Source/core/bridge triage:
- `source-facing`: the textbook bijection
  `Hom(K, L ⟹ M) ≃ Hom(K ⊗ L, M)`;
- `core/canonical`: `MonoidalClosed.braidedHomEquiv`, equivalently
  `MonoidalClosed.internalHomAdjunction₂.homEquiv` transported across `β_ K L`;
- `bridge/view`: the generic evaluation formula
  `MonoidalClosed.braidedHomEquiv_symm_apply`.

Primitive data versus derived API:
- primitive data: only the owner category `(RingedSpace.Modules X)` and the monoidal closed structure and
  braiding on `DerivedCategory (RingedSpace.Modules X)`;
- derived API: the book-order Hom-bijection, obtained from the owner adjunction plus the braiding.

This numbered item therefore recalls the high-reuse generic owner
`MonoidalClosed.braidedHomEquiv` from `Lemma_18.27.6`, and keeps the ringed-space specialization
below only as thin source-facing recall/check surfaces instead of a second owner definition. -/

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

local notation "DModX" => RingedSpaceDerived X

/- Core recall: the Stacks Project bijection is the inverse of the tensor-internal-Hom adjunction
transported across the braiding. -/
recall CategoryTheory.MonoidalClosed.braidedHomEquiv

/- Specialized check for 20.42.0.1 on `D(𝒪_X)`. -/
#check
  (braidedHomEquiv : ∀ K L M : DModX, (K ⊗ L ⟶ M) ≃ (K ⟶ (L ⟹ M)))

/- Companion recall: the evaluation formula is the generic owner theorem
`MonoidalClosed.braidedHomEquiv_symm_apply`. -/
recall CategoryTheory.MonoidalClosed.braidedHomEquiv_symm_apply

/- Specialized check for the inverse evaluation formula on `D(𝒪_X)`. -/
#check
  (braidedHomEquiv_symm_apply :
    ∀ {K L M : DModX} (f : K ⟶ (L ⟹ M)),
      (braidedHomEquiv K L M).symm f = (β_ K L).hom ≫ uncurry f)

end

end AlgebraicGeometry.RingedSpace
