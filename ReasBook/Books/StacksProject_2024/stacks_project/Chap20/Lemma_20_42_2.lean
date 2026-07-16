import StacksProject_2024.stacks_project.Chap20.«20_42_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CartesianClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.42.2:
- primary domain: braided closed monoidal structure on `D(𝒪_X)`;
- inspected owner declarations:
  `MonoidalClosed.braidedHomEquiv`,
  `CategoryTheory.MonoidalClosed.internalHomTensorIso`,
  `MonoidalClosed.braidedHomEquiv_symm_apply`,
  the standard internal-Hom notation `K ⟹ L`;
- best owner abstraction: the chapter owner
  `CategoryTheory.MonoidalClosed.internalHomTensorIso`, whose tensor-side transpose is governed by
  `MonoidalClosed.braidedHomEquiv`;
- primitive data: the ambient braided monoidal closed structure on `RingedSpaceDerived X` and the
  objects `K`, `L`, `M`;
- derived API: the source-facing objectwise isomorphism
  `K ⟹ (L ⟹ M) ≅ (K ⊗ L) ⟹ M`, i.e.
  `RHom(K, RHom(L, M)) ≅ RHom(K ⊗^L L, M)`.

Source/core/bridge triage:
- `source-facing`: the textbook objectwise isomorphism of Lemma `20.42.2`;
- `core/canonical`: `CategoryTheory.MonoidalClosed.internalHomTensorIso`,
  `MonoidalClosed.braidedHomEquiv`, and the theorem-surface notation `K ⟹ L`;
- `bridge/view`: the ringed-space specialization of that canonical currying isomorphism.
-/

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

local notation "DModX" => RingedSpaceDerived X

/- Lemma 20.42.2: for a ringed space `(X, 𝒪_X)` and objects
`K`, `L`, `M ∈ D(𝒪_X)`, there is a canonical isomorphism
`K ⟹ (L ⟹ M) ≅ (K ⊗ L) ⟹ M`,
equivalently
`RHom(K, RHom(L, M)) ≅ RHom(K ⊗^L_{𝒪_X} L, M)`.
This is the generic owner theorem
`CategoryTheory.MonoidalClosed.internalHomTensorIso`, specialized to
`RingedSpaceDerived X`. -/
recall CategoryTheory.MonoidalClosed.internalHomTensorIso

/-- Applying the source-order tensor-internal-Hom owner `MonoidalClosed.braidedHomEquiv` to the
comparison of Lemma `20.42.2` identifies its underlying morphism with the corresponding owner-side
uncurrying composite. -/
theorem ringedSpaceDerivedInternalHomTensorIso_spec
    (K L M : DModX) :
    (braidedHomEquiv (K ⟹ (L ⟹ M)) (K ⊗ L) M).symm (internalHomTensorIso K L M).hom =
      (β_ (K ⟹ (L ⟹ M)) (K ⊗ L)).hom ≫ uncurry (internalHomTensorIso K L M).hom := by
  simpa using
    MonoidalClosed.braidedHomEquiv_symm_apply (internalHomTensorIso K L M).hom

end

end AlgebraicGeometry.RingedSpace
