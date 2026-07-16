import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap15.Lemma_15_59_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

attribute [local instance] HasDerivedCategory.standard

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for 15.74.0.1:
- primary domain: the closed monoidal structure on the derived category `D(R)`;
- sampled owner declarations:
  `CategoryTheory.ihom`,
  `CategoryTheory.ihom.adjunction`,
  `CategoryTheory.derivedTensorProduct`,
  `CategoryTheory.tensoringRightIsoDerivedTensorProduct`;
- best owner abstraction:
  `core/canonical`: an ambient instance `[MonoidalClosed DMod]`, with the canonical internal-Hom
  object `L ⟶[DMod] M`;
  `source-facing`: the derived tensor notation `K ⊗[R]^L L` and the textbook bijection
  `Hom(K, R\mathrm{Hom}_R(L, M)) ≃ Hom(K \otimes_R^{\mathbf L} L, M)`;
  `bridge/view`: the tensor-right/derived-tensor comparison
  `tensoringRightIsoDerivedTensorProduct L`.
- primitive data: only the ambient monoidal-closed instance on `D(R)`;
- derived API: the canonical internal-Hom object `L ⟶[DMod] M`, the notation `K ⊗[R]^L L`, and
  the resulting hom-set equivalence.

Source/core/bridge triage:
- `source-facing`: the tensor/internal-Hom bijection
  `Hom(K, R\mathrm{Hom}_R(L, M)) ≃ Hom(K \otimes_R^{\mathbf L} L, M)`;
- `core/canonical`: the ambient internal-Hom owner `L ⟶[DMod] -`;
- `bridge/view`: this file builds the specialized right-tensor adjunction by transporting
  `ihom.adjunction L` across the braiding and `tensoringRightIsoDerivedTensorProduct L`.

This file is now a bridge/view layer: it specializes the canonical closed-monoidal owner on
`D(R)` and records the adjunction equivalence without reintroducing a second public owner or
exposing an auxiliary chosen `MonoidalClosed` package as a source-facing parameter. -/

open scoped DerivedTensorProduct

recall CategoryTheory.ihom
variable (K L M : DMod)

/-- Helper for 15.74.0.1: the target-oriented Hom equivalence obtained by reversing the
transported derived tensor adjunction. -/
noncomputable abbrev derivedTensorAdj_homEquiv_symm
    [MonoidalClosed DMod] :
    (K ⟶ (L ⟶[DMod] M)) ≃ (K ⊗[R]^L L ⟶ M) :=
  -- Reverse the right-tensor adjunction after transporting tensor-righting through the standard
  -- derived-tensor comparison.
  (((((ihom.adjunction L).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight L)).ofNatIsoLeft
      (tensoringRightIsoDerivedTensorProduct (R := R) L)).homEquiv K M).symm :
    (K ⟶ (L ⟶[DMod] M)) ≃ (K ⊗[R]^L L ⟶ M))

/-- 15.74.0.1: in the derived category `D(R)`, the canonical tensor/internal-Hom adjunction gives
`Hom_{D(R)}(K, R\mathrm{Hom}_R(L, M)) ≃ Hom_{D(R)}(K \otimes_R^{\mathbf L} L, M)`. -/
noncomputable abbrev derived_tensor_internal_hom_hom_equiv
    [MonoidalClosed DMod] :
    (K ⟶ (L ⟶[DMod] M)) ≃ (K ⊗[R]^L L ⟶ M) :=
  -- This source-facing bijection is the reversed transported right-tensor adjunction above.
  derivedTensorAdj_homEquiv_symm (R := R) K L M

end

end CategoryTheory
