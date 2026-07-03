import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap15.Lemma_15_74_4

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
  `CategoryTheory.MonoidalClosed.derivedTensorAdj`;
- best owner abstraction:
  `core/canonical`: an ambient instance `[MonoidalClosed DMod]`, with the canonical internal-Hom
  object `L ⟶[DMod] M`;
  `source-facing`: the derived tensor notation `K ⊗[R]^L L` and the textbook bijection
  `Hom(K, R\mathrm{Hom}_R(L, M)) ≃ Hom(K \otimes_R^{\mathbf L} L, M)`;
  `bridge/view`: the transported right-tensor adjunction `inferInstance.derivedTensorAdj L`.
- primitive data: only the ambient monoidal-closed instance on `D(R)`;
- derived API: the canonical internal-Hom object `L ⟶[DMod] M`, the notation `K ⊗[R]^L L`, and
  the resulting hom-set equivalence.

Source/core/bridge triage:
- `source-facing`: the tensor/internal-Hom bijection
  `Hom(K, R\mathrm{Hom}_R(L, M)) ≃ Hom(K \otimes_R^{\mathbf L} L, M)`;
- `core/canonical`: the ambient internal-Hom owner `L ⟶[DMod] -`;
- `bridge/view`: this file merely recalls the specialized right-tensor adjunction
  `inferInstance.derivedTensorAdj L`.

This file is now a bridge/view layer: it specializes the canonical owner from
`Lemma_15_74_4.lean` to `D(R)` and recalls the adjunction equivalence without reintroducing a
second public owner or exposing an auxiliary chosen `MonoidalClosed` package as a source-facing
parameter. -/

open scoped DerivedTensorProduct

recall CategoryTheory.ihom
recall CategoryTheory.MonoidalClosed.derivedTensorAdj

variable (K L M : DMod)

/-
15.74.0.1: with an ambient monoidal-closed structure on `D(R)`, morphisms
`K ⟶ (L ⟶[DMod] M)` are canonically equivalent to morphisms
`K ⊗[R]^L L ⟶ M`. This is exactly the inverse of the adjunction hom-set
equivalence attached to the canonical right-tensor adjunction on `D(R)`.
-/
set_option linter.hashCommand false in
#check
  fun [MonoidalClosed DMod] ↦
    let H : MonoidalClosed DMod := inferInstance
    (((H.derivedTensorAdj L).homEquiv K M).symm :
      (K ⟶ (L ⟶[DMod] M)) ≃ (K ⊗[R]^L L ⟶ M))

end

end CategoryTheory
