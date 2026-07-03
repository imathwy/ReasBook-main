import StacksProject_2024.Chap15.Lemma_15_60_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Algebra.TensorProduct
open scoped TensorProduct DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

section

variable {R R' A B A' B' : Type u}
variable [CommRing R] [CommRing R'] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
variable [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra R' A'] [Algebra R' B']
variable [Algebra R A'] [Algebra A A'] [IsScalarTower R A A'] [IsScalarTower R R' A']
variable [Algebra R B'] [IsScalarTower R R' B']
variable [Module.Flat R R']

local notation "S" => TensorProduct R A B
local notation "T" => TensorProduct R' A' B'
local notation "ATensor" => TensorProduct R A R'
local notation "BTensor" => TensorProduct R R' B
local notation "DModA" => DerivedCategory (ModuleCat A)

private abbrev baseChangeProductMap
    (bMap : BTensor →ₐ[R'] B') : S →ₐ[R] T :=
  (productMap
      (((includeLeft : A' →ₐ[R'] T).restrictScalars R).comp (IsScalarTower.toAlgHom R A A'))
      (((includeRight : B' →ₐ[R'] T).restrictScalars R).comp
        ((bMap.restrictScalars R).comp (includeRight : B →ₐ[R] BTensor))))

private abbrev baseChangeLeftMap : ATensor →ₐ[R] A' :=
  productMap
    (IsScalarTower.toAlgHom R A A')
    (IsScalarTower.toAlgHom R R' A')

/- Domain-style sampling for Lemma 15.61.5:
- primary domain: derived base-change comparison in module-category derived categories and the
  induced maps on homology;
- sampled owner declarations of the same kind:
  `derivedTensorWithAlgebra`,
  `derivedTensorWithAlgebraHomologyComparison`,
  `derivedTensorWithAlgebraAdjunction`,
  `DerivedCategory.homologyFunctor`,
  `ModuleCat.extendScalars`,
- best owner abstraction: the source-facing owner is the canonical homology base-change map for
  the canonical `Algebra S T` coming from `productMap : A ⊗[R] B →ₐ[R] A' ⊗[R'] B'`, built from
  `derivedTensorWithAlgebraHomologyComparison`, with `productMap` supplying the textbook ring
  map and no parallel local tensor-map or local homology-comparison owner;
- primitive data: the comparison map `bMap : R' ⊗[R] B →ₐ[R'] B'`, the induced canonical ring
  map `baseChangeProductMap bMap : A ⊗[R] B →ₐ[R] A' ⊗[R'] B'`, together with `M : D(A)` and
  the degree `i : ℤ`;
- derived API: the source-facing flat-base-change statement on homology, expressed by saying that
  this canonical comparison morphism is an isomorphism.

Source/core/bridge triage:
- `source-facing`: the textbook flat-base-change isomorphism on homology modules over
  `A' ⊗[R'] B'`;
- `core/canonical`: `derivedTensorWithAlgebra`,
  `derivedTensorWithAlgebraHomologyComparison`, and `DerivedCategory.homologyFunctor`;
- `bridge/view`: the explicit tensor-product presentation via the canonical
  `Algebra.TensorProduct.productMap`; no parallel local owner theorem or local public tensor-map
  wrapper is kept. -/

-- Proof sketch: apply the flat-base-change argument of Lemma `15.61.3` to the canonical
-- ring map `A ⊗[R] B → A' ⊗[R'] B'` encoded by `baseChangeProductMap bMap`, then pass from the
-- derived-category
-- comparison to the canonical owner morphism `derivedTensorWithAlgebraHomologyComparison` for the
-- induced `S`-algebra structure on `T`.
/-- Lemma 15.61.5: under the flat base-change hypotheses of Lemma `15.61.3`, the canonical
homology comparison
`derivedTensorWithAlgebraHomologyComparison T (M ⊗[A]^L[S]) i`
for the explicit `baseChangeProductMap bMap`-induced `S`-algebra structure on
`T = A' ⊗[R'] B'` is an isomorphism. This is the owner-level formulation of the textbook
statement about `(M \otimes_A^{\mathbf L} A') \otimes_{R'}^{\mathbf L} B'`. -/
theorem derivedTensorWithAlgebraHomologyComparison_isIso_of_flat_baseChange
    (bMap : BTensor →ₐ[R'] B')
    (haFlat :
      letI : Algebra ATensor A' := baseChangeLeftMap.toAlgebra
      Module.Flat ATensor A')
    (hbFlat :
      letI : Algebra BTensor B' := bMap.toAlgebra
      Module.Flat BTensor B')
    (M : DModA) (i : ℤ) :
    letI : Algebra S T := (baseChangeProductMap bMap).toAlgebra
    IsIso (derivedTensorWithAlgebraHomologyComparison T (M ⊗[A]^L[S]) i) := sorry

end

end CategoryTheory
