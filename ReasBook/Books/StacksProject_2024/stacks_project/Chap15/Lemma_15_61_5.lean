import StacksProject_2024.Chap15.Lemma_15_60_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Algebra.TensorProduct ComplexShape
open scoped TensorProduct DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

/-- Helper for Lemma 15.61.5: package the standard homotopy-to-derived functor so the local
flat scalar-extension API does not depend on a later file's abbreviation. -/
private abbrev mapHomotopyCategoryToDerived
    {𝒜 ℬ : Type u} [Category 𝒜] [Category ℬ]
    [Abelian 𝒜] [Abelian ℬ]
    [HasDerivedCategory 𝒜] [HasDerivedCategory ℬ]
    (F : 𝒜 ⥤ ℬ) [F.Additive] :
    HomotopyCategory 𝒜 (up ℤ) ⥤ DerivedCategory ℬ :=
  F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

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
local notation "STensor" => TensorProduct R' A' BTensor
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

section flat_scalar_extension

variable {U V : Type u}
variable [CommRing U] [CommRing V] [Algebra U V]

local notation "DModU" => DerivedCategory (ModuleCat U)
local notation "DModV" => DerivedCategory (ModuleCat V)
local notation "KModU" => HomotopyCategory (ModuleCat U) (up ℤ)
local notation "HU" => DerivedCategory.homologyFunctor (ModuleCat U)
local notation "HV" => DerivedCategory.homologyFunctor (ModuleCat V)
local notation "QhU" => (DerivedCategory.Qh : KModU ⥤ DModU)
local notation "QisU" => HomotopyCategory.quasiIso (ModuleCat U) (up ℤ)

/-- Helper for Lemma 15.61.5: scalar extension is additive on module categories. -/
local instance extendScalars_additive :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap U V)).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
    (algebraMap U V)).left_adjoint_additive

/-- Helper for Lemma 15.61.5: flat scalar extension preserves finite limits. -/
local instance extendScalars_preservesFiniteLimits [Module.Flat U V] :
    CategoryTheory.Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap U V)) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr (show Module.Flat U V from inferInstance))

/-- Helper for Lemma 15.61.5: exact scalar extension is already the left derived functor of the
homotopy-level scalar-extension functor. -/
private theorem extend_scalars_mapDerivedCategoryh_isLeftDerivedFunctor
    [Module.Flat U V] :
    ((ModuleCat.extendScalars (algebraMap U V)).mapDerivedCategory).IsLeftDerivedFunctor
      ((ModuleCat.extendScalars (algebraMap U V)).mapDerivedCategoryFactorsh.hom)
      QisU := by
  let F : ModuleCat U ⥤ ModuleCat V := ModuleCat.extendScalars (algebraMap U V)
  -- Flat scalar extension preserves quasi-isomorphisms, so its exact derived functor is already
  -- the left-derived owner.
  simpa [F] using
    (Functor.isLeftDerivedFunctor_of_inverts
      QisU
      F.mapDerivedCategory
      F.mapDerivedCategoryFactorsh)

/-- Helper for Lemma 15.61.5: under flatness, exact scalar extension on modules agrees with the
owner functor `derivedTensorWithAlgebra` on the derived category. -/
private noncomputable def flat_extend_scalars_mapDerivedCategory_iso
    [Module.Flat U V] :
    (ModuleCat.extendScalars (algebraMap U V)).mapDerivedCategory ≅
      derivedTensorWithAlgebra (algebraMap U V) := by
  let F₀ : ModuleCat U ⥤ ModuleCat V := ModuleCat.extendScalars (algebraMap U V)
  let F : KModU ⥤ DModV := mapHomotopyCategoryToDerived F₀
  letI : F.HasLeftDerivedFunctor QisU := by
    simpa [F, F₀] using
      (extendScalarsToDerived_hasLeftDerivedFunctor
        (R := U) (A := V) (algebraMap U V))
  letI :
      F₀.mapDerivedCategory.IsLeftDerivedFunctor
        F₀.mapDerivedCategoryFactorsh.hom
        QisU := by
    simpa [F₀] using
      (extend_scalars_mapDerivedCategoryh_isLeftDerivedFunctor (U := U) (V := V))
  -- Compare the exact derived functor of flat extension with the total-left-derived owner
  -- `derivedTensorWithAlgebra`.
  simpa [derivedTensorWithAlgebra, F, F₀] using
    (Functor.leftDerivedNatIso
      F₀.mapDerivedCategory
      (F.totalLeftDerived QhU QisU)
      F₀.mapDerivedCategoryFactorsh.hom
      (Functor.totalLeftDerivedCounit F QhU QisU)
      QisU
      (Iso.refl F))

/-- Helper for Lemma 15.61.5: exact flat scalar extension commutes with taking homology. -/
private noncomputable def flat_extend_scalars_homology_iso
    [Module.Flat U V]
    (L : DModU) (i : ℤ) :
    (ModuleCat.extendScalars (algebraMap U V)).obj ((HU i).obj L) ≅
      (HV i).obj (((ModuleCat.extendScalars (algebraMap U V)).mapDerivedCategory).obj L) := by
  let K := DerivedCategory.Q.objPreimage L
  let FK :=
    ((ModuleCat.extendScalars (algebraMap U V)).mapHomologicalComplex (up ℤ)).obj K
  let eU : (HU i).obj L ≅ K.homology i :=
    ((HU i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app K
  let e :
      (HV i).obj (((ModuleCat.extendScalars (algebraMap U V)).mapDerivedCategory).obj L) ≅
        (ModuleCat.extendScalars (algebraMap U V)).obj ((HU i).obj L) :=
    (HV i).mapIso
        (((((ModuleCat.extendScalars (algebraMap U V)).mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm) ≪≫
          ((ModuleCat.extendScalars (algebraMap U V)).mapDerivedCategoryFactors.app K)) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat V) i).app FK ≪≫
      (K.sc i).mapHomologyIso (ModuleCat.extendScalars (algebraMap U V)) ≪≫
        (ModuleCat.extendScalars (algebraMap U V)).mapIso eU.symm
  -- Pass to a chosen complex representative, commute homology past exact scalar extension, and
  -- then invert the comparison to obtain the source-facing orientation.
  exact e.symm

/-- Helper for Lemma 15.61.5: flat scalar extension identifies the scalar extension of homology
with the homology of the derived scalar extension. -/
private noncomputable def flat_derived_tensor_homology_iso
    [Module.Flat U V]
    (K : DModU) (i : ℤ) :
    (ModuleCat.extendScalars (algebraMap U V)).obj ((HU i).obj K) ≅
      (HV i).obj ((derivedTensorWithAlgebra (algebraMap U V)).obj K) :=
  -- First commute exact flat scalar extension with homology, then rewrite exact extension as the
  -- owner-level derived scalar extension.
  flat_extend_scalars_homology_iso (U := U) (V := V) K i ≪≫
    (HV i).mapIso ((flat_extend_scalars_mapDerivedCategory_iso (U := U) (V := V)).app K)

end flat_scalar_extension

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

/-- Helper for Lemma 15.61.5: the first normalization step replaces
`A ⊗[R] B` by `A' ⊗[R'] (R' ⊗[R] B)` using the `A`-base change on the left tensor factor and the
canonical `B → R' ⊗[R] B` map on the right tensor factor. -/
private abbrev normalizedBaseChangeLeft :
    A →ₐ[R] STensor :=
  ((includeLeft : A' →ₐ[R'] STensor).restrictScalars R).comp
    (IsScalarTower.toAlgHom R A A')

/-- Helper for Lemma 15.61.5: the right tensor factor of the normalized source is obtained by the
canonical base-change map `B → R' ⊗[R] B`. -/
private abbrev normalizedBaseChangeRight :
    B →ₐ[R] STensor :=
  ((includeRight : BTensor →ₐ[R'] STensor).restrictScalars R).comp
    (includeRight : B →ₐ[R] BTensor)

/-- Helper for Lemma 15.61.5: this is the source-faithful intermediate ring map
`A ⊗[R] B → A' ⊗[R'] (R' ⊗[R] B)` used to separate the `A`-base change from the final
`R' ⊗[R] B → B'` flat step. -/
private abbrev normalizedBaseChangeMap :
    S →ₐ[R] STensor :=
  @Algebra.TensorProduct.productMap R STensor A B _ _ _ _ _ _ _
    normalizedBaseChangeLeft normalizedBaseChangeRight

/-- Helper for Lemma 15.61.5: after normalizing the source to
`A' ⊗[R'] (R' ⊗[R] B)`, the last step to `A' ⊗[R'] B'` is induced by `bMap` on the right tensor
factor. -/
private abbrev normalizedTensorMap
    (bMap : BTensor →ₐ[R'] B') :
    STensor →ₐ[R'] T :=
  @Algebra.TensorProduct.productMap R' T A' BTensor _ _ _ _ _ _ _
    (includeLeft : A' →ₐ[R'] T)
    ((includeRight : B' →ₐ[R'] T).comp bMap)

/-- Helper for Lemma 15.61.5: the direct textbook map
`A ⊗[R] B → A' ⊗[R'] B'` factors through the normalized intermediate tensor ring. -/
private theorem base_change_productMap_factor_eq
    (bMap : BTensor →ₐ[R'] B') :
    ((normalizedTensorMap bMap : STensor →ₐ[R'] T).toRingHom.comp
        (normalizedBaseChangeMap : S →ₐ[R] STensor).toRingHom) =
      (baseChangeProductMap bMap : S →ₐ[R] T).toRingHom := by
  -- Both maps are determined by their values on pure tensors, where the factorization simply
  -- inserts the intermediate tensor factor and then applies `bMap` on the right.
  ext x
  · -- On the left tensor factor, both routes are just the canonical `A → A' → T` map.
    simp [RingHom.comp_apply, normalizedBaseChangeMap, normalizedBaseChangeLeft,
      normalizedBaseChangeRight, normalizedTensorMap, baseChangeProductMap,
      Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply]
  · -- On the right tensor factor, the factorization only inserts the intermediate `BTensor`
    -- stage before applying `bMap`.
    simp [RingHom.comp_apply, normalizedBaseChangeMap, normalizedBaseChangeLeft,
      normalizedBaseChangeRight, normalizedTensorMap, baseChangeProductMap,
      Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply]

/-- Helper for Lemma 15.61.5: composing `A → A'` with the left inclusion into the normalized
tensor ring gives the direct `A → A' ⊗[R'] (R' ⊗[R] B)` map. -/
private theorem normalizedBaseChangeLeft_comp_eq :
    ((includeLeft : A' →ₐ[R'] STensor).toRingHom.comp (algebraMap A A')) =
      normalizedBaseChangeLeft.toRingHom := by
  -- On the left tensor factor, the normalized source remembers exactly the `A → A'` base change.
  ext a
  simp [normalizedBaseChangeLeft]

/-- Helper for Lemma 15.61.5: the normalized source ring map restricts on `A` to the direct
base-change map into the intermediate tensor ring. -/
private theorem normalizedBaseChangeMap_left_comp_eq :
    (normalizedBaseChangeMap : S →ₐ[R] STensor).toRingHom.comp (algebraMap A S) =
      normalizedBaseChangeLeft.toRingHom := by
  -- On the left tensor factor, the normalized source map is exactly the direct `A → STensor`
  -- map used by the source proof.
  ext a
  simp [normalizedBaseChangeMap, normalizedBaseChangeLeft, normalizedBaseChangeRight,
    Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.one_def]

/-- Helper for Lemma 15.61.5: the normalized source ring map restricts on `B` to the direct
base-change map into the intermediate tensor ring. -/
private theorem normalizedBaseChangeMap_right_comp_eq :
    (normalizedBaseChangeMap : S →ₐ[R] STensor).toRingHom.comp (algebraMap B S) =
      normalizedBaseChangeRight.toRingHom := by
  -- On the right tensor factor, the normalized source map is exactly the canonical
  -- `B → R' ⊗[R] B → STensor` map from the source proof.
  ext b
  change
    (normalizedBaseChangeMap : S →ₐ[R] STensor) ((1 : A) ⊗ₜ[R] b) =
      normalizedBaseChangeRight b
  simp [normalizedBaseChangeMap, normalizedBaseChangeLeft, normalizedBaseChangeRight,
    Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.includeRight_apply]

/-- Helper for Lemma 15.61.5: the left tensor factor is unchanged by the last normalized map
`A' ⊗[R'] (R' ⊗[R] B) → A' ⊗[R'] B'`. -/
private theorem normalizedTensorMap_left_comp_eq
    (bMap : BTensor →ₐ[R'] B') :
    (normalizedTensorMap bMap).toRingHom.comp
        (includeLeft : A' →ₐ[R'] STensor).toRingHom =
      (includeLeft : A' →ₐ[R'] T).toRingHom := by
  -- The final flat step acts only on the right tensor factor, so the left inclusion is fixed.
  ext a
  simp [normalizedTensorMap, Algebra.TensorProduct.productMap_apply_tmul,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]

/-- Helper for Lemma 15.61.5: the right tensor factor of the last normalized map is exactly
`bMap`, followed by the canonical inclusion into `A' ⊗[R'] B'`. -/
private theorem normalizedTensorMap_right_comp_eq
    (bMap : BTensor →ₐ[R'] B') :
    (normalizedTensorMap bMap).toRingHom.comp
        (includeRight : BTensor →ₐ[R'] STensor).toRingHom =
      ((includeRight : B' →ₐ[R'] T).toRingHom.comp bMap.toRingHom) := by
  -- The final normalized step changes only the right tensor factor.
  ext x
  · simp [normalizedTensorMap, RingHom.comp_apply, Algebra.TensorProduct.productMap_apply_tmul,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]
  · change
      (normalizedTensorMap bMap) ((1 : A') ⊗ₜ[R'] ((1 : R') ⊗ₜ[R] x)) =
        (includeRight : B' →ₐ[R'] T) (bMap ((1 : R') ⊗ₜ[R] x))
    simp [normalizedTensorMap, Algebra.TensorProduct.productMap_apply_tmul,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]

/-- Helper for Lemma 15.61.5: the last normalized map is the tensor-product map that is the
identity on the `A'` factor and `bMap` on the `R' ⊗[R] B` factor. -/
private theorem normalizedTensorMap_eq_tensorProductMap
    (bMap : BTensor →ₐ[R'] B') :
    normalizedTensorMap bMap =
      Algebra.TensorProduct.map (AlgHom.id R' A') bMap := by
  -- Compare the two algebra maps on the left and right tensor generators separately.
  apply Algebra.TensorProduct.ext
  · ext a
    simp [normalizedTensorMap, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply]
  · ext x
    simp [normalizedTensorMap, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply]

/-- Helper for Lemma 15.61.5: the final normalized map is flat because it is the tensor-product
base change of the flat map `bMap` along the identity on `A'`. -/
private theorem normalizedTensorMap_flat
    (bMap : BTensor →ₐ[R'] B')
    (hbFlat :
      letI : Algebra BTensor B' := bMap.toAlgebra
      Module.Flat BTensor B') :
    letI : Algebra STensor T := (normalizedTensorMap bMap).toAlgebra
    Module.Flat STensor T := by
  letI : Algebra BTensor B' := bMap.toAlgebra
  letI : Algebra STensor T := (normalizedTensorMap bMap).toAlgebra
  have hflatId : (AlgHom.id R' A' : A' →ₐ[R'] A').Flat := by
    simpa using RingHom.Flat.id A'
  have hflatBMap : bMap.toRingHom.Flat := by
    -- Convert the given module-flatness hypothesis on `bMap` into flatness of the corresponding
    -- algebra map.
    simpa [RingHom.algebraMap_toAlgebra] using
      (RingHom.flat_algebraMap_iff.mpr hbFlat)
  have hmapFlat :
      (Algebra.TensorProduct.map (AlgHom.id R' A') bMap).Flat :=
    RingHom.Flat.tensorProductMap hflatId hflatBMap
  have hnormalized :
      ((normalizedTensorMap bMap : STensor →ₐ[R'] T).toRingHom).Flat := by
    -- Identify the normalized target map with the tensor-product map that is the identity on `A'`
    -- and `bMap` on the right tensor factor.
    rw [normalizedTensorMap_eq_tensorProductMap bMap]
    exact hmapFlat
  have halg :
      (algebraMap STensor T).Flat := by
    -- Reinterpret the transported ring-hom flatness as flatness of the canonical algebra map.
    simpa [RingHom.algebraMap_toAlgebra] using hnormalized
  exact RingHom.flat_algebraMap_iff.mp halg

/-- Helper for Lemma 15.61.5: the normalized intermediate ring
`STensor = A' ⊗[R'] (R' ⊗[R] B)` is canonically the `A`-base change `A' ⊗[A] S`. -/
private noncomputable def normalizedIntermediateAlgEquiv :
    A' ⊗[A] S ≃ₐ[A'] STensor :=
  (Algebra.TensorProduct.cancelBaseChange R A A' A' B).trans
    (Algebra.TensorProduct.cancelBaseChange R R' A' A' B).symm

/-- Helper for Lemma 15.61.5: under the canonical identification
`A' ⊗[A] S ≃ STensor`, the left `A'`-tensor factor is the usual left inclusion into `STensor`. -/
private theorem normalizedIntermediateAlgEquiv_includeLeft
    (a' : A') :
    normalizedIntermediateAlgEquiv (R := R) (R' := R') (A := A) (B := B) (A' := A')
        ((includeLeft : A' →ₐ[A] A' ⊗[A] S) a') =
      (includeLeft : A' →ₐ[R'] STensor) a' := by
  -- Push both sides through the final cancellation equivalence so the comparison becomes a pure
  -- tensor computation in `A' ⊗[R] B`.
  apply (Algebra.TensorProduct.cancelBaseChange R R' A' A' B).injective
  simp [normalizedIntermediateAlgEquiv, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.one_def, Algebra.TensorProduct.cancelBaseChange_tmul]

/-- Helper for Lemma 15.61.5: transporting `normalizedBaseChangeLeft` across
`A' ⊗[A] S ≃ STensor` recovers the canonical left-factor map into the ordinary `A`-base change. -/
private theorem normalizedIntermediateAlgEquiv_symm_comp_normalizedBaseChangeLeft :
    normalizedIntermediateAlgEquiv
        (R := R) (R' := R') (A := A) (B := B) (A' := A').symm.toRingHom.comp
        normalizedBaseChangeLeft.toRingHom =
      ((includeLeft : A' →ₐ[A] A' ⊗[A] S).toRingHom.comp (algebraMap A A')) := by
  -- Apply the forward equivalence and use the left-factor computation above.
  ext a
  -- Apply the inverse equivalence to the already computed forward image of the left factor.
  simpa [normalizedBaseChangeLeft] using
    (congrArg
      (normalizedIntermediateAlgEquiv
        (R := R) (R' := R') (A := A) (B := B) (A' := A')).symm
      (normalizedIntermediateAlgEquiv_includeLeft
        (R := R) (R' := R') (A := A) (B := B) (A' := A')
        (a' := algebraMap A A' a))).symm

/-- Helper for Lemma 15.61.5: under the canonical identification
`A' ⊗[A] S ≃ STensor`, the right `B`-factor map becomes the normalized right-factor map
`B → STensor`. -/
private theorem normalizedIntermediateAlgEquiv_includeRight
    (b : B) :
    normalizedIntermediateAlgEquiv
        (R := R) (R' := R') (A := A) (B := B) (A' := A')
        ((includeRight : S →ₐ[A] A' ⊗[A] S) ((includeRight : B →ₐ[R] S) b)) =
      normalizedBaseChangeRight b := by
  -- Again pass to `A' ⊗[R] B`, where both maps become the same pure tensor `1 ⊗ b`.
  apply (Algebra.TensorProduct.cancelBaseChange R R' A' A' B).injective
  simp [normalizedIntermediateAlgEquiv, normalizedBaseChangeRight,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.one_def,
    Algebra.TensorProduct.cancelBaseChange_tmul]

/-- Helper for Lemma 15.61.5: transporting `normalizedBaseChangeRight` across
`A' ⊗[A] S ≃ STensor` recovers the canonical right-factor map into the ordinary `A`-base change. -/
private theorem normalizedIntermediateAlgEquiv_symm_comp_normalizedBaseChangeRight :
    normalizedIntermediateAlgEquiv
        (R := R) (R' := R') (A := A) (B := B) (A' := A').symm.toRingHom.comp
        normalizedBaseChangeRight.toRingHom =
      ((includeRight : S →ₐ[A] A' ⊗[A] S).toRingHom.comp (algebraMap B S)) := by
  -- Apply the inverse equivalence to the forward computation on the `B` factor.
  ext b
  simpa using
    (congrArg
      (normalizedIntermediateAlgEquiv
        (R := R) (R' := R') (A := A) (B := B) (A' := A')).symm
      (normalizedIntermediateAlgEquiv_includeRight
        (R := R) (R' := R') (A := A) (B := B) (A' := A')
        (b := b))).symm

/-- Helper for Lemma 15.61.5: in the ordinary `A`-base change, the left tensor factor is the
canonical map `A → A'`. -/
private theorem algebraMap_to_normalizedIntermediate_left_comp :
    (algebraMap S (A' ⊗[A] S)).comp (algebraMap A S) =
      ((includeLeft : A' →ₐ[A] A' ⊗[A] S).toRingHom.comp (algebraMap A A')) := by
  -- Compare the two maps on `A`: one route lands in the right factor, and the other in the left
  -- factor, so the tensor balancing relation identifies them.
  ext a
  simpa [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.smul_def] using
    (TensorProduct.smul_tmul (R := A) (r := a) (m := (1 : A')) (n := (1 : S))).symm

/-- Helper for Lemma 15.61.5: in the ordinary `A`-base change, the right tensor factor is the
canonical inclusion of `S`. -/
private theorem algebraMap_to_normalizedIntermediate_right_comp :
    (algebraMap S (A' ⊗[A] S)).comp (algebraMap B S) =
      ((includeRight : S →ₐ[A] A' ⊗[A] S).toRingHom.comp (algebraMap B S)) := by
  -- The `S`-algebra structure on `A' ⊗[A] S` is the right tensor-factor inclusion.
  rfl

/-- Helper for Lemma 15.61.5: transporting the normalized source map across
`A' ⊗[A] S ≃ STensor` identifies it with the canonical algebra map
`S → A' ⊗[A] S`. -/
private theorem normalizedIntermediateAlgEquiv_symm_comp_normalizedBaseChangeMap :
    normalizedIntermediateAlgEquiv
        (R := R) (R' := R') (A := A) (B := B) (A' := A').symm.toRingHom.comp
        normalizedBaseChangeMap.toRingHom =
      algebraMap S (A' ⊗[A] S) := by
  -- Compare the two ring maps on the `A` and `B` tensor generators separately.
  ext x
  · change
      (((normalizedIntermediateAlgEquiv
          (R := R) (R' := R') (A := A) (B := B) (A' := A')).symm.toRingHom.comp
          normalizedBaseChangeMap.toRingHom).comp (algebraMap A S)) x =
        ((algebraMap S (A' ⊗[A] S)).comp (algebraMap A S)) x
    rw [RingHom.comp_assoc]
    rw [normalizedBaseChangeMap_left_comp_eq]
    rw [normalizedIntermediateAlgEquiv_symm_comp_normalizedBaseChangeLeft]
    rw [algebraMap_to_normalizedIntermediate_left_comp]
  · change
      (((normalizedIntermediateAlgEquiv
          (R := R) (R' := R') (A := A) (B := B) (A' := A')).symm.toRingHom.comp
          normalizedBaseChangeMap.toRingHom).comp (algebraMap B S)) x =
        ((algebraMap S (A' ⊗[A] S)).comp (algebraMap B S)) x
    rw [RingHom.comp_assoc]
    rw [normalizedBaseChangeMap_right_comp_eq]
    rw [normalizedIntermediateAlgEquiv_symm_comp_normalizedBaseChangeRight]
    rw [algebraMap_to_normalizedIntermediate_right_comp]

/-- Helper for Lemma 15.61.5: the left base-change map
`A ⊗[R] R' → A'` restricts on `A` to the standard algebra map `A → A'`. -/
private theorem baseChangeLeftMap_comp_algebraMapA :
    baseChangeLeftMap.toRingHom.comp (algebraMap A ATensor) =
      algebraMap A A' := by
  -- Evaluate both maps on the `A`-generator `a ⊗ 1` of `A ⊗[R] R'`.
  ext a
  change baseChangeLeftMap ((a : A) ⊗ₜ[R] (1 : R')) = algebraMap A A' a
  simp [baseChangeLeftMap, Algebra.TensorProduct.productMap_apply_tmul]

/-- Helper for Lemma 15.61.5: if `A → B` is flat, then the right tensor factor
`C → B ⊗[A] C` is flat. -/
private theorem tensor_right_flat_of_flat_left
    {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (hAB_flat : (algebraMap A B).Flat) :
    Module.Flat C (B ⊗[A] C) := by
  letI : Module.Flat A B := RingHom.flat_algebraMap_iff.mp hAB_flat
  have hbase : Module.Flat C (C ⊗[A] B) := by
    -- Base change the flat `A`-module `B` along `A → C`.
    simpa using (Module.Flat.baseChange A C B)
  letI : Module.Flat C (C ⊗[A] B) := hbase
  let e : B ⊗[A] C ≃ₗ[C] C ⊗[A] B :=
    (Algebra.TensorProduct.commRight A C B).symm.toLinearEquiv
  -- Commute the tensor factors to recover the source-facing tensor order `B ⊗[A] C`.
  exact Module.Flat.of_linearEquiv e

/-- Helper for Lemma 15.61.5: flatness of the base-change map
`A ⊗[R] R' → A'` forces flatness of the underlying map `A → A'`. -/
private theorem algebraMap_flat_of_baseChangeLeftMap_flat
    (haFlat :
      letI : Algebra ATensor A' := baseChangeLeftMap.toAlgebra
      Module.Flat ATensor A') :
    (algebraMap A A').Flat := by
  have hbaseModule : Module.Flat A ATensor := by
    -- Base change the given flat `R`-module `R'` along `R → A`.
    simpa using (Module.Flat.baseChange R A R')
  have hbase : (algebraMap A ATensor).Flat := by
    exact RingHom.flat_algebraMap_iff.mpr hbaseModule
  have htarget :
      ((baseChangeLeftMap : ATensor →ₐ[R] A').toRingHom).Flat := by
    -- Rewrite the assumed module-flatness of `A ⊗[R] R' → A'` to flatness of its ring map.
    letI : Algebra ATensor A' := baseChangeLeftMap.toAlgebra
    simpa [RingHom.algebraMap_toAlgebra] using
      (RingHom.flat_algebraMap_iff.mpr haFlat)
  have hcomp :
      (baseChangeLeftMap.toRingHom.comp (algebraMap A ATensor)).Flat :=
    RingHom.Flat.comp hbase htarget
  -- Replace the composed base-change map by the ordinary algebra map `A → A'`.
  rw [baseChangeLeftMap_comp_algebraMapA] at hcomp
  exact hcomp

/-- Helper for Lemma 15.61.5: transport the standard flat source map
`S → A' ⊗[A] S` across the canonical equivalence
`A' ⊗[A] S ≃ A' ⊗[R'] (R' ⊗[R] B)`. -/
private theorem normalized_source_base_change_flat_transport
    (hAA' : (algebraMap A A').Flat) :
    (normalizedBaseChangeMap : S →ₐ[R] STensor).toRingHom.Flat := by
  have hstandardModule : Module.Flat S (A' ⊗[A] S) := by
    -- The ordinary `A`-base change `S → A' ⊗[A] S` is flat because `A → A'` is flat.
    exact tensor_right_flat_of_flat_left (A := A) (B := A') (C := S) hAA'
  have hstandard : (algebraMap S (A' ⊗[A] S)).Flat := by
    exact RingHom.flat_algebraMap_iff.mpr hstandardModule
  have he :
      (normalizedIntermediateAlgEquiv
        (R := R) (R' := R') (A := A) (B := B) (A' := A')).toRingHom.Flat := by
    -- Ring equivalences preserve flatness of the underlying ring map.
    exact RingHom.Flat.of_bijective
      (normalizedIntermediateAlgEquiv
        (R := R) (R' := R') (A := A) (B := B) (A' := A')).bijective
  have hcomp :
      ((normalizedIntermediateAlgEquiv
          (R := R) (R' := R') (A := A) (B := B) (A' := A')).toRingHom.comp
          (algebraMap S (A' ⊗[A] S))).Flat :=
    RingHom.Flat.comp hstandard he
  have hEq :
      (normalizedIntermediateAlgEquiv
          (R := R) (R' := R') (A := A) (B := B) (A' := A')).toRingHom.comp
          (algebraMap S (A' ⊗[A] S)) =
        (normalizedBaseChangeMap : S →ₐ[R] STensor).toRingHom := by
    apply RingHom.ext
    intro s
    have hs :=
      DFunLike.congr_fun
        (normalizedIntermediateAlgEquiv_symm_comp_normalizedBaseChangeMap
          (R := R) (R' := R') (A := A) (B := B) (A' := A'))
        s
    -- Apply the forward equivalence pointwise to undo the source normalization.
    have hs' :
        (normalizedIntermediateAlgEquiv
            (R := R) (R' := R') (A := A) (B := B) (A' := A'))
            ((normalizedIntermediateAlgEquiv
              (R := R) (R' := R') (A := A) (B := B) (A' := A')).symm
                ((normalizedBaseChangeMap : S →ₐ[R] STensor) s)) =
          (normalizedIntermediateAlgEquiv
            (R := R) (R' := R') (A := A) (B := B) (A' := A'))
            ((algebraMap S (A' ⊗[A] S)) s) := by
      exact congrArg
        (fun x ↦
          (normalizedIntermediateAlgEquiv
            (R := R) (R' := R') (A := A) (B := B) (A' := A')) x)
        hs
    simpa [RingHom.comp_apply] using hs'.symm
  -- Rewrite the transported flat composite to the normalized source map.
  rwa [hEq] at hcomp

/-- Helper for Lemma 15.61.5: the normalized source map
`A ⊗[R] B → A' ⊗[R'] (R' ⊗[R] B)` is flat. -/
private theorem normalizedBaseChangeMap_flat
    (haFlat :
      letI : Algebra ATensor A' := baseChangeLeftMap.toAlgebra
      Module.Flat ATensor A') :
    letI : Algebra S STensor := normalizedBaseChangeMap.toAlgebra
    Module.Flat S STensor := by
  letI : Algebra S STensor := normalizedBaseChangeMap.toAlgebra
  have hAA' :
      (algebraMap A A').Flat :=
    algebraMap_flat_of_baseChangeLeftMap_flat
      (R := R) (R' := R') (A := A) (A' := A') haFlat
  have hnormalized :
      (normalizedBaseChangeMap : S →ₐ[R] STensor).toRingHom.Flat :=
    normalized_source_base_change_flat_transport
      (R := R) (R' := R') (A := A) (B := B) (A' := A') hAA'
  have halg : (algebraMap S STensor).Flat := by
    -- Reinterpret the normalized source flatness as flatness of the induced algebra map.
    simpa [RingHom.algebraMap_toAlgebra] using hnormalized
  exact RingHom.flat_algebraMap_iff.mp halg

/-- Helper for Lemma 15.61.5: the full base-change map
`A ⊗[R] B → A' ⊗[R'] B'` is flat because it factors as the composition of the two normalized flat
steps isolated above. -/
private theorem baseChangeProductMap_flat
    (bMap : BTensor →ₐ[R'] B')
    (haFlat :
      letI : Algebra ATensor A' := baseChangeLeftMap.toAlgebra
      Module.Flat ATensor A')
    (hbFlat :
      letI : Algebra BTensor B' := bMap.toAlgebra
      Module.Flat BTensor B') :
    letI : Algebra S T := (baseChangeProductMap bMap).toAlgebra
    Module.Flat S T := by
  letI : Algebra S T := (baseChangeProductMap bMap).toAlgebra
  have hfirstModule :
      letI : Algebra S STensor := normalizedBaseChangeMap.toAlgebra
      Module.Flat S STensor :=
    normalizedBaseChangeMap_flat
      (R := R) (R' := R') (A := A) (B := B) (A' := A') haFlat
  have hfirst :
      (normalizedBaseChangeMap : S →ₐ[R] STensor).toRingHom.Flat := by
    letI : Algebra S STensor := normalizedBaseChangeMap.toAlgebra
    -- Convert the normalized source module-flatness to flatness of the source ring map.
    simpa [RingHom.algebraMap_toAlgebra] using
      (RingHom.flat_algebraMap_iff.mpr hfirstModule)
  have hsecondModule :
      letI : Algebra STensor T := (normalizedTensorMap bMap).toAlgebra
      Module.Flat STensor T :=
    normalizedTensorMap_flat
      (R := R) (R' := R') (bMap := bMap) hbFlat
  have hsecond :
      ((normalizedTensorMap bMap : STensor →ₐ[R'] T).toRingHom).Flat := by
    letI : Algebra STensor T := (normalizedTensorMap bMap).toAlgebra
    -- Convert the final normalized module-flatness to flatness of the target ring map.
    simpa [RingHom.algebraMap_toAlgebra] using
      (RingHom.flat_algebraMap_iff.mpr hsecondModule)
  have hcomp :
      ((normalizedTensorMap bMap : STensor →ₐ[R'] T).toRingHom.comp
          (normalizedBaseChangeMap : S →ₐ[R] STensor).toRingHom).Flat :=
    RingHom.Flat.comp hfirst hsecond
  have hbase :
      (baseChangeProductMap bMap : S →ₐ[R] T).toRingHom.Flat := by
    -- Rewrite the composed normalized map to the direct textbook base-change map.
    rwa [base_change_productMap_factor_eq
      (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B') bMap] at hcomp
  have halg : (algebraMap S T).Flat := by
    -- Reinterpret the direct ring-hom flatness as flatness of the induced `S`-algebra structure.
    simpa [RingHom.algebraMap_toAlgebra] using hbase
  exact RingHom.flat_algebraMap_iff.mp halg

/-- Helper for Lemma 15.61.5: derived scalar extension from `S` to the normalized intermediate
ring. -/
private abbrev normalizedFirstStep :
    DerivedCategory (ModuleCat S) ⥤ DerivedCategory (ModuleCat STensor) :=
  derivedTensorWithAlgebra
    (R := S) (A := STensor) normalizedBaseChangeMap.toRingHom

/-- Helper for Lemma 15.61.5: derived scalar extension from `A` directly to the normalized
intermediate ring. -/
private abbrev normalizedDirectStep :
    DModA ⥤ DerivedCategory (ModuleCat STensor) :=
  derivedTensorWithAlgebra
    (R := A) (A := STensor) normalizedBaseChangeLeft.toRingHom

/-- Helper for Lemma 15.61.5: derived scalar extension from `A'` to the normalized intermediate
ring. -/
private abbrev normalizedAprimeStep :
    DerivedCategory (ModuleCat A') ⥤ DerivedCategory (ModuleCat STensor) :=
  derivedTensorWithAlgebra
    (R := A') (A := STensor) (includeLeft : A' →ₐ[R'] STensor).toRingHom

/-- Helper for Lemma 15.61.5: the final normalized flat step from
`A' ⊗[R'] (R' ⊗[R] B)` to `A' ⊗[R'] B'`. -/
private abbrev normalizedFinalStep
    (bMap : BTensor →ₐ[R'] B') :
    DerivedCategory (ModuleCat STensor) ⥤ DerivedCategory (ModuleCat T) :=
  derivedTensorWithAlgebra
    (R := STensor) (A := T) (normalizedTensorMap bMap).toRingHom

/-- Helper for Lemma 15.61.5: the direct `S → T` scalar-extension functor attached to the
textbook map `baseChangeProductMap bMap`. -/
private abbrev directFinalStep
    (bMap : BTensor →ₐ[R'] B') :
    DerivedCategory (ModuleCat S) ⥤ DerivedCategory (ModuleCat T) :=
  derivedTensorWithAlgebra
    (R := S) (A := T) (baseChangeProductMap bMap).toRingHom

/-- Helper for Lemma 15.61.5: a public clone of the restriction-of-scalars homology transport
from Lemma `15.60.3`, so later rewrites do not depend on the imported private name. -/
private noncomputable def restrictScalarsDerivedHomologyIso_public
    {U V : Type u}
    [CommRing U] [CommRing V] [Algebra U V]
    (L : DerivedCategory (ModuleCat V)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat U) i).obj
        (((ModuleCat.restrictScalars (algebraMap U V)).mapDerivedCategory).obj L) ≅
      (ModuleCat.restrictScalars (algebraMap U V)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat V) i).obj L) := by
  let K := DerivedCategory.Q.objPreimage L
  let FK := ((ModuleCat.restrictScalars (algebraMap U V)).mapHomologicalComplex (up ℤ)).obj K
  let eV :
      (DerivedCategory.homologyFunctor (ModuleCat V) i).obj L ≅
        K.homology i :=
    ((DerivedCategory.homologyFunctor (ModuleCat V) i).mapIso
      (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat V) i).app K
  -- Use the same chosen `Q.objPreimage` model as Lemma `15.60.3`, but keep the transport public
  -- in this file so the adjoint-side rewrite can be stated without private imported names.
  exact
    ((DerivedCategory.homologyFunctor (ModuleCat U) i).mapIso
        ((((ModuleCat.restrictScalars (algebraMap U V)).mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
          ((ModuleCat.restrictScalars (algebraMap U V)).mapDerivedCategoryFactors.app K))) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FK ≪≫
      (K.sc i).mapHomologyIso (ModuleCat.restrictScalars (algebraMap U V)) ≪≫
      (ModuleCat.restrictScalars (algebraMap U V)).mapIso eV.symm

/-- Helper for Lemma 15.61.5: the adjoint-side description of the owner homology comparison can
be rewritten using the public transport just defined above. -/
private theorem derivedTensorWithAlgebraHomologyComparison_adjoint_public_eq
    {U V : Type u}
    [CommRing U] [CommRing V] [Algebra U V]
    (K : DerivedCategory (ModuleCat U)) (i : ℤ) :
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap U V)).homEquiv _ _)
        (derivedTensorWithAlgebraHomologyComparison V K i) =
      (DerivedCategory.homologyFunctor (ModuleCat U) i).map
          ((derivedTensorWithAlgebraAdjunction (R := U) (A := V)).unit.app K) ≫
        (restrictScalarsDerivedHomologyIso_public
          (U := U) (V := V)
          ((derivedTensorWithAlgebra (algebraMap U V)).obj K) i).hom := by
  -- Unfold the owner comparison once; the remaining term is definitionally the same adjoint-side
  -- composite, now phrased through the public transport.
  rw [derivedTensorWithAlgebraHomologyComparison]
  simp only [Equiv.apply_symm_apply]
  rfl

/-- Helper for Lemma 15.61.5: under restriction of scalars, the homology map of a short-complex
morphism rewrites into the forward `mapHomologyIso` form needed by the expanded transport square.
-/
private theorem restrictScalars_mapHomologyIso_hom_formula
    {U V : Type u}
    [CommRing U] [CommRing V] [Algebra U V]
    {S₁ S₂ : ShortComplex (ModuleCat V)}
    (φ : S₁ ⟶ S₂) :
    (ModuleCat.restrictScalars (algebraMap U V)).map (ShortComplex.homologyMap φ) =
      (S₁.mapHomologyIso (ModuleCat.restrictScalars (algebraMap U V))).inv ≫
        ShortComplex.homologyMap
          (((ModuleCat.restrictScalars (algebraMap U V)).mapShortComplex).map φ) ≫
        (S₂.mapHomologyIso (ModuleCat.restrictScalars (algebraMap U V))).hom := by
  -- Start from the inverse-form naturality square already in mathlib and solve it for the
  -- forward homology map used in the public transport expansion.
  calc
    (ModuleCat.restrictScalars (algebraMap U V)).map (ShortComplex.homologyMap φ) =
        (ModuleCat.restrictScalars (algebraMap U V)).map (ShortComplex.homologyMap φ) ≫
          (S₂.mapHomologyIso (ModuleCat.restrictScalars (algebraMap U V))).inv ≫
            (S₂.mapHomologyIso (ModuleCat.restrictScalars (algebraMap U V))).hom := by
      simp [Category.assoc]
    _ =
        (S₁.mapHomologyIso (ModuleCat.restrictScalars (algebraMap U V))).inv ≫
          ShortComplex.homologyMap
            (((ModuleCat.restrictScalars (algebraMap U V)).mapShortComplex).map φ) ≫
          (S₂.mapHomologyIso (ModuleCat.restrictScalars (algebraMap U V))).hom := by
      -- Postcompose the inverse-form naturality square by the target comparison isomorphism.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ k ≫ (S₂.mapHomologyIso (ModuleCat.restrictScalars (algebraMap U V))).hom)
          (ShortComplex.mapHomologyIso_inv_naturality
            (F := ModuleCat.restrictScalars (algebraMap U V)) (φ := φ))

/-- Helper for Lemma 15.61.5: the short-complex model of degree-`i` homology agrees
definitionally with the cochain-level homology map. -/
private theorem shortComplexFunctor_homologyMap_eq
    {V : Type u} [CommRing V]
    {Y Z : CochainComplex (ModuleCat V) ℤ}
    (β : Y ⟶ Z) (i : ℤ) :
    ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor (ModuleCat V) (up ℤ) i).map β) =
      HomologicalComplex.homologyMap β i := by
  -- The degree-`i` short-complex model is just a definitional reindexing of cochain homology.
  rfl

/-- Helper for Lemma 15.61.5: restriction of scalars commutes definitionally with the
degree-`i` short-complex functor on cochain complexes. -/
private theorem restrictScalars_shortComplexFunctor_map_eq
    {U V : Type u} [CommRing U] [CommRing V] [Algebra U V]
    {Y Z : CochainComplex (ModuleCat V) ℤ}
    (β : Y ⟶ Z) (i : ℤ) :
    (((ModuleCat.restrictScalars (algebraMap U V)).mapShortComplex).map
        ((HomologicalComplex.shortComplexFunctor (ModuleCat V) (up ℤ) i).map β)) =
      ((HomologicalComplex.shortComplexFunctor (ModuleCat U) (up ℤ) i).map
        (((ModuleCat.restrictScalars (algebraMap U V)).mapHomologicalComplex (up ℤ)).map β)) := by
  -- Both sides are the same short-complex morphism after unfolding the functorial definitions.
  rfl

/-- Helper for Lemma 15.61.5: after rewriting the short-complex transport square for
restriction of scalars, the source `mapHomologyIso` comparison cancels and yields the forward
cochain-level homology-map formula used below. -/
private theorem restrictScalars_mapHomologyIso_source_cancel
    {U V : Type u} [CommRing U] [CommRing V] [Algebra U V]
    {Y Z : CochainComplex (ModuleCat V) ℤ}
    (β : Y ⟶ Z) (i : ℤ) :
    let res : ModuleCat V ⥤ ModuleCat U := ModuleCat.restrictScalars (algebraMap U V)
    ((Y.sc i).mapHomologyIso res).hom ≫
        res.map (HomologicalComplex.homologyMap β i) =
      HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
        ((Z.sc i).mapHomologyIso res).hom := by
  let res : ModuleCat V ⥤ ModuleCat U := ModuleCat.restrictScalars (algebraMap U V)
  have hformula :
      res.map (HomologicalComplex.homologyMap β i) =
        ((Y.sc i).mapHomologyIso res).inv ≫
          HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
            ((Z.sc i).mapHomologyIso res).hom := by
    -- Rewrite the short-complex comparison into the cochain-level homology map.
    simpa [shortComplexFunctor_homologyMap_eq, restrictScalars_shortComplexFunctor_map_eq] using
      (restrictScalars_mapHomologyIso_hom_formula
        (U := U) (V := V)
        (S₁ := Y.sc i) (S₂ := Z.sc i)
        ((HomologicalComplex.shortComplexFunctor (ModuleCat V) (up ℤ) i).map β))
  -- Cancel the source `mapHomologyIso` inverse from the forward short-complex transport square.
  let t :=
    ((Y.sc i).mapHomologyIso res).hom ≫
      (((Y.sc i).mapHomologyIso res).inv ≫
        HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
          ((Z.sc i).mapHomologyIso res).hom)
  have hpre :
      ((Y.sc i).mapHomologyIso res).hom ≫ res.map (HomologicalComplex.homologyMap β i) =
        t := by
    exact congrArg (fun k ↦ ((Y.sc i).mapHomologyIso res).hom ≫ k) hformula
  simpa [t, Category.assoc] using hpre

/-- Helper for Lemma 15.61.5: once a transported derived morphism is represented by a chosen
`Q.objPreimage` chain map `β`, the restriction-of-scalars transport collapses to the standard
`mapDerivedCategoryFactors` naturality square. -/
private theorem restrictScalars_q_objPreimage_transport_bridge
    {U V : Type u}
    [CommRing U] [CommRing V] [Algebra U V]
    {K L : DerivedCategory (ModuleCat V)}
    (f : K ⟶ L)
    (β : DerivedCategory.Q.objPreimage K ⟶ DerivedCategory.Q.objPreimage L)
    (hβ :
      DerivedCategory.Q.map β =
        (DerivedCategory.Q.objObjPreimageIso K).hom ≫ f ≫
          (DerivedCategory.Q.objObjPreimageIso L).inv) :
    let res : ModuleCat V ⥤ ModuleCat U := ModuleCat.restrictScalars (algebraMap U V)
    let K' := DerivedCategory.Q.objPreimage K
    let L' := DerivedCategory.Q.objPreimage L
    res.mapDerivedCategory.map f ≫
        ((((res.mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
          (res.mapDerivedCategoryFactors.app L')).hom) =
      ((((res.mapDerivedCategory).mapIso
          (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
        (res.mapDerivedCategoryFactors.app K')).hom) ≫
        DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β) := by
  let res : ModuleCat V ⥤ ModuleCat U := ModuleCat.restrictScalars (algebraMap U V)
  let K' := DerivedCategory.Q.objPreimage K
  let L' := DerivedCategory.Q.objPreimage L
  let eK : DerivedCategory.Q.obj K' ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let eL : DerivedCategory.Q.obj L' ≅ L := DerivedCategory.Q.objObjPreimageIso L
  have hf :
      f = eK.inv ≫ DerivedCategory.Q.map β ≫ eL.hom := by
    -- Reexpress `f` by conjugating the chosen representative `β` with the standard preimage
    -- isomorphisms.
    simpa [eK, eL, Category.assoc] using
      (congrArg (fun k ↦ eK.inv ≫ k ≫ eL.hom) hβ).symm
  -- Once `f` is rewritten through `β`, the whole transport square is the naturality of
  -- `mapDerivedCategoryFactors.hom`.
  calc
    res.mapDerivedCategory.map f ≫
        ((((res.mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
          (res.mapDerivedCategoryFactors.app L')).hom) =
      (((res.mapDerivedCategory).mapIso eK).symm).hom ≫
        (res.mapDerivedCategory.map (DerivedCategory.Q.map β) ≫
          (res.mapDerivedCategoryFactors.app L').hom) := by
        -- The source-side `Q.objObjPreimageIso` conjugations cancel, leaving the transported
        -- `Q.map β` term in the middle.
        rw [hf]
        simp [res, K', L', eK, eL, Functor.map_comp, Category.assoc]
    _ =
      (((res.mapDerivedCategory).mapIso eK).symm).hom ≫
        ((res.mapDerivedCategoryFactors.app K').hom ≫
          DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) := by
        -- This is exactly the naturality square for the derived-comparison natural isomorphism.
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ (((res.mapDerivedCategory).mapIso eK).symm).hom ≫ k)
            (res.mapDerivedCategoryFactors.hom.naturality β)
    _ =
      ((((res.mapDerivedCategory).mapIso
          (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
        (res.mapDerivedCategoryFactors.app K')).hom) ≫
        DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β) := by
        simp [res, K', eK, Category.assoc]

/-- Helper for Lemma 15.61.5: the public restriction-of-scalars homology transport is natural in
the derived-category object. -/
private theorem q_objPreimage_homologyMap_conjugated
    {V : Type u}
    [CommRing V]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat V)}
    (f : K ⟶ L)
    (β : DerivedCategory.Q.objPreimage K ⟶ DerivedCategory.Q.objPreimage L)
    (hβ :
      DerivedCategory.Q.map β =
        (DerivedCategory.Q.objObjPreimageIso K).hom ≫ f ≫
          (DerivedCategory.Q.objObjPreimageIso L).inv) :
    let HV := DerivedCategory.homologyFunctor (ModuleCat V)
    let K' := DerivedCategory.Q.objPreimage K
    let L' := DerivedCategory.Q.objPreimage L
    let eK : (HV i).obj K ≅ K'.homology i :=
      ((HV i).mapIso (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat V) i).app K'
    let eL : (HV i).obj L ≅ L'.homology i :=
      ((HV i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat V) i).app L'
    HomologicalComplex.homologyMap β i =
      eK.inv ≫ (HV i).map f ≫ eL.hom := by
  let HV := DerivedCategory.homologyFunctor (ModuleCat V)
  let K' := DerivedCategory.Q.objPreimage K
  let L' := DerivedCategory.Q.objPreimage L
  let eQK : DerivedCategory.Q.obj K' ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let eQL : DerivedCategory.Q.obj L' ≅ L := DerivedCategory.Q.objObjPreimageIso L
  let ηK := (DerivedCategory.homologyFunctorFactors (ModuleCat V) i).app K'
  let ηL := (DerivedCategory.homologyFunctorFactors (ModuleCat V) i).app L'
  let eK : (HV i).obj K ≅ K'.homology i :=
    ((HV i).mapIso eQK).symm ≪≫ ηK
  let eL : (HV i).obj L ≅ L'.homology i :=
    ((HV i).mapIso eQL).symm ≪≫ ηL
  have hnat :
      (HV i).map (DerivedCategory.Q.map β) ≫ ηL.hom =
        ηK.hom ≫ HomologicalComplex.homologyMap β i := by
    -- Naturality identifies the derived homology map of `Q.map β` with the cochain-level map.
    simpa [ηK, ηL] using
      (DerivedCategory.homologyFunctorFactors_hom_naturality
        (C := ModuleCat V) β i)
  have hconj :
      HomologicalComplex.homologyMap β i =
        ηK.inv ≫ (HV i).map (DerivedCategory.Q.map β) ≫ ηL.hom := by
    have hpre :
        ηK.inv ≫ (ηK.hom ≫ HomologicalComplex.homologyMap β i) =
          ηK.inv ≫ ((HV i).map (DerivedCategory.Q.map β) ≫ ηL.hom) := by
      -- Precompose the naturality square by the inverse source comparison to isolate the
      -- cochain-level homology map.
      simpa [Category.assoc] using
        congrArg (fun k ↦ ηK.inv ≫ k) hnat.symm
    simpa [Category.assoc] using hpre
  have hf :
      f = eQK.inv ≫ DerivedCategory.Q.map β ≫ eQL.hom := by
    -- Reexpress `f` by conjugating the chosen representative `β` with the standard preimage
    -- isomorphisms.
    simpa [eQK, eQL, Category.assoc] using
      (congrArg (fun k ↦ eQK.inv ≫ k ≫ eQL.hom) hβ).symm
  have hstep :
      ηK.inv ≫ (HV i).map (DerivedCategory.Q.map β) ≫ ηL.hom =
        eK.inv ≫ (HV i).map f ≫ eL.hom := by
    -- Rewrite the represented derived morphism to the actual target morphism `f`.
    rw [hf]
    simp [HV, eK, eL, eQK, eQL, ηK, ηL, Functor.map_comp, Category.assoc]
  -- Replace the derived map of `Q.map β` by the target morphism `f` using the standard
  -- `Q.objObjPreimageIso` conjugation.
  exact hconj.trans hstep

/-- Helper for Lemma 15.61.5: the same homology conjugation works for any chosen source
representative of `K`, not only the canonical `Q.objPreimage K`. -/
private theorem q_representative_homologyMap_conjugated
    {V : Type u}
    [CommRing V]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat V)}
    {Y : CochainComplex (ModuleCat V) ℤ}
    (f : K ⟶ L)
    (eY : DerivedCategory.Q.obj Y ≅ K)
    (β : Y ⟶ DerivedCategory.Q.objPreimage L)
    (hβ :
      DerivedCategory.Q.map β =
        eY.hom ≫ f ≫
          (DerivedCategory.Q.objObjPreimageIso L).inv) :
    let HV := DerivedCategory.homologyFunctor (ModuleCat V)
    let L' := DerivedCategory.Q.objPreimage L
    let ηY := (DerivedCategory.homologyFunctorFactors (ModuleCat V) i).app Y
    let ηL := (DerivedCategory.homologyFunctorFactors (ModuleCat V) i).app L'
    let eSrc : (HV i).obj K ≅ Y.homology i :=
      ((HV i).mapIso eY).symm ≪≫ ηY
    let eL : (HV i).obj L ≅ L'.homology i :=
      ((HV i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫ ηL
    HomologicalComplex.homologyMap β i =
      eSrc.inv ≫ (HV i).map f ≫ eL.hom := by
  let HV := DerivedCategory.homologyFunctor (ModuleCat V)
  let L' := DerivedCategory.Q.objPreimage L
  let eQL : DerivedCategory.Q.obj L' ≅ L := DerivedCategory.Q.objObjPreimageIso L
  let ηY := (DerivedCategory.homologyFunctorFactors (ModuleCat V) i).app Y
  let ηL := (DerivedCategory.homologyFunctorFactors (ModuleCat V) i).app L'
  let eSrc : (HV i).obj K ≅ Y.homology i :=
    ((HV i).mapIso eY).symm ≪≫ ηY
  let eL : (HV i).obj L ≅ L'.homology i :=
    ((HV i).mapIso eQL).symm ≪≫ ηL
  have hnat :
      (HV i).map (DerivedCategory.Q.map β) ≫ ηL.hom =
        ηY.hom ≫ HomologicalComplex.homologyMap β i := by
    -- Naturality of `homologyFunctorFactors` rewrites the derived map of `Q.map β` into the
    -- chain-level homology map of the chosen representative.
    simpa [ηY, ηL] using
      (DerivedCategory.homologyFunctorFactors_hom_naturality
        (C := ModuleCat V) β i)
  have hconj :
      HomologicalComplex.homologyMap β i =
        ηY.inv ≫ (HV i).map (DerivedCategory.Q.map β) ≫ ηL.hom := by
    have hpre :
        ηY.inv ≫ (ηY.hom ≫ HomologicalComplex.homologyMap β i) =
          ηY.inv ≫ ((HV i).map (DerivedCategory.Q.map β) ≫ ηL.hom) := by
      -- Precompose the naturality square by the inverse source comparison to isolate the
      -- cochain-level homology map.
      simpa [Category.assoc] using
        congrArg (fun k ↦ ηY.inv ≫ k) hnat.symm
    simpa [Category.assoc] using hpre
  have hf :
      f = eY.inv ≫ DerivedCategory.Q.map β ≫ eQL.hom := by
    -- Conjugate the representative equation by the chosen source iso and the canonical target
    -- `Q.objPreimage` iso.
    simpa [eQL, Category.assoc] using
      (congrArg (fun k ↦ eY.inv ≫ k ≫ eQL.hom) hβ).symm
  have hstep :
      ηY.inv ≫ (HV i).map (DerivedCategory.Q.map β) ≫ ηL.hom =
        eSrc.inv ≫ (HV i).map f ≫ eL.hom := by
    -- Rewrite the represented derived morphism to the actual target morphism `f`.
    rw [hf]
    simp [HV, eSrc, eL, eQL, ηY, ηL, Functor.map_comp, Category.assoc]
  -- Replace `Q.map β` by the target morphism `f`.
  exact hconj.trans hstep

/-- Helper for Lemma 15.61.5: after choosing a `Q.objPreimage` representative `β`, the
restriction-of-scalars homology transport reduces to the naturality square for
`homologyFunctorFactors` followed by the forward `mapHomologyIso` transport. -/
private theorem restrictScalars_q_objPreimage_homology_transport
    {U V : Type u}
    [CommRing U] [CommRing V] [Algebra U V]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat V)}
    (β : DerivedCategory.Q.objPreimage K ⟶ DerivedCategory.Q.objPreimage L) :
    let res : ModuleCat V ⥤ ModuleCat U := ModuleCat.restrictScalars (algebraMap U V)
    let HU := DerivedCategory.homologyFunctor (ModuleCat U)
    let K' := DerivedCategory.Q.objPreimage K
    let L' := DerivedCategory.Q.objPreimage L
    let FK := (res.mapHomologicalComplex (up ℤ)).obj K'
    let FL := (res.mapHomologicalComplex (up ℤ)).obj L'
    (HU i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FL).hom ≫
        ((L'.sc i).mapHomologyIso res).hom =
      ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FK).hom ≫
        ((K'.sc i).mapHomologyIso res).hom ≫
        res.map (HomologicalComplex.homologyMap β i) := by
  let res : ModuleCat V ⥤ ModuleCat U := ModuleCat.restrictScalars (algebraMap U V)
  let HU := DerivedCategory.homologyFunctor (ModuleCat U)
  let K' := DerivedCategory.Q.objPreimage K
  let L' := DerivedCategory.Q.objPreimage L
  let FK := (res.mapHomologicalComplex (up ℤ)).obj K'
  let FL := (res.mapHomologicalComplex (up ℤ)).obj L'
  have hnat :
      (HU i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FL).hom =
        ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FK).hom ≫
          HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i := by
    -- Naturality transports the derived homology map to the chosen cochain representative.
    simpa [FK, FL] using
      (DerivedCategory.homologyFunctorFactors_hom_naturality
        (C := ModuleCat U)
        ((res.mapHomologicalComplex (up ℤ)).map β) i)
  have hmap :
      ((K'.sc i).mapHomologyIso res).hom ≫
          res.map (HomologicalComplex.homologyMap β i) =
        HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
          ((L'.sc i).mapHomologyIso res).hom :=
    restrictScalars_mapHomologyIso_source_cancel
      (U := U) (V := V) (β := β) (i := i)
  have hnat' :
      (HU i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FL).hom ≫
          ((L'.sc i).mapHomologyIso res).hom =
        ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FK).hom ≫
          HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
            ((L'.sc i).mapHomologyIso res).hom := by
    -- Postcompose the derived naturality square by the target `mapHomologyIso`.
    simpa [Category.assoc] using
      congrArg (fun k ↦ k ≫ ((L'.sc i).mapHomologyIso res).hom) hnat
  have hmap' :
      ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FK).hom ≫
          HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
            ((L'.sc i).mapHomologyIso res).hom =
        ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FK).hom ≫
          ((K'.sc i).mapHomologyIso res).hom ≫
            res.map (HomologicalComplex.homologyMap β i) := by
    -- Precompose the forward `mapHomologyIso` transport by the source comparison on `FK`.
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FK).hom ≫ k)
        hmap.symm
  -- Splice the derived naturality square with the forward `mapHomologyIso` transport.
  exact hnat'.trans hmap'

/-- Helper for Lemma 15.61.5: the restriction-of-scalars transport square is equally valid for an
arbitrary source representative `Y` of `K`. -/
private theorem restrictScalars_q_representative_transport_bridge
    {U V : Type u}
    [CommRing U] [CommRing V] [Algebra U V]
    {K L : DerivedCategory (ModuleCat V)}
    {Y : CochainComplex (ModuleCat V) ℤ}
    (f : K ⟶ L)
    (eY : DerivedCategory.Q.obj Y ≅ K)
    (β : Y ⟶ DerivedCategory.Q.objPreimage L)
    (hβ :
      DerivedCategory.Q.map β =
        eY.hom ≫ f ≫
          (DerivedCategory.Q.objObjPreimageIso L).inv) :
    let res : ModuleCat V ⥤ ModuleCat U := ModuleCat.restrictScalars (algebraMap U V)
    let L' := DerivedCategory.Q.objPreimage L
    res.mapDerivedCategory.map f ≫
        ((((res.mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
          (res.mapDerivedCategoryFactors.app L')).hom) =
      ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
          (res.mapDerivedCategoryFactors.app Y)).hom) ≫
        DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β) := by
  let res : ModuleCat V ⥤ ModuleCat U := ModuleCat.restrictScalars (algebraMap U V)
  let L' := DerivedCategory.Q.objPreimage L
  let eL : DerivedCategory.Q.obj L' ≅ L := DerivedCategory.Q.objObjPreimageIso L
  have hf :
      f = eY.inv ≫ DerivedCategory.Q.map β ≫ eL.hom := by
    -- Reexpress `f` through the chosen representative `β`.
    simpa [eL, Category.assoc] using
      (congrArg (fun k ↦ eY.inv ≫ k ≫ eL.hom) hβ).symm
  -- After this conjugation, the claim is the naturality square for
  -- `mapDerivedCategoryFactors.hom`.
  calc
    res.mapDerivedCategory.map f ≫
        ((((res.mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
          (res.mapDerivedCategoryFactors.app L')).hom) =
      (((res.mapDerivedCategory).mapIso eY).symm).hom ≫
        (res.mapDerivedCategory.map (DerivedCategory.Q.map β) ≫
          (res.mapDerivedCategoryFactors.app L').hom) := by
        -- The source and target `Q`-model isomorphisms collapse the conjugated form of `f`.
        rw [hf]
        simp [res, L', eL, Functor.map_comp, Category.assoc]
    _ =
      (((res.mapDerivedCategory).mapIso eY).symm).hom ≫
        ((res.mapDerivedCategoryFactors.app Y).hom ≫
          DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) := by
        -- This is exactly the naturality of the derived comparison on the representative `β`.
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ (((res.mapDerivedCategory).mapIso eY).symm).hom ≫ k)
            (res.mapDerivedCategoryFactors.hom.naturality β)
    _ =
      ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
          (res.mapDerivedCategoryFactors.app Y)).hom) ≫
        DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β) := by
        simp [res, Category.assoc]

/-- Helper for Lemma 15.61.5: the restriction-of-scalars homology transport through
`mapHomologyIso` only depends on the chosen chain representative, not on using the canonical
source preimage. -/
private theorem restrictScalars_q_representative_homology_transport
    {U V : Type u}
    [CommRing U] [CommRing V] [Algebra U V]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat V)}
    {Y : CochainComplex (ModuleCat V) ℤ}
    (β : Y ⟶ DerivedCategory.Q.objPreimage L) :
    let res : ModuleCat V ⥤ ModuleCat U := ModuleCat.restrictScalars (algebraMap U V)
    let HU := DerivedCategory.homologyFunctor (ModuleCat U)
    let L' := DerivedCategory.Q.objPreimage L
    let FY := (res.mapHomologicalComplex (up ℤ)).obj Y
    let FL := (res.mapHomologicalComplex (up ℤ)).obj L'
    (HU i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FL).hom ≫
        ((L'.sc i).mapHomologyIso res).hom =
      ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FY).hom ≫
        ((Y.sc i).mapHomologyIso res).hom ≫
        res.map (HomologicalComplex.homologyMap β i) := by
  let res : ModuleCat V ⥤ ModuleCat U := ModuleCat.restrictScalars (algebraMap U V)
  let HU := DerivedCategory.homologyFunctor (ModuleCat U)
  let L' := DerivedCategory.Q.objPreimage L
  let FY := (res.mapHomologicalComplex (up ℤ)).obj Y
  let FL := (res.mapHomologicalComplex (up ℤ)).obj L'
  have hnat :
      (HU i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FL).hom =
        ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FY).hom ≫
          HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i := by
    -- Naturality again identifies the derived homology map with the chain-level one.
    simpa [FY, FL] using
      (DerivedCategory.homologyFunctorFactors_hom_naturality
        (C := ModuleCat U)
        ((res.mapHomologicalComplex (up ℤ)).map β) i)
  have hmap :
      ((Y.sc i).mapHomologyIso res).hom ≫
          res.map (HomologicalComplex.homologyMap β i) =
        HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
          ((L'.sc i).mapHomologyIso res).hom :=
    restrictScalars_mapHomologyIso_source_cancel
      (U := U) (V := V) (β := β) (i := i)
  have hnat' :
      (HU i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FL).hom ≫
          ((L'.sc i).mapHomologyIso res).hom =
        ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FY).hom ≫
          HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
            ((L'.sc i).mapHomologyIso res).hom := by
    -- Postcompose the derived naturality square by the target `mapHomologyIso`.
    simpa [Category.assoc] using
      congrArg (fun k ↦ k ≫ ((L'.sc i).mapHomologyIso res).hom) hnat
  have hmap' :
      ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FY).hom ≫
          HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
            ((L'.sc i).mapHomologyIso res).hom =
        ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FY).hom ≫
          ((Y.sc i).mapHomologyIso res).hom ≫
            res.map (HomologicalComplex.homologyMap β i) := by
    -- Precompose the forward `mapHomologyIso` transport by the source comparison on `FY`.
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FY).hom ≫ k)
        hmap.symm
  -- Splice the derived naturality square with the forward `mapHomologyIso` transport.
  exact hnat'.trans hmap'

/-- Helper for Lemma 15.61.5: once the source morphism is represented by an arbitrary roof
`Y → Q.objPreimage L`, the public restriction-of-scalars homology square is fully explicit. -/
private theorem restrictScalarsDerivedHomologyIso_public_naturality_of_representative
    {U V : Type u}
    [CommRing U] [CommRing V] [Algebra U V]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat V)}
    (f : K ⟶ L)
    {Y : CochainComplex (ModuleCat V) ℤ}
    (eY : DerivedCategory.Q.obj Y ≅ K)
    (β : Y ⟶ DerivedCategory.Q.objPreimage L)
    (hβ :
      DerivedCategory.Q.map β =
        eY.hom ≫ f ≫
          (DerivedCategory.Q.objObjPreimageIso L).inv) :
    let res : ModuleCat V ⥤ ModuleCat U := ModuleCat.restrictScalars (algebraMap U V)
    let HU := DerivedCategory.homologyFunctor (ModuleCat U)
    let HV := DerivedCategory.homologyFunctor (ModuleCat V)
    let L' := DerivedCategory.Q.objPreimage L
    let FY := (res.mapHomologicalComplex (up ℤ)).obj Y
    let FL := (res.mapHomologicalComplex (up ℤ)).obj L'
    let eSrc : (HV i).obj K ≅ Y.homology i :=
      ((HV i).mapIso eY).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat V) i).app Y
    let eL : (HV i).obj L ≅ L'.homology i :=
      ((HV i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat V) i).app L'
    (HU i).map (res.mapDerivedCategory.map f) ≫
        ((HU i).mapIso
          ((((res.mapDerivedCategory).mapIso
              (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
            (res.mapDerivedCategoryFactors.app L')))).hom ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FL).hom ≫
        ((L'.sc i).mapHomologyIso res).hom ≫
        (res.mapIso eL.symm).hom =
      ((HU i).mapIso
          ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
            (res.mapDerivedCategoryFactors.app Y)))).hom ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FY).hom ≫
        ((Y.sc i).mapHomologyIso res).hom ≫
        (res.mapIso eSrc.symm).hom ≫
        res.map ((HV i).map f) := by
  let res : ModuleCat V ⥤ ModuleCat U := ModuleCat.restrictScalars (algebraMap U V)
  let HU := DerivedCategory.homologyFunctor (ModuleCat U)
  let HV := DerivedCategory.homologyFunctor (ModuleCat V)
  let L' := DerivedCategory.Q.objPreimage L
  let FY := (res.mapHomologicalComplex (up ℤ)).obj Y
  let FL := (res.mapHomologicalComplex (up ℤ)).obj L'
  let eSrc : (HV i).obj K ≅ Y.homology i :=
    ((HV i).mapIso eY).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat V) i).app Y
  let eL : (HV i).obj L ≅ L'.homology i :=
    ((HV i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat V) i).app L'
  have hbridge :
      res.mapDerivedCategory.map f ≫
          ((((res.mapDerivedCategory).mapIso
              (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
            (res.mapDerivedCategoryFactors.app L')).hom) =
        ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
            (res.mapDerivedCategoryFactors.app Y)).hom) ≫
          DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β) :=
    restrictScalars_q_representative_transport_bridge
      (U := U) (V := V) (f := f) (eY := eY) (β := β) hβ
  have hbridge_homology :
      (HU i).map (res.mapDerivedCategory.map f) ≫
          ((HU i).mapIso
            ((((res.mapDerivedCategory).mapIso
                (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
              (res.mapDerivedCategoryFactors.app L')))).hom =
        ((HU i).mapIso
            ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
              (res.mapDerivedCategoryFactors.app Y)))).hom ≫
          (HU i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) := by
    -- Apply degree-`i` homology to the representative bridge between the derived morphism and
    -- the chosen cochain map.
    simpa [Functor.map_comp, Functor.mapIso_hom, Category.assoc] using
      congrArg (fun k ↦ (HU i).map k) hbridge
  have htransport :
      (HU i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FL).hom ≫
          ((L'.sc i).mapHomologyIso res).hom =
        ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FY).hom ≫
          ((Y.sc i).mapHomologyIso res).hom ≫
          res.map (HomologicalComplex.homologyMap β i) :=
    restrictScalars_q_representative_homology_transport
      (U := U) (V := V) (i := i) (K := K) (L := L) (β := β)
  have hβ_homology :
      res.map (HomologicalComplex.homologyMap β i) ≫ (res.mapIso eL.symm).hom =
        (res.mapIso eSrc.symm).hom ≫ res.map ((HV i).map f) := by
    -- Map the representative-level conjugation formula through restriction of scalars and cancel
    -- the target `mapIso` tail explicitly.
    have hconj :
        HomologicalComplex.homologyMap β i =
          eSrc.inv ≫ (HV i).map f ≫ eL.hom :=
      q_representative_homologyMap_conjugated
        (V := V) (i := i) (f := f) (eY := eY) (β := β) hβ
    rw [hconj]
    simp [Functor.map_comp, Category.assoc]
  let sourceComparison :
      (HU i).obj (res.mapDerivedCategory.obj K) ⟶
        (HU i).obj (DerivedCategory.Q.obj ((res.mapHomologicalComplex (up ℤ)).obj Y)) :=
    ((HU i).mapIso
      ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
        (res.mapDerivedCategoryFactors.app Y)))).hom
  have hstep₁ :
      (HU i).map (res.mapDerivedCategory.map f) ≫
          ((HU i).mapIso
            ((((res.mapDerivedCategory).mapIso
                (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
              (res.mapDerivedCategoryFactors.app L')))).hom ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FL).hom ≫
          ((L'.sc i).mapHomologyIso res).hom ≫
          (res.mapIso eL.symm).hom =
        sourceComparison ≫
          (HU i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FL).hom ≫
          ((L'.sc i).mapHomologyIso res).hom ≫
          (res.mapIso eL.symm).hom := by
    -- Append the remaining homology-side tail to the derived representative bridge.
    simpa [sourceComparison, Category.assoc] using
      congrArg
        (fun k ↦ k ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FL).hom ≫
          ((L'.sc i).mapHomologyIso res).hom ≫
          (res.mapIso eL.symm).hom)
        hbridge_homology
  have hstep₂ :
      sourceComparison ≫
          (HU i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FL).hom ≫
          ((L'.sc i).mapHomologyIso res).hom ≫
          (res.mapIso eL.symm).hom =
        sourceComparison ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FY).hom ≫
          ((Y.sc i).mapHomologyIso res).hom ≫
          res.map (HomologicalComplex.homologyMap β i) ≫
          (res.mapIso eL.symm).hom := by
    -- Replace the transported chain-level homology map by the forward representative transport.
    simpa [sourceComparison, Category.assoc] using
      congrArg
        (fun k ↦ sourceComparison ≫ k ≫ (res.mapIso eL.symm).hom)
        htransport
  have hstep₃ :
      sourceComparison ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FY).hom ≫
          ((Y.sc i).mapHomologyIso res).hom ≫
          res.map (HomologicalComplex.homologyMap β i) ≫
          (res.mapIso eL.symm).hom =
        sourceComparison ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FY).hom ≫
          ((Y.sc i).mapHomologyIso res).hom ≫
          (res.mapIso eSrc.symm).hom ≫
          res.map ((HV i).map f) := by
    -- Replace the representative cochain homology map by the derived homology map of `f`.
    simpa [sourceComparison, Category.assoc] using
      congrArg
        (fun k ↦ sourceComparison ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FY).hom ≫
          ((Y.sc i).mapHomologyIso res).hom ≫ k)
        hβ_homology
  -- Expose the chosen roof on the derived side, then replace the cochain-level homology map by
  -- the conjugated derived homology map of `f`.
  exact hstep₁.trans (hstep₂.trans hstep₃)

/-- Helper for Lemma 15.61.5: every morphism into a derived object can be represented by a roof
whose target is the chosen `Q.objPreimage` model of that object. -/
private theorem exists_quasi_iso_fraction_to_preimage
    {V : Type u}
    [CommRing V]
    {K₀ : CochainComplex (ModuleCat V) ℤ}
    {L : DerivedCategory (ModuleCat V)}
    (α : DerivedCategory.Q.obj K₀ ⟶ L) :
    ∃ (Y : CochainComplex (ModuleCat V) ℤ) (σ : Y ⟶ K₀) (_ : QuasiIso σ)
      (β : Y ⟶ DerivedCategory.Q.objPreimage L),
      DerivedCategory.Q.map σ ≫ α =
        DerivedCategory.Q.map β ≫ (DerivedCategory.Q.objObjPreimageIso L).hom := by
  -- Move the target to the chosen complex representative so that `right_fac` applies directly.
  let γ :
      DerivedCategory.Q.obj K₀ ⟶
        DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage L) :=
    α ≫ (DerivedCategory.Q.objObjPreimageIso L).inv
  obtain ⟨Y, σ, hσ, β, hγ⟩ := DerivedCategory.right_fac γ
  refine ⟨Y, σ, ?_, β, ?_⟩
  · -- `right_fac` gives an isomorphism after applying `Q`, which is the same as a quasi-isomorphism.
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso] at hσ
    exact hσ
  -- Cancel the inverse denominator from `right_fac` to recover the usual roof identity.
  calc
    DerivedCategory.Q.map σ ≫ α =
        DerivedCategory.Q.map σ ≫
          (α ≫ (DerivedCategory.Q.objObjPreimageIso L).inv) ≫
            (DerivedCategory.Q.objObjPreimageIso L).hom := by
          simp [Category.assoc]
    _ = DerivedCategory.Q.map σ ≫ γ ≫
          (DerivedCategory.Q.objObjPreimageIso L).hom := by
          rfl
    _ = DerivedCategory.Q.map σ ≫
          (inv (DerivedCategory.Q.map σ) ≫ DerivedCategory.Q.map β) ≫
            (DerivedCategory.Q.objObjPreimageIso L).hom := by
          rw [hγ]
    _ = DerivedCategory.Q.map β ≫
          (DerivedCategory.Q.objObjPreimageIso L).hom := by
          simp [Category.assoc]

/-- Helper for Lemma 15.61.5: the public restriction-of-scalars homology transport is natural in
the derived-category object. -/
private theorem restrictScalarsDerivedHomologyIso_public_naturality_expanded
    {U V : Type u}
    [CommRing U] [CommRing V] [Algebra U V]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat V)}
    (f : K ⟶ L) :
    let res : ModuleCat V ⥤ ModuleCat U := ModuleCat.restrictScalars (algebraMap U V)
    let HU := DerivedCategory.homologyFunctor (ModuleCat U)
    let HV := DerivedCategory.homologyFunctor (ModuleCat V)
    let K' := DerivedCategory.Q.objPreimage K
    let L' := DerivedCategory.Q.objPreimage L
    let FK := (res.mapHomologicalComplex (up ℤ)).obj K'
    let FL := (res.mapHomologicalComplex (up ℤ)).obj L'
    let eK : (HV i).obj K ≅ K'.homology i :=
      ((HV i).mapIso (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat V) i).app K'
    let eL : (HV i).obj L ≅ L'.homology i :=
      ((HV i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat V) i).app L'
    (HU i).map (res.mapDerivedCategory.map f) ≫
        ((HU i).mapIso
          ((((res.mapDerivedCategory).mapIso
              (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
            (res.mapDerivedCategoryFactors.app L')))).hom ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FL).hom ≫
        ((L'.sc i).mapHomologyIso res).hom ≫
        (res.mapIso eL.symm).hom =
        ((HU i).mapIso
          ((((res.mapDerivedCategory).mapIso
              (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
            (res.mapDerivedCategoryFactors.app K')))).hom ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FK).hom ≫
        ((K'.sc i).mapHomologyIso res).hom ≫
        (res.mapIso eK.symm).hom ≫
        res.map ((HV i).map f) := by
  let res : ModuleCat V ⥤ ModuleCat U := ModuleCat.restrictScalars (algebraMap U V)
  let HU := DerivedCategory.homologyFunctor (ModuleCat U)
  let HV := DerivedCategory.homologyFunctor (ModuleCat V)
  let K' := DerivedCategory.Q.objPreimage K
  let L' := DerivedCategory.Q.objPreimage L
  let FK := (res.mapHomologicalComplex (up ℤ)).obj K'
  let FL := (res.mapHomologicalComplex (up ℤ)).obj L'
  let eK : (HV i).obj K ≅ K'.homology i :=
    ((HV i).mapIso (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat V) i).app K'
  let eL : (HV i).obj L ≅ L'.homology i :=
    ((HV i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat V) i).app L'
  -- Route correction: package the transported morphism by `DerivedCategory.right_fac` directly at
  -- the `Q.objPreimage` level, rather than via raw localization fractions.
  obtain ⟨Y, σ, hσ, β, hroof⟩ :=
    exists_quasi_iso_fraction_to_preimage
      (V := V) (K₀ := DerivedCategory.Q.objPreimage K)
      (L := L) ((DerivedCategory.Q.objObjPreimageIso K).hom ≫ f)
  let eY : DerivedCategory.Q.obj Y ≅ K :=
    (asIso (DerivedCategory.Q.map σ)) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have hβ :
      DerivedCategory.Q.map β =
        eY.hom ≫ f ≫ (DerivedCategory.Q.objObjPreimageIso L).inv := by
    -- The chosen roof already has the representative shape needed downstream.
    apply (cancel_mono (DerivedCategory.Q.objObjPreimageIso L).hom).1
    simpa [eY, Category.assoc] using hroof.symm
  have hrepr :=
    restrictScalarsDerivedHomologyIso_public_naturality_of_representative
      (U := U) (V := V) (i := i) (f := f) (eY := eY) (β := β) hβ
  have hs :
      DerivedCategory.Q.map σ =
        eY.hom ≫ 𝟙 K ≫ (DerivedCategory.Q.objObjPreimageIso K).inv := by
    -- The denominator itself is the chosen source isomorphism `Q.obj Y ≅ K`.
    simp [eY, Category.assoc]
  have hsource_cancel :=
    restrictScalarsDerivedHomologyIso_public_naturality_of_representative
      (U := U) (V := V) (i := i) (K := K) (L := K) (f := 𝟙 K)
      (Y := Y) (eY := eY) (β := σ) hs
  -- Cancel the denominator by comparing the representative source transport against the
  -- canonical `Q.objPreimage K` transport through the identity morphism of `K`.
  calc
    (HU i).map (res.mapDerivedCategory.map f) ≫
        ((HU i).mapIso
          ((((res.mapDerivedCategory).mapIso
              (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
            (res.mapDerivedCategoryFactors.app L')))).hom ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FL).hom ≫
        ((L'.sc i).mapHomologyIso res).hom ≫
        (res.mapIso eL.symm).hom =
      ((HU i).mapIso
          ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
            (res.mapDerivedCategoryFactors.app Y)))).hom ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app
          ((res.mapHomologicalComplex (up ℤ)).obj Y)).hom ≫
        ((Y.sc i).mapHomologyIso res).hom ≫
        (res.mapIso
          ((((HV i).mapIso eY).symm ≪≫
            (DerivedCategory.homologyFunctorFactors (ModuleCat V) i).app Y)).symm).hom ≫
        res.map ((HV i).map f) := by
        simpa [Category.assoc] using hrepr
    _ =
      ((HU i).mapIso
          ((((res.mapDerivedCategory).mapIso
              (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
            (res.mapDerivedCategoryFactors.app K')))).hom ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat U) i).app FK).hom ≫
        ((K'.sc i).mapHomologyIso res).hom ≫
        (res.mapIso eK.symm).hom ≫
        res.map ((HV i).map f) := by
        -- The identity-case representative theorem shows that the displayed source transport is
        -- exactly the canonical `Q.objPreimage K` transport.
        simpa [Category.assoc, Functor.map_id, eY] using
          congrArg (fun k ↦ k ≫ res.map ((HV i).map f)) hsource_cancel.symm

/-- Helper for Lemma 15.61.5: the public restriction-of-scalars homology transport is natural in
the derived-category object. -/
private theorem restrictScalarsDerivedHomologyIso_public_naturality
    {U V : Type u}
    [CommRing U] [CommRing V] [Algebra U V]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat V)}
    (f : K ⟶ L) :
    (DerivedCategory.homologyFunctor (ModuleCat U) i).map
        (((ModuleCat.restrictScalars (algebraMap U V)).mapDerivedCategory).map f) ≫
        (restrictScalarsDerivedHomologyIso_public (U := U) (V := V) L i).hom =
        (restrictScalarsDerivedHomologyIso_public (U := U) (V := V) K i).hom ≫
          (ModuleCat.restrictScalars (algebraMap U V)).map
            ((DerivedCategory.homologyFunctor (ModuleCat V) i).map f) := by
  -- Route correction: this is the single public transport-naturality frontier that replaces the
  -- old private-name blocker from `Lemma_15_60_3`. The real remaining work is now isolated in
  -- the expanded transport square above.
  simpa [restrictScalarsDerivedHomologyIso_public, Category.assoc, Iso.trans_hom,
    Functor.mapIso_hom] using
    (restrictScalarsDerivedHomologyIso_public_naturality_expanded
      (U := U) (V := V) (i := i) (f := f))

/-- Helper for Lemma 15.61.5: postcomposing the homology image of the derived adjunction-unit
naturality square preserves the equality used in the comparison proof. -/
private theorem derived_adjunction_unit_homology_naturality_postcompose
    {U V : Type u}
    [CommRing U] [CommRing V] [Algebra U V]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat U)}
    (f : K ⟶ L)
    (g :
      (DerivedCategory.homologyFunctor (ModuleCat U) i).obj
          (((ModuleCat.restrictScalars (algebraMap U V)).mapDerivedCategory).obj
            ((derivedTensorWithAlgebra (algebraMap U V)).obj L)) ⟶
        (ModuleCat.restrictScalars (algebraMap U V)).obj
          ((DerivedCategory.homologyFunctor (ModuleCat V) i).obj
            ((derivedTensorWithAlgebra (algebraMap U V)).obj L))) :
    let HU := DerivedCategory.homologyFunctor (ModuleCat U) i
    let η := (derivedTensorWithAlgebraAdjunction (R := U) (A := V)).unit
    HU.map f ≫ HU.map (η.app L) ≫ g =
      HU.map (η.app K) ≫
        HU.map
          (((ModuleCat.restrictScalars (algebraMap U V)).mapDerivedCategory).map
            ((derivedTensorWithAlgebra (algebraMap U V)).map f)) ≫
          g := by
  let HU := DerivedCategory.homologyFunctor (ModuleCat U) i
  let η := (derivedTensorWithAlgebraAdjunction (R := U) (A := V)).unit
  have hη :
      HU.map f ≫ HU.map (η.app L) =
        HU.map (η.app K) ≫
          HU.map
            (((ModuleCat.restrictScalars (algebraMap U V)).mapDerivedCategory).map
              ((derivedTensorWithAlgebra (algebraMap U V)).map f)) := by
    -- Naturality of the derived adjunction unit moves the source morphism across the unit.
    simpa [HU, Functor.map_comp] using
      congrArg (fun h ↦ HU.map h) (η.naturality f)
  -- Postcompose the unit square by the later transport morphism and reassociate once.
  simpa [HU, η, Category.assoc] using congrArg (fun h ↦ h ≫ g) hη

/-- Helper for Lemma 15.61.5: the canonical homology comparison is natural in the source
derived-category object. -/
private theorem derivedTensorWithAlgebraHomologyComparison_naturality
    {U V : Type u}
    [CommRing U] [CommRing V] [Algebra U V]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat U)}
    (f : K ⟶ L) :
    (ModuleCat.extendScalars (algebraMap U V)).map
        ((DerivedCategory.homologyFunctor (ModuleCat U) i).map f) ≫
      derivedTensorWithAlgebraHomologyComparison V L i =
        derivedTensorWithAlgebraHomologyComparison V K i ≫
          (DerivedCategory.homologyFunctor (ModuleCat V) i).map
            ((derivedTensorWithAlgebra (algebraMap U V)).map f) := by
  let HU := DerivedCategory.homologyFunctor (ModuleCat U) i
  let η := (derivedTensorWithAlgebraAdjunction (R := U) (A := V)).unit
  -- Apply the module adjunction hom-set equivalence; after rewriting both sides to the public
  -- adjoint model, only the public transport naturality square remains.
  refine ((ModuleCat.extendRestrictScalarsAdj (algebraMap U V)).homEquiv _ _).injective ?_
  rw [CategoryTheory.Adjunction.homEquiv_naturality_left]
  rw [CategoryTheory.Adjunction.homEquiv_naturality_right]
  rw [derivedTensorWithAlgebraHomologyComparison_adjoint_public_eq
    (U := U) (V := V) (K := L) (i := i)]
  rw [derivedTensorWithAlgebraHomologyComparison_adjoint_public_eq
    (U := U) (V := V) (K := K) (i := i)]
  calc
    HU.map f ≫ HU.map (η.app L) ≫
        (restrictScalarsDerivedHomologyIso_public
          (U := U) (V := V)
          ((derivedTensorWithAlgebra (algebraMap U V)).obj L) i).hom =
      HU.map (η.app K) ≫
          HU.map
            (((ModuleCat.restrictScalars (algebraMap U V)).mapDerivedCategory).map
              ((derivedTensorWithAlgebra (algebraMap U V)).map f)) ≫
        (restrictScalarsDerivedHomologyIso_public
          (U := U) (V := V)
          ((derivedTensorWithAlgebra (algebraMap U V)).obj L) i).hom := by
        simpa using
          (derived_adjunction_unit_homology_naturality_postcompose
            (U := U) (V := V) (i := i) (f := f)
            (g := (restrictScalarsDerivedHomologyIso_public
              (U := U) (V := V)
              ((derivedTensorWithAlgebra (algebraMap U V)).obj L) i).hom))
    _ = HU.map (η.app K) ≫
          ((restrictScalarsDerivedHomologyIso_public
              (U := U) (V := V)
              ((derivedTensorWithAlgebra (algebraMap U V)).obj K) i).hom ≫
            (ModuleCat.restrictScalars (algebraMap U V)).map
              ((DerivedCategory.homologyFunctor (ModuleCat V) i).map
                ((derivedTensorWithAlgebra (algebraMap U V)).map f))) := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ HU.map (η.app K) ≫ k)
            (restrictScalarsDerivedHomologyIso_public_naturality
              (U := U) (V := V) (i := i)
              (f := (derivedTensorWithAlgebra (algebraMap U V)).map f))
    _ = HU.map (η.app K) ≫
          (restrictScalarsDerivedHomologyIso_public
            (U := U) (V := V)
            ((derivedTensorWithAlgebra (algebraMap U V)).obj K) i).hom ≫
          (ModuleCat.restrictScalars (algebraMap U V)).map
            ((DerivedCategory.homologyFunctor (ModuleCat V) i).map
              ((derivedTensorWithAlgebra (algebraMap U V)).map f)) := by
        simp [Category.assoc]

/-- Helper for Lemma 15.61.5: whiskering the forward map of `leftDerivedNatIso` by the
localization functor and then composing with the target counit recovers the original
prederived comparison morphism. -/
private theorem Functor.leftDerivedNatIso_hom_assoc_totalLeftDerivedCounit
    {C D H : Type*} [Category C] [Category D] [Category H]
    {L : C ⥤ D} {W : MorphismProperty C} [L.IsLocalization W]
    {F F' : C ⥤ H} {LF LF' : D ⥤ H}
    {α : L ⋙ LF ⟶ F} {α' : L ⋙ LF' ⟶ F'}
    [LF.IsLeftDerivedFunctor α W] [LF'.IsLeftDerivedFunctor α' W]
    (e : F' ≅ F) :
    Functor.whiskerLeft L (Functor.leftDerivedNatIso LF' LF α' α W e).hom ≫ α =
      α' ≫ e.hom := by
  -- Expand `leftDerivedNatIso` to the underlying `leftDerivedNatTrans`, then use the defining
  -- left-derived factorization identity.
  simpa [Functor.leftDerivedNatIso] using
    (Functor.leftDerivedNatTrans_fac LF' LF α' α W e.hom)

/-- Helper for Lemma 15.61.5: for a flat scalar extension, the owner homology comparison agrees
with the already named flat homology isomorphism. -/
private theorem flat_derived_tensor_homology_iso_hom
    {U V : Type u}
    [CommRing U] [CommRing V] [Algebra U V] [Module.Flat U V]
    (K : DerivedCategory (ModuleCat U)) (i : ℤ) :
    (flat_derived_tensor_homology_iso (U := U) (V := V) K i).hom =
      (flat_extend_scalars_homology_iso (U := U) (V := V) K i).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat V) i).map
          ((flat_extend_scalars_mapDerivedCategory_iso (U := U) (V := V)).app K).hom := by
  -- Unfold the explicit flat homology isomorphism into its exact-extension part followed by the
  -- comparison from exact flat extension to the owner derived functor.
  simp [flat_derived_tensor_homology_iso, Category.assoc]

/-- Helper for Lemma 15.61.5: under the ordinary module adjunction, the explicit flat homology
isomorphism transposes to the exact adjunction unit followed by restriction of scalars applied to
its defining composite. -/
private theorem flat_derived_tensor_homology_iso_adjoint_public_eq
    {U V : Type u}
    [CommRing U] [CommRing V] [Algebra U V] [Module.Flat U V]
    (K : DerivedCategory (ModuleCat U)) (i : ℤ) :
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap U V)).homEquiv _ _)
        ((flat_derived_tensor_homology_iso (U := U) (V := V) K i).hom) =
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap U V)).unit.app
          ((DerivedCategory.homologyFunctor (ModuleCat U) i).obj K) ≫
        (ModuleCat.restrictScalars (algebraMap U V)).map
          (flat_extend_scalars_homology_iso (U := U) (V := V) K i).hom) ≫
        (ModuleCat.restrictScalars (algebraMap U V)).map
          ((DerivedCategory.homologyFunctor (ModuleCat V) i).map
            ((flat_extend_scalars_mapDerivedCategory_iso (U := U) (V := V)).app K).hom) := by
  -- Rewrite the hom-set transpose by `Adjunction.homEquiv_unit`, then expand the explicit flat
  -- homology isomorphism into its exact and derived comparison pieces.
  rw [flat_derived_tensor_homology_iso_hom (U := U) (V := V) (K := K) (i := i)]
  rw [CategoryTheory.Adjunction.homEquiv_unit]
  simp [Functor.map_comp, Category.assoc]

/-- Helper for Lemma 15.61.5: for a flat scalar extension, the owner homology comparison agrees
with the already named flat homology isomorphism. -/
private theorem flat_derived_tensor_homology_comparison_adjoint_bridge
    {U V : Type u}
    [CommRing U] [CommRing V] [Algebra U V] [Module.Flat U V]
    (K : DerivedCategory (ModuleCat U)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat U) i).map
        ((derivedTensorWithAlgebraAdjunction (R := U) (A := V)).unit.app K) ≫
      (restrictScalarsDerivedHomologyIso_public
        (U := U) (V := V)
        ((derivedTensorWithAlgebra (algebraMap U V)).obj K) i).hom =
        ((ModuleCat.extendRestrictScalarsAdj (algebraMap U V)).unit.app
            ((DerivedCategory.homologyFunctor (ModuleCat U) i).obj K) ≫
          (ModuleCat.restrictScalars (algebraMap U V)).map
            (flat_extend_scalars_homology_iso (U := U) (V := V) K i).hom) ≫
          (ModuleCat.restrictScalars (algebraMap U V)).map
            ((DerivedCategory.homologyFunctor (ModuleCat V) i).map
              ((flat_extend_scalars_mapDerivedCategory_iso (U := U) (V := V)).app K).hom) := by
  -- Route correction: the remaining flat comparison is now a public adjoint-side identity, no
  -- longer phrased through imported private transports.
  have htarget :
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap U V)).homEquiv _ _)
          ((flat_derived_tensor_homology_iso (U := U) (V := V) K i).hom) =
        ((ModuleCat.extendRestrictScalarsAdj (algebraMap U V)).unit.app
            ((DerivedCategory.homologyFunctor (ModuleCat U) i).obj K) ≫
          (ModuleCat.restrictScalars (algebraMap U V)).map
            (flat_extend_scalars_homology_iso (U := U) (V := V) K i).hom) ≫
          (ModuleCat.restrictScalars (algebraMap U V)).map
            ((DerivedCategory.homologyFunctor (ModuleCat V) i).map
              ((flat_extend_scalars_mapDerivedCategory_iso (U := U) (V := V)).app K).hom) := by
    -- The right-hand side is already the ordinary module-adjunction transpose of the explicit
    -- flat homology isomorphism.
    simpa using
      (flat_derived_tensor_homology_iso_adjoint_public_eq
        (U := U) (V := V) (K := K) (i := i))
  -- TODO(Lemma 15.61.5): compare the two sides by unfolding
  -- `restrictScalarsDerivedHomologyIso_public`, and use `Adjunction.derivedη_fac_app` on a
  -- chosen `Q.objPreimage K` to identify the left-hand side with the same transpose `htarget`.
  -- The remaining blocker is this derived-unit identification; the exact adjunction side is now
  -- isolated in the proved helper `flat_derived_tensor_homology_iso_adjoint_public_eq`.
  sorry

/-- Helper for Lemma 15.61.5: for a flat scalar extension, the owner homology comparison agrees
with the already named flat homology isomorphism. -/
private theorem flat_derived_tensor_homology_comparison_eq
    {U V : Type u}
    [CommRing U] [CommRing V] [Algebra U V] [Module.Flat U V]
    (K : DerivedCategory (ModuleCat U)) (i : ℤ) :
    derivedTensorWithAlgebraHomologyComparison V K i =
      (flat_derived_tensor_homology_iso (U := U) (V := V) K i).hom := by
  -- Compare both morphisms after applying the ordinary scalar-extension/restriction hom-set
  -- equivalence for `U → V`.
  refine ((ModuleCat.extendRestrictScalarsAdj (algebraMap U V)).homEquiv _ _).injective ?_
  rw [derivedTensorWithAlgebraHomologyComparison_adjoint_public_eq
    (U := U) (V := V) (K := K) (i := i)]
  rw [flat_derived_tensor_homology_iso]
  -- On the derived side, rewrite the final comparison by the naturality of the derived adjunction
  -- and then unfold the exact flat scalar-extension model.
  change _ =
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap U V)).homEquiv _ _)
      ((flat_extend_scalars_homology_iso (U := U) (V := V) K i).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat V) i).map
          ((flat_extend_scalars_mapDerivedCategory_iso (U := U) (V := V)).app K).hom)
  rw [CategoryTheory.Adjunction.homEquiv_naturality_right]
  rw [CategoryTheory.Adjunction.homEquiv_unit]
  -- The remaining comparison is exactly the public adjoint bridge isolated above.
  simpa [Category.assoc] using
    (flat_derived_tensor_homology_comparison_adjoint_bridge
      (U := U) (V := V) (K := K) (i := i))

/-- Helper for Lemma 15.61.5: for any flat scalar extension, the owner homology comparison is an
isomorphism because it rewrites to the hom of the explicit flat homology isomorphism. -/
private theorem derivedTensorWithAlgebraHomologyComparison_isIso_of_flat
    {U V : Type u}
    [CommRing U] [CommRing V] [Algebra U V] [Module.Flat U V]
    (K : DerivedCategory (ModuleCat U)) (i : ℤ) :
    IsIso (derivedTensorWithAlgebraHomologyComparison V K i) := by
  -- Rewrite the owner comparison to the explicit flat homology isomorphism for `U → V`.
  rw [flat_derived_tensor_homology_comparison_eq (U := U) (V := V) (K := K) (i := i)]
  infer_instance

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
    IsIso (derivedTensorWithAlgebraHomologyComparison T (M ⊗[A]^L[S]) i) := by
  letI : Algebra S T := (baseChangeProductMap bMap).toAlgebra
  letI : Module.Flat S T :=
    baseChangeProductMap_flat
      (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B')
      bMap haFlat hbFlat
  -- Route correction: once the two normalized flat steps are packaged into flatness of the
  -- direct map `S → T`, the owner flat-comparison theorem closes the target statement directly.
  simpa using
    (derivedTensorWithAlgebraHomologyComparison_isIso_of_flat
      (U := S) (V := T) (K := (M ⊗[A]^L[S])) (i := i))

end

end CategoryTheory
