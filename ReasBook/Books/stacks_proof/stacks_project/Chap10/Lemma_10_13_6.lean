import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open LocalizedModule

universe u v w

section TensorSymmetricLocalization

variable {R : Type u} [CommSemiring R]
variable (S : Submonoid R)
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-
Lemma 10.13.6 (1) and (2) are `bridge/view` items. Their owner abstractions are the universal
properties of `TensorAlgebra` and `SymmetricAlgebra`, together with the canonical
localization/base-change equivalence `equivTensorProduct`.
-/

@[stacks 0C6F]
private noncomputable def tensorAlgebraToLocalized :
    TensorAlgebra R M →ₐ[R] TensorAlgebra (Localization S) (LocalizedModule S M) :=
  TensorAlgebra.lift R
    (((TensorAlgebra.ι (Localization S)).restrictScalars R) ∘ₗ mkLinearMap S M)

private noncomputable def localizedTensorAlgebraToBaseChange :
    TensorAlgebra (Localization S) (LocalizedModule S M) →ₐ[Localization S]
      Localization S ⊗[R] TensorAlgebra R M :=
  TensorAlgebra.lift (Localization S)
    (((TensorAlgebra.ι R).baseChange (Localization S)) ∘ₗ
      (equivTensorProduct S M).toLinearMap)

private noncomputable def tensorAlgebraBaseChangeToLocalized :
    Localization S ⊗[R] TensorAlgebra R M →ₐ[Localization S]
      TensorAlgebra (Localization S) (LocalizedModule S M) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (tensorAlgebraToLocalized S)
    (fun _ _ ↦ Algebra.commutes _ _)

/-- Helper for Lemma 10.13.6: base change sends the localized generator `m / s` to the
corresponding pure tensor in the tensor product. -/
private theorem baseChange_apply_equivTensorProduct_mk
    {N : Type w} [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (m : M) (s : S) :
    (f.baseChange (Localization S)) ((equivTensorProduct S M) (LocalizedModule.mk m s)) =
      Localization.mk (1 : R) s ⊗ₜ[R] f m := by
  -- Normalize the localized generator before applying any algebra lift.
  rw [LocalizedModule.equivTensorProduct_apply_mk, LinearMap.baseChange_tmul]

-- Proof sketch: check both composites on the generators `LocalizedModule.mk m s` of the localized
-- module; the universal property of `TensorAlgebra` then upgrades the generator computation to an
-- equality of algebra morphisms.
/-- The tensor-algebra localization map followed by its base-change inverse is the identity. -/
private theorem localizedTensorAlgebraToBaseChange_comp_tensorAlgebraBaseChangeToLocalized :
    (localizedTensorAlgebraToBaseChange S).comp
        (tensorAlgebraBaseChangeToLocalized S) =
      AlgHom.id (Localization S) (Localization S ⊗[R] TensorAlgebra R M) := by
  -- Route correction: normalize localized generators in the tensor product before invoking the
  -- tensor-algebra universal property.
  refine Algebra.TensorProduct.ext ?_ ?_
  · -- The scalar branch is preserved because both maps are algebra morphisms over `Localization S`.
    calc
      ((localizedTensorAlgebraToBaseChange S).comp (tensorAlgebraBaseChangeToLocalized S)).comp
          Algebra.TensorProduct.includeLeft
        = (localizedTensorAlgebraToBaseChange S).comp (Algebra.ofId _ _) := by
            rw [AlgHom.comp_assoc, tensorAlgebraBaseChangeToLocalized,
              Algebra.TensorProduct.lift_comp_includeLeft]
      _ = Algebra.TensorProduct.includeLeft := by
        apply AlgHom.ext
        intro a
        simp [localizedTensorAlgebraToBaseChange]
  · -- The tensor-algebra branch is determined by its values on the generators `m : M`.
    apply TensorAlgebra.hom_ext
    ext m
    simp [tensorAlgebraBaseChangeToLocalized, tensorAlgebraToLocalized,
      localizedTensorAlgebraToBaseChange, Localization.mk_one]

-- Proof sketch: check both composites on the generators `m : M` of `TensorAlgebra R M`, then use
-- the universal property of the tensor algebra together with the tensor-product universal property.
/-- The tensor-algebra base-change map followed by its localization inverse is the identity. -/
private theorem tensorAlgebraBaseChangeToLocalized_comp_localizedTensorAlgebraToBaseChange :
    (tensorAlgebraBaseChangeToLocalized S).comp
        (localizedTensorAlgebraToBaseChange S) =
      AlgHom.id (Localization S) (TensorAlgebra (Localization S) (LocalizedModule S M)) := by
  -- Route correction: reduce immediately to a representative `m / s` and simplify the scalar
  -- multiple before re-entering the tensor algebra.
  apply TensorAlgebra.hom_ext
  ext x
  obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M) x
  -- Rewrite the surjective representative to the canonical localized fraction `mk m s`.
  simp only [Function.uncurry_apply_pair]
  rw [← IsLocalizedModule.mk_eq_mk']
  -- The tensor-product normalization lemma reduces the composite to the scalar action on `mk m 1`.
  simp [tensorAlgebraBaseChangeToLocalized, tensorAlgebraToLocalized,
    localizedTensorAlgebraToBaseChange, baseChange_apply_equivTensorProduct_mk]
  rw [← Algebra.smul_def, ← LinearMap.map_smul]
  simpa [LocalizedModule.mk_smul_mk]

/-- Lemma 10.13.6 (1): localizing the tensor algebra of `M` at `S` is canonically the same as the
tensor algebra of the localized module `LocalizedModule S M` over `Localization S`. -/
@[stacks 0C6F]
noncomputable def localizedTensorAlgebraEquiv :
    TensorAlgebra (Localization S) (LocalizedModule S M) ≃ₐ[Localization S]
      Localization S ⊗[R] TensorAlgebra R M :=
  AlgEquiv.ofAlgHom
    (localizedTensorAlgebraToBaseChange S)
    (tensorAlgebraBaseChangeToLocalized S)
    (localizedTensorAlgebraToBaseChange_comp_tensorAlgebraBaseChangeToLocalized S)
    (tensorAlgebraBaseChangeToLocalized_comp_localizedTensorAlgebraToBaseChange S)

-- Proof sketch: every `AlgEquiv` is in particular a bijection of underlying functions, so apply
-- the standard `bijective` field of the equivalence defined above.
/-- The localization/base-change equivalence for tensor algebras is bijective on underlying
functions. -/
theorem localizedTensorAlgebraEquiv_bijective :
    Function.Bijective
      (localizedTensorAlgebraEquiv S :
        TensorAlgebra (Localization S) (LocalizedModule S M) →
          Localization S ⊗[R] TensorAlgebra R M) := by
  -- This is the underlying bijection of the algebra equivalence above.
  exact (localizedTensorAlgebraEquiv S).bijective

-- Proof sketch: unfold `localizedTensorAlgebraEquiv` to the forward algebra homomorphism built by
-- `TensorAlgebra.lift`, then evaluate that lift on the generator `x`.
/-- The localization/base-change equivalence for tensor algebras sends a localized generator to the
corresponding base-changed generator. -/
@[simp] theorem localizedTensorAlgebraEquiv_apply_ι (x : LocalizedModule S M) :
    localizedTensorAlgebraEquiv S (TensorAlgebra.ι (Localization S) x) =
      ((TensorAlgebra.ι R).baseChange (Localization S)) ((equivTensorProduct S M) x) := by
  -- Unfold the forward map and evaluate the tensor-algebra lift on the generator `x`.
  simp [localizedTensorAlgebraEquiv, localizedTensorAlgebraToBaseChange]

private noncomputable def symmetricAlgebraToLocalized :
    SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra (Localization S) (LocalizedModule S M) :=
  SymmetricAlgebra.lift
    (((SymmetricAlgebra.ι (Localization S) (LocalizedModule S M)).restrictScalars R) ∘ₗ
      mkLinearMap S M)

private noncomputable def localizedSymmetricAlgebraToBaseChange :
    SymmetricAlgebra (Localization S) (LocalizedModule S M) →ₐ[Localization S]
      Localization S ⊗[R] SymmetricAlgebra R M :=
  SymmetricAlgebra.lift
    (((SymmetricAlgebra.ι R M).baseChange (Localization S)) ∘ₗ
      (equivTensorProduct S M).toLinearMap)

private noncomputable def symmetricAlgebraBaseChangeToLocalized :
    Localization S ⊗[R] SymmetricAlgebra R M →ₐ[Localization S]
      SymmetricAlgebra (Localization S) (LocalizedModule S M) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (symmetricAlgebraToLocalized S)
    (fun _ _ ↦ Algebra.commutes _ _)

-- Proof sketch: compare the two maps on the generators `LocalizedModule.mk m s` and use the
-- universal property of the symmetric algebra to conclude equality of algebra morphisms.
/-- The symmetric-algebra localization map followed by its base-change inverse is the identity. -/
private theorem localizedSymmetricAlgebraToBaseChange_comp_symmetricAlgebraBaseChangeToLocalized :
    (localizedSymmetricAlgebraToBaseChange S).comp
        (symmetricAlgebraBaseChangeToLocalized S) =
      AlgHom.id (Localization S) (Localization S ⊗[R] SymmetricAlgebra R M) := by
  -- The same tensor-product normalization controls the symmetric-algebra generators as well.
  refine Algebra.TensorProduct.ext ?_ ?_
  · -- Scalars are fixed because the composite is an algebra endomorphism over `Localization S`.
    calc
      ((localizedSymmetricAlgebraToBaseChange S).comp (symmetricAlgebraBaseChangeToLocalized S)).comp
          Algebra.TensorProduct.includeLeft
        = (localizedSymmetricAlgebraToBaseChange S).comp (Algebra.ofId _ _) := by
            rw [AlgHom.comp_assoc, symmetricAlgebraBaseChangeToLocalized,
              Algebra.TensorProduct.lift_comp_includeLeft]
      _ = Algebra.TensorProduct.includeLeft := by
        apply AlgHom.ext
        intro a
        simp [localizedSymmetricAlgebraToBaseChange]
  · -- A symmetric-algebra morphism is determined by its restriction to the generators `m : M`.
    apply SymmetricAlgebra.algHom_ext
    ext m
    simp [symmetricAlgebraBaseChangeToLocalized, symmetricAlgebraToLocalized,
      localizedSymmetricAlgebraToBaseChange, Localization.mk_one]

-- Proof sketch: compare the two maps on the generators `m : M`, then use the universal property
-- of the symmetric algebra and the tensor-product universal property.
/-- The symmetric-algebra base-change map followed by its localization inverse is the identity. -/
private theorem symmetricAlgebraBaseChangeToLocalized_comp_localizedSymmetricAlgebraToBaseChange :
    (symmetricAlgebraBaseChangeToLocalized S).comp
        (localizedSymmetricAlgebraToBaseChange S) =
      AlgHom.id (Localization S) (SymmetricAlgebra (Localization S) (LocalizedModule S M)) := by
  -- Reduce to representatives `m / s` and transport the scalar action back to the localized
  -- module generator.
  apply SymmetricAlgebra.algHom_ext
  ext x
  obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M) x
  -- Rewrite the representative to the canonical localization element.
  simp only [Function.uncurry_apply_pair]
  rw [← IsLocalizedModule.mk_eq_mk']
  -- The normalized tensor-product image matches the expected scalar multiple of `mk m 1`.
  simp [symmetricAlgebraBaseChangeToLocalized, symmetricAlgebraToLocalized,
    localizedSymmetricAlgebraToBaseChange, baseChange_apply_equivTensorProduct_mk]
  rw [← Algebra.smul_def, ← LinearMap.map_smul]
  simpa [LocalizedModule.mk_smul_mk]

/-- Lemma 10.13.6 (2): localizing the symmetric algebra of `M` at `S` is canonically the same as
the symmetric algebra of the localized module `LocalizedModule S M` over `Localization S`. -/
@[stacks 0C6F]
noncomputable def localizedSymmetricAlgebraEquiv :
    SymmetricAlgebra (Localization S) (LocalizedModule S M) ≃ₐ[Localization S]
      Localization S ⊗[R] SymmetricAlgebra R M :=
  AlgEquiv.ofAlgHom
    (localizedSymmetricAlgebraToBaseChange S)
    (symmetricAlgebraBaseChangeToLocalized S)
    (localizedSymmetricAlgebraToBaseChange_comp_symmetricAlgebraBaseChangeToLocalized S)
    (symmetricAlgebraBaseChangeToLocalized_comp_localizedSymmetricAlgebraToBaseChange S)

-- Proof sketch: the underlying function of an algebra equivalence is bijective by the standard
-- equivalence API, so this follows from the `bijective` field of `localizedSymmetricAlgebraEquiv`.
/-- The localization/base-change equivalence for symmetric algebras is bijective on underlying
functions. -/
theorem localizedSymmetricAlgebraEquiv_bijective :
    Function.Bijective
      (localizedSymmetricAlgebraEquiv S :
        SymmetricAlgebra (Localization S) (LocalizedModule S M) →
          Localization S ⊗[R] SymmetricAlgebra R M) := by
  -- This is the underlying bijection of the algebra equivalence above.
  exact (localizedSymmetricAlgebraEquiv S).bijective

-- Proof sketch: unfold `localizedSymmetricAlgebraEquiv` to the forward lift from the universal
-- property of `SymmetricAlgebra`, then evaluate it on the generator `x`.
/-- The localization/base-change equivalence for symmetric algebras sends a localized generator to
the corresponding base-changed generator. -/
@[simp] theorem localizedSymmetricAlgebraEquiv_apply_ι (x : LocalizedModule S M) :
    localizedSymmetricAlgebraEquiv S
        (SymmetricAlgebra.ι (Localization S) (LocalizedModule S M) x) =
      ((SymmetricAlgebra.ι R M).baseChange (Localization S)) ((equivTensorProduct S M) x) := by
  -- Unfold the forward map and evaluate the symmetric-algebra lift on the generator `x`.
  simp [localizedSymmetricAlgebraEquiv, localizedSymmetricAlgebraToBaseChange]

end TensorSymmetricLocalization

section ExteriorLocalization

variable {R : Type u} [CommRing R]
variable (S : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Lemma 10.13.6 (3) is a `bridge/view` item. Its owner abstractions are the universal property
-- of `ExteriorAlgebra`, the canonical localization/base-change equivalence `equivTensorProduct`,
-- and, under the stronger hypothesis `[Invertible (2 : R)]`, the more general owner theorem
-- `CliffordAlgebra.equivBaseChange`, since `ExteriorAlgebra` is the zero-quadratic-form Clifford
-- algebra.

private instance exteriorAlgebraLocalized_isScalarTower :
    IsScalarTower R (Localization S) (ExteriorAlgebra (Localization S) (LocalizedModule S M)) :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

/-- Helper for Lemma 10.13.6: the canonical map from `M` into the exterior algebra of the
localized module has square-zero generators. -/
private theorem mkLinearMap_exterior_sq_zero (m : M) :
    ((((ExteriorAlgebra.ι (Localization S)).restrictScalars R) ∘ₗ mkLinearMap S M) m) *
      ((((ExteriorAlgebra.ι (Localization S)).restrictScalars R) ∘ₗ mkLinearMap S M) m) =
      0 := by
  -- The image is an exterior generator in the localized module, whose square is zero.
  simpa using
    (ExteriorAlgebra.ι_sq_zero (R := Localization S) (M := LocalizedModule S M)
      ((mkLinearMap S M) m))

-- Proof sketch: every localized element is represented by some `m / s`; its image is a scalar
-- multiple of `1 ⊗ ExteriorAlgebra.ι R m`, whose square vanishes because `ExteriorAlgebra.ι_sq_zero`
-- vanishes before base change.
/-- The localized-module map into the base-changed exterior algebra squares to zero on every
generator. -/
private theorem localizedModuleToBaseChange_exterior_sq_zero (x : LocalizedModule S M) :
    ((((ExteriorAlgebra.ι R).baseChange (Localization S)) ∘ₗ
        (equivTensorProduct S M).toLinearMap) x) *
      ((((ExteriorAlgebra.ι R).baseChange (Localization S)) ∘ₗ
          (equivTensorProduct S M).toLinearMap) x) =
      0 := by
  -- Reduce to a representative `m / s` so the tensor-product normalization lemma applies.
  obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M) x
  -- Rewrite the representative to the canonical localized fraction `mk m s`.
  simp only [Function.uncurry_apply_pair]
  rw [← IsLocalizedModule.mk_eq_mk']
  -- Keep the result as a pure tensor and annihilate the square in the exterior factor.
  simp [LinearMap.comp_apply, baseChange_apply_equivTensorProduct_mk,
    Algebra.TensorProduct.tmul_mul_tmul, ExteriorAlgebra.ι_sq_zero]

private noncomputable def exteriorAlgebraToLocalized :
    ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra (Localization S) (LocalizedModule S M) :=
  ExteriorAlgebra.lift R
    ⟨(((ExteriorAlgebra.ι (Localization S)).restrictScalars R) ∘ₗ mkLinearMap S M),
      mkLinearMap_exterior_sq_zero (S := S)⟩

private noncomputable def localizedExteriorAlgebraToBaseChange :
    ExteriorAlgebra (Localization S) (LocalizedModule S M) →ₐ[Localization S]
      Localization S ⊗[R] ExteriorAlgebra R M :=
  ExteriorAlgebra.lift (Localization S)
    ⟨(((ExteriorAlgebra.ι R).baseChange (Localization S)) ∘ₗ
        (equivTensorProduct S M).toLinearMap),
      localizedModuleToBaseChange_exterior_sq_zero S⟩

private noncomputable def exteriorAlgebraBaseChangeToLocalized :
    Localization S ⊗[R] ExteriorAlgebra R M →ₐ[Localization S]
      ExteriorAlgebra (Localization S) (LocalizedModule S M) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (exteriorAlgebraToLocalized S)
    (fun _ _ ↦ Algebra.commutes _ _)

-- Proof sketch: compare the two maps on the generators of the localized module and invoke the
-- exterior-algebra universal property, which is controlled by square-zero linear maps.
/-- The exterior-algebra localization map followed by its base-change inverse is the identity. -/
private theorem localizedExteriorAlgebraToBaseChange_comp_exteriorAlgebraBaseChangeToLocalized :
    ((localizedExteriorAlgebraToBaseChange S :
        ExteriorAlgebra (Localization S) (LocalizedModule S M) →ₐ[Localization S]
          Localization S ⊗[R] ExteriorAlgebra R M)).comp
        (exteriorAlgebraBaseChangeToLocalized S) =
      AlgHom.id (Localization S) (Localization S ⊗[R] ExteriorAlgebra R M) := by
  -- The exterior case follows the same tensor-product generator check.
  refine Algebra.TensorProduct.ext ?_ ?_
  · -- Scalars are fixed because the composite is an algebra endomorphism over `Localization S`.
    apply AlgHom.ext
    intro a
    simp [exteriorAlgebraBaseChangeToLocalized, localizedExteriorAlgebraToBaseChange]
  · -- Exterior-algebra maps are determined by the square-zero generators.
    apply ExteriorAlgebra.hom_ext
    ext m
    simp [exteriorAlgebraBaseChangeToLocalized, exteriorAlgebraToLocalized,
      localizedExteriorAlgebraToBaseChange, Localization.mk_one]

-- Proof sketch: compare the two maps on `m : M`, then appeal to the universal property of the
-- exterior algebra together with the tensor-product universal property.
/-- The exterior-algebra base-change map followed by its localization inverse is the identity. -/
private theorem exteriorAlgebraBaseChangeToLocalized_comp_localizedExteriorAlgebraToBaseChange :
    ((exteriorAlgebraBaseChangeToLocalized S :
        Localization S ⊗[R] ExteriorAlgebra R M →ₐ[Localization S]
          ExteriorAlgebra (Localization S) (LocalizedModule S M))).comp
        (localizedExteriorAlgebraToBaseChange S) =
      AlgHom.id (Localization S) (ExteriorAlgebra (Localization S) (LocalizedModule S M)) := by
  -- Reduce to representatives `m / s` and use the normalized tensor-product image.
  apply ExteriorAlgebra.hom_ext
  ext x
  obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M) x
  -- Rewrite the representative to the canonical localized fraction.
  simp only [Function.uncurry_apply_pair]
  rw [← IsLocalizedModule.mk_eq_mk']
  -- The scalar multiple of `mk m 1` is exactly the generator `mk m s`.
  simp [exteriorAlgebraBaseChangeToLocalized, exteriorAlgebraToLocalized,
    localizedExteriorAlgebraToBaseChange, baseChange_apply_equivTensorProduct_mk]
  rw [← Algebra.smul_def, ← LinearMap.map_smul]
  simpa [LocalizedModule.mk_smul_mk]

/-- Lemma 10.13.6 (3): localizing the exterior algebra of `M` at `S` is canonically the same as
the exterior algebra of the localized module `LocalizedModule S M` over `Localization S`. -/
@[stacks 0C6F]
noncomputable def localizedExteriorAlgebraEquiv :
    ExteriorAlgebra (Localization S) (LocalizedModule S M) ≃ₐ[Localization S]
      Localization S ⊗[R] ExteriorAlgebra R M :=
  AlgEquiv.ofAlgHom
    (localizedExteriorAlgebraToBaseChange S)
    (exteriorAlgebraBaseChangeToLocalized S)
    (localizedExteriorAlgebraToBaseChange_comp_exteriorAlgebraBaseChangeToLocalized S)
    (exteriorAlgebraBaseChangeToLocalized_comp_localizedExteriorAlgebraToBaseChange S)

-- Proof sketch: an algebra equivalence is a bijection of underlying functions; apply the standard
-- `bijective` field to `localizedExteriorAlgebraEquiv`.
/-- The localization/base-change equivalence for exterior algebras is bijective on underlying
functions. -/
theorem localizedExteriorAlgebraEquiv_bijective :
    Function.Bijective
      (localizedExteriorAlgebraEquiv S :
        ExteriorAlgebra (Localization S) (LocalizedModule S M) →
          Localization S ⊗[R] ExteriorAlgebra R M) := by
  -- This is the underlying bijection of the algebra equivalence above.
  exact (localizedExteriorAlgebraEquiv S).bijective

-- Proof sketch: unfold `localizedExteriorAlgebraEquiv` to the forward square-zero lift and
-- evaluate it on the generator `x` using the universal property of `ExteriorAlgebra`.
/-- The localization/base-change equivalence for exterior algebras sends a localized generator to
the corresponding base-changed generator. -/
@[simp] theorem localizedExteriorAlgebraEquiv_apply_ι (x : LocalizedModule S M) :
    localizedExteriorAlgebraEquiv S (ExteriorAlgebra.ι (Localization S) x) =
      ((ExteriorAlgebra.ι R).baseChange (Localization S)) ((equivTensorProduct S M) x) := by
  -- Unfold the forward map and evaluate the exterior-algebra lift on the generator `x`.
  simp [localizedExteriorAlgebraEquiv, localizedExteriorAlgebraToBaseChange]

end ExteriorLocalization
