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

-- Proof sketch: check both composites on the generators `LocalizedModule.mk m s` of the localized
-- module; the universal property of `TensorAlgebra` then upgrades the generator computation to an
-- equality of algebra morphisms.
/-- The tensor-algebra localization map followed by its base-change inverse is the identity. -/
private theorem localizedTensorAlgebraToBaseChange_comp_tensorAlgebraBaseChangeToLocalized :
    (localizedTensorAlgebraToBaseChange S).comp
        (tensorAlgebraBaseChangeToLocalized S) =
      AlgHom.id (Localization S) (Localization S ⊗[R] TensorAlgebra R M) := sorry

-- Proof sketch: check both composites on the generators `m : M` of `TensorAlgebra R M`, then use
-- the universal property of the tensor algebra together with the tensor-product universal property.
/-- The tensor-algebra base-change map followed by its localization inverse is the identity. -/
private theorem tensorAlgebraBaseChangeToLocalized_comp_localizedTensorAlgebraToBaseChange :
    (tensorAlgebraBaseChangeToLocalized S).comp
        (localizedTensorAlgebraToBaseChange S) =
      AlgHom.id (Localization S) (TensorAlgebra (Localization S) (LocalizedModule S M)) := sorry

/-- Lemma 10.13.6 (1): localizing the tensor algebra of `M` at `S` is canonically the same as the
tensor algebra of the localized module `LocalizedModule S M` over `Localization S`. -/
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
          Localization S ⊗[R] TensorAlgebra R M) := sorry

-- Proof sketch: unfold `localizedTensorAlgebraEquiv` to the forward algebra homomorphism built by
-- `TensorAlgebra.lift`, then evaluate that lift on the generator `x`.
/-- The localization/base-change equivalence for tensor algebras sends a localized generator to the
corresponding base-changed generator. -/
@[simp] theorem localizedTensorAlgebraEquiv_apply_ι (x : LocalizedModule S M) :
    localizedTensorAlgebraEquiv S (TensorAlgebra.ι (Localization S) x) =
      ((TensorAlgebra.ι R).baseChange (Localization S)) ((equivTensorProduct S M) x) := sorry

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
      AlgHom.id (Localization S) (Localization S ⊗[R] SymmetricAlgebra R M) := sorry

-- Proof sketch: compare the two maps on the generators `m : M`, then use the universal property
-- of the symmetric algebra and the tensor-product universal property.
/-- The symmetric-algebra base-change map followed by its localization inverse is the identity. -/
private theorem symmetricAlgebraBaseChangeToLocalized_comp_localizedSymmetricAlgebraToBaseChange :
    (symmetricAlgebraBaseChangeToLocalized S).comp
        (localizedSymmetricAlgebraToBaseChange S) =
      AlgHom.id (Localization S) (SymmetricAlgebra (Localization S) (LocalizedModule S M)) := sorry

/-- Lemma 10.13.6 (2): localizing the symmetric algebra of `M` at `S` is canonically the same as
the symmetric algebra of the localized module `LocalizedModule S M` over `Localization S`. -/
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
          Localization S ⊗[R] SymmetricAlgebra R M) := sorry

-- Proof sketch: unfold `localizedSymmetricAlgebraEquiv` to the forward lift from the universal
-- property of `SymmetricAlgebra`, then evaluate it on the generator `x`.
/-- The localization/base-change equivalence for symmetric algebras sends a localized generator to
the corresponding base-changed generator. -/
@[simp] theorem localizedSymmetricAlgebraEquiv_apply_ι (x : LocalizedModule S M) :
    localizedSymmetricAlgebraEquiv S
        (SymmetricAlgebra.ι (Localization S) (LocalizedModule S M) x) =
      ((SymmetricAlgebra.ι R M).baseChange (Localization S)) ((equivTensorProduct S M) x) := sorry

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
      0 := sorry

private noncomputable def exteriorAlgebraToLocalized :
    ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra (Localization S) (LocalizedModule S M) :=
  ExteriorAlgebra.lift R
    ⟨(((ExteriorAlgebra.ι (Localization S)).restrictScalars R) ∘ₗ mkLinearMap S M),
      fun m ↦ by
        change
          ExteriorAlgebra.ι (Localization S) (mkLinearMap S M m) *
              ExteriorAlgebra.ι (Localization S) (mkLinearMap S M m) =
            0
        simp⟩

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
      AlgHom.id (Localization S) (Localization S ⊗[R] ExteriorAlgebra R M) := sorry

-- Proof sketch: compare the two maps on `m : M`, then appeal to the universal property of the
-- exterior algebra together with the tensor-product universal property.
/-- The exterior-algebra base-change map followed by its localization inverse is the identity. -/
private theorem exteriorAlgebraBaseChangeToLocalized_comp_localizedExteriorAlgebraToBaseChange :
    ((exteriorAlgebraBaseChangeToLocalized S :
        Localization S ⊗[R] ExteriorAlgebra R M →ₐ[Localization S]
          ExteriorAlgebra (Localization S) (LocalizedModule S M))).comp
        (localizedExteriorAlgebraToBaseChange S) =
      AlgHom.id (Localization S) (ExteriorAlgebra (Localization S) (LocalizedModule S M)) := sorry

/-- Lemma 10.13.6 (3): localizing the exterior algebra of `M` at `S` is canonically the same as
the exterior algebra of the localized module `LocalizedModule S M` over `Localization S`. -/
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
          Localization S ⊗[R] ExteriorAlgebra R M) := sorry

-- Proof sketch: unfold `localizedExteriorAlgebraEquiv` to the forward square-zero lift and
-- evaluate it on the generator `x` using the universal property of `ExteriorAlgebra`.
/-- The localization/base-change equivalence for exterior algebras sends a localized generator to
the corresponding base-changed generator. -/
@[simp] theorem localizedExteriorAlgebraEquiv_apply_ι (x : LocalizedModule S M) :
    localizedExteriorAlgebraEquiv S (ExteriorAlgebra.ι (Localization S) x) =
      ((ExteriorAlgebra.ι R).baseChange (Localization S)) ((equivTensorProduct S M) x) := sorry

end ExteriorLocalization
