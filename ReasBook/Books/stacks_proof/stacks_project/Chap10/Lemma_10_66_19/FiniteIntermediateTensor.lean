import stacks_proof.stacks_project.Chap10.Lemma_10_66_19.IntermediateOwnerDescent

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w x

section

variable {k : Type u} [Field k]
variable {R : Type w} [CommRing R] [Algebra k R]
variable {M : Type x} [AddCommGroup M] [Module R M]

/-- Helper for Lemma 10.66.19: tensoring the finite stage `R ⊗[k] F` along the intermediate-field
map `F → L` gives the canonical algebra `R ⊗[k] L`. -/
instance ringTensorIntermediateFieldAlgebra
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    Algebra (R ⊗[k] F) (R ⊗[k] L) :=
  (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k F L)).toAlgebra

/-- Helper for Lemma 10.66.19: the two tensor-factor maps out of `R` through
`R ⊗[k] F → R ⊗[k] L` agree with the direct map `R → R ⊗[k] L`. -/
instance ringTensorIntermediateFieldIsScalarTower
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    IsScalarTower R (R ⊗[k] F) (R ⊗[k] L) := by
  refine IsScalarTower.of_algebraMap_eq' (R := R) (S := R ⊗[k] F) (A := R ⊗[k] L) ?_
  ext r
  simp [RingHom.algebraMap_toAlgebra]

/-- Helper for Lemma 10.66.19: the right tensor-factor algebra structures on `R ⊗[k] F` and
`R ⊗[k] L` fit into the expected scalar tower over the intermediate field `F`. -/
instance ringTensorIntermediateFieldRightIsScalarTower
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    IsScalarTower F (R ⊗[k] F) (R ⊗[k] L) := by
  refine IsScalarTower.of_algebraMap_eq' (R := F) (S := R ⊗[k] F) (A := R ⊗[k] L) ?_
  ext a
  rfl

/-- Helper for Lemma 10.66.19: the `L`-stage owner module carries the restricted
`R ⊗[k] F`-module structure coming from the left tensor factor. -/
instance ringTensorIntermediateFieldOwnerModule
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    Module (R ⊗[k] F) (((R ⊗[k] L) ⊗[R] M)) :=
  Module.compHom _ (algebraMap (R ⊗[k] F) (R ⊗[k] L))

/-- Helper for Lemma 10.66.19: the restricted-scalar action on the `L`-stage owner module
commutes with the original `R ⊗[k] L`-action. -/
instance ringTensorIntermediateFieldOwnerIsScalarTower
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    IsScalarTower (R ⊗[k] F) (R ⊗[k] L) (((R ⊗[k] L) ⊗[R] M)) :=
  inferInstance

/-- Helper for Lemma 10.66.19: the literal owner base change from `F` to `L` also carries the
expected `R ⊗[k] F`-module structure via the left tensor factor. -/
instance ringTensorIntermediateFieldBaseChangeModule
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    Module (R ⊗[k] F)
      (((R ⊗[k] L) ⊗[(R ⊗[k] F)] (((R ⊗[k] F) ⊗[R] M)))) :=
  inferInstance

/-- Helper for Lemma 10.66.19: tensoring the finite field extension `F → L` with `R` produces a
finite `R ⊗[k] F`-module structure on `R ⊗[k] L`. -/
theorem ringTensorIntermediateField_moduleFinite
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) [FiniteDimensional F L] :
    Module.Finite (R ⊗[k] F) (R ⊗[k] L) := by
  have hId : (AlgHom.id k R).Finite := AlgHom.Finite.id k R
  have hField : (IsScalarTower.toAlgHom k F L).Finite := by
    have hFieldRing : (algebraMap F L).Finite := RingHom.finite_algebraMap.mpr inferInstance
    simpa [AlgHom.Finite, RingHom.algebraMap_toAlgebra] using hFieldRing
  have hTensor :
      (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k F L)).toRingHom.Finite := by
    simpa using
      (RingHom.Finite.tensorProductMap
        (R := k) (S := R) (S' := R) (T := F) (T' := L)
        (f := AlgHom.id k R) (g := IsScalarTower.toAlgHom k F L) hId hField)
  have hTensorAlg : (algebraMap (R ⊗[k] F) (R ⊗[k] L)).Finite := by
    simpa [ringTensorIntermediateFieldAlgebra, RingHom.algebraMap_toAlgebra] using hTensor
  exact RingHom.finite_algebraMap.mp hTensorAlg

/-- Helper for Lemma 10.66.19: after passing from the purely transcendental stage `F` to the
finite extension stage `L`, the owner base-change module is canonically the ordinary `L`-stage
owner module. -/
noncomputable def owner_baseChange_reassoc_over_intermediate_field
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    ((R ⊗[k] L) ⊗[(R ⊗[k] F)] (((R ⊗[k] F) ⊗[R] M))) ≃ₗ[(R ⊗[k] L)]
      (((R ⊗[k] L) ⊗[R] M)) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange
    R (R ⊗[k] F) (R ⊗[k] L) (R ⊗[k] L) M

/-- Helper for Lemma 10.66.19: the intermediate-field tensor comparison commutes with the
canonical algebra map from `R ⊗[k] F`. -/
theorem ringTensorIntermediateField_baseChange_algEquiv_commutes
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L)
    (x : R ⊗[k] F) :
    (Algebra.IsPushout.cancelBaseChangeAlg
        (R := k) (S := R) (A := F) (B := R ⊗[k] F) (C := L))
      (algebraMap (R ⊗[k] F) ((R ⊗[k] F) ⊗[F] L) x) =
        algebraMap (R ⊗[k] F) (R ⊗[k] L) x := by
  let e := Algebra.IsPushout.cancelBaseChangeAlg
    (R := k) (S := R) (A := F) (B := R ⊗[k] F) (C := L)
  have hsymm :
      e.symm (algebraMap (R ⊗[k] F) (R ⊗[k] L) x) =
        algebraMap (R ⊗[k] F) ((R ⊗[k] F) ⊗[F] L) x := by
    -- Proof comment: this is the pushout identity saying that the inverse comparison sends the
    -- standard left-tensor inclusion in `R ⊗[k] L` back to the literal base-change inclusion.
    simpa [e, RingHom.algebraMap_toAlgebra] using
      congr($(Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor
        (R := k) (S := R) (A := F) (C := L)) x)
  -- Proof comment: apply the forward equivalence to the inverse comparison identity.
  calc
    e (algebraMap (R ⊗[k] F) ((R ⊗[k] F) ⊗[F] L) x) =
        e (e.symm (algebraMap (R ⊗[k] F) (R ⊗[k] L) x)) := by
          rw [hsymm.symm]
    _ = algebraMap (R ⊗[k] F) (R ⊗[k] L) x := by
          simp [e]

/-- Helper for Lemma 10.66.19: the ring pushout description of `R ⊗[k] L` identifies the literal
base change `((R ⊗[k] F) ⊗[F] L)` with the usual tensor product over `k`. -/
noncomputable def ringTensorIntermediateField_baseChange_algEquiv
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    ((R ⊗[k] F) ⊗[F] L) ≃ₐ[(R ⊗[k] F)] (R ⊗[k] L) :=
  { __ := Algebra.IsPushout.cancelBaseChangeAlg
      (R := k) (S := R) (A := F) (B := R ⊗[k] F) (C := L)
    commutes' := ringTensorIntermediateField_baseChange_algEquiv_commutes
      (k := k) (R := R) (F := F) }

end
