import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.LinearAlgebra.PowerOperations

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

section SymmetricPowerBridge

variable (R : Type) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

open SymmetricPower

private theorem reindex_rel {ι ι' : Type} (e : ι ≃ ι') {x y : ⨂[R] (_ : ι), M}
    (h : addConGen (Rel R ι M) x y) :
    addConGen (Rel R ι' M)
      (PiTensorProduct.reindex R (fun _ ↦ M) e x)
      (PiTensorProduct.reindex R (fun _ ↦ M) e y) := by
  induction h with
  | of _ _ h =>
      cases h with
      | perm σ f =>
          simpa [Function.comp_def] using
            (AddConGen.Rel.of _ _
              (Rel.perm ((e.symm.trans σ).trans e) (fun i ↦ f (e.symm i))))
  | refl => exact AddCon.refl _ _
  | symm hxy ih => exact AddCon.symm _ ih
  | trans hxy hyz ihxy ihyz => exact AddCon.trans _ ihxy ihyz
  | add hxy hyz ihxy ihyz =>
      simpa using AddCon.add (addConGen (Rel R ι' M)) ihxy ihyz

private noncomputable def reindexLinearEquiv {ι ι' : Type} (e : ι ≃ ι') :
    Sym[R] ι M ≃ₗ[R] Sym[R] ι' M :=
  LinearEquiv.ofLinear
    { __ :=
        AddCon.lift _
          ((SymmetricPower.mk R ι' M).toAddMonoidHom.comp
            (PiTensorProduct.reindex R (fun _ ↦ M) e).toLinearMap.toAddMonoidHom)
          (fun x y h ↦ Quotient.sound (reindex_rel R M e h))
      map_smul' r q := by
        refine AddCon.induction_on q ?_
        intro x
        change SymmetricPower.mk R ι' M
            (PiTensorProduct.reindex R (fun _ ↦ M) e (r • x)) =
          SymmetricPower.smul' ι' M r
            (SymmetricPower.mk R ι' M (PiTensorProduct.reindex R (fun _ ↦ M) e x))
        rw [show SymmetricPower.smul' ι' M r
            (SymmetricPower.mk R ι' M (PiTensorProduct.reindex R (fun _ ↦ M) e x)) =
              SymmetricPower.mk R ι' M
                (r • PiTensorProduct.reindex R (fun _ ↦ M) e x) by
                  rfl]
        simp }
    { __ :=
        AddCon.lift _
          ((SymmetricPower.mk R ι M).toAddMonoidHom.comp
            (PiTensorProduct.reindex R (fun _ ↦ M) e.symm).toLinearMap.toAddMonoidHom)
          (fun x y h ↦ Quotient.sound (reindex_rel R M e.symm h))
      map_smul' r q := by
        refine AddCon.induction_on q ?_
        intro x
        change SymmetricPower.mk R ι M
            (PiTensorProduct.reindex R (fun _ ↦ M) e.symm (r • x)) =
          SymmetricPower.smul' ι M r
            (SymmetricPower.mk R ι M (PiTensorProduct.reindex R (fun _ ↦ M) e.symm x))
        rw [show SymmetricPower.smul' ι M r
            (SymmetricPower.mk R ι M (PiTensorProduct.reindex R (fun _ ↦ M) e.symm x)) =
              SymmetricPower.mk R ι M
                (r • PiTensorProduct.reindex R (fun _ ↦ M) e.symm x) by
                  rfl]
        simp }
    (by
      ext q
      refine AddCon.induction_on q ?_
      intro x
      simpa using
        congrArg (SymmetricPower.mk R ι' M) (PiTensorProduct.reindex_reindex e.symm e x))
    (by
      ext q
      refine AddCon.induction_on q ?_
      intro x
      simpa using
        congrArg (SymmetricPower.mk R ι M) (PiTensorProduct.reindex_reindex e e.symm x))

/- Lemma 10.13.1 (1): this is a `bridge/view` statement. The core owner theorem is the
universe-polymorphic project instance `SymmetricPower.instFree`; reindexing along
`Equiv.ulift : SymmetricPower.UFin n ≃ Fin n` presents the same result on the canonical
textbook surface `Sym[R]^n M`. -/
instance symmetricPower_instFree [Module.Free R M] (n : ℕ) :
    Module.Free R (Sym[R]^n M) := by
  let eι : SymmetricPower.UFin n ≃ Fin n := Equiv.ulift
  let e : Sym[R] (SymmetricPower.UFin n) M ≃ₗ[R] Sym[R]^n M :=
    reindexLinearEquiv R M eι
  exact Module.Free.of_equiv' (SymmetricPower.instFree n) e

end SymmetricPowerBridge

section

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/- Lemma 10.13.1 (2): if a module `M` is free over `R`, then every exterior power `⋀[R]^n M`
is a free `R`-module. This is the canonical mathlib owner instance `exteriorPower.instFree`. -/
recall exteriorPower.instFree

end
