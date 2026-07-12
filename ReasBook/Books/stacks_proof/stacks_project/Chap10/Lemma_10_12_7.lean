import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open TensorProduct

universe u v w x y

section

variable {A : Type u} [CommRing A]
variable {B : Type v} [CommRing B]
variable {M : Type w} [AddCommGroup M] [Module A M]
variable {N : Type x} [AddCommGroup N] [Module A N] [Module B N] [SMulCommClass A B N]
variable {P : Type y} [AddCommGroup P] [Module B P]

/- Lemma 10.12.7 is `source-facing`: it records the induced scalar actions on
`M ⊗[A] N` and `N ⊗[B] P`, together with the canonical reassociation
`((M ⊗[A] N) ⊗[B] P) ≃ₗ[A] M ⊗[A] (N ⊗[B] P)`. The sampled owner abstractions in this domain are
`TensorProduct.leftModule`, `TensorProduct.smulCommClass_left`, `TensorProduct.assoc`, and
`TensorProduct.AlgebraTensorModule.assoc`. Mathlib does not currently expose this exact mixed-base
associator as a single owner declaration, so the file should export only the source-facing bridge
and keep the transported tensor-product instances internal. -/

@[stacks 00D2]
private noncomputable instance : Module B (M ⊗[A] N) :=
  AddEquiv.module B (TensorProduct.comm A M N).toAddEquiv

@[simp] private theorem leftTensorRight_smul_tmul (b : B) (m : M) (n : N) :
    b • (m ⊗ₜ[A] n : M ⊗[A] N) = m ⊗ₜ[A] (b • n) := by
  apply (TensorProduct.comm A M N).injective
  rfl

private instance : SMulCommClass A B (M ⊗[A] N) where
  smul_comm a b x := by
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro m n
      rw [leftTensorRight_smul_tmul, smul_tmul']
      change (a • m) ⊗ₜ[A] (b • n) = b • ((a • m) ⊗ₜ[A] n)
      rw [leftTensorRight_smul_tmul]
    · intro x y hx hy
      simp [hx, hy, smul_add]

private instance : SMulCommClass B A (M ⊗[A] N) :=
  SMulCommClass.symm A B (M ⊗[A] N)

private instance : Module A (N ⊗[B] P) := by
  letI : SMulCommClass B A N := SMulCommClass.symm A B N
  infer_instance

@[simp] private theorem rightTensorLeft_smul_tmul (a : A) (n : N) (p : P) :
    a • (n ⊗ₜ[B] p : N ⊗[B] P) = (a • n) ⊗ₜ[B] p := by
  letI : SMulCommClass B A N := SMulCommClass.symm A B N
  simpa using (smul_tmul' a n p : a • (n ⊗ₜ[B] p : N ⊗[B] P) = (a • n) ⊗ₜ[B] p)

private noncomputable def assocCurry :
    M ⊗[A] N →+ P →+ M ⊗[A] (N ⊗[B] P) :=
  liftAddHom
    { toFun := fun m ↦
        { toFun := fun n ↦
            { toFun := fun p ↦ m ⊗ₜ[A] (n ⊗ₜ[B] p)
              map_zero' := by simp
              map_add' := by
                intro p q
                simp [tmul_add] }
          map_zero' := by
            ext p
            simp
          map_add' := by
            intro n n'
            ext p
            simp [add_tmul, tmul_add] }
      map_zero' := by
        ext n p
        simp
      map_add' := by
        intro m m'
        ext n p
        simp [add_tmul] }
    (fun a m n ↦ by
      ext p
      simp [smul_tmul, rightTensorLeft_smul_tmul])

@[simp]
private theorem assocCurry_tmul (m : M) (n : N) (p : P) :
    assocCurry (m ⊗ₜ[A] n) p = m ⊗ₜ[A] (n ⊗ₜ[B] p) :=
  rfl

private noncomputable def assocHom :
    ((M ⊗[A] N) ⊗[B] P) →+ M ⊗[A] (N ⊗[B] P) :=
  liftAddHom assocCurry
    (fun b x p ↦ by
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · simp
      · intro m n
        change m ⊗ₜ[A] ((b • n) ⊗ₜ[B] p) = m ⊗ₜ[A] (n ⊗ₜ[B] (b • p))
        congr 1
        exact smul_tmul b n p
      · intro x y hx hy
        simp [hx, hy])

@[simp]
private theorem assocHom_tmul (m : M) (n : N) (p : P) :
    assocHom ((m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] p) = m ⊗ₜ[A] (n ⊗ₜ[B] p) :=
  rfl

private theorem assocHom_map_smul (a : A) (x : ((M ⊗[A] N) ⊗[B] P)) :
    assocHom (a • x) = a • assocHom x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro y p
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp
    · intro m n
      simp [assocHom_tmul]
    · intro y z hy hz
      have hy' : assocHom ((a • y) ⊗ₜ[B] p) = a • assocHom (y ⊗ₜ[B] p) := by
        simpa [smul_tmul'] using hy
      have hz' : assocHom ((a • z) ⊗ₜ[B] p) = a • assocHom (z ⊗ₜ[B] p) := by
        simpa [smul_tmul'] using hz
      rw [smul_tmul', smul_add, add_tmul, AddMonoidHom.map_add, hy', hz']
      rw [add_tmul, AddMonoidHom.map_add, smul_add]
  · intro x y hx hy
    rw [smul_add, AddMonoidHom.map_add, hx, hy, AddMonoidHom.map_add, smul_add]

private noncomputable def assocLinearMap :
    ((M ⊗[A] N) ⊗[B] P) →ₗ[A] M ⊗[A] (N ⊗[B] P) where
  toFun := assocHom
  map_add' := assocHom.map_add
  map_smul' := assocHom_map_smul

private noncomputable def assocInvCurry :
    M →+ (N ⊗[B] P) →+ ((M ⊗[A] N) ⊗[B] P) :=
  { toFun := fun m ↦
      liftAddHom
        { toFun := fun n ↦
            { toFun := fun p ↦ (m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] p
              map_zero' := by simp
              map_add' := by
                intro p q
                simp [tmul_add] }
          map_zero' := by
            ext p
            simp
          map_add' := by
            intro n n'
            ext p
            simp [tmul_add, add_tmul] }
        (fun b n p ↦ by
          change ((m ⊗ₜ[A] (b • n) : M ⊗[A] N) ⊗ₜ[B] p) =
              ((m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] (b • p))
          rw [← leftTensorRight_smul_tmul, smul_tmul])
    map_zero' := by
      ext x
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · simp
      · intro n p
        simp
      · intro x y hx hy
        rw [AddMonoidHom.map_add, hx, hy]
        simp
    map_add' := by
      intro m m'
      ext x
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · simp
      · intro n p
        simp [add_tmul]
      · intro x y hx hy
        rw [AddMonoidHom.map_add, AddMonoidHom.map_add, hx, hy] }

@[simp]
private theorem assocInvCurry_tmul (m : M) (n : N) (p : P) :
    assocInvCurry m (n ⊗ₜ[B] p) = ((m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] p) :=
  rfl

private noncomputable def assocInvHom :
    M ⊗[A] (N ⊗[B] P) →+ ((M ⊗[A] N) ⊗[B] P) :=
  liftAddHom assocInvCurry
    (fun a m x ↦ by
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · simp
      · intro n p
        rw [rightTensorLeft_smul_tmul, assocInvCurry_tmul, assocInvCurry_tmul]
        rw [smul_tmul]
      · intro x y hx hy
        simp [hx, hy])

@[simp]
private theorem assocInvHom_tmul (m : M) (n : N) (p : P) :
    assocInvHom (m ⊗ₜ[A] (n ⊗ₜ[B] p)) = ((m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] p) := by
  change assocInvCurry m (n ⊗ₜ[B] p) = ((m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] p)
  rw [assocInvCurry_tmul]

private theorem assocInvHom_map_smul (a : A) (x : M ⊗[A] (N ⊗[B] P)) :
    assocInvHom (a • x) = a • assocInvHom x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro m y
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp
    · intro n p
      simp [assocInvHom_tmul]
    · intro y z hy hz
      rw [tmul_add, smul_add, AddMonoidHom.map_add, hy, hz, AddMonoidHom.map_add, smul_add]
  · intro x y hx hy
    rw [smul_add, AddMonoidHom.map_add, hx, hy, AddMonoidHom.map_add, smul_add]

private noncomputable def assocInvLinearMap :
    M ⊗[A] (N ⊗[B] P) →ₗ[A] ((M ⊗[A] N) ⊗[B] P) where
  toFun := assocInvHom
  map_add' := assocInvHom.map_add
  map_smul' := assocInvHom_map_smul

/-- Lemma 10.12.7: tensoring an `(A, B)`-bimodule on the left by an `A`-module and on the right by
a `B`-module is associative up to a canonical `A`-linear equivalence. -/
@[stacks 00D2]
noncomputable def tensorBimoduleAssoc :
    ((M ⊗[A] N) ⊗[B] P) ≃ₗ[A] M ⊗[A] (N ⊗[B] P) where
  toLinearMap := assocLinearMap
  invFun := assocInvLinearMap
  left_inv x := by
    change assocInvHom (assocHom x) = x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro y p
      refine TensorProduct.induction_on y ?_ ?_ ?_
      · simp
      · intro m n
        simp
      · intro y z hy hz
        rw [add_tmul, AddMonoidHom.map_add, AddMonoidHom.map_add, hy, hz]
    · intro x y hx hy
      rw [AddMonoidHom.map_add, AddMonoidHom.map_add, hx, hy]
  right_inv x := by
    change assocHom (assocInvHom x) = x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro m y
      refine TensorProduct.induction_on y ?_ ?_ ?_
      · simp
      · intro n p
        simp
      · intro y z hy hz
        rw [tmul_add, AddMonoidHom.map_add, AddMonoidHom.map_add, hy, hz]
    · intro x y hx hy
      rw [AddMonoidHom.map_add, AddMonoidHom.map_add, hx, hy]

@[simp]
theorem tensorBimoduleAssoc_tmul (m : M) (n : N) (p : P) :
    tensorBimoduleAssoc ((m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] p) = m ⊗ₜ[A] (n ⊗ₜ[B] p) :=
  rfl

@[simp]
theorem tensorBimoduleAssoc_symm_tmul (m : M) (n : N) (p : P) :
    tensorBimoduleAssoc.symm (m ⊗ₜ[A] (n ⊗ₜ[B] p)) = ((m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] p) :=
  assocInvHom_tmul m n p

end
