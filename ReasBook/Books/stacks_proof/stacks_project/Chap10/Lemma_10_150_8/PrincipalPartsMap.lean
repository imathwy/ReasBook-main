import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_133_1
import stacks_proof.stacks_project.Chap10.Lemma_10_133_9
import stacks_proof.stacks_project.Chap10.Lemma_10_150_7

open scoped PrincipalParts TensorProduct
open LinearMap

universe u

noncomputable section

section

variable {A B A' B' M M' : Type u}
variable [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
variable [Algebra A B] [Algebra A A'] [Algebra A B'] [Algebra A' B'] [Algebra B B']
variable [IsScalarTower A B B'] [IsScalarTower A A' B']
variable [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
variable [AddCommGroup M'] [Module B' M'] [Module A M'] [Module A' M'] [Module B M']
variable [IsScalarTower A' B' M'] [IsScalarTower B B' M'] [IsScalarTower A A' M']
variable [IsScalarTower A B M']
variable [SMulCommClass B' A M'] [SMulCommClass B' A' M']
variable [SMulCommClass B A M'] [SMulCommClass B' B M']

/-- Helper for Lemma 10.150.8: the universal principal-parts map is a differential operator of
the declared order. -/
private theorem principalPartsUniversalDifferential_isDifferentialOperatorOfOrder
    (k : ℕ) :
    (principal_parts_universal_differential
      (R := A') (S := B') (M := M') k).IsDifferentialOperatorOfOrder B' k := by
  let e := principal_parts_linear_map_equiv_differential_operators A' B' M' k
    (P^{k}_{B'⁄A'}(M'))
  have hId :
      LinearMap.IsDifferentialOperatorOfOrder
        (((e (LinearMap.id : P^{k}_{B'⁄A'}(M') →ₗ[B'] P^{k}_{B'⁄A'}(M'))) :
          differential_operators_order_le A' B' M' k (P^{k}_{B'⁄A'}(M'))).1) B' k := by
    change
      (((e (LinearMap.id : P^{k}_{B'⁄A'}(M') →ₗ[B'] P^{k}_{B'⁄A'}(M'))) :
          differential_operators_order_le A' B' M' k (P^{k}_{B'⁄A'}(M'))).1) ∈
        differential_operators_order_le_submodule A' B' M' k (P^{k}_{B'⁄A'}(M'))
    exact
      ((e (LinearMap.id : P^{k}_{B'⁄A'}(M') →ₗ[B'] P^{k}_{B'⁄A'}(M'))) :
        differential_operators_order_le A' B' M' k (P^{k}_{B'⁄A'}(M'))).2
  simpa [e] using hId

/-- Helper for Lemma 10.150.8: restricting the linearity ring does not change a differential
operator order bound. -/
private theorem restrictScalars_isDifferentialOperatorOfOrder
    {X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
    [Module B' X] [Module A' X] [Module A X]
    [IsScalarTower A A' X] [IsScalarTower A' B' X]
    [SMulCommClass B' A X] [SMulCommClass B' A' X]
    [Module B' Y] [Module A' Y] [Module A Y]
    [IsScalarTower A A' Y] [IsScalarTower A' B' Y]
    [SMulCommClass B' A Y] [SMulCommClass B' A' Y]
    {D : X →ₗ[A'] Y} {k : ℕ}
    (hD : D.IsDifferentialOperatorOfOrder B' k) :
    (D.restrictScalars A).IsDifferentialOperatorOfOrder B' k := by
  induction k generalizing X Y D with
  | zero =>
      rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff] at hD ⊢
      exact hD
  | succ k ih =>
      rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff] at hD ⊢
      intro b
      simpa [LinearMap.scalarCommutator] using
        (ih (D := D.scalarCommutator b) (hD b))

/-- Helper for Lemma 10.150.8: a differential-operator order bound over `B'` restricts along
`B → B'`. -/
private theorem isDifferentialOperatorOfOrder_restrictAlongAlgebraMap
    {X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
    [Module B' X] [Module A X] [Module B X]
    [SMulCommClass B A X] [SMulCommClass B' A X] [IsScalarTower B B' X]
    [Module B' Y] [Module A Y] [Module B Y]
    [SMulCommClass B A Y] [SMulCommClass B' A Y] [IsScalarTower B B' Y]
    {D : X →ₗ[A] Y} {k : ℕ}
    (hD : D.IsDifferentialOperatorOfOrder B' k) :
    D.IsDifferentialOperatorOfOrder B k := by
  induction k generalizing X Y D with
  | zero =>
      rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff] at hD ⊢
      intro b x
      simpa using hD (algebraMap B B' b) x
  | succ k ih =>
      rw [LinearMap.isDifferentialOperatorOfOrder_succ_iff] at hD ⊢
      intro b
      have hcomm :
          D.scalarCommutator (S := B) b =
            D.scalarCommutator (S := B') (algebraMap B B' b) := by
        ext x
        simp [LinearMap.scalarCommutator_apply]
      rw [hcomm]
      exact ih (D := D.scalarCommutator (S := B') (algebraMap B B' b))
        (hD (algebraMap B B' b))

/-- Helper for Lemma 10.150.8: the target universal differential viewed as an `A`-linear map. -/
private def principalPartsBaseChangeTargetMap (k : ℕ) :
    M' →ₗ[A] P^{k}_{B'⁄A'}(M') :=
  (principal_parts_universal_differential (R := A') (S := B') (M := M') k).restrictScalars A

/-- Helper for Lemma 10.150.8: precomposing the target universal differential with a `B`-linear
map gives an order-`k` differential operator over `B`. -/
private theorem principalPartsBaseChangeDifferentialOperator_mem
    (k : ℕ) (f : M →ₗ[B] M') :
    ((principalPartsBaseChangeTargetMap (A := A) (A' := A') (B' := B') (M' := M') k).comp
        (f.restrictScalars A)).IsDifferentialOperatorOfOrder B k := by
  have htargetB' :
      (principalPartsBaseChangeTargetMap
        (A := A) (A' := A') (B' := B') (M' := M') k).IsDifferentialOperatorOfOrder B' k := by
    exact restrictScalars_isDifferentialOperatorOfOrder
      (A := A) (A' := A') (B' := B')
      (D := principal_parts_universal_differential (R := A') (S := B') (M := M') k)
      (principalPartsUniversalDifferential_isDifferentialOperatorOfOrder
        (A' := A') (B' := B') (M' := M') k)
  have htarget :
      (principalPartsBaseChangeTargetMap
        (A := A) (A' := A') (B' := B') (M' := M') k).IsDifferentialOperatorOfOrder B k := by
    exact isDifferentialOperatorOfOrder_restrictAlongAlgebraMap
      (A := A) (B := B) (B' := B')
      (D := principalPartsBaseChangeTargetMap (A := A) (A' := A') (B' := B') (M' := M') k)
      htargetB'
  have hsource : (f.restrictScalars A).IsDifferentialOperatorOfOrder B 0 := by
    rw [LinearMap.isDifferentialOperatorOfOrder_zero_iff]
    intro b m
    simpa using f.map_smul b m
  simpa using LinearMap.isDifferentialOperatorOfOrder_comp hsource htarget

/-- Helper for Lemma 10.150.8: the principal-parts map induced by a module map over a
commutative square of rings. -/
@[stacks 09CP]
noncomputable def principalPartsBaseChangeMap (k : ℕ) (f : M →ₗ[B] M') :
    P^{k}_{B⁄A}(M) →ₗ[B] P^{k}_{B'⁄A'}(M') :=
  (principal_parts_linear_map_equiv_differential_operators A B M k (P^{k}_{B'⁄A'}(M'))).symm
    ⟨(principalPartsBaseChangeTargetMap
        (A := A) (A' := A') (B' := B') (M' := M') k).comp (f.restrictScalars A),
      principalPartsBaseChangeDifferentialOperator_mem
        (A := A) (B := B) (A' := A') (B' := B') (M := M) (M' := M') k f⟩

/-- Helper for Lemma 10.150.8: evaluating the linear map corresponding to a differential operator
on the universal class recovers the operator value. -/
private theorem principal_parts_linear_map_equiv_symm_apply_universal_differential'
    {Q : Type u} [AddCommGroup Q] [Module B Q] [Module A Q] [IsScalarTower A B Q]
    (k : ℕ) (D : differential_operators_order_le A B M k Q) (m : M) :
    (principal_parts_linear_map_equiv_differential_operators A B M k Q).symm D
      (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) = D.1 m := by
  let e := principal_parts_linear_map_equiv_differential_operators A B M k Q
  have h : (e (e.symm D)).1 m = D.1 m := by
    simpa using
      congrArg (fun E : differential_operators_order_le A B M k Q ↦ E.1 m)
        (e.apply_symm_apply D)
  change (e (e.symm D)).1 m = D.1 m
  exact h

/-- Helper for Lemma 10.150.8: the principal-parts base-change map sends a universal class to the
universal class of the image. -/
theorem principalPartsBaseChangeMap_universal_differential
    (k : ℕ) (f : M →ₗ[B] M') (m : M) :
    principalPartsBaseChangeMap (A := A) (B := B) (A' := A') (B' := B') (M := M) (M' := M') k f
        (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) =
      principal_parts_universal_differential (R := A') (S := B') (M := M') k (f m) := by
  simpa [principalPartsBaseChangeMap, principalPartsBaseChangeTargetMap] using
    principal_parts_linear_map_equiv_symm_apply_universal_differential'
      (A := A) (B := B) (M := M) (Q := P^{k}_{B'⁄A'}(M')) k
      (D := ⟨(principalPartsBaseChangeTargetMap
          (A := A) (A' := A') (B' := B') (M' := M') k).comp (f.restrictScalars A),
        principalPartsBaseChangeDifferentialOperator_mem
          (A := A) (B := B) (A' := A') (B' := B') (M := M) (M' := M') k f⟩) m

end
