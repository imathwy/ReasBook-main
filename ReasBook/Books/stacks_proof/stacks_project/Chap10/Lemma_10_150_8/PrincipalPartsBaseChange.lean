import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_133_1
import stacks_proof.stacks_project.Chap10.Lemma_10_133_9
import stacks_proof.stacks_project.Chap10.Lemma_10_150_7
import stacks_proof.stacks_project.Chap10.Lemma_10_150_8.PrincipalPartsMap

open scoped PrincipalParts TensorProduct
open LinearMap
open TensorProduct.AlgebraTensorModule

universe u

noncomputable section

section

variable {R S S' M N X : Type u}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

open scoped PrincipalParts

section HelperLemmas

variable {Q : Type u}
variable [AddCommGroup Q] [Module S Q] [Module R Q] [IsScalarTower R S Q]

/-- Helper for Lemma 10.150.8: evaluating the linear map corresponding to a differential operator
on the universal principal-parts class recovers the underlying operator value. -/
theorem principal_parts_linear_map_equiv_symm_apply_universal_differential
    (k : ℕ) (D : differential_operators_order_le R S M k Q) (m : M) :
    (principal_parts_linear_map_equiv_differential_operators R S M k Q).symm D
      (principal_parts_universal_differential (R := R) (S := S) (M := M) k m) = D.1 m := by
  let e := principal_parts_linear_map_equiv_differential_operators R S M k Q
  -- Evaluate the identity `e (e.symm D) = D` at `m`.
  have h : (e (e.symm D)).1 m = D.1 m := by
    simpa using
      congrArg (fun E : differential_operators_order_le R S M k Q ↦ E.1 m)
        (e.apply_symm_apply D)
  change (e (e.symm D)).1 m = D.1 m
  exact h

/-- Helper for Lemma 10.150.8: evaluating the differential operator represented by a linear map
out of principal parts amounts to evaluating that linear map on the universal class. -/
theorem principal_parts_linear_map_equiv_apply_universal_differential
    (k : ℕ) (L : P^{k}_{S⁄R}(M) →ₗ[S] Q) (m : M) :
    ((principal_parts_linear_map_equiv_differential_operators R S M k Q L).1 m) =
      L (principal_parts_universal_differential (R := R) (S := S) (M := M) k m) := by
  let e := principal_parts_linear_map_equiv_differential_operators R S M k Q
  -- Reduce the forward evaluation formula to the inverse-direction formula above.
  simpa [e] using
    (principal_parts_linear_map_equiv_symm_apply_universal_differential
      (R := R) (S := S) (M := M) (Q := Q) k (D := e L) m).symm

/-- Helper for Lemma 10.150.8: a linear map out of principal parts is determined by its values on
the universal differential classes. -/
theorem principal_parts_linear_map_eq_of_apply_universal_differential_eq
    (k : ℕ) {L₁ L₂ : P^{k}_{S⁄R}(M) →ₗ[S] Q}
    (h : ∀ m : M,
      L₁ (principal_parts_universal_differential (R := R) (S := S) (M := M) k m) =
        L₂ (principal_parts_universal_differential (R := R) (S := S) (M := M) k m)) :
    L₁ = L₂ := by
  let e := principal_parts_linear_map_equiv_differential_operators R S M k Q
  -- The representing equivalence turns equality on universal classes into equality of
  -- differential operators.
  apply e.injective
  ext m
  simpa [principal_parts_linear_map_equiv_apply_universal_differential] using h m

end HelperLemmas

/-- Helper for Lemma 10.150.8: the canonical principal-parts base-change map sends the universal
class `[m]` to the universal class of the image of `m`. -/
theorem principalPartsBaseChangeMap_apply_universal_differential
    (k : ℕ) (m : M) :
    (principalPartsBaseChangeMap k (mk S S' S' M (1 : S')) :
        P^{k}_{S⁄R}(M) →ₗ[S] P^{k}_{S'⁄R}(S' ⊗[S] M))
      (principal_parts_universal_differential (R := R) (S := S) (M := M) k m) =
        principal_parts_universal_differential (R := R) (S := S') (M := S' ⊗[S] M) k
          ((mk S S' S' M (1 : S')) m) := by
  exact principalPartsBaseChangeMap_universal_differential
    (A := R) (B := S) (A' := R) (B' := S') (M := M) (M' := S' ⊗[S] M) k
    (mk S S' S' M (1 : S')) m

/-- Helper for Lemma 10.150.8: after lifting the canonical principal-parts comparison along
`S → S'`, the generator `1 ⊗ [m]` maps to the target universal class of `1 ⊗ m`. -/
theorem principalPartsFormallyEtaleBaseChangeMap_apply_tmul_universal_differential
    (k : ℕ) (m : M) :
    (((principalPartsBaseChangeMap k (mk S S' S' M (1 : S'))).liftBaseChange S') :
        S' ⊗[S] P^{k}_{S⁄R}(M) →ₗ[S'] P^{k}_{S'⁄R}(S' ⊗[S] M))
      ((1 : S') ⊗ₜ[S]
        principal_parts_universal_differential (R := R) (S := S) (M := M) k m) =
      principal_parts_universal_differential (R := R) (S := S') (M := S' ⊗[S] M) k
        ((mk S S' S' M (1 : S')) m) := by
  -- Evaluate the lifted map on the distinguished tensor generator.
  rw [LinearMap.liftBaseChange_tmul]
  rw [one_smul]
  exact principalPartsBaseChangeMap_apply_universal_differential
    (R := R) (S := S) (S' := S') (M := M) k m

section TensorExtensionality

variable {Q : Type u}
variable [AddCommGroup Q] [Module S' Q] [Module S Q] [Module R Q]
variable [IsScalarTower S S' Q] [IsScalarTower R S Q] [IsScalarTower R S' Q]

/-- Helper for Lemma 10.150.8: an `S'`-linear map out of `S' ⊗[S] P^k_{S/R}(M)` is determined by
its values on the tensors `1 ⊗ [m]`. -/
theorem tensor_principal_parts_linear_map_eq_of_apply_tmul_universal_differential_eq
    (k : ℕ)
    {L₁ L₂ : S' ⊗[S] P^{k}_{S⁄R}(M) →ₗ[S'] Q}
    (h : ∀ m : M,
      L₁ ((1 : S') ⊗ₜ[S]
        principal_parts_universal_differential (R := R) (S := S) (M := M) k m) =
        L₂ ((1 : S') ⊗ₜ[S]
          principal_parts_universal_differential (R := R) (S := S) (M := M) k m)) :
    L₁ = L₂ := by
  let K₁ : P^{k}_{S⁄R}(M) →ₗ[S] Q :=
    { toFun := fun p ↦ L₁ ((1 : S') ⊗ₜ[S] p)
      map_add' := by
        intro p q
        rw [TensorProduct.tmul_add, map_add]
      map_smul' := by
        intro s p
        -- Rewrite `s ⊗ p` as `(algebraMap S S' s) • (1 ⊗ p)` and use `S'`-linearity.
        calc
          L₁ ((1 : S') ⊗ₜ[S] (s • p)) = L₁ (((algebraMap S S' s : S') • ((1 : S') ⊗ₜ[S] p))) := by
            congr 1
            simpa [TensorProduct.smul_tmul', smul_eq_mul]
          _ = (algebraMap S S' s : S') • L₁ ((1 : S') ⊗ₜ[S] p) := by
            rw [map_smul]
          _ = s • L₁ ((1 : S') ⊗ₜ[S] p) := by
            simpa using
              (IsScalarTower.algebraMap_smul S S' s (L₁ ((1 : S') ⊗ₜ[S] p))) }
  let K₂ : P^{k}_{S⁄R}(M) →ₗ[S] Q :=
    { toFun := fun p ↦ L₂ ((1 : S') ⊗ₜ[S] p)
      map_add' := by
        intro p q
        rw [TensorProduct.tmul_add, map_add]
      map_smul' := by
        intro s p
        -- The same tensor-scalar rewrite gives the `S`-linearity of `K₂`.
        calc
          L₂ ((1 : S') ⊗ₜ[S] (s • p)) = L₂ (((algebraMap S S' s : S') • ((1 : S') ⊗ₜ[S] p))) := by
            congr 1
            simpa [TensorProduct.smul_tmul', smul_eq_mul]
          _ = (algebraMap S S' s : S') • L₂ ((1 : S') ⊗ₜ[S] p) := by
            rw [map_smul]
          _ = s • L₂ ((1 : S') ⊗ₜ[S] p) := by
            simpa using
              (IsScalarTower.algebraMap_smul S S' s (L₂ ((1 : S') ⊗ₜ[S] p))) }
  have hK : K₁ = K₂ := by
    -- Collapse the comparison to the source principal-parts module and use source extensionality.
    apply principal_parts_linear_map_eq_of_apply_universal_differential_eq
      (R := R) (S := S) (M := M) (Q := Q) k
    intro m
    simpa [K₁, K₂] using h m
  -- Once the restrictions agree on `1 ⊗ p`, tensor induction lifts that equality to all tensors.
  apply DFunLike.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro a p
    calc
      L₁ (a ⊗ₜ[S] p) = a • L₁ ((1 : S') ⊗ₜ[S] p) := by
        rw [show (a ⊗ₜ[S] p : S' ⊗[S] P^{k}_{S⁄R}(M)) = a • ((1 : S') ⊗ₜ[S] p) by
          simpa using (TensorProduct.tmul_eq_smul_one_tmul (R := S) a p)]
        rw [map_smul]
      _ = a • K₁ p := by rfl
      _ = a • K₂ p := by rw [hK]
      _ = a • L₂ ((1 : S') ⊗ₜ[S] p) := by rfl
      _ = L₂ (a ⊗ₜ[S] p) := by
        rw [show (a ⊗ₜ[S] p : S' ⊗[S] P^{k}_{S⁄R}(M)) = a • ((1 : S') ⊗ₜ[S] p) by
          simpa using (TensorProduct.tmul_eq_smul_one_tmul (R := S) a p)]
        rw [map_smul]
  · intro x y hx hy
    simp [hx, hy]

end TensorExtensionality

end
