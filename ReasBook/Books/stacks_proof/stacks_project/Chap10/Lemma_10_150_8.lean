import StacksProject_2024.Chap10.Definition_10_133_1
import StacksProject_2024.Chap10.Lemma_10_133_8
import StacksProject_2024.Chap10.Lemma_10_133_9
import StacksProject_2024.Chap10.Lemma_10_150_7
import StacksProject_2024.Chap10.Lemma_10_150_8.Index

-- Declarations for this item will be appended below by the statement pipeline.

open scoped PrincipalParts TensorProduct
open LinearMap
open TensorProduct.AlgebraTensorModule

universe u

noncomputable section

section

variable {R S S' M N : Type u}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- Chap10 Lemma 10 150 8 (1): if `S → S'` is formally étale and `M' = S' ⊗[S] M`, then the
canonical map `S' ⊗[S] P^k_{S/R}(M) → P^k_{S'/R}(M')` is bijective. -/
@[stacks 0H94]
theorem principalPartsFormallyEtaleBaseChangeMap_bijective [Algebra.FormallyEtale S S']
    (k : ℕ) :
    Function.Bijective
      (((principalPartsBaseChangeMap k (mk S S' S' M (1 : S'))).liftBaseChange S') :
        S' ⊗[S] P^{k}_{S⁄R}(M) →ₗ[S'] P^{k}_{S'⁄R}(S' ⊗[S] M)) := by
  -- Proof comment: this is the formally étale specialization of the earlier owner-level
  -- base-change theorem for principal parts.
  simpa [principalPartsTensorBaseChangeMap] using
    (principal_parts_module_base_change_bijective
      (A := R) (B := S) (A' := R) (B' := S') (M := M) k)

/-- If `D : M → N` is an order-`k` differential operator, then along a formally étale map
`S → S'` it extends uniquely to an order-`k` differential operator
`S' ⊗[S] M → S' ⊗[S] N`. -/
theorem existsUnique_baseChange_extension_of_isDifferentialOperatorOfOrder_of_formallyEtale
    [Algebra.FormallyEtale S S'] {D : M →ₗ[R] N} {k : ℕ}
    (hD : D.IsDifferentialOperatorOfOrder S k) :
    ∃! D' : S' ⊗[S] M →ₗ[R] S' ⊗[S] N,
      D'.comp ((mk S S' S' M (1 : S')).restrictScalars R) =
          ((mk S S' S' N (1 : S')).restrictScalars R).comp D ∧
        D'.IsDifferentialOperatorOfOrder S' k := by
  let f :
      S' ⊗[S] P^{k}_{S⁄R}(M) →ₗ[S'] P^{k}_{S'⁄R}(S' ⊗[S] M) :=
    ((principalPartsBaseChangeMap k (mk S S' S' M (1 : S'))).liftBaseChange S')
  let eComp :
      S' ⊗[S] P^{k}_{S⁄R}(M) ≃ₗ[S'] P^{k}_{S'⁄R}(S' ⊗[S] M) :=
    LinearEquiv.ofBijective f
      (principalPartsFormallyEtaleBaseChangeMap_bijective
        (R := R) (S := S) (S' := S') (M := M) k)
  let eSource := principal_parts_linear_map_equiv_differential_operators R S M k N
  let γ : P^{k}_{S⁄R}(M) →ₗ[S] N := eSource.symm ⟨D, hD⟩
  let γLift : S' ⊗[S] P^{k}_{S⁄R}(M) →ₗ[S'] S' ⊗[S] N :=
    γ.baseChange S'
  let γTarget : P^{k}_{S'⁄R}(S' ⊗[S] M) →ₗ[S'] S' ⊗[S] N :=
    γLift.comp eComp.symm.toLinearMap
  let eTarget :=
    principal_parts_linear_map_equiv_differential_operators
      R S' (S' ⊗[S] M) k (S' ⊗[S] N)
  let DTarget :
      differential_operators_order_le R S' (S' ⊗[S] M) k (S' ⊗[S] N) :=
    eTarget γTarget
  refine ⟨DTarget.1, ?_, ?_⟩
  · constructor
    · -- Proof comment: compare both extensions on the generators `1 ⊗ m`.
      ext m
      have hγ :
          γ (principal_parts_universal_differential (R := R) (S := S) (M := M) k m) = D m := by
        simpa [γ] using
          (principal_parts_linear_map_equiv_symm_apply_universal_differential
            (R := R) (S := S) (M := M) (Q := N) k (D := ⟨D, hD⟩) m)
      have hgen :
          eComp.symm
              (principal_parts_universal_differential
                (R := R) (S := S') (M := S' ⊗[S] M) k
                ((mk S S' S' M (1 : S')) m)) =
            ((1 : S') ⊗ₜ[S]
              principal_parts_universal_differential (R := R) (S := S) (M := M) k m) := by
        have hmap :
            eComp
                (((1 : S') ⊗ₜ[S]
                  principal_parts_universal_differential
                    (R := R) (S := S) (M := M) k m)) =
              principal_parts_universal_differential
                (R := R) (S := S') (M := S' ⊗[S] M) k
                ((mk S S' S' M (1 : S')) m) := by
          simpa [eComp, f] using
            principalPartsFormallyEtaleBaseChangeMap_apply_tmul_universal_differential
              (R := R) (S := S) (S' := S') (M := M) k m
        exact eComp.symm_apply_eq.2 hmap.symm
      calc
        (DTarget.1.comp ((mk S S' S' M (1 : S')).restrictScalars R)) m =
            DTarget.1 ((mk S S' S' M (1 : S')) m) := by
              rfl
        _ =
            γTarget
              (principal_parts_universal_differential
                (R := R) (S := S') (M := S' ⊗[S] M) k
                ((mk S S' S' M (1 : S')) m)) := by
              simpa [DTarget, eTarget] using
                (principal_parts_linear_map_equiv_apply_universal_differential
                  (R := R) (S := S') (M := S' ⊗[S] M) (Q := S' ⊗[S] N) k
                  (L := γTarget) ((mk S S' S' M (1 : S')) m)).symm
        _ =
            γLift
              (((1 : S') ⊗ₜ[S]
                principal_parts_universal_differential
                  (R := R) (S := S) (M := M) k m)) := by
              simpa [γTarget, LinearMap.comp_apply] using congrArg γLift hgen
        _ = ((1 : S') ⊗ₜ[S] D m : S' ⊗[S] N) := by
          simpa [γLift, hγ] using
            (LinearMap.baseChange_tmul
              (f := γ) (a := (1 : S'))
              (x := principal_parts_universal_differential (R := R) (S := S) (M := M) k m))
        _ =
            (((mk S S' S' N (1 : S')).restrictScalars R).comp D) m := by
              rfl
    · exact DTarget.2
  · intro E hE
    let δ : P^{k}_{S'⁄R}(S' ⊗[S] M) →ₗ[S'] S' ⊗[S] N :=
      eTarget.symm ⟨E, hE.2⟩
    have hcomp :
        δ.comp f = γLift := by
      -- Proof comment: both maps out of the source tensor principal-parts module agree on the
      -- generators `1 ⊗ [m]`, so source extensionality identifies them.
      apply tensor_principal_parts_linear_map_eq_of_apply_tmul_universal_differential_eq
        (R := R) (S := S) (S' := S') (M := M) (Q := S' ⊗[S] N) k
      intro m
      have hγ :
          γ (principal_parts_universal_differential (R := R) (S := S) (M := M) k m) = D m := by
        simpa [γ] using
          (principal_parts_linear_map_equiv_symm_apply_universal_differential
            (R := R) (S := S) (M := M) (Q := N) k (D := ⟨D, hD⟩) m)
      have hEcomp :
          E ((mk S S' S' M (1 : S')) m) = ((mk S S' S' N (1 : S')) (D m)) := by
        simpa [LinearMap.comp_apply] using DFunLike.congr_fun hE.1 m
      calc
        (δ.comp f)
            ((1 : S') ⊗ₜ[S]
              principal_parts_universal_differential (R := R) (S := S) (M := M) k m) =
            δ
              (principal_parts_universal_differential
                (R := R) (S := S') (M := S' ⊗[S] M) k
                ((mk S S' S' M (1 : S')) m)) := by
              rw [LinearMap.comp_apply,
                principalPartsFormallyEtaleBaseChangeMap_apply_tmul_universal_differential
                  (R := R) (S := S) (S' := S') (M := M) k m]
        _ = E ((mk S S' S' M (1 : S')) m) := by
          simpa [δ] using
            (principal_parts_linear_map_equiv_symm_apply_universal_differential
              (R := R) (S := S') (M := S' ⊗[S] M) (Q := S' ⊗[S] N) k
              (D := ⟨E, hE.2⟩) ((mk S S' S' M (1 : S')) m))
        _ = ((1 : S') ⊗ₜ[S] D m : S' ⊗[S] N) := by
          simpa using hEcomp
        _ = γLift
            ((1 : S') ⊗ₜ[S]
              principal_parts_universal_differential (R := R) (S := S) (M := M) k m) := by
          simpa [γLift, hγ] using
            (LinearMap.baseChange_tmul
              (f := γ) (a := (1 : S'))
              (x := principal_parts_universal_differential (R := R) (S := S) (M := M) k m)).symm
    have hδ :
        δ = γTarget := by
      -- Proof comment: `f` is bijective, so the equality after precomposition with `f`
      -- determines the target-side linear map uniquely.
      apply LinearMap.ext
      intro y
      obtain ⟨x, rfl⟩ := eComp.surjective y
      simpa [γTarget, LinearMap.comp_apply] using DFunLike.congr_fun hcomp x
    have hSubtype :
        (⟨E, hE.2⟩ :
          differential_operators_order_le R S' (S' ⊗[S] M) k (S' ⊗[S] N)) =
            DTarget := by
      apply eTarget.symm.injective
      simpa [δ, DTarget] using hδ
    exact congrArg Subtype.val hSubtype

end
