import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_3.GrothendieckBasics
import LinearRepresentations_Serre_1977.Serre.Chap14.Proposition_14_14_3_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra Representation TensorProduct

universe u

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type u} [Field K] [Algebra A K]
variable {G : Type u} [Group G]

local notation "k" => IsLocalRing.ResidueField A

section StableLatticeModuleBridge

variable {E : Type u} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]

/-- Helper for Proposition 15-15.5-1: the underlying `A`-submodule of a stable lattice carries
the induced `A[G]`-module structure. -/
private instance stableLattice_toSubmodule_module_local
    {ρ : Representation K G E} (L : StableLattice A ρ) :
    Module A[G] L.toSubmodule := by
  change Module A[G] L.toRepresentation.asModule
  infer_instance

/-- Helper for Proposition 15-15.5-1: the induced `A[G]`-module structure on a stable lattice is
compatible with restriction of scalars from `A`. -/
private instance stableLattice_toSubmodule_isScalarTower_local
    {ρ : Representation K G E} (L : StableLattice A ρ) :
    IsScalarTower A A[G] L.toSubmodule := by
  change IsScalarTower A A[G] L.toRepresentation.asModule
  infer_instance

end StableLatticeModuleBridge

namespace LinearMap

omit [Field K] [Algebra A K] in
/-- Helper for Proposition 15-15.5-1: quotienting an `A`-module by `𝔪_A • ⊤` realizes the
canonical residue-field base change. -/
private theorem mkQ_maximalIdeal_isBaseChange_local
    (M : Type u) [AddCommGroup M] [Module A M] :
    letI : Module (A ⧸ IsLocalRing.maximalIdeal A)
        (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) :=
      inferInstanceAs
        (Module (A ⧸ IsLocalRing.maximalIdeal A)
          (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))))
    letI : IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A)
        (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) :=
      inferInstanceAs
        (IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A)
          (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))))
    IsBaseChange (A ⧸ IsLocalRing.maximalIdeal A)
      (Submodule.mkQ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)) :
        M →ₗ[A] M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) := by
  let e :=
    LinearEquiv.extendScalarsOfSurjective
      (R := A)
      (S := A ⧸ IsLocalRing.maximalIdeal A)
      (M := TensorProduct A (A ⧸ IsLocalRing.maximalIdeal A) M)
      (N := M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)))
      (by
        simpa [IsLocalRing.ResidueField.algebraMap_eq] using
          (IsLocalRing.residue_surjective (R := A)))
      (TensorProduct.quotTensorEquivQuotSMul M (IsLocalRing.maximalIdeal A))
  letI : Module (A ⧸ IsLocalRing.maximalIdeal A)
      (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) :=
    inferInstanceAs
      (Module (A ⧸ IsLocalRing.maximalIdeal A)
        (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))))
  letI : IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A)
      (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) :=
    inferInstanceAs
      (IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A)
        (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))))
  refine IsBaseChange.of_equiv e ?_
  intro x
  have h :=
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul
      (R := A) (M := M) (I := IsLocalRing.maximalIdeal A) x
  simp [e] at h ⊢

end LinearMap

namespace StableLattice

variable {E : Type u} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]
variable {ρ : Representation K G E}

/-- Helper for Proposition 15-15.5-1: the standard quotient `k`-module on
`L.toSubmodule ⧸ (𝔪_A • ⊤)` identifies linearly with the Chapter 15 reduction owner
`L.reduction`. -/
private noncomputable def reduction_standard_quotient_linear_equiv_local (L : StableLattice A ρ) :
    letI : Module k
        (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))) :=
      inferInstanceAs
        (Module k
          (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))))
    (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))) ≃ₗ[k]
      L.reduction := by
  letI : Module k
      (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))) :=
    inferInstanceAs
      (Module k
        (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))))
  refine
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro x
        rfl
      map_add' := by
        intro x y
        rfl
      map_smul' := ?_ }
  intro c x
  refine Quotient.inductionOn' c ?_
  intro a
  refine Quotient.inductionOn' x ?_
  intro y
  simp

/-- Helper for Proposition 15-15.5-1: after transporting the standard quotient owner to
`L.reduction`, the usual quotient class is still represented by the same lattice element. -/
private theorem reduction_standard_quotient_linear_equiv_comp_mkQ_local (L : StableLattice A ρ) :
    ∀ x : L.toSubmodule,
      reduction_standard_quotient_linear_equiv_local (A := A) (K := K) (G := G) L
          (Submodule.mkQ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule)) x) =
        (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) x := by
  intro x
  rfl

/-- Helper for Proposition 15-15.5-1: the quotient map from the lattice to its reduction sends
the action of `g` upstairs to the induced action of `g` on the reduction. -/
private theorem reduction_mkQ_commutes_local (L : StableLattice A ρ) (g : G)
    (x : L.toSubmodule) :
    (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction)
        ((L.toRepresentation g) x) =
      L.reductionRepresentation g
        ((Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) x) := by
  simpa using (StableLattice.reductionRepresentation_apply_mk (L := L) g x)

/-- Helper for Proposition 15-15.5-1: in the reduced `k[G]`-module, the group-algebra generator
`[g]` acts through `L.reductionRepresentation g`. -/
private theorem reduction_monoidAlgebra_of_smul_local (L : StableLattice A ρ) :
    letI : Module k[G] L.reduction := by
      change Module k[G] L.reductionRepresentation.asModule
      infer_instance
    letI : IsScalarTower k k[G] L.reduction := by
      change IsScalarTower k k[G] L.reductionRepresentation.asModule
      infer_instance
    ∀ g : G, ∀ x : L.reduction, MonoidAlgebra.of k G g • x = L.reductionRepresentation g x := by
  letI : Module k[G] L.reduction := by
    change Module k[G] L.reductionRepresentation.asModule
    infer_instance
  letI : IsScalarTower k k[G] L.reduction := by
    change IsScalarTower k k[G] L.reductionRepresentation.asModule
    infer_instance
  intro g x
  rw [← Representation.asAlgebraHom_single_one (ρ := L.reductionRepresentation) g]
  rfl

/-- Helper for Proposition 15-15.5-1: the quotient map from the lattice to its reduction is the
canonical residue-field base change on the underlying `A`-module. -/
private theorem reduction_mkQ_isBaseChange_local (L : StableLattice A ρ) :
    letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
    letI : IsScalarTower A k L.reduction :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    IsBaseChange k
      (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) := by
  letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
  letI : IsScalarTower A k L.reduction :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module k
      (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))) :=
    inferInstanceAs
      (Module k
        (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))))
  let hstd :=
    LinearMap.mkQ_maximalIdeal_isBaseChange_local (A := A) (M := L.toSubmodule)
  let e :
      (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))) ≃ₗ[k]
        L.reduction :=
    reduction_standard_quotient_linear_equiv_local (A := A) (K := K) (G := G) L
  refine IsBaseChange.of_equiv
    { toFun := fun z ↦ e (hstd.equiv z)
      invFun := fun y ↦ hstd.equiv.symm (e.symm y)
      left_inv := by
        intro z
        simp [e]
      right_inv := by
        intro y
        simp [e]
      map_add' := by
        intro z w
        calc
          e (hstd.equiv (z + w)) = e (hstd.equiv z + hstd.equiv w) := by
            exact congrArg e (hstd.equiv.map_add z w)
          _ = e (hstd.equiv z) + e (hstd.equiv w) := by
            exact e.map_add _ _
      map_smul' := by
        intro c z
        refine Quotient.inductionOn' c ?_
        intro a
        calc
          e (hstd.equiv ((IsLocalRing.residue A a) • z)) =
              e ((IsLocalRing.residue A a) • hstd.equiv z) := by
                exact congrArg e (hstd.equiv.map_smul (IsLocalRing.residue A a) z)
          _ = (IsLocalRing.residue A a) • e (hstd.equiv z) := by
                exact e.map_smul _ _ } ?_
  intro x
  calc
    e (hstd.equiv (1 ⊗ₜ[A] x)) =
        e ((Submodule.mkQ (IsLocalRing.maximalIdeal A •
          (⊤ : Submodule A L.toSubmodule)) : L.toSubmodule →ₗ[A]
            L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A •
              (⊤ : Submodule A L.toSubmodule))) x) := by
          simp [e]
    _ = (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) x := by
          simpa [e] using
            reduction_standard_quotient_linear_equiv_comp_mkQ_local
              (A := A) (K := K) (G := G) L x

/-- Helper for Proposition 15-15.5-1: after restricting scalars along `A[G] → k[G]`, the quotient
map from the lattice still sees the source generator `[g]` through `L.toRepresentation g`. -/
private theorem toRepresentation_monoidAlgebra_of_smul_local (L : StableLattice A ρ) :
    letI : Module A[G] L.toSubmodule := by
      change Module A[G] L.toRepresentation.asModule
      infer_instance
    letI : IsScalarTower A A[G] L.toSubmodule := by
      change IsScalarTower A A[G] L.toRepresentation.asModule
      infer_instance
    ∀ g : G, ∀ x : L.toSubmodule, MonoidAlgebra.of A G g • x = L.toRepresentation g x := by
  letI : Module A[G] L.toSubmodule := by
    change Module A[G] L.toRepresentation.asModule
    infer_instance
  letI : IsScalarTower A A[G] L.toSubmodule := by
    change IsScalarTower A A[G] L.toRepresentation.asModule
    infer_instance
  intro g x
  rw [← Representation.asAlgebraHom_single_one (ρ := L.toRepresentation) g]
  rfl

/-- Helper for Proposition 15-15.5-1: the reduced `A[G]`-action obtained by restriction of scalars
along `A[G] → k[G]` is compatible with the ambient `A`-scalar action. -/
private theorem reduction_restrict_groupAlgebra_isScalarTower_local (L : StableLattice A ρ) :
    letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
    letI : IsScalarTower A k L.reduction :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    letI : Module k[G] L.reduction := by
      change Module k[G] L.reductionRepresentation.asModule
      infer_instance
    letI : IsScalarTower k k[G] L.reduction := by
      change IsScalarTower k k[G] L.reductionRepresentation.asModule
      infer_instance
    letI : Module A[G] L.reduction :=
      Module.compHom L.reduction (MonoidAlgebra.mapRingHom G (algebraMap A k))
    IsScalarTower A A[G] L.reduction := by
  letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
  letI : IsScalarTower A k L.reduction :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module k[G] L.reduction := by
    change Module k[G] L.reductionRepresentation.asModule
    infer_instance
  letI : IsScalarTower k k[G] L.reduction := by
    change IsScalarTower k k[G] L.reductionRepresentation.asModule
    infer_instance
  letI : Module A[G] L.reduction :=
    Module.compHom L.reduction (MonoidAlgebra.mapRingHom G (algebraMap A k))
  refine IsScalarTower.of_algebraMap_smul ?_
  intro a x
  change
    (MonoidAlgebra.mapRingHom G (algebraMap A k))
        (MonoidAlgebra.single (1 : G) a) • x =
      a • x
  rw [MonoidAlgebra.mapRingHom_single]
  have hsingle :
      MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) =
        algebraMap k (k[G]) (IsLocalRing.residue A a) := by
    rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
    simp
  calc
    MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) • x
        = (IsLocalRing.residue A a) • x := by
            simpa only [hsingle] using
              (IsScalarTower.algebraMap_smul (k[G]) (IsLocalRing.residue A a) x)
    _ = a • x := by
          rfl

/-- Helper for Proposition 15-15.5-1: after restricting scalars along `A[G] → k[G]`, the quotient
map intertwines the source and reduced actions of the group-algebra generators. -/
private theorem reduction_mkQ_map_monoidAlgebra_of_local (L : StableLattice A ρ) :
    letI : Module A[G] L.toSubmodule := by
      change Module A[G] L.toRepresentation.asModule
      infer_instance
    letI : IsScalarTower A A[G] L.toSubmodule := by
      change IsScalarTower A A[G] L.toRepresentation.asModule
      infer_instance
    letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
    letI : IsScalarTower A k L.reduction :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    letI : Module k[G] L.reduction := by
      change Module k[G] L.reductionRepresentation.asModule
      infer_instance
    letI : IsScalarTower k k[G] L.reduction := by
      change IsScalarTower k k[G] L.reductionRepresentation.asModule
      infer_instance
    letI : Module A[G] L.reduction :=
      Module.compHom L.reduction (MonoidAlgebra.mapRingHom G (algebraMap A k))
    letI : IsScalarTower A A[G] L.reduction :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change
          (MonoidAlgebra.mapRingHom G (algebraMap A k))
              (MonoidAlgebra.single (1 : G) a) • x =
            a • x
        rw [MonoidAlgebra.mapRingHom_single]
        have hsingle :
            MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) =
              algebraMap k (k[G]) (IsLocalRing.residue A a) := by
          rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
          simp
        calc
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) • x
              = (IsLocalRing.residue A a) • x := by
                  simpa only [hsingle] using
                    (IsScalarTower.algebraMap_smul (k[G])
                      (IsLocalRing.residue A a) x)
          _ = a • x := by
                rfl
    ∀ g : G, ∀ x : L.toSubmodule,
      (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction)
          (MonoidAlgebra.of A G g • x) =
        MonoidAlgebra.of A G g •
          ((Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) x) := by
  letI : Module A[G] L.toSubmodule := by
    change Module A[G] L.toRepresentation.asModule
    infer_instance
  letI : IsScalarTower A A[G] L.toSubmodule := by
    change IsScalarTower A A[G] L.toRepresentation.asModule
    infer_instance
  letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
  letI : IsScalarTower A k L.reduction :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module k[G] L.reduction := by
    change Module k[G] L.reductionRepresentation.asModule
    infer_instance
  letI : IsScalarTower k k[G] L.reduction := by
    change IsScalarTower k k[G] L.reductionRepresentation.asModule
    infer_instance
  letI : Module A[G] L.reduction :=
    Module.compHom L.reduction (MonoidAlgebra.mapRingHom G (algebraMap A k))
  have htower : IsScalarTower A A[G] L.reduction :=
    reduction_restrict_groupAlgebra_isScalarTower_local (A := A) (K := K) (G := G) L
  letI : IsScalarTower A A[G] L.reduction := htower
  intro g x
  -- Rewrite the source generator action as the actual lattice representation.
  rw [toRepresentation_monoidAlgebra_of_smul_local (A := A) (K := K) (G := G) L g x]
  -- Rewrite the quotient term using the proved equivariance of the actual group action.
  rw [reduction_mkQ_commutes_local (A := A) (K := K) (G := G) L g x]
  -- Rewrite the reduced representation as the reduced generator action.
  rw [← reduction_monoidAlgebra_of_smul_local (A := A) (K := K) (G := G) L g
    (L.maximalIdealSubmodule.mkQ x)]
  -- Identify the restricted `A[G]`-action with the coefficientwise image in `k[G]`.
  rw [show MonoidAlgebra.of k G g =
    (MonoidAlgebra.mapRingHom G (algebraMap A k)) (MonoidAlgebra.of A G g) by simp]
  rfl

/-- Helper for Proposition 15-15.5-1: the quotient map from a stable lattice to its reduction is
a residue-field reduction in the Chapter 14 sense. -/
theorem reduction_mkQ_isResidueFieldReduction_local (L : StableLattice A ρ) :
    letI : Module A[G] L.toSubmodule := by
      change Module A[G] L.toRepresentation.asModule
      infer_instance
    letI : IsScalarTower A A[G] L.toSubmodule := by
      change IsScalarTower A A[G] L.toRepresentation.asModule
      infer_instance
    letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
    letI : IsScalarTower A k L.reduction :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    letI : Module k[G] L.reduction := by
      change Module k[G] L.reductionRepresentation.asModule
      infer_instance
    letI : IsScalarTower k k[G] L.reduction := by
      change IsScalarTower k k[G] L.reductionRepresentation.asModule
      infer_instance
    LinearMap.IsResidueFieldReduction G
      ((Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction)) := by
  letI : Module A[G] L.toSubmodule := by
    change Module A[G] L.toRepresentation.asModule
    infer_instance
  letI : IsScalarTower A A[G] L.toSubmodule := by
    change IsScalarTower A A[G] L.toRepresentation.asModule
    infer_instance
  letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
  letI : IsScalarTower A k L.reduction :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module k[G] L.reduction := by
    change Module k[G] L.reductionRepresentation.asModule
    infer_instance
  letI : IsScalarTower k k[G] L.reduction := by
    change IsScalarTower k k[G] L.reductionRepresentation.asModule
    infer_instance
  constructor
  · simpa using reduction_mkQ_isBaseChange_local (A := A) (K := K) (G := G) L
  · letI : Module A[G] L.reduction :=
        Module.compHom L.reduction (MonoidAlgebra.mapRingHom G (algebraMap A k))
    letI : IsScalarTower A A[G] L.reduction :=
      reduction_restrict_groupAlgebra_isScalarTower_local (A := A) (K := K) (G := G) L
    refine Representation.IsIntertwiningMap.mk ?_
    intro g x
    simpa [Representation.ofModule'] using
      reduction_mkQ_map_monoidAlgebra_of_local (A := A) (K := K) (G := G) L g x

end StableLattice

end

end Representation
