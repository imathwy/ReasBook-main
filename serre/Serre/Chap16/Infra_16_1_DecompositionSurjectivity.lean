import Serre.Chap14.Corollary_14_14_4_3.GrothendieckBasics
import Serre.Chap14.Corollary_14_14_4_4
import Serre.Chap14.Proposition_14_14_3_1
import Serre.Chap14.Infra_14_4_ProjectiveLift
import Serre.Chap15.Definition_15_15_1_1
import Serre.Chap15.Definition_15_15_3_1
import Serre.Chap15.Theorem_15_15_2_2
import Serre.Chap16.Corollary_16_16_1_8_ProjectiveTriangleSupport
import Serre.Chap16.Remark_16_16_3_5

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra Representation TensorProduct

universe u

namespace Representation


section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A

section StableLatticeModuleBridge

variable {E : Type u} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]

/-- Helper for Infra 16 1 DecompositionSurjectivity: the underlying `A`-submodule of a stable
lattice carries the induced `A[G]`-module structure. -/
private instance stableLattice_toSubmodule_module
    {ρ : Representation K G E} (L : StableLattice A ρ) :
    Module A[G] L.toSubmodule := by
  change Module A[G] L.toRepresentation.asModule
  infer_instance

/-- Helper for Infra 16 1 DecompositionSurjectivity: the induced `A[G]`-module structure on a
stable lattice is compatible with restriction of scalars from `A`. -/
private instance stableLattice_toSubmodule_isScalarTower
    {ρ : Representation K G E} (L : StableLattice A ρ) :
    IsScalarTower A A[G] L.toSubmodule := by
  change IsScalarTower A A[G] L.toRepresentation.asModule
  infer_instance

end StableLatticeModuleBridge

namespace LinearMap

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- Helper for Infra 16 1 DecompositionSurjectivity: quotienting an `A`-module by
`𝔪_A • ⊤` realizes the canonical residue-field base change. -/
private theorem mkQ_maximalIdeal_isBaseChange
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

/-- Helper for Infra 16 1 DecompositionSurjectivity: the standard quotient `k`-module on
`L.toSubmodule ⧸ (𝔪_A • ⊤)` identifies linearly with the Chapter `15` reduction owner
`L.reduction`. -/
private noncomputable def reduction_standard_quotient_linear_equiv (L : StableLattice A ρ) :
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

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] [Finite G] in
/-- Helper for Infra 16 1 DecompositionSurjectivity: after transporting the standard quotient
owner to `L.reduction`, the usual quotient class is still represented by the same lattice element.
-/
private theorem reduction_standard_quotient_linear_equiv_comp_mkQ (L : StableLattice A ρ) :
    ∀ x : L.toSubmodule,
      reduction_standard_quotient_linear_equiv (A := A) (K := K) (G := G) L
          (Submodule.mkQ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule)) x) =
        (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) x := by
  intro x
  rfl

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] [Finite G] in
/-- Helper for Infra 16 1 DecompositionSurjectivity: the quotient map from the lattice to its
reduction sends the action of `g` upstairs to the induced action of `g` on the reduction. -/
private theorem reduction_mkQ_commutes (L : StableLattice A ρ) (g : G) (x : L.toSubmodule) :
    (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction)
        ((L.toRepresentation g) x) =
      L.reductionRepresentation g
        ((Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) x) := by
  simpa using (StableLattice.reductionRepresentation_apply_mk (L := L) g x)

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] [Finite G] in
/-- Helper for Infra 16 1 DecompositionSurjectivity: in the reduced `k[G]`-module, the
group-algebra generator `[g]` acts through `L.reductionRepresentation g`. -/
private theorem reduction_monoidAlgebra_of_smul (L : StableLattice A ρ) :
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

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] [Finite G] in
/-- Helper for Infra 16 1 DecompositionSurjectivity: the quotient map from the lattice to its
reduction is the canonical residue-field base change on the underlying `A`-module. -/
private theorem reduction_mkQ_isBaseChange (L : StableLattice A ρ) :
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
    LinearMap.mkQ_maximalIdeal_isBaseChange (A := A) (M := L.toSubmodule)
  let e :
      (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))) ≃ₗ[k]
        L.reduction :=
    reduction_standard_quotient_linear_equiv (A := A) (K := K) (G := G) L
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
            reduction_standard_quotient_linear_equiv_comp_mkQ
              (A := A) (K := K) (G := G) L x

omit [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] [Finite G] in
/-- Helper for Infra 16 1 DecompositionSurjectivity: after restricting scalars along
`A[G] → k[G]`, the quotient map from the lattice still sees the source generator `[g]` through
`L.toRepresentation g`. -/
private theorem toRepresentation_monoidAlgebra_of_smul (L : StableLattice A ρ) :
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

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] [Finite G] in
/-- Helper for Infra 16 1 DecompositionSurjectivity: the reduced `A[G]`-action obtained by
restriction of scalars along `A[G] → k[G]` is compatible with the ambient `A`-scalar action. -/
private theorem reduction_restrict_groupAlgebra_isScalarTower_early (L : StableLattice A ρ) :
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

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] [Finite G] in
/-- Helper for Infra 16 1 DecompositionSurjectivity: after restricting scalars along `A[G] → k[G]`,
the quotient map intertwines the source and reduced actions of the group-algebra generators. -/
private theorem reduction_mkQ_map_monoidAlgebra_of (L : StableLattice A ρ) :
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
    reduction_restrict_groupAlgebra_isScalarTower_early (A := A) (K := K) (G := G) L
  letI : IsScalarTower A A[G] L.reduction := htower
  intro g x
  -- Rewrite the source generator action as the actual lattice representation.
  rw [toRepresentation_monoidAlgebra_of_smul (A := A) (K := K) (G := G) L g x]
  -- Rewrite the quotient term using the proved equivariance of the actual group action.
  rw [reduction_mkQ_commutes (A := A) (K := K) (G := G) L g x]
  -- Rewrite the reduced representation as the reduced generator action.
  rw [← reduction_monoidAlgebra_of_smul (A := A) (K := K) (G := G) L g
    (L.maximalIdealSubmodule.mkQ x)]
  -- Identify the restricted `A[G]`-action with the coefficientwise image in `k[G]`.
  rw [show MonoidAlgebra.of k G g =
    (MonoidAlgebra.mapRingHom G (algebraMap A k)) (MonoidAlgebra.of A G g) by simp]
  rfl

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] [Finite G] in
/-- Helper for Infra 16 1 DecompositionSurjectivity: the quotient map from a stable lattice to
its reduction is a residue-field reduction in the Chapter `14` sense. -/
theorem reduction_mkQ_isResidueFieldReduction (L : StableLattice A ρ) :
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
  · simpa using reduction_mkQ_isBaseChange (A := A) (K := K) (G := G) L
  · letI : Module A[G] L.reduction :=
        Module.compHom L.reduction (MonoidAlgebra.mapRingHom G (algebraMap A k))
    letI : IsScalarTower A A[G] L.reduction :=
      reduction_restrict_groupAlgebra_isScalarTower_early (A := A) (K := K) (G := G) L
    refine Representation.IsIntertwiningMap.mk ?_
    intro g x
    simpa [Representation.ofModule'] using
      reduction_mkQ_map_monoidAlgebra_of (A := A) (K := K) (G := G) L g x

end StableLattice

/-- Helper for Infra 16 1 DecompositionSurjectivity: on a lifted projective generator, the
decomposition map is the class of the residue-field reduction. -/
private theorem decompositionHom_projective_scalarExtension_class_eq_residueFieldReduction_class
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    decompositionHom A K G [Q.scalarExtension K]₀ =
      [Q.residueFieldReduction.toFiniteRep]₀ := by
  calc
    decompositionHom A K G [Q.scalarExtension K]₀ =
        cartanHom k G [Q.residueFieldReduction]ₚ₀ := by
          exact
            decompositionHom_projective_scalarExtension_class_eq_cartan_reduction_class_support
              (A := A) (K := K) (G := G) Q
    _ = [Q.residueFieldReduction.toFiniteRep]₀ := by
      symm
      exact cartanHom_projectiveClass_eq k G Q.residueFieldReduction

/-- Infrastructure for Theorem 16-16.1-1: the class of a residue-field reduction of a lifted
finite projective module lies in the image of the decomposition homomorphism.

Proof route from Serre, Ch. 16, Sec. 1:
1. Start with a finite projective `A[G]`-module `Q`.  Scalar extension to the fraction field gives
   the finite-dimensional `K[G]`-representation `Q.scalarExtension K`.
2. The decomposition homomorphism `d : R_K(G) -> R_k(G)` is defined by choosing a stable lattice
   and reducing it modulo the maximal ideal.  For `Q.scalarExtension K`, the natural stable lattice
   is precisely the original `A[G]`-module `Q`.
3. Therefore `d [Q.scalarExtension K]` is the class of `Q.residueFieldReduction.toFiniteRep`.
   This is the projective special case of `decompositionHom_finiteRepClass_eq`.
4. In Lean, the proof should exhibit the preimage `[Q.scalarExtension K]₀` and then rewrite with
   the triangle relating `projectiveGrothendieckScalarExtensionHom`, `cartanHom`,
   `projectiveGrothendieckReductionEquiv`, and `decompositionHom`.
5. Existing local versions of this argument appear in `Theorem_16_16_1_1.lean` and
   `Proposition_16_16_3_2.lean`; this theorem is the public reusable form. -/
theorem residueFieldReduction_toFiniteRep_class_mem_range_decompositionHom
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    [Q.residueFieldReduction.toFiniteRep]₀ ∈ Set.range (decompositionHom A K G) := by
  refine ⟨[Q.scalarExtension K]₀, ?_⟩
  exact
    decompositionHom_projective_scalarExtension_class_eq_residueFieldReduction_class
      (A := A) (K := K) (G := G) Q

/-- Infrastructure for Theorem 16-16.1-1: if a simple module is a quotient of a reduced lifted
projective module and the kernel class is already in the image of `decompositionHom`, then the
simple class is also in the image.

Proof route from Serre, Ch. 16, Sec. 1:
1. Serre lifts a projective envelope of a simple `k[G]`-module to characteristic zero, then uses
   the exact sequence `0 -> Ker -> Q_bar -> S -> 0` after reduction.
2. In the Grothendieck group this exact sequence is the identity
   `[Q_bar] = [Ker] + [S]`, here supplied as `hshort`.
3. By `residueFieldReduction_toFiniteRep_class_mem_range_decompositionHom`, `[Q_bar]` is in the
   image of `decompositionHom`.
4. By hypothesis, `[Ker]` is also in the image.  Since `decompositionHom` is an additive group
   homomorphism, subtracting the kernel preimage from the projective preimage gives a preimage of
   `[S]`.
5. The Lean proof is purely additive after the two range hypotheses: destruct both range witnesses
   and compute `d (xQ - xK)`. -/
theorem simple_class_mem_range_decompositionHom_of_projective_quotient
    (S : FDRep k G) [Simple S]
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (K0 : FDRep k G)
    (hshort :
      [Q.residueFieldReduction.toFiniteRep]₀ = [K0]₀ + [S]₀)
    (hkernel : [K0]₀ ∈ Set.range (decompositionHom A K G)) :
    [S]₀ ∈ Set.range (decompositionHom A K G) := by
  have hQ :=
    residueFieldReduction_toFiniteRep_class_mem_range_decompositionHom
      (A := A) (K := K) (G := G) Q
  rcases hQ with ⟨xQ, hxQ⟩
  rcases hkernel with ⟨xK, hxK⟩
  refine ⟨xQ - xK, ?_⟩
  calc
    decompositionHom A K G (xQ - xK) =
        decompositionHom A K G xQ - decompositionHom A K G xK := by
          simp
    _ = [Q.residueFieldReduction.toFiniteRep]₀ - [K0]₀ := by
          simp [hxQ, hxK]
    _ = [S]₀ := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            congrArg (fun z : R₀[k](G) => z - [K0]₀) hshort

omit [IsDomain A] [IsDiscreteValuationRing A] [Finite G] in
/-- Helper for Infra 16 1 DecompositionSurjectivity: the source of a projective envelope of a
simple `k[G]`-module is finitely generated over the group algebra. -/
private theorem moduleFinite_of_projectiveEnvelope_simple_local
    {P M : Type u} [AddCommGroup P] [Module k[G] P]
    [AddCommGroup M] [Module k[G] M] [IsSimpleModule k[G] M]
    {f : P →ₗ[k[G]] M} (hf : f.IsProjectiveEnvelope) :
    Module.Finite k[G] P := by
  letI : Nontrivial M := IsSimpleModule.nontrivial (R := k[G]) (M := M)
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨x, hx⟩ := hf.surjective m
  let N : Submodule k[G] P := Submodule.span k[G] {x}
  have hmap_ne_bot : N.map f ≠ ⊥ := by
    -- The chosen generator maps to a nonzero vector, so the image cannot be trivial.
    intro hbot
    have hxmem : f x ∈ N.map f := by
      exact ⟨x, Submodule.mem_span_singleton_self x, rfl⟩
    have hfx : f x = 0 := by
      rw [hbot] at hxmem
      simpa using hxmem
    exact hm <| by simpa [hx] using hfx
  have hmap_top : N.map f = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top (N.map f)).resolve_left hmap_ne_bot
  have hN_top : N = ⊤ := hf.toIsEssential.eq_top_of_map_eq_top N hmap_top
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton k[G] P x) := by
    -- Once the cyclic span is all of `P`, the canonical map from `k[G]` onto that span is onto.
    simpa [LinearMap.toSpanSingleton_apply] using
      (Submodule.span_singleton_eq_top_iff (R := k[G]) (x := x)).1 (by simpa [N] using hN_top)
  exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k[G] P x) hsurj

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- Helper for Infra 16 1 DecompositionSurjectivity: every simple finite-dimensional `k[G]`-
representation admits a finite projective envelope in the canonical owner category of projective
modules. -/
private theorem exists_finite_projective_envelope_of_simple_local
    (S : FDRep k G) [Simple S] :
    ∃ P : FiniteProjectiveGroupAlgebraModule k G,
      ∃ f : P.V →ₗ[k[G]] asModule S.ρ, f.IsProjectiveEnvelope := by
  let ρ : Representation k G S := S.ρ
  letI : Module k[G] S := by
    -- Expose the ambient `k[G]`-module structure carried by the owner `S`.
    simpa [ρ] using (inferInstance : Module k[G] ρ.asModule)
  letI : Representation.IsIrreducible ρ := by
    -- Convert categorical simplicity of `S` into irreducibility of the underlying representation.
    simpa [ρ] using (FDRep.isIrreducible_of_simple S)
  letI : IsSimpleModule k[G] S := by
    -- The projective-envelope theorem is stated for modules, so move to `k[G]`-modules here.
    simpa [ρ] using
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  let M : ModuleCat k[G] := ModuleCat.of k[G] S
  let _ : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing k[G] := IsArtinianRing.of_finite k k[G]
  obtain ⟨P', f', hf'⟩ := exists_isProjectiveEnvelope M
  have hfinite : Module.Finite k[G] P' :=
    moduleFinite_of_projectiveEnvelope_simple_local (G := G) (f := f'.hom) hf'
  let Pfg : FGModuleCat k[G] := by
    -- Repackage the projective-envelope source as a finitely generated `k[G]`-module.
    refine ⟨P', ?_⟩
    change Module.Finite k[G] P'
    exact hfinite
  have hproj : Module.Projective k[G] Pfg := by
    -- Projectivity is already part of the projective-envelope structure.
    change Module.Projective k[G] P'
    infer_instance
  let P : FiniteProjectiveGroupAlgebraModule k G := ⟨Pfg, hproj⟩
  refine ⟨P, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [ρ] using f'.hom
  · simpa [P, ρ] using hf'

/-- Helper for Infra 16 1 DecompositionSurjectivity: any residue-field class coming from the
reduction of a stable characteristic-zero lattice already lies in the range of
`decompositionHom`. -/
private theorem finiteRep_class_mem_range_decompositionHom_of_exists_lift
    (S : FDRep k G)
    (hS :
      ∃ X : FDRep K G, ∃ L : StableLattice A X.ρ,
        Nonempty (FDRep.of L.reductionRepresentation ≅ S)) :
    [S]₀ ∈ Set.range (decompositionHom A K G) := by
  rcases hS with ⟨X, L, hReduction⟩
  rcases hReduction with ⟨e⟩
  refine ⟨[X]₀, ?_⟩
  -- Evaluate `decompositionHom` on the chosen characteristic-zero witness and then transport the
  -- reduced class across the supplied isomorphism with `S`.
  calc
    decompositionHom A K G [X]₀ = [FDRep.of L.reductionRepresentation]₀ := by
      simpa using decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) X L
    _ = [S]₀ := by
      simpa using
        (finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G)
          (V := FDRep.of L.reductionRepresentation) (W := S) ⟨e⟩)

/-- Helper for Infra 16 1 DecompositionSurjectivity: an explicit `(R')`-style lift witness already
places the corresponding simple class in the image of the decomposition homomorphism. -/
private theorem simple_class_mem_range_of_rprime_lift_local
    (S : FDRep k G)
    (hS :
      ∃ X : FDRep K G, Simple X ∧
        ∃ L : StableLattice A X.ρ, Nonempty (FDRep.of L.reductionRepresentation ≅ S)) :
    [S]₀ ∈ Set.range (decompositionHom A K G) := by
  rcases hS with ⟨X, _hX, L, hReduction⟩
  -- Forget the irreducibility flag: the existing range lemma only needs the reduction witness.
  exact
    finiteRep_class_mem_range_decompositionHom_of_exists_lift
      (A := A) (K := K) (G := G) S ⟨X, L, hReduction⟩

omit [IsDomain A] [IsDiscreteValuationRing A] [Finite G] in
/-- Helper for Infra 16 1 DecompositionSurjectivity: choose one representative of each
isomorphism class of simple finite-dimensional `k[G]`-representations. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family_surjectivity :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep k G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep k G // Simple τ }
  let r : Setoid SimpleRep :=
    { r := fun a b ↦ Nonempty (a.1 ≅ b.1)
      iseqv :=
        ⟨fun a ↦ ⟨Iso.refl _⟩,
          fun {a b} hab ↦ by
            rcases hab with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {a b c} hab hbc ↦ by
            rcases hab with ⟨eab⟩
            rcases hbc with ⟨ebc⟩
            exact ⟨eab.trans ebc⟩⟩ }
  let ι : Type (u + 1) := Quotient r
  let π : ι → FDRep k G := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : PairwiseNonisomorphic π := by
    -- Distinct quotient classes cannot admit an isomorphism.
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨e⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine ⟨?_, ?_⟩
    · intro q
      exact (Quotient.out q).2
    · intro τ hτ
      let q : ι := ⟦⟨τ, hτ⟩⟧
      refine ⟨q, ?_⟩
      have hq : Nonempty ((Quotient.out q).1 ≅ τ) := by
        exact Quotient.exact (Quotient.out_eq q)
      rcases hq with ⟨e⟩
      exact ⟨e.symm⟩
  exact ⟨ι, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Infra 16 1 DecompositionSurjectivity: under the large-field hypothesis, the
simple residue-field class has an explicit preimage under `decompositionHom`. -/
theorem exists_preimage_of_simple_class_of_hasEnoughRootsOfUnity
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (S : FDRep k G) [Simple S] :
    ∃ x : R₀[K](G), decompositionHom A K G x = [S]₀ := by
  -- Route correction: the source proof for surjectivity only needs a preimage of `[S]₀`; the
  -- earlier projective-envelope detour asked for a stronger bare-DVR lift that lives on the wrong
  -- Chapter `14` surface.
  have hRPrime : SatisfiesConditionRPrime A K G :=
    satisfiesConditionRPrime_of_sufficiently_large
      (A := A) (K := K) (G := G)
  rcases hRPrime S inferInstance with ⟨X, hX, L, hReduction⟩
  rcases
      simple_class_mem_range_of_rprime_lift_local
        (A := A) (K := K) (G := G) S ⟨X, hX, L, hReduction⟩ with ⟨x, hx⟩
  -- Unpack the range statement into the explicit preimage consumed by the basis argument.
  exact ⟨x, hx⟩

/-- Infrastructure for Theorem 16-16.1-1: under the large-field hypothesis, every simple
residue-field class belongs to the image of the decomposition homomorphism.

Proof route from Serre, Ch. 16, Sec. 1:
1. Under `[HasEnoughRootsOfUnity K (Monoid.exponent G)]`, the existing Chapter `16` theorem
   `satisfiesConditionRPrime_of_sufficiently_large` gives Serre's `(R')` witness for any simple
   `k[G]`-representation `S`.
2. Unpack that witness as a characteristic-zero representation `X` together with a stable lattice
   `L` whose reduction is isomorphic to `S`.
3. Apply `decompositionHom_finiteRepClass_eq` to `[X]₀`, so the decomposition map lands on the
   class of `FDRep.of L.reductionRepresentation`.
4. Transport across the reduction isomorphism to identify that class with `[S]₀`.
5. The theorem is therefore just the range formulation of this explicit lifted witness. -/
theorem simple_class_mem_range_decompositionHom_of_hasEnoughRootsOfUnity
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (S : FDRep k G) [Simple S] :
    [S]₀ ∈ Set.range (decompositionHom A K G) := by
  -- Route correction: once the large-field `(R')` witness is available, Serre's basis argument
  -- only needs the simple class itself to have a preimage under `decompositionHom`.
  rcases
      exists_preimage_of_simple_class_of_hasEnoughRootsOfUnity
        (A := A) (K := K) (G := G) S with ⟨x, hx⟩
  exact ⟨x, hx⟩

/-- Infrastructure for Theorem 16-16.1-1: once all simple basis vectors lie in the image, the
decomposition homomorphism is surjective.

Proof route from Serre, Ch. 16, Sec. 1:
1. A complete pairwise-nonisomorphic family of simple `k[G]`-representations gives the standard
   `ℤ`-basis of `R₀[k](G)` by
   `simple_finiteRep_classes_basis_of_complete_family`.
2. The hypothesis `hπ_range` says each basis vector `[π i]₀` has a preimage under
   `decompositionHom A K G`; choose these preimages.
3. For an arbitrary `y : R₀[k](G)`, expand it in the simple-class basis:
   `y = ∑ i, (b.repr y i) • b i`.
4. Lift this expansion termwise to `R₀[K](G)` using the chosen preimages and the same integer
   coefficients.
5. Since `decompositionHom` is additive and commutes with integer scalar multiplication, the image
   of the lifted linear combination is exactly `y`.  This is the formal final step in Serre's proof
   after all simple classes have been shown to lift. -/
theorem decompositionHom_surjective_of_complete_simple_family
    {ι : Type*} (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ_range : ∀ i, [π i]₀ ∈ Set.range (decompositionHom A K G)) :
    Function.Surjective (decompositionHom A K G) := by
  classical
  let b : Module.Basis ι ℤ (R₀[k](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  have hb : ∀ i, b i ∈ Set.range (decompositionHom A K G) := by
    intro i
    simpa [b, simple_finiteRep_classes_basis_of_complete_family_apply] using hπ_range i
  choose x hx using hb
  intro y
  refine ⟨(b.repr y).sum fun i a ↦ a • x i, ?_⟩
  calc
    decompositionHom A K G ((b.repr y).sum fun i a ↦ a • x i)
        = (b.repr y).sum fun i a ↦ a • decompositionHom A K G (x i) := by
            simp [Finsupp.sum, map_sum, map_zsmul]
    _ = (b.repr y).sum fun i a ↦ a • b i := by
          simp [Finsupp.sum, hx]
    _ = y := by
          simpa [Finsupp.linearCombination_apply, Finsupp.sum] using b.linearCombination_repr y

/-- Infra 16 1 DecompositionSurjectivity: under the large-field hypothesis on `K`, every simple
residue-field class lifts and the resulting basis argument makes the decomposition homomorphism
`decompositionHom A K G : R₀[K](G) → R₀[k](G)` surjective. -/
theorem decompositionHom_surjective_of_hasEnoughRootsOfUnity
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    Function.Surjective (decompositionHom A K G) := by
  classical
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_surjectivity
      (A := A) (G := G)
  refine
    decompositionHom_surjective_of_complete_simple_family
      (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete ?_
  intro i
  letI : Simple (π i) := hπ_complete.isSimple i
  exact
    simple_class_mem_range_decompositionHom_of_hasEnoughRootsOfUnity
      (A := A) (K := K) (G := G) (π i)

end

end Representation
