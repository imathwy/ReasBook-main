import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3.GrothendieckBasics
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_3_1
import LinearRepresentations_Serre_1977.Chap14.Infra_14_4_ProjectiveLift
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3.ResidueFieldLiftDecomposition
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.ProjectiveLiteralReduction
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_5.SubgroupInduction
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_5
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3
import LinearRepresentations_Serre_1977.Chap16.Remark_16_16_3_5.Core
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1.DecompositionInductionBridge
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1.HindComplete
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1

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
  letI : Module (A ⧸ IsLocalRing.maximalIdeal A)
      ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] M) :=
    inferInstance
  letI : IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A)
      ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] M) :=
    inferInstance
  letI : Module k ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] M) :=
    inferInstanceAs
      (Module (A ⧸ IsLocalRing.maximalIdeal A)
        ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] M))
  letI : IsScalarTower A k ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] M) :=
    inferInstanceAs
      (IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A)
        ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] M))
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
  letI : Module k (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) :=
    inferInstanceAs
      (Module (A ⧸ IsLocalRing.maximalIdeal A)
        (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))))
  letI : IsScalarTower A k (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) :=
    inferInstanceAs
      (IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A)
        (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))))
  let e :=
    (TensorProduct.quotTensorEquivQuotSMul M (IsLocalRing.maximalIdeal A)).extendScalarsOfSurjective
      (by
        simpa [IsLocalRing.ResidueField.algebraMap_eq] using
          (@IsLocalRing.residue_surjective A _ _))
  refine IsBaseChange.of_equiv e ?_
  intro x
  change (TensorProduct.quotTensorEquivQuotSMul M (IsLocalRing.maximalIdeal A)) (1 ⊗ₜ[A] x) =
    Submodule.Quotient.mk x
  exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul (IsLocalRing.maximalIdeal A) x

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
      reduction_standard_quotient_linear_equiv L
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
  simpa using StableLattice.reductionRepresentation_apply_mk L g x

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
  change (L.reductionRepresentation.asAlgebraHom (MonoidAlgebra.of k G g)) x =
    L.reductionRepresentation g x
  simpa [Representation.asAlgebraHom_single_one]

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
  let hstd :
      IsBaseChange (A ⧸ IsLocalRing.maximalIdeal A)
        (Submodule.mkQ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule)) :
          L.toSubmodule →ₗ[A]
            L.toSubmodule ⧸
              (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))) :=
    LinearMap.mkQ_maximalIdeal_isBaseChange L.toSubmodule
  let e :
      (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))) ≃ₗ[k]
        L.reduction :=
    reduction_standard_quotient_linear_equiv L
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
            reduction_standard_quotient_linear_equiv_comp_mkQ L x

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
  change (L.toRepresentation.asAlgebraHom (MonoidAlgebra.of A G g)) x =
    L.toRepresentation g x
  simpa [Representation.asAlgebraHom_single_one]

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
    reduction_restrict_groupAlgebra_isScalarTower_early L
  letI : IsScalarTower A A[G] L.reduction := htower
  intro g x
  -- Rewrite the source generator action as the actual lattice representation.
  rw [toRepresentation_monoidAlgebra_of_smul L g x]
  -- Rewrite the quotient term using the proved equivariance of the actual group action.
  rw [reduction_mkQ_commutes L g x]
  -- Rewrite the reduced representation as the reduced generator action.
  rw [← reduction_monoidAlgebra_of_smul L g (L.maximalIdealSubmodule.mkQ x)]
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
  · simpa using reduction_mkQ_isBaseChange L
  · letI : Module A[G] L.reduction :=
        Module.compHom L.reduction (MonoidAlgebra.mapRingHom G (algebraMap A k))
    letI : IsScalarTower A A[G] L.reduction :=
      reduction_restrict_groupAlgebra_isScalarTower_early L
    refine Representation.IsIntertwiningMap.mk ?_
    intro g x
    simpa [Representation.ofModule'] using
      reduction_mkQ_map_monoidAlgebra_of L g x

end StableLattice

/-- Helper for Infra 16 1 DecompositionSurjectivity: on a lifted projective generator, the
decomposition map is the class of the residue-field reduction. -/
private theorem decompositionHom_projective_scalarExtension_class_eq_residueFieldReduction_class
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    decompositionHom A K G [Q.scalarExtension K]₀ =
      [Q.residueFieldReduction.toFiniteRep]₀ := by
  -- Use the literal scalar-extension lattice attached directly to the projective module.  This
  -- avoids importing later Chapter `16` triangle support, keeping this infrastructure closer to
  -- the Chapter `15` decomposition owner it uses.
  exact
    decompositionHom_projective_scalarExtension_class_eq_residueFieldReduction_finiteRepClass_support
      Q

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
    decompositionHom_projective_scalarExtension_class_eq_residueFieldReduction_class Q

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
  have hQ : [Q.residueFieldReduction.toFiniteRep]₀ ∈ Set.range (decompositionHom A K G) :=
    residueFieldReduction_toFiniteRep_class_mem_range_decompositionHom Q
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
            congrArg (fun z : R₀[k](G) ↦ z - [K0]₀) hshort

omit [IsDomain A] [IsDiscreteValuationRing A] [Finite G] in
/-- Helper for Infra 16 1 DecompositionSurjectivity: the source of a projective envelope of a
simple `k[G]`-module is finitely generated over the group algebra. -/
private theorem moduleFinite_of_projectiveEnvelope_simple_local
    {P M : Type u} [AddCommGroup P] [Module k[G] P]
    [AddCommGroup M] [Module k[G] M] [IsSimpleModule k[G] M]
    {f : P →ₗ[k[G]] M} (hf : f.IsProjectiveEnvelope) :
    Module.Finite k[G] P := by
  letI : Nontrivial M := by
    exact IsSimpleModule.nontrivial (k[G]) M
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
      (Submodule.span_singleton_eq_top_iff k[G] x).1 (by simpa [N] using hN_top)
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
    moduleFinite_of_projectiveEnvelope_simple_local hf'
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
  exact
    finiteRepClass_mem_range_decompositionHom_of_exists_stableLattice_reduction A K G S hS

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
    finiteRep_class_mem_range_decompositionHom_of_exists_lift S ⟨X, L, hReduction⟩

/-- Helper for Theorem 16-16.1-1: a finite decomposition by subgroup inductions lifts through
`decompositionHom` once the summands lift and `decompositionHom` commutes with those inductions. -/
theorem finiteRepGrothendieckClass_mem_range_decompositionHom_of_induction_decomposition
    {ι : Type*} [Fintype ι]
    (H : ι → Subgroup G)
    (y : ∀ i, R₀[k](H i))
    (z : R₀[k](G))
    (hdecomp :
      z =
        ∑ i,
          Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i) (y i))
    (hRange : ∀ i, y i ∈ Set.range (decompositionHom A K (H i)))
    (hcompat :
      ∀ i (x : R₀[K](H i)),
        decompositionHom A K G
            (Representation.Subgroup.finiteRepGrothendieckGroupInduction K (H i) x) =
          Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i)
            (decompositionHom A K (H i) x)) :
    z ∈ Set.range (decompositionHom A K G) := by
  classical
  choose x hx using hRange
  refine
    ⟨∑ i, Representation.Subgroup.finiteRepGrothendieckGroupInduction K (H i) (x i), ?_⟩
  calc
    decompositionHom A K G
        (∑ i, Representation.Subgroup.finiteRepGrothendieckGroupInduction K (H i) (x i)) =
        ∑ i,
          decompositionHom A K G
            (Representation.Subgroup.finiteRepGrothendieckGroupInduction K (H i) (x i)) := by
          simp [map_sum]
    _ =
        ∑ i,
          Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i)
            (decompositionHom A K (H i) (x i)) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact hcompat i (x i)
    _ =
        ∑ i,
          Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i) (y i) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [hx i]
    _ = z := hdecomp.symm

/-- Helper for Theorem 16-16.1-1: a finite decomposition by subgroup inductions lifts through
`decompositionHom` once the subgroup-side summands lift.  The compatibility of `decompositionHom`
with induction is supplied by the canonical induced-lattice bridge. -/
theorem finiteRepGrothendieckClass_mem_range_decompositionHom_of_induction_decomposition'
    {ι : Type*} [Fintype ι]
    (H : ι → Subgroup G)
    (y : ∀ i, R₀[k](H i))
    (z : R₀[k](G))
    (hdecomp :
      z =
        ∑ i,
          Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i) (y i))
    (hRange : ∀ i, y i ∈ Set.range (decompositionHom A K (H i))) :
    z ∈ Set.range (decompositionHom A K G) := by
  exact
    finiteRepGrothendieckClass_mem_range_decompositionHom_of_induction_decomposition
      H y z hdecomp hRange
      (fun i x ↦
        decompositionHom_subgroupInduction_of_bridge
          (H i) (hind_complete (H i)) x)

/-- Helper for Theorem 16-16.1-1: in the cyclotomic-intermediate-field setting of Serre's
Theorem 39, surjectivity of `decompositionHom` on all `Γ_K`-elementary subgroups implies
surjectivity for the ambient group. -/
theorem decompositionHom_surjective_of_gammaElementary_subgroups
    {L : Type u} [Field L] [NumberField L]
    [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
    (K₀ : IntermediateField ℚ L) [Algebra A K₀] [IsFractionRing A K₀]
    (hSub :
      ∀ H : Subgroup G, Subgroup.IsGammaElementary (Γ[K₀](G)) H →
        Function.Surjective (decompositionHom A K₀ H)) :
    Function.Surjective (decompositionHom A K₀ G) := by
  classical
  intro z
  rcases
      gammaElementarySubgroupFiniteRepGrothendieckInduction_surjective
        K₀ z with
    ⟨ι, hι, H, hH, y, hz⟩
  letI : Fintype ι := hι
  have hRange : ∀ i, y i ∈ Set.range (decompositionHom A K₀ (H i)) := by
    intro i
    exact hSub (H i) (hH i) (y i)
  exact
    finiteRepGrothendieckClass_mem_range_decompositionHom_of_induction_decomposition'
      H y z hz hRange

-- `decompositionHom_surjective_of_brauer_induction` (Serre's Theorem 33, surjectivity of `d`) is
-- proved further below, in the `LargeFieldSurjectivity` section, once the elementary-subgroup
-- lifting theorem `decompositionHom_surjective_of_isElementary` (Serre's Theorem 41) is available.
-- It is stated in the faithful cyclotomic DVR framework (`K = Frac A` an intermediate field of a
-- cyclotomic realization of the exponent of `G`, with `Γ_K = ⊥`), matching Theorem 17-17.2-1: the
-- earlier abstract-field statement quantified over an unrelated large field `K` is not provable
-- from the repository's Brauer induction, which is itself set in that cyclotomic framework.

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

-- The simple-class preimage wrappers `exists_preimage_of_simple_class_of_hasEnoughRootsOfUnity` and
-- `simple_class_mem_range_decompositionHom_of_hasEnoughRootsOfUnity` are also given below in the
-- `LargeFieldSurjectivity` section, in the same cyclotomic DVR framework.

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
            rw [Finsupp.sum, Finsupp.sum, map_sum]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            exact map_zsmul (decompositionHom A K G) ((b.repr y) i) (x i)
    _ = (b.repr y).sum fun i a ↦ a • b i := by
          simp [Finsupp.sum, hx]
    _ = y := by
          simpa [Finsupp.linearCombination_apply, Finsupp.sum] using b.linearCombination_repr y

omit [IsDomain A] [IsDiscreteValuationRing A] [Finite G] in
/-- Helper for Theorem 16-16.1-1: rebundling the underlying representation of a finite-dimensional
representation does not change its Grothendieck class. -/
private theorem finiteRepGrothendieckClass_fdRepOf_rho_eq
    (S : FDRep k G) :
    [FDRep.of S.ρ]₀ = [S]₀ := by
  -- Compare the two finite-representation owners by the identity equivariant map.
  refine finiteRepGrothendieckClass_eq_of_nonempty_iso ⟨?_⟩
  let fRep : (forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of S.ρ) ⟶
      (forget₂ (FDRep k G) (Rep k G)).obj S :=
    Rep.ofHom ⟨LinearMap.id, fun g ↦ by ext x; rfl⟩
  let gRep : (forget₂ (FDRep k G) (Rep k G)).obj S ⟶
      (forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of S.ρ) :=
    Rep.ofHom ⟨LinearMap.id, fun g ↦ by ext x; rfl⟩
  refine ⟨(FDRep.forget₂HomLinearEquiv _ _) fRep,
    (FDRep.forget₂HomLinearEquiv _ _) gRep, ?_, ?_⟩
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    ext x
    rfl
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    ext x
    rfl

/-- Helper for Theorem 16-16.1-1: an explicit free finite `A[G]`-lift of a simple
residue-field representation puts its class in the image of `decompositionHom`. -/
private theorem simple_class_mem_range_of_residueFieldLift_local
    (S : FDRep k G) [Simple S]
    (hS :
      ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module A P)
        (_ : Module.Free A P) (_ : Module.Finite A P)
        (ρA : Representation A G P)
        (red :
          letI : Module A S := Module.compHom S (algebraMap A k)
          P →ₗ[A] S),
          IsResidueFieldLift S.ρ ρA red) :
    [S]₀ ∈ Set.range (decompositionHom A K G) := by
  rcases hS with ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hred⟩
  letI : AddCommGroup P := hPadd
  letI : Module A P := hPmod
  letI : Module.Free A P := hPfree
  letI : Module.Finite A P := hPfinite
  -- Chapter `15` turns an actual residue-field lift into a decomposition-map preimage.
  have hOf : [FDRep.of S.ρ]₀ ∈ Set.range (decompositionHom A K G) :=
    finiteRepClass_mem_range_decompositionHom_of_isResidueFieldLift S.ρ ρA red hred
  simpa [finiteRepGrothendieckClass_fdRepOf_rho_eq S] using hOf

/-- Helper for Theorem 16-16.1-1: if every simple residue-field representation has a free finite
`A[G]`-lift, then the decomposition homomorphism is surjective.  This is the basis argument used
after Serre's Theorem `41` supplies the elementary-subgroup lifting step. -/
theorem decompositionHom_surjective_of_simple_residueField_lifts
    (hLift :
      ∀ S : FDRep k G, Simple S →
        ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module A P)
          (_ : Module.Free A P) (_ : Module.Finite A P)
          (ρA : Representation A G P)
          (red :
            letI : Module A S := Module.compHom S (algebraMap A k)
            P →ₗ[A] S),
            IsResidueFieldLift S.ρ ρA red) :
    Function.Surjective (decompositionHom A K G) := by
  classical
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :
      ∃ (ι : Type (u + 1)) (π : ι → FDRep k G),
        PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π :=
    exists_complete_pairwise_nonisomorphic_simple_family_surjectivity
  -- It is enough to lift the basis vectors `[π i]₀`.
  refine
    decompositionHom_surjective_of_complete_simple_family
      π hπ_pairwise hπ_complete ?_
  intro i
  letI : Simple (π i) := hπ_complete.isSimple i
  exact
    simple_class_mem_range_of_residueFieldLift_local (π i) (hLift (π i) inferInstance)

/-- Helper for Theorem 16-16.1-1: Serre's condition `(R')` is a sufficient image criterion for
the decomposition homomorphism.  This records only the formal consequence of actual simple
stable-lattice lifts; the large-field hypothesis alone is deliberately not used here. -/
theorem decompositionHom_surjective_of_satisfiesConditionRPrime
    (hR' : SatisfiesConditionRPrime A K G) :
    Function.Surjective (decompositionHom A K G) := by
  classical
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :
      ∃ (ι : Type (u + 1)) (π : ι → FDRep k G),
        PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π :=
    exists_complete_pairwise_nonisomorphic_simple_family_surjectivity
  -- Condition `(R')` gives a stable-lattice lift for each simple basis vector.
  refine
    decompositionHom_surjective_of_complete_simple_family
      π hπ_pairwise hπ_complete ?_
  intro i
  letI : Simple (π i) := hπ_complete.isSimple i
  exact
    simple_class_mem_range_of_rprime_lift_local (π i) (hR' (π i) inferInstance)

section LargeFieldSurjectivity

variable [HenselianLocalRing A]
variable {p : ℕ} [hpp : Fact p.Prime] [hCharP : CharP (IsLocalRing.ResidueField A) p]

include hpp hCharP in
/-- Serre's Theorem 41 (large-field / Henselian case): on an elementary subgroup `H` of `G`, the
decomposition homomorphism is surjective.  Every simple `k[H]`-module is, after the elementary
decomposition `H ≅ S₀ × P` (with `P` the `p`-Sylow and `|S₀|` prime to `p`), an inflation of a
simple `k[S₀]`-module, which lifts to a free `A[S₀]`-representation (Maschke + Henselian lifting,
`exists_residueFieldLift`); the inflation of that lift is the required residue-field lift over `H`,
and the basis argument `decompositionHom_surjective_of_simple_residueField_lifts` finishes. -/
theorem decompositionHom_surjective_of_isElementary
    (H : Subgroup G) (hH : IsElementary H) :
    Function.Surjective (decompositionHom A K H) := by
  classical
  haveI : Finite ↥H := Finite.of_injective H.subtype H.subtype_injective
  apply decompositionHom_surjective_of_simple_residueField_lifts
  intro S hS
  haveI : Simple S := hS
  haveI : Representation.IsIrreducible S.ρ := FDRep.isIrreducible_of_simple S
  -- Serre's elementary decomposition `H ≅ S₀ × P` with `S₀` prime-to-`p` and `P` a `p`-group.
  have hcomp :
      ∃ (S₀ P : Subgroup H),
        Nat.Coprime p (Nat.card S₀) ∧
          IsPGroup p P ∧
            S₀ ≤ Subgroup.centralizer (P : Set H) ∧
              S₀.IsComplement' P :=
    elementary_primeToP_pGroup_complement_forSurjectivity H hH
  obtain ⟨S₀, P, hS₀, hP, hS₀Pcent, hS₀Pcomp⟩ :=
    hcomp
  haveI : Finite ↥S₀ := Finite.of_injective S₀.subtype S₀.subtype_injective
  haveI : Finite ↥P := Finite.of_injective P.subtype P.subtype_injective
  have hcomm : ∀ s : S₀, ∀ p' : P, Commute ((s : ↥H)) ((p' : ↥H)) := by
    intro s p'
    exact (Subgroup.mem_centralizer_iff.mp (hS₀Pcent s.2) (p' : ↥H) p'.2).symm
  let e : (S₀ × P) ≃* ↥H := hS₀Pcomp.prodMulEquiv hcomm
  -- Pull `S` back to `S₀ × P`; it stays simple and the `p`-group factor acts trivially.
  let τprod : FDRep k (S₀ × P) := FDRep.of (S.ρ.comp e.toMonoidHom)
  haveI hτprodIrr : Representation.IsIrreducible τprod.ρ :=
    isIrreducible_comp_mulEquiv_forSurjectivity e S.ρ
  haveI : Simple τprod := FDRep.simple_of_isIrreducible τprod
  have hTriv : Representation.IsTrivial (τprod.ρ.comp (MonoidHom.inr S₀ P)) :=
    simple_right_factor_isTrivial_of_isPGroup hP τprod
  obtain ⟨ρS, hρSirr, hfact⟩ := split_product_simple_factorization τprod hTriv
  let U : FDRep k ↥S₀ := FDRep.of ρS
  haveI : Representation.IsIrreducible U.ρ := hρSirr
  -- The inflation hom `f : H →* S₀` recovering `S` from the left factor.
  let f : ↥H →* ↥S₀ := (MonoidHom.fst S₀ P).comp e.symm.toMonoidHom
  have hrep_eq : U.ρ.comp f = S.ρ := by
    have hfact' : U.ρ.comp (MonoidHom.fst S₀ P) = S.ρ.comp e.toMonoidHom := hfact.symm
    have hassoc : U.ρ.comp f = (U.ρ.comp (MonoidHom.fst S₀ P)).comp e.symm.toMonoidHom := rfl
    rw [hassoc, hfact']
    ext g x
    show S.ρ (e.toMonoidHom (e.symm.toMonoidHom g)) x = S.ρ g x
    simp
  -- The prime-to-`p` residue-field lift of `U` over `S₀`.
  have hS₀dvd : ¬ p ∣ Nat.card ↥S₀ :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mp hS₀
  obtain ⟨Pm, hPmAdd, hPmMod, hPmFree, hPmFin, ρA0, red, hLift0⟩ :=
    exists_residueFieldLift hS₀dvd U.ρ
  letI := hPmAdd
  letI := hPmMod
  letI := hPmFree
  letI := hPmFin
  -- Inflate the lift along `f` (its reduction stays the canonical residue-field reduction).
  refine ⟨Pm, hPmAdd, hPmMod, hPmFree, hPmFin, ρA0.comp f, red, ?_⟩
  have hinfl := LinearMap.IsResidueFieldReduction.comp_monoidHom hLift0 f
  -- `hinfl : IsResidueFieldLift (U.ρ.comp f) (ρA0.comp f) red`; rewrite `U.ρ.comp f = S.ρ`.
  exact hrep_eq ▸ hinfl

include hpp hCharP in
/-- Serre's Theorem 33 (Theorem 16-16.1-1), faithful cyclotomic DVR form: the decomposition
homomorphism `d = decompositionHom A K₀ G` is surjective, where `K₀` is an intermediate field of a
cyclotomic realization `L ⊇ ℚ` of the exponent of `G` that is large enough to make Serre's
arithmetic subgroup `Γ_{K₀}` trivial (`hΓ`).  Theorem `39`
(`gammaElementarySubgroupFiniteRepGrothendieckInduction_surjective`) generates `R₀[k](G)` by
induction from `Γ_{K₀}`-elementary subgroups — here ordinary elementary subgroups, since
`Γ_{K₀} = ⊥` — `d` commutes with subgroup induction by the induced-lattice/reduction bridge, and
Theorem `41` (`decompositionHom_surjective_of_isElementary`) supplies the elementary lifting step. -/
theorem decompositionHom_surjective_of_brauer_induction
    {L : Type u} [Field L] [NumberField L]
    [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
    (K₀ : IntermediateField ℚ L) [Algebra A K₀] [IsFractionRing A K₀]
    (hΓ : Γ[K₀](G) = ⊥) :
    Function.Surjective (decompositionHom A K₀ G) := by
  apply decompositionHom_surjective_of_gammaElementary_subgroups K₀
  intro H hH
  rw [hΓ] at hH
  refine decompositionHom_surjective_of_isElementary H ?_
  rcases hH with ⟨q, hq⟩
  exact ⟨q, (Subgroup.IsGammaPElementary.bot_iff_isPElementary q H).1 hq⟩

include hpp hCharP in
/-- Infrastructure for Theorem 16-16.1-1: in the large-field cyclotomic DVR setting, every simple
residue-field class has an explicit preimage under `decompositionHom`. -/
theorem exists_preimage_of_simple_class_of_hasEnoughRootsOfUnity
    {L : Type u} [Field L] [NumberField L]
    [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
    (K₀ : IntermediateField ℚ L) [Algebra A K₀] [IsFractionRing A K₀]
    (hΓ : Γ[K₀](G) = ⊥)
    (S : FDRep k G) [Simple S] :
    ∃ x, decompositionHom A K₀ G x = [S]₀ :=
  decompositionHom_surjective_of_brauer_induction K₀ hΓ [S]₀

include hpp hCharP in
/-- Infrastructure for Theorem 16-16.1-1: in the large-field cyclotomic DVR setting, every simple
residue-field class belongs to the image of the decomposition homomorphism. -/
theorem simple_class_mem_range_decompositionHom_of_hasEnoughRootsOfUnity
    {L : Type u} [Field L] [NumberField L]
    [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
    (K₀ : IntermediateField ℚ L) [Algebra A K₀] [IsFractionRing A K₀]
    (hΓ : Γ[K₀](G) = ⊥)
    (S : FDRep k G) [Simple S] :
    [S]₀ ∈ Set.range (decompositionHom A K₀ G) :=
  decompositionHom_surjective_of_brauer_induction K₀ hΓ [S]₀

include hpp hCharP in
/-- Infra 16 1 DecompositionSurjectivity (Serre's Theorem 33): in the large-field cyclotomic DVR
setting, the decomposition homomorphism `decompositionHom A K₀ G : R₀[K₀](G) → R₀[k](G)` is
surjective. -/
theorem decompositionHom_surjective_of_hasEnoughRootsOfUnity
    {L : Type u} [Field L] [NumberField L]
    [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
    (K₀ : IntermediateField ℚ L) [Algebra A K₀] [IsFractionRing A K₀]
    (hΓ : Γ[K₀](G) = ⊥) :
    Function.Surjective (decompositionHom A K₀ G) :=
  decompositionHom_surjective_of_brauer_induction K₀ hΓ

end LargeFieldSurjectivity

end

end Representation
