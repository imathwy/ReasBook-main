import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3.ResidueFieldLift
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.ReductionMkQ
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2

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

/-- Helper for Theorem 16-16.1-1: the non-reducible scalar-extension owner attached to an
`A[G]`-representation used as a residue-field lift. -/
def residueFieldLiftScalarExtensionOwner
    {P : Type u} [AddCommGroup P] [Module A P] [Module.Free A P] [Module.Finite A P]
    (ρA : Representation A G P) : FDRep K G :=
  FDRep.of (Representation.scalarExtension ρA)

/-- Helper for Theorem 16-16.1-1: build an `A`-linear map into an abstract `FDRep` owner from
raw map data. -/
private noncomputable def rangeMapLinearMap
    {P : Type u} [AddCommGroup P] [Module A P]
    (V : FDRep K G) (toFun : P → V.V)
    (hadd : ∀ x y, toFun (x + y) = toFun x + toFun y)
    (hsmul : ∀ (a : A) (x : P), toFun (a • x) = a • toFun x) :
    P →ₗ[A] V.V where
  toFun := toFun
  map_add' := hadd
  map_smul' := hsmul

/-- Helper for Theorem 16-16.1-1: assemble a stable lattice as the range of a map into an
abstract `FDRep` owner. -/
private noncomputable def stableLatticeOfRangeMap
    {P : Type u} [AddCommGroup P] [Module A P]
    (V : FDRep K G) (f : P →ₗ[A] V.V)
    (hstab : ∀ (g : G) ⦃x : V.V⦄, x ∈ LinearMap.range f → V.ρ g x ∈ LinearMap.range f)
    (hlat : Submodule.IsLattice K (LinearMap.range f)) :
    StableLattice A V.ρ where
  toSubmodule := LinearMap.range f
  apply_mem_toSubmodule := hstab
  isLattice := hlat

/-- Helper for Theorem 16-16.1-1: the literal scalar-extension map preserves addition. -/
private theorem residueFieldLiftScalarExtensionOwner_literal_map_add
    {P : Type u} [AddCommGroup P] [Module A P] [Module.Free A P] [Module.Finite A P]
    (ρA : Representation A G P) (x y : P) :
    (TensorProduct.mk A K P 1 (x + y) :
        (residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA).V) =
      (TensorProduct.mk A K P 1 x :
        (residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA).V) +
      (TensorProduct.mk A K P 1 y :
        (residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA).V) := by
  change (TensorProduct.mk A K P 1 (x + y) : K ⊗[A] P) =
    TensorProduct.mk A K P 1 x + TensorProduct.mk A K P 1 y
  rw [map_add]

/-- Helper for Theorem 16-16.1-1: the raw literal scalar-extension function evaluates to
`1 ⊗ x`. -/
private theorem residueFieldLiftScalarExtensionOwner_literal_raw_apply
    {P : Type u} [AddCommGroup P] [Module A P] [Module.Free A P] [Module.Finite A P]
    (ρA : Representation A G P) (x : P) :
    (fun x : P ↦
      (TensorProduct.mk A K P 1 x :
        (residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA).V)) x =
      TensorProduct.mk A K P 1 x := rfl

/-- Helper for Theorem 16-16.1-1: the literal scalar-extension function is `A`-linear. -/
private theorem residueFieldLiftScalarExtensionOwner_literal_toFun_smul
    {P : Type u} [AddCommGroup P] [Module A P] [Module.Free A P] [Module.Finite A P]
    (ρA : Representation A G P)
    (toFun : P →
      (residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA).V)
    (htoFun : ∀ x, toFun x = TensorProduct.mk A K P 1 x) :
    ∀ (a : A) (x : P), toFun (a • x) = a • toFun x := by
  intro a x
  rw [htoFun, htoFun]
  change (TensorProduct.mk A K P 1 (a • x) : K ⊗[A] P) =
    (algebraMap A K a) • (TensorProduct.mk A K P 1 x : K ⊗[A] P)
  simp only [TensorProduct.mk_apply]
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul,
    Algebra.smul_def, mul_one]

/-- Helper for Theorem 16-16.1-1: Serre's literal map `x ↦ 1 ⊗ x` into the
scalar-extension owner. -/
private noncomputable def residueFieldLiftScalarExtensionOwner_literal_map
    {P : Type u} [AddCommGroup P] [Module A P] [Module.Free A P] [Module.Finite A P]
    (ρA : Representation A G P) :
    P →ₗ[A] (residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA).V :=
  rangeMapLinearMap (residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA)
    (fun x ↦ TensorProduct.mk A K P 1 x)
    (residueFieldLiftScalarExtensionOwner_literal_map_add
      (A := A) (K := K) (G := G) ρA)
    (residueFieldLiftScalarExtensionOwner_literal_toFun_smul
      (A := A) (K := K) (G := G) ρA
      (fun x ↦ TensorProduct.mk A K P 1 x)
      (residueFieldLiftScalarExtensionOwner_literal_raw_apply
        (A := A) (K := K) (G := G) ρA))

/-- Helper for Theorem 16-16.1-1: the literal map evaluates to the pure tensor `1 ⊗ x`. -/
private theorem residueFieldLiftScalarExtensionOwner_literal_map_apply
    {P : Type u} [AddCommGroup P] [Module A P] [Module.Free A P] [Module.Finite A P]
    (ρA : Representation A G P) (x : P) :
    residueFieldLiftScalarExtensionOwner_literal_map (A := A) (K := K) (G := G) ρA x =
      TensorProduct.mk A K P 1 x := rfl

/-- Helper for Theorem 16-16.1-1: over the fraction field, the literal map is injective. -/
private theorem residueFieldLiftScalarExtensionOwner_literal_map_injective
    {P : Type u} [AddCommGroup P] [Module A P] [Module.Free A P] [Module.Finite A P]
    (ρA : Representation A G P) :
    Function.Injective
      (residueFieldLiftScalarExtensionOwner_literal_map
        (A := A) (K := K) (G := G) ρA) := by
  let b : Module.Basis (Module.Free.ChooseBasisIndex A P) A P :=
    Module.Free.chooseBasis A P
  intro x y hxy
  apply b.repr.injective
  ext i
  have hxy' : (TensorProduct.mk A K P 1 x : K ⊗[A] P) =
      TensorProduct.mk A K P 1 y := by
    simpa [residueFieldLiftScalarExtensionOwner_literal_map_apply] using hxy
  have hcoord :=
    congrArg (fun z ↦ ((Algebra.TensorProduct.basis K b).repr z) i) hxy'
  apply IsFractionRing.injective A K
  simpa using hcoord

/-- Helper for Theorem 16-16.1-1: the image of the literal map is stable under the
scalar-extended group action. -/
private theorem residueFieldLiftScalarExtensionOwner_literal_map_apply_mem_range
    {P : Type u} [AddCommGroup P] [Module A P] [Module.Free A P] [Module.Finite A P]
    (ρA : Representation A G P)
    (g : G)
    {x : (residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA).V}
    (hx :
      x ∈
        (residueFieldLiftScalarExtensionOwner_literal_map
          (A := A) (K := K) (G := G) ρA).range) :
    (residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA).ρ g x ∈
      (residueFieldLiftScalarExtensionOwner_literal_map
        (A := A) (K := K) (G := G) ρA).range := by
  rcases hx with ⟨y, rfl⟩
  refine ⟨ρA g y, ?_⟩
  rw [residueFieldLiftScalarExtensionOwner_literal_map_apply]
  rw [residueFieldLiftScalarExtensionOwner_literal_map_apply]
  change (1 : K) ⊗ₜ[A] ρA g y =
    ((Module.End.baseChangeHom A K P) (ρA g)) ((1 : K) ⊗ₜ[A] y)
  exact (LinearMap.baseChange_tmul (f := ρA g) (A := K) (1 : K) y).symm

/-- Helper for Theorem 16-16.1-1: the image of the literal map is an `A`-lattice in the
scalar extension. -/
private theorem residueFieldLiftScalarExtensionOwner_literal_map_range_isLattice
    {P : Type u} [AddCommGroup P] [Module A P] [Module.Free A P] [Module.Finite A P]
    (ρA : Representation A G P) :
    Submodule.IsLattice K
      ((residueFieldLiftScalarExtensionOwner_literal_map
        (A := A) (K := K) (G := G) ρA).range) := by
  refine
    { fg := ?_
      span_eq_top := ?_ }
  · rw [LinearMap.range_eq_map]
    exact Submodule.FG.map _
      ((Module.Finite.iff_fg (N := (⊤ : Submodule A P))).1 inferInstance)
  · let b : Module.Basis (Module.Free.ChooseBasisIndex A P) A P :=
      Module.Free.chooseBasis A P
    apply eq_top_iff.2
    intro x hx
    have hxrepr :
        x = ∑ i, ((Algebra.TensorProduct.basis K b).repr x) i •
          (Algebra.TensorProduct.basis K b) i := by
      simpa using ((Algebra.TensorProduct.basis K b).sum_repr x).symm
    rw [hxrepr]
    refine Submodule.sum_mem _ ?_
    intro i hi
    refine Submodule.smul_mem _ _ ?_
    apply Submodule.subset_span
    refine ⟨b i, ?_⟩
    rw [residueFieldLiftScalarExtensionOwner_literal_map_apply]
    simpa using (Algebra.TensorProduct.basis_apply (A := K) (b := b) i)

/-- Helper for Theorem 16-16.1-1: Serre's literal image is a stable lattice in the
scalar-extension owner. -/
private noncomputable def residueFieldLiftScalarExtensionOwner_literal_lattice
    {P : Type u} [AddCommGroup P] [Module A P] [Module.Free A P] [Module.Finite A P]
    (ρA : Representation A G P) :
    StableLattice A
      (residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA).ρ :=
  stableLatticeOfRangeMap
    (residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA)
    (residueFieldLiftScalarExtensionOwner_literal_map
      (A := A) (K := K) (G := G) ρA)
    (residueFieldLiftScalarExtensionOwner_literal_map_apply_mem_range
      (A := A) (K := K) (G := G) ρA)
    (residueFieldLiftScalarExtensionOwner_literal_map_range_isLattice
      (A := A) (K := K) (G := G) ρA)

/-- Helper for Theorem 16-16.1-1: the tautological group-algebra module of a representation is
canonically equivalent to its carrier. -/
private theorem nonempty_asModuleLinearEquiv_target
    {F : Type u} [Field F]
    {V : Type u} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) :
    letI : Module F[G] V := Module.compHom V ρ.asAlgebraHom.toRingHom
    letI : IsScalarTower F F[G] V :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change ρ.asAlgebraHom (algebraMap F F[G] a) x = a • x
        simp [Algebra.smul_def]
    Nonempty (ρ.asModule ≃ₗ[F[G]] V) := by
  letI : Module F[G] V := Module.compHom V ρ.asAlgebraHom.toRingHom
  letI : IsScalarTower F F[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρ.asAlgebraHom (algebraMap F F[G] a) x = a • x
      simp [Algebra.smul_def]
  refine ⟨
    { toFun := fun x ↦ ρ.asModuleEquiv x
      invFun := fun x ↦ ρ.asModuleEquiv.symm x
      left_inv := fun x ↦ ρ.asModuleEquiv.symm_apply_apply x
      right_inv := fun x ↦ ρ.asModuleEquiv.apply_symm_apply x
      map_add' := fun x y ↦ ρ.asModuleEquiv.map_add x y
      map_smul' := ?_ }⟩
  intro a x
  calc
    ρ.asModuleEquiv (a • x) = ρ.asAlgebraHom a (ρ.asModuleEquiv x) := by
      simpa using Representation.asModuleEquiv_map_smul (ρ := ρ) a x
    _ = a • ρ.asModuleEquiv x := rfl

/-- Helper for Theorem 16-16.1-1: a group-algebra equivalence between owner modules gives an
isomorphism in `FDRep`. -/
private theorem fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv
    {F : Type u} [Field F]
    {σ τ : FDRep F G}
    (hστ : Nonempty (asModule σ.ρ ≃ₗ[F[G]] asModule τ.ρ)) :
    Nonempty (σ ≅ τ) := by
  rcases hστ with ⟨e⟩
  let f : Representation.IntertwiningMap σ.ρ τ.ρ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := σ.ρ) (σ := τ.ρ)).symm e.toLinearMap
  let eRep : Representation.Equiv σ.ρ τ.ρ :=
    Representation.Equiv.mk (e.restrictScalars F) f.isIntertwining'
  exact ⟨(Representation.Equiv.toFDRepIso eRep)⟩

/-- Helper for Theorem 16-16.1-1: the literal source module identifies with its range as an
`A[G]`-module. -/
private theorem residueFieldLiftScalarExtensionOwner_literal_range_nonempty_linearEquivGroupAlgebra
    {P : Type u} [AddCommGroup P] [Module A P] [Module.Free A P] [Module.Finite A P]
    (ρA : Representation A G P) :
    letI : Module A[G] P := Module.compHom P ρA.asAlgebraHom.toRingHom
    letI : IsScalarTower A A[G] P :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change ρA.asAlgebraHom (algebraMap A A[G] a) x = a • x
        simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA.asAlgebraHom.commutes a) x
    let L := residueFieldLiftScalarExtensionOwner_literal_lattice
      (A := A) (K := K) (G := G) ρA
    letI : Module A[G] L.toSubmodule := by
      change Module A[G] L.toRepresentation.asModule
      infer_instance
    Nonempty (P ≃ₗ[A[G]] L.toSubmodule) := by
  letI : Module A[G] P := Module.compHom P ρA.asAlgebraHom.toRingHom
  letI : IsScalarTower A A[G] P :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA.asAlgebraHom (algebraMap A A[G] a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA.asAlgebraHom.commutes a) x
  let f := residueFieldLiftScalarExtensionOwner_literal_map (A := A) (K := K) (G := G) ρA
  let L := residueFieldLiftScalarExtensionOwner_literal_lattice
    (A := A) (K := K) (G := G) ρA
  letI : Module A[G] L.toSubmodule := by
    change Module A[G] L.toRepresentation.asModule
    infer_instance
  have hf_inj : Function.Injective f :=
    residueFieldLiftScalarExtensionOwner_literal_map_injective (A := A) (K := K) (G := G) ρA
  let eA : P ≃ₗ[A] L.toSubmodule :=
    LinearEquiv.ofBijective f.rangeRestrict
      ⟨(LinearMap.injective_rangeRestrict_iff (f := f)).2 hf_inj,
        LinearMap.surjective_rangeRestrict f⟩
  refine ⟨
    { toFun := fun x ↦ eA x
      map_add' := fun x y ↦ eA.map_add x y
      invFun := fun x ↦ eA.symm x
      left_inv := eA.left_inv
      right_inv := eA.right_inv
      map_smul' := ?_ }⟩
  intro r x
  refine MonoidAlgebra.induction_on (p := fun r ↦ eA (r • x) = r • eA x) r ?_ ?_ ?_
  · intro g
    apply Subtype.ext
    have hof : (MonoidAlgebra.of A G g) • eA x = L.toRepresentation g (eA x) := by
      rw [← Representation.asAlgebraHom_single_one (ρ := L.toRepresentation) g]
      rfl
    rw [hof, StableLattice.toRepresentation_apply_coe]
    show f (MonoidAlgebra.of A G g • x) =
      (residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA).ρ g (f x)
    rw [residueFieldLiftScalarExtensionOwner_literal_map_apply]
    rw [residueFieldLiftScalarExtensionOwner_literal_map_apply]
    have hsource : MonoidAlgebra.of A G g • x = ρA g x := by
      change ρA.asAlgebraHom (MonoidAlgebra.of A G g) x = ρA g x
      simp [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single]
    change (TensorProduct.mk A K P 1 (MonoidAlgebra.of A G g • x) : K ⊗[A] P) =
      ((Module.End.baseChangeHom A K P) (ρA g)) ((1 : K) ⊗ₜ[A] x)
    rw [hsource]
    exact (LinearMap.baseChange_tmul (f := ρA g) (A := K) (1 : K) x).symm
  · intro a b ha hb
    simp [add_smul, ha, hb]
  · intro c a ha
    rw [smul_assoc, map_smul, ha, smul_assoc]

/-- Helper for Theorem 16-16.1-1: an explicit residue-field lift is the reduction of the
literal stable lattice in the scalar extension of the lift. -/
theorem residueFieldLift_scalarExtension_reduction_iso
    {P : Type u} [AddCommGroup P] [Module A P] [Module.Free A P] [Module.Finite A P]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (ρA : Representation A G P)
    (red :
      letI : Module A V := Module.compHom V (algebraMap A k)
      P →ₗ[A] V)
    (hred : IsResidueFieldLift ρ ρA red) :
    ∃ L : StableLattice A
        (residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA).ρ,
      Nonempty (FDRep.of L.reductionRepresentation ≅ FDRep.of ρ) := by
  let L := residueFieldLiftScalarExtensionOwner_literal_lattice
    (A := A) (K := K) (G := G) ρA
  refine ⟨L, ?_⟩
  letI : Module A[G] P := Module.compHom P ρA.asAlgebraHom.toRingHom
  letI : IsScalarTower A A[G] P :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA.asAlgebraHom (algebraMap A A[G] a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA.asAlgebraHom.commutes a) x
  letI : Module A V := Module.compHom V (algebraMap A k)
  letI : IsScalarTower A k V :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module k[G] V := Module.compHom V ρ.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρ.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
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
  rcases
      residueFieldLiftScalarExtensionOwner_literal_range_nonempty_linearEquivGroupAlgebra
        (A := A) (K := K) (G := G) ρA with
    ⟨eAG⟩
  have hmkQ :
      (Submodule.mkQ L.maximalIdealSubmodule :
        L.toSubmodule →ₗ[A] L.reduction).IsResidueFieldReduction G := by
    simpa [L] using
      StableLattice.reduction_mkQ_isResidueFieldReduction_local
        (A := A) (K := K) (G := G) L
  have hred₀ : red.IsResidueFieldReduction G := by
    simpa [IsResidueFieldLift] using hred
  have hredL :
      (red.comp (eAG.symm.restrictScalars A).toLinearMap).IsResidueFieldReduction G := by
    exact
      LinearMap.IsResidueFieldReduction.comp_sourceLinearEquiv
        (A := A) (G := G) hred₀ eAG.symm
  rcases
      LinearMap.IsResidueFieldReduction.targetLinearEquivOfCommonReduction
        (A := A) (G := G) hmkQ hredL with
    ⟨ered⟩
  have hLowner :
      Nonempty (asModule (FDRep.of L.reductionRepresentation).ρ ≃ₗ[k[G]] L.reduction) := by
    simpa using
      nonempty_asModuleLinearEquiv_target
        (G := G) (ρ := (FDRep.of L.reductionRepresentation).ρ)
  have hVowner :
      Nonempty (asModule (FDRep.of ρ).ρ ≃ₗ[k[G]] V) := by
    simpa using
      nonempty_asModuleLinearEquiv_target
        (G := G) (ρ := (FDRep.of ρ).ρ)
  rcases hLowner with ⟨eLowner⟩
  rcases hVowner with ⟨eVowner⟩
  exact
    fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv
      (G := G)
      ⟨eLowner.trans (ered.trans eVowner.symm)⟩

/-- Helper for Theorem 16-16.1-1: a finite residue-field representation with an explicit
`A[G]`-lift lies in the range of the decomposition homomorphism. -/
theorem finiteRepClass_mem_range_decompositionHom_of_isResidueFieldLift
    {P : Type u} [AddCommGroup P] [Module A P] [Module.Free A P] [Module.Finite A P]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (ρA : Representation A G P)
    (red :
      letI : Module A V := Module.compHom V (algebraMap A k)
      P →ₗ[A] V)
    (hred : IsResidueFieldLift ρ ρA red) :
    [FDRep.of ρ]₀ ∈ Set.range (decompositionHom A K G) := by
  rcases
      residueFieldLift_scalarExtension_reduction_iso
        (A := A) (K := K) (G := G) ρ ρA red hred with
    ⟨L, hL⟩
  exact
    finiteRepClass_mem_range_decompositionHom_of_exists_stableLattice_reduction
      (A := A) (K := K) (G := G) (FDRep.of ρ)
      ⟨residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA, L, hL⟩

/-- Helper for Theorem 16-16.1-1: on the scalar extension of an explicit lift, the decomposition
homomorphism returns the class of the residue-field representation. -/
theorem decompositionHom_fdRepOf_scalarExtension_eq_of_isResidueFieldLift
    {P : Type u} [AddCommGroup P] [Module A P] [Module.Free A P] [Module.Finite A P]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (ρA : Representation A G P)
    (red :
      letI : Module A V := Module.compHom V (algebraMap A k)
      P →ₗ[A] V)
    (hred : IsResidueFieldLift ρ ρA red) :
    decompositionHom A K G
        [residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA]₀ =
      [FDRep.of ρ]₀ := by
  rcases
      residueFieldLift_scalarExtension_reduction_iso
        (A := A) (K := K) (G := G) ρ ρA red hred with
    ⟨L, hL⟩
  rcases hL with ⟨eL⟩
  calc
    decompositionHom A K G
        [residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA]₀ =
        [FDRep.of L.reductionRepresentation]₀ := by
          simpa using
            decompositionHom_finiteRepClass_eq
              (A := A) (K := K) (G := G)
              (residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA) L
    _ = [FDRep.of ρ]₀ := by
          exact
            finiteRepGrothendieckClass_eq_of_nonempty_iso
              (L := k) (G := G)
              (V := FDRep.of L.reductionRepresentation) (W := FDRep.of ρ) ⟨eL⟩

end

end Representation
