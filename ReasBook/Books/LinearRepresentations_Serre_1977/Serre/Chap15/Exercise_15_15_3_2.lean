import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_1_2
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.ReductionMkQ
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.StableLatticeExactOwner
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.ReductionIsoReflection
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2

noncomputable section

universe u

namespace Representation

open scoped Representation TensorProduct

section ScalarExtensionCompatibility

variable {K : Type u} [Field K]
variable {G : Type u} [Group G] [Finite G]

variable (A : Type u) [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
  [IsDomain A] [IsDiscreteValuationRing A] [Algebra A K] [IsFractionRing A K]

local notation "k" => IsLocalRing.ResidueField A
local notation:max "P_k(" G ")" => finiteProjectiveGroupAlgebraGrothendieckGroup k G
local notation:max "R_K(" G ")" => finiteRepGrothendieckGroup K G
local notation:max "R_k(" G ")" => finiteRepGrothendieckGroup k G
local notation "d" => decompositionHom A K G

local notation "e" => projectiveGrothendieckScalarExtensionHom (A := A) (K := K) (G := G)

/-- Helper for Exercise 15-15.3-2: a representation equivalence induces the corresponding
group-algebra-linear equivalence on owner modules. -/
private noncomputable def representationEquivAsModuleLinearEquiv
    {F : Type u} [Field F]
    {V W : Type u} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    {ρ : Representation F G V} {σ : Representation F G W}
    (hρσ : ρ.Equiv σ) :
    ρ.asModule ≃ₗ[MonoidAlgebra F G] σ.asModule := by
  -- Repackage the representation equivalence as the corresponding module equivalence once.
  refine
    { toFun := (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ)
          hρσ.toIntertwiningMap
      invFun := (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ)
          hρσ.symm.toIntertwiningMap
      left_inv := by
        intro x
        change hρσ.symm (hρσ x) = x
        simp
      right_inv := by
        intro x
        change hρσ (hρσ.symm x) = x
        simp
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro a x
        simp }

/-- Helper for Exercise 15-15.3-2: a group-algebra-linear equivalence of exact owners
repackages as an equivalence of the corresponding representations. -/
private noncomputable def representationEquivOfAsModuleLinearEquiv
    {F : Type u} [Field F]
    {V W : Type u} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    {ρ : Representation F G V} {σ : Representation F G W}
    (eMod : ρ.asModule ≃ₗ[MonoidAlgebra F G] σ.asModule) :
    ρ.Equiv σ := by
  let f : ρ.IntertwiningMap σ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ).symm eMod.toLinearMap
  exact Representation.Equiv.mk (eMod.restrictScalars F) f.isIntertwining'

/-- Helper for Exercise 15-15.3-2: every finite-dimensional owner is isomorphic to the canonical
`FDRep.of` owner rebuilt from its representation. -/
private noncomputable def fdRepIsoOfRhoLocal
    {F : Type u} [Field F] (τ : FDRep F G) : τ ≅ FDRep.of τ.ρ :=
  Action.mkIso (CategoryTheory.Iso.refl _) fun g ↦ by
    ext x
    rfl

/-- Helper for Exercise 15-15.3-2: transporting a residue-field projective generator back across
Serre's reduction equivalence recovers the original lifted projective class. -/
private theorem projectiveGrothendieckReductionEquiv_symm_residueFieldReductionClass_eq
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm
        [Q.residueFieldReduction]ₚ₀ = [Q]ₚ₀ := by
  -- Rewrite the inverse transport through the defining projective reduction class formula.
  have hQ :
      (projectiveGrothendieckReductionEquiv (A := A) (G := G)) [Q]ₚ₀ =
        [Q.residueFieldReduction]ₚ₀ := by
    change projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ =
      [Q.residueFieldReduction]ₚ₀
    exact projectiveGrothendieckReductionHom_projectiveClass_eq (A := A) (G := G) Q
  exact
    (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm_apply_eq.2 hQ.symm

/-- Helper for Exercise 15-15.3-2: Serre's scalar-extension homomorphism sends a reduced
projective generator to the scalar extension of its lift. -/
private theorem projectiveGrothendieckScalarExtensionHom_residueFieldReductionClass_eq
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    e [Q.residueFieldReduction]ₚ₀ = [Q.scalarExtension K]₀ := by
  -- Evaluate `e` via the inverse reduction transport and then collapse both generator formulas.
  calc
    e [Q.residueFieldReduction]ₚ₀ =
        projectiveGrothendieckBaseChangeHom K
          ((projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm
            [Q.residueFieldReduction]ₚ₀) := by
              rw [projectiveGrothendieckScalarExtensionHom_apply]
    _ = projectiveGrothendieckBaseChangeHom K [Q]ₚ₀ := by
          rw [projectiveGrothendieckReductionEquiv_symm_residueFieldReductionClass_eq
            (A := A) (G := G) Q]
    _ = [Q.scalarExtension K]₀ := by
          rw [projectiveGrothendieckBaseChangeHom_projectiveClass_eq]

/-- Helper for Exercise 15-15.3-2: the generator case reduces to comparing one lifted tensor
owner with its reduction and scalar extension. -/
private theorem stableLatticeReductionOwnerLinearEquiv
    (V : FDRep K G) (L : StableLattice A V.ρ) :
    letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
    letI : IsScalarTower A k L.reduction :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    letI : Module (MonoidAlgebra k G) L.reduction := by
      change Module (MonoidAlgebra k G) L.reductionRepresentation.asModule
      infer_instance
    letI : IsScalarTower k (MonoidAlgebra k G) L.reduction := by
      change IsScalarTower k (MonoidAlgebra k G) L.reductionRepresentation.asModule
      infer_instance
    Nonempty
      ((TensorProduct A k L.toSubmodule) ≃ₗ[k] L.reduction) := by
  letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
  letI : IsScalarTower A k L.reduction :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module (MonoidAlgebra k G) L.reduction := by
    change Module (MonoidAlgebra k G) L.reductionRepresentation.asModule
    infer_instance
  letI : IsScalarTower k (MonoidAlgebra k G) L.reduction := by
    change IsScalarTower k (MonoidAlgebra k G) L.reductionRepresentation.asModule
    infer_instance
  -- Reuse the public residue-field-reduction witness attached to the stable lattice quotient map.
  exact ⟨(StableLattice.reduction_mkQ_isResidueFieldReduction_local
    (A := A) (K := K) (G := G) L).1.equiv⟩

/-- Helper for Exercise 15-15.3-2: the base-change equivalence from the exact lattice owner to its
scalar-extended owner is the tautological `k[G]`-linear equivalence on the raw tensor carrier. -/
private theorem stableLatticeScalarExtensionOwnerAsModuleLinearEquiv
    (V : FDRep K G) (L : StableLattice A V.ρ) :
    Nonempty
      (asModule
          (show Representation k G (TensorProduct A k L.toSubmodule) from
            Representation.scalarExtension L.toRepresentation) ≃ₗ[MonoidAlgebra k G]
        TensorProduct A k L.toSubmodule) := by
  let ρ :
      Representation k G (TensorProduct A k L.toSubmodule) :=
    Representation.scalarExtension L.toRepresentation
  -- Transport the `k[G]`-action through `ρ.asModuleEquiv`, then check it matches the raw
  -- tensor-product action by reducing to `MonoidAlgebra` generators and pure tensors.
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
    _ = a • ρ.asModuleEquiv x := by
        refine MonoidAlgebra.induction_on
          (p := fun b : MonoidAlgebra k G =>
            ρ.asAlgebraHom b (ρ.asModuleEquiv x) = b • ρ.asModuleEquiv x) a ?_ ?_ ?_
        · intro g
          induction ρ.asModuleEquiv x using TensorProduct.induction_on with
          | zero =>
              simp [ρ]
          | tmul z y =>
              have hρ :
                  ρ g (z ⊗ₜ[A] y) =
                    (z ⊗ₜ[A] (L.toRepresentation g y) : TensorProduct A k L.toSubmodule) := by
                change
                  ((Module.End.baseChangeHom A k L.toSubmodule) (L.toRepresentation g))
                      (z ⊗ₜ[A] y) =
                    _
                exact LinearMap.baseChange_tmul (f := L.toRepresentation g) (A := k) z y
              have hy :
                  L.toRepresentation g y = MonoidAlgebra.of A G g • y := by
                exact Representation.asModuleEquiv_symm_map_rho
                  (ρ := L.toRepresentation) g y
              have hsmul :
                  MonoidAlgebra.of k G g • (z ⊗ₜ[A] y : TensorProduct A k L.toSubmodule) =
                    (z ⊗ₜ[A] (MonoidAlgebra.of A G g • y) : TensorProduct A k L.toSubmodule) := by
                exact
                  monoidAlgebra_of_smul_tmul
                    (Λ := A) (κ := k) (G := G) (P := L.toSubmodule) g z y
              calc
                ρ.asAlgebraHom (MonoidAlgebra.of k G g) (z ⊗ₜ[A] y)
                    = ρ g (z ⊗ₜ[A] y) := by
                        simp [ρ, Representation.asAlgebraHom_of]
                _ = (z ⊗ₜ[A] (L.toRepresentation g y) : TensorProduct A k L.toSubmodule) := by
                      rw [hρ]
                _ = (z ⊗ₜ[A] (MonoidAlgebra.of A G g • y) : TensorProduct A k L.toSubmodule) := by
                      rw [hy]
                _ = MonoidAlgebra.of k G g • (z ⊗ₜ[A] y : TensorProduct A k L.toSubmodule) := by
                      rw [hsmul]
          | add y z hy hz =>
              calc
                ρ.asAlgebraHom (MonoidAlgebra.of k G g) (y + z)
                    = ρ.asAlgebraHom (MonoidAlgebra.of k G g) y +
                        ρ.asAlgebraHom (MonoidAlgebra.of k G g) z := by
                          simp [map_add]
                _ = MonoidAlgebra.of k G g • y + MonoidAlgebra.of k G g • z := by
                      rw [hy, hz]
                _ = MonoidAlgebra.of k G g • (y + z) := by
                      simp [smul_add]
        · intro b c hb hc
          simp [map_add, add_smul, hb, hc]
        · intro c b hb
          calc
            ρ.asAlgebraHom (c • b) (ρ.asModuleEquiv x)
                = c • ρ.asAlgebraHom b (ρ.asModuleEquiv x) := by
                    simp
            _ = c • (b • ρ.asModuleEquiv x) := by
                  rw [hb]
            _ = (c • b) • ρ.asModuleEquiv x := by
                  simp [smul_smul]

/-- Helper for Exercise 15-15.3-2: the rebundled reduction representation is tautologically
`k[G]`-linearly equivalent to its underlying reduced owner. -/
private theorem stableLatticeReductionRebundledAsModuleLinearEquiv
    (V : FDRep K G) (L : StableLattice A V.ρ) :
    letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
    letI : IsScalarTower A k L.reduction :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    letI : Module (MonoidAlgebra k G) L.reduction := by
      change Module (MonoidAlgebra k G) L.reductionRepresentation.asModule
      infer_instance
    letI : IsScalarTower k (MonoidAlgebra k G) L.reduction := by
      change IsScalarTower k (MonoidAlgebra k G) L.reductionRepresentation.asModule
      infer_instance
    Nonempty
      (asModule ((FDRep.of L.reductionRepresentation).ρ) ≃ₗ[MonoidAlgebra k G]
        L.reduction) := by
  -- Reuse the same public `asModule` bridge for the rebundled reduction representation.
  simpa using
    (nonempty_asModuleLinearEquiv_target_field_local
      (G := G) (ρ := ((FDRep.of L.reductionRepresentation).ρ)))

/-- Helper for Exercise 15-15.3-2: two residue-field reduction maps out of the same exact owner
identify their targets by a canonical `k[G]`-linear equivalence. -/
private theorem targetLinearEquivOfCommonReduction
    {P : Type u} [AddCommGroup P] [Module A P] [Module (MonoidAlgebra A G) P]
      [IsScalarTower A (MonoidAlgebra A G) P]
    {W₁ : Type u} [AddCommGroup W₁] [Module k W₁] [Module A W₁] [IsScalarTower A k W₁]
      [Module (MonoidAlgebra k G) W₁] [IsScalarTower k (MonoidAlgebra k G) W₁]
    {W₂ : Type u} [AddCommGroup W₂] [Module k W₂] [Module A W₂] [IsScalarTower A k W₂]
      [Module (MonoidAlgebra k G) W₂] [IsScalarTower k (MonoidAlgebra k G) W₂]
    {red₁ : P →ₗ[A] W₁} {red₂ : P →ₗ[A] W₂}
    (hred₁ : red₁.IsResidueFieldReduction G)
    (hred₂ : red₂.IsResidueFieldReduction G) :
    Nonempty (W₁ ≃ₗ[MonoidAlgebra k G] W₂) := by
  let eCommon := (hred₁.1.equiv.symm.trans hred₂.1.equiv : W₁ ≃ₗ[k] W₂)
  have happly (x : P) : eCommon (red₁ x) = red₂ x := by
    have h₁ : hred₁.1.equiv (1 ⊗ₜ[A] x) = red₁ x := by
      simpa using hred₁.1.equiv_tmul (1 : k) x
    have h₂ : hred₂.1.equiv (1 ⊗ₜ[A] x) = red₂ x := by
      simpa using hred₂.1.equiv_tmul (1 : k) x
    -- Compare both reductions on the distinguished tensor `1 ⊗ x`.
    calc
      eCommon (red₁ x) = eCommon (hred₁.1.equiv (1 ⊗ₜ[A] x)) := by rw [h₁.symm]
      _ = hred₂.1.equiv (1 ⊗ₜ[A] x) := by
            simp [eCommon]
      _ = red₂ x := h₂
  have hsurj : Function.Surjective red₁ :=
    by
      intro y
      -- Write `y` through the base-change equivalence and then lift the pure tensor.
      obtain ⟨t, rfl⟩ := hred₁.1.equiv.surjective y
      have hres : Function.Surjective (algebraMap A k) := by
        simpa [IsLocalRing.ResidueField.algebraMap_eq] using IsLocalRing.residue_surjective
      obtain ⟨x, hx⟩ := TensorProduct.mk_surjective (R := A) (S := k) (M := P) hres t
      refine ⟨x, ?_⟩
      calc
        red₁ x = (1 : k) • red₁ x := by simp
        _ = hred₁.1.equiv ((TensorProduct.mk A k P 1) x) := by
              symm
              simpa using hred₁.1.equiv_tmul (1 : k) x
        _ = hred₁.1.equiv t := by rw [hx]
  refine
    ⟨{ toFun := eCommon
       invFun := eCommon.symm
       left_inv := eCommon.left_inv
       right_inv := eCommon.right_inv
       map_add' := eCommon.map_add
       map_smul' := ?_ }⟩
  intro a y
  obtain ⟨x, rfl⟩ := hsurj y
  -- Check `k[G]`-linearity on vectors lifted from the common source and extend from
  -- `MonoidAlgebra.of`.
  refine
    MonoidAlgebra.induction_on
      (p := fun b : MonoidAlgebra k G =>
        eCommon (b • red₁ x) = b • eCommon (red₁ x)) a ?_ ?_ ?_
  · intro g
    calc
      eCommon (MonoidAlgebra.of k G g • red₁ x)
          = eCommon (red₁ (MonoidAlgebra.of A G g • x)) := by
              rw [LinearMap.IsResidueFieldReduction.map_monoidAlgebra_of hred₁ g x]
      _ = red₂ (MonoidAlgebra.of A G g • x) := by
            rw [happly]
      _ = MonoidAlgebra.of k G g • red₂ x := by
            rw [LinearMap.IsResidueFieldReduction.map_monoidAlgebra_of hred₂ g x]
      _ = MonoidAlgebra.of k G g • eCommon (red₁ x) := by
            rw [happly]
  · intro b c hb hc
    calc
      eCommon ((b + c) • red₁ x) = eCommon (b • red₁ x + c • red₁ x) := by rw [add_smul]
      _ = eCommon (b • red₁ x) + eCommon (c • red₁ x) := by rw [eCommon.map_add]
      _ = b • eCommon (red₁ x) + c • eCommon (red₁ x) := by rw [hb, hc]
      _ = (b + c) • eCommon (red₁ x) := by rw [add_smul]
  · intro a' b hb
    calc
      eCommon ((a' • b) • red₁ x) = eCommon (a' • (b • red₁ x)) := by rw [smul_assoc]
      _ = a' • eCommon (b • red₁ x) := by rw [eCommon.map_smul]
      _ = a' • (b • eCommon (red₁ x)) := by rw [hb]
      _ = (a' • b) • eCommon (red₁ x) := by rw [smul_assoc]

/-- Helper for Exercise 15-15.3-2: the base-change equivalence from the exact lattice owner to its
reduction matches the rebundled reduced owner as a genuine `k[G]`-module equivalence. -/
private theorem stableLatticeReductionOwnerAsModuleLinearEquiv
    (V : FDRep K G) (L : StableLattice A V.ρ) :
    letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
    letI : IsScalarTower A k L.reduction :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    letI : Module (MonoidAlgebra k G) L.reduction := by
      change Module (MonoidAlgebra k G) L.reductionRepresentation.asModule
      infer_instance
    letI : IsScalarTower k (MonoidAlgebra k G) L.reduction := by
      change IsScalarTower k (MonoidAlgebra k G) L.reductionRepresentation.asModule
      infer_instance
    Nonempty
      ((TensorProduct A k L.toSubmodule) ≃ₗ[MonoidAlgebra k G]
        asModule ((FDRep.of L.reductionRepresentation).ρ)) := by
  letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
  letI : IsScalarTower A k L.reduction :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module (MonoidAlgebra k G) L.reduction := by
    change Module (MonoidAlgebra k G) L.reductionRepresentation.asModule
    infer_instance
  letI : IsScalarTower k (MonoidAlgebra k G) L.reduction := by
    change IsScalarTower k (MonoidAlgebra k G) L.reductionRepresentation.asModule
    infer_instance
  rcases
      targetLinearEquivOfCommonReduction
        (A := A) (G := G)
        (P := L.toSubmodule)
        (W₁ := TensorProduct A k L.toSubmodule)
        (W₂ := L.reduction)
        (red₁ := TensorProduct.mk A k L.toSubmodule 1)
        (red₂ := (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction))
        (MonoidAlgebra.tensorProduct_mk_isResidueFieldReduction
          (Λ := A) (G := G) (P := L.toSubmodule))
        (StableLattice.reduction_mkQ_isResidueFieldReduction_local
          (A := A) (K := K) (G := G) L) with
    ⟨ered⟩
  rcases stableLatticeReductionRebundledAsModuleLinearEquiv
      (A := A) (K := K) (G := G) V L with
    ⟨erebundle⟩
  -- Compare the two reductions on the common exact owner, then invert the rebundled owner bridge.
  exact ⟨ered.trans erebundle.symm⟩

/-- Helper for Exercise 15-15.3-2: the intrinsic residue-field reduction of a projective
`A[G]`-module already carries the tautological `MonoidAlgebra k G`-module owner. -/
private theorem residueFieldReductionAsModuleLinearEquiv
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    letI : Module k Q.residueFieldReduction.V :=
      Module.compHom Q.residueFieldReduction.V (algebraMap k (MonoidAlgebra k G))
    letI : IsScalarTower k (MonoidAlgebra k G) Q.residueFieldReduction.V :=
      IsScalarTower.of_compHom k (MonoidAlgebra k G) Q.residueFieldReduction.V
    Nonempty
      (asModule Q.residueFieldReduction.toFiniteRep.ρ ≃ₗ[MonoidAlgebra k G]
        Q.residueFieldReduction.V) := by
  letI : Module k Q.residueFieldReduction.V :=
    Module.compHom Q.residueFieldReduction.V (algebraMap k (MonoidAlgebra k G))
  letI : IsScalarTower k (MonoidAlgebra k G) Q.residueFieldReduction.V :=
    IsScalarTower.of_compHom k (MonoidAlgebra k G) Q.residueFieldReduction.V
  change Nonempty
    ((Representation.ofModule
        (ModuleCat.of (MonoidAlgebra k G) Q.residueFieldReduction.V)).asModule
          ≃ₗ[MonoidAlgebra k G]
      Q.residueFieldReduction.V)
  let Mmod : ModuleCat (MonoidAlgebra k G) :=
    ModuleCat.of (MonoidAlgebra k G) Q.residueFieldReduction.V
  let toFun : (Representation.ofModule Mmod).asModule → Q.residueFieldReduction.V := fun x ↦
    (RestrictScalars.addEquiv k (MonoidAlgebra k G) Q.residueFieldReduction.V)
      ((Representation.ofModule Mmod).asModuleEquiv x)
  let invFun : Q.residueFieldReduction.V → (Representation.ofModule Mmod).asModule := fun x ↦
    (Representation.ofModule Mmod).asModuleEquiv.symm
      ((RestrictScalars.addEquiv k (MonoidAlgebra k G) Q.residueFieldReduction.V).symm x)
  -- Work directly on the owner of `Representation.ofModule` so the scalar restriction is explicit
  -- only once.
  refine ⟨
    { toFun := toFun
      invFun := invFun
      left_inv := by
        intro x
        simp [toFun, invFun, Mmod]
      right_inv := by
        intro x
        simp [toFun, invFun, Mmod]
      map_add' := by
        intro x y
        dsimp [toFun]
        rw [(Representation.ofModule Mmod).asModuleEquiv.map_add]
        exact
          (RestrictScalars.addEquiv k (MonoidAlgebra k G) Q.residueFieldReduction.V).map_add _ _
      map_smul' := by
        intro r x
        exact Representation.smul_ofModule_asModule (M := Mmod) r x }⟩

/-- Helper for Exercise 15-15.3-2: scalar extension of the exact lattice owner recovers the
ambient finite-dimensional representation. -/
private theorem stableLatticeBaseChangeIso
    (V : FDRep K G) (L : StableLattice A V.ρ) :
    Nonempty (FDRep.of (Representation.scalarExtension L.toRepresentation) ≅ V) := by
  -- The later exact-owner support file already proves the canonical base-change comparison.
  exact StableLattice.scalarExtension_exact_owner_fdrep_iso_local_support
    (A := A) (K := K) (G := G) L

/-- Helper for Exercise 15-15.3-2: the scalar-extension owner of a finite projective
`A[G]`-module is the raw tensor-product `K[G]`-module `K ⊗[A] Q.V`. -/
private theorem projectiveScalarExtensionOwnerLinearEquiv
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Nonempty
      ((TensorProduct A K Q.V) ≃ₗ[MonoidAlgebra K G] asModule ((Q.scalarExtension K).ρ)) := by
  -- Work with the exact owner of `Q.scalarExtension K` before packaging back into `FDRep`.
  exact
    ⟨(Classical.choice <|
      Representation.fdRepAsModule_scalarExtension_exact_owner_linearEquiv_local_support
        (A := A) (K := K) (G := G) Q).symm⟩

/-- Helper for Exercise 15-15.3-2: a `toRep`-level isomorphism between finite projective owners
already determines an isomorphism of the owners themselves. -/
private theorem finiteProjectiveNonemptyIsoOfToRepIsoLocal
    {P Q : FiniteProjectiveGroupAlgebraModule A G}
    (hPQ : Nonempty (P.toRep ≅ Q.toRep)) :
    Nonempty (P ≅ Q) := by
  let eIso : P.toRep ≅ Q.toRep := Classical.choice hPQ
  let eMod := Rep.toModuleMonoidAlgebra.mapIso eIso
  let eLin : P.V ≃ₗ[MonoidAlgebra A G] Q.V :=
    (Rep.counitIso P.V).toLinearEquiv.symm.trans
      (eMod.toLinearEquiv.trans (Rep.counitIso Q.V).toLinearEquiv)
  -- Repackage the ambient `A[G]`-linear equivalence as an isomorphism of projective owners.
  exact
    (Representation.finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
      (A := A) (G := G) P Q).2 ⟨eLin⟩

/-- Helper for Exercise 15-15.3-2: over a field, a `toRep`-level isomorphism between finite
projective owners already determines an isomorphism of the owners themselves. -/
private theorem finiteProjectiveFieldNonemptyIsoOfToRepIso
    {F : Type u} [Field F]
    {P Q : FiniteProjectiveGroupAlgebraModule F G}
    (hPQ : Nonempty (P.toRep ≅ Q.toRep)) :
    Nonempty (P ≅ Q) := by
  rcases hPQ with ⟨eIso⟩
  let eMod := Rep.toModuleMonoidAlgebra.mapIso eIso
  let eLin : P.V ≃ₗ[MonoidAlgebra F G] Q.V :=
    (Rep.counitIso P.V).toLinearEquiv.symm.trans
      (eMod.toLinearEquiv.trans (Rep.counitIso Q.V).toLinearEquiv)
  -- Repackage the ambient `F[G]`-linear equivalence as an isomorphism of projective owners.
  exact
    (Representation.finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
      (A := F) (G := G) P Q).2 ⟨eLin⟩

/-- Helper for Exercise 15-15.3-2: once the scalar-extended owner of a projective `A[G]`-module
is identified with a target `K`-representation at the `K[G]`-module level, Serre's support file
packages that comparison as an isomorphism of finite-dimensional representations. -/
private theorem scalarExtensionNonemptyIsoOfOwnerLinearEquiv
    (P : FiniteProjectiveGroupAlgebraModule A G)
    {V : Type u} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (ρ : Representation K G V)
    (hρ : Nonempty ((TensorProduct A K P.V) ≃ₗ[MonoidAlgebra K G] asModule ρ)) :
    Nonempty (P.scalarExtension K ≅ FDRep.of ρ) := by
  -- This is exactly the scalar-extension packaging step supplied by the Chapter `15` support
  -- file; keeping it named here shrinks the final assembly proof.
  exact
    Representation.finiteProjective_scalarExtension_nonempty_iso_of_nonempty_owner_linearEquiv_local_support
      (A := A) (K := K) (G := G) P ρ hρ

/-- Helper for Exercise 15-15.3-2: the exact tensor owner
`Rep.of (Representation.tprod L.toRepresentation Q.toRep.ρ)` is finite over the base ring `A`. -/
private theorem stableLatticeTensorOwnerFinite
    (V : FDRep K G) (L : StableLattice A V.ρ)
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let ρA : Rep A G := Rep.of <| Representation.tprod L.toRepresentation Q.toRep.ρ
    let Wk : ModuleCat (MonoidAlgebra A G) := Rep.toModuleMonoidAlgebra.obj ρA
    let _ : Module A Wk := Module.compHom Wk (algebraMap A (MonoidAlgebra A G))
    let _ : IsScalarTower A (MonoidAlgebra A G) Wk :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    Module.Finite A Wk := by
  let ρA : Rep A G := Rep.of <| Representation.tprod L.toRepresentation Q.toRep.ρ
  let Wk : ModuleCat (MonoidAlgebra A G) := Rep.toModuleMonoidAlgebra.obj ρA
  let _ : Module A Wk := Module.compHom Wk (algebraMap A (MonoidAlgebra A G))
  let _ : IsScalarTower A (MonoidAlgebra A G) Wk :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Module.Finite A ρA := by
    infer_instance
  let f : ρA →ₗ[A] Wk :=
    { toFun := fun x ↦ ρA.ρ.asModuleEquiv.symm x
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        change ρA.ρ.asModuleEquiv.symm (r • x) =
          ((algebraMap A (MonoidAlgebra A G)) r) • ρA.ρ.asModuleEquiv.symm x
        exact ρA.ρ.asModuleEquiv_symm_map_smul r x }
  -- Transfer finite generation from the representation carrier to the packaged `ModuleCat` owner.
  exact Module.Finite.of_surjective f fun y : Wk ↦ ⟨ρA.ρ.asModuleEquiv y, by rfl⟩

/-- Helper for Exercise 15-15.3-2: once the exact tensor owner is finite over `A`, it is finite
over the group algebra `A[G]` by restriction of scalars. -/
private theorem stableLatticeTensorOwnerGroupAlgebraFinite
    (V : FDRep K G) (L : StableLattice A V.ρ)
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let ρA : Rep A G := Rep.of <| Representation.tprod L.toRepresentation Q.toRep.ρ
    let Wk : ModuleCat (MonoidAlgebra A G) := Rep.toModuleMonoidAlgebra.obj ρA
    let _ : Module A Wk := Module.compHom Wk (algebraMap A (MonoidAlgebra A G))
    let _ : IsScalarTower A (MonoidAlgebra A G) Wk :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    Module.Finite (MonoidAlgebra A G) Wk := by
  let ρA : Rep A G := Rep.of <| Representation.tprod L.toRepresentation Q.toRep.ρ
  let Wk : ModuleCat (MonoidAlgebra A G) := Rep.toModuleMonoidAlgebra.obj ρA
  let _ : Module A Wk := Module.compHom Wk (algebraMap A (MonoidAlgebra A G))
  let _ : IsScalarTower A (MonoidAlgebra A G) Wk :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Module.Finite A Wk := stableLatticeTensorOwnerFinite (A := A) (K := K) (G := G) V L Q
  -- The exact owner is already finite over `A`, so restriction of scalars upgrades it to
  -- finiteness over `A[G]`.
  exact Module.Finite.of_restrictScalars_finite A (MonoidAlgebra A G) Wk

/-- Helper for Exercise 15-15.3-2: forgetting scalars from `A[G]` to `A` preserves projectivity
of a finite projective owner. -/
private theorem projectiveOwnerUnderlyingProjective
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Module.Projective A Q.V := by
  obtain ⟨M', _instAddCommGroup, _instModule, _instFree, i, s, hs⟩ :=
    Module.Projective.iff_split.mp Q.projective
  let _ : Module A M' := Module.compHom M' (algebraMap A (MonoidAlgebra A G))
  let _ : IsScalarTower A (MonoidAlgebra A G) M' :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Module.Free A M' :=
    Module.Free.of_basis
      ((MonoidAlgebra.basis G A).smulTower
        (Module.Free.chooseBasis (MonoidAlgebra A G) M'))
  -- Forget the split surjection along `A → A[G]`, keeping the same retraction data.
  exact Module.Projective.of_split (i.restrictScalars A) (s.restrictScalars A) <| by
    ext x
    exact LinearMap.congr_fun hs x

/-- Helper for Exercise 15-15.3-2: the raw tensor carrier inherits the exact diagonal
`A[G]`-action coming from `Representation.tprod`. -/
private instance stableLatticeTensorWrappedOwnerModule
    (V : FDRep K G) (L : StableLattice A V.ρ)
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Module (MonoidAlgebra A G) (TensorProduct A L.toSubmodule Q.V) := by
  change Module (MonoidAlgebra A G)
    (Representation.tprod L.toRepresentation Q.toRep.ρ).asModule
  infer_instance

/-- Helper for Exercise 15-15.3-2: after freezing the diagonal `A[G]`-action on the raw tensor
carrier via `compHom`, the raw tensor carrier can be bundled once as an exact owner. -/
private abbrev stableLatticeTensorWrappedOwner
    (V : FDRep K G) (L : StableLattice A V.ρ)
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    ModuleCat (MonoidAlgebra A G) :=
  ModuleCat.of (MonoidAlgebra A G) (TensorProduct A L.toSubmodule Q.V)

/-- Helper for Exercise 15-15.3-2: after transporting the tensor-product representation owner to
the raw tensor carrier, the generator action on a pure tensor is the expected diagonal action. -/
private theorem stableLatticeTensorWrappedOwnerMapOfTmul_image
    (V : FDRep K G) (L : StableLattice A V.ρ)
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (g : G) (z : L.toSubmodule) (y : Q.toRep.V) :
    let σ := Representation.tprod L.toRepresentation Q.toRep.ρ
    σ.asModuleEquiv
        ((MonoidAlgebra.of A G g : MonoidAlgebra A G) •
          σ.asModuleEquiv.symm (z ⊗ₜ[A] y)) =
      (L.toRepresentation g z) ⊗ₜ[A] (Q.toRep.ρ g y) := by
  let σ := Representation.tprod L.toRepresentation Q.toRep.ρ
  -- The tensor-product representation computes the diagonal action on pure tensors directly after
  -- moving through `σ.asModuleEquiv`.
  simpa [σ, Representation.asAlgebraHom_of, Representation.tprod_apply, TensorProduct.map_tmul]
    using
      (Representation.asModuleEquiv_map_smul
        (ρ := σ)
        (r := MonoidAlgebra.of A G g)
        (x := σ.asModuleEquiv.symm (z ⊗ₜ[A] y)))

/-- Helper for Exercise 15-15.3-2: after freezing the wrapped owner, base change across
`A → k` reassociates the raw tensor carrier to the factorwise reduction tensor. -/
private theorem stableLatticeTensorReductionRawTensorEquiv
    (V : FDRep K G) (L : StableLattice A V.ρ)
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k L.toSubmodule) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k Q.V) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A L.toSubmodule Q.V)) :=
      TensorProduct.leftModule
    Nonempty
      (TensorProduct A k (TensorProduct A L.toSubmodule Q.V) ≃ₗ[k]
        TensorProduct k (TensorProduct A k L.toSubmodule) (TensorProduct A k Q.V)) := by
  let _ : Module A k := Algebra.toModule
  let _ : Module k k := Semiring.toModule
  let _ : Module k (TensorProduct A k L.toSubmodule) := TensorProduct.leftModule
  let _ : Module k (TensorProduct A k Q.V) := TensorProduct.leftModule
  let _ : Module k (TensorProduct A k (TensorProduct A L.toSubmodule Q.V)) :=
    TensorProduct.leftModule
  let X := TensorProduct A L.toSubmodule Q.V
  let e0 :
      TensorProduct A k X ≃ₗ[k] TensorProduct k k (TensorProduct A k X) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A k k k X).symm
  let e1 :
      TensorProduct k k (TensorProduct A k X) ≃ₗ[k] TensorProduct A (TensorProduct k k k) X :=
    (TensorProduct.AlgebraTensorModule.assoc A k k k k X).symm
  let e2 :
      TensorProduct A (TensorProduct k k k) X ≃ₗ[k]
        TensorProduct k (TensorProduct A k L.toSubmodule) (TensorProduct A k Q.V) :=
    (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
      A A k k k L.toSubmodule k Q.V).symm
  -- Reassociate the scalar extension once so later owner comparisons work on factorwise tensors.
  exact ⟨by simpa [X] using ((e0.trans e1).trans e2)⟩

/-- Helper for Exercise 15-15.3-2: after freezing the wrapped owner, base change across
`A → K` reassociates the raw tensor carrier to the factorwise scalar-extension tensor. -/
private theorem stableLatticeTensorScalarExtensionRawTensorEquiv
    (V : FDRep K G) (L : StableLattice A V.ρ)
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let _ : Module A K := Algebra.toModule
    let _ : Module K K := Semiring.toModule
    let _ : Module K (TensorProduct A K L.toSubmodule) := TensorProduct.leftModule
    let _ : Module K (TensorProduct A K Q.V) := TensorProduct.leftModule
    let _ : Module K (TensorProduct A K (TensorProduct A L.toSubmodule Q.V)) :=
      TensorProduct.leftModule
    Nonempty
      (TensorProduct A K (TensorProduct A L.toSubmodule Q.V) ≃ₗ[K]
        TensorProduct K (TensorProduct A K L.toSubmodule) (TensorProduct A K Q.V)) := by
  let _ : Module A K := Algebra.toModule
  let _ : Module K K := Semiring.toModule
  let _ : Module K (TensorProduct A K L.toSubmodule) := TensorProduct.leftModule
  let _ : Module K (TensorProduct A K Q.V) := TensorProduct.leftModule
  let _ : Module K (TensorProduct A K (TensorProduct A L.toSubmodule Q.V)) :=
    TensorProduct.leftModule
  let X := TensorProduct A L.toSubmodule Q.V
  let e0 :
      TensorProduct A K X ≃ₗ[K] TensorProduct K K (TensorProduct A K X) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A K K K X).symm
  let e1 :
      TensorProduct K K (TensorProduct A K X) ≃ₗ[K] TensorProduct A (TensorProduct K K K) X :=
    (TensorProduct.AlgebraTensorModule.assoc A K K K K X).symm
  let e2 :
      TensorProduct A (TensorProduct K K K) X ≃ₗ[K]
        TensorProduct K (TensorProduct A K L.toSubmodule) (TensorProduct A K Q.V) :=
    (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
      A A K K K L.toSubmodule K Q.V).symm
  -- The same reassociation works for the generic-fiber scalar extension.
  exact ⟨by simpa [X] using ((e0.trans e1).trans e2)⟩

/-- Helper for Exercise 15-15.3-2: the raw scalar-extension reassociation for a tensor product. -/
private noncomputable def tensorScalarExtensionRawTensorEquiv
    {F : Type u} [Field F] [Algebra A F]
    {M N : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] :
    TensorProduct A F (TensorProduct A M N) ≃ₗ[F]
      TensorProduct F (TensorProduct A F M) (TensorProduct A F N) := by
  let X := TensorProduct A M N
  let e0 :
      TensorProduct A F X ≃ₗ[F] TensorProduct F F (TensorProduct A F X) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A F F F X).symm
  let e1 :
      TensorProduct F F (TensorProduct A F X) ≃ₗ[F] TensorProduct A (TensorProduct F F F) X :=
    (TensorProduct.AlgebraTensorModule.assoc A F F F F X).symm
  let e2 :
      TensorProduct A (TensorProduct F F F) X ≃ₗ[F]
        TensorProduct F (TensorProduct A F M) (TensorProduct A F N) :=
    (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm A A F F F M F N).symm
  exact (e0.trans e1).trans e2

private theorem tensorScalarExtensionRawTensorEquiv_tmul
    {F : Type u} [Field F] [Algebra A F]
    {M N : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (a : F) (m : M) (n : N) :
    tensorScalarExtensionRawTensorEquiv (A := A) (F := F) (M := M) (N := N)
      (a ⊗ₜ[A] (m ⊗ₜ[A] n)) =
      (a ⊗ₜ[A] m) ⊗ₜ[F] ((1 : F) ⊗ₜ[A] n) := by
  simp [tensorScalarExtensionRawTensorEquiv]

private theorem scalarExtension_apply_tmul
    {F : Type u} [Field F] [Algebra A F]
    {M : Type u} [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (g : G) (a : F) (m : M) :
    (show Representation F G (TensorProduct A F M) from Representation.scalarExtension ρ) g
        (a ⊗ₜ[A] m) =
      a ⊗ₜ[A] (ρ g m) := by
  change ((ρ g).baseChange F) (a ⊗ₜ[A] m) = _
  rw [LinearMap.baseChange_tmul]

/-- Helper for Exercise 15-15.3-2: scalar extension commutes with tensor-product
representations, through the explicit reassociation map. -/
private noncomputable def tensorScalarExtensionTprodEquiv
    {F : Type u} [Field F] [Algebra A F]
    {M N : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (ρ : Representation A G M) (σ : Representation A G N) :
    (show Representation F G (TensorProduct A F (TensorProduct A M N)) from
      Representation.scalarExtension (Representation.tprod ρ σ)).Equiv
      (Representation.tprod
        (show Representation F G (TensorProduct A F M) from Representation.scalarExtension ρ)
        (show Representation F G (TensorProduct A F N) from Representation.scalarExtension σ)) := by
  let eAssoc := tensorScalarExtensionRawTensorEquiv (A := A) (F := F) (M := M) (N := N)
  refine Representation.Equiv.mk eAssoc ?_
  intro g
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp [eAssoc]
  | tmul a y =>
      induction y using TensorProduct.induction_on with
      | zero => simp [eAssoc]
      | tmul m n =>
          have hleft :
              (show Representation F G (TensorProduct A F (TensorProduct A M N)) from
                Representation.scalarExtension (Representation.tprod ρ σ)) g
                  (a ⊗ₜ[A] (m ⊗ₜ[A] n)) =
                a ⊗ₜ[A] ((ρ g m) ⊗ₜ[A] (σ g n)) := by
            rw [scalarExtension_apply_tmul, Representation.tprod_apply, TensorProduct.map_tmul]
          have hρ :
              (show Representation F G (TensorProduct A F M) from
                Representation.scalarExtension ρ) g (a ⊗ₜ[A] m) =
                a ⊗ₜ[A] (ρ g m) :=
            scalarExtension_apply_tmul (A := A) (F := F) ρ g a m
          have hσ :
              (show Representation F G (TensorProduct A F N) from
                Representation.scalarExtension σ) g ((1 : F) ⊗ₜ[A] n) =
                (1 : F) ⊗ₜ[A] (σ g n) :=
            scalarExtension_apply_tmul (A := A) (F := F) σ g 1 n
          simp [hleft, eAssoc, tensorScalarExtensionRawTensorEquiv_tmul,
            Representation.tprod_apply, TensorProduct.map_tmul, hρ, hσ]
      | add y z hy hz =>
          simpa [LinearMap.comp_apply, map_add, TensorProduct.tmul_add] using
            congrArg₂ HAdd.hAdd hy hz
  | add x y hx hy =>
      simpa [LinearMap.comp_apply, map_add] using congrArg₂ HAdd.hAdd hx hy

/-- Helper for Exercise 15-15.3-2: tensoring representation equivalences gives an equivalence of
the tensor-product representations. -/
private noncomputable def tprodEquivOfEquiv
    {F : Type u} [Field F]
    {M₁ M₂ N₁ N₂ : Type u}
    [AddCommGroup M₁] [Module F M₁] [AddCommGroup M₂] [Module F M₂]
    [AddCommGroup N₁] [Module F N₁] [AddCommGroup N₂] [Module F N₂]
    {ρ₁ : Representation F G M₁} {ρ₂ : Representation F G M₂}
    {σ₁ : Representation F G N₁} {σ₂ : Representation F G N₂}
    (eρ : ρ₁.Equiv ρ₂) (eσ : σ₁.Equiv σ₂) :
    (Representation.tprod ρ₁ σ₁).Equiv (Representation.tprod ρ₂ σ₂) := by
  let eLin : TensorProduct F M₁ N₁ ≃ₗ[F] TensorProduct F M₂ N₂ :=
    TensorProduct.congr eρ.toLinearEquiv eσ.toLinearEquiv
  refine Representation.Equiv.mk eLin ?_
  intro g
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp [eLin]
  | tmul m n =>
      have hρ := LinearMap.congr_fun (eρ.isIntertwining' g) m
      have hσ := LinearMap.congr_fun (eσ.isIntertwining' g) n
      have hρ' : eρ (ρ₁ g m) = ρ₂ g (eρ m) := by
        simpa [LinearMap.comp_apply] using hρ
      have hσ' : eσ (σ₁ g n) = σ₂ g (eσ n) := by
        simpa [LinearMap.comp_apply] using hσ
      simp [eLin, Representation.tprod_apply, TensorProduct.map_tmul, hρ', hσ']
  | add x y hx hy =>
      simpa [LinearMap.comp_apply, map_add] using congrArg₂ HAdd.hAdd hx hy

/-- Helper for Exercise 15-15.3-2: a `Rep`-level isomorphism survives scalar extension. -/
private noncomputable def scalarExtensionIsoOfRepIso
    {F : Type u} [Field F] [Algebra A F]
    {M N : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    {ρ : Representation A G M} {σ : Representation A G N}
    (eIso : Rep.of ρ ≅ Rep.of σ) :
    Rep.of (show Representation F G (TensorProduct A F M) from Representation.scalarExtension ρ) ≅
      Rep.of (show Representation F G (TensorProduct A F N) from Representation.scalarExtension σ) := by
  let eA : M ≃ₗ[A] N :=
    { toFun := eIso.hom.hom.toLinearMap
      invFun := eIso.inv.hom.toLinearMap
      left_inv := by
        intro x
        have h := congrArg (fun f : Rep.of ρ ⟶ Rep.of ρ => f.hom.toLinearMap x)
          eIso.hom_inv_id
        simpa using h
      right_inv := by
        intro x
        have h := congrArg (fun f : Rep.of σ ⟶ Rep.of σ => f.hom.toLinearMap x)
          eIso.inv_hom_id
        simpa using h
      map_add' := eIso.hom.hom.toLinearMap.map_add
      map_smul' := eIso.hom.hom.toLinearMap.map_smul }
  let eF : TensorProduct A F M ≃ₗ[F] TensorProduct A F N :=
    eA.baseChange A F M N
  refine Rep.mkIso (Representation.Equiv.mk eF ?_)
  intro g
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  have hx := LinearMap.congr_fun (eIso.hom.hom.isIntertwining' g) x
  simpa [Representation.scalarExtension, eF, eA] using
    congrArg (fun y ↦ a ⊗ₜ[A] y) hx

/-- Helper for Exercise 15-15.3-2: the canonical tensor exact owner attached to a stable lattice
and a projective `A[G]`-owner is itself projective over `A[G]`. -/
private theorem stableLatticeTensorAsModuleProjective
    (V : FDRep K G) (L : StableLattice A V.ρ)
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let ρA : Rep A G := Rep.of <| Representation.tprod L.toRepresentation Q.toRep.ρ
    Module.Projective (MonoidAlgebra A G) ρA.ρ.asModule := by
  -- Route correction: prove projectivity on the exact owner `ρA.ρ.asModule`, where the Chapter
  -- `14` averaging criterion and the raw tensor calculations share the same owner spelling.
  let ρ := Q.toRep.ρ
  let hρMod : Module A ρ.asModule := Representation.instModuleAsModule ρ
  let _ : Module A ρ.asModule := hρMod
  let hρAdd : AddCommGroup ρ.asModule := inferInstance
  let _ : AddCommGroup ρ.asModule := hρAdd
  let hρGMod : Module (MonoidAlgebra A G) ρ.asModule := inferInstance
  let _ : Module (MonoidAlgebra A G) ρ.asModule := hρGMod
  let hρTower : IsScalarTower A (MonoidAlgebra A G) ρ.asModule := inferInstance
  let _ : IsScalarTower A (MonoidAlgebra A G) ρ.asModule := hρTower
  let hFin : Fintype G := Fintype.ofFinite G
  let _ : Fintype G := hFin
  classical
  have hρProj : Module.Projective (MonoidAlgebra A G) ρ.asModule := by
    -- Freeze the projective structure on `Q` at the exact `toRep` owner before transporting the
    -- averaging witness to the tensor owner.
    let MQ : ModuleCat (MonoidAlgebra A G) :=
      Rep.toModuleMonoidAlgebra.obj (Rep.ofModuleMonoidAlgebra.obj Q.V)
    have hMQ : Module.Projective (MonoidAlgebra A G) MQ := by
      let _ : Module.Projective (MonoidAlgebra A G) Q.V := Q.projective
      simpa [MQ] using
        (Module.Projective.of_equiv'
          ((Rep.counitIso Q.V).toLinearEquiv.symm) :
          Module.Projective (MonoidAlgebra A G) MQ)
    simpa [ρ, FiniteProjectiveGroupAlgebraModule.toRep, MQ] using hMQ
  obtain ⟨_, u, hu⟩ :=
    (@projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
      A inferInstance G inferInstance inferInstance
      ρ.asModule hρAdd hρMod hρGMod hρTower).mp hρProj
  let σ : Rep A G := Rep.of <| Representation.tprod L.toRepresentation Q.toRep.ρ
  let hσMod : Module A σ.ρ.asModule := Representation.instModuleAsModule σ.ρ
  let _ : Module A σ.ρ.asModule := hσMod
  let hσAdd : AddCommGroup σ.ρ.asModule := inferInstance
  let _ : AddCommGroup σ.ρ.asModule := hσAdd
  let hσGMod : Module (MonoidAlgebra A G) σ.ρ.asModule := inferInstance
  let _ : Module (MonoidAlgebra A G) σ.ρ.asModule := hσGMod
  let hσTower : IsScalarTower A (MonoidAlgebra A G) σ.ρ.asModule := inferInstance
  let _ : IsScalarTower A (MonoidAlgebra A G) σ.ρ.asModule := hσTower
  have hQUnderlyingProj : Module.Projective A Q.V :=
    projectiveOwnerUnderlyingProjective (A := A) (G := G) Q
  have hTensorProj : Module.Projective A (TensorProduct A L.toSubmodule Q.V) := by
    let _ : Module.Projective A L.toSubmodule := inferInstance
    let _ : Module.Projective A Q.V := hQUnderlyingProj
    simpa using
      (Module.Projective.tensorProduct
        (R := A) (R₀ := A) (M := L.toSubmodule) (N := Q.V))
  have hσUnderlyingProj : Module.Projective A σ := by
    simpa [σ, FiniteProjectiveGroupAlgebraModule.toRep] using hTensorProj
  have hσAsModuleProj : Module.Projective A σ.ρ.asModule := by
    -- The raw tensor carrier and the exact owner differ only by `asModuleEquiv`.
    let _ : Module.Projective A σ := hσUnderlyingProj
    simpa using
      (Module.Projective.of_equiv' (σ.ρ.asModuleEquiv.symm) :
        Module.Projective A σ.ρ.asModule)
  let uRaw : Module.End A Q.toRep.V :=
    (((Q.toRep.ρ.asModuleEquiv : Q.toRep.ρ.asModule ≃ₗ[A] Q.toRep.V) :
        Q.toRep.ρ.asModule →ₗ[A] Q.toRep.V)) ∘ₗ
      (u ∘ₗ
        (((Q.toRep.ρ.asModuleEquiv.symm : Q.toRep.V ≃ₗ[A] Q.toRep.ρ.asModule) :
          Q.toRep.V →ₗ[A] Q.toRep.ρ.asModule)))
  let uσ : Module.End A σ.ρ.asModule :=
    ((σ.ρ.asModuleEquiv.symm : (↑σ) →ₗ[A] σ.ρ.asModule)) ∘ₗ
      ((TensorProduct.map
          (LinearMap.id : L.toSubmodule →ₗ[A] L.toSubmodule)
          uRaw) ∘ₗ
        (σ.ρ.asModuleEquiv : σ.ρ.asModule →ₗ[A] (↑σ)))
  have huCarrier :
      ∀ x : Q.toRep.V,
        (∑ g : G,
          Q.toRep.ρ.asModuleEquiv
            ((MonoidAlgebra.of A G g : MonoidAlgebra A G) •
              u ((MonoidAlgebra.of A G g⁻¹ : MonoidAlgebra A G) •
                Q.toRep.ρ.asModuleEquiv.symm x))) = x := by
    intro x
    have howner :
        ∑ g : G,
          (MonoidAlgebra.of A G g : MonoidAlgebra A G) •
            u ((MonoidAlgebra.of A G g⁻¹ : MonoidAlgebra A G) •
              Q.toRep.ρ.asModuleEquiv.symm x) =
          Q.toRep.ρ.asModuleEquiv.symm x := by
      -- Rewrite Serre's textbook average as `sumOfConjugates` on the frozen exact owner.
      calc
        _ =
            @LinearMap.sumOfConjugates A inferInstance G inferInstance
              ρ.asModule hρAdd hρMod hρGMod hρTower
              ρ.asModule hρAdd hρMod hρGMod hρTower
              u hFin
              (Q.toRep.ρ.asModuleEquiv.symm x) := by
              simpa [ρ, MonoidAlgebra.of_apply] using
                (@textbook_average_eq_sumOfConjugates
                  A inferInstance G inferInstance inferInstance
                  ρ.asModule hρAdd hρMod hρGMod hρTower inferInstance
                  u (Q.toRep.ρ.asModuleEquiv.symm x))
        _ = (LinearMap.id : Module.End A ρ.asModule) (Q.toRep.ρ.asModuleEquiv.symm x) := by
              simpa using
                congrArg
                  (fun f : Module.End A ρ.asModule =>
                    f (Q.toRep.ρ.asModuleEquiv.symm x))
                  hu
        _ = Q.toRep.ρ.asModuleEquiv.symm x := by
              rfl
    -- Apply the exact-owner linear equivalence to move back to the raw tensor factor.
    simpa [map_sum] using
      congrArg
        (fun z : Q.toRep.ρ.asModule => Q.toRep.ρ.asModuleEquiv z)
        howner
  have huσ :
      @LinearMap.sumOfConjugates A inferInstance G inferInstance
        σ.ρ.asModule hσAdd hσMod hσGMod hσTower
        σ.ρ.asModule hσAdd hσMod hσGMod hσTower
        uσ hFin =
      (LinearMap.id : Module.End A σ.ρ.asModule) := by
    let hσSum : Module.End A σ.ρ.asModule :=
      @LinearMap.sumOfConjugates A inferInstance G inferInstance
        σ.ρ.asModule hσAdd hσMod hσGMod hσTower
        σ.ρ.asModule hσAdd hσMod hσGMod hσTower
        uσ hFin
    let _ : Module A (↑σ) := by
      infer_instance
    let F : Module.End A (↑σ) :=
      (σ.ρ.asModuleEquiv : σ.ρ.asModule →ₗ[A] (↑σ)) ∘ₗ
        (hσSum ∘ₗ
          (σ.ρ.asModuleEquiv.symm : (↑σ) →ₗ[A] σ.ρ.asModule))
    have hF : F = LinearMap.id := by
      apply LinearMap.ext
      intro z
      -- After transporting to the raw tensor carrier, only the pure-tensor branch uses the
      -- averaging identity; zero and addition follow from linearity.
      refine TensorProduct.induction_on z ?_ ?_ ?_
      · simp [F]
      · intro z x
        have htext :
            σ.ρ.asModuleEquiv
                (∑ g : G,
                  (MonoidAlgebra.of A G g : MonoidAlgebra A G) •
                    uσ ((MonoidAlgebra.of A G g⁻¹ : MonoidAlgebra A G) •
                      σ.ρ.asModuleEquiv.symm (z ⊗ₜ[A] x))) =
              σ.ρ.asModuleEquiv
                (hσSum (σ.ρ.asModuleEquiv.symm (z ⊗ₜ[A] x))) := by
          simpa using
            congrArg
              (fun y : σ.ρ.asModule => σ.ρ.asModuleEquiv y)
              (@textbook_average_eq_sumOfConjugates
                A inferInstance G inferInstance inferInstance
                σ.ρ.asModule hσAdd hσMod hσGMod hσTower inferInstance
                uσ (σ.ρ.asModuleEquiv.symm (z ⊗ₜ[A] x)))
        have hsum :
            σ.ρ.asModuleEquiv
                (∑ g : G,
                  (MonoidAlgebra.of A G g : MonoidAlgebra A G) •
                    uσ ((MonoidAlgebra.of A G g⁻¹ : MonoidAlgebra A G) •
                      σ.ρ.asModuleEquiv.symm (z ⊗ₜ[A] x))) =
              z ⊗ₜ[A]
                ∑ g : G,
                  Q.toRep.ρ.asModuleEquiv
                    ((MonoidAlgebra.of A G g : MonoidAlgebra A G) •
                      u ((MonoidAlgebra.of A G g⁻¹ : MonoidAlgebra A G) •
                        Q.toRep.ρ.asModuleEquiv.symm x)) := by
          -- Compare the transported average termwise on pure tensors.
          rw [map_sum, TensorProduct.tmul_sum]
          refine Finset.sum_congr rfl ?_
          intro g _
          have hginv :
              ((MonoidAlgebra.of A G g⁻¹ : MonoidAlgebra A G) •
                  σ.ρ.asModuleEquiv.symm (z ⊗ₜ[A] x)) =
                σ.ρ.asModuleEquiv.symm
                  ((L.toRepresentation g⁻¹ z) ⊗ₜ[A] (Q.toRep.ρ g⁻¹ x)) := by
            apply
              (Representation.asModuleEquiv
                (Representation.tprod L.toRepresentation Q.toRep.ρ)).injective
            simpa [MonoidAlgebra.of_apply, Representation.asAlgebraHom_of,
              Representation.tprod_apply, TensorProduct.map_tmul] using
              (Representation.asModuleEquiv_map_smul
                (ρ := Representation.tprod L.toRepresentation Q.toRep.ρ)
                (r := MonoidAlgebra.of A G g⁻¹)
                (x := (Representation.tprod L.toRepresentation Q.toRep.ρ).asModuleEquiv.symm
                  (z ⊗ₜ[A] x)))
          have huPure :
              σ.ρ.asModuleEquiv
                  (uσ
                    (σ.ρ.asModuleEquiv.symm
                      ((L.toRepresentation g⁻¹ z) ⊗ₜ[A] (Q.toRep.ρ g⁻¹ x)))) =
                (L.toRepresentation g⁻¹ z) ⊗ₜ[A]
                  (Q.toRep.ρ.asModuleEquiv
                    (u (Q.toRep.ρ.asModuleEquiv.symm (Q.toRep.ρ g⁻¹ x)))) := by
            rfl
          rw [hginv]
          -- Push the outer `A[G]`-action through `asModuleEquiv`, then simplify the pure tensor.
          calc
            σ.ρ.asModuleEquiv
                ((MonoidAlgebra.of A G g : MonoidAlgebra A G) •
                  uσ
                    (σ.ρ.asModuleEquiv.symm
                      ((L.toRepresentation g⁻¹ z) ⊗ₜ[A] (Q.toRep.ρ g⁻¹ x)))) =
                σ.ρ.asAlgebraHom (MonoidAlgebra.of A G g)
                  (σ.ρ.asModuleEquiv
                    (uσ
                      (σ.ρ.asModuleEquiv.symm
                        ((L.toRepresentation g⁻¹ z) ⊗ₜ[A] (Q.toRep.ρ g⁻¹ x)))) ) := by
                  simpa using
                    (Representation.asModuleEquiv_map_smul
                      (ρ := σ.ρ)
                      (r := MonoidAlgebra.of A G g)
                      (x := uσ
                        (σ.ρ.asModuleEquiv.symm
                          ((L.toRepresentation g⁻¹ z) ⊗ₜ[A] (Q.toRep.ρ g⁻¹ x)))))
            _ =
                σ.ρ.asAlgebraHom (MonoidAlgebra.of A G g)
                  ((L.toRepresentation g⁻¹ z) ⊗ₜ[A]
                    (Q.toRep.ρ.asModuleEquiv
                      (u (Q.toRep.ρ.asModuleEquiv.symm (Q.toRep.ρ g⁻¹ x))))) := by
                  rw [huPure]
            _ =
                z ⊗ₜ[A]
                  (Q.toRep.ρ.asModuleEquiv
                    ((MonoidAlgebra.of A G g : MonoidAlgebra A G) •
                      u ((MonoidAlgebra.of A G g⁻¹ : MonoidAlgebra A G) •
                        Q.toRep.ρ.asModuleEquiv.symm x))) := by
                  rw [Representation.asAlgebraHom_of, Representation.tprod_apply,
                    TensorProduct.map_tmul]
                  have hz :
                      L.toRepresentation g (L.toRepresentation g⁻¹ z) = z := by
                    simp
                  have hx :
                      Q.toRep.ρ g
                          (Q.toRep.ρ.asModuleEquiv
                            (u
                              ((MonoidAlgebra.of A G g⁻¹ : MonoidAlgebra A G) •
                                Q.toRep.ρ.asModuleEquiv.symm x))) =
                        Q.toRep.ρ.asModuleEquiv
                          ((MonoidAlgebra.of A G g : MonoidAlgebra A G) •
                            u ((MonoidAlgebra.of A G g⁻¹ : MonoidAlgebra A G) •
                              Q.toRep.ρ.asModuleEquiv.symm x)) := by
                    simpa [Representation.asAlgebraHom_of] using
                      (Representation.asModuleEquiv_map_smul
                        (ρ := Q.toRep.ρ)
                        (r := MonoidAlgebra.of A G g)
                        (x := u
                          ((MonoidAlgebra.of A G g⁻¹ : MonoidAlgebra A G) •
                            Q.toRep.ρ.asModuleEquiv.symm x))).symm
                  have hxinverse :
                      Q.toRep.ρ.asModuleEquiv.symm (Q.toRep.ρ g⁻¹ x) =
                        (MonoidAlgebra.of A G g⁻¹ : MonoidAlgebra A G) •
                          Q.toRep.ρ.asModuleEquiv.symm x := by
                    exact
                      Representation.asModuleEquiv_symm_map_rho
                        (ρ := Q.toRep.ρ) g⁻¹ x
                  rw [hxinverse, hz, hx]
        calc
          F (z ⊗ₜ[A] x) =
              σ.ρ.asModuleEquiv
                (hσSum (σ.ρ.asModuleEquiv.symm (z ⊗ₜ[A] x))) := by
                  rfl
          _ =
              σ.ρ.asModuleEquiv
                (∑ g : G,
                  (MonoidAlgebra.of A G g : MonoidAlgebra A G) •
                    uσ ((MonoidAlgebra.of A G g⁻¹ : MonoidAlgebra A G) •
                      σ.ρ.asModuleEquiv.symm (z ⊗ₜ[A] x))) := by
                exact htext.symm
          _ =
              z ⊗ₜ[A]
                ∑ g : G,
                  Q.toRep.ρ.asModuleEquiv
                    ((MonoidAlgebra.of A G g : MonoidAlgebra A G) •
                      u ((MonoidAlgebra.of A G g⁻¹ : MonoidAlgebra A G) •
                        Q.toRep.ρ.asModuleEquiv.symm x)) := by
                exact hsum
          _ = z ⊗ₜ[A] x := by
                rw [huCarrier x]
      · intro z₁ z₂ hz₁ hz₂
        calc
          F (z₁ + z₂) = F z₁ + F z₂ := by
            simp [F]
          _ = z₁ + z₂ := by
            simp [hz₁, hz₂]
    -- Transport the raw tensor identity back to the exact owner.
    change hσSum = (LinearMap.id : Module.End A σ.ρ.asModule)
    apply LinearMap.ext
    intro y
    apply (σ.ρ.asModuleEquiv : σ.ρ.asModule ≃ₗ[A] (↑σ)).injective
    have hy := congrArg (fun f : Module.End A (↑σ) => f (σ.ρ.asModuleEquiv y)) hF
    simpa [F] using hy
  -- Apply the Chapter `14` criterion once the averaging witness has been transported to the exact
  -- tensor owner.
  exact
    (@projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
      A inferInstance G inferInstance inferInstance
      σ.ρ.asModule hσAdd hσMod hσGMod hσTower).mpr
      ⟨hσAsModuleProj, uσ, huσ⟩

/-- Helper for Exercise 15-15.3-2: the canonical tensor exact owner attached to a stable lattice
and a projective `A[G]`-owner is itself projective over `A[G]`. -/
private theorem stableLatticeTensorOwnerProjective
    (V : FDRep K G) (L : StableLattice A V.ρ)
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let ρA : Rep A G := Rep.of <| Representation.tprod L.toRepresentation Q.toRep.ρ
    let Wk : ModuleCat (MonoidAlgebra A G) := Rep.toModuleMonoidAlgebra.obj ρA
    Module.Projective (MonoidAlgebra A G) Wk := by
  let ρA : Rep A G := Rep.of <| Representation.tprod L.toRepresentation Q.toRep.ρ
  let Wk : ModuleCat (MonoidAlgebra A G) := Rep.toModuleMonoidAlgebra.obj ρA
  -- Package the exact-owner projectivity once; no second averaging proof is needed on `Wk`.
  simpa [ρA, Wk] using
    (stableLatticeTensorAsModuleProjective (A := A) (K := K) (G := G) V L Q)

/-- Helper for Exercise 15-15.3-2: the explicit tensor lift already has the expected reduction and
scalar-extension Grothendieck classes. -/
private theorem stableLatticeTensorLift_exists
    (V : FDRep K G) (L : StableLattice A V.ρ)
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    ∃ P : FiniteProjectiveGroupAlgebraModule A G,
      [P.residueFieldReduction]ₚ₀ =
        [FiniteProjectiveGroupAlgebraModule.tprod
          (FDRep.of L.reductionRepresentation) Q.residueFieldReduction]ₚ₀ ∧
      [P.scalarExtension K]₀ =
        [CategoryTheory.MonoidalCategoryStruct.tensorObj V (Q.scalarExtension K)]₀ := by
  -- Route correction: the failed `Iso.refl` proof was using the wrong normal form for the exact
  -- tensor owner. The intended route is to package
  -- `Rep.of (Representation.tprod L.toRepresentation Q.toRep.ρ)` as a finite projective
  -- `A[G]`-module and then compare both reduction and scalar extension through `Rep.unitIso`.
  let ρA : Rep A G := Rep.of <| Representation.tprod L.toRepresentation Q.toRep.ρ
  let Wk : ModuleCat (MonoidAlgebra A G) := Rep.toModuleMonoidAlgebra.obj ρA
  let _ : Module A Wk := Module.compHom Wk (algebraMap A (MonoidAlgebra A G))
  let _ : IsScalarTower A (MonoidAlgebra A G) Wk :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Module.Finite A Wk := stableLatticeTensorOwnerFinite (A := A) (K := K) (G := G) V L Q
  let _ : Module.Finite (MonoidAlgebra A G) Wk :=
    stableLatticeTensorOwnerGroupAlgebraFinite (A := A) (K := K) (G := G) V L Q
  let _ : Module.Projective (MonoidAlgebra A G) Wk :=
    stableLatticeTensorOwnerProjective (A := A) (K := K) (G := G) V L Q
  let W : FGModuleCat (MonoidAlgebra A G) := by
    refine ⟨Wk, ?_⟩
    change Module.Finite (MonoidAlgebra A G) Wk
    infer_instance
  let P : FiniteProjectiveGroupAlgebraModule A G := ⟨W, inferInstance⟩
  have hPtoRepTensor : P.toRep ≅ ρA := by
    simpa [P, W, Wk, ρA, FiniteProjectiveGroupAlgebraModule.toRep] using
      (Rep.unitIso ρA).symm
  refine ⟨P, ?_, ?_⟩
  · -- Unfold the canonical residue-field reduction of the exact tensor owner once.
    let T : FiniteProjectiveGroupAlgebraModule k G :=
      FiniteProjectiveGroupAlgebraModule.tprod
        (FDRep.of L.reductionRepresentation) Q.residueFieldReduction
    -- Reduce the projective Grothendieck-class computation to an isomorphism of exact owners.
    have hPT : Nonempty (P.residueFieldReduction ≅ T) := by
      have hRep : Nonempty (P.residueFieldReduction.toRep ≅ T.toRep) := by
        let ρPred : Rep k G :=
          Rep.of
            (show Representation k G (TensorProduct A k P.V) from
              Representation.scalarExtension P.toRep.ρ)
        have ePred : P.residueFieldReduction.toRep ≅ ρPred := by
          simpa [ρPred, FiniteProjectiveGroupAlgebraModule.residueFieldReduction,
            FiniteProjectiveGroupAlgebraModule.toRep] using
            (Rep.unitIso ρPred).symm
        let ePscalar :
            Rep.of
                (show Representation k G (TensorProduct A k P.toRep.V) from
                  Representation.scalarExtension P.toRep.ρ) ≅
              Rep.of
                (show Representation k G
                    (TensorProduct A k (TensorProduct A L.toSubmodule Q.V)) from
                  Representation.scalarExtension
                    (Representation.tprod L.toRepresentation Q.toRep.ρ)) :=
          scalarExtensionIsoOfRepIso (A := A) (F := k) hPtoRepTensor
        let eAssoc :
            Rep.of
                (show Representation k G
                    (TensorProduct A k (TensorProduct A L.toSubmodule Q.V)) from
                  Representation.scalarExtension
                    (Representation.tprod L.toRepresentation Q.toRep.ρ)) ≅
              Rep.of
                (Representation.tprod
                  (show Representation k G (TensorProduct A k L.toSubmodule) from
                    Representation.scalarExtension L.toRepresentation)
                  (show Representation k G (TensorProduct A k Q.V) from
                    Representation.scalarExtension Q.toRep.ρ)) :=
          Rep.mkIso
            (tensorScalarExtensionTprodEquiv
              (A := A) (F := k) L.toRepresentation Q.toRep.ρ)
        have eLRep :
            (show Representation k G (TensorProduct A k L.toSubmodule) from
              Representation.scalarExtension L.toRepresentation).Equiv
              (FDRep.of L.reductionRepresentation).ρ := by
          let eLsource := Classical.choice
            (stableLatticeScalarExtensionOwnerAsModuleLinearEquiv
              (A := A) (K := K) (G := G) V L)
          let eLtarget := Classical.choice
            (stableLatticeReductionOwnerAsModuleLinearEquiv
              (A := A) (K := K) (G := G) V L)
          exact representationEquivOfAsModuleLinearEquiv (eLsource.trans eLtarget)
        have eQRep :
            (show Representation k G (TensorProduct A k Q.V) from
              Representation.scalarExtension Q.toRep.ρ).Equiv
              Q.residueFieldReduction.toRep.ρ := by
          have hQsource :
              Nonempty
                (asModule
                    (show Representation k G (TensorProduct A k Q.V) from
                      Representation.scalarExtension Q.toRep.ρ) ≃ₗ[MonoidAlgebra k G]
                  TensorProduct A k Q.V) := by
            simpa [FiniteProjectiveGroupAlgebraModule.toRep] using
              (nonempty_asModuleLinearEquiv_target_field_local
                (G := G)
                (ρ := (show Representation k G (TensorProduct A k Q.V) from
                  Representation.scalarExtension Q.toRep.ρ)))
          let eQsource := Classical.choice hQsource
          let eQtarget := Classical.choice
            (residueFieldReductionAsModuleLinearEquiv (A := A) (G := G) Q)
          let eQtarget' :
              TensorProduct A k Q.V ≃ₗ[MonoidAlgebra k G]
                asModule Q.residueFieldReduction.toRep.ρ := by
            simpa [FiniteProjectiveGroupAlgebraModule.residueFieldReduction,
              FiniteProjectiveGroupAlgebraModule.toFiniteRep,
              FiniteProjectiveGroupAlgebraModule.toRep] using eQtarget.symm
          exact representationEquivOfAsModuleLinearEquiv (eQsource.trans eQtarget')
        let eFactors :
            Rep.of
                (Representation.tprod
                  (show Representation k G (TensorProduct A k L.toSubmodule) from
                    Representation.scalarExtension L.toRepresentation)
                  (show Representation k G (TensorProduct A k Q.V) from
                    Representation.scalarExtension Q.toRep.ρ)) ≅
              Rep.of
                (Representation.tprod
                  (FDRep.of L.reductionRepresentation).ρ
                  Q.residueFieldReduction.toRep.ρ) :=
          Rep.mkIso (tprodEquivOfEquiv eLRep eQRep)
        let ρT : Rep k G :=
          Rep.of <|
            Representation.tprod
              (FDRep.of L.reductionRepresentation).ρ
              Q.residueFieldReduction.toRep.ρ
        have eT : ρT ≅ T.toRep := by
          simpa [ρT, T, FiniteProjectiveGroupAlgebraModule.tprod,
            FiniteProjectiveGroupAlgebraModule.toRep] using
            (Rep.unitIso ρT)
        exact ⟨ePred.trans (ePscalar.trans (eAssoc.trans (eFactors.trans eT)))⟩
      exact finiteProjectiveFieldNonemptyIsoOfToRepIso (G := G) hRep
    exact
      Representation.finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso hPT
  · -- The scalar extension of the exact tensor owner is definitionally the upstairs tensor
    -- product representation.
    let VL : FDRep K G := FDRep.of (Representation.scalarExtension L.toRepresentation)
    let T : FDRep K G := CategoryTheory.MonoidalCategoryStruct.tensorObj VL (Q.scalarExtension K)
    -- Package the finite-representation class comparison through the explicit scalar-extended
    -- tensor owner before replacing `VL` by the ambient `V`.
    have hPT : Nonempty (P.scalarExtension K ≅ T) := by
      let ePscalar :
          Rep.of
              (show Representation K G (TensorProduct A K P.toRep.V) from
                Representation.scalarExtension P.toRep.ρ) ≅
            Rep.of
              (show Representation K G
                  (TensorProduct A K (TensorProduct A L.toSubmodule Q.V)) from
                Representation.scalarExtension
                  (Representation.tprod L.toRepresentation Q.toRep.ρ)) :=
        scalarExtensionIsoOfRepIso (A := A) (F := K) hPtoRepTensor
      let eAssoc :
          Rep.of
              (show Representation K G
                  (TensorProduct A K (TensorProduct A L.toSubmodule Q.V)) from
                Representation.scalarExtension
                  (Representation.tprod L.toRepresentation Q.toRep.ρ)) ≅
            Rep.of
              (Representation.tprod
                (show Representation K G (TensorProduct A K L.toSubmodule) from
                  Representation.scalarExtension L.toRepresentation)
                (show Representation K G (TensorProduct A K Q.V) from
                  Representation.scalarExtension Q.toRep.ρ)) :=
        Rep.mkIso
          (tensorScalarExtensionTprodEquiv
            (A := A) (F := K) L.toRepresentation Q.toRep.ρ)
      let eRep :
          (CategoryTheory.forget₂ (FDRep K G) (Rep K G)).obj (P.scalarExtension K) ≅
            (CategoryTheory.forget₂ (FDRep K G) (Rep K G)).obj T := by
        simpa [FiniteProjectiveGroupAlgebraModule.scalarExtension,
          FiniteProjectiveGroupAlgebraModule.toRep, T, VL] using ePscalar.trans eAssoc
      let eFD : FDRep.of (P.scalarExtension K).ρ ≅ FDRep.of T.ρ :=
        Representation.Equiv.toFDRepIso (Representation.equivOfIso eRep)
      exact ⟨(fdRepIsoOfRhoLocal (P.scalarExtension K)).trans
        (eFD.trans (fdRepIsoOfRhoLocal T).symm)⟩
    calc
      [P.scalarExtension K]₀ = [T]₀ := by
        exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := K) (G := G) hPT
      _ = [VL]₀ * [Q.scalarExtension K]₀ := by
        symm
        simpa [T] using
          (finiteRepGrothendieckClass_mul (V := VL) (W := Q.scalarExtension K))
      _ = [V]₀ * [Q.scalarExtension K]₀ := by
        rcases stableLatticeBaseChangeIso (A := A) (K := K) (G := G) V L with
          ⟨eVL⟩
        rw [finiteRepGrothendieckClass_eq_of_nonempty_iso (L := K) (G := G) ⟨eVL⟩]

/-- Helper for Exercise 15-15.3-2: the generator case follows once one explicit tensor lift is
fixed upstairs. -/
private theorem projectiveGrothendieckScalarExtensionHom_generator_smul
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (V : FDRep K G) (L : StableLattice A V.ρ)
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    e (d [V]₀ • [Q.residueFieldReduction]ₚ₀) = [V]₀ * [Q.scalarExtension K]₀ := by
  obtain ⟨P, hredClass, hscalarClass⟩ :=
    stableLatticeTensorLift_exists (A := A) (K := K) (G := G) V L Q
  -- Route correction: once the tensor lift is fixed as an actual projective owner `P`, the
  -- generator computation is only a chain of standard class formulas.
  calc
    e (d [V]₀ • [Q.residueFieldReduction]ₚ₀) =
        e ([FDRep.of L.reductionRepresentation]₀ • [Q.residueFieldReduction]ₚ₀) := by
          rw [decompositionHom_finiteRepClass_eq]
    _ =
        e [FiniteProjectiveGroupAlgebraModule.tprod
          (FDRep.of L.reductionRepresentation) Q.residueFieldReduction]ₚ₀ := by
          rw [finiteProjectiveGroupAlgebraGrothendieckClass_smul]
    _ = e [P.residueFieldReduction]ₚ₀ := by
          rw [hredClass.symm]
    _ = [P.scalarExtension K]₀ := by
          rw [projectiveGrothendieckScalarExtensionHom_residueFieldReductionClass_eq]
    _ = [CategoryTheory.MonoidalCategoryStruct.tensorObj V (Q.scalarExtension K)]₀ := by
          rw [hscalarClass]
    _ = [V]₀ * [Q.scalarExtension K]₀ := by
          rw [finiteRepGrothendieckClass_mul]

/-- Exercise 15-15.3-2: Serre's scalar-extension homomorphism intertwines the tensor-product
action of `d x ∈ R_k(G)` on `P_k(G)` with multiplication by `x ∈ R_K(G)`. -/
theorem projectiveGrothendieckScalarExtensionHom_smul
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (x : R_K(G)) (y : P_k(G)) :
    e (d x • y) = x * e y := by
  let yA : finiteProjectiveGroupAlgebraGrothendieckGroup A G :=
    (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm y
  have hy : (projectiveGrothendieckReductionEquiv (A := A) (G := G)) yA = y := by
    -- The transported class `yA` was defined as the inverse image of `y`.
    simp [yA]
  have hmain :
      ∀ x : R_K(G), ∀ yA : finiteProjectiveGroupAlgebraGrothendieckGroup A G,
        e (d x • (projectiveGrothendieckReductionEquiv (A := A) (G := G) yA)) =
          x * projectiveGrothendieckBaseChangeHom K yA := by
    intro x yA
    refine QuotientAddGroup.induction_on x ?_
    intro a
    refine QuotientAddGroup.induction_on yA ?_
    intro b
    refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
    · -- Both additive maps send the zero generator to zero.
      simp
    · intro V
      obtain ⟨L⟩ := exists_stableLattice A V.ρ
      refine FreeAbelianGroup.induction_on b ?_ ?_ ?_ ?_
      · -- The projective action of any class on `0` is zero.
        simp
      · intro Q
        -- On generators, transport `Q` through reduction and use the chosen stable lattice in `V`.
        have hQ :
            (projectiveGrothendieckReductionEquiv (A := A) (G := G)) [Q]ₚ₀ =
              [Q.residueFieldReduction]ₚ₀ := by
          change projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ =
            [Q.residueFieldReduction]ₚ₀
          exact projectiveGrothendieckReductionHom_projectiveClass_eq (A := A) (G := G) Q
        calc
          e (d [V]₀ • (projectiveGrothendieckReductionEquiv (A := A) (G := G) [Q]ₚ₀)) =
              e (d [V]₀ • [Q.residueFieldReduction]ₚ₀) := by
                rw [hQ]
          _ = [V]₀ * [Q.scalarExtension K]₀ := by
                simpa using
                  projectiveGrothendieckScalarExtensionHom_generator_smul
                    (A := A) (K := K) (G := G) V L Q
          _ = [V]₀ * projectiveGrothendieckBaseChangeHom K [Q]ₚ₀ := by
                rw [projectiveGrothendieckBaseChangeHom_projectiveClass_eq]
      · intro b hb
        -- Negation is preserved by all additive maps involved.
        simp [map_neg, smul_neg, mul_neg, hb]
      · intro b₁ b₂ hb₁ hb₂
        -- Addition is preserved by the projective action, scalar extension, and multiplication.
        simp [map_add, smul_add, mul_add, hb₁, hb₂]
    · intro a ha
      -- Negation in the representation variable is respected throughout.
      simp [map_neg, neg_smul, neg_mul, ha]
    · intro a₁ a₂ ha₁ ha₂
      -- Addition in the representation variable is respected throughout.
      simp [map_add, add_smul, add_mul, ha₁, ha₂]
  -- Rewrite `y` through its transported lift `yA`, prove the transported statement, and fold
  -- the definition of `e y` back to the original target.
  calc
    e (d x • y) =
        e (d x • (projectiveGrothendieckReductionEquiv (A := A) (G := G) yA)) := by
          rw [hy]
    _ = x * projectiveGrothendieckBaseChangeHom K yA := hmain x yA
    _ = x * e y := by
          simpa [yA] using
            congrArg
              (fun z : R_K(G) => x * z)
              (projectiveGrothendieckScalarExtensionHom_apply
                (A := A) (K := K) (G := G) y).symm

end ScalarExtensionCompatibility
#print axioms projectiveGrothendieckScalarExtensionHom_smul
end Representation
