import LinearRepresentations_Serre_1977.Chap14.Lemma_14_14_4_2
import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_4_5
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3.LocalProjectiveBridges
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.ReductionMkQ
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2

noncomputable section

open CategoryTheory
open Representation
open scoped MonoidAlgebra Representation TensorProduct

universe u x

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {p : ℕ} [CharP (IsLocalRing.ResidueField A) p]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable {E : Type x} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]

local notation "k" => IsLocalRing.ResidueField A

namespace StableLattice

section ModuleBridges

variable {ρ : Representation K G E}

/-- Helper for Proposition 15-15.5-1: the exact lattice owner carries the induced `A[G]`-module
structure. -/
private instance toSubmodule_module_local_support
    (L : StableLattice A ρ) :
    Module A[G] L.toSubmodule := by
  change Module A[G] L.toRepresentation.asModule
  infer_instance

/-- Helper for Proposition 15-15.5-1: the induced `A[G]`-action on the exact owner is compatible
with restriction of scalars from `A`. -/
private instance toSubmodule_isScalarTower_local_support
    (L : StableLattice A ρ) :
    IsScalarTower A A[G] L.toSubmodule := by
  change IsScalarTower A A[G] L.toRepresentation.asModule
  infer_instance

/-- Helper for Proposition 15-15.5-1: the reduction owner carries the natural restricted
`A`-module structure. -/
private instance reduction_module_local_support
    (L : StableLattice A ρ) :
    Module A L.reduction :=
  Module.compHom L.reduction (algebraMap A k)

/-- Helper for Proposition 15-15.5-1: the reduction owner forms the expected scalar tower over the
residue field. -/
private instance reduction_isScalarTower_local_support
    (L : StableLattice A ρ) :
    IsScalarTower A k L.reduction :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Proposition 15-15.5-1: the exact reduced owner carries the induced `k[G]`-module
structure. -/
private instance reduction_groupAlgebra_module_local_support
    (L : StableLattice A ρ) :
    Module k[G] L.reduction := by
  change Module k[G] L.reductionRepresentation.asModule
  infer_instance

/-- Helper for Proposition 15-15.5-1: the induced `k[G]`-action on the reduction owner is
compatible with the residue-field scalar action. -/
private instance reduction_groupAlgebra_isScalarTower_local_support
    (L : StableLattice A ρ) :
    IsScalarTower k k[G] L.reduction := by
  change IsScalarTower k k[G] L.reductionRepresentation.asModule
  infer_instance

end ModuleBridges

/-- Helper for Proposition 15-15.5-1: rebundling an `FDRep` from its underlying representation
does not change its isomorphism class. -/
private noncomputable def fdRepIsoOfRho_local_support
    (X : FDRep K G) : X ≅ FDRep.of X.ρ :=
  Action.mkIso (Iso.refl _) fun g => by
    -- Rebundling preserves the carrier and the action pointwise.
    ext x
    rfl

/-- Helper for Proposition 15-15.5-1: the tautological `F[G]`-module attached to a
representation is canonically linear-equivalent to its carrier. -/
private theorem nonempty_asModuleLinearEquiv_target_local_support
    {F : Type u} [Field F]
    {V : Type x} [AddCommGroup V] [Module F V]
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
    _ = a • ρ.asModuleEquiv x := by
          rfl

/-- Helper for Proposition 15-15.5-1: an isomorphism of reduced `FDRep` owners gives a
`k[G]`-linear equivalence of the exact reduction modules. -/
private theorem reduction_nonempty_linearEquiv_of_nonempty_iso_local_support
    {X Y : FDRep K G}
    (LX : StableLattice A X.ρ) (LY : StableLattice A Y.ρ)
    (hXY :
      Nonempty (FDRep.of LX.reductionRepresentation ≅
        FDRep.of LY.reductionRepresentation)) :
    Nonempty (LX.reduction ≃ₗ[k[G]] LY.reduction) := by
  rcases hXY with ⟨e⟩
  have hLX :
      Nonempty
        (asModule (FDRep.of LX.reductionRepresentation).ρ ≃ₗ[k[G]] LX.reduction) := by
    simpa using
      (nonempty_asModuleLinearEquiv_target_local_support
        (G := G) (ρ := (FDRep.of LX.reductionRepresentation).ρ))
  have hLY :
      Nonempty
        (asModule (FDRep.of LY.reductionRepresentation).ρ ≃ₗ[k[G]] LY.reduction) := by
    simpa using
      (nonempty_asModuleLinearEquiv_target_local_support
        (G := G) (ρ := (FDRep.of LY.reductionRepresentation).ρ))
  rcases hLX with ⟨eLX⟩
  rcases hLY with ⟨eLY⟩
  let eMod :
      asModule (FDRep.of LX.reductionRepresentation).ρ ≃ₗ[k[G]]
        asModule (FDRep.of LY.reductionRepresentation).ρ :=
    (((forget₂ (FDRep k G) (Rep k G)) ⋙ Rep.toModuleMonoidAlgebra).mapIso e).toLinearEquiv
  -- Forget the bundled `FDRep` isomorphism to the exact reduction owners and compare there.
  exact ⟨eLX.trans (eMod.trans eLY.symm)⟩

/-- Helper for Proposition 15-15.5-1: the scalar extension of the exact lattice owner already
has the raw tensor-product `K[G]`-module structure on `K ⊗[A] L.toSubmodule`. -/
lemma scalarExtension_exact_owner_asModule_linearEquiv_local_support
    {X : FDRep K G} (L : StableLattice A X.ρ) :
    Nonempty
      (asModule
          (show Representation K G (K ⊗[A] L.toSubmodule) from
            Representation.scalarExtension L.toRepresentation) ≃ₗ[K[G]]
        (K ⊗[A] L.toSubmodule)) := by
  let ρ : Representation K G (K ⊗[A] L.toSubmodule) :=
    Representation.scalarExtension L.toRepresentation
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
        -- Route correction: prove the generator case on pure tensors, then extend linearly in
        -- the `K[G]`-variable so the raw tensor-product owner remains fixed throughout.
        refine MonoidAlgebra.induction_on
          (p := fun b : K[G] =>
            ρ.asAlgebraHom b (ρ.asModuleEquiv x) = b • ρ.asModuleEquiv x) a ?_ ?_ ?_
        · intro g
          induction ρ.asModuleEquiv x using TensorProduct.induction_on with
          | zero =>
              simp [ρ]
          | tmul z y =>
              have hρ :
                  ρ g (z ⊗ₜ[A] y) =
                    (z ⊗ₜ[A] (L.toRepresentation g y) : K ⊗[A] L.toSubmodule) := by
                change
                  ((Module.End.baseChangeHom A K L.toSubmodule) (L.toRepresentation g))
                      (z ⊗ₜ[A] y) =
                    _
                exact LinearMap.baseChange_tmul (f := L.toRepresentation g) (A := K) z y
              have hy :
                  L.toRepresentation g y = MonoidAlgebra.of A G g • y := by
                exact
                  Representation.asModuleEquiv_symm_map_rho
                    (ρ := L.toRepresentation) g y
              have hsmul :
                  MonoidAlgebra.of K G g • (z ⊗ₜ[A] y : K ⊗[A] L.toSubmodule) =
                    (z ⊗ₜ[A] (MonoidAlgebra.of A G g • y) : K ⊗[A] L.toSubmodule) := by
                exact
                  monoidAlgebra_of_smul_tmul
                    (Λ := A) (κ := K) (G := G) (P := L.toSubmodule) g z y
              calc
                ρ.asAlgebraHom (MonoidAlgebra.of K G g) (z ⊗ₜ[A] y)
                    = ρ g (z ⊗ₜ[A] y) := by
                        simp [ρ, Representation.asAlgebraHom_of]
                _ = (z ⊗ₜ[A] (L.toRepresentation g y) : K ⊗[A] L.toSubmodule) := by
                      rw [hρ]
                _ = (z ⊗ₜ[A] (MonoidAlgebra.of A G g • y) : K ⊗[A] L.toSubmodule) := by
                      rw [hy]
                _ = MonoidAlgebra.of K G g • (z ⊗ₜ[A] y : K ⊗[A] L.toSubmodule) := by
                      rw [hsmul]
          | add y z hy hz =>
              calc
                ρ.asAlgebraHom (MonoidAlgebra.of K G g) (y + z)
                    = ρ.asAlgebraHom (MonoidAlgebra.of K G g) y +
                        ρ.asAlgebraHom (MonoidAlgebra.of K G g) z := by
                          simp [map_add]
                _ = MonoidAlgebra.of K G g • y + MonoidAlgebra.of K G g • z := by
                      rw [hy, hz]
                _ = MonoidAlgebra.of K G g • (y + z) := by
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

/-- Helper for Proposition 15-15.5-1: the inclusion of a stable lattice into the ambient
representation is the canonical base change from `A` to the fraction field `K`. -/
lemma toSubmodule_subtype_isBaseChange_local_support
    {ρ : Representation K G E} (L : StableLattice A ρ) :
    IsBaseChange K (L.toSubmodule.subtype : L.toSubmodule →ₗ[A] E) := by
  let ι := Module.Free.ChooseBasisIndex A L.toSubmodule
  let b : Module.Basis ι A L.toSubmodule := Module.Free.chooseBasis A L.toSubmodule
  let e : Module.Basis ι K E := b.extendOfIsLattice K
  let ibc : IsBaseChange K (Finsupp.linearCombination A e) := IsBaseChange.of_basis A e
  -- Route correction: record the lattice inclusion itself as the base-change owner, so later
  -- exact-owner packaging can reuse this bridge instead of rebuilding tensor transports.
  refine IsBaseChange.of_equiv ((b.repr.baseChange A K _ _).trans ibc.equiv) ?_
  intro x
  suffices
      Finsupp.linearCombination A e (b.repr x) = ((x : L.toSubmodule) : E) by
    simpa only [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, IsBaseChange.equiv_tmul,
      one_smul, Submodule.subtype_apply] using this
  -- Expand the lattice vector in the chosen `A`-basis and then read the same coordinates in the
  -- ambient `K`-basis supplied by `extendOfIsLattice`.
  calc
    Finsupp.linearCombination A e (b.repr x) = (b.repr x).sum fun i a ↦ a • e i := by
      simp [Finsupp.linearCombination_apply]
    _ = ∑ i, (b.repr x i : A) • e i := by
      exact
        Finsupp.sum_fintype (b.repr x) (fun i a ↦ a • e i) (fun i ↦ zero_smul A (e i))
    _ = ∑ i, (b.repr x i : A) • ((b i : L.toSubmodule) : E) := by
      simp [e, Module.Basis.extendOfIsLattice_apply]
    _ = ((((∑ i, (b.repr x i : A) • b i : L.toSubmodule)) : L.toSubmodule) : E) := by
      symm
      simpa [Submodule.coe_smul_of_tower] using
        (Submodule.coe_sum (p := L.toSubmodule) (s := Finset.univ)
          (x := fun i ↦ ((b.repr x i : A) • b i : L.toSubmodule)))
    _ = ((x : L.toSubmodule) : E) := by
      exact congrArg Subtype.val (b.sum_repr x)

/-- Helper for Proposition 15-15.5-1: scalar extension of the exact lattice owner recovers the
ambient generic representation. -/
lemma scalarExtension_exact_owner_fdrep_iso_local_support
    {X : FDRep K G} (L : StableLattice A X.ρ) :
    Nonempty (FDRep.of (Representation.scalarExtension L.toRepresentation) ≅ X) := by
  let hbase :=
    toSubmodule_subtype_isBaseChange_local_support
      (A := A) (K := K) (G := G) (E := X.V) L
  have hinter :
      (Representation.scalarExtension L.toRepresentation).IsIntertwiningMap
        X.ρ hbase.equiv.toLinearMap := by
    refine Representation.IsIntertwiningMap.mk ?_
    intro g v
    -- The base-change equivalence already matches the scalar-extended action with the ambient one
    -- on pure tensors, so tensor induction upgrades it to an honest intertwiner.
    refine TensorProduct.induction_on v ?_ ?_ ?_
    · simp
    · intro z x
      calc
        hbase.equiv (((L.toRepresentation g).baseChange K) (z ⊗ₜ[A] x)) =
            hbase.equiv (z ⊗ₜ[A] (L.toRepresentation g x)) := by
              simp [Representation.scalarExtension]
        _ = z • (((L.toRepresentation g x : L.toSubmodule) : X.V)) := by
              simpa using hbase.equiv_tmul z (L.toRepresentation g x)
        _ = z • (X.ρ g (((x : L.toSubmodule) : X.V))) := by
              rfl
        _ = X.ρ g (z • (((x : L.toSubmodule) : X.V))) := by
              rw [LinearMap.map_smul]
        _ = X.ρ g (hbase.equiv (z ⊗ₜ[A] x)) := by
              rw [show hbase.equiv (z ⊗ₜ[A] x) = z • (((x : L.toSubmodule) : X.V)) by
                    simpa using hbase.equiv_tmul z x]
    · intro v₁ v₂ hv₁ hv₂
      simpa [LinearEquiv.map_add, LinearMap.map_add] using
        congrArg₂ HAdd.hAdd hv₁ hv₂
  let eRep :
      (Representation.scalarExtension L.toRepresentation).Equiv X.ρ :=
    Representation.Equiv.mk hbase.equiv fun g ↦ by
      exact LinearMap.ext (hinter.isIntertwining g)
  -- Package the representation equivalence as an isomorphism in `FDRep`, then remove the final
  -- rebundling of `X`.
  exact ⟨eRep.toFDRepIso.trans (fdRepIsoOfRho_local_support (X := X)).symm⟩

/-- Helper for Proposition 15-15.5-1: an isomorphism of reductions reflects to an exact-owner
`A[G]`-linear equivalence when `p ∤ |G|`. -/
lemma reduction_iso_reflects_exact_owner_linearEquiv_of_order_prime_to_p
    (hG : ¬ p ∣ Nat.card G)
    {X Y : FDRep K G}
    (LX : StableLattice A X.ρ) (LY : StableLattice A Y.ρ)
    (hXY :
      Nonempty (FDRep.of LX.reductionRepresentation ≅
        FDRep.of LY.reductionRepresentation)) :
    Nonempty (LX.toSubmodule ≃ₗ[A[G]] LY.toSubmodule) := by
  have hred :
      Nonempty (LX.reduction ≃ₗ[k[G]] LY.reduction) :=
    reduction_nonempty_linearEquiv_of_nonempty_iso_local_support
      (A := A) (K := K) (G := G) LX LY hXY
  let _ : Module.Free A LX.toSubmodule := by
    infer_instance
  let _ : Module.Free A LY.toSubmodule := by
    infer_instance
  have hprojLX : Module.Projective A[G] LX.toSubmodule := by
    -- Over the local ring, Serre's averaging argument makes each exact owner projective.
    exact
      Representation.free_groupAlgebra_module_projective_of_order_prime_to_p
        (A := A) (G := G) (p := p) (P := LX.toSubmodule) hG
  have hprojLY : Module.Projective A[G] LY.toSubmodule := by
    -- The same prime-to-`p` averaging argument applies to the second exact owner.
    exact
      Representation.free_groupAlgebra_module_projective_of_order_prime_to_p
        (A := A) (G := G) (p := p) (P := LY.toSubmodule) hG
  -- Chapter 14 reflects an equivalence of residue-field reductions back to an equivalence of the
  -- projective exact owners themselves.
  exact
    (projective_monoidAlgebra_nonempty_linearEquiv_iff_of_isResidueFieldReduction
      (Λ := A) (G := G)
      (P := LX.toSubmodule)
      (Pbar := LX.reduction)
      (f := (Submodule.mkQ LX.maximalIdealSubmodule : LX.toSubmodule →ₗ[A] LX.reduction))
      (hf := StableLattice.reduction_mkQ_isResidueFieldReduction_local
        (A := A) (K := K) (G := G) LX)
      (P' := LY.toSubmodule)
      (Pbar' := LY.reduction)
      (f' := (Submodule.mkQ LY.maximalIdealSubmodule : LY.toSubmodule →ₗ[A] LY.reduction))
      (hf' := StableLattice.reduction_mkQ_isResidueFieldReduction_local
        (A := A) (K := K) (G := G) LY)
      hprojLX hprojLY).2 hred

end StableLattice

namespace Representation

section ExactOwnerScalarExtension

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {p : ℕ} [CharP (IsLocalRing.ResidueField A) p]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Proposition 15-15.5-1: rebundling an `FDRep` from its underlying representation
does not change its isomorphism class on the field side either. -/
private noncomputable def fdRepIsoOfRho_field_local_support
    (X : FDRep K G) : X ≅ FDRep.of X.ρ :=
  Action.mkIso (Iso.refl _) fun g => by
    -- Rebundling preserves the carrier and the action pointwise.
    ext x
    rfl

/-- Helper for Proposition 15-15.5-1: the owner module of the scalar extension of an exact
finite-projective owner is the raw tensor-product `K[G]`-module. -/
lemma fdRepAsModule_scalarExtension_exact_owner_linearEquiv_local_support
    (P : FiniteProjectiveGroupAlgebraModule A G) :
    Nonempty (asModule (P.scalarExtension K).ρ ≃ₗ[K[G]] (K ⊗[A] P.V)) := by
  -- Unfold the scalar-extension owner once; afterwards the carrier is definitionally the ambient
  -- tensor-product module.
  refine ⟨?_⟩
  simpa [FiniteProjectiveGroupAlgebraModule.scalarExtension] using
    (LinearEquiv.refl K[G] (asModule (P.scalarExtension K).ρ))

/-- Helper for Proposition 15-15.5-1: a `K[G]`-linear equivalence between owner modules upgrades
to an isomorphism of finite-dimensional `G`-representations over `K`. -/
lemma fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv_field_local_support
    {σ τ : FDRep K G}
    (hστ : Nonempty (asModule σ.ρ ≃ₗ[K[G]] asModule τ.ρ)) :
    Nonempty (σ ≅ τ) := by
  rcases hστ with ⟨e⟩
  let f : Representation.IntertwiningMap σ.ρ τ.ρ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := σ.ρ) (σ := τ.ρ)).symm e.toLinearMap
  let eRep : Representation.Equiv σ.ρ τ.ρ :=
    Representation.Equiv.mk (e.restrictScalars K) f.isIntertwining'
  -- Route correction: package the owner equivalence directly as a representation equivalence to
  -- keep `Rep.ofModuleMonoidAlgebra` out of the scalar-extension closing step.
  exact ⟨((fdRepIsoOfRho_field_local_support (K := K) (G := G) σ).trans
    (Representation.Equiv.toFDRepIso eRep)).trans
    (fdRepIsoOfRho_field_local_support (K := K) (G := G) τ).symm⟩

/-- Helper for Proposition 15-15.5-1: a raw tensor-product owner equivalence packages the scalar
extension of an exact finite-projective owner as the corresponding `FDRep`. -/
lemma finiteProjective_scalarExtension_nonempty_iso_of_nonempty_owner_linearEquiv_local_support
    (P : FiniteProjectiveGroupAlgebraModule A G)
    {V : Type u} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (ρ : Representation K G V)
    (hρ : Nonempty ((K ⊗[A] P.V) ≃ₗ[K[G]] asModule ρ)) :
    Nonempty (P.scalarExtension K ≅ FDRep.of ρ) := by
  rcases
      fdRepAsModule_scalarExtension_exact_owner_linearEquiv_local_support
        (A := A) (K := K) (G := G) P with
    ⟨eOwner⟩
  rcases hρ with ⟨eρ⟩
  -- First compare the scalar-extension owner with the target owner as `K[G]`-modules, then
  -- repackage that comparison as an `FDRep` isomorphism.
  exact
    fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv_field_local_support
      (K := K) (G := G) ⟨by simpa using eOwner.trans eρ⟩

end ExactOwnerScalarExtension

end Representation

end
