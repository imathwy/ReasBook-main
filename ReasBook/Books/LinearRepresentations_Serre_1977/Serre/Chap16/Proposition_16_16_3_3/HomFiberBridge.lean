import LinearRepresentations_Serre_1977.Serre.Chap16.Proposition_16_16_3_3.PositiveBasics

noncomputable section

universe u

open CategoryTheory
open scoped MonoidAlgebra Representation TensorProduct

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A

omit [IsLocalRing A] [IsFractionRing A K] [Finite G] in
/-- Helper for Proposition 16-16.3-3: a representation whose action is the ambient
group-algebra generator action is equivalent to the canonical `ofModule'` representation. -/
theorem nonempty_ofModulePrimeEquivOfActionEqComm
    {R : Type u} [CommRing R] {G : Type u} [Group G]
    {M : Type u} [AddCommGroup M] [Module R M] [Module (MonoidAlgebra R G) M]
    [IsScalarTower R (MonoidAlgebra R G) M]
    (ρ : Representation R G M)
    (hρ : ∀ (g : G) (x : M), ρ g x = MonoidAlgebra.of R G g • x) :
    Nonempty ((show Representation R G M from Representation.ofModule' M).Equiv ρ) := by
  -- The identity linear equivalence intertwines once both actions agree on group-algebra
  -- generators.
  refine ⟨Representation.Equiv.mk (LinearEquiv.refl R M) fun g ↦ ?_⟩
  ext x
  simp only [LinearMap.comp_apply, LinearEquiv.refl_apply, LinearEquiv.coe_coe]
  rw [hρ g x]
  simp [Representation.ofModule', MonoidAlgebra.of]

omit [IsLocalRing A] [IsFractionRing A K] [Finite G] in
/-- Helper for Proposition 16-16.3-3: the exact lattice owner representation is the canonical
representation attached to its `A[G]`-module structure. -/
theorem stableLattice_toRepresentation_ofModule_equiv
    [IsDomain A] [IsDiscreteValuationRing A]
    {X : FDRep K G} (L : StableLattice A X.ρ) :
    Nonempty
      ((show Representation A G L.toSubmodule from Representation.ofModule' L.toSubmodule).Equiv
        L.toRepresentation) := by
  letI : Module A[G] L.toSubmodule := by
    change Module A[G] L.toRepresentation.asModule
    infer_instance
  letI : IsScalarTower A A[G] L.toSubmodule := by
    change IsScalarTower A A[G] L.toRepresentation.asModule
    infer_instance
  -- Reduce the comparison to the generator-action formula for the lattice representation.
  refine nonempty_ofModulePrimeEquivOfActionEqComm L.toRepresentation ?_
  intro g x
  rw [← Representation.asAlgebraHom_single_one (ρ := L.toRepresentation) g]
  rfl

omit [IsLocalRing A] [IsFractionRing A K] in
/-- Helper for Proposition 16-16.3-3: the finite-projective scalar-extension owner has the
expected underlying scalar-extended representation. -/
theorem finiteProjective_scalarExtension_rep_equiv
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Nonempty
      ((show Representation K G (TensorProduct A K Q.V) from
        Representation.scalarExtension (Representation.ofModule' Q.V)).Equiv
          (Q.scalarExtension K).ρ) := by
  -- This owner is an abbreviation around `FDRep.of` of the same scalar-extended representation.
  exact ⟨Representation.Equiv.refl _⟩

/-- Helper for Proposition 16-16.3-3: scalar-extending the exact lattice owner recovers the
ambient generic representation. -/
theorem stableLattice_scalarExtension_ofModule_equiv
    [IsDomain A] [IsDiscreteValuationRing A]
    {X : FDRep K G} (L : StableLattice A X.ρ) :
    Nonempty
      ((show Representation K G (TensorProduct A K L.toSubmodule) from
        Representation.scalarExtension (Representation.ofModule' L.toSubmodule)).Equiv X.ρ) := by
  rcases stableLattice_toRepresentation_ofModule_equiv (A := A) (K := K) (G := G) L with
    ⟨eA⟩
  let eScalar :
      (show Representation K G (TensorProduct A K L.toSubmodule) from
        Representation.scalarExtension (Representation.ofModule' L.toSubmodule)).Equiv
        (Representation.scalarExtension L.toRepresentation) :=
    Representation.scalarExtensionEquiv (A := A) (F := K) (G := G) eA
  rcases StableLattice.scalarExtension_exact_owner_fdrep_iso_local_support
      (A := A) (K := K) (G := G) L with
    ⟨eFD⟩
  let eFDRep :
      (Representation.scalarExtension L.toRepresentation).Equiv X.ρ := by
    simpa using Representation.equivOfIso ((forget₂ (FDRep K G) (Rep K G)).mapIso eFD)
  -- Compose functorial scalar extension with the exact-owner lattice theorem.
  exact ⟨eScalar.trans eFDRep⟩

/-- Helper for Proposition 16-16.3-3: a chosen projective lift identifies the residue scalar
extension of its owner with the target residue projective representation. -/
theorem projectiveLift_residue_scalarExtension_equiv
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (P : FiniteProjectiveGroupAlgebraModule k G)
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (hQ : Nonempty (Q.residueFieldReduction ≅ P)) :
    Nonempty
      ((show Representation k G (TensorProduct A k Q.V) from
        Representation.scalarExtension (Representation.ofModule' Q.V)).Equiv P.toRep.ρ) := by
  rcases hQ with ⟨eQP⟩
  let ρred : Rep k G :=
    Rep.of (show Representation k G (TensorProduct A k Q.V) from
      Representation.scalarExtension (Representation.ofModule' Q.V))
  have eSrcIso : ρred ≅ Q.residueFieldReduction.toRep := by
    simpa [ρred, FiniteProjectiveGroupAlgebraModule.residueFieldReduction,
      FiniteProjectiveGroupAlgebraModule.toRep] using
      (Rep.unitIso ρred)
  have hlin : Nonempty (Q.residueFieldReduction.V ≃ₗ[k[G]] P.V) := by
    exact (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
      (A := k) (G := G) Q.residueFieldReduction P).1 ⟨eQP⟩
  rcases hlin with ⟨elin⟩
  let eRedP : Q.residueFieldReduction.toRep ≅ P.toRep :=
    Rep.ofModuleMonoidAlgebra.mapIso elin.toModuleIso
  let eρ : (show Representation k G (TensorProduct A k Q.V) from
      Representation.scalarExtension (Representation.ofModule' Q.V)).Equiv P.toRep.ρ :=
    (Representation.equivOfIso eSrcIso).trans (Representation.equivOfIso eRedP)
  -- The residue reduction isomorphism supplies the source-side Hom-fiber transport.
  exact ⟨eρ⟩

omit [IsFractionRing A K] [Finite G] in
/-- Helper for Proposition 16-16.3-3: the residue scalar extension of the exact lattice owner is
the stable-lattice reduction representation. -/
theorem stableLattice_reduction_scalarExtension_equiv
    [IsDomain A] [IsDiscreteValuationRing A]
    {X : FDRep K G} (L : StableLattice A X.ρ) :
    Nonempty
      ((show Representation k G (TensorProduct A k L.toSubmodule) from
        Representation.scalarExtension (Representation.ofModule' L.toSubmodule)).Equiv
          (FDRep.of L.reductionRepresentation).ρ) := by
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
  have hred :=
    StableLattice.reduction_mkQ_isResidueFieldReduction_local
      (A := A) (K := K) (G := G) L
  have hact : ∀ (g : G) (x : L.toSubmodule),
      L.toRepresentation g x = MonoidAlgebra.of A G g • x := by
    intro g x
    rw [← Representation.asAlgebraHom_single_one (ρ := L.toRepresentation) g]
    rfl
  let ρL : Representation A G L.toSubmodule := Representation.ofModule' L.toSubmodule
  let ρLk : Representation k G (TensorProduct A k L.toSubmodule) :=
    Representation.scalarExtension ρL
  let eσ : ρLk.Equiv L.reductionRepresentation :=
    Representation.Equiv.mk hred.1.equiv fun g ↦ by
      apply LinearMap.ext
      intro y
      -- Check equivariance on pure tensors and extend additively across the tensor product.
      induction y using TensorProduct.induction_on with
      | zero =>
          simp [ρLk]
      | tmul c x =>
          have hsource : ρLk g (c ⊗ₜ[A] x) = c ⊗ₜ[A] (ρL g x) := by
            change (LinearMap.baseChange k (ρL g)) (c ⊗ₜ[A] x) = c ⊗ₜ[A] (ρL g x)
            rw [LinearMap.baseChange_tmul]
          have hsrc_action : ρL g x = L.toRepresentation g x := by
            change MonoidAlgebra.of A G g • x = L.toRepresentation g x
            rw [← hact g x]
          calc
            hred.1.equiv (ρLk g (c ⊗ₜ[A] x))
                = hred.1.equiv (c ⊗ₜ[A] (ρL g x)) := by rw [hsource]
            _ = c • (Submodule.mkQ L.maximalIdealSubmodule :
                  L.toSubmodule →ₗ[A] L.reduction) (ρL g x) := by
                    exact IsBaseChange.equiv_tmul hred.1 c (ρL g x)
            _ = c • (Submodule.mkQ L.maximalIdealSubmodule :
                  L.toSubmodule →ₗ[A] L.reduction) (L.toRepresentation g x) := by
                    rw [hsrc_action]
            _ = c • L.reductionRepresentation g
                  ((Submodule.mkQ L.maximalIdealSubmodule :
                    L.toSubmodule →ₗ[A] L.reduction) x) := by
                    exact congrArg (fun z ↦ c • z)
                      (StableLattice.reductionRepresentation_apply_mk (L := L) g x).symm
            _ = L.reductionRepresentation g (c •
                  ((Submodule.mkQ L.maximalIdealSubmodule :
                    L.toSubmodule →ₗ[A] L.reduction) x)) := by
                    rw [LinearMap.map_smul]
            _ = L.reductionRepresentation g (hred.1.equiv (c ⊗ₜ[A] x)) := by
                    rw [IsBaseChange.equiv_tmul hred.1 c x]
      | add y z hy hz =>
          simpa only [map_add, LinearMap.comp_apply] using congrArg₂ HAdd.hAdd hy hz
  have eσ' :
      (show Representation k G (TensorProduct A k L.toSubmodule) from
        Representation.scalarExtension (Representation.ofModule' L.toSubmodule)).Equiv
          (FDRep.of L.reductionRepresentation).ρ := by
    simpa [ρL, ρLk] using eσ
  -- The quotient map is a residue-field base change, so its base-change equivalence is the
  -- target-side Hom-fiber transport.
  exact ⟨eσ'⟩

/-- Helper for Proposition 16-16.3-3: a chosen projective lift and a stable lattice identify the
generic and residue Hom dimensions used in the Brauer pairing argument. -/
theorem projectiveLiftBaseChange_stableLattice_hom_finrank_eq
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (P : FiniteProjectiveGroupAlgebraModule k G)
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (hQ : Nonempty (Q.residueFieldReduction ≅ P))
    {X : FDRep K G} (L : StableLattice A X.ρ) :
    Module.finrank K (Representation.IntertwiningMap (Q.scalarExtension K).ρ X.ρ) =
      Module.finrank k
        (Representation.IntertwiningMap P.toRep.ρ (FDRep.of L.reductionRepresentation).ρ) := by
  letI : Module.Projective A[G] Q.V := Q.projective
  letI : Module.Free A Q.V := Q.free
  letI : Module.Finite A Q.V := inferInstance
  letI : Module A[G] L.toSubmodule := by
    change Module A[G] L.toRepresentation.asModule
    infer_instance
  letI : IsScalarTower A A[G] L.toSubmodule := by
    change IsScalarTower A A[G] L.toRepresentation.asModule
    infer_instance
  letI : Module.Free A L.toSubmodule := inferInstance
  letI : Module.Finite A L.toSubmodule := inferInstance
  have hbase :
      Module.finrank K (scalarExtIntertwiner A G Q.V L.toSubmodule K) =
        Module.finrank k (scalarExtIntertwiner A G Q.V L.toSubmodule k) := by
    -- The common-owner Hom-fiber theorem computes both field fibers as the same `A`-rank.
    exact scalarExtIntertwiner_finrank_eq
      (A := A) (G := G) (Q := Q.V) (T := L.toSubmodule) (S₁ := K) (S₂ := k)
  rcases finiteProjective_scalarExtension_rep_equiv (A := A) (K := K) (G := G) Q with
    ⟨eQK⟩
  rcases stableLattice_scalarExtension_ofModule_equiv (A := A) (K := K) (G := G) L with
    ⟨eLK⟩
  have hK :
      Module.finrank K (scalarExtIntertwiner A G Q.V L.toSubmodule K) =
        Module.finrank K (Representation.IntertwiningMap (Q.scalarExtension K).ρ X.ρ) := by
    -- Transport the generic fiber from the raw scalar-extension owners to the theorem-facing
    -- projective module and stable-lattice owners.
    exact Representation.IntertwiningMap.finrank_eq_of_equiv eQK eLK
  rcases projectiveLift_residue_scalarExtension_equiv (A := A) (G := G) P Q hQ with
    ⟨eQk⟩
  rcases stableLattice_reduction_scalarExtension_equiv (A := A) (K := K) (G := G) L with
    ⟨eLk⟩
  have hk :
      Module.finrank k (scalarExtIntertwiner A G Q.V L.toSubmodule k) =
        Module.finrank k
          (Representation.IntertwiningMap P.toRep.ρ (FDRep.of L.reductionRepresentation).ρ) := by
    -- Transport the residue fiber using the chosen projective lift and residue-lattice
    -- base-change equivalence.
    exact Representation.IntertwiningMap.finrank_eq_of_equiv eQk eLk
  -- Compare the raw Hom fibers first, then transport each side to the public owners.
  exact hK.symm.trans (hbase.trans hk)

end

end Representation
