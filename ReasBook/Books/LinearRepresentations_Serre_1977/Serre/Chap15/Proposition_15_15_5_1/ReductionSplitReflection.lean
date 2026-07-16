import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Serre.Chap14.Exercise_14_14_4_5
import LinearRepresentations_Serre_1977.Serre.Chap14.Infra_14_4_ProjectiveLift
import LinearRepresentations_Serre_1977.Serre.Chap14.Lemma_14_14_4_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_2_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_2_5
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_2_6.Foundations
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_5_3.LocalProjectiveBridges
import LinearRepresentations_Serre_1977.Serre.Chap15.Proposition_15_15_5_1.ReductionMkQ
import LinearRepresentations_Serre_1977.Serre.Chap15.Proposition_15_15_5_1.StableLatticeExactOwner
import LinearRepresentations_Serre_1977.Serre.Chap15.Proposition_15_15_5_1.ProjectiveScalarExtensionClasses
import LinearRepresentations_Serre_1977.Serre.Chap15.Proposition_15_15_5_1.ReductionProductOwners
import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2

noncomputable section

open CategoryTheory
open Representation
open scoped MonoidAlgebra Representation TensorProduct

universe u v

section DecompositionHom

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [HenselianLocalRing A]
variable [CharP (IsLocalRing.ResidueField A) p]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
local notation:max "R_K(" G ")" => finiteRepGrothendieckGroup K G
local notation:max "R_k(" G ")" => finiteRepGrothendieckGroup k G

/-- Helper for Proposition 15-15.5-1: irreducibility transports across a representation
equivalence. -/
private noncomputable def subrepresentationOrderIso_local
    {F : Type u} [Field F]
    {W W' : Type v} [AddCommGroup W] [Module F W]
    [AddCommGroup W'] [Module F W']
    {ρ : Representation F G W} {σ : Representation F G W'}
    (e : ρ.Equiv σ) :
    Subrepresentation ρ ≃o Subrepresentation σ where
  toFun U :=
    { toSubmodule := U.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule := by
        intro g x hx
        rcases hx with ⟨y, hy, rfl⟩
        refine ⟨ρ g y, U.apply_mem_toSubmodule g hy, ?_⟩
        simp [e.isIntertwining] }
  invFun U :=
    { toSubmodule := U.toSubmodule.map e.symm.toLinearMap
      apply_mem_toSubmodule := by
        intro g x hx
        rcases hx with ⟨y, hy, rfl⟩
        refine ⟨σ g y, U.apply_mem_toSubmodule g hy, ?_⟩
        simp [e.symm.isIntertwining] }
  left_inv := by
    intro U
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have : y = e x := by
        simpa using congrArg e hxy
      subst this
      simp at hy
      exact hy
    · intro hx
      change x ∈
        Submodule.map e.symm.toLinearMap (Submodule.map e.toLinearMap U.toSubmodule)
      exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩
  right_inv := by
    intro U
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have : y = e.symm x := by
        simpa using congrArg e.symm hxy
      subst this
      simp at hy
      exact hy
    · intro hx
      change x ∈
        Submodule.map e.toLinearMap (Submodule.map e.symm.toLinearMap U.toSubmodule)
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩
  map_rel_iff' := by
    intro U V
    constructor
    · intro h x hx
      have hx' : e x ∈ U.toSubmodule.map e.toLinearMap := ⟨x, hx, rfl⟩
      rcases h hx' with ⟨y, hy, hxy⟩
      have : y = x := by
        apply e.toLinearEquiv.injective
        simpa using hxy
      simpa [this] using hy
    · intro h x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨y, h hy, rfl⟩

/-- Helper for Proposition 15-15.5-1: irreducibility transports across a representation
equivalence. -/
private theorem isIrreducible_of_equiv_local
    {F : Type u} [Field F]
    {W W' : Type v} [AddCommGroup W] [Module F W]
    [AddCommGroup W'] [Module F W']
    {ρ : Representation F G W} {σ : Representation F G W'}
    [ρ.IsIrreducible] (e : ρ.Equiv σ) : σ.IsIrreducible := by
  -- Irreducibility is the simple-order owner on subrepresentations, so transport it through the
  -- mapped-carrier order isomorphism.
  exact OrderIso.isSimpleOrder_iff (subrepresentationOrderIso_local (G := G) e) |>.mp inferInstance

/-- Helper for Proposition 15-15.5-1: under Maschke's hypothesis, a reduced subrepresentation can
be packaged on its exact `asModule` owner as a finite projective `k[G]`-module. -/
private theorem subrepresentation_asModule_finiteProjective_owner_of_order_prime_to_p
    (τ : FDRep k G)
    (U : Subrepresentation τ.ρ)
    (hG : ¬ p ∣ Nat.card G) :
    ∃ P : FiniteProjectiveGroupAlgebraModule k G,
      Nonempty (P.V ≃ₗ[k[G]] asModule U.toRepresentation) := by
  letI : Module k[G] U.toSubmodule :=
    Module.compHom U.toSubmodule U.toRepresentation.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] U.toSubmodule :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change U.toRepresentation.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  let M : ModuleCat k[G] := ModuleCat.of k[G] U.toSubmodule
  have hfinite : Module.Finite k[G] M := by
    -- The reduced summand is finite-dimensional over `k`, hence finite over the group algebra.
    change Module.Finite k[G] U.toSubmodule
    exact Module.Finite.of_restrictScalars_finite k k[G] U.toSubmodule
  let Pfg : FGModuleCat k[G] := ⟨M, hfinite⟩
  have hproj_sub : Module.Projective k[G] U.toSubmodule := by
    let _ : Fintype G := Fintype.ofFinite G
    let _ : NeZero (Nat.card G : k) := NeZero.of_not_dvd k hG
    let _ : IsSemisimpleRing k[G] := by
      infer_instance
    exact Module.projective_of_isSemisimpleRing k[G] U.toSubmodule
  have hproj : Module.Projective k[G] Pfg := by
    -- Route correction: package the summand on the exact `asModule` carrier itself, so the
    -- Maschke projectivity owner applies without any subtype-owner transport.
    simpa [Pfg, M] using hproj_sub
  let P : FiniteProjectiveGroupAlgebraModule k G := ⟨Pfg, hproj⟩
  rcases
      nonempty_asModuleLinearEquiv_target_field_local
        (G := G) (ρ := U.toRepresentation) with
    ⟨eU⟩
  refine ⟨P, ?_⟩
  -- The chosen owner is definitionally the exact `asModule` carrier of `U`.
  exact ⟨by
    simpa [P, Pfg, M, FiniteProjectiveGroupAlgebraModule.V] using
      eU.symm⟩

/-- Helper for Proposition 15-15.5-1: each reduced summand lifts to a finite projective
`A[G]`-module whose residue-field reduction is the exact `asModule` owner of that summand. -/
private theorem subrepresentation_exists_projective_lift_of_order_prime_to_p
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (τ : FDRep k G)
    (U : Subrepresentation τ.ρ)
    (hG : ¬ p ∣ Nat.card G) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G,
      Nonempty ((k ⊗[A] Q.V) ≃ₗ[k[G]] asModule U.toRepresentation) := by
  obtain ⟨P, hP⟩ :=
    subrepresentation_asModule_finiteProjective_owner_of_order_prime_to_p
      (G := G) (p := p) τ U hG
  obtain ⟨Q, hQP⟩ :=
    Representation.exists_projective_lift_of_residueField_projective
      (A := A) (G := G) P
  rcases hP with ⟨eP⟩
  rcases
      (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
        (A := k) (G := G) Q.residueFieldReduction P).1 hQP with
    ⟨eQP⟩
  refine ⟨Q, ?_⟩
  -- The Chapter `14` lift theorem already identifies the residue-field reduction of `Q` with the
  -- canonical summand owner `P`; now forget the owner and read the carrier as `asModule U`.
  exact ⟨by
    simpa [FiniteProjectiveGroupAlgebraModule.residueFieldReduction,
      FiniteProjectiveGroupAlgebraModule.V] using
      eQP.trans eP⟩

/-- Helper for Proposition 15-15.5-1: a complemented split of the reduction rewrites as the
reduction of a product of projective lifts of the two factors. -/
private theorem reduction_split_to_lifted_product_linearEquiv_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (X : FDRep K G)
    (hG : ¬ p ∣ Nat.card G)
    (L : StableLattice A X.ρ)
    (U V : Subrepresentation L.reductionRepresentation)
    (hUV : IsCompl U V) :
    ∃ QU QV : FiniteProjectiveGroupAlgebraModule A G,
      Nonempty ((k ⊗[A] QU.V) ≃ₗ[k[G]] asModule U.toRepresentation) ∧
      Nonempty ((k ⊗[A] QV.V) ≃ₗ[k[G]] asModule V.toRepresentation) ∧
      Nonempty (L.reduction ≃ₗ[k[G]] k ⊗[A] (QU.V × QV.V)) := by
  obtain ⟨QU, hQU⟩ :=
    subrepresentation_exists_projective_lift_of_order_prime_to_p
      (A := A) (G := G) (p := p) (τ := FDRep.of L.reductionRepresentation) U hG
  obtain ⟨QV, hQV⟩ :=
    subrepresentation_exists_projective_lift_of_order_prime_to_p
      (A := A) (G := G) (p := p) (τ := FDRep.of L.reductionRepresentation) V hG
  rcases hQU with ⟨eQU⟩
  rcases hQV with ⟨eQV⟩
  rcases
      subrepresentation_prod_nonempty_asModuleLinearEquiv_of_isCompl_local
        (G := G) U V
        (subrepresentation_isCompl_toSubmodule_local (G := G) hUV) with
    ⟨eSplit⟩
  rcases
      subrepresentation_prod_asModule_to_factorwise_product_linearEquiv_local
        (G := G) U V with
    ⟨eProd⟩
  rcases
      reduction_prod_nonempty_linearEquiv_local
        (A := A) (G := G) (P := QU.V) (Q := QV.V) with
    ⟨ered⟩
  refine ⟨QU, QV, ?_, ?_, ?_⟩
  · exact ⟨eQU⟩
  · exact ⟨eQV⟩
  · -- Follow Serre's source route: split the reduced module, identify the product owner
    -- factorwise, then rewrite the factorwise summands as reductions of lifted projectives.
    exact ⟨by
      simpa using
        eSplit.symm.trans
          (eProd.trans
            ((LinearEquiv.prodCongr eQU.symm eQV.symm).trans ered.symm))⟩
/-- Helper for Proposition 15-15.5-1: scalar extension of the product exact owner identifies
directly with the `asModule` owner of the product representation upstairs. -/
private theorem scalarExtension_prod_exact_owner_asModule_linearEquiv_local
    (QU QV : FiniteProjectiveGroupAlgebraModule A G) :
    Nonempty ((K ⊗[A] (QU.V × QV.V)) ≃ₗ[K[G]]
      asModule (Representation.prod (QU.scalarExtension K).ρ (QV.scalarExtension K).ρ)) := by
  let Dom := (K ⊗[A] QU.V) × (K ⊗[A] QV.V)
  let ρprod : Representation K G Dom :=
    Representation.prod (QU.scalarExtension K).ρ (QV.scalarExtension K).ρ
  rcases
      scalarExtension_prod_nonempty_linearEquiv_local
        (A := A) (K := K) (G := G) (P := QU.V) (Q := QV.V) with
    ⟨eprod⟩
  let eρprod : asModule ρprod ≃ₗ[K[G]] Dom :=
    { toFun := fun x ↦ ρprod.asModuleEquiv x
      invFun := fun x ↦ ρprod.asModuleEquiv.symm x
      left_inv := fun x ↦ ρprod.asModuleEquiv.left_inv x
      right_inv := fun x ↦ ρprod.asModuleEquiv.right_inv x
      map_add' := fun x y ↦ ρprod.asModuleEquiv.map_add x y
      map_smul' := by
        intro r x
        calc
          ρprod.asModuleEquiv (r • x) = ρprod.asAlgebraHom r (ρprod.asModuleEquiv x) := by
            exact Representation.asModuleEquiv_map_smul (ρ := ρprod) r x
          _ = r • ρprod.asModuleEquiv x := by
            rcases ρprod.asModuleEquiv x with ⟨x₁, x₂⟩
            refine MonoidAlgebra.induction_on
              (p := fun s : K[G] => ρprod.asAlgebraHom s (x₁, x₂) = s • (x₁, x₂)) r ?_ ?_ ?_
            · intro g
              have hQU :
                  ((QU.scalarExtension K).ρ g) x₁ =
                    MonoidAlgebra.of K G g • x₁ := by
                exact Representation.asModuleEquiv_symm_map_rho
                  (ρ := (QU.scalarExtension K).ρ) g x₁
              have hQV :
                  ((QV.scalarExtension K).ρ g) x₂ =
                    MonoidAlgebra.of K G g • x₂ := by
                exact Representation.asModuleEquiv_symm_map_rho
                  (ρ := (QV.scalarExtension K).ρ) g x₂
              ext
              · simpa [ρprod, Representation.prod, Representation.asAlgebraHom_of] using hQU
              · simpa [ρprod, Representation.prod, Representation.asAlgebraHom_of] using hQV
            · intro a b ha hb
              calc
                ρprod.asAlgebraHom (a + b) (x₁, x₂)
                    = ρprod.asAlgebraHom a (x₁, x₂) + ρprod.asAlgebraHom b (x₁, x₂) := by
                        simp [map_add]
                _ = a • (x₁, x₂) + b • (x₁, x₂) := by rw [ha, hb]
                _ = (a + b) • (x₁, x₂) := by simp [add_smul]
            · intro c a ha
              calc
                ρprod.asAlgebraHom (c • a) (x₁, x₂)
                    = c • ρprod.asAlgebraHom a (x₁, x₂) := by simp
                _ = c • (a • (x₁, x₂)) := by rw [ha]
                _ = (c • a) • (x₁, x₂) := by simp }
  -- Keep the product side unbundled until the end: first split the tensor product, then identify
  -- the resulting carrier with the canonical `asModule` owner of the product representation.
  exact ⟨by
    simpa [Dom, ρprod] using eprod.trans eρprod.symm⟩

/-- Helper for Proposition 15-15.5-1: the scalar extension of the exact lattice owner is already
the raw tensor-product `K[G]`-module on `K ⊗[A] L.toSubmodule`. -/
private theorem scalarExtension_exact_owner_asModule_linearEquiv_local
    (X : FDRep K G)
    (L : StableLattice A X.ρ) :
    Nonempty
      (asModule
          (show Representation K G (K ⊗[A] L.toSubmodule) from
            Representation.scalarExtension L.toRepresentation) ≃ₗ[K[G]]
        (K ⊗[A] L.toSubmodule)) := by
  exact
    StableLattice.scalarExtension_exact_owner_asModule_linearEquiv_local_support
      (A := A) (K := K) (G := G) L

/-- Helper for Proposition 15-15.5-1: after reflecting the reduced split to the exact owner
upstairs, scalar extension lands directly in the product representation owner. -/
private theorem reflected_exact_owner_scalarExtension_to_prod_asModule_linearEquiv_local
    (X : FDRep K G)
    (L : StableLattice A X.ρ)
    (QU QV : FiniteProjectiveGroupAlgebraModule A G)
    (hA : Nonempty (L.toSubmodule ≃ₗ[A[G]] (QU.V × QV.V))) :
    Nonempty ((K ⊗[A] L.toSubmodule) ≃ₗ[K[G]]
      asModule (Representation.prod (QU.scalarExtension K).ρ (QV.scalarExtension K).ρ)) := by
  rcases
      scalarExtension_nonempty_linearEquiv_of_nonempty_linearEquiv_local
        (A := A) (K := K) (G := G) (P := L.toSubmodule) (Q := QU.V × QV.V) hA with
    ⟨eK⟩
  rcases
      scalarExtension_prod_exact_owner_asModule_linearEquiv_local
        (A := A) (K := K) (G := G) QU QV with
    ⟨eprod⟩
  -- Base-change Serre's exact-owner equivalence once, then compose with the raw product-owner
  -- adapter instead of bundling a separate product projective owner.
  exact ⟨eK.trans eprod⟩

/-- Helper for Proposition 15-15.5-1: the scalar extension of the exact lattice owner is
isomorphic to the product of the lifted summands upstairs. -/
private theorem stableLattice_exact_owner_scalarExtension_to_product_iso_local
    (X : FDRep K G)
    (L : StableLattice A X.ρ)
    (QU QV : FiniteProjectiveGroupAlgebraModule A G)
    (hA : Nonempty (L.toSubmodule ≃ₗ[A[G]] (QU.V × QV.V))) :
    Nonempty (FDRep.of (Representation.scalarExtension L.toRepresentation) ≅
      FDRep.of (Representation.prod (QU.scalarExtension K).ρ (QV.scalarExtension K).ρ)) := by
  let ρL : Representation K G (K ⊗[A] L.toSubmodule) :=
    Representation.scalarExtension L.toRepresentation
  let ρprod : Representation K G ((K ⊗[A] QU.V) × (K ⊗[A] QV.V)) :=
    Representation.prod (QU.scalarExtension K).ρ (QV.scalarExtension K).ρ
  rcases
      scalarExtension_exact_owner_asModule_linearEquiv_local
        (A := A) (K := K) (G := G) X L with
    ⟨eOwnerL⟩
  rcases
      reflected_exact_owner_scalarExtension_to_prod_asModule_linearEquiv_local
        (A := A) (K := K) (G := G) X L QU QV hA with
    ⟨hKprod⟩
  -- Compare the explicit scalar-extension owner of `L` with the product owner obtained from the
  -- reflected split, then package that owner comparison as an `FDRep` isomorphism.
  exact
    fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv_field_local
      (σ := FDRep.of (Representation.scalarExtension L.toRepresentation))
      (τ := FDRep.of
        (Representation.prod (QU.scalarExtension K).ρ (QV.scalarExtension K).ρ))
      (G := G) ⟨eOwnerL.trans hKprod⟩

/-- Helper for Proposition 15-15.5-1: a reduced product split reflects directly to an exact-owner
`A[G]`-linear equivalence when `p ∤ |G|`. -/
-- Route correction: apply Chapter `14`'s projective reflection theorem to the actual product owner
-- `QU.V × QV.V`, rather than trying to rebundle that owner as a second stable lattice.
private theorem StableLattice.reduction_split_reflects_exact_owner_product_linearEquiv_of_order_prime_to_p_local
    (hG : ¬ p ∣ Nat.card G)
    {X : FDRep K G}
    (L : StableLattice A X.ρ)
    (QU QV : FiniteProjectiveGroupAlgebraModule A G)
    (hred : Nonempty (L.reduction ≃ₗ[k[G]] k ⊗[A] (QU.V × QV.V))) :
    Nonempty (L.toSubmodule ≃ₗ[A[G]] (QU.V × QV.V)) := by
  let _ : Module.Free A L.toSubmodule := by
    infer_instance
  have hprojL : Module.Projective A[G] L.toSubmodule := by
    -- Serre's averaging argument packages the exact lattice owner as projective over `A[G]`.
    exact
      free_groupAlgebra_module_projective_of_order_prime_to_p
        (A := A) (G := G) (p := p) (P := L.toSubmodule) hG
  have hprojProd : Module.Projective A[G] (QU.V × QV.V) := by
    -- The product owner remains projective because both lifted summands already are.
    infer_instance
  -- Reflect the reduced product equivalence through the canonical residue-field reductions on the
  -- two exact owners.
  exact
    (projective_monoidAlgebra_nonempty_linearEquiv_iff_of_isResidueFieldReduction
      (Λ := A) (G := G)
      (P := L.toSubmodule)
      (Pbar := L.reduction)
      (f := (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction))
      (hf := StableLattice.reduction_mkQ_isResidueFieldReduction_local
        (A := A) (K := K) (G := G) L)
      (P' := QU.V × QV.V)
      (Pbar' := k ⊗[A] (QU.V × QV.V))
      (f' := (TensorProduct.mk A k (QU.V × QV.V) 1 :
        (QU.V × QV.V) →ₗ[A] k ⊗[A] (QU.V × QV.V)))
      (hf' := MonoidAlgebra.tensorProduct_mk_isResidueFieldReduction
        (Λ := A) (G := G) (P := QU.V × QV.V))
      hprojL hprojProd).2 hred

/-- Helper for Proposition 15-15.5-1: nontriviality of a residue-field tensor factor already
forces nontriviality after scalar extension to the fraction field. -/
private theorem nontrivial_scalar_extension_of_nontrivial_reduction_factor_local
    {P : Type v} [AddCommGroup P] [Module A P] [Module.Free A P]
    (hred : Nontrivial (k ⊗[A] P)) :
    Nontrivial (K ⊗[A] P) := by
  have hP : Nontrivial P := by
    by_contra hP
    let _ : Subsingleton P := not_nontrivial_iff_subsingleton.mp hP
    -- If the exact owner collapsed to a singleton, so would its reduction tensor.
    exact
      (not_nontrivial_iff_subsingleton.mpr
        (inferInstance : Subsingleton (k ⊗[A] P))) hred
  let _ : Nontrivial P := hP
  -- Once the exact owner is nontrivial, the fraction-field tensor stays nontrivial by
  -- injectivity of `x ↦ 1 ⊗ x` on free modules.
  exact tensorProduct_nontrivial_of_free_local (A := A) (K := K) (P := P)

-- Helper for Proposition 15-15.5-1: the reduction of a stable lattice in a simple
-- `K[G]`-representation should again be simple when `p ∤ |G|`.
-- Route correction: the source proof reflects a nontrivial reduced splitting back to the generic
-- fiber via the exact-owner projective package on `L.toSubmodule`; that reflection step is the
-- only remaining blocker here.
/-- Helper for Proposition 15-15.5-1: core split-reflection package for the exact-owner route. -/
private theorem stableLattice_reduction_split_reflects_generic_nonsimple_of_order_prime_to_p_core
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hG : ¬ p ∣ Nat.card G)
    (X : FDRep K G) [Simple X]
    (L : StableLattice A X.ρ)
    (U V : Subrepresentation L.reductionRepresentation)
    (hUV : IsCompl U V) (hU : U ≠ ⊥) (hV : V ≠ ⊥) :
    False := by
  obtain ⟨QU, QV, hQU, hQV, hred⟩ :=
    reduction_split_to_lifted_product_linearEquiv_local
      (A := A) (K := K) (G := G) (p := p) X hG L U V hUV
  rcases hQU with ⟨eQU⟩
  rcases hQV with ⟨eQV⟩
  have hA :
      Nonempty (L.toSubmodule ≃ₗ[A[G]] (QU.V × QV.V)) :=
    StableLattice.reduction_split_reflects_exact_owner_product_linearEquiv_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p) hG L QU QV hred
  let ρprod : Representation K G ((K ⊗[A] QU.V) × (K ⊗[A] QV.V)) :=
    Representation.prod (QU.scalarExtension K).ρ (QV.scalarExtension K).ρ
  rcases
      StableLattice.scalarExtension_exact_owner_fdrep_iso_local_support
        (A := A) (K := K) (G := G) (X := X) (L := L) with
    ⟨eLX⟩
  rcases
      stableLattice_exact_owner_scalarExtension_to_product_iso_local
        (A := A) (K := K) (G := G) X L QU QV hA with
    ⟨eProd⟩
  let eXProd : X ≅ FDRep.of ρprod := eLX.symm.trans eProd
  let eRep : Representation.Equiv X.ρ ρprod :=
    Representation.equivOfIso ((forget₂ (FDRep K G) (Rep K G)).mapIso eXProd)
  let _ : Representation.IsIrreducible X.ρ := FDRep.isIrreducible_of_simple X
  let _ : Representation.IsIrreducible ρprod :=
    isIrreducible_of_equiv_local (G := G) (ρ := X.ρ) (σ := ρprod) eRep
  have hU_sub : U.toSubmodule ≠ ⊥ := by
    intro hU_sub
    apply hU
    apply Subrepresentation.toSubmodule_injective
    simpa using hU_sub
  have hV_sub : V.toSubmodule ≠ ⊥ := by
    intro hV_sub
    apply hV
    apply Subrepresentation.toSubmodule_injective
    simpa using hV_sub
  let _ : Nontrivial (asModule U.toRepresentation) := by
    change Nontrivial U.toSubmodule
    exact Submodule.nontrivial_iff_ne_bot.mpr hU_sub
  let _ : Nontrivial (asModule V.toRepresentation) := by
    change Nontrivial V.toSubmodule
    exact Submodule.nontrivial_iff_ne_bot.mpr hV_sub
  have hQUred_nontrivial : Nontrivial (k ⊗[A] QU.V) := by
    -- The nonzero reduced factor transfers across the chosen exact-owner identification.
    obtain ⟨x, hx⟩ := exists_ne (0 : asModule U.toRepresentation)
    refine ⟨eQU.symm x, 0, ?_⟩
    intro hzero
    apply hx
    simpa using congrArg eQU hzero
  have hQVred_nontrivial : Nontrivial (k ⊗[A] QV.V) := by
    -- The same transfer works for the complementary reduced factor.
    obtain ⟨x, hx⟩ := exists_ne (0 : asModule V.toRepresentation)
    refine ⟨eQV.symm x, 0, ?_⟩
    intro hzero
    apply hx
    simpa using congrArg eQV hzero
  let _ : Module.Free A QU.V := FiniteProjectiveGroupAlgebraModule.free (A := A) (G := G) QU
  let _ : Module.Free A QV.V := FiniteProjectiveGroupAlgebraModule.free (A := A) (G := G) QV
  let _ : Nontrivial (K ⊗[A] QU.V) :=
    nontrivial_scalar_extension_of_nontrivial_reduction_factor_local
      (A := A) (K := K) (P := QU.V) hQUred_nontrivial
  let _ : Nontrivial (K ⊗[A] QV.V) :=
    nontrivial_scalar_extension_of_nontrivial_reduction_factor_local
      (A := A) (K := K) (P := QV.V) hQVred_nontrivial
  have hprod_not_irreducible : ¬ ρprod.IsIrreducible := by
    -- A genuine product of two nonzero factors cannot stay irreducible upstairs.
    simpa [ρprod] using
      (prod_representation_not_isIrreducible_of_nontrivial_local
        (G := G) (F := K) (ρ := (QU.scalarExtension K).ρ) (σ := (QV.scalarExtension K).ρ))
  exact hprod_not_irreducible inferInstance

/-- Helper for Proposition 15-15.5-1: a nontrivial complemented split of the reduction of a stable
lattice should contradict simplicity of the generic fiber. -/
private theorem stableLattice_reduction_split_reflects_generic_nonsimple_of_order_prime_to_p
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hG : ¬ p ∣ Nat.card G)
    (X : FDRep K G) [Simple X]
    (L : StableLattice A X.ρ)
    (U V : Subrepresentation L.reductionRepresentation)
    (hUV : IsCompl U V) (hU : U ≠ ⊥) (hV : V ≠ ⊥) :
    False := by
  exact
    stableLattice_reduction_split_reflects_generic_nonsimple_of_order_prime_to_p_core
      (A := A) (K := K) (G := G) (p := p) hG X L U V hUV hU hV

/-- Helper for Proposition 15-15.5-1: under Maschke's prime-to-`p` hypothesis, every reduced
subrepresentation has a complementary reduced subrepresentation. -/
private theorem stableLattice_reduction_exists_isCompl_of_order_prime_to_p
    (hG : ¬ p ∣ Nat.card G)
    (X : FDRep K G)
    (L : StableLattice A X.ρ)
    (U : Subrepresentation L.reductionRepresentation) :
    ∃ V : Subrepresentation L.reductionRepresentation, IsCompl U V := by
  let _ : NeZero (Nat.card G : k) := NeZero.of_not_dvd k hG
  let _ : IsSemisimpleRepresentation L.reductionRepresentation := by
    infer_instance
  -- Maschke makes the reduced representation semisimple, so complements already exist downstairs.
  simpa using exists_isCompl U

/-- Helper for Proposition 15-15.5-1: if a complement of a reduced subrepresentation is zero, then
the original subrepresentation is all of the reduction. -/
private theorem subrepresentation_eq_top_of_isCompl_right_eq_bot
    {F : Type u} [Field F]
    {V : Type v} [AddCommGroup V] [Module F V]
    {ρ : Representation F G V}
    {U V' : Subrepresentation ρ}
    (hUV : IsCompl U V') (hV : V' = ⊥) :
    U = ⊤ := by
  rw [hV] at hUV
  -- Once the complementary summand vanishes, codisjointness forces the remaining summand to be
  -- the whole representation.
  simpa [codisjoint_iff] using hUV.codisjoint

/-- Helper for Proposition 15-15.5-1: the reduction of a stable lattice in a simple generic
representation is irreducible under the prime-to-`p` hypothesis. -/
private theorem stableLattice_reduction_isIrreducible_of_order_prime_to_p
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hG : ¬ p ∣ Nat.card G)
    (X : FDRep K G) [Simple X]
    (L : StableLattice A X.ρ) :
    L.reductionRepresentation.IsIrreducible := by
  let _ : Representation.IsIrreducible X.ρ := FDRep.isIrreducible_of_simple X
  let _ : Nontrivial X.V := by
    by_contra hXV
    let _ : Subsingleton X.V := not_nontrivial_iff_subsingleton.mp hXV
    exact (show (⊥ : Subrepresentation X.ρ) ≠ ⊤ from IsSimpleOrder.bot_ne_top) <| by
      apply Subrepresentation.toSubmodule_injective
      ext x
      constructor
      · intro _
        trivial
      · intro _
        simpa using (show x = 0 from Subsingleton.elim x 0)
  let _ : Nontrivial L.reduction :=
    StableLattice.reduction_nontrivial_monoid (A := A) (K := K) L
  let _ : Nontrivial (Subrepresentation L.reductionRepresentation) :=
    ⟨⊥, ⊤, fun h ↦
      bot_ne_top <| by simpa using congrArg Subrepresentation.toSubmodule h⟩
  refine IsSimpleOrder.of_forall_eq_top fun U hU ↦ ?_
  obtain ⟨V, hUV⟩ :=
    stableLattice_reduction_exists_isCompl_of_order_prime_to_p
      (A := A) (K := K) (G := G) (p := p) hG X L U
  by_cases hV : V = ⊥
  · -- If the complement vanishes, the original subrepresentation is the whole reduction.
    exact subrepresentation_eq_top_of_isCompl_right_eq_bot hUV hV
  · -- Otherwise the nontrivial split contradicts the simplicity of the generic fiber.
    exact False.elim <|
      stableLattice_reduction_split_reflects_generic_nonsimple_of_order_prime_to_p
        (A := A) (K := K) (G := G) (p := p) hG X L U V hUV hU hV

private theorem stableLattice_reduction_simple_of_order_prime_to_p
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hG : ¬ p ∣ Nat.card G)
    (X : FDRep K G) [Simple X]
    (L : StableLattice A X.ρ) :
    Simple (FDRep.of L.reductionRepresentation) := by
  letI : L.reductionRepresentation.IsIrreducible :=
    stableLattice_reduction_isIrreducible_of_order_prime_to_p
      (A := A) (K := K) (G := G) (p := p) hG X L
  letI : Representation.IsIrreducible (FDRep.of L.reductionRepresentation).ρ := by
    simpa using (inferInstance : L.reductionRepresentation.IsIrreducible)
  -- Once irreducibility of the reduced representation is isolated, the bundled `FDRep` simplicity
  -- statement is the standard Chapter `2` wrapper.
  exact FDRep.simple_of_isIrreducible (FDRep.of L.reductionRepresentation)

/-- Helper for Proposition 15-15.5-1: in a complete simple generic family, Serre's reduction
argument makes every chosen reduction simple. -/
theorem stableLattice_reductionFamily_isSimple_of_order_prime_to_p
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ) :
    ∀ i, Simple (FDRep.of (L i).reductionRepresentation) := by
  intro i
  -- Each generic family member is simple by completeness, so the pointwise reduction lemma applies
  -- directly to Serre's chosen stable lattice in that member.
  letI : Simple (πK i) := hπK_complete.isSimple i
  exact
    stableLattice_reduction_simple_of_order_prime_to_p
      (A := A) (K := K) (G := G) (p := p) hG (πK i) (L i)

/-- Helper for Proposition 15-15.5-1: Serre's projective-envelope inverse map already proves the
existence clause for the reduced family attached to a complete simple `K[G]`-family. -/
-- Proof sketch: lift the simple `k[G]`-representation through a projective envelope over `A[G]`,
-- show the scalar extension of that lift is simple, then use completeness of `πK` and compare
-- Grothendieck classes via `decompositionHom`.
private theorem stableLattice_reductionFamily_exists_iso_of_order_prime_to_p
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ)
    {τ : FDRep k G} [Simple τ] :
    ∃ i, Nonempty (τ ≅ FDRep.of (L i).reductionRepresentation) := by
  classical
  let πk : S → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation
  letI : Representation.IsIrreducible τ.ρ := FDRep.isIrreducible_of_simple τ
  obtain ⟨Q, hQτ⟩ :=
    exists_projective_lift_reducing_to_simple_of_order_prime_to_p
      (A := A) (G := G) (p := p) hG τ
  have hQsimple : Simple (Q.scalarExtension K) :=
    projective_lift_scalarExtension_simple_of_order_prime_to_p
      (A := A) (K := K) (G := G) (p := p) hG τ Q hQτ
  letI : Simple (Q.scalarExtension K) := hQsimple
  letI : Representation.IsIrreducible (Q.scalarExtension K).ρ := by
    simpa using FDRep.isIrreducible_of_simple (Q.scalarExtension K)
  obtain ⟨i, hi⟩ :=
    IsCompleteIrreducibleFamily.exists_iso_of_representation
      (π := πK) hπK_complete (τ := (Q.scalarExtension K).ρ) inferInstance
  refine ⟨i, ?_⟩
  have hQiso : Nonempty (Q.scalarExtension K ≅ πK i) := by
    simpa using hi
  have hclassτ :
      [τ]₀ = decompositionHom A K G [Q.scalarExtension K]₀ := by
    -- Serre's projective-lift identity computes the reduction class of `Q` directly as `[τ]₀`.
    simpa using
      (decompositionHom_projective_scalarExtension_class_eq_iso_target_local
        (A := A) (K := K) (G := G) Q hQτ).symm
  have hclassi :
      decompositionHom A K G [Q.scalarExtension K]₀ = [πk i]₀ := by
    -- Completeness picks out one member of `πK`; its chosen lattice computes the same
    -- decomposition class as the lifted projective envelope.
    calc
      decompositionHom A K G [Q.scalarExtension K]₀ =
          decompositionHom A K G [πK i]₀ := by
            rw [finiteRepGrothendieckClass_eq_of_nonempty_iso (L := K) (G := G) hQiso]
      _ = [πk i]₀ := by
            simpa [πk] using
              decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) (πK i) (L i)
  have hclass : [τ]₀ = [πk i]₀ := hclassτ.trans hclassi
  let _ : NeZero (Nat.card G : k) := NeZero.of_not_dvd k hG
  have hsemiτ : IsSemisimpleRepresentation τ.ρ := by
    infer_instance
  have hsemii : IsSemisimpleRepresentation (πk i).ρ := by
    infer_instance
  exact
    (finiteRepGrothendieckClass_eq_iff_nonempty_iso_of_isSemisimple hsemiτ hsemii).mp hclass

/-- Helper for Proposition 15-15.5-1: once the reductions `FDRep.of (L i).reductionRepresentation`
are known to be simple, Serre's projective-envelope inverse map already supplies the completeness
of the reduced family. -/
theorem stableLattice_reductionFamily_complete_of_isSimple_of_order_prime_to_p
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (hsimple : ∀ i, Simple (FDRep.of (L i).reductionRepresentation)) :
    let πk : S → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation
    IsCompleteIrreducibleFamily πk := by
  classical
  let πk : S → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation
  refine
    { isSimple := ?_
      exists_iso := ?_ }
  · intro i
    simpa [πk] using hsimple i
  · intro τ hτ
    letI : Simple τ := hτ
    -- Serre's lifted-projective-envelope argument already provides the completeness clause.
    exact
      stableLattice_reductionFamily_exists_iso_of_order_prime_to_p
        (A := A) (K := K) (G := G) (p := p) hG πK hπK_complete L
end DecompositionHom
