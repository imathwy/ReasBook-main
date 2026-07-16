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
import LinearRepresentations_Serre_1977.Serre.Chap15.Proposition_15_15_5_1.ReductionMkQ
import LinearRepresentations_Serre_1977.Serre.Chap15.Proposition_15_15_5_1.StableLatticeExactOwner
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

/-- Helper for Proposition 15-15.5-1: once an isomorphism of reductions reflects to an
isomorphism of the generic fibers, pairwise nonisomorphism of the reduced family follows
immediately. -/
theorem stableLattice_reductionFamily_pairwise_of_iso_reflection
    {S : Type v}
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (hreflect :
      ∀ {i j : S},
        Nonempty (FDRep.of (L i).reductionRepresentation ≅
          FDRep.of (L j).reductionRepresentation) →
        Nonempty (πK i ≅ πK j)) :
    let πk : S → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation
    PairwiseNonisomorphic πk := by
  dsimp
  intro i j hij hijred
  -- Any isomorphism between the chosen reductions would lift back upstairs, contradicting the
  -- pairwise nonisomorphism of the simple generic family.
  exact hπK_pairwise hij (hreflect hijred)

/-- Helper for Proposition 15-15.5-1: the tautological `F[G]`-module attached to a
representation is canonically linear-equivalent to its carrier. -/
theorem nonempty_asModuleLinearEquiv_target_field_local
    {F : Type u} [Field F]
    {V : Type v} [AddCommGroup V] [Module F V]
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

/-- Helper for Proposition 15-15.5-1: a `K[G]`-linear equivalence of owner modules upgrades to an
isomorphism in `FDRep K G`. -/
theorem fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv_field_local
    {σ τ : FDRep K G}
    (hστ : Nonempty (asModule σ.ρ ≃ₗ[K[G]] asModule τ.ρ)) :
    Nonempty (σ ≅ τ) := by
  exact
    Representation.fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv_field_local_support
      (K := K) (G := G) hστ

/-- Helper for Proposition 15-15.5-1: scalar extension transports an exact-owner
`A[G]`-linear equivalence to the corresponding `K[G]`-linear equivalence on the generic fibers. -/
theorem scalarExtension_nonempty_linearEquiv_of_nonempty_linearEquiv_local
    {P Q : Type v} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup Q] [Module A Q] [Module A[G] Q] [IsScalarTower A A[G] Q]
    (hPQ : Nonempty (P ≃ₗ[A[G]] Q)) :
    Nonempty ((K ⊗[A] P) ≃ₗ[K[G]] (K ⊗[A] Q)) := by
  rcases hPQ with ⟨e⟩
  let e₀ : (K ⊗[A] P) ≃ₗ[K] (K ⊗[A] Q) :=
    LinearEquiv.baseChange A K P Q (LinearEquiv.restrictScalars A e)
  refine ⟨
    { toFun := e₀
      invFun := e₀.symm
      left_inv := e₀.left_inv
      right_inv := e₀.right_inv
      map_add' := e₀.map_add
      map_smul' := ?_ }⟩
  intro a x
  -- Extend the `MonoidAlgebra.of` computation from pure tensors to all scalars in `K[G]`.
  refine MonoidAlgebra.induction_on
    (p := fun b : K[G] => e₀ (b • x) = b • e₀ x) a ?_ ?_ ?_
  · intro g
    induction x using TensorProduct.induction_on with
    | zero =>
        simp [e₀]
    | tmul c p =>
        have hq :
            MonoidAlgebra.of K G g • (c ⊗ₜ[A] e p : K ⊗[A] Q) =
              (c ⊗ₜ[A] (MonoidAlgebra.of A G g • e p) : K ⊗[A] Q) := by
          simpa using
            monoidAlgebra_of_smul_tmul (Λ := A) (κ := K) (G := G) (P := Q) g c (e p)
        have hp :
            MonoidAlgebra.of K G g • (c ⊗ₜ[A] p : K ⊗[A] P) =
              (c ⊗ₜ[A] (MonoidAlgebra.of A G g • p) : K ⊗[A] P) := by
          simpa using
            monoidAlgebra_of_smul_tmul (Λ := A) (κ := K) (G := G) (P := P) g c p
        calc
          e₀ (MonoidAlgebra.of K G g • (c ⊗ₜ[A] p : K ⊗[A] P))
              = e₀ (c ⊗ₜ[A] (MonoidAlgebra.of A G g • p) : K ⊗[A] P) := by
                  rw [hp]
          _ = (c ⊗ₜ[A] e (MonoidAlgebra.of A G g • p) : K ⊗[A] Q) := by
                simp [e₀, LinearEquiv.baseChange_tmul]
          _ = (c ⊗ₜ[A] (MonoidAlgebra.of A G g • e p) : K ⊗[A] Q) := by
                rw [e.map_smul]
          _ = MonoidAlgebra.of K G g • e₀ (c ⊗ₜ[A] p : K ⊗[A] P) := by
                rw [← hq]
                simp [e₀, LinearEquiv.baseChange_tmul]
    | add y z hy hz =>
        calc
          e₀ (MonoidAlgebra.of K G g • (y + z))
              = e₀ (MonoidAlgebra.of K G g • y) + e₀ (MonoidAlgebra.of K G g • z) := by
                  rw [smul_add, map_add]
          _ = MonoidAlgebra.of K G g • e₀ y + MonoidAlgebra.of K G g • e₀ z := by
                rw [hy, hz]
          _ = MonoidAlgebra.of K G g • e₀ (y + z) := by
                simp [smul_add, e₀.map_add]
  · intro a b ha hb
    simp [ha, hb, add_smul]
  · intro c b hb
    calc
      e₀ ((c • b) • x) = e₀ (c • (b • x)) := by simp [smul_smul]
      _ = c • e₀ (b • x) := by simp
      _ = c • (b • e₀ x) := by rw [hb]
      _ = (c • b) • e₀ x := by simp [smul_smul]

/-- Helper for Proposition 15-15.5-1: an isomorphism between the chosen reductions should
reflect to an isomorphism between the generic fibers when `p ∤ |G|`. -/
-- Route correction: Serre's injectivity step should stay on the exact owners `L.toSubmodule`;
-- once the reduction isomorphism reflects there, scalar extension and the support-file exact-owner
-- identifications transport it back to the original generic fibers.
theorem stableLattice_reduction_iso_implies_generic_iso_of_order_prime_to_p
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (L : ∀ i, StableLattice A (πK i).ρ)
    {i j : S}
    (hij :
      Nonempty (FDRep.of (L i).reductionRepresentation ≅
        FDRep.of (L j).reductionRepresentation)) :
    Nonempty (πK i ≅ πK j) := by
  have hOwner :
      Nonempty ((L i).toSubmodule ≃ₗ[A[G]] (L j).toSubmodule) :=
    StableLattice.reduction_iso_reflects_exact_owner_linearEquiv_of_order_prime_to_p
      (A := A) (K := K) (G := G) (p := p) hG (L i) (L j) hij
  have hOwnerK :
      Nonempty ((K ⊗[A] (L i).toSubmodule) ≃ₗ[K[G]] (K ⊗[A] (L j).toSubmodule)) :=
    scalarExtension_nonempty_linearEquiv_of_nonempty_linearEquiv_local
      (A := A) (K := K) (G := G) hOwner
  have hi_owner :
      Nonempty
        (asModule
            (show Representation K G (K ⊗[A] (L i).toSubmodule) from
              Representation.scalarExtension (L i).toRepresentation) ≃ₗ[K[G]]
          (K ⊗[A] (L i).toSubmodule)) :=
    StableLattice.scalarExtension_exact_owner_asModule_linearEquiv_local_support
      (A := A) (K := K) (G := G) (L i)
  have hj_owner :
      Nonempty
        (asModule
            (show Representation K G (K ⊗[A] (L j).toSubmodule) from
              Representation.scalarExtension (L j).toRepresentation) ≃ₗ[K[G]]
          (K ⊗[A] (L j).toSubmodule)) :=
    StableLattice.scalarExtension_exact_owner_asModule_linearEquiv_local_support
      (A := A) (K := K) (G := G) (L j)
  have hExact :
      Nonempty
        (FDRep.of
            (show Representation K G (K ⊗[A] (L i).toSubmodule) from
              Representation.scalarExtension (L i).toRepresentation) ≅
          FDRep.of
            (show Representation K G (K ⊗[A] (L j).toSubmodule) from
              Representation.scalarExtension (L j).toRepresentation)) := by
    rcases hi_owner with ⟨ei⟩
    rcases hOwnerK with ⟨eij⟩
    rcases hj_owner with ⟨ej⟩
    -- Compare the two exact-owner scalar extensions through the transported tensor-owner
    -- equivalence.
    exact
      fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv_field_local
        (σ := FDRep.of
          (show Representation K G (K ⊗[A] (L i).toSubmodule) from
            Representation.scalarExtension (L i).toRepresentation))
        (τ := FDRep.of
          (show Representation K G (K ⊗[A] (L j).toSubmodule) from
            Representation.scalarExtension (L j).toRepresentation))
        (G := G)
        ⟨by simpa using ei.trans (eij.trans ej.symm)⟩
  rcases StableLattice.scalarExtension_exact_owner_fdrep_iso_local_support
      (A := A) (K := K) (G := G) (X := πK i) (L := L i) with
    ⟨ei⟩
  rcases hExact with ⟨eExact⟩
  rcases StableLattice.scalarExtension_exact_owner_fdrep_iso_local_support
      (A := A) (K := K) (G := G) (X := πK j) (L := L j) with
    ⟨ej⟩
  -- Reflect the reduced isomorphism to the exact owners, scalar-extend, and then identify those
  -- exact-owner scalar extensions with the original generic fibers.
  exact ⟨ei.symm.trans (eExact.trans ej)⟩
end DecompositionHom
