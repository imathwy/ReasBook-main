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
import LinearRepresentations_Serre_1977.Serre.Chap15.Proposition_15_15_5_1.ProjectiveLiteralLifts
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

/-- Helper for Proposition 15-15.5-1: the restricted `A`-action on a rebundled `FDRep` carrier
forms the expected scalar tower over `K`. -/
private theorem fdRep_compHom_isScalarTower_local
    (V : FDRep K G) :
    letI : Module A V.V := Module.compHom V.V (algebraMap A K)
    IsScalarTower A K V.V := by
  letI : Module A V.V := Module.compHom V.V (algebraMap A K)
  -- The `A`-action is obtained by restricting scalars through `A → K`, so the tower relation is
  -- exactly the `compHom` scalar action.
  refine IsScalarTower.of_algebraMap_smul ?_
  intro a x
  show ((algebraMap A K a) • x : V.V) =
    @SMul.smul A V.V (Module.compHom V.V (algebraMap A K)).toSMul a x
  rfl

/-- Helper for Proposition 15-15.5-1: the literal tensor-product `A`-action on
`Q.scalarExtension K` forms the ambient scalar tower over `K`. -/
private theorem projective_scalarExtension_tensor_left_isScalarTower_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let V : FDRep K G := Q.scalarExtension K
    IsScalarTower A K V.V := by
  let V : FDRep K G := Q.scalarExtension K
  -- The source-faithful literal lattice lives on the tensor-product owner, so verify the scalar
  -- tower directly on pure tensors for that owner.
  refine IsScalarTower.of_algebraMap_smul fun a x ↦ ?_
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro z y
    simp [Algebra.smul_def, TensorProduct.smul_tmul']
  · intro x₁ x₂ hx₁ hx₂
    rw [smul_add, smul_add, hx₁, hx₂]

/-- Helper for Proposition 15-15.5-1: rebundling an `FDRep` from its underlying representation
does not change its isomorphism class. -/
private noncomputable def fdRepIsoOfRho_local
    (τ : FDRep K G) : τ ≅ FDRep.of τ.ρ :=
  Action.mkIso (Iso.refl _) fun g ↦ by
    -- Rebundling preserves the carrier and the action pointwise.
    ext x
    rfl

/-- Helper for Proposition 15-15.5-1: rebundling `Q.scalarExtension K` as `FDRep.of` does not
change its generic Grothendieck class. -/
private theorem finiteRepClass_projective_scalarExtension_eq_fdrepOfRho_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    [Q.scalarExtension K]₀ = [FDRep.of (Q.scalarExtension K).ρ]₀ := by
  -- The scalar-extended representation and its `FDRep.of` rebundling are canonically isomorphic.
  rw [finiteRepGrothendieckClass_eq_of_nonempty_iso
    (L := K) (G := G) ⟨fdRepIsoOfRho_local (τ := Q.scalarExtension K)⟩]

/-- Helper for Proposition 15-15.5-1: the decomposition class of `Q.scalarExtension K` is
unchanged after rebundling through `FDRep.of`. -/
private theorem decompositionHom_projective_scalarExtension_class_eq_fdrepOfRho_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    decompositionHom A K G [Q.scalarExtension K]₀ =
      decompositionHom A K G [FDRep.of (Q.scalarExtension K).ρ]₀ := by
  -- `decompositionHom` sees only the Grothendieck class, and the rebundled class is equal.
  rw [finiteRepClass_projective_scalarExtension_eq_fdrepOfRho_local
    (A := A) (K := K) (G := G) Q]

/-- Helper for Proposition 15-15.5-1: the literal map `x ↦ 1 ⊗ x` with the exact
restrict-scalars owner used by `FDRep.of (Q.scalarExtension K).ρ`. -/
private noncomputable def projective_scalarExtension_literal_map_fdrep_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
    let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
    letI : SMul A V.V := instMod.toSMul
    letI : Module A V.V := instMod
    letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
      change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
      rfl
    Q.V →ₗ[A] V.V := by
  let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
  let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
  letI : SMul A V.V := instMod.toSMul
  letI : Module A V.V := instMod
  letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
    change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
    rfl
  exact
    { toFun := fun x => (TensorProduct.mk A K Q.V 1 x : V.V)
      map_add' := by
        intro x y
        simp [TensorProduct.tmul_add]
      map_smul' := by
        intro a x
        change
          (TensorProduct.mk A K Q.V 1 (a • x) : V.V) =
            @SMul.smul A V.V instMod.toSMul a
              (TensorProduct.mk A K Q.V 1 x : V.V)
        change
          (TensorProduct.mk A K Q.V 1 (a • x) : K ⊗[A] Q.V) =
            (algebraMap A K a) • (TensorProduct.mk A K Q.V 1 x : K ⊗[A] Q.V)
        calc
          (TensorProduct.mk A K Q.V 1 (a • x) : K ⊗[A] Q.V) =
              TensorProduct.mk A K Q.V (a • (1 : K)) x := by
                exact TensorProduct.tmul_smul (R := A) (M := K) (N := Q.V) a (1 : K) x
          _ = (algebraMap A K a) •
              (TensorProduct.mk A K Q.V 1 x : K ⊗[A] Q.V) := by
                symm
                calc
                  (algebraMap A K a) •
                      (TensorProduct.mk A K Q.V 1 x : K ⊗[A] Q.V) =
                      TensorProduct.mk A K Q.V ((algebraMap A K a) • (1 : K)) x := by
                        exact TensorProduct.smul_tmul' (algebraMap A K a) (1 : K) x
                  _ = TensorProduct.mk A K Q.V (a • (1 : K)) x := by
                        congr 1
                        simp [Algebra.smul_def] }

/-- Helper for Proposition 15-15.5-1: rebuild Serre's literal range lattice on the explicit
`FDRep.of (Q.scalarExtension K).ρ` owner used by `decompositionHom`. -/
private noncomputable def projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
    let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
    letI : SMul A V.V := instMod.toSMul
    letI : Module A V.V := instMod
    letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
      change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
      rfl
    StableLattice A V.ρ := by
  let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
  let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
  letI : SMul A V.V := instMod.toSMul
  letI : Module A V.V := instMod
  letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
    change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
    rfl
  let f :=
    projective_scalarExtension_literal_map_fdrep_owner_local
      (A := A) (K := K) (G := G) Q
  refine
    { toSubmodule := f.range
      apply_mem_toSubmodule := ?_
      isLattice := ?_ }
  · intro g x hx
    rcases hx with ⟨y, rfl⟩
    refine ⟨MonoidAlgebra.of A G g • y, ?_⟩
    let ρK : Representation K G (K ⊗[A] Q.V) :=
      Representation.scalarExtension (Representation.ofModule' Q.V)
    have hsingle :=
      Representation.single_smul (ρ := ρK) (t := (1 : K)) (g := g)
        (v := TensorProduct.mk A K Q.V 1 y)
    have haction :
        MonoidAlgebra.of K G g • (TensorProduct.mk A K Q.V 1 y) =
          ρK g (TensorProduct.mk A K Q.V 1 y) := by
      simpa [ρK, MonoidAlgebra.of_apply] using hsingle
    change
      (TensorProduct.mk A K Q.V 1 ((MonoidAlgebra.of A G g) • y) : V.V) =
        (Q.scalarExtension K).ρ g (TensorProduct.mk A K Q.V 1 y)
    exact
      (monoidAlgebra_of_smul_tmul (Λ := A) (P := Q.V) (κ := K) g (1 : K) y).symm.trans
        haction
  · refine
      { fg := ?_
        span_eq_top := ?_ }
    · have hfg_top : (⊤ : Submodule A Q.V).FG := by
        exact (Module.Finite.iff_fg (N := (⊤ : Submodule A Q.V))).1 inferInstance
      rw [LinearMap.range_eq_map]
      exact Submodule.FG.map f hfg_top
    · let _ : Module.Free A Q.V := Q.free
      let b := Module.Free.chooseBasis A Q.V
      apply eq_top_iff.2
      intro x hx
      have hxrepr :
          x = ∑ i, ((Algebra.TensorProduct.basis K b).repr x) i •
            (Algebra.TensorProduct.basis K b) i := by
        simpa using ((Algebra.TensorProduct.basis K b).sum_repr x).symm
      rw [hxrepr]
      refine Submodule.sum_mem _ ?_
      intro i hi
      have hi' :
          (Algebra.TensorProduct.basis K b) i ∈
            Submodule.span K ((f.range : Submodule A V.V) : Set V.V) := by
        apply Submodule.subset_span
        refine ⟨b i, ?_⟩
        rw [Algebra.TensorProduct.basis_apply (A := K) (b := b) i]
        rfl
      exact Submodule.smul_mem _ _ hi'

/-- Helper for Proposition 15-15.5-1: the exact-owner literal map remains injective. -/
private theorem projective_scalarExtension_literal_map_fdrep_owner_injective_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
    let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
    letI : SMul A V.V := instMod.toSMul
    letI : Module A V.V := instMod
    letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
      change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
      rfl
    Function.Injective
      (projective_scalarExtension_literal_map_fdrep_owner_local
        (A := A) (K := K) (G := G) Q) := by
  let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
  let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
  letI : SMul A V.V := instMod.toSMul
  letI : Module A V.V := instMod
  letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
    change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
    rfl
  intro x y hxy
  apply
    projective_scalarExtension_literal_map_injective_local_support
      (A := A) (K := K) (G := G) Q

/-- Helper for Proposition 15-15.5-1: restrict the exact-owner literal map to its range. -/
private noncomputable def
    projective_scalarExtension_literal_rangeRestrictLinearMap_fdrep_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
    let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
    letI : SMul A V.V := instMod.toSMul
    letI : Module A V.V := instMod
    letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
      change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
      rfl
    let L : StableLattice A V.ρ :=
      projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local
        (A := A) (K := K) (G := G) Q
    Q.V →ₗ[A] L.toSubmodule := by
  let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
  let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
  letI : SMul A V.V := instMod.toSMul
  letI : Module A V.V := instMod
  letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
    change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
    rfl
  let f :=
    projective_scalarExtension_literal_map_fdrep_owner_local
      (A := A) (K := K) (G := G) Q
  exact f.rangeRestrict

/-- Helper for Proposition 15-15.5-1: the range-restricted exact-owner literal map is bijective. -/
private theorem
    projective_scalarExtension_literal_rangeRestrictLinearMap_bijective_fdrep_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
    let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
    letI : SMul A V.V := instMod.toSMul
    letI : Module A V.V := instMod
    letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
      change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
      rfl
    Function.Bijective
      (projective_scalarExtension_literal_rangeRestrictLinearMap_fdrep_owner_local
        (A := A) (K := K) (G := G) Q) := by
  let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
  let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
  letI : SMul A V.V := instMod.toSMul
  letI : Module A V.V := instMod
  letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
    change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
    rfl
  let f :=
    projective_scalarExtension_literal_map_fdrep_owner_local
      (A := A) (K := K) (G := G) Q
  constructor
  · intro x y hxy
    apply
      projective_scalarExtension_literal_map_fdrep_owner_injective_local
        (A := A) (K := K) (G := G) Q
    exact congrArg Subtype.val hxy
  · intro z
    rcases z.2 with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx

/-- Helper for Proposition 15-15.5-1: the exact-owner literal range is `A`-linearly equivalent to
the original projective owner. -/
private noncomputable def projective_scalarExtension_literal_rangeLinearEquiv_fdrep_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
    let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
    letI : SMul A V.V := instMod.toSMul
    letI : Module A V.V := instMod
    letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
      change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
      rfl
    let L : StableLattice A V.ρ :=
      projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local
        (A := A) (K := K) (G := G) Q
    Q.V ≃ₗ[A] L.toSubmodule := by
  let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
  let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
  letI : SMul A V.V := instMod.toSMul
  letI : Module A V.V := instMod
  letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
    change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
    rfl
  exact
    LinearEquiv.ofBijective
      (projective_scalarExtension_literal_rangeRestrictLinearMap_fdrep_owner_local
        (A := A) (K := K) (G := G) Q)
      (projective_scalarExtension_literal_rangeRestrictLinearMap_bijective_fdrep_owner_local
        (A := A) (K := K) (G := G) Q)

/-- Helper for Proposition 15-15.5-1: the exact-owner range-restricted literal map intertwines
the action of a group generator. -/
private theorem projective_scalarExtension_literal_rangeRestrict_map_of_fdrep_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
    let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
    letI : SMul A V.V := instMod.toSMul
    letI : Module A V.V := instMod
    letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
      change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
      rfl
    let L : StableLattice A V.ρ :=
      projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local
        (A := A) (K := K) (G := G) Q
    ∀ g : G, ∀ x : Q.V,
      projective_scalarExtension_literal_rangeRestrictLinearMap_fdrep_owner_local
          (A := A) (K := K) (G := G) Q ((MonoidAlgebra.of A G g) • x) =
        (MonoidAlgebra.of A G g) •
          projective_scalarExtension_literal_rangeRestrictLinearMap_fdrep_owner_local
            (A := A) (K := K) (G := G) Q x := by
  let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
  let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
  letI : SMul A V.V := instMod.toSMul
  letI : Module A V.V := instMod
  letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
    change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
    rfl
  let L : StableLattice A V.ρ :=
    projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local
      (A := A) (K := K) (G := G) Q
  let f :=
    projective_scalarExtension_literal_map_fdrep_owner_local
      (A := A) (K := K) (G := G) Q
  let fr :=
    projective_scalarExtension_literal_rangeRestrictLinearMap_fdrep_owner_local
      (A := A) (K := K) (G := G) Q
  change ∀ g : G, ∀ x : Q.V,
    fr ((MonoidAlgebra.of A G g) • x) = (MonoidAlgebra.of A G g) • fr x
  intro g x
  apply Subtype.ext
  rw [show (MonoidAlgebra.of A G g) • fr x = L.toRepresentation g (fr x) by
    rw [← Representation.asAlgebraHom_single_one (ρ := L.toRepresentation) g]
    rfl]
  have hrestrict : ↑(fr x) = f x := by
    rfl
  let ρK : Representation K G (K ⊗[A] Q.V) :=
    Representation.scalarExtension (Representation.ofModule' Q.V)
  have hsingle :=
    Representation.single_smul (ρ := ρK) (t := (1 : K)) (g := g)
      (v := TensorProduct.mk A K Q.V 1 x)
  have haction :
      MonoidAlgebra.of K G g • (TensorProduct.mk A K Q.V 1 x) =
        ρK g (TensorProduct.mk A K Q.V 1 x) := by
    simpa [ρK, MonoidAlgebra.of_apply] using hsingle
  calc
    ↑(fr ((MonoidAlgebra.of A G g) • x)) =
        f ((MonoidAlgebra.of A G g) • x) := by
          rfl
    _ =
        TensorProduct.mk A K Q.V 1 ((MonoidAlgebra.of A G g) • x) := by
          rfl
    _ =
        (MonoidAlgebra.mapRingHom G (algebraMap A K) (MonoidAlgebra.of A G g)) •
          TensorProduct.mk A K Q.V 1 x := by
            simpa [MonoidAlgebra.of_apply] using
              (monoidAlgebra_of_smul_tmul
                (Λ := A) (P := Q.V) (κ := K) g (1 : K) x).symm
    _ =
        ((Q.scalarExtension K).ρ g)
          (TensorProduct.mk A K Q.V 1 x) := by
            simpa [MonoidAlgebra.of_apply] using haction
    _ =
        ((Q.scalarExtension K).ρ g) (f x) := by
          rfl
    _ =
        ((Q.scalarExtension K).ρ g) ↑(fr x) := by
          rw [hrestrict]
    _ =
        ↑(L.toRepresentation g (fr x)) := by
          rfl

/-- Helper for Proposition 15-15.5-1: the exact-owner range-restricted literal map intertwines
the `A[G]`-action. -/
private theorem projective_scalarExtension_literal_rangeRestrict_map_groupAlgebra_fdrep_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
    let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
    letI : SMul A V.V := instMod.toSMul
    letI : Module A V.V := instMod
    letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
      change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
      rfl
    let L : StableLattice A V.ρ :=
      projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local
        (A := A) (K := K) (G := G) Q
    ∀ r : A[G], ∀ x : Q.V,
      projective_scalarExtension_literal_rangeRestrictLinearMap_fdrep_owner_local
          (A := A) (K := K) (G := G) Q (r • x) =
        r •
          projective_scalarExtension_literal_rangeRestrictLinearMap_fdrep_owner_local
            (A := A) (K := K) (G := G) Q x := by
  let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
  let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
  letI : SMul A V.V := instMod.toSMul
  letI : Module A V.V := instMod
  letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
    change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
    rfl
  let fr :=
    projective_scalarExtension_literal_rangeRestrictLinearMap_fdrep_owner_local
      (A := A) (K := K) (G := G) Q
  change ∀ r : A[G], ∀ x : Q.V, fr (r • x) = r • fr x
  intro r x
  refine MonoidAlgebra.induction_on
    (p := fun a : A[G] => fr (a • x) = a • fr x) r ?_ ?_ ?_
  · intro g
    simpa using
      projective_scalarExtension_literal_rangeRestrict_map_of_fdrep_owner_local
        (A := A) (K := K) (G := G) Q g x
  · intro a b ha hb
    simp [add_smul, ha, hb]
  · intro c a ha
    calc
      fr ((c • a) • x) = fr (c • (a • x)) := by
            simpa [smul_smul]
      _ =
        c • fr (a • x) := by
            simp
      _ =
        c • (a • fr x) := by
            rw [ha]
      _ =
        (c • a) • fr x := by
            simpa using (smul_assoc c a (fr x)).symm

/-- Helper for Proposition 15-15.5-1: the exact-owner literal range is `A[G]`-linearly equivalent
to the original projective owner. -/
private noncomputable def
    projective_scalarExtension_literal_rangeLinearEquiv_groupAlgebra_fdrep_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
    let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
    letI : SMul A V.V := instMod.toSMul
    letI : Module A V.V := instMod
    letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
      change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
      rfl
    let L : StableLattice A V.ρ :=
      projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local
        (A := A) (K := K) (G := G) Q
    Q.V ≃ₗ[A[G]] L.toSubmodule := by
  let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
  let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
  letI : SMul A V.V := instMod.toSMul
  letI : Module A V.V := instMod
  letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
    change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
    rfl
  let eA :=
    projective_scalarExtension_literal_rangeLinearEquiv_fdrep_owner_local
      (A := A) (K := K) (G := G) Q
  refine
    { toFun := eA
      invFun := eA.symm
      left_inv := eA.left_inv
      right_inv := eA.right_inv
      map_add' := eA.map_add
      map_smul' := ?_ }
  intro r x
  change
    projective_scalarExtension_literal_rangeRestrictLinearMap_fdrep_owner_local
        (A := A) (K := K) (G := G) Q (r • x) =
      r • projective_scalarExtension_literal_rangeRestrictLinearMap_fdrep_owner_local
        (A := A) (K := K) (G := G) Q x
  exact
    projective_scalarExtension_literal_rangeRestrict_map_groupAlgebra_fdrep_owner_local
      (A := A) (K := K) (G := G) Q r x

/-- Helper for Proposition 15-15.5-1: the exact-owner literal range is projective over `A[G]`
because it is `A[G]`-linearly equivalent to the original projective module. -/
private theorem projective_scalarExtension_literal_range_projective_fdrep_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
    let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
    letI : SMul A V.V := instMod.toSMul
    letI : Module A V.V := instMod
    letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
      change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
      rfl
    let L : StableLattice A V.ρ :=
      projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local
        (A := A) (K := K) (G := G) Q
    Module.Projective A[G] L.toSubmodule := by
  let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
  let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
  letI : SMul A V.V := instMod.toSMul
  letI : Module A V.V := instMod
  letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
    change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
    rfl
  let L : StableLattice A V.ρ :=
    projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local
      (A := A) (K := K) (G := G) Q
  let e :=
    projective_scalarExtension_literal_rangeLinearEquiv_groupAlgebra_fdrep_owner_local
      (A := A) (K := K) (G := G) Q
  change Module.Projective A[G] L.toSubmodule
  exact Module.Projective.of_equiv' e

/-- Helper for Proposition 15-15.5-1: the exact-owner literal range has the same residue-field
reduction as the original projective module. -/
private theorem projective_scalarExtension_literal_range_reduction_linearEquiv_fdrep_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
    let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
    letI : SMul A V.V := instMod.toSMul
    letI : Module A V.V := instMod
    letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
      change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
      rfl
    let L : StableLattice A V.ρ :=
      projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local
        (A := A) (K := K) (G := G) Q
    letI : Module k[G] L.reduction := by
      change Module k[G] L.reductionRepresentation.asModule
      infer_instance
    Nonempty (L.reduction ≃ₗ[k[G]] (k ⊗[A] Q.V)) := by
  let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
  let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
  letI : SMul A V.V := instMod.toSMul
  letI : Module A V.V := instMod
  letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
    change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
    rfl
  let L : StableLattice A V.ρ :=
    projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local
      (A := A) (K := K) (G := G) Q
  letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
  letI : IsScalarTower A k L.reduction :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module k[G] L.reduction := by
    change Module k[G] L.reductionRepresentation.asModule
    infer_instance
  let eAQ :=
    projective_scalarExtension_literal_rangeLinearEquiv_groupAlgebra_fdrep_owner_local
      (A := A) (K := K) (G := G) Q
  have hprojQ : Module.Projective A[G] Q.V := by
    infer_instance
  have hprojL : Module.Projective A[G] L.toSubmodule :=
    projective_scalarExtension_literal_range_projective_fdrep_owner_local
      (A := A) (K := K) (G := G) Q
  have hAQ : Nonempty (Q.V ≃ₗ[A[G]] L.toSubmodule) := ⟨eAQ⟩
  rcases
      (projective_monoidAlgebra_nonempty_linearEquiv_iff_of_isResidueFieldReduction
        (Λ := A) (G := G)
        (P := Q.V)
        (Pbar := k ⊗[A] Q.V)
        (f := TensorProduct.mk A k Q.V 1)
        (hf := MonoidAlgebra.tensorProduct_mk_isResidueFieldReduction
          (Λ := A) (G := G) (P := Q.V))
        (P' := L.toSubmodule)
        (Pbar' := L.reduction)
        (f' := (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction))
        (hf' := StableLattice.reduction_mkQ_isResidueFieldReduction_local
          (A := A) (K := K) (G := G) L)
        hprojQ hprojL).mp hAQ with
    ⟨ered⟩
  exact ⟨ered.symm⟩

/-- Helper for Proposition 15-15.5-1: the module owner of the intrinsic residue-field reduction
matches the tautological owner of its finite representation. -/
private theorem residueFieldReduction_asModule_nonempty_linearEquiv_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    letI : Module k Q.residueFieldReduction.V :=
      Module.compHom Q.residueFieldReduction.V (algebraMap k k[G])
    letI : IsScalarTower k k[G] Q.residueFieldReduction.V :=
      IsScalarTower.of_compHom k k[G] Q.residueFieldReduction.V
    Nonempty
      (asModule Q.residueFieldReduction.toFiniteRep.ρ ≃ₗ[k[G]]
        Q.residueFieldReduction.V) := by
  letI : Module k Q.residueFieldReduction.V :=
    Module.compHom Q.residueFieldReduction.V (algebraMap k k[G])
  letI : IsScalarTower k k[G] Q.residueFieldReduction.V :=
    IsScalarTower.of_compHom k k[G] Q.residueFieldReduction.V
  change Nonempty
    ((Representation.ofModule (ModuleCat.of k[G] Q.residueFieldReduction.V)).asModule ≃ₗ[k[G]]
      Q.residueFieldReduction.V)
  let Mmod : ModuleCat k[G] := ModuleCat.of k[G] Q.residueFieldReduction.V
  let toFun : (Representation.ofModule Mmod).asModule → Q.residueFieldReduction.V := fun x =>
    (RestrictScalars.addEquiv k k[G] Q.residueFieldReduction.V)
      ((Representation.ofModule Mmod).asModuleEquiv x)
  let invFun : Q.residueFieldReduction.V → (Representation.ofModule Mmod).asModule := fun x =>
    (Representation.ofModule Mmod).asModuleEquiv.symm
      ((RestrictScalars.addEquiv k k[G] Q.residueFieldReduction.V).symm x)
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
        exact (RestrictScalars.addEquiv k k[G] Q.residueFieldReduction.V).map_add _ _
      map_smul' := by
        intro r x
        exact Representation.smul_ofModule_asModule (M := Mmod) r x }⟩

/-- Helper for Proposition 15-15.5-1: the exact-owner literal range reduction is isomorphic to the
intrinsic residue-field reduction of `Q`. -/
private theorem projective_scalarExtension_literal_range_reduction_iso_fdrep_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
    let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
    letI : SMul A V.V := instMod.toSMul
    letI : Module A V.V := instMod
    letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
      change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
      rfl
    let L : StableLattice A V.ρ :=
      projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local
        (A := A) (K := K) (G := G) Q
    Nonempty (FDRep.of L.reductionRepresentation ≅ Q.residueFieldReduction.toFiniteRep) := by
  let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
  let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
  letI : SMul A V.V := instMod.toSMul
  letI : Module A V.V := instMod
  letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
    change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
    rfl
  let L : StableLattice A V.ρ :=
    projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local
      (A := A) (K := K) (G := G) Q
  letI : Module k[G] L.reduction := by
    change Module k[G] L.reductionRepresentation.asModule
    infer_instance
  have hL :
      Nonempty
        (asModule (FDRep.of L.reductionRepresentation).ρ ≃ₗ[k[G]] L.reduction) := by
    simpa using
      (nonempty_asModuleLinearEquiv_target_local_support
        (G := G) (ρ := (FDRep.of L.reductionRepresentation).ρ))
  rcases hL with ⟨eL⟩
  rcases
      projective_scalarExtension_literal_range_reduction_linearEquiv_fdrep_owner_local
        (A := A) (K := K) (G := G) Q with
    ⟨ered⟩
  letI : Module k Q.residueFieldReduction.V :=
    Module.compHom Q.residueFieldReduction.V (algebraMap k k[G])
  letI : IsScalarTower k k[G] Q.residueFieldReduction.V :=
    IsScalarTower.of_compHom k k[G] Q.residueFieldReduction.V
  rcases residueFieldReduction_asModule_nonempty_linearEquiv_local Q with
    ⟨eQas⟩
  have hQowner :
      Nonempty (Q.residueFieldReduction.V ≃ₗ[k[G]] (k ⊗[A] Q.V)) := by
    simpa [FiniteProjectiveGroupAlgebraModule.residueFieldReduction,
      FiniteProjectiveGroupAlgebraModule.V] using
        (show Nonempty ((k ⊗[A] Q.V) ≃ₗ[k[G]] (k ⊗[A] Q.V)) from
          ⟨LinearEquiv.refl k[G] (k ⊗[A] Q.V)⟩)
  rcases hQowner with ⟨eQowner⟩
  let eQ : asModule Q.residueFieldReduction.toFiniteRep.ρ ≃ₗ[k[G]] (k ⊗[A] Q.V) :=
    eQas.trans eQowner
  refine
    fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv_local_support
      (G := G) ?_
  exact ⟨eL.trans (ered.trans eQ.symm)⟩

/-- Helper for Proposition 15-15.5-1: the explicit-owner literal range lattice still reduces to
the intrinsic residue-field reduction of `Q`. -/
private theorem projective_scalarExtension_literal_range_reduction_class_fdrep_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
    let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
    letI : SMul A V.V := instMod.toSMul
  letI : Module A V.V := instMod
  letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
    change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
    rfl
  let L : StableLattice A V.ρ :=
    projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local
      (A := A) (K := K) (G := G) Q
  [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀ := by
  exact
    finiteRepGrothendieckClass_eq_of_nonempty_iso
      (L := k) (G := G)
      (projective_scalarExtension_literal_range_reduction_iso_fdrep_owner_local
        (A := A) (K := K) (G := G) Q)

/-- Helper for Proposition 15-15.5-1: Serre's literal scalar-extension lattice can be chosen on
the exact `FDRep.of` owner used by the decomposition-map computation. -/
private theorem projective_scalarExtension_literal_reduction_class_fdrep_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
    let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
    letI : SMul A V.V := instMod.toSMul
    letI : Module A V.V := instMod
    letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
      change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
      rfl
    ∃ L : StableLattice A V.ρ,
      [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀ := by
  let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
  let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
  letI : SMul A V.V := instMod.toSMul
  letI : Module A V.V := instMod
  letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
    change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
    rfl
  let L :=
    projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local
      (A := A) (K := K) (G := G) Q
  -- Package the fixed literal lattice with the already proved reduction-class computation.
  refine ⟨L, ?_⟩
  simpa [L] using
    projective_scalarExtension_literal_range_reduction_class_fdrep_owner_local
      (A := A) (K := K) (G := G) Q

/-- Helper for Proposition 15-15.5-1: computing `decompositionHom` on the rebundled
scalar-extension owner recovers the literal residue-field reduction class of `Q`. -/
private theorem decompositionHom_fdrepOf_scalarExtension_eq_literal_reduction_class_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    decompositionHom A K G [FDRep.of (Q.scalarExtension K).ρ]₀ =
      [Q.residueFieldReduction.toFiniteRep]₀ := by
  let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
  let instMod : Module A V.V := Module.compHom V.V (algebraMap A K)
  letI : SMul A V.V := instMod.toSMul
  letI : Module A V.V := instMod
  letI : IsScalarTower A K V.V := IsScalarTower.of_algebraMap_smul fun a x => by
    change ((algebraMap A K a) • x : V.V) = @SMul.smul A V.V instMod.toSMul a x
    rfl
  obtain ⟨L, hL⟩ :=
    projective_scalarExtension_literal_reduction_class_fdrep_owner_local
      (A := A) (K := K) (G := G) Q
  -- Compute `decompositionHom` using the explicit stable lattice already placed on the
  -- `FDRep.of` owner, then replace its reduction by the intrinsic residue-field reduction of `Q`.
  change decompositionHom A K G [V]₀ = [Q.residueFieldReduction.toFiniteRep]₀
  calc
    decompositionHom A K G [V]₀ =
        [FDRep.of L.reductionRepresentation]₀ := by
          simpa using
            decompositionHom_finiteRepClass_eq
              (A := A) (K := K) (G := G) V L
    _ = [Q.residueFieldReduction.toFiniteRep]₀ := hL

theorem decompositionHom_projective_scalarExtension_class_eq_residueFieldReduction_class
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    decompositionHom A K G [Q.scalarExtension K]₀ =
      cartanHom k G [Q.residueFieldReduction]ₚ₀ := by
  -- Route correction: pass once through the explicit `FDRep.of` owner of the literal lattice,
  -- then identify the resulting reduction class with the Cartan class of `Q mod 𝔪`.
  calc
    decompositionHom A K G [Q.scalarExtension K]₀ =
        decompositionHom A K G [FDRep.of (Q.scalarExtension K).ρ]₀ := by
          exact
            decompositionHom_projective_scalarExtension_class_eq_fdrepOfRho_local
              (A := A) (K := K) (G := G) Q
    _ = [Q.residueFieldReduction.toFiniteRep]₀ := by
          exact
            decompositionHom_fdrepOf_scalarExtension_eq_literal_reduction_class_local
              (A := A) (K := K) (G := G) Q
    _ = cartanHom k G [Q.residueFieldReduction]ₚ₀ := by
          simpa using
            (cartanHom_projectiveClass_eq k G Q.residueFieldReduction).symm

/-- Helper for Proposition 15-15.5-1: the Cartan class of the residue-field reduction of a
projective `A[G]`-module is its finite-representation class. -/
private theorem residueFieldReduction_cartan_class_eq_finiteRepClass_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    cartanHom k G [Q.residueFieldReduction]ₚ₀ = [Q.residueFieldReduction.toFiniteRep]₀ := by
  -- The residue-field reduction is already projective over `k[G]`, so its Cartan class is the
  -- corresponding finite-representation class.
  exact cartanHom_projectiveClass_eq k G Q.residueFieldReduction

/-- Helper for Proposition 15-15.5-1: Serre's projective generator identity immediately rewrites
the scalar-extension class of `Q` to the finite-representation class of its residue reduction. -/
private theorem decompositionHom_projective_scalarExtension_class_eq_finiteRepClass_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    decompositionHom A K G [Q.scalarExtension K]₀ =
      [Q.residueFieldReduction.toFiniteRep]₀ := by
  -- First compute `d([Q_K])` by Serre's projective formula, then collapse the Cartan class of the
  -- projective residue reduction to its ordinary finite-representation class.
  calc
    decompositionHom A K G [Q.scalarExtension K]₀ =
        cartanHom k G [Q.residueFieldReduction]ₚ₀ := by
          exact
            decompositionHom_projective_scalarExtension_class_eq_residueFieldReduction_class
              (A := A) (K := K) (G := G) Q
    _ = [Q.residueFieldReduction.toFiniteRep]₀ := by
          exact residueFieldReduction_cartan_class_eq_finiteRepClass_local Q

/-- Helper for Proposition 15-15.5-1: if a projective lift reduces to `τ`, then Serre's
decomposition map sends its generic class to `[τ]₀`. -/
theorem decompositionHom_projective_scalarExtension_class_eq_iso_target_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) {τ : FDRep k G}
    (hQτ : Nonempty (Q.residueFieldReduction.toFiniteRep ≅ τ)) :
    decompositionHom A K G [Q.scalarExtension K]₀ = [τ]₀ := by
  -- Compute `d([Q_K])` by the reduction of `Q`, then transport along the chosen reduction
  -- isomorphism to the target simple class.
  calc
    decompositionHom A K G [Q.scalarExtension K]₀ =
        [Q.residueFieldReduction.toFiniteRep]₀ := by
          exact
            decompositionHom_projective_scalarExtension_class_eq_finiteRepClass_local
              (A := A) (K := K) (G := G) Q
    _ = [τ]₀ := by
          simpa using
            finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G) hQτ

/-- Helper for Proposition 15-15.5-1: if a lifted projective module reduces to a simple
`k[G]`-representation, then its generic fiber is simple. -/
theorem projective_lift_scalarExtension_simple_of_order_prime_to_p
    (hG : ¬ p ∣ Nat.card G)
    (S : FDRep k G) [Simple S]
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (hQS : Nonempty (Q.residueFieldReduction.toFiniteRep ≅ S)) :
    Simple (Q.scalarExtension K) := by
  let _ : NeZero (Nat.card G : k) := NeZero.of_not_dvd k hG
  obtain ⟨L, hL⟩ :=
    projective_scalarExtension_literal_reduction_class_local
      (A := A) (K := K) (G := G) Q
  have hsemiL : IsSemisimpleRepresentation (FDRep.of L.reductionRepresentation).ρ := by
    infer_instance
  have hsemiS : IsSemisimpleRepresentation S.ρ := by
    infer_instance
  have hclass :
      [FDRep.of L.reductionRepresentation]₀ = [S]₀ := by
    -- First rewrite the reduction of the literal lattice to the intrinsic residue reduction of
    -- `Q`, and then use the chosen isomorphism with the simple target `S`.
    calc
      [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀ := hL
      _ = [S]₀ := by
            simpa using finiteRepGrothendieckClass_eq_of_nonempty_iso
              (L := k) (G := G) hQS
  rcases
      (finiteRepGrothendieckClass_eq_iff_nonempty_iso_of_isSemisimple hsemiL hsemiS).mp hclass
    with ⟨eLS⟩
  let _ : Simple (FDRep.of L.reductionRepresentation) := CategoryTheory.Simple.of_iso eLS
  have hLirr : L.reductionRepresentation.IsIrreducible := by
    -- The reduction representation is simple because it is isomorphic to `S`.
    simpa using FDRep.isIrreducible_of_simple (FDRep.of L.reductionRepresentation)
  have hQirr : Representation.IsIrreducible (Q.scalarExtension K).ρ := by
    -- Serre's route now applies the simple-reduction criterion to the literal stable lattice.
    simpa using simple_reduction_implies_isIrreducible
      (A := A) (K := K) (G := G) ((Q.scalarExtension K).ρ) L hLirr
  exact FDRep.simple_of_isIrreducible (Q.scalarExtension K)

end DecompositionHom
