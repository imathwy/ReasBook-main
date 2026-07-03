import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_4_5
import LinearRepresentations_Serre_1977.Chap14.Infra_14_4_ProjectiveLift
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_2_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.ReductionMkQ
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.StableLatticeExactOwner
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

section StableLatticeModuleBridge

variable {E : Type u} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]

/-- Helper for Proposition 15-15.5-1: the underlying `A`-submodule of a stable lattice carries
the induced `A[G]`-module structure. -/
private instance stableLattice_toSubmodule_module_local_support
    {ρ : Representation K G E} (L : StableLattice A ρ) :
    Module A[G] L.toSubmodule := by
  change Module A[G] L.toRepresentation.asModule
  infer_instance

/-- Helper for Proposition 15-15.5-1: the induced `A[G]`-module structure on a stable lattice is
compatible with restriction of scalars from `A`. -/
private instance stableLattice_toSubmodule_isScalarTower_local_support
    {ρ : Representation K G E} (L : StableLattice A ρ) :
    IsScalarTower A A[G] L.toSubmodule := by
  change IsScalarTower A A[G] L.toRepresentation.asModule
  infer_instance

end StableLatticeModuleBridge

/-- Helper for Proposition 15-15.5-1: the literal scalar-extension map sends `x` to the pure
tensor `1 ⊗ x` inside `Q.scalarExtension K`. -/
private abbrev projective_scalarExtension_literal_map_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Q.V →ₗ[A] K ⊗[A] Q.V :=
  TensorProduct.mk A K Q.V 1

/-- Helper for Proposition 15-15.5-1: over the fraction field, the literal map `x ↦ 1 ⊗ x` is
injective. -/
private theorem projective_scalarExtension_literal_map_injective_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Function.Injective
      (projective_scalarExtension_literal_map_local_support
        (A := A) (K := K) (G := G) Q) := by
  let _ : Module.Free A Q.V := Q.free
  let b : Module.Basis (Module.Free.ChooseBasisIndex A Q.V) A Q.V :=
    Module.Free.chooseBasis A Q.V
  intro x y hxy
  -- Compare coordinates in the tensor-product basis to recover equality upstairs.
  apply b.repr.injective
  ext i
  have hcoord :=
    congrArg (fun z ↦ ((Algebra.TensorProduct.basis K b).repr z) i) hxy
  apply (IsFractionRing.injective A K)
  simpa using hcoord

/-- Helper for Proposition 15-15.5-1: the image of the literal map is stable under the
scalar-extended `G`-action. -/
private theorem projective_scalarExtension_literal_map_apply_mem_range_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (g : G) {x : K ⊗[A] Q.V}
    (hx :
      x ∈
        (projective_scalarExtension_literal_map_local_support
          (A := A) (K := K) (G := G) Q).range) :
    (Q.scalarExtension K).ρ g x ∈
      (projective_scalarExtension_literal_map_local_support
        (A := A) (K := K) (G := G) Q).range := by
  rcases hx with ⟨y, rfl⟩
  -- Rewrite the scalar-extended action on a pure tensor and keep the source vector upstairs.
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
  exact
    (monoidAlgebra_of_smul_tmul (Λ := A) (P := Q.V) (κ := K) g (1 : K) y).symm.trans
      haction

/-- Helper for Proposition 15-15.5-1: the literal image of `Q.V` spans the scalar extension over
`K` and is finite over `A`, so it forms a lattice. -/
private theorem projective_scalarExtension_literal_map_range_isLattice_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Submodule.IsLattice K
      ((projective_scalarExtension_literal_map_local_support
        (A := A) (K := K) (G := G) Q).range) := by
  refine
    { fg := ?_
      span_eq_top := ?_ }
  · -- Finite generation is inherited from the finite `A`-module `Q.V`.
    have hfg_top : (⊤ : Submodule A Q.V).FG := by
      exact (Module.Finite.iff_fg (N := (⊤ : Submodule A Q.V))).1 inferInstance
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map
      (projective_scalarExtension_literal_map_local_support
        (A := A) (K := K) (G := G) Q) hfg_top
  · let _ : Module.Free A Q.V := Q.free
    let b := Module.Free.chooseBasis A Q.V
    -- The tensor-product basis vectors are literal pure tensors, hence already in the image.
    apply eq_top_iff.2
    intro x hx
    have hxrepr : x = ∑ i, ((Algebra.TensorProduct.basis K b).repr x) i •
        (Algebra.TensorProduct.basis K b) i := by
      simpa using ((Algebra.TensorProduct.basis K b).sum_repr x).symm
    rw [hxrepr]
    refine Submodule.sum_mem _ ?_
    intro i hi
    have hi' :
        (Algebra.TensorProduct.basis K b) i ∈
          Submodule.span K
            (((projective_scalarExtension_literal_map_local_support
                (A := A) (K := K) (G := G) Q).range :
                Submodule A (K ⊗[A] Q.V)) :
              Set (K ⊗[A] Q.V)) := by
      apply Submodule.subset_span
      refine ⟨b i, ?_⟩
      simpa [projective_scalarExtension_literal_map_local_support] using
        (Algebra.TensorProduct.basis_apply (A := K) (b := b) i)
    exact Submodule.smul_mem _ _ hi'

/-- Helper for Proposition 15-15.5-1: the literal range inside `Q.scalarExtension K` is the fixed
stable lattice used in LinearRepresentations_Serre_1977's projective comparison. -/
private noncomputable def projective_scalarExtension_literal_range_stableLattice_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    StableLattice A (Q.scalarExtension K).ρ :=
  { toSubmodule :=
      (projective_scalarExtension_literal_map_local_support
        (A := A) (K := K) (G := G) Q).range
    apply_mem_toSubmodule :=
      projective_scalarExtension_literal_map_apply_mem_range_local_support
        (A := A) (K := K) (G := G) Q
    isLattice :=
      projective_scalarExtension_literal_map_range_isLattice_local_support
        (A := A) (K := K) (G := G) Q }

/-- Helper for Proposition 15-15.5-1: restricting the literal map to its image keeps the exact
owner needed later for the decomposition-map computation. -/
private noncomputable def
    projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Q.V →ₗ[A]
      (projective_scalarExtension_literal_range_stableLattice_local_support
        (A := A) (K := K) (G := G) Q).toSubmodule :=
  (projective_scalarExtension_literal_map_local_support
    (A := A) (K := K) (G := G) Q).rangeRestrict

/-- Helper for Proposition 15-15.5-1: the range-restricted literal map is bijective. -/
private theorem
    projective_scalarExtension_literal_rangeRestrictLinearMap_bijective_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Function.Bijective
      (projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
        (A := A) (K := K) (G := G) Q) := by
  constructor
  · exact
      (LinearMap.injective_rangeRestrict_iff
        (f := projective_scalarExtension_literal_map_local_support
          (A := A) (K := K) (G := G) Q)).2
        (projective_scalarExtension_literal_map_injective_local_support
          (A := A) (K := K) (G := G) Q)
  · exact LinearMap.surjective_rangeRestrict
      (projective_scalarExtension_literal_map_local_support
        (A := A) (K := K) (G := G) Q)

/-- Helper for Proposition 15-15.5-1: the literal source module identifies `A`-linearly with its
range inside `Q.scalarExtension K`. -/
private noncomputable def projective_scalarExtension_literal_rangeLinearEquiv_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Q.V ≃ₗ[A]
      (projective_scalarExtension_literal_range_stableLattice_local_support
        (A := A) (K := K) (G := G) Q).toSubmodule :=
  LinearEquiv.ofBijective
    (projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
      (A := A) (K := K) (G := G) Q)
    (projective_scalarExtension_literal_rangeRestrictLinearMap_bijective_local_support
      (A := A) (K := K) (G := G) Q)

/-- Helper for Proposition 15-15.5-1: inside the literal-range lattice, the generator `[g]`
acts through the restricted ambient representation. -/
private theorem
    projective_scalarExtension_literal_range_toRepresentation_monoidAlgebra_of_smul_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    ∀ g : G, ∀ x :
      (projective_scalarExtension_literal_range_stableLattice_local_support
        (A := A) (K := K) (G := G) Q).toSubmodule,
      MonoidAlgebra.of A G g • x =
        (projective_scalarExtension_literal_range_stableLattice_local_support
          (A := A) (K := K) (G := G) Q).toRepresentation g x := by
  intro g x
  rw [← Representation.asAlgebraHom_single_one
    (ρ :=
      (projective_scalarExtension_literal_range_stableLattice_local_support
        (A := A) (K := K) (G := G) Q).toRepresentation) g]
  rfl

/-- Helper for Proposition 15-15.5-1: on group generators, the range-restricted literal map
already intertwines the exact subtype owner with the ambient scalar-extension action. -/
private theorem projective_scalarExtension_literal_rangeRestrict_map_of_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (g : G) (x : Q.V) :
    projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
        (A := A) (K := K) (G := G) Q ((MonoidAlgebra.of A G g) • x) =
      (MonoidAlgebra.of A G g) •
        projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
          (A := A) (K := K) (G := G) Q x := by
  -- Compare the two subtype points after forgetting back to the ambient tensor-product owner.
  apply Subtype.ext
  rw [projective_scalarExtension_literal_range_toRepresentation_monoidAlgebra_of_smul_local_support
    (A := A) (K := K) (G := G) Q g
    (projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
      (A := A) (K := K) (G := G) Q x)]
  have hrestrict :
      ↑(projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
          (A := A) (K := K) (G := G) Q x) =
        TensorProduct.mk A K Q.V 1 x := by
    rfl
  calc
    ↑((projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
          (A := A) (K := K) (G := G) Q) ((MonoidAlgebra.of A G g) • x)) =
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
            simpa [MonoidAlgebra.of_apply] using
              (Representation.single_smul
                (ρ := (Q.scalarExtension K).ρ)
                (t := (1 : K)) (g := g) (v := TensorProduct.mk A K Q.V 1 x))
    _ =
        ((Q.scalarExtension K).ρ g)
          ↑(projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
            (A := A) (K := K) (G := G) Q x) := by
              rw [hrestrict]
    _ =
        ↑((projective_scalarExtension_literal_range_stableLattice_local_support
            (A := A) (K := K) (G := G) Q).toRepresentation g
          (projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
            (A := A) (K := K) (G := G) Q x)) := by
              simp [projective_scalarExtension_literal_rangeRestrictLinearMap_local_support,
                projective_scalarExtension_literal_map_local_support]

/-- Helper for Proposition 15-15.5-1: the range-restricted literal map already intertwines the
`A[G]`-action on `Q.V` with the induced action on the literal-range subtype. -/
private theorem projective_scalarExtension_literal_rangeRestrict_map_groupAlgebra_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (r : A[G]) (x : Q.V) :
    projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
        (A := A) (K := K) (G := G) Q (r • x) =
      r • projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
        (A := A) (K := K) (G := G) Q x := by
  -- Check equivariance on `MonoidAlgebra.of`, then extend linearly while keeping the subtype
  -- owner fixed.
  refine MonoidAlgebra.induction_on
    (p := fun a : A[G] =>
      projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
          (A := A) (K := K) (G := G) Q (a • x) =
        a • projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
          (A := A) (K := K) (G := G) Q x) r ?_ ?_ ?_
  · intro g
    simpa using
      projective_scalarExtension_literal_rangeRestrict_map_of_local_support
        (A := A) (K := K) (G := G) Q g x
  · intro a b ha hb
    simp [add_smul, ha, hb]
  · intro c a ha
    calc
      projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
          (A := A) (K := K) (G := G) Q ((c • a) • x) =
        projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
          (A := A) (K := K) (G := G) Q (c • (a • x)) := by
            simpa [smul_smul]
      _ =
        c • projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
          (A := A) (K := K) (G := G) Q (a • x) := by
            simp
      _ =
        c • (a • projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
          (A := A) (K := K) (G := G) Q x) := by
            rw [ha]
      _ =
        (c • a) • projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
          (A := A) (K := K) (G := G) Q x := by
            simpa using
              (smul_assoc c a
                (projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
                  (A := A) (K := K) (G := G) Q x)).symm

/-- Helper for Proposition 15-15.5-1: the literal range identification is compatible with the
`A[G]`-action. -/
private theorem projective_scalarExtension_literal_rangeLinearEquiv_map_groupAlgebra_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (r : A[G]) (x : Q.V) :
    projective_scalarExtension_literal_rangeLinearEquiv_local_support
        (A := A) (K := K) (G := G) Q (r • x) =
      r • projective_scalarExtension_literal_rangeLinearEquiv_local_support
        (A := A) (K := K) (G := G) Q x := by
  -- The `A`-linear equivalence is defined by the same range-restricted literal map.
  simpa [projective_scalarExtension_literal_rangeLinearEquiv_local_support] using
    projective_scalarExtension_literal_rangeRestrict_map_groupAlgebra_local_support
      (A := A) (K := K) (G := G) Q r x

/-- Helper for Proposition 15-15.5-1: the source module `Q.V` identifies with the literal range
as an `A[G]`-module. -/
private noncomputable def projective_scalarExtension_literal_rangeLinearEquiv_groupAlgebra_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Q.V ≃ₗ[A[G]]
      (projective_scalarExtension_literal_range_stableLattice_local_support
        (A := A) (K := K) (G := G) Q).toSubmodule :=
  { toFun :=
      projective_scalarExtension_literal_rangeLinearEquiv_local_support
        (A := A) (K := K) (G := G) Q
    map_add' := by
      intro x y
      exact
        (projective_scalarExtension_literal_rangeLinearEquiv_local_support
          (A := A) (K := K) (G := G) Q).map_add x y
    map_smul' :=
      projective_scalarExtension_literal_rangeLinearEquiv_map_groupAlgebra_local_support
        (A := A) (K := K) (G := G) Q
    invFun :=
      (projective_scalarExtension_literal_rangeLinearEquiv_local_support
        (A := A) (K := K) (G := G) Q).symm
    left_inv :=
      (projective_scalarExtension_literal_rangeLinearEquiv_local_support
        (A := A) (K := K) (G := G) Q).left_inv
    right_inv :=
      (projective_scalarExtension_literal_rangeLinearEquiv_local_support
        (A := A) (K := K) (G := G) Q).right_inv }

/-- Helper for Proposition 15-15.5-1: the fixed literal range is `A[G]`-linearly equivalent to
`Q.V`. -/
theorem projective_scalarExtension_literal_range_nonempty_linearEquiv_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Nonempty
      (Q.V ≃ₗ[A[G]]
        (projective_scalarExtension_literal_range_stableLattice_local_support
          (A := A) (K := K) (G := G) Q).toSubmodule) := by
  -- The owner-stable lattice is defined as the literal range, so the range-restricted map gives
  -- the needed `A[G]`-linear equivalence directly.
  exact
    ⟨projective_scalarExtension_literal_rangeLinearEquiv_groupAlgebra_local_support
      (A := A) (K := K) (G := G) Q⟩

/-- Helper for Proposition 15-15.5-1: the literal range is projective over `A[G]` because it is
`A[G]`-linearly equivalent to `Q.V`. -/
private theorem projective_scalarExtension_literal_range_projective_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Module.Projective A[G]
      (projective_scalarExtension_literal_range_stableLattice_local_support
        (A := A) (K := K) (G := G) Q).toSubmodule := by
  let e :=
    projective_scalarExtension_literal_rangeLinearEquiv_groupAlgebra_local_support
      (A := A) (K := K) (G := G) Q
  -- Transport projectivity across the explicit `A[G]`-linear equivalence.
  exact Module.Projective.of_equiv' e

/-- Helper for Proposition 15-15.5-1: after freezing the literal-range lattice on the exact
owner, its reduction is `k[G]`-linearly equivalent to the canonical tensor-product reduction of
`Q.V`. -/
theorem projective_scalarExtension_literal_range_reduction_linearEquiv_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let L :=
      projective_scalarExtension_literal_range_stableLattice_local_support
        (A := A) (K := K) (G := G) Q
    letI : Module k[G] L.reduction := by
      change Module k[G] L.reductionRepresentation.asModule
      infer_instance
    Nonempty (L.reduction ≃ₗ[k[G]] (k ⊗[A] Q.V)) := by
  let L :=
    projective_scalarExtension_literal_range_stableLattice_local_support
      (A := A) (K := K) (G := G) Q
  letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
  letI : IsScalarTower A k L.reduction :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module k[G] L.reduction := by
    change Module k[G] L.reductionRepresentation.asModule
    infer_instance
  letI : IsScalarTower k k[G] L.reduction := by
    change IsScalarTower k k[G] L.reductionRepresentation.asModule
    infer_instance
  let eAQ :=
    projective_scalarExtension_literal_rangeLinearEquiv_groupAlgebra_local_support
      (A := A) (K := K) (G := G) Q
  have hprojQ : Module.Projective A[G] Q.V := by
    infer_instance
  have hprojL : Module.Projective A[G] L.toSubmodule :=
    projective_scalarExtension_literal_range_projective_local_support
      (A := A) (K := K) (G := G) Q
  have hAQ : Nonempty (Q.V ≃ₗ[A[G]] L.toSubmodule) := ⟨eAQ⟩
  -- Compare the tensor-product reduction of `Q.V` with the quotient reduction of the fixed
  -- literal lattice `L`.
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

/-- Helper for Proposition 15-15.5-1: the tautological owner module of a representation is
canonically `k[G]`-linearly equivalent to its underlying carrier. -/
private theorem nonempty_asModuleLinearEquiv_target_local_support
    {V : Type u} [AddCommGroup V] [Module k V] (ρ : Representation k G V) :
    letI : Module k[G] V := Module.compHom V ρ.asAlgebraHom.toRingHom
    letI : IsScalarTower k k[G] V :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change ρ.asAlgebraHom (algebraMap k k[G] a) x = a • x
        simp [Algebra.smul_def]
    Nonempty (ρ.asModule ≃ₗ[k[G]] V) := by
  letI : Module k[G] V := Module.compHom V ρ.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρ.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  refine ⟨
    { toFun := fun x ↦ ρ.asModuleEquiv x
      invFun := fun x ↦ ρ.asModuleEquiv.symm x
      left_inv := fun x ↦ ρ.asModuleEquiv.symm_apply_apply x
      right_inv := fun x ↦ ρ.asModuleEquiv.apply_symm_apply x
      map_add' := fun x y ↦ ρ.asModuleEquiv.map_add x y
      map_smul' := ?_ }⟩
  intro a x
  -- Transport the `k[G]`-action through `asModuleEquiv`, then read it as the original action.
  calc
    ρ.asModuleEquiv (a • x) = ρ.asAlgebraHom a (ρ.asModuleEquiv x) := by
      simpa using Representation.asModuleEquiv_map_smul (ρ := ρ) a x
    _ = a • ρ.asModuleEquiv x := rfl

/-- Helper for Proposition 15-15.5-1: the owner module of
`Rep.ofModuleMonoidAlgebra.obj (ModuleCat.of k[G] M)` is canonically `k[G]`-linearly equivalent
to `M`. -/
private theorem nonempty_ofModuleMonoidAlgebra_asModuleLinearEquiv_local_support
    (M : Type u) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M] :
    Nonempty ((Rep.ofModuleMonoidAlgebra.obj (ModuleCat.of k[G] M)).ρ.asModule ≃ₗ[k[G]] M) := by
  change Nonempty ((Representation.ofModule (ModuleCat.of k[G] M)).asModule ≃ₗ[k[G]] M)
  let Mmod : ModuleCat k[G] := ModuleCat.of k[G] M
  let toFun : (Representation.ofModule Mmod).asModule → M := fun x ↦
    (RestrictScalars.addEquiv k k[G] M) ((Representation.ofModule Mmod).asModuleEquiv x)
  let invFun : M → (Representation.ofModule Mmod).asModule := fun x ↦
    (Representation.ofModule Mmod).asModuleEquiv.symm
      ((RestrictScalars.addEquiv k k[G] M).symm x)
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
        simp [toFun, Mmod]
      map_smul' := by
        intro r x
        exact Representation.smul_ofModule_asModule (M := Mmod) r x }⟩

/-- Helper for Proposition 15-15.5-1: a `k[G]`-linear equivalence between the owner modules of two
finite-dimensional representations upgrades to an isomorphism in `FDRep k G`. -/
private theorem fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv_local_support
    {σ τ : FDRep k G}
    (hστ : Nonempty (asModule σ.ρ ≃ₗ[k[G]] asModule τ.ρ)) :
    Nonempty (σ ≅ τ) := by
  rcases hστ with ⟨e⟩
  -- Repackage the recovered `k[G]`-linear equivalence as an isomorphism in `Rep k G`.
  let eRep : ((forget₂ (FDRep k G) (Rep k G)).obj σ) ≅
      ((forget₂ (FDRep k G) (Rep k G)).obj τ) :=
    Rep.unitIso ((forget₂ (FDRep k G) (Rep k G)).obj σ) ≪≫
      Rep.ofModuleMonoidAlgebra.mapIso e.toModuleIso ≪≫
      (Rep.unitIso ((forget₂ (FDRep k G) (Rep k G)).obj τ)).symm
  -- Faithfulness of `FDRep ⥤ Rep` transports that isomorphism back to `FDRep`.
  refine ⟨⟨(FDRep.forget₂HomLinearEquiv σ τ) eRep.hom,
    (FDRep.forget₂HomLinearEquiv τ σ) eRep.inv, ?_, ?_⟩⟩
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change eRep.hom ≫ eRep.inv = 𝟙 _
    exact eRep.hom_inv_id
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change eRep.inv ≫ eRep.hom = 𝟙 _
    exact eRep.inv_hom_id

/-- Helper for Proposition 15-15.5-1: the reduction of the fixed literal range lattice is
isomorphic to the intrinsic residue-field reduction of `Q`. -/
theorem projective_scalarExtension_literal_range_reduction_iso_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Nonempty
      (FDRep.of
          (projective_scalarExtension_literal_range_stableLattice_local_support
            (A := A) (K := K) (G := G) Q).reductionRepresentation ≅
        Q.residueFieldReduction.toFiniteRep) := by
  let L :=
    projective_scalarExtension_literal_range_stableLattice_local_support
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
  rcases projective_scalarExtension_literal_range_reduction_linearEquiv_local_support
      (A := A) (K := K) (G := G) Q with
    ⟨ered⟩
  letI : Module k Q.residueFieldReduction.V :=
    Module.compHom Q.residueFieldReduction.V (algebraMap k k[G])
  letI : IsScalarTower k k[G] Q.residueFieldReduction.V :=
    IsScalarTower.of_compHom k k[G] Q.residueFieldReduction.V
  have hQas :
      Nonempty
        (asModule Q.residueFieldReduction.toFiniteRep.ρ ≃ₗ[k[G]] Q.residueFieldReduction.V) := by
    change Nonempty
      ((Representation.ofModule (ModuleCat.of k[G] Q.residueFieldReduction.V)).asModule ≃ₗ[k[G]]
        Q.residueFieldReduction.V)
    let Mmod : ModuleCat k[G] := ModuleCat.of k[G] Q.residueFieldReduction.V
    let toFun : (Representation.ofModule Mmod).asModule → Q.residueFieldReduction.V := fun x ↦
      (RestrictScalars.addEquiv k k[G] Q.residueFieldReduction.V)
        ((Representation.ofModule Mmod).asModuleEquiv x)
    let invFun : Q.residueFieldReduction.V → (Representation.ofModule Mmod).asModule := fun x ↦
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
          simp [toFun, Mmod]
        map_smul' := by
          intro r x
          exact Representation.smul_ofModule_asModule (M := Mmod) r x }⟩
  have hQowner :
      Nonempty (Q.residueFieldReduction.V ≃ₗ[k[G]] (k ⊗[A] Q.V)) := by
    simpa [FiniteProjectiveGroupAlgebraModule.residueFieldReduction,
      FiniteProjectiveGroupAlgebraModule.V] using
        (show Nonempty ((k ⊗[A] Q.V) ≃ₗ[k[G]] (k ⊗[A] Q.V)) from
          ⟨LinearEquiv.refl k[G] (k ⊗[A] Q.V)⟩)
  rcases hQas with ⟨eQas⟩
  rcases hQowner with ⟨eQowner⟩
  let eQ : asModule Q.residueFieldReduction.toFiniteRep.ρ ≃ₗ[k[G]] (k ⊗[A] Q.V) :=
    eQas.trans eQowner
  -- Route correction: compare the two `FDRep` owners through explicit `asModule` bridges, so the
  -- exact tensor-product carrier is only exposed once.
  refine
    fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv_local_support
      (G := G) ?_
  refine ⟨eL.trans (ered.trans eQ.symm)⟩

/-- Helper for Proposition 15-15.5-1: an honest projective scalar extension carries the literal
stable lattice whose reduction is exactly the intrinsic residue-field reduction of the original
projective module. -/
-- Route correction: this existential witness is now a corollary of the exact-owner reduction
-- comparison on the fixed literal range lattice.
theorem projective_scalarExtension_literal_reduction_class_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    ∃ L : StableLattice A (Q.scalarExtension K).ρ,
      [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀ := by
  let L :=
    projective_scalarExtension_literal_range_stableLattice_local_support
      (A := A) (K := K) (G := G) Q
  refine ⟨L, ?_⟩
  -- Package the fixed literal lattice with the already proved reduction isomorphism.
  exact
    finiteRepGrothendieckClass_eq_of_nonempty_iso
      (L := k) (G := G)
      (projective_scalarExtension_literal_range_reduction_iso_local_support
        (A := A) (K := K) (G := G) Q)

/-- Helper for Proposition 15-15.5-1: rebundling an `FDRep` from its underlying representation
does not change its isomorphism class. -/
private noncomputable def fdRepIsoOfRho_local_support
    (τ : FDRep K G) : τ ≅ FDRep.of τ.ρ :=
  Action.mkIso (Iso.refl _) fun g => by
    -- Rebundling preserves the underlying carrier and the action pointwise.
    ext x
    rfl

/-- Helper for Proposition 15-15.5-1: the restricted `A`-action on a rebundled `FDRep` carrier
forms the expected scalar tower over `K`. -/
private theorem fdRep_compHom_isScalarTower_local_support
    (V : FDRep K G) :
    letI : Module A V.V := Module.compHom V.V (algebraMap A K)
    IsScalarTower A K V.V := by
  letI : Module A V.V := Module.compHom V.V (algebraMap A K)
  refine IsScalarTower.of_algebraMap_smul ?_
  intro a x
  show ((algebraMap A K a) • x : V.V) =
    @SMul.smul A V.V (Module.compHom V.V (algebraMap A K)).toSMul a x
  rfl

/-- Helper for Proposition 15-15.5-1: rebuild the literal range lattice on the default
restrict-scalars `A`-module owner carried by `Q.scalarExtension K`. -/
private noncomputable def
    projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    StableLattice A (FDRep.of (Q.scalarExtension K).ρ).ρ := by
  let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
  let L :=
    projective_scalarExtension_literal_range_stableLattice_local_support
      (A := A) (K := K) (G := G) Q
  refine
    { toSubmodule :=
        { carrier := (L.toSubmodule : Set V.V)
          zero_mem' := L.toSubmodule.zero_mem
          add_mem' := fun hx hy ↦ L.toSubmodule.add_mem hx hy
          smul_mem' := fun a x hx ↦ by
            -- The restrict-scalars `A`-action on `FDRep.of (Q.scalarExtension K).ρ` is the
            -- ambient tensor-product action used to define the literal lattice.
            simpa [Algebra.smul_def] using L.toSubmodule.smul_mem a hx }
      apply_mem_toSubmodule := ?_
      isLattice := ?_ }
  · intro g x hx
    exact L.apply_mem_toSubmodule g hx
  · simpa using L.isLattice

/-- Helper for Proposition 15-15.5-1: after rebuilding the literal range lattice on the default
`FDRep` owner, its reduction class is still the intrinsic residue-field reduction of `Q`. -/
private theorem
    projective_scalarExtension_literal_range_reduction_class_fdrep_owner_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let L :=
      projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local_support
        (A := A) (K := K) (G := G) Q
    [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀ := by
  -- The exact-owner rebundling does not change the literal lattice or its reduced class.
  simpa [projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local_support] using
    finiteRepGrothendieckClass_eq_of_nonempty_iso
      (L := k) (G := G)
      (projective_scalarExtension_literal_range_reduction_iso_local_support
        (A := A) (K := K) (G := G) Q)

/-- Helper for Proposition 15-15.5-1: LinearRepresentations_Serre_1977's literal scalar-extension lattice can be chosen on
the exact `FDRep.of` owner used by the decomposition-map computation, and its reduction class is
the intrinsic residue-field reduction of `Q`. -/
theorem projective_scalarExtension_literal_reduction_class_fdrep_owner_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    ∃ L : StableLattice A (FDRep.of (Q.scalarExtension K).ρ).ρ,
      [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀ := by
  let L :=
    projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local_support
      (A := A) (K := K) (G := G) Q
  refine ⟨L, ?_⟩
  -- Package the already constructed exact-owner literal lattice with its fixed reduction class.
  simpa [L] using
    projective_scalarExtension_literal_range_reduction_class_fdrep_owner_local_support
      (A := A) (K := K) (G := G) Q

/-- Helper for Proposition 15-15.5-1: restate the rebundled literal lattice on a `let`-bound
`FDRep` owner so later applications pick the canonical restrict-scalars instance. -/
private noncomputable def
    projective_scalarExtension_literal_range_stableLattice_fdrep_default_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    StableLattice A (FDRep.of (Q.scalarExtension K).ρ).ρ := by
  let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
  let L :=
    projective_scalarExtension_literal_range_stableLattice_local_support
      (A := A) (K := K) (G := G) Q
  refine
    { toSubmodule :=
        { carrier := (L.toSubmodule : Set V.V)
          zero_mem' := L.toSubmodule.zero_mem
          add_mem' := fun hx hy ↦ L.toSubmodule.add_mem hx hy
          smul_mem' := fun a x hx ↦ by
            -- The canonical restrict-scalars action on the rebundled owner is still scalar
            -- multiplication through `A → K`.
            simpa [Algebra.smul_def] using L.toSubmodule.smul_mem a hx }
      apply_mem_toSubmodule := ?_
      isLattice := ?_ }
  · intro g x hx
    exact L.apply_mem_toSubmodule g hx
  · simpa using L.isLattice

/-- Helper for Proposition 15-15.5-1: the `let`-bound exact-owner rebundling keeps the same
reduction class as the intrinsic residue-field reduction of `Q`. -/
private theorem
    projective_scalarExtension_literal_range_reduction_class_fdrep_default_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    [FDRep.of
      (projective_scalarExtension_literal_range_stableLattice_fdrep_default_local_support
        (A := A) (K := K) (G := G) Q).reductionRepresentation]₀ =
      [Q.residueFieldReduction.toFiniteRep]₀ := by
  -- The `let`-bound rebundling changes only the owner packaging, not the underlying lattice.
  simpa [projective_scalarExtension_literal_range_stableLattice_fdrep_default_local_support] using
    projective_scalarExtension_literal_range_reduction_class_fdrep_owner_local_support
      (A := A) (K := K) (G := G) Q

/-- Helper for Proposition 15-15.5-1: the literal range on the source owner and on the
`FDRep.of` default owner already define the same reduction class. -/
private theorem
    projective_scalarExtension_literal_range_reduction_class_agrees_with_fdrep_default_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let Lsrc :=
      projective_scalarExtension_literal_range_stableLattice_local_support
        (A := A) (K := K) (G := G) Q
    let Ldst :=
      projective_scalarExtension_literal_range_stableLattice_fdrep_default_local_support
        (A := A) (K := K) (G := G) Q
    [FDRep.of Lsrc.reductionRepresentation]₀ = [FDRep.of Ldst.reductionRepresentation]₀ := by
  -- Both literal lattices reduce to LinearRepresentations_Serre_1977's intrinsic residue-field reduction of `Q`, so their
  -- Grothendieck classes coincide before any exact-owner transport is applied.
  calc
    [FDRep.of
        (projective_scalarExtension_literal_range_stableLattice_local_support
          (A := A) (K := K) (G := G) Q).reductionRepresentation]₀ =
        [Q.residueFieldReduction.toFiniteRep]₀ := by
          exact
            finiteRepGrothendieckClass_eq_of_nonempty_iso
              (L := k) (G := G)
              (projective_scalarExtension_literal_range_reduction_iso_local_support
                (A := A) (K := K) (G := G) Q)
    _ =
        [FDRep.of
          (projective_scalarExtension_literal_range_stableLattice_fdrep_default_local_support
            (A := A) (K := K) (G := G) Q).reductionRepresentation]₀ := by
          symm
          simpa using
            projective_scalarExtension_literal_range_reduction_class_fdrep_default_local_support
              (A := A) (K := K) (G := G) Q

/-- Helper for Proposition 15-15.5-1: the `let`-bound rebundling on `FDRep.of` keeps the literal
range submodule unchanged as an `A`-module. -/
private noncomputable def
    projective_scalarExtension_literal_range_submoduleEquiv_fdrep_default_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    (projective_scalarExtension_literal_range_stableLattice_local_support
      (A := A) (K := K) (G := G) Q).toSubmodule ≃ₗ[A]
      (projective_scalarExtension_literal_range_stableLattice_fdrep_default_local_support
        (A := A) (K := K) (G := G) Q).toSubmodule := by
  -- The `let`-bound rebundling only changes how Lean names the owner, so the identity map on the
  -- shared carrier gives the required linear equivalence.
  refine
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      invFun := fun x ↦ ⟨x.1, x.2⟩
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro x
        rfl
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro a x
        rfl }

/-- Helper for Proposition 15-15.5-1: rebundling `Q.scalarExtension K` as `FDRep.of` keeps the
literal range unchanged as an `A[G]`-submodule. -/
private noncomputable def
    projective_scalarExtension_literal_range_submoduleEquiv_groupAlgebra_fdrep_owner_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    (projective_scalarExtension_literal_range_stableLattice_local_support
      (A := A) (K := K) (G := G) Q).toSubmodule ≃ₗ[A[G]]
      (projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local_support
        (A := A) (K := K) (G := G) Q).toSubmodule := by
  -- The rebundled owner has the same carrier subset and the same `A[G]`-action, so the identity
  -- map is already the required `A[G]`-linear equivalence.
  refine
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      invFun := fun x ↦ ⟨x.1, x.2⟩
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro x
        rfl
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro r x
        rfl }

/-- Helper for Proposition 15-15.5-1: rebundling `Q.scalarExtension K` as `FDRep.of` does not
change the literal-range lattice as an `A`-submodule. -/
private noncomputable def
    projective_scalarExtension_literal_range_submoduleEquiv_fdrep_owner_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    (projective_scalarExtension_literal_range_stableLattice_local_support
      (A := A) (K := K) (G := G) Q).toSubmodule ≃ₗ[A]
      (projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local_support
        (A := A) (K := K) (G := G) Q).toSubmodule := by
  refine
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      invFun := fun x ↦ ⟨x.1, x.2⟩
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro x
        rfl
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro a x
        rfl }

/-- Helper for Proposition 15-15.5-1: rebundling `Q.scalarExtension K` as `FDRep.of` does not
change the generic Grothendieck class seen by `decompositionHom`. -/
private theorem finiteRepClass_projective_scalarExtension_eq_fdrepOfRho_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    [Q.scalarExtension K]₀ = [FDRep.of (Q.scalarExtension K).ρ]₀ := by
  -- Rebundling keeps the generic scalar-extension class unchanged in the Grothendieck group.
  rw [finiteRepGrothendieckClass_eq_of_nonempty_iso
    (L := K) (G := G) ⟨fdRepIsoOfRho_local_support (τ := Q.scalarExtension K)⟩]

/-- Helper for Proposition 15-15.5-1: rebundling `Q.scalarExtension K` as `FDRep.of` does not
change the generic Grothendieck class seen by `decompositionHom`. -/
private theorem decompositionHom_projective_scalarExtension_class_eq_fdrepOfRho_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    decompositionHom A K G [Q.scalarExtension K]₀ =
      decompositionHom A K G [FDRep.of (Q.scalarExtension K).ρ]₀ := by
  -- `FDRep.of` only repackages the same scalar-extended representation, so the input class is
  -- unchanged before we evaluate `decompositionHom`.
  rw [finiteRepClass_projective_scalarExtension_eq_fdrepOfRho_local_support
    (A := A) (K := K) (G := G) Q]

/-- Helper for Proposition 15-15.5-1: the source-owner literal lattice and the rebundled
`FDRep.of` literal lattice already determine the same reduced Grothendieck class. -/
private theorem projective_scalarExtension_literal_range_reduction_class_agrees_with_fdrep_owner_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let Lsrc :=
      projective_scalarExtension_literal_range_stableLattice_local_support
        (A := A) (K := K) (G := G) Q
    let Ldst :=
      projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local_support
        (A := A) (K := K) (G := G) Q
    [FDRep.of Lsrc.reductionRepresentation]₀ = [FDRep.of Ldst.reductionRepresentation]₀ := by
  -- Both literal lattices reduce to LinearRepresentations_Serre_1977's intrinsic residue-field reduction of `Q`, so their
  -- reduced classes agree before the exact-owner transport issue enters.
  calc
    [FDRep.of
        (projective_scalarExtension_literal_range_stableLattice_local_support
          (A := A) (K := K) (G := G) Q).reductionRepresentation]₀ =
        [Q.residueFieldReduction.toFiniteRep]₀ := by
          exact
            finiteRepGrothendieckClass_eq_of_nonempty_iso
              (L := k) (G := G)
              (projective_scalarExtension_literal_range_reduction_iso_local_support
                (A := A) (K := K) (G := G) Q)
    _ =
        [FDRep.of
          (projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local_support
            (A := A) (K := K) (G := G) Q).reductionRepresentation]₀ := by
          symm
          simpa using
            projective_scalarExtension_literal_range_reduction_class_fdrep_owner_local_support
              (A := A) (K := K) (G := G) Q

/-- Helper for Proposition 15-15.5-1: after rebundling the scalar extension through a `let`-bound
`FDRep.of` owner, the decomposition map is still computed by the fixed literal stable lattice. -/
private theorem decompositionHom_fdrepOf_scalarExtension_eq_literal_reduction_class_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    decompositionHom A K G [FDRep.of (Q.scalarExtension K).ρ]₀ =
      [Q.residueFieldReduction.toFiniteRep]₀ := by
  let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
  obtain ⟨L, hL⟩ :=
    projective_scalarExtension_literal_reduction_class_fdrep_owner_support
      (A := A) (K := K) (G := G) Q
  letI : SMul A V.V := SMul.comp (M := K) (N := A) (α := V.V) (algebraMap A K)
  letI : Module A V.V := Module.compHom V.V (algebraMap A K)
  letI : IsScalarTower A K V.V :=
    fdRep_compHom_isScalarTower_local_support (A := A) (K := K) (G := G) V
  have Lcanon : StableLattice A V.ρ := by
    refine
      { toSubmodule :=
          { carrier := (L.toSubmodule : Set V.V)
            zero_mem' := L.toSubmodule.zero_mem
            add_mem' := fun hx hy ↦ L.toSubmodule.add_mem hx hy
            smul_mem' := ?_ }
        apply_mem_toSubmodule := ?_
        isLattice := ?_ }
    · intro a x hx
      simpa [Module.compHom, Algebra.smul_def] using
        L.toSubmodule.smul_mem a hx
    · intro g x hx
      exact L.apply_mem_toSubmodule g hx
    · simpa using L.isLattice
  have hLcanon : [FDRep.of Lcanon.reductionRepresentation]₀ =
      [Q.residueFieldReduction.toFiniteRep]₀ := by
    simpa [V, Lcanon] using hL
  -- Compute `decompositionHom` from the canonical exact-owner literal lattice witness, then
  -- identify its reduction class with the intrinsic residue-field reduction of `Q`.
  calc
    decompositionHom A K G [FDRep.of (Q.scalarExtension K).ρ]₀ =
        [FDRep.of Lcanon.reductionRepresentation]₀ := by
          simpa [V] using
            (decompositionHom_finiteRepClass_eq
              (A := A) (K := K) (G := G) V Lcanon)
    _ = [Q.residueFieldReduction.toFiniteRep]₀ := hLcanon

/-- Helper for Proposition 15-15.5-1: LinearRepresentations_Serre_1977's literal scalar-extension lattice computes the
decomposition class of a projective generic fiber as the finite-representation class of its
intrinsic residue-field reduction. -/
theorem decompositionHom_projective_scalarExtension_class_eq_residueFieldReduction_finiteRepClass_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    decompositionHom A K G [Q.scalarExtension K]₀ =
      [Q.residueFieldReduction.toFiniteRep]₀ := by
  -- First rebundle the scalar extension through `FDRep.of`; this does not change the source class.
  calc
    decompositionHom A K G [Q.scalarExtension K]₀ =
        decompositionHom A K G [FDRep.of (Q.scalarExtension K).ρ]₀ := by
          exact
            decompositionHom_projective_scalarExtension_class_eq_fdrepOfRho_local_support
              (A := A) (K := K) (G := G) Q
    -- Next evaluate `decompositionHom` using the exact-owner literal lattice witness.
    _ = [Q.residueFieldReduction.toFiniteRep]₀ := by
          exact
            decompositionHom_fdrepOf_scalarExtension_eq_literal_reduction_class_local_support
              (A := A) (K := K) (G := G) Q

/-- Helper for Proposition 15-15.5-1: the exact-owner `A`-action on the scalar extension of a
projective module is the composed action along `A → K`, and together with the ambient `K`-action
it forms the scalar tower needed for the rebundled `FDRep` owner. -/
private theorem projective_scalarExtension_compHom_isScalarTower_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let V : FDRep K G := Q.scalarExtension K
    letI : SMul A K := SMul.comp (M := K) (N := A) (α := K) (algebraMap A K)
    letI : SMul A V.V := SMul.comp (M := K) (N := A) (α := V.V) (algebraMap A K)
    letI : Module A V.V := Module.compHom V.V (algebraMap A K)
    IsScalarTower A K V.V := by
  let V : FDRep K G := Q.scalarExtension K
  letI : SMul A K := SMul.comp (M := K) (N := A) (α := K) (algebraMap A K)
  letI : SMul A V.V := SMul.comp (M := K) (N := A) (α := V.V) (algebraMap A K)
  letI : Module A V.V := Module.compHom V.V (algebraMap A K)
  -- The composed `A`-action is exactly the one transported along `A → K`, so the standard
  -- `SMul.comp.isScalarTower` theorem packages the required scalar tower on the rebundled owner.
  exact SMul.comp.isScalarTower (M := K) (N := A) (α := K) (β := V.V) (g := algebraMap A K)

/-- Helper for Proposition 15-15.5-1: the fixed literal-range lattice already has the same
Grothendieck class as the intrinsic residue-field reduction of `Q`. -/
private theorem projective_scalarExtension_literal_range_reduction_class_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let L :=
      projective_scalarExtension_literal_range_stableLattice_local_support
        (A := A) (K := K) (G := G) Q
    [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀ := by
  -- Package the previously constructed reduction isomorphism as an equality of Grothendieck
  -- classes for LinearRepresentations_Serre_1977's fixed literal lattice.
  simpa using
    finiteRepGrothendieckClass_eq_of_nonempty_iso
      (L := k) (G := G)
      (projective_scalarExtension_literal_range_reduction_iso_local_support
        (A := A) (K := K) (G := G) Q)

end

end Representation
