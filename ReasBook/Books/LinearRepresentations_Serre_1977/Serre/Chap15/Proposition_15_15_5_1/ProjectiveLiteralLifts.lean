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

section ProjectiveLiteralReductionLocal

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

end ProjectiveLiteralReductionLocal

/-- Helper for Proposition 15-15.5-1: the literal scalar-extension map sends `x` to the pure
tensor `1 ⊗ x` inside `Q.scalarExtension K`. -/
private abbrev projective_scalarExtension_literal_map_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Q.V →ₗ[A] K ⊗[A] Q.V :=
  TensorProduct.mk A K Q.V 1

/-- Helper for Proposition 15-15.5-1: over the fraction field, the literal map `x ↦ 1 ⊗ x` is
injective. -/
theorem projective_scalarExtension_literal_map_injective_local_support
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
    have hxrepr :
        x = ∑ i, ((Algebra.TensorProduct.basis K b).repr x) i •
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
stable lattice used in Serre's projective comparison. -/
noncomputable def projective_scalarExtension_literal_range_stableLattice_local_support
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
theorem nonempty_asModuleLinearEquiv_target_local_support
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

/-- Helper for Proposition 15-15.5-1: a `k[G]`-linear equivalence between the owner modules of two
finite-dimensional representations upgrades to an isomorphism in `FDRep k G`. -/
theorem fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv_local_support
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
  rcases _root_.projective_scalarExtension_literal_range_reduction_linearEquiv_local_support
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
          dsimp [toFun]
          rw [(Representation.ofModule Mmod).asModuleEquiv.map_add]
          exact (RestrictScalars.addEquiv k k[G] Q.residueFieldReduction.V).map_add _ _
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
      (_root_.projective_scalarExtension_literal_range_reduction_iso_local_support
        (A := A) (K := K) (G := G) Q)

/-- Helper for Proposition 15-15.5-1: `Q.scalarExtension K` should carry the literal stable
lattice coming from the image of `x ↦ 1 ⊗ x`, and that lattice should reduce to
`Q.residueFieldReduction.toFiniteRep`. -/
theorem projective_scalarExtension_literal_reduction_class_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    ∃ L : StableLattice A (Q.scalarExtension K).ρ,
      [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀ := by
  -- Reuse the literal-range reduction theorem proved in this file instead of delegating through
  -- the theorem-local support import.
  exact
    projective_scalarExtension_literal_reduction_class_support
      (A := A) (K := K) (G := G) Q

/-- Helper for Proposition 15-15.5-1: the `k[G]`-module underlying a finite-dimensional
representation. -/
private noncomputable abbrev fdRepAsModule (τ : FDRep k G) : ModuleCat k[G] :=
  Rep.toModuleMonoidAlgebra.obj ((forget₂ (FDRep k G) (Rep k G)).obj τ)

/-- Helper for Proposition 15-15.5-1: choose Serre's literal scalar-extension lattice on the
ambient scalar-extension owner once and for all. -/
private noncomputable def projective_scalarExtension_literal_stableLattice_source_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    StableLattice A (Q.scalarExtension K).ρ :=
  Classical.choose <|
    projective_scalarExtension_literal_reduction_class_local
      (A := A) (K := K) (G := G) Q

/-- Helper for Proposition 15-15.5-1: the chosen literal scalar-extension lattice on the ambient
owner reduces to the intrinsic residue-field reduction of `Q`. -/
private theorem projective_scalarExtension_literal_stableLattice_source_reduction_class_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let L :=
      projective_scalarExtension_literal_stableLattice_source_local
        (A := A) (K := K) (G := G) Q
    [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀ := by
  simpa [projective_scalarExtension_literal_stableLattice_source_local] using
    Classical.choose_spec <|
      projective_scalarExtension_literal_reduction_class_local
        (A := A) (K := K) (G := G) Q

/-- Helper for Proposition 15-15.5-1: restate the chosen literal scalar-extension lattice on the
default `FDRep.of` owner so later applications use the canonical restrict-scalars instance. -/
private noncomputable def projective_scalarExtension_literal_stableLattice_fdrep_default_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
    StableLattice A V.ρ := by
  let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
  let L :=
    projective_scalarExtension_literal_stableLattice_source_local
      (A := A) (K := K) (G := G) Q
  refine
    { toSubmodule :=
        { carrier := (L.toSubmodule : Set V.V)
          zero_mem' := L.toSubmodule.zero_mem
          add_mem' := fun hx hy ↦ L.toSubmodule.add_mem hx hy
          smul_mem' := fun a x hx ↦ by
            -- The canonical restrict-scalars action on the rebundled owner is still multiplication
            -- by the image of `a` in `K`.
            simpa [Algebra.smul_def] using L.toSubmodule.smul_mem a hx }
      apply_mem_toSubmodule := ?_
      isLattice := ?_ }
  · intro g x hx
    exact L.apply_mem_toSubmodule g hx
  · simpa using L.isLattice

/-- Helper for Proposition 15-15.5-1: the default-owner rebundling of the chosen literal
scalar-extension lattice keeps the same residue-field reduction class. -/
private theorem
    projective_scalarExtension_literal_stableLattice_fdrep_default_reduction_class_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
    let L :=
      projective_scalarExtension_literal_stableLattice_fdrep_default_local
        (A := A) (K := K) (G := G) Q
    [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀ := by
  -- Rebundling changes only the owner packaging, not the underlying literal lattice or its
  -- reduction class.
  simpa [projective_scalarExtension_literal_stableLattice_fdrep_default_local,
    projective_scalarExtension_literal_stableLattice_source_local] using
    projective_scalarExtension_literal_stableLattice_source_reduction_class_local
      (A := A) (K := K) (G := G) Q

/-- Helper for Proposition 15-15.5-1: package the rebundled literal lattice on the explicit
`FDRep.of (Q.scalarExtension K).ρ` owner so later theorems can use it without `let`-bound
transport noise. -/
private noncomputable def projective_scalarExtension_literal_stableLattice_fdrep_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    StableLattice A (FDRep.of (Q.scalarExtension K).ρ).ρ :=
  projective_scalarExtension_literal_stableLattice_fdrep_default_local
    (A := A) (K := K) (G := G) Q

/-- Helper for Proposition 15-15.5-1: the explicit-owner rebundling of the literal lattice keeps
the same residue-field reduction class. -/
private theorem projective_scalarExtension_literal_stableLattice_fdrep_owner_reduction_class_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    [FDRep.of
      (projective_scalarExtension_literal_stableLattice_fdrep_owner_local
        (A := A) (K := K) (G := G) Q).reductionRepresentation]₀ =
      [Q.residueFieldReduction.toFiniteRep]₀ := by
  -- The explicit-owner version is definitionally the previously proved default-owner rebundling.
  simpa [projective_scalarExtension_literal_stableLattice_fdrep_owner_local] using
    projective_scalarExtension_literal_stableLattice_fdrep_default_reduction_class_local
      (A := A) (K := K) (G := G) Q

/-- Helper for Proposition 15-15.5-1: the source of a projective envelope of a simple `k[G]`
module is finitely generated over `k[G]`. -/
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
    -- The chosen cyclic generator maps to a nonzero element of the simple target.
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
    -- Once the cyclic span is all of `P`, the canonical map from `k[G]` is onto.
    simpa [LinearMap.toSpanSingleton_apply] using
      (Submodule.span_singleton_eq_top_iff (R := k[G]) (x := x)).1 (by simpa [N] using hN_top)
  exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k[G] P x) hsurj

/-- Helper for Proposition 15-15.5-1: every simple finite-dimensional `k[G]`-representation
admits a finite projective envelope in the canonical owner category. -/
private theorem exists_finite_projective_envelope_of_simple_local
    (S : FDRep k G) [Simple S] :
    ∃ P : FiniteProjectiveGroupAlgebraModule k G,
      ∃ f : P.V →ₗ[k[G]] asModule S.ρ, f.IsProjectiveEnvelope := by
  let ρ : Representation k G S := S.ρ
  letI : Module k[G] S := by
    -- Expose the ambient `k[G]`-module structure carried by the owner `S`.
    simpa [ρ] using (inferInstance : Module k[G] ρ.asModule)
  letI : Representation.IsIrreducible ρ := by
    -- Categorical simplicity of `S` implies irreducibility of its bundled representation.
    simpa [ρ] using (FDRep.isIrreducible_of_simple S)
  letI : IsSimpleModule k[G] S := by
    -- The projective-envelope owner theorem is stated for `k[G]`-modules.
    simpa [ρ] using
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  let M : ModuleCat k[G] := ModuleCat.of k[G] S
  let _ : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing k[G] := IsArtinianRing.of_finite k k[G]
  obtain ⟨P', f', hf'⟩ := exists_isProjectiveEnvelope M
  have hfinite : Module.Finite k[G] P' :=
    moduleFinite_of_projectiveEnvelope_simple_local (G := G) (f := f'.hom) hf'
  let Pfg : FGModuleCat k[G] := by
    -- Repackage the envelope source as a finite projective owner.
    refine ⟨P', ?_⟩
    change Module.Finite k[G] P'
    exact hfinite
  have hproj : Module.Projective k[G] Pfg := by
    -- Projectivity is already part of the envelope source structure.
    change Module.Projective k[G] P'
    infer_instance
  let P : FiniteProjectiveGroupAlgebraModule k G := ⟨Pfg, hproj⟩
  refine ⟨P, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [ρ] using f'.hom
  · simpa [P, ρ] using hf'

/-- Helper for Proposition 15-15.5-1: under the prime-to-`p` hypothesis, a projective envelope
over `k[G]` is already isomorphic to its target because Maschke makes the target projective. -/
theorem finite_projective_envelope_toFiniteRep_iso_target_of_order_prime_to_p
    (hG : ¬ p ∣ Nat.card G)
    {π : FDRep k G}
    {P : FiniteProjectiveGroupAlgebraModule k G}
    {f : P.V →ₗ[k[G]] asModule π.ρ}
    (hf : f.IsProjectiveEnvelope) :
    Nonempty (P.toFiniteRep ≅ π) := by
  let M := fdRepAsModule π
  let _ : Module.Projective k[G] M := by
    let _ : Fintype G := Fintype.ofFinite G
    let _ : NeZero (Nat.card G : k) := NeZero.of_not_dvd k hG
    let _ : IsSemisimpleRing k[G] := by
      infer_instance
    exact Module.projective_of_isSemisimpleRing k[G] M
  let f' : P.V →ₗ[k[G]] M := by
    -- Re-express the envelope in the canonical `ModuleCat` owner of the target `FDRep`.
    simpa [fdRepAsModule] using f
  have hf' : f'.IsProjectiveEnvelope := by
    -- The projective-envelope structure is unchanged by that definitional rebundling.
    simpa [f', fdRepAsModule] using hf
  obtain ⟨e⟩ := hf'.nonempty_linearEquiv_target
  let eRep' : P.toRep ≅ ((forget₂ (FDRep k G) (Rep k G)).obj π) :=
    Rep.ofModuleMonoidAlgebra.mapIso e.toModuleIso ≪≫
      (Rep.unitIso ((forget₂ (FDRep k G) (Rep k G)).obj π)).symm
  let eRep : ((forget₂ (FDRep k G) (Rep k G)).obj P.toFiniteRep) ≅
      ((forget₂ (FDRep k G) (Rep k G)).obj π) := by
    -- `P.toFiniteRep` forgets to the same `Rep` owner as `P.toRep`.
    simpa [FiniteProjectiveGroupAlgebraModule.toFiniteRep,
      FiniteProjectiveGroupAlgebraModule.toRep] using eRep'
  -- Transport the recovered `Rep` isomorphism back to `FDRep`.
  refine ⟨⟨(FDRep.forget₂HomLinearEquiv P.toFiniteRep π) eRep.hom,
    (FDRep.forget₂HomLinearEquiv π P.toFiniteRep) eRep.inv, ?_, ?_⟩⟩
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change eRep.hom ≫ eRep.inv = 𝟙 _
    exact eRep.hom_inv_id
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change eRep.inv ≫ eRep.hom = 𝟙 _
    exact eRep.inv_hom_id

/-- Helper for Proposition 15-15.5-1: every simple `k[G]`-representation lifts to a finite
projective `A[G]`-module whose residue-field reduction is isomorphic to it. -/
theorem exists_projective_lift_reducing_to_simple_of_order_prime_to_p
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hG : ¬ p ∣ Nat.card G)
    (S : FDRep k G) [Simple S] :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G,
      Nonempty (Q.residueFieldReduction.toFiniteRep ≅ S) := by
  -- First package the simple target as an actual finite projective `k[G]`-module by taking a
  -- projective envelope and then using Maschke to identify the source with the target.
  obtain ⟨P, f, hf⟩ :=
    exists_finite_projective_envelope_of_simple_local (A := A) (G := G) S
  have hPS : Nonempty (P.toFiniteRep ≅ S) :=
    finite_projective_envelope_toFiniteRep_iso_target_of_order_prime_to_p
      (A := A) (p := p) (G := G) (π := S) (P := P) (f := f) hG hf
  -- Then lift that honest projective `k[G]`-module through the Chapter `14` owner theorem.
  obtain ⟨Q, hQP⟩ :=
    Representation.exists_projective_lift_of_residueField_projective
      (A := A) (G := G) P
  refine ⟨Q, ?_⟩
  have hQredP :
      Nonempty (Q.residueFieldReduction.toFiniteRep ≅ P.toFiniteRep) := by
    rcases
        (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
          (A := k) (G := G) Q.residueFieldReduction P).1 hQP with
      ⟨e⟩
    let eRep :
        ((forget₂ (FDRep k G) (Rep k G)).obj Q.residueFieldReduction.toFiniteRep) ≅
          ((forget₂ (FDRep k G) (Rep k G)).obj P.toFiniteRep) :=
      Rep.ofModuleMonoidAlgebra.mapIso e.toModuleIso
    -- Transport the recovered `Rep` isomorphism back to `FDRep`.
    refine ⟨⟨(FDRep.forget₂HomLinearEquiv _ _) eRep.hom,
      (FDRep.forget₂HomLinearEquiv _ _) eRep.inv, ?_, ?_⟩⟩
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.hom ≫ eRep.inv = 𝟙 _
      exact eRep.hom_inv_id
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.inv ≫ eRep.hom = 𝟙 _
      exact eRep.inv_hom_id
  rcases hQredP with ⟨eQredP⟩
  rcases hPS with ⟨ePS⟩
  -- Compose the lifted reduction identification with the envelope-source identification.
  exact ⟨eQredP.trans ePS⟩

end DecompositionHom
