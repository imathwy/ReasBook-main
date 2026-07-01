import Mathlib
import Serre.Chap14.Corollary_14_14_4_3.GrothendieckBasics
import Serre.Chap14.Proposition_14_14_3_1
import Serre.Chap14.Infra_14_4_ProjectiveLift
import Serre.Chap15.Definition_15_15_1_1
import Serre.Chap15.Definition_15_15_3_1
import Serre.Chap15.Theorem_15_15_2_2

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

/-- Helper for Infra 16 1 DecompositionSurjectivity: the literal scalar-extension map sends `x` to
the pure tensor `1 ⊗ x` inside `Q.scalarExtension K`. -/
private abbrev projective_scalarExtension_literal_map
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Q.V →ₗ[A] K ⊗[A] Q.V :=
  TensorProduct.mk A K Q.V 1

/-- Helper for Infra 16 1 DecompositionSurjectivity: over the fraction field, the literal map
`x ↦ 1 ⊗ x` is injective. -/
private theorem projective_scalarExtension_literal_map_injective
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Function.Injective
      (projective_scalarExtension_literal_map (A := A) (K := K) (G := G) Q) := by
  intro x y hxy
  letI : Module.Free A Q.V := Module.free_of_flat_of_isLocalRing (R := A) (P := Q.V)
  let b : Module.Basis (Module.Free.ChooseBasisIndex A Q.V) A Q.V :=
    Module.Free.chooseBasis A Q.V
  apply b.repr.injective
  ext i
  have hcoord :=
    congrArg ((Algebra.TensorProduct.basis K b).repr · i) hxy
  simpa [projective_scalarExtension_literal_map, Algebra.TensorProduct.basis] using hcoord

/-- Helper for Infra 16 1 DecompositionSurjectivity: the image of `x ↦ 1 ⊗ x` is stable under the
scalar-extended `G`-action. -/
private theorem projective_scalarExtension_literal_map_apply_mem_range
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (g : G) {x : K ⊗[A] Q.V}
    (hx :
      x ∈
        (projective_scalarExtension_literal_map (A := A) (K := K) (G := G) Q).range) :
    (Q.scalarExtension K).ρ g x ∈
      (projective_scalarExtension_literal_map (A := A) (K := K) (G := G) Q).range := by
  rcases hx with ⟨y, rfl⟩
  -- Rewrite the scalar-extended action on a pure tensor and keep the source vector upstairs.
  refine ⟨Q.toRep g y, ?_⟩
  ext
  simp [projective_scalarExtension_literal_map, Representation.ofModule',
    MonoidAlgebra.tensorProduct_mk_map_monoidAlgebra_of]

/-- Helper for Infra 16 1 DecompositionSurjectivity: the literal image of `Q.V` inside
`Q.scalarExtension K` spans the scalar extension over `K` and is finite over `A`, hence is a
stable lattice. -/
private theorem projective_scalarExtension_literal_map_range_isLattice
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Submodule.IsLattice K
      ((projective_scalarExtension_literal_map (A := A) (K := K) (G := G) Q).range) := by
  refine
    { fg := ?_
      span_eq_top := ?_ }
  · -- Finite generation is inherited from the finite `A`-module `Q.V`.
    have hfg_top : (⊤ : Submodule A Q.V).FG := by
      exact (Module.Finite.iff_fg (N := (⊤ : Submodule A Q.V))).1 inferInstance
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map
      (projective_scalarExtension_literal_map (A := A) (K := K) (G := G) Q) hfg_top
  · letI : Module.Free A Q.V := Module.free_of_flat_of_isLocalRing (R := A) (P := Q.V)
    let b := Module.Free.chooseBasis A Q.V
    -- The tensor-product basis `1 ⊗ b_i` already lies in the range, so the `K`-span is all of
    -- `K ⊗[A] Q.V`.
    apply eq_top_iff.2
    intro x hx
    have hxrepr : x = (Algebra.TensorProduct.basis K b).sum_repr x :=
      ((Algebra.TensorProduct.basis K b).sum_repr x).symm
    rw [hxrepr]
    refine Submodule.sum_mem _ ?_
    intro i hi
    have hi' :
        (Algebra.TensorProduct.basis K b) i ∈
          Submodule.span K
            (((projective_scalarExtension_literal_map
                (A := A) (K := K) (G := G) Q).range :
                Submodule A (K ⊗[A] Q.V)) :
              Set (K ⊗[A] Q.V)) := by
      apply Submodule.subset_span
      refine ⟨b i, ?_⟩
      simp [projective_scalarExtension_literal_map, Algebra.TensorProduct.basis]
    exact Submodule.smul_mem _ _ hi'

/-- Helper for Infra 16 1 DecompositionSurjectivity: the literal image of `Q.V` inside
`Q.scalarExtension K` defines the stable lattice used in Serre's honest-projective calculation. -/
private noncomputable def projective_scalarExtension_literal_stableLattice
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    StableLattice A (Q.scalarExtension K).ρ :=
  { toSubmodule :=
      (projective_scalarExtension_literal_map (A := A) (K := K) (G := G) Q).range
    apply_mem_toSubmodule :=
      projective_scalarExtension_literal_map_apply_mem_range
        (A := A) (K := K) (G := G) Q
    isLattice :=
      projective_scalarExtension_literal_map_range_isLattice
        (A := A) (K := K) (G := G) Q }

/-- Helper for Infra 16 1 DecompositionSurjectivity: restricting the literal map to its image is
bijective. -/
private theorem projective_scalarExtension_literal_map_rangeRestrict_bijective
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Function.Bijective
      (projective_scalarExtension_literal_map (A := A) (K := K) (G := G) Q).rangeRestrict := by
  constructor
  · exact
      (LinearMap.injective_rangeRestrict_iff
        (f := projective_scalarExtension_literal_map (A := A) (K := K) (G := G) Q)).2
        (projective_scalarExtension_literal_map_injective
          (A := A) (K := K) (G := G) Q)
  · exact LinearMap.surjective_rangeRestrict
      (projective_scalarExtension_literal_map (A := A) (K := K) (G := G) Q)

/-- Helper for Infra 16 1 DecompositionSurjectivity: the literal source module `Q.V` identifies
`A`-linearly with its image inside `Q.scalarExtension K`. -/
private noncomputable def projective_scalarExtension_literal_rangeEquiv
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Q.V ≃ₗ[A]
      (projective_scalarExtension_literal_stableLattice
        (A := A) (K := K) (G := G) Q).toSubmodule :=
  LinearEquiv.ofBijective
    (projective_scalarExtension_literal_map (A := A) (K := K) (G := G) Q).rangeRestrict
    (projective_scalarExtension_literal_map_rangeRestrict_bijective
      (A := A) (K := K) (G := G) Q)

/-- Helper for Infra 16 1 DecompositionSurjectivity: the `A`-linear identification with the
literal range is in fact `A[G]`-linear. -/
private theorem projective_scalarExtension_literal_rangeEquiv_map_groupAlgebra
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (r : A[G]) (x : Q.V) :
    projective_scalarExtension_literal_rangeEquiv (A := A) (K := K) (G := G) Q (r • x) =
      r • projective_scalarExtension_literal_rangeEquiv (A := A) (K := K) (G := G) Q x := by
  -- Both sides are the same pure tensor after expanding the group-algebra action.
  ext
  simp [projective_scalarExtension_literal_rangeEquiv, projective_scalarExtension_literal_map,
    Algebra.smul_def, MonoidAlgebra.tensorProduct_mk_map_monoidAlgebra_of]

/-- Helper for Infra 16 1 DecompositionSurjectivity: the literal source module `Q.V` identifies
with the lattice range as an `A[G]`-module. -/
private noncomputable def projective_scalarExtension_literal_rangeLinearEquiv
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Q.V ≃ₗ[A[G]]
      (projective_scalarExtension_literal_stableLattice
        (A := A) (K := K) (G := G) Q).toSubmodule :=
  { toLinearMap :=
      (projective_scalarExtension_literal_rangeEquiv
        (A := A) (K := K) (G := G) Q).toLinearMap
    invFun :=
      (projective_scalarExtension_literal_rangeEquiv
        (A := A) (K := K) (G := G) Q).symm
    left_inv :=
      (projective_scalarExtension_literal_rangeEquiv
        (A := A) (K := K) (G := G) Q).left_inv
    right_inv :=
      (projective_scalarExtension_literal_rangeEquiv
        (A := A) (K := K) (G := G) Q).right_inv
    map_smul' :=
      projective_scalarExtension_literal_rangeEquiv_map_groupAlgebra
        (A := A) (K := K) (G := G) Q }

/-- Helper for Infra 16 1 DecompositionSurjectivity: the literal lattice range is projective over
`A[G]` because it is `A[G]`-linearly equivalent to `Q.V`. -/
private theorem projective_scalarExtension_literal_range_projective
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Module.Projective A[G]
      (projective_scalarExtension_literal_stableLattice
        (A := A) (K := K) (G := G) Q).toSubmodule := by
  let e :=
    projective_scalarExtension_literal_rangeLinearEquiv
      (A := A) (K := K) (G := G) Q
  -- Transport projectivity across the explicit `A[G]`-linear equivalence.
  simpa using
    Module.Projective.of_equiv
      (p := Q.V)
      (q := (projective_scalarExtension_literal_stableLattice
        (A := A) (K := K) (G := G) Q).toSubmodule)
      e.toLinearMap e.symm.toLinearMap

/-- Helper for Infra 16 1 DecompositionSurjectivity: the reduction of the literal stable lattice
is isomorphic, as a `k[G]`-representation, to the intrinsic residue-field reduction of `Q`. -/
private theorem projective_scalarExtension_literal_stableLattice_reduction_iso
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Nonempty
      (FDRep.of
          (projective_scalarExtension_literal_stableLattice
            (A := A) (K := K) (G := G) Q).reductionRepresentation ≅
        Q.residueFieldReduction.toFiniteRep) := by
  let L :=
    projective_scalarExtension_literal_stableLattice
      (A := A) (K := K) (G := G) Q
  let eAQ :=
    projective_scalarExtension_literal_rangeLinearEquiv
      (A := A) (K := K) (G := G) Q
  have hprojQ : Module.Projective A[G] Q.V := by infer_instance
  have hprojL : Module.Projective A[G] L.toSubmodule :=
    projective_scalarExtension_literal_range_projective
      (A := A) (K := K) (G := G) Q
  have hAQ :
      Nonempty (Q.V ≃ₗ[A[G]] L.toSubmodule) := ⟨eAQ⟩
  have hred : Nonempty (L.reduction ≃ₗ[k[G]] (k ⊗[A] Q.V)) := by
    -- Compare the two residue-field reduction realizations of the same projective `A[G]`-module:
    -- the tensor-product reduction of `Q.V`, and the quotient reduction of the literal lattice.
    simpa using
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
        (hf' := L.reduction_mkQ_isResidueFieldReduction)
        hprojQ hprojL).mp hAQ
  rcases hred with ⟨ered⟩
  let eRep : L.reductionRepresentation.Equiv (Representation.ofModule' (k ⊗[A] Q.V)) :=
    Representation.Equiv.mk ered fun g ↦ by
      -- The module linear equivalence intertwines the group action because it is `(k[G])`-linear.
      ext x
      exact ered.map_smul (MonoidAlgebra.of k G g) x
  let eFD :
      FDRep.of L.reductionRepresentation ≅ Q.residueFieldReduction.toFiniteRep :=
    ⟨(FDRep.forget₂HomLinearEquiv _ _) eRep.hom,
      (FDRep.forget₂HomLinearEquiv _ _) eRep.inv,
      by
        ext x
        exact eRep.left_inv x,
      by
        ext x
        exact eRep.right_inv x⟩
  exact ⟨eFD⟩

/-- Helper for Infra 16 1 DecompositionSurjectivity: the Grothendieck class of the reduction of
the literal stable lattice is the class of `Q.residueFieldReduction.toFiniteRep`. -/
private theorem projective_scalarExtension_literal_stableLattice_reduction_class
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    [FDRep.of
        (projective_scalarExtension_literal_stableLattice
          (A := A) (K := K) (G := G) Q).reductionRepresentation]₀ =
      [Q.residueFieldReduction.toFiniteRep]₀ := by
  exact
    finiteRepGrothendieckClass_eq_of_nonempty_iso
      (L := k) (G := G)
      (projective_scalarExtension_literal_stableLattice_reduction_iso
        (A := A) (K := K) (G := G) Q)

/-- Helper for Infra 16 1 DecompositionSurjectivity: an honest projective scalar extension carries
the literal stable lattice whose reduction is exactly the intrinsic residue-field reduction of the
original projective module. -/
theorem projective_scalarExtension_literal_reduction_class
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    ∃ L : StableLattice A (Q.scalarExtension K).ρ,
      [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀ := by
  refine
    ⟨projective_scalarExtension_literal_stableLattice (A := A) (K := K) (G := G) Q, ?_⟩
  -- The literal range lattice reduces to the canonical residue-field reduction of `Q`.
  exact
    projective_scalarExtension_literal_stableLattice_reduction_class
      (A := A) (K := K) (G := G) Q

end

end Representation
