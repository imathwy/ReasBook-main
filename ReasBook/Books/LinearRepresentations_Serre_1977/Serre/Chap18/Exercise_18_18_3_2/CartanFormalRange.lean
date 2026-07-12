import Mathlib
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_6
import LinearRepresentations_Serre_1977.Chap18.Definition_18_18_1_1
import LinearRepresentations_Serre_1977.Chap18.Proposition_18_18_1_2
import LinearRepresentations_Serre_1977.Chap18.Remark_18_18_1_3
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerCoordinateReadback
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanFormalRangeRegularValueSourceWorker
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.FinalSourceBlockerEquivalenceWorker

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section CartanCokernel

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]
variable {ι : Type x}

local instance :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Support bridge for Exercise 18-18.3-2: Serre's projective-character divisibility theorem,
transported through the `c = d ∘ e` triangle, identifies the full integral Cartan image with the
regular-class diagonal lattice up to an additive coordinate equivalence. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_projectiveCharacterLattice_support :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) →
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  intro hregular
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_regularValueSource
      (p := p) (k := k) (G := G) hregular

/-- Helper for Exercise 18-18.3-2: once the reindexed family is still coordinate-normalized and
its projective generators satisfy the Cartan generator formula, the distinguished Cartan matrix is
already the expected diagonal matrix. -/
theorem reindexed_cartanMatrix_diagonal_of_generator_formula
    [Fintype ι] [DecidableEq ι]
    (e : ι ≃ PRegularConjClass G p)
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ_coord :
      ∀ i : ι,
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π i]₀ =
          (Pi.single (e i) (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (hgen :
      ∀ i : ι,
        cartanCoordinateAddHom (p := p) (k := k) (G := G) [P i]ₚ₀ =
          scaled_regular_integer_indicator (p := p) (G := G) (e i)) :
    cartanMatrix k G
        (projectiveEnvelope_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete P hP_envelope)
        (simple_finiteRep_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete) =
      Matrix.diagonal (fun i : ι ↦ (ConjClasses.centralizerPPart p (e i).1 : ℤ)) := by
  classical
  let bP :=
    projectiveEnvelope_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete P hP_envelope
  let bR :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  have hcoord_repr :
      ∀ y : R₀[k](G), ∀ i : ι,
        bR.repr y i = regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) y (e i) := by
    intro y i
    have hcoord_sum :
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) y =
          ∑ j, (bR.repr y j) •
            (Pi.single (e j) (1 : ℤ) : PRegularConjClass G p → ℤ) := by
      calc
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) y =
            regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)
              (∑ j, (bR.repr y j) • bR j) := by
                rw [bR.sum_repr]
        _ =
            ∑ j, (bR.repr y j) •
              regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) (bR j) := by
                rw [map_sum]
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [map_zsmul]
        _ =
            ∑ j, (bR.repr y j) •
              (Pi.single (e j) (1 : ℤ) : PRegularConjClass G p → ℤ) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                refine congrArg (fun z ↦ (bR.repr y j) • z) ?_
                simpa [bR, simple_finiteRep_classes_basis_of_complete_family_apply] using
                  hπ_coord j
    have hvalue := congrArg (fun f : PRegularConjClass G p → ℤ ↦ f (e i)) hcoord_sum
    simpa [Pi.smul_apply, Pi.single_apply] using hvalue.symm
  ext j i
  have hvalue := congrArg (fun f : PRegularConjClass G p → ℤ ↦ f (e j)) (hgen i)
  calc
    cartanMatrix k G bP bR j i = bR.repr (cartanHom k G [P i]ₚ₀) j := by
      simp [cartanMatrix, bP, bR, Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply]
    _ = regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)
          (cartanHom k G [P i]ₚ₀) (e j) := by
            rw [hcoord_repr (cartanHom k G [P i]ₚ₀) j]
    _ = cartanCoordinateAddHom (p := p) (k := k) (G := G) [P i]ₚ₀ (e j) := rfl
    _ = Matrix.diagonal (fun i : ι ↦ (ConjClasses.centralizerPPart p (e i).1 : ℤ)) j i := by
          by_cases hji : j = i
          · subst hji
            simpa [scaled_regular_integer_indicator, Matrix.diagonal] using hvalue
          · have hne : e i ≠ e j := by
              intro hij
              exact hji (e.injective hij.symm)
            simpa [scaled_regular_integer_indicator, Matrix.diagonal, hji, hne] using hvalue

/-- Helper for Exercise 18-18.3-2: if two complete simple/projective families represent the same
Grothendieck basis classes indexwise, then their distinguished Cartan matrices coincide. -/
theorem cartanMatrix_eq_of_complete_family_class_equalities
    [Fintype ι] [DecidableEq ι]
    (π π₀ : ι → FDRep k G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ₀_pairwise : CategoryTheory.PairwiseNonisomorphic π₀)
    (hπ₀_complete : IsCompleteIrreducibleFamily π₀)
    (P P₀ : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (hP₀_envelope :
      ∀ i, ∃ f : (P₀ i).V →ₗ[k[G]] asModule (π₀ i).ρ, f.IsProjectiveEnvelope)
    (hπ_class : ∀ i : ι, ([π₀ i]₀ : R₀[k](G)) = [π i]₀)
    (hP_class : ∀ i : ι, ([P₀ i]ₚ₀ : P₀[k](G)) = [P i]ₚ₀) :
    cartanMatrix k G
        (projectiveEnvelope_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete P hP_envelope)
        (simple_finiteRep_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete) =
      cartanMatrix k G
        (projectiveEnvelope_classes_basis_of_complete_family
          π₀ hπ₀_pairwise hπ₀_complete P₀ hP₀_envelope)
        (simple_finiteRep_classes_basis_of_complete_family
          π₀ hπ₀_pairwise hπ₀_complete) := by
  let bP :=
    projectiveEnvelope_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete P hP_envelope
  let bP₀ :=
    projectiveEnvelope_classes_basis_of_complete_family
      π₀ hπ₀_pairwise hπ₀_complete P₀ hP₀_envelope
  let bR :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let bR₀ :=
    simple_finiteRep_classes_basis_of_complete_family π₀ hπ₀_pairwise hπ₀_complete
  have hbP : bP = bP₀ := by
    ext i
    -- The projective-envelope bases are identical once their basis vectors agree classwise.
    simpa [bP, bP₀, projectiveEnvelope_classes_basis_of_complete_family_apply] using
      (hP_class i).symm
  have hbR : bR = bR₀ := by
    ext i
    -- The same indexwise class equality identifies the complete-family simple bases.
    simpa [bR, bR₀, simple_finiteRep_classes_basis_of_complete_family_apply] using
      (hπ_class i).symm
  -- After the two basis families are identified, the Cartan matrices are definitionally the
  -- same matrix.
  show cartanMatrix k G bP bR = cartanMatrix k G bP₀ bR₀
  rw [hbP, hbR]

/-
/-- Helper for Exercise 18-18.3-2: after choosing the coordinate-normalized simple family, Serre's
mixed-character argument should supply projective envelopes whose Cartan images are the scaled
regular indicators. This is the exact generator package needed by the generic range theorem
already proved below. -/
private theorem
    exists_coordinate_normalized_projective_family_with_cartan_generator_formula :
    ∃ π : PRegularConjClass G p → FDRep k G,
      (∀ c, Simple (π c)) ∧
        (∀ c,
          regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π c]₀ =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∧
        ∃ P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G,
          (∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope) ∧
            (∀ c : PRegularConjClass G p,
              cartanCoordinateAddHom (p := p) (k := k) (G := G) [P c]ₚ₀ =
                scaled_regular_integer_indicator (p := p) (G := G) c) := by
  -- Once the single source-facing generator theorem is isolated, the existence package should use
  -- the coordinate-normalized family over `k` directly instead of transporting through an
  -- auxiliary residue-field owner.
  obtain ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope⟩ :=
    exists_coordinate_normalized_complete_family_with_projective_envelopes
      (p := p) (k := k) (G := G)
  refine ⟨π, hπ_simple, hπ_coord, P, hP_envelope, ?_⟩
  exact
    coordinate_normalized_projective_envelope_cartan_generator_formula
      (p := p) (k := k) (G := G) π hπ_simple hπ_coord P hP_envelope
-/

/-- Helper for Exercise 18-18.3-2: once the Cartan generator images are identified, the full
Cartan range becomes the diagonal lattice by a formal basis expansion. -/
theorem cartan_range_map_eq_regularIntegerDiagonal_of_generator_formula
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hgen :
      ∀ c : PRegularConjClass G p,
        cartanCoordinateAddHom (p := p) (k := k) (G := G) [P c]ₚ₀ =
          scaled_regular_integer_indicator (p := p) (G := G) c) :
    (cartanHom k G).range.map
        (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)).toAddMonoidHom =
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  classical
  let bP :=
    projectiveEnvelope_classes_basis_of_complete_family π hπ_pairwise hπ_complete P hP_envelope
  let f := cartanCoordinateAddHom (p := p) (k := k) (G := G)
  apply AddSubgroup.toIntSubmodule.injective
  apply le_antisymm
  · intro y hy
    rcases AddSubgroup.mem_map.1 hy with ⟨z, hz, rfl⟩
    rcases hz with ⟨x, rfl⟩
    change f x ∈ regularIntegerDiagonalSubmodule (p := p) (G := G)
    have hfx :
        f x = ∑ c, (bP.repr x c) • f (bP c) := by
      -- Expand `x` in the projective-envelope basis and push the additive Cartan-coordinate map
      -- through that basis expansion.
      symm
      calc
        ∑ c, (bP.repr x c) • f (bP c) = ∑ c, f ((bP.repr x c) • bP c) := by
          refine Finset.sum_congr rfl ?_
          intro c hc
          rw [map_zsmul]
        _ = f (∑ c, (bP.repr x c) • bP c) := by
          rw [map_sum]
        _ = f x := by
          rw [bP.sum_repr x]
    rw [hfx]
    refine Submodule.sum_mem _ ?_
    intro c hc
    have hc_eq :
        f (bP c) = scaled_regular_integer_indicator (p := p) (G := G) c := by
      simpa [f, bP, cartanCoordinateAddHom,
        projectiveEnvelope_classes_basis_of_complete_family_apply] using hgen c
    rw [hc_eq]
    rw [regularIntegerDiagonalSubmodule_eq_span_scaled_regular_integer_indicator (p := p) (G := G)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
  · rw [regularIntegerDiagonalSubmodule_eq_span_scaled_regular_integer_indicator (p := p) (G := G)]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, rfl⟩
    change scaled_regular_integer_indicator (p := p) (G := G) c ∈
      ((cartanHom k G).range.map
        (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)).toAddMonoidHom).toIntSubmodule
    have hc_mem :
        scaled_regular_integer_indicator (p := p) (G := G) c ∈
          (cartanHom k G).range.map
            (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)).toAddMonoidHom := by
      rw [← hgen c]
      exact AddSubgroup.mem_map.2 ⟨cartanHom k G [P c]ₚ₀, ⟨[P c]ₚ₀, rfl⟩, rfl⟩
    exact hc_mem

/-- Helper for Exercise 18-18.3-2: to identify the Cartan range with the diagonal integer
lattice, it is enough to prove the forward divisibility inclusion and realize every scaled
regular-class indicator in the range. -/
theorem cartan_range_map_eq_regularIntegerDiagonal_of_subset_and_scaled_indicators
    (hsubset :
      (cartanHom k G).range.map
          (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)).toAddMonoidHom ≤
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)
    (hscaled :
      ∀ c : PRegularConjClass G p,
        scaled_regular_integer_indicator (p := p) (G := G) c ∈
          (cartanHom k G).range.map
            (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)).toAddMonoidHom) :
    (cartanHom k G).range.map
        (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)).toAddMonoidHom =
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  -- Convert the additive-subgroup equality to the equivalent `ℤ`-submodule equality, where the
  -- diagonal lattice is already described as a span of scaled point masses.
  apply AddSubgroup.toIntSubmodule.injective
  apply le_antisymm
  · intro y hy
    exact hsubset hy
  · rw [regularIntegerDiagonalSubmodule_eq_span_scaled_regular_integer_indicator (p := p) (G := G)]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, rfl⟩
    exact hscaled c
end CartanCokernel

end Representation
