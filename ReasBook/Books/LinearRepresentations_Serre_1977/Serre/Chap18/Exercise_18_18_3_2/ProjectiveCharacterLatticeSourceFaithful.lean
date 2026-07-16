import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeCokernelDescent
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CanonicalSourceProductSerreIntegralRepresentatives
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.IntegerDivisibilityDescent

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section ProjectiveCharacterLatticeSourceFaithful

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

local instance projectiveCharacterLatticeSourceFaithfulFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCharacterLatticeSourceFaithfulDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [Fintype ι] [DecidableEq ι] in
/-- A source-faithful sufficient theorem for the projective-character lattice congruence.

It allows an arbitrary additive choice of integer regular-class representatives `ρ`.  To recover
the fixed `regularClassCoordinateAddEquiv` representatives, it is enough that `ρ` agree with that
coordinate map modulo Serre's diagonal integer lattice.  This is weaker than forcing each Brauer
row to use its coordinate point mass. -/
theorem
    projectiveCharacterLatticeIntegerRepresentativeCongruence_of_additiveRepresentativeModuloDiagonal
    (ρ : R₀[k](G) →+ (PRegularConjClass G p → ℤ))
    (hρ :
      ∀ x : R₀[k](G),
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) (ρ x) ∈
            Submodule.map
              (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
              (projectiveCharacterSubmodule (A := A) (K := K) (G := G)))
    (hcoord :
      ∀ x : R₀[k](G),
        ρ x - (regularClassCoordinateAddEquiv (p := p) (G := G) x) ∈
          regularIntegerDiagonalSubmodule (p := p) (G := G)) :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (A := A) (K := K) (G := G) := by
  intro x
  let S : Submodule A (PRegularConjClass G p → K) :=
    Submodule.map
      (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
      (projectiveCharacterSubmodule (A := A) (K := K) (G := G))
  have hρx :
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
        regularIntegerFunctionCast (p := p) (K := K) (G := G) (ρ x) ∈ S := by
    simpa [S] using hρ x
  have hcoordD :
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (ρ x -
            regularClassCoordinateAddEquiv
              (p := p) (G := G) x) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
    regularIntegerFunctionCast_mem_regularValueDivisibilitySubmodule_of_mem
      (p := p) (A := A) (K := K) (G := G) (hcoord x)
  have hcoordS :
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (ρ x -
            regularClassCoordinateAddEquiv (p := p) (G := G) x) ∈ S := by
    simpa [S, (projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G))] using hcoordD
  have hdecomp :
      virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (regularClassCoordinateAddEquiv
            (p := p) (G := G) x) =
          (virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) (ρ x)) +
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (ρ x -
              regularClassCoordinateAddEquiv
                (p := p) (G := G) x) := by
    ext c
    simp [regularIntegerFunctionCast]
  rw [hdecomp]
  exact S.add_mem hρx hcoordS

set_option linter.style.longLine false in
omit [DecidableEq ι] in
/-- Serre 18.4 basis version of the previous sufficient theorem.

Each simple Brauer row may use an arbitrary integer representative `g i` modulo Serre's
projective-character lattice.  The only compatibility required with the fixed coordinates is that
the induced integer representative of a general virtual modular character agrees with
`regularClassCoordinateAddEquiv` modulo the diagonal integer lattice. -/
theorem projectiveCharacterLatticeIntegerRepresentativeCongruence_of_serreBasis_projectiveLatticeRepresentatives
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (g : ι → PRegularConjClass G p → ℤ)
    (hrow :
      ∀ i : ι,
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
            ([π i]₀ : R₀[k](G)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) (g i) ∈
            Submodule.map
              (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
              (projectiveCharacterSubmodule (A := A) (K := K) (G := G)))
    (hcompat :
      ∀ x : R₀[k](G),
        (∑ i : ι,
            ((simple_finiteRep_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete).repr x i) • g i) -
            (regularClassCoordinateAddEquiv (p := p) (G := G) x) ∈
          regularIntegerDiagonalSubmodule (p := p) (G := G)) :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (A := A) (K := K) (G := G) := by
  classical
  let χ : R₀[k](G) →+ (PRegularConjClass G p → K) :=
    virtualModularCharacterOnPRegularConjClass
      (p := p) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
  let S : Submodule A (PRegularConjClass G p → K) :=
    Submodule.map
      (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
      (projectiveCharacterSubmodule (A := A) (K := K) (G := G))
  let bR : Module.Basis ι ℤ R₀[k](G) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let ρ : R₀[k](G) →+ (PRegularConjClass G p → ℤ) :=
    { toFun := fun x => ∑ i : ι, ((bR.repr x) i) • g i
      map_zero' := by
        ext c
        simp
      map_add' := by
        intro x y
        ext c
        simp [Finset.sum_apply, Finset.sum_add_distrib, add_mul] }
  refine
    projectiveCharacterLatticeIntegerRepresentativeCongruence_of_additiveRepresentativeModuloDiagonal
      (p := p) (A := A) (K := K) (G := G) ρ ?_ ?_
  · intro x
    change χ x - regularIntegerFunctionCast (p := p) (K := K) (G := G) (ρ x) ∈ S
    have hx_expand :
        x = ∑ i : ι, ((bR.repr x) i) • ([π i]₀ : R₀[k](G)) := by
      calc
        x = ∑ i : ι, ((bR.repr x) i) • bR i := (bR.sum_repr x).symm
        _ = ∑ i : ι, ((bR.repr x) i) • ([π i]₀ : R₀[k](G)) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simp [bR, simple_finiteRep_classes_basis_of_complete_family_apply]
    have hχ_expand :
        χ x =
          ∑ i : ι, ((bR.repr x) i) • χ ([π i]₀ : R₀[k](G)) := by
      calc
        χ x = χ (∑ i : ι, ((bR.repr x) i) • ([π i]₀ : R₀[k](G))) := by
          exact congrArg χ hx_expand
        _ = ∑ i : ι, χ (((bR.repr x) i) • ([π i]₀ : R₀[k](G))) := by
          rw [map_sum]
        _ = ∑ i : ι, ((bR.repr x) i) • χ ([π i]₀ : R₀[k](G)) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [map_zsmul]
    have hcast_expand :
        regularIntegerFunctionCast (p := p) (K := K) (G := G) (ρ x) =
          ∑ i : ι,
            ((bR.repr x) i) •
              regularIntegerFunctionCast (p := p) (K := K) (G := G) (g i) := by
      change
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (∑ i : ι, ((bR.repr x) i) • g i) =
          ∑ i : ι,
            ((bR.repr x) i) •
              regularIntegerFunctionCast (p := p) (K := K) (G := G) (g i)
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [map_zsmul]
    have hdiff :
        χ x - regularIntegerFunctionCast (p := p) (K := K) (G := G) (ρ x) =
          ∑ i : ι,
            ((bR.repr x) i) •
              (χ ([π i]₀ : R₀[k](G)) -
                regularIntegerFunctionCast (p := p) (K := K) (G := G) (g i)) := by
      rw [hχ_expand, hcast_expand, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [zsmul_sub]
    rw [hdiff]
    refine Submodule.sum_mem S ?_
    intro i _hi
    exact S.toAddSubgroup.zsmul_mem (by simpa [S, χ] using hrow i) ((bR.repr x) i)
  · intro x
    change
      (∑ i : ι, ((bR.repr x) i) • g i) -
          regularClassCoordinateAddEquiv (p := p) (G := G) x ∈
        regularIntegerDiagonalSubmodule (p := p) (G := G)
    simpa [bR] using hcompat x

set_option linter.style.longLine false in
omit [DecidableEq ι] in
/-- Divisibility-lattice version of the Serre-basis sufficient theorem.

This is the form closest to Serre 18.5(a): the row representatives are checked in the
coordinatewise `p^{z(s)}` divisibility lattice, then converted to the projective-character lattice
by the formalized 18.5(a) equality. -/
theorem projectiveCharacterLatticeIntegerRepresentativeCongruence_of_serreBasis_divisibilityRepresentatives
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (g : ι → PRegularConjClass G p → ℤ)
    (hrow :
      ∀ i : ι,
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
            ([π i]₀ : R₀[k](G)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) (g i) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hcompat :
      ∀ x : R₀[k](G),
        (∑ i : ι,
            ((simple_finiteRep_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete).repr x i) • g i) -
            (regularClassCoordinateAddEquiv (p := p) (G := G) x) ∈
          regularIntegerDiagonalSubmodule (p := p) (G := G)) :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (A := A) (K := K) (G := G) :=
  projectiveCharacterLatticeIntegerRepresentativeCongruence_of_serreBasis_projectiveLatticeRepresentatives
    (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete g
    (by
      intro i
      simpa [(projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
        (p := p) (A := A) (K := K) (G := G))] using hrow i)
    hcompat

omit [HenselianLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [DecidableEq ι] in
/-- Rowwise compatibility with the fixed regular-class coordinates implies the global
compatibility hypothesis used by the Serre-basis sufficient theorem.

This is only the additive basis bookkeeping: it does not choose fixed point-mass witnesses or
Cartan columns. -/
theorem serreBasis_hcompat_of_rowwiseModuloDiagonal
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (g : ι → PRegularConjClass G p → ℤ)
    (hrowCompat :
      ∀ i : ι,
        g i -
            regularClassCoordinateAddEquiv (p := p) (G := G) ([π i]₀ : R₀[k](G)) ∈
          regularIntegerDiagonalSubmodule (p := p) (G := G)) :
    ∀ x : R₀[k](G),
      (∑ i : ι,
          ((simple_finiteRep_classes_basis_of_complete_family
              π hπ_pairwise hπ_complete).repr x i) • g i) -
          regularClassCoordinateAddEquiv (p := p) (G := G) x ∈
        regularIntegerDiagonalSubmodule (p := p) (G := G) := by
  classical
  let D : Submodule ℤ (PRegularConjClass G p → ℤ) :=
    regularIntegerDiagonalSubmodule (p := p) (G := G)
  let bR : Module.Basis ι ℤ R₀[k](G) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  intro x
  have hx_expand :
      x = ∑ i : ι, (bR.repr x i) • ([π i]₀ : R₀[k](G)) := by
    calc
      x = ∑ i : ι, (bR.repr x i) • bR i := (bR.sum_repr x).symm
      _ = ∑ i : ι, (bR.repr x i) • ([π i]₀ : R₀[k](G)) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        simp [bR, simple_finiteRep_classes_basis_of_complete_family_apply]
  have hcoord_expand :
      regularClassCoordinateAddEquiv (p := p) (G := G) x =
        ∑ i : ι,
          (bR.repr x i) •
            regularClassCoordinateAddEquiv (p := p) (G := G)
              ([π i]₀ : R₀[k](G)) := by
    calc
      regularClassCoordinateAddEquiv (p := p) (G := G) x =
          regularClassCoordinateAddEquiv (p := p) (G := G)
            (∑ i : ι, (bR.repr x i) • ([π i]₀ : R₀[k](G))) := by
            exact congrArg (regularClassCoordinateAddEquiv (p := p) (G := G)) hx_expand
      _ =
          ∑ i : ι,
            regularClassCoordinateAddEquiv (p := p) (G := G)
              ((bR.repr x i) • ([π i]₀ : R₀[k](G))) := by
            rw [map_sum]
      _ =
          ∑ i : ι,
            (bR.repr x i) •
              regularClassCoordinateAddEquiv (p := p) (G := G)
                ([π i]₀ : R₀[k](G)) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [map_zsmul]
  have hdiff :
      (∑ i : ι, (bR.repr x i) • g i) -
          regularClassCoordinateAddEquiv (p := p) (G := G) x =
        ∑ i : ι,
          (bR.repr x i) •
            (g i -
              regularClassCoordinateAddEquiv (p := p) (G := G)
                ([π i]₀ : R₀[k](G))) := by
    rw [hcoord_expand, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [zsmul_sub]
  rw [hdiff]
  refine Submodule.sum_mem D ?_
  intro i _hi
  exact zsmul_mem (by simpa [D] using hrowCompat i) (bR.repr x i)

omit [Fintype ι] [DecidableEq ι] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- If a Brauer-row integer representative and the fixed regular-class coordinate representative
both represent the same row modulo Serre's regular-value divisibility lattice, then the two
integer representatives agree modulo the integer diagonal lattice.

The only non-formal input is the second row congruence, typically the Serre 18.4/18.5(a)
integral-image statement for the fixed coordinates. -/
theorem rowwiseModuloDiagonal_of_regularValueRepresentatives
    (π : ι → FDRep k G)
    (g : ι → PRegularConjClass G p → ℤ)
    (hrow :
      ∀ i : ι,
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
            ([π i]₀ : R₀[k](G)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) (g i) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hcoordRow :
      ∀ i : ι,
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
            ([π i]₀ : R₀[k](G)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv (p := p) (G := G) ([π i]₀ : R₀[k](G))) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    ∀ i : ι,
      g i - regularClassCoordinateAddEquiv (p := p) (G := G) ([π i]₀ : R₀[k](G)) ∈
        regularIntegerDiagonalSubmodule (p := p) (G := G) := by
  intro i
  let χ : PRegularConjClass G p → K :=
    virtualModularCharacterOnPRegularConjClass
      (p := p) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
      ([π i]₀ : R₀[k](G))
  let coord : PRegularConjClass G p → ℤ :=
    regularClassCoordinateAddEquiv (p := p) (G := G) ([π i]₀ : R₀[k](G))
  let D : Submodule A (PRegularConjClass G p → K) :=
    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  have hcast :
      regularIntegerFunctionCast (p := p) (K := K) (G := G) (g i - coord) ∈ D := by
    have hsub : (χ -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) coord) -
        (χ - regularIntegerFunctionCast (p := p) (K := K) (G := G) (g i)) ∈ D := by
      exact D.sub_mem (by simpa [D, χ, coord] using hcoordRow i)
        (by simpa [D, χ] using hrow i)
    convert hsub using 1
    ext c
    simp [regularIntegerFunctionCast]
  exact
    regularIntegerFunctionCast_mem_regularIntegerDiagonalSubmodule_of_mem_regularValue
      (p := p) (A := A) (K := K) (G := G)
      (f := g i - coord) (by simpa [D, coord] using hcast)

omit [DecidableEq ι] in
/-- Serre-basis sufficient theorem with rowwise integer-coordinate compatibility instead of the
expanded `hcompat` hypothesis. -/
theorem projectiveCharacterLatticeIntegerRepresentativeCongruence_of_serreBasis_projectiveLatticeRepresentatives_rowwiseModuloDiagonal
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (g : ι → PRegularConjClass G p → ℤ)
    (hrow :
      ∀ i : ι,
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
            ([π i]₀ : R₀[k](G)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) (g i) ∈
            Submodule.map
              (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
              (projectiveCharacterSubmodule (A := A) (K := K) (G := G)))
    (hrowCompat :
      ∀ i : ι,
        g i -
            regularClassCoordinateAddEquiv (p := p) (G := G) ([π i]₀ : R₀[k](G)) ∈
          regularIntegerDiagonalSubmodule (p := p) (G := G)) :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (A := A) (K := K) (G := G) :=
  projectiveCharacterLatticeIntegerRepresentativeCongruence_of_serreBasis_projectiveLatticeRepresentatives
    (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete g hrow
    (serreBasis_hcompat_of_rowwiseModuloDiagonal
      (p := p) (G := G) π hπ_pairwise hπ_complete g hrowCompat)

omit [DecidableEq ι] in
/-- Divisibility-lattice sufficient theorem with rowwise integer-coordinate compatibility instead
of the expanded `hcompat` hypothesis. -/
theorem projectiveCharacterLatticeIntegerRepresentativeCongruence_of_serreBasis_divisibilityRepresentatives_rowwiseModuloDiagonal
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (g : ι → PRegularConjClass G p → ℤ)
    (hrow :
      ∀ i : ι,
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
            ([π i]₀ : R₀[k](G)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) (g i) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hrowCompat :
      ∀ i : ι,
        g i -
            regularClassCoordinateAddEquiv (p := p) (G := G) ([π i]₀ : R₀[k](G)) ∈
          regularIntegerDiagonalSubmodule (p := p) (G := G)) :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (A := A) (K := K) (G := G) :=
  projectiveCharacterLatticeIntegerRepresentativeCongruence_of_serreBasis_divisibilityRepresentatives
    (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete g hrow
    (serreBasis_hcompat_of_rowwiseModuloDiagonal
      (p := p) (G := G) π hπ_pairwise hπ_complete g hrowCompat)

omit [DecidableEq ι] in
/-- Divisibility-lattice sufficient theorem where rowwise compatibility is obtained by descending
two regular-value representatives of each Brauer row to the integer diagonal lattice. -/
theorem projectiveCharacterLatticeIntegerRepresentativeCongruence_of_serreBasis_divisibilityRepresentatives_coordinateRows
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (g : ι → PRegularConjClass G p → ℤ)
    (hrow :
      ∀ i : ι,
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
            ([π i]₀ : R₀[k](G)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) (g i) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hcoordRow :
      ∀ i : ι,
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
            ([π i]₀ : R₀[k](G)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv (p := p) (G := G) ([π i]₀ : R₀[k](G))) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    projectiveCharacterLatticeIntegerRepresentativeCongruence
      (p := p) (A := A) (K := K) (G := G) :=
  projectiveCharacterLatticeIntegerRepresentativeCongruence_of_serreBasis_divisibilityRepresentatives_rowwiseModuloDiagonal
    (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete g hrow
    (rowwiseModuloDiagonal_of_regularValueRepresentatives
      (p := p) (A := A) (K := K) (G := G) π g hrow hcoordRow)

end ProjectiveCharacterLatticeSourceFaithful

end Representation
