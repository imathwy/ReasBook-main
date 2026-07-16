import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanForwardScaledProducer

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanForwardSpanClosureWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCartanForwardSpanClosureWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanForwardSpanClosureWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Cartan-image readback congruence for the forward span-closure problem.

It is the regular-value congruence restricted to classes in the Cartan image. -/
def projectiveCartanForwardSpanClosureCartanReadbackCongruence : Prop :=
  ∀ x : P₀[IsLocalRing.ResidueField A](G),
    virtualModularCharacterOnPRegularConjClass
        (p := p) (k := IsLocalRing.ResidueField A) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        (cartanHom (IsLocalRing.ResidueField A) G x) -
      projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G) x ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

/-- The virtual modular character attached to a Cartan-image class is the regular restriction of
a projective character, hence lies in Serre's regular-value divisibility lattice. -/
theorem virtualModularCharacter_cartanHom_mem_regularValueDivisibilitySubmodule
    (x : P₀[IsLocalRing.ResidueField A](G)) :
    virtualModularCharacterOnPRegularConjClass
        (p := p) (k := IsLocalRing.ResidueField A) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        (cartanHom (IsLocalRing.ResidueField A) G x) ∈
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  let D : Submodule A (PRegularConjClass G p → K) :=
    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  let row : PRegularConjClass G p → K :=
    regularRestriction (p := p) (A := A) (K := K) (G := G)
      (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x)
  let χ : PRegularConjClass G p → K :=
    virtualModularCharacterOnPRegularConjClass
      (p := p) (k := IsLocalRing.ResidueField A) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
      (cartanHom (IsLocalRing.ResidueField A) G x)
  have hrowMap :
      row ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
    refine Submodule.mem_map.2 ?_
    refine
      ⟨projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x, ?_, ?_⟩
    · exact projectiveCharacterScalarExtension_mem_projectiveCharacterSubmodule
        (A := A) (K := K) (G := G) x
    · rfl
  have hrowD : row ∈ D := by
    have hrowMap' := hrowMap
    rw [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] at hrowMap'
    simpa [D] using hrowMap'
  have hrow_eq : row = χ := by
    simpa [row, χ, projectiveCartanASpanFieldLift] using
      (regularRestriction_projectiveCharacterScalarExtension_eq_cartan_virtual_row
        (p := p) (A := A) (K := K) (G := G) (x := x))
  simpa [χ, D, hrow_eq] using hrowD

/-- The forward span inclusion is exactly the Cartan-image readback congruence, after using
Serre `18.5(a)` for projective regular restrictions. -/
theorem
    projectiveCartanCoordinate_span_le_regularValueDivisibilitySubmodule_iff_cartanReadbackCongruence :
    (Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) ≤
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ↔
    projectiveCartanForwardSpanClosureCartanReadbackCongruence
      (p := p) (A := A) (K := K) (G := G) := by
  classical
  let D : Submodule A (PRegularConjClass G p → K) :=
    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  constructor
  · intro hspan x
    let χ : PRegularConjClass G p → K :=
      virtualModularCharacterOnPRegularConjClass
        (p := p) (k := IsLocalRing.ResidueField A) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        (cartanHom (IsLocalRing.ResidueField A) G x)
    have hχD : χ ∈ D := by
      simpa [χ, D] using
        virtualModularCharacter_cartanHom_mem_regularValueDivisibilitySubmodule
          (p := p) (A := A) (K := K) (G := G) x
    have hcoordD :
        projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G) x ∈ D :=
      hspan (Submodule.subset_span ⟨x, rfl⟩)
    simpa [projectiveCartanForwardSpanClosureCartanReadbackCongruence, χ, D] using
      D.sub_mem hχD hcoordD
  · intro hread
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, rfl⟩
    let χ : PRegularConjClass G p → K :=
      virtualModularCharacterOnPRegularConjClass
        (p := p) (k := IsLocalRing.ResidueField A) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
        (cartanHom (IsLocalRing.ResidueField A) G x)
    have hχD : χ ∈ D := by
      simpa [χ, D] using
        virtualModularCharacter_cartanHom_mem_regularValueDivisibilitySubmodule
          (p := p) (A := A) (K := K) (G := G) x
    have hcong :
        χ - projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G) x ∈
          D := by
      simpa [projectiveCartanForwardSpanClosureCartanReadbackCongruence, χ, D] using
        hread x
    have hcoordD :
        χ - (χ - projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G) x) ∈
          D :=
      D.sub_mem hχD hcong
    have hcoord_eq :
        χ - (χ - projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G) x) =
          projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G) x := by
      ext c
      simp only [Pi.sub_apply]
      ring
    simpa [hcoord_eq, D] using hcoordD

/-- Source-side forward span inclusion from the regular-value congruence form of Serre `18.5(a)`.

For a projective class `x`, its fixed Cartan-coordinate cast is congruent, modulo Serre's
regular-value divisibility lattice, to the regular restriction of the projective character
attached to `x`.  The latter lies in the divisibility lattice by the already-proved
projective-character form of `18.5(a)`, so the Cartan-coordinate row lies there as well. -/
theorem projectiveCartanCoordinate_span_le_regularValueDivisibilitySubmodule_of_regularValueCongruence
    (hregular :
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)) :
    Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) ≤
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  classical
  let D : Submodule A (PRegularConjClass G p → K) :=
    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, rfl⟩
  let row : PRegularConjClass G p → K :=
    regularRestriction (p := p) (A := A) (K := K) (G := G)
      (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x)
  let χ : PRegularConjClass G p → K :=
    virtualModularCharacterOnPRegularConjClass
      (p := p) (k := IsLocalRing.ResidueField A) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
      (cartanHom (IsLocalRing.ResidueField A) G x)
  let coord : PRegularConjClass G p → ℤ :=
    cartanCoordinateAddHom
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) x
  let coordK : PRegularConjClass G p → K :=
    regularIntegerFunctionCast (p := p) (K := K) (G := G) coord
  have hrowMap :
      row ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
    refine Submodule.mem_map.2 ?_
    refine
      ⟨projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x, ?_, ?_⟩
    · exact projectiveCharacterScalarExtension_mem_projectiveCharacterSubmodule
        (A := A) (K := K) (G := G) x
    · rfl
  have hrowD : row ∈ D := by
    have hrowMap' := hrowMap
    rw [projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] at hrowMap'
    simpa [D] using hrowMap'
  have hrow_eq : row = χ := by
    simpa [row, χ, projectiveCartanASpanFieldLift] using
      (regularRestriction_projectiveCharacterScalarExtension_eq_cartan_virtual_row
        (p := p) (A := A) (K := K) (G := G) (x := x))
  have hχD : χ ∈ D := by
    simpa [hrow_eq] using hrowD
  have hcong : χ - coordK ∈ D := by
    simpa [χ, coordK, coord, cartanCoordinateAddHom, D] using
      hregular (cartanHom (IsLocalRing.ResidueField A) G x)
  have hcoordD : coordK ∈ D := by
    have hdiff : χ - (χ - coordK) ∈ D := D.sub_mem hχD hcong
    have hdiff_eq : χ - (χ - coordK) = coordK := by
      ext c
      simp only [Pi.sub_apply]
      ring
    simpa [hdiff_eq] using hdiff
  simpa [coordK, coord, D, regularIntegerFunctionCast_cartanCoordinateAddHom
    (p := p) (A := A) (K := K) (G := G) x] using hcoordD

end ProjectiveCartanForwardSpanClosureWorker

section FullMixedProjectiveCartanForwardSpanClosureWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedProjectiveCartanForwardSpanClosureWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedProjectiveCartanForwardSpanClosureWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model forward source inclusion from the regular-value source statement.

This is the `B`-side forward inclusion supplied by Serre `18.5(a)`: it produces only
`span(cartanCoordinateCast.range) ≤ regularValueDivisibilitySubmodule`, not a final Cartan range,
cokernel, or product endpoint. -/
theorem fullMixedModelProjectiveCartanCoordinateSpanLeStatement_of_regularValueSource
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanCoordinateSpanLeStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    projectiveCartanCoordinate_span_le_regularValueDivisibilitySubmodule_of_regularValueCongruence
      (p := p) (A := A) (K := K) (G := G)
      (hregular (A := A) (K := K) e0)

end FullMixedProjectiveCartanForwardSpanClosureWorker

end Representation
