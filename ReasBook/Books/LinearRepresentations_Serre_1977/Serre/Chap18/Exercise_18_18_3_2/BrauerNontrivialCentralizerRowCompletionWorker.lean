import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisResidualDirectCompletionWorker

/-!
Nontrivial-centralizer Brauer row completion worker.

This file keeps the remaining row congruence on the source side.  The bridge below says that a
K-valued row congruence for the same Brauer character, evaluated with the canonical fraction-field
lift, descends to the requested A-valued congruence by naturality of
`FDRep.modularCharacterOnPRegularConjClass` and injectivity of `A → K`.

No Cartan range/cokernel/product/determinant endpoint, and no projective-character lattice reverse
route, is used here.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerNontrivialCentralizerRowCompletionWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerNontrivialCentralizerRowCompletionWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerNontrivialCentralizerRowCompletionWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsFractionRing A K] [CharZero K] in
/-- Naturality of the canonical Brauer-character row under the fraction-field map `A → K`. -/
theorem modularCharacterOnPRegularConjClass_algebraMap_canonicalLift
    (E : FDRep k G) (d : PRegularConjClass G p) :
    algebraMap A K
        (FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := A) E
          (primeToPRoot_canonicalLift (p := p) (A := A)) d) =
      FDRep.modularCharacterOnPRegularConjClass
        (p := p) (G := G) (A := K) E
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d := by
  simpa [projectiveCartanASpanFieldLift, primeToPRoot_canonicalLift] using
    congrFun
      (modularCharacterOnPRegularConjClass_comp_lift_local
        (σ := (algebraMap A K))
        (lift := (Units.coeHom A).comp
          (primeToPRoot_unitsLift (p := p) (A := A)))
        (E := E)) d

/-- K-valued source-side nontrivial-column row congruence for one Brauer family.

This is the same literal row congruence as the requested A-valued target, but after applying the
canonical fraction-field lift of prime-to-`p` roots and casting the integer point mass to `K`. -/
def coordinateNormalizedBrauerCharacterNontrivialFieldRowSource
    (π : PRegularConjClass G p → FDRep k G) : Prop :=
  ∀ c d : PRegularConjClass G p,
    ConjClasses.centralizerPPart p d.1 ≠ 1 →
      ∃ a : A,
        FDRep.modularCharacterOnPRegularConjClass
              (p := p) (G := G) (A := K) (π c)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d =
          algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)

omit [CharZero K] in
/-- The K-valued source row congruence descends to the requested A-valued nontrivial-column
Brauer-character readback congruence.

The only algebraic input is injectivity of the fraction-field map `A → K`; the character row is
transported by the existing lift-naturality lemma. -/
theorem coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence_of_fieldRowSource
    (π : PRegularConjClass G p → FDRep k G)
    (hsource :
      coordinateNormalizedBrauerCharacterNontrivialFieldRowSource
        (p := p) (A := A) (K := K) (G := G) π) :
    coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence
      (p := p) (A := A) (G := G) π := by
  intro c d hd
  rcases hsource c d hd with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  apply IsFractionRing.injective A K
  have hchar :
      algebraMap A K
          (FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := A) (π c)
            (primeToPRoot_canonicalLift (p := p) (A := A)) d) =
        FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d := by
    exact
      modularCharacterOnPRegularConjClass_algebraMap_canonicalLift
        (p := p) (A := A) (K := K) (G := G) (π c) d
  calc
    algebraMap A K
        (FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := A) (π c)
            (primeToPRoot_canonicalLift (p := p) (A := A)) d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A))
        =
      FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := K) (π c)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d := by
          simp [map_sub, hchar, regularIntegerFunctionCast]
    _ = algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) := ha

omit [IsFractionRing A K] [CharZero K] in
/-- The requested A-valued nontrivial-column congruence maps to the K-valued source-side
nontrivial-column row congruence. -/
theorem coordinateNormalizedBrauerCharacterNontrivialFieldRowSource_of_pointwiseReadbackCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hpoint :
      coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π) :
    coordinateNormalizedBrauerCharacterNontrivialFieldRowSource
      (p := p) (A := A) (K := K) (G := G) π := by
  intro c d hd
  rcases hpoint c d hd with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hchar :
      algebraMap A K
          (FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := A) (π c)
            (primeToPRoot_canonicalLift (p := p) (A := A)) d) =
        FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d := by
    exact
      modularCharacterOnPRegularConjClass_algebraMap_canonicalLift
        (p := p) (A := A) (K := K) (G := G) (π c) d
  calc
    FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d
        =
      algebraMap A K
        (FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := A) (π c)
            (primeToPRoot_canonicalLift (p := p) (A := A)) d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A)) := by
          simp [map_sub, hchar, regularIntegerFunctionCast]
    _ = algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a) := by
          rw [ha]

omit [CharZero K] in
/-- Exact fixed-family source boundary: the requested A-valued nontrivial-column congruence is
equivalent to the same nontrivial-column row congruence after scalar extension to `K`. -/
theorem coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence_iff_fieldRowSource
    (π : PRegularConjClass G p → FDRep k G) :
    coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π ↔
      coordinateNormalizedBrauerCharacterNontrivialFieldRowSource
        (p := p) (A := A) (K := K) (G := G) π := by
  constructor
  · exact
      coordinateNormalizedBrauerCharacterNontrivialFieldRowSource_of_pointwiseReadbackCongruence
        (p := p) (A := A) (K := K) (G := G) π
  · exact
      coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence_of_fieldRowSource
        (p := p) (A := A) (K := K) (G := G) π

/-- Global coordinate-normalized source-side API for the nontrivial centralizer columns. -/
def coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep k G)
    (_hπ_simple : ∀ c, Simple (π c))
    (_hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
    coordinateNormalizedBrauerCharacterNontrivialFieldRowSource
      (p := p) (A := A) (K := K) (G := G) π

/-- Global A-valued API matching the user's fixed-family target for every coordinate-normalized
Brauer family. -/
def coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruenceAPI : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep k G)
    (_hπ_simple : ∀ c, Simple (π c))
    (_hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
    coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence
      (p := p) (A := A) (G := G) π

omit [CharZero K] in
/-- Exact global source boundary for coordinate-normalized families: the A-valued requested API
is equivalent to the K-valued source-side API. -/
theorem coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruenceAPI_iff_fieldRowSourceAPI :
    coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruenceAPI
        (p := p) (A := A) (G := G) ↔
      coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · intro hapi π hπ_simple hπ_coord
    exact
      (coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence_iff_fieldRowSource
        (p := p) (A := A) (K := K) (G := G) π).1
        (hapi π hπ_simple hπ_coord)
  · intro hapi π hπ_simple hπ_coord
    exact
      (coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence_iff_fieldRowSource
        (p := p) (A := A) (K := K) (G := G) π).2
        (hapi π hπ_simple hπ_coord)

omit [CharZero K] in
/-- If the source-side K-valued API is available for all coordinate-normalized rows, then the
requested A-valued nontrivial-column congruence follows for each such row. -/
theorem coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence_of_fieldRowSourceAPI
    (hapi :
      coordinateNormalizedBrauerCharacterNontrivialFieldRowSourceAPI
        (p := p) (A := A) (K := K) (G := G))
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence
      (p := p) (A := A) (G := G) π :=
  coordinateNormalizedBrauerCharacterNontrivialPointwiseReadbackCongruence_of_fieldRowSource
    (p := p) (A := A) (K := K) (G := G) π
    (hapi π hπ_simple hπ_coord)

end BrauerNontrivialCentralizerRowCompletionWorker

end Representation
