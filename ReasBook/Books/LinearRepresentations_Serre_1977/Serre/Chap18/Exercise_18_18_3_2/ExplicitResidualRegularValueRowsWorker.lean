import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.PointMassRowsSourceClosureWorker

/-!
Explicit source-side regular-value rows for the point-mass residual.

This worker isolates the literal value-divisibility form of Serre `18.5(a)` for the
coordinate-normalized point-mass rows.  It does not use any Cartan range/cokernel/product
endpoint: the only remaining mathematical input is the pointwise regular-value divisibility
of the row residuals themselves.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalExplicitResidualRegularValueRowsWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "kA" => IsLocalRing.ResidueField A

local instance explicitResidualRegularValueRowsWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance explicitResidualRegularValueRowsWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Literal value-side form of the point-mass row residual condition.

For each coordinate row `c` and each regular class `d`, the residual row value is divisible by
Serre's centralizer `p`-part `p^{z(d)}` in `A`, after mapping to `K`. -/
def coordinateNormalizedPointMassResidualRegularValueRows
    (π : PRegularConjClass G p → FDRep kA G) : Prop :=
  ∀ c d : PRegularConjClass G p,
    ∃ a : A,
      FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) (π c)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) d -
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d =
          algebraMap A K ((ConjClasses.centralizerPPart p d.1 : A) * a)

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The explicit value-divisibility rows are exactly the regular-value submodule row input. -/
theorem coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_explicitRows
    (π : PRegularConjClass G p → FDRep kA G)
    (hrows : coordinateNormalizedPointMassResidualRegularValueRows
      (p := p) (A := A) (K := K) (G := G) π) :
    coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
      (p := p) (A := A) (K := K) (G := G) π := by
  intro c
  refine
    (mem_regularValueDivisibilitySubmodule_iff
      (p := p) (A := A) (K := K) (G := G) _).2 ?_
  intro d
  exact hrows c d

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Conversely, membership in the regular-value row submodule unpacks to the explicit
coordinatewise centralizer-`p`-part divisibility. -/
theorem explicitRows_of_coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
    (π : PRegularConjClass G p → FDRep kA G)
    (hrows :
      coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π) :
    coordinateNormalizedPointMassResidualRegularValueRows
      (p := p) (A := A) (K := K) (G := G) π := by
  intro c d
  exact
    (mem_regularValueDivisibilitySubmodule_iff
      (p := p) (A := A) (K := K) (G := G) _).1
      (hrows c) d

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Fixed-family equivalence between the row-submodule input and the explicit regular-value
divisibility rows. -/
theorem coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_iff_explicitRows
    (π : PRegularConjClass G p → FDRep kA G) :
    coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π ↔
      coordinateNormalizedPointMassResidualRegularValueRows
        (p := p) (A := A) (K := K) (G := G) π := by
  constructor
  · exact
      explicitRows_of_coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π
  · exact
      coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_explicitRows
        (p := p) (A := A) (K := K) (G := G) π

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Existing `brauerPointMassCoordinateDivisibility` is the same explicit value-side condition,
with the coordinate-normalization hypotheses attached. -/
theorem coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_iff_coordinateDivisibility
    (π : PRegularConjClass G p → FDRep kA G)
    (_hπ_simple : ∀ c, Simple (π c))
    (_hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
        (p := p) (A := A) (K := K) (G := G) π ↔
      brauerPointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π _hπ_simple _hπ_coord := by
  simpa [coordinateNormalizedPointMassResidualRegularValueRows,
    brauerPointMassCoordinateDivisibility] using
    (coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_iff_explicitRows
      (p := p) (A := A) (K := K) (G := G) π)

/-- Existential explicit value-side source input for the residual row route. -/
def regularValueCongruenceSourceFaithfulExistsExplicitResidualRows : Prop :=
  ∃ π : PRegularConjClass G p → FDRep kA G,
    ∃ _hπ_simple : ∀ c, Simple (π c),
      ∃ _hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (G := G) ([π c]₀ : R₀[kA](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
        coordinateNormalizedPointMassResidualRegularValueRows
          (p := p) (A := A) (K := K) (G := G) π

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The explicit value-divisibility rows supply the named source-row input used by the pairing
residual worker. -/
theorem regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows_of_explicitRows
    (hrows :
      regularValueCongruenceSourceFaithfulExistsExplicitResidualRows
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hrows with ⟨π, hπ_simple, hπ_coord, hrows⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_of_explicitRows
      (p := p) (A := A) (K := K) (G := G) π hrows

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The named source-row input unpacks back to the explicit value-divisibility rows. -/
theorem explicitRows_of_regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows
    (hrows :
      regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsExplicitResidualRows
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hrows with ⟨π, hπ_simple, hπ_coord, hrows⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    explicitRows_of_coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule
      (p := p) (A := A) (K := K) (G := G) π hrows

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Exact local source equivalence: the current row input is no stronger and no weaker than the
literal regular-value divisibility of the point-mass residual rows. -/
theorem regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows_iff_explicitRows :
    regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows
        (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsExplicitResidualRows
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · exact
      explicitRows_of_regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows
        (p := p) (A := A) (K := K) (G := G)
  · exact
      regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows_of_explicitRows
        (p := p) (A := A) (K := K) (G := G)

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- The existing coordinate-divisibility blocker is enough for the requested source-row input.
This is only the `mem_regularValueDivisibilitySubmodule_iff` unpacking, not a Cartan endpoint
argument. -/
theorem regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows_of_coordinateDivisibility
    (hcoord :
      regularValueCongruenceSourceFaithfulExistsPointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows
      (p := p) (A := A) (K := K) (G := G) := by
  rcases hcoord with ⟨π, hπ_simple, hπ_coord, hcoord⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    (coordinateNormalizedBrauerBasisPointMassRowsInRegularValueSubmodule_iff_coordinateDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).2 hcoord

end LocalExplicitResidualRegularValueRowsWorker

section FullMixedExplicitResidualRegularValueRowsWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedExplicitResidualRegularValueRowsWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedExplicitResidualRegularValueRowsWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model form of the explicit regular-value residual row input. -/
def fullMixedModelExplicitResidualRowsBlocker : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulExistsExplicitResidualRows
        (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model explicit residual rows give the requested direct point-mass row input. -/
theorem fullMixedModelPointMassRowsInRegularValueSubmoduleInput_of_explicitResidualRows
    (hrows :
      fullMixedModelExplicitResidualRowsBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassRowsInRegularValueSubmoduleInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  simpa [regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows] using
    regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows_of_explicitRows
      (p := p) (A := A) (K := K) (G := G)
      (hrows (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Conversely, the requested direct row input is exactly the full mixed explicit residual row
condition. -/
theorem explicitResidualRows_of_fullMixedModelPointMassRowsInRegularValueSubmoduleInput
    (hrows :
      fullMixedModelPointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G)) :
    fullMixedModelExplicitResidualRowsBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    explicitRows_of_regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows
      (p := p) (A := A) (K := K) (G := G)
      (by
        simpa [regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows] using
          hrows (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed exact equivalence between the requested row input and the explicit
regular-value residual row condition. -/
theorem fullMixedModelPointMassRowsInRegularValueSubmoduleInput_iff_explicitResidualRows :
    fullMixedModelPointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G) ↔
      fullMixedModelExplicitResidualRowsBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      explicitResidualRows_of_fullMixedModelPointMassRowsInRegularValueSubmoduleInput
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelPointMassRowsInRegularValueSubmoduleInput_of_explicitResidualRows
        (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model coordinatewise regular-value divisibility closes the requested direct row
input.  This is the strongest closed bridge available here; the remaining missing source input
is a proof of that coordinatewise divisibility for one coordinate-normalized Brauer family. -/
theorem fullMixedModelPointMassRowsInRegularValueSubmoduleInput_of_coordinateDivisibility
    (hcoord :
      fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassRowsInRegularValueSubmoduleInput
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  simpa [regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows] using
    regularValueCongruenceSourceFaithfulExistsPairingResidualSourceRows_of_coordinateDivisibility
      (p := p) (A := A) (K := K) (G := G)
      (hcoord (A := A) (K := K) e0)

end FullMixedExplicitResidualRegularValueRowsWorker

end Representation
