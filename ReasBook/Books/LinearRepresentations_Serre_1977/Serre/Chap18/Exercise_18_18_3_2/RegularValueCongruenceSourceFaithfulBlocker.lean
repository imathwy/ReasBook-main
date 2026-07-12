import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanCokernelProductDirect
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerPointMassSourceCriterion

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section RegularValueCongruenceSourceFaithfulBlocker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance regularValueCongruenceSourceFaithfulBlockerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance regularValueCongruenceSourceFaithfulBlockerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Existence of one coordinate-normalized Brauer family satisfying the fixed point-mass
source congruence. This is the exact basis-vector form of the global source-faithful
regular-value congruence. -/
def regularValueCongruenceSourceFaithfulExistsBrauerPointMassSourceCongruence : Prop :=
  ∃ π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G,
    ∃ hπ_simple : ∀ c, Simple (π c),
      ∃ hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
        brauerPointMassSourceCongruence
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

/-- For any fixed normalized Brauer family, the global congruence is equivalent to the fixed
point-mass source congruence on that family. -/
theorem regularValueCongruenceSourceFaithfulStatement_iff_brauerPointMassSourceCongruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    regularValueCongruenceSourceFaithfulStatement (p := p) (A := A) (K := K) (G := G) ↔
      brauerPointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  constructor
  · intro hglobal c
    simpa [brauerPointMassSourceCongruence, hπ_coord c] using
      hglobal ([π c]₀ : R₀[IsLocalRing.ResidueField A](G))
  · intro hsource
    exact
      regularValueCongruence_of_brauerPointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hsource

/-- The global source-faithful congruence is equivalent to existence of one normalized family
satisfying the fixed point-mass source congruences. -/
theorem regularValueCongruenceSourceFaithfulStatement_iff_exists_brauerPointMassSourceCongruence :
    regularValueCongruenceSourceFaithfulStatement (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsBrauerPointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · intro hglobal
    rcases
        exists_coordinate_normalized_complete_family_with_projective_envelopes
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
      ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    exact
      (regularValueCongruenceSourceFaithfulStatement_iff_brauerPointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).1 hglobal
  · rintro ⟨π, hπ_simple, hπ_coord, hsource⟩
    exact
      (regularValueCongruenceSourceFaithfulStatement_iff_brauerPointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).2 hsource

/-- Existence of one coordinate-normalized Brauer family satisfying the coordinatewise
divisibility form of the point-mass source congruence. -/
def regularValueCongruenceSourceFaithfulExistsPointMassCoordinateDivisibility : Prop :=
  ∃ π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G,
    ∃ hπ_simple : ∀ c, Simple (π c),
      ∃ hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
        brauerPointMassCoordinateDivisibility
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

/-- The global source-faithful congruence is equivalent to the point-mass coordinatewise
divisibility statement for one normalized Brauer family. -/
theorem regularValueCongruenceSourceFaithfulStatement_iff_exists_pointMassCoordinateDivisibility :
    regularValueCongruenceSourceFaithfulStatement (p := p) (A := A) (K := K) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · intro hglobal
    rcases
        (regularValueCongruenceSourceFaithfulStatement_iff_exists_brauerPointMassSourceCongruence
          (p := p) (A := A) (K := K) (G := G)).1 hglobal with
      ⟨π, hπ_simple, hπ_coord, hsource⟩
    refine ⟨π, hπ_simple, hπ_coord, ?_⟩
    exact
      (brauerPointMassSourceCongruence_iff_coordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).1 hsource
  · rintro ⟨π, hπ_simple, hπ_coord, hcoord⟩
    have hsource :
        brauerPointMassSourceCongruence
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord :=
      (brauerPointMassSourceCongruence_iff_coordinateDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).2 hcoord
    exact
      (regularValueCongruenceSourceFaithfulStatement_iff_brauerPointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).2 hsource

end RegularValueCongruenceSourceFaithfulBlocker

section FullMixedModelRegularValueCongruenceSourceFaithfulBlocker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedModelRegularValueCongruenceSourceFaithfulBlockerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedPointMassBlockerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-model version of the point-mass source-congruence blocker. -/
def fullMixedModelBrauerPointMassSourceCongruenceBlocker : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulExistsBrauerPointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G)

/- The full mixed-model global congruence is equivalent to the full mixed-model point-mass
source-congruence blocker. -/
omit [IsAlgClosed k] [CharP k p] in
theorem fullMixedModelRegularValueCongruenceSourceFaithfulStatement_iff_pointMassSourceBlocker :
    fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerPointMassSourceCongruenceBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hregular A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulStatement_iff_exists_brauerPointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G)).1
        (hregular (A := A) (K := K) e0)
  · intro hblock A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulStatement_iff_exists_brauerPointMassSourceCongruence
        (p := p) (A := A) (K := K) (G := G)).2
        (hblock (A := A) (K := K) e0)

/-- Full mixed-model version of the point-mass coordinatewise-divisibility blocker. -/
def fullMixedModelPointMassCoordinateDivisibilityBlocker : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulExistsPointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G)

/- The full mixed-model global congruence is equivalent to point-mass coordinatewise
divisibility in every full mixed-characteristic model. -/
omit [IsAlgClosed k] [CharP k p] in
theorem
    fullMixedModelRegularValueCongruence_iff_pointMassCoordinateDivisibilityBlocker :
    fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassCoordinateDivisibilityBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hregular A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulStatement_iff_exists_pointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G)).1
        (hregular (A := A) (K := K) e0)
  · intro hblock A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulStatement_iff_exists_pointMassCoordinateDivisibility
        (p := p) (A := A) (K := K) (G := G)).2
        (hblock (A := A) (K := K) e0)

end FullMixedModelRegularValueCongruenceSourceFaithfulBlocker

end Representation
