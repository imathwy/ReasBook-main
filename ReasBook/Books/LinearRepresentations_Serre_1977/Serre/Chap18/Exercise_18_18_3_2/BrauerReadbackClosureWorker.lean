import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackACompletion
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerReadbackFinalIntegration

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalBrauerReadbackClosureWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerReadbackClosureWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerReadbackClosureWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The smallest fixed-family residual witness needed to produce the local Brauer-basis
readback input: one coordinate-normalized simple family, with the nontrivial centralizer columns
checked pointwise. -/
def regularValueCongruenceSourceFaithfulBrauerBasisNontrivialPointwiseResidualWitness :
    Prop :=
  ∃ π : PRegularConjClass G p → FDRep k G,
    ∃ hπ_simple : ∀ c, Simple (π c),
      ∃ hπ_coord :
        (∀ c : PRegularConjClass G p,
          regularClassCoordinateAddEquiv ([π c]₀ : R₀[k](G)) =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
        coordinateNormalizedBrauerBasisNontrivialPointwiseResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- A fixed-family nontrivial pointwise residual witness closes the local readback input. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_nontrivialPointwiseResidualWitness
    (hpoint :
      regularValueCongruenceSourceFaithfulBrauerBasisNontrivialPointwiseResidualWitness
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  rcases hpoint with ⟨π, hπ_simple, hπ_coord, hpoint⟩
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_fixedFamilyReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
      (brauerBasisFixedCoordinateReadbackDivisibility_of_nontrivialPointwiseResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord hpoint)

/-- The local readback input gives the same fixed family with its nontrivial pointwise residual,
by the fixed-coordinate readback equivalence. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisNontrivialPointwiseResidualWitness_of_readbackInput
    (hread :
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisNontrivialPointwiseResidualWitness
      (p := p) (A := A) (G := G) := by
  rcases hread with ⟨π, hπ_simple, hπ_coord, hread⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    (brauerBasisFixedCoordinateReadbackDivisibility_iff_nontrivialPointwiseResidual
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hread

/-- Local equivalence between the existing Brauer-basis readback input and the minimal
fixed-family nontrivial pointwise residual witness. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_iff_nontrivialPointwiseResidualWitness :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulBrauerBasisNontrivialPointwiseResidualWitness
        (p := p) (A := A) (G := G) := by
  constructor
  · exact
      regularValueCongruenceSourceFaithfulBrauerBasisNontrivialPointwiseResidualWitness_of_readbackInput
        (p := p) (A := A) (G := G)
  · exact
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_nontrivialPointwiseResidualWitness
        (p := p) (A := A) (G := G)

end LocalBrauerReadbackClosureWorker

section FullMixedBrauerReadbackClosureWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerReadbackClosureWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerReadbackClosureWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-model package of the fixed-family nontrivial pointwise residual witness.  The
fraction field parameters mirror `fullMixedModelBrauerBasisReadbackInput`; the local residual
condition itself is the `A`-valued witness above. -/
def fullMixedModelBrauerBasisNontrivialPointwiseResidualWitness : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulBrauerBasisNontrivialPointwiseResidualWitness
        (p := p) (A := A) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed closure from the minimal fixed-family nontrivial pointwise residual witness. -/
theorem fullMixedModelBrauerBasisReadbackInput_of_nontrivialPointwiseResidualWitness
    (hpoint :
      fullMixedModelBrauerBasisNontrivialPointwiseResidualWitness
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_nontrivialPointwiseResidualWitness
      (p := p) (A := A) (G := G)
      (hpoint (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed readback input carries exactly the same fixed-family residual witness in each
mixed model. -/
theorem fullMixedModelBrauerBasisNontrivialPointwiseResidualWitness_of_readbackInput
    (hread : fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisNontrivialPointwiseResidualWitness
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisNontrivialPointwiseResidualWitness_of_readbackInput
      (p := p) (A := A) (G := G)
      (hread (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed equivalence: no extra universal residual over all coordinate-normalized families is
needed beyond the fixed-family witness packaged here. -/
theorem fullMixedModelBrauerBasisReadbackInput_iff_nontrivialPointwiseResidualWitness :
    fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisNontrivialPointwiseResidualWitness
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelBrauerBasisNontrivialPointwiseResidualWitness_of_readbackInput
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelBrauerBasisReadbackInput_of_nontrivialPointwiseResidualWitness
        (p := p) (k := k) (G := G)

end FullMixedBrauerReadbackClosureWorker

end Representation
