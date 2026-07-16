import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassProjectiveRestrictionProof
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerPointMassBasisResidualEndpoint

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerPointMassNontrivialResidualProof

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local instance brauerPointMassNontrivialResidualProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerPointMassNontrivialResidualProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The full pure `A`-basis residual immediately supplies the reduced nontrivial-column
residual input.  This direction only forgets the `centralizerPPart = 1` columns; it uses no
Cartan range, cokernel, or product endpoint. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassNontrivialResidualDivisibility_of_basisResidualDivisibility
    (hbasis :
      regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulExistsPointMassNontrivialResidualDivisibility
      (p := p) (A := A) (G := G) := by
  rcases hbasis with ⟨π, hπ_simple, hπ_coord, hbasis⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  intro c d _hd
  exact hbasis c d

/-- Local equivalence between the full pure basis residual and its nontrivial-column form.

The reverse implication is the existing pointwise `centralizerPPart = 1` filler from the
Exercise `18.4` pairing API; the forward implication is restriction to the nontrivial columns. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassNontrivialResidualDivisibility_iff_basisResidualDivisibility :
    regularValueCongruenceSourceFaithfulExistsPointMassNontrivialResidualDivisibility
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility
        (p := p) (A := A) (G := G) := by
  constructor
  · exact
      regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility_of_nontrivialResidualDivisibility
        (p := p) (A := A) (G := G)
  · exact
      regularValueCongruenceSourceFaithfulExistsPointMassNontrivialResidualDivisibility_of_basisResidualDivisibility
        (p := p) (A := A) (G := G)

/-- The nontrivial residual input is exactly the existing fixed-coordinate Brauer-basis
readback input, after the already-proved basis-residual/readback equivalence.  This records the
actual local A-side blocker without using final Cartan range or cokernel/product endpoints. -/
theorem regularValueCongruenceSourceFaithfulExistsPointMassNontrivialResidualDivisibility_iff_brauerBasisReadbackInput :
    regularValueCongruenceSourceFaithfulExistsPointMassNontrivialResidualDivisibility
        (p := p) (A := A) (G := G) ↔
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
        (p := p) (A := A) (G := G) :=
  (regularValueCongruenceSourceFaithfulExistsPointMassNontrivialResidualDivisibility_iff_basisResidualDivisibility
    (p := p) (A := A) (G := G)).trans
    (existsPointMassBasisResidualDivisibility_iff_brauerBasisReadbackInput
      (p := p) (A := A) (G := G))

end BrauerPointMassNontrivialResidualProof

section FullMixedModelBrauerPointMassNontrivialResidualProof

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedModelBrauerPointMassNontrivialResidualProofFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedModelBrauerPointMassNontrivialResidualProofDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed-model basis-residual blocker supplies the requested nontrivial-column
residual blocker.  This is the full mixed version of the local restriction-to-nontrivial-columns
argument. -/
theorem fullMixedModelPointMassNontrivialResidualDivisibilityBlocker_of_basisResidualDivisibilityBlocker
    (hbasis :
      fullMixedModelPointMassBasisResidualDivisibilityBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassNontrivialResidualDivisibilityBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulExistsPointMassNontrivialResidualDivisibility_of_basisResidualDivisibility
      (p := p) (A := A) (G := G)
      (hbasis (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model equivalence between the nontrivial-column residual blocker and the full
basis-residual blocker. -/
theorem fullMixedModelPointMassNontrivialResidualDivisibilityBlocker_iff_basisResidualDivisibilityBlocker :
    fullMixedModelPointMassNontrivialResidualDivisibilityBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelPointMassBasisResidualDivisibilityBlocker
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hresidual A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      regularValueCongruenceSourceFaithfulExistsPointMassBasisResidualDivisibility_of_nontrivialResidualDivisibility
        (p := p) (A := A) (G := G)
        (hresidual (A := A) (K := K) e0)
  · exact
      fullMixedModelPointMassNontrivialResidualDivisibilityBlocker_of_basisResidualDivisibilityBlocker
        (p := p) (k := k) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed nontrivial residual blocker is exactly the full mixed fixed-coordinate
Brauer-basis readback input.  This isolates the remaining source-side Exercise `18.4` readback
problem for the final split, without deriving it from final Cartan range/cokernel/product
endpoints. -/
theorem fullMixedModelPointMassNontrivialResidualDivisibilityBlocker_iff_brauerBasisReadbackInput :
    fullMixedModelPointMassNontrivialResidualDivisibilityBlocker
        (p := p) (k := k) (G := G) ↔
      fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  constructor
  · intro hresidual A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulExistsPointMassNontrivialResidualDivisibility_iff_brauerBasisReadbackInput
        (p := p) (A := A) (G := G)).1
        (hresidual (A := A) (K := K) e0)
  · intro hread A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      (regularValueCongruenceSourceFaithfulExistsPointMassNontrivialResidualDivisibility_iff_brauerBasisReadbackInput
        (p := p) (A := A) (G := G)).2
        (hread (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model fixed-coordinate Brauer-basis readback gives the nontrivial residual input
requested by the final split. -/
theorem fullMixedModelPointMassNontrivialResidualDivisibilityBlocker_of_brauerBasisReadbackInput
    (hread : fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G)) :
    fullMixedModelPointMassNontrivialResidualDivisibilityBlocker
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    (regularValueCongruenceSourceFaithfulExistsPointMassNontrivialResidualDivisibility_iff_brauerBasisReadbackInput
      (p := p) (A := A) (G := G)).2
      (hread (A := A) (K := K) e0)

end FullMixedModelBrauerPointMassNontrivialResidualProof

end Representation
