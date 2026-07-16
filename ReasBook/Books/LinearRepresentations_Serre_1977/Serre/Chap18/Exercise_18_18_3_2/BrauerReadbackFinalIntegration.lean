import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackEndpoint
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.BrauerBasisReadbackResidualProof
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanCokernelProductDirect

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section LocalBrauerReadbackFinalIntegration

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerReadbackFinalIntegrationFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerReadbackFinalIntegrationDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Local universal A-side pairing residual input for the coordinate-normalized Brauer basis.

This is the residual statement isolated upstream in `BrauerBasisReadbackResidualProof`, required
for every coordinate-normalized complete simple family. -/
def regularValueCongruenceSourceFaithfulPairingResidualProof : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)),
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- Local universal pointwise version of the A-side pairing residual input.

Only the coordinates with nontrivial centralizer `p`-part are requested; the trivial coordinates
are supplied by the existing A-side pointwise lemma. -/
def regularValueCongruenceSourceFaithfulPointwiseResidualProof : Prop :=
  ∀ (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p),
    ConjClasses.centralizerPPart p d.1 ≠ 1 →
      let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord
      let bA :=
        canonicalDVRBrauerBasis
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
      ∃ a : A,
        bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
          (ConjClasses.centralizerPPart p d.1 : A) *
            (bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G)
                (inversePRegularConjClass (p := p) d)) c) =
            (ConjClasses.centralizerPPart p d.1 : A) * a

/-- A universal A-side pairing residual proof closes the local Brauer-basis readback endpoint.

This is the non-circular local integration step for
`regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_proof`: choose the standard
coordinate-normalized family, then apply the existing residual-to-readback bridge. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pairingResidualProof
    (hresidual :
      regularValueCongruenceSourceFaithfulPairingResidualProof
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_universalReadback
      (p := p) (A := A) (G := G)
      (fun π hπ_simple hπ_coord =>
        brauerBasisFixedCoordinateReadbackDivisibility_of_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord
          (hresidual π hπ_simple hπ_coord))

/-- A universal pointwise A-side residual proof closes the local Brauer-basis readback endpoint.

The existing A-side pointwise bridge first fills the `centralizerPPart = 1` coordinates, then the
pairing-residual readback bridge converts the resulting residual into fixed-coordinate readback. -/
theorem regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointwiseResidualProof
    (hresidual :
      regularValueCongruenceSourceFaithfulPointwiseResidualProof
        (p := p) (A := A) (G := G)) :
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput
      (p := p) (A := A) (G := G) := by
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_universalReadback
      (p := p) (A := A) (G := G)
      (fun π hπ_simple hπ_coord =>
        brauerBasisFixedCoordinateReadbackDivisibility_of_pairingResidual
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord
          (coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_nontrivial_centralizerPPart
            (p := p) (A := A) (G := G) π hπ_simple hπ_coord
            (hresidual π hπ_simple hπ_coord)))

end LocalBrauerReadbackFinalIntegration

section FullMixedBrauerReadbackFinalIntegration

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedBrauerReadbackFinalIntegrationFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedBrauerReadbackFinalIntegrationDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-characteristic form of the universal A-side pairing residual blocker. -/
def fullMixedModelBrauerBasisPairingResidualBlocker : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulPairingResidualProof
        (p := p) (A := A) (G := G)

/-- Full mixed-characteristic form of the universal A-side pointwise residual blocker. -/
def fullMixedModelBrauerBasisPointwiseResidualBlocker : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulPointwiseResidualProof
        (p := p) (A := A) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model pairing residuals close the full mixed Brauer-basis readback input. -/
theorem fullMixedModelBrauerBasisReadbackInput_of_pairingResidualBlocker
    (hresidual :
      fullMixedModelBrauerBasisPairingResidualBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pairingResidualProof
      (p := p) (A := A) (G := G)
      (hresidual (A := A) (K := K) e0)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model pointwise residuals close the full mixed Brauer-basis readback input. -/
theorem fullMixedModelBrauerBasisReadbackInput_of_pointwiseResidualBlocker
    (hresidual :
      fullMixedModelBrauerBasisPointwiseResidualBlocker
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointwiseResidualProof
      (p := p) (A := A) (G := G)
      (hresidual (A := A) (K := K) e0)

/-- The full mixed Brauer-basis readback input closes the final Cartan range support theorem.

This is the direct non-circular integration API: readback gives the full mixed regular-value
source-faithful congruence, and the direct cokernel-product endpoint gives the final support
statement. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_fullMixedModelBrauerBasisReadbackInput
    (hread : fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  have hregular :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G) := by
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
        (p := p) (A := A) (K := K) (G := G)
        (hread (A := A) (K := K) e0)
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_fullMixedModelRegularValue
      (p := p) (k := k) (G := G) hregular

/-- Pairing-residual version of the final Cartan range support theorem. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_pairingResidualBlocker
    (hresidual :
      fullMixedModelBrauerBasisPairingResidualBlocker
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  have hread :
      fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pairingResidualProof
        (p := p) (A := A) (G := G)
        (hresidual (A := A) (K := K) e0)
  have hregular :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G) := by
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
        (p := p) (A := A) (K := K) (G := G)
        (hread (A := A) (K := K) e0)
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_fullMixedModelRegularValue
      (p := p) (k := k) (G := G) hregular

/-- Pointwise-residual version of the final Cartan range support theorem. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_pointwiseResidualBlocker
    (hresidual :
      fullMixedModelBrauerBasisPointwiseResidualBlocker
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  have hread :
      fullMixedModelBrauerBasisReadbackInput (p := p) (k := k) (G := G) := by
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      regularValueCongruenceSourceFaithfulBrauerBasisReadbackInput_of_pointwiseResidualProof
        (p := p) (A := A) (G := G)
        (hresidual (A := A) (K := K) e0)
  have hregular :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G) := by
    intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    exact
      regularValueCongruenceSourceFaithfulStatement_of_brauerBasisReadbackInput
        (p := p) (A := A) (K := K) (G := G)
        (hread (A := A) (K := K) e0)
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_fullMixedModelRegularValue
      (p := p) (k := k) (G := G) hregular

end FullMixedBrauerReadbackFinalIntegration

end Representation
