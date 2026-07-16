import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanDetSmithProductEquiv
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCharacterLatticeCokernelDescent

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanDetProductSpanProducer

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanDetProductSpanProducerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanDetProductSpanProducerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-model source-span input for the determinant/Smith product route.

For each full mixed-characteristic model with residue field identified with `k`, this asks that
the fixed Cartan-coordinate `A`-span is exactly Serre's regular-value divisibility lattice.  This
is the non-circular source-side statement needed before the existing determinant and Smith
producers apply. -/
def fullMixedModelProjectiveCartanCoordinateSpanStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Full mixed-model determinant/product producer from the source-span input.

This only packages the already source-faithful per-model determinant endpoint; it does not use
the final formal range theorem or the final cokernel product theorem. -/
theorem fullMixedModelCartanDetNatAbsProductStatement_of_projectiveCartanCoordinate_span
    (hspan :
      fullMixedModelProjectiveCartanCoordinateSpanStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, _hπ_simple, _hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope⟩
  refine
    ⟨PRegularConjClass G p, inferInstance, inferInstance,
      π, hπ_pairwise, hπ_complete, P, hP_envelope, ?_⟩
  exact
    cartanMatrix_det_natAbs_eq_prod_centralizerPPart_of_projectiveCartanCoordinate_span_eq
      (p := p) (A := A) (K := K) (G := G)
      (hspan (A := A) (K := K) e0)
      π hπ_pairwise hπ_complete P hP_envelope

end CartanDetProductSpanProducer

end Representation
