import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanFormalRangeSourceProductTransport
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CanonicalSourceProductImageFromSerreBasis

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section CartanFormalRangeSerreBasisEndpoint

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanFormalRangeSerreBasisEndpointFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanFormalRangeSerreBasisEndpointDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

include p in
/-- Terminal adapter from Serre-basis projective witnesses to the formal Cartan range support
statement.

This theorem performs only the endpoint plumbing: it converts the supplied Serre 18.4/18.5(a)
projective-witness data into the canonical source-product image statement, then applies the
existing full mixed-characteristic transport endpoint. -/
theorem
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_serreBasisProjectiveWitness
    (hwitness :
      ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
        [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent G)]
        [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
        IsLocalRing.ResidueField A ≃+* k →
          ∃ (ι : Type x) (_ : Fintype ι) (_ : DecidableEq ι)
            (π : ι → FDRep (IsLocalRing.ResidueField A) G),
              PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π ∧
                canonicalSourceProductSerreBasisForwardProjectiveWitness
                  (p := p) (A := A) (K := K) (G := G) π ∧
                canonicalSourceProductSerreBasisReversePointProjectiveWitness
                  (p := p) (A := A) (K := K) (G := G) π) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_fullMixedModel_sourceProductImage
      (p := p) (k := k) (G := G) ?_
  intro A instComm instLocal instHenselian instDomain instDVR instNoeth instComplete
    K instField instAlg instFrac instCharZero instRoots instAlgClosed instCharP e0
  rcases hwitness (A := A) (K := K) e0 with
    ⟨ι, instFintype, instDecidableEq, π, hπ_pairwise, hπ_complete, hforward, hreverse⟩
  letI := instFintype
  letI := instDecidableEq
  exact
    canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_serreBasis_projectiveWitness
      (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete hforward hreverse

end CartanFormalRangeSerreBasisEndpoint

end Representation
