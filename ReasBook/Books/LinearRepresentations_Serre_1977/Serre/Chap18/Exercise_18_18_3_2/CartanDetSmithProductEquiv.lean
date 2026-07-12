import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanDetProductProducer
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanProjectiveSmith

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanDetSmithProductEquiv

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanDetSmithProductEquivFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanDetSmithProductEquivDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- The full mixed-model determinant product statement gives the intrinsic Smith-product input:
both sides compute the cardinality of the same Cartan cokernel. -/
theorem fullMixedModelCartanSmithNormalFormCoeffProductStatement_of_detProduct
    (hdet : fullMixedModelCartanDetNatAbsProductStatement (p := p) (k := k) (G := G)) :
    fullMixedModelCartanSmithNormalFormCoeffProductStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hdet (A := A) (K := K) e0 with
    ⟨ι, instFintype, instDecidableEq, π, hπ_pairwise, hπ_complete, P, hP_envelope,
      hdet_model⟩
  letI : Fintype ι := instFintype
  letI : DecidableEq ι := instDecidableEq
  let b : Module.Basis (PRegularConjClass G p) ℤ (R₀[IsLocalRing.ResidueField A](G)) :=
    Classical.choose
      (simple_basis_on_pRegular_classes_ring_owner
        (p := p) (k := IsLocalRing.ResidueField A) (G := G))
  let hfull :
      Module.finrank ℤ
          ((cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule) =
        Module.finrank ℤ (R₀[IsLocalRing.ResidueField A](G)) :=
    cartanProjectiveSmith_cartanRange_toIntSubmodule_finrank_eq
      (k := IsLocalRing.ResidueField A) (G := G)
  refine ⟨b, hfull, ?_⟩
  calc
    (∏ c : PRegularConjClass G p,
        Int.natAbs
          (Submodule.smithNormalFormCoeffs
            (N := (cartanHom (IsLocalRing.ResidueField A) G).range.toIntSubmodule)
            b hfull c)) =
        Nat.card (cartanCokernel (IsLocalRing.ResidueField A) G) := by
          exact
            (cartanCokernel_natCard_eq_prod_smithNormalFormCoeffs_field
              (p := p) (k := IsLocalRing.ResidueField A) (G := G)
              b hfull).symm
    _ =
        Int.natAbs
          (Matrix.det
            (cartanMatrix (IsLocalRing.ResidueField A) G
              (projectiveEnvelope_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete P hP_envelope)
              (simple_finiteRep_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete))) := by
          exact
            (cartanMatrix_det_natAbs_eq_cartanCokernel_natCard
              (p := p) (k := IsLocalRing.ResidueField A) (G := G)
              π hπ_pairwise hπ_complete P hP_envelope).symm
    _ = ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := hdet_model

omit [IsAlgClosed k] [CharP k p] in
/-- The determinant-product and Smith-product formulations of the full mixed-model 18.5(b)
input are equivalent. -/
theorem fullMixedModelCartanSmithNormalFormCoeffProductStatement_iff_detProduct :
    fullMixedModelCartanSmithNormalFormCoeffProductStatement
        (p := p) (k := k) (G := G) ↔
      fullMixedModelCartanDetNatAbsProductStatement
        (p := p) (k := k) (G := G) := by
  constructor
  · exact
      fullMixedModelCartanDetNatAbsProductStatement_of_smithNormalFormCoeffProduct
        (p := p) (k := k) (G := G)
  · exact
      fullMixedModelCartanSmithNormalFormCoeffProductStatement_of_detProduct
        (p := p) (k := k) (G := G)

end CartanDetSmithProductEquiv

end Representation
