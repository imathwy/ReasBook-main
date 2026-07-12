import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanCokernelProductRegularValueEndpoint
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanFormalRangeCokernelProductEndpoint
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularValueCongruenceSourceFaithful

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanCokernelProductDirect

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanCokernelProductDirectFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanCokernelProductDirectDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Minimal remaining source-faithful input for the direct cokernel-product route.

For every full mixed-characteristic model with residue field identified with `k`, virtual
modular characters must be congruent to their integer regular-class coordinate functions modulo
Serre's regular-value divisibility lattice. This is exactly the non-cyclic input left by the
current API; the reverse source-product representatives are then formal. -/
def fullMixedModelRegularValueCongruenceSourceFaithfulStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      regularValueCongruenceSourceFaithfulStatement
        (p := p) (A := A) (K := K) (G := G)

include p in
/-- Direct abstract cokernel-product endpoint from the minimal regular-value congruence input.

This is the shortest clean conditional chain for the non-cyclic route: no fixed Cartan-column
diagonalization is used. -/
theorem cartanCokernel_product_of_fullMixedModelRegularValueCongruence
    (hregular :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G)) :
    Nonempty
      (cartanCokernel k G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
  refine
    cartanCokernel_product_via_fullMixedModel_regularValue_congruence
      (p := p) (k := k) (G := G) ?_
  intro A instComm instLocal instHenselian instDomain instDVR instNoetherian instComplete
    K instField instAlgebra instFraction instCharZero instRoots instAlgClosed instCharP e0
  exact hregular (A := A) (K := K) e0

include p in
/-- Cartan-range support endpoint obtained from the direct abstract cokernel-product route.

This is the conditional replacement for the support gap in `CartanFormalRange.lean`; the only
remaining mathematical input is
`fullMixedModelRegularValueCongruenceSourceFaithfulStatement`. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_fullMixedModelRegularValue
    (hregular :
      fullMixedModelRegularValueCongruenceSourceFaithfulStatement
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_cokernelProduct_endpoint
    (p := p) (k := k) (G := G)
    (cartanCokernel_product_of_fullMixedModelRegularValueCongruence
      (p := p) (k := k) (G := G) hregular)

end CartanCokernelProductDirect

end Representation
