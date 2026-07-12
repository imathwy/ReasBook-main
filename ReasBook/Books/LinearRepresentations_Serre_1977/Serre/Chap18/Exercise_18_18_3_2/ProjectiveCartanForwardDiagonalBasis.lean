import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanCoordinateSpanProducer

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanForwardDiagonalBasis

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCartanForwardDiagonalBasisFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanForwardDiagonalBasisDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Basis-vector form of the forward Brauer-coordinate congruence on Serre's diagonal integer
lattice: it is enough to check the scaled point masses which generate the diagonal lattice. -/
theorem brauerRepr_forward_regularIntegerDiagonal_congruence_of_scaled_indicators
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hscaled :
      ∀ c : PRegularConjClass G p,
        projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
            (regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (scaled_regular_integer_indicator (p := p) (G := G) c)) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (scaled_regular_integer_indicator (p := p) (G := G) c) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
      ∀ f : PRegularConjClass G p → ℤ,
        f ∈ regularIntegerDiagonalSubmodule (p := p) (G := G) →
          projectiveCartanASpanBrauerRepr
              (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
              (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  classical
  let T :=
    projectiveCartanASpanBrauerRepr
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  let D := regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  intro f hf
  rw [regularIntegerDiagonalSubmodule_eq_span_scaled_regular_integer_indicator
    (p := p) (G := G)] at hf
  induction hf using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩
      simpa [T, D] using hscaled c
  | zero =>
      simp
  | add y z _ _ hy hz =>
      have hdiff :
          T (regularIntegerFunctionCast (p := p) (K := K) (G := G) (y + z)) -
              regularIntegerFunctionCast (p := p) (K := K) (G := G) (y + z) =
            (T (regularIntegerFunctionCast (p := p) (K := K) (G := G) y) -
                regularIntegerFunctionCast (p := p) (K := K) (G := G) y) +
              (T (regularIntegerFunctionCast (p := p) (K := K) (G := G) z) -
                regularIntegerFunctionCast (p := p) (K := K) (G := G) z) := by
        rw [map_add, map_add]
        abel
      rw [hdiff]
      exact D.add_mem hy hz
  | smul n y _ hy =>
      have hdiff :
          T (regularIntegerFunctionCast (p := p) (K := K) (G := G) (n • y)) -
              regularIntegerFunctionCast (p := p) (K := K) (G := G) (n • y) =
            n • (T (regularIntegerFunctionCast (p := p) (K := K) (G := G) y) -
              regularIntegerFunctionCast (p := p) (K := K) (G := G) y) := by
        rw [map_zsmul, map_zsmul, zsmul_sub]
      rw [hdiff]
      exact zsmul_mem hy n

end ProjectiveCartanForwardDiagonalBasis

section FullMixedModelProjectiveCartanForwardDiagonalBasis

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance fullMixedModelProjectiveCartanForwardDiagonalBasisFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance fullMixedModelProjectiveCartanForwardDiagonalBasisDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-model basis-vector version of the forward diagonal congruence. -/
def fullMixedModelBrauerReprForwardScaledIndicatorCongruenceStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      ∃ π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G,
        ∃ hπ_simple : ∀ c, Simple (π c),
          ∃ hπ_coord :
            ∀ c,
              regularClassCoordinateAddEquiv
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
            ∀ c : PRegularConjClass G p,
              projectiveCartanASpanBrauerRepr
                  (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
                  (regularIntegerFunctionCast (p := p) (K := K) (G := G)
                    (scaled_regular_integer_indicator (p := p) (G := G) c)) -
                regularIntegerFunctionCast (p := p) (K := K) (G := G)
                  (scaled_regular_integer_indicator (p := p) (G := G) c) ∈
                  regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- The scaled-indicator basis-vector task implies the whole-diagonal forward congruence used by
`ProjectiveCartanCoordinateSpanProducer`. -/
theorem fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement_of_scaledIndicators
    (hscaled :
      fullMixedModelBrauerReprForwardScaledIndicatorCongruenceStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hscaled (A := A) (K := K) e0 with ⟨π, hπ_simple, hπ_coord, hbasis⟩
  refine ⟨π, hπ_simple, hπ_coord, ?_⟩
  exact
    brauerRepr_forward_regularIntegerDiagonal_congruence_of_scaled_indicators
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hbasis

end FullMixedModelProjectiveCartanForwardDiagonalBasis

end Representation
