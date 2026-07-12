import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanDetProductSpanProducer
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterDivisibilityEndpoint
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanSpanStability

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanCoordinateSpanProducer

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance projectiveCartanCoordinateSpanProducerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanCoordinateSpanProducerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-model quotient statement for the Cartan-coordinate `A`-span.

This is the non-circular source-side output already supplied by the projective-character lattice
route: the quotient by the Cartan-coordinate `A`-span is identified, after the Brauer-coordinate
transport, with the coordinatewise quotients by the centralizer-`p`-part ideals. It deliberately
does not assert that the fixed Cartan-coordinate span itself is the original divisibility lattice.
-/
def fullMixedModelProjectiveCartanCoordinateQuotientProductStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      Nonempty
        (((PRegularConjClass G p → K) ⧸
            Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K))) ≃ₗ[A]
          ∀ c : PRegularConjClass G p,
            K ⧸ Submodule.span A
              ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))

omit [IsAlgClosed k] [CharP k p] in
/-- Proven full mixed-model quotient product for the Cartan-coordinate `A`-span.

This is the strongest unconditional source-side statement available from the existing
projective-character APIs without adding the stronger fixed-coordinate span equality.
-/
theorem fullMixedModelProjectiveCartanCoordinateQuotientProductStatement_proof :
    fullMixedModelProjectiveCartanCoordinateQuotientProductStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP _e0
  exact
    projectiveCartanCoordinateASpanQuotientLinearEquivPi_nonempty
      (p := p) (A := A) (K := K) (G := G)

/-- Per-model diagnostic equivalence for the stronger fixed-coordinate span target.

The B2 source-span target is equivalent to saying that the fixed regular-class coordinate
equivalence itself sends the Cartan range to the diagonal integer lattice. This is stronger than
the final formal range theorem, which only asks for the existence of some coordinate equivalence.
-/
theorem projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_iff_coordinateRange_eq
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p] :
    (Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) =
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ↔
    (cartanCoordinateAddHom
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range =
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  constructor
  · intro hspan
    exact
      cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_span_eq
        (p := p) (A := A) (K := K) (G := G) hspan
  · intro hrange
    refine
      projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_of_range_le_and_scaled_mem
        (p := p) (A := A) (K := K) (G := G) ?_ ?_
    · rw [hrange]
    · intro c
      rw [hrange]
      change
        scaled_regular_integer_indicator (p := p) (G := G) c ∈
          regularIntegerDiagonalSubmodule (p := p) (G := G)
      rw [regularIntegerDiagonalSubmodule_eq_span_scaled_regular_integer_indicator
        (p := p) (G := G)]
      exact Submodule.subset_span ⟨c, rfl⟩

/-- Full mixed-model form of the fixed-coordinate Cartan range equality.

This is the exact fixed-coordinate theorem equivalent to the stronger B2 span target. It should
not be replaced by the final existential range endpoint without checking circularity and
strengthening. -/
def fullMixedModelFixedCartanCoordinateRangeStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup

omit [IsAlgClosed k] [CharP k p] in
/-- The fixed-coordinate range equality is exactly strong enough to prove the B2 span target. -/
theorem fullMixedModelProjectiveCartanCoordinateSpanStatement_of_fixedCoordinateRange
    (hrange :
      fullMixedModelFixedCartanCoordinateRangeStatement (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanCoordinateSpanStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  exact
    (projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_iff_coordinateRange_eq
      (p := p) (A := A) (K := K) (G := G)).2
      (hrange (A := A) (K := K) e0)

/-- Full mixed-model fixed-coordinate source inputs: coordinatewise divisibility of all Cartan
coordinate rows and one fixed-coordinate Cartan preimage of each scaled normalized simple class.

This isolates the smallest source-side inputs currently known to imply the stronger B2 span
target. The second clause is a fixed-coordinate generator statement, not the final existential
coordinate equivalence. -/
def fullMixedModelCartanCoordinateDivisibilityAndGeneratorsStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      ∃ π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G,
        (∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∧
        (∀ x : P₀[IsLocalRing.ResidueField A](G), ∀ c : PRegularConjClass G p,
          ∃ a : ℤ,
            cartanCoordinateAddHom
                (p := p) (k := IsLocalRing.ResidueField A) (G := G) x c =
              (ConjClasses.centralizerPPart p c.1 : ℤ) * a) ∧
        (∀ c : PRegularConjClass G p,
          ∃ x : P₀[IsLocalRing.ResidueField A](G),
            cartanHom (IsLocalRing.ResidueField A) G x =
              (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀)

omit [IsAlgClosed k] [CharP k p] in
/-- The coordinatewise divisibility plus fixed Cartan-generator source inputs give the exact
fixed-coordinate range equality. -/
theorem fullMixedModelFixedCartanCoordinateRangeStatement_of_coordinateDivisibilityAndGenerators
    (hsource :
      fullMixedModelCartanCoordinateDivisibilityAndGeneratorsStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelFixedCartanCoordinateRangeStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hsource (A := A) (K := K) e0 with ⟨π, hπ_coord, hdiv, hgen⟩
  exact
    cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_coordinate_divisible_and_cartan_generators
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)
      (π := π) hπ_coord hdiv hgen

omit [IsAlgClosed k] [CharP k p] in
/-- Source-side fixed-coordinate divisibility and generator inputs imply the B2 span target. -/
theorem fullMixedModelProjectiveCartanCoordinateSpanStatement_of_coordinateDivisibilityAndGenerators
    (hsource :
      fullMixedModelCartanCoordinateDivisibilityAndGeneratorsStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanCoordinateSpanStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hsource (A := A) (K := K) e0 with ⟨π, hπ_coord, hdiv, hgen⟩
  have hrange :
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
    cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_coordinate_divisible_and_cartan_generators
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)
      (π := π) hπ_coord hdiv hgen
  exact
    (projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_iff_coordinateRange_eq
      (p := p) (A := A) (K := K) (G := G)).2 hrange

/-- Full mixed-model forward Brauer-coordinate congruence on Serre's integer diagonal lattice.

Combined with the source-faithful regular-value congruence, this is exactly the remaining
fixed-coordinate stability input needed for the B2 span target. It is weaker than requiring
individual Cartan-column generators and does not use the final range/product theorem.
-/
def fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement : Prop :=
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
            ∀ f : PRegularConjClass G p → ℤ,
              f ∈ regularIntegerDiagonalSubmodule (p := p) (G := G) →
                projectiveCartanASpanBrauerRepr
                    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
                    (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) -
                  regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
                    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Source-faithful regular-value congruence plus the forward diagonal Brauer-coordinate
congruence proves the B2 Cartan-coordinate span target. -/
theorem fullMixedModelProjectiveCartanCoordinateSpanStatement_of_regularValue_and_forwardDiagonal
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G))
    (hforward :
      fullMixedModelBrauerReprForwardRegularIntegerDiagonalCongruenceStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelProjectiveCartanCoordinateSpanStatement (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hforward (A := A) (K := K) e0 with ⟨π, hπ_simple, hπ_coord, hdiag⟩
  exact
    projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_of_regularValue_congruence_and_brauerRepr_forward_regularIntegerDiagonal_congruence
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord
      (by
        simpa [regularValueCongruenceSourceFaithfulStatement] using
          hregular (A := A) (K := K) e0)
      hdiag

end ProjectiveCartanCoordinateSpanProducer

end Representation
