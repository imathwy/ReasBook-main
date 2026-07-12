import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterDivisibilityEndpoint

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanSpanProviderFinal

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCartanSpanProviderFinalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanSpanProviderFinalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Direct combination of Serre 18.5(a) in regular-restriction form with the Cartan-coordinate
Brauer-readback theorem.

This is the strongest unconditional statement obtained from
`projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule` and
`projectiveCharacterSubmodule_regularRestriction_brauerRepr_eq_cartanCoordinate_span`: it proves
`T(D) = S`, where `D` is Serre's regular value-divisibility lattice, `T` is the chosen
Brauer-coordinate map, and `S` is the fixed Cartan-coordinate span. It does not identify `S` with
`D`. -/
theorem projectiveCharacter_regularRestriction_brauerRepr_regularValueDivisibility_eq_cartanCoordinate_span_final
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    Submodule.map
        (projectiveCartanASpanBrauerRepr
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
        (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
      Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) := by
  rw [← projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule
    (p := p) (A := A) (K := K) (G := G)]
  exact
    projectiveCharacterSubmodule_regularRestriction_brauerRepr_eq_cartanCoordinate_span
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

/-- Precise blocker for the fixed-coordinate span target.

After the unconditional image theorem above, the desired equality `S = D` is equivalent to
Brauer-coordinate stability `T(D) = D`. Thus the two projective-character facts alone leave exactly
the missing input `Submodule.map T D = D` (or an equivalent forward diagonal/fixed-coordinate range
statement). -/
theorem projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_iff_brauerRepr_stable_final
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    (Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) =
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ↔
      Submodule.map
          (projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  exact
    cartanCoordinate_span_eq_regularValueDivisibilitySubmodule_iff_brauerRepr_stable
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

/-- Conditional source-span provider: Brauer-coordinate stability is sufficient to prove the
mixed-characteristic fixed-coordinate span equality. -/
theorem projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_of_brauerRepr_stable_final
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hstable :
      Submodule.map
          (projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) =
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  exact
    (projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_iff_brauerRepr_stable_final
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).2 hstable

/-- The same conditional source-span input in the exact existential coordinate-equivalence form
needed by the upstream saturation bridge. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_brauerRepr_stable_final
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hstable :
      Submodule.map
          (projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    ∃ e : R₀[IsLocalRing.ResidueField A](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom (IsLocalRing.ResidueField A) G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_span_eq
      (p := p) (A := A) (K := K) (G := G)
      (projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_of_brauerRepr_stable_final
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hstable)

end ProjectiveCartanSpanProviderFinal

section ProjectiveCartanSpanProviderFinalFullMixed

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance projectiveCartanSpanProviderFinalFullMixedFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanSpanProviderFinalFullMixedDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-characteristic version of the precise blocker isolated above. -/
def fullMixedModelBrauerReprRegularValueDivisibilityStableStatement : Prop :=
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
            Submodule.map
                (projectiveCartanASpanBrauerRepr
                  (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
                (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

omit [IsAlgClosed k] [CharP k p] in
/-- Strongest compiled conditional provider obtained in this file: a full mixed-characteristic
Brauer-stability input supplies the requested fixed-coordinate span equality for every model. -/
theorem fullMixedModelProjectiveCartanCoordinateSpanStatement_of_brauerRepr_stable_final
    (hstable :
      fullMixedModelBrauerReprRegularValueDivisibilityStableStatement
        (p := p) (k := k) (G := G)) :
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
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hstable (A := A) (K := K) e0 with ⟨π, hπ_simple, hπ_coord, hstable_model⟩
  exact
    projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_of_brauerRepr_stable_final
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hstable_model

end ProjectiveCartanSpanProviderFinalFullMixed

end Representation
