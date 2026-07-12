import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanIntegerDescent

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanSourceProduct

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]

local notation "k" => IsLocalRing.ResidueField A

local instance projectiveCartanSourceProductFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

/-- Source-side quotient form of Serre 18.5(a), with the denominator lattice written as the
`A`-span of the Cartan range after reading modular characters on `p`-regular classes.

This is deliberately an `A`-linear source quotient statement. It avoids fixed regular-class
coordinates and Cartan matrix diagonalization, but it is not yet an integral
`cartanCokernel` statement; that final step still needs an integer lattice descent from this
source lattice to `R₀[k](G) / (cartanHom k G).range`. -/
noncomputable def virtualModularCartanRangeASpanQuotientLinearEquivPi
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s)) :
    ((PRegularConjClass G p → K) ⧸
        Submodule.span A
          (((cartanHom k G).range.map
            (virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift lift))) :
            Set (PRegularConjClass G p → K))) ≃ₗ[A]
      ∀ c : PRegularConjClass G p,
        K ⧸ Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K) := by
  let sourceSpan : Submodule A (PRegularConjClass G p → K) :=
    Submodule.span A
      (((cartanHom k G).range.map
        (virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift lift))) :
        Set (PRegularConjClass G p → K))
  have hsource :
      sourceSpan =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    have hcartan :=
      projectiveCharacterSubmodule_map_regularRestriction_eq_span_virtualModularCharacterOnPRegularConjClass_cartanHom_range
        (p := p) (A := A) (K := K) (G := G) lift hred hω
    have hdiv :=
      projectiveCharacterSubmodule_map_regularRestriction_eq_regularValueDivisibilitySubmodule
        (p := p) (A := A) (K := K) (G := G) hω
    exact hcartan.symm.trans hdiv
  exact
    (Submodule.Quotient.equiv
        sourceSpan
        (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
        (LinearEquiv.refl A (PRegularConjClass G p → K))
        (by
          simpa [sourceSpan] using hsource)).trans
      (regularValueDivisibilityQuotientLinearEquivPi
        (p := p) (A := A) (K := K) (G := G))

/-- Canonical complete-DVR root-lift specialization of
`virtualModularCartanRangeASpanQuotientLinearEquivPi`. -/
noncomputable def canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ((PRegularConjClass G p → K) ⧸
        Submodule.span A
          (((cartanHom k G).range.map
            (virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))))) :
            Set (PRegularConjClass G p → K))) ≃ₗ[A]
      ∀ c : PRegularConjClass G p,
        K ⧸ Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K) := by
  let liftK : PrimeToPRoot p k →* Kˣ :=
    projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)
  have hredK : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((liftK x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k) := by
    intro x
    refine ⟨((primeToPRoot_unitsLift (p := p) (A := A) x : Aˣ) : A), ?_, ?_⟩
    · simp [liftK, projectiveCartanASpanFieldLift]
    · exact residue_primeToPRoot_unitLift (p := p) (A := A) x
  have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
    intro s _hs
    haveI : HasEnoughRootsOfUnity K (orderOf s) :=
      HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
  exact
    virtualModularCartanRangeASpanQuotientLinearEquivPi
      (p := p) (A := A) (K := K) (G := G) liftK hredK hω

/-- Nonempty wrapper for the canonical source-side quotient product. -/
theorem canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi_nonempty
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    Nonempty
      (((PRegularConjClass G p → K) ⧸
          Submodule.span A
            (((cartanHom k G).range.map
              (virtualModularCharacterOnPRegularConjClass
                (p := p) (A := K) (G := G)
                (PrimeToPRoot.toFieldLift
                  (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))))) :
              Set (PRegularConjClass G p → K))) ≃ₗ[A]
        ∀ c : PRegularConjClass G p,
          K ⧸ Submodule.span A
            ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K)) :=
  ⟨canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi
    (p := p) (A := A) (K := K) (G := G)⟩

end ProjectiveCartanSourceProduct

end Representation
