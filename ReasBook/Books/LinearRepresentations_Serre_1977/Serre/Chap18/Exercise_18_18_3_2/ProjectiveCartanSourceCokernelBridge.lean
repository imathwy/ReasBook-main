import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanSourceProduct
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanCokernelSmith
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanCokernelSaturation
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanIntegerImageForward

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanSourceCokernelBridge

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCartanSourceCokernelBridgeFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanSourceCokernelBridgeDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The canonical source-side Cartan span appearing in the Serre 18.5(a) product quotient. -/
noncomputable def canonicalVirtualModularCartanRangeASpan :
    Submodule A (PRegularConjClass G p → K) :=
  Submodule.span A
    (((cartanHom (IsLocalRing.ResidueField A) G).range.map
      (virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))))) :
      Set (PRegularConjClass G p → K))

/-- The canonical virtual-modular Cartan span is Serre's coordinatewise divisibility lattice. -/
theorem canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule :
    canonicalVirtualModularCartanRangeASpan (p := p) (A := A) (K := K) (G := G) =
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  let liftK : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ :=
    projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)
  have hredK : ∀ x : PrimeToPRoot p (IsLocalRing.ResidueField A), ∃ a : A,
      algebraMap A K a = ((liftK x : Kˣ) : K) ∧
        IsLocalRing.residue A a =
          ((x : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A) := by
    intro x
    refine ⟨((primeToPRoot_unitsLift (p := p) (A := A) x : Aˣ) : A), ?_, ?_⟩
    · simp [liftK, projectiveCartanASpanFieldLift]
    · exact residue_primeToPRoot_unitLift (p := p) (A := A) x
  have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
    intro s _hs
    haveI : HasEnoughRootsOfUnity K (orderOf s) :=
      HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
  have hcartan :=
    projectiveCharacterSubmodule_map_regularRestriction_eq_span_virtualModularCharacterOnPRegularConjClass_cartanHom_range
      (p := p) (A := A) (K := K) (G := G) liftK hredK hω
  have hdiv :=
    projectiveCharacterSubmodule_map_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G) hω
  exact hcartan.symm.trans hdiv

/-- Brauer-coordinate readback for the canonical virtual modular character map, in the exact
`regularIntegerFunctionCast` form used by the source-to-cokernel kernel argument. -/
theorem projectiveCartanASpanBrauerRepr_virtualModularCharacter
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (x : R₀[IsLocalRing.ResidueField A](G)) :
    projectiveCartanASpanBrauerRepr (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord
        (virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x) =
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (regularClassCoordinateAddEquiv
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) := by
  ext d
  simpa [projectiveCartanASpanBrauerRepr, projectiveCartanASpanBrauerBasis,
    regularIntegerFunctionCast, projectiveCartanASpanFieldLift] using
    (virtualModularCharacter_basis_repr_eq_cast_regularClassCoordinate
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) (K' := K)
      (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))
      (projectiveCartanASpanFieldLift_injective (p := p) (A := A) (K := K))
      π hπ_simple hπ_coord x d)

/-- Applying the Brauer-coordinate readback map to the canonical source-side Cartan span gives
the fixed Cartan-coordinate `A`-span.

This is only a coordinate-readback statement: it does not assert that the Brauer-coordinate
change of basis preserves Serre's divisibility lattice. -/
theorem projectiveCartanASpanBrauerRepr_canonicalVirtualModularCartanRangeASpan_eq_cartanCoordinate_span
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
        (canonicalVirtualModularCartanRangeASpan
          (p := p) (A := A) (K := K) (G := G)) =
      Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) := by
  simpa [canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule
    (p := p) (A := A) (K := K) (G := G)] using
    projectiveCartanASpanBrauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

/-- The canonical source quotient map induced by virtual modular characters on the Cartan
cokernel. Its codomain is the source-side quotient from Serre 18.5(a), not the fixed-coordinate
Cartan-span quotient. -/
noncomputable def cartanCokernelToCanonicalVirtualModularCartanRangeASpanQuotient :
    cartanCokernel (IsLocalRing.ResidueField A) G →+
      ((PRegularConjClass G p → K) ⧸
        canonicalVirtualModularCartanRangeASpan (p := p) (A := A) (K := K) (G := G)) := by
  let N : AddSubgroup R₀[IsLocalRing.ResidueField A](G) :=
    (cartanHom (IsLocalRing.ResidueField A) G).range
  let S : Submodule A (PRegularConjClass G p → K) :=
    canonicalVirtualModularCartanRangeASpan (p := p) (A := A) (K := K) (G := G)
  let χ : R₀[IsLocalRing.ResidueField A](G) →+ (PRegularConjClass G p → K) :=
    virtualModularCharacterOnPRegularConjClass
      (p := p) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
  let φ : R₀[IsLocalRing.ResidueField A](G) →+ ((PRegularConjClass G p → K) ⧸ S) :=
    S.mkQ.toAddMonoidHom.comp χ
  exact QuotientAddGroup.lift N φ (by
    intro x hx
    change Submodule.Quotient.mk (p := S) (χ x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span (by
      change χ x ∈
        (((cartanHom (IsLocalRing.ResidueField A) G).range.map χ) :
          Set (PRegularConjClass G p → K))
      exact ⟨x, by simpa [N] using hx, rfl⟩))

@[simp]
theorem cartanCokernelToCanonicalVirtualModularCartanRangeASpanQuotient_mk
    (x : R₀[IsLocalRing.ResidueField A](G)) :
    cartanCokernelToCanonicalVirtualModularCartanRangeASpanQuotient
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x) =
      (Submodule.Quotient.mk
        (p := canonicalVirtualModularCartanRangeASpan
          (p := p) (A := A) (K := K) (G := G))
        (virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x)) := by
  rw [cartanCokernelToCanonicalVirtualModularCartanRangeASpanQuotient]
  rfl

/-- The canonical source quotient map is injective. This is the integral descent step needed to
compare Serre's source product with the actual Cartan cokernel: a class whose virtual modular
character lies in the canonical source span already lies in the Cartan range. -/
theorem cartanCokernelToCanonicalVirtualModularCartanRangeASpanQuotient_injective :
    Function.Injective
      (cartanCokernelToCanonicalVirtualModularCartanRangeASpanQuotient
        (p := p) (A := A) (K := K) (G := G)) := by
  rw [← AddMonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro q hq
    rw [AddSubgroup.mem_bot]
    revert hq
    refine QuotientAddGroup.induction_on q ?_
    intro x hx
    have hxquot :
        cartanCokernelToCanonicalVirtualModularCartanRangeASpanQuotient
            (p := p) (A := A) (K := K) (G := G)
            (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x) =
          0 := by
      simpa [AddMonoidHom.mem_ker] using hx
    have hxsource :
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x ∈
          canonicalVirtualModularCartanRangeASpan (p := p) (A := A) (K := K) (G := G) := by
      rw [cartanCokernelToCanonicalVirtualModularCartanRangeASpanQuotient_mk] at hxquot
      exact (Submodule.Quotient.mk_eq_zero
        (p := canonicalVirtualModularCartanRangeASpan
          (p := p) (A := A) (K := K) (G := G))).1 hxquot
    have hxregular :
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
      simpa [canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule
        (p := p) (A := A) (K := K) (G := G)] using hxsource
    rcases
        exists_coordinate_normalized_complete_family_with_projective_envelopes
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
      ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
    let B : (PRegularConjClass G p → K) →ₗ[A] (PRegularConjClass G p → K) :=
      projectiveCartanASpanBrauerRepr
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
    have hxB :
        B
          (virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x) ∈
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K)) := by
      have hxmap :
          B
            (virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x) ∈
            Submodule.map B
              (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :=
        ⟨_, hxregular, rfl⟩
      simpa [B,
        projectiveCartanASpanBrauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord] using hxmap
    have hxcast :
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K)) := by
      simpa [B,
        projectiveCartanASpanBrauerRepr_virtualModularCharacter
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord x] using hxB
    have hxcoord :
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) x ∈
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range :=
      (regularIntegerFunctionCast_mem_projectiveCartanCoordinate_span_iff_mem_cartanCoordinateAddHom_range
        (p := p) (A := A) (K := K) (G := G)
        (regularClassCoordinateAddEquiv
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) x)).1 hxcast
    rw [cartanCoordinateAddHom_range_eq_cartanHom_range_map
      (p := p) (A := A) (G := G)] at hxcoord
    rcases hxcoord with ⟨y, hy, hyx⟩
    have hxy : x = y := by
      apply (regularClassCoordinateAddEquiv
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)).injective
      simpa using hyx.symm
    exact
      (QuotientAddGroup.eq_zero_iff
        (N := (cartanHom (IsLocalRing.ResidueField A) G).range) x).2
        (by simpa [hxy] using hy)
  · exact bot_le

/-- The canonical source product map from the Cartan cokernel into Serre's displayed product of
fraction-field quotients. Its range is the source-product image whose identification is the
remaining Serre 18.5(b) input. -/
noncomputable def cartanCokernelToCanonicalVirtualModularCartanProduct :
    cartanCokernel (IsLocalRing.ResidueField A) G →+
      ∀ c : PRegularConjClass G p,
        K ⧸ Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K) :=
  (canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi
      (p := p) (A := A) (K := K) (G := G)).toAddMonoidHom.comp
    (cartanCokernelToCanonicalVirtualModularCartanRangeASpanQuotient
      (p := p) (A := A) (K := K) (G := G))

@[simp]
theorem cartanCokernelToCanonicalVirtualModularCartanProduct_mk
    (x : R₀[IsLocalRing.ResidueField A](G)) :
    cartanCokernelToCanonicalVirtualModularCartanProduct
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x) =
      (canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi
        (p := p) (A := A) (K := K) (G := G))
        (Submodule.Quotient.mk
          (p := canonicalVirtualModularCartanRangeASpan
            (p := p) (A := A) (K := K) (G := G))
          (virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x)) := by
  change
    (canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi
      (p := p) (A := A) (K := K) (G := G)).toAddMonoidHom
      (cartanCokernelToCanonicalVirtualModularCartanRangeASpanQuotient
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x)) =
      (canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi
        (p := p) (A := A) (K := K) (G := G))
        (Submodule.Quotient.mk
          (p := canonicalVirtualModularCartanRangeASpan
            (p := p) (A := A) (K := K) (G := G))
          (virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x))
  rw [cartanCokernelToCanonicalVirtualModularCartanRangeASpanQuotient_mk]
  rfl

@[simp]
theorem cartanCokernelToCanonicalVirtualModularCartanProduct_mk_apply
    (x : R₀[IsLocalRing.ResidueField A](G)) (c : PRegularConjClass G p) :
    cartanCokernelToCanonicalVirtualModularCartanProduct
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x) c =
      (canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi
        (p := p) (A := A) (K := K) (G := G))
        (Submodule.Quotient.mk
          (p := canonicalVirtualModularCartanRangeASpan
            (p := p) (A := A) (K := K) (G := G))
          (virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x)) c := by
  rw [cartanCokernelToCanonicalVirtualModularCartanProduct_mk]

@[simp]
theorem canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi_mk_apply
    (x : PRegularConjClass G p → K) (c : PRegularConjClass G p) :
    canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi
        (p := p) (A := A) (K := K) (G := G)
        (Submodule.Quotient.mk
          (p := canonicalVirtualModularCartanRangeASpan
            (p := p) (A := A) (K := K) (G := G)) x) c =
      Submodule.Quotient.mk
        (p := Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
        (x c) := by
  unfold canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi
  unfold virtualModularCartanRangeASpanQuotientLinearEquivPi
  rw [LinearEquiv.trans_apply]
  rw [Submodule.Quotient.equiv_apply]
  change
    regularValueDivisibilityQuotientLinearEquivPi
        (p := p) (A := A) (K := K) (G := G)
        (Submodule.Quotient.mk
          (p := regularValueDivisibilitySubmodule
            (p := p) (A := A) (K := K) (G := G)) x) c =
      Submodule.Quotient.mk
        (p := Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
        (x c)
  rw [regularValueDivisibilityQuotientLinearEquivPi_mk_apply]

/-- The concrete Cartan product map and the canonical source-product map agree on corresponding
integer representatives.

This is only a definition-level bridge: it uses the Brauer-coordinate readback theorem
`projectiveCartanASpanBrauerRepr_virtualModularCharacter`, and does not assert any point-mass
congruence for Brauer character values. -/
theorem concreteProjectiveCartanProduct_mk_regularClassCoordinate_eq_canonicalProduct_mk
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (x : R₀[IsLocalRing.ResidueField A](G)) :
    cartanCoordinateRangeQuotientToProjectiveCartanProduct
        (p := p) (A := A) (K := K) (G := G)
        (projectiveCartanCoordinateASpanQuotientLinearEquivPi
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
        (QuotientAddGroup.mk'
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range
          (regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) x)) =
      cartanCokernelToCanonicalVirtualModularCartanProduct
        (p := p) (A := A) (K := K) (G := G)
        (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x) := by
  ext c
  rw [concreteProjectiveCartanProduct_integerRepresentative_apply
    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
    (regularClassCoordinateAddEquiv
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) c]
  rw [cartanCokernelToCanonicalVirtualModularCartanProduct_mk_apply]
  rw [canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi_mk_apply]
  let χ : PRegularConjClass G p → K :=
    virtualModularCharacterOnPRegularConjClass
      (p := p) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x
  let coord : PRegularConjClass G p → ℤ :=
    regularClassCoordinateAddEquiv
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) x
  let T : (PRegularConjClass G p → K) ≃ₗ[A] (PRegularConjClass G p → K) :=
    projectiveCartanASpanBrauerReprLinearEquiv
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  have hT : T χ = regularIntegerFunctionCast (p := p) (K := K) (G := G) coord := by
    simpa [T, χ, coord, projectiveCartanASpanBrauerReprLinearEquiv_toLinearMap
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord] using
      projectiveCartanASpanBrauerRepr_virtualModularCharacter
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord x
  have hsymm :
      T.symm (regularIntegerFunctionCast (p := p) (K := K) (G := G) coord) = χ := by
    rw [← hT]
    simp [T]
  change
    Submodule.Quotient.mk
        (p := Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
        (T.symm (regularIntegerFunctionCast (p := p) (K := K) (G := G) coord) c) =
      Submodule.Quotient.mk
        (p := Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K))
        (χ c)
  rw [hsymm]

/-- The concrete fixed-coordinate product image is exactly the canonical source-product image.

The proof is by representatives, using the fixed coordinate equivalence between
`R₀[k](G)` and integer-valued regular-class functions. This records the honest image equality
available from the definitions, before any comparison with the coordinatewise integer image. -/
theorem concreteProjectiveCartanProduct_range_eq_canonicalVirtualModularCartanProduct_range
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    (cartanCoordinateRangeQuotientToProjectiveCartanProduct
        (p := p) (A := A) (K := K) (G := G)
        (projectiveCartanCoordinateASpanQuotientLinearEquivPi
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)).range =
      (cartanCokernelToCanonicalVirtualModularCartanProduct
        (p := p) (A := A) (K := K) (G := G)).range := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    refine QuotientAddGroup.induction_on q ?_
    intro f
    let x : R₀[IsLocalRing.ResidueField A](G) :=
      (regularClassCoordinateAddEquiv
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)).symm f
    refine
      ⟨QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x, ?_⟩
    have hx :
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) x = f := by
      simp [x]
    have hcalc :
        cartanCoordinateRangeQuotientToProjectiveCartanProduct
            (p := p) (A := A) (K := K) (G := G)
            (projectiveCartanCoordinateASpanQuotientLinearEquivPi
              (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
            (QuotientAddGroup.mk'
              (cartanCoordinateAddHom
                (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range f) =
          cartanCokernelToCanonicalVirtualModularCartanProduct
            (p := p) (A := A) (K := K) (G := G)
            (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x) := by
      calc
        cartanCoordinateRangeQuotientToProjectiveCartanProduct
            (p := p) (A := A) (K := K) (G := G)
            (projectiveCartanCoordinateASpanQuotientLinearEquivPi
              (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
            (QuotientAddGroup.mk'
              (cartanCoordinateAddHom
                (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range f) =
          cartanCoordinateRangeQuotientToProjectiveCartanProduct
            (p := p) (A := A) (K := K) (G := G)
            (projectiveCartanCoordinateASpanQuotientLinearEquivPi
              (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
            (QuotientAddGroup.mk'
              (cartanCoordinateAddHom
                (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range
              (regularClassCoordinateAddEquiv
                (p := p) (k := IsLocalRing.ResidueField A) (G := G) x)) := by
              rw [hx]
        _ =
          cartanCokernelToCanonicalVirtualModularCartanProduct
            (p := p) (A := A) (K := K) (G := G)
            (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x) :=
              concreteProjectiveCartanProduct_mk_regularClassCoordinate_eq_canonicalProduct_mk
                (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord x
    exact hcalc.symm
  · rintro ⟨q, rfl⟩
    refine QuotientAddGroup.induction_on q ?_
    intro x
    refine
      ⟨QuotientAddGroup.mk'
        (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range
        (regularClassCoordinateAddEquiv
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) x), ?_⟩
    exact
      concreteProjectiveCartanProduct_mk_regularClassCoordinate_eq_canonicalProduct_mk
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord x

/-- The source product map is injective, by the source-quotient injectivity and the canonical
Serre 18.5(a) product equivalence. -/
theorem cartanCokernelToCanonicalVirtualModularCartanProduct_injective :
    Function.Injective
      (cartanCokernelToCanonicalVirtualModularCartanProduct
        (p := p) (A := A) (K := K) (G := G)) := by
  exact
    (canonicalVirtualModularCartanRangeASpanQuotientLinearEquivPi
      (p := p) (A := A) (K := K) (G := G)).injective.comp
      (cartanCokernelToCanonicalVirtualModularCartanRangeASpanQuotient_injective
        (p := p) (A := A) (K := K) (G := G))

/-- The Cartan cokernel is additively equivalent to its canonical source-product image. -/
noncomputable def cartanCokernel_addEquiv_canonicalVirtualModularCartanProductRange :
    cartanCokernel (IsLocalRing.ResidueField A) G ≃+
      (cartanCokernelToCanonicalVirtualModularCartanProduct
        (p := p) (A := A) (K := K) (G := G)).range :=
  AddMonoidHom.ofInjective
    (cartanCokernelToCanonicalVirtualModularCartanProduct_injective
      (p := p) (A := A) (K := K) (G := G))

/-- Source-product-to-cokernel bridge in cyclic-product form.

Once Serre 18.5(b) identifies the actual image of the canonical source product map with the
displayed product of cyclic groups, the Cartan cokernel has that product decomposition. -/
theorem cartanCokernel_nonempty_addEquiv_pi_of_canonicalVirtualModularCartanProductRange
    (himage :
      Nonempty
        ((cartanCokernelToCanonicalVirtualModularCartanProduct
            (p := p) (A := A) (K := K) (G := G)).range ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1))) :
    Nonempty
      (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
  rcases himage with ⟨himage⟩
  exact
    ⟨(cartanCokernel_addEquiv_canonicalVirtualModularCartanProductRange
        (p := p) (A := A) (K := K) (G := G)).trans himage⟩

/-- Source-product image identification against the coordinatewise integer image.

This is the source-faithful finite-image formulation of Serre 18.5(b): it does not identify the
whole `K / dA` product with a finite group, only the actual image of the integral Cartan cokernel
inside it. -/
def canonicalVirtualModularCartanProductImageMatchesIntegerImage : Prop :=
  Nonempty
    ((cartanCokernelToCanonicalVirtualModularCartanProduct
        (p := p) (A := A) (K := K) (G := G)).range ≃+
      (regularIntegerDiagonalQuotientToIntegerImageProduct
        (p := p) (A := A) (K := K) (G := G)).range)

/-- The concrete fixed-coordinate product image match follows from the canonical source-product
image match.

The only comparison step is the actual range equality
`concreteProjectiveCartanProduct_range_eq_canonicalVirtualModularCartanProduct_range`; no
point-mass Brauer character value congruence is used. -/
theorem concreteProjectiveCartanProductImageMatchesIntegerImage_of_canonicalVirtualModularCartanProductImage
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (himage :
      canonicalVirtualModularCartanProductImageMatchesIntegerImage
        (p := p) (A := A) (K := K) (G := G)) :
    concreteProjectiveCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord := by
  dsimp [concreteProjectiveCartanProductImageMatchesIntegerImage]
  rw [concreteProjectiveCartanProduct_range_eq_canonicalVirtualModularCartanProduct_range
    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord]
  exact himage

/-- If the canonical source-product image is the coordinatewise integer image, then Serre's
cyclic-product cokernel decomposition follows formally. -/
theorem cartanCokernel_nonempty_addEquiv_pi_of_canonicalVirtualModularCartanProductImage
    (himage :
      canonicalVirtualModularCartanProductImageMatchesIntegerImage
        (p := p) (A := A) (K := K) (G := G)) :
    Nonempty
      (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
  rcases himage with ⟨himage⟩
  exact
    ⟨(cartanCokernel_addEquiv_canonicalVirtualModularCartanProductRange
        (p := p) (A := A) (K := K) (G := G)).trans
      (himage.trans
        (regularIntegerDiagonalQuotientToIntegerImageProductRangeAddEquivPiZMod
          (p := p) (A := A) (K := K) (G := G)))⟩

/-- Representative-level criterion for the canonical source-product image.

The forward hypothesis checks every residue-field virtual character representative of the
Cartan cokernel. The reverse hypothesis checks every integer regular-class representative of
Serre's displayed diagonal quotient. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_integerRepresentatives
    (hforward :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        ∃ g : PRegularConjClass G p → ℤ,
          cartanCokernelToCanonicalVirtualModularCartanProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x) =
            regularIntegerDiagonalQuotientToIntegerImageProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk'
                (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g))
    (hreverse :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ x : R₀[IsLocalRing.ResidueField A](G),
          regularIntegerDiagonalQuotientToIntegerImageProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk'
                (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g) =
            cartanCokernelToCanonicalVirtualModularCartanProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x)) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) := by
  let φ :=
    cartanCokernelToCanonicalVirtualModularCartanProduct
      (p := p) (A := A) (K := K) (G := G)
  let ψ :=
    regularIntegerDiagonalQuotientToIntegerImageProduct
      (p := p) (A := A) (K := K) (G := G)
  refine range_nonempty_addEquiv_of_mutualRepresentativeImages φ ψ ?_ ?_
  · intro q
    refine QuotientAddGroup.induction_on q ?_
    intro x
    rcases hforward x with ⟨g, hg⟩
    refine ⟨QuotientAddGroup.mk'
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g, ?_⟩
    simpa [φ, ψ] using hg
  · intro q
    refine QuotientAddGroup.induction_on q ?_
    intro g
    rcases hreverse g with ⟨x, hx⟩
    refine ⟨QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x, ?_⟩
    simpa [φ, ψ] using hx

/-- Coordinatewise quotient form of the forward representative condition for the canonical
source-product image. -/
theorem canonicalVirtualModularCartanProduct_forwardRepresentative_of_coordinateQuotients
    (hquot :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        ∃ g : PRegularConjClass G p → ℤ,
          ∀ c : PRegularConjClass G p,
            cartanCokernelToCanonicalVirtualModularCartanProduct
                (p := p) (A := A) (K := K) (G := G)
                (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x) c =
              integerQuotientImageHom
                (A := A) (K := K) (ConjClasses.centralizerPPart p c.1) (g c)) :
      ∀ x : R₀[IsLocalRing.ResidueField A](G),
        ∃ g : PRegularConjClass G p → ℤ,
          cartanCokernelToCanonicalVirtualModularCartanProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x) =
            regularIntegerDiagonalQuotientToIntegerImageProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk'
                (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g) := by
  intro x
  rcases hquot x with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  ext c
  rw [regularIntegerDiagonalQuotientToIntegerImageProduct_mk]
  exact hg c

/-- The reverse representative condition for the canonical source-product image can be checked
on the point-mass generators of the integer regular-class lattice. This is the parallelizable
form of the reverse half of Serre 18.5(b). -/
theorem canonicalVirtualModularCartanProduct_reverseRepresentative_of_single
    (hsingle :
      ∀ c : PRegularConjClass G p,
        ∃ x : R₀[IsLocalRing.ResidueField A](G),
          regularIntegerDiagonalQuotientToIntegerImageProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk'
                (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) =
            cartanCokernelToCanonicalVirtualModularCartanProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x)) :
      ∀ g : PRegularConjClass G p → ℤ,
        ∃ x : R₀[IsLocalRing.ResidueField A](G),
          regularIntegerDiagonalQuotientToIntegerImageProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk'
                (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup g) =
            cartanCokernelToCanonicalVirtualModularCartanProduct
              (p := p) (A := A) (K := K) (G := G)
              (QuotientAddGroup.mk' (cartanHom (IsLocalRing.ResidueField A) G).range x) := by
  classical
  intro g
  choose x hx using hsingle
  let D : AddSubgroup (PRegularConjClass G p → ℤ) :=
    (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup
  let N : AddSubgroup R₀[IsLocalRing.ResidueField A](G) :=
    (cartanHom (IsLocalRing.ResidueField A) G).range
  let φ :=
    cartanCokernelToCanonicalVirtualModularCartanProduct
      (p := p) (A := A) (K := K) (G := G)
  let ψ :=
    regularIntegerDiagonalQuotientToIntegerImageProduct
      (p := p) (A := A) (K := K) (G := G)
  refine ⟨∑ c : PRegularConjClass G p, g c • x c, ?_⟩
  have hsum_fun :
      (∑ c : PRegularConjClass G p,
          g c • (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) = g := by
    ext c
    simp [Pi.single_apply]
  have hmkD :
      QuotientAddGroup.mk' D g =
        ∑ c : PRegularConjClass G p,
          g c • QuotientAddGroup.mk' D
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) := by
    calc
      QuotientAddGroup.mk' D g =
          QuotientAddGroup.mk' D
            (∑ c : PRegularConjClass G p,
              g c • (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) := by
            rw [hsum_fun]
      _ =
          ∑ c : PRegularConjClass G p,
            QuotientAddGroup.mk' D
              (g c • (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) := by
            rw [map_sum]
      _ =
          ∑ c : PRegularConjClass G p,
            g c • QuotientAddGroup.mk' D
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) := by
            refine Finset.sum_congr rfl ?_
            intro c _
            rw [map_zsmul]
  have hmkN :
      QuotientAddGroup.mk' N (∑ c : PRegularConjClass G p, g c • x c) =
        ∑ c : PRegularConjClass G p, g c • QuotientAddGroup.mk' N (x c) := by
    calc
      QuotientAddGroup.mk' N (∑ c : PRegularConjClass G p, g c • x c) =
          ∑ c : PRegularConjClass G p, QuotientAddGroup.mk' N (g c • x c) := by
            rw [map_sum]
      _ = ∑ c : PRegularConjClass G p, g c • QuotientAddGroup.mk' N (x c) := by
            refine Finset.sum_congr rfl ?_
            intro c _
            rw [map_zsmul]
  have hψsum :
      ψ (QuotientAddGroup.mk' D g) =
        ∑ c : PRegularConjClass G p,
          g c • ψ (QuotientAddGroup.mk' D
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) := by
    rw [hmkD, map_sum]
    refine Finset.sum_congr rfl ?_
    intro c _
    rw [map_zsmul]
  have hφsum :
      φ (QuotientAddGroup.mk' N (∑ c : PRegularConjClass G p, g c • x c)) =
        ∑ c : PRegularConjClass G p, g c • φ (QuotientAddGroup.mk' N (x c)) := by
    rw [hmkN, map_sum]
    refine Finset.sum_congr rfl ?_
    intro c _
    rw [map_zsmul]
  calc
    ψ (QuotientAddGroup.mk' D g) =
        ∑ c : PRegularConjClass G p,
          g c • ψ (QuotientAddGroup.mk' D
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) := hψsum
    _ =
        ∑ c : PRegularConjClass G p,
          g c • φ (QuotientAddGroup.mk' N (x c)) := by
            refine Finset.sum_congr rfl ?_
            intro c _
            exact congrArg (fun y ↦ g c • y) (hx c)
    _ =
        φ (QuotientAddGroup.mk' N (∑ c : PRegularConjClass G p, g c • x c)) := hφsum.symm

/-- Source-product-to-cokernel bridge in the final coordinate-equivalence form used by
`CartanFormalRange`. -/
theorem existsCartanRangeCoordinateEquiv_of_canonicalVirtualModularCartanProductRange
    (himage :
      Nonempty
        ((cartanCokernelToCanonicalVirtualModularCartanProduct
            (p := p) (A := A) (K := K) (G := G)).range ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1))) :
    ∃ e : R₀[IsLocalRing.ResidueField A](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom (IsLocalRing.ResidueField A) G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_of_cokernelProduct
    (p := p) (k := IsLocalRing.ResidueField A) (G := G)
    (cartanCokernel_nonempty_addEquiv_pi_of_canonicalVirtualModularCartanProductRange
      (p := p) (A := A) (K := K) (G := G) himage)

/-- Final-coordinate form of the canonical source-product image criterion. -/
theorem existsCartanRangeCoordinateEquiv_of_canonicalVirtualModularCartanProductImage
    (himage :
      canonicalVirtualModularCartanProductImageMatchesIntegerImage
        (p := p) (A := A) (K := K) (G := G)) :
    ∃ e : R₀[IsLocalRing.ResidueField A](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom (IsLocalRing.ResidueField A) G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_of_cokernelProduct
    (p := p) (k := IsLocalRing.ResidueField A) (G := G)
    (cartanCokernel_nonempty_addEquiv_pi_of_canonicalVirtualModularCartanProductImage
      (p := p) (A := A) (K := K) (G := G) himage)

end ProjectiveCartanSourceCokernelBridge

end Representation
