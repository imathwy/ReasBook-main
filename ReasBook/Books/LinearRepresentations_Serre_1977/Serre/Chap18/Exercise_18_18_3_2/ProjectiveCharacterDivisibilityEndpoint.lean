import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanSpanStability
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanSourceCokernelBridge

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCharacterDivisibilityEndpoint

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCharacterDivisibilityEndpointFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCharacterDivisibilityEndpointDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Serre 18.5(a), in the exact regular-restriction form needed by the Cartan adapters. -/
theorem projectiveCharacter_regularRestriction_eq_regularValueDivisibilitySubmodule :
    Submodule.map
        (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
        (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) =
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
    intro s _hs
    haveI : HasEnoughRootsOfUnity K (orderOf s) :=
      HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
  exact
    projectiveCharacterSubmodule_map_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G) hω

/-- The source-faithful Cartan span obtained by applying virtual modular characters to the
Cartan range is exactly Serre's divisibility lattice. -/
theorem canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule_endpoint :
    canonicalVirtualModularCartanRangeASpan (p := p) (A := A) (K := K) (G := G) =
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
  canonicalVirtualModularCartanRangeASpan_eq_regularValueDivisibilitySubmodule
    (p := p) (A := A) (K := K) (G := G)

/-- Fixed-coordinate Cartan span equality is exactly Brauer-coordinate stability of Serre's
regular divisibility lattice. -/
theorem cartanCoordinate_span_eq_regularValueDivisibilitySubmodule_iff_brauerRepr_stable
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) ↔
      Submodule.map
          (projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  exact
    (projectiveCartanASpanBrauerRepr_regularValueDivisibility_stable_iff_cartanCoordinate_span_eq
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).symm

/-- Brauer-coordinate readback rewritten as an equality in regular class functions. -/
theorem virtualModularCharacterOnPRegularConjClass_eq_brauerRepr_symm_regularIntegerCoordinate
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (x : R₀[IsLocalRing.ResidueField A](G)) :
    virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x =
      (projectiveCartanASpanBrauerReprLinearEquiv
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).symm
        (regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) x)) := by
  let E := PRegularConjClass G p → K
  let T : E ≃ₗ[A] E :=
    projectiveCartanASpanBrauerReprLinearEquiv
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  let χ : E :=
    virtualModularCharacterOnPRegularConjClass
      (p := p) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x
  let z : E :=
    regularIntegerFunctionCast (p := p) (K := K) (G := G)
      (regularClassCoordinateAddEquiv
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) x)
  have hTχ : T χ = z := by
    simpa [T, χ, z,
      projectiveCartanASpanBrauerReprLinearEquiv_toLinearMap
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord] using
      projectiveCartanASpanBrauerRepr_virtualModularCharacter
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord x
  calc
    virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x = χ := rfl
    _ = T.symm (T χ) := by simp
    _ = T.symm z := by rw [hTχ]
    _ =
      (projectiveCartanASpanBrauerReprLinearEquiv
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).symm
        (regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) x)) := rfl

/-- The direct regular-character congruence is equivalent to inverse-Brauer stability modulo
Serre's divisibility lattice on all integer regular-class coordinate functions. -/
theorem virtualModularCharacter_integerCoordinate_congruence_iff_brauerInverse_congruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    (∀ x : R₀[IsLocalRing.ResidueField A](G),
        virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift
              (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ↔
      (∀ f : PRegularConjClass G p → ℤ,
        (projectiveCartanASpanBrauerReprLinearEquiv
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).symm
            (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
            regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) := by
  constructor
  · intro h f
    let x :=
      (regularClassCoordinateAddEquiv
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)).symm f
    have hx := h x
    simpa [x,
      virtualModularCharacterOnPRegularConjClass_eq_brauerRepr_symm_regularIntegerCoordinate
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord x] using hx
  · intro h x
    simpa [
      virtualModularCharacterOnPRegularConjClass_eq_brauerRepr_symm_regularIntegerCoordinate
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord x] using
      h (regularClassCoordinateAddEquiv
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) x)

  /-- The source-faithful regular-value congruence gives the inverse half of Brauer-coordinate
  stability on Serre's divisibility lattice.

  This uses the whole integer diagonal lattice, not fixed projective-envelope columns: the
  divisibility lattice is the `A`-span of the cast integer diagonal lattice, and the congruence
  controls `T⁻¹` on every integer regular-class coordinate function. -/
  theorem projectiveCartanASpanBrauerRepr_symm_regularValueDivisibility_le_of_regularValue_congruence
      (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
      (hπ_simple : ∀ c, Simple (π c))
      (hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
      (hregular :
        ∀ x : R₀[IsLocalRing.ResidueField A](G),
          virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (regularClassCoordinateAddEquiv
                (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
      Submodule.map
          ((projectiveCartanASpanBrauerReprLinearEquiv
            (p := p) (A := A) (K := K) (G := G)
            π hπ_simple hπ_coord).symm :
              (PRegularConjClass G p → K) →ₗ[A] (PRegularConjClass G p → K))
          (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ≤
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    let E := PRegularConjClass G p → K
    let D : Submodule A E :=
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
    let T : E ≃ₗ[A] E :=
      projectiveCartanASpanBrauerReprLinearEquiv
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
    have hinteger :
        ∀ f : PRegularConjClass G p → ℤ,
          T.symm (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈ D := by
      simpa [D, T, E] using
        (virtualModularCharacter_integerCoordinate_congruence_iff_brauerInverse_congruence
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).1 hregular
    rintro _ ⟨f, hf, rfl⟩
    change T.symm f ∈ D
    rw [regularValueDivisibilitySubmodule_eq_span_regularIntegerDiagonal_cast
      (p := p) (A := A) (K := K) (G := G)] at hf
    induction hf using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨g, hg, rfl⟩
        have hdiff :
            T.symm (regularIntegerFunctionCast (p := p) (K := K) (G := G) g) -
              regularIntegerFunctionCast (p := p) (K := K) (G := G) g ∈ D :=
          hinteger g
        have hcast :
            regularIntegerFunctionCast (p := p) (K := K) (G := G) g ∈ D :=
          regularIntegerFunctionCast_mem_regularValueDivisibilitySubmodule_of_mem
            (p := p) (A := A) (K := K) (G := G) hg
        have hsum :
            T.symm (regularIntegerFunctionCast (p := p) (K := K) (G := G) g) =
              (T.symm (regularIntegerFunctionCast (p := p) (K := K) (G := G) g) -
                regularIntegerFunctionCast (p := p) (K := K) (G := G) g) +
              regularIntegerFunctionCast (p := p) (K := K) (G := G) g := by
          abel
        rw [hsum]
        exact D.add_mem hdiff hcast
    | zero =>
        simp [D, T]
    | add y z _ _ hy hz =>
        simpa [map_add] using D.add_mem hy hz
    | smul a y _ hy =>
        simpa [map_smul] using D.smul_mem a hy

  omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
  /-- To prove full Brauer-coordinate stability it remains, after the source-faithful
  regular-value congruence, to prove only the forward inclusion `T(D) ≤ D`. -/
  theorem projectiveCartanASpanBrauerRepr_regularValueDivisibility_forward_le_of_regularIntegerDiagonal_congruence
      (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
      (hπ_simple : ∀ c, Simple (π c))
      (hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
      (hdiag :
        ∀ f : PRegularConjClass G p → ℤ,
          f ∈ regularIntegerDiagonalSubmodule (p := p) (G := G) →
            projectiveCartanASpanBrauerRepr
                (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
                (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) -
              regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
                regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
      Submodule.map
          (projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ≤
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    let E := PRegularConjClass G p → K
    let D : Submodule A E :=
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
    let T : E →ₗ[A] E :=
      projectiveCartanASpanBrauerRepr
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
    rintro _ ⟨f, hf, rfl⟩
    change T f ∈ D
    rw [regularValueDivisibilitySubmodule_eq_span_regularIntegerDiagonal_cast
      (p := p) (A := A) (K := K) (G := G)] at hf
    induction hf using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨g, hg, rfl⟩
        have hdiff :
            T (regularIntegerFunctionCast (p := p) (K := K) (G := G) g) -
              regularIntegerFunctionCast (p := p) (K := K) (G := G) g ∈ D := by
          simpa [D, T] using hdiag g hg
        have hcast :
            regularIntegerFunctionCast (p := p) (K := K) (G := G) g ∈ D :=
          regularIntegerFunctionCast_mem_regularValueDivisibilitySubmodule_of_mem
            (p := p) (A := A) (K := K) (G := G) hg
        have hsum :
            T (regularIntegerFunctionCast (p := p) (K := K) (G := G) g) =
              (T (regularIntegerFunctionCast (p := p) (K := K) (G := G) g) -
                regularIntegerFunctionCast (p := p) (K := K) (G := G) g) +
              regularIntegerFunctionCast (p := p) (K := K) (G := G) g := by
          abel
        rw [hsum]
        exact D.add_mem hdiff hcast
    | zero =>
        simp [D, T]
    | add y z _ _ hy hz =>
        simpa [map_add] using D.add_mem hy hz
    | smul a y _ hy =>
        simpa [map_smul] using D.smul_mem a hy

  /-- Whole-diagonal-lattice forward congruence is enough for the remaining forward inclusion.

  This avoids fixed point-mass or fixed Cartan-column hypotheses: the input is a single statement
  on every element of Serre's integer diagonal lattice. -/
  theorem projectiveCartanASpanBrauerRepr_regularValueDivisibility_stable_of_regularValue_congruence_and_forward_le
      (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
      (hπ_simple : ∀ c, Simple (π c))
      (hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
      (hregular :
        ∀ x : R₀[IsLocalRing.ResidueField A](G),
          virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (regularClassCoordinateAddEquiv
                (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
      (hforward :
        Submodule.map
            (projectiveCartanASpanBrauerRepr
              (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
            (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ≤
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
      Submodule.map
            (projectiveCartanASpanBrauerRepr
              (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
            (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    let E := PRegularConjClass G p → K
    let D : Submodule A E :=
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
    let T : E ≃ₗ[A] E :=
      projectiveCartanASpanBrauerReprLinearEquiv
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
    have hsymm :
        Submodule.map (T.symm : E →ₗ[A] E) D ≤ D := by
      simpa [D, T, E] using
        projectiveCartanASpanBrauerRepr_symm_regularValueDivisibility_le_of_regularValue_congruence
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hregular
    apply le_antisymm
    · simpa [D, T, E, projectiveCartanASpanBrauerReprLinearEquiv_toLinearMap
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord] using hforward
    · intro f hf
      have hpre : T.symm f ∈ D := hsymm ⟨f, by simpa [D] using hf, rfl⟩
      refine ⟨T.symm f, hpre, ?_⟩
      rw [← projectiveCartanASpanBrauerReprLinearEquiv_toLinearMap
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord]
      exact T.apply_symm_apply f

  theorem projectiveCartanASpanBrauerRepr_regularValueDivisibility_stable_of_regularValue_congruence_and_forward_regularIntegerDiagonal_congruence
      (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
      (hπ_simple : ∀ c, Simple (π c))
      (hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
      (hregular :
        ∀ x : R₀[IsLocalRing.ResidueField A](G),
          virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (regularClassCoordinateAddEquiv
                (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
      (hdiag :
        ∀ f : PRegularConjClass G p → ℤ,
          f ∈ regularIntegerDiagonalSubmodule (p := p) (G := G) →
            projectiveCartanASpanBrauerRepr
                (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
                (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) -
              regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
                regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
      Submodule.map
            (projectiveCartanASpanBrauerRepr
              (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
            (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
    projectiveCartanASpanBrauerRepr_regularValueDivisibility_stable_of_regularValue_congruence_and_forward_le
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hregular
      (projectiveCartanASpanBrauerRepr_regularValueDivisibility_forward_le_of_regularIntegerDiagonal_congruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hdiag)

  /-- Span endpoint using the weakened forward-inclusion form of Brauer-coordinate stability. -/
  theorem projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_of_regularValue_congruence_and_brauerRepr_forward_le
      (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
      (hπ_simple : ∀ c, Simple (π c))
      (hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
      (hregular :
        ∀ x : R₀[IsLocalRing.ResidueField A](G),
          virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (regularClassCoordinateAddEquiv
                (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
      (hforward :
        Submodule.map
            (projectiveCartanASpanBrauerRepr
              (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
            (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ≤
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
    projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_of_brauerRepr_stable
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (projectiveCartanASpanBrauerRepr_regularValueDivisibility_stable_of_regularValue_congruence_and_forward_le
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hregular hforward)

  theorem projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_of_regularValue_congruence_and_brauerRepr_forward_regularIntegerDiagonal_congruence
      (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
      (hπ_simple : ∀ c, Simple (π c))
      (hπ_coord :
        ∀ c,
          regularClassCoordinateAddEquiv
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
      (hregular :
        ∀ x : R₀[IsLocalRing.ResidueField A](G),
          virtualModularCharacterOnPRegularConjClass
              (p := p) (A := K) (G := G)
              (PrimeToPRoot.toFieldLift
                (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))) x -
            regularIntegerFunctionCast (p := p) (K := K) (G := G)
              (regularClassCoordinateAddEquiv
                (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
              regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
      (hdiag :
        ∀ f : PRegularConjClass G p → ℤ,
          f ∈ regularIntegerDiagonalSubmodule (p := p) (G := G) →
            projectiveCartanASpanBrauerRepr
                (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
                (regularIntegerFunctionCast (p := p) (K := K) (G := G) f) -
              regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
                regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
    projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_of_brauerRepr_stable
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (projectiveCartanASpanBrauerRepr_regularValueDivisibility_stable_of_regularValue_congruence_and_forward_regularIntegerDiagonal_congruence
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hregular hdiag)

end ProjectiveCharacterDivisibilityEndpoint

end Representation
