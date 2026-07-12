import Mathlib
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveTriangle
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerCoordinateReadback

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanASpan

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local instance instFintypePRegularConjClassProjectiveCartanASpan :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance instDecidableEqPRegularConjClassProjectiveCartanASpan :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The canonical field-valued lift obtained from the complete-DVR root lift. -/
noncomputable def projectiveCartanASpanFieldLift :
    PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ :=
  (Units.map (algebraMap A K).toMonoidHom).comp
    (primeToPRoot_unitsLift (p := p) (A := A))

/-- The canonical field-valued lift is injective after passing to the fraction field. -/
theorem projectiveCartanASpanFieldLift_injective :
    Function.Injective
      (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)) := by
  intro y z hyz
  apply primeToPRoot_unitsLift_injective (p := p) (A := A)
  apply IsFractionRing.injective A K
  exact congrArg (fun u : Kˣ ↦ (u : K)) hyz

/-- The Exercise `18.4` Brauer basis attached to a coordinate-normalized simple family, using
the canonical field-valued lift from the mixed-characteristic system. -/
noncomputable def projectiveCartanASpanBrauerBasis
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    Module.Basis (PRegularConjClass G p) K (PRegularConjClass G p → K) :=
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_simple hπ_coord
  exercise_18_18_2_9_field_irreducible_modular_characters_basis
    (p := p) (k := IsLocalRing.ResidueField A) (K := K)
    (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))
    (projectiveCartanASpanFieldLift_injective (p := p) (A := A) (K := K))
    π hπ_pairwise hπ_complete

/-- Brauer-basis coordinates, viewed as an `A`-linear map from regular class functions to
coordinate functions. -/
noncomputable def projectiveCartanASpanBrauerRepr
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    (PRegularConjClass G p → K) →ₗ[A] (PRegularConjClass G p → K) :=
  (((projectiveCartanASpanBrauerBasis
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).repr ≪≫ₗ
      Finsupp.linearEquivFunOnFinite K K (PRegularConjClass G p)).toLinearMap).restrictScalars A

/-- The Cartan image written in the fixed regular-class coordinates and cast to `K`. -/
noncomputable def projectiveCartanCoordinateCast :
    P₀[IsLocalRing.ResidueField A](G) →+ (PRegularConjClass G p → K) where
  toFun x d := (cartanCoordinateAddHom (p := p) (k := IsLocalRing.ResidueField A) (G := G) x d : K)
  map_zero' := by
    ext d
    simp [cartanCoordinateAddHom]
  map_add' x y := by
    ext d
    simp [cartanCoordinateAddHom]

/-- Row-level bridge: Brauer coordinates of a descended virtual modular character on the Cartan
range are exactly the fixed Cartan coordinates, cast to `K`. -/
theorem projectiveCartanASpanBrauerRepr_virtualModularCharacter_cartanHom
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (x : P₀[IsLocalRing.ResidueField A](G)) :
    projectiveCartanASpanBrauerRepr (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord
        (virtualModularCharacterOnPRegularConjClass
          (p := p) (k := IsLocalRing.ResidueField A) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          (cartanHom (IsLocalRing.ResidueField A) G x)) =
      projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G) x := by
  ext d
  simpa [projectiveCartanASpanBrauerRepr, projectiveCartanASpanBrauerBasis,
    projectiveCartanCoordinateCast, projectiveCartanASpanFieldLift] using
    (virtualModularCharacter_basis_repr_eq_cast_regularClassCoordinate
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) (K' := K)
      (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))
      (projectiveCartanASpanFieldLift_injective (p := p) (A := A) (K := K))
      π hπ_simple hπ_coord (cartanHom (IsLocalRing.ResidueField A) G x) d)

variable [CharZero K]

/-- Row-level bridge for projective characters: after regular restriction, Brauer-basis
coordinates recover the fixed Cartan coordinates of `cartanHom`. -/
theorem projectiveCartanASpanBrauerRepr_regularRestriction_projectiveCharacter
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (x : P₀[IsLocalRing.ResidueField A](G)) :
    projectiveCartanASpanBrauerRepr (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord
        (regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x)) =
      projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G) x := by
  ext d
  simpa [projectiveCartanASpanBrauerRepr, projectiveCartanASpanBrauerBasis,
    projectiveCartanCoordinateCast, projectiveCartanASpanFieldLift] using
    (regularRestriction_projectiveCharacterScalarExtension_basis_repr_eq_cast_cartanCoordinate
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord x d)

set_option linter.style.longLine false in
/-- Main bridge: after regular restriction of the projective-character lattice and passage to
Brauer-basis coordinates, the resulting `A`-span is precisely the `A`-span of the Cartan range in
the fixed regular-class coordinates. -/
theorem projectiveCharacterSubmodule_regularRestriction_brauerRepr_eq_cartanCoordinate_span
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    Submodule.map
        (projectiveCartanASpanBrauerRepr (p := p) (A := A) (K := K) (G := G)
          π hπ_simple hπ_coord)
        (Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G))) =
      Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) := by
  rw [
    projectiveCharacterSubmodule_map_regularRestriction_eq_span_projectiveCharacterRegularRestrictionHom_range
      (p := p) (A := A) (K := K) (G := G)]
  rw [Submodule.map_span]
  apply congrArg (Submodule.span A)
  ext f
  constructor
  · rintro ⟨row, ⟨x, rfl⟩, rfl⟩
    refine ⟨x, ?_⟩
    simpa [projectiveCharacterRegularRestrictionHom] using
      (projectiveCartanASpanBrauerRepr_regularRestriction_projectiveCharacter
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord x).symm
  · rintro ⟨x, rfl⟩
    refine
      ⟨projectiveCharacterRegularRestrictionHom (p := p) (A := A) (K := K) (G := G) x,
        ⟨x, rfl⟩, ?_⟩
    simpa [projectiveCharacterRegularRestrictionHom] using
      (projectiveCartanASpanBrauerRepr_regularRestriction_projectiveCharacter
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord x)

end ProjectiveCartanASpan

end Representation
