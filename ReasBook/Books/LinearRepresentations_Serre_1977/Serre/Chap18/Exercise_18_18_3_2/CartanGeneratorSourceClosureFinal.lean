import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanCoordinateRangeGenerators
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.IntegerDivisibilityDescent

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanGeneratorSourceClosureFinal

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanGeneratorSourceClosureFinalFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanGeneratorSourceClosureFinalDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Source-side closure for the Cartan generator input.

If the projective envelopes of a coordinate-normalized simple family satisfy Serre's Cartan
class identity, then the fixed-coordinate generator input required by
`CartanCoordinateRangeGenerators.lean` follows immediately by taking the projective-envelope
class itself.  This is the source-facing lemma that remains to be proved without using any
range endpoint. -/
theorem cartan_generators_of_projectiveEnvelope_cartan_class
    (π : PRegularConjClass G p → FDRep k G)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hcartan :
      ∀ c : PRegularConjClass G p,
        cartanHom k G [P c]ₚ₀ =
          (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀) :
    ∀ c : PRegularConjClass G p,
      ∃ x : P₀[k](G),
        cartanHom k G x =
          (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀ := by
  intro c
  exact ⟨[P c]ₚ₀, hcartan c⟩

/-- Source-side closure for the fixed Cartan-coordinate range equality.

The only non-formal source inputs are the coordinatewise Cartan divisibility statement and the
Cartan class identity for the projective envelopes.  The proof then uses the existing
source-side generator criterion, not a downstream endpoint. -/
theorem cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_coordinate_divisible_and_projectiveEnvelope_cartan_class
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hdiv :
      ∀ x : P₀[k](G), ∀ c : PRegularConjClass G p,
        ∃ a : ℤ,
          cartanCoordinateAddHom (p := p) (k := k) (G := G) x c =
            (ConjClasses.centralizerPPart p c.1 : ℤ) * a)
    (hcartan :
      ∀ c : PRegularConjClass G p,
        cartanHom k G [P c]ₚ₀ =
          (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀) :
    (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range =
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  exact
    cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_coordinate_divisible_and_cartan_generators
      (p := p) (k := k) (G := G) (π := π) hπ_coord hdiv
      (cartan_generators_of_projectiveEnvelope_cartan_class
        (p := p) (k := k) (G := G) π P hcartan)

end CartanGeneratorSourceClosureFinal

section CartanCoordinateResidualDivisibility

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance cartanCoordinateResidualDivisibilityFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

/-- Exact source-side form of the remaining residual obstruction for coordinatewise
divisibility.

The projective-character row is already in Serre's regular-value divisibility lattice by
`ProjectiveCharacterDivisibility.lean`.  Therefore fixed Cartan-coordinate divisibility is
equivalent to saying that the difference between that row and the cast integer Cartan-coordinate
row also lies in the same lattice. -/
theorem cartanCoordinateAddHom_coordinate_divisible_iff_projective_regularRestriction_residual
    :
    (∀ x : P₀[IsLocalRing.ResidueField A](G), ∀ c : PRegularConjClass G p,
      ∃ a : ℤ,
        cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) x c =
          (ConjClasses.centralizerPPart p c.1 : ℤ) * a) ↔
      ∀ x : P₀[IsLocalRing.ResidueField A](G),
        regularRestriction (p := p) (A := A) (K := K) (G := G)
            (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x) -
          regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · intro hdiv x
    let D : Submodule A (PRegularConjClass G p → K) :=
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
    let row : PRegularConjClass G p → K :=
      regularRestriction (p := p) (A := A) (K := K) (G := G)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x)
    let coord : PRegularConjClass G p → K :=
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) x)
    have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
      intro s _hs
      haveI : HasEnoughRootsOfUnity K (orderOf s) :=
        HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
      exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
    have hrowD : row ∈ D :=
      regularRestriction_projectiveCharacter_mem_regularValueDivisibilitySubmodule
        (p := p) (A := A) (K := K) (G := G) hω x
    have hcoordDiag :
        cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) x ∈
          regularIntegerDiagonalSubmodule (p := p) (G := G) :=
      (mem_regularIntegerDiagonalSubmodule_iff
        (p := p) (G := G)
        (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) x)).2 (hdiv x)
    have hcoordD : coord ∈ D := by
      simpa [coord, D] using
        (regularIntegerFunctionCast_mem_regularValueDivisibilitySubmodule_iff
          (p := p) (A := A) (K := K) (G := G)).2 hcoordDiag
    simpa [row, coord, D] using D.sub_mem hrowD hcoordD
  · intro hres x c
    let D : Submodule A (PRegularConjClass G p → K) :=
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
    let row : PRegularConjClass G p → K :=
      regularRestriction (p := p) (A := A) (K := K) (G := G)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x)
    let coord : PRegularConjClass G p → K :=
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) x)
    have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
      intro s _hs
      haveI : HasEnoughRootsOfUnity K (orderOf s) :=
        HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
      exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
    have hrowD : row ∈ D :=
      regularRestriction_projectiveCharacter_mem_regularValueDivisibilitySubmodule
        (p := p) (A := A) (K := K) (G := G) hω x
    have hresD : row - coord ∈ D := by
      simpa [row, coord, D] using hres x
    have hcoordD : coord ∈ D := by
      have hdiff : row - (row - coord) ∈ D := D.sub_mem hrowD hresD
      have hcoord_eq : row - (row - coord) = coord := by
        ext d
        simp only [Pi.sub_apply]
        ring
      simpa [hcoord_eq]
        using hdiff
    have hcoordDiag :
        cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) x ∈
          regularIntegerDiagonalSubmodule (p := p) (G := G) := by
      simpa [coord, D] using
        (regularIntegerFunctionCast_mem_regularValueDivisibilitySubmodule_iff
          (p := p) (A := A) (K := K) (G := G)).1 hcoordD
    exact
      (mem_regularIntegerDiagonalSubmodule_iff
        (p := p) (G := G)
        (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) x)).1 hcoordDiag c

end CartanCoordinateResidualDivisibility

end Representation
