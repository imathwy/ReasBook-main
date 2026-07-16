import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanCoordinates

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanCoordinateRangeGenerators

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanCoordinateRangeGeneratorsFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanCoordinateRangeGeneratorsDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Forward fixed-coordinate range criterion: to prove that the Cartan-coordinate range is
contained in Serre's diagonal integer lattice, it is enough to prove coordinatewise divisibility
by the centralizer `p`-part for every Cartan-coordinate vector. -/
theorem cartanCoordinateAddHom_range_le_regularIntegerDiagonalSubmodule_of_coordinate_divisible
    (hdiv :
      ∀ x : P₀[k](G), ∀ c : PRegularConjClass G p,
        ∃ a : ℤ,
          cartanCoordinateAddHom (p := p) (k := k) (G := G) x c =
            (ConjClasses.centralizerPPart p c.1 : ℤ) * a) :
    (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range ≤
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  rintro f ⟨x, rfl⟩
  change
    cartanCoordinateAddHom (p := p) (k := k) (G := G) x ∈
      regularIntegerDiagonalSubmodule (p := p) (G := G)
  exact (mem_regularIntegerDiagonalSubmodule_iff
    (p := p) (G := G)
    (cartanCoordinateAddHom (p := p) (k := k) (G := G) x)).2 (hdiv x)

/-- A Cartan class identity for one coordinate-normalized simple class realizes the corresponding
scaled regular-class indicator in the fixed Cartan-coordinate range. -/
theorem scaled_regular_integer_indicator_mem_cartanCoordinateAddHom_range_of_cartan_class
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c : PRegularConjClass G p)
    (x : P₀[k](G))
    (hx :
      cartanHom k G x =
        (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀) :
    scaled_regular_integer_indicator (p := p) (G := G) c ∈
      (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range := by
  refine ⟨x, ?_⟩
  exact
    cartanCoordinateAddHom_eq_scaled_regular_integer_indicator_of_cartan_class
      (p := p) (k := k) (G := G) (π := π) hπ_coord x c hx

/-- Generator membership in the fixed Cartan-coordinate range follows from one Cartan preimage of
the centralizer-`p`-part multiple of each coordinate-normalized simple class. -/
theorem scaled_regular_integer_indicator_mem_cartanCoordinateAddHom_range_of_cartan_generators
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hgen :
      ∀ c : PRegularConjClass G p,
        ∃ x : P₀[k](G),
          cartanHom k G x =
            (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀) :
    ∀ c : PRegularConjClass G p,
      scaled_regular_integer_indicator (p := p) (G := G) c ∈
        (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range := by
  intro c
  rcases hgen c with ⟨x, hx⟩
  exact
    scaled_regular_integer_indicator_mem_cartanCoordinateAddHom_range_of_cartan_class
      (p := p) (k := k) (G := G) (π := π) hπ_coord c x hx

/-- Conversely, a scaled regular-class indicator in the fixed Cartan-coordinate range gives the
corresponding fixed Cartan generator class. -/
theorem cartan_generator_of_scaled_regular_integer_indicator_mem_cartanCoordinateAddHom_range
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c : PRegularConjClass G p)
    (hmem :
      scaled_regular_integer_indicator (p := p) (G := G) c ∈
        (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range) :
    ∃ x : P₀[k](G),
      cartanHom k G x =
        (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀ := by
  rcases hmem with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  apply (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)).injective
  change
    cartanCoordinateAddHom (p := p) (k := k) (G := G) x =
      regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)
        ((ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀)
  rw [hx, map_zsmul, hπ_coord c]
  ext c'
  by_cases h : c' = c
  · subst h
    simp [scaled_regular_integer_indicator]
  · simp [scaled_regular_integer_indicator, h]

/-- The fixed Cartan generator statement is equivalent to membership of every scaled
regular-class indicator in the fixed Cartan-coordinate range. -/
theorem cartan_generators_iff_scaled_regular_integer_indicators_mem_cartanCoordinateAddHom_range
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    (∀ c : PRegularConjClass G p,
      ∃ x : P₀[k](G),
        cartanHom k G x =
          (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀) ↔
      ∀ c : PRegularConjClass G p,
        scaled_regular_integer_indicator (p := p) (G := G) c ∈
          (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range := by
  constructor
  · exact
      scaled_regular_integer_indicator_mem_cartanCoordinateAddHom_range_of_cartan_generators
        (p := p) (k := k) (G := G) (π := π) hπ_coord
  · intro hmem c
    exact
      cartan_generator_of_scaled_regular_integer_indicator_mem_cartanCoordinateAddHom_range
        (p := p) (k := k) (G := G) (π := π) hπ_coord c (hmem c)

/-- Fixed-coordinate generator criterion: if every scaled regular-class indicator is in the
Cartan-coordinate range, then the diagonal lattice is contained in that range. -/
theorem regularIntegerDiagonalSubmodule_le_cartanCoordinateAddHom_range_of_scaled_mem
    (hscaled :
      ∀ c : PRegularConjClass G p,
        scaled_regular_integer_indicator (p := p) (G := G) c ∈
          (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range) :
    (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup ≤
      (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range := by
  let R : AddSubgroup (PRegularConjClass G p → ℤ) :=
    (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range
  have hle :
      regularIntegerDiagonalSubmodule (p := p) (G := G) ≤ R.toIntSubmodule := by
    rw [regularIntegerDiagonalSubmodule_eq_span_scaled_regular_integer_indicator
      (p := p) (G := G)]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, rfl⟩
    exact hscaled c
  intro f hf
  change f ∈ R
  change f ∈ R.toIntSubmodule
  exact hle hf

/-- The two non-circular fixed-coordinate inputs requested by
`ProjectiveCartanSpanStability.lean` imply the desired range equality. -/
theorem cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_range_le_and_scaled_mem
    (hsubset :
      (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range ≤
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)
    (hscaled :
      ∀ c : PRegularConjClass G p,
        scaled_regular_integer_indicator (p := p) (G := G) c ∈
          (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range) :
    (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range =
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  exact le_antisymm hsubset
    (regularIntegerDiagonalSubmodule_le_cartanCoordinateAddHom_range_of_scaled_mem
      (p := p) (k := k) (G := G) hscaled)

/-- If coordinatewise divisibility gives the forward inclusion and Serre's generator membership
gives one Cartan preimage for each coordinate-normalized simple class, then the fixed
Cartan-coordinate range is exactly the diagonal integer lattice.

The second hypothesis is the smallest missing source-side generator lemma in this route. -/
theorem
    cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_coordinate_divisible_and_cartan_generators
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hdiv :
      ∀ x : P₀[k](G), ∀ c : PRegularConjClass G p,
        ∃ a : ℤ,
          cartanCoordinateAddHom (p := p) (k := k) (G := G) x c =
            (ConjClasses.centralizerPPart p c.1 : ℤ) * a)
    (hgen :
      ∀ c : PRegularConjClass G p,
        ∃ x : P₀[k](G),
          cartanHom k G x =
            (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀) :
    (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range =
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_range_le_and_scaled_mem
      (p := p) (k := k) (G := G) ?_ ?_
  · exact
      cartanCoordinateAddHom_range_le_regularIntegerDiagonalSubmodule_of_coordinate_divisible
        (p := p) (k := k) (G := G) hdiv
  · intro c
    exact
      scaled_regular_integer_indicator_mem_cartanCoordinateAddHom_range_of_cartan_generators
        (p := p) (k := k) (G := G) (π := π) hπ_coord hgen c

end CartanCoordinateRangeGenerators

end Representation
