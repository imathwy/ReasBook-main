import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanCoordinateRangeGenerators

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanScaledIndicatorSourceWorker

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanScaledIndicatorSourceWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanScaledIndicatorSourceWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Source-side reverse-inclusion constructor for one regular class.

Once Serre's source argument supplies the Cartan class identity for a coordinate-normalized
projective-envelope family, the required preimage of the scaled regular-class indicator is the
projective-envelope class itself. The remaining missing source lemma is exactly the `hcartan`
hypothesis. -/
theorem exists_cartanCoordinateAddHom_eq_scaled_regular_integer_indicator_of_projectiveEnvelope_cartan_class
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hcartan :
      ∀ c : PRegularConjClass G p,
        cartanHom k G [P c]ₚ₀ =
          (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀)
    (c : PRegularConjClass G p) :
    ∃ x : P₀[k](G),
      cartanCoordinateAddHom (p := p) (k := k) (G := G) x =
        scaled_regular_integer_indicator (p := p) (G := G) c := by
  refine ⟨[P c]ₚ₀, ?_⟩
  exact
    cartanCoordinateAddHom_eq_scaled_regular_integer_indicator_of_cartan_class
      (p := p) (k := k) (G := G) (π := π) hπ_coord [P c]ₚ₀ c (hcartan c)

/-- Range form of the same source-side constructor. -/
theorem scaled_regular_integer_indicator_mem_cartanCoordinateAddHom_range_of_projectiveEnvelope_cartan_class
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hcartan :
      ∀ c : PRegularConjClass G p,
        cartanHom k G [P c]ₚ₀ =
          (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀)
    (c : PRegularConjClass G p) :
    scaled_regular_integer_indicator (p := p) (G := G) c ∈
      (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range := by
  rcases
      exists_cartanCoordinateAddHom_eq_scaled_regular_integer_indicator_of_projectiveEnvelope_cartan_class
        (p := p) (k := k) (G := G) (π := π) hπ_coord P hcartan c with
    ⟨x, hx⟩
  exact ⟨x, hx⟩

/-- Family form of the reverse-inclusion constructor. This is the exact fixed-coordinate
generator input needed by `CartanCoordinateRangeGenerators.lean`. -/
theorem scaled_regular_integer_indicators_mem_cartanCoordinateAddHom_range_of_projectiveEnvelope_cartan_class
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hcartan :
      ∀ c : PRegularConjClass G p,
        cartanHom k G [P c]ₚ₀ =
          (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀) :
    ∀ c : PRegularConjClass G p,
      scaled_regular_integer_indicator (p := p) (G := G) c ∈
        (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range := by
  intro c
  exact
    scaled_regular_integer_indicator_mem_cartanCoordinateAddHom_range_of_projectiveEnvelope_cartan_class
      (p := p) (k := k) (G := G) (π := π) hπ_coord P hcartan c

end CartanScaledIndicatorSourceWorker

end Representation
