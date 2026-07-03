import Mathlib
import LinearRepresentations_Serre_1977.Chap11.Proposition_11_11_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe v

noncomputable section

open Proposition_11_11_4_1
open Representation
open scoped Representation

section

variable {G : Type} [Group G]
variable {A : Type v} [CommRing A]
variable [Finite G] [Algebra A ℂ]

noncomputable local instance : Fintype G := Fintype.ofFinite G

local notation "P0" => tensorCharacterRingZeroPrimeIdeal
local notation "Pm" => tensorCharacterRingRegularPrime

/-- Helper for Proposition 11-11.4-2: distinct zero-residual class primes should be separated by
an element of the tensor character ring lying in exactly one of the two kernels. -/
private lemma zero_prime_separator_of_ne
    (c₁ c₂ : ConjClasses G) (hc : c₁ ≠ c₂) :
    ∃ χ : A ⊗R(G), χ ∈ (P0 A c₂).asIdeal ∧ χ ∉ (P0 A c₁).asIdeal := by
  -- TODO: the source-faithful proof should separate the two kernels through LinearRepresentations_Serre_1977's source
  -- value profile and the point-mass functions `conjClassDelta`. The currently exported rewrite
  -- `zero_line_point_eq_comap_tensorCharacterRingValueAtConjClass` only applies in the arithmetic
  -- `[IsDomain] [Ring.HasFiniteQuotients] [IsIntegralClosure]` setting, so the remaining gap is a
  -- coefficient-descent-free separation lemma at the present generality of part (i).
  sorry

/-- Proposition 11-11.4-2 (1): when the maximal ideal is `0`, the equality `P₀,c₁ = P₀,c₂` holds
exactly for equal conjugacy classes `c₁ = c₂`. -/
theorem zero_residual_prime_eq_iff
    (c₁ c₂ : ConjClasses G) :
    P0 A c₁ = P0 A c₂ ↔
        c₁ = c₂ := by
  constructor
  · intro hP
    -- Route correction: the forward implication is reduced to a separator witness between the two
    -- zero kernels, so only the source-profile separation lemma remains open.
    by_contra hc
    obtain ⟨χ, hχ₂, hχ₁⟩ := zero_prime_separator_of_ne (A := A) c₁ c₂ hc
    have hχ₁' : χ ∈ (P0 A c₁).asIdeal := by
      simpa [hP] using hχ₂
    exact hχ₁ hχ₁'
  · intro hc
    -- The reverse implication is just substitution of the conjugacy-class parameter.
    subst hc
    rfl

section RegularPrime

variable [IsDomain A] [Ring.HasFiniteQuotients A] [IsIntegralClosure A ℤ ℂ]

/-- Helper for Proposition 11-11.4-2: equality of the regular-branch value-comap primes over a
fixed residual maximal ideal should already determine the underlying `p`-regular conjugacy class.
-/
private theorem regular_value_comap_eq_iff
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c₁ c₂ : PRegularConjClass G p) :
    PrimeSpectrum.comap
        (tensorCharacterRingValueAtConjClass (A := A) (G := G) (c₁ : ConjClasses G)).toRingHom
        (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) =
      PrimeSpectrum.comap
        (tensorCharacterRingValueAtConjClass (A := A) (G := G) (c₂ : ConjClasses G)).toRingHom
        (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) ↔
      c₁ = c₂ := by
  constructor
  · intro hcomap
    -- TODO: the intended proof uses the residue-field delta witness
    -- `exists_tensorCharacter_preimage_of_pregular_delta`, together with the Chapter 11 owner
    -- transport already packaged around `value_comap_eq_tensorCharacterRingRegularPrime`. The
    -- missing bridge is a dependency-closed identification of these comap primes with the
    -- coordinate-evaluation primes on the regular fiber.
    sorry
  · intro hc
    -- Equal class parameters give definitionally equal fixed-class pullback primes.
    subst hc
    rfl

/-- Proposition 11-11.4-2 (2): for a fixed nonzero maximal ideal `M` of residual characteristic
`p`, the equality `P_{M,c₁} = P_{M,c₂}` holds exactly for equal `p`-regular conjugacy classes
`c₁ = c₂` in the arithmetic coefficient-ring setting where `Pm` is defined. -/
theorem regular_prime_eq_iff
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c₁ c₂ : PRegularConjClass G p) :
    Pm p M c₁ = Pm p M c₂ ↔
        c₁ = c₂ := by
  constructor
  · intro hP
    -- Route correction: rewrite LinearRepresentations_Serre_1977's regular owners as fixed-class pullbacks over `M`, then
    -- delegate uniqueness to the remaining comap-level blocker.
    have hcomap :
        PrimeSpectrum.comap
            (tensorCharacterRingValueAtConjClass (A := A) (G := G) (c₁ : ConjClasses G)).toRingHom
            (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) =
          PrimeSpectrum.comap
            (tensorCharacterRingValueAtConjClass (A := A) (G := G) (c₂ : ConjClasses G)).toRingHom
            (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) := by
      calc
        PrimeSpectrum.comap
            (tensorCharacterRingValueAtConjClass (A := A) (G := G) (c₁ : ConjClasses G)).toRingHom
            (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) =
          Pm p M c₁ := by
            simpa using
              (value_comap_eq_tensorCharacterRingRegularPrime
                (A := A) (G := G) p M (c₁ : ConjClasses G))
      _ = Pm p M c₂ := hP
      _ =
          PrimeSpectrum.comap
            (tensorCharacterRingValueAtConjClass (A := A) (G := G) (c₂ : ConjClasses G)).toRingHom
            (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) := by
            simpa using
              (value_comap_eq_tensorCharacterRingRegularPrime
                (A := A) (G := G) p M (c₂ : ConjClasses G)).symm
    exact (regular_value_comap_eq_iff (A := A) (G := G) p M c₁ c₂).mp hcomap
  · intro hc
    -- The reverse implication is substitution of the regular owner parameter.
    subst hc
    rfl

end RegularPrime

end
