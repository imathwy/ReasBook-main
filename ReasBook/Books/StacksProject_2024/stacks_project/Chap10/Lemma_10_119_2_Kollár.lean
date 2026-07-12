import Mathlib
import StacksProject_2024.Chap10.Definition_10_72_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- A finite `R`-algebra appearing in Kollár's fourth alternative: the canonical map `R → S` is
not an isomorphism, its kernel and cokernel are annihilated by a power of the maximal ideal of
`R`, the maximal ideal is not an associated prime of `S`, and `S` is nonzero. -/
def HasKollarExceptionalFiniteExtension : Prop :=
  ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Module.Finite R S) (_ : Nontrivial S),
    ¬ Function.Bijective (algebraMap R S) ∧
      (∃ n : ℕ,
        (maximalIdeal R) ^ n • (RingHom.ker (algebraMap R S) : Submodule R R) = ⊥ ∧
        (maximalIdeal R) ^ n • (⊤ : Submodule R S) ≤ (Algebra.linearMap R S).range) ∧
      maximalIdeal R ∉ associatedPrimes R S

-- Proof sketch: this is just the defining existential package for the fourth alternative; later
-- arguments can unfold it to access the finite `R`-algebra, the `𝔪`-power torsion conditions on
-- the kernel and cokernel, the non-associated-prime hypothesis, and the nontriviality of the
-- target ring.
/-- Unfolding `HasKollarExceptionalFiniteExtension R` into its finite `R`-algebra data and the
torsion conditions on the kernel and cokernel of the canonical map. -/
theorem hasKollarExceptionalFiniteExtension_iff :
    HasKollarExceptionalFiniteExtension R ↔
      ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Module.Finite R S)
        (_ : Nontrivial S),
        ¬ Function.Bijective (algebraMap R S) ∧
          (∃ n : ℕ,
            (maximalIdeal R) ^ n • (RingHom.ker (algebraMap R S) : Submodule R R) = ⊥ ∧
            (maximalIdeal R) ^ n • (⊤ : Submodule R S) ≤ (Algebra.linearMap R S).range) ∧
          maximalIdeal R ∉ associatedPrimes R S := sorry

namespace RingHom

variable {R}
variable {S : Type u} [CommRing S]

/-- A specific finite ring map `f : R →+* S` realizes Kollár's exceptional finite-extension
alternative when the canonical `R`-algebra structure induced by `f` makes `S` a nontrivial finite
`R`-algebra, the map is not bijective, its kernel and cokernel are annihilated by a power of the
maximal ideal, and that maximal ideal is not an associated prime of `S`. This is a
`bridge/view` proposition from an explicit map to the owner predicate
`HasKollarExceptionalFiniteExtension R`. -/
def IsKollarExceptionalFiniteExtension (f : R →+* S) : Prop :=
  let _ : Algebra R S := f.toAlgebra
  Nontrivial S ∧
    Module.Finite R S ∧
      ¬ Function.Bijective f ∧
        (∃ n : ℕ,
          (maximalIdeal R) ^ n • (RingHom.ker f : Submodule R R) = ⊥ ∧
            (maximalIdeal R) ^ n • (⊤ : Submodule R S) ≤ (Algebra.linearMap R S).range) ∧
          maximalIdeal R ∉ associatedPrimes R S

/-- A map-level witness of Kollár's exceptional finite-extension alternative yields the canonical
owner proposition `HasKollarExceptionalFiniteExtension R`. -/
theorem hasKollarExceptionalFiniteExtension (f : R →+* S)
    (hf : f.IsKollarExceptionalFiniteExtension) :
    HasKollarExceptionalFiniteExtension R := by
  let _ : Algebra R S := f.toAlgebra
  rcases hf with ⟨hS, hfinite, hbij, htorsion, hassoc⟩
  exact (hasKollarExceptionalFiniteExtension_iff (R := R)).2
    ⟨S, inferInstance, f.toAlgebra, hfinite, hS, hbij, htorsion, hassoc⟩

end RingHom

variable [IsNoetherianRing R]

-- Proof sketch: the textbook argument first proves that one of the four alternatives must occur
-- by killing the maximal `𝔪`-power-torsion ideal, finding a nonzerodivisor in `𝔪`, and then
-- splitting into the depth-at-least-two, regular-dimension-one, and exceptional-finite-extension
-- cases via the determinantal trick. It then shows these alternatives are pairwise incompatible,
-- with the nontrivial exclusions against the fourth case handled by the freeness result for
-- maximal Cohen-Macaulay modules over a one-dimensional regular local ring and by the depth
-- inequalities in short exact sequences.
/-- Lemma 10.119.2 (Kollár): for a local Noetherian ring `R`, exactly one of the following holds:
`R` is Artinian, `R` is a regular local ring of dimension `1`, the depth of `R` is at least `2`,
or there exists a finite ring map `R → S` which is not an isomorphism, whose kernel and cokernel
are annihilated by a power of the maximal ideal, such that the maximal ideal of `R` is not an
associated prime of `S` and `S` is nonzero. -/
theorem kollar_exactly_one_of_artinian_regular_dim_one_depth_ge_two_or_exceptional_finite_extension :
    Xor' (IsArtinianRing R)
      (Xor' (IsRegularLocalRing R ∧ ringKrullDim R = 1)
        (Xor' ((2 : WithTop ℕ) ≤ moduleDepth R R)
          (HasKollarExceptionalFiniteExtension R))) := sorry

end
