import Mathlib
import StacksProject_2024.Chap10.Lemma_10_35_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Classical

universe u

/-
Domain sampling:
* primary domain: commutative algebra of `Spec R`, `MaxSpec R`, Jacobson rings, and Krull
  dimension in the Noetherian setting;
* owner declarations inspected in this domain:
  - `isJacobsonRing_of_isNoetherianRing_of_dimensionLEOne_of_infinite_maximalSpectrum`
  - `exists_nonmaximal_prime_basicOpen_inter_zeroLocus_eq_singleton_of_not_isJacobsonRing`
  - `infinite_open_subset_of_local_noetherian_domain_of_two_le_ringKrullDim`
  - `Ideal.primeSpectrumQuotientOrderIsoZeroLocus`;
* best owner abstraction: `IsJacobsonRing R`, with `Ring.DimensionLEOne` as the canonical
  dimension-one owner and quotient/localization spectrum identifications as bridge/view API;
* primitive vs. derived: the source-facing inputs are infinitude of prime ideals and the primewise
  maximal-or-infinite-over condition, while the comparison between `PrimeSpectrum R` and
  `MaximalSpectrum R` in dimension one is derived API and stays private.
-/

section

variable {R : Type u} [CommRing R] [Ring.DimensionLEOne R]

private theorem finite_primeSpectrum_of_finite_maximalSpectrum
    [Finite (MaximalSpectrum R)] :
    Finite (PrimeSpectrum R) := by
  classical
  let s : Set (Ideal R) := {(⊥ : Ideal R)} ∪ Set.range MaximalSpectrum.asIdeal
  have hs : s.Finite :=
    (Set.finite_singleton (⊥ : Ideal R)).union (Set.finite_range MaximalSpectrum.asIdeal)
  letI : Fintype s := hs.fintype
  let f : PrimeSpectrum R → s := fun x ↦ by
    refine ⟨x.asIdeal, ?_⟩
    by_cases hx : x.asIdeal = ⊥
    · exact Or.inl hx
    · exact Or.inr
        ⟨⟨x.asIdeal, x.isPrime.isMaximal hx⟩, rfl⟩
  exact Finite.of_injective f fun x y hxy ↦
    PrimeSpectrum.ext <| by simpa using congrArg Subtype.val hxy

private theorem infinite_maximalSpectrum_of_infinite_primeSpectrum
    [Infinite (PrimeSpectrum R)] : Infinite (MaximalSpectrum R) := by
  by_contra h
  haveI : Finite (MaximalSpectrum R) := not_infinite_iff_finite.mp h
  haveI : Finite (PrimeSpectrum R) := finite_primeSpectrum_of_finite_maximalSpectrum
  exact Finite.false (inferInstance : Finite (PrimeSpectrum R))

end

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

-- Proof sketch: this is a reformulation of Lemma `10.35.6`. In a domain of Krull dimension `1`,
-- every nonzero prime ideal is maximal, so only `⊥` can fail to be maximal. Hence infinitely many
-- prime ideals force infinitely many maximal ideals, and the dimension-one Jacobson criterion
-- applies.
/-- Lemma 10.61.4 (1): any Noetherian domain of Krull dimension `1` with infinitely many prime
ideals is a Jacobson ring. In Lean, “infinitely many prime ideals” is expressed canonically by
`[Infinite (PrimeSpectrum R)]`. -/
theorem isJacobsonRing_of_isNoetherianRing_of_ringKrullDim_eq_one_of_infinite_primeIdeals
    [IsDomain R] [Infinite (PrimeSpectrum R)] (hdim : ringKrullDim R = 1) :
    IsJacobsonRing R := by
  have hdim' : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by simp [hdim])
  letI : Ring.DimensionLEOne R :=
    ⟨fun {p} hp hprime ↦ Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hdim' p hp hprime⟩
  letI : Infinite (MaximalSpectrum R) := infinite_maximalSpectrum_of_infinite_primeSpectrum
  exact isJacobsonRing_of_isNoetherianRing_of_dimensionLEOne_of_infinite_maximalSpectrum R

-- Proof sketch: argue by contradiction. If `R` were not Jacobson, Lemma `10.35.5` gives a
-- nonmaximal prime `P` whose singleton is locally closed in `Spec R`. For each prime `Q ⊇ P`,
-- the corresponding localization of `R ⧸ P` has locally closed generic point, so Lemma `10.61.1`
-- forces it to have Krull dimension `1`; thus `R ⧸ P` is a one-dimensional Noetherian domain.
-- The hypothesis gives infinitely many primes above `P`, hence infinitely many primes of `R ⧸ P`,
-- so clause `(1)` makes `R ⧸ P` Jacobson, contradicting that `{P}` is open in `V(P)`.
/-- Lemma 10.61.4 (2): any Noetherian ring such that every prime ideal is either maximal or
contained in infinitely many prime ideals is a Jacobson ring. -/
theorem isJacobsonRing_of_isNoetherianRing_of_primeIdeal_isMaximal_or_infinite_primesOver
    (hprime :
      ∀ p : PrimeSpectrum R,
        p.asIdeal.IsMaximal ∨ Infinite { q : PrimeSpectrum R // p ≤ q }) :
    IsJacobsonRing R := sorry

end
