import Mathlib
import Mathlib.Data.List.TFAE
import stacks_proof.stacks_project.Chap13.Situation_13_15_1
import stacks_proof.stacks_project.Chap15.«15_60_1_1»
import stacks_proof.stacks_project.Chap15.Definition_15_65_1
import stacks_proof.stacks_project.Chap15.Definition_15_67_1
import stacks_proof.stacks_project.Chap15.Definition_15_75_1

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/-- Helper for Lemma 15.78.2: the degree-`i` homology of the derived fiber over `κ(𝔭)`. -/
abbrev primeResidueFieldDerivedHomology (𝔭 : PrimeSpectrum R) (K : DMod) (i : ℤ) :
    ModuleCat 𝔭.asIdeal.ResidueField :=
  (DerivedCategory.homologyFunctor (ModuleCat 𝔭.asIdeal.ResidueField) i).obj
    ((derivedTensorWithAlgebra (algebraMap R 𝔭.asIdeal.ResidueField)).obj K)

/-- Helper for Lemma 15.78.2: a maximal-local principal-open condition can be replaced by one
finite principal-open cover whose generators span the unit ideal. -/
lemma exists_finite_localizationAway_cover_of_maximal_local_property
    (P : R → Prop)
    (hP : ∀ (m : Ideal R) (_ : m.IsMaximal), ∃ f : R, f ∉ m ∧ P f) :
    ∃ n : ℕ, ∃ g : Fin n → R, Ideal.span (Set.range g) = ⊤ ∧ ∀ j, P (g j) := by
  classical
  let S : Set R := {f : R | P f}
  have hspan : Ideal.span S = ⊤ := by
    -- If the span were proper, some maximal ideal would contain every element satisfying `P`,
    -- contradicting the maximal-local hypothesis.
    by_contra hspan
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span S) hspan
    obtain ⟨f, hfm, hfP⟩ := hP m hm
    have hfmem : f ∈ Ideal.span S := Ideal.subset_span hfP
    exact hfm (hle hfmem)
  obtain ⟨s, hsS, hsTop⟩ := (Ideal.span_eq_top_iff_finite S).mp hspan
  let t : Finset R := s
  let g : Fin t.card → R := fun i ↦ (t.equivFin.symm i : R)
  have hg_range : Set.range g = (↑t : Set R) := by
    -- Reindex the chosen finite subset by `Fin t.card`.
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (t.equivFin.symm i).2
    · intro hx
      exact ⟨t.equivFin ⟨x, hx⟩, by simp [g]⟩
  refine ⟨t.card, g, ?_, ?_⟩
  · simpa [hg_range] using hsTop
  · intro i
    exact (hsS (t.equivFin.symm i).2 : P (g i))

/- Domain-style sampling for Lemma 15.78.2:
- primary domain: perfectness and tor-amplitude for pseudo-coherent derived `R`-complexes,
  detected on residue-field fibers over prime and maximal ideals;
- sampled owner declarations:
  `K.IsPerfect`,
  `HasTorAmplitudeIn K a b`,
  `primeResidueFieldDerivedHomology`,
  `K ⊗[R]^L[κ(𝔭)]`;
- best owner abstraction: the public source-facing statement should be expressed in terms of the
  canonical owners `K.IsPerfect`, `HasTorAmplitudeIn`, and the earlier chapter bridge
  `primeResidueFieldDerivedHomology`, rather than re-expanding residue-field fibers through
  `derivedTensorProduct` and `singleFunctor`;
- primitive vs. derived:
  primitive data are the pseudo-coherent object `K`, the interval bounds `a, b`, and the
  residue-field homology objects indexed by primes;
  derived API is the conjunction `K.IsPerfect ∧ HasTorAmplitudeIn K a b` and the maximal-ideal
  specialization of the prime-fiber vanishing condition.

Source/core/bridge triage:
- `source-facing`: the TFAE criterion below;
- `core/canonical`: `K.IsPerfect` and `HasTorAmplitudeIn K a b`;
- `bridge/view`: `primeResidueFieldDerivedHomology`, which names the degreewise homology of the
  canonical derived base change `K ⊗_R^L κ(𝔭)` without introducing a second owner abstraction.
-/

-- Proof sketch: the implications from perfection with tor-amplitude to prime fibers and then to
-- maximal fibers are immediate by derived base change. For the converse, use Lemma `15.77.4` to
-- deduce vanishing of the cohomology of `K` outside `[a, b]` and to obtain local perfect
-- tor-amplitude bounds near every maximal ideal; then conclude globally from Lemma `15.75.12` and
-- Lemma `15.67.16`.
/-- Lemma 15.78.2: for a pseudo-coherent object `K` of `D(R)`, the following are equivalent:
`K` is perfect with tor-amplitude in `[a, b]`; for every prime `𝔭` of `R`, the derived fiber
`K \otimes_R^{\mathbf L} κ(\mathfrak p)` has vanishing homology outside `[a, b]`; and it is
enough to check this only on maximal ideals. -/
@[stacks 068V]
theorem perfect_torAmplitude_tfae_prime_and_maximal_residueField_homology_vanishing_of_isPseudoCoherent
    (K : DMod) (a b : ℤ) (hK : K.IsPseudoCoherent) :
    List.TFAE [
      K.IsPerfect ∧ HasTorAmplitudeIn K a b,
      ∀ 𝔭 : PrimeSpectrum R, ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero (primeResidueFieldDerivedHomology 𝔭 K i),
      ∀ (𝔪 : PrimeSpectrum R) (_ : 𝔪.asIdeal.IsMaximal) (i : ℤ), i ∉ Set.Icc a b →
        IsZero (primeResidueFieldDerivedHomology 𝔪 K i)
    ] := by
  tfae_have 1 → 2 := by
    intro hPerfectTor
    -- TODO: compare the derived scalar-extension owner
    -- `((derivedTensorWithAlgebra (algebraMap R 𝔭.asIdeal.ResidueField)).obj K)` with the
    -- tor-amplitude test object `K ⊗[R]^L (κ(𝔭)[0])`. The current blocker is this exact bridge,
    -- not the vanishing step after the bridge is available.
    have _ := hPerfectTor
    sorry
  tfae_have 2 → 3 := by
    intro hPrime 𝔪 _ i hi
    -- Maximal ideals are a special case of prime ideals.
    have hzero := hPrime 𝔪 i hi
    change IsZero (primeResidueFieldDerivedHomology 𝔪 K i) at hzero ⊢
    exact hzero
  tfae_have 3 → 1 := by
    intro hMax
    -- Route correction: the source proof first globalizes the homology vanishing outside
    -- `[a, b]`, then extracts a finite principal-open cover on which `K` is already perfect with
    -- tor-amplitude in `[a, b]`.
    -- TODO: implement the source-faithful localization step:
    -- 1. use Lemma `15.77.4` degreewise to show `H^i(K)` vanishes globally for `i ∉ [a, b]`;
    -- 2. for each maximal ideal, combine the lower-end gap splitting with the global cohomology
    --    vanishing to obtain some `f ∉ 𝔪` with `(K ⊗[R]^L[Localization.Away f]).IsPerfect` and
    --    `HasTorAmplitudeIn (K ⊗[R]^L[Localization.Away f]) a b`;
    -- 3. apply `exists_finite_localizationAway_cover_of_maximal_local_property`,
    --    `isPerfect_of_localizationAway_unitIdeal`, and
    --    `hasTorAmplitudeIn_of_localizationAway_unitIdeal`.
    have _ := hK
    have _ := hMax
    sorry
  tfae_finish

end

end CategoryTheory
