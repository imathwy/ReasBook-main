import Mathlib
import stacks_project.Chap10.Definition_10_72_1
import stacks_project.Chap10.Lemma_10_72_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open RingTheory.Sequence
open IsLocalRing
open scoped ENat

namespace Ideal

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- 
Source/core/bridge triage:
* primary domain: commutative algebra of depth, regular sequences, and localization at primes;
* sampled owner API: `Ideal.depth`, `Ideal.regularSequenceLengths`,
  `Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top` from the local chapter owner file, together
  with mathlib's `Module.supportDim_add_length_eq_supportDim_of_isRegular`;
* layer: `source-facing`, since this item is a finiteness consequence for the existing owner
  object `Ideal.depth`, not a new definition of depth data;
* primitive vs derived split: the primitive data are only the ideal `I`, the finite module `M`,
  and the owner predicate `Sequence.IsRegular M rs`; finiteness is a derived theorem, so this file
  should stay a thin companion to the owner abstraction instead of introducing a parallel wrapper.
-/

-- Proof sketch: `I • ⊤ ≠ ⊤` already forces `M` to be nontrivial; otherwise `⊤ = ⊥`, hence
-- `I • ⊤ = ⊤`. The quotient `M ⧸ I • ⊤` is then nonzero, so choose a prime in its support and
-- localize there. Any `M`-regular sequence in `I` localizes to an `M_𝔭`-regular sequence in
-- `I_𝔭`, so `depth I M` is bounded by the depth of the localized module, which is finite by
-- Lemma 10.72.3.
omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.72.4: a prime in the support of `M / IM` also lies in the support of `M`
and contains `I`. -/
private lemma support_quotient_prime_contains_ideal (I : Ideal R) {p : PrimeSpectrum R}
    (hp : p ∈ Module.support R (M ⧸ I • (⊤ : Submodule R M))) :
    p ∈ Module.support R M ∧ I ≤ p.asIdeal := by
  -- Rewrite `Supp(M / IM)` as `Supp(M) ∩ V(I)` and read off the two pieces of data we need.
  have hp' : p ∈ Module.support R M ∩ PrimeSpectrum.zeroLocus I := by
    simpa [Module.support_quotient] using hp
  refine ⟨hp'.1, ?_⟩
  simpa [PrimeSpectrum.mem_zeroLocus] using hp'.2

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.72.4: every `I`-regular sequence on `M` remains regular after localizing
at a prime in `Supp(M)` that contains `I`, now inside the maximal ideal of the local ring. -/
private lemma regularSequenceLengths_subset_localizationAtPrime (I : Ideal R) (p : PrimeSpectrum R)
    (hpM : p ∈ Module.support R M) (hIp : I ≤ p.asIdeal) :
    Ideal.regularSequenceLengths I M ⊆
      Ideal.regularSequenceLengths (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule.AtPrime p.asIdeal M) := by
  -- Localize a witness sequence and transport both regularity and ideal membership termwise.
  intro d hd
  rcases hd with ⟨rs, hreg, hI, rfl⟩
  let Rp := Localization.AtPrime p.asIdeal
  let Mp := LocalizedModule.AtPrime p.asIdeal M
  letI : Nontrivial Mp := Module.mem_support_iff.mp hpM
  have hmem : ∀ r ∈ rs, r ∈ p.asIdeal := by
    intro r hr
    exact hIp (hI (Ideal.subset_span hr))
  have hreg_loc : IsRegular Mp (rs.map (algebraMap R Rp)) := by
    simpa [Mp, Rp] using
      hreg.1.isRegular_of_isLocalizedModule_of_mem
        (S := Rp) (p := p.asIdeal)
        (N := Mp) (f := LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) hmem
  have hI_loc :
      Ideal.ofList (rs.map (algebraMap R Rp)) ≤ maximalIdeal Rp := by
    -- The localized ideal lands in the unique maximal ideal because all terms lie in `p`.
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)]
    simpa [Rp, Ideal.map_ofList] using
      (Ideal.map_mono (f := algebraMap R (Localization.AtPrime p.asIdeal)) (le_trans hI hIp))
  exact ⟨rs.map (algebraMap R Rp), hreg_loc, hI_loc, by simp⟩

/-- Helper for Lemma 10.72.4: if `p` lies in `Supp(M)`, then the depth of the localized module
`Mₚ` over the local ring `Rₚ` is finite. -/
private lemma moduleDepth_localizationAtPrime_lt_top_of_mem_support (p : PrimeSpectrum R)
    (hpM : p ∈ Module.support R M) :
    moduleDepth (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) < ⊤ := by
  let Rp := Localization.AtPrime p.asIdeal
  let Mp := LocalizedModule.AtPrime p.asIdeal M
  letI : Nontrivial Mp := Module.mem_support_iff.mp hpM
  -- Compare the localized depth to the support dimension and then to the finite span-rank bound.
  have hdepth_le :
      WithBot.some (moduleDepth Rp Mp : ℕ∞) ≤ Module.supportDim Rp Mp :=
    depth_le_supportDim (R := Rp) (M := Mp)
  have hsupport_le : Module.supportDim Rp Mp ≤ ringKrullDim Rp :=
    Module.supportDim_le_ringKrullDim (R := Rp) (M := Mp)
  have hkrull_le : ringKrullDim Rp ≤ (maximalIdeal Rp).spanFinrank := by
    simpa [Rp] using ringKrullDim_le_spanFinrank_maximalIdeal (R := Rp)
  have hle :
      WithBot.some (moduleDepth Rp Mp : ℕ∞) ≤ (maximalIdeal Rp).spanFinrank := by
    exact le_trans hdepth_le (le_trans hsupport_le hkrull_le)
  have hle_nat : moduleDepth Rp Mp ≤ (maximalIdeal Rp).spanFinrank := by
    exact_mod_cast hle
  exact lt_of_le_of_lt hle_nat (ENat.coe_lt_top _)

/-- Lemma 10.72.4: if `R` is Noetherian, `I ⊆ R` is an ideal, and `M` is a finite `R`-module
with `IM ≠ M`, then the `I`-depth of `M` is finite. -/
theorem depth_lt_top_of_smul_top_ne_top (I : Ideal R)
    (hIM : I • (⊤ : Submodule R M) ≠ ⊤) :
    I.depth M < ⊤ := by
  letI : Nontrivial M := by
    by_contra hM
    letI : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
    have htop : (⊤ : Submodule R M) = ⊥ := (⊤ : Submodule R M).eq_bot_of_subsingleton
    exact hIM <| by rw [htop, Submodule.smul_bot]
  letI : Nontrivial (M ⧸ I • (⊤ : Submodule R M)) := by
    simpa using hIM
  -- Choose a prime of `Supp(M / IM)` and extract the support/containment information from it.
  obtain ⟨p, hp⟩ := Module.nonempty_support_of_nontrivial
    (R := R) (M := M ⧸ I • (⊤ : Submodule R M))
  rcases support_quotient_prime_contains_ideal (R := R) (M := M) I (p := p) hp
    with ⟨hpM, hIp⟩
  let Rp := Localization.AtPrime p.asIdeal
  let Mp := LocalizedModule.AtPrime p.asIdeal M
  have hdepth_le_local : I.depth M ≤ moduleDepth Rp Mp := by
    -- Every global `I`-regular sequence localizes to a maximal-ideal regular sequence on `Mₚ`.
    rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I M hIM]
    by_cases hlocal : maximalIdeal Rp • (⊤ : Submodule Rp Mp) = ⊤
    · rw [show moduleDepth Rp Mp = ⊤ from Ideal.depth_eq_top_of_smul_top (maximalIdeal Rp) Mp hlocal]
      exact le_top
    · rw [show moduleDepth Rp Mp =
          sSup (Ideal.regularSequenceLengths (maximalIdeal Rp) Mp) from
          Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal Rp) Mp hlocal]
      refine sSup_le ?_
      intro d hd
      exact le_sSup (regularSequenceLengths_subset_localizationAtPrime
        (R := R) (M := M) I p hpM hIp hd)
  -- The localized depth is finite, so the original depth is finite as well.
  exact lt_of_le_of_lt hdepth_le_local <|
    moduleDepth_localizationAtPrime_lt_top_of_mem_support (R := R) (M := M) p hpM

end Ideal
