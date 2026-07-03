import Mathlib
import StacksProject_2024.Chap10.Lemma_10_25_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open PrimeSpectrum
open TopologicalSpace
open scoped BigOperators

variable {R : Type u} [CommRing R]

-- Layering for this item:
-- * source-facing: the set-theoretic formulation `D(f) ∩ W = ∅` in the second theorem.
-- * core/canonical owner: `CompactOpens (PrimeSpectrum R)` together with
--   `PrimeSpectrum.isCompact_isOpen_iff_ideal`.
-- * bridge/view: the second theorem rewrites `Disjoint` back to the textbook equality.

/-- Lemma 10.26.4, in library-facing owner form: if `p` is a minimal prime of `R` and `W` is a
compact open subset of `Spec R` not containing `p`, then some basic open neighborhood `D(f)` of
`p` is disjoint from `W`. -/
-- Proof sketch: cover the quasi-compact open `W` by finitely many basic opens `D(gᵢ)`. Since
-- `p ∉ W`, each `gᵢ` lies in `p.asIdeal`, hence becomes nilpotent in `Localization.AtPrime p.asIdeal`
-- by Lemma `10.25.1`. Clear denominators for the finitely many nilpotence relations to obtain
-- `f ∉ p.asIdeal` with `f * gᵢ ^ nᵢ = 0` for all `i`, which forces `D(f)` to miss each `D(gᵢ)`.
theorem exists_basicOpen_disjoint_of_isCompact_open_not_mem_of_mem_minimalPrimes
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R)
    (W : CompactOpens (PrimeSpectrum R)) (hpW : p ∉ W) :
    ∃ f : R, p ∈ basicOpen f ∧
      Disjoint (basicOpen f : Set (PrimeSpectrum R)) (W : Set (PrimeSpectrum R)) := by
  classical
  let pmin : minimalPrimes R := ⟨p.asIdeal, hp⟩
  obtain ⟨I, hIFG, hW⟩ :=
    (PrimeSpectrum.isCompact_isOpen_iff_ideal :
      IsCompact (W : Set (PrimeSpectrum R)) ∧ IsOpen (W : Set (PrimeSpectrum R)) ↔
        ∃ I : Ideal R, I.FG ∧
          (zeroLocus (I : Set R))ᶜ = (W : Set (PrimeSpectrum R))).mp ⟨W.isCompact, W.isOpen⟩
  obtain ⟨t, htI⟩ := hIFG
  have hpz : p ∈ zeroLocus (I : Set R) := by
    change p ∉ (W : Set (PrimeSpectrum R)) at hpW
    rw [← hW] at hpW
    simpa [Set.mem_compl_iff] using hpW
  have hIp : I ≤ p.asIdeal :=
    (mem_zeroLocus p (I : Set R)).mp hpz
  have hs :
      ∀ g : t, ∃ s : p.asIdeal.primeCompl, ∃ n : ℕ, 0 < n ∧ (s : R) * (g : R) ^ n = 0 := by
    intro g
    have hgmax :
        algebraMap R (Localization.AtPrime p.asIdeal) (g : R) ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) := by
      change (g : R) ∈
        Ideal.comap (algebraMap R (Localization.AtPrime p.asIdeal))
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
      rw [Localization.AtPrime.comap_maximalIdeal]
      exact hIp <| by
        rw [← htI]
        exact Ideal.subset_span g.2
    obtain ⟨n, hn⟩ :=
      isNilpotent_of_mem_maximalIdeal_localizationAtPrime_of_minimalPrime pmin hgmax
    have hnpos : 0 < n := by
      refine Nat.pos_of_ne_zero fun h0 ↦ ?_
      simp [h0] at hn
    obtain ⟨s, hs⟩ :=
      (IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
        ((g : R) ^ n)).mp <| by
          simpa [map_pow] using hn
    exact ⟨s, n, hnpos, hs⟩
  choose s n hnpos hzero using hs
  let f : R := Finset.univ.prod fun g : t ↦ (s g : R)
  refine ⟨f, ?_, ?_⟩
  · change f ∉ p.asIdeal
    have hf : f ∈ p.asIdeal.primeCompl := by
      simpa [f] using
        (Submonoid.prod_mem p.asIdeal.primeCompl fun g _ ↦ (s g).2)
    exact hf
  · refine Set.disjoint_left.2 fun x hxf hxW ↦ ?_
    have hsf :
        ∀ g : t, (s g : R) ∉ x.asIdeal := by
      intro g hsg
      apply hxf
      have hprod :
          f ∈ x.asIdeal ↔ ∃ g ∈ (Finset.univ : Finset t), (s g : R) ∈ x.asIdeal := by
        exact x.2.prod_mem_iff
      exact hprod.mpr ⟨g, by simp, hsg⟩
    have hxz : x ∉ zeroLocus (t : Set R) := by
      change x ∈ (W : Set (PrimeSpectrum R)) at hxW
      rw [← hW] at hxW
      have hxI : ¬ I ≤ x.asIdeal := by
        simpa [mem_zeroLocus, Set.mem_compl_iff] using hxW
      intro hxt
      apply hxI
      rw [← htI]
      exact Ideal.span_le.mpr hxt
    rw [mem_zeroLocus, Set.not_subset] at hxz
    obtain ⟨g, hg, hxg⟩ := hxz
    let g' : t := ⟨g, hg⟩
    have hxs : x ∈ basicOpen (s g' : R) :=
      hsf g'
    have hxg' : x ∈ basicOpen (g' : R) := by
      simpa [g'] using hxg
    have hxgn : x ∈ basicOpen ((g' : R) ^ n g') := by
      rw [basicOpen_pow (g' : R) (n g') (hnpos g')]
      exact hxg'
    have : x ∈ (basicOpen ((s g' : R) * (g' : R) ^ n g') : Set (PrimeSpectrum R)) := by
      rw [basicOpen_mul]
      exact ⟨hxs, hxgn⟩
    simpa [g', hzero g'] using this

/-- Textbook wording of Lemma 10.26.4: the disjoint basic open can be chosen as `D(f)` with
`f ∉ p`, equivalently `p ∈ D(f)`, and disjointness is the set-theoretic equality
`D(f) ∩ W = ∅`. -/
theorem exists_basicOpen_disjoint_set_of_isCompact_open_not_mem_of_mem_minimalPrimes
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R)
    (W : Opens (PrimeSpectrum R)) (hWqc : IsCompact (W : Set (PrimeSpectrum R))) (hpW : p ∉ W) :
    ∃ f : R, f ∉ p.asIdeal ∧
      ((basicOpen f : Set (PrimeSpectrum R)) ∩ (W : Set (PrimeSpectrum R)) = ∅) := by
  let Wc : CompactOpens (PrimeSpectrum R) := ⟨⟨(W : Set (PrimeSpectrum R)), hWqc⟩, W.isOpen⟩
  rcases exists_basicOpen_disjoint_of_isCompact_open_not_mem_of_mem_minimalPrimes p hp Wc hpW with
    ⟨f, hf, hdisj⟩
  exact ⟨f, hf, by simpa [Set.disjoint_iff_inter_eq_empty] using hdisj⟩

end
