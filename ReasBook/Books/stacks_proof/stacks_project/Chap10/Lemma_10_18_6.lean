import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable (p : PrimeSpectrum R)

local notation "f" => algebraMap R S
local notation "pS" => Ideal.map f p.asIdeal
local notation "Sₚ" => Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
local notation "pSₚ" => Ideal.map (algebraMap S Sₚ) pS
local notation "SmodpSₚ" =>
  Localization (Algebra.algebraMapSubmonoid (S ⧸ pS) p.asIdeal.primeCompl)

/-
Domain triage:
* primary domain: fibers of the canonical spectral map `PrimeSpectrum.comap (algebraMap R S)`
  together with their localization-at-`p` nontriviality criteria;
* sampled owner declarations: `PrimeSpectrum.nontrivial_iff_mem_rangeComap`,
  `PrimeSpectrum.mem_range_comap_iff`, `Ideal.Fiber`,
  `IsLocalization.map_algebraMap_ne_top_iff_disjoint`;
* best owner abstraction: the pair consisting of the spectral map
  `PrimeSpectrum.comap (algebraMap R S)` and the canonical fiber ring `p.asIdeal.Fiber S`;
* primitive data: only the `R`-algebra structure on `S` and the prime `p`;
* derived API: the localized quotient rings `Sₚ ⧸ pSₚ` and `(S / pS)ₚ`, whose nontriviality is
  another source-facing test for the same image condition.

Layering:
* `source-facing`: the textbook TFAE for a fixed `p : Spec R`;
* `core/canonical`: `PrimeSpectrum.comap (algebraMap R S)` and `p.asIdeal.Fiber S`;
* `bridge/view`: the two localization-and-quotient nontriviality criteria and the contraction
  formula `(p.asIdeal.map f).comap f = p.asIdeal`.
-/

namespace PrimeSpectrum

/-- Lemma 10.18.6: for a ring map `R → S` and a prime `p : Spec R`, the following are equivalent:
`p` lies in the image of `Spec S → Spec R`, the fiber ring `κ(p) ⊗[R] S` is nontrivial, the
localized quotient `Sₚ / pSₚ` is nontrivial, the localization `(S / pS)ₚ` is nontrivial, and
contracting `pS` back along `R → S` recovers `p`. -/
-- Proof sketch: use the owner theorem `PrimeSpectrum.nontrivial_iff_mem_rangeComap` for the
-- equivalence between the image condition and the fiber ring `κ(p) ⊗[R] S`. Localizing at `p`
-- turns this into the local map `Rₚ → Sₚ`, whose residue-field fiber is canonically the quotient
-- `Sₚ / pSₚ`. For the two localized quotient conditions, use
-- `Ideal.Quotient.nontrivial_iff`, `IsLocalization.map_algebraMap_ne_top_iff_disjoint`, and
-- `IsLocalization.subsingleton_iff` to identify their nontriviality with the same contraction
-- criterion. Finally, `PrimeSpectrum.mem_range_comap_iff` identifies the image condition with
-- that contraction criterion.
@[stacks 00E7]
theorem mem_range_comap_tfae :
    List.TFAE
      [ p ∈ Set.range (comap f),
        Nontrivial (p.asIdeal.Fiber S),
        Nontrivial (Sₚ ⧸ pSₚ),
        Nontrivial SmodpSₚ,
        Ideal.comap f pS = p.asIdeal ] := by
  tfae_have 1 ↔ 2 := by
    simpa using p.nontrivial_iff_mem_rangeComap.symm
  tfae_have 1 ↔ 5 := by
    change p ∈ Set.range (comap f) ↔ Ideal.comap f (Ideal.map f p.asIdeal) = p.asIdeal
    simpa using
      (PrimeSpectrum.mem_range_comap_iff f :
        p ∈ Set.range (comap f) ↔ Ideal.comap f (Ideal.map f p.asIdeal) = p.asIdeal)
  tfae_have 3 ↔ 5 := by
    let M := Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl
    change Nontrivial (Localization M ⧸ Ideal.map (algebraMap S (Localization M)) pS) ↔
      Ideal.comap f pS = p.asIdeal
    rw [Ideal.Quotient.nontrivial_iff]
    change Ideal.map (algebraMap S (Localization M)) pS ≠ ⊤ ↔ Ideal.comap f pS = p.asIdeal
    have hdisj :
        Ideal.map (algebraMap S (Localization M)) pS ≠ ⊤ ↔ Disjoint (M : Set S) (pS : Set S) :=
      IsLocalization.map_algebraMap_ne_top_iff_disjoint M (Localization M) pS
    rw [hdisj]
    constructor
    · intro h
      apply le_antisymm
      · intro x hx
        by_contra hx'
        exact Set.disjoint_left.mp h ⟨x, hx', rfl⟩ hx
      · exact Ideal.le_comap_map
    · intro h
      rw [Set.disjoint_left]
      intro x hxM hxI
      rcases hxM with ⟨x, hx, rfl⟩
      exact hx <| by simpa [← Ideal.mem_comap, h] using hxI
  tfae_have 4 ↔ 5 := by
    let M := Algebra.algebraMapSubmonoid (S ⧸ pS) p.asIdeal.primeCompl
    change Nontrivial (Localization M) ↔ Ideal.comap f pS = p.asIdeal
    rw [← not_subsingleton_iff_nontrivial]
    have hsub : Subsingleton (Localization M) ↔ (0 : S ⧸ pS) ∈ M :=
      IsLocalization.subsingleton_iff
    rw [hsub]
    constructor
    · intro h
      apply le_antisymm
      · intro x hx
        by_contra hx'
        apply h
        refine ⟨x, hx', ?_⟩
        change Ideal.Quotient.mk pS (algebraMap R S x) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.2 <| by simpa [Ideal.mem_comap] using hx
      · exact Ideal.le_comap_map
    · intro h hx
      rcases hx with ⟨x, hx, hx0⟩
      have hxmem : x ∈ Ideal.comap (algebraMap R S) pS := by
        change Ideal.Quotient.mk pS (algebraMap R S x) = 0 at hx0
        simpa [Ideal.mem_comap] using Ideal.Quotient.eq_zero_iff_mem.1 hx0
      exact hx <| by simpa [h] using hxmem
  tfae_finish

end PrimeSpectrum

end
