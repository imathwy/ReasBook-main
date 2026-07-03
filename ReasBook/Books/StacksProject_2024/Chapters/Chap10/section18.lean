import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_18_1 (from Chap10) -/
/- Definition 10.18.1: a local ring is the canonical mathlib predicate `IsLocalRing`. -/
recall IsLocalRing

/- Companion recall: for a local ring `R`, the unique maximal ideal is the canonical ideal
`IsLocalRing.maximalIdeal R`. -/
recall IsLocalRing.maximalIdeal

/- Companion recall: for a local ring `R`, the residue field is the quotient
`IsLocalRing.ResidueField R`. -/
recall IsLocalRing.ResidueField

/- Companion recall: for a local ring `R`, the canonical residue map is
`IsLocalRing.residue R : R →+* IsLocalRing.ResidueField R`. -/
recall IsLocalRing.residue

/- Companion recall: the canonical mathlib notion of a local ring homomorphism is `IsLocalHom`. -/
recall IsLocalHom

/-! ### Example_10_18_2 (from Chap10) -/
universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable (p : Ideal R) [p.IsPrime]

/-- Example 10.18.2: if `R` is a local ring and `p` is a prime ideal different from the maximal
ideal, then the canonical map `R → Localization.AtPrime p` is not a local ring homomorphism. -/
-- Proof sketch: if the localization map were local, then the maximal ideal of
-- `Localization.AtPrime p` would comap to the maximal ideal of `R`. But for localization at a
-- prime, that same comap is exactly `p`, so `p = maximalIdeal R`, contradicting the hypothesis.
theorem localization_atPrime_not_isLocalHom_of_ne_maximalIdeal
    (hp : p ≠ maximalIdeal R) :
    ¬ IsLocalHom (algebraMap R (Localization.AtPrime p)) := by
  intro h
  letI : IsLocalHom (algebraMap R (Localization.AtPrime p)) := h
  exact hp <| by
    simpa [Localization.AtPrime.comap_maximalIdeal] using
      (IsLocalRing.maximalIdeal_comap (algebraMap R (Localization.AtPrime p)))

end

/-! ### Lemma_10_18_3 (from Chap10) -/
universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R]

/-- Lemma 10.18.3: for a commutative ring `R`, the following are equivalent: `R` is local; the
prime spectrum `Spec(R)` has exactly one closed point; `R` has a maximal ideal whose complement is
exactly the set of units; and `R` is nontrivial with the property that for every `x`, either `x` or
`1 - x` is a unit. -/
-- Proof sketch: `(1) ↔ (2)` identifies closed points of `Spec R` with `MaximalSpectrum R` via
-- `MaximalSpectrum.toPrimeSpectrum_range`, `PrimeSpectrum.isClosed_singleton_iff_isMaximal`, and
-- `IsLocalRing.of_singleton_maximalSpectrum`; `(1) ↔ (3)` uses
-- `IsLocalRing.notMem_maximalIdeal` to identify the complement of the unique maximal ideal with the
-- units; `(1) ↔ (4)` is given by
-- `IsLocalRing.isUnit_or_isUnit_one_sub_self` and `IsLocalRing.of_isUnit_or_isUnit_one_sub_self`.
theorem local_ring_tfae :
    List.TFAE
      [ IsLocalRing R
      , ∃! x : PrimeSpectrum R, IsClosed ({x} : Set (PrimeSpectrum R))
      , ∃ m : MaximalSpectrum R, ∀ x : R, x ∉ m.asIdeal ↔ IsUnit x
      , Nontrivial R ∧ ∀ x : R, IsUnit x ∨ IsUnit (1 - x)
      ] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · intro h
      letI : IsLocalRing R := h
      refine ⟨closedPoint R, isClosed_singleton_closedPoint R, fun x hx ↦ ?_⟩
      rw [PrimeSpectrum.ext_iff]
      simpa [closedPoint] using
        eq_maximalIdeal ((PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hx)
    · rintro ⟨x, hx, huniq⟩
      letI : Nonempty (MaximalSpectrum R) :=
        ⟨⟨x.asIdeal, (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hx⟩⟩
      letI : Subsingleton (MaximalSpectrum R) := ⟨fun m n ↦
        MaximalSpectrum.toPrimeSpectrum_injective <|
          (huniq _ ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr m.isMaximal)).trans
            (huniq _ ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr n.isMaximal)).symm⟩
      exact of_singleton_maximalSpectrum
  tfae_have 1 ↔ 3 := by
    constructor
    · intro h
      letI : IsLocalRing R := h
      refine ⟨⟨maximalIdeal R, maximalIdeal.isMaximal R⟩, fun x ↦ ?_⟩
      change x ∉ maximalIdeal R ↔ IsUnit x
      exact notMem_maximalIdeal
    · rintro ⟨m, hm⟩
      refine of_unique_max_ideal ⟨m.asIdeal, m.isMaximal, fun I hI ↦ ?_⟩
      refine Ideal.IsMaximal.eq_of_le hI m.isMaximal.ne_top fun x hxI ↦ ?_
      by_contra hxM
      exact hI.ne_top (I.eq_top_of_isUnit_mem hxI ((hm x).mp hxM))
  tfae_have 1 ↔ 4 := by
    constructor
    · intro h
      letI : IsLocalRing R := h
      exact ⟨inferInstance, isUnit_or_isUnit_one_sub_self⟩
    · rintro ⟨_, h⟩
      exact of_isUnit_or_isUnit_one_sub_self h
  tfae_finish

end

/-! ### Lemma_10_18_4 (from Chap10) -/
universe u v

open IsLocalRing

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

/-- Lemma 10.18.4: for a ring map `φ : R →+* S` between local rings, the following are
equivalent: `φ` is a local ring homomorphism, the image of the maximal ideal of `R` is contained
in the maximal ideal of `S`, the preimage of the maximal ideal of `S` is the maximal ideal of
`R`, and every element of `R` whose image is a unit in `S` is already a unit in `R`. -/
-- Proof sketch: clauses `(1)`, `(2)`, and `(3)` are exactly clauses `(1)`, `(2)`, and `(5)` of
-- the canonical owner theorem `IsLocalRing.local_hom_TFAE φ`; clause `(4)` is the primitive
-- unit-reflection field of `IsLocalHom φ`.
theorem local_ring_hom_tfae (φ : R →+* S) :
    List.TFAE
      [IsLocalHom φ,
        φ '' maximalIdeal R ⊆ maximalIdeal S,
        (maximalIdeal S).comap φ = maximalIdeal R,
        ∀ x : R, IsUnit (φ x) → IsUnit x] := by
  have hφ := local_hom_TFAE φ
  tfae_have 1 ↔ 2 := hφ.out 0 1
  tfae_have 1 ↔ 3 := hφ.out 0 4
  tfae_have 1 ↔ 4 := by
    constructor
    · intro h x hx
      letI := h
      exact IsUnit.of_map φ x hx
    · intro h
      exact ⟨h⟩
  tfae_finish

end

/-! ### Remark_10_18_5 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Remark 10.18.5 is a core/canonical recall. The primitive fiber-ring object is
`p.asIdeal.Fiber S = κ(p) ⊗[R] S`, and the source-facing fiber of `Spec S → Spec R` over `p`
is canonically homeomorphic to its prime spectrum. -/
recall PrimeSpectrum.preimageHomeomorphFiber

/- Companion derived recall: the same fiber is nonempty exactly when the primitive fiber ring
`p.asIdeal.Fiber S` is nontrivial, equivalently when `p` lies in the image of `Spec S → Spec R`.
-/
recall PrimeSpectrum.nontrivial_iff_mem_rangeComap

end

/-! ### Lemma_10_18_6 (from Chap10) -/
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
