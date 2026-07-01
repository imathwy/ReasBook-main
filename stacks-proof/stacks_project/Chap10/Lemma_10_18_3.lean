import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

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
