import Mathlib
import StacksProject_2024.Chap10.Lemma_10_52_4
import StacksProject_2024.Chap10.Lemma_10_52_8
import StacksProject_2024.Chap10.Lemma_10_62_4

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing PrimeSpectrum

universe u v

section SupportAndDimensionOfModules

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

-- Proof sketch: use the owner support-annihilator criterion from Lemma `10.62.4`. If
-- `Module.support R M = {closedPoint R}`, then `Module.support R M ⊆ V(maximalIdeal R)`, so some
-- power of `maximalIdeal R` annihilates `M`; Lemma `10.52.8` turns that into finite length.
-- Conversely, finite length gives such a power by Lemma `10.52.4`, hence the same support
-- inclusion via Lemma `10.62.4`. The local closed point lies in the support of a nontrivial
-- module, so the inclusion is an equality.
/-- Lemma 10.62.3: for a nonzero finite module over a Noetherian local ring, the support is the
singleton consisting of the closed point of `Spec R` if and only if the module has finite length
over `R`. -/
theorem support_eq_singleton_closedPoint_iff_isFiniteLength [Nontrivial M] :
    Module.support R M = ({closedPoint R} : Set (PrimeSpectrum R)) ↔ IsFiniteLength R M := by
  have hclosed :
      ({closedPoint R} : Set (PrimeSpectrum R)) = PrimeSpectrum.zeroLocus (maximalIdeal R) := by
    simp [PrimeSpectrum.zeroLocus_eq_singleton, IsLocalRing.closedPoint]
  have hsupport :
      Module.support R M ⊆ PrimeSpectrum.zeroLocus (maximalIdeal R) ↔ IsFiniteLength R M := by
    rw [← Module.exists_pow_smul_top_eq_bot_iff_support_subset_zeroLocus
      (maximalIdeal R) (Ideal.fg_of_isNoetherianRing (maximalIdeal R))]
    constructor
    · rintro ⟨n, hn⟩
      exact isFiniteLength_of_pow_smul_eq_bot (maximalIdeal R)
        (Ideal.fg_of_isNoetherianRing (maximalIdeal R)) hn
    · exact exists_pow_maximalIdeal_smul_eq_bot_of_isFiniteLength
  constructor
  · intro hsupp
    have hsubset : Module.support R M ⊆ PrimeSpectrum.zeroLocus (maximalIdeal R) := by
      rw [hsupp, hclosed]
    exact hsupport.mp hsubset
  · intro hM
    exact Set.Subset.antisymm (by simpa [hclosed] using hsupport.mpr hM) <|
      Set.singleton_subset_iff.mpr <| IsLocalRing.closedPoint_mem_support R M

end SupportAndDimensionOfModules
