import StacksProject_2024.Chap10.Lemma_10_17_7
import StacksProject_2024.Chap10.Lemma_10_39_16
import StacksProject_2024.Chap10.Lemma_10_97_2
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing PrimeSpectrum

section

variable {R : Type u} [CommRing R] (I : Ideal R) [IsNoetherianRing R]

-- Proof sketch: use the owner criterion `faithfullyFlat_iff_closedPoints_subset_range` together
-- with Lemma `10.97.2` for flatness. If `I ≤ Ring.jacobson R`, then every closed point of
-- `Spec R` contains `I`, so it comes from `Spec (R ⧸ I)` via the quotient-spectrum homeomorphism
-- from Lemma `10.17.7`; composing with the surjective map `AdicCompletion I R → R ⧸ I` gives a
-- lift to `Spec (AdicCompletion I R)`.
/-- Lemma 10.97.3: if `I` is contained in the Jacobson radical of a Noetherian ring `R`, then the
canonical map from `R` to its `I`-adic completion is faithfully flat. -/
@[stacks 00MC]
theorem adicCompletion_algebraMap_faithfullyFlat_of_le_jacobson
    (hI : I ≤ Ring.jacobson R) :
    RingHom.FaithfullyFlat (algebraMap R (AdicCompletion I R)) := by
  rw [faithfullyFlat_iff_closedPoints_subset_range _ (adicCompletion_algebraMap_flat I)]
  intro x hx
  have hxmax : x.asIdeal.IsMaximal := by
    exact (isClosed_singleton_iff_isMaximal x).mp (by simpa [closedPoints] using hx)
  let _ : x.asIdeal.IsMaximal := hxmax
  have hxI : I ≤ x.asIdeal := hI.trans (Ring.jacobson_le_of_isMaximal x.asIdeal)
  let x' : PrimeSpectrum (R ⧸ I) :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I).symm ⟨x, by simpa using hxI⟩
  refine ⟨PrimeSpectrum.comap (AdicCompletion.evalOneₐ I).toRingHom x', ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply]
  change PrimeSpectrum.comap
      ((AdicCompletion.evalOneₐ I).toRingHom.comp (algebraMap R (AdicCompletion I R))) x' = x
  have hx'' : ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I) x').1 = x := by
    exact congrArg Subtype.val
      ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I).apply_symm_apply
        ⟨x, by simpa using hxI⟩)
  have hx' :
      PrimeSpectrum.comap (Ideal.Quotient.mk I) x' = x := by
    simpa using hx''
  rw [show (AdicCompletion.evalOneₐ I).toRingHom.comp (algebraMap R (AdicCompletion I R)) =
      Ideal.Quotient.mk I by
        ext r
        simp]
  exact hx'

-- Proof sketch: apply the previous theorem to `I = maximalIdeal R`. In a local ring the maximal
-- ideal is contained in the Jacobson radical, by `maximalIdeal_le_jacobson`.
/-- For a Noetherian local ring, the canonical map to its maximal-ideal adic completion is
faithfully flat. This is the completion `\varprojlim_n R / (maximalIdeal R)^n` from the textbook
statement. -/
theorem maximalIdeal_adicCompletion_algebraMap_faithfullyFlat
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    RingHom.FaithfullyFlat (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  adicCompletion_algebraMap_faithfullyFlat_of_le_jacobson (maximalIdeal R)
    (by
      simpa [Ideal.jacobson_bot] using
        (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R)))

end
