import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.36.12: an element `x : S` is integral over `R` if and only if, for every prime ideal
`p` of `R`, the image of `x` in the localization of `S` at `p` is integral over
`Localization.AtPrime p.asIdeal`. -/
-- Proof sketch: localization preserves integrality for the forward implication. For the converse,
-- consider the ideal `I = { r ∈ R | r • x is integral over R }`. The primewise hypothesis shows
-- that after localizing at each maximal ideal, the image of `I` is the unit ideal: clear one
-- denominator using `exists_multiple_integral_of_isLocalization`, then clear the remaining
-- localization denominator using `exists_isIntegral_smul_of_isIntegral_map`. The local-global
-- ideal criterion `Ideal.eq_of_localization_maximal` gives `I = ⊤`, so `1 ∈ I` and hence `x` is
-- integral over `R`. This is Stacks Project, tag `034K`.
@[stacks 034K]
theorem isIntegral_iff_forall_isIntegral_atPrime {x : S} :
    IsIntegral R x ↔
      ∀ p : PrimeSpectrum R,
        IsIntegral (Localization.AtPrime p.asIdeal)
          (algebraMap S (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)) x) :=
  by
    constructor
    · intro hx p
      exact (hx.map (IsScalarTower.toAlgHom R S _)).tower_top
    · intro hx
      let I : Ideal R := {
        carrier := { r | IsIntegral R (r • x) }
        zero_mem' := by simpa using (isIntegral_zero : IsIntegral R (0 : S))
        add_mem' := by
          intro a b ha hb
          simpa [add_smul] using ha.add hb
        smul_mem' := by
          intro a b hb
          simpa [Algebra.smul_def, smul_smul, mul_assoc, mul_left_comm, mul_comm] using
            ((show IsIntegral R (algebraMap R S a) from isIntegral_algebraMap).mul hb) }
      have hlocalized :
          ∀ (P : Ideal R) (_ : P.IsMaximal), Ideal.map (algebraMap R (Localization.AtPrime P)) I = ⊤ :=
        by
        intro P hP
        let Sₚ := Localization (Algebra.algebraMapSubmonoid S P.primeCompl)
        have hxₚ : IsIntegral (Localization.AtPrime P) (algebraMap S Sₚ x) := by
          simpa [Sₚ] using hx (PrimeSpectrum.mk P hP.isPrime)
        obtain ⟨r, hr⟩ :=
          hxₚ.exists_multiple_integral_of_isLocalization P.primeCompl (algebraMap S Sₚ x)
        have hr' : IsIntegral R (algebraMap S Sₚ (r.1 • x)) := by
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R S Sₚ]
          simpa [Submonoid.smul_def, Algebra.smul_def] using hr
        obtain ⟨s, hs, hsr⟩ :=
          IsLocalization.exists_isIntegral_smul_of_isIntegral_map P.primeCompl hr'
        have hmemI : s * r.1 ∈ I := by
          simpa [I, smul_smul, mul_assoc, mul_left_comm, mul_comm] using hsr
        exact (Ideal.map (algebraMap R (Localization.AtPrime P)) I).eq_top_of_isUnit_mem
          (Ideal.mem_map_of_mem _ hmemI)
          (IsLocalization.map_units (Localization.AtPrime P) ⟨s * r.1, P.primeCompl.mul_mem hs r.2⟩)
      have htop : I = ⊤ := by
        refine Ideal.eq_of_localization_maximal fun m hm ↦ ?_
        simpa [Ideal.map_top] using hlocalized m hm
      have hone : (1 : R) ∈ I := by
        simp [htop]
      simpa [I, one_smul] using hone

end
