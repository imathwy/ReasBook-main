import Mathlib
import StacksProject_2024.Chap10.Lemma_10_97_3

universe u

section

open IsLocalRing
open scoped TensorProduct

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

local notation "RCompletion" => AdicCompletion (maximalIdeal R) R

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- Helper for Lemma 10.162.11: a DVR localization at `p` admits a source element of `R` whose
image generates the maximal ideal of `R_p` and is nonzero there. -/
lemma exists_source_generator_of_maximalIdeal_localizationAtPrime
    (p : PrimeSpectrum R)
    (hp : ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
      IsDiscreteValuationRing (Localization.AtPrime p.asIdeal)) :
    ∃ x : R,
      Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) (Ideal.span ({x} : Set R)) =
        maximalIdeal (Localization.AtPrime p.asIdeal) ∧
      algebraMap R (Localization.AtPrime p.asIdeal) x ≠ 0 := by
  rcases hp with ⟨_, hDVR⟩
  let Rp := Localization.AtPrime p.asIdeal
  letI : IsDiscreteValuationRing Rp := hDVR
  -- Choose a uniformizer in `R_p`, then clear its denominator to get a source element `x : R`.
  obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible Rp
  obtain ⟨x, s, hπ⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl π
  have hsunit : IsUnit (IsLocalization.mk' Rp (1 : R) s) := by
    simpa using
      (IsLocalization.AtPrime.isUnit_mk'_iff Rp p.asIdeal (1 : R) s).2
        p.asIdeal.primeCompl.one_mem
  have hassoc : Associated π (algebraMap R Rp x) := by
    rw [← hπ, IsLocalization.mk'_eq_mul_mk'_one]
    simpa [IsLocalization.mk'_one] using
      (associated_mul_unit_right (algebraMap R Rp x)
        (IsLocalization.mk' Rp (1 : R) s) hsunit).symm
  have hmax_span :
      maximalIdeal Rp = Ideal.span ({algebraMap R Rp x} : Set Rp) := by
    calc
      maximalIdeal Rp = Ideal.span ({π} : Set Rp) := hπirr.maximalIdeal_eq
      _ = Ideal.span ({algebraMap R Rp x} : Set Rp) :=
        Ideal.span_singleton_eq_span_singleton.mpr hassoc
  refine ⟨x, ?_, ?_⟩
  · -- Rewrite the chosen source element as the principal generator of the maximal ideal in `R_p`.
    calc
      Ideal.map (algebraMap R Rp) (Ideal.span ({x} : Set R)) =
          Ideal.span ({algebraMap R Rp x} : Set Rp) := by
            rw [Ideal.map_span]
            simp
      _ = maximalIdeal Rp := hmax_span.symm
  · -- A generator of the nonzero maximal ideal in a DVR localization cannot vanish.
    intro hxzero
    exact IsDiscreteValuationRing.not_a_field Rp <| by
      rw [hmax_span, hxzero, Ideal.span_singleton_eq_bot]

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.162.11: once the source element `x : R` generates the maximal ideal of
`R_p`, its image also generates the maximal ideal of `(R^∧)_q`. -/
lemma source_generator_maps_to_target_maximalIdeal
    (p : PrimeSpectrum R) (q : PrimeSpectrum RCompletion) {x : R}
    (hx :
      Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) (Ideal.span ({x} : Set R)) =
        maximalIdeal (Localization.AtPrime p.asIdeal))
    (hunder : q.asIdeal.under R = p.asIdeal)
    (hImax :
      Ideal.map (algebraMap RCompletion (Localization.AtPrime q.asIdeal))
        (Ideal.map (algebraMap R RCompletion) p.asIdeal) =
          maximalIdeal (Localization.AtPrime q.asIdeal)) :
    Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (Ideal.span ({x} : Set R)) =
      maximalIdeal (Localization.AtPrime q.asIdeal) := by
  let f : Localization.AtPrime p.asIdeal →+* Localization.AtPrime q.asIdeal :=
    Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R RCompletion) hunder.symm
  have hfcomp :
      f.comp (algebraMap R (Localization.AtPrime p.asIdeal)) =
        algebraMap R (Localization.AtPrime q.asIdeal) := by
    ext r
    change f (algebraMap R (Localization.AtPrime p.asIdeal) r) =
      algebraMap R (Localization.AtPrime q.asIdeal) r
    rw [Localization.localRingHom_to_map
      (I := p.asIdeal) (J := q.asIdeal) (algebraMap R RCompletion) hunder.symm]
    rfl
  have hp_to_target :
      Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal =
        Ideal.map (algebraMap RCompletion (Localization.AtPrime q.asIdeal))
          (Ideal.map (algebraMap R RCompletion) p.asIdeal) := by
    symm
    simpa using
      (Ideal.map_map (f := algebraMap R RCompletion)
        (g := algebraMap RCompletion (Localization.AtPrime q.asIdeal))
        (I := p.asIdeal))
  have hspan_to_target :
      Ideal.map f
        (Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) (Ideal.span ({x} : Set R))) =
          Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (Ideal.span ({x} : Set R)) := by
    simpa [hfcomp] using
      (Ideal.map_map (f := algebraMap R (Localization.AtPrime p.asIdeal))
        (g := f) (I := Ideal.span ({x} : Set R)))
  have hp_to_target' :
      Ideal.map f (Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) p.asIdeal) =
        Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal := by
    simpa [hfcomp] using
      (Ideal.map_map (f := algebraMap R (Localization.AtPrime p.asIdeal))
        (g := f) (I := p.asIdeal))
  -- Push the principal ideal through the local map and rewrite it through the localized image of
  -- `pR^∧`.
  calc
    Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (Ideal.span ({x} : Set R)) =
        Ideal.map f
          (Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) (Ideal.span ({x} : Set R))) := by
            simpa using hspan_to_target.symm
    _ = Ideal.map f (maximalIdeal (Localization.AtPrime p.asIdeal)) := by rw [hx]
    _ = Ideal.map f (Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) p.asIdeal) := by
          rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)]
    _ = Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal := by
          simpa using hp_to_target'
    _ = Ideal.map (algebraMap RCompletion (Localization.AtPrime q.asIdeal))
          (Ideal.map (algebraMap R RCompletion) p.asIdeal) := hp_to_target
    _ = maximalIdeal (Localization.AtPrime q.asIdeal) := hImax

/-- Helper for Lemma 10.162.11: the source generator stays regular after passing from `R_p` to
`(R^∧)_q` along the flat local map. -/
lemma source_generator_isSMulRegular_in_target
    (p : PrimeSpectrum R) (q : PrimeSpectrum RCompletion)
    (hp : ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
      IsDiscreteValuationRing (Localization.AtPrime p.asIdeal))
    {x : R}
    (hx : algebraMap R (Localization.AtPrime p.asIdeal) x ≠ 0)
    (hunder : q.asIdeal.under R = p.asIdeal) :
    IsSMulRegular (Localization.AtPrime q.asIdeal)
      (algebraMap R (Localization.AtPrime q.asIdeal) x) := by
  rcases hp with ⟨_, hDVR⟩
  let Rp := Localization.AtPrime p.asIdeal
  let Rq := Localization.AtPrime q.asIdeal
  letI : IsDiscreteValuationRing Rp := hDVR
  let f : Rp →+* Rq :=
    Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R RCompletion) hunder.symm
  letI : Algebra Rp Rq := f.toAlgebra
  have hflat : f.Flat := by
    exact RingHom.Flat.localRingHom
      (f := algebraMap R RCompletion)
      (maximalIdeal_adicCompletion_algebraMap_faithfullyFlat R).flat
      q.asIdeal p.asIdeal hunder.symm
  letI : Module.Flat Rp Rq := hflat
  have hxreg_target :
      IsSMulRegular Rq ((algebraMap Rp Rq) (algebraMap R Rp x)) := by
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors
      (M := Rq)
      (mem_nonZeroDivisors_iff_ne_zero.mpr hx)
  have hmap_x :
      (algebraMap Rp Rq) (algebraMap R Rp x) = algebraMap R Rq x := by
    change f (algebraMap R Rp x) = algebraMap R Rq x
    rw [Localization.localRingHom_to_map
      (I := p.asIdeal) (J := q.asIdeal) (algebraMap R RCompletion) hunder.symm]
    rfl
  -- Flatness of `R_p → (R^∧)_q` makes the same source element regular on the target localization.
  exact hmap_x ▸ hxreg_target

end
