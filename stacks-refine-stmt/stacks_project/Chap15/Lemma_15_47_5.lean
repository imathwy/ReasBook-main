import Mathlib
import stacks_project.Chap10.Definition_10_137_10
import stacks_project.Chap10.Lemma_10_137_2
import stacks_project.Chap10.Lemma_10_140_9
import stacks_project.Chap10.Lemma_10_163_10
import stacks_project.Chap15.Lemma_15_47_4

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

universe u v

open Localization IsLocalization

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsDomain R] [IsDomain S] [Algebra.FiniteType R S] [IsJ0Ring R]

/- Source/core/bridge triage:
* source-facing: ascent of the `J-0` condition along an injective finite type map of domains with
  separable fraction-field extension;
* core/canonical: the chapter owner `IsJ0Ring`;
* bridge/view: in the domain case, a nonempty regular open can be represented by a nonzero
  principal localization that is regular, and the induced fraction-field extension of an
  injective domain map is measured by the canonical owner predicate
  `fractionRingIsSeparableOver hinj`.

The primitive data are the `J-0` owner and the separability condition on fraction fields. The
principal-localization witness is derived chapter API via
`exists_nonzero_isRegularRing_localizationAway_of_isJ0Ring`, so this file should state the main
result using `IsJ0Ring` rather than a parallel existential interface.
-/

-- Proof sketch: choose a nonzero `f : R` with `R[1 / f]` regular from the `J-0` hypothesis on
-- `R`. By Lemma `10.140.9`, the generic point `(0) ∈ Spec S` is `IsSmoothAt` over `R`, and the
-- bridge `smoothAtPrime_iff_isSmoothAt` then yields a principal localization `S[1 / g]` with
-- `g ≠ 0` that is smooth over `R`. Localizing once more away from the image of `f` gives a
-- smooth `R[1 / f]`-algebra, so Lemma `10.163.10` makes that iterated localization regular.
-- Regular rings are `J-0`, and Lemma `15.47.4` then descends `J-0` twice: first from the iterated
-- localization to `S[1 / g]`, then from `S[1 / g]` to `S`.
/-- Lemma 15.47.5: for an injective finite type ring map `R → S` from a Noetherian domain to a
domain, if `R` is `J-0` and the induced extension of fraction fields `FractionRing S /
FractionRing R` is separable in the Stacks Project sense, then `S` is `J-0`. -/
theorem isJ0Ring_of_injective_finiteType_of_separable_fractionRingExtension
    (hinj : Function.Injective (algebraMap R S))
    (hsep : fractionRingIsSeparableOver hinj) :
    IsJ0Ring S := by
  let hR : IsJ0Ring R := inferInstance
  obtain ⟨f, hf, hRf_reg⟩ := exists_nonzero_isRegularRing_localizationAway_of_isJ0Ring R
  let Rf := Localization.Away f
  letI : IsNoetherianRing R := hR.toIsNoetherian
  letI : IsRegularRing Rf := hRf_reg
  letI : FinitePresentation R S := FinitePresentation.of_finiteType.mp inferInstance
  have hS0 : IsSmoothAt R (⊥ : Ideal S) :=
    (isSmoothAt_zero_iff_isSeparableOver_fractionRing hinj).2 hsep
  obtain ⟨g, hg, hSg_smooth⟩ :=
    (smoothAtPrime_iff_isSmoothAt R S (⊥ : PrimeSpectrum S)).2 hS0
  have hg0 : g ≠ 0 := by
    intro h0
    exact hg (h0 ▸ Ideal.zero_mem _)
  let Sg := Localization.Away g
  letI : Smooth R Sg := hSg_smooth
  have hgPowers := powers_le_nonZeroDivisors_of_noZeroDivisors hg0
  letI : IsDomain Sg := isDomain_of_le_nonZeroDivisors Sg hgPowers
  have hinjSg : Function.Injective (algebraMap S Sg) := IsLocalization.injective Sg hgPowers
  have hinjRSg : Function.Injective (algebraMap R Sg) := by
    simpa [IsScalarTower.algebraMap_eq R S Sg] using hinjSg.comp hinj
  have hfSg : algebraMap R Sg f ≠ 0 := (map_ne_zero_iff (algebraMap R Sg) hinjRSg).2 hf
  let Sgf := Localization.Away (algebraMap R Sg f)
  have hfSgPowers := powers_le_nonZeroDivisors_of_noZeroDivisors hfSg
  letI : IsDomain Sgf := isDomain_of_le_nonZeroDivisors Sgf hfSgPowers
  have hfSgf_unit : IsUnit (algebraMap R Sgf f) := by
    change IsUnit (algebraMap Sg Sgf (algebraMap R Sg f))
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap R Sg f)
  letI : Algebra Rf Sgf := (Localization.awayLift (algebraMap R Sgf) f hfSgf_unit).toAlgebra
  have hRfSgf : RingHom.Smooth (Localization.awayLift (algebraMap R Sgf) f hfSgf_unit) :=
    by
      letI : Smooth R Sgf := smooth_localization_away_target R Sg (algebraMap R Sg f)
      exact smooth_away_lift_of_isUnit R Sgf f hfSgf_unit
  letI : Smooth Rf Sgf := hRfSgf.toAlgebra
  have hSgf_reg : IsRegularRing Sgf := by
    letI : IsNoetherianRing Sgf := Algebra.FiniteType.isNoetherianRing Rf Sgf
    let _ : RingHom.IsRegularRingMap (algebraMap Rf Sgf) := by
      exact
        { toFlat := RingHom.flat_algebraMap_iff.mpr inferInstance
          isGeometricallyRegular_fiber := fun p ↦ by
            letI : Algebra.Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber Sgf) := inferInstance
            letI :
                Algebra.IsGeometricallyRegular p.asIdeal.ResidueField p.asIdeal.ResidueField :=
              inferInstance
            infer_instance }
    exact Algebra.isRegularRing_of_regularRingMap Rf
  letI : IsRegularRing Sgf := hSgf_reg
  letI : IsJ0Ring Sgf := isJ0Ring_of_isRegularRing Sgf
  have hinjSgf : Function.Injective (algebraMap Sg Sgf) := IsLocalization.injective Sgf hfSgPowers
  letI : IsNoetherianRing Sg := Algebra.FiniteType.isNoetherianRing R Sg
  letI : IsJ0Ring Sg := isJ0Ring_of_injective_finiteType hinjSgf
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  exact isJ0Ring_of_injective_finiteType hinjSg

end

end Algebra
