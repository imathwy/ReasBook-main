import Mathlib
import StacksProject_2024.Chap10.Lemma_10_118_3
import StacksProject_2024.Chap10.Lemma_10_164_4
import StacksProject_2024.Chap15.Definition_15_47_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

universe u v

open GenericFlatness IsLocalization
open PrimeSpectrum
open scoped PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsDomain R] [IsDomain S] [Algebra.FiniteType R S]

/- Domain-style sampling:
* primary domain: `J-0` descent for finite type maps of domains, organized around the regular locus
  on `Spec`;
* sampled owner and bridge declarations of the same kind:
  `IsJ0Ring`,
  `isJ0Ring_iff_exists_nonempty_open_subset_regularLocus`,
  `exists_nonzero_isRegularRing_localizationAway_of_isJ0Ring`,
  `isRegularRing_of_faithfullyFlat`;
* best owner abstraction: the public statement should stay on the chapter owner `IsJ0Ring`;
  the nonzero principal-localization witness is reused from owner-derived API in
  `Definition_15_47_1`, and regularity descent remains derived bridge data inside the proof;
* primitive vs. derived: the primitive public data are the injective finite type domain map
  `R → S` and the owner hypothesis that `S` is `J-0`. A witness `f ≠ 0` with
  `Localization.Away f` regular belongs to the domain-localization bridge and should not appear as
  parallel public data.

Source/core/bridge triage:
* source-facing: the descent statement for `IsJ0Ring` along an injective finite type map of
  domains;
* core/canonical: the owner `IsJ0Ring`;
* bridge/view: principal localizations `Localization.Away f` and faithful-flat descent of
  `IsRegularRing`.
-/

-- Proof sketch: choose `g : S` with `S[1 / g]` regular from the `J-0` hypothesis on `S`, and
-- replace `S` by this localization. Generic flatness then gives a nonzero `f : R` such that the
-- induced map `R[1 / f] → S[1 / f]` is faithfully flat. Apply faithful-flat descent of regularity
-- to conclude that `R[1 / f]` is regular.
/-- Lemma 15.47.4: for an injective finite type map `R → S` from a Noetherian domain to a domain,
if `S` is `J-0`, then `R` is `J-0`. -/
theorem isJ0Ring_of_injective_finiteType
    (hinj : Function.Injective (algebraMap R S)) [IsJ0Ring S] :
    IsJ0Ring R := by
  obtain ⟨g, hg, hSg_reg⟩ := exists_nonzero_isRegularRing_localizationAway_of_isJ0Ring S
  let Sg := Localization.Away g
  have hgPowers := powers_le_nonZeroDivisors_of_noZeroDivisors hg
  letI : IsRegularRing Sg := hSg_reg
  letI : IsNoetherianRing Sg := IsRegularRing.toIsNoetherian
  letI : IsDomain Sg := isDomain_of_le_nonZeroDivisors Sg hgPowers
  letI : Algebra.FiniteType R Sg :=
    Algebra.FiniteType.trans
      (inferInstance : Algebra.FiniteType R S)
      (inferInstance : Algebra.FiniteType S Sg)
  have hinjSg : Function.Injective (algebraMap R Sg) := by
    intro x y hxy
    exact hinj <| (IsLocalization.injective Sg hgPowers) <| by
      change algebraMap S Sg (algebraMap R S x) = algebraMap S Sg (algebraMap R S y)
      exact hxy
  obtain ⟨f, hf, hcond⟩ :
      ∃ f : R, f ≠ 0 ∧ LocalizationCondition R Sg Sg f :=
    exists_nonzero_localization_away_free_and_finitePresentation_of_finiteType
  let Rf := Localization.Away f
  letI : LocalizationCondition R Sg Sg f := hcond
  have hfSg : algebraMap R Sg f ≠ 0 := by
    intro h0
    apply hf
    exact hinjSg <| by
      rw [map_zero]
      exact h0
  let Sgf := Localization.Away (algebraMap R Sg f)
  letI : Module.Free Rf Sgf := hcond.free_algebra
  have hfSgPowers := powers_le_nonZeroDivisors_of_noZeroDivisors hfSg
  letI : IsDomain Sgf := isDomain_of_le_nonZeroDivisors Sgf hfSgPowers
  have hRf_reg : IsRegularRing Rf := by
    letI : IsRegularRing Sgf :=
      (isRegularRing_localizationAway_iff_basicOpen_subset_regularLocus (algebraMap R Sg f)).2
        fun p _hp ↦ by
          simpa using IsRegularRing.isRegularLocalRing_atPrime p
    have hff : Module.FaithfullyFlat Rf Sgf := by infer_instance
    exact isRegularRing_of_faithfullyFlat
      (algebraMap Rf Sgf)
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hff)
  have hbasic_subset :
      (basicOpen f : Set (PrimeSpectrum R)) ⊆ Reg(Spec R) :=
    (isRegularRing_localizationAway_iff_basicOpen_subset_regularLocus f).1 hRf_reg
  have hbasic_nonempty : (basicOpen f : Set (PrimeSpectrum R)).Nonempty := by
    refine ⟨⟨⊥, inferInstance⟩, ?_⟩
    simpa using (mem_basicOpen f ⟨⊥, inferInstance⟩).2 hf
  exact (isJ0Ring_iff_exists_nonempty_open_subset_regularLocus).2
    ⟨basicOpen f, isOpen_basicOpen, hbasic_nonempty, hbasic_subset⟩

end

end Algebra
