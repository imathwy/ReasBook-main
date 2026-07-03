import Mathlib
import stacks_project.Chap10.Lemma_10_97_6
import stacks_project.Chap10.Lemma_10_157_5
import stacks_project.Chap10.Lemma_10_161_15
import stacks_project.Chap10.Lemma_10_162_3
import stacks_project.Chap10.Lemma_10_162_10
import stacks_project.Chap15.Lemma_15_42_1
import stacks_project.Chap15.Lemma_15_47_6
import stacks_project.Chap15.Lemma_15_50_14
import stacks_project.Chap15.Definition_15_52_1
import stacks_project.Chap15.Lemma_15_52_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Algebra
open IsLocalRing

section

variable (R : Type u) [CommRing R]

/- Domain-style sampling:
- primary domain: quasi-excellent rings, Nagata rings, and the `N-1`/`N-2` bridge in
  commutative algebra;
- sampled owner declarations:
  `IsQuasiExcellentRing`,
  `NagataRing`,
  `universallyJapaneseRing_of_finiteType_domain_isN1`,
  `isQuasiExcellentRing_localization_of_finiteType`;
- best owner abstraction: `IsQuasiExcellentRing` remains the source-facing owner and
  `NagataRing` remains the downstream canonical owner; this file should therefore build the
  target instance directly from the existing `N-1` criterion and localization permanence rather
  than introducing any parallel local wrapper.

Source/core/bridge triage:
- `source-facing`: the statement that a quasi-excellent ring is Nagata;
- `core/canonical`: `IsQuasiExcellentRing`, `NagataRing`, `IsN1Ring`, and
  `UniversallyJapaneseRing`;
- `bridge/view`: the private helper below, which turns a finite type domain algebra over a
  quasi-excellent ring into the `IsN1Ring` input required by
  `universallyJapaneseRing_of_finiteType_domain_isN1`.

Primitive data vs. derived API:
- primitive public data are only `[IsQuasiExcellentRing R]`;
- the `J-0` witness, the local analytic-unramified argument, and the induced
  `UniversallyJapaneseRing` structure are derived proof data and stay internal.
-/

private theorem finiteType_domain_isN1
    [IsQuasiExcellentRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [IsDomain S] :
    IsN1Ring S := by
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  letI : IsJ2Ring.{u, u} S :=
    { isJ1Ring_of_finiteType := by
        intro (A : Type u) _ _ _
        letI : Algebra R A := ((algebraMap S A).comp (algebraMap R S)).toAlgebra
        letI : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq' rfl
        letI : Algebra.FiniteType R A := Algebra.FiniteType.trans
          (inferInstance : Algebra.FiniteType R S) (inferInstance : Algebra.FiniteType S A)
        exact inferInstance }
  have hTFAE :
      List.TFAE
        [ IsJ2Ring.{u, u} S,
          ∀ (A : Type u) [CommRing A] [Algebra S A] [Algebra.FiniteType S A] [IsDomain A],
            IsJ0Ring A,
          ∀ (A : Type u) [CommRing A] [Algebra S A] [Module.Finite S A],
            IsJ1Ring A,
          ∀ (p : Ideal S) [p.IsPrime] (L : Type u) [Field L] [Algebra p.ResidueField L]
            [FiniteDimensional p.ResidueField L] [IsPurelyInseparable p.ResidueField L],
            let _ : Algebra S L :=
              RingHom.toAlgebra
                ((algebraMap p.ResidueField L).comp (algebraMap S p.ResidueField))
            let _ : IsScalarTower S p.ResidueField L := IsScalarTower.of_algebraMap_eq' rfl
            ∃ (A : Type u) (_ : CommRing A) (_ : Algebra S A) (_ : Module.Finite S A)
              (_ : IsDomain A) (_ : Algebra A L) (_ : IsScalarTower S A L)
              (_ : IsFractionRing A L),
              IsJ0Ring A
        ] :=
    isJ2Ring_tfae_finiteType_domain_isJ0_finite_algebra_isJ1_purelyInseparable_residueField_extension
  have hJ0_all :
      ∀ (A : Type u) [CommRing A] [Algebra S A] [Algebra.FiniteType S A] [IsDomain A],
        IsJ0Ring A := by
    have hJ2 : IsJ2Ring.{u, u} S := inferInstance
    exact (hTFAE.out 0 1).1 hJ2
  letI : IsJ0Ring S := hJ0_all S
  have hnormalAway :
      ∃ f : S, f ≠ 0 ∧ IsNormalRing (Localization.Away f) := by
    obtain ⟨f, hf, hreg⟩ := exists_nonzero_isRegularRing_localizationAway_of_isJ0Ring S
    letI : IsRegularRing (Localization.Away f) := hreg
    exact ⟨f, hf, isNormalRing_of_isRegularRing⟩
  have hlocal : ∀ m : MaximalSpectrum S, IsN1Ring (Localization.AtPrime m.asIdeal) := by
    intro m
    let A : Type u := Localization.AtPrime m.asIdeal
    letI : IsQuasiExcellentRing.{u, u} A :=
      isQuasiExcellentRing_localization_of_finiteType R m.asIdeal.primeCompl
    letI : IsNoetherianRing (AdicCompletion (maximalIdeal A) A) :=
      adicCompletion_isNoetherianRing (maximalIdeal A)
    letI : IsReduced (AdicCompletion (maximalIdeal A) A) :=
      Algebra.isReduced_of_regularRingMap (algebraMap A (AdicCompletion (maximalIdeal A) A))
    letI : IsAnalyticallyUnramified A := (isAnalyticallyUnramified_iff A).2 inferInstance
    exact isN1Ring_of_isAnalyticallyUnramified A
  exact
    isN1Ring_of_exists_isNormalRing_localizationAway_of_forall_maximal_isN1Ring_localizationAtMaximal
      hnormalAway hlocal

-- Proof sketch: by Lemma `15.52.2`, every finite type `R`-algebra is again quasi-excellent. To
-- prove that `R` is Nagata, use Lemma `10.162.3` to reduce to checking that every finite type
-- domain `R`-algebra is `N-1`. For a quasi-excellent domain, Lemma `10.161.15` reduces `N-1` to
-- the local case. For a quasi-excellent local domain, the completion map is regular, so Lemma
-- `15.42.1` shows the completion is reduced, i.e. the ring is analytically unramified; then Lemma
-- `10.162.10` gives the `N-1` property.
/-- Lemma 15.52.5: a quasi-excellent ring is Nagata. -/
instance instNagataRingOfIsQuasiExcellentRing [IsQuasiExcellentRing R] :
    NagataRing R := by
  have hUniversallyJapanese : UniversallyJapaneseRing R := by
    exact
      universallyJapaneseRing_of_finiteType_domain_isN1 R
        (fun S ↦ finiteType_domain_isN1 R S)
  refine NagataRing.mk ?_
  intro p hp
  letI : p.IsPrime := hp
  letI : Algebra.FiniteType R (R ⧸ p) := RingHom.finiteType_algebraMap.mpr inferInstance
  letI : UniversallyJapaneseRing R := hUniversallyJapanese
  exact inferInstance

end
