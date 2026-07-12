import Mathlib
import StacksProject_2024.Chap10.Lemma_10_97_6
import StacksProject_2024.Chap10.Lemma_10_157_5
import StacksProject_2024.Chap10.Lemma_10_161_15
import StacksProject_2024.Chap10.Lemma_10_162_3
import StacksProject_2024.Chap10.Lemma_10_162_10
import StacksProject_2024.Chap15.Lemma_15_42_1
import StacksProject_2024.Chap15.Lemma_15_47_6
import StacksProject_2024.Chap15.Lemma_15_50_14
import StacksProject_2024.Chap15.Definition_15_52_1
import StacksProject_2024.Chap15.Proposition_15_48_7

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

/-- Helper for Lemma 15.52.5: a `J-2` domain is automatically `J-0`. -/
lemma isJ0Ring_of_isJ2Ring_domain
    (A : Type u) [CommRing A] [IsDomain A] [IsJ2Ring A] :
    IsJ0Ring A := by
  -- Apply the `J-2` condition to the identity finite type algebra and then use `J-1 → J-0`.
  have hA : IsJ1Ring A := inferInstance
  exact @isJ0Ring_of_isJ1Ring_domain A inferInstance inferInstance hA

/-- Helper for Lemma 15.52.5: a quasi-excellent local domain is `N-1`. -/
lemma local_quasiExcellent_domain_isN1
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsQuasiExcellentRing A] :
    IsN1Ring A := by
  -- The completion map is regular for `G`-rings, so the completion is reduced.
  letI : IsNoetherianRing (AdicCompletion (maximalIdeal A) A) :=
    adicCompletion_isNoetherianRing (maximalIdeal A)
  have hReduced :
      IsReduced (AdicCompletion (maximalIdeal A) A) :=
    Algebra.isReduced_of_regularRingMap (algebraMap A (AdicCompletion (maximalIdeal A) A))
  letI : IsReduced (AdicCompletion (maximalIdeal A) A) := hReduced
  -- Reduced completion is exactly analytic unramifiedness, which implies `N-1`.
  letI : IsAnalyticallyUnramified A := (isAnalyticallyUnramified_iff A).2 inferInstance
  exact isN1Ring_of_isAnalyticallyUnramified A

private theorem finiteType_domain_isN1
    [IsQuasiExcellentRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [IsDomain S] :
    IsN1Ring S := by
  -- TODO: use `isJ0Ring_of_isJ2Ring_domain S` to obtain a normal principal open, then invoke
  -- `local_quasiExcellent_domain_isN1` on each maximal localization of `S`. The remaining blocker
  -- is the localization permanence statement from Lemma `15.52.2 (1)`, whose current dependency
  -- chain through `Proposition 15.50.10` hits the broken files `Lemma_15_51_3` / `Lemma_15_51_4`.
  sorry

-- Proof sketch: by Lemma `15.52.2`, every finite type `R`-algebra is again quasi-excellent. To
-- prove that `R` is Nagata, use Lemma `10.162.3` to reduce to checking that every finite type
-- domain `R`-algebra is `N-1`. For a quasi-excellent domain, Lemma `10.161.15` reduces `N-1` to
-- the local case. For a quasi-excellent local domain, the completion map is regular, so Lemma
-- `15.42.1` shows the completion is reduced, i.e. the ring is analytically unramified; then Lemma
-- `10.162.10` gives the `N-1` property.
/-- Lemma 15.52.5: a quasi-excellent ring is Nagata. -/
instance instNagataRingOfIsQuasiExcellentRing [IsQuasiExcellentRing R] :
    NagataRing R := by
  -- Package the finite-type-domain `N-1` criterion into the universally Japanese owner.
  have hUniversallyJapanese : UniversallyJapaneseRing R := by
    exact
      universallyJapaneseRing_of_finiteType_domain_isN1 R
        (fun S ↦ finiteType_domain_isN1 R S)
  -- Prime quotients are finite type algebras, so the universal Japanese owner supplies `N-2`.
  refine NagataRing.mk ?_
  intro p hp
  letI : p.IsPrime := hp
  letI : Algebra.FiniteType R (R ⧸ p) := RingHom.finiteType_algebraMap.mpr inferInstance
  letI : IsDomain (R ⧸ p) := Ideal.Quotient.isDomain p
  exact hUniversallyJapanese.finiteType_algebra_isN2Ring

end
