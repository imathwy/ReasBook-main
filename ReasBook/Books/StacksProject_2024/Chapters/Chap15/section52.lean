import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_52_1 (from Chap15) -/
universe u v

section

variable (R : Type u) [CommRing R]

/-
Domain-style sampling in the commutative-algebra excellence API:
- source-facing owners introduced here: `IsQuasiExcellentRing`, `IsExcellentRing`
- sampled project owners of the same kind:
  - `IsGRing` from `Definition_15_50_1`,
  - `IsJ2Ring` from `Definition_15_47_1`,
  - `UniversallyCatenaryRing` from `Chap10/Definition_10_105_3`,
  - `NagataRing` from `Chap10/Definition_10_162_1` as downstream derived API

Layer triage:
- `source-facing`: the textbook notions of quasi-excellent and excellent rings
- `core/canonical`: the existing owner predicates `IsGRing`, `IsJ2Ring`, and
  `UniversallyCatenaryRing`
- `bridge/view`: downstream consequences such as the Nagata-property instance belong in later
  files, not as primitive fields here

Primitive data vs derived API:
- primitive data for quasi-excellence are exactly the already-canonical owners `IsGRing` and
  `IsJ2Ring`;
- primitive data for excellence are exactly quasi-excellence together with
  `UniversallyCatenaryRing`;
- derived API should come from inherited instances, so this file should not introduce wrapper
  aliases or extra fields restating those owners.
-/

/-- Definition 15.52.1 (1): a ring `R` is quasi-excellent if it is Noetherian, a `G`-ring, and
`J-2`. -/
class IsQuasiExcellentRing : Prop extends IsGRing R, IsJ2Ring.{u, v} R

/-- Definition 15.52.1 (2): a ring `R` is excellent if it is quasi-excellent and universally
catenary. -/
class IsExcellentRing : Prop extends IsQuasiExcellentRing.{u, v} R, UniversallyCatenaryRing.{u, v} R

end

/-! ### Lemma_15_52_2 (from Chap15) -/
universe u v w

section

variable (R : Type u) [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

private theorem finiteType_isJ2Ring [IsJ2Ring R] :
    IsJ2Ring S :=
  (isJ2Ring_of_finiteType R : IsJ2Ring S)

private theorem essFiniteType_universallyCatenaryRing {T : Type w} [CommRing T] [Algebra R T]
    [UniversallyCatenaryRing R] [Algebra.EssFiniteType R T] :
    UniversallyCatenaryRing T :=
  (universallyCatenaryRing_of_essFiniteType R : UniversallyCatenaryRing T)

/- Domain-style sampling:
- primary domain: commutative algebra of quasi-excellent and excellent rings under localization of
  finite type algebras;
- sampled owner declarations:
  `IsQuasiExcellentRing`,
  `IsExcellentRing`,
  `IsGRing`,
  `IsJ2Ring`,
  `isJ2Ring_of_finiteType`,
  `universallyCatenaryRing_of_essFiniteType`;
- best owner abstraction: the source-facing statements here should remain about quasi-excellent and
  excellent rings for an arbitrary localization target `T` with `[IsLocalization M T]`, while
  their proof data is derived from the upstream owner chain
  `IsGRing`/`IsJ2Ring`/`UniversallyCatenaryRing` together with the canonical essential-finite-type
  localization bridge `Algebra.EssFiniteType.of_isLocalization`;
- primitive data: the finite type `R`-algebra `S`, the localization submonoid `M`, and the source
  owner assumptions `[IsQuasiExcellentRing R]` or `[IsExcellentRing R]`, plus the owner witness
  `[IsLocalization M T]`;
- derived API: the localized owners `IsQuasiExcellentRing T` and `IsExcellentRing T`; the
  concrete ring `Localization M` is only the canonical specialization.

Source/core/bridge triage:
- `source-facing`: the two localization permanence statements below;
- `core/canonical`: `IsQuasiExcellentRing`, `IsExcellentRing`, and their component owners;
- `bridge/view`: `Algebra.EssFiniteType.of_isLocalization` and
  `universallyCatenaryRing_of_essFiniteType`.
-/

-- Proof sketch: an arbitrary localization target `T` of `S` is essentially of finite type over
-- `R`, so Proposition `15.50.10` gives the `G`-ring condition. The finite type `R`-algebra `S`
-- is `J-2` by Proposition `15.48.7`, and `J-2` is preserved by localization. Combining these
-- two stability statements yields quasi-excellence of `T`.
/-- Lemma 15.52.2 (1): if `R` is quasi-excellent and `S` is a finite type `R`-algebra, then any
localization `T` of `S` is quasi-excellent. The textbook ring `Localization M` is the canonical
special case. -/
theorem isQuasiExcellentRing_localization_of_finiteType
    (M : Submonoid S) {T : Type w} [CommRing T] [Algebra S T] [IsLocalization M T]
    [IsQuasiExcellentRing R] :
    IsQuasiExcellentRing T := by
  letI : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.EssFiniteType S T := .of_isLocalization T M
  letI : Algebra.EssFiniteType R T := .comp R S T
  letI : IsGRing T := by
    sorry
  letI : IsJ2Ring S := finiteType_isJ2Ring R
  letI : IsJ2Ring T := inferInstance
  exact IsQuasiExcellentRing.mk

-- Proof sketch: apply part `(1)` to get that the localization target `T` is quasi-excellent.
-- Since `T` is essentially of finite type over `R`, Lemma `10.105.5` gives that it is
-- universally catenary. These two facts are exactly the data of excellence.
/-- Lemma 15.52.2 (2): if `R` is excellent and `S` is a finite type `R`-algebra, then any
localization `T` of `S` is excellent. The textbook ring `Localization M` is the canonical
special case. -/
theorem isExcellentRing_localization_of_finiteType
    (M : Submonoid S) {T : Type w} [CommRing T] [Algebra S T] [IsLocalization M T]
    [IsExcellentRing R] :
    IsExcellentRing T := by
  letI : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.EssFiniteType S T := .of_isLocalization T M
  letI : Algebra.EssFiniteType R T := .comp R S T
  letI : IsQuasiExcellentRing T :=
    (isQuasiExcellentRing_localization_of_finiteType R M : IsQuasiExcellentRing T)
  let hUC : UniversallyCatenaryRing T := essFiniteType_universallyCatenaryRing R
  letI : UniversallyCatenaryRing T := hUC
  exact IsExcellentRing.mk hUC.catenary_of_finiteType

end

/-! ### Proposition_15_52_3 (from Chap15) -/
universe u v

/- Domain-style sampling:
- primary domain: excellence in commutative algebra, owned by the chapter class
  `IsExcellentRing`.
- sampled owner declarations of the same kind:
  `IsExcellentRing`,
  `IsQuasiExcellentRing`,
  `isGRing_of_finiteType`,
  `isJ2Ring_of_finiteType`,
  `universallyCatenaryRing_of_cohenMacaulayRing`,
  `universallyCatenaryRing_of_isCompleteLocalRing`,
  `universallyCatenaryRing_of_essFiniteType`.
- best owner abstraction: `IsExcellentRing`.
- primitive data vs. derived API:
  the primitive data for excellence are exactly the upstream owner components
  `IsGRing`, `IsJ2Ring`, and `UniversallyCatenaryRing`;
  the field, complete-local, Dedekind, and finite-type clauses below should therefore build
  `IsExcellentRing` directly from those owners, while the special case `ℤ` should be recorded by
  direct recall instead of a parallel wrapper instance.

Source/core/bridge triage:
- `source-facing`: the concrete excellence sources listed in Proposition `15.52.3`;
- `core/canonical`: the owner classes `IsExcellentRing`, `IsQuasiExcellentRing`,
  `IsGRing`, `IsJ2Ring`, and `UniversallyCatenaryRing`;
- `bridge/view`: the regular/Cohen-Macaulay-to-universal-catenarity bridge, the complete-local
  universal-catenarity theorem, and the finite-type permanence theorems for the component owners.
-/

section

variable (K : Type u) [Field K]

-- Proof sketch: Proposition `15.50.12` shows that a field is a `G`-ring, and
-- Proposition `15.48.7` shows that it is `J-2`. Fields are universally catenary because fields
-- are regular, hence Cohen-Macaulay, and Lemma `10.105.9` implies that Noetherian
-- Cohen-Macaulay rings are universally catenary.
/-- Proposition 15.52.3 (1): fields are excellent. -/
instance field_isExcellentRing : IsExcellentRing K := by
  letI : IsQuasiExcellentRing K := IsQuasiExcellentRing.mk
  let hUC : UniversallyCatenaryRing K :=
    universallyCatenaryRing_of_cohenMacaulayRing inferInstance
  letI : UniversallyCatenaryRing K := hUC
  exact IsExcellentRing.mk hUC.catenary_of_finiteType

end

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]

-- Proof sketch: Propositions `15.50.12` and `15.48.7` give the `G`-ring and `J-2` conditions.
-- Remark `10.160.9` supplies universal catenarity via the Cohen structure theorem.
/-- Proposition 15.52.3 (2): Noetherian complete local rings are excellent. -/
instance isExcellentRing_of_noetherian_completeLocalRing : IsExcellentRing R := by
  letI : IsQuasiExcellentRing R := IsQuasiExcellentRing.mk
  let hUC : UniversallyCatenaryRing R := universallyCatenaryRing_of_isCompleteLocalRing R
  letI : UniversallyCatenaryRing R := hUC
  exact IsExcellentRing.mk hUC.catenary_of_finiteType

end

section

variable (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero (FractionRing R)]

-- Proof sketch: Propositions `15.50.12` and `15.48.7` give the `G`-ring and `J-2` conditions.
-- A Dedekind domain is regular, hence Cohen-Macaulay, so Lemma `10.105.9` gives universal
-- catenarity.
/-- Proposition 15.52.3 (4): Dedekind domains with fraction field of characteristic zero are
excellent. -/
instance dedekindDomain_isExcellentRing_of_fractionRing_charZero : IsExcellentRing R := by
  sorry

end

section

/- Proposition 15.52.3 (3): the ring of integers `ℤ` is excellent, by the
Dedekind-domain characteristic-zero instance above. -/
#check (inferInstance : IsExcellentRing ℤ)

end

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: finite type algebras over an excellent ring are `G`-rings by Proposition
-- `15.50.12`, `J-2` by Proposition `15.48.7`, and universally catenary by the essentially finite
-- type stability lemma. Combining these three facts yields excellence.
/-- Proposition 15.52.3 (5): finite type ring extensions of any of the preceding excellent rings
are excellent. -/
theorem isExcellentRing_of_finiteType [IsExcellentRing R] [Algebra.FiniteType R S] :
    IsExcellentRing S := by
  let hG : IsGRing S := isGRing_of_finiteType R
  letI : IsJ2Ring.{u, v} R := inferInstance
  let hJ2 : IsJ2Ring S := isJ2Ring_of_finiteType R
  let hQE : IsQuasiExcellentRing S := { toIsGRing := hG, toIsJ2Ring := hJ2 }
  letI : Algebra.EssFiniteType R S := inferInstance
  let hUC : UniversallyCatenaryRing S :=
    universallyCatenaryRing_of_essFiniteType R
  exact { toIsQuasiExcellentRing := hQE, catenary_of_finiteType := hUC.catenary_of_finiteType }

end

/-! ### Lemma_15_52_4 (from Chap15) -/
universe u

open IsLocalRing

section

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-
Domain-style sampling:
- primary domain: Noetherian local Nagata rings and geometric reducedness of formal fibers;
- sampled owner declarations:
  `NagataRing`,
  `LocalFormalFibersHaveProperty`,
  `IsAnalyticallyUnramified`,
  `Algebra.IsGeometricallyReducedProperty`;
- best owner abstraction: the source-facing local formal-fiber hypothesis should use the Chapter 15
  owner `LocalFormalFibersHaveProperty`, specialized to the canonical bridge
  `Algebra.IsGeometricallyReducedProperty`, while `NagataRing` remains the source-facing owner on
  the ring side;
- primitive data vs. derived API: the primitive data are the Noetherian local ring `A` and the
  formal-fiber property owner. The expanded quantifier over `q : PrimeSpectrum A` and the explicit
  fiber expression are derived API and should not remain the main public surface.

Source/core/bridge triage:
- `source-facing`: the equivalence between the Nagata condition and geometrically reduced formal
  fibers for a Noetherian local ring;
- `core/canonical`: `NagataRing`, `LocalFormalFibersHaveProperty`, `IsAnalyticallyUnramified`, and
  `Algebra.IsGeometricallyReducedProperty`;
- `bridge/view`: Lemma `10.162.14` supplies the analytic-unramified bridge, while
  `LocalFormalFibersHaveProperty` packages the fiberwise condition.
-/

-- Proof sketch: apply Lemma `10.162.14` to identify the Nagata condition for a Noetherian local
-- ring with analytic unramifiedness of finite local domain extensions. For the forward direction,
-- geometrically reduced formal fibers imply the relevant completions are reduced after passing to
-- fraction fields, hence those local extensions are analytically unramified. For the reverse
-- direction, use the Nagata criterion to show that every finite residue-field extension of every
-- prime formal fiber remains reduced.
/-- Lemma 15.52.4: for a Noetherian local ring `A`, being Nagata is equivalent to having
geometrically reduced formal fibers. -/
theorem nagataRing_iff_geometricallyReduced_formalFibers :
    NagataRing A ↔
      LocalFormalFibersHaveProperty Algebra.IsGeometricallyReducedProperty A := sorry

end

/-! ### Lemma_15_52_5 (from Chap15) -/
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

/-! ### Lemma_15_52_6 (from Chap15) -/
open IsLocalRing
open Algebra

universe u

namespace Algebra

/-- The canonical `FieldAlgebraProperty` bridge for ordinary normality. -/
abbrev IsNormalProperty : FieldAlgebraProperty :=
  fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦ IsNormalRing A

end Algebra

section

/-
Domain-style sampling:
- primary domain: normality of Noetherian local rings, formal fibers, and maximal-ideal
  completion;
- sampled owner declarations:
  `LocalFormalFibersHaveProperty`,
  `IsNormalProperty`,
  `adicCompletion_isNoetherianRing`,
  `maximalIdeal_adicCompletion_algebraMap_faithfullyFlat`,
  `isNormalRing_of_flat_of_fiber`;
- best owner abstraction: the source-facing extra hypothesis is the chapter owner
  `LocalFormalFibersHaveProperty`, while the conclusion is obtained from the canonical ascent
  theorem `isNormalRing_of_flat_of_fiber`;
- primitive data: `IsNormalRing A` and the fiberwise normality hypothesis for the completion map
  `A → A^∧`;
- derived API: the bridge `IsNormalProperty`, reusing the upstream specialization of
  `FieldAlgebraProperty` instead of a file-local alias.

Source/core/bridge triage:
- `source-facing`: the normality statement for the maximal-ideal completion;
- `core/canonical`: `LocalFormalFibersHaveProperty` and `isNormalRing_of_flat_of_fiber`;
- `bridge/view`: `IsNormalProperty`.
-/
variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

-- Proof sketch: the completion map `A → ACompletion` is flat for Noetherian local rings. Apply
-- `isNormalRing_of_flat_of_fiber` to this map, using the normality of `A` and the owner
-- hypothesis `LocalFormalFibersHaveProperty IsNormalProperty A`.
/-- Lemma 15.52.6: if a Noetherian local ring `A` is normal and has normal formal fibers, then its
maximal-ideal completion `AdicCompletion (maximalIdeal A) A` is normal; in particular this
applies when the formal fibers are normal because `A` is excellent or quasi-excellent. -/
theorem isNormalRing_maximalIdeal_adicCompletion_of_normal_formalFibers
    [IsNormalRing A]
    (hformal : LocalFormalFibersHaveProperty IsNormalProperty A) :
    IsNormalRing ACompletion := by
  let _ : IsNoetherianRing ACompletion :=
    adicCompletion_isNoetherianRing (maximalIdeal A)
  let _ : Module.Flat A ACompletion :=
    (maximalIdeal_adicCompletion_algebraMap_faithfullyFlat A).flat
  simpa using isNormalRing_of_flat_of_fiber hformal

end
