import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap12.Remark_12_29_2
import StacksProject_2024.Chap15.Lemma_15_67_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {a b : ℤ}

local notation "DModB" => DerivedCategory (ModuleCat B)

local instance extendScalars_additive_atPrime (q : PrimeSpectrum B) :
    (ModuleCat.extendScalars.{u, u, u}
      (algebraMap B (Localization.AtPrime q.asIdeal))).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
    (algebraMap B (Localization.AtPrime q.asIdeal))).left_adjoint_additive

local instance extendScalars_preservesFiniteLimits_atPrime (q : PrimeSpectrum B) :
    Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u}
        (algebraMap B (Localization.AtPrime q.asIdeal))) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr <|
      IsLocalization.flat (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl)

/- Domain sampling pass:
* primary domain: tor-amplitude in derived categories of module categories under restriction of
  scalars and prime localization;
* sampled owner declarations:
  - `HasTorAmplitudeIn` from `Definition_15_67_1`, the chapter owner for tor-amplitude;
  - `(ModuleCat.extendScalars f).mapDerivedCategory`, the canonical exact derived localization
    functor for flat scalar extension;
  - `(ModuleCat.restrictScalars f).mapDerivedCategory`, the canonical derived restriction functor;
  - `Localization.localRingHom`, the canonical owner for the localized map
    `A_(q ∩ A) → B_q`;
  - `hasTorAmplitudeIn_restrictScalars_of_flat` from `Lemma_15_67_11`, the chapter-local reuse
    point for passing tor-amplitude across flat restriction of scalars.

Source/core/bridge triage:
* `source-facing`: `hasTorAmplitudeIn_over_base_tfae_of_localizations`;
* `core/canonical`: `HasTorAmplitudeIn`, `ModuleCat.extendScalars`,
  `Localization.localRingHom`, and `mapDerivedCategory`;
* `bridge/view`: the localized restricted derived object over the contracted prime, written
  directly from those canonical owners in the prime-local and maximal-local clauses.

Primitive data is only the derived object `K : DModB` together with the canonical localization and
restriction functors. The public theorem below is kept source-facing as a `TFAE`, and its local
clauses are stated directly from those owners, using only theorem-local names to avoid repeating
the same dependent-type expression in every clause.
-/

-- Proof sketch: the implication from the global statement to the prime-local and maximal-local
-- statements comes from exactness of derived localization and restriction of scalars. For the
-- converse, test the homology modules of `K ⊗_A^L M` at maximal ideals of `B`; by the localized
-- hypotheses these stalks vanish outside `[a, b]`, so Lemma `10.23.1` forces the global homology
-- modules to vanish.
/-- Lemma 15.67.15: for a derived `B`-complex `K`, the following are equivalent: `K`, viewed over
`A`, has tor-amplitude in `[a, b]`; for every prime `q` of `B`, the localization `K_q` has
tor-amplitude in `[a, b]` over `A_(q ∩ A)`; and it is enough to check this only at maximal ideals
of `B`. -/
theorem hasTorAmplitudeIn_over_base_tfae_of_localizations (K : DModB) :
    let restrictedK : DerivedCategory (ModuleCat A) :=
      (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K
    let localizedOverBase :
        (q : PrimeSpectrum B) →
          DerivedCategory (ModuleCat (Localization.AtPrime (q.asIdeal.under A))) :=
      fun q ↦
        (ModuleCat.restrictScalars
            (Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl)).mapDerivedCategory.obj
          ((ModuleCat.extendScalars
              (algebraMap B (Localization.AtPrime q.asIdeal))).mapDerivedCategory.obj K)
    List.TFAE [
      HasTorAmplitudeIn restrictedK a b,
      ∀ q : PrimeSpectrum B, HasTorAmplitudeIn (localizedOverBase q) a b,
      ∀ m : MaximalSpectrum B,
        HasTorAmplitudeIn (localizedOverBase m.toPrimeSpectrum) a b
    ] := by
  sorry

end

end CategoryTheory
