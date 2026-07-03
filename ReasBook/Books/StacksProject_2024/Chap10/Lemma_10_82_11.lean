import Mathlib
import StacksProject_2024.Chap10.Definition_10_82_1
import StacksProject_2024.Chap10.Lemma_10_39_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open LocalizedModule TensorProduct
open TensorProduct.AlgebraTensorModule

universe u v w x

namespace LinearMap

noncomputable section

open IsLocalization

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]
variable {M' : Type x} [AddCommGroup M'] [Module S M']
variable [Module R M] [Module R M'] [IsScalarTower R S M] [IsScalarTower R S M']

/-- Helper for Lemma 10.82.11: the localized tensor map of `f ⊗[R] Q` is exactly the tensor map
of the localized morphism `f_q`. -/
lemma localized_rTensor_intertwines_localized_map
    (f : M →ₗ[S] M') (q : PrimeSpectrum S) (Q : Type*) [AddCommGroup Q] [Module R Q] :
    IsLocalizedModule.map q.asIdeal.primeCompl
      (AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M))
      (AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M'))
      (AlgebraTensorModule.rTensor R Q f) =
      AlgebraTensorModule.rTensor R Q (LocalizedModule.map q.asIdeal.primeCompl f) := by
  -- We compare the two maps after precomposing with the canonical localization map on
  -- `M ⊗[R] Q`, where both sides reduce to the same map on pure tensors.
  apply IsLocalizedModule.linearMap_ext q.asIdeal.primeCompl
    (AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M))
    (AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M'))
  rw [IsLocalizedModule.map_comp, ← AlgebraTensorModule.rTensor_comp, AlgebraTensorModule.rTensor_comp]
  ext x
  simp [LocalizedModule.map_mk]

/-- Helper for Lemma 10.82.11: localizing `f ⊗[R] Q` at `q` is injective exactly when the tensor
map of `f_q` with `Q` is injective. -/
lemma localized_rTensor_injective_iff
    (f : M →ₗ[S] M') (q : PrimeSpectrum S) (Q : Type*) [AddCommGroup Q] [Module R Q] :
    Function.Injective (LocalizedModule.map q.asIdeal.primeCompl (AlgebraTensorModule.rTensor R Q f)) ↔
      Function.Injective (AlgebraTensorModule.rTensor R Q (LocalizedModule.map q.asIdeal.primeCompl f)) :=
by
  -- We transfer injectivity from the canonical localized-module model of `M ⊗[R] Q`
  -- to the tensor of the localized map by the explicit intertwining identity above.
  simpa [localized_rTensor_intertwines_localized_map (R := R) (S := S) (M := M) (M' := M')
      (f := f) (q := q) (Q := Q)] using
    (IsLocalizedModule.map_injective_iff_localizedModuleMap_injective
      (S := q.asIdeal.primeCompl)
      (g₁ := AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M))
      (g₂ := AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M'))
      (l := AlgebraTensorModule.rTensor R Q f)).symm

/-- Helper for Lemma 10.82.11: for an `R_(q ∩ R)`-module `Q`, tensoring `M_q` with `Q` over the
localized base ring agrees with tensoring over `R`. -/
noncomputable def localized_rTensor_over_under_equiv
    (q : PrimeSpectrum S) (Q : Type*) [AddCommGroup Q]
    [Module (Localization.AtPrime (q.asIdeal.under R)) Q]
    [Module R Q] [IsScalarTower R (Localization.AtPrime (q.asIdeal.under R)) Q] :
    LocalizedModule.AtPrime q.asIdeal M ⊗[Localization.AtPrime (q.asIdeal.under R)] Q
      ≃ₗ[Localization.AtPrime q.asIdeal]
      LocalizedModule.AtPrime q.asIdeal M ⊗[R] Q := sorry

/-- Helper for Lemma 10.82.11: the over-under tensor equivalence intertwines the tensor maps of
the localized morphism `f_q`. -/
lemma localized_rTensor_over_under_intertwines
    (f : M →ₗ[S] M') (q : PrimeSpectrum S) (Q : Type*) [AddCommGroup Q]
    [Module (Localization.AtPrime (q.asIdeal.under R)) Q]
    [Module R Q] [IsScalarTower R (Localization.AtPrime (q.asIdeal.under R)) Q] :
    (AlgebraTensorModule.rTensor R Q (LocalizedModule.map q.asIdeal.primeCompl f)).comp
        (localized_rTensor_over_under_equiv (R := R) (S := S) (M := M) (q := q) Q).toLinearMap =
      (localized_rTensor_over_under_equiv (R := R) (S := S) (M := M') (q := q) Q).toLinearMap.comp
        (AlgebraTensorModule.rTensor (Localization.AtPrime (q.asIdeal.under R)) Q
          (LocalizedModule.map q.asIdeal.primeCompl f)) := by
  -- TODO: express the source proof identity `M_q ⊗[R] Q = M_q ⊗[R_(q ∩ R)] Q`
  -- through a transport-stable `A_q`-linear equivalence, then rewrite both composites on
  -- pure tensors using the canonical comparison map.
  sorry

/-- Helper for Lemma 10.82.11: if `Q` is already an `R_(q ∩ R)`-module, then injectivity of the
tensor map of `f_q` is the same over `R` and over `R_(q ∩ R)`. -/
lemma localized_rTensor_injective_iff_over_under
    (f : M →ₗ[S] M') (q : PrimeSpectrum S) (Q : Type*) [AddCommGroup Q]
    [Module (Localization.AtPrime (q.asIdeal.under R)) Q]
    [Module R Q] [IsScalarTower R (Localization.AtPrime (q.asIdeal.under R)) Q] :
    Function.Injective (AlgebraTensorModule.rTensor R Q (LocalizedModule.map q.asIdeal.primeCompl f)) ↔
      Function.Injective
        (AlgebraTensorModule.rTensor (Localization.AtPrime (q.asIdeal.under R)) Q
          (LocalizedModule.map q.asIdeal.primeCompl f)) := by
  -- TODO: once `localized_rTensor_over_under_intertwines` is proved via the canonical over/under
  -- equivalence, transfer injectivity across that equivalence in both directions.
  sorry

/-- Helper for Lemma 10.82.11: after localizing the test module `Q` at `q ∩ R`, tensoring `M_q`
over `R_(q ∩ R)` identifies canonically with tensoring over `R`. -/
noncomputable def localized_rTensor_over_under_localizedModule_equiv
    (q : PrimeSpectrum S) (Q : Type*) [AddCommGroup Q] [Module R Q] :
    LocalizedModule.AtPrime q.asIdeal M ⊗[Localization.AtPrime (q.asIdeal.under R)]
        LocalizedModule.AtPrime (q.asIdeal.under R) Q
      ≃ₗ[Localization.AtPrime q.asIdeal]
      LocalizedModule.AtPrime q.asIdeal M ⊗[R] Q := sorry

/-- Helper for Lemma 10.82.11: the localized-module version of the over-under tensor equivalence
also intertwines the tensor maps of `f_q`. -/
lemma localized_rTensor_over_under_localizedModule_intertwines
    (f : M →ₗ[S] M') (q : PrimeSpectrum S) (Q : Type*) [AddCommGroup Q] [Module R Q] :
    (AlgebraTensorModule.rTensor R Q (LocalizedModule.map q.asIdeal.primeCompl f)).comp
        (localized_rTensor_over_under_localizedModule_equiv
          (R := R) (S := S) (M := M) (q := q) Q).toLinearMap =
      (localized_rTensor_over_under_localizedModule_equiv
          (R := R) (S := S) (M := M') (q := q) Q).toLinearMap.comp
        (AlgebraTensorModule.rTensor (Localization.AtPrime (q.asIdeal.under R))
          (LocalizedModule.AtPrime (q.asIdeal.under R) Q)
          (LocalizedModule.map q.asIdeal.primeCompl f)) := by
  -- TODO: factor the comparison through `LocalizedModule.equivTensorProduct` on the test module
  -- and `AlgebraTensorModule.cancelBaseChange`, then verify the two composites on generators.
  sorry

/-- Helper for Lemma 10.82.11: for an `R`-module `Q`, injectivity of the tensor map of `f_q`
against `Q` is equivalent to injectivity of the over-under tensor map against `Q_(q ∩ R)`. -/
lemma localized_rTensor_injective_iff_over_under_localizedModule
    (f : M →ₗ[S] M') (q : PrimeSpectrum S) (Q : Type*) [AddCommGroup Q] [Module R Q] :
    Function.Injective (AlgebraTensorModule.rTensor R Q (LocalizedModule.map q.asIdeal.primeCompl f)) ↔
      Function.Injective
        (AlgebraTensorModule.rTensor (Localization.AtPrime (q.asIdeal.under R))
          (LocalizedModule.AtPrime (q.asIdeal.under R) Q)
          (LocalizedModule.map q.asIdeal.primeCompl f)) := by
  -- TODO: transfer injectivity across `localized_rTensor_over_under_localizedModule_equiv`
  -- after the corresponding intertwining lemma is established.
  sorry

-- Proof sketch: localize the tensor map `M ⊗[R] Q → M' ⊗[R] Q` at primes or maximal ideals of
-- `S`, identify these localizations with the tensor maps of the localized morphisms, and then use
-- exactness of localization together with the local criterion that a module is zero iff all of its
-- maximal localizations are zero.
/-- Lemma 10.82.11: for an `R`-algebra `S` and an `S`-linear map `M → M'`, universal injectivity
over `R` is equivalent to universal injectivity after localizing at every prime or maximal ideal of
`S`, either as a map of `R`-modules or as a map over the local rings `R_(q ∩ R)` and `R_(m ∩ R)`.
-/
theorem universallyInjective_localizedModule_atPrime_over_under_tfae (f : M →ₗ[S] M') :
    letI : Module R M := Module.restrictScalars R S M
    letI : Module R M' := Module.restrictScalars R S M'
    letI : IsScalarTower R S M := IsScalarTower.restrictScalars R S M
    letI : IsScalarTower R S M' := IsScalarTower.restrictScalars R S M'
    List.TFAE [
      UniversallyInjective.{u, w, x, max u v w x} (f.restrictScalars R),
      ∀ q : PrimeSpectrum S,
        UniversallyInjective.{u, max v w, max v x, max u v w x}
          ((LocalizedModule.map q.asIdeal.primeCompl f).restrictScalars R),
      ∀ m : MaximalSpectrum S,
        UniversallyInjective.{u, max v w, max v x, max u v w x}
          ((LocalizedModule.map m.asIdeal.primeCompl f).restrictScalars R),
      ∀ q : PrimeSpectrum S,
        UniversallyInjective.{u, max v w, max v x, max u v w x}
          ((LocalizedModule.map q.asIdeal.primeCompl f).restrictScalars
            (Localization.AtPrime (q.asIdeal.under R))),
      ∀ m : MaximalSpectrum S,
        UniversallyInjective.{u, max v w, max v x, max u v w x}
          ((LocalizedModule.map m.asIdeal.primeCompl f).restrictScalars
            (Localization.AtPrime (m.asIdeal.under R)))
    ] := by
  classical
  letI : Module R M := Module.restrictScalars R S M
  letI : Module R M' := Module.restrictScalars R S M'
  letI : IsScalarTower R S M := IsScalarTower.restrictScalars R S M
  letI : IsScalarTower R S M' := IsScalarTower.restrictScalars R S M'
  -- We use the tensor map `f ⊗[R] Q` as the main controlled object.
  tfae_have 1 → 2 := by
    intro hf q
    unfold UniversallyInjective at hf ⊢
    intro Q _ _
    -- We first tensor the global map with `Q`, then localize the resulting injective map at `q`.
    have hTensor : Function.Injective (AlgebraTensorModule.rTensor R Q f) := by
      simpa [restrictScalars_rTensor] using hf Q inferInstance inferInstance
    have hLocalized :
        Function.Injective (LocalizedModule.map q.asIdeal.primeCompl
          (AlgebraTensorModule.rTensor R Q f)) :=
      LocalizedModule.map_injective q.asIdeal.primeCompl (AlgebraTensorModule.rTensor R Q f) hTensor
    -- The localized tensor map is the same as tensoring the localized morphism.
    simpa [restrictScalars_rTensor] using
      (localized_rTensor_injective_iff (R := R) (S := S) (M := M) (M' := M')
        (f := f) (q := q) (Q := Q)).1 hLocalized
  tfae_have 2 → 3 := by
    intro h m
    -- Maximal ideals are special cases of prime ideals.
    simpa using h m.toPrimeSpectrum
  tfae_have 3 → 1 := by
    intro h
    unfold UniversallyInjective at h ⊢
    intro Q _ _
    -- We test injectivity of `f ⊗[R] Q` at every maximal ideal of `S`.
    have hLocal :
        ∀ (J : Ideal S) [J.IsMaximal],
          Function.Injective (LocalizedModule.map J.primeCompl (AlgebraTensorModule.rTensor R Q f)) := by
      intro J _
      let m : MaximalSpectrum S := ⟨J, inferInstance⟩
      have hm : UniversallyInjective ((LocalizedModule.map J.primeCompl f).restrictScalars R) := by
        simpa using h m
      have hmTensor :
          Function.Injective (AlgebraTensorModule.rTensor R Q (LocalizedModule.map J.primeCompl f)) := by
        simpa [restrictScalars_rTensor] using hm Q inferInstance inferInstance
      -- The maximal localization of `f ⊗[R] Q` is the tensor map of `f_m`.
      simpa using
        (localized_rTensor_injective_iff (R := R) (S := S) (M := M) (M' := M')
          (f := f) (q := m.toPrimeSpectrum) (Q := Q)).2 hmTensor
    simpa [restrictScalars_rTensor] using
      (injective_of_localized_maximal (f := AlgebraTensorModule.rTensor R Q f) hLocal)
  tfae_have 1 → 4 := by
    intro hf q
    unfold UniversallyInjective at hf ⊢
    intro Q _ _
    letI : Module R Q := Module.restrictScalars R (Localization.AtPrime (q.asIdeal.under R)) Q
    letI : IsScalarTower R (Localization.AtPrime (q.asIdeal.under R)) Q :=
      IsScalarTower.restrictScalars R (Localization.AtPrime (q.asIdeal.under R)) Q
    -- First tensor the global map with `Q` viewed as an `R`-module, then localize at `q`.
    have hTensor : Function.Injective (AlgebraTensorModule.rTensor R Q f) := by
      simpa [restrictScalars_rTensor] using hf Q inferInstance inferInstance
    have hLocalized :
        Function.Injective (LocalizedModule.map q.asIdeal.primeCompl
          (AlgebraTensorModule.rTensor R Q f)) :=
      LocalizedModule.map_injective q.asIdeal.primeCompl
        (AlgebraTensorModule.rTensor R Q f) hTensor
    have hTensorLocalized :
        Function.Injective
          (AlgebraTensorModule.rTensor R Q (LocalizedModule.map q.asIdeal.primeCompl f)) := by
      exact (localized_rTensor_injective_iff (R := R) (S := S) (M := M) (M' := M')
        (f := f) (q := q) (Q := Q)).1 hLocalized
    -- The source identity `M_q ⊗[R] Q = M_q ⊗[R_(q ∩ R)] Q` is the remaining bridge.
    simpa [restrictScalars_rTensor] using
      (localized_rTensor_injective_iff_over_under (R := R) (S := S) (M := M) (M' := M')
        (f := f) (q := q) (Q := Q)).1 hTensorLocalized
  tfae_have 4 → 5 := by
    intro h m
    -- Maximal ideals are special cases of prime ideals on the over-under side as well.
    simpa using h m.toPrimeSpectrum
  tfae_have 5 → 1 := by
    -- Route correction: test the maximal-local hypothesis on `Q_(m ∩ R)` and then transport back
    -- via `localized_rTensor_injective_iff_over_under_localizedModule`.
    intro h
    unfold UniversallyInjective at h ⊢
    intro Q _ _
    -- It is enough to test the tensor map after localizing at every maximal ideal of `S`.
    have hLocal :
        ∀ (J : Ideal S) [J.IsMaximal],
          Function.Injective (LocalizedModule.map J.primeCompl (AlgebraTensorModule.rTensor R Q f)) := by
      intro J _
      let m : MaximalSpectrum S := ⟨J, inferInstance⟩
      have hm :
          UniversallyInjective
            ((LocalizedModule.map J.primeCompl f).restrictScalars
              (Localization.AtPrime (J.under R))) := by
        simpa using h m
      have hmTensor :
          Function.Injective
            (AlgebraTensorModule.rTensor (Localization.AtPrime (J.under R))
              (LocalizedModule.AtPrime (J.under R) Q)
              (LocalizedModule.map J.primeCompl f)) := by
        simpa [restrictScalars_rTensor] using
          hm (LocalizedModule.AtPrime (J.under R) Q) inferInstance inferInstance
      have hmTensorR :
          Function.Injective
            (AlgebraTensorModule.rTensor R Q (LocalizedModule.map J.primeCompl f)) := by
        exact
          (localized_rTensor_injective_iff_over_under_localizedModule
            (R := R) (S := S) (M := M) (M' := M')
            (f := f) (q := m.toPrimeSpectrum) (Q := Q)).2 hmTensor
      -- The maximal localization of `f ⊗[R] Q` is again the tensor map of `f_m`.
      simpa using
        (localized_rTensor_injective_iff (R := R) (S := S) (M := M) (M' := M')
          (f := f) (q := m.toPrimeSpectrum) (Q := Q)).2 hmTensorR
    simpa [restrictScalars_rTensor] using
      (injective_of_localized_maximal (f := AlgebraTensorModule.rTensor R Q f) hLocal)
  tfae_finish

end

end

end LinearMap
