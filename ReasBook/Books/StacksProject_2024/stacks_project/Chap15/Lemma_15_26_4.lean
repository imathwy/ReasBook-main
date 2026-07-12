import Mathlib
import StacksProject_2024.Chap10.Lemma_10_70_2
import StacksProject_2024.Chap10.Lemma_10_23_1
import StacksProject_2024.Chap15.Definition_15_26_1
import StacksProject_2024.Chap15.Lemma_15_10_5
import StacksProject_2024.Chap15.Lemma_15_18_3
import StacksProject_2024.Chap15.Lemma_15_26_3
import StacksProject_2024.Chap15.Lemma_15_8_4
import StacksProject_2024.Chap15.Lemma_15_8_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open scoped FittingIdeal
open scoped TensorProduct
open scoped AffineBlowupChart

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-
Domain-style sampling pass for Lemma 15.26.4.

Primary domain: commutative algebra of Fitting ideals, prime localizations, and affine blowup
strict transforms.

Sampled owner declarations:
* `Module.FiniteLocallyFreeOfRank` from `Chap10/Definition_10_78_1.lean`;
* `fittingIdeal_not_le_prime_tfae_residueField_finrank_and_local_generators` from
  `Chap15/Lemma_15_8_7.lean`;
* `finiteLocallyFreeOfRank_tfae_fittingIdeal_conditions` from `Chap15/Lemma_15_8_8.lean`;
* `fittingIdeal_affineBlowupStrictTransform_eq_top` from `Chap15/Lemma_15_26_3.lean`.

Owner abstraction: this item is `source-facing`. The conclusion should use the chapter owner
`Module.FiniteLocallyFreeOfRank` on the strict transform over the affine blowup chart
`R[Fit[R]_(k)(M) / a]`, while the primewise freeness assumption is theorem input data and should be
stated directly rather than packaged as a parallel local proposition.

Primitive data: the intrinsic ideal `Fit[R]_(k)(M)`, a chart element `a` in that ideal, and the
primewise rank-`k` freeness hypothesis for localizations away from the corresponding closed locus.
Derived API: the finite-locally-free-of-rank conclusion for the strict transform on the chart.

Source/core/bridge triage:
* `source-facing`: the strict-transform finite-locally-free statement below;
* `core/canonical`: `Fit[R]_(k)(M)`, `R[Fit[R]_(k)(M) / a]`,
  `affineBlowupStrictTransform`, and `Module.FiniteLocallyFreeOfRank`;
* `bridge/view`: the Fitting-ideal computations from Lemmas `15.8.8` and `15.26.3`, together with
  the prime-local freeness input.
-/

-- Proof sketch: Lemma `15.26.3` gives `Fit_k(M') = R'` for the strict transform `M'`. By Lemma
-- `15.8.8`, it remains to show `Fit_{k-1}(M') = 0`. After inverting `a`, the affine blowup chart
-- `R[Fit_k(M)/a]` becomes `R_a` by Lemma `10.70.2`, the strict transform becomes `M_a`, and
-- Fitting ideals commute with this base change by Lemma `15.8.4`. The hypothesis implies that
-- `M_a` is finite locally free of rank `k`, so Lemma `15.8.8` forces `Fit_{k-1}(M_a) = 0`, hence
-- also `Fit_{k-1}(M') = 0`.
/-- Helper for Lemma 15.26.4: the affine-blowup-chart map to the away localization is injective,
because the chart element `a` is regular on the chart. -/
lemma affineBlowupChartToLocalizationAway_injective (k : ℕ)
    (a : Fit[R]_(k)(M)) :
    Function.Injective (affineBlowupChartToLocalizationAway (Fit[R]_(k)(M)) a) := by
  let A := R[Fit[R]_(k)(M) / a]
  have hregular : IsRegular (algebraMap R A a.1) := by
    -- Lemma `10.70.2` supplies regularity of the distinguished chart element.
    simpa [A] using affineBlowupChart_isRegular (Fit[R]_(k)(M)) a
  have hdenom : Submonoid.powers (algebraMap R A a.1) ≤ nonZeroDivisors A := by
    -- Every power of a regular element is again a nonzerodivisor.
    intro x hx
    rcases hx with ⟨n, rfl⟩
    exact pow_mem hregular.mem_nonZeroDivisors n
  have hinj : Function.Injective (algebraMap A (Localization.Away a.1)) :=
    IsLocalization.injective (Localization.Away a.1) hdenom
  -- The ambient algebra structure on `Localization.Away a.1` is the chart comparison map.
  simpa [A, RingHom.algebraMap_toAlgebra] using hinj

/-- Helper for Lemma 15.26.4: if an ideal of the affine blowup chart maps to zero after inverting
the distinguished chart element, then the ideal was already zero on the chart. -/
lemma ideal_eq_bot_of_affineBlowupChart_map_eq_bot (k : ℕ)
    (a : Fit[R]_(k)(M))
    {J : Ideal R[Fit[R]_(k)(M) / a]}
    (hJ :
      Ideal.map (affineBlowupChartToLocalizationAway (Fit[R]_(k)(M)) a) J = ⊥) :
    J = ⊥ := by
  have hinj :
      Function.Injective (affineBlowupChartToLocalizationAway (Fit[R]_(k)(M)) a) :=
    affineBlowupChartToLocalizationAway_injective (R := R) (M := M) k a
  have hle :
      J ≤ RingHom.ker (affineBlowupChartToLocalizationAway (Fit[R]_(k)(M)) a) :=
    (Ideal.map_eq_bot_iff_le_ker _).mp hJ
  have hker :
      RingHom.ker (affineBlowupChartToLocalizationAway (Fit[R]_(k)(M)) a) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hinj
  -- Injectivity identifies the kernel with `⊥`, so the ideal itself must vanish.
  exact le_antisymm (by simpa [hker] using hle) bot_le

/-- Helper for Lemma 15.26.4: an ideal is zero once all of its prime localizations are zero. -/
lemma ideal_eq_bot_of_localizedAtPrime_map_eq_bot
    {A : Type*} [CommRing A]
    (J : Ideal A)
    (hJ : ∀ q : PrimeSpectrum A,
      Ideal.map (algebraMap A (Localization.AtPrime q.asIdeal)) J = ⊥) :
    J = ⊥ := by
  ext x
  constructor
  · intro hx
    have hx_local :
        ∀ (P : Ideal A) [P.IsPrime],
          LocalizedModule.mkLinearMap P.primeCompl A x = 0 := by
      intro P hP
      let q : PrimeSpectrum A := ⟨P, hP⟩
      have hx_map :
          algebraMap A (Localization.AtPrime P) x ∈
            Ideal.map (algebraMap A (Localization.AtPrime P)) J :=
        Ideal.mem_map_of_mem _ hx
      simpa [q, hJ q] using hx_map
    -- The standard local-to-global criterion detects vanishing of ring elements from all prime
    -- localizations.
    exact
      ((element_zero_localization_tfae (R := A) (M := A) x).out 1 0).mp
        hx_local
  · intro hx
    have hx_zero : x = 0 := by
      simpa using hx
    simpa [hx_zero] using J.zero_mem

/-- Helper for Lemma 15.26.4: localizing the finite free module `A^k` away from `f` is just
coordinatewise localization. -/
private noncomputable def localized_free_module_equiv_coords_over_base
    {A : Type*} [CommRing A] {k : ℕ} (f : A) :
    LocalizedModule.Away f (Fin k → A) ≃ₗ[A] (Fin k → Localization.Away f) :=
  IsLocalizedModule.linearEquiv (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin k → A))
    (LinearMap.pi fun i : Fin k ↦
      (Algebra.linearMap A (Localization.Away f)).comp (LinearMap.proj i))

/-- Helper for Lemma 15.26.4: the previous free-module localization equivalence is already linear
over the away ring `A_f`. -/
private noncomputable def localized_free_module_equiv_coords
    {A : Type*} [CommRing A] {k : ℕ} (f : A) :
    LocalizedModule.Away f (Fin k → A) ≃ₗ[Localization.Away f] (Fin k → Localization.Away f) :=
  LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f)
    (localized_free_module_equiv_coords_over_base (A := A) (k := k) f)

/-- Helper for Lemma 15.26.4: the free module `A^k` is finite locally free of rank `k`. -/
lemma fin_pi_finiteLocallyFreeOfRank
    {A : Type*} [CommRing A] (k : ℕ) :
    Module.FiniteLocallyFreeOfRank A (Fin k → A) k := by
  refine ⟨Set.univ, ?_, ?_⟩
  · -- The basic opens indexed by all elements certainly cover `Spec A`.
    rw [Ideal.eq_top_iff_one]
    exact Ideal.subset_span (by simp)
  · intro f hf
    -- On every basic open, the localized free module stays the standard free rank-`k` module.
    exact ⟨localized_free_module_equiv_coords (A := A) (k := k) f⟩

/-- Helper for Lemma 15.26.4: the preceding Fitting ideal of the free module `A^k` vanishes. -/
lemma precedingFittingIdeal_fin_pi_eq_bot
    {A : Type*} [CommRing A] (k : ℕ) :
    precedingFittingIdeal A (Fin k → A) k = ⊥ := by
  letI : Module.FiniteLocallyFreeOfRank A (Fin k → A) k :=
    fin_pi_finiteLocallyFreeOfRank (A := A) k
  -- Lemma `15.8.8` turns the finite-locally-free rank statement into the Fitting equalities.
  have hconditions :
      precedingFittingIdeal A (Fin k → A) k = ⊥ ∧
        Fit[A]_(k)(Fin k → A) = ⊤ := by
    exact
      ((finiteLocallyFreeOfRank_tfae_fittingIdeal_conditions
        (R := A) (M := Fin k → A) k).out 0 1).mp
        (show Module.FiniteLocallyFreeOfRank A (Fin k → A) k from inferInstance)
  exact hconditions.1

/-- Helper for Lemma 15.26.4: any finite module that is linearly equivalent to the free module
`A^k` has vanishing preceding Fitting ideal. -/
lemma precedingFittingIdeal_eq_bot_of_linearEquiv_fin_pi
    {A : Type*} [CommRing A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (k : ℕ) (e : N ≃ₗ[A] (Fin k → A)) :
    precedingFittingIdeal A N k = ⊥ := by
  cases k with
  | zero =>
      -- In rank `0`, the preceding Fitting ideal is definitionally `⊥`.
      simp
  | succ r =>
      -- For positive rank, transport the previous Fitting ideal across the linear equivalence.
      calc
        precedingFittingIdeal A N (r + 1) = Fit[A]_(r)(N) := by
          simp
        _ = Fit[A]_(r)(Fin (r + 1) → A) := by
          simpa using
            (fittingIdeal_eq_of_linearEquiv
              (R := A)
              (M := N)
              (M' := Fin (r + 1) → A)
              (k := r)
              e)
        _ = precedingFittingIdeal A (Fin (r + 1) → A) (r + 1) := by
          simp
        _ = ⊥ := precedingFittingIdeal_fin_pi_eq_bot (A := A) (r + 1)

/-- Helper for Lemma 15.26.4: once the strict transform has top `k`th Fitting ideal and its
preceding Fitting ideal vanishes after inverting `a`, Lemma `15.8.8` upgrades those Fitting
conditions to finite local freeness of rank `k`. -/
lemma strictTransform_finiteLocallyFreeOfRank_of_fitting_conditions (k : ℕ)
    (a : Fit[R]_(k)(M))
    (hfitTop :
      let A := R[Fit[R]_(k)(M) / a]
      let M' := affineBlowupStrictTransform (Fit[R]_(k)(M)) a M
      Fit[A]_(k)(M') = ⊤)
    (hprevMapBot :
      let A := R[Fit[R]_(k)(M) / a]
      let M' := affineBlowupStrictTransform (Fit[R]_(k)(M)) a M
      Ideal.map
          (affineBlowupChartToLocalizationAway (Fit[R]_(k)(M)) a)
          (precedingFittingIdeal A M' k) = ⊥) :
    Module.FiniteLocallyFreeOfRank
      R[Fit[R]_(k)(M) / a] (affineBlowupStrictTransform (Fit[R]_(k)(M)) a M) k := by
  let A := R[Fit[R]_(k)(M) / a]
  let M' := affineBlowupStrictTransform (Fit[R]_(k)(M)) a M
  let T := TensorProduct R A M
  let J : Ideal A := principalIdeal (algebraMap R A a.1)
  have hfitTop' : Fit[A]_(k)(M') = ⊤ := by
    -- Re-express the top Fitting-ideal hypothesis in the local owner notation used below.
    simpa [A, M'] using hfitTop
  have hprevMapBot' :
      Ideal.map
          (affineBlowupChartToLocalizationAway (Fit[R]_(k)(M)) a)
          (precedingFittingIdeal A M' k) = ⊥ := by
    -- Re-express the preceding Fitting-ideal hypothesis in the same local notation.
    simpa [A, M'] using hprevMapBot
  letI : Module.Finite A T := Module.Finite.base_change (R := R) (A := A) (M := M)
  letI : Module.Finite A M' := by
    -- The strict transform is a quotient of the finite base-changed module `A ⊗[R] M`.
    change Module.Finite A (T ⧸ J.primaryComponent T)
    infer_instance
  have hprevBot : precedingFittingIdeal A M' k = ⊥ := by
    -- Descend the vanishing of the preceding Fitting ideal from the injective away localization.
    exact ideal_eq_bot_of_affineBlowupChart_map_eq_bot (R := R) (M := M) k a hprevMapBot'
  -- Lemma `15.8.8` is the textbook bridge from the two Fitting-ideal equalities to rank-`k`
  -- local freeness.
  exact
    ((finiteLocallyFreeOfRank_tfae_fittingIdeal_conditions (R := A) (M := M') k).out 1 0).mp
      (show precedingFittingIdeal A M' k = ⊥ ∧ Fit[A]_(k)(M') = ⊤ from
        ⟨hprevBot, hfitTop'⟩)

/-- Helper for Lemma 15.26.4: if the preceding Fitting ideal of `M_a` vanishes after localizing at
every prime of `Spec(R_a)`, then it already vanishes over the away ring `R_a` itself. -/
lemma away_precedingFittingIdeal_eq_bot (k : ℕ)
    (a : Fit[R]_(k)(M))
    (hlocal :
      ∀ qAway : PrimeSpectrum (Localization.Away a.1),
        Ideal.map
            (algebraMap (Localization.Away a.1) (Localization.AtPrime qAway.asIdeal))
            (precedingFittingIdeal (Localization.Away a.1)
              (LocalizedModule.Away a.1 M) k) = ⊥) :
    precedingFittingIdeal (Localization.Away a.1)
      (LocalizedModule.Away a.1 M) k = ⊥ := by
  -- The general local-to-global criterion from prime localizations applies directly on `R_a`.
  exact
    ideal_eq_bot_of_localizedAtPrime_map_eq_bot
      (A := Localization.Away a.1)
      (precedingFittingIdeal (Localization.Away a.1)
        (LocalizedModule.Away a.1 M) k)
      hlocal

/-- Helper for Lemma 15.26.4: at every prime `p` away from `Fit_k(M)`, the localized module `M_p`
has vanishing preceding Fitting ideal because it is free of rank `k` there. -/
lemma precedingFittingIdeal_atPrime_eq_bot_of_not_le (k : ℕ)
    (hM :
      ∀ (p : Ideal R) [p.IsPrime] (_ : ¬ Fit[R]_(k)(M) ≤ p),
        Nonempty
          ((LocalizedModule.AtPrime p M) ≃ₗ[Localization.AtPrime p]
            (Fin k → Localization.AtPrime p))) :
    ∀ (p : Ideal R) [p.IsPrime], ¬ Fit[R]_(k)(M) ≤ p →
      precedingFittingIdeal (Localization.AtPrime p)
        (LocalizedModule.AtPrime p M) k = ⊥ := by
  intro p hp hpk
  rcases hM p hpk with ⟨e⟩
  -- Transport the preceding Fitting ideal across the chosen free-rank-`k` trivialization.
  exact
    precedingFittingIdeal_eq_bot_of_linearEquiv_fin_pi
      (A := Localization.AtPrime p)
      (N := LocalizedModule.AtPrime p M)
      k
      e

/-- Helper for Lemma 15.26.4: after tensoring with `R_a`, the `a`-power torsion submodule
defining the strict transform disappears. -/
lemma strict_transform_tensor_primaryComponent_range_eq_bot (k : ℕ)
    (a : Fit[R]_(k)(M)) :
    let A := R[Fit[R]_(k)(M) / a]
    let S := Localization.Away a.1
    let T := A ⊗[R] M
    let J : Ideal A := principalIdeal (algebraMap R A a.1)
    LinearMap.range
        (TensorProduct.map
          (LinearMap.id : S →ₗ[A] S)
          (J.primaryComponent T).subtype) = ⊥ := by
  -- TODO for Lemma 15.26.4: prove that every simple tensor from the primary component is zero
  -- after tensoring with `R_a`, by using `Ideal.primaryComponent_mem` to obtain a power of `a`
  -- killing the numerator and then the fact that `a` becomes a unit in the away localization.
  sorry

/-- Helper for Lemma 15.26.4: after inverting `a`, tensoring the strict transform with `R_a`
recovers the away localization `M_a`. -/
noncomputable def strict_transform_away_linearEquiv (k : ℕ)
    (a : Fit[R]_(k)(M)) :
    let A := R[Fit[R]_(k)(M) / a]
    let S := Localization.Away a.1
    let T := A ⊗[R] M
    let J : Ideal A := principalIdeal (algebraMap R A a.1)
    let M' := affineBlowupStrictTransform (Fit[R]_(k)(M)) a M
    TensorProduct A S M' ≃ₗ[S] LocalizedModule.Away a.1 M :=
  -- TODO for Lemma 15.26.4: combine the quotient-to-tensor comparison for the strict transform
  -- with the previous torsion-killing lemma and `TensorProduct.AlgebraTensorModule.cancelBaseChange`
  -- to realize the source identity `(M')_a = M_a`.
  sorry

/-- Helper for Lemma 15.26.4: every prime localization of the preceding Fitting ideal of `M_a`
vanishes because the contracted prime of `R` still lies away from `Fit_k(M)`. -/
lemma localized_precedingFittingIdeal_away_map_eq_bot (k : ℕ)
    (a : Fit[R]_(k)(M))
    (hM :
      ∀ (p : Ideal R) [p.IsPrime] (_ : ¬ Fit[R]_(k)(M) ≤ p),
        Nonempty
          ((LocalizedModule.AtPrime p M) ≃ₗ[Localization.AtPrime p]
            (Fin k → Localization.AtPrime p))) :
    ∀ qAway : PrimeSpectrum (Localization.Away a.1),
      Ideal.map
          (algebraMap (Localization.Away a.1) (Localization.AtPrime qAway.asIdeal))
          (precedingFittingIdeal (Localization.Away a.1)
            (LocalizedModule.Away a.1 M) k) = ⊥ := by
  -- TODO for Lemma 15.26.4: after the structural equivalence `(M')_a ≃ M_a`, the remaining
  -- source-faithful blocker is to transport prime-local vanishing from
  -- `LocalizedModule.AtPrime p M` to the iterated localization
  -- `LocalizedModule.AtPrime qAway (LocalizedModule.Away a.1 M)` with the correct target-ring
  -- identification, then apply `fittingIdeal_baseChange` in that transported ring.
  sorry

/-- Helper for Lemma 15.26.4: base change along the chart map rewrites the preceding Fitting ideal
of the strict transform to the corresponding ideal of the away-localized strict transform. -/
lemma chart_precedingFittingIdeal_baseChange_eq (r : ℕ)
    (a : Fit[R]_(r + 1)(M)) :
    let A := R[Fit[R]_(r + 1)(M) / a]
    let S := Localization.Away a.1
    let M' := affineBlowupStrictTransform (Fit[R]_(r + 1)(M)) a M
    Ideal.map
        (affineBlowupChartToLocalizationAway (Fit[R]_(r + 1)(M)) a)
        (precedingFittingIdeal A M' (r + 1)) =
      precedingFittingIdeal S (TensorProduct A S M') (r + 1) := by
  -- TODO for Lemma 15.26.4: this is the final base-change rewrite
  -- `Ideal.map ... (Fit_r M') = Fit_r(S ⊗[A] M')`. The statement is mathematically correct; the
  -- remaining work is to align the chart map with the ambient algebra map used by
  -- `fittingIdeal_baseChange`.
  sorry

/-- Helper for Lemma 15.26.4: after identifying the away localization of the strict transform with
`M_a`, the mapped preceding Fitting ideal on the affine blowup chart vanishes. -/
lemma precedingFittingIdeal_map_eq_bot_on_chart_away (k : ℕ)
    (a : Fit[R]_(k)(M))
    (hM :
      ∀ (p : Ideal R) [p.IsPrime] (_ : ¬ Fit[R]_(k)(M) ≤ p),
        Nonempty
          ((LocalizedModule.AtPrime p M) ≃ₗ[Localization.AtPrime p]
            (Fin k → Localization.AtPrime p))) :
    let A := R[Fit[R]_(k)(M) / a]
    let M' := affineBlowupStrictTransform (Fit[R]_(k)(M)) a M
    Ideal.map
        (affineBlowupChartToLocalizationAway (Fit[R]_(k)(M)) a)
        (precedingFittingIdeal A M' k) = ⊥ := by
  -- TODO for Lemma 15.26.4: combine `chart_precedingFittingIdeal_baseChange_eq`,
  -- `strict_transform_away_linearEquiv`, and `away_precedingFittingIdeal_eq_bot` fed by
  -- `localized_precedingFittingIdeal_away_map_eq_bot`.
  sorry

/-- Lemma 15.26.4: let `I = Fit_k(M)`. If every localization `M_p` with `p ∉ V(I)` is free of
rank `k`, then for every `a ∈ I`, with `R' = R[I/a]`, the strict transform
`M' = (M ⊗[R] R')/(a`-power torsion)` is finite locally free of rank `k`. -/
theorem fittingIdealAffineBlowupStrictTransform_finiteLocallyFreeOfRank (k : ℕ)
    (a : Fit[R]_(k)(M))
    (hM :
      ∀ (p : Ideal R) [p.IsPrime] (_ : ¬ Fit[R]_(k)(M) ≤ p),
        Nonempty
          ((LocalizedModule.AtPrime p M) ≃ₗ[Localization.AtPrime p]
            (Fin k → Localization.AtPrime p))) :
    Module.FiniteLocallyFreeOfRank
      R[Fit[R]_(k)(M) / a] (affineBlowupStrictTransform (Fit[R]_(k)(M)) a M) k := by
  -- Route correction: factor the textbook proof through the two Fitting-ideal statements that are
  -- genuinely specific to the strict transform, and keep the injective descent from the chart to
  -- `R_a` as a separate proved helper.
  let A := R[Fit[R]_(k)(M) / a]
  let M' := affineBlowupStrictTransform (Fit[R]_(k)(M)) a M
  have hfitTop : Fit[A]_(k)(M') = ⊤ := by
    -- Lemma `15.26.3` is exactly the source computation that the strict transform has unit
    -- `k`th Fitting ideal on the affine blowup chart.
    simpa [A, M'] using
      fittingIdeal_affineBlowupStrictTransform_eq_top (R := R) (M := M) k a
  have hprevMapBot :
      Ideal.map
          (affineBlowupChartToLocalizationAway (Fit[R]_(k)(M)) a)
          (precedingFittingIdeal A M' k) = ⊥ := by
    -- Delegate the remaining source-faithful chart comparison to the dedicated helper above.
    simpa [A, M'] using
      precedingFittingIdeal_map_eq_bot_on_chart_away (R := R) (M := M) k a hM
  have hfitTop' :
      let A' := R[Fit[R]_(k)(M) / a]
      let M'' := affineBlowupStrictTransform (Fit[R]_(k)(M)) a M
      Fit[A']_(k)(M'') = ⊤ := by
    -- Re-express the localized chart statement using the ambient owner notation expected by the
    -- helper theorem.
    simpa [A, M'] using hfitTop
  have hprevMapBot' :
      let A' := R[Fit[R]_(k)(M) / a]
      let M'' := affineBlowupStrictTransform (Fit[R]_(k)(M)) a M
      Ideal.map
          (affineBlowupChartToLocalizationAway (Fit[R]_(k)(M)) a)
          (precedingFittingIdeal A' M'' k) = ⊥ := by
    -- Re-express the preceding Fitting-ideal vanishing in the same owner surface.
    simpa [A, M'] using hprevMapBot
  -- With the chart-local descent step proved above, the main theorem now reduces to the two
  -- source-faithful Fitting-ideal claims.
  exact strictTransform_finiteLocallyFreeOfRank_of_fitting_conditions
    (R := R) (M := M) k a hfitTop' hprevMapBot'

end
