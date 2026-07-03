import Mathlib
import StacksProject_2024.Chap10.Definition_10_157_1
import StacksProject_2024.Chap10.Lemma_10_25_1
import StacksProject_2024.Chap10.Lemma_10_63_18
import StacksProject_2024.Chap10.Lemma_10_72_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/- Domain-style sampling:
* primary domain: LinearRepresentations_Serre_1977 conditions and reducedness for Noetherian commutative rings;
* sampled owner/bridge declarations:
  `SerreConditionR`,
  `SerreConditionS`,
  `Module.embeddedAssociatedPrimes_eq_empty_iff_serreConditionS_one`,
  `embeddedPrimes_eq_empty_iff`;
* best owner abstraction: the ring-theoretic owner classes `SerreConditionR R 0` and
  `SerreConditionS R 1` from Definition 10.157.1;
* primitive data vs derived API: the LinearRepresentations_Serre_1977 conditions are primitive owners here, while the
  embedded-prime and associated-prime criteria are bridge/view API already provided upstream.

Source/core/bridge triage:
* `source-facing`: reducedness versus the textbook LinearRepresentations_Serre_1977 conditions `(R_0)` and `(S_1)`;
* `core/canonical`: the owner classes `SerreConditionR R 0` and `SerreConditionS R 1`;
* `bridge/view`: the source-facing localized and associated-prime criteria already live upstream,
  so this file keeps only the reducedness implications and does not repackage the `(S_1)` clause
  as a new ring-specific wrapper.
-/

/-- Helper for Lemma 10.157.3: localizing the self-module `R` at a prime ideal agrees with the
localized ring itself. -/
noncomputable abbrev localized_self_linearEquiv (p : Ideal R) [p.IsPrime] :
    LocalizedModule.AtPrime p R ≃ₗ[Localization.AtPrime p] Localization.AtPrime p :=
  (LocalizedModule.equivTensorProduct p.primeCompl R).trans
    (Algebra.TensorProduct.rid R (Localization.AtPrime p) (Localization.AtPrime p)).toLinearEquiv

/-- Helper for Lemma 10.157.3: a reduced Noetherian local ring of positive Krull dimension cannot
have its maximal ideal among the associated primes of the self-module. -/
lemma maximalIdeal_not_mem_associatedPrimes_of_isReduced_of_ringKrullDim_ne_zero
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsReduced A]
    (hdim : ringKrullDim A ≠ 0) :
    maximalIdeal A ∉ associatedPrimes A A := by
  intro hmax
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hmax
  rcases hmax with ⟨_, x, hx⟩
  have hnot_field : ¬ IsField A := by
    intro hfield
    letI : Field A := hfield.toField
    exact hdim (ringKrullDim_eq_zero_of_field A)
  have hmax_ne_bot : maximalIdeal A ≠ ⊥ := by
    intro hbot
    exact hnot_field ((IsLocalRing.isField_iff_maximalIdeal_eq).2 hbot)
  have hx_not_unit : ¬ IsUnit x := by
    intro hx_unit
    have hbot : maximalIdeal A = ⊥ := by
      rw [hx]
      ext a
      constructor
      · intro ha
        have ha_zero : a * x = 0 := by
          simpa [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] using ha
        rcases hx_unit with ⟨u, rfl⟩
        apply_fun fun y => y * ↑u⁻¹ at ha_zero
        simpa [mul_assoc] using ha_zero
      · intro ha
        rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul]
        have ha_zero : a = 0 := by
          simpa using ha
        simp [ha_zero]
    exact hmax_ne_bot hbot
  have hx_mem : x ∈ maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hx_not_unit
  -- The associated-prime witness lies in the maximal ideal, so it annihilates itself.
  have hx_sq_zero : x * x = 0 := by
    have hx_colon : x ∈ Submodule.colon (⊥ : Submodule A A) ({x} : Set A) := by
      simpa [hx] using hx_mem
    simpa [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] using hx_colon
  have hx_zero : x = 0 := by
    exact IsNilpotent.eq_zero ⟨2, by simpa [pow_two] using hx_sq_zero⟩
  have htop : maximalIdeal A = ⊤ := by
    rw [hx, hx_zero]
    ext a
    simp [Submodule.mem_colon_singleton, smul_eq_mul]
  exact (IsLocalRing.maximalIdeal.isMaximal A).1.1 htop

/-- Helper for Lemma 10.157.3: in a Noetherian local ring, an associated closed point forces the
local module depth to vanish. -/
lemma moduleDepth_eq_zero_of_maximalIdeal_mem_associatedPrimes
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hmax : maximalIdeal A ∈ associatedPrimes A N) :
    moduleDepth A N = 0 := by
  -- Bound the depth by the zero-dimensional residue field attached to the associated closed point.
  have hle :
      WithBot.some (moduleDepth A N : ℕ∞) ≤ ringKrullDim (A ⧸ maximalIdeal A) :=
    moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes (maximalIdeal A) hmax
  have hdim : ringKrullDim (A ⧸ maximalIdeal A) = 0 := by
    letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
    exact ringKrullDim_eq_zero_of_field (A ⧸ maximalIdeal A)
  rw [hdim] at hle
  have hdepth_le : moduleDepth A N ≤ 0 := by
    simpa [WithBot.some_eq_coe] using hle
  exact le_antisymm hdepth_le bot_le

/-- Helper for Lemma 10.157.3: over a Noetherian local ring, depth zero forces the maximal ideal
to be an associated prime of the module. -/
lemma maximalIdeal_mem_associatedPrimes_of_moduleDepth_eq_zero
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hdepth : moduleDepth A N = 0) :
    maximalIdeal A ∈ associatedPrimes A N := by
  -- Route correction: instead of importing Lemma `10.157.2`, rebuild the local depth-zero bridge
  -- directly from the regular-element criterion.
  have htop :
      maximalIdeal A • (⊤ : Submodule A N) ≠ ⊤ := by
    intro htop
    rw [show moduleDepth A N = ⊤ from
          Ideal.depth_eq_top_of_smul_top (maximalIdeal A) N htop] at hdepth
    simp at hdepth
  have hnontrivial : Nontrivial N := by
    by_contra hsub
    letI : Subsingleton N := not_nontrivial_iff_subsingleton.mp hsub
    exact htop <| by
      ext n
      simp [Subsingleton.elim n 0]
  have hno_regular : ¬ ∃ x ∈ maximalIdeal A, IsSMulRegular N x := by
    intro hreg
    rcases hreg with ⟨x, hx, hxreg⟩
    have hdepth_pos : (1 : ℕ∞) ≤ moduleDepth A N := by
      -- A regular element in the maximal ideal gives a regular sequence of length one.
      rw [show moduleDepth A N = sSup (Ideal.regularSequenceLengths (maximalIdeal A) N) from
            Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) N htop]
      refine le_sSup ?_
      refine ⟨[x], ?_, ?_, by simp⟩
      · exact RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal N
          (by
            intro r hr
            simpa [List.mem_singleton.mp hr] using hx)
          ((RingTheory.Sequence.isWeaklyRegular_singleton_iff N x).2 hxreg)
      · simpa using hx
    exact (ENat.one_le_iff_ne_zero.1 hdepth_pos) hdepth
  by_contra hmax
  have hforall :
      ∀ q ∈ associatedPrimes A N, ¬ maximalIdeal A ≤ q := by
    intro q hq hmq
    -- In a local ring, any prime containing the maximal ideal must equal the maximal ideal.
    have hq_le : q ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal hq.1.ne_top
    have hq_eq : q = maximalIdeal A := le_antisymm hq_le hmq
    exact hmax (hq_eq ▸ hq)
  exact hno_regular <|
    (exists_mem_isSMulRegular_iff_forall_not_le_associatedPrimes
      (R := A) (M := N) (I := maximalIdeal A)).2 hforall

/-- Helper for Lemma 10.157.3: positive local depth on the self-module yields a nonzerodivisor in
the maximal ideal. -/
lemma exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : moduleDepth A A ≠ 0) :
    ∃ t ∈ maximalIdeal A, IsSMulRegular A t := by
  -- Exclude the maximal ideal from the associated primes, then apply the regular-element criterion.
  have hforall :
      ∀ q ∈ associatedPrimes A A, ¬ maximalIdeal A ≤ q := by
    intro q hq hmq
    have hq_le : q ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal hq.1.ne_top
    have hq_eq : q = maximalIdeal A := le_antisymm hq_le hmq
    exact hdepth <| moduleDepth_eq_zero_of_maximalIdeal_mem_associatedPrimes (A := A) (hq_eq ▸ hq)
  exact
    (exists_mem_isSMulRegular_iff_forall_not_le_associatedPrimes
      (R := A) (M := A) (I := maximalIdeal A)).2 hforall

/-- Helper for Lemma 10.157.3: a zero-dimensional regular local ring is a field. -/
lemma isField_of_isRegularLocalRing_of_krullDim_eq_zero
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 0) :
    IsField A := by
  -- In dimension zero, regularity forces the maximal ideal to need zero generators.
  have hspan : (maximalIdeal A).spanFinrank = ringKrullDim A :=
    (isRegularLocalRing_iff A).1 inferInstance
  have hspan_zero : (maximalIdeal A).spanFinrank = 0 := by
    simpa [hdim] using hspan
  have hfg : (maximalIdeal A).FG := IsNoetherian.noetherian (maximalIdeal A)
  have hbot : maximalIdeal A = ⊥ :=
    (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).1 hspan_zero
  exact (IsLocalRing.isField_iff_maximalIdeal_eq).2 hbot

/-- Helper for Lemma 10.157.3: under `(S_1)`, localizing at a positive-height prime ideal gives a
self-module of nonzero depth. -/
lemma moduleDepth_localizationAtPrime_ne_zero_of_serreConditionS_one_of_primeHeight_ne_zero
    (hS : SerreConditionS R 1) (p : PrimeSpectrum R)
    (hp0 : p.asIdeal.primeHeight ≠ 0) :
    moduleDepth (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) ≠ 0 := by
  let A := Localization.AtPrime p.asIdeal
  have hdim_ne_zero : ringKrullDim A ≠ 0 := by
    intro hdim
    have hheight : p.asIdeal.height = 0 := by
      simpa [A, hdim] using
        (IsLocalization.AtPrime.ringKrullDim_eq_height
          p.asIdeal A).symm
    rw [Ideal.height_eq_primeHeight] at hheight
    exact hp0 hheight
  have hdim_ne_bot : ringKrullDim A ≠ ⊥ := ringKrullDim_ne_bot
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hdim_ne_bot
  have hd_ne_zero : d ≠ 0 := by
    intro hd_zero
    exact hdim_ne_zero <| by simpa [hd_zero] using hd.symm
  have hdim_ge_one : (1 : WithBot ℕ∞) ≤ ringKrullDim A := by
    have hd_ge_one : (1 : ℕ∞) ≤ d := ENat.one_le_iff_ne_zero.2 hd_ne_zero
    simpa [hd] using (WithBot.coe_le_coe.2 hd_ge_one)
  by_contra hdepth
  -- Compare the `(S_1)` lower bound with the positive Krull dimension forced by `hp0`.
  have hmin_le_zero : min (1 : WithBot ℕ∞) (ringKrullDim A) ≤ 0 := by
    simpa [A, hdepth] using
      (SerreConditionS.moduleDepth_localizationAtPrime_ge_min (R := R) hS p)
  have hmin_ge_one : (1 : WithBot ℕ∞) ≤ min (1 : WithBot ℕ∞) (ringKrullDim A) := by
    exact le_min le_rfl hdim_ge_one
  have : (1 : WithBot ℕ∞) ≤ 0 := le_trans hmin_ge_one hmin_le_zero
  exact not_le_of_gt (by simp : (0 : WithBot ℕ∞) < 1) this

/-- Helper for Lemma 10.157.3: a regular element stays nonzerodivisorial after inverting its
powers, so the away-localization map is injective. -/
lemma localizationAway_injective_of_isSMulRegular
    {A : Type*} [CommRing A] {t : A} (ht : IsSMulRegular A t) :
    Function.Injective (algebraMap A (Localization.Away t)) := by
  -- Every denominator in `A[1/t]` is a power of the regular element `t`, hence a nonzerodivisor.
  refine IsLocalization.injective (M := Submonoid.powers t) (S := Localization.Away t) ?_
  intro y hy
  rcases (show ∃ n : ℕ, t ^ n = y by simpa [Submonoid.mem_powers_iff] using hy) with ⟨n, rfl⟩
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  exact (ht.pow n) <| by simpa [mul_comm] using hx

/-- Helper for Lemma 10.157.3: every maximal ideal of `A[1/t]` contracts to a prime of `A`
strictly below the closed point because `t` becomes a unit after localization away from `t`. -/
lemma away_maximal_contraction_lt_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] {t : A}
    (ht_mem : t ∈ maximalIdeal A) (m : Ideal (Localization.Away t)) [m.IsMaximal] :
    Ideal.comap (algebraMap A (Localization.Away t)) m < maximalIdeal A := by
  let qA : Ideal A := Ideal.comap (algebraMap A (Localization.Away t)) m
  haveI : qA.IsPrime := Ideal.comap_isPrime (algebraMap A (Localization.Away t)) m
  have hle : qA ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal_of_isPrime qA
  refine lt_of_le_of_ne hle ?_
  intro hqA
  have ht_qA : t ∈ qA := by
    simpa [qA, hqA] using ht_mem
  have ht_m : algebraMap A (Localization.Away t) t ∈ m := by
    simpa [qA] using ht_qA
  -- The inverted element lands in `m`, so `m` would contain a unit and hence be the unit ideal.
  exact
    Ideal.IsMaximal.ne_top (inferInstance : m.IsMaximal) <|
      Ideal.eq_top_of_isUnit_mem _ ht_m (IsLocalization.Away.algebraMap_isUnit t)

/-- Helper for Lemma 10.157.3: localizing `A[1/t]` at a prime ideal is canonically the same as
localizing `A` at the contracted prime. -/
noncomputable abbrev away_maximal_localization_compare_to_contracted_atPrime
    {A : Type*} [CommRing A] {t : A} (m : Ideal (Localization.Away t)) [m.IsPrime] :
    Localization.AtPrime (Ideal.comap (algebraMap A (Localization.Away t)) m) ≃ₐ[A]
      Localization.AtPrime m :=
  IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := Submonoid.powers t) m

/-- Helper for Lemma 10.157.3: localizing `R_p` again at a prime ideal is canonically the same as
localizing `R` at the underlying prime. -/
noncomputable abbrev atPrime_contracted_localization_compare_to_under
    (p : PrimeSpectrum R) (qA : Ideal (Localization.AtPrime p.asIdeal)) [qA.IsPrime] :
    Localization.AtPrime (qA.under R) ≃ₐ[R] Localization.AtPrime qA :=
  by
    simpa [Ideal.under_def] using
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        (M := p.asIdeal.primeCompl) qA)

/-- Helper for Lemma 10.157.3: a maximal ideal of `A[1/t]` comes from a strictly smaller-height
prime of the original ring `R`, where `A = R_p`. -/
lemma away_maximal_under_primeHeight_lt
    (p : PrimeSpectrum R) {t : Localization.AtPrime p.asIdeal}
    (ht_mem : t ∈ maximalIdeal (Localization.AtPrime p.asIdeal))
    (m : Ideal (Localization.Away t)) [m.IsMaximal] :
    let qA : Ideal (Localization.AtPrime p.asIdeal) :=
      Ideal.comap (algebraMap (Localization.AtPrime p.asIdeal) (Localization.Away t)) m
    let qR : Ideal R := qA.under R
    qR.primeHeight < p.asIdeal.primeHeight := by
  let A := Localization.AtPrime p.asIdeal
  let qA : Ideal A := Ideal.comap (algebraMap A (Localization.Away t)) m
  haveI : qA.IsPrime := Ideal.comap_isPrime (algebraMap A (Localization.Away t)) m
  have hltA : qA < maximalIdeal A :=
    away_maximal_contraction_lt_maximalIdeal (A := A) ht_mem m
  have hheightA : qA.primeHeight < (maximalIdeal A).primeHeight :=
    Ideal.primeHeight_strict_mono hltA
  have hunder :
      (qA.under R).primeHeight = qA.primeHeight := by
    -- Compare heights through the canonical localization `R → R_p`.
    simpa [A, Ideal.under_def] using
      (IsLocalization.primeHeight_comap p.asIdeal.primeCompl (A := A) qA)
  have hmax :
      (maximalIdeal A).primeHeight = p.asIdeal.primeHeight := by
    -- The closed point of `R_p` has height equal to the height of `p`.
    exact WithBot.coe_inj.mp <| by
      calc
        ((maximalIdeal A).primeHeight : WithBot ℕ∞) = ringKrullDim A := by
          simpa [A] using (IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim (R := A))
        _ = p.asIdeal.height := IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal A
        _ = (p.asIdeal.primeHeight : WithBot ℕ∞) := by rw [Ideal.height_eq_primeHeight]
  change (qA.under R).primeHeight < p.asIdeal.primeHeight
  calc
    (qA.under R).primeHeight = qA.primeHeight := hunder
    _ < (maximalIdeal A).primeHeight := hheightA
    _ = p.asIdeal.primeHeight := hmax

-- Proof sketch: localize at a height-zero prime ideal. Reducedness localizes, and a reduced local
-- ring of Krull dimension `0` is a field, hence a regular local ring.
/-- A reduced Noetherian ring satisfies LinearRepresentations_Serre_1977's condition `(R_0)`. -/
instance [IsReduced R] : SerreConditionR R 0 where
  toIsNoetherian := inferInstance
  isRegularLocalRing_localizationAtPrime p hp := by
    have hp_zero : p.asIdeal.primeHeight = 0 := le_antisymm hp bot_le
    have hp_min : p.asIdeal ∈ minimalPrimes R := Ideal.primeHeight_eq_zero_iff.mp hp_zero
    let pmin : minimalPrimes R := ⟨p.asIdeal, hp_min⟩
    -- Height-zero localizations of a reduced ring are fields, so regularity follows from the
    -- standard field instance for regular local rings.
    letI : Field (Localization.AtPrime p.asIdeal) :=
      (isField_localizationAtPrime_of_minimalPrime pmin).toField
    infer_instance

-- Proof sketch: localize at a prime ideal. In dimension `0` the depth bound is automatic. In
-- positive dimension, depth `0` would force the closed point to be associated, contradicting the
-- reduced local lemma above.
/-- A reduced Noetherian ring satisfies LinearRepresentations_Serre_1977's condition `(S_1)`. -/
instance [IsReduced R] : SerreConditionS R 1 where
  toIsNoetherian := inferInstance
  toSerreConditionS := by
    -- Route correction: avoid the broken import of Lemma `10.157.2` and prove the primewise depth
    -- inequality directly on the localized self-module.
    refine
      { toFinite := inferInstance
        moduleDepth_localizationAtPrime_ge_min_supportDim := ?_ }
    intro p
    let A := Localization.AtPrime p.asIdeal
    let e := localized_self_linearEquiv (R := R) p.asIdeal
    have hsupport :
        Module.supportDim A (LocalizedModule.AtPrime p.asIdeal R) = ringKrullDim A := by
      simpa [A, Module.supportDim_self_eq_ringKrullDim] using Module.supportDim_eq_of_equiv e
    have hdepth :
        moduleDepth A (LocalizedModule.AtPrime p.asIdeal R) = moduleDepth A A := by
      simpa [A] using moduleDepth_eq_of_equiv e
    by_cases hdim : ringKrullDim A = 0
    · -- In dimension zero the right-hand side is `0`, so the depth bound is automatic.
      rw [hdepth, hsupport, hdim]
      simp
    · -- In positive dimension, reducedness rules out depth zero at the closed point.
      have hdepth_ne_zero : moduleDepth A A ≠ 0 := by
        intro hdepth_zero
        have hmax :
            maximalIdeal A ∈ associatedPrimes A A :=
          maximalIdeal_mem_associatedPrimes_of_moduleDepth_eq_zero
            (A := A) (N := A) hdepth_zero
        exact
          maximalIdeal_not_mem_associatedPrimes_of_isReduced_of_ringKrullDim_ne_zero
            (A := A) hdim hmax
      have hdepth_ge_one : (1 : ℕ∞) ≤ moduleDepth A A :=
        ENat.one_le_iff_ne_zero.2 hdepth_ne_zero
      have hdepth_ge_one' :
          (1 : WithBot ℕ∞) ≤ WithBot.some (moduleDepth A A : ℕ∞) := by
        simpa [WithBot.some_eq_coe] using (WithBot.coe_le_coe.2 hdepth_ge_one)
      rw [hdepth, hsupport]
      exact le_trans (min_le_left _ _) hdepth_ge_one'

/-- Helper for Lemma 10.157.3: under `(R_0)` and `(S_1)`, each height-zero localization is
reduced, and the positive-height case is the remaining induction step. -/
lemma isReduced_localizationAtPrime_of_serreConditionR_zero_and_serreConditionS_one
    (hR : SerreConditionR R 0) (hS : SerreConditionS R 1)
    (p : PrimeSpectrum R) :
    IsReduced (Localization.AtPrime p.asIdeal) := by
  -- Route correction: run the converse by strong induction on prime height, matching the source
  -- proof's passage from `R_p` to `R_p[1/t]` and then to smaller localizations of `R`.
  let P : ℕ → Prop := fun n =>
    ∀ q : PrimeSpectrum R,
      ENat.toNat q.asIdeal.primeHeight = n →
        IsReduced (Localization.AtPrime q.asIdeal)
  have hP : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih q hqn
    by_cases hq0 : q.asIdeal.primeHeight = 0
    · -- The base case is exactly `(R_0)`: a zero-dimensional regular local ring is a field.
      have hregular : IsRegularLocalRing (Localization.AtPrime q.asIdeal) :=
        hR.isRegularLocalRing_localizationAtPrime q hq0.le
      letI := hregular
      have hdim :
          ringKrullDim (Localization.AtPrime q.asIdeal) = 0 := by
        simpa [Ideal.height_eq_primeHeight, hq0] using
          (IsLocalization.AtPrime.ringKrullDim_eq_height
            q.asIdeal (Localization.AtPrime q.asIdeal))
      letI : Field (Localization.AtPrime q.asIdeal) :=
        (isField_of_isRegularLocalRing_of_krullDim_eq_zero
          (A := Localization.AtPrime q.asIdeal) hdim).toField
      infer_instance
    · let A := Localization.AtPrime q.asIdeal
      -- In positive height, extract a regular element in the closed point and embed `A` into
      -- the away-localization `A[1/t]`.
      have hdepth_ne_zero :
          moduleDepth A A ≠ 0 :=
        moduleDepth_localizationAtPrime_ne_zero_of_serreConditionS_one_of_primeHeight_ne_zero
          (R := R) hS q hq0
      obtain ⟨t, ht_mem, ht_reg⟩ :=
        exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero
          (A := A) hdepth_ne_zero
      have hinj : Function.Injective (algebraMap A (Localization.Away t)) :=
        localizationAway_injective_of_isSMulRegular (A := A) ht_reg
      have hAwayReduced : IsReduced (Localization.Away t) := by
        -- Each maximal localization of `A[1/t]` comes from a strictly smaller-height
        -- localization of `R`, so the induction hypothesis applies after the two canonical
        -- localization-of-a-localization comparisons.
        refine isReduced_ofLocalizationMaximal (Localization.Away t) fun m _ ↦ ?_
        let qA : Ideal A := Ideal.comap (algebraMap A (Localization.Away t)) m
        haveI : qA.IsPrime := Ideal.comap_isPrime (algebraMap A (Localization.Away t)) m
        let qR : Ideal R := qA.under R
        haveI : qR.IsPrime := by
          simpa [qR, Ideal.under_def] using (Ideal.comap_isPrime (algebraMap R A) qA)
        let q' : PrimeSpectrum R := ⟨qR, inferInstance⟩
        have hltHeight : qR.primeHeight < q.asIdeal.primeHeight := by
          simpa [A, qA, qR] using
            away_maximal_under_primeHeight_lt (R := R) q ht_mem m
        have hltNat : ENat.toNat qR.primeHeight < n := by
          rw [← hqn]
          have hltCoe :
              ((ENat.toNat qR.primeHeight : ℕ∞) < ENat.toNat q.asIdeal.primeHeight) := by
            simpa
              [ENat.coe_toNat (ne_of_lt (Ideal.primeHeight_lt_top qR)),
                ENat.coe_toNat (ne_of_lt (Ideal.primeHeight_lt_top q.asIdeal))] using hltHeight
          exact_mod_cast hltCoe
        have hred_qR : IsReduced (Localization.AtPrime qR) :=
          ih (ENat.toNat qR.primeHeight) hltNat q' rfl
        have hred_qA : IsReduced (Localization.AtPrime qA) := by
          let e := atPrime_contracted_localization_compare_to_under (R := R) q qA
          letI : IsReduced (Localization.AtPrime qR) := hred_qR
          exact isReduced_of_injective e.symm.toRingHom e.symm.injective
        let eAway := away_maximal_localization_compare_to_contracted_atPrime (A := A) (t := t) m
        letI : IsReduced (Localization.AtPrime qA) := hred_qA
        exact isReduced_of_injective eAway.symm.toRingHom eAway.symm.injective
      letI : IsReduced (Localization.Away t) := hAwayReduced
      -- Reducedness descends back along the injective map `A → A[1/t]`.
      exact isReduced_of_injective (algebraMap A (Localization.Away t)) hinj
  exact hP (ENat.toNat p.asIdeal.primeHeight) p rfl

-- Proof sketch: the forward implication is given by the two preceding reducedness instances. For
-- the converse, use `(R_0)` to see that localizations at minimal primes are fields, and use the
-- canonical `(S_1)` owner together with its upstream associated-prime bridge to rule out
-- nilpotents in every localization.
/-- Lemma 10.157.3: for a Noetherian ring `R`, reducedness is equivalent to LinearRepresentations_Serre_1977's conditions
`(R_0)` and `(S_1)`. -/
lemma isReduced_iff_serreConditionR_zero_and_serreConditionS_one :
    IsReduced R ↔ SerreConditionR R 0 ∧ SerreConditionS R 1 := by
  constructor
  · intro h
    letI := h
    exact ⟨inferInstance, inferInstance⟩
  · intro h
    rcases h with ⟨hR, hS⟩
    -- The global converse reduces to checking reducedness after localizing at maximal ideals.
    refine isReduced_ofLocalizationMaximal R fun p _ ↦ ?_
    let p' : PrimeSpectrum R := ⟨p, inferInstance⟩
    simpa using
      isReduced_localizationAtPrime_of_serreConditionR_zero_and_serreConditionS_one
        (R := R) hR hS p'

end
