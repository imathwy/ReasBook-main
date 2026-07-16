import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_25_1
import stacks_proof.stacks_project.Chap10.Lemma_10_72_5
import stacks_proof.stacks_project.Chap10.Lemma_10_157_2
import stacks_proof.stacks_project.Chap10.Lemma_10_163_4
import stacks_proof.stacks_project.Chap10.Lemma_10_163_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing
open scoped TensorProduct

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling pass:
* primary domain: Noetherian commutative algebra of ascent of reducedness along flat maps;
* sampled owner declarations of the same kind:
  - `IsReduced`, the owner for ring reducedness;
  - `isReduced_iff_serreConditionR_zero_and_serreConditionS_one`, the canonical owner-level
    characterization of reducedness by Serre conditions;
  - `serreConditionR_of_flat_of_fiber`, the chapter ascent theorem for `(R₀)`;
  - `serreConditionS_of_flat_of_fiber`, the chapter ascent theorem for `(S₁)`.

Best owner abstraction:
* the public target stays the source-facing reducedness theorem, but the proof should pass entirely
  through the canonical owners `IsReduced`, `SerreConditionR`, and `SerreConditionS`, instead of
  keeping a parallel reducedness-specific local wheel.

Primitive data vs. derived API:
* primitive data: the flat algebra `R → S`, the Noetherian hypotheses on `R` and `S`, the
  reduced base-ring owner `[IsReduced R]`, and the fiberwise reducedness hypothesis `hfiber`;
* derived API: the `(R₀)` and `(S₁)` instances for the base and the fibers, obtained canonically
  from the Serre criterion and then fed into the existing ascent theorems.

Source/core/bridge triage:
* `source-facing`: `isReduced_of_flat_of_fiber`, the textbook ascent statement for reducedness;
* `core/canonical`: `IsReduced`, `SerreConditionR`, `SerreConditionS`, and the criterion
  `isReduced_iff_serreConditionR_zero_and_serreConditionS_one`;
* `bridge/view`: the two ascent theorems for `(R₀)` and `(S₁)` along the flat map.
-/
-- Proof sketch: for Noetherian rings, reducedness is equivalent to Serre's conditions `(S_1)` and
-- `(R_0)` by Lemma `10.157.3`. Apply the flat ascent results `10.163.4` and `10.163.5` to the base
-- ring `R` and the reduced fiber rings `p.asIdeal.Fiber S`, then invoke Lemma `10.157.3` again to
-- recover reducedness of `S`.
/-- Helper for Lemma 10.163.6: a reduced Noetherian local ring of positive Krull dimension cannot
have its maximal ideal as an associated prime of the self-module. -/
lemma reduced_local_ring_maximalIdeal_not_associated_of_positive_krullDim
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsReduced A]
    (hdim : ringKrullDim A ≠ 0) :
    maximalIdeal A ∉ associatedPrimes A A := by
  -- Proof comment: an associated maximal ideal would annihilate a nonunit `x`, forcing `x² = 0`
  -- and hence `x = 0` in the reduced ring, which collapses the maximal ideal to `⊤`.
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

/-- Helper for Lemma 10.163.6: a reduced Noetherian ring satisfies Serre's conditions `(R_0)` and
`(S_1)`. -/
lemma serreConditionR_zero_and_serreConditionS_one_of_isReduced_noetherian_ring
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsReduced A] :
    SerreConditionR A 0 ∧ SerreConditionS A 1 := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: a height-zero localization is the localization at a minimal prime, hence a
    -- field in the reduced Noetherian case.
    refine
      { toIsNoetherian := inferInstance
        isRegularLocalRing_localizationAtPrime := ?_ }
    intro p hp
    have hp_zero : p.asIdeal.primeHeight = 0 := le_antisymm hp bot_le
    have hp_min : p.asIdeal ∈ minimalPrimes A := Ideal.primeHeight_eq_zero_iff.mp hp_zero
    let pmin : minimalPrimes A := ⟨p.asIdeal, hp_min⟩
    letI : Field (Localization.AtPrime p.asIdeal) :=
      (isField_localizationAtPrime_of_minimalPrime (R := A) pmin).toField
    infer_instance
  · -- Proof comment: after localizing the self-module, positive dimension forces positive depth
    -- because reducedness rules out the closed point as an associated prime.
    refine
      { toIsNoetherian := inferInstance
        toSerreConditionS := ?_ }
    refine
      { toFinite := inferInstance
        moduleDepth_localizationAtPrime_ge_min_supportDim := ?_ }
    intro p
    let Ap := Localization.AtPrime p.asIdeal
    let e := localized_self_linearEquiv (R := A) p.asIdeal
    have hsupport :
        Module.supportDim Ap (LocalizedModule.AtPrime p.asIdeal A) = ringKrullDim Ap := by
      simpa [Ap, Module.supportDim_self_eq_ringKrullDim] using Module.supportDim_eq_of_equiv e
    have hdepth :
        moduleDepth Ap (LocalizedModule.AtPrime p.asIdeal A) = moduleDepth Ap Ap := by
      simpa [Ap] using moduleDepth_eq_of_equiv e
    by_cases hdim : ringKrullDim Ap = 0
    · -- Proof comment: in dimension zero, the right-hand side is `0`, so the depth inequality is automatic.
      rw [hdepth, hsupport, hdim]
      simp
    · have hdepth_ne_zero : moduleDepth Ap Ap ≠ 0 := by
        intro hdepth_zero
        have hmax :
            maximalIdeal Ap ∈ associatedPrimes Ap Ap :=
          Module.maximalIdeal_mem_associatedPrimes_of_moduleDepth_eq_zero
            (A := Ap) hdepth_zero
        exact
          reduced_local_ring_maximalIdeal_not_associated_of_positive_krullDim
            (A := Ap) hdim hmax
      have hdepth_ge_one : (1 : ℕ∞) ≤ moduleDepth Ap Ap :=
        ENat.one_le_iff_ne_zero.2 hdepth_ne_zero
      have hdepth_ge_one' :
          (1 : WithBot ℕ∞) ≤ WithBot.some (moduleDepth Ap Ap : ℕ∞) := by
        simpa [WithBot.some_eq_coe] using (WithBot.coe_le_coe.2 hdepth_ge_one)
      rw [hdepth, hsupport]
      exact le_trans (min_le_left _ _) hdepth_ge_one'

/-- Helper for Lemma 10.163.6: a zero-dimensional regular local ring is a field. -/
private lemma regularLocalRing_isField_of_krullDim_eq_zero
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 0) :
    IsField A := by
  -- Proof comment: regularity identifies the Krull dimension with the minimal number of generators
  -- of the maximal ideal, so dimension zero forces the maximal ideal to vanish.
  have hspan : (maximalIdeal A).spanFinrank = ringKrullDim A :=
    (isRegularLocalRing_iff A).1 inferInstance
  have hspan_zero : (maximalIdeal A).spanFinrank = 0 := by
    simpa [hdim] using hspan
  have hfg : (maximalIdeal A).FG := IsNoetherian.noetherian (maximalIdeal A)
  have hbot : maximalIdeal A = ⊥ :=
    (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).1 hspan_zero
  exact (IsLocalRing.isField_iff_maximalIdeal_eq).2 hbot

/-- Helper for Lemma 10.163.6: under `(S₁)`, a positive-height localization has nonzero depth. -/
private lemma localized_depth_ne_zero_of_serreConditionS_one
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (hS : SerreConditionS A 1) (p : PrimeSpectrum A)
    (hp0 : p.asIdeal.primeHeight ≠ 0) :
    moduleDepth (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) ≠ 0 := by
  let Ap := Localization.AtPrime p.asIdeal
  have hdim_ne_zero : ringKrullDim Ap ≠ 0 := by
    intro hdim
    have hheight : p.asIdeal.height = 0 := by
      simpa [Ap, hdim] using
        (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal Ap).symm
    rw [Ideal.height_eq_primeHeight] at hheight
    exact hp0 hheight
  have hdim_ne_bot : ringKrullDim Ap ≠ ⊥ := ringKrullDim_ne_bot
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hdim_ne_bot
  have hd_ne_zero : d ≠ 0 := by
    intro hd_zero
    exact hdim_ne_zero <| by simpa [hd_zero] using hd.symm
  have hdim_ge_one : (1 : WithBot ℕ∞) ≤ ringKrullDim Ap := by
    have hd_ge_one : (1 : ℕ∞) ≤ d := ENat.one_le_iff_ne_zero.2 hd_ne_zero
    simpa [hd] using (WithBot.coe_le_coe.2 hd_ge_one)
  by_contra hdepth
  -- Proof comment: `(S₁)` gives `depth ≥ min (1, dim)`, and positive dimension makes that minimum at least `1`.
  have hmin_le_zero : min (1 : WithBot ℕ∞) (ringKrullDim Ap) ≤ 0 := by
    simpa [Ap, hdepth] using
      (SerreConditionS.moduleDepth_localizationAtPrime_ge_min (R := A) hS p)
  have hmin_ge_one : (1 : WithBot ℕ∞) ≤ min (1 : WithBot ℕ∞) (ringKrullDim Ap) := by
    exact le_min le_rfl hdim_ge_one
  have : (1 : WithBot ℕ∞) ≤ 0 := le_trans hmin_ge_one hmin_le_zero
  exact not_le_of_gt (by simp : (0 : WithBot ℕ∞) < 1) this

/-- Helper for Lemma 10.163.6: inverting powers of a regular element gives an injective map to the
away-localization. -/
private lemma localizationAway_injective_of_regular_element
    {A : Type*} [CommRing A] {t : A} (ht : IsSMulRegular A t) :
    Function.Injective (algebraMap A (Localization.Away t)) := by
  -- Proof comment: every denominator is a power of the same regular element, so zero upstairs
  -- already vanishes downstairs before localization.
  refine IsLocalization.injective (M := Submonoid.powers t) (S := Localization.Away t) ?_
  intro y hy
  rcases (show ∃ n : ℕ, t ^ n = y by simpa [Submonoid.mem_powers_iff] using hy) with ⟨n, rfl⟩
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  exact (ht.pow n) <| by simpa [mul_comm] using hx

/-- Helper for Lemma 10.163.6: a maximal ideal of `A[1/t]` contracts strictly below the closed
point when `t` lies in the closed point of the local ring `A`. -/
private lemma away_maximal_contraction_lt_closed_point
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
  -- Proof comment: if the image of `t` lay in a maximal ideal upstairs, that ideal would contain a unit.
  exact
    Ideal.IsMaximal.ne_top (inferInstance : m.IsMaximal) <|
      Ideal.eq_top_of_isUnit_mem _ ht_m (IsLocalization.Away.algebraMap_isUnit t)

/-- Helper for Lemma 10.163.6: localizing `A[1/t]` at a prime is canonically the same as
localizing `A` at the contracted prime. -/
private noncomputable abbrev away_localization_compare_to_contracted_prime
    {A : Type*} [CommRing A] {t : A} (m : Ideal (Localization.Away t)) [m.IsPrime] :
    Localization.AtPrime (Ideal.comap (algebraMap A (Localization.Away t)) m) ≃ₐ[A]
      Localization.AtPrime m :=
  IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := Submonoid.powers t) m

/-- Helper for Lemma 10.163.6: localizing `Rₚ` at a prime is canonically the same as localizing
`R` at the underlying prime. -/
private noncomputable abbrev atPrime_localization_compare_to_under
    {A : Type*} [CommRing A] (p : PrimeSpectrum A)
    (qA : Ideal (Localization.AtPrime p.asIdeal)) [qA.IsPrime] :
    Localization.AtPrime (Ideal.comap (algebraMap A (Localization.AtPrime p.asIdeal)) qA) ≃ₐ[A]
      Localization.AtPrime qA :=
  IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := p.asIdeal.primeCompl) qA

/-- Helper for Lemma 10.163.6: a maximal ideal of `A[1/t]` over `A = Rₚ` comes from a strictly
smaller-height prime of `R`. -/
private lemma away_maximal_under_primeHeight_lt
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (p : PrimeSpectrum A) {t : Localization.AtPrime p.asIdeal}
    (ht_mem : t ∈ maximalIdeal (Localization.AtPrime p.asIdeal))
    (m : Ideal (Localization.Away t)) [m.IsMaximal] :
    let qA : Ideal (Localization.AtPrime p.asIdeal) :=
      Ideal.comap (algebraMap (Localization.AtPrime p.asIdeal) (Localization.Away t)) m
    let qR : Ideal A := qA.under A
    qR.primeHeight < p.asIdeal.primeHeight := by
  let Ap := Localization.AtPrime p.asIdeal
  let qA : Ideal Ap := Ideal.comap (algebraMap Ap (Localization.Away t)) m
  haveI : qA.IsPrime := Ideal.comap_isPrime (algebraMap Ap (Localization.Away t)) m
  have hltA : qA < maximalIdeal Ap :=
    away_maximal_contraction_lt_closed_point (A := Ap) ht_mem m
  have hheightA : qA.primeHeight < (maximalIdeal Ap).primeHeight :=
    Ideal.primeHeight_strict_mono hltA
  have hunder : (qA.under A).primeHeight = qA.primeHeight := by
    -- Proof comment: prime heights are preserved when comparing `Rₚ` with the underlying prime of `R`.
    simpa [Ap, Ideal.under_def] using
      (IsLocalization.primeHeight_comap p.asIdeal.primeCompl (A := Ap) qA)
  have hmax : (maximalIdeal Ap).primeHeight = p.asIdeal.primeHeight := by
    -- Proof comment: the closed point of `Rₚ` has exactly the height of `p`.
    exact WithBot.coe_inj.mp <| by
      calc
        ((maximalIdeal Ap).primeHeight : WithBot ℕ∞) = ringKrullDim Ap := by
          simpa [Ap] using (IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim (R := Ap))
        _ = p.asIdeal.height := IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal Ap
        _ = (p.asIdeal.primeHeight : WithBot ℕ∞) := by rw [Ideal.height_eq_primeHeight]
  change (qA.under A).primeHeight < p.asIdeal.primeHeight
  calc
    (qA.under A).primeHeight = qA.primeHeight := hunder
    _ < (maximalIdeal Ap).primeHeight := hheightA
    _ = p.asIdeal.primeHeight := hmax

/-- Helper for Lemma 10.163.6: under `(R₀)` and `(S₁)`, every prime localization is reduced. -/
private lemma isReduced_localizationAtPrime_of_serreConditionR_zero_and_serreConditionS_one_entry
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (hR : SerreConditionR A 0) (hS : SerreConditionS A 1)
    (p : PrimeSpectrum A) :
    IsReduced (Localization.AtPrime p.asIdeal) := by
  -- Route correction: follow the source proof by induction on prime height and compare
  -- maximal localizations of `A[1/t]` with strictly smaller localizations of `A`.
  let P : ℕ → Prop := fun n =>
    ∀ q : PrimeSpectrum A,
      ENat.toNat q.asIdeal.primeHeight = n → IsReduced (Localization.AtPrime q.asIdeal)
  have hP : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih q hqn
    by_cases hq0 : q.asIdeal.primeHeight = 0
    · have hregular : IsRegularLocalRing (Localization.AtPrime q.asIdeal) :=
        hR.isRegularLocalRing_localizationAtPrime q hq0.le
      letI := hregular
      have hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 0 := by
        simpa [Ideal.height_eq_primeHeight, hq0] using
          (IsLocalization.AtPrime.ringKrullDim_eq_height
            q.asIdeal (Localization.AtPrime q.asIdeal))
      letI : Field (Localization.AtPrime q.asIdeal) :=
        (regularLocalRing_isField_of_krullDim_eq_zero
          (A := Localization.AtPrime q.asIdeal) hdim).toField
      infer_instance
    · let Aq := Localization.AtPrime q.asIdeal
      have hdepth_ne_zero :
          moduleDepth Aq Aq ≠ 0 :=
        localized_depth_ne_zero_of_serreConditionS_one (A := A) hS q hq0
      obtain ⟨t, ht_mem, ht_reg⟩ :=
        exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero
          (R := Aq) (M := Aq) hdepth_ne_zero
      have hinj : Function.Injective (algebraMap Aq (Localization.Away t)) :=
        localizationAway_injective_of_regular_element (A := Aq) ht_reg
      have hAwayReduced : IsReduced (Localization.Away t) := by
        refine isReduced_ofLocalizationMaximal (Localization.Away t) fun m _ ↦ ?_
        let qA : Ideal Aq := Ideal.comap (algebraMap Aq (Localization.Away t)) m
        haveI : qA.IsPrime := Ideal.comap_isPrime (algebraMap Aq (Localization.Away t)) m
        let qR : Ideal A := qA.under A
        haveI : qR.IsPrime := by
          simpa [qR, Ideal.under_def] using (Ideal.comap_isPrime (algebraMap A Aq) qA)
        let q' : PrimeSpectrum A := ⟨qR, inferInstance⟩
        have hltHeight : qR.primeHeight < q.asIdeal.primeHeight := by
          simpa [Aq, qA, qR] using
            away_maximal_under_primeHeight_lt (A := A) q ht_mem m
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
          let e := atPrime_localization_compare_to_under (A := A) q qA
          letI : IsReduced (Localization.AtPrime qR) := hred_qR
          exact isReduced_of_injective e.symm.toRingHom e.symm.injective
        let eAway := away_localization_compare_to_contracted_prime (A := Aq) (t := t) m
        letI : IsReduced (Localization.AtPrime qA) := hred_qA
        exact isReduced_of_injective eAway.symm.toRingHom eAway.symm.injective
      letI : IsReduced (Localization.Away t) := hAwayReduced
      exact isReduced_of_injective (algebraMap Aq (Localization.Away t)) hinj
  exact hP (ENat.toNat p.asIdeal.primeHeight) p rfl

/-- Helper for Lemma 10.163.6: Serre's conditions `(R₀)` and `(S₁)` imply reducedness. -/
private lemma isReduced_of_serreConditionR_zero_and_serreConditionS_one_entry
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (hR : SerreConditionR A 0) (hS : SerreConditionS A 1) :
    IsReduced A := by
  -- Proof comment: reducedness is local on maximal localizations, so the primewise induction closes the global claim.
  refine isReduced_ofLocalizationMaximal A fun p _ ↦ ?_
  let p' : PrimeSpectrum A := ⟨p, inferInstance⟩
  simpa using
    isReduced_localizationAtPrime_of_serreConditionR_zero_and_serreConditionS_one_entry
      (A := A) hR hS p'

/-- Lemma 10.163.6: if `R → S` is flat, `R` and `S` are Noetherian, `R` is reduced, and every
fiber ring `κ(𝔭) ⊗[R] S`, formalized as `p.asIdeal.Fiber S`, is reduced, then `S` is reduced. -/
@[stacks 0C21]
theorem isReduced_of_flat_of_fiber
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S] [IsReduced R]
    (hfiber : ∀ p : PrimeSpectrum R, IsReduced (p.asIdeal.Fiber S)) :
    IsReduced S := by
  have hbase :
      SerreConditionR R 0 ∧ SerreConditionS R 1 :=
    serreConditionR_zero_and_serreConditionS_one_of_isReduced_noetherian_ring (A := R)
  have hfiberSerre (p : PrimeSpectrum R) :
      SerreConditionR (p.asIdeal.Fiber S) 0 ∧ SerreConditionS (p.asIdeal.Fiber S) 1 := by
    -- Proof comment: the fiber is Noetherian via its tensor-product presentation over the
    -- Noetherian ring `S`, so the reduced-to-Serre bridge applies verbatim.
    let _ : Algebra.EssFiniteType S (S ⊗[R] p.asIdeal.ResidueField) := inferInstance
    let _ : IsNoetherianRing (S ⊗[R] p.asIdeal.ResidueField) :=
      Algebra.EssFiniteType.isNoetherianRing S (S ⊗[R] p.asIdeal.ResidueField)
    let _ : IsNoetherianRing (p.asIdeal.Fiber S) :=
      isNoetherianRing_of_ringEquiv (S ⊗[R] p.asIdeal.ResidueField)
        (Algebra.TensorProduct.comm R p.asIdeal.ResidueField S).toRingEquiv.symm
    exact
      serreConditionR_zero_and_serreConditionS_one_of_isReduced_noetherian_ring
        (A := p.asIdeal.Fiber S)
  letI : SerreConditionR R 0 := hbase.1
  letI : SerreConditionS R 1 := hbase.2
  -- Proof comment: ascend `(R_0)` and `(S_1)` separately from the base and the fibers.
  have hSR : SerreConditionR S 0 :=
    serreConditionR_of_flat_of_fiber fun p ↦ (hfiberSerre p).1
  have hSS : SerreConditionS S 1 :=
    serreConditionS_of_flat_of_fiber fun p ↦ (hfiberSerre p).2
  -- Proof comment: the local criterion from Lemma `10.157.3` now reconstructs reducedness of `S`.
  exact isReduced_of_serreConditionR_zero_and_serreConditionS_one_entry (A := S) hSR hSS

end
