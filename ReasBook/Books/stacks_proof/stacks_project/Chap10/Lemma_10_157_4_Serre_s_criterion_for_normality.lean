import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_37_11
import stacks_proof.stacks_project.Chap10.Definition_10_157_1
import stacks_proof.stacks_project.Chap10.Lemma_10_37_16
import stacks_proof.stacks_project.Chap10.Lemma_10_62_4
import stacks_proof.stacks_project.Chap10.Lemma_10_119_2_Koll_r
import stacks_proof.stacks_project.Chap10.Lemma_10_119_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: a discrete valuation ring
is a regular local ring of Krull dimension `1`. -/
lemma regularLocalRing_dim_one_of_isDiscreteValuationRing
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    IsRegularLocalRing A ∧ ringKrullDim A = 1 := by
  constructor
  · infer_instance
  · exact IsPrincipalIdealRing.ringKrullDim_eq_one A
      (IsDiscreteValuationRing.not_isField (R := A))

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: a one-dimensional regular
local ring is a discrete valuation ring. -/
lemma isDiscreteValuationRing_of_isRegularLocalRing_of_ringKrullDim_eq_one
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hreg : IsRegularLocalRing A) (hdim : ringKrullDim A = 1) :
    IsDiscreteValuationRing A := by
  letI : IsRegularLocalRing A := hreg
  letI : IsDomain A := regularLocalRing_isDomain
  have hnotField : ¬ IsField A :=
    (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain (R := A)).mp hdim |>.1
  have hcot :
      Module.finrank (ResidueField A) (CotangentSpace A) = 1 :=
    finrank_cotangentSpace_eq_one_of_regular_dim_one (R := A) hdim
  have hprincipal : maximalIdeal A ≠ ⊥ ∧ (maximalIdeal A).IsPrincipal := by
    constructor
    · -- Proof comment: Krull dimension `1` rules out the field case, so the maximal ideal is
      -- nonzero.
      exact isField_iff_maximalIdeal_eq.not.mp hnotField
    · -- Proof comment: in a one-dimensional regular local ring the cotangent space has
      -- dimension `1`, which is equivalent to principality of the maximal ideal.
      exact
        (IsLocalRing.finrank_cotangentSpace_le_one_iff (R := A)).mp <|
          by simpa [hcot]
  exact ((IsDiscreteValuationRing.TFAE A hnotField).out 4 0).mp hprincipal.2

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: a one-dimensional normal
local domain is a regular local ring of dimension `1`. -/
lemma regularLocalRing_dim_one_of_normalLocalDomain_dim_one
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsDomain A] [IsIntegrallyClosed A] (hdim : ringKrullDim A = 1) :
    IsRegularLocalRing A ∧ ringKrullDim A = 1 := by
  have hnotField : ¬ IsField A :=
    (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain (R := A)).mp hdim |>.1
  letI : Ring.DimensionLEOne A := by
    -- Proof comment: Krull dimension `1` gives the Dedekind-domain dimension bound.
    refine ⟨?_⟩
    intro p hp0 hpPrime
    exact
      (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp
        (Ring.krullDimLE_iff.mpr (by simpa [hdim]))) p hp0 hpPrime
  letI : IsDedekindDomain A :=
    (isDedekindDomain_iff A (FractionRing A)).mpr
      ⟨inferInstance, inferInstance, inferInstance, by
        -- Proof comment: integrally closed means each integral fraction already lies in `A`.
        intro x hx
        exact (isIntegrallyClosed_iff (FractionRing A)).mp
          (inferInstance : IsIntegrallyClosed A) hx⟩
  have hprincipal : maximalIdeal A ≠ ⊥ ∧ (maximalIdeal A).IsPrincipal := by
    constructor
    · exact isField_iff_maximalIdeal_eq.not.mp hnotField
    · exact maximalIdeal_isPrincipal_of_isDedekindDomain A
  have hDVR : IsDiscreteValuationRing A :=
    ((IsDiscreteValuationRing.TFAE A hnotField).out 4 0).mp hprincipal.2
  letI : IsDiscreteValuationRing A := hDVR
  exact regularLocalRing_dim_one_of_isDiscreteValuationRing (A := A)

/-- Helper for Lemma 10.157.4 (Serre's criterion for normality): a normal Noetherian ring is
regular in codimension at most `1`. -/
lemma serreConditionR_one_of_isNormalRing [IsNormalRing R] : SerreConditionR R 1 := by
  refine
    { toIsNoetherian := inferInstance
      isRegularLocalRing_localizationAtPrime := ?_ }
  intro p hp
  let A := Localization.AtPrime p.asIdeal
  letI : IsDomain A := isDomain_localizationAtPrime p
  by_cases hp0 : p.asIdeal.primeHeight = 0
  · -- In codimension `0`, the prime localization is a field, hence regular local.
    have hdim0 : ringKrullDim A = 0 := by
      calc
        ringKrullDim A = p.asIdeal.height := by
          simpa [A] using
            (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal A)
        _ = p.asIdeal.primeHeight := by
          rw [Ideal.height_eq_primeHeight]
        _ = 0 := by
          simpa using congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hp0
    letI : Ring.KrullDimLE 0 A := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim0
    let hField : IsField A := Ring.KrullDimLE.isField_of_isDomain
    have hmax : IsLocalRing.maximalIdeal A = ⊥ :=
      (IsLocalRing.isField_iff_maximalIdeal_eq (R := A)).1 hField
    have hspan0 : (IsLocalRing.maximalIdeal A).spanFinrank = 0 := by
      simpa [hmax] using (Submodule.spanFinrank_bot : (⊥ : Ideal A).spanFinrank = 0)
    have hspan_le : (IsLocalRing.maximalIdeal A).spanFinrank ≤ ringKrullDim A := by
      simpa [hspan0, hdim0]
    exact IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (R := A) hspan_le
  · -- In codimension `1`, Lemma `10.119.7` upgrades the normal local domain to a DVR, hence to a
    -- regular local ring.
    have hp1 : p.asIdeal.primeHeight = 1 := by
      exact le_antisymm hp (ENat.one_le_iff_ne_zero.2 hp0)
    have hdim1 : ringKrullDim A = 1 := by
      calc
        ringKrullDim A = p.asIdeal.height := by
          simpa [A] using
            (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal A)
        _ = p.asIdeal.primeHeight := by
          rw [Ideal.height_eq_primeHeight]
        _ = 1 := by
          simpa using congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hp1
    letI : IsIntegrallyClosed A := isIntegrallyClosed_localizationAtPrime p
    have hNormalDimOne :
        ∃ (_ : IsLocalRing A) (_ : IsNoetherianRing A) (_ : IsDomain A)
          (_ : IsIntegrallyClosed A), ringKrullDim A = 1 := by
      exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, hdim1⟩
    have hRegDim : IsRegularLocalRing A ∧ ringKrullDim A = 1 := by
      rcases hNormalDimOne with ⟨_, _, _, _, hdimA⟩
      exact regularLocalRing_dim_one_of_normalLocalDomain_dim_one (A := A) hdimA
    exact hRegDim.1

/-- Helper for Lemma 10.157.4 (Serre's criterion for normality): `(R₁)` and `(S₂)` imply the
weaker Serre conditions `(R₀)` and `(S₁)`. -/
lemma serreConditionR_zero_and_serreConditionS_one_of_serreConditionR_one_and_serreConditionS_two
    (hR : R ⊧ (R₁)) (hS : R ⊧ (S₂)) :
    SerreConditionR R 0 ∧ SerreConditionS R 1 := by
  refine ⟨?_, ?_⟩
  · refine
      { toIsNoetherian := inferInstance
        isRegularLocalRing_localizationAtPrime := ?_ }
    intro p hp0
    -- The codimension-zero clause is a direct weakening of `(R₁)`.
    exact hR.isRegularLocalRing_localizationAtPrime p (le_trans hp0 (by norm_num))
  · refine
      { toIsNoetherian := inferInstance
        toSerreConditionS := ?_ }
    refine
      { toFinite := inferInstance
        moduleDepth_localizationAtPrime_ge_min_supportDim := ?_ }
    intro p
    -- Replace the support-dimension formulation by the ring self-module dimension and weaken
    -- `min (2, dim)` to `min (1, dim)`.
    rw [Module.supportDim_self_eq_ringKrullDim]
    have hdepth := SerreConditionS.moduleDepth_localizationAtPrime_ge_min (R := R) hS p
    exact le_trans (min_le_min (by norm_num) le_rfl) hdepth

/-- Helper for Lemma 10.157.4 (Serre's criterion for normality): localizing the self-module at a
prime ideal agrees with the localized ring itself. -/
private noncomputable abbrev localized_self_linearEquiv (p : Ideal R) [p.IsPrime] :
    LocalizedModule.AtPrime p R ≃ₗ[Localization.AtPrime p] Localization.AtPrime p :=
  (LocalizedModule.equivTensorProduct p.primeCompl R).trans
    (Algebra.TensorProduct.rid R (Localization.AtPrime p) (Localization.AtPrime p)).toLinearEquiv

/-- Helper for Lemma 10.157.4 (Serre's criterion for normality): a zero-dimensional regular local
ring is a field. -/
lemma isField_of_isRegularLocalRing_of_krullDim_eq_zero
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 0) :
    IsField A := by
  -- Proof comment: in Krull dimension zero, regularity forces the maximal ideal to need zero
  -- generators, so the maximal ideal must vanish.
  have hspan : (maximalIdeal A).spanFinrank = ringKrullDim A :=
    (isRegularLocalRing_iff A).1 inferInstance
  have hspan_zero : (maximalIdeal A).spanFinrank = 0 := by
    simpa [hdim] using hspan
  have hfg : (maximalIdeal A).FG := IsNoetherian.noetherian (maximalIdeal A)
  have hbot : maximalIdeal A = ⊥ :=
    (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).1 hspan_zero
  exact (IsLocalRing.isField_iff_maximalIdeal_eq).2 hbot

/-- Helper for Lemma 10.157.4 (Serre's criterion for normality): under `(S₁)`, localizing at a
positive-height prime ideal gives a self-module of nonzero depth. -/
lemma moduleDepth_localizationAtPrime_ne_zero_of_serreConditionS_one_of_primeHeight_ne_zero
    (hS : SerreConditionS R 1) (p : PrimeSpectrum R)
    (hp0 : p.asIdeal.primeHeight ≠ 0) :
    moduleDepth (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) ≠ 0 := by
  let A := Localization.AtPrime p.asIdeal
  have hdim_ne_zero : ringKrullDim A ≠ 0 := by
    intro hdim
    have hheight : p.asIdeal.height = 0 := by
      simpa [A, hdim] using
        (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal A).symm
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
  -- Proof comment: `(S₁)` gives `depth ≥ min (1, dim)`, and positive dimension makes that lower
  -- bound at least `1`.
  have hmin_le_zero : min (1 : WithBot ℕ∞) (ringKrullDim A) ≤ 0 := by
    simpa [A, hdepth] using
      (SerreConditionS.moduleDepth_localizationAtPrime_ge_min (R := R) hS p)
  have hmin_ge_one : (1 : WithBot ℕ∞) ≤ min (1 : WithBot ℕ∞) (ringKrullDim A) := by
    exact le_min le_rfl hdim_ge_one
  have : (1 : WithBot ℕ∞) ≤ 0 := le_trans hmin_ge_one hmin_le_zero
  exact not_le_of_gt (by simp : (0 : WithBot ℕ∞) < 1) this

/-- Helper for Lemma 10.157.4 (Serre's criterion for normality): a regular element stays
nonzerodivisorial after inverting its powers, so the away-localization map is injective. -/
lemma localizationAway_injective_of_isSMulRegular
    {A : Type*} [CommRing A] {t : A} (ht : IsSMulRegular A t) :
    Function.Injective (algebraMap A (Localization.Away t)) := by
  -- Proof comment: every denominator in `A[1/t]` is a power of the same regular element `t`.
  refine IsLocalization.injective (M := Submonoid.powers t) (S := Localization.Away t) ?_
  intro y hy
  rcases (show ∃ n : ℕ, t ^ n = y by simpa [Submonoid.mem_powers_iff] using hy) with ⟨n, rfl⟩
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  exact (ht.pow n) <| by simpa [mul_comm] using hx

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: every prime of `A[1/t]`
contracts to a prime of `A` strictly below the closed point when `t` lies in the closed point,
because `t` becomes a unit after localization away from `t`. -/
lemma away_prime_contraction_lt_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] {t : A}
    (ht_mem : t ∈ maximalIdeal A) (q : Ideal (Localization.Away t)) [q.IsPrime] :
    Ideal.comap (algebraMap A (Localization.Away t)) q < maximalIdeal A := by
  let qA : Ideal A := Ideal.comap (algebraMap A (Localization.Away t)) q
  letI : qA.IsPrime := Ideal.comap_isPrime (algebraMap A (Localization.Away t)) q
  have hle : qA ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal_of_isPrime qA
  refine lt_of_le_of_ne hle ?_
  intro hqA
  have ht_qA : t ∈ qA := by
    simpa [qA, hqA] using ht_mem
  have ht_q : algebraMap A (Localization.Away t) t ∈ q := by
    simpa [qA] using ht_qA
  -- Proof comment: if the contraction were the closed point, the prime upstairs would contain
  -- the inverted element, hence a unit, contradicting primality.
  exact
    Ideal.IsPrime.ne_top (inferInstance : q.IsPrime) <|
      Ideal.eq_top_of_isUnit_mem _ ht_q (IsLocalization.Away.algebraMap_isUnit t)

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: the maximal-prime version
of the principal-open contraction bridge. -/
lemma away_maximal_contraction_lt_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] {t : A}
    (ht_mem : t ∈ maximalIdeal A) (m : Ideal (Localization.Away t)) [m.IsMaximal] :
    Ideal.comap (algebraMap A (Localization.Away t)) m < maximalIdeal A := by
  -- Proof comment: maximal ideals are prime, so the general principal-open contraction bridge
  -- immediately gives the strict closed-point inequality.
  exact away_prime_contraction_lt_maximalIdeal (A := A) ht_mem m

/-- Helper for Lemma 10.157.4 (Serre's criterion for normality): localizing `A[1/t]` at a prime
ideal is canonically the same as localizing `A` at the contracted prime. -/
noncomputable abbrev away_maximal_localization_compare_to_contracted_atPrime
    {A : Type*} [CommRing A] {t : A} (m : Ideal (Localization.Away t)) [m.IsPrime] :
    Localization.AtPrime (Ideal.comap (algebraMap A (Localization.Away t)) m) ≃ₐ[A]
      Localization.AtPrime m :=
  IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := Submonoid.powers t) m

/-- Helper for Lemma 10.157.4 (Serre's criterion for normality): localizing `Rₚ` again at a prime
ideal is canonically the same as localizing `R` at the underlying prime. -/
noncomputable abbrev atPrime_contracted_localization_compare_to_under
    (p : PrimeSpectrum R) (qA : Ideal (Localization.AtPrime p.asIdeal)) [qA.IsPrime] :
    Localization.AtPrime (qA.under R) ≃ₐ[R] Localization.AtPrime qA :=
  by
    simpa [Ideal.under_def] using
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        (M := p.asIdeal.primeCompl) qA)

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: a normal-domain pair
transports across a ring equivalence. -/
lemma normalPair_of_ringEquiv
    {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (h : IsDomain A ∧ IsIntegrallyClosed A) :
    IsDomain B ∧ IsIntegrallyClosed B := by
  -- Proof comment: domainhood and integral closedness are both invariant under the same
  -- equivalence, so this records the transport once for the later localization comparisons.
  letI : IsIntegrallyClosed A := h.2
  exact ⟨((e : A ≃* B).isDomain_iff).mp h.1, IsIntegrallyClosed.of_equiv e⟩

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: local normality at the
underlying prime of `R` transports to the corresponding prime localization of `Rₚ`. -/
lemma normalPair_atPrime_of_under
    (p : PrimeSpectrum R) {qA : Ideal (Localization.AtPrime p.asIdeal)} [qA.IsPrime]
    (h : IsDomain (Localization.AtPrime (qA.under R)) ∧
      IsIntegrallyClosed (Localization.AtPrime (qA.under R))) :
    IsDomain (Localization.AtPrime qA) ∧ IsIntegrallyClosed (Localization.AtPrime qA) := by
  -- Proof comment: the canonical iterated-localization comparison is exactly the bridge from
  -- the contracted prime over `R` to the prime of `Rₚ`.
  exact normalPair_of_ringEquiv
    (atPrime_contracted_localization_compare_to_under (R := R) p qA).toRingEquiv h

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: local normality at the
contraction of a prime of `A[1/t]` transports to that prime localization upstairs. -/
lemma normalPair_awayAtPrime_of_contracted
    {A : Type*} [CommRing A] {t : A} (q : Ideal (Localization.Away t)) [q.IsPrime]
    (h : IsDomain (Localization.AtPrime (Ideal.comap (algebraMap A (Localization.Away t)) q)) ∧
      IsIntegrallyClosed
        (Localization.AtPrime (Ideal.comap (algebraMap A (Localization.Away t)) q))) :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  -- Proof comment: use the principal-open localization comparison to move the normal-domain pair
  -- from the contracted prime of `A` to the actual prime of `A[1/t]`.
  exact normalPair_of_ringEquiv
    (away_maximal_localization_compare_to_contracted_atPrime (A := A) (t := t) q).toRingEquiv h

/-- Helper for Lemma 10.157.4 (Serre's criterion for normality): a maximal ideal of `Rₚ[1/t]`
comes from a strictly smaller-height prime of `R`. -/
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
  have hunder : (qA.under R).primeHeight = qA.primeHeight := by
    -- Proof comment: compare heights through the canonical localization `R → Rₚ`.
    simpa [A, Ideal.under_def] using
      (IsLocalization.primeHeight_comap p.asIdeal.primeCompl (A := A) qA)
  have hmax : (maximalIdeal A).primeHeight = p.asIdeal.primeHeight := by
    -- Proof comment: the closed point of `Rₚ` has height equal to the height of `p`.
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

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: a nonclosed prime of
`Rₚ` contracts to a strictly smaller-height prime of `R`. -/
lemma under_primeHeight_lt_of_lt_maximalIdeal_atPrime
    (p : PrimeSpectrum R) {qA : Ideal (Localization.AtPrime p.asIdeal)} [qA.IsPrime]
    (hlt : qA < maximalIdeal (Localization.AtPrime p.asIdeal)) :
    (qA.under R).primeHeight < p.asIdeal.primeHeight := by
  let A := Localization.AtPrime p.asIdeal
  have hheightA : qA.primeHeight < (maximalIdeal A).primeHeight :=
    Ideal.primeHeight_strict_mono hlt
  have hunder : (qA.under R).primeHeight = qA.primeHeight := by
    -- Proof comment: localization at `p` preserves the height of primes lying under `Rₚ`.
    simpa [A, Ideal.under_def] using
      (IsLocalization.primeHeight_comap p.asIdeal.primeCompl (A := A) qA)
  have hmax : (maximalIdeal A).primeHeight = p.asIdeal.primeHeight := by
    -- Proof comment: the closed point of `Rₚ` has height equal to the height of `p`.
    exact WithBot.coe_inj.mp <| by
      calc
        ((maximalIdeal A).primeHeight : WithBot ℕ∞) = ringKrullDim A := by
          simpa [A] using (IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim (R := A))
        _ = p.asIdeal.height := IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal A
        _ = (p.asIdeal.primeHeight : WithBot ℕ∞) := by rw [Ideal.height_eq_primeHeight]
  -- Proof comment: compare contracted height, upstairs height, and the closed-point height.
  calc
    (qA.under R).primeHeight = qA.primeHeight := hunder
    _ < (maximalIdeal A).primeHeight := hheightA
    _ = p.asIdeal.primeHeight := hmax

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: every prime of
`Rₚ[1/t]` contracts to a strictly smaller-height prime of `R` when `t` lies in the closed point
of `Rₚ`. -/
lemma away_prime_under_primeHeight_lt
    (p : PrimeSpectrum R) {t : Localization.AtPrime p.asIdeal}
    (ht_mem : t ∈ maximalIdeal (Localization.AtPrime p.asIdeal))
    (q : Ideal (Localization.Away t)) [q.IsPrime] :
    let qA : Ideal (Localization.AtPrime p.asIdeal) :=
      Ideal.comap (algebraMap (Localization.AtPrime p.asIdeal) (Localization.Away t)) q
    let qR : Ideal R := qA.under R
    qR.primeHeight < p.asIdeal.primeHeight := by
  let A := Localization.AtPrime p.asIdeal
  let qA : Ideal A := Ideal.comap (algebraMap A (Localization.Away t)) q
  letI : qA.IsPrime := Ideal.comap_isPrime (algebraMap A (Localization.Away t)) q
  have hltA : qA < maximalIdeal A :=
    away_prime_contraction_lt_maximalIdeal (A := A) ht_mem q
  -- Proof comment: first contract the away-prime to a nonclosed prime of `Rₚ`, then use the
  -- localization height comparison already isolated for nonclosed primes.
  change (qA.under R).primeHeight < p.asIdeal.primeHeight
  exact under_primeHeight_lt_of_lt_maximalIdeal_atPrime (R := R) p hltA

/-- Helper for Lemma 10.157.4 (Serre's criterion for normality): under `(R₀)` and `(S₁)`, every
prime localization is reduced. This is the strong-induction core of the source proof. -/
lemma isReduced_localizationAtPrime_of_serreConditionR_zero_and_serreConditionS_one
    (hR : SerreConditionR R 0) (hS : SerreConditionS R 1)
    (p : PrimeSpectrum R) :
    IsReduced (Localization.AtPrime p.asIdeal) := by
  -- Route correction: follow the source proof exactly. Induct on prime height, move from `Rₚ`
  -- to `Rₚ[1/t]` using a regular element from positive depth, and compare maximal localizations
  -- of `Rₚ[1/t]` with smaller-height localizations of `R`.
  let P : ℕ → Prop := fun n =>
    ∀ q : PrimeSpectrum R,
      ENat.toNat q.asIdeal.primeHeight = n → IsReduced (Localization.AtPrime q.asIdeal)
  have hP : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih q hqn
    by_cases hq0 : q.asIdeal.primeHeight = 0
    · -- Proof comment: the height-zero branch is exactly `(R₀)`.
      have hregular : IsRegularLocalRing (Localization.AtPrime q.asIdeal) :=
        hR.isRegularLocalRing_localizationAtPrime q hq0.le
      letI := hregular
      have hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 0 := by
        simpa [Ideal.height_eq_primeHeight, hq0] using
          (IsLocalization.AtPrime.ringKrullDim_eq_height
            q.asIdeal (Localization.AtPrime q.asIdeal))
      letI : Field (Localization.AtPrime q.asIdeal) :=
        (isField_of_isRegularLocalRing_of_krullDim_eq_zero
          (A := Localization.AtPrime q.asIdeal) hdim).toField
      infer_instance
    · let A := Localization.AtPrime q.asIdeal
      -- Proof comment: positive height gives positive depth by `(S₁)`, hence a nonzerodivisor
      -- `t ∈ 𝔪_A`; reducedness then descends from `A[1/t]`.
      have hdepth_ne_zero :
          moduleDepth A A ≠ 0 :=
        moduleDepth_localizationAtPrime_ne_zero_of_serreConditionS_one_of_primeHeight_ne_zero
          (R := R) hS q hq0
      obtain ⟨t, ht_mem, ht_reg⟩ :=
        exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero
          (R := A) (M := A) hdepth_ne_zero
      have hinj : Function.Injective (algebraMap A (Localization.Away t)) :=
        localizationAway_injective_of_isSMulRegular (A := A) ht_reg
      have hAwayReduced : IsReduced (Localization.Away t) := by
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
      exact isReduced_of_injective (algebraMap A (Localization.Away t)) hinj
  exact hP (ENat.toNat p.asIdeal.primeHeight) p rfl

/-- Helper for Lemma 10.157.4 (Serre's criterion for normality): `(R₀)` and `(S₁)` imply that the
ring is reduced. This is the local fragment of Lemma `10.157.3` needed here. -/
lemma isReduced_of_serreConditionR_zero_and_serreConditionS_one
    (hR : SerreConditionR R 0) (hS : SerreConditionS R 1) :
    IsReduced R := by
  -- Route correction: keep the source proof from Lemma `10.157.3` internal to this file instead
  -- of importing the whole earlier item. Global reducedness follows by checking every maximal
  -- localization with the local induction above.
  refine isReduced_ofLocalizationMaximal R fun p _ ↦ ?_
  let p' : PrimeSpectrum R := ⟨p, inferInstance⟩
  simpa using
    isReduced_localizationAtPrime_of_serreConditionR_zero_and_serreConditionS_one
      (R := R) hR hS p'

/-- Helper for Lemma 10.157.4 (Serre's criterion for normality): a positive-dimensional normal
local domain cannot occur in Kollár's exceptional finite-extension branch. -/
lemma not_hasKollarExceptionalFiniteExtension_of_normal_local_domain_of_krullDim_ne_zero
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    [IsIntegrallyClosed A] (hdim : ringKrullDim A ≠ 0) :
    ¬ HasKollarExceptionalFiniteExtension A := by
  intro hExceptional
  rcases (hasKollarExceptionalFiniteExtension_iff (R := A)).1 hExceptional with
    ⟨S, _, _, _, hS_nontrivial, hnotbij, ⟨n, hkerPow, hcokerPow⟩, hmax_not_assoc⟩
  let η : A →+* S := algebraMap A S
  have hnot_field : ¬ IsField A := by
    intro hfield
    letI : Field A := hfield.toField
    exact hdim (ringKrullDim_eq_zero_of_field A)
  have hmax_ne_bot : maximalIdeal A ≠ ⊥ := by
    intro hbot
    exact hnot_field ((IsLocalRing.isField_iff_maximalIdeal_eq).2 hbot)
  have hforall :
      ∀ q ∈ associatedPrimes A S, ¬ maximalIdeal A ≤ q := by
    intro q hq hmq
    have hq_le : q ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal hq.1.ne_top
    have hq_eq : q = maximalIdeal A := le_antisymm hq_le hmq
    exact hmax_not_assoc (hq_eq ▸ hq)
  obtain ⟨x, hx, hxreg⟩ :=
    (exists_mem_isSMulRegular_iff_forall_not_le_associatedPrimes
      (R := A) (M := S) (I := maximalIdeal A)).2 hforall
  have hx_ne_zero : x ≠ 0 := by
    intro hx0
    have : (1 : S) = 0 := by
      exact hxreg.right_eq_zero_of_smul <| by simpa [hx0]
    exact one_ne_zero this
  have hηinj : Function.Injective η := by
    -- Proof comment: `x^n` kills the kernel, and `x ≠ 0` in the domain `A`, so the kernel is
    -- already zero before localizing.
    refine (RingHom.injective_iff_ker_eq_bot η).2 ?_
    ext a
    constructor
    · intro ha
      have hxa_mem :
          x ^ n • a ∈ (maximalIdeal A) ^ n • (RingHom.ker η : Submodule A A) := by
        exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hx n) ha
      have hxa_zero : x ^ n * a = 0 := by
        have : x ^ n • a ∈ ((maximalIdeal A) ^ n • (RingHom.ker η : Submodule A A)) := hxa_mem
        rw [hkerPow] at this
        simpa [Submodule.mem_bot, smul_eq_mul] using this
      have ha_zero : a = 0 := by
        rcases mul_eq_zero.mp hxa_zero with hxpow_zero | ha_zero
        · exact False.elim ((pow_ne_zero n hx_ne_zero) hxpow_zero)
        · exact ha_zero
      simpa [Submodule.mem_bot, ha_zero]
    · intro ha
      have ha_zero : a = 0 := by simpa [Submodule.mem_bot] using ha
      simpa [RingHom.mem_ker, ha_zero]
  have hxreg_image : IsSMulRegular S (algebraMap A S x) := by
    -- Proof comment: regularity of the scalar action by `x` is exactly regularity of
    -- multiplication by its image in the `A`-algebra `S`.
    refine IsSMulRegular.of_right_eq_zero_of_smul ?_
    intro s hs
    exact hxreg.right_eq_zero_of_smul <| by simpa [Algebra.smul_def] using hs
  have hAwayInj :
      Function.Injective (Localization.awayMap η x) := by
    rw [Localization.awayMap_injective_iff]
    intro a ha
    have ha_mem : a ∈ RingHom.ker η := by simpa [η] using ha
    have hxa_mem :
        x ^ n • a ∈ (maximalIdeal A) ^ n • (RingHom.ker η : Submodule A A) := by
      exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hx n) ha_mem
    refine ⟨n, ?_⟩
    have : x ^ n • a ∈ ((maximalIdeal A) ^ n • (RingHom.ker η : Submodule A A)) := hxa_mem
    rw [hkerPow] at this
    simpa [Submodule.mem_bot, smul_eq_mul] using this
  have hAwaySurj :
      Function.Surjective (Localization.awayMap η x) := by
    rw [Localization.awayMap_surjective_iff]
    intro s
    -- Proof comment: `x^n ∈ 𝔪^n`, so the cokernel torsion hypothesis writes `x^n * s` in the
    -- image of `A → S`, which is the explicit surjectivity criterion for the away map.
    have hxs_mem :
        x ^ n • s ∈ (maximalIdeal A) ^ n • (⊤ : Submodule A S) := by
      exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hx n) (by simp)
    have hxs_range : x ^ n • s ∈ (Algebra.linearMap A S).range := hcokerPow hxs_mem
    rcases hxs_range with ⟨a, ha⟩
    refine ⟨a, n, ?_⟩
    simpa [η, Algebra.smul_def, map_pow] using ha
  let e : Localization.Away x ≃ₐ[A] Localization.Away (η x) :=
    AlgEquiv.ofBijective (Localization.awayMapₐ (Algebra.ofId A S) x) <|
      by
        simpa [Localization.awayMapₐ] using ⟨hAwayInj, hAwaySurj⟩
  have hpow :
      Submonoid.powers x ≤ nonZeroDivisors A := by
    intro y hy
    rcases (show ∃ m : ℕ, x ^ m = y by simpa [Submonoid.mem_powers_iff] using hy) with ⟨m, rfl⟩
    rw [mem_nonZeroDivisors_iff_right]
    intro a ha
    rcases mul_eq_zero.mp ha with ha_zero | hxpow_zero
    · exact ha_zero
    · exact False.elim ((pow_ne_zero m hx_ne_zero) hxpow_zero)
  letI : Algebra (Localization.Away x) (FractionRing A) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe
      (Localization.Away x) (FractionRing A) (Submonoid.powers x) (nonZeroDivisors A) hpow
  letI : IsScalarTower A (Localization.Away x) (FractionRing A) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (Localization.Away x) (FractionRing A) (Submonoid.powers x) (nonZeroDivisors A) hpow
  letI : IsFractionRing (Localization.Away x) (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers x) (Localization.Away x) (FractionRing A)
  let ψ : S →ₐ[A] FractionRing A :=
    (IsScalarTower.toAlgHom A (Localization.Away x) (FractionRing A)).comp <|
      e.symm.toAlgHom.comp
        (IsScalarTower.toAlgHom A S (Localization.Away (η x)))
  have hSLocInj :
      Function.Injective (algebraMap S (Localization.Away (η x))) := by
    simpa using localizationAway_injective_of_isSMulRegular (A := S) hxreg_image
  have hFracInj :
      Function.Injective (algebraMap (Localization.Away x) (FractionRing A)) := by
    simpa using (IsFractionRing.injective (Localization.Away x) (FractionRing A))
  have hψinj : Function.Injective ψ := by
    exact hFracInj.comp (e.symm.injective.comp hSLocInj)
  have hηsurj : Function.Surjective η := by
    intro s
    -- Proof comment: every `s : S` maps into the fraction field of `A`, remains integral over
    -- `A` by finiteness, and therefore comes from `A` because `A` is integrally closed.
    have hs_integral : IsIntegral A s := Algebra.IsIntegral.isIntegral s
    have hψs_integral : IsIntegral A (ψ s) := IsIntegral.map ψ hs_integral
    obtain ⟨a, ha⟩ :=
      IsIntegrallyClosed.algebraMap_eq_of_integral (K := FractionRing A) hψs_integral
    refine ⟨a, hψinj ?_⟩
    calc
      ψ (η a) = algebraMap A (FractionRing A) a := by simpa [η] using (AlgHom.commutes ψ a)
      _ = ψ s := ha
  exact hnotbij ⟨hηinj, hηsurj⟩

/-- Helper for Lemma 10.157.4 (Serre's criterion for normality): a normal Noetherian ring
satisfies Serre's condition `(S₂)`. -/
lemma serreConditionS_two_of_isNormalRing [IsNormalRing R] : SerreConditionS R 2 := by
  refine
    { toIsNoetherian := inferInstance
      toSerreConditionS := ?_ }
  refine
    { toFinite := inferInstance
      moduleDepth_localizationAtPrime_ge_min_supportDim := ?_ }
  intro p
  let A := Localization.AtPrime p.asIdeal
  letI : IsDomain A := isDomain_localizationAtPrime p
  letI : IsIntegrallyClosed A := isIntegrallyClosed_localizationAtPrime p
  let e := localized_self_linearEquiv (R := R) p.asIdeal
  have hsupport :
      Module.supportDim A (LocalizedModule.AtPrime p.asIdeal R) = ringKrullDim A := by
    simpa [A, Module.supportDim_self_eq_ringKrullDim] using Module.supportDim_eq_of_equiv e
  have hdepth :
      moduleDepth A (LocalizedModule.AtPrime p.asIdeal R) = moduleDepth A A := by
    simpa [A] using moduleDepth_eq_of_equiv e
  rw [hsupport, hdepth]
  by_cases hdim0 : ringKrullDim A = 0
  · -- In dimension `0`, the `(S₂)` lower bound is trivial.
    simpa [hdim0]
  · by_cases hdim1 : ringKrullDim A = 1
    · -- In dimension `1`, the normal local domain is a DVR and hence Cohen-Macaulay.
      have hNormalDimOne :
          ∃ (_ : IsLocalRing A) (_ : IsNoetherianRing A) (_ : IsDomain A)
            (_ : IsIntegrallyClosed A), ringKrullDim A = 1 := by
        exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, hdim1⟩
      have hRegDim : IsRegularLocalRing A ∧ ringKrullDim A = 1 := by
        rcases hNormalDimOne with ⟨_, _, _, _, hdimA⟩
        exact regularLocalRing_dim_one_of_normalLocalDomain_dim_one (A := A) hdimA
      letI : IsRegularLocalRing A := hRegDim.1
      have hCM : Module.CohenMacaulay A A := inferInstance
      have hdepth_eq :
          WithBot.some (moduleDepth A A : ℕ∞) = 1 := by
        simpa [Module.supportDim_self_eq_ringKrullDim, hRegDim.2] using
          hCM.supportDim_eq_moduleDepth.symm
      simpa [hdim1, hdepth_eq]
    · -- Outside dimensions `0` and `1`, Kollár's trichotomy forces depth at least `2`.
      have hArtFalse : ¬ IsArtinianRing A := by
        intro hArt
        exact hdim0 <|
          ringKrullDimZero_iff_ringKrullDim_eq_zero.mp
            ((isArtinianRing_iff_krullDimLE_zero).mp hArt)
      have hRegFalse : ¬ (IsRegularLocalRing A ∧ ringKrullDim A = 1) := by
        rintro ⟨_, hdimA⟩
        exact hdim1 hdimA
      have hExceptionalFalse : ¬ HasKollarExceptionalFiniteExtension A :=
        not_hasKollarExceptionalFiniteExtension_of_normal_local_domain_of_krullDim_ne_zero
          (A := A) hdim0
      have hxor :=
        kollar_exactly_one_of_artinian_regular_dim_one_depth_ge_two_or_exceptional_finite_extension
          (R := A)
      have hdepth : (2 : WithTop ℕ) ≤ moduleDepth A A := by
        simpa [Xor', hArtFalse, hRegFalse, hExceptionalFalse] using hxor
      have hdepth_enat : (2 : ℕ∞) ≤ moduleDepth A A := by
        simpa using hdepth
      have hdepth_bot : (2 : WithBot ℕ∞) ≤ WithBot.some (moduleDepth A A : ℕ∞) := by
        simpa [WithBot.some_eq_coe] using (WithBot.coe_le_coe.2 hdepth_enat)
      exact le_trans (min_le_left _ _) hdepth_bot

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: `(R₁)` makes every prime
localization of height at most one a normal domain. -/
lemma normalPair_localizationAtPrime_of_serreConditionR_one_of_primeHeight_le_one
    (hR : R ⊧ (R₁)) (p : PrimeSpectrum R) (hp : p.asIdeal.primeHeight ≤ 1) :
    IsDomain (Localization.AtPrime p.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := by
  let A := Localization.AtPrime p.asIdeal
  have hreg : IsRegularLocalRing A :=
    hR.isRegularLocalRing_localizationAtPrime p hp
  letI : IsRegularLocalRing A := hreg
  have hDomain : IsDomain A := regularLocalRing_isDomain
  letI : IsDomain A := hDomain
  by_cases hp0 : p.asIdeal.primeHeight = 0
  · have hdim0 : ringKrullDim A = 0 := by
      calc
        ringKrullDim A = p.asIdeal.height := by
          simpa [A] using
            (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal A)
        _ = p.asIdeal.primeHeight := by
          rw [Ideal.height_eq_primeHeight]
        _ = 0 := by
          simpa using congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hp0
    have hField : IsField A :=
      isField_of_isRegularLocalRing_of_krullDim_eq_zero (A := A) hdim0
    letI : Field A := hField.toField
    -- Proof comment: a field is a domain and integrally closed, closing the height-zero case.
    exact ⟨hDomain, inferInstance⟩
  · have hp1 : p.asIdeal.primeHeight = 1 := by
      exact le_antisymm hp (ENat.one_le_iff_ne_zero.2 hp0)
    have hdim1 : ringKrullDim A = 1 := by
      calc
        ringKrullDim A = p.asIdeal.height := by
          simpa [A] using
            (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal A)
        _ = p.asIdeal.primeHeight := by
          rw [Ideal.height_eq_primeHeight]
        _ = 1 := by
          simpa using congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hp1
    have hRegularDimOne : IsRegularLocalRing A ∧ ringKrullDim A = 1 := by
      -- Proof comment: package the regular-local and one-dimensional data in the clause-3
      -- normal form of the DVR equivalence.
      exact ⟨hreg, hdim1⟩
    have hDVR : IsDiscreteValuationRing A :=
      isDiscreteValuationRing_of_isRegularLocalRing_of_ringKrullDim_eq_one
        (A := A) hreg hdim1
    letI : IsDiscreteValuationRing A := hDVR
    -- Proof comment: a one-dimensional regular local domain is a DVR, hence integrally closed.
    exact ⟨hDomain, inferInstance⟩

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: `(S₂)` gives depth at
least two at prime localizations whose closed point has height at least two. -/
lemma moduleDepth_localizationAtPrime_ge_two_of_serreConditionS_two_of_primeHeight_ge_two
    (hS : R ⊧ (S₂)) (p : PrimeSpectrum R) (hp : (2 : ℕ∞) ≤ p.asIdeal.primeHeight) :
    (2 : WithTop ℕ) ≤
      moduleDepth (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) := by
  let A := Localization.AtPrime p.asIdeal
  have hdim_ge_two : (2 : WithBot ℕ∞) ≤ ringKrullDim A := by
    calc
      (2 : WithBot ℕ∞) ≤ (p.asIdeal.primeHeight : WithBot ℕ∞) :=
        WithBot.coe_le_coe.2 hp
      _ = p.asIdeal.height := by rw [Ideal.height_eq_primeHeight]
      _ = ringKrullDim A := (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal A).symm
  have hmin : min (2 : WithBot ℕ∞) (ringKrullDim A) = 2 :=
    min_eq_left hdim_ge_two
  have hdepth :=
    SerreConditionS.moduleDepth_localizationAtPrime_ge_min (R := R) hS p
  have hdepth_bot :
      (2 : WithBot ℕ∞) ≤ WithBot.some (moduleDepth A A : ℕ∞) := by
    simpa [A, hmin] using hdepth
  have hdepth_enat : (2 : ℕ∞) ≤ moduleDepth A A := by
    exact WithBot.coe_le_coe.mp (by simpa [WithBot.some_eq_coe] using hdepth_bot)
  -- Proof comment: the `ℕ∞` inequality is the same depth inequality in `WithTop ℕ`.
  simpa [A] using hdepth_enat

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: if every strict
contraction below the closed point of a local ring is normal, then the principal open obtained
by inverting an element of the closed point is normal. -/
lemma isNormalRing_localizationAway_of_normal_contractions
    {A : Type*} [CommRing A] [IsLocalRing A] {t : A}
    (ht_mem : t ∈ maximalIdeal A)
    (hnormal : ∀ q : PrimeSpectrum A, q.asIdeal < maximalIdeal A →
      IsDomain (Localization.AtPrime q.asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime q.asIdeal)) :
    IsNormalRing (Localization.Away t) := by
  -- Proof comment: prove the owner condition primewise after contracting each away-prime back to
  -- a strict prime below the closed point of `A`.
  refine ⟨fun q ↦ ?_⟩
  let qA : Ideal A := Ideal.comap (algebraMap A (Localization.Away t)) q.asIdeal
  letI : qA.IsPrime := Ideal.comap_isPrime (algebraMap A (Localization.Away t)) q.asIdeal
  have hlt : qA < maximalIdeal A :=
    away_prime_contraction_lt_maximalIdeal (A := A) ht_mem q.asIdeal
  have hpairA :
      IsDomain (Localization.AtPrime qA) ∧ IsIntegrallyClosed (Localization.AtPrime qA) :=
    hnormal ⟨qA, inferInstance⟩ hlt
  exact normalPair_awayAtPrime_of_contracted (A := A) (t := t) q.asIdeal hpairA

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: the strong-induction
transport step from a strict prime of `Rₚ` back to a smaller-height prime of `R`. -/
lemma normalPair_strictPrime_of_localizationAtPrime_induction
    (p : PrimeSpectrum R)
    (ih :
      ∀ q : PrimeSpectrum R,
        ENat.toNat q.asIdeal.primeHeight < ENat.toNat p.asIdeal.primeHeight →
          IsDomain (Localization.AtPrime q.asIdeal) ∧
            IsIntegrallyClosed (Localization.AtPrime q.asIdeal))
    {qA : Ideal (Localization.AtPrime p.asIdeal)} [qA.IsPrime]
    (hlt : qA < maximalIdeal (Localization.AtPrime p.asIdeal)) :
    IsDomain (Localization.AtPrime qA) ∧ IsIntegrallyClosed (Localization.AtPrime qA) := by
  let qR : Ideal R := qA.under R
  haveI : qR.IsPrime := by
    simpa [qR, Ideal.under_def] using
      (Ideal.comap_isPrime (algebraMap R (Localization.AtPrime p.asIdeal)) qA)
  let q : PrimeSpectrum R := ⟨qR, inferInstance⟩
  have hltHeight : qR.primeHeight < p.asIdeal.primeHeight := by
    simpa [qR] using
      under_primeHeight_lt_of_lt_maximalIdeal_atPrime (R := R) p hlt
  have hltNat : ENat.toNat qR.primeHeight < ENat.toNat p.asIdeal.primeHeight := by
    -- Proof comment: convert the strict prime-height drop from `ℕ∞` to the natural-number
    -- induction parameter used in the main proof.
    have hltCoe :
        ((ENat.toNat qR.primeHeight : ℕ∞) < ENat.toNat p.asIdeal.primeHeight) := by
      simpa
        [ENat.coe_toNat (ne_of_lt (Ideal.primeHeight_lt_top qR)),
          ENat.coe_toNat (ne_of_lt (Ideal.primeHeight_lt_top p.asIdeal))] using hltHeight
    exact_mod_cast hltCoe
  have hpairR :
      IsDomain (Localization.AtPrime qR) ∧ IsIntegrallyClosed (Localization.AtPrime qR) :=
    ih q hltNat
  -- Proof comment: once the smaller-height contraction is normal, the canonical iterated
  -- localization comparison transports that normal pair back to the strict prime of `Rₚ`.
  exact normalPair_atPrime_of_under (R := R) p (qA := qA) hpairR

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: a local normal ring is a
normal domain at its closed point. -/
lemma normalPair_of_isNormalRing_local
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNormalRing A] :
    IsDomain A ∧ IsIntegrallyClosed A := by
  let p : PrimeSpectrum A := ⟨maximalIdeal A, inferInstance⟩
  letI : IsLocalization (maximalIdeal A).primeCompl A :=
    IsLocalization.self <| by
      intro x hx
      simpa [Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Classical.not_not] using hx
  have hpair :
      IsDomain (Localization.AtPrime p.asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := by
    -- Proof comment: `IsNormalRing` gives the normal-domain pair at every prime localization,
    -- in particular at the closed point of the local ring.
    exact ⟨isDomain_localizationAtPrime p, isIntegrallyClosed_localizationAtPrime p⟩
  -- Proof comment: localizing a local ring at its maximal ideal canonically recovers the ring.
  exact
    normalPair_of_ringEquiv
      (IsLocalization.algEquiv (maximalIdeal A).primeCompl
        (Localization.AtPrime (maximalIdeal A)) A).toRingEquiv hpair

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: a regular element of a
reduced ring stays regular on every fraction-ring subalgebra. -/
lemma isSMulRegular_subalgebra_fractionRing
    {A : Type*} [CommRing A] [IsReduced A] {x : A}
    (hxreg : IsSMulRegular A x) (S : Subalgebra A (FractionRing A)) :
    IsSMulRegular S x := by
  have hx_nd : x ∈ nonZeroDivisors A := by
    rw [mem_nonZeroDivisors_iff_right]
    intro a ha
    exact hxreg.right_eq_zero_of_smul <| by
      simpa [Algebra.smul_def, mul_comm] using ha
  have hfrac : IsSMulRegular (FractionRing A) x := by
    have hx_unit : IsUnit (algebraMap A (FractionRing A) x) :=
      IsLocalization.map_units (FractionRing A) ⟨x, hx_nd⟩
    rcases hx_unit with ⟨u, hu⟩
    have hu_reg :
        IsSMulRegular (FractionRing A) (algebraMap A (FractionRing A) x) := by
      simpa using
        (IsSMulRegular.of_mul_eq_one
          (M := FractionRing A)
          (a := ↑u⁻¹)
          (b := algebraMap A (FractionRing A) x)
          (by simpa [hu] using Units.inv_mul u))
    exact
      IsSMulRegular.of_map
        (f := algebraMap A (FractionRing A))
        (smul := fun m ↦ by simp [Algebra.smul_def]) hu_reg
  -- Proof comment: restrict the ambient fraction-ring regularity along the subalgebra inclusion.
  change IsSMulRegular S.toSubmodule x
  simpa using IsSMulRegular.submodule S.toSubmodule x hfrac

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: if `A_q` is a normal
domain, then an element of `FractionRing A` integral over `A` already comes from `A_q` after
passing to the iterated localization at `q`. -/
lemma existsAtPrimePreimageInIteratedLocalization_of_normalPair
    {A : Type*} [CommRing A] [IsReduced A]
    (z : FractionRing A) (hz : IsIntegral A z) (q : PrimeSpectrum A)
    (hpair :
      IsDomain (Localization.AtPrime q.asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime q.asIdeal)) :
    let Aq := Localization.AtPrime q.asIdeal
    let Tp := Localization (Algebra.algebraMapSubmonoid (FractionRing A) q.asIdeal.primeCompl)
    ∃ a : Aq, algebraMap (FractionRing A) Tp z = algebraMap Aq Tp a := by
  let Aq := Localization.AtPrime q.asIdeal
  let Tp := Localization (Algebra.algebraMapSubmonoid (FractionRing A) q.asIdeal.primeCompl)
  letI : IsDomain Aq := hpair.1
  letI : IsIntegrallyClosed Aq := hpair.2
  have hAq_nzd :
      Algebra.algebraMapSubmonoid Aq (nonZeroDivisors A) ≤ nonZeroDivisors Aq := by
    intro y hy
    rcases hy with ⟨a, ha, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hzero
    obtain ⟨s, hs⟩ :=
      (IsLocalization.map_eq_zero_iff q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal) a).1
        hzero
    have hs0 : (s : A) = 0 := by
      exact (mem_nonZeroDivisors_iff_right.1 ha) _ (by simpa [mul_comm] using hs)
    exact s.2 (hs0 ▸ Ideal.zero_mem q.asIdeal)
  have hTpLoc :
      IsLocalization (Algebra.algebraMapSubmonoid Aq (nonZeroDivisors A)) Tp := by
    dsimp [Aq, Tp]
    exact atPrime_totalFraction_isLocalization (R := A) q.asIdeal
  let M := Algebra.algebraMapSubmonoid Aq (nonZeroDivisors A)
  letI : IsLocalization M Tp := hTpLoc
  have hprimeCompl_map :
      q.asIdeal.primeCompl ≤
        (Algebra.algebraMapSubmonoid (FractionRing A) q.asIdeal.primeCompl).comap
          (algebraMap A (FractionRing A)) := by
    simpa using
      (Algebra.algebraMapSubmonoid_le_comap
        (M := q.asIdeal.primeCompl)
        (f := Algebra.ofId A (FractionRing A)))
  let mapAqTp : Aq →+* Tp :=
    IsLocalization.map Tp (algebraMap A (FractionRing A))
      hprimeCompl_map
  letI : Algebra Aq Tp := mapAqTp.toAlgebra
  letI : IsScalarTower A Aq Tp := IsScalarTower.of_algebraMap_eq' <|
    (IsLocalization.map_comp
      (S := Aq)
      (Q := Tp)
      (g := algebraMap A (FractionRing A))
      hprimeCompl_map).symm
  letI : Algebra (Localization.AtPrime q.asIdeal)
      (FractionRing (Localization.AtPrime q.asIdeal)) := OreLocalization.instAlgebra
  have hFracAq :
      IsFractionRing (Localization.AtPrime q.asIdeal)
        (FractionRing (Localization.AtPrime q.asIdeal)) := by
    exact inferInstanceAs
      (IsLocalization (nonZeroDivisors (Localization.AtPrime q.asIdeal))
        (FractionRing (Localization.AtPrime q.asIdeal)))
  letI : IsFractionRing Aq (FractionRing Aq) := hFracAq
  have hRToAqFraction :
      nonZeroDivisors A ≤
        Submonoid.comap (algebraMap A Aq) (nonZeroDivisors Aq) := by
    intro y hy
    exact hAq_nzd ⟨y, hy, rfl⟩
  let mapToAqFraction :
      FractionRing A →+* FractionRing (Localization.AtPrime q.asIdeal) :=
    IsLocalization.map (S := FractionRing A)
      (Q := FractionRing (Localization.AtPrime q.asIdeal))
      (algebraMap A Aq) hRToAqFraction
  have hzAq :
      IsIntegral Aq (mapToAqFraction z) := by
    exact
      IsIntegral.map_of_comp_eq
        (algebraMap A Aq)
        mapToAqFraction
        (IsLocalization.map_comp
          (S := FractionRing A)
          (Q := FractionRing Aq)
          hRToAqFraction).symm
        hz
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hzAq
  let mapTpToFraction : Tp →+* FractionRing (Localization.AtPrime q.asIdeal) :=
    IsLocalization.lift (S := Tp) (P := FractionRing (Localization.AtPrime q.asIdeal))
      (fun y : M => IsLocalization.map_units (FractionRing (Localization.AtPrime q.asIdeal))
        ⟨(y : Aq), hAq_nzd y.2⟩)
  have hcompAtPrime :
      mapTpToFraction.comp (algebraMap Aq Tp) =
        algebraMap Aq (FractionRing (Localization.AtPrime q.asIdeal)) := by
    -- Proof comment: the lift from `Tp` to `Frac(Aq)` is chosen to commute with `Aq`.
    exact IsLocalization.lift_comp
      (M := M)
      (S := Tp)
      (P := FractionRing (Localization.AtPrime q.asIdeal))
      (g := algebraMap Aq (FractionRing (Localization.AtPrime q.asIdeal)))
      (fun y : M =>
        IsLocalization.map_units (FractionRing (Localization.AtPrime q.asIdeal))
        ⟨(y : Aq), hAq_nzd y.2⟩)
  have hcompFraction :
      mapTpToFraction.comp (algebraMap (FractionRing A) Tp) =
        mapToAqFraction := by
    -- Proof comment: both maps out of `FractionRing A` agree on the image of `A`.
    apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    ext r
    simp only [RingHom.coe_comp, Function.comp_apply]
    have hleft :
        mapTpToFraction
            ((algebraMap (FractionRing A) Tp) ((algebraMap A (FractionRing A)) r)) =
          mapTpToFraction
            ((algebraMap Aq Tp) ((algebraMap A Aq) r)) := by
      rw [← IsScalarTower.algebraMap_apply A (FractionRing A) Tp r]
      rw [← IsScalarTower.algebraMap_apply A Aq Tp r]
    calc
      mapTpToFraction
          ((algebraMap (FractionRing A) Tp) ((algebraMap A (FractionRing A)) r)) =
        mapTpToFraction
          ((algebraMap Aq Tp) ((algebraMap A Aq) r)) := hleft
      _ = (algebraMap Aq (FractionRing (Localization.AtPrime q.asIdeal)))
            ((algebraMap A Aq) r) :=
        DFunLike.congr_fun hcompAtPrime _
      _ = mapToAqFraction ((algebraMap A (FractionRing A)) r) :=
        (IsLocalization.map_eq
          (S := FractionRing A)
          (Q := FractionRing (Localization.AtPrime q.asIdeal))
          hRToAqFraction r).symm
  let algTp : Algebra Tp (FractionRing (Localization.AtPrime q.asIdeal)) :=
    mapTpToFraction.toAlgebra
  letI : Algebra Tp (FractionRing (Localization.AtPrime q.asIdeal)) := algTp
  letI : SMul Tp (FractionRing (Localization.AtPrime q.asIdeal)) := algTp.toSMul
  have hTower :
      IsScalarTower Aq Tp (FractionRing (Localization.AtPrime q.asIdeal)) := by
    -- Proof comment: this scalar tower records that the explicit lift is the algebra map from
    -- `Tp`.
    refine IsScalarTower.of_algebraMap_eq' ?_
    rw [RingHom.algebraMap_toAlgebra]
    exact hcompAtPrime.symm
  letI : IsScalarTower Aq Tp (FractionRing (Localization.AtPrime q.asIdeal)) := hTower
  have hFraction :
      @IsFractionRing Tp _ (FractionRing (Localization.AtPrime q.asIdeal)) _ algTp := by
    exact IsFractionRing.isFractionRing_of_isLocalization M Tp
      (FractionRing (Localization.AtPrime q.asIdeal)) hAq_nzd
  have hTpInj : Function.Injective mapTpToFraction := by
    -- Proof comment: the canonical map from `Tp` into `Frac(Aq)` is injective.
    have hinjAlg : Function.Injective
        ((@algebraMap Tp (FractionRing (Localization.AtPrime q.asIdeal)) _ _ algTp) :
          Tp → FractionRing (Localization.AtPrime q.asIdeal)) :=
      @IsFractionRing.injective Tp _ (FractionRing (Localization.AtPrime q.asIdeal)) _ algTp
        hFraction
    intro x y hxy
    exact hinjAlg (by simpa [RingHom.algebraMap_toAlgebra, algTp] using hxy)
  refine ⟨a, ?_⟩
  apply hTpInj
  calc
    mapTpToFraction (algebraMap (FractionRing A) Tp z) = mapToAqFraction z := by
      exact DFunLike.congr_fun hcompFraction z
    _ = algebraMap Aq (FractionRing (Localization.AtPrime q.asIdeal)) a := ha.symm
    _ = mapTpToFraction (algebraMap Aq Tp a) := by
      exact (DFunLike.congr_fun hcompAtPrime a).symm

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: localizing a subalgebra
`S ≤ FractionRing A` at a prime complement maps injectively into the corresponding iterated
localization of `FractionRing A`. -/
lemma localizedSubalgebraMap_injective
    {A : Type*} [CommRing A] [IsReduced A]
    (S : Subalgebra A (FractionRing A)) (q : PrimeSpectrum A) :
    let Sq := Localization (Algebra.algebraMapSubmonoid S q.asIdeal.primeCompl)
    let Tp := Localization (Algebra.algebraMapSubmonoid (FractionRing A) q.asIdeal.primeCompl)
    let j : Sq →+* Tp :=
      IsLocalization.map Tp (algebraMap S (FractionRing A)) <|
        by
          simpa using
            (Algebra.algebraMapSubmonoid_le_comap
              (M := q.asIdeal.primeCompl)
              (f := IsScalarTower.toAlgHom A S (FractionRing A)))
    Function.Injective j := by
  dsimp
  letI :
      IsLocalization
        ((Algebra.algebraMapSubmonoid S q.asIdeal.primeCompl).map
          (algebraMap S (FractionRing A)))
        (Localization (Algebra.algebraMapSubmonoid (FractionRing A) q.asIdeal.primeCompl)) := by
    simpa using
      (inferInstance :
        IsLocalization
          ((Algebra.algebraMapSubmonoid S q.asIdeal.primeCompl).map
            (IsScalarTower.toAlgHom A S (FractionRing A)).toRingHom)
          (Localization (Algebra.algebraMapSubmonoid (FractionRing A) q.asIdeal.primeCompl)))
  exact
    IsLocalization.map_injective_of_injective
      (M := Algebra.algebraMapSubmonoid S q.asIdeal.primeCompl)
      (S := Localization (Algebra.algebraMapSubmonoid S q.asIdeal.primeCompl))
      (Q := Localization (Algebra.algebraMapSubmonoid (FractionRing A) q.asIdeal.primeCompl))
      (g := algebraMap S (FractionRing A))
      Subtype.val_injective

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: if the localized image of
the adjoined generator `z` lies in the range of `f`, then every element of `S = A[z]` has
localized image in the same range. -/
lemma localizedAdjoin_range_of_generator
    {A : Type*} [CommRing A]
    {Aq : Type*} [CommRing Aq] [Algebra A Aq]
    (z : FractionRing A) (S : Subalgebra A (FractionRing A))
    (hS : S = Algebra.adjoin A ({z} : Set (FractionRing A)))
    {Sq : Type*} [CommRing Sq] [Algebra A Sq] [Algebra S Sq] [IsScalarTower A S Sq]
    [Algebra Aq Sq] [IsScalarTower A Aq Sq]
    (f : Aq →ₐ[Aq] Sq) (hz_memS : z ∈ S)
    (hz_range : algebraMap S Sq ⟨z, hz_memS⟩ ∈ f.range) :
    ∀ s : S, algebraMap S Sq s ∈ f.range := by
  intro s
  have hs_mem : (s : FractionRing A) ∈ Algebra.adjoin A ({z} : Set (FractionRing A)) := by
    simpa [hS] using s.2
  simpa using
    (Algebra.adjoin_induction
      (s := ({z} : Set (FractionRing A)))
      (p := fun x hx ↦ algebraMap S Sq ⟨x, by simpa [hS] using hx⟩ ∈ f.range)
      (fun x hx ↦ by
        rw [Set.mem_singleton_iff] at hx
        subst hx
        simpa using hz_range)
      (fun r ↦ by
        refine (AlgHom.mem_range f).2 ?_
        refine ⟨algebraMap A Aq r, ?_⟩
        calc
          f (algebraMap A Aq r) = algebraMap Aq Sq (algebraMap A Aq r) := by
            simpa using AlgHom.commutes f (algebraMap A Aq r)
          _ = algebraMap A Sq r := by
            exact (IsScalarTower.algebraMap_apply A Aq Sq r).symm
          _ = (algebraMap S Sq) (algebraMap A S r) := by
            exact IsScalarTower.algebraMap_apply A S Sq r)
      (fun x y hx hy hx' hy' ↦ by
        rcases hx' with ⟨ax, hax⟩
        rcases hy' with ⟨ay, hay⟩
        refine ⟨ax + ay, ?_⟩
        calc
          f (ax + ay) = f ax + f ay := by simp [map_add]
          _ = (algebraMap S Sq) ⟨x, by simpa [hS] using hx⟩ +
                (algebraMap S Sq) ⟨y, by simpa [hS] using hy⟩ := by
                  simpa using congrArg₂ HAdd.hAdd hax hay
          _ = (algebraMap S Sq)
                (⟨x, by simpa [hS] using hx⟩ + ⟨y, by simpa [hS] using hy⟩) := by
                  exact ((algebraMap S Sq).map_add _ _).symm
          _ = (algebraMap S Sq) ⟨x + y, by simpa [hS] using Subalgebra.add_mem _ hx hy⟩ := by
                rfl)
      (fun x y hx hy hx' hy' ↦ by
        rcases hx' with ⟨ax, hax⟩
        rcases hy' with ⟨ay, hay⟩
        refine ⟨ax * ay, ?_⟩
        calc
          f (ax * ay) = f ax * f ay := by simp [map_mul]
          _ = (algebraMap S Sq) ⟨x, by simpa [hS] using hx⟩ *
                (algebraMap S Sq) ⟨y, by simpa [hS] using hy⟩ := by
                  simpa using congrArg₂ HMul.hMul hax hay
          _ = (algebraMap S Sq)
                (⟨x, by simpa [hS] using hx⟩ * ⟨y, by simpa [hS] using hy⟩) := by
                  exact ((algebraMap S Sq).map_mul _ _).symm
          _ = (algebraMap S Sq) ⟨x * y, by simpa [hS] using Subalgebra.mul_mem _ hx hy⟩ := by
                rfl)
      hs_mem)

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: if every element of `S`
maps into the range of `f`, then the localization `f : Aq → Sq` is surjective. -/
lemma localizedMap_surjective_of_range
    {A : Type*} [CommRing A]
    {S : Type*} [CommRing S] [Algebra A S]
    {Aq : Type*} [CommRing Aq] [Algebra A Aq]
    (q : PrimeSpectrum A)
    [IsLocalization q.asIdeal.primeCompl Aq]
    {Sq : Type*} [CommRing Sq] [Algebra A Sq] [Algebra S Sq] [IsScalarTower A S Sq]
    [Algebra Aq Sq] [IsScalarTower A Aq Sq]
    [IsLocalization (Algebra.algebraMapSubmonoid S q.asIdeal.primeCompl) Sq]
    (hs_range :
      ∀ s : S,
        algebraMap S Sq s ∈
          (IsLocalization.mapₐ q.asIdeal.primeCompl Aq Aq Sq (Algebra.ofId A S)).range) :
    Function.Surjective
      (IsLocalization.mapₐ q.asIdeal.primeCompl Aq Aq Sq (Algebra.ofId A S)) := by
  let f : Aq →ₐ[Aq] Sq := IsLocalization.mapₐ q.asIdeal.primeCompl Aq Aq Sq (Algebra.ofId A S)
  letI : IsLocalization (Submonoid.map (Algebra.ofId A S).toRingHom q.asIdeal.primeCompl) Sq := by
    simpa using
      (inferInstance :
        IsLocalization (Algebra.algebraMapSubmonoid S q.asIdeal.primeCompl) Sq)
  intro y
  obtain ⟨s, m, rfl⟩ := IsLocalization.exists_mk'_eq (Algebra.algebraMapSubmonoid S q.asIdeal.primeCompl) y
  rcases hs_range s with ⟨a', ha'⟩
  rcases m with ⟨m, hm⟩
  rcases hm with ⟨t, ht, rfl⟩
  refine ⟨a' * IsLocalization.mk' Aq (1 : A) ⟨t, ht⟩, ?_⟩
  calc
    f (a' * IsLocalization.mk' Aq (1 : A) ⟨t, ht⟩)
        = f a' * IsLocalization.mk' Sq (1 : S)
            ⟨algebraMap A S t, Algebra.mem_algebraMapSubmonoid_of_mem ⟨t, ht⟩⟩ := by
              rw [map_mul]
              have hmap :=
                (IsLocalization.map_mk'
                  (S := Aq)
                  (Q := Sq)
                  (g := (Algebra.ofId A S).toRingHom)
                  (hy := q.asIdeal.primeCompl.le_comap_map)
                  (1 : A) ⟨t, ht⟩)
              simpa [f, map_mul] using
                congrArg
                  (fun u ↦
                    (IsLocalization.map Sq (Algebra.ofId A S).toRingHom q.asIdeal.primeCompl.le_comap_map) a' *
                      u)
                  hmap
    _ = IsLocalization.mk' Sq s
          ⟨algebraMap A S t, Algebra.mem_algebraMapSubmonoid_of_mem ⟨t, ht⟩⟩ := by
            have ha'_map :
                (IsLocalization.map Sq (Algebra.ofId A S).toRingHom q.asIdeal.primeCompl.le_comap_map) a' =
                  (algebraMap S Sq) s := by
              simpa [f] using ha'
            calc
              f a' * IsLocalization.mk' Sq (1 : S)
                  ⟨algebraMap A S t, Algebra.mem_algebraMapSubmonoid_of_mem ⟨t, ht⟩⟩
                  =
                (algebraMap S Sq) s * IsLocalization.mk' Sq (1 : S)
                  ⟨algebraMap A S t, Algebra.mem_algebraMapSubmonoid_of_mem ⟨t, ht⟩⟩ := by
                    simpa [f] using
                      congrArg
                        (fun u ↦ u * IsLocalization.mk' Sq (1 : S)
                          ⟨algebraMap A S t, Algebra.mem_algebraMapSubmonoid_of_mem ⟨t, ht⟩⟩)
                        ha'_map
              _ = IsLocalization.mk' Sq s
                    ⟨algebraMap A S t, Algebra.mem_algebraMapSubmonoid_of_mem ⟨t, ht⟩⟩ := by
                      rw [← IsLocalization.mk'_eq_mul_mk'_one]

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: after localizing the
simple adjoin `A[z]` at a strict prime below the closed point, the generator already comes from
the localized base, so the localized map is surjective. -/
lemma localizedModuleMap_surjective_of_ownerMapSurjective
    {R : Type*} [CommSemiring R] {M : Submonoid R}
    {B : Type*} [CommSemiring B] [Algebra R B]
    {Rₚ : Type*} [CommSemiring Rₚ] [Algebra R Rₚ] [IsLocalization M Rₚ]
    {Bₚ : Type*} [CommSemiring Bₚ] [Algebra R Bₚ] [Algebra B Bₚ] [IsScalarTower R B Bₚ]
    [Algebra Rₚ Bₚ] [IsScalarTower R Rₚ Bₚ]
    [IsLocalization (Algebra.algebraMapSubmonoid B M) Bₚ]
    (h :
      Function.Surjective (IsLocalization.mapₐ M Rₚ Rₚ Bₚ (Algebra.ofId R B))) :
    Function.Surjective (LocalizedModule.map M (Algebra.linearMap R B)) := by
  have hmap :
      Function.Surjective
        (IsLocalizedModule.map M (Algebra.linearMap R Rₚ)
          ((IsScalarTower.toAlgHom R B Bₚ).toLinearMap)
          (Algebra.linearMap R B)) := by
    simpa [IsLocalization.map_linearMap_eq_toLinearMap_mapₐ] using h
  exact
    (IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective
      (S := M)
      (g₁ := Algebra.linearMap R Rₚ)
      (g₂ := (IsScalarTower.toAlgHom R B Bₚ).toLinearMap)
      (l := Algebra.linearMap R B)).1 hmap

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: the simple intermediate
subalgebra `A[z]` inside `FractionRing A`. -/
abbrev fractionSimpleAdjoin
    (A : Type*) [CommRing A] (z : FractionRing A) : Subalgebra A (FractionRing A) :=
  Algebra.adjoin A ({z} : Set (FractionRing A))

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: once the localized image of
the generator `z` lies in the range, every element of the localized simple adjoin `A[z]` does. -/
lemma fractionSimpleAdjoin_localizedRange_of_generator
    {A : Type*} [CommRing A]
    {Aq : Type*} [CommRing Aq] [Algebra A Aq]
    (z : FractionRing A) (S : Subalgebra A (FractionRing A))
    (hS : S = fractionSimpleAdjoin A z)
    {Sq : Type*} [CommRing Sq] [Algebra A Sq] [Algebra S Sq] [IsScalarTower A S Sq]
    [Algebra Aq Sq] [IsScalarTower A Aq Sq]
    (f : Aq →ₐ[Aq] Sq) (hz_memS : z ∈ S)
    (hz_range : algebraMap S Sq ⟨z, hz_memS⟩ ∈ f.range) :
    ∀ s : S, algebraMap S Sq s ∈ f.range := by
  simpa [fractionSimpleAdjoin] using
    localizedAdjoin_range_of_generator
      (A := A)
      (Aq := Aq)
      (z := z)
      (S := S)
      (hS := hS)
      (Sq := Sq)
      (f := f)
      hz_memS
      hz_range

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: at a punctured normal
prime, the localized image of the adjoined generator `z` already comes from `A_q`. -/
lemma fractionSimpleAdjoin_localizedGenerator_mem_range_of_normalPair
    {A : Type*} [CommRing A] [IsReduced A]
    (z : FractionRing A) (S : Subalgebra A (FractionRing A))
    (hz_memS : z ∈ S) (hz : IsIntegral A z) (q : PrimeSpectrum A)
    (hnormal :
      IsDomain (Localization.AtPrime q.asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime q.asIdeal)) :
    let Aq := Localization.AtPrime q.asIdeal
    let Sq := Localization (Algebra.algebraMapSubmonoid S q.asIdeal.primeCompl)
    let fAlg : Aq →ₐ[Aq] Sq := IsLocalization.mapₐ q.asIdeal.primeCompl Aq Aq Sq (Algebra.ofId A S)
    algebraMap S Sq ⟨z, hz_memS⟩ ∈ fAlg.range := by
  let Aq := Localization.AtPrime q.asIdeal
  let Sq := Localization (Algebra.algebraMapSubmonoid S q.asIdeal.primeCompl)
  letI :
      IsLocalization (Submonoid.map (Algebra.ofId A S).toRingHom q.asIdeal.primeCompl) Sq := by
    simpa using
      (inferInstance :
        IsLocalization (Algebra.algebraMapSubmonoid S q.asIdeal.primeCompl) Sq)
  let fAlg : Aq →ₐ[Aq] Sq := IsLocalization.mapₐ q.asIdeal.primeCompl Aq Aq Sq (Algebra.ofId A S)
  let f : Aq →+* Sq :=
    IsLocalization.map Sq (Algebra.ofId A S).toRingHom q.asIdeal.primeCompl.le_comap_map
  let Tp := Localization (Algebra.algebraMapSubmonoid (FractionRing A) q.asIdeal.primeCompl)
  have hSFrac :
      Submonoid.map (Algebra.ofId A S).toRingHom q.asIdeal.primeCompl ≤
        (Algebra.algebraMapSubmonoid (FractionRing A) q.asIdeal.primeCompl).comap
          (algebraMap S (FractionRing A)) := by
    intro y hy
    rw [Submonoid.mem_comap]
    obtain ⟨x, hx, rfl⟩ : ∃ x : A, x ∈ q.asIdeal.primeCompl ∧ algebraMap A S x = y := by
      simpa [Submonoid.mem_map] using hy
    simpa using
      (Algebra.mem_algebraMapSubmonoid_of_mem
        (S := FractionRing A) (x := ⟨x, hx⟩))
  let j : Sq →+* Tp := IsLocalization.map Tp (algebraMap S (FractionRing A)) hSFrac
  letI : IsDomain Aq := hnormal.1
  letI : IsIntegrallyClosed Aq := hnormal.2
  have hpre : ∃ a : Aq, algebraMap (FractionRing A) Tp z = algebraMap Aq Tp a := by
    simpa [Aq, Tp] using
      (existsAtPrimePreimageInIteratedLocalization_of_normalPair
        (A := A) z hz q hnormal)
  have hj_inj : Function.Injective j := by
    simpa [Sq, Tp, j] using localizedSubalgebraMap_injective (A := A) S q
  have hcomp : j.comp f = algebraMap Aq Tp := by
    simpa [f, j] using
      (IsLocalization.map_comp_map
        (Q := Sq)
        (g := (Algebra.ofId A S).toRingHom)
        (hy := q.asIdeal.primeCompl.le_comap_map)
        (W := Tp)
        (l := algebraMap S (FractionRing A))
        (hl := hSFrac))
  rcases hpre with ⟨a, ha⟩
  refine (AlgHom.mem_range fAlg).2 ⟨a, ?_⟩
  apply hj_inj
  calc
    j (fAlg a) = algebraMap Aq Tp a := by
      simpa [f, fAlg] using congrArg (fun φ : Aq →+* Tp ↦ φ a) hcomp
    _ = algebraMap (FractionRing A) Tp z := ha.symm
    _ = j (algebraMap S Sq ⟨z, hz_memS⟩) := by
      symm
      simpa [j] using
        (IsLocalization.map_eq
          (S := Sq)
          (Q := Tp)
          (g := algebraMap S (FractionRing A))
          (hy := hSFrac)
          ⟨z, hz_memS⟩)

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: if the localization
`A_q` is a normal domain, then localizing the simple adjoin `A[z]` at `q` is surjective. -/
lemma fractionSimpleAdjoin_localizedMap_surjective_of_normalPair
    {A : Type*} [CommRing A] [IsReduced A]
    (z : FractionRing A) (S : Subalgebra A (FractionRing A))
    (hS : S = fractionSimpleAdjoin A z) (hz : IsIntegral A z) (q : PrimeSpectrum A)
    (hnormal :
      IsDomain (Localization.AtPrime q.asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime q.asIdeal)) :
    let Aq := Localization.AtPrime q.asIdeal
    let Sq := Localization (Algebra.algebraMapSubmonoid S q.asIdeal.primeCompl)
    Function.Surjective
      (IsLocalization.mapₐ q.asIdeal.primeCompl Aq Aq Sq (Algebra.ofId A S)) := by
  let Aq := Localization.AtPrime q.asIdeal
  let Sq := Localization (Algebra.algebraMapSubmonoid S q.asIdeal.primeCompl)
  letI :
      IsLocalization (Submonoid.map (Algebra.ofId A S).toRingHom q.asIdeal.primeCompl) Sq := by
    simpa using
      (inferInstance :
        IsLocalization (Algebra.algebraMapSubmonoid S q.asIdeal.primeCompl) Sq)
  let fAlg : Aq →ₐ[Aq] Sq := IsLocalization.mapₐ q.asIdeal.primeCompl Aq Aq Sq (Algebra.ofId A S)
  let f : Aq →+* Sq :=
    IsLocalization.map Sq (Algebra.ofId A S).toRingHom q.asIdeal.primeCompl.le_comap_map
  have hz_memS : z ∈ S := by
    rw [hS]
    exact Algebra.subset_adjoin (R := A) (a := z) (by simp)
  have hz_range : algebraMap S Sq ⟨z, hz_memS⟩ ∈ fAlg.range := by
    simpa [Aq, Sq, fAlg] using
      fractionSimpleAdjoin_localizedGenerator_mem_range_of_normalPair
        (A := A) z S hz_memS hz q hnormal
  have hs_range : ∀ s : S, algebraMap S Sq s ∈ fAlg.range := by
    exact
      fractionSimpleAdjoin_localizedRange_of_generator
        (A := A)
        (Aq := Aq)
        (z := z)
        (S := S)
        (hS := hS)
        (Sq := Sq)
        (f := fAlg)
        hz_memS
        hz_range
  exact localizedMap_surjective_of_range (A := A) (S := S) (Aq := Aq) q (Sq := Sq) hs_range

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: if every strict-prime
localization of `A → S` is surjective, then a power of the maximal ideal kills the cokernel
`S / A`. -/
lemma pow_maximalIdeal_smul_top_eq_bot_cokernel_of_punctured_surjectivity
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {S : Type*} [CommRing S] [Algebra A S] [Module.Finite A S]
    (hsurj :
      ∀ q : PrimeSpectrum A, q.asIdeal < maximalIdeal A →
        Function.Surjective
          (LocalizedModule.map q.asIdeal.primeCompl (Algebra.linearMap A S))) :
    ∃ n : ℕ,
      (maximalIdeal A) ^ n •
          (⊤ : Submodule A (S ⧸ LinearMap.range (Algebra.linearMap A S))) =
        ⊥ := by
  let φ : A →ₗ[A] S := Algebra.linearMap A S
  have hsupport :
      Module.support A (S ⧸ LinearMap.range φ) ⊆
        PrimeSpectrum.zeroLocus (maximalIdeal A) := by
    intro q hq
    rw [PrimeSpectrum.mem_zeroLocus]
    by_contra hnot
    have hq_le : q.asIdeal ≤ maximalIdeal A :=
      IsLocalRing.le_maximalIdeal_of_isPrime q.asIdeal
    have hlt : q.asIdeal < maximalIdeal A :=
      lt_of_le_of_ne hq_le fun hEq => hnot hEq.ge
    exact ((localized_surjective_iff_not_mem_support_cokernel φ q).1 (hsurj q hlt)) hq
  -- Proof comment: Lemma `10.62.4` converts punctured-support containment into uniform
  -- annihilation of the cokernel by a power of the maximal ideal.
  simpa [φ] using
    (Module.exists_pow_smul_top_eq_bot_iff_support_subset_zeroLocus
      (R := A)
      (M := S ⧸ LinearMap.range (Algebra.linearMap A S))
      (I := maximalIdeal A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal A))).2 hsupport

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: in the local depth-`≥ 2`
case, punctured normality forces the ring to be integrally closed in its fraction ring. -/
lemma isIntegrallyClosed_local_of_depth_ge_two_of_puncturedNormality
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsReduced A]
    (hdepth : (2 : WithTop ℕ) ≤ moduleDepth A A)
    (hnormal :
      ∀ q : PrimeSpectrum A, q.asIdeal < maximalIdeal A →
        IsDomain (Localization.AtPrime q.asIdeal) ∧
          IsIntegrallyClosed (Localization.AtPrime q.asIdeal)) :
    IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (K := FractionRing A)]
  intro z hz
  let S : Subalgebra A (FractionRing A) := fractionSimpleAdjoin A z
  let η : A →+* S := algebraMap A S
  have hz_memS : z ∈ S := by
    dsimp [S]
    exact Algebra.subset_adjoin (R := A) (a := z) (by simp)
  have hfiniteS : Module.Finite A S := by
    -- Proof comment: adjoining one integral fraction gives a finite intermediate `A`-algebra.
    dsimp [S]
    exact Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_singleton z) <| by
      intro w hw
      rcases Set.mem_singleton_iff.1 hw with rfl
      exact hz
  letI : Module.Finite A S := hfiniteS
  have hdepth_ne_zero : moduleDepth A A ≠ 0 := by
    intro hzero
    have hcontra := hdepth
    rw [hzero] at hcontra
    have hfalse : ¬ ((2 : WithTop ℕ) ≤ 0) := by
      norm_num
    exact hfalse hcontra
  obtain ⟨t, ht_mem, ht_reg⟩ :=
    exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero
      (R := A) (M := A) hdepth_ne_zero
  have ht_regS : IsSMulRegular S t :=
    isSMulRegular_subalgebra_fractionRing (A := A) ht_reg S
  have hmax_not_assoc : maximalIdeal A ∉ associatedPrimes A S := by
    exact
      maximalIdeal_not_mem_associatedPrimes_of_mem_maximalIdeal_of_isSMulRegular
        (R := A) (M := S) ht_mem ht_regS
  have hηinj : Function.Injective η := by
    intro a b hab
    exact
      (IsFractionRing.injective A (FractionRing A)) <|
        congrArg Subtype.val hab
  have hsurjLoc :
      ∀ q : PrimeSpectrum A, q.asIdeal < maximalIdeal A →
        Function.Surjective
          (LocalizedModule.map q.asIdeal.primeCompl (Algebra.linearMap A S)) := by
    intro q hlt
    -- Proof comment: strict-prime punctured normality collapses the localized simple adjoin.
    let Aq := Localization.AtPrime q.asIdeal
    let Sq := Localization (Algebra.algebraMapSubmonoid S q.asIdeal.primeCompl)
    have hsurj_owner :
        Function.Surjective
          (IsLocalization.mapₐ q.asIdeal.primeCompl Aq Aq Sq (Algebra.ofId A S)) := by
      simpa [S, Aq, Sq] using
        fractionSimpleAdjoin_localizedMap_surjective_of_normalPair
          (A := A) z S rfl hz q (hnormal q hlt)
    exact
      localizedModuleMap_surjective_of_ownerMapSurjective
        (R := A)
        (M := q.asIdeal.primeCompl)
        (B := S)
        (Rₚ := Aq)
        (Bₚ := Sq)
        hsurj_owner
  obtain ⟨n, hcokerQ⟩ :=
    pow_maximalIdeal_smul_top_eq_bot_cokernel_of_punctured_surjectivity
      (A := A) (S := S) hsurjLoc
  by_contra hz_not
  have hnot_surj : ¬ Function.Surjective η := by
    intro hsurj
    rcases hsurj ⟨z, hz_memS⟩ with ⟨a, ha⟩
    exact hz_not ⟨a, congrArg Subtype.val ha⟩
  have hS_not_subsingleton : ¬ Subsingleton S := by
    intro hsub
    letI : Subsingleton S := hsub
    exact hnot_surj fun s => ⟨0, Subsingleton.elim _ _⟩
  letI : Nontrivial S := not_subsingleton_iff_nontrivial.mp hS_not_subsingleton
  have hnotbij : ¬ Function.Bijective η := by
    intro hbij
    exact hnot_surj hbij.2
  have hkerPow :
      (maximalIdeal A) ^ n • (RingHom.ker η : Submodule A A) = ⊥ := by
    have hker_bot : RingHom.ker η = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot η).1 hηinj
    simpa [hker_bot]
  have hcokerRange :
      (maximalIdeal A) ^ n • (⊤ : Submodule A S) ≤ (Algebra.linearMap A S).range := by
    intro y hy
    let q : S →ₗ[A] S ⧸ LinearMap.range (Algebra.linearMap A S) :=
      Submodule.mkQ (LinearMap.range (Algebra.linearMap A S))
    have hmap :
        Submodule.map q ((maximalIdeal A) ^ n • (⊤ : Submodule A S)) =
          (maximalIdeal A) ^ n •
            (⊤ : Submodule A (S ⧸ LinearMap.range (Algebra.linearMap A S))) := by
      rw [Submodule.map_smul'', Submodule.map_top]
      rw [LinearMap.range_eq_top.2
        (Submodule.mkQ_surjective (LinearMap.range (Algebra.linearMap A S)))]
    have hyQ :
        q y ∈
          (maximalIdeal A) ^ n •
            (⊤ : Submodule A (S ⧸ LinearMap.range (Algebra.linearMap A S))) := by
      rw [← hmap]
      exact Submodule.mem_map_of_mem hy
    have hyQ0 : q y = 0 := by
      rw [hcokerQ, Submodule.mem_bot] at hyQ
      exact hyQ
    simpa [q, Submodule.Quotient.mk_eq_zero] using hyQ0
  have hExceptionalFalse : ¬ HasKollarExceptionalFiniteExtension A :=
    not_hasKollarExceptionalFiniteExtension_of_depth_ge_two
      (R := A) hdepth
  exact hExceptionalFalse <|
    (hasKollarExceptionalFiniteExtension_iff (R := A)).2
      ⟨S, inferInstance, inferInstance, hfiniteS, inferInstance, hnotbij,
        ⟨n, hkerPow, hcokerRange⟩, hmax_not_assoc⟩

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: the remaining local closing
step in Serre's criterion, reducing the target to the depth-`≥ 2` plus punctured-normality case. -/
lemma normalPair_local_of_depth_ge_two_of_puncturedNormality
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsReduced A]
    (hdepth : (2 : WithTop ℕ) ≤ moduleDepth A A)
    (hnormal :
      ∀ q : PrimeSpectrum A, q.asIdeal < maximalIdeal A →
        IsDomain (Localization.AtPrime q.asIdeal) ∧
          IsIntegrallyClosed (Localization.AtPrime q.asIdeal)) :
    IsDomain A ∧ IsIntegrallyClosed A := by
  have hclosed : IsIntegrallyClosed A :=
    isIntegrallyClosed_local_of_depth_ge_two_of_puncturedNormality
      (A := A) hdepth hnormal
  have hNormal : IsNormalRing A := by
    -- Proof comment: for reduced rings, Lemma `10.37.16` upgrades integrally closedness to
    -- normality.
    letI : Fintype (minimalPrimes A) := (minimalPrimes.finite_of_isNoetherianRing (R := A)).fintype
    exact
      ((normalRing_tfae_isIntegrallyClosed_isFiniteProductOfNormalDomains
        (R := A)).out 1 0).mp hclosed
  letI : IsNormalRing A := hNormal
  -- Proof comment: once the local ring is normal, its closed-point localization is a normal
  -- domain and hence gives the required pair.
  exact normalPair_of_isNormalRing_local (A := A)

/-- Helper for Chap10 Lemma 10 157 4 Serre s criterion for normality: the primewise normality
conclusion needed to package a reduced ring satisfying `(R₁)` and `(S₂)` as normal. -/
lemma normalPair_localizationAtPrime_of_isReduced_serreConditionR_one_serreConditionS_two
    [IsReduced R] (hR : R ⊧ (R₁)) (hS : R ⊧ (S₂)) (p : PrimeSpectrum R) :
    IsDomain (Localization.AtPrime p.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := by
  -- Route correction: first make the source height induction explicit. The only remaining
  -- unresolved ingredient is the local depth-`≥ 2` closing lemma isolated just above.
  let P : ℕ → Prop := fun n =>
    ∀ q : PrimeSpectrum R,
      ENat.toNat q.asIdeal.primeHeight = n →
        IsDomain (Localization.AtPrime q.asIdeal) ∧
          IsIntegrallyClosed (Localization.AtPrime q.asIdeal)
  have hP : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih q hqn
    by_cases hn : n ≤ 1
    · have hq_le_one : q.asIdeal.primeHeight ≤ 1 := by
        have hqCoe : ((ENat.toNat q.asIdeal.primeHeight : ℕ∞) ≤ 1) := by
          rw [hqn]
          exact_mod_cast hn
        simpa [ENat.coe_toNat (ne_of_lt (Ideal.primeHeight_lt_top q.asIdeal))] using hqCoe
      -- Proof comment: the low-height branch is exactly the `(R₁)` input.
      exact
        normalPair_localizationAtPrime_of_serreConditionR_one_of_primeHeight_le_one
          (R := R) hR q hq_le_one
    · let A := Localization.AtPrime q.asIdeal
      have hn_ge_two : 2 ≤ n := by omega
      have hq_ge_two : (2 : ℕ∞) ≤ q.asIdeal.primeHeight := by
        have hqCoe : (2 : ℕ∞) ≤ ENat.toNat q.asIdeal.primeHeight := by
          rw [hqn]
          exact_mod_cast hn_ge_two
        simpa [ENat.coe_toNat (ne_of_lt (Ideal.primeHeight_lt_top q.asIdeal))] using hqCoe
      have hdepth :
          (2 : WithTop ℕ) ≤ moduleDepth A A :=
        moduleDepth_localizationAtPrime_ge_two_of_serreConditionS_two_of_primeHeight_ge_two
          (R := R) hS q hq_ge_two
      have hstrict :
          ∀ qA : PrimeSpectrum A, qA.asIdeal < maximalIdeal A →
            IsDomain (Localization.AtPrime qA.asIdeal) ∧
              IsIntegrallyClosed (Localization.AtPrime qA.asIdeal) := by
        intro qA hlt
        have hih :
            ∀ q' : PrimeSpectrum R,
              ENat.toNat q'.asIdeal.primeHeight < ENat.toNat q.asIdeal.primeHeight →
                IsDomain (Localization.AtPrime q'.asIdeal) ∧
                  IsIntegrallyClosed (Localization.AtPrime q'.asIdeal) := by
          intro q' hltNat
          have hltNat' : ENat.toNat q'.asIdeal.primeHeight < n := by
            simpa [hqn] using hltNat
          exact ih (ENat.toNat q'.asIdeal.primeHeight) hltNat' q' rfl
        -- Proof comment: every strict prime of `Rₚ` contracts to strictly smaller height in `R`,
        -- so the induction hypothesis supplies the normal pair after transport.
        exact
          normalPair_strictPrime_of_localizationAtPrime_induction
            (R := R) q hih (qA := qA.asIdeal) hlt
      -- Proof comment: the high-height branch is now reduced to the local Serre-closing lemma.
      exact
        normalPair_local_of_depth_ge_two_of_puncturedNormality
          (A := A) hdepth hstrict
  exact hP (ENat.toNat p.asIdeal.primeHeight) p rfl

/-- Helper for Lemma 10.157.4 (Serre's criterion for normality): a reduced Noetherian ring with
`(R₁)` and `(S₂)` is normal. -/
theorem isNormalRing_of_isReduced_serreConditionR_one_serreConditionS_two
    [IsReduced R] (hR : R ⊧ (R₁)) (hS : R ⊧ (S₂)) :
    IsNormalRing R := by
  -- Proof comment: the owner `IsNormalRing` asks exactly for the primewise local normal-domain
  -- pair isolated in the preceding helper.
  refine ⟨fun p ↦ ?_⟩
  exact
    normalPair_localizationAtPrime_of_isReduced_serreConditionR_one_serreConditionS_two
      (R := R) hR hS p

/-
Domain-style sampling:
* primary domain: Serre's criterion for normality in Noetherian commutative algebra;
* sampled owner/bridge declarations:
  `IsNormalRing`,
  `SerreConditionR`,
  `SerreConditionS`,
  `SerreConditionS.moduleDepth_localizationAtPrime_ge_min`;
* best owner abstraction: the ring-level owner predicates `IsNormalRing R`,
  `SerreConditionR R 1`, and `SerreConditionS R 2`;
* primitive data vs derived API: the primitive public objects are the owner predicates above,
  while the primewise domain/integrally-closed and depth inequalities are derived local API
  already exposed by those owners.

Source/core/bridge triage:
* `source-facing`: Serre's criterion identifying normality with `(R_1)` and `(S_2)`;
* `core/canonical`: `IsNormalRing`, `SerreConditionR`, and `SerreConditionS`;
* `bridge/view`: the localized primewise clauses inside those owners.

The previous `List.TFAE` duplicated the owner-level normality and Serre-condition fields by
expanding them back into their local primewise formulations. This file now states the textbook
criterion directly at the owner level.
-/

-- Proof sketch: for `→`, unpack `IsNormalRing R` into normal localizations. Height-`≤ 1`
-- localizations are regular by the one-dimensional normal-local-domain criterion, and the
-- depth bound `S₂` comes from the standard depth estimate for normal local domains. For `←`,
-- use Lemma `10.157.3` to obtain reducedness from `(R₁)` and `(S₂)`, then combine reducedness
-- with `(R₁)` and `(S₂)` to show each localization is an integrally closed domain.
/-- Chap10 Lemma 10 157 4 (Serre's criterion for normality): for a Noetherian ring `R`, `R` is
normal if and only if it satisfies Serre's conditions `(R_1)` and `(S_2)`. -/
@[stacks 031S]
theorem isNormalRing_iff_serreConditionR_one_and_serreConditionS_two :
    IsNormalRing R ↔ R ⊧ (R₁) ∧ R ⊧ (S₂) := by
  constructor
  · intro hNormal
    letI : IsNormalRing R := hNormal
    -- Proof comment: combine the codimension-one regularity lemma with the primewise `(S₂)` proof.
    exact ⟨serreConditionR_one_of_isNormalRing (R := R), serreConditionS_two_of_isNormalRing (R := R)⟩
  · rintro ⟨hR, hS⟩
    have hWeak :=
      serreConditionR_zero_and_serreConditionS_one_of_serreConditionR_one_and_serreConditionS_two
        (R := R) hR hS
    -- Proof comment: recover reducedness from Lemma `10.157.3`, then defer the remaining local
    -- normality argument to the dedicated helper matching the source proof.
    have hReduced : IsReduced R :=
      isReduced_of_serreConditionR_zero_and_serreConditionS_one (R := R) hWeak.1 hWeak.2
    letI : IsReduced R := hReduced
    exact
      isNormalRing_of_isReduced_serreConditionR_one_serreConditionS_two
        (R := R) hR hS

end
