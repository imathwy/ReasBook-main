import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_110_7
import stacks_proof.stacks_project.Chap10.Definition_10_161_1
import stacks_proof.stacks_project.Chap10.Definition_10_162_9
import stacks_proof.stacks_project.Chap10.Example_10_119_5
import stacks_proof.stacks_project.Chap10.Lemma_10_36_2
import stacks_proof.stacks_project.Chap10.Lemma_10_112_4
import stacks_proof.stacks_project.Chap10.Lemma_10_119_3
import stacks_proof.stacks_project.Chap10.Lemma_10_119_12_Krull_Akizuki

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {R : Type u}
variable [CommRing R] [IsDomain R]

/- 
Domain-style sampling:
- primary domain: iterative finite overrings of one-dimensional semilocal Noetherian domains
  inside the canonical fraction field `FractionRing R`, together with analytic unramifiedness of
  the maximal-local
  completions that controls whether this process can continue indefinitely;
- sampled owner declarations in the same domain:
  `IsRegularRing`,
  `IsAnalyticallyUnramified`,
  `isN1Ring_of_isAnalyticallyUnramified`,
  `finitePthPowerCoefficientAdjoinSubring_completion_not_reduced`;
- best owner abstraction: each stage of the source construction should be an intermediate
  `Subalgebra R (FractionRing R)`, the whole source-facing chain should be owned by a single
  predicate on such sequences, and each finite extension step should be expressed by the canonical
  inclusion
  `Subalgebra.inclusion hle` between consecutive stages rather than by a parallel packaged ring,
  and the completion hypothesis should use the owner predicate
  `IsAnalyticallyUnramified (Localization.AtPrime m.asIdeal)` instead of a parallel
  completion-reducedness wrapper.

Source/core/bridge triage:
- `source-facing`: the sequence `R = R_0 ⊆ R_1 ⊆ R_2 ⊆ ...` of finite intermediate overrings
  discussed in the remark, the characteristic-`0` and characteristic-`p` counterexamples, and the
  stopping criterion under reduced maximal-local completions;
- `core/canonical`: the stage owner `R_n : Subalgebra R (FractionRing R)` together with the
  sequence predicate `IsFiniteSemilocalDomainOverringSequence`, the regularity owner
  `IsRegularRing (R_n)`, and the completion owner
  `IsAnalyticallyUnramified (Localization.AtPrime m.asIdeal)`;
- `bridge/view`: semilocality and dimension-one statements for each stage, the maximal-local
  regularity data used to construct `IsRegularRing (R_n)`, and the finite strict inclusion
  `Subalgebra.inclusion hle` when the next step is taken, plus the owner-form reformulation of
  Example `10.119.5` from nonreduced completion to `¬ IsAnalyticallyUnramified`.

Primitive data are the stage family `R_n : ℕ → Subalgebra R (FractionRing R)` and the finite step
morphisms between consecutive stages. Noetherianity, domain structure, and the algebra
`R_n → FractionRing R` are canonical derived owner data and should not remain packaged as separate
primitive witnesses in the public API. For the completion side, reducedness of the maximal-ideal
completion is derived bridge API from `IsAnalyticallyUnramified`; the public surface should
therefore use the owner predicate instead of a second primitive notion.
-/

/-- A remark-style sequence of finite semilocal one-dimensional overrings of `R` in its fraction
field. Each step is finite; once a stage is regular, the sequence is constant there, and otherwise
the next step is strict. -/
def IsFiniteSemilocalDomainOverringSequence
    (S : ℕ → Subalgebra R (FractionRing R)) : Prop :=
  S 0 = ⊥ ∧
    ∀ n,
      (Finite (MaximalSpectrum (S n)) ∧ ringKrullDim (S n) = 1) ∧
        ∃ hle : S n ≤ S (n + 1),
          (Subalgebra.inclusion hle).toRingHom.Finite ∧
            (IsRegularRing (S n) → S (n + 1) = S n) ∧
            (IsRegularRing (S n) ∨ S n < S (n + 1))

/-- A remark-style overring chain is already semilocal at the base: the stage condition at `0`
identifies `S 0` with the bottom subalgebra, hence with `R`. -/
theorem finite_maximalSpectrum_of_isFiniteSemilocalDomainOverringSequence
    {R : Type u} [CommRing R] [IsDomain R]
    {S : ℕ → Subalgebra R (FractionRing R)}
    (hS : IsFiniteSemilocalDomainOverringSequence S) :
    Finite (MaximalSpectrum R) := by
  let e : S 0 ≃ₐ[R] R :=
    (Subalgebra.equivOfEq (S 0) ⊥ hS.1).trans
      (Algebra.botEquivOfInjective (IsFractionRing.injective R (FractionRing R)))
  let eMax : MaximalSpectrum R ≃ MaximalSpectrum (S 0) := by
    refine
      { toFun := fun m ↦ ⟨Ideal.comap e.toRingEquiv m.asIdeal, inferInstance⟩
        invFun := fun m ↦ ⟨Ideal.map e.toRingEquiv m.asIdeal, inferInstance⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro m
      apply MaximalSpectrum.ext
      simpa using m.asIdeal.map_comap_of_surjective e.toRingEquiv e.toRingEquiv.surjective
    · intro m
      apply MaximalSpectrum.ext
      simpa using m.asIdeal.comap_map_of_bijective e.toRingEquiv e.toRingEquiv.bijective
  letI : Finite (MaximalSpectrum (S 0)) := (hS.2 0).1.1
  exact Finite.of_equiv (MaximalSpectrum (S 0)) eMax.symm

variable [IsNoetherianRing R] [Finite (MaximalSpectrum R)]

/-- Helper for Remark 10.119.6: a one-dimensional nonregular local domain has cotangent-space
dimension strictly greater than `1`. -/
lemma one_lt_finrank_cotangentSpace_of_nonregular_dim_one
    {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1) (hreg : ¬ IsRegularLocalRing A) :
    1 < Module.finrank (ResidueField A) (CotangentSpace A) := by
  by_contra hcot
  -- Proof comment: if the cotangent space had dimension at most `1`, the maximal ideal would be
  -- principal, and Kollár's principal-maximal-ideal branch would force regularity in dimension `1`.
  have hprincipal : (maximalIdeal A).IsPrincipal :=
    (IsLocalRing.finrank_cotangentSpace_le_one_iff (R := A)).mp (le_of_not_gt hcot)
  have hnotArt : ¬ IsArtinianRing A :=
    not_isArtinianRing_of_ringKrullDim_eq_one (R := A) hdim
  have hregular : IsRegularLocalRing A ∧ ringKrullDim A = 1 :=
    regular_dim_one_of_principal_maximalIdeal_and_not_artinian
      (R := A) hprincipal hnotArt
  exact hreg hregular.1

omit [IsNoetherianRing R] [Finite (MaximalSpectrum R)] in
/-- Helper for Remark 10.119.6: in a one-dimensional domain, every maximal ideal has height
`1`. -/
lemma primeHeight_maximal_eq_one_of_ringKrullDim_eq_one
    (hdim : ringKrullDim R = 1) (m : MaximalSpectrum R) :
    m.asIdeal.primeHeight = 1 := by
  have hupper' : ((m.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞) ≤ 1 := by
    -- Proof comment: Krull dimension `1` bounds the height of every prime by `1`.
    simpa [hdim] using (Ideal.primeHeight_le_ringKrullDim (I := m.asIdeal))
  have hupper : m.asIdeal.primeHeight ≤ 1 := by
    exact_mod_cast hupper'
  have hm_ne_bot : m.asIdeal ≠ ⊥ := by
    -- Proof comment: a maximal ideal equal to `0` would make the domain a field, contradicting
    -- the one-dimensional hypothesis.
    intro hm_bot
    letI : Field R := Field.ofIsUnitOrEqZero (R := R) fun a ↦ by
      by_cases ha : a = 0
      · exact Or.inr ha
      · have hspan_ne_bot : Ideal.span ({a} : Set R) ≠ ⊥ := by
          intro hspan
          exact ha (Ideal.span_singleton_eq_bot.mp hspan)
        by_cases htop : Ideal.span ({a} : Set R) = ⊤
        · exact Or.inl (Ideal.span_singleton_eq_top.mp htop)
        · have hbot : (⊥ : Ideal R) = Ideal.span ({a} : Set R) :=
            (hm_bot ▸ m.isMaximal).eq_of_le htop bot_le
          exact False.elim (hspan_ne_bot hbot.symm)
    have hzero : ringKrullDim R = 0 := ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
    have : (0 : WithBot ℕ∞) = 1 := by
      simpa [hzero] using hdim
    norm_num at this
  have hbot_height : (⊥ : Ideal R).primeHeight = 0 := by
    rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
    simp
  have hlower : (1 : ℕ∞) ≤ m.asIdeal.primeHeight := by
    -- Proof comment: the chain `(0) < m` contributes one step to the height.
    simpa [hbot_height] using
      (Ideal.primeHeight_add_one_le_of_lt
        (I := (⊥ : Ideal R)) (J := m.asIdeal) (bot_lt_iff_ne_bot.mpr hm_ne_bot))
  exact le_antisymm hupper hlower

omit [IsNoetherianRing R] [Finite (MaximalSpectrum R)] in
/-- Helper for Remark 10.119.6: localizing a one-dimensional domain at a maximal ideal preserves
Krull dimension `1`. -/
lemma ringKrullDim_localizationAtMaximal_eq_one_of_ringKrullDim_eq_one
    (hdim : ringKrullDim R = 1) (m : MaximalSpectrum R) :
    ringKrullDim (Localization.AtPrime m.asIdeal) = 1 := by
  have hm_height : ((m.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞) = 1 := by
    exact congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞))
      (primeHeight_maximal_eq_one_of_ringKrullDim_eq_one (R := R) hdim m)
  -- Proof comment: the localized closed point has height equal to the height of `m`, which is
  -- already `1` in the ambient one-dimensional domain.
  calc
    ringKrullDim (Localization.AtPrime m.asIdeal) = m.asIdeal.height := by
      simpa using
        (IsLocalization.AtPrime.ringKrullDim_eq_height
          m.asIdeal (Localization.AtPrime m.asIdeal))
    _ = m.asIdeal.primeHeight := by
      rw [Ideal.height_eq_primeHeight]
    _ = 1 := hm_height

omit [Finite (MaximalSpectrum R)] in
/-- Helper for Remark 10.119.6: a one-dimensional semilocal Noetherian domain that is not regular
has a maximal localization that is not regular. -/
lemma exists_nonregular_maximalLocalization_of_not_isRegularRing
    (hdim : ringKrullDim R = 1) (hreg : ¬ IsRegularRing R) :
    ∃ m : MaximalSpectrum R, ¬ IsRegularLocalRing (Localization.AtPrime m.asIdeal) := by
  classical
  have hbad : ∃ p : PrimeSpectrum R, ¬ IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
    by_contra hbad
    push Not at hbad
    exact hreg
      { toIsNoetherian := inferInstance
        isRegularLocalRing_atPrime := hbad }
  rcases hbad with ⟨p, hp⟩
  have hp_ne_bot : p.asIdeal ≠ ⊥ := by
    -- Proof comment: localizing a domain at the generic point gives its fraction field, which is
    -- a field and hence a regular local ring.
    intro hp_bot
    have hdim0 : ringKrullDim (Localization.AtPrime p.asIdeal) = 0 := by
      have hp_height_zero : p.asIdeal.primeHeight = 0 := by
        have hbot_height : (⊥ : Ideal R).primeHeight = 0 := by
          rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
          simp
        simpa [hp_bot] using hbot_height
      have hp_height_zero' : ((p.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞) = 0 := by
        exact congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hp_height_zero
      calc
        ringKrullDim (Localization.AtPrime p.asIdeal) = p.asIdeal.height := by
          simpa using
            (IsLocalization.AtPrime.ringKrullDim_eq_height
              p.asIdeal (Localization.AtPrime p.asIdeal))
        _ = p.asIdeal.primeHeight := by
          rw [Ideal.height_eq_primeHeight]
        _ = 0 := hp_height_zero'
    letI : Ring.KrullDimLE 0 (Localization.AtPrime p.asIdeal) :=
      ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim0
    letI : Field (Localization.AtPrime p.asIdeal) :=
      (Ring.KrullDimLE.isField_of_isDomain (R := Localization.AtPrime p.asIdeal)).toField
    have hregular : IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
      infer_instance
    exact hp <| by
      simpa using hregular
  have hupper' : ((p.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞) ≤ 1 := by
    -- Proof comment: the ambient dimension-one bound controls the height of `p`.
    simpa [hdim] using (Ideal.primeHeight_le_ringKrullDim (I := p.asIdeal))
  have hupper : p.asIdeal.primeHeight ≤ 1 := by
    exact_mod_cast hupper'
  have hbot_height : (⊥ : Ideal R).primeHeight = 0 := by
    rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
    simp
  have hlower : (1 : ℕ∞) ≤ p.asIdeal.primeHeight := by
    -- Proof comment: the strict chain `(0) < p` forces positive height.
    simpa [hbot_height] using
      (Ideal.primeHeight_add_one_le_of_lt
        (I := (⊥ : Ideal R)) (J := p.asIdeal) (bot_lt_iff_ne_bot.mpr hp_ne_bot))
  have hp_height : p.asIdeal.primeHeight = 1 := le_antisymm hupper hlower
  have hne_bot : ringKrullDim R ≠ ⊥ := by
    intro hbot
    have : (1 : WithBot ℕ∞) = ⊥ := by
      simpa [hdim] using hbot
    cases this
  have hne_top : ringKrullDim R ≠ ⊤ := by
    intro htop
    have : (1 : WithBot ℕ∞) = ⊤ := by
      simpa [hdim] using htop
    cases this
  letI : FiniteRingKrullDim R :=
    (finiteRingKrullDim_iff_ne_bot_and_top (R := R)).2 ⟨hne_bot, hne_top⟩
  have hp_height' : (p.asIdeal.primeHeight : WithBot ℕ∞) = ringKrullDim R := by
    simpa [hdim] using congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hp_height
  have hp_max : p.asIdeal.IsMaximal :=
    Ideal.isMaximal_of_primeHeight_eq_ringKrullDim hp_height'
  let m : MaximalSpectrum R := ⟨p.asIdeal, hp_max⟩
  refine ⟨m, ?_⟩
  simpa [m] using hp

/-- Helper for Remark 10.119.6: in a one-dimensional nonregular local domain, Kollár's source
determinantal branch yields explicit elements `x` and `y` with `y * maximalIdeal ⊆ x *
maximalIdeal` and `y ∉ (x)`. -/
lemma exists_localized_ratio_determinantal_data_of_nonregular_dim_one_local_domain
    {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1) (hreg : ¬ IsRegularLocalRing A) :
    ∃ x y : A,
      x ∈ maximalIdeal A ∧
        IsSMulRegular A x ∧
        y ∉ Ideal.span ({x} : Set A) ∧
        ∀ t ∈ maximalIdeal A, ∃ s ∈ maximalIdeal A, y * t = x * s := by
  have hnotArt : ¬ IsArtinianRing A :=
    not_isArtinianRing_of_ringKrullDim_eq_one (R := A) hdim
  have hmax_ne_bot : maximalIdeal A ≠ ⊥ := by
    -- Proof comment: if the maximal ideal vanished, the local domain would be a field, forcing
    -- Krull dimension `0`.
    intro hbot
    have hfield : IsField A :=
      (IsLocalRing.isField_iff_maximalIdeal_eq (R := A)).2 hbot
    letI : Field A := hfield.toField
    have hzero : ringKrullDim A = 0 :=
      ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
    have : (0 : WithBot ℕ∞) = 1 := by
      simpa [hzero] using hdim
    norm_num at this
  have hJzero : maximalIdealPowTorsionIdeal A = ⊥ := by
    -- Proof comment: in a domain, an element killed by a power of the maximal ideal is already
    -- zero because some nonzero element of that power annihilates it.
    refine le_antisymm ?_ bot_le
    intro z hz
    rcases hz with ⟨n, hn⟩
    obtain ⟨a, ha_mem, ha_ne_zero⟩ := (maximalIdeal A).ne_bot_iff.mp hmax_ne_bot
    have hpow_mem : a ^ n ∈ (maximalIdeal A) ^ n :=
      Ideal.pow_mem_pow ha_mem n
    have htors : a ^ n ∈ Ideal.torsionOf A A z := hn hpow_mem
    rw [Ideal.mem_torsionOf_iff] at htors
    have hmul_zero : a ^ n * z = 0 := by
      change a ^ n • z = 0 at htors
      simpa [smul_eq_mul] using htors
    have hzero : z = 0 := by
      rcases mul_eq_zero.mp hmul_zero with hpow_zero | hz_zero
      · exact False.elim <| pow_ne_zero n ha_ne_zero hpow_zero
      · exact hz_zero
    simpa [hzero]
  have hmax_not_assoc :
      maximalIdeal A ∉ associatedPrimes A A :=
    maximalIdeal_not_mem_associatedPrimes_self_of_maximalIdealPowTorsionIdeal_eq_bot
      (R := A) hJzero
  have hdepth_ne_zero : moduleDepth A A ≠ 0 := by
    -- Proof comment: depth zero would make the maximal ideal an associated prime of the self
    -- module, contradicting the domain branch above.
    intro hzero
    exact hmax_not_assoc <|
      Module.maximalIdeal_mem_associatedPrimes_of_moduleDepth_eq_zero
        (A := A) (N := A) hzero
  have hnotDepth : ¬ ((2 : WithTop ℕ) ≤ moduleDepth A A) := by
    -- Proof comment: depth cannot exceed `dim A = 1`.
    intro hdepth
    have hdepth' : (2 : ℕ∞) ≤ moduleDepth A A := by
      simpa using hdepth
    have hdepth_le : moduleDepth A A ≤ 1 :=
      moduleDepth_self_le_one_of_ringKrullDim_eq_one (R := A) hdim
    have : (2 : ℕ∞) ≤ 1 := le_trans hdepth' hdepth_le
    norm_num at this
  obtain ⟨x, hx, hxreg⟩ :=
    exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero
      (R := A) (M := A) hdepth_ne_zero
  by_cases hx_assoc : maximalIdeal A ∈ associatedPrimes A (QuotSMulTop x A)
  · obtain ⟨y, hy_not_span, hy_mul⟩ :=
      exists_lift_outside_span_singleton_of_associated_quotSMulTop
        (R := A) hx_assoc
    rcases
      mul_maximalIdeal_into_span_singleton_dichotomy
        (R := A) (x := x) (y := y) hy_mul with
      hdet | hunit
    · exact ⟨x, y, hx, hxreg, hy_not_span, hdet⟩
    · have hprincipal :
        (maximalIdeal A).IsPrincipal :=
          maximalIdeal_isPrincipal_of_unit_multiple_branch
            (R := A) hx hxreg hy_not_span hy_mul hunit
      have hregular :
          IsRegularLocalRing A ∧ ringKrullDim A = 1 :=
        regular_dim_one_of_principal_maximalIdeal_and_not_artinian
          (R := A) hprincipal hnotArt
      exact False.elim (hreg hregular.1)
  · exact False.elim <|
      hnotDepth <|
        depth_ge_two_of_regular_element_and_maximalIdeal_not_mem_associatedPrimes_quotSMulTop
          (R := A) hx hxreg hx_assoc

omit [IsNoetherianRing R] [Finite (MaximalSpectrum R)] in
/-- Helper for Remark 10.119.6: the determinantal data from the bad maximal localization can be
cleared back to generator relations in the original ring by one finite denominator choice. -/
lemma clear_generator_relations_with_common_denominator
    (m : MaximalSpectrum R) (s : Finset R)
    {x' y' : Localization.AtPrime m.asIdeal}
    {coeff' : {r // r ∈ s} → Localization.AtPrime m.asIdeal}
    (hrel : ∀ i, y' * algebraMap R (Localization.AtPrime m.asIdeal) i.1 = x' * coeff' i) :
    ∃ x y : R,
      ∃ coeff : {r // r ∈ s} → R,
        ∃ ux uy ucoeff : m.asIdeal.primeCompl,
          algebraMap R (Localization.AtPrime m.asIdeal) x =
              algebraMap R (Localization.AtPrime m.asIdeal) (ux : R) * x' ∧
            algebraMap R (Localization.AtPrime m.asIdeal) y =
              algebraMap R (Localization.AtPrime m.asIdeal) (uy : R) * y' ∧
            (∀ i,
              algebraMap R (Localization.AtPrime m.asIdeal) (coeff i) =
                algebraMap R (Localization.AtPrime m.asIdeal) (ucoeff : R) * coeff' i) ∧
            ∀ i, y * i.1 = x * coeff i := by
  classical
  let Rp := Localization.AtPrime m.asIdeal
  obtain ⟨aX, sX, hsX⟩ := IsLocalization.exists_mk'_eq m.asIdeal.primeCompl x'
  obtain ⟨aY, sY, hsY⟩ := IsLocalization.exists_mk'_eq m.asIdeal.primeCompl y'
  choose aCoeff sCoeff hsCoeff using
    fun i : {r // r ∈ s} ↦
      IsLocalization.exists_mk'_eq m.asIdeal.primeCompl (coeff' i)
  let ucoeff : m.asIdeal.primeCompl := s.attach.prod sCoeff
  let ux : m.asIdeal.primeCompl := sX * sY
  let uy : m.asIdeal.primeCompl := ux * ucoeff
  let tail : {r // r ∈ s} → m.asIdeal.primeCompl := fun i ↦ (s.attach.erase i).prod sCoeff
  let x : R := aX * sY
  let y : R := aY * sX * (ucoeff : R)
  let coeff : {r // r ∈ s} → R := fun i ↦ aCoeff i * (tail i : R)
  have hsX_mul :
      algebraMap R Rp aX = x' * algebraMap R Rp (sX : R) := by
    exact (IsLocalization.mk'_eq_iff_eq_mul (S := Rp) (x := aX) (y := sX) (z := x')).mp hsX
  have hsY_mul :
      algebraMap R Rp aY = y' * algebraMap R Rp (sY : R) := by
    exact (IsLocalization.mk'_eq_iff_eq_mul (S := Rp) (x := aY) (y := sY) (z := y')).mp hsY
  have hsCoeff_mul :
      ∀ i,
        algebraMap R Rp (aCoeff i) = coeff' i * algebraMap R Rp (sCoeff i : R) := by
    intro i
    exact
      (IsLocalization.mk'_eq_iff_eq_mul
        (S := Rp) (x := aCoeff i) (y := sCoeff i) (z := coeff' i)).mp (hsCoeff i)
  have hscale_x :
      algebraMap R Rp x = algebraMap R Rp (ux : R) * x' := by
    -- Proof comment: clear the denominator of `x'` by multiplying only with the denominator of
    -- `y'`; the source relation will supply the missing complementary factor later.
    calc
      algebraMap R Rp x = algebraMap R Rp aX * algebraMap R Rp (sY : R) := by
        simp [x, Rp, map_mul]
      _ = (x' * algebraMap R Rp (sX : R)) * algebraMap R Rp (sY : R) := by
        rw [hsX_mul]
      _ = algebraMap R Rp (ux : R) * x' := by
        simp [ux, Rp, map_mul, mul_left_comm, mul_comm]
  have hscale_y :
      algebraMap R Rp y = algebraMap R Rp (uy : R) * y' := by
    -- Proof comment: `y` absorbs the common product of coefficient denominators, so one scaled
    -- localization identity serves every generator relation at once.
    calc
      algebraMap R Rp y =
          algebraMap R Rp aY * algebraMap R Rp (sX : R) *
            algebraMap R Rp (ucoeff : R) := by
          simp [y, Rp, map_mul, mul_assoc]
      _ =
          (y' * algebraMap R Rp (sY : R)) * algebraMap R Rp (sX : R) *
            algebraMap R Rp (ucoeff : R) := by
          rw [hsY_mul]
      _ = algebraMap R Rp (uy : R) * y' := by
          simp [uy, ux, ucoeff, Rp, map_mul, mul_assoc, mul_left_comm, mul_comm]
  have hscale_coeff :
      ∀ i,
        algebraMap R Rp (coeff i) = algebraMap R Rp (ucoeff : R) * coeff' i := by
    intro i
    have hucoeff :
        ucoeff = sCoeff i * tail i := by
      -- Proof comment: split the common coefficient denominator into the distinguished factor for
      -- `i` and the product of the remaining factors.
      simp [ucoeff, tail, Finset.mul_prod_erase]
    calc
      algebraMap R Rp (coeff i) =
          algebraMap R Rp (aCoeff i) * algebraMap R Rp (tail i : R) := by
        simp [coeff, Rp, map_mul]
      _ = (coeff' i * algebraMap R Rp (sCoeff i : R)) * algebraMap R Rp (tail i : R) := by
        rw [hsCoeff_mul i]
      _ = algebraMap R Rp (ucoeff : R) * coeff' i := by
        rw [hucoeff]
        simp [Rp, map_mul, mul_left_comm, mul_comm]
  have hrel_cleared : ∀ i, y * i.1 = x * coeff i := by
    intro i
    have hinj : Function.Injective (algebraMap R Rp) :=
      IsLocalization.injective Rp m.asIdeal.primeCompl_le_nonZeroDivisors
    apply hinj
    -- Proof comment: after the scaling identities are fixed, the local relation becomes a single
    -- equality in the localization whose two sides are images of the desired equation in `R`.
    calc
      algebraMap R Rp (y * i.1) = algebraMap R Rp y * algebraMap R Rp i.1 := by
        rw [map_mul]
      _ = (algebraMap R Rp (uy : R) * y') * algebraMap R Rp i.1 := by
        rw [hscale_y]
      _ = algebraMap R Rp (uy : R) * (y' * algebraMap R Rp i.1) := by
        simp [mul_assoc]
      _ = algebraMap R Rp (uy : R) * (x' * coeff' i) := by
        rw [hrel i]
      _ = algebraMap R Rp x * algebraMap R Rp (coeff i) := by
        rw [hscale_x, hscale_coeff i]
        simp [uy, ux, ucoeff, Rp, map_mul, mul_assoc, mul_left_comm, mul_comm]
      _ = algebraMap R Rp (x * coeff i) := by
        simpa [x, Rp, map_mul, mul_assoc]
  exact ⟨x, y, coeff, ux, uy, ucoeff, hscale_x, hscale_y, hscale_coeff, hrel_cleared⟩

omit [IsDomain R] [IsNoetherianRing R] [Finite (MaximalSpectrum R)] in
/-- Helper for Remark 10.119.6: if a numerator localizes to a prime-complement multiple of an
element of the localized maximal ideal, then the numerator already lies in the original maximal
ideal. -/
lemma mem_maximal_of_scaled_localized_mem
    (m : MaximalSpectrum R) {z : R} {z' : Localization.AtPrime m.asIdeal}
    {u : m.asIdeal.primeCompl}
    (hz' : z' ∈ IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal))
    (hscale :
      algebraMap R (Localization.AtPrime m.asIdeal) z =
        algebraMap R (Localization.AtPrime m.asIdeal) (u : R) * z') :
    z ∈ m.asIdeal := by
  let Rp := Localization.AtPrime m.asIdeal
  have hz_map : algebraMap R Rp z ∈ IsLocalRing.maximalIdeal Rp := by
    -- Proof comment: multiplying a maximal-ideal element by a unit coming from the localization
    -- denominator still leaves it inside the maximal ideal.
    rw [hscale]
    exact Ideal.mul_mem_left _ _ hz'
  exact
    (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (S := Rp) (I := m.asIdeal) z).mp hz_map

omit [IsDomain R] [IsNoetherianRing R] [Finite (MaximalSpectrum R)] in
/-- Helper for Remark 10.119.6: principal-ideal non-membership descends from the bad maximal
localization once `x` and `y` differ from `x'` and `y'` only by prime-complement factors. -/
lemma not_mem_span_singleton_of_scaled_localized_not_mem
    (m : MaximalSpectrum R) {x y : R}
    {x' y' : Localization.AtPrime m.asIdeal}
    {ux uy : m.asIdeal.primeCompl}
    (hy' : y' ∉ Ideal.span ({x'} : Set (Localization.AtPrime m.asIdeal)))
    (hx :
      algebraMap R (Localization.AtPrime m.asIdeal) x =
        algebraMap R (Localization.AtPrime m.asIdeal) (ux : R) * x')
    (hy :
      algebraMap R (Localization.AtPrime m.asIdeal) y =
        algebraMap R (Localization.AtPrime m.asIdeal) (uy : R) * y') :
    y ∉ Ideal.span ({x} : Set R) := by
  let Rp := Localization.AtPrime m.asIdeal
  intro hy_span
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hy_span
  have hmap :
      algebraMap R Rp y = algebraMap R Rp x * algebraMap R Rp c := by
    rw [hc, map_mul]
  rw [hy, hx] at hmap
  rcases IsLocalization.map_units Rp uy with ⟨uyUnit, huyUnit⟩
  have hy'_span : y' ∈ Ideal.span ({x'} : Set Rp) := by
    refine Ideal.mem_span_singleton.mpr ?_
    refine ⟨algebraMap R Rp c * algebraMap R Rp (ux : R) * ↑(uyUnit⁻¹), ?_⟩
    -- Proof comment: multiply the localized principal-ideal relation by the inverse of the
    -- denominator unit for `y`, then rearrange in the commutative localization.
    calc
      y' = ↑(uyUnit⁻¹) * (↑uyUnit * y') := by
        simp
      _ = ↑(uyUnit⁻¹) * (algebraMap R Rp (uy : R) * y') := by
        rw [huyUnit]
      _ = ↑(uyUnit⁻¹) * ((algebraMap R Rp (ux : R) * x') * algebraMap R Rp c) := by
        rw [hmap]
      _ = x' * (algebraMap R Rp c * algebraMap R Rp (ux : R) * ↑(uyUnit⁻¹)) := by
        simp [mul_left_comm, mul_comm]
  exact hy' hy'_span

omit [Finite (MaximalSpectrum R)] in
/-- Helper for Remark 10.119.6: the determinantal data from the bad maximal localization can be
cleared back to a finite generating set of the original maximal ideal. -/
lemma clear_localized_determinantal_coefficients_on_generators
    (hdim : ringKrullDim R = 1) (m : MaximalSpectrum R)
    (hreg : ¬ IsRegularLocalRing (Localization.AtPrime m.asIdeal))
    (s : Finset R) (hs : Ideal.span (↑s : Set R) = m.asIdeal) :
    ∃ x y : R,
      x ∈ m.asIdeal ∧
        x ≠ 0 ∧
        y ∉ Ideal.span ({x} : Set R) ∧
        ∃ coeff : {r // r ∈ s} → R,
          (∀ i, coeff i ∈ m.asIdeal) ∧
            ∀ i, y * i.1 = x * coeff i := by
  classical
  let Rp := Localization.AtPrime m.asIdeal
  -- Route correction: the source-faithful next step is still the finite-generator denominator
  -- clearing in `Localization.AtPrime m`. The ideal-span closure is now isolated below, so the
  -- remaining work is to descend the local ratio data and then reflect maximal-ideal membership
  -- and principal-ideal non-membership separately.
  obtain ⟨x', y', hx'_mem, hx'_reg, hy'_not_span, hdet⟩ :=
    exists_localized_ratio_determinantal_data_of_nonregular_dim_one_local_domain
      (A := Rp)
      (ringKrullDim_localizationAtMaximal_eq_one_of_ringKrullDim_eq_one
        (R := R) hdim m)
      hreg
  choose coeff' hcoeff'_mem hrel' using
    fun i : {r // r ∈ s} ↦ by
      have hi_mem : i.1 ∈ m.asIdeal := by
        rw [← hs]
        exact Ideal.subset_span i.2
      have hi_mem_loc :
          algebraMap R Rp i.1 ∈ IsLocalRing.maximalIdeal Rp := by
        exact
          (IsLocalization.AtPrime.to_map_mem_maximal_iff
            (S := Rp) (I := m.asIdeal) i.1).mpr hi_mem
      simpa using hdet (algebraMap R Rp i.1) hi_mem_loc
  obtain ⟨x, y, coeff, ux, uy, ucoeff, hscale_x, hscale_y, hscale_coeff, hrel⟩ :=
    clear_generator_relations_with_common_denominator
      (R := R) m s (x' := x') (y' := y') (coeff' := coeff') hrel'
  have hx_mem : x ∈ m.asIdeal :=
    mem_maximal_of_scaled_localized_mem
      (R := R) m hx'_mem hscale_x
  have hcoeff_mem : ∀ i, coeff i ∈ m.asIdeal := by
    intro i
    exact
      mem_maximal_of_scaled_localized_mem
        (R := R) m (hcoeff'_mem i) (hscale_coeff i)
  have hx'_ne : x' ≠ 0 := by
    have hnot_regular_zero : ¬ IsSMulRegular Rp (0 : Rp) :=
      IsSMulRegular.not_zero (M := Rp)
    intro hx'_zero
    exact hnot_regular_zero (hx'_zero ▸ hx'_reg)
  have hx_ne : x ≠ 0 := by
    intro hx_zero
    rcases IsLocalization.map_units Rp ux with ⟨uxUnit, huxUnit⟩
    have hx'_zero : x' = 0 := by
      have hx_map_zero :
          algebraMap R Rp (ux : R) * x' = 0 := by
        simpa [hx_zero] using hscale_x
      calc
        x' = ↑(uxUnit⁻¹) * (↑uxUnit * x') := by
          simp
        _ = ↑(uxUnit⁻¹) * (algebraMap R Rp (ux : R) * x') := by
          rw [huxUnit]
        _ = 0 := by
          rw [hx_map_zero, mul_zero]
    exact hx'_ne hx'_zero
  have hy_not_span : y ∉ Ideal.span ({x} : Set R) :=
    not_mem_span_singleton_of_scaled_localized_not_mem
      (R := R) m hy'_not_span hscale_x hscale_y
  exact ⟨x, y, hx_mem, hx_ne, hy_not_span, coeff, hcoeff_mem, hrel⟩

omit [IsDomain R] [IsNoetherianRing R] [Finite (MaximalSpectrum R)] in
/-- Helper for Remark 10.119.6: generator-level determinantal relations extend to the full ideal
they generate. -/
lemma determinantal_relation_of_generator_relations
    (s : Finset R) {x y : R} {coeff : {r // r ∈ s} → R} {I : Ideal R}
    (hI : Ideal.span (↑s : Set R) = I)
    (hcoeff_mem : ∀ i, coeff i ∈ I)
    (hrel : ∀ i, y * i.1 = x * coeff i) :
    ∀ t ∈ I, ∃ u ∈ I, y * t = x * u := by
  intro t ht
  subst hI
  -- Proof comment: `Ideal.span` is a submodule span, so one span induction closes the ideal-level
  -- relation from the generator equalities.
  refine Submodule.span_induction
    (p := fun z _ ↦ ∃ u ∈ Ideal.span (↑s : Set R), y * z = x * u)
    ?_ ?_ ?_ ?_ ht
  · intro z hz
    let i : {r // r ∈ s} := ⟨z, hz⟩
    exact ⟨coeff i, hcoeff_mem i, hrel i⟩
  · exact ⟨0, Ideal.zero_mem _, by simp⟩
  · rintro z₁ z₂ _ _ ⟨u₁, hu₁, hu₁eq⟩ ⟨u₂, hu₂, hu₂eq⟩
    refine ⟨u₁ + u₂, Ideal.add_mem _ hu₁ hu₂, ?_⟩
    calc
      y * (z₁ + z₂) = y * z₁ + y * z₂ := by ring
      _ = x * u₁ + x * u₂ := by rw [hu₁eq, hu₂eq]
      _ = x * (u₁ + u₂) := by ring
  · intro a z _ ⟨u, hu, hueq⟩
    refine ⟨a * u, Ideal.mul_mem_left (I := Ideal.span (↑s : Set R)) a hu, ?_⟩
    calc
      y * (a * z) = a * (y * z) := by ring
      _ = a * (x * u) := by rw [hueq]
      _ = x * (a * u) := by ring

omit [Finite (MaximalSpectrum R)] in
/-- Helper for Remark 10.119.6: the determinantal data from the bad maximal localization can be
cleared back to elements of the original semilocal domain. -/
lemma exists_determinantal_ratio_data_of_nonregular_maximalLocalization
    (hdim : ringKrullDim R = 1) (m : MaximalSpectrum R)
    (hreg : ¬ IsRegularLocalRing (Localization.AtPrime m.asIdeal)) :
    ∃ x y : R,
      x ∈ m.asIdeal ∧
        x ≠ 0 ∧
        y ∉ Ideal.span ({x} : Set R) ∧
        ∀ t ∈ m.asIdeal, ∃ s ∈ m.asIdeal, y * t = x * s := by
  obtain ⟨t, ht_finite, ht_span⟩ := Submodule.fg_def.mp (m.asIdeal.fg_of_isNoetherianRing)
  let s : Finset R := ht_finite.toFinset
  have hs_span : Ideal.span (↑s : Set R) = m.asIdeal := by
    simpa [s] using ht_span
  obtain ⟨x, y, hx_mem, hx_ne, hy_not_span, coeff, hcoeff_mem, hrel⟩ :=
    clear_localized_determinantal_coefficients_on_generators
      (R := R) hdim m hreg s hs_span
  refine ⟨x, y, hx_mem, hx_ne, hy_not_span, ?_⟩
  -- Proof comment: once the generator equations are descended, one span induction upgrades them
  -- to the whole ideal `m`.
  exact determinantal_relation_of_generator_relations
    (R := R) s hs_span hcoeff_mem hrel

omit [IsNoetherianRing R] [Finite (MaximalSpectrum R)] in
/-- Helper for Remark 10.119.6: the descended determinantal relation makes the ambient fraction
ring ratio `y / x` send every generator `t / x` of the source submodule back into that same
submodule. -/
lemma fractionRing_ratio_mul_eq_of_determinantal_ratio_data
    (m : MaximalSpectrum R) {x y : R} (hx_ne : x ≠ 0)
    (hdet : ∀ t ∈ m.asIdeal, ∃ s ∈ m.asIdeal, y * t = x * s) :
    let z : FractionRing R :=
      algebraMap R (FractionRing R) y / algebraMap R (FractionRing R) x
    ∀ t ∈ m.asIdeal, ∃ s ∈ m.asIdeal,
      algebraMap R (FractionRing R) t * z = algebraMap R (FractionRing R) s := by
  intro z t ht
  rcases hdet t ht with ⟨s, hs, hys⟩
  refine ⟨s, hs, ?_⟩
  have hx_frac_ne : algebraMap R (FractionRing R) x ≠ 0 := by
    intro hx_zero
    exact hx_ne <| (IsFractionRing.injective R (FractionRing R)) <| by simpa using hx_zero
  -- Proof comment: the source relation `y * t = x * s` clears the denominator of `z = y / x`
  -- directly inside the fraction field.
  calc
    algebraMap R (FractionRing R) t * z =
        algebraMap R (FractionRing R) t *
          (algebraMap R (FractionRing R) y / algebraMap R (FractionRing R) x) := by
            rfl
    _ =
        algebraMap R (FractionRing R) (y * t) *
          (algebraMap R (FractionRing R) x)⁻¹ := by
            simp [div_eq_mul_inv, map_mul, mul_assoc, mul_left_comm]
    _ =
        algebraMap R (FractionRing R) (x * s) *
          (algebraMap R (FractionRing R) x)⁻¹ := by
            rw [hys]
    _ = algebraMap R (FractionRing R) s := by
      rw [map_mul]
      calc
        algebraMap R (FractionRing R) x *
            algebraMap R (FractionRing R) s *
            (algebraMap R (FractionRing R) x)⁻¹ =
            algebraMap R (FractionRing R) s *
              (algebraMap R (FractionRing R) x *
                (algebraMap R (FractionRing R) x)⁻¹) := by
                  ring
        _ = algebraMap R (FractionRing R) s * 1 := by
          rw [mul_inv_cancel₀ hx_frac_ne]
        _ = algebraMap R (FractionRing R) s := by simp

omit [Finite (MaximalSpectrum R)] in
/-- Helper for Remark 10.119.6: the descended determinantal relation yields a finitely generated
`R`-submodule of `FractionRing R` that contains `1` and is stable under multiplication by
`y / x`. -/
lemma ratio_fractionRing_isIntegral_of_determinantal_ratio_data
    (m : MaximalSpectrum R) {x y : R}
    (hx : x ∈ m.asIdeal) (hx_ne : x ≠ 0)
    (hdet : ∀ t ∈ m.asIdeal, ∃ s ∈ m.asIdeal, y * t = x * s) :
    let z : FractionRing R :=
      algebraMap R (FractionRing R) y / algebraMap R (FractionRing R) x
    IsIntegral R z := by
  intro z
  let invx : FractionRing R := (algebraMap R (FractionRing R) x)⁻¹
  let ψ : m.asIdeal →ₗ[R] FractionRing R :=
    (Algebra.lsmul R R (FractionRing R) invx).comp
      ((Algebra.linearMap R (FractionRing R)).comp m.asIdeal.subtype)
  let M : Submodule R (FractionRing R) := LinearMap.range ψ
  have hx_frac_ne : algebraMap R (FractionRing R) x ≠ 0 := by
    intro hx_zero
    exact hx_ne <| (IsFractionRing.injective R (FractionRing R)) <| by simpa using hx_zero
  -- Proof comment: use the canonical finite-submodule criterion with the submodule generated by
  -- the fractions `t / x` for `t ∈ m`.
  exact isIntegral_of_exists_fg_submodule_of_one_mem_of_mul_mem <| by
    refine ⟨M, ?_, ?_, ?_⟩
    · letI : Module.Finite R (m.asIdeal) :=
        Module.Finite.of_injective m.asIdeal.subtype m.asIdeal.injective_subtype
      have hfg : (Submodule.map ψ (⊤ : Submodule R m.asIdeal)).FG :=
        Submodule.FG.map ψ Module.Finite.fg_top
      have hrange : M = Submodule.map ψ (⊤ : Submodule R m.asIdeal) := by
        simpa [M] using (LinearMap.range_eq_map ψ)
      rw [hrange]
      exact hfg
    · refine ⟨⟨x, hx⟩, ?_⟩
      -- Proof comment: the chosen denominator element contributes `x / x = 1`.
      calc
        ψ ⟨x, hx⟩ = invx * algebraMap R (FractionRing R) x := by
          simp [ψ, invx, mul_comm]
        _ = 1 := by
          simpa [invx] using
            (inv_mul_cancel₀ hx_frac_ne :
              ((algebraMap R (FractionRing R) x)⁻¹) *
                algebraMap R (FractionRing R) x = 1)
    · intro w hw
      rcases hw with ⟨t, rfl⟩
      rcases
        (fractionRing_ratio_mul_eq_of_determinantal_ratio_data
          (R := R) m hx_ne hdet) t t.2 with
        ⟨s, hs, hsz⟩
      refine ⟨⟨s, hs⟩, ?_⟩
      -- Proof comment: rewrite `z * (t / x)` using the cleared relation `t * z = s`.
      calc
        ψ ⟨s, hs⟩ = algebraMap R (FractionRing R) s * invx := by
          simp [ψ, invx, mul_comm]
        _ = (algebraMap R (FractionRing R) t * z) * invx := by
          rw [hsz]
        _ = z * ψ t := by
          simp [ψ, invx, mul_assoc, mul_left_comm, mul_comm]

omit [IsNoetherianRing R] [Finite (MaximalSpectrum R)] in
/-- Helper for Remark 10.119.6: the ambient fraction ring ratio `y / x` does not already come
from `R` when `y ∉ (x)`. -/
lemma fractionRing_ratio_not_mem_range_of_not_mem_span_singleton
    {x y : R} (hx_ne : x ≠ 0) (hy : y ∉ Ideal.span ({x} : Set R)) :
    let z : FractionRing R :=
      algebraMap R (FractionRing R) y / algebraMap R (FractionRing R) x
    z ∉ Set.range (algebraMap R (FractionRing R)) := by
  intro z
  rintro ⟨r, hr⟩
  have hx_frac_ne : algebraMap R (FractionRing R) x ≠ 0 := by
    intro hx_zero
    exact hx_ne <| (IsFractionRing.injective R (FractionRing R)) <| by simpa using hx_zero
  have hyr_map :
      algebraMap R (FractionRing R) y =
        algebraMap R (FractionRing R) r * algebraMap R (FractionRing R) x := by
    -- Proof comment: multiply the identity `y / x = r` by `x` to move back to `R`.
    exact (div_eq_iff hx_frac_ne).mp <| by
      simpa [z] using hr.symm
  have hyr : r * x = y :=
    (IsFractionRing.injective R (FractionRing R)) <| by
      simpa [map_mul] using hyr_map.symm
  exact hy <| Ideal.mem_span_singleton'.2 ⟨r, hyr⟩

omit [IsNoetherianRing R] [Finite (MaximalSpectrum R)] in
/-- Helper for Remark 10.119.6: adjoining the ambient fraction ring ratio `y / x` is a strict
extension whenever `y ∉ (x)`. -/
lemma bot_lt_adjoin_singleton_ratio_of_not_mem_span_singleton
    {x y : R} (hx_ne : x ≠ 0) (hy : y ∉ Ideal.span ({x} : Set R)) :
    let z : FractionRing R :=
      algebraMap R (FractionRing R) y / algebraMap R (FractionRing R) x
    (⊥ : Subalgebra R (FractionRing R)) <
      Algebra.adjoin R ({z} : Set (FractionRing R)) := by
  intro z
  refine lt_of_le_of_ne bot_le ?_
  intro hEq
  have hz_mem_bot : z ∈ (⊥ : Subalgebra R (FractionRing R)) := by
    simpa [hEq] using
      (Algebra.subset_adjoin (R := R) (a := z) (Set.mem_singleton z) :
        z ∈ Algebra.adjoin R ({z} : Set (FractionRing R)))
  exact
    (fractionRing_ratio_not_mem_range_of_not_mem_span_singleton
      (R := R) hx_ne hy) <|
      Algebra.mem_bot.mp hz_mem_bot

omit [IsDomain R] [IsNoetherianRing R] [Finite (MaximalSpectrum R)] in
/-- Helper for Remark 10.119.6: once the first overring `S` is finite over `R`, the inclusion from
the bottom subalgebra is finite as well. -/
lemma finite_inclusion_bot_of_moduleFinite_subalgebra
    (S : Subalgebra R (FractionRing R))
    (h : (⊥ : Subalgebra R (FractionRing R)) < S)
    [Module.Finite R S] :
    (Subalgebra.inclusion h.le).toRingHom.Finite := by
  let e : (⊥ : Subalgebra R (FractionRing R)) ≃+* R :=
    (Algebra.botEquivOfInjective
      (R := R) (A := FractionRing R)
      (IsFractionRing.injective R (FractionRing R))).toRingEquiv
  have hcomp :
      ((Subalgebra.inclusion h.le).toRingHom.comp e.symm.toRingHom).Finite := by
    -- Proof comment: after identifying `⊥` with `R`, the inclusion map becomes the usual algebra
    -- map `R → S`.
    have hmap :
        (Subalgebra.inclusion h.le).toRingHom.comp e.symm.toRingHom = algebraMap R S := by
      ext r
      rfl
    rw [hmap]
    exact RingHom.finite_algebraMap.mpr inferInstance
  exact RingHom.Finite.of_comp_finite hcomp

omit [IsDomain R] [IsNoetherianRing R] in
/-- Helper for Remark 10.119.6: a finite subalgebra of `FractionRing R` over a semilocal base is
again semilocal. -/
lemma finite_maximalSpectrum_of_moduleFinite_fraction_subalgebra_of_semilocal
    (S : Subalgebra R (FractionRing R)) [Module.Finite R S] :
    Finite (MaximalSpectrum S) := by
  letI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  letI : Algebra.QuasiFinite R S :=
    (RingHom.quasiFinite_algebraMap : (algebraMap R S).QuasiFinite ↔ Algebra.QuasiFinite R S).mp <|
      RingHom.QuasiFinite.of_finite <| RingHom.finite_algebraMap.mpr inferInstance
  let f : MaximalSpectrum S → Σ m : MaximalSpectrum R, m.asIdeal.primesOver S := fun M ↦ by
    let m : MaximalSpectrum R := ⟨Ideal.comap (algebraMap R S) M.asIdeal,
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M.asIdeal⟩
    letI : M.asIdeal.LiesOver m.asIdeal := ⟨by
      simpa [Ideal.under_def, m]⟩
    exact ⟨m, Ideal.primesOver.mk m.asIdeal M.asIdeal⟩
  have hf : Function.Injective f := by
    intro M N hMN
    have hIdeal : M.asIdeal = N.asIdeal := by
      simpa [f] using congrArg (fun q => q.2.1) hMN
    exact MaximalSpectrum.ext hIdeal
  let _ : Fintype (MaximalSpectrum R) := Fintype.ofFinite (MaximalSpectrum R)
  let _ : ∀ m : MaximalSpectrum R, Fintype (m.asIdeal.primesOver S) := fun m ↦
    Set.Finite.fintype
      (Algebra.QuasiFinite.finite_primesOver (R := R) (S := S) m.asIdeal)
  let _ : Fintype (Σ m : MaximalSpectrum R, m.asIdeal.primesOver S) := inferInstance
  exact Finite.of_injective f hf

/-- Helper for Remark 10.119.6: the determinantal ratio data over a bad maximal localization
produces a strict finite one-dimensional semilocal overring inside `FractionRing R`. -/
lemma exists_first_step_overring_of_nonregular_localization
    (hdim : ringKrullDim R = 1) (m : MaximalSpectrum R)
    (hreg : ¬ IsRegularLocalRing (Localization.AtPrime m.asIdeal)) :
    ∃ S : Subalgebra R (FractionRing R),
      ∃ hlt : (⊥ : Subalgebra R (FractionRing R)) < S,
        (Subalgebra.inclusion hlt.le).toRingHom.Finite ∧
          Finite (MaximalSpectrum S) ∧
          ringKrullDim S = 1 := by
  -- Route correction: once the global determinantal data are descended to `R`, the first-step
  -- overring should be `R[y / x] ⊆ FractionRing R`; the remaining work is to finish that explicit
  -- construction and its finiteness/strictness/semilocality checks.
  obtain ⟨x, y, hx_mem, hx_ne, hy_not_span, hdet⟩ :=
    exists_determinantal_ratio_data_of_nonregular_maximalLocalization
      (R := R) hdim m hreg
  let z : FractionRing R :=
    algebraMap R (FractionRing R) y / algebraMap R (FractionRing R) x
  let S : Subalgebra R (FractionRing R) := Algebra.adjoin R ({z} : Set (FractionRing R))
  have hz_integral : IsIntegral R z := by
    -- Proof comment: the descended determinantal data provide the stable finite submodule needed
    -- for the standard integrality criterion.
    simpa [z] using
      ratio_fractionRing_isIntegral_of_determinantal_ratio_data
        (R := R) m hx_mem hx_ne hdet
  have hfiniteS : Module.Finite R S := by
    -- Proof comment: adjoining one integral fraction produces a finite `R`-algebra.
    dsimp [S]
    exact Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_singleton z) <| by
      intro w hw
      rcases Set.mem_singleton_iff.1 hw with rfl
      exact hz_integral
  letI : Module.Finite R S := hfiniteS
  have hlt : (⊥ : Subalgebra R (FractionRing R)) < S := by
    -- Proof comment: `y / x` cannot already lie in the image of `R`, so adjoining it is strict.
    simpa [S, z] using
      bot_lt_adjoin_singleton_ratio_of_not_mem_span_singleton
        (R := R) hx_ne hy_not_span
  have hfiniteInclusion : (Subalgebra.inclusion hlt.le).toRingHom.Finite :=
    finite_inclusion_bot_of_moduleFinite_subalgebra (R := R) S hlt
  have hfinMax : Finite (MaximalSpectrum S) :=
    finite_maximalSpectrum_of_moduleFinite_fraction_subalgebra_of_semilocal
      (R := R) S
  have hdimS : ringKrullDim S = 1 := by
    letI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
    have hinj : Function.Injective (algebraMap R S) := by
      intro a b hab
      exact
        (IsFractionRing.injective R (FractionRing R)) <|
          congrArg Subtype.val hab
    -- Proof comment: integral finite extensions inside a common fraction field preserve Krull
    -- dimension.
    simpa [hdim] using
      ringKrullDim_eq_of_injective_algebraMap_of_isIntegral
        (R := R) (S := S) hinj |>.symm
  exact ⟨S, hlt, hfiniteInclusion, hfinMax, hdimS⟩

/-- Helper for Remark 10.119.6: semilocality transports across a ring equivalence. -/
lemma finite_maximalSpectrum_of_ringEquiv
    {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    [Finite (MaximalSpectrum A)] :
    Finite (MaximalSpectrum B) := by
  let eMax : MaximalSpectrum B ≃ MaximalSpectrum A := by
    refine
      { toFun := fun m ↦ ⟨Ideal.comap e m.asIdeal, inferInstance⟩
        invFun := fun m ↦ ⟨Ideal.map e m.asIdeal, inferInstance⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro m
      apply MaximalSpectrum.ext
      simpa using m.asIdeal.map_comap_of_surjective e e.surjective
    · intro m
      apply MaximalSpectrum.ext
      simpa using m.asIdeal.comap_map_of_bijective e e.bijective
  exact Finite.of_equiv (MaximalSpectrum A) eMax.symm

omit [IsDomain R] [IsNoetherianRing R] [Finite (MaximalSpectrum R)] in
/-- Helper for Remark 10.119.6: finiteness of the bottom inclusion into an overring upgrades to
module-finiteness over the base ring. -/
lemma moduleFinite_of_finite_bottom_inclusion
    (S : Subalgebra R (FractionRing R))
    {h : (⊥ : Subalgebra R (FractionRing R)) ≤ S}
    (hfinite : (Subalgebra.inclusion h).toRingHom.Finite) :
    Module.Finite R S := by
  let e : (⊥ : Subalgebra R (FractionRing R)) ≃+* R :=
    (Algebra.botEquivOfInjective
      (R := R) (A := FractionRing R)
      (IsFractionRing.injective R (FractionRing R))).toRingEquiv
  have hcomp :
      (((Subalgebra.inclusion h).toRingHom).comp e.symm.toRingHom).Finite := by
    -- Proof comment: composing with the canonical `R ≃ ⊥` identifies the bottom inclusion with
    -- the ordinary algebra map `R → S`.
    exact RingHom.Finite.comp hfinite e.symm.finite
  have hmap :
      ((Subalgebra.inclusion h).toRingHom.comp e.symm.toRingHom) = algebraMap R S := by
    ext r
    rfl
  exact RingHom.finite_algebraMap.mp <| hmap ▸ hcomp

omit [IsNoetherianRing R] [Finite (MaximalSpectrum R)] in
/-- Helper for Remark 10.119.6: after transporting a bottom subalgebra across the canonical
fraction-field equivalence and then forgetting back to `R`, one recovers the original stage
subalgebra `T`. -/
lemma bot_map_fractionRing_algEquiv_restrictScalars_eq_self
    (T : Subalgebra R (FractionRing R)) :
    (((⊥ : Subalgebra T (FractionRing T)).map
        (FractionRing.algEquiv T (FractionRing R)).toAlgHom).restrictScalars R) = T := by
  ext z
  constructor
  · intro hz
    change z ∈ ((⊥ : Subalgebra T (FractionRing T)).map
      (FractionRing.algEquiv T (FractionRing R)).toAlgHom) at hz
    rcases Subalgebra.mem_map.mp hz with ⟨x, hx, rfl⟩
    rcases Algebra.mem_bot.mp hx with ⟨t, rfl⟩
    simpa using t.2
  · intro hz
    change z ∈ ((⊥ : Subalgebra T (FractionRing T)).map
      (FractionRing.algEquiv T (FractionRing R)).toAlgHom)
    refine Subalgebra.mem_map.mpr ?_
    refine ⟨algebraMap T (FractionRing T) ⟨z, hz⟩, ?_, ?_⟩
    · exact Algebra.mem_bot.mpr ⟨⟨z, hz⟩, rfl⟩
    · simpa using (FractionRing.algEquiv T (FractionRing R)).commutes ⟨z, hz⟩

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
omit [Finite (MaximalSpectrum R)] in
/-- Helper for Remark 10.119.6: if a one-dimensional semilocal stage `T` is not regular, applying
the first-step theorem to `T` and transporting the result back to the fixed ambient fraction field
produces a strict finite next stage. -/
lemma exists_next_ambient_stage_of_not_isRegularRing
    (hdimR : ringKrullDim R = 1)
    (T : Subalgebra R (FractionRing R))
    [Finite (MaximalSpectrum T)]
    (hdimT : ringKrullDim T = 1) (hnotregT : ¬ IsRegularRing T) :
    ∃ U : Subalgebra R (FractionRing R),
      ∃ hlt : T < U,
        (Subalgebra.inclusion hlt.le).toRingHom.Finite ∧
          Finite (MaximalSpectrum U) ∧
          ringKrullDim U = 1 := by
  letI : IsNoetherianRing ↥T :=
    Subalgebra.isNoetherianRing_of_ringKrullDim_eq_one
      (R := R) (L := FractionRing R) T hdimR
  obtain ⟨m, hm⟩ :=
    exists_nonregular_maximalLocalization_of_not_isRegularRing
      (R := T) hdimT hnotregT
  obtain ⟨A, hltA, hfiniteA, hfinMaxA, hdimA⟩ :=
    exists_first_step_overring_of_nonregular_localization
      (R := T) hdimT m hm
  let e : FractionRing ↥T ≃ₐ[↥T] FractionRing R := FractionRing.algEquiv ↥T (FractionRing R)
  let U' : Subalgebra ↥T (FractionRing R) := A.map e.toAlgHom
  let V : Subalgebra R (FractionRing R) :=
    (((⊥ : Subalgebra ↥T (FractionRing ↥T)).map e.toAlgHom).restrictScalars R :
      Subalgebra R (FractionRing R))
  let U : Subalgebra R (FractionRing R) := U'.restrictScalars R
  have hbot : V = T :=
    bot_map_fractionRing_algEquiv_restrictScalars_eq_self (R := R) T
  have hle_map : ((⊥ : Subalgebra ↥T (FractionRing ↥T)).map e.toAlgHom) ≤ U' :=
    Subalgebra.map_mono hltA.le
  have hleV : V ≤ U := by
    intro x hx
    exact hle_map hx
  have hle : T ≤ U := by
    exact hbot.symm ▸ hleV
  have hnotle_map : ¬ U' ≤ (⊥ : Subalgebra ↥T (FractionRing ↥T)).map e.toAlgHom := by
    intro hU
    have hA : A ≤ ⊥ := by
      intro x hx
      have hxU' : e x ∈ U' := by
        exact Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩
      have hxbot : e x ∈ (⊥ : Subalgebra T (FractionRing T)).map e.toAlgHom := hU hxU'
      rcases Subalgebra.mem_map.mp hxbot with ⟨y, hy, hxy⟩
      exact e.injective hxy ▸ hy
    exact hltA.2 hA
  have hnotle : ¬ U ≤ T := by
    intro hUT
    have hUT' : U' ≤ (⊥ : Subalgebra ↥T (FractionRing ↥T)).map e.toAlgHom := by
      intro x hx
      have hxU : x ∈ (U : Subalgebra R (FractionRing R)) := by
        simpa [U] using hx
      have hxT : x ∈ T := hUT hxU
      have hxT' : x ∈ V := by
        exact hbot.symm ▸ hxT
      exact hxT'
    exact hnotle_map hUT'
  have hne : T ≠ U := by
    intro hTU
    exact hnotle (hTU.ge)
  have hlt : T < U := lt_of_le_of_ne hle hne
  let eBotMap : ↥(⊥ : Subalgebra ↥T (FractionRing ↥T)) ≃+* ↥V :=
    (Subalgebra.equivMapOfInjective
      (⊥ : Subalgebra ↥T (FractionRing ↥T)) e.toAlgHom e.injective).toRingEquiv
  let eCodMap := Subalgebra.equivMapOfInjective A e.toAlgHom e.injective
  let eCod : ↥A ≃+* ↥U := eCodMap.toRingEquiv
  have hfiniteVtoU : (Subalgebra.inclusion hleV).toRingHom.Finite := by
    have hfiniteBotToA :
        (((Subalgebra.inclusion hltA.le).toRingHom).comp eBotMap.symm.toRingHom).Finite := by
      exact RingHom.Finite.comp hfiniteA eBotMap.symm.finite
    have hfiniteComp : (eCod.toRingHom.comp
        (((Subalgebra.inclusion hltA.le).toRingHom).comp eBotMap.symm.toRingHom)).Finite := by
      exact RingHom.Finite.comp eCod.finite hfiniteBotToA
    have hmapV :
      (eCod.toRingHom.comp
        (((Subalgebra.inclusion hltA.le).toRingHom).comp eBotMap.symm.toRingHom)) =
        (Subalgebra.inclusion hleV).toRingHom := by
      ext t
      rcases t with ⟨x, hx⟩
      change ↑(eBotMap (eBotMap.symm ⟨x, hx⟩)) = x
      exact congrArg Subtype.val (eBotMap.apply_symm_apply ⟨x, hx⟩)
    exact hmapV ▸ hfiniteComp
  let eTV : ↥T ≃+* ↥V := (Subalgebra.equivOfEq T V hbot.symm).toRingEquiv
  have hcompHle :
      (((Subalgebra.inclusion hle).toRingHom).comp eTV.symm.toRingHom).Finite := by
    have hmap :
        ((Subalgebra.inclusion hle).toRingHom).comp eTV.symm.toRingHom =
          (Subalgebra.inclusion hleV).toRingHom := by
      ext t
      cases t
      rfl
    exact hmap ▸ hfiniteVtoU
  have hfiniteHle : (Subalgebra.inclusion hle).toRingHom.Finite := by
    exact RingHom.Finite.of_comp_finite hcompHle
  have hfiniteU : (Subalgebra.inclusion hlt.le).toRingHom.Finite := by
    have hlt_le_eq_hle : hlt.le = hle := Subsingleton.elim _ _
    simpa [hlt_le_eq_hle] using hfiniteHle
  have hfinMaxMap : Finite (MaximalSpectrum (A.map e.toAlgHom)) :=
    finite_maximalSpectrum_of_ringEquiv eCodMap.toRingEquiv
  have hfinMaxU : Finite (MaximalSpectrum U) := by
    simpa [U, U'] using hfinMaxMap
  have hdimMap : ringKrullDim (A.map e.toAlgHom) = 1 := by
    calc
      ringKrullDim (A.map e.toAlgHom) = ringKrullDim A := by
        simpa using (ringKrullDim_eq_of_ringEquiv eCodMap.toRingEquiv).symm
      _ = 1 := hdimA
  have hdimU : ringKrullDim U = 1 := by
    simpa [U, U'] using hdimMap
  exact ⟨U, hlt, hfiniteU, hfinMaxU, hdimU⟩

omit [Finite (MaximalSpectrum R)] in
/-- Helper for Remark 10.119.6: every one-dimensional semilocal stage admits a packaged successor;
regular stages stay put, and nonregular stages enlarge strictly by the transported first-step
construction. -/
lemma exists_stage_successor_of_fraction_subalgebra
    (hdimR : ringKrullDim R = 1)
    (T : Subalgebra R (FractionRing R))
    [Finite (MaximalSpectrum T)]
    (hdimT : ringKrullDim T = 1) :
    ∃ U : Subalgebra R (FractionRing R),
      ∃ hle : T ≤ U,
        (Subalgebra.inclusion hle).toRingHom.Finite ∧
          (IsRegularRing T → U = T) ∧
          (IsRegularRing T ∨ T < U) ∧
          Finite (MaximalSpectrum U) ∧
          ringKrullDim U = 1 := by
  by_cases hreg : IsRegularRing T
  · refine ⟨T, le_rfl, ?_, ?_, ?_, inferInstance, hdimT⟩
    · simpa using (RingHom.Finite.id (A := T))
    · intro _
      rfl
    · exact Or.inl hreg
  · obtain ⟨U, hlt, hfiniteU, hfinMaxU, hdimU⟩ :=
      exists_next_ambient_stage_of_not_isRegularRing
        (R := R) hdimR T hdimT hreg
    refine ⟨U, hlt.le, hfiniteU, ?_, Or.inr hlt, hfinMaxU, hdimU⟩
    intro hregT
    exact False.elim (hreg hregT)

/-- Helper for Remark 10.119.6: a stage package records one recursive step of the finite-overring
process inside the fixed ambient fraction field. -/
structure FiniteSemilocalStagePackage where
  carrier : Subalgebra R (FractionRing R)
  finiteMax_carrier : Finite (MaximalSpectrum carrier)
  dim_carrier : ringKrullDim carrier = 1
  next : Subalgebra R (FractionRing R)
  carrier_le_next : carrier ≤ next
  finite_carrier_to_next : (Subalgebra.inclusion carrier_le_next).toRingHom.Finite
  regular_stops : IsRegularRing carrier → next = carrier
  regular_or_strict : IsRegularRing carrier ∨ carrier < next
  finiteMax_next : Finite (MaximalSpectrum next)
  dim_next : ringKrullDim next = 1

/-- Helper for Remark 10.119.6: the bottom subalgebra already carries the stage data needed to
start the recursive finite-overring process. -/
theorem exists_initial_stage_package
    (hdimR : ringKrullDim R = 1) :
    ∃ P : FiniteSemilocalStagePackage (R := R), P.carrier = ⊥ := by
  let e : (⊥ : Subalgebra R (FractionRing R)) ≃ₐ[R] R :=
    Algebra.botEquivOfInjective
      (R := R) (A := FractionRing R)
      (IsFractionRing.injective R (FractionRing R))
  letI : Finite (MaximalSpectrum (⊥ : Subalgebra R (FractionRing R))) :=
    finite_maximalSpectrum_of_ringEquiv e.toRingEquiv.symm
  have hdimBot : ringKrullDim (⊥ : Subalgebra R (FractionRing R)) = 1 := by
    calc
      ringKrullDim (⊥ : Subalgebra R (FractionRing R)) = ringKrullDim R := by
        simpa using ringKrullDim_eq_of_ringEquiv e.toRingEquiv
      _ = 1 := hdimR
  obtain ⟨U, hle, hfiniteU, hstop, hreg_or_strict, hfinMaxU, hdimU⟩ :=
    exists_stage_successor_of_fraction_subalgebra (R := R) hdimR ⊥ hdimBot
  refine ⟨{
      carrier := ⊥
      finiteMax_carrier := inferInstance
      dim_carrier := hdimBot
      next := U
      carrier_le_next := hle
      finite_carrier_to_next := hfiniteU
      regular_stops := hstop
      regular_or_strict := hreg_or_strict
      finiteMax_next := hfinMaxU
      dim_next := hdimU
    }, rfl⟩

omit [Finite (MaximalSpectrum R)] in
/-- Helper for Remark 10.119.6: once one step package is known, the same construction applied to
its successor yields the next package in the chain. -/
theorem exists_stage_package_successor
    (hdimR : ringKrullDim R = 1)
    (P : FiniteSemilocalStagePackage (R := R)) :
    ∃ Q : FiniteSemilocalStagePackage (R := R), Q.carrier = P.next := by
  letI : Finite (MaximalSpectrum ↥P.next) := P.finiteMax_next
  obtain ⟨U, hle, hfiniteU, hstop, hreg_or_strict, hfinMaxU, hdimU⟩ :=
    exists_stage_successor_of_fraction_subalgebra
      (R := R) hdimR P.next P.dim_next
  refine ⟨{
      carrier := P.next
      finiteMax_carrier := P.finiteMax_next
      dim_carrier := P.dim_next
      next := U
      carrier_le_next := hle
      finite_carrier_to_next := hfiniteU
      regular_stops := hstop
      regular_or_strict := hreg_or_strict
      finiteMax_next := hfinMaxU
      dim_next := hdimU
    }, rfl⟩

noncomputable section

/-- Remark 10.119.6: if `R` is a one-dimensional semilocal Noetherian domain and one maximal
localization `R_m` is not regular, then there exists a sequence of intermediate subalgebras
`R = R_0 ⊆ R_1 ⊆ R_2 ⊆ ...` inside `FractionRing R` such that every stage is again a
one-dimensional semilocal domain, each consecutive inclusion `R_n ⊆ R_{n+1}` is finite, and at
each stage either `R_n` is regular and the chain stabilizes there, or the next inclusion is
strict. The initial stage is the bottom subalgebra
`⊥ : Subalgebra R (FractionRing R)`. -/
@[stacks 00PC]
theorem exists_finite_semilocal_domain_extension_sequence_of_nonregular_maximalLocalization
    (hdim : ringKrullDim R = 1) (m : MaximalSpectrum R)
    (hreg : ¬ IsRegularLocalRing (Localization.AtPrime m.asIdeal)) :
    ∃ S : ℕ → Subalgebra R (FractionRing R), IsFiniteSemilocalDomainOverringSequence S := by
  classical
  let _ := m
  let _ := hreg
  obtain hinit := exists_initial_stage_package (R := R) hdim
  let package : ℕ → FiniteSemilocalStagePackage (R := R) :=
    Nat.rec (Classical.choose hinit) fun n P ↦
      Classical.choose (exists_stage_package_successor (R := R) hdim P)
  have hpackage_zero : (package 0).carrier = ⊥ := by
    exact Classical.choose_spec hinit
  have hpackage_succ :
      ∀ n, (package (n + 1)).carrier = (package n).next := by
    intro n
    simpa [package] using
      (Classical.choose_spec (exists_stage_package_successor (R := R) hdim (package n)))
  let S : ℕ → Subalgebra R (FractionRing R)
    | 0 => (package 0).carrier
    | n + 1 => (package n).next
  have hS_carrier : ∀ n, S n = (package n).carrier := by
    intro n
    cases n with
    | zero =>
        simpa [S] using hpackage_zero
    | succ n =>
        exact (hpackage_succ n).symm
  refine ⟨S, ?_⟩
  constructor
  · simpa [S] using hpackage_zero
  · intro n
    have hsrc : S n = (package n).carrier := hS_carrier n
    have hfiniteMax : Finite (MaximalSpectrum ↥(S n)) := by
      exact hsrc ▸ (package n).finiteMax_carrier
    have hdimStage : ringKrullDim ↥(S n) = 1 := by
      exact hsrc ▸ (package n).dim_carrier
    have hstop : IsRegularRing ↥(S n) → S (n + 1) = S n := by
      intro hregStage
      have hregPackage : IsRegularRing ↥((package n).carrier) := by
        exact hsrc ▸ hregStage
      calc
        S (n + 1) = (package n).next := by simp [S]
        _ = (package n).carrier := (package n).regular_stops hregPackage
        _ = S n := hsrc.symm
    have hreg_or_strict : IsRegularRing ↥(S n) ∨ S n < S (n + 1) := by
      cases (package n).regular_or_strict with
      | inl hregPackage =>
          exact Or.inl (hsrc.symm ▸ hregPackage)
      | inr hltPackage =>
          exact Or.inr (by simpa [S, hsrc] using hltPackage)
    have hcanon : S n ≤ S (n + 1) := by
      simpa [S, hsrc] using (package n).carrier_le_next
    have hcanonFinite : (Subalgebra.inclusion hcanon).toRingHom.Finite := by
      let eStage : ↥(S n) ≃+* ↥((package n).carrier) :=
        (Subalgebra.equivOfEq (S n) (package n).carrier hsrc).toRingEquiv
      have hcompFinite :
          (((Subalgebra.inclusion (package n).carrier_le_next).toRingHom).comp
            eStage.toRingHom).Finite := by
        exact RingHom.Finite.comp (package n).finite_carrier_to_next eStage.finite
      have hmap :
          ((Subalgebra.inclusion (package n).carrier_le_next).toRingHom).comp
              eStage.toRingHom =
            (Subalgebra.inclusion hcanon).toRingHom := by
        ext t
        cases t
        rfl
      exact hmap ▸ hcompFinite
    exact ⟨⟨hfiniteMax, hdimStage⟩, ⟨hcanon, hcanonFinite, hstop, hreg_or_strict⟩⟩

/-- The first-step consequence of Remark 10.119.6: if one maximal localization of `R` is not
regular, then there is already a strict finite first overring in the canonical subalgebra chain
`R = R₀ ⊂ R₁ ⊆ FractionRing R`, and that first stage is again a one-dimensional semilocal
domain. -/
theorem exists_finite_semilocal_domain_extension_of_nonregular_maximalLocalization
    (hdim : ringKrullDim R = 1) (m : MaximalSpectrum R)
    (hreg : ¬ IsRegularLocalRing (Localization.AtPrime m.asIdeal)) :
    ∃ S : Subalgebra R (FractionRing R),
      ∃ hlt : (⊥ : Subalgebra R (FractionRing R)) < S,
        (Subalgebra.inclusion hlt.le).toRingHom.Finite ∧
        Finite (MaximalSpectrum S) ∧
        ringKrullDim S = 1 := by
  -- Proof comment: the single-step theorem is exactly the first-step package extracted above from
  -- the source's determinantal branch.
  exact exists_first_step_overring_of_nonregular_localization
    (R := R) hdim m hreg

end

end
