import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_61_1 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]

open IsLocalRing PrimeSpectrum TopologicalSpace

-- Layering for this item:
-- * source-facing: infinitude of a nonempty open subset of `Spec(R)`.
-- * core/canonical owners: `Opens (PrimeSpectrum R)` for the open subset, the generic point
--   `(⊥ : PrimeSpectrum R)` of the spectrum of a domain, specialization via
--   `PrimeSpectrum.le_iff_specializes`, and the one-dimensional owner predicate
--   `Ring.KrullDimLE 1 R`.
-- * bridge/view: a finite nonempty open subset contains an open singleton by
--   `exists_isOpen_singleton_of_isOpen_finite`; since every nonempty open subset of `Spec(R)` for
--   a domain contains the generic point, that singleton must be `{⊥}`. An isolated generic point
--   is the owner-level bridge to `Ring.KrullDimLE 1 R`, contradicting `2 ≤ ringKrullDim R`.

/-- Helper for Lemma 10.61.1: an open singleton generic point contains a nonzero basic open. -/
private lemma exists_nonzero_basicOpen_eq_singleton_bot_of_isOpen_singleton_bot
    (hgenericOpen : IsOpen ({(⊥ : PrimeSpectrum R)} : Set (PrimeSpectrum R))) :
    ∃ x : R, x ≠ 0 ∧
      (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum R)) =
        ({(⊥ : PrimeSpectrum R)} : Set (PrimeSpectrum R)) := by
  -- Refine the open singleton neighborhood of the generic point to a basic open.
  have hbot_mem :
      (⊥ : PrimeSpectrum R) ∈ ({(⊥ : PrimeSpectrum R)} : Set (PrimeSpectrum R)) := by
    simp
  obtain ⟨_, ⟨x, rfl⟩, hxbot, hxsubset⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      hbot_mem
      hgenericOpen
  have hxne : x ≠ 0 := by
    -- The generic point lies in `D(x)` exactly when `x` is nonzero.
    exact (PrimeSpectrum.mem_basicOpen x (⊥ : PrimeSpectrum R)).1 hxbot
  refine ⟨x, hxne, Set.Subset.antisymm hxsubset ?_⟩
  intro p hp
  rcases Set.mem_singleton_iff.mp hp with rfl
  exact hxbot

/-- Helper for Lemma 10.61.1: if `D(x)` is the singleton generic point and the local ring is not a
field, then `x` lies in the maximal ideal. -/
private lemma mem_maximalIdeal_of_basicOpen_eq_singleton_bot {x : R}
    (hbasic :
      (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum R)) =
        ({(⊥ : PrimeSpectrum R)} : Set (PrimeSpectrum R)))
    (hmax : maximalIdeal R ≠ ⊥) :
    x ∈ maximalIdeal R := by
  let mSpec : PrimeSpectrum R := ⟨maximalIdeal R, (maximalIdeal.isMaximal R).isPrime⟩
  have hmSpec_ne : mSpec ≠ (⊥ : PrimeSpectrum R) := by
    intro hmSpec
    exact hmax <| PrimeSpectrum.ext_iff.mp hmSpec
  have hmSpec_not_mem : mSpec ∉ (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum R)) := by
    rw [hbasic]
    simpa using hmSpec_ne
  by_contra hxmem
  exact hmSpec_not_mem <| (PrimeSpectrum.mem_basicOpen x mSpec).2 hxmem

/-- Helper for Lemma 10.61.1: the Krull dimension of a nontrivial Noetherian local ring is
represented by a natural number. -/
private lemma ringKrullDim_eq_nat_of_local_noetherian_ring
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    ∃ n : ℕ, ringKrullDim A = n := by
  -- Convert the finite-dimensional local Krull dimension into an actual natural number.
  have hbot : ringKrullDim A ≠ ⊥ := ringKrullDim_ne_bot
  have htop : ringKrullDim A ≠ ⊤ := ringKrullDim_ne_top
  let n : ℕ := ((ringKrullDim A).unbot hbot).toNat
  have hneTop : (ringKrullDim A).unbot hbot ≠ ⊤ := by
    intro htop'
    exact htop <| by
      simpa [WithBot.coe_unbot] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) htop'
  have hdim' : ((ringKrullDim A).unbot hbot : WithBot ℕ∞) = n := by
    simpa [n] using
      congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
  refine ⟨n, ?_⟩
  calc
    ringKrullDim A = (ringKrullDim A).unbot hbot := by
      exact (WithBot.coe_unbot (ringKrullDim A) hbot).symm
    _ = n := hdim'

/-- Helper for Lemma 10.61.1: a positive-dimensional Noetherian local ring has an element of the
maximal ideal outside every minimal prime. -/
private lemma exists_mem_maximalIdeal_avoiding_minimalPrimes
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hpos : 0 < ringKrullDim A) :
    ∃ x ∈ maximalIdeal A, ∀ p ∈ minimalPrimes A, x ∉ p := by
  let U : Set A := ⋃ p ∈ minimalPrimes A, (p : Set A)
  have hnot_subset : ¬ (maximalIdeal A : Set A) ⊆ U := by
    -- Prime avoidance prevents the maximal ideal from being covered by the finite set of minimal
    -- primes unless the maximal ideal itself were minimal.
    intro hsubset
    obtain ⟨p, hp, hmp⟩ :=
      ((maximalIdeal A).subset_union_prime_finite
        (minimalPrimes.finite_of_isNoetherianRing A) (maximalIdeal A) (maximalIdeal A)
        fun p hp _ _ ↦ Ideal.minimalPrimes_isPrime hp).mp hsubset
    haveI : p.IsPrime := Ideal.minimalPrimes_isPrime hp
    have hpeq : p = maximalIdeal A := by
      refine le_antisymm ?_ hmp
      exact le_maximalIdeal Ideal.IsPrime.ne_top'
    have hpheight : (maximalIdeal A).primeHeight = 0 := by
      simpa [hpeq] using (Ideal.primeHeight_eq_zero_iff (I := p)).2 hp
    have hheight : (maximalIdeal A).height = 0 := by
      simpa [Ideal.height_eq_primeHeight (I := maximalIdeal A)] using hpheight
    have hheight' : ↑(maximalIdeal A).height = (0 : WithBot ℕ∞) := by
      exact_mod_cast hheight
    have hzero : ringKrullDim A = 0 := by
      calc
        ringKrullDim A = ↑(maximalIdeal A).height := by
          exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
        _ = 0 := hheight'
    exact (ne_of_gt hpos) hzero
  obtain ⟨x, hx, hxnot⟩ := Set.not_subset.mp hnot_subset
  refine ⟨x, hx, ?_⟩
  intro p hp hxp
  exact hxnot <| Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hp, hxp⟩⟩

/-- Helper for Lemma 10.61.1: an element of the quotient maximal ideal lifts to the maximal ideal
of the original local ring. -/
private lemma lift_maximalIdeal_element_from_quotient {I : Ideal R}
    [Nontrivial (R ⧸ I)] [IsLocalRing (R ⧸ I)]
    {z : R ⧸ I} (hz : z ∈ maximalIdeal (R ⧸ I)) :
    ∃ y : maximalIdeal R, Ideal.Quotient.mk I y = z := by
  let S := R ⧸ I
  have hmap :
      Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal S := by
    exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hmem : z ∈ Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) := by
    simpa [S, hmap] using hz
  obtain ⟨r, hr, hr_eq⟩ :=
    (Ideal.mem_map_iff_of_surjective (f := Ideal.Quotient.mk I)
      (hf := Ideal.Quotient.mk_surjective) (I := maximalIdeal R) (y := z)).1 hmem
  refine ⟨⟨r, hr⟩, ?_⟩
  simpa using hr_eq

/-- Helper for Lemma 10.61.1: when `x` lies in the maximal ideal and `dim R = n ≥ 2`, one can
choose a head parameter `y` with the expected one-step and two-step quotient dimension drops. -/
private lemma exists_head_parameter_with_quotient_dimension_drop {n : ℕ} {x : R}
    (hdimR : ringKrullDim R = n) (htwo : 2 ≤ n) (hx0 : x ≠ 0) (hx : x ∈ maximalIdeal R) :
    ∃ y : maximalIdeal R,
      ringKrullDim (R ⧸ Ideal.span ({(y : R)} : Set R)) = (n - 1 : ℕ) ∧
        ringKrullDim (R ⧸ Ideal.span ({(y : R), x} : Set R)) = (n - 2 : ℕ) := by
  let I : Ideal R := Ideal.span ({x} : Set R)
  let Q := R ⧸ I
  have hI_le_max : I ≤ maximalIdeal R := by
    -- The quotient ideal `(x)` is still contained in the maximal ideal.
    dsimp [I]
    exact (Ideal.span_singleton_le_iff_mem (I := maximalIdeal R) (x := x)).2 hx
  have hI_ne_top : I ≠ ⊤ := by
    -- An ideal inside the maximal ideal cannot be the unit ideal.
    intro htop
    have hmax_top : maximalIdeal R = ⊤ := top_le_iff.mp (htop ▸ hI_le_max)
    exact (maximalIdeal.isMaximal R).ne_top hmax_top
  letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hI_ne_top
  letI : IsLocalRing Q :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hx_avoid : ∀ p ∈ minimalPrimes R, x ∉ p := by
    -- In a domain the only minimal prime is `(0)`, so `x ≠ 0` avoids it.
    intro p hp hxmem
    have hp_bot : p = ⊥ := by
      simpa [IsDomain.minimalPrimes_eq_singleton_bot R] using hp
    exact hx0 <| by simpa [hp_bot] using hxmem
  have hdimQ_succ : ringKrullDim R = ringKrullDim Q + 1 := by
    -- Lemma `10.60.13` gives the exact dimension drop by a nonzero element of a domain.
    simpa [I, Q] using
      ringKrullDim_eq_ringKrullDim_quotient_span_singleton_add_one_of_not_mem_minimalPrimes
        (R := R) x hx hx_avoid
  obtain ⟨m, hdimQ_nat⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (A := Q)
  have hm_succ : m + 1 = n := by
    have hm_succ' : (((m + 1 : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞)) := by
      simpa [hdimR, hdimQ_nat] using hdimQ_succ.symm
    exact_mod_cast hm_succ'
  have hm : m = n - 1 := by
    omega
  have hdimQ : ringKrullDim Q = (n - 1 : ℕ) := by
    simpa [hdimQ_nat, hm]
  have hposQ_nat : 0 < n - 1 := by
    omega
  have hposQ : 0 < ringKrullDim Q := by
    simpa [hdimQ] using
      (show (0 : WithBot ℕ∞) < ((n - 1 : ℕ) : WithBot ℕ∞) by
        exact_mod_cast hposQ_nat)
  obtain ⟨ybar, hybar_mem, hybar_avoid⟩ :=
    exists_mem_maximalIdeal_avoiding_minimalPrimes (A := Q) hposQ
  obtain ⟨y, hybar_eq⟩ :=
    lift_maximalIdeal_element_from_quotient (R := R) (I := I) hybar_mem
  let Jbar : Ideal Q := Ideal.span ({(ybar : Q)} : Set Q)
  let Qy := Q ⧸ Jbar
  have hJbar_le_max : Jbar ≤ maximalIdeal Q := by
    -- The principal ideal generated by `ȳ` is still inside the quotient maximal ideal.
    dsimp [Jbar]
    exact (Ideal.span_singleton_le_iff_mem (I := maximalIdeal Q) (x := (ybar : Q))).2 hybar_mem
  have hJbar_ne_top : Jbar ≠ ⊤ := by
    -- Again, containment in the maximal ideal prevents the principal ideal from being all of `Q`.
    intro htop
    have hmax_top : maximalIdeal Q = ⊤ := top_le_iff.mp (htop ▸ hJbar_le_max)
    exact (maximalIdeal.isMaximal Q).ne_top hmax_top
  letI : Nontrivial Qy := Ideal.Quotient.nontrivial_iff.mpr hJbar_ne_top
  letI : IsLocalRing Qy :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk Jbar) Ideal.Quotient.mk_surjective
  have hdimQy_succ : ringKrullDim Q = ringKrullDim Qy + 1 := by
    -- Apply the same exact-drop statement inside `Q`.
    simpa [Jbar, Qy] using
      ringKrullDim_eq_ringKrullDim_quotient_span_singleton_add_one_of_not_mem_minimalPrimes
        (R := Q) (ybar : Q) hybar_mem hybar_avoid
  obtain ⟨k, hdimQy_nat⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (A := Qy)
  have hk_succ : k + 1 = n - 1 := by
    have hk_succ' : (((k + 1 : ℕ) : WithBot ℕ∞) = ((n - 1 : ℕ) : WithBot ℕ∞)) := by
      simpa [hdimQ, hdimQy_nat] using hdimQy_succ.symm
    exact_mod_cast hk_succ'
  have hk : k = n - 2 := by
    omega
  have hybar_ne_zero : (ybar : Q) ≠ 0 := by
    -- If `ȳ = 0`, then the second quotient is just `Q`, contradicting the computed dimension drop.
    intro hybar_zero
    have hJbar_zero : Jbar = (⊥ : Ideal Q) := by
      simpa [Jbar, hybar_zero, Ideal.span_singleton_zero]
    have hQy_zero : ringKrullDim Qy = ringKrullDim Q := by
      calc
        ringKrullDim Qy = ringKrullDim (Q ⧸ (⊥ : Ideal Q)) := by
          simpa [Qy] using
            ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq Q hJbar_zero).toRingEquiv
        _ = ringKrullDim Q := ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot Q)
    have hk_eq_m : k = m := by
      exact WithBot.coe_inj.mp <| by
        simpa [hdimQ_nat, hdimQy_nat] using hQy_zero
    omega
  have hy_nonzero : (y : R) ≠ 0 := by
    -- A zero lift would map to the zero class `ȳ`.
    intro hy_zero
    apply hybar_ne_zero
    simpa [hybar_eq] using congrArg (Ideal.Quotient.mk I) hy_zero
  let Jy : Ideal R := Ideal.span ({(y : R)} : Set R)
  let Ry := R ⧸ Jy
  have hJy_le_max : Jy ≤ maximalIdeal R := by
    -- The lifted element still lies in the original maximal ideal.
    dsimp [Jy]
    exact (Ideal.span_singleton_le_iff_mem (I := maximalIdeal R) (x := (y : R))).2 y.2
  have hJy_ne_top : Jy ≠ ⊤ := by
    intro htop
    have hmax_top : maximalIdeal R = ⊤ := top_le_iff.mp (htop ▸ hJy_le_max)
    exact (maximalIdeal.isMaximal R).ne_top hmax_top
  letI : Nontrivial Ry := Ideal.Quotient.nontrivial_iff.mpr hJy_ne_top
  letI : IsLocalRing Ry :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk Jy) Ideal.Quotient.mk_surjective
  have hy_avoid : ∀ p ∈ minimalPrimes R, (y : R) ∉ p := by
    -- The same domain argument shows that every nonzero element avoids the unique minimal prime.
    intro p hp hy_mem
    have hp_bot : p = ⊥ := by
      simpa [IsDomain.minimalPrimes_eq_singleton_bot R] using hp
    exact hy_nonzero <| by simpa [hp_bot] using hy_mem
  have hdimY_succ : ringKrullDim R = ringKrullDim Ry + 1 := by
    simpa [Jy, Ry] using
      ringKrullDim_eq_ringKrullDim_quotient_span_singleton_add_one_of_not_mem_minimalPrimes
        (R := R) (y : R) y.2 hy_avoid
  obtain ⟨ℓ, hdimY_nat⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (A := Ry)
  have hℓ_succ : ℓ + 1 = n := by
    have hℓ_succ' : (((ℓ + 1 : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞)) := by
      simpa [hdimR, hdimY_nat] using hdimY_succ.symm
    exact_mod_cast hℓ_succ'
  have hℓ : ℓ = n - 1 := by
    omega
  have hdimY : ringKrullDim (R ⧸ Ideal.span ({(y : R)} : Set R)) = (n - 1 : ℕ) := by
    simpa [Jy, Ry, hdimY_nat, hℓ]
  have hmap_span :
      Ideal.map (Ideal.Quotient.mk I) Jy = Jbar := by
    -- Mapping the principal ideal `(y)` to `Q = R / (x)` yields the principal ideal `(ȳ)`.
    rw [Ideal.map_span]
    apply le_antisymm
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨z, hz, rfl⟩
      rcases Set.mem_singleton_iff.mp hz with rfl
      rw [hybar_eq]
      exact Ideal.subset_span (by simp)
    · refine Ideal.span_le.2 ?_
      rintro _ hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      have hy_image_mem :
          Ideal.Quotient.mk I (y : R) ∈
            Ideal.span ((Ideal.Quotient.mk I) '' ({(y : R)} : Set R)) := by
        exact Ideal.subset_span ⟨(y : R), by simp, rfl⟩
      simpa [hybar_eq] using hy_image_mem
  have hpair_span :
      I ⊔ Jy = Ideal.span ({(y : R), x} : Set R) := by
    -- The join of the principal ideals `(x)` and `(y)` is the ideal generated by both elements.
    apply le_antisymm
    · refine sup_le ?_ ?_
      · dsimp [I]
        exact Ideal.span_mono (by simp)
      · dsimp [Jy]
        exact Ideal.span_mono (by simp)
    · refine Ideal.span_le.2 ?_
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      ·
        exact (show Jy ≤ I ⊔ Jy from le_sup_right) <| by
          dsimp [Jy]
          exact Ideal.subset_span (by simp)
      ·
        exact (show I ≤ I ⊔ Jy from le_sup_left) <| by
          dsimp [I]
          exact Ideal.subset_span (by simp)
  have hdimQy :
      ringKrullDim (Q ⧸ Jbar) = (n - 2 : ℕ) := by
    simpa [Qy, hdimQy_nat, hk]
  have hdimYX :
      ringKrullDim (R ⧸ Ideal.span ({(y : R), x} : Set R)) = (n - 2 : ℕ) := by
    -- Transport the quotient-of-quotient dimension back to the two-generator ideal `(y, x)`.
    calc
      ringKrullDim (R ⧸ Ideal.span ({(y : R), x} : Set R))
          = ringKrullDim (R ⧸ (I ⊔ Jy)) := by rw [hpair_span]
      _ = ringKrullDim (Q ⧸ Ideal.map (Ideal.Quotient.mk I) Jy) := by
            symm
            simpa [Q, Jy] using
              ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup I Jy)
      _ = ringKrullDim (Q ⧸ Jbar) := by rw [hmap_span]
      _ = ((n - 2 : ℕ) : WithBot ℕ∞) := hdimQy
  refine ⟨y, hdimY, hdimYX⟩

private theorem krullDimLE_one_of_isOpen_singleton_genericPoint
    (hgenericOpen : IsOpen ({(⊥ : PrimeSpectrum R)} : Set (PrimeSpectrum R))) :
    Ring.KrullDimLE 1 R := by
  classical
  obtain ⟨x, hx0, hbasic⟩ :=
    exists_nonzero_basicOpen_eq_singleton_bot_of_isOpen_singleton_bot hgenericOpen
  by_cases hmax : maximalIdeal R = ⊥
  · -- If the maximal ideal vanishes, the local domain is already a field.
    have hfield : IsField R := (IsLocalRing.isField_iff_maximalIdeal_eq (R := R)).2 hmax
    have hzero : ringKrullDim R = 0 := ringKrullDim_eq_zero_of_isField hfield
    exact Ring.krullDimLE_iff.mpr <| by
      simpa [hzero]
  obtain ⟨n, hdimR⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (A := R)
  have hx : x ∈ maximalIdeal R :=
    mem_maximalIdeal_of_basicOpen_eq_singleton_bot hbasic hmax
  have hnot_two : ¬ 2 ≤ n := by
    intro htwo
    obtain ⟨y, hdimY, hdimYX⟩ :=
      exists_head_parameter_with_quotient_dimension_drop
        (R := R) (n := n) hdimR htwo hx0 hx
    have hy_nonzero : (y : R) ≠ 0 := by
      -- If `y = 0`, then the first quotient is just `R`, contradicting the computed dimension drop.
      intro hyzero
      have hy_span :
          Ideal.span ({(y : R)} : Set R) = (⊥ : Ideal R) := by
        simpa [hyzero, Ideal.span_singleton_zero]
      have hquot_zero :
          ringKrullDim (R ⧸ Ideal.span ({(y : R)} : Set R)) = ringKrullDim R := by
        calc
          ringKrullDim (R ⧸ Ideal.span ({(y : R)} : Set R))
              = ringKrullDim (R ⧸ (⊥ : Ideal R)) := by rw [hy_span]
          _ = ringKrullDim R := ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)
      have : n - 1 = n := by
        exact WithBot.coe_inj.mp <| by
          simpa [hdimR, hdimY] using hquot_zero
      omega
    have hzeroLocus_ne :
        PrimeSpectrum.zeroLocus (R := R) (Ideal.span ({(y : R)} : Set R)) ≠
          PrimeSpectrum.zeroLocus (R := R) (Ideal.span ({(y : R), x} : Set R)) := by
      -- Equal zero loci would force equal quotient dimensions, contradicting `n - 1 ≠ n - 2`.
      intro hzero
      have hdimEq :
          ringKrullDim (R ⧸ Ideal.span ({(y : R)} : Set R)) =
            ringKrullDim (R ⧸ Ideal.span ({(y : R), x} : Set R)) := by
        rw [ringKrullDim_quotient, ringKrullDim_quotient, hzero]
      have : n - 1 = n - 2 := by
        exact WithBot.coe_inj.mp <| by
          simpa [hdimY, hdimYX] using hdimEq
      omega
    have hzeroLocus_not_subset :
        ¬ PrimeSpectrum.zeroLocus (R := R) (Ideal.span ({(y : R)} : Set R)) ⊆
          PrimeSpectrum.zeroLocus (R := R) (Ideal.span ({(y : R), x} : Set R)) := by
      -- The two zero loci are nested in the reverse direction, so forward inclusion would give
      -- equality.
      intro hsubset
      have hsuperset :
          PrimeSpectrum.zeroLocus (R := R) (Ideal.span ({(y : R), x} : Set R)) ⊆
            PrimeSpectrum.zeroLocus (R := R) (Ideal.span ({(y : R)} : Set R)) := by
        exact PrimeSpectrum.zeroLocus_anti_mono_ideal <|
          Ideal.span_mono (by simp)
      exact hzeroLocus_ne (Set.Subset.antisymm hsubset hsuperset)
    obtain ⟨p, hpY, hpYX⟩ := Set.not_subset.mp hzeroLocus_not_subset
    have hy_mem : (y : R) ∈ p.asIdeal := by
      simpa [PrimeSpectrum.mem_zeroLocus] using hpY
    have hx_not_mem : x ∉ p.asIdeal := by
      intro hxmem
      exact hpYX <| by
        rw [PrimeSpectrum.mem_zeroLocus]
        refine Ideal.span_le.2 ?_
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact hy_mem
        · exact hxmem
    have hp_basic : p ∈ (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum R)) := by
      exact (PrimeSpectrum.mem_basicOpen x p).2 hx_not_mem
    have hp_eq_bot : p = (⊥ : PrimeSpectrum R) := by
      simpa [hbasic] using hp_basic
    have hy_zero : (y : R) = 0 := by
      simpa [hp_eq_bot] using hy_mem
    exact hy_nonzero hy_zero
  have hnle : n ≤ 1 := by
    omega
  exact Ring.krullDimLE_iff.mpr <| by
    simpa [hdimR] using hnle

/-- Lemma 10.61.1: if `R` is a Noetherian local domain of Krull dimension at least `2`, then every
nonempty open subset of `Spec(R)` is infinite. The open subset is stated canonically as
`U : Opens (PrimeSpectrum R)`, with nonemptiness expressed owner-canonically by `U ≠ ⊥`; the
conclusion concerns the underlying set of points. -/
theorem infinite_open_subset_of_local_noetherian_domain_of_two_le_ringKrullDim
    (U : Opens (PrimeSpectrum R)) (hU : U ≠ ⊥)
    (hdim : 2 ≤ ringKrullDim R) :
    Set.Infinite (U : Set (PrimeSpectrum R)) := by
  classical
  by_contra hfinite
  have hfinite' : Set.Finite (U : Set (PrimeSpectrum R)) :=
    not_not.mp hfinite
  have hne : Set.Nonempty (U : Set (PrimeSpectrum R)) := (U.ne_bot_iff_nonempty).mp hU
  obtain ⟨x, -, hxopen⟩ := exists_isOpen_singleton_of_isOpen_finite hfinite' hne U.2
  have hxbot : x = (⊥ : PrimeSpectrum R) := by
    have hmem : (⊥ : PrimeSpectrum R) ∈ ({x} : Set (PrimeSpectrum R)) :=
      ((PrimeSpectrum.le_iff_specializes (⊥ : PrimeSpectrum R) x).mp bot_le).mem_open hxopen
        (by simp)
    simpa using hmem.symm
  have hgenericOpen : IsOpen ({(⊥ : PrimeSpectrum R)} : Set (PrimeSpectrum R)) := by
    simpa [hxbot] using hxopen
  have hdim1 : Ring.KrullDimLE 1 R :=
    krullDimLE_one_of_isOpen_singleton_genericPoint hgenericOpen
  have hdim' : ringKrullDim R ≤ 1 := Ring.krullDimLE_iff.mp hdim1
  have : ¬ (2 : WithBot ℕ∞) ≤ 1 := by
    simp
  exact this (hdim.trans hdim')

end

/-! ### Lemma_10_61_2 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Finite (PrimeSpectrum R)]

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.61.2: a quotient of a ring with finite prime spectrum again has finite
prime spectrum. -/
private theorem finite_primeSpectrum_quotient (I : Ideal R) :
    Finite (PrimeSpectrum (R ⧸ I)) := by
  -- Transport finiteness across the canonical order isomorphism with the zero locus `V(I)`.
  let e : PrimeSpectrum (R ⧸ I) ≃o PrimeSpectrum.zeroLocus (R := R) I :=
    Ideal.primeSpectrumQuotientOrderIsoZeroLocus I
  exact Finite.of_injective (f := e) e.injective

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.61.2: localizing at a prime ideal preserves finiteness of the prime
spectrum. -/
private theorem finite_primeSpectrum_localizationAtPrime (p : PrimeSpectrum R) :
    Finite (PrimeSpectrum (Localization.AtPrime p.asIdeal)) := by
  -- The spectrum of the localization identifies with the lower interval `Set.Iic p`.
  let e :
      PrimeSpectrum (Localization.AtPrime p.asIdeal) ≃o Set.Iic p :=
    IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime p.asIdeal) p.asIdeal
  exact Finite.of_injective (f := e) e.injective

omit [IsNoetherianRing R] [Finite (PrimeSpectrum R)] in
/-- Helper for Lemma 10.61.2: the Krull dimension of a prime quotient is the coheight of the
corresponding point of the ambient spectrum. -/
private theorem ringKrullDim_quotient_eq_coheight (q : Ideal R) [q.IsPrime] :
    ringKrullDim (R ⧸ q) = Order.coheight (⟨q, inferInstance⟩ : PrimeSpectrum R) := by
  -- Rewrite the quotient spectrum as the upper interval above `q`.
  let x : PrimeSpectrum R := ⟨q, inferInstance⟩
  rw [ringKrullDim_quotient]
  have hzero : PrimeSpectrum.zeroLocus (q : Set R) = Set.Ici x := by
    ext p
    change q ≤ p.asIdeal ↔ x ≤ p
    rfl
  rw [hzero]
  exact (Order.coheight_eq_krullDim_Ici x).symm

/-- Helper for Lemma 10.61.2: a Noetherian domain with finite prime spectrum has Krull dimension
at most `1`. -/
private theorem krullDimLE_one_of_finite_primeSpectrum_domain
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Finite (PrimeSpectrum A)] :
    Ring.KrullDimLE 1 A := by
  -- Bound the global dimension by checking every maximal localization, as in the source proof.
  refine Ring.krullDimLE_of_isLocalization_maximal
    (R := A) (Rₚ := fun P _ => Localization.AtPrime P) ?_
  intro P hP
  letI : Finite (PrimeSpectrum (Localization.AtPrime P)) :=
    finite_primeSpectrum_localizationAtPrime (R := A) ⟨P, hP.isPrime⟩
  refine Ring.krullDimLE_iff.mpr ?_
  by_contra hdim
  -- If the localized ring had dimension at least `2`, Lemma `10.61.1` would force its whole
  -- spectrum to be infinite, contradicting finiteness.
  have htwo : (2 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime P) := by
    simpa using Order.succ_le_of_lt (lt_of_not_ge hdim)
  have huniv_ne_bot :
      (⊤ : TopologicalSpace.Opens (PrimeSpectrum (Localization.AtPrime P))) ≠ ⊥ := by
    intro htop
    have hmem :
        (⊥ : PrimeSpectrum (Localization.AtPrime P)) ∈
          ((⊤ : TopologicalSpace.Opens (PrimeSpectrum (Localization.AtPrime P))) :
            Set (PrimeSpectrum (Localization.AtPrime P))) := by
      simp
    simpa [htop] using hmem
  have hinfinite :
      Set.Infinite
        ((⊤ : TopologicalSpace.Opens (PrimeSpectrum (Localization.AtPrime P))) :
          Set (PrimeSpectrum (Localization.AtPrime P))) :=
    infinite_open_subset_of_local_noetherian_domain_of_two_le_ringKrullDim
      (R := Localization.AtPrime P) ⊤ huniv_ne_bot htwo
  have hfinite_univ :
      Set.Finite (Set.univ : Set (PrimeSpectrum (Localization.AtPrime P))) :=
    Set.toFinite _
  exact hfinite_univ.not_infinite (by simpa using hinfinite)

/-- Helper for Lemma 10.61.2: every prime ideal of a Noetherian ring with finite spectrum has
coheight at most `1`. -/
private theorem coheight_le_one_of_prime (p : PrimeSpectrum R) :
    Order.coheight p ≤ 1 := by
  -- Choose a minimal prime below `p` and compare coheights with the corresponding domain quotient.
  obtain ⟨q, hq, hqp⟩ :=
    Ideal.exists_minimalPrimes_le (R := R) (I := (⊥ : Ideal R)) (J := p.asIdeal) bot_le
  haveI : q.IsPrime := Ideal.minimalPrimes_isPrime hq
  let qPoint : PrimeSpectrum R := ⟨q, inferInstance⟩
  letI : IsDomain (R ⧸ q) := (Ideal.Quotient.isDomain_iff_prime (I := q)).2 inferInstance
  letI : Finite (PrimeSpectrum (R ⧸ q)) := finite_primeSpectrum_quotient (R := R) q
  have hqdim :
      ringKrullDim (R ⧸ q) ≤ 1 := by
    exact Ring.krullDimLE_iff.mp (krullDimLE_one_of_finite_primeSpectrum_domain (A := R ⧸ q))
  have hqcoheight : Order.coheight qPoint ≤ 1 := by
    simpa [qPoint, ringKrullDim_quotient_eq_coheight (R := R) q] using hqdim
  exact le_trans (Order.coheight_anti (show qPoint ≤ p from hqp)) hqcoheight

-- Layering for this item:
-- * source-facing: a Noetherian ring with finite prime spectrum has dimension at most `1`.
-- * core/canonical owner: `Ring.KrullDimLE 1 R`.
-- * bridge/view: `ringKrullDim R ≤ 1` is recovered from the owner instance by
--   `Ring.krullDimLE_iff`.
-- Primitive data are exactly the assumptions `[IsNoetherianRing R]` and
-- `[Finite (PrimeSpectrum R)]`; the inequality theorem below is derived API from the owner
-- abstraction.

-- Proof sketch: first treat the local domain case using Lemma `10.61.1`, which rules out
-- Krull dimension at least `2` because a finite prime spectrum cannot contain an infinite nonempty
-- open subset. Then localize a domain at each maximal ideal and apply Lemma `10.60.4` to bound
-- `ringKrullDim R` by the supremum of maximal heights. For a general Noetherian ring, pass to each
-- quotient by a minimal prime and use Lemma `10.17.2` to see that every prime contains a minimal
-- prime, so all prime chains still have length at most `1`.
/-- Owner-level form of Lemma 10.61.2. The source-facing inequality
`ringKrullDim R ≤ 1` is the companion theorem below, obtained via `Ring.krullDimLE_iff`. -/
instance krullDimLE_one_of_finite_primeSpectrum : Ring.KrullDimLE 1 R := by
  -- Separate the degenerate ring from the nontrivial case before applying the primewise argument.
  cases subsingleton_or_nontrivial R with
  | inl hR =>
      letI := hR
      exact Ring.krullDimLE_iff.mpr <| by
        simp [ringKrullDim_eq_bot_of_subsingleton]
  | inr hR =>
      letI := hR
      -- Bound `ringKrullDim R` by bounding the coheight of every prime ideal by `1`.
      refine Ring.krullDimLE_iff.mpr ?_
      rw [ringKrullDim, Order.krullDim_eq_iSup_coheight]
      refine iSup_le fun p => ?_
      exact WithBot.coe_le_coe.mpr (coheight_le_one_of_prime (R := R) p)

end

section

variable {R : Type u} [CommRing R]

/-- Lemma 10.61.2, source-facing form: a Noetherian ring with finitely many prime ideals has
Krull dimension at most `1`. -/
theorem ringKrullDim_le_one_of_finite_primeSpectrum [IsNoetherianRing R] [Finite (PrimeSpectrum R)] :
    ringKrullDim R ≤ 1 :=
  Ring.krullDimLE_iff.mp inferInstance

end

/-! ### Lemma_10_61_3 (from Chap10) -/
universe u v

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
variable [Algebra.FiniteType k S]

-- Proof sketch: finite type over a field makes `S` Noetherian and Jacobson. The owner-side
-- equivalence `Module.finite_iff_krullDimLE_zero` identifies the zero-dimensional clause with
-- `FiniteDimensional k S`, and `Module.finite_iff_isArtinianRing` identifies that clause with
-- `IsArtinianRing S`. The Artinian-to-finite-maximal-spectrum step is then delegated to the owner
-- instance `IsArtinianRing.instFiniteMaximalSpectrum`, and the Jacobson/discrete-spectrum clauses
-- are recovered from the canonical prime-spectrum API.
/-- Lemma 10.61.3: for a finite type `k`-algebra `S`, the canonical zero-dimensional, finite-
spectrum, Hausdorff-spectrum, finite-dimensional, Artinian, and discrete-spectrum clauses are
equivalent.

Canonical Lean form: clause `(1)` uses the owner predicate `Ring.KrullDimLE 0 S`. Under the extra
hypothesis `[Nontrivial S]`, this recovers the source wording `ringKrullDim S = 0` via
`ringKrullDimZero_iff_ringKrullDim_eq_zero`. The theorem itself does not need `[Nontrivial S]`,
since all seven canonical clauses still agree in the zero-ring edge case. -/
theorem finiteTypeAlgebra_over_field_zeroDimensional_tfae :
    List.TFAE
      [ Ring.KrullDimLE 0 S
      , Finite (PrimeSpectrum S)
      , Finite (MaximalSpectrum S)
      , T2Space (PrimeSpectrum S)
      , FiniteDimensional k S
      , IsArtinianRing S
      , DiscreteTopology (PrimeSpectrum S)
      ] := by
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have hFiniteType : (algebraMap k S).FiniteType := by
    rwa [RingHom.finiteType_algebraMap]
  letI : IsJacobsonRing S := hFiniteType.isJacobsonRing
  have hclosedPoints_of_finiteMax [Finite (MaximalSpectrum S)] :
      (closedPoints (PrimeSpectrum S)).Finite := by
    let f : MaximalSpectrum S → closedPoints (PrimeSpectrum S) := fun x ↦
      ⟨x.toPrimeSpectrum, (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr x.isMaximal⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      exact
        ⟨⟨x.asIdeal, (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hx⟩, rfl⟩
    exact Finite.of_surjective f hf
  tfae_have 1 ↔ 5 := by
    simpa using (Module.finite_iff_krullDimLE_zero k S).symm
  tfae_have 5 ↔ 6 := by
    simpa using Module.finite_iff_isArtinianRing k S
  tfae_have 6 → 3 := by
    intro hArt
    letI : IsArtinianRing S := hArt
    infer_instance
  tfae_have 3 → 7 := by
    intro hfin
    letI : Finite (MaximalSpectrum S) := hfin
    exact JacobsonSpace.discreteTopology hclosedPoints_of_finiteMax
  tfae_have 6 ↔ 7 := by
    constructor
    · intro hArt
      letI : IsArtinianRing S := hArt
      letI : Finite (MaximalSpectrum S) := inferInstance
      exact JacobsonSpace.discreteTopology hclosedPoints_of_finiteMax
    · intro hdisc
      exact
        (Module.finite_iff_isArtinianRing k S).mp <|
          (Module.finite_iff_krullDimLE_zero k S).mpr <|
            (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp hdisc).2
  tfae_have 7 → 2 := by
    intro hdisc
    exact (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp hdisc).1
  tfae_have 2 → 4 := by
    intro hfin
    letI : Finite (PrimeSpectrum S) := hfin
    let hclosed : (closedPoints (PrimeSpectrum S)).Finite := Set.toFinite _
    letI : DiscreteTopology (PrimeSpectrum S) := JacobsonSpace.discreteTopology hclosed
    infer_instance
  tfae_have 4 → 1 := by
    intro hT2
    letI : T2Space (PrimeSpectrum S) := hT2
    letI : T1Space (PrimeSpectrum S) := T2Space.t1Space
    refine Ring.KrullDimLE.mk₀ fun I hI ↦ ?_
    exact
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal ⟨I, hI⟩).mp
        isClosed_singleton
  tfae_finish

end

/-! ### Lemma_10_61_4 (from Chap10) -/
open scoped Classical

universe u

/-
Domain sampling:
* primary domain: commutative algebra of `Spec R`, `MaxSpec R`, Jacobson rings, and Krull
  dimension in the Noetherian setting;
* owner declarations inspected in this domain:
  - `isJacobsonRing_of_isNoetherianRing_of_dimensionLEOne_of_infinite_maximalSpectrum`
  - `exists_nonmaximal_prime_basicOpen_inter_zeroLocus_eq_singleton_of_not_isJacobsonRing`
  - `infinite_open_subset_of_local_noetherian_domain_of_two_le_ringKrullDim`
  - `Ideal.primeSpectrumQuotientOrderIsoZeroLocus`;
* best owner abstraction: `IsJacobsonRing R`, with `Ring.DimensionLEOne` as the canonical
  dimension-one owner and quotient/localization spectrum identifications as bridge/view API;
* primitive vs. derived: the source-facing inputs are infinitude of prime ideals and the primewise
  maximal-or-infinite-over condition, while the comparison between `PrimeSpectrum R` and
  `MaximalSpectrum R` in dimension one is derived API and stays private.
-/

section

variable {R : Type u} [CommRing R] [Ring.DimensionLEOne R]

private theorem finite_primeSpectrum_of_finite_maximalSpectrum
    [Finite (MaximalSpectrum R)] :
    Finite (PrimeSpectrum R) := by
  classical
  let s : Set (Ideal R) := {(⊥ : Ideal R)} ∪ Set.range MaximalSpectrum.asIdeal
  have hs : s.Finite :=
    (Set.finite_singleton (⊥ : Ideal R)).union (Set.finite_range MaximalSpectrum.asIdeal)
  letI : Fintype s := hs.fintype
  let f : PrimeSpectrum R → s := fun x ↦ by
    refine ⟨x.asIdeal, ?_⟩
    by_cases hx : x.asIdeal = ⊥
    · exact Or.inl hx
    · exact Or.inr
        ⟨⟨x.asIdeal, x.isPrime.isMaximal hx⟩, rfl⟩
  exact Finite.of_injective f fun x y hxy ↦
    PrimeSpectrum.ext <| by simpa using congrArg Subtype.val hxy

private theorem infinite_maximalSpectrum_of_infinite_primeSpectrum
    [Infinite (PrimeSpectrum R)] : Infinite (MaximalSpectrum R) := by
  by_contra h
  haveI : Finite (MaximalSpectrum R) := not_infinite_iff_finite.mp h
  haveI : Finite (PrimeSpectrum R) := finite_primeSpectrum_of_finite_maximalSpectrum
  exact Finite.false (inferInstance : Finite (PrimeSpectrum R))

end

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Helper for Lemma 10.61.4: quotienting by a prime ideal transports the Stacks obstruction
`V(p) ∩ D(f) = {p}` to the singleton generic basic open on `Spec (R / p)`. -/
lemma basicOpen_quotient_eq_singleton_bot_of_zeroLocus_inter_basicOpen_eq_singleton
    (p : PrimeSpectrum R) (f : R)
    (hp :
      PrimeSpectrum.zeroLocus (R := R) (p.asIdeal : Set R) ∩
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) = {p}) :
    (PrimeSpectrum.basicOpen (Ideal.Quotient.mk p.asIdeal f) :
        Set (PrimeSpectrum (R ⧸ p.asIdeal))) =
      ({(⊥ : PrimeSpectrum (R ⧸ p.asIdeal))} : Set (PrimeSpectrum (R ⧸ p.asIdeal))) := by
  let e := Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal
  have hpV : p ∈ PrimeSpectrum.zeroLocus (R := R) (p.asIdeal : Set R) := by
    exact (PrimeSpectrum.mem_zeroLocus p (p.asIdeal : Set R)).2 le_rfl
  have hbot_image : e (⊥ : PrimeSpectrum (R ⧸ p.asIdeal)) = ⟨p, hpV⟩ := by
    apply Subtype.ext
    apply PrimeSpectrum.ext
    -- The generic point of `Spec (R / p)` contracts to `p`.
    change Ideal.comap (Ideal.Quotient.mk p.asIdeal) (⊥ : Ideal (R ⧸ p.asIdeal)) = p.asIdeal
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  ext x
  constructor
  · intro hx
    have hxVD :
        (e x).1 ∈ PrimeSpectrum.zeroLocus (R := R) (p.asIdeal : Set R) ∩
          (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
      refine ⟨(e x).2, ?_⟩
      exact (PrimeSpectrum.mem_basicOpen f (PrimeSpectrum.comap (Ideal.Quotient.mk p.asIdeal) x)).2
        (by
          simpa [Ideal.mem_comap] using
            (PrimeSpectrum.mem_basicOpen (Ideal.Quotient.mk p.asIdeal f) x).1 hx)
    have hx_singleton : (e x).1 ∈ ({p} : Set (PrimeSpectrum R)) := by
      rw [← hp]
      exact hxVD
    have hx_image : e x = ⟨p, hpV⟩ := by
      apply Subtype.ext
      simpa using hx_singleton
    refine Set.mem_singleton_iff.mpr ?_
    exact e.injective (hx_image.trans hbot_image.symm)
  · intro hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    have hp_basic : p ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
      have hp_mem :
          p ∈ PrimeSpectrum.zeroLocus (R := R) (p.asIdeal : Set R) ∩
            (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
        rw [hp]
        simp
      exact hp_mem.2
    -- The generic point of `Spec (R / p)` still avoids the image of `f`.
    refine (PrimeSpectrum.mem_basicOpen (Ideal.Quotient.mk p.asIdeal f)
      (⊥ : PrimeSpectrum (R ⧸ p.asIdeal))).2 ?_
    simpa [Ideal.Quotient.eq_zero_iff_mem] using
      (PrimeSpectrum.mem_basicOpen f p).1 hp_basic

/-- Helper for Lemma 10.61.4: once a basic open is the singleton generic point in a domain, the
same remains true after localizing at any prime. -/
lemma basicOpen_localizationAtPrime_eq_singleton_bot_of_basicOpen_eq_singleton_bot
    {A : Type u} [CommRing A] [IsDomain A] {x : A}
    (hbasic :
      (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum A)) =
        ({(⊥ : PrimeSpectrum A)} : Set (PrimeSpectrum A)))
    (q : PrimeSpectrum A) :
    (PrimeSpectrum.basicOpen (algebraMap A (Localization.AtPrime q.asIdeal) x) :
        Set (PrimeSpectrum (Localization.AtPrime q.asIdeal))) =
      ({(⊥ : PrimeSpectrum (Localization.AtPrime q.asIdeal))} :
        Set (PrimeSpectrum (Localization.AtPrime q.asIdeal))) := by
  let S := Localization.AtPrime q.asIdeal
  letI : IsDomain S := IsLocalization.isDomain_of_atPrime S q.asIdeal
  have hinj :
      Function.Injective (PrimeSpectrum.comap (algebraMap A S)) :=
    (PrimeSpectrum.localization_comap_isEmbedding S q.asIdeal.primeCompl).injective
  have halg_inj : Function.Injective (algebraMap A S) :=
    IsLocalization.injective S (Ideal.primeCompl_le_nonZeroDivisors q.asIdeal)
  have hx0 : x ≠ 0 := by
    -- The generic point belongs to `D(x)`, so `x` is nonzero.
    have hbot_mem : (⊥ : PrimeSpectrum A) ∈ (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum A)) := by
      simpa [hbasic]
    exact (PrimeSpectrum.mem_basicOpen x (⊥ : PrimeSpectrum A)).1 hbot_mem
  have hbot_comap :
      PrimeSpectrum.comap (algebraMap A S) (⊥ : PrimeSpectrum S) = (⊥ : PrimeSpectrum A) := by
    apply PrimeSpectrum.ext
    -- Injectivity of the localization map identifies the contracted zero ideal with `(0)`.
    change Ideal.comap (algebraMap A S) (⊥ : Ideal S) = (⊥ : Ideal A)
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp halg_inj
  ext y
  constructor
  · intro hy
    have hy_comap_mem :
        PrimeSpectrum.comap (algebraMap A S) y ∈
          (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum A)) := by
      exact (PrimeSpectrum.mem_basicOpen x (PrimeSpectrum.comap (algebraMap A S) y)).2 <|
        by
          simpa [Ideal.mem_comap] using
            (PrimeSpectrum.mem_basicOpen (algebraMap A S x) y).1 hy
    have hy_comap_eq_bot : PrimeSpectrum.comap (algebraMap A S) y = (⊥ : PrimeSpectrum A) := by
      simpa [hbasic] using hy_comap_mem
    refine Set.mem_singleton_iff.mpr ?_
    exact hinj (hy_comap_eq_bot.trans hbot_comap.symm)
  · intro hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    -- Injectivity of `A → A_q` keeps the nonzero element `x` nonzero after localization.
    refine (PrimeSpectrum.mem_basicOpen (algebraMap A S x) (⊥ : PrimeSpectrum S)).2 ?_
    intro hxS
    exact hx0 (halg_inj (by simpa using hxS))

/-- Helper for Lemma 10.61.4: the Krull dimension of a Noetherian local ring is represented by a
natural number. -/
lemma exists_nat_ringKrullDim_of_local_noetherian_ring
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    ∃ n : ℕ, ringKrullDim A = n := by
  have hbot : ringKrullDim A ≠ ⊥ := ringKrullDim_ne_bot
  have htop : ringKrullDim A ≠ ⊤ := ringKrullDim_ne_top
  let n : ℕ := ((ringKrullDim A).unbot hbot).toNat
  have hneTop : (ringKrullDim A).unbot hbot ≠ ⊤ := by
    intro htop'
    exact htop <| by
      simpa [WithBot.coe_unbot] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) htop'
  have hdim' : ((ringKrullDim A).unbot hbot : WithBot ℕ∞) = n := by
    simpa [n] using
      congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
  refine ⟨n, ?_⟩
  calc
    ringKrullDim A = (ringKrullDim A).unbot hbot := by
      exact (WithBot.coe_unbot (ringKrullDim A) hbot).symm
    _ = n := hdim'

/-- Helper for Lemma 10.61.4: in a Noetherian domain, a nonzero prime under an open generic
singleton has prime height exactly `1`. -/
lemma primeHeight_eq_one_of_ne_bot_of_basicOpen_eq_singleton_bot
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] {x : A}
    (hbasic :
      (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum A)) =
        ({(⊥ : PrimeSpectrum A)} : Set (PrimeSpectrum A)))
    (q : PrimeSpectrum A) (hq : q ≠ ⊥) :
    q.asIdeal.primeHeight = 1 := by
  let S := Localization.AtPrime q.asIdeal
  letI : IsDomain S := IsLocalization.isDomain_of_atPrime S q.asIdeal
  have hlocal_basic :
      (PrimeSpectrum.basicOpen (algebraMap A S x) : Set (PrimeSpectrum S)) =
        ({(⊥ : PrimeSpectrum S)} : Set (PrimeSpectrum S)) :=
    basicOpen_localizationAtPrime_eq_singleton_bot_of_basicOpen_eq_singleton_bot
      (A := A) hbasic q
  let U := PrimeSpectrum.basicOpen (algebraMap A S x)
  have hU_ne : U ≠ ⊥ := by
    rw [U.ne_bot_iff_nonempty]
    refine ⟨⊥, ?_⟩
    rw [hlocal_basic]
    simp
  have hnot_two : ¬ 2 ≤ ringKrullDim S := by
    intro hdim
    have hfinite : Set.Finite (U : Set (PrimeSpectrum S)) := by
      rw [hlocal_basic]
      exact Set.finite_singleton (⊥ : PrimeSpectrum S)
    exact hfinite.not_infinite <|
      infinite_open_subset_of_local_noetherian_domain_of_two_le_ringKrullDim
        (R := S) U hU_ne hdim
  obtain ⟨n, hdimS⟩ := exists_nat_ringKrullDim_of_local_noetherian_ring (A := S)
  have hnle : n ≤ 1 := by
    by_contra hnle'
    have htwo : 2 ≤ n := by omega
    exact hnot_two <| by
      simpa [hdimS] using (show (2 : WithBot ℕ∞) ≤ n by exact_mod_cast htwo)
  have hupper : q.asIdeal.primeHeight ≤ 1 := by
    have hheight_le : (q.asIdeal.height : WithBot ℕ∞) ≤ 1 := by
      calc
        (q.asIdeal.height : WithBot ℕ∞) = ringKrullDim S := by
          simpa [S] using (IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal S).symm
        _ = n := hdimS
        _ ≤ 1 := by exact_mod_cast hnle
    simpa [Ideal.height_eq_primeHeight] using hheight_le
  have hbot_primeHeight : (⊥ : Ideal A).primeHeight = 0 := by
    rw [Ideal.primeHeight_eq_zero_iff]
    simpa [IsDomain.minimalPrimes_eq_singleton_bot A]
  have hbot_lt_q : (⊥ : Ideal A) < q.asIdeal := by
    refine lt_of_le_of_ne bot_le ?_
    intro hEq
    exact hq (PrimeSpectrum.ext hEq.symm)
  have hlower : (1 : ℕ∞) ≤ q.asIdeal.primeHeight := by
    simpa [hbot_primeHeight] using
      (Ideal.primeHeight_add_one_le_of_lt hbot_lt_q)
  exact le_antisymm hupper hlower

/-- Helper for Lemma 10.61.4: infinitely many primes above `p` give infinitely many primes of the
quotient `R / p`. -/
lemma infinite_primeSpectrum_quotient_of_infinite_primesOver
    (p : PrimeSpectrum R) [Infinite { q : PrimeSpectrum R // p ≤ q }] :
    Infinite (PrimeSpectrum (R ⧸ p.asIdeal)) := by
  let f : { q : PrimeSpectrum R // p ≤ q } → PrimeSpectrum (R ⧸ p.asIdeal) := fun q ↦
    (Ideal.primeSpectrumQuotientOrderIsoZeroLocus p.asIdeal).symm
      ⟨q.1, (PrimeSpectrum.mem_zeroLocus q.1 (p.asIdeal : Set R)).2 q.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hab' := congrArg
      (Ideal.primeSpectrumQuotientOrderIsoZeroLocus p.asIdeal) hab
    have hab'' : a.1 = b.1 := by
      simpa [f] using congrArg Subtype.val hab'
    exact Subtype.ext hab''
  exact Infinite.of_injective f hf

-- Proof sketch: this is a reformulation of Lemma `10.35.6`. In a domain of Krull dimension `1`,
-- every nonzero prime ideal is maximal, so only `⊥` can fail to be maximal. Hence infinitely many
-- prime ideals force infinitely many maximal ideals, and the dimension-one Jacobson criterion
-- applies.
/-- Lemma 10.61.4 (1): any Noetherian domain of Krull dimension `1` with infinitely many prime
ideals is a Jacobson ring. In Lean, “infinitely many prime ideals” is expressed canonically by
`[Infinite (PrimeSpectrum R)]`. -/
theorem isJacobsonRing_of_isNoetherianRing_of_ringKrullDim_eq_one_of_infinite_primeIdeals
    [IsDomain R] [Infinite (PrimeSpectrum R)] (hdim : ringKrullDim R = 1) :
    IsJacobsonRing R := by
  have hdim' : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by simp [hdim])
  letI : Ring.DimensionLEOne R :=
    ⟨fun {p} hp hprime ↦ Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hdim' p hp hprime⟩
  letI : Infinite (MaximalSpectrum R) := infinite_maximalSpectrum_of_infinite_primeSpectrum
  exact isJacobsonRing_of_isNoetherianRing_of_dimensionLEOne_of_infinite_maximalSpectrum R

-- Proof sketch: argue by contradiction. If `R` were not Jacobson, Lemma `10.35.5` gives a
-- nonmaximal prime `P` whose singleton is locally closed in `Spec R`. For each prime `Q ⊇ P`,
-- the corresponding localization of `R ⧸ P` has locally closed generic point, so Lemma `10.61.1`
-- forces it to have Krull dimension `1`; thus `R ⧸ P` is a one-dimensional Noetherian domain.
-- The hypothesis gives infinitely many primes above `P`, hence infinitely many primes of `R ⧸ P`,
-- so clause `(1)` makes `R ⧸ P` Jacobson, contradicting that `{P}` is open in `V(P)`.
/-- Lemma 10.61.4 (2): any Noetherian ring such that every prime ideal is either maximal or
contained in infinitely many prime ideals is a Jacobson ring. -/
theorem isJacobsonRing_of_isNoetherianRing_of_primeIdeal_isMaximal_or_infinite_primesOver
    (hprime :
      ∀ p : PrimeSpectrum R,
        p.asIdeal.IsMaximal ∨ Infinite { q : PrimeSpectrum R // p ≤ q }) :
    IsJacobsonRing R := by
  by_contra hR
  obtain ⟨p, f, hp_nonmax, hp⟩ :=
    exists_nonmaximal_prime_basicOpen_inter_zeroLocus_eq_singleton_of_not_isJacobsonRing
      (R := R) hR
  let A := R ⧸ p.asIdeal
  let xbar : A := Ideal.Quotient.mk p.asIdeal f
  have hbasicA :
      (PrimeSpectrum.basicOpen xbar : Set (PrimeSpectrum A)) =
        ({(⊥ : PrimeSpectrum A)} : Set (PrimeSpectrum A)) := by
    -- Pass to the quotient ring, where the obstruction becomes an open generic singleton.
    simpa [A, xbar] using
      basicOpen_quotient_eq_singleton_bot_of_zeroLocus_inter_basicOpen_eq_singleton
        (R := R) p f hp
  have hp_inf : Infinite { q : PrimeSpectrum R // p ≤ q } := by
    rcases hprime p with hp_max | hp_inf
    · exact False.elim (hp_nonmax hp_max)
    · exact hp_inf
  letI : Infinite (PrimeSpectrum A) :=
    infinite_primeSpectrum_quotient_of_infinite_primesOver (R := R) p
  have hdimA_le : ringKrullDim A ≤ 1 := by
    refine (ringKrullDim_le_iff_isMaximal_height_le (R := A) 1).2 ?_
    intro m hm
    by_cases hm0 : m = ⊥
    · simpa [hm0]
    · let q : PrimeSpectrum A := ⟨m, hm.isPrime⟩
      have hq : q ≠ ⊥ := by
        intro hq
        exact hm0 (congrArg PrimeSpectrum.asIdeal hq)
      have hq_height :
          q.asIdeal.primeHeight = 1 :=
        primeHeight_eq_one_of_ne_bot_of_basicOpen_eq_singleton_bot
          (A := A) hbasicA q hq
      -- Every maximal ideal of `A` has height at most `1`.
      simpa [q, Ideal.height_eq_primeHeight, hq_height]
  have hp_ne_top : p.asIdeal ≠ ⊤ := p.isPrime.ne_top
  obtain ⟨M, hMmax, hpMle⟩ := Ideal.exists_le_maximal p.asIdeal hp_ne_top
  have hMp : p.asIdeal < M := by
    refine lt_of_le_of_ne hpMle ?_
    intro hEq
    exact hp_nonmax (hEq ▸ hMmax)
  let mSpec : PrimeSpectrum R := ⟨M, hMmax.isPrime⟩
  have hm_zeroLocus :
      mSpec ∈ PrimeSpectrum.zeroLocus (R := R) (p.asIdeal : Set R) := by
    rw [PrimeSpectrum.mem_zeroLocus]
    exact hpMle
  let qbar : PrimeSpectrum A :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal).symm
      ⟨mSpec, hm_zeroLocus⟩
  have hqbar_ne : qbar ≠ (⊥ : PrimeSpectrum A) := by
    intro hqbar
    have hqbar_asIdeal : qbar.asIdeal = (⊥ : Ideal A) := congrArg PrimeSpectrum.asIdeal hqbar
    have hmap_eq_bot : Ideal.map (Ideal.Quotient.mk p.asIdeal) M = (⊥ : Ideal A) := by
      calc
        Ideal.map (Ideal.Quotient.mk p.asIdeal) M = qbar.asIdeal := by
          symm
          simpa [A, qbar] using
            (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus_symm_asIdeal
              (I := p.asIdeal) ⟨mSpec, hm_zeroLocus⟩)
        _ = (⊥ : Ideal A) := hqbar_asIdeal
    have hM_eq_p : M = p.asIdeal := by
      have hcomap_map :
          Ideal.comap (Ideal.Quotient.mk p.asIdeal)
            (Ideal.map (Ideal.Quotient.mk p.asIdeal) M) = M := by
        calc
          Ideal.comap (Ideal.Quotient.mk p.asIdeal)
              (Ideal.map (Ideal.Quotient.mk p.asIdeal) M) =
                M ⊔ Ideal.comap (Ideal.Quotient.mk p.asIdeal) (⊥ : Ideal A) := by
                  simpa using
                    (Ideal.comap_map_of_surjective (Ideal.Quotient.mk p.asIdeal)
                      Ideal.Quotient.mk_surjective M)
          _ = M ⊔ p.asIdeal := by
                rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
          _ = M := sup_eq_left.mpr hpMle
      calc
        M = Ideal.comap (Ideal.Quotient.mk p.asIdeal)
            (Ideal.map (Ideal.Quotient.mk p.asIdeal) M) := by
              symm
              exact hcomap_map
        _ = Ideal.comap (Ideal.Quotient.mk p.asIdeal) (⊥ : Ideal A) := by rw [hmap_eq_bot]
        _ = p.asIdeal := by
              rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact hMp.ne hM_eq_p.symm
  have hdimA_ge : (1 : WithBot ℕ∞) ≤ ringKrullDim A := by
    have hqbar_height :
        qbar.asIdeal.primeHeight = 1 :=
      primeHeight_eq_one_of_ne_bot_of_basicOpen_eq_singleton_bot
        (A := A) hbasicA qbar hqbar_ne
    calc
      (1 : WithBot ℕ∞) = (qbar.asIdeal.height : WithBot ℕ∞) := by
        simpa [Ideal.height_eq_primeHeight, hqbar_height]
      _ ≤ ringKrullDim A := Ideal.height_le_ringKrullDim_of_ne_top qbar.isPrime.ne_top
  have hdimA : ringKrullDim A = 1 := le_antisymm hdimA_le hdimA_ge
  have hJacobsonA : IsJacobsonRing A :=
    isJacobsonRing_of_isNoetherianRing_of_ringKrullDim_eq_one_of_infinite_primeIdeals
      (R := A) hdimA
  have hbot_nonmax : ¬ (⊥ : Ideal A).IsMaximal := by
    intro hbot_max
    have hsub : Subsingleton (PrimeSpectrum A) := by
      refine ⟨fun q₁ q₂ ↦ ?_⟩
      apply PrimeSpectrum.ext
      have hq₁ : (⊥ : Ideal A) = q₁.asIdeal := hbot_max.eq_of_le q₁.isPrime.ne_top bot_le
      have hq₂ : (⊥ : Ideal A) = q₂.asIdeal := hbot_max.eq_of_le q₂.isPrime.ne_top bot_le
      exact hq₁.symm.trans hq₂
    letI : Finite (PrimeSpectrum A) := Finite.of_subsingleton
    exact Finite.false (inferInstance : Finite (PrimeSpectrum A))
  have hxbar_not_mem_bot : xbar ∉ (⊥ : Ideal A) := by
    -- The singleton basic open is nonempty, so its defining element is nonzero.
    simpa [hbasicA] using
      (PrimeSpectrum.mem_basicOpen xbar (⊥ : PrimeSpectrum A)).1
        (by simpa [hbasicA] : (⊥ : PrimeSpectrum A) ∈
          (PrimeSpectrum.basicOpen xbar : Set (PrimeSpectrum A)))
  have hinfinite_basic :
      Set.Infinite
        (PrimeSpectrum.zeroLocus (R := A) ((⊥ : Ideal A) : Set A) ∩
          (PrimeSpectrum.basicOpen xbar : Set (PrimeSpectrum A))) :=
    infinite_zeroLocus_inter_basicOpen_of_isJacobsonRing
      (R := A) (p := (⊥ : PrimeSpectrum A)) xbar hbot_nonmax hxbar_not_mem_bot
  have hfinite_basic :
      ¬ Set.Infinite
        (PrimeSpectrum.zeroLocus (R := A) ((⊥ : Ideal A) : Set A) ∩
          (PrimeSpectrum.basicOpen xbar : Set (PrimeSpectrum A))) := by
    simpa [PrimeSpectrum.zeroLocus_bot, hbasicA] using
      (Set.not_infinite.mpr (Set.finite_singleton (⊥ : PrimeSpectrum A)))
  exact hfinite_basic hinfinite_basic

end
