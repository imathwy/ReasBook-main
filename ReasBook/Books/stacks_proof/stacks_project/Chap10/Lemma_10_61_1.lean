import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_60_13

-- Declarations for this item will be appended below by the statement pipeline.

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
@[stacks 02IG]
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
