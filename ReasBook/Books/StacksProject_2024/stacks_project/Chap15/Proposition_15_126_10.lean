import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_37_11
import StacksProject_2024.stacks_project.Chap10.Lemma_10_105_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_126_9
import StacksProject_2024.stacks_project.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open IsLocalRing

/- Domain-style sampling:
- primary domain: local commutative algebra over Noetherian catenary normal local rings, with the
  normality and catenary hypotheses carried by the chapter ring-level owners;
- sampled owner declarations:
  `IsNormalRing`,
  `IsCatenaryRing`,
  `principalIdeal`,
  `Ideal.IsRadical`;
- best owner abstraction: the ambient ring hypotheses should be expressed through the existing
  chapter owners `IsNormalRing R` and `IsCatenaryRing R`, while principal quotients use the
  Chapter 15 owner `principalIdeal`;
- primitive data vs. derived API:
  primitive data is the radical ideal `J` together with `hJrad : J.IsRadical` and `hJne : J ≠ ⊥`;
  derived API is the existence of a nonzero element of `J` whose principal quotient is reduced.

Source/core/bridge triage:
- `source-facing`: the existence statement for a nonzero element of the given radical ideal;
- `core/canonical`: `IsNormalRing`, `IsCatenaryRing`, `Ideal.IsRadical`, and `principalIdeal`;
- `bridge/view`: none. The local redeclaration of `IsCatenaryRing` would be a duplicate owner and
  should be removed in favor of the chapter owner. -/

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsNormalRing R]
  [IsCatenaryRing R]

/-- Helper for Proposition 15.126.10: a local ring is the localization at the complement of its
maximal ideal. -/
private theorem self_isLocalization_primeCompl_maximalIdeal :
    IsLocalization (maximalIdeal R).primeCompl R := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact IsLocalRing.notMem_maximalIdeal.mp y.2
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y hxy
    exact ⟨1, by simpa using hxy⟩

attribute [local instance] self_isLocalization_primeCompl_maximalIdeal

/-- Helper for Proposition 15.126.10: a Noetherian local normal ring is a domain. -/
private theorem local_normal_ring_isDomain :
    IsDomain R := by
  let e : Localization.AtPrime (maximalIdeal R) ≃ₐ[R] R :=
    Localization.algEquiv (maximalIdeal R).primeCompl R
  -- Transport the domain structure from the maximal-ideal localization back to `R`.
  exact Function.Injective.isDomain e.symm e.symm.injective

attribute [local instance] local_normal_ring_isDomain

/-- Helper for Proposition 15.126.10: a nonzero ideal contains a nonzero element. -/
private theorem exists_mem_ne_zero_of_ne_bot
    (J : Ideal R) (hJne : J ≠ ⊥) :
    ∃ x : R, x ∈ J ∧ x ≠ 0 := by
  have hlt : (⊥ : Ideal R) < J := bot_lt_iff_ne_bot.mpr hJne
  rcases SetLike.exists_of_lt hlt with ⟨x, hxJ, hx0⟩
  refine ⟨x, hxJ, ?_⟩
  intro hx
  exact hx0 (hx ▸ Ideal.zero_mem _)

/-- Helper for Proposition 15.126.10: a positive-dimensional local ring is not a field, hence its
maximal ideal contains a nonzero element. -/
private theorem exists_mem_maximalIdeal_ne_zero_of_not_isField
    (hR : ¬ IsField R) :
    ∃ x : R, x ∈ maximalIdeal R ∧ x ≠ 0 := by
  have hm_ne : maximalIdeal R ≠ (⊥ : Ideal R) := by
    intro hbot
    exact hR ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr hbot)
  have hlt : (⊥ : Ideal R) < maximalIdeal R := bot_lt_iff_ne_bot.mpr hm_ne
  rcases SetLike.exists_of_lt hlt with ⟨x, hxmem, hxnotmem⟩
  refine ⟨x, hxmem, ?_⟩
  intro hx0
  exact hxnotmem (hx0 ▸ Ideal.zero_mem _)

/-- Helper for Proposition 15.126.10: a zero-dimensional local normal ring is a field. -/
private theorem zero_dim_local_normal_ring_isField
    (hdim : ringKrullDim R = 0) :
    IsField R := by
  have hmax_primeHeight_zero' : ((maximalIdeal R).primeHeight : WithBot ℕ∞) = 0 := by
    simpa [IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim] using hdim
  have hmax_primeHeight_zero : (maximalIdeal R).primeHeight = 0 := by
    exact_mod_cast hmax_primeHeight_zero'
  have hmax_min : maximalIdeal R ∈ minimalPrimes R :=
    (Ideal.primeHeight_eq_zero_iff (I := maximalIdeal R)).mp hmax_primeHeight_zero
  have hmax_eq_bot : maximalIdeal R = (⊥ : Ideal R) := by
    simpa [IsDomain.minimalPrimes_eq_singleton_bot] using hmax_min
  -- A local domain with trivial maximal ideal is a field.
  exact (IsLocalRing.isField_iff_maximalIdeal_eq).mpr hmax_eq_bot

/-- Helper for Proposition 15.126.10: in Krull dimension `0`, a nonzero radical ideal is all of
`R`, so `f = 1` already gives a reduced principal quotient. -/
private theorem exists_nonzero_mem_radicalIdeal_with_reduced_principal_quotient_of_zero_dim
    (J : Ideal R) (hJne : J ≠ ⊥) (hdim : ringKrullDim R = 0) :
    ∃ f : R, f ≠ 0 ∧ f ∈ J ∧ IsReduced (R ⧸ principalIdeal f) := by
  have hfield : IsField R :=
    zero_dim_local_normal_ring_isField (R := R) hdim
  letI : Field R := IsField.toField hfield
  -- A nonzero ideal in a field is the unit ideal, so `1` lies in `J`.
  rcases exists_mem_ne_zero_of_ne_bot (R := R) J hJne with ⟨x, hxJ, hx0⟩
  have hJ_top : J = ⊤ := by
    exact J.eq_top_of_isUnit_mem hxJ (isUnit_iff_ne_zero.mpr hx0)
  have htop_rad : (⊤ : Ideal R).IsRadical := by
    simpa [Ideal.IsRadical, Ideal.radical_top]
  have hred_top : IsReduced (R ⧸ (⊤ : Ideal R)) :=
    (Ideal.isRadical_iff_quotient_reduced (⊤ : Ideal R)).1 htop_rad
  have hspan_top : principalIdeal (1 : R) = ⊤ := by
    simpa [principalIdeal] using (Ideal.span_singleton_eq_top.mpr isUnit_one)
  refine ⟨1, one_ne_zero, ?_, ?_⟩
  · simpa [hJ_top]
  · rw [hspan_top]
    exact hred_top

/-- Helper for Proposition 15.126.10: in positive dimension, the radical ideal contains a nonzero
maximal-ideal element that can serve as the source-proof perturbation seed. -/
private theorem exists_nonzero_mem_radicalIdeal_and_maximalIdeal_of_pos_dim
    (J : Ideal R) {d : ℕ} (hdim : ringKrullDim R = d.succ) (hJne : J ≠ ⊥) :
    ∃ f0 : maximalIdeal R, (f0 : R) ∈ J ∧ (f0 : R) ≠ 0 := by
  by_cases hJtop : J = ⊤
  · have hdim_ne_zero : ringKrullDim R ≠ 0 := by
      intro hzero
      rw [hdim] at hzero
      have hsucc_ne_zero :
          ((((Nat.succ d : ℕ) : ℕ∞) : WithBot ℕ∞)) ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero d)
      exact hsucc_ne_zero hzero
    have hnotField : ¬ IsField R := by
      intro hfield
      exact hdim_ne_zero (ringKrullDim_eq_zero_of_isField hfield)
    rcases exists_mem_maximalIdeal_ne_zero_of_not_isField (R := R) hnotField with
      ⟨x, hxmax, hx0⟩
    refine ⟨⟨x, hxmax⟩, ?_, hx0⟩
    simpa [hJtop]
  · have hJ_le_max : J ≤ maximalIdeal R :=
      le_maximalIdeal hJtop
    rcases exists_mem_ne_zero_of_ne_bot (R := R) J hJne with ⟨x, hxJ, hx0⟩
    refine ⟨⟨x, hJ_le_max hxJ⟩, hxJ, hx0⟩

/-- Helper for Proposition 15.126.10: in the present local normal domain, every nonzero element
avoids all minimal primes. -/
private theorem nonzero_not_mem_minimalPrimes {x : R} (hx : x ≠ 0) :
    ∀ p ∈ minimalPrimes R, x ∉ p := by
  intro p hp hxmem
  have hp_eq_bot : p = (⊥ : Ideal R) := by
    simpa [IsDomain.minimalPrimes_eq_singleton_bot] using hp
  exact hx (by simpa [hp_eq_bot] using hxmem)

/-- Helper for Proposition 15.126.10: the score of a perturbation is the number of minimal
primes of its principal quotient. -/
private noncomputable def perturbation_branch_count
    (f0 h : maximalIdeal R) : ℕ :=
  (minimalPrimes (R ⧸ principalIdeal (((f0 + h : maximalIdeal R) : R)))).encard.toNat

/-- Helper for Proposition 15.126.10: any uniformly bounded natural-valued score on the nonzero
perturbations of `f0` attains a maximum. -/
private theorem exists_maximizing_nonzero_perturbation_score
    (J : Ideal R) (f0 : maximalIdeal R) (N : ℕ) (score : maximalIdeal R → ℕ)
    (hf0ne : ((f0 : maximalIdeal R) : R) ≠ 0) (B : ℕ)
    (hbound : ∀ h : maximalIdeal R,
      (h : R) ∈ J → (h : R) ∈ maximalIdeal R ^ (N + 1) →
        (((f0 + h : maximalIdeal R) : R) ≠ 0) → score h ≤ B) :
    ∃ hmax : maximalIdeal R,
      (hmax : R) ∈ J ∧
        (hmax : R) ∈ maximalIdeal R ^ (N + 1) ∧
        (((f0 + hmax : maximalIdeal R) : R) ≠ 0) ∧
        ∀ h : maximalIdeal R, (h : R) ∈ J → (h : R) ∈ maximalIdeal R ^ (N + 1) →
          (((f0 + h : maximalIdeal R) : R) ≠ 0) → score h ≤ score hmax := by
  classical
  let good : ℕ → Prop := fun m ↦
    ∃ h : maximalIdeal R,
      (h : R) ∈ J ∧
        (h : R) ∈ maximalIdeal R ^ (N + 1) ∧
        (((f0 + h : maximalIdeal R) : R) ≠ 0) ∧
        score h = m
  have hzeroJ : ((0 : maximalIdeal R) : R) ∈ J := Ideal.zero_mem _
  have hzeroPow : ((0 : maximalIdeal R) : R) ∈ maximalIdeal R ^ (N + 1) := by
    exact Ideal.zero_mem _
  have hzeroNe : (((f0 + (0 : maximalIdeal R) : maximalIdeal R) : R)) ≠ 0 := by
    simpa using hf0ne
  have hscore0_le : score (0 : maximalIdeal R) ≤ B :=
    hbound 0 hzeroJ hzeroPow hzeroNe
  have hgood0 : good (score (0 : maximalIdeal R)) := by
    exact ⟨0, hzeroJ, hzeroPow, hzeroNe, rfl⟩
  let mmax := Nat.findGreatest good B
  have hmmax_good : good mmax := by
    exact Nat.findGreatest_spec hscore0_le hgood0
  rcases hmmax_good with ⟨hmax, hhmaxJ, hhmaxPow, hhmaxNe, hhmaxScore⟩
  refine ⟨hmax, hhmaxJ, hhmaxPow, hhmaxNe, ?_⟩
  intro h hhJ hhPow hhNe
  have hscore_le : score h ≤ B := hbound h hhJ hhPow hhNe
  have hgood_h : good (score h) := by
    exact ⟨h, hhJ, hhPow, hhNe, rfl⟩
  calc
    score h ≤ mmax := Nat.le_findGreatest hscore_le hgood_h
    _ = score hmax := hhmaxScore.symm

/-- Helper for Proposition 15.126.10: Lemma `15.126.8` should bound the branch count of each
nonzero perturbation by the fixed parameter-ideal length coming from Lemma `15.126.9`. -/
private theorem nonzero_perturbation_branch_count_le_fixed_length
    (J : Ideal R) {d N : ℕ} (f0 : maximalIdeal R) (y : Fin d → maximalIdeal R)
    (hsop : IsSystemOfParameters (Fin.cons f0 y))
    (hstable : ∀ h : maximalIdeal R, ((h : R) ∈ maximalIdeal R ^ (N + 1)) →
      IsSystemOfParameters (Fin.cons (f0 + h) y) ∧
        Module.length R (R ⧸ parameterIdeal (Fin.cons f0 y)) =
          Module.length R (R ⧸ parameterIdeal (Fin.cons (f0 + h) y))) :
    ∀ h : maximalIdeal R, (h : R) ∈ J → (h : R) ∈ maximalIdeal R ^ (N + 1) →
      (((f0 + h : maximalIdeal R) : R) ≠ 0) →
      perturbation_branch_count (R := R) f0 h ≤
        (Module.length R (R ⧸ parameterIdeal (Fin.cons f0 y))).toNat := by
  -- TODO: set `A = R ⧸ principalIdeal (f0 + h)` and apply Lemma `15.126.8` to `A`.
  -- The catenary input should identify every minimal prime of `A` with a top-dimensional branch,
  -- while Lemma `15.126.9` transports the quotient length back to the fixed parameter family.
  let _ := hsop
  let _ := hstable
  let _ := J
  sorry

/-- Helper for Proposition 15.126.10: once a nonzero perturbation maximizes the branch count, one
further source-faithful correction inside `J ∩ maximalIdeal R ^ (N + 1)` should produce a reduced
principal quotient. -/
private theorem exists_reduced_nonzero_perturbation_of_maximizer
    (J : Ideal R) (hJrad : J.IsRadical) {d N : ℕ} (f0 : maximalIdeal R)
    (y : Fin d → maximalIdeal R) (hsop : IsSystemOfParameters (Fin.cons f0 y))
    (hstable : ∀ h : maximalIdeal R, ((h : R) ∈ maximalIdeal R ^ (N + 1)) →
      IsSystemOfParameters (Fin.cons (f0 + h) y) ∧
        Module.length R (R ⧸ parameterIdeal (Fin.cons f0 y)) =
          Module.length R (R ⧸ parameterIdeal (Fin.cons (f0 + h) y)))
    {hmax : maximalIdeal R}
    (hhmaxJ : (hmax : R) ∈ J)
    (hhmaxPow : (hmax : R) ∈ maximalIdeal R ^ (N + 1))
    (hhmaxNe : (((f0 + hmax : maximalIdeal R) : R) ≠ 0))
    (hmaximal : ∀ h : maximalIdeal R, (h : R) ∈ J → (h : R) ∈ maximalIdeal R ^ (N + 1) →
      (((f0 + h : maximalIdeal R) : R) ≠ 0) →
      perturbation_branch_count (R := R) f0 h ≤
        perturbation_branch_count (R := R) f0 hmax) :
    ∃ hgood : maximalIdeal R,
      (hgood : R) ∈ J ∧
        (hgood : R) ∈ maximalIdeal R ^ (N + 1) ∧
        (((f0 + hgood : maximalIdeal R) : R) ≠ 0) ∧
        IsReduced (R ⧸ principalIdeal (((f0 + hgood : maximalIdeal R) : R))) := by
  -- Route correction: the source proof does not show that the maximizing perturbation itself is
  -- reduced. It performs one more symbolic-power correction inside `J ∩ maximalIdeal R ^ (N + 1)`
  -- and then uses maximality to rule out new branches.
  -- TODO: enumerate the old height-one branches of `principalIdeal (((f0 + hmax : maximalIdeal R)
  -- : R))`, build the symbolic-power correction inside `J ∩ maximalIdeal R ^ (N + 1)`, and then
  -- use maximality of `perturbation_branch_count` to show the corrected perturbation has order
  -- `1` on every old branch and hence reduced principal quotient.
  let _ := hJrad
  let _ := hsop
  let _ := hstable
  let _ := hhmaxJ
  let _ := hhmaxPow
  let _ := hhmaxNe
  let _ := hmaximal
  sorry

/-- Helper for Proposition 15.126.10: the positive-dimensional catenary case is the remaining
source-faithful perturbation argument. -/
private theorem exists_nonzero_mem_radicalIdeal_with_reduced_principal_quotient_of_pos_dim
    (J : Ideal R) (hJrad : J.IsRadical) {d : ℕ} (hdim : ringKrullDim R = d.succ)
    (hJne : J ≠ ⊥) :
    ∃ f : R, f ≠ 0 ∧ f ∈ J ∧ IsReduced (R ⧸ principalIdeal f) := by
  -- Route correction: the zero-dimensional branch is handled separately in the main theorem.
  -- The remaining source route must still implement the catenary perturbation-maximization
  -- argument through Lemmas `15.126.8` and `15.126.9`.
  rcases exists_nonzero_mem_radicalIdeal_and_maximalIdeal_of_pos_dim
      (R := R) J hdim hJne with ⟨f0, hf0J, hf0ne⟩
  have hf0_not_mem_minimalPrimes :
      ∀ p ∈ minimalPrimes R, ((f0 : maximalIdeal R) : R) ∉ p :=
    nonzero_not_mem_minimalPrimes (R := R) hf0ne
  rcases
    exists_systemOfParameters_stable_under_highOrder_perturbation_of_not_mem_minimalPrimes
      (R := R) hdim f0 hf0_not_mem_minimalPrimes with
    ⟨y, N, hsop, hstable⟩
  have hbound :
      ∀ h : maximalIdeal R, (h : R) ∈ J → (h : R) ∈ maximalIdeal R ^ (N + 1) →
        (((f0 + h : maximalIdeal R) : R) ≠ 0) →
        perturbation_branch_count (R := R) f0 h ≤
          (Module.length R (R ⧸ parameterIdeal (Fin.cons f0 y))).toNat :=
    nonzero_perturbation_branch_count_le_fixed_length
      (R := R) J f0 y hsop hstable
  rcases exists_maximizing_nonzero_perturbation_score
      (R := R) J f0 N (perturbation_branch_count (R := R) f0) hf0ne
      (Module.length R (R ⧸ parameterIdeal (Fin.cons f0 y))).toNat hbound with
    ⟨hmax, hhmaxJ, hhmaxPow, hhmaxNe, hmaximal⟩
  rcases exists_reduced_nonzero_perturbation_of_maximizer
      (R := R) J hJrad f0 y hsop hstable hhmaxJ hhmaxPow hhmaxNe hmaximal with
    ⟨hgood, hhgoodJ, hhgoodPow, hhgoodNe, hhgoodRed⟩
  let f : R := ((f0 + hgood : maximalIdeal R) : R)
  have hfJ : f ∈ J := by
    -- The corrected perturbation still lies in `J`, so adding it to the seed stays in `J`.
    change ((f0 : R) + (hgood : R)) ∈ J
    exact J.add_mem hf0J hhgoodJ
  have hred : IsReduced (R ⧸ principalIdeal f) := by
    -- The new helper now returns the corrected perturbation directly in the source proof shape.
    simpa [f] using hhgoodRed
  exact ⟨f, hhgoodNe, hfJ, hred⟩

-- Proof sketch: imitate Lemma `15.126.5` using the catenary version of the perturbation argument.
-- Start with a nonzero element of the nonzero radical ideal `J`, use the stable perturbation
-- family from Lemma `15.126.9`, and bound the number of minimal primes of the perturbed principal
-- quotients via Lemma `15.126.8`. Choosing a perturbation with maximal number of minimal primes
-- forces every height-one valuation multiplicity to become `1`, which is equivalent to the
-- reducedness of the principal quotient.
/-- Proposition 15.126.10: if `J` is a nonzero radical ideal in a catenary Noetherian local normal
domain, then `J` contains a nonzero element whose principal quotient is reduced. -/
theorem exists_nonzero_mem_radicalIdeal_with_reduced_principal_quotient
    (J : Ideal R) (hJrad : J.IsRadical) (hJne : J ≠ ⊥) :
    ∃ f : R, f ≠ 0 ∧ f ∈ J ∧ IsReduced (R ⧸ principalIdeal f) := by
  -- Route correction: the zero-dimensional branch is now isolated in the helper above.
  -- The unresolved work is the source-faithful positive-dimensional perturbation argument that
  -- maximizes the branch count using Lemmas `15.126.8` and `15.126.9`.
  have hdim_eq :
      ringKrullDim R =
        ((((ringKrullDim R).unbotD 0).toNat : ℕ∞) : WithBot ℕ∞) := by
    have hbot : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
    have htop : ringKrullDim R ≠ ⊤ := ringKrullDim_ne_top
    cases hs : ringKrullDim R with
    | bot =>
        exact (hbot hs).elim
    | coe d =>
        have hd_ne_top : d ≠ ⊤ := by
          intro hd_top
          exact htop <| by simp [hs, hd_top]
        simpa [hs] using
          congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hd_ne_top).symm
  by_cases hzero : ((ringKrullDim R).unbotD 0).toNat = 0
  · -- In dimension `0`, the earlier helper reduces the statement to the field case.
    have hdim_zero : ringKrullDim R = 0 := by
      simpa [hzero] using hdim_eq
    exact
      exists_nonzero_mem_radicalIdeal_with_reduced_principal_quotient_of_zero_dim
        (R := R) J hJne hdim_zero
  · -- Otherwise the finite dimension is a successor, so the positive-dimensional helper applies.
    obtain ⟨d, hd⟩ :
        ∃ d : ℕ, ((ringKrullDim R).unbotD 0).toNat = d.succ :=
      Nat.exists_eq_succ_of_ne_zero hzero
    have hdim_succ : ringKrullDim R = d.succ := by
      simpa [hd] using hdim_eq
    exact
      exists_nonzero_mem_radicalIdeal_with_reduced_principal_quotient_of_pos_dim
        (R := R) J hJrad hdim_succ hJne

end
