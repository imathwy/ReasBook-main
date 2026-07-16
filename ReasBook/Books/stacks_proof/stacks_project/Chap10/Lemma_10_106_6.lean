import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_103_8
import stacks_proof.stacks_project.Chap10.Lemma_10_63_2
import stacks_proof.stacks_project.Chap10.Lemma_10_72_9
import stacks_proof.stacks_project.Chap10.Lemma_10_103_5
import stacks_proof.stacks_project.Chap10.Lemma_10_103_6
import stacks_proof.stacks_project.Chap10.Lemma_10_106_5
import stacks_proof.stacks_project.Chap10.Definition_10_60_10
import stacks_proof.stacks_project.Chap10.Lemma_10_60_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing
open RingTheory Sequence
open scoped ENat Pointwise

section

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

/-
Domain triage:
* primary domain: maximal Cohen-Macaulay modules over regular local rings;
* sampled owner declarations:
  `Module.MaximalCohenMacaulay`,
  `hasFiniteFreeResolutionLengthLE_of_moduleDepth_of_isRegularLocalRing`,
  `hasFiniteFreeResolutionLengthLE_zero_iff`,
  `IsRegularLocalRing.spanFinrank_maximalIdeal`;
* owner abstraction: the ambient owner predicates `Module.MaximalCohenMacaulay R M` and
  `IsRegularLocalRing R`;
* layer: `source-facing`, with the finite-free-resolution owner API providing the canonical bridge
  to freeness.
-/

-- Proof sketch: `IsRegularLocalRing.spanFinrank_maximalIdeal` identifies `ringKrullDim R` with a
-- natural number `d = (maximalIdeal R).spanFinrank`, and the maximal Cohen-Macaulay hypothesis
-- gives the same value for `moduleDepth R M`. Proposition `10.110.1` then yields a finite free
-- resolution of `M` of length at most `d - d = 0`, which is exactly freeness by the owner
-- definition of `HasFiniteFreeResolutionLengthLE`.
/-- Helper for Lemma 10.106.6: a maximal Cohen-Macaulay module over a regular local ring has
depth equal to the span finrank of the maximal ideal. -/
lemma moduleDepth_eq_spanFinrank_maximalIdeal_of_maximalCohenMacaulay
    (hMCM : Module.MaximalCohenMacaulay R M) :
    moduleDepth R M = (maximalIdeal R).spanFinrank := by
  -- Rewrite both the module depth and the ring dimension into the same `WithBot ℕ∞` value.
  have hdepth_cast :
      ((moduleDepth R M : ℕ∞) : WithBot ℕ∞) =
        (((maximalIdeal R).spanFinrank : ℕ∞) : WithBot ℕ∞) := by
    calc
      ((moduleDepth R M : ℕ∞) : WithBot ℕ∞) = ringKrullDim R :=
        hMCM.depth_eq_ringKrullDim
      _ = (((maximalIdeal R).spanFinrank : ℕ∞) : WithBot ℕ∞) := by
        simpa using (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  -- Remove the outer coercion to recover the desired equality in `ℕ∞`.
  exact WithBot.coe_inj.mp hdepth_cast

/-- Helper for Lemma 10.106.6: a zero-dimensional regular local ring is a field. -/
lemma isField_of_isRegularLocalRing_of_ringKrullDim_eq_zero
    (hdim : ringKrullDim R = 0) :
    IsField R := by
  have hspan : (maximalIdeal R).spanFinrank = 0 := by
    simpa [hdim] using IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  have hfg : (maximalIdeal R).FG := (maximalIdeal R).fg_of_isNoetherianRing
  have hbot : maximalIdeal R = ⊥ :=
    (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).1 hspan
  exact (IsLocalRing.isField_iff_maximalIdeal_eq (R := R)).2 hbot

/-- Helper for Lemma 10.106.6: the dimension-zero case is immediate because the ring is a field. -/
lemma free_of_maximalCohenMacaulay_of_ringKrullDim_eq_zero
    (hdim : ringKrullDim R = 0) (hMCM : Module.MaximalCohenMacaulay R M) :
    Module.Free R M := by
  let _ : Field R := (isField_of_isRegularLocalRing_of_ringKrullDim_eq_zero
    (R := R) hdim).toField
  infer_instance

/-- Helper for Lemma 10.106.6: a one-step equality in `WithBot ℕ∞` with finite target recovers
the predecessor value. -/
lemma withBotENat_eq_nat_pred_of_add_one_eq_nat {x : WithBot ℕ∞} {d : ℕ}
    (h : x + 1 = d) :
    x = (d - 1 : ℕ) := by
  -- Split on whether `x` is bottom or an actual extended natural number.
  cases hx : x with
  | bot =>
      simp [hx] at h
  | coe n =>
      apply WithBot.coe_inj.mp
      have hn_cast :
          ((((n : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) = ((d : ℕ∞) : WithBot ℕ∞)) := by
        simpa [hx] using h
      have hn : (n : ℕ∞) + 1 = d :=
        WithBot.coe_inj.mp hn_cast
      have hn_ne_top : (n : ℕ∞) ≠ ⊤ := by
        intro hn_top
        have htop : (⊤ : ℕ∞) = d := by
          simpa [hn_top] using hn
        simpa using htop
      have hnat : ENat.toNat (n : ℕ∞) + 1 = d := by
        have hnat' := congrArg ENat.toNat hn
        calc
          ENat.toNat (n : ℕ∞) + 1 = ENat.toNat ((n : ℕ∞) + (1 : ℕ∞)) := by
            symm
            simpa using ENat.toNat_add hn_ne_top (by simp : (1 : ℕ∞) ≠ ⊤)
          _ = d := by
            simpa using hnat'
      have hnat_sub : ENat.toNat (n : ℕ∞) = d - 1 := by
        omega
      rw [← ENat.coe_toNat hn_ne_top, hnat_sub]
      rfl

/-- Helper for Lemma 10.106.6: in a Cohen-Macaulay local module, a one-step support-dimension
drop forces the quotient element into the maximal ideal. -/
lemma mem_maximalIdeal_of_supportDim_quotSMulTop_add_one_eq
    [Module.CohenMacaulay R M] {g : R}
    (hdim : Module.supportDim R (QuotSMulTop g M) + 1 = Module.supportDim R M) :
    g ∈ maximalIdeal R := by
  -- A unit would make the quotient zero, contradicting the Cohen-Macaulay support identity.
  by_contra hg
  have hg_unit : IsUnit g := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hg
    exact not_not.mp hg
  have hsmul_top : g • (⊤ : Submodule R M) = ⊤ := by
    refine top_unique ?_
    intro m hm
    rcases hg_unit with ⟨u, rfl⟩
    rw [Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨(↑u⁻¹ : R) • m, by simp, ?_⟩
    simp [smul_smul]
  have hquot_subsingleton : Subsingleton (QuotSMulTop g M) := by
    rw [Submodule.Quotient.subsingleton_iff]
    simpa using hsmul_top
  let _ : Subsingleton (QuotSMulTop g M) := hquot_subsingleton
  have hquot_bot : Module.supportDim R (QuotSMulTop g M) = ⊥ := by
    simpa using Module.supportDim_eq_bot_of_subsingleton (R := R) (M := QuotSMulTop g M)
  have hM_bot : Module.supportDim R M = ⊥ := by
    simpa [hquot_bot] using hdim.symm
  simpa [hM_bot] using
    (Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := M))

/-- Helper for Lemma 10.106.6: every associated prime of a Cohen-Macaulay module realizes the
full support dimension. -/
lemma ringKrullDim_quotient_eq_supportDim_of_mem_associatedPrimes_of_cohenMacaulay
    [Module.CohenMacaulay R M] (p : Ideal R) (hp : p ∈ associatedPrimes R M) :
    ringKrullDim (R ⧸ p) = Module.supportDim R M := by
  -- Compare the associated-prime depth lower bound with the annihilator quotient upper bound.
  have hlower :
      ((moduleDepth R M : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) :=
    moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes (R := R) (M := M) p hp
  have hlower' : Module.supportDim R M ≤ ringKrullDim (R ⧸ p) := by
    simpa [Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := M)] using hlower
  have hp_support :
      (⟨p, (AssociatedPrimes.mem_iff.mp hp).isPrime⟩ : PrimeSpectrum R) ∈ Module.support R M :=
    Module.associatedPrimes_subset_support (R := R) (M := M) (by simpa using hp)
  have hann_le : Module.annihilator R M ≤ p :=
    Module.annihilator_le_of_mem_support hp_support
  have hup : ringKrullDim (R ⧸ p) ≤ Module.supportDim R M := by
    rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator (R := R) (M := M)]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hann_le)
      (Ideal.Quotient.factor_surjective hann_le)
  exact le_antisymm hup hlower'

/-- Helper for Lemma 10.106.6: in a Cohen-Macaulay local module, a one-step support-dimension
drop along `g` forces `g` to be a nonzerodivisor. -/
lemma isSMulRegular_of_supportDim_quotSMulTop_add_one_eq_of_cohenMacaulay
    [Module.CohenMacaulay R M] {g : R}
    (hdim : Module.supportDim R (QuotSMulTop g M) + 1 = Module.supportDim R M) :
    IsSMulRegular M g := by
  have hg_mem : g ∈ maximalIdeal R :=
    mem_maximalIdeal_of_supportDim_quotSMulTop_add_one_eq (R := R) (M := M) hdim
  -- Exclude `g` from every associated prime by comparing quotient dimensions.
  have hg_not_mem_union : g ∉ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    intro hg_union
    rcases Set.mem_iUnion.1 hg_union with ⟨p, hp⟩
    rcases Set.mem_iUnion.1 hp with ⟨hp_assoc, hg_mem_p⟩
    let p' : PrimeSpectrum R := ⟨p, (AssociatedPrimes.mem_iff.mp hp_assoc).isPrime⟩
    have hp_supportM : p' ∈ Module.support R M :=
      Module.associatedPrimes_subset_support (R := R) (M := M) (by simpa using hp_assoc)
    have hp_zeroLocus : p' ∈ PrimeSpectrum.zeroLocus ({g} : Set R) := by
      exact (PrimeSpectrum.mem_zeroLocus p' ({g} : Set R)).2
        (Set.singleton_subset_iff.mpr hg_mem_p)
    have hp_supportQuot : p' ∈ Module.support R (QuotSMulTop g M) := by
      simpa [Module.support_quotSMulTop] using And.intro hp_supportM hp_zeroLocus
    have hquot_le : ringKrullDim (R ⧸ p) ≤ Module.supportDim R (QuotSMulTop g M) := by
      have hann_le : Module.annihilator R (QuotSMulTop g M) ≤ p :=
        Module.annihilator_le_of_mem_support hp_supportQuot
      rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator (R := R) (M := QuotSMulTop g M)]
      exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hann_le)
        (Ideal.Quotient.factor_surjective hann_le)
    have hp_dim : ringKrullDim (R ⧸ p) = Module.supportDim R M :=
      ringKrullDim_quotient_eq_supportDim_of_mem_associatedPrimes_of_cohenMacaulay
        (R := R) (M := M) p hp_assoc
    have hle : Module.supportDim R M ≤ Module.supportDim R (QuotSMulTop g M) := by
      calc
        Module.supportDim R M = ringKrullDim (R ⧸ p) := hp_dim.symm
        _ ≤ Module.supportDim R (QuotSMulTop g M) := hquot_le
    have hnot :
        ¬ Module.supportDim R M ≤ Module.supportDim R (QuotSMulTop g M) := by
      cases hq : Module.supportDim R (QuotSMulTop g M) with
      | bot =>
          have hM_bot : Module.supportDim R M = ⊥ := by
            simpa [hq] using hdim.symm
          have : False := by
            simpa [hM_bot] using
              (Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := M))
          exact False.elim this
      | coe n =>
          let _ : Nontrivial (R ⧸ p) :=
            Ideal.Quotient.nontrivial_iff.mpr (AssociatedPrimes.mem_iff.mp hp_assoc).isPrime.ne_top
          have hM_ne_top : Module.supportDim R M ≠ ⊤ := by
            let _ : IsLocalRing (R ⧸ p) :=
              IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
            intro htop
            have htop' : ringKrullDim (R ⧸ p) = ⊤ := by
              simpa [hp_dim] using htop
            exact ringKrullDim_ne_top htop'
          have hn_ne_top : (n : ℕ∞) ≠ ⊤ := by
            intro hn_top
            have hM_top : Module.supportDim R M = ⊤ := by
              calc
                Module.supportDim R M = Module.supportDim R (QuotSMulTop g M) + 1 := hdim.symm
                _ = (((⊤ : ℕ∞) : WithBot ℕ∞) + 1) := by rw [hq, hn_top]
                _ = ⊤ := by rfl
            exact hM_ne_top hM_top
          exact fun hle' ↦
            (lt_irrefl (n : ℕ∞)) <|
              (ENat.add_one_le_iff hn_ne_top).1 <| by
                have hle'' :
                    (((n : ℕ∞) : WithBot ℕ∞) + 1) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by
                  calc
                    (((n : ℕ∞) : WithBot ℕ∞) + 1) = Module.supportDim R M := by
                      simpa [hq] using hdim
                    _ ≤ ((n : ℕ∞) : WithBot ℕ∞) := by
                      simpa [hq] using hle'
                exact_mod_cast hle''
    exact hnot hle
  -- Avoiding the union of associated primes is exactly the nonzerodivisor criterion.
  simpa [Set.mem_compl_iff, biUnion_associatedPrimes_eq_compl_regular R M] using hg_not_mem_union

/-- Helper for Lemma 10.106.6: a length-one parameter ideal is the principal ideal generated by
its unique entry. -/
lemma parameterIdeal_fin1_eq_span_singleton
    (y : Fin 1 → maximalIdeal R) :
    IsLocalRing.parameterIdeal y = Ideal.span ({(y 0 : R)} : Set R) := by
  -- The range of a map out of `Fin 1` is the singleton consisting of its zeroth value.
  have hrange :
      Set.range (fun i ↦ (y i : R)) = ({(y 0 : R)} : Set R) := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      simp
    · intro hr
      rcases Set.mem_singleton_iff.mp hr with rfl
      exact ⟨0, rfl⟩
  rw [IsLocalRing.parameterIdeal_eq_span]
  simp [hrange]

/-- Helper for Lemma 10.106.6: restricting scalars along a surjective algebra map preserves
support dimension. -/
lemma supportDim_eq_of_surjective_algebraMap
    {A : Type*} {B : Type*} {N : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite A N] [Module.Finite B N]
    (hsurj : Function.Surjective (algebraMap A B)) :
    Module.supportDim A N = Module.supportDim B N := by
  -- Compare both support dimensions through the annihilator quotient presentations.
  have hann :
      Ideal.comap (algebraMap A B) (Module.annihilator B N) = Module.annihilator A N :=
    Module.comap_annihilator (R₀ := A) (R := B) (M := N)
  have hann_le :
      Module.annihilator A N ≤ Ideal.comap (algebraMap A B) (Module.annihilator B N) :=
    hann.symm.le
  have hann_ge :
      Ideal.comap (algebraMap A B) (Module.annihilator B N) ≤ Module.annihilator A N :=
    hann.le
  let φ : A ⧸ Module.annihilator A N →+* B ⧸ Module.annihilator B N :=
    Ideal.quotientMap (Module.annihilator B N) (algebraMap A B) hann_le
  have hφinj : Function.Injective φ :=
    Ideal.quotientMap_injective' hann_ge
  have hφsurj : Function.Surjective φ :=
    Ideal.quotientMap_surjective hsurj
  let e : A ⧸ Module.annihilator A N ≃+* B ⧸ Module.annihilator B N :=
    RingEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator,
    ringKrullDim_eq_of_ringEquiv e]

omit [IsRegularLocalRing R] in
/-- Helper for Lemma 10.106.6: the quotient `M / aM` is naturally annihilated by `(a)`, so it
carries the canonical `R ⧸ (a)`-module structure. -/
lemma quotSMulTop_torsionBySet_head_parameter
    (a : R) :
    Module.IsTorsionBySet R (QuotSMulTop a M) (Ideal.span ({a} : Set R)) := by
  -- The quotient by `a • ⊤` is exactly the canonical module killed by the principal ideal `(a)`.
  rw [← Module.isTorsionBySet_iff_is_torsion_by_span (R := R) (M := QuotSMulTop a M)
    ({a} : Set R)]
  rw [Module.isTorsionBySet_singleton_iff]
  simpa using (Module.isTorsionBy_quotient_element_smul (R := R) (M := M) a)

/-- Helper for Lemma 10.106.6: an element of the maximal ideal does not generate the unit ideal. -/
lemma span_singleton_ne_top_of_mem_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] (a : A)
    (ha : a ∈ maximalIdeal A) :
    Ideal.span ({a} : Set A) ≠ ⊤ := by
  intro htop
  have ha_nonunit : ¬ IsUnit a := by
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
  exact ha_nonunit (Ideal.span_singleton_eq_top.mp htop)

/-- Helper for Lemma 10.106.6: quotienting by the head parameter of a regular system of
parameters stays regular local and lowers the dimension by one. -/
lemma head_parameter_quotient_regular_local_and_dim
    {d : ℕ} {x : Fin (d + 1) → maximalIdeal R}
    (hx : IsLocalRing.IsRegularSystemOfParameters x) :
    let a : R := (x 0 : R)
    let S := R ⧸ Ideal.span ({a} : Set R)
    IsRegularLocalRing S ∧ ringKrullDim S = d := by
  let a : R := (x 0 : R)
  let I : Ideal R := Ideal.span ({a} : Set R)
  let S := R ⧸ I
  have hI_ne_top : I ≠ ⊤ := by
    simpa [I, a] using span_singleton_ne_top_of_mem_maximalIdeal (A := R) a (x 0).2
  letI : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hI_ne_top
  letI : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmaxmap : Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal S := by
    -- The quotient map identifies the image of the maximal ideal with the quotient maximal ideal.
    exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hxbar_mem :
      ∀ i : Fin d,
        Ideal.Quotient.mk I (((x i.succ : maximalIdeal R) : R)) ∈ maximalIdeal S := by
    intro i
    have hmem :
        Ideal.Quotient.mk I (((x i.succ : maximalIdeal R) : R)) ∈
          Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) := by
      refine (Ideal.mem_map_iff_of_surjective (f := Ideal.Quotient.mk I)
        (hf := Ideal.Quotient.mk_surjective) (I := maximalIdeal R)
        (y := Ideal.Quotient.mk I (((x i.succ : maximalIdeal R) : R)))).2 ?_
      exact ⟨((x i.succ : maximalIdeal R) : R), (x i.succ).2, rfl⟩
    simpa [hmaxmap] using hmem
  let xbar : Fin d → maximalIdeal S := fun i ↦
    ⟨Ideal.Quotient.mk I (((x i.succ : maximalIdeal R) : R)), hxbar_mem i⟩
  have hmap_parameter :
      Ideal.map (Ideal.Quotient.mk I) (parameterIdeal x) = parameterIdeal xbar := by
    -- Modding out by the head parameter kills exactly the head generator and keeps the tail.
    suffices
        hspan :
          Ideal.map (Ideal.Quotient.mk I)
              (Ideal.span (Set.range fun i ↦ ((x i : maximalIdeal R) : R))) =
            Ideal.span (Set.range fun i ↦ ((xbar i : maximalIdeal S) : S)) by
      simpa [parameterIdeal_eq_span, xbar] using hspan
    rw [Ideal.map_span]
    apply le_antisymm
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨y, ⟨i, rfl⟩, rfl⟩
      refine Fin.cases ?_ ?_ i
      · have hx0 :
          Ideal.Quotient.mk I (((x 0 : maximalIdeal R) : R)) = 0 := by
          rw [Ideal.Quotient.eq_zero_iff_mem]
          dsimp [I, a]
          exact Ideal.subset_span (by simp)
        simpa [hx0]
      · intro j
        exact Ideal.subset_span ⟨j, rfl⟩
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      simpa [xbar] using
        (Ideal.subset_span
          ⟨((x i.succ : maximalIdeal R) : R), ⟨i.succ, rfl⟩, rfl⟩ :
            Ideal.Quotient.mk I (((x i.succ : maximalIdeal R) : R)) ∈
              Ideal.span ((Ideal.Quotient.mk I) ''
                Set.range fun j ↦ ((x j : maximalIdeal R) : R)))
  have hxbar_parameter : parameterIdeal xbar = maximalIdeal S := by
    calc
      parameterIdeal xbar = Ideal.map (Ideal.Quotient.mk I) (parameterIdeal x) := by
        rw [hmap_parameter]
      _ = Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) := by rw [hx.2]
      _ = maximalIdeal S := hmaxmap
  have hrange_ncard :
      (Set.range fun i : Fin d ↦ ((xbar i : maximalIdeal S) : S)).ncard ≤ d := by
    -- The tail parameter family still has at most `d` distinct generators.
    rw [← Nat.card_coe_set_eq]
    simpa using
      (Finite.card_range_le (fun i : Fin d ↦ ((xbar i : maximalIdeal S) : S)))
  have hspanS : (maximalIdeal S).spanFinrank ≤ d := by
    -- The quotient maximal ideal is generated by the `d` tail parameters.
    have hspan_eq :
        maximalIdeal S =
          Ideal.span (Set.range fun i : Fin d ↦ ((xbar i : maximalIdeal S) : S)) := by
      simpa [parameterIdeal_eq_span] using hxbar_parameter.symm
    calc
      (maximalIdeal S).spanFinrank =
          (Ideal.span (Set.range fun i : Fin d ↦ ((xbar i : maximalIdeal S) : S))).spanFinrank :=
            congrArg Submodule.spanFinrank hspan_eq
      _ ≤ (Set.range fun i : Fin d ↦ ((xbar i : maximalIdeal S) : S)).ncard := by
            exact Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)
      _ ≤ d := hrange_ncard
  have hupper : ringKrullDim S ≤ d := by
    -- Krull dimension is always bounded by the span finrank of the maximal ideal.
    calc
      ringKrullDim S ≤ (maximalIdeal S).spanFinrank :=
        ringKrullDim_le_spanFinrank_maximalIdeal (R := S)
      _ ≤ d := by exact_mod_cast hspanS
  have hlower : (d + 1 : WithBot ℕ∞) ≤ ringKrullDim S + 1 := by
    -- Lemma 10.60.13 gives the opposite inequality for the head parameter quotient.
    simpa [a, I, S, hx.1.1] using
      (ringKrullDim_le_ringKrullDim_quotient_span_singleton_add_one
        (R := R) a (x 0).2)
  have hdim : ringKrullDim S = d := by
    have hsucc : ringKrullDim S + 1 = d + 1 := by
      apply le_antisymm
      · simpa [add_comm] using add_le_add_left hupper 1
      · exact hlower
    simpa using
      withBotENat_eq_nat_pred_of_add_one_eq_nat
        (x := ringKrullDim S) (d := d + 1) hsucc
  have hregular : IsRegularLocalRing S := by
    -- A `d`-generated maximal ideal at dimension `d` gives a regular local ring.
    refine
      (isRegularLocalRing_iff_exists_regularSystemOfParameters (R := S) (d := d) hdim).2 ?_
    refine ⟨xbar, ?_⟩
    exact (isRegularSystemOfParameters_iff_of_ringKrullDim_eq (R := S) hdim xbar).2
      hxbar_parameter
  exact ⟨hregular, hdim⟩

/-- Helper for Lemma 10.106.6: over the head-parameter quotient ring, the quotient module has
the expected support dimension `d`. -/
lemma supportDim_over_head_parameter_quotient_eq
    {d : ℕ} (hdim : ringKrullDim R = d + 1)
    {x : Fin (d + 1) → maximalIdeal R}
    (hx : IsLocalRing.IsRegularSystemOfParameters x)
    (hMCM : Module.MaximalCohenMacaulay R M) :
    let a : R := (x 0 : R)
    let S := R ⧸ Ideal.span ({a} : Set R)
    Module.supportDim S (QuotSMulTop a M) = d := by
  let a : R := (x 0 : R)
  let I : Ideal R := Ideal.span ({a} : Set R)
  let S := R ⧸ I
  let Q := QuotSMulTop a M
  let hTors : Module.IsTorsionBySet R Q I :=
    quotSMulTop_torsionBySet_head_parameter (R := R) (M := M) a
  letI : Module S Q := hTors.module
  letI : IsScalarTower R S Q := Module.IsTorsionBySet.isScalarTower hTors
  letI : Module.Finite S Q := Module.Finite.of_restrictScalars_finite R S Q
  have hS :
      IsRegularLocalRing S ∧ ringKrullDim S = d := by
    -- Route correction: first identify the quotient ring as regular local of dimension `d`.
    simpa [a, S, I] using
      head_parameter_quotient_regular_local_and_dim (R := R) (x := x) hx
  letI : IsRegularLocalRing S := hS.1
  have hupperS : Module.supportDim S Q ≤ d := by
    -- The quotient ring is regular local, so support dimension is bounded by its Krull
    -- dimension.
    calc
      Module.supportDim S Q ≤ ringKrullDim S :=
        Module.supportDim_le_ringKrullDim (R := S) (M := Q)
      _ = d := hS.2
  have hsurj : Function.Surjective (algebraMap R S) := by
    simpa [S, I] using (Ideal.Quotient.mk_surjective (I := I))
  have htransport :
      Module.supportDim R Q = Module.supportDim S Q :=
    supportDim_eq_of_surjective_algebraMap (A := R) (B := S) (N := Q) hsurj
  have hupperR : Module.supportDim R Q ≤ d := by
    -- Transport the quotient-side upper bound back to `R`.
    calc
      Module.supportDim R Q = Module.supportDim S Q := htransport
      _ ≤ d := hupperS
  have ha_mem : a ∈ maximalIdeal R := (x 0).2
  have hMdim : Module.supportDim R M = d + 1 := by
    -- Maximal Cohen-Macaulay identifies `dim Supp(M)` with `dim R`.
    calc
      Module.supportDim R M = ringKrullDim R := hMCM.supportDim_eq_ringKrullDim
      _ = d + 1 := hdim
  have hlowerR : d + 1 ≤ Module.supportDim R Q + 1 := by
    -- The standard one-step quotient bound gives the opposite inequality over `R`.
    calc
      (d + 1 : WithBot ℕ∞) = Module.supportDim R M := hMdim.symm
      _ ≤ Module.supportDim R Q + 1 :=
        (Module.supportDim_quotSMulTop_bounds_of_mem_maximalIdeal
          (R := R) (M := M) a ha_mem).2
  have hsuccR : Module.supportDim R Q + 1 = d + 1 := by
    -- The upper and lower bounds force the expected one-step drop.
    apply le_antisymm
    · simpa [add_comm] using add_le_add_left hupperR 1
    · exact hlowerR
  have hdimQ_R : Module.supportDim R Q = d := by
    -- Cancel the common `+ 1` against the finite target `d + 1`.
    simpa using
      withBotENat_eq_nat_pred_of_add_one_eq_nat
        (x := Module.supportDim R Q) (d := d + 1) hsuccR
  -- Transport the resulting equality back to the quotient-ring view used by the induction step.
  calc
    Module.supportDim S Q = Module.supportDim R Q := htransport.symm
    _ = d := hdimQ_R

/-- Helper for Lemma 10.106.6: quotienting a maximal Cohen-Macaulay module by the head parameter
of a regular system of parameters lowers the support dimension by one. -/
lemma supportDim_quotSMulTop_eq_of_head_parameter
    {d : ℕ} (hdim : ringKrullDim R = d + 1)
    {x : Fin (d + 1) → maximalIdeal R}
    (hx : IsLocalRing.IsRegularSystemOfParameters x)
    (hMCM : Module.MaximalCohenMacaulay R M) :
    let a : R := (x 0 : R)
    Module.supportDim R (QuotSMulTop a M) = d := by
  let a : R := (x 0 : R)
  let I : Ideal R := Ideal.span ({a} : Set R)
  let S := R ⧸ I
  let hTors : Module.IsTorsionBySet R (QuotSMulTop a M) I :=
    quotSMulTop_torsionBySet_head_parameter (R := R) (M := M) a
  letI : Module S (QuotSMulTop a M) := hTors.module
  letI : IsScalarTower R S (QuotSMulTop a M) := Module.IsTorsionBySet.isScalarTower hTors
  letI : Module.Finite S (QuotSMulTop a M) := Module.Finite.of_restrictScalars_finite R S
    (QuotSMulTop a M)
  have hS :
      IsRegularLocalRing S ∧ ringKrullDim S = d := by
    simpa [a, S, I] using
      head_parameter_quotient_regular_local_and_dim (R := R) (x := x) hx
  letI : IsRegularLocalRing S := hS.1
  have hsurj : Function.Surjective (algebraMap R S) := by
    simpa [S, I] using (Ideal.Quotient.mk_surjective (I := I))
  have hsupportS : Module.supportDim S (QuotSMulTop a M) = d := by
    -- Route correction: first prove the quotient-side equality over `S`, then transport it back.
    simpa [a, S, I] using
      supportDim_over_head_parameter_quotient_eq
        (R := R) (M := M) hdim (x := x) hx hMCM
  -- The surjective quotient map identifies the ambient and quotient-ring support dimensions.
  calc
    Module.supportDim R (QuotSMulTop a M) = Module.supportDim S (QuotSMulTop a M) :=
      supportDim_eq_of_surjective_algebraMap
        (A := R) (B := S) (N := QuotSMulTop a M) hsurj
    _ = d := hsupportS

/-- Helper for Lemma 10.106.6: the head parameter acts regularly on a maximal Cohen-Macaulay
module. -/
lemma isSMulRegular_of_head_parameter_of_maximalCohenMacaulay
    {d : ℕ} (hdim : ringKrullDim R = d + 1)
    {x : Fin (d + 1) → maximalIdeal R}
    (hx : IsLocalRing.IsRegularSystemOfParameters x)
    (hMCM : Module.MaximalCohenMacaulay R M) :
    let a : R := (x 0 : R)
    IsSMulRegular M a := by
  let a : R := (x 0 : R)
  let _ : Module.CohenMacaulay R M := hMCM.toCohenMacaulay
  have hquot_dim : Module.supportDim R (QuotSMulTop a M) = d := by
    -- First identify the quotient support dimension with the predecessor value `d`.
    simpa [a] using
      supportDim_quotSMulTop_eq_of_head_parameter
        (R := R) (M := M) hdim (x := x) hx hMCM
  have hdrop :
      Module.supportDim R (QuotSMulTop a M) + 1 = Module.supportDim R M := by
    -- Reassemble the one-step drop against `dim Supp(M) = dim R = d + 1`.
    calc
      Module.supportDim R (QuotSMulTop a M) + 1 = d + 1 := by rw [hquot_dim]
      _ = ringKrullDim R := hdim.symm
      _ = Module.supportDim R M := hMCM.supportDim_eq_ringKrullDim.symm
  -- The existing singleton criterion turns the one-step support-dimension drop into regularity.
  exact
    isSMulRegular_of_supportDim_quotSMulTop_add_one_eq_of_cohenMacaulay
      (R := R) (M := M) (g := a) hdrop

/-- Helper for Lemma 10.106.6: after quotienting by the head parameter, the quotient module is
maximal Cohen-Macaulay over the quotient regular local ring. -/
lemma maximalCohenMacaulay_quotSMulTop_over_head_parameter_quotient
    {d : ℕ} (hdim : ringKrullDim R = d + 1)
    {x : Fin (d + 1) → maximalIdeal R}
    (hx : IsLocalRing.IsRegularSystemOfParameters x)
    (hMCM : Module.MaximalCohenMacaulay R M)
    [IsRegularLocalRing (R ⧸ Ideal.span ({((x 0 : maximalIdeal R) : R)} : Set R))] :
    Module.MaximalCohenMacaulay
      (R ⧸ Ideal.span ({((x 0 : maximalIdeal R) : R)} : Set R))
      (QuotSMulTop ((x 0 : R)) M) := by
  let a : R := (x 0 : R)
  let I : Ideal R := Ideal.span ({a} : Set R)
  let S := R ⧸ I
  let Q := QuotSMulTop a M
  let hTors : Module.IsTorsionBySet R Q I :=
    quotSMulTop_torsionBySet_head_parameter (R := R) (M := M) a
  letI : Module S Q := hTors.module
  letI : IsScalarTower R S Q := Module.IsTorsionBySet.isScalarTower hTors
  letI : Module.Finite S Q := Module.Finite.of_restrictScalars_finite R S Q
  letI : IsRegularLocalRing S := by infer_instance
  have hSdim : ringKrullDim S = d := by
    simpa [a, S, I] using
      (head_parameter_quotient_regular_local_and_dim (R := R) (x := x) hx).2
  have hsurj : Function.Surjective (algebraMap R S) := by
    simpa [S, I] using (Ideal.Quotient.mk_surjective (I := I))
  have ha_mem : a ∈ maximalIdeal R := (x 0).2
  let _ : Module.CohenMacaulay R M := hMCM.toCohenMacaulay
  have hreg : IsSMulRegular M a := by
    -- The quotient support-dimension calculation provides the needed nonzerodivisor.
    simpa [a] using
      isSMulRegular_of_head_parameter_of_maximalCohenMacaulay
        (R := R) (M := M) hdim (x := x) hx hMCM
  have hCM_R : Module.CohenMacaulay R Q := by
    -- Quotienting by a regular maximal-ideal element preserves Cohen-Macaulayness over `R`.
    exact
      (Module.cohenMacaulay_iff_quotSMulTop_of_mem_maximalIdeal
        (R := R) (M := M) (x := a) ha_mem hreg).1 inferInstance
  have hCM_S : Module.CohenMacaulay S Q := by
    -- Then transport the Cohen-Macaulay condition across the surjective quotient map.
    exact
      (Module.cohenMacaulay_iff_restrictScalars_of_surjective
        (R := R) (S := S) (N := Q) hsurj).2 hCM_R
  have hsupportS : Module.supportDim S Q = d := by
    -- The quotient-side support-dimension equality matches the quotient-ring dimension `d`.
    simpa [a, S, I, Q] using
      supportDim_over_head_parameter_quotient_eq
        (R := R) (M := M) hdim (x := x) hx hMCM
  refine
    { toFinite := Module.Finite.of_restrictScalars_finite R S Q
      depth_eq_ringKrullDim := ?_ }
  -- Combine the Cohen-Macaulay equality over `S` with the quotient-ring dimension drop.
  calc
    (((moduleDepth S Q : ℕ∞) : WithBot ℕ∞)) = Module.supportDim S Q := by
      simpa using hCM_S.supportDim_eq_moduleDepth.symm
    _ = d := hsupportS
    _ = ringKrullDim S := hSdim.symm

/-- Helper for Lemma 10.106.6: freeness follows by induction on the Krull dimension. -/
lemma free_of_maximalCohenMacaulay_of_ringKrullDim_eq
    {d : ℕ} (hdim : ringKrullDim R = d) (hMCM : Module.MaximalCohenMacaulay R M) :
    Module.Free R M := by
  letI : Module.Finite R M := hMCM.toFinite
  induction d generalizing R M with
  | zero =>
      -- The base case uses that a zero-dimensional regular local ring is a field.
      exact free_of_maximalCohenMacaulay_of_ringKrullDim_eq_zero
        (R := R) (M := M) hdim hMCM
  | succ d ih =>
      let d' := d + 1
      have hd' : ringKrullDim R = d' := hdim
      obtain ⟨x, hx⟩ :=
        (isRegularLocalRing_iff_exists_regularSystemOfParameters
          (R := R) (d := d') hd').1 inferInstance
      let a : R := (x 0 : R)
      let I : Ideal R := Ideal.span ({a} : Set R)
      let S := R ⧸ I
      let Q := QuotSMulTop a M
      let hTors : Module.IsTorsionBySet R Q I :=
        quotSMulTop_torsionBySet_head_parameter (R := R) (M := M) a
      letI : Module S Q := hTors.module
      letI : IsScalarTower R S Q := Module.IsTorsionBySet.isScalarTower hTors
      letI : Module.Finite S Q := Module.Finite.of_restrictScalars_finite R S Q
      have hS :
          IsRegularLocalRing S ∧ ringKrullDim S = d := by
        -- The source proof first passes to the quotient by the head parameter.
        simpa [d', a, S, I] using
          head_parameter_quotient_regular_local_and_dim (R := R) (x := x) hx
      letI : IsRegularLocalRing S := hS.1
      have hQ_mcm : Module.MaximalCohenMacaulay S Q := by
        -- The quotient module is maximal Cohen-Macaulay over the quotient regular local ring.
        letI : IsRegularLocalRing S := hS.1
        simpa [d', a, S, I, Q] using
          maximalCohenMacaulay_quotSMulTop_over_head_parameter_quotient
            (R := R) (M := M) hd' (x := x) hx hMCM
      have hQ_free : Module.Free S Q := by
        -- Apply the induction hypothesis over the quotient regular local ring `S`.
        exact ih (R := S) (M := Q) hS.2 hQ_mcm
      have ha_mem : a ∈ maximalIdeal R := (x 0).2
      have hreg : IsSMulRegular M a := by
        -- The head parameter is a nonzerodivisor on a maximal Cohen-Macaulay module.
        simpa [d', a] using
          isSMulRegular_of_head_parameter_of_maximalCohenMacaulay
            (R := R) (M := M) hd' (x := x) hx hMCM
      have hQ_free' : Module.Free (R ⧸ Ideal.span ({a} : Set R)) (QuotSMulTop a M) := by
        simpa [a, S, I, Q] using hQ_free
      letI : Module.Free (R ⧸ Ideal.span ({a} : Set R)) (QuotSMulTop a M) := hQ_free'
      -- Lemma 10.106.5 lifts freeness of `M / aM` across the regular element `a`.
      have hfree : Module.Free R M := by
        exact @free_of_isSMulRegular_of_free_quotSMulTop
          R _ _ _ M _ _ _ a ha_mem hreg hQ_free'
      simpa [a, S, I, Q] using hfree

/-- Helper for Lemma 10.106.6: the regular-local dimension formula supplies the induction index. -/
lemma free_of_maximalCohenMacaulay_of_spanFinrank_maximalIdeal
    (hMCM : Module.MaximalCohenMacaulay R M) :
    Module.Free R M := by
  have hdim :
      ringKrullDim R = (maximalIdeal R).spanFinrank :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  -- The ring dimension written as `spanFinrank` is the induction parameter used in the source
  -- proof.
  exact free_of_maximalCohenMacaulay_of_ringKrullDim_eq
    (R := R) (M := M) hdim hMCM

/-- Lemma 10.106.6: over a regular local ring `R`, every maximal Cohen-Macaulay `R`-module,
is free. -/
@[stacks 00NT]
theorem free_of_maximalCohenMacaulay_of_isRegularLocalRing
    (hMCM : Module.MaximalCohenMacaulay R M) :
    Module.Free R M := by
  -- Reduce to the induction helper indexed by the regular-local dimension formula.
  exact free_of_maximalCohenMacaulay_of_spanFinrank_maximalIdeal
    (R := R) (M := M) hMCM

end
