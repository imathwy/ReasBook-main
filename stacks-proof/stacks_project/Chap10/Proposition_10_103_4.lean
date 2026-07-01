import Mathlib
import stacks_project.Chap10.Definition_10_103_1
import stacks_project.Chap10.Lemma_10_63_2
import stacks_project.Chap10.Lemma_10_63_10
import stacks_project.Chap10.Lemma_10_68_10
import stacks_project.Chap10.Lemma_10_72_7
import stacks_project.Chap10.Lemma_10_72_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open RingTheory Sequence IsLocalRing
open scoped ENat Pointwise

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

namespace Module

/- 
Source/core/bridge triage:
* source-facing: Proposition `10.103.4` is the textbook criterion that a sequence in the maximal
  ideal of a Cohen-Macaulay local module is regular, and hence extends to a maximal regular
  sequence, once the quotient has the expected support dimension;
* core/canonical: `CohenMacaulay R M`, `supportDim R M`, and `RingTheory.Sequence.IsRegular M`;
* bridge/view: the quotient module `M ⧸ (Ideal.ofList gs • (⊤ : Submodule R M))`.

Primitive data are only the maximal-ideal membership of `gs`, the ambient support dimension of
`M`, and the owner-level additive equality
`supportDim R (M ⧸ (Ideal.ofList gs • ⊤)) + gs.length = supportDim R M`. The maximal extension is
derived from the existing regular-sequence extension theorem to depth, so this file should not
repackage that owner API through a separate truncated-subtraction condition.
-/

/-- Helper for Proposition 10.103.4: the quotient by a cons list is the quotient by the head
followed by the quotient by the tail on `QuotSMulTop`. -/
private theorem supportDim_quotient_cons_eq_supportDim_tail_on_quotSMulTop
    {N : Type u} [AddCommGroup N] [Module R N] {g : R} {gs : List R} :
    Module.supportDim R (N ⧸ (Ideal.ofList (g :: gs) • (⊤ : Submodule R N))) =
      Module.supportDim R
        ((QuotSMulTop g N) ⧸ (Ideal.ofList gs • (⊤ : Submodule R (QuotSMulTop g N)))) := by
  -- The canonical quotient-by-prefix equivalence realizes the source proof's nested quotient.
  exact Module.supportDim_eq_of_equiv <|
    Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner N g gs

/-- Helper for Proposition 10.103.4: quotienting by a list of maximal-ideal elements lowers the
support dimension by at most the length of the list. -/
private theorem supportDim_le_supportDim_quotient_ofList_add_length_of_mem_maximalIdeal
    {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N]
    {rs : List R} (hrs : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    Module.supportDim R N ≤
      Module.supportDim R (N ⧸ (Ideal.ofList rs • (⊤ : Submodule R N))) + rs.length := by
  induction rs generalizing N with
  | nil =>
      -- The empty list leaves the module unchanged.
      have hquot :
          Module.supportDim R (N ⧸ (Ideal.ofList ([] : List R) • (⊤ : Submodule R N))) =
            Module.supportDim R N := by
        calc
          Module.supportDim R (N ⧸ (Ideal.ofList ([] : List R) • (⊤ : Submodule R N))) =
              Module.supportDim R (N ⧸ (⊥ : Submodule R N)) := by
                rw [Ideal.ofList_nil, Submodule.bot_smul]
          _ = Module.supportDim R N := by
                simpa using
                  (Module.supportDim_eq_of_equiv
                    (Submodule.quotEquivOfEqBot (⊥ : Submodule R N) rfl))
      simpa [hquot] using (le_rfl : Module.supportDim R N ≤ Module.supportDim R N)
  | cons r rs ih =>
      have hr_mem : r ∈ maximalIdeal R := hrs r (by simp)
      have hrs_mem : ∀ s ∈ rs, s ∈ maximalIdeal R := fun s hs ↦ hrs s (by simp [hs])
      have hhead :
          Module.supportDim R N ≤ Module.supportDim R (QuotSMulTop r N) + 1 :=
        (Module.supportDim_quotSMulTop_bounds_of_mem_maximalIdeal (R := R) (M := N) r hr_mem).2
      have htail :
          Module.supportDim R (QuotSMulTop r N) ≤
            Module.supportDim R
                ((QuotSMulTop r N) ⧸
                  (Ideal.ofList rs • (⊤ : Submodule R (QuotSMulTop r N)))) +
              rs.length :=
        ih (N := QuotSMulTop r N) hrs_mem
      -- Compare the one-step quotient bound with the inductive tail bound.
      calc
        Module.supportDim R N ≤ Module.supportDim R (QuotSMulTop r N) + 1 := hhead
        _ ≤
            (Module.supportDim R
                ((QuotSMulTop r N) ⧸
                  (Ideal.ofList rs • (⊤ : Submodule R (QuotSMulTop r N)))) +
              rs.length) +
              1 := by
                simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right htail 1
        _ =
            Module.supportDim R (N ⧸ (Ideal.ofList (r :: rs) • (⊤ : Submodule R N))) +
              (r :: rs).length := by
              rw [supportDim_quotient_cons_eq_supportDim_tail_on_quotSMulTop (R := R) (N := N)
                (g := r) (gs := rs)]
              simp [add_assoc]

/-- Helper for Proposition 10.103.4: an equality `x + 1 = d` with `d : ℕ` forces
`x = d - 1` in `WithBot ℕ∞`. -/
private theorem withBotENat_eq_nat_pred_of_add_one_eq_nat {x : WithBot ℕ∞} {d : ℕ}
    (h : x + 1 = d) :
    x = (d - 1 : ℕ) := by
  cases hx : x with
  | bot =>
      simp [hx] at h
  | coe n =>
      apply WithBot.coe_injective
      have hn_cast :
          ((((n : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) = ((d : ℕ∞) : WithBot ℕ∞)) := by
        simpa [hx] using h
      have hn : (n : ℕ∞) + 1 = d :=
        WithBot.coe_inj.mp hn_cast
      have hn_ne_top : (n : ℕ∞) ≠ ⊤ := by
        intro hn_top
        have : (⊤ : ℕ∞) = d := by
          simpa [hn_top] using hn
        simpa using this
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

/-- Helper for Proposition 10.103.4: a one-step support-dimension drop forces the element into
the maximal ideal. -/
private theorem mem_maximalIdeal_of_supportDim_quotSMulTop_add_one_eq
    {N : Type u} [AddCommGroup N] [Module R N] [CohenMacaulay R N] {g : R}
    (hdim : Module.supportDim R (QuotSMulTop g N) + 1 = Module.supportDim R N) :
    g ∈ maximalIdeal R := by
  -- A unit would make the quotient zero, contradicting the Cohen-Macaulay support-depth identity.
  by_contra hg
  have hg_unit : IsUnit g := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hg
    exact not_not.mp hg
  have hsmul_top : g • (⊤ : Submodule R N) = ⊤ := by
    refine top_unique ?_
    intro n hn
    rcases hg_unit with ⟨u, rfl⟩
    rw [Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨(↑u⁻¹ : R) • n, by simp, ?_⟩
    simp [smul_smul]
  have hquot_subsingleton : Subsingleton (QuotSMulTop g N) := by
    rw [Submodule.Quotient.subsingleton_iff]
    simpa using hsmul_top
  letI : Subsingleton (QuotSMulTop g N) := hquot_subsingleton
  have hquot_bot : Module.supportDim R (QuotSMulTop g N) = ⊥ := by
    simpa using Module.supportDim_eq_bot_of_subsingleton (R := R) (M := QuotSMulTop g N)
  have hN_bot : Module.supportDim R N = ⊥ := by
    simpa [hquot_bot] using hdim.symm
  simpa [hN_bot] using
    (Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := N))

/-- Helper for Proposition 10.103.4: every associated prime of a Cohen-Macaulay module realizes
the full support dimension. -/
private theorem ringKrullDim_quotient_eq_supportDim_of_mem_associatedPrimes_of_cohenMacaulay
    {N : Type u} [AddCommGroup N] [Module R N] [CohenMacaulay R N]
    (p : Ideal R) (hp : p ∈ associatedPrimes R N) :
    ringKrullDim (R ⧸ p) = Module.supportDim R N := by
  -- Compare the associated-prime depth lower bound with the annihilator quotient upper bound.
  have hlower :
      ((moduleDepth R N : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) :=
    moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes (R := R) (M := N) p hp
  have hlower' : Module.supportDim R N ≤ ringKrullDim (R ⧸ p) := by
    simpa [Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := N)] using hlower
  have hp_support :
      (⟨p, (AssociatedPrimes.mem_iff.mp hp).isPrime⟩ : PrimeSpectrum R) ∈ Module.support R N :=
    Module.associatedPrimes_subset_support (R := R) (M := N) (by simpa using hp)
  have hann_le : Module.annihilator R N ≤ p :=
    Module.annihilator_le_of_mem_support hp_support
  have hup : ringKrullDim (R ⧸ p) ≤ Module.supportDim R N := by
    rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator (R := R) (M := N)]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hann_le)
      (Ideal.Quotient.factor_surjective hann_le)
  exact le_antisymm hup hlower'

/-- Helper for Proposition 10.103.4: a one-step support-dimension drop makes the head element a
nonzerodivisor and keeps the quotient Cohen-Macaulay. -/
private theorem regular_and_cohenMacaulay_quotSMulTop_of_supportDim_add_one_eq
    {N : Type u} [AddCommGroup N] [Module R N] [CohenMacaulay R N] {g : R}
    (hdim : Module.supportDim R (QuotSMulTop g N) + 1 = Module.supportDim R N) :
    IsSMulRegular N g ∧ CohenMacaulay R (QuotSMulTop g N) := by
  have hg_mem : g ∈ maximalIdeal R :=
    mem_maximalIdeal_of_supportDim_quotSMulTop_add_one_eq (R := R) (N := N) hdim
  -- Route correction: instead of importing the broken later file, reproduce only the one-step
  -- associated-prime argument needed by the source proof.
  have hg_not_mem_union : g ∉ ⋃ p ∈ associatedPrimes R N, (p : Set R) := by
    intro hg_union
    rcases Set.mem_iUnion.1 hg_union with ⟨p, hp⟩
    rcases Set.mem_iUnion.1 hp with ⟨hp_assoc, hg_mem_p⟩
    let p' : PrimeSpectrum R := ⟨p, (AssociatedPrimes.mem_iff.mp hp_assoc).isPrime⟩
    have hp_supportN : p' ∈ Module.support R N :=
      Module.associatedPrimes_subset_support (R := R) (M := N) (by simpa using hp_assoc)
    have hp_zeroLocus : p' ∈ PrimeSpectrum.zeroLocus ({g} : Set R) := by
      exact (PrimeSpectrum.mem_zeroLocus p' ({g} : Set R)).2
        (Set.singleton_subset_iff.mpr hg_mem_p)
    have hp_supportQuot : p' ∈ Module.support R (QuotSMulTop g N) := by
      simpa [Module.support_quotSMulTop] using And.intro hp_supportN hp_zeroLocus
    have hquot_le : ringKrullDim (R ⧸ p) ≤ Module.supportDim R (QuotSMulTop g N) := by
      have hann_le : Module.annihilator R (QuotSMulTop g N) ≤ p :=
        Module.annihilator_le_of_mem_support hp_supportQuot
      rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator (R := R)
        (M := QuotSMulTop g N)]
      exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hann_le)
        (Ideal.Quotient.factor_surjective hann_le)
    have hp_dim : ringKrullDim (R ⧸ p) = Module.supportDim R N :=
      ringKrullDim_quotient_eq_supportDim_of_mem_associatedPrimes_of_cohenMacaulay
        (R := R) (N := N) p hp_assoc
    have hle : Module.supportDim R N ≤ Module.supportDim R (QuotSMulTop g N) := by
      calc
        Module.supportDim R N = ringKrullDim (R ⧸ p) := hp_dim.symm
        _ ≤ Module.supportDim R (QuotSMulTop g N) := hquot_le
    have hnot :
        ¬ Module.supportDim R N ≤ Module.supportDim R (QuotSMulTop g N) := by
      cases hq : Module.supportDim R (QuotSMulTop g N) with
      | bot =>
          have hN_bot : Module.supportDim R N = ⊥ := by
            simpa [hq] using hdim.symm
          have : False := by
            simpa [hN_bot] using
              (Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := N))
          exact False.elim this
      | coe n =>
          letI : Nontrivial (R ⧸ p) :=
            Ideal.Quotient.nontrivial_iff.mpr (AssociatedPrimes.mem_iff.mp hp_assoc).isPrime.ne_top
          have hN_ne_top : Module.supportDim R N ≠ ⊤ := by
            letI : IsLocalRing (R ⧸ p) :=
              IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
            intro htop
            have : ringKrullDim (R ⧸ p) = ⊤ := by
              simpa [hp_dim] using htop
            exact ringKrullDim_ne_top this
          have hn_ne_top : (n : ℕ∞) ≠ ⊤ := by
            intro hn_top
            have hN_top : Module.supportDim R N = ⊤ := by
              calc
                Module.supportDim R N = Module.supportDim R (QuotSMulTop g N) + 1 := hdim.symm
                _ = (((⊤ : ℕ∞) : WithBot ℕ∞) + 1) := by rw [hq, hn_top]
                _ = ⊤ := by rfl
            exact hN_ne_top hN_top
          exact fun hle' ↦
            (lt_irrefl (n : ℕ∞)) <|
              (ENat.add_one_le_iff hn_ne_top).1 <| by
                have hle'' :
                    (((n : ℕ∞) : WithBot ℕ∞) + 1) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by
                  calc
                    (((n : ℕ∞) : WithBot ℕ∞) + 1) = Module.supportDim R N := by
                      simpa [hq] using hdim
                    _ ≤ ((n : ℕ∞) : WithBot ℕ∞) := by
                      simpa [hq] using hle'
                exact_mod_cast hle''
    exact hnot hle
  have hg_reg : IsSMulRegular N g := by
    simpa [Set.mem_compl_iff, biUnion_associatedPrimes_eq_compl_regular R N] using hg_not_mem_union
  have hdepth :
      moduleDepth R (QuotSMulTop g N) = moduleDepth R N - 1 :=
    IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one hg_reg hg_mem
  refine ⟨hg_reg, ?_⟩
  refine Module.CohenMacaulay.mk ?_
  -- Rewriting the quotient support dimension against the depth drop shows the quotient is still
  -- Cohen-Macaulay.
  cases hq : Module.supportDim R (QuotSMulTop g N) with
  | bot =>
      have hN_bot : Module.supportDim R N = ⊥ := by
        simpa [hq] using hdim.symm
      have : False := by
        simpa [hN_bot] using
          (Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := N))
      exact False.elim this
  | coe n =>
      rw [hdepth]
      have hn_cast :
          (((n : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) = ((moduleDepth R N : ℕ∞) : WithBot ℕ∞) := by
        simpa [hq, Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := N)] using hdim
      have hn : (n : ℕ∞) + 1 = moduleDepth R N :=
        WithBot.coe_inj.mp hn_cast
      have hn_tsub : (n : ℕ∞) = moduleDepth R N - 1 := by
        rw [← hn]
        simpa using
          (tsub_add_cancel_of_le (show (1 : ℕ∞) ≤ (n : ℕ∞) + 1 by simp)).symm
      simpa using congrArg (fun depth : ℕ∞ ↦ (depth : WithBot ℕ∞)) hn_tsub

/-- Helper for Proposition 10.103.4: the expected total support-dimension drop forces the whole
list to be regular by successively applying Lemma `10.103.3` to the head quotient. -/
private theorem regularSequence_of_supportDim_quotient_add_length_eq
    {N : Type u} [AddCommGroup N] [Module R N] [CohenMacaulay R N]
    {gs : List R} {d : ℕ} (hgs : ∀ g ∈ gs, g ∈ maximalIdeal R)
    (hNdim : Module.supportDim R N = d)
    (hquot :
      Module.supportDim R (N ⧸ (Ideal.ofList gs • (⊤ : Submodule R N))) + gs.length =
        Module.supportDim R N) :
    IsRegular N gs := by
  induction gs generalizing N d with
  | nil =>
      have hN_ne_bot : Module.supportDim R N ≠ ⊥ := by
        simpa [hNdim]
      letI : Nontrivial N := (supportDim_ne_bot_iff_nontrivial R N).mp hN_ne_bot
      -- A Cohen-Macaulay module with finite support dimension is nontrivial, so the empty list
      -- is regular.
      simpa using (IsRegular.nil R N)
  | cons g gs ih =>
      have hg_mem : g ∈ maximalIdeal R := hgs g (by simp)
      have htail_mem : ∀ r ∈ gs, r ∈ maximalIdeal R := fun r hr ↦ hgs r (by simp [hr])
      have htail_le :
          Module.supportDim R (QuotSMulTop g N) ≤
            Module.supportDim R
                ((QuotSMulTop g N) ⧸
                  (Ideal.ofList gs • (⊤ : Submodule R (QuotSMulTop g N)))) +
              gs.length :=
        supportDim_le_supportDim_quotient_ofList_add_length_of_mem_maximalIdeal
          (R := R) (N := QuotSMulTop g N) htail_mem
      have hhead_upper :
          Module.supportDim R (QuotSMulTop g N) + 1 ≤ Module.supportDim R N := by
        -- The total equality forces the first step to drop by exactly one.
        calc
          Module.supportDim R (QuotSMulTop g N) + 1 ≤
              (Module.supportDim R
                  ((QuotSMulTop g N) ⧸
                    (Ideal.ofList gs • (⊤ : Submodule R (QuotSMulTop g N)))) +
                gs.length) +
                1 := by
                  simpa [add_comm, add_left_comm, add_assoc] using
                    add_le_add_right htail_le 1
          _ =
              Module.supportDim R (N ⧸ (Ideal.ofList (g :: gs) • (⊤ : Submodule R N))) +
                (g :: gs).length := by
                rw [supportDim_quotient_cons_eq_supportDim_tail_on_quotSMulTop (R := R)
                  (N := N) (g := g) (gs := gs)]
                simp [add_assoc]
          _ = Module.supportDim R N := hquot
      have hhead_lower :
          Module.supportDim R N ≤ Module.supportDim R (QuotSMulTop g N) + 1 :=
        (Module.supportDim_quotSMulTop_bounds_of_mem_maximalIdeal (R := R) (M := N) g hg_mem).2
      have hhead_eq :
          Module.supportDim R (QuotSMulTop g N) + 1 = Module.supportDim R N :=
        le_antisymm hhead_upper hhead_lower
      have hstep :
          IsSMulRegular N g ∧ CohenMacaulay R (QuotSMulTop g N) :=
        regular_and_cohenMacaulay_quotSMulTop_of_supportDim_add_one_eq
          (R := R) (N := N) hhead_eq
      have hg_reg : IsSMulRegular N g := hstep.1
      have hquot_cm :
          CohenMacaulay R (QuotSMulTop g N) :=
        hstep.2
      let _ : CohenMacaulay R (QuotSMulTop g N) := hquot_cm
      have hquot_dim_nat :
          Module.supportDim R (QuotSMulTop g N) = (d - 1 : ℕ) := by
        -- Rewrite the one-step dimension drop against the ambient finite dimension `d`.
        exact withBotENat_eq_nat_pred_of_add_one_eq_nat <| by
          calc
            Module.supportDim R (QuotSMulTop g N) + 1 = Module.supportDim R N := hhead_eq
            _ = d := hNdim
      have htail_quot_nat :
          Module.supportDim R
              ((QuotSMulTop g N) ⧸
                (Ideal.ofList gs • (⊤ : Submodule R (QuotSMulTop g N)))) +
            gs.length =
              (d - 1 : ℕ) := by
        -- The same finite-dimension calculation identifies the quotient seen by the recursive
        -- tail step.
        exact withBotENat_eq_nat_pred_of_add_one_eq_nat <| by
          calc
            (Module.supportDim R
                ((QuotSMulTop g N) ⧸
                  (Ideal.ofList gs • (⊤ : Submodule R (QuotSMulTop g N)))) +
              gs.length) +
                1 =
                Module.supportDim R (N ⧸ (Ideal.ofList (g :: gs) • (⊤ : Submodule R N))) +
                  (g :: gs).length := by
                    rw [supportDim_quotient_cons_eq_supportDim_tail_on_quotSMulTop (R := R)
                      (N := N) (g := g) (gs := gs)]
                    simp [add_assoc]
            _ = Module.supportDim R N := hquot
            _ = d := hNdim
      have htail_quot :
          Module.supportDim R
              ((QuotSMulTop g N) ⧸
                (Ideal.ofList gs • (⊤ : Submodule R (QuotSMulTop g N)))) +
            gs.length =
              Module.supportDim R (QuotSMulTop g N) := by
        rw [hquot_dim_nat]
        exact htail_quot_nat
      have htail_reg :
          IsRegular (QuotSMulTop g N) gs :=
        ih (N := QuotSMulTop g N) (d := d - 1) htail_mem hquot_dim_nat htail_quot
      -- After proving regularity of the head and of the tail on the head quotient, rebuild the
      -- full regular sequence.
      exact IsRegular.cons hg_reg htail_reg

-- Proof sketch: compare the support dimensions of the successive quotients by the prefixes of
-- `gs` using the one-step bound from Lemma `10.60.13`; the hypothesis `hquot` forces each step to
-- drop the support dimension by exactly one. Apply Lemma `10.103.3` inductively to show that each
-- element of `gs` is a nonzerodivisor on the preceding quotient, hence `gs` is `M`-regular.
-- Then use prime avoidance to choose further elements of `maximalIdeal R` that keep lowering the
-- support dimension until the sequence has length `d`, which is maximal because `M` is
-- Cohen-Macaulay and `hMdim` identifies `d` with `dim (Supp M)`.
/-- Proposition 10.103.4: if `M` is a Cohen-Macaulay module over a Noetherian local ring `R`,
`gs` is a list of elements of `maximalIdeal R`, `dim (Supp M) = d`, and the quotient by the
submodule `(g₁, …, g_c)M`, written as `M ⧸ (Ideal.ofList gs • ⊤)`, has support dimension
`dim (Supp M) - c` in the canonical owner form
`supportDim R (M ⧸ (Ideal.ofList gs • ⊤)) + gs.length = supportDim R M`, then `gs` extends to an
`M`-regular sequence of length `d`. In a local ring, containment of the extended sequence in
`maximalIdeal R` is recovered from regularity by the auxiliary companion
`IsRegular.ofList_le_maximalIdeal`. Since `M` is
Cohen-Macaulay, this is a maximal `M`-regular sequence. -/
theorem exists_maximal_regularSequence_extension_of_supportDim_quotient_add_length_eq_of_cohenMacaulay
    [CohenMacaulay R M] {gs : List R} {d : ℕ} (hgs : ∀ g ∈ gs, g ∈ maximalIdeal R)
    (hMdim : Module.supportDim R M = d)
    (hquot :
      Module.supportDim R (M ⧸ (Ideal.ofList gs • (⊤ : Submodule R M))) + gs.length =
        Module.supportDim R M) :
    ∃ gs' : List R,
      IsRegular M (gs ++ gs') ∧ d = (gs ++ gs').length := by
  have hreg : IsRegular M gs :=
    regularSequence_of_supportDim_quotient_add_length_eq
      (R := R) (N := M) hgs hMdim hquot
  -- Extend the verified regular prefix to one of depth length and identify depth with `d`.
  obtain ⟨gs', hreg', hdepth⟩ := IsRegular.exists_append_eq_moduleDepth hreg
  have hdepth_cast :
      ((moduleDepth R M : ℕ∞) : WithBot ℕ∞) = ((d : ℕ∞) : WithBot ℕ∞) := by
    simpa [Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := M)] using hMdim
  have hdepth_nat : moduleDepth R M = d :=
    WithBot.coe_inj.mp hdepth_cast
  have hlen_enat : (d : ℕ∞) = (gs ++ gs').length := by
    calc
      (d : ℕ∞) = moduleDepth R M := by simpa using hdepth_nat.symm
      _ = (gs ++ gs').length := hdepth
  refine ⟨gs', hreg', ?_⟩
  exact_mod_cast hlen_enat

-- Proof sketch: apply
-- `exists_maximal_regularSequence_extension_of_supportDim_quotient_add_length_eq_of_cohenMacaulay`
-- then pass from regularity of the appended sequence to regularity of its initial segment `gs`.
/-- If the quotient by `(g₁, …, g_c)M` has the expected support dimension drop in a
Cohen-Macaulay module, then `gs` itself is an `M`-regular sequence. -/
theorem isRegular_of_supportDim_quotient_add_length_eq_of_cohenMacaulay [CohenMacaulay R M]
    {gs : List R} {d : ℕ} (hgs : ∀ g ∈ gs, g ∈ maximalIdeal R)
    (hMdim : Module.supportDim R M = d)
    (hquot :
      Module.supportDim R (M ⧸ (Ideal.ofList gs • (⊤ : Submodule R M))) + gs.length =
        Module.supportDim R M) :
    IsRegular M gs := by
  obtain ⟨gs', hreg', -⟩ :=
    exists_maximal_regularSequence_extension_of_supportDim_quotient_add_length_eq_of_cohenMacaulay
      (R := R) (M := M) hgs hMdim hquot
  -- Only the prefix corresponding to the original list is needed here.
  exact isRegular_left_of_isRegular_append (M := M) hreg'

end Module

end
