import StacksProject_2024.Chap10.Definition_10_67_1
import StacksProject_2024.Chap10.Definition_10_157_1
import StacksProject_2024.Chap10.Lemma_10_40_6
import StacksProject_2024.Chap10.Lemma_10_63_15
import StacksProject_2024.Chap10.Lemma_10_63_18
import StacksProject_2024.Chap10.Lemma_10_72_9
import StacksProject_2024.Chap10.Proposition_10_63_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing
open scoped ENat TensorProduct

namespace Module

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Helper for Lemma 10.157.2: support of the localization `M_𝔭` is detected by contracting prime
ideals along `Spec(R_𝔭) → Spec(R)`. -/
lemma mem_support_localizationAtPrime_iff (p : PrimeSpectrum R)
    (q : PrimeSpectrum (Localization.AtPrime p.asIdeal)) :
    q ∈ Module.support (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) ↔
      PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q ∈
        Module.support R M := by
  -- Rewrite the localized module as the standard tensor-product base change, so support follows
  -- from the chapter's base-change support theorem.
  let e := LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M
  have hsupp :
      Module.support (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) =
        Module.support (Localization.AtPrime p.asIdeal)
          ((Localization.AtPrime p.asIdeal) ⊗[R] M) := by
    simpa using (LinearEquiv.support_eq (R := Localization.AtPrime p.asIdeal) e)
  rw [hsupp, Module.Lemma_10_40_6 (R := R) (R' := Localization.AtPrime p.asIdeal) (M := M)]
  rfl

/-- Helper for Lemma 10.157.2: if `q ∈ Supp(M)` lies below `p`, then it lifts to a support point
of the localization `M_𝔭`. -/
lemma exists_mem_support_localizationAtPrime_of_mem_support_of_le
    (p q : PrimeSpectrum R) (hq : q ∈ Module.support R M) (hqp : q ≤ p) :
    ∃ q' : PrimeSpectrum (Localization.AtPrime p.asIdeal),
      PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q' = q ∧
        q' ∈ Module.support (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M) := by
  -- Use the localization order isomorphism to pick the unique prime of `Spec(R_𝔭)` over `q`, then
  -- transport support membership through the previous support-comparison lemma.
  let e := IsLocalization.AtPrime.primeSpectrumOrderIso
    (Localization.AtPrime p.asIdeal) p.asIdeal
  let q' : PrimeSpectrum (Localization.AtPrime p.asIdeal) := e.symm ⟨q, hqp⟩
  have hcomap : PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q' = q := by
    have hq' : e q' = ⟨q, hqp⟩ := by
      simpa [q'] using e.apply_symm_apply ⟨q, hqp⟩
    simpa using congrArg Subtype.val hq'
  refine ⟨q', hcomap, ?_⟩
  exact (mem_support_localizationAtPrime_iff (R := R) (M := M) p q').2 (hcomap ▸ hq)

/-- Helper for Lemma 10.157.2: over a Noetherian local ring, depth zero forces the maximal ideal
to be an associated prime of the module. -/
lemma maximalIdeal_mem_associatedPrimes_of_moduleDepth_eq_zero
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hdepth : moduleDepth A N = 0) :
    maximalIdeal A ∈ associatedPrimes A N := by
  -- Route correction: instead of trying to read depth zero directly from the owner definition, we
  -- rule out regular elements in the maximal ideal and then apply Lemma 10.63.18 contrapositively.
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

/-- Helper for Lemma 10.157.2: if `p` is minimal in the global support of `M`, then the localized
support `Supp(M_𝔭)` is exactly the closed point of `Spec(R_𝔭)`. -/
lemma support_eq_singleton_localizationAtPrime_of_minimal_support
    (p : PrimeSpectrum R) (hp : Minimal (· ∈ Module.support R M) p) :
    Module.support (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) =
      {IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal)} := by
  ext q
  constructor
  · intro hq
    -- Any support point of `M_𝔭` contracts to a support point below `p`, hence to `p` itself by
    -- minimality of `p`.
    have hq_support :
        PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q ∈
          Module.support R M :=
      (mem_support_localizationAtPrime_iff (R := R) (M := M) p q).1 hq
    have hq_le :
        PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q ≤ p := by
      change
        ((IsLocalization.AtPrime.primeSpectrumOrderIso
          (Localization.AtPrime p.asIdeal) p.asIdeal q).1 ≤ p)
      exact
        (IsLocalization.AtPrime.primeSpectrumOrderIso
          (Localization.AtPrime p.asIdeal) p.asIdeal q).2
    have hq_comap_eq :
        PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q = p := by
      exact le_antisymm hq_le (hp.2 hq_support hq_le)
    have hq_asIdeal :
        q.asIdeal = maximalIdeal (Localization.AtPrime p.asIdeal) := by
      have hq_comap_eq_asIdeal :
          Ideal.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q.asIdeal = p.asIdeal := by
        simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hq_comap_eq
      exact Localization.AtPrime.eq_maximalIdeal_iff_comap_eq.mp hq_comap_eq_asIdeal
    have hq_eq :
        q = IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal) := by
      exact PrimeSpectrum.ext_iff.mpr hq_asIdeal
    simpa [hq_eq]
  · intro hq
    -- The closed point belongs to the localized support because `p ∈ Supp(M)` means `M_𝔭 ≠ 0`.
    rcases Set.mem_singleton_iff.1 hq with rfl
    have hnontrivial : Nontrivial (LocalizedModule.AtPrime p.asIdeal M) := by
      simpa using (Module.mem_support_iff.mp hp.1)
    letI := hnontrivial
    simpa using
      (IsLocalRing.closedPoint_mem_support
        (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M))

/-- Helper for Lemma 10.157.2: minimality of `p` in the global support forces the localization
`M_𝔭` to have support dimension zero. -/
lemma supportDim_localizationAtPrime_eq_zero_of_minimal_support
    (p : PrimeSpectrum R) (hp : Minimal (· ∈ Module.support R M) p) :
    Module.supportDim (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) = 0 := by
  -- Once the localized support is a singleton, its Krull dimension is zero.
  have hsupp :
      Module.support (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) =
        {IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal)} :=
    support_eq_singleton_localizationAtPrime_of_minimal_support (R := R) (M := M) p hp
  have hclosed :
      IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal) ∈
        Module.support (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) := by
    simpa [hsupp]
  classical
  letI : Unique
      (Module.support (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M)) := {
    default := ⟨IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal), hclosed⟩
    uniq := by
      intro q
      apply Subtype.ext
      have hq_eq :
          (q : PrimeSpectrum (Localization.AtPrime p.asIdeal)) =
            IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal) := by
        simpa [hsupp] using q.2
      simpa using hq_eq
  }
  simpa [Module.supportDim] using
    (Order.krullDim_eq_zero_of_unique
      (α := Module.support (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M)))

/- Domain triage:
* source-facing: the equivalence between LinearRepresentations_Serre_1977's condition `(S_1)` and having no embedded
  associated primes;
* core/canonical: `Module.SerreConditionS R M 1` for `(S_1)` and `embeddedAssociatedPrimes R M`
  for the no-embedded-primes condition;
* bridge/view: the theorem below, which keeps the source-facing equivalence as a thin companion of
  those owners.

Primitive data live in the owner abstractions above. The localized regular-element criterion and
the "every associated prime is minimal" wording are derived API and should not remain separate
owners in this file.
-/

-- Proof sketch: if `M` has an embedded associated prime `p`, localizing at `p` gives depth `0`
-- while the support dimension stays at least `1`, so `(S_1)` fails. Conversely, if `(S_1)` fails
-- at some prime `p`, then `depth(M_p) = 0` makes `p` associated after localization and descent,
-- while support dimension at least `1` produces a smaller prime in the support; a minimal such
-- prime is associated, so `p` is embedded.
/-- Lemma 10.157.2: a finite module over a Noetherian ring has no embedded associated primes if
and only if it satisfies LinearRepresentations_Serre_1977's condition `(S_1)`. -/
theorem embeddedAssociatedPrimes_eq_empty_iff_serreConditionS_one :
    embeddedAssociatedPrimes R M = ∅ ↔ Module.SerreConditionS R M 1 := by
  constructor
  · intro hM
    have hminimal_assoc :
        ∀ p ∈ associatedPrimes R M, Minimal (· ∈ associatedPrimes R M) p :=
      (embeddedAssociatedPrimes_eq_empty_iff R M).1 hM
    refine
      { toFinite := inferInstance
        moduleDepth_localizationAtPrime_ge_min_supportDim := ?_ }
    intro p
    by_cases hdepth :
        moduleDepth (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) = 0
    · -- Depth zero at `p` makes `p` associated; the no-embedded-primes hypothesis then forces
      -- `p` to be minimal in the support, so the localized support is zero-dimensional.
      have hmax_assoc :
          maximalIdeal (Localization.AtPrime p.asIdeal) ∈ associatedPrimes
            (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) :=
        maximalIdeal_mem_associatedPrimes_of_moduleDepth_eq_zero hdepth
      have hmax_assoc_text :
          maximalIdeal (Localization.AtPrime p.asIdeal) ∈
            associatedPrimesOfModule (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal M) := by
        simpa [associatedPrimesOfModule_eq_associatedPrimes] using hmax_assoc
      have hp_assoc_text : p.asIdeal ∈ associatedPrimesOfModule R M :=
        mem_associatedPrimesOfModule_of_mem_associatedPrimesOfModule_atPrime_of_fg
          hmax_assoc_text (Ideal.fg_of_isNoetherianRing p.asIdeal)
      have hp_assoc : p.asIdeal ∈ associatedPrimes R M := by
        simpa [associatedPrimesOfModule_eq_associatedPrimes] using hp_assoc_text
      have hp_min_assoc : Minimal (· ∈ associatedPrimes R M) p.asIdeal :=
        hminimal_assoc _ hp_assoc
      have hp_min_support : Minimal (· ∈ Module.support R M) p :=
        (minimal_support_iff_minimal_associatedPrimes (R := R) (M := M) p).2 hp_min_assoc
      have hsupp0 :
          Module.supportDim (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M) = 0 :=
        supportDim_localizationAtPrime_eq_zero_of_minimal_support (R := R) (M := M) p hp_min_support
      simpa [hdepth, hsupp0]
    · -- Outside the depth-zero case, the left-hand side is at least `1`, while the right-hand
      -- side is bounded above by `1`.
      have hdepth_ge_one :
          (1 : WithBot ℕ∞) ≤
            WithBot.some
              (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal M) : ℕ∞) := by
        have hdepth_ge_one' :
            (1 : ℕ∞) ≤ moduleDepth (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal M) :=
          ENat.one_le_iff_ne_zero.2 hdepth
        simpa [WithBot.some_eq_coe] using (WithBot.coe_le_coe.2 hdepth_ge_one')
      simpa using le_trans
        (min_le_left (1 : WithBot ℕ∞)
          (Module.supportDim (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M)))
        hdepth_ge_one
  · intro hS
    refine (embeddedAssociatedPrimes_eq_empty_iff R M).2 ?_
    intro p hp
    letI : p.IsPrime := hp.1
    let p' : PrimeSpectrum R := ⟨p, hp.1⟩
    letI : p'.asIdeal.IsPrime := p'.2
    have hp_text : p ∈ associatedPrimesOfModule R M := by
      simpa [associatedPrimesOfModule_eq_associatedPrimes] using hp
    have hmax_assoc_text :
        maximalIdeal (Localization.AtPrime p'.asIdeal) ∈
          associatedPrimesOfModule (Localization.AtPrime p'.asIdeal)
            (LocalizedModule.AtPrime p'.asIdeal M) :=
      mem_associatedPrimesOfModule_atPrime_of_mem_associatedPrimesOfModule hp_text
    have hmax_assoc :
        maximalIdeal (Localization.AtPrime p'.asIdeal) ∈ associatedPrimes
          (Localization.AtPrime p'.asIdeal) (LocalizedModule.AtPrime p'.asIdeal M) := by
      simpa [associatedPrimesOfModule_eq_associatedPrimes] using hmax_assoc_text
    have hp_support : p' ∈ Module.support R M :=
      Module.associatedPrimes_subset_support (by simpa using hp)
    have hnontrivial : Nontrivial (LocalizedModule.AtPrime p'.asIdeal M) := by
      simpa using (Module.mem_support_iff.mp hp_support)
    have hdepth_le :
        moduleDepth (Localization.AtPrime p'.asIdeal) (LocalizedModule.AtPrime p'.asIdeal M) ≤ 0 := by
      -- The associated closed point in the localization bounds the depth by the dimension of the
      -- residue field, which is zero.
      have hle :
          WithBot.some
              (moduleDepth (Localization.AtPrime p'.asIdeal)
                (LocalizedModule.AtPrime p'.asIdeal M) : ℕ∞) ≤
            ringKrullDim
              ((Localization.AtPrime p'.asIdeal) ⧸
                maximalIdeal (Localization.AtPrime p'.asIdeal)) :=
        moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes
          (R := Localization.AtPrime p'.asIdeal)
          (M := LocalizedModule.AtPrime p'.asIdeal M)
          (maximalIdeal (Localization.AtPrime p'.asIdeal))
          hmax_assoc
      have hdim :
          ringKrullDim
              ((Localization.AtPrime p'.asIdeal) ⧸
                maximalIdeal (Localization.AtPrime p'.asIdeal)) = 0 := by
        letI : Field
            ((Localization.AtPrime p'.asIdeal) ⧸
              maximalIdeal (Localization.AtPrime p'.asIdeal)) :=
          Ideal.Quotient.field (maximalIdeal (Localization.AtPrime p'.asIdeal))
        exact ringKrullDim_eq_zero_of_field
          ((Localization.AtPrime p'.asIdeal) ⧸
            maximalIdeal (Localization.AtPrime p'.asIdeal))
      rw [hdim] at hle
      simpa [WithBot.some_eq_coe] using hle
    have hdepth :
        moduleDepth (Localization.AtPrime p'.asIdeal) (LocalizedModule.AtPrime p'.asIdeal M) = 0 :=
      le_antisymm hdepth_le bot_le
    have hsupport_ne_bot :
        Module.supportDim (Localization.AtPrime p'.asIdeal)
          (LocalizedModule.AtPrime p'.asIdeal M) ≠ ⊥ :=
      Module.supportDim_ne_bot_of_nontrivial
        (R := Localization.AtPrime p'.asIdeal)
        (M := LocalizedModule.AtPrime p'.asIdeal M)
    obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hsupport_ne_bot
    have hmin_le_zero : min (1 : WithBot ℕ∞) (d : WithBot ℕ∞) ≤ 0 := by
      simpa [hd, hdepth] using hS.moduleDepth_localizationAtPrime_ge_min_supportDim p'
    have hd_zero : d = 0 := by
      by_contra hd_nonzero
      have hmin_ge_one : (1 : WithBot ℕ∞) ≤ min (1 : WithBot ℕ∞) (d : WithBot ℕ∞) := by
        refine le_min le_rfl ?_
        have hd_ge_one : (1 : ℕ∞) ≤ d := ENat.one_le_iff_ne_zero.2 hd_nonzero
        simpa using (WithBot.coe_le_coe.2 hd_ge_one)
      have : (1 : WithBot ℕ∞) ≤ 0 := le_trans hmin_ge_one hmin_le_zero
      exact not_le_of_gt (by simp : (0 : WithBot ℕ∞) < 1) this
    have hsupport0 :
        Module.supportDim (Localization.AtPrime p'.asIdeal) (LocalizedModule.AtPrime p'.asIdeal M) =
          0 := by
      simpa [hd_zero] using hd.symm
    refine ⟨hp, ?_⟩
    intro q hq hqp
    let q' : PrimeSpectrum R := ⟨q, hq.1⟩
    have hq_support : q' ∈ Module.support R M :=
      Module.associatedPrimes_subset_support (by simpa using hq)
    obtain ⟨qₚ, hqₚ_comap, hqₚ_support⟩ :=
      exists_mem_support_localizationAtPrime_of_mem_support_of_le
        (R := R) (M := M) p' q' hq_support hqp
    have hsupport_eq :
        Module.support (Localization.AtPrime p'.asIdeal) (LocalizedModule.AtPrime p'.asIdeal M) =
          PrimeSpectrum.zeroLocus (maximalIdeal (Localization.AtPrime p'.asIdeal)) :=
      support_of_supportDim_eq_zero
        (R := Localization.AtPrime p'.asIdeal)
        (N := LocalizedModule.AtPrime p'.asIdeal M)
        hsupport0
    have hqₚ_closed :
        qₚ = IsLocalRing.closedPoint (Localization.AtPrime p'.asIdeal) := by
      have : qₚ ∈ PrimeSpectrum.zeroLocus (maximalIdeal (Localization.AtPrime p'.asIdeal)) := by
        simpa [hsupport_eq] using hqₚ_support
      simpa [PrimeSpectrum.zeroLocus_eq_singleton] using this
    have hclosed_comap :
        Ideal.comap (algebraMap R (Localization.AtPrime p'.asIdeal))
          (IsLocalRing.closedPoint (Localization.AtPrime p'.asIdeal)).asIdeal = p'.asIdeal := by
      simpa using Localization.AtPrime.comap_maximalIdeal (R := R) (I := p'.asIdeal)
    have hq_eq_p : q = p'.asIdeal := by
      have hqₚ_comap_asIdeal :
          Ideal.comap (algebraMap R (Localization.AtPrime p'.asIdeal)) qₚ.asIdeal = q := by
        simpa [PrimeSpectrum.comap_asIdeal, q'] using congrArg PrimeSpectrum.asIdeal hqₚ_comap
      rw [hqₚ_closed] at hqₚ_comap_asIdeal
      exact (hclosed_comap.symm.trans hqₚ_comap_asIdeal).symm
    exact hq_eq_p.symm.le

end

end Module
