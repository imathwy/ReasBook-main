import Mathlib
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.RegularLocalRing.Defs

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_157_1 (from Chap10) -/
universe u v

open scoped ENat

section

variable {R : Type u} [CommRing R]

private theorem regularSequenceLengths_eq_of_equiv {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] (I : Ideal R) (e : M ≃ₗ[R] N) :
    Ideal.regularSequenceLengths I M = Ideal.regularSequenceLengths I N := by
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).1 hreg, hI, rfl⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).2 hreg, hI, rfl⟩

private theorem idealDepth_eq_of_equiv {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N]
    (I : Ideal R) (e : M ≃ₗ[R] N) :
    Ideal.depth I M = Ideal.depth I N := by
  have htop : I • (⊤ : Submodule R M) = ⊤ ↔ I • (⊤ : Submodule R N) = ⊤ := by
    constructor
    · intro h
      have := congrArg (Submodule.map e.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using this
    · intro h
      have := congrArg (Submodule.map e.symm.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using this
  by_cases hM : I • (⊤ : Submodule R M) = ⊤
  · rw [Ideal.depth_eq_top_of_smul_top I M hM, Ideal.depth_eq_top_of_smul_top I N (htop.mp hM)]
  · rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I M hM,
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N (mt htop.mpr hM),
      regularSequenceLengths_eq_of_equiv I e]

/-- Linear equivalences preserve module depth over a local ring. -/
theorem moduleDepth_eq_of_equiv {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M]
    [Module R M] [IsLocalRing R] {N : Type*} [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] (e : M ≃ₗ[R] N) :
    moduleDepth R M = moduleDepth R N :=
  idealDepth_eq_of_equiv (IsLocalRing.maximalIdeal R) e

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

namespace Module

/-
Source/core/bridge triage:
* source-facing: `Module.SerreConditionS R M k`, the module-theoretic LinearRepresentations_Serre_1977 condition `(S_k)`;
* core/canonical: the localized owner data `moduleDepth` and `Module.supportDim` on
  `LocalizedModule.AtPrime p.asIdeal M`;
* bridge/view: the ring self-module specialization `SerreConditionS R k` below.

Primitive data are exactly the finiteness hypothesis and the primewise depth inequality for the
localized modules. The ring version is derived from this owner by specializing to `M = R`.
-/
/-- Definition 10.157.1 (3): a finite `R`-module satisfies LinearRepresentations_Serre_1977's condition `(S_k)` if, for every
prime ideal `𝔭`, the depth of `M_𝔭` is at least `min(k, dim(Supp(M_𝔭)))`. -/
class SerreConditionS (k : outParam ℕ) : Prop extends Module.Finite R M where
  moduleDepth_localizationAtPrime_ge_min_supportDim :
    ∀ p : PrimeSpectrum R,
      WithBot.some
          (moduleDepth (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) :
            ℕ∞) ≥
        min (k : WithBot ℕ∞)
          (_root_.Module.supportDim (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M))

namespace SerreConditionS

/-- LinearRepresentations_Serre_1977's condition `(S_k)` is invariant under linear equivalence. -/
theorem of_linearEquiv {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] {k : ℕ} (e : M ≃ₗ[R] N)
    [hM : Module.SerreConditionS R M k] : Module.SerreConditionS R N k where
  toFinite := Module.Finite.equiv e
  moduleDepth_localizationAtPrime_ge_min_supportDim := by
    intro p
    let _ : Module.Finite R N := Module.Finite.equiv e
    let ep : LocalizedModule.AtPrime p.asIdeal M ≃ₗ[Localization.AtPrime p.asIdeal]
        LocalizedModule.AtPrime p.asIdeal N :=
      LinearEquiv.ofBijective (LocalizedModule.map p.asIdeal.primeCompl e.toLinearMap)
        ⟨LocalizedModule.map_injective p.asIdeal.primeCompl e.toLinearMap e.injective,
          LocalizedModule.map_surjective p.asIdeal.primeCompl e.toLinearMap e.surjective⟩
    have hsupport :
        Module.supportDim (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) =
          Module.supportDim (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal N) :=
      Module.supportDim_eq_of_equiv ep
    have hdepth :
        moduleDepth (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) =
          moduleDepth (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal N) :=
      moduleDepth_eq_of_equiv ep
    simpa [hdepth, hsupport] using hM.moduleDepth_localizationAtPrime_ge_min_supportDim p

end SerreConditionS

end Module

end

section

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-
Source/core/bridge triage:
* source-facing: `SerreConditionR R k` and `SerreConditionS R k`, the textbook ring conditions;
* core/canonical: `IsRegularLocalRing (Localization.AtPrime p.asIdeal)` for `(R_k)` and the
  module owner `Module.SerreConditionS R R k` for `(S_k)`;
* bridge/view: `SerreConditionS.moduleDepth_localizationAtPrime_ge_min`, recovering the ringwise
  depth bound from the self-module owner.

For `(S_k)`, the old ring-specific primewise depth field was duplicate derived API for the
self-module. The primitive owner data are Noetherianity together with `Module.SerreConditionS R R`.
-/
/-- Definition 10.157.1 (1): a Noetherian ring satisfies LinearRepresentations_Serre_1977's condition `(R_k)` if every
localization at a prime ideal of height at most `k` is a regular local ring; equivalently, `R` is
regular in codimension at most `k`. -/
class SerreConditionR (k : outParam ℕ) : Prop extends IsNoetherianRing R where
  isRegularLocalRing_localizationAtPrime :
    ∀ p : PrimeSpectrum R,
      Ideal.primeHeight p.asIdeal ≤ k →
        IsRegularLocalRing (Localization.AtPrime p.asIdeal)

/-- Definition 10.157.1 (2): a Noetherian ring satisfies LinearRepresentations_Serre_1977's condition `(S_k)` if, for every
prime ideal `𝔭`, the depth of `R_𝔭` is at least `min(k, dim(R_𝔭))`. -/
class SerreConditionS (k : outParam ℕ) : Prop extends IsNoetherianRing R, Module.SerreConditionS R R k

namespace SerreConditionS

/-- The self-module owner `Module.SerreConditionS R R k` recovers the usual ring-theoretic depth
bound in each localization. -/
theorem moduleDepth_localizationAtPrime_ge_min {k : ℕ} (h : SerreConditionS R k)
    (p : PrimeSpectrum R) :
    WithBot.some
        (moduleDepth (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) : ℕ∞) ≥
      min (k : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime p.asIdeal)) := by
  rw [← _root_.Module.supportDim_self_eq_ringKrullDim]
  simpa using h.toSerreConditionS.moduleDepth_localizationAtPrime_ge_min_supportDim p

end SerreConditionS

end

notation:max R:max " ⊧ " "(" "R₁" ")" => SerreConditionR R 1
notation:max R:max " ⊧ " "(" "S₂" ")" => SerreConditionS R 2

/-! ### Lemma_10_157_2 (from Chap10) -/
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

/-! ### Lemma_10_157_3 (from Chap10) -/
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

/-! ### Lemma_10_157_4_Serre_s_criterion_for_normality (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-
Domain-style sampling:
* primary domain: LinearRepresentations_Serre_1977's criterion for normality in Noetherian commutative algebra;
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
* `source-facing`: LinearRepresentations_Serre_1977's criterion identifying normality with `(R_1)` and `(S_2)`;
* `core/canonical`: `IsNormalRing`, `SerreConditionR`, and `SerreConditionS`;
* `bridge/view`: the localized primewise clauses inside those owners.

The previous `List.TFAE` duplicated the owner-level normality and LinearRepresentations_Serre_1977-condition fields by
expanding them back into their local primewise formulations. This file now states the textbook
criterion directly at the owner level.
-/

-- Proof sketch: for `→`, unpack `IsNormalRing R` into normal localizations. Height-`≤ 1`
-- localizations are regular by the one-dimensional normal-local-domain criterion, and the
-- depth bound `S₂` comes from the standard depth estimate for normal local domains. For `←`,
-- use Lemma `10.157.3` to obtain reducedness from `(R₁)` and `(S₂)`, then combine reducedness
-- with `(R₁)` and `(S₂)` to show each localization is an integrally closed domain.
/-- Lemma 10.157.4 (LinearRepresentations_Serre_1977's criterion for normality): for a Noetherian ring `R`, `R` is normal if
and only if it satisfies LinearRepresentations_Serre_1977's conditions `(R_1)` and `(S_2)`. -/
theorem isNormalRing_iff_serreConditionR_one_and_serreConditionS_two :
    IsNormalRing R ↔ R ⊧ (R₁) ∧ R ⊧ (S₂) := by
  sorry

end

/-! ### Lemma_10_157_5 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R]

/-
Domain-style sampling:
* primary domain: regular and normal Noetherian commutative rings;
* sampled owner declarations:
  `IsRegularRing`,
  `IsNormalRing`,
  `IsRegularRing.isRegularLocalRing_atPrime`,
  `IsNormalRing.isNormalLocalizationAtPrime`;
* best owner abstraction: the source-facing hypothesis is the chapter owner `IsRegularRing R`, and
  the conclusion should be the chapter owner `IsNormalRing R`;
* primitive data vs derived API: the primitive public input is only `[IsRegularRing R]`; the old
  primewise pair of `IsDomain` and `IsIntegrallyClosed` instances is derived local API already
  packaged by `IsNormalRing`.

Layering:
* `source-facing`: the textbook statement that a regular ring is normal;
* `core/canonical`: the owner predicates `IsRegularRing R` and `IsNormalRing R`;
* `bridge/view`: the prime-local domain and integrally-closed consequences recovered from
  `IsNormalRing.isNormalLocalizationAtPrime`.
-/

-- Proof sketch: a regular ring satisfies the primewise regular-local hypothesis built into
-- `IsRegularRing`; LinearRepresentations_Serre_1977's criterion from Lemma `10.157.4` then yields that the ring is normal.
/-- Lemma 10.157.5: a regular ring is normal. -/
theorem isNormalRing_of_isRegularRing [IsRegularRing R] : IsNormalRing R := by
  sorry

end

/-! ### Lemma_10_157_6 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

/- Domain-style sampling:
- primary domain: commutative algebra of Noetherian normal domains, with principal quotients,
  embedded associated primes, fraction fields, principal submodules in the fraction field, and
  height-one localizations;
- sampled owner/bridge declarations:
  `embeddedAssociatedPrimes`,
  `embeddedAssociatedPrimes_eq_empty_iff`,
  `Module.embeddedAssociatedPrimes_eq_empty_iff_serreConditionS_one`,
  `Submodule.comap`,
  `Algebra.linearMap`,
  `moduleHeightOneLocalizationIntersection`,
  and `(algebraMap A K).range` as the canonical image owner used in `Lemma_10_50_11`;
- best owner abstractions:
  `embeddedAssociatedPrimes R M` for the no-embedded-primes clause,
  `(algebraMap R K).range` for image-membership in ambient fraction fields/localizations,
  `{ p : PrimeSpectrum R // p.asIdeal.height = 1 }` for the height-one-prime quantification,
  and the contracted principal `R`-submodule
  `((R ∙ x).comap (Algebra.linearMap R (FractionRing R)) : Ideal R)` for `R ∩ xR`;
- primitive data vs. derived API:
  the quotient modules, the principal `R`-submodule `R ∙ x ⊆ FractionRing R`, and the canonical
  algebra-map images are primitive here,
  while the older "every associated prime is minimal" packaging and `Set.range (algebraMap ...)`
  are bridge-level restatements that should not remain the public surface.

Source/core/bridge triage:
- `source-facing`: the three Stacks statements about principal quotients and height-one
  localization tests in a normal domain;
- `core/canonical`: `embeddedAssociatedPrimes`, `associatedPrimes`, `Ideal.comap`,
  `Submodule.comap`, the principal submodule owner `R ∙ x`, and ring-hom ranges;
- `bridge/view`: the height-one-prime subtype used to index those localizations and the
  membership criterion for the fraction field.
-/

/-- Lemma 10.157.6 (1): for a nonzero element `a` of a Noetherian normal domain `R`, the quotient
`R / aR` has no embedded associated primes, and every associated prime of `R / aR` has height
`1`. -/
-- Proof sketch: LinearRepresentations_Serre_1977's criterion gives `(S_2)` for `R`, and Lemma `10.72.6` descends this to
-- `(S_1)` for `R / aR`. Then Lemma `10.157.2` removes embedded primes, while Lemma `10.60.11`
-- shows that minimal primes over `(a)` have height at most `1`; since `a ≠ 0` in a domain, any
-- associated prime of `R / aR` is nonzero and hence has height exactly `1`.
theorem quotient_span_singleton_has_no_embedded_primes_and_associatedPrimes_height_eq_one
    {a : R} (ha : a ≠ 0) :
    embeddedAssociatedPrimes R (R ⧸ Ideal.span ({a} : Set R)) = ∅ ∧
      ∀ p ∈ associatedPrimes R (R ⧸ Ideal.span ({a} : Set R)), p.height = 1 := sorry

/-- Lemma 10.157.6 (2): an element of the fraction field of a Noetherian normal domain belongs to
`R` exactly when it belongs to every localization `R_𝔭` at a height-one prime `𝔭`. -/
-- Proof sketch: write the element as `b / a` with `a ≠ 0`. Apply part (1) to identify the
-- associated primes of `R / aR` with height-one primes and then use Lemma `10.63.19` in the cyclic
-- module `R / aR` to test membership in `aR` after localizing at those primes.
theorem mem_range_algebraMap_iff_mem_range_localizationAtPrime_forall_height_one
    (x : FractionRing R) :
    x ∈ (algebraMap R (FractionRing R)).range ↔
      ∀ p : { p : PrimeSpectrum R // p.asIdeal.height = 1 },
        x ∈ (algebraMap (Localization.AtPrime p.1.asIdeal) (FractionRing R)).range := sorry

/-- Lemma 10.157.6 (3): for a nonzero element `x` of the fraction field of a Noetherian normal
domain `R`, the quotient by the contraction of the principal `R`-submodule `xR ⊆ FractionRing R`,
namely `R / (R ∩ xR)`, has no embedded associated primes, and every associated prime of this
quotient has height `1`. -/
-- Proof sketch: write `x = a / b` and use part (2) to express `R ∩ xR` as an intersection over
-- the height-one primes minimal over `(ab)`. This embeds `R / (R ∩ xR)` into a finite direct sum
-- of quotients by symbolic powers of those primes, whose associated primes are singletons by Lemma
-- `10.64.2`; hence every associated prime is height one and none is embedded.
theorem quotient_fractionRing_principalSubmoduleContraction_has_no_embedded_primes_and_associatedPrimes_height_eq_one
    {x : FractionRing R} (hx : x ≠ 0) :
    embeddedAssociatedPrimes R
        (R ⧸
          ((R ∙ x).comap (Algebra.linearMap R (FractionRing R)) : Ideal R)) = ∅ ∧
      ∀ p ∈ associatedPrimes R
          (R ⧸
            ((R ∙ x).comap (Algebra.linearMap R (FractionRing R)) : Ideal R)),
        p.height = 1 := sorry

end
