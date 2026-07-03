import Mathlib
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Regular.RegularSequence

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_72_1 (from Chap10) -/
universe u v

open RingTheory.Sequence
open scoped ENat

namespace Ideal

variable {R : Type u} [CommRing R]

/-
Source/core/bridge triage:
* source-facing: `Ideal.depth I M`, the Stacks depth of a finite module with respect to an ideal;
* core/canonical: `Sequence.IsRegular M rs`, the owner notion for regular sequences from mathlib;
* bridge/view: `moduleDepth R M`, the local-ring specialization to the maximal ideal.

Primitive data are only the ideal `I`, the module `M`, and the owner predicate `IsRegular M rs`.
The set of admissible lengths and the local specialization are derived from that owner API.
-/
/-- The set of lengths of `M`-regular sequences whose terms all lie in the ideal `I`. -/
def regularSequenceLengths (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    Set ℕ∞ :=
  {d | ∃ rs : List R, IsRegular M rs ∧ Ideal.ofList rs ≤ I ∧ d = rs.length}

/-- Definition 10.72.1: for a finite `R`-module `M`, the `I`-depth of `M` is `∞` when `IM = M`,
and otherwise it is the supremum of the lengths of `M`-regular sequences contained in `I`. -/
noncomputable def depth (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    ℕ∞ :=
  if I • (⊤ : Submodule R M) = ⊤ then
    ⊤
  else
    sSup (regularSequenceLengths I M)

/-- If `IM = M`, then the `I`-depth of `M` is infinite. -/
@[simp] theorem depth_eq_top_of_smul_top (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hIM : I • (⊤ : Submodule R M) = ⊤) :
    depth I M = ⊤ := by
  simp [depth, hIM]

/-- If `IM ≠ M`, then the `I`-depth of `M` is the supremum of the lengths of `M`-regular
sequences contained in `I`. -/
theorem depth_eq_sSup_lengths_of_smul_top_ne_top (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hIM : I • (⊤ : Submodule R M) ≠ ⊤) :
    depth I M = sSup (regularSequenceLengths I M) := by
  simp [depth, hIM]

end Ideal

section

open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Definition 10.72.1 in the local case: in a local ring, the depth of `M` is the depth with
respect to the maximal ideal. This is the high-reuse bridge/view notation for later local
statements, not a second owner definition. -/
noncomputable abbrev moduleDepth (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ℕ∞ :=
  Ideal.depth (maximalIdeal R) M

end

/-! ### Lemma_10_72_2 (from Chap10) -/
universe u v

open RingTheory Sequence
open scoped ENat Pointwise

private lemma isWeaklyRegular_replicate_of_smul_eq_self {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] {f : R} (hf : ∀ m : M, f • m = m) :
    ∀ n : ℕ, IsWeaklyRegular M (List.replicate n f)
  | 0 => IsWeaklyRegular.nil R M
  | n + 1 => by
      refine IsWeaklyRegular.cons ?_ (isWeaklyRegular_replicate_of_smul_eq_self ?_ n)
      · intro x y hxy
        simpa [hf x, hf y] using hxy
      · intro q
        refine Quotient.inductionOn' q ?_
        intro x
        change (f • (Submodule.Quotient.mk x : QuotSMulTop f M)) = Submodule.Quotient.mk x
        rw [← Submodule.Quotient.mk_smul]
        exact congrArg Submodule.Quotient.mk (hf x)

namespace Ideal

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

-- Proof sketch: split according to whether `IM = M`. In the nontrivial case, a weakly regular
-- sequence in `I` is automatically regular because `Ideal.ofList rs • ⊤ = ⊤` would force
-- `I • ⊤ = ⊤`. In the case `IM = M`, Nakayama produces `f ∈ I` acting as the identity on `M`,
-- so `List.replicate n f` is weakly regular for every `n`, forcing the supremum to be `∞`.
/-
Source/core/bridge triage:
* primary domain: commutative algebra, specifically depth and regular sequences;
* sampled owner API: `Ideal.depth`, `Ideal.regularSequenceLengths`,
  `RingTheory.Sequence.IsWeaklyRegular`,
  `Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top`;
* layer: `source-facing`, since the textbook statement reformulates the owner notion `depth` using
  weakly regular sequences rather than introducing new primitive data;
* primitive vs derived split: the primitive data are the ideal `I`, the finite module `M`, and
  the owner predicates `IsRegular` / `IsWeaklyRegular`; the set of admissible lengths is derived
  API, so this proof compares the existing owner-side set `regularSequenceLengths I M` with the
  weakly-regular source-facing set instead of introducing a parallel public wrapper.
-/
/-- Lemma 10.72.2: for a finite `R`-module `M`, the depth of `M` with respect to `I` is the
supremum of the lengths of sequences `f₁, …, fᵣ` in `I` such that each `fᵢ` is a nonzerodivisor on
`M / (f₁, …, fᵢ₋₁)M`. -/
theorem depth_eq_sSup_lengths_of_isWeaklyRegular (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    I.depth M =
      sSup {d : ℕ∞ | ∃ rs : List R, IsWeaklyRegular M rs ∧ ofList rs ≤ I ∧ d = rs.length} := by
  let weaklyRegularSequenceLengths : Set ℕ∞ :=
    {d : ℕ∞ | ∃ rs : List R, IsWeaklyRegular M rs ∧ ofList rs ≤ I ∧ d = rs.length}
  change I.depth M = sSup weaklyRegularSequenceLengths
  by_cases hIM : I • (⊤ : Submodule R M) = ⊤
  · have hrange : Set.range (fun n : ℕ ↦ (n : ℕ∞)) ⊆ weaklyRegularSequenceLengths := by
      intro d hd
      rcases hd with ⟨n, rfl⟩
      obtain ⟨r, hrI, hr0⟩ :=
        exists_sub_one_mem_and_smul_eq_zero_of_ideal_smul_top_eq_top I hIM
      let f : R := 1 - r
      have hfI : f ∈ I := by
        dsimp [f]
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using I.neg_mem hrI
      have hf : ∀ m : M, f • m = m := by
        intro m
        dsimp [f]
        calc
          (1 - r) • m = (1 : R) • m - r • m := sub_smul _ _ _
          _ = m := by simpa using hr0 m
      dsimp [weaklyRegularSequenceLengths]
      refine ⟨List.replicate n f, isWeaklyRegular_replicate_of_smul_eq_self hf n, ?_, by simp⟩
      rw [span_le]
      intro a ha
      have hfa : a = f := (List.mem_replicate.mp ha).2
      simpa [hfa] using hfI
    rw [depth_eq_top_of_smul_top I M hIM]
    simpa [weaklyRegularSequenceLengths] using
      (top_unique <| calc
        (⊤ : ℕ∞) = sSup (Set.range fun n : ℕ ↦ (n : ℕ∞)) := by
          rw [sSup_range, ENat.iSup_natCast]
        _ ≤ sSup weaklyRegularSequenceLengths := by
          exact sSup_le_sSup hrange).symm
  · have hEq : I.regularSequenceLengths M = weaklyRegularSequenceLengths := by
      ext d
      dsimp [Ideal.regularSequenceLengths, weaklyRegularSequenceLengths]
      constructor
      · rintro ⟨rs, hreg, hmem, rfl⟩
        refine ⟨rs, hreg.toIsWeaklyRegular, ?_, rfl⟩
        change span {r | r ∈ rs} ≤ I
        rw [span_le]
        intro r hr
        exact hmem <| Ideal.subset_span hr
      · rintro ⟨rs, hweak, hle, rfl⟩
        refine ⟨rs, ⟨hweak, ?_⟩, hle, rfl⟩
        intro htop
        apply hIM
        exact top_unique <| htop.le.trans <|
          Submodule.smul_mono hle le_rfl
    simpa [weaklyRegularSequenceLengths] using
      (depth_eq_sSup_lengths_of_smul_top_ne_top I M hIM).trans (congrArg sSup hEq)

end Ideal

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

namespace Ideal

/-- In a Noetherian local ring, the source-style condition that `I` is the unit ideal or contains
a regular sequence of length `n` is equivalent to the owner depth inequality `n ≤ I.depth R`. -/
theorem eq_top_or_exists_regularSequence_of_length_iff_le_depth (I : Ideal R) (n : ℕ) :
    (I = ⊤ ∨ ∃ rs : List R, IsRegular R rs ∧ ofList rs ≤ I ∧ rs.length = n) ↔
      (n : WithTop ℕ) ≤ I.depth R := sorry

end Ideal

end

/-! ### Lemma_10_72_3 (from Chap10) -/
universe u v

open RingTheory.Sequence
open IsLocalRing
open Submodule
open scoped ENat

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]

-- Proof sketch: `maximalIdeal R • M ≠ M` by Nakayama, so `Ideal.depth (maximalIdeal R) M` is the
-- supremum of the lengths of regular sequences contained in `maximalIdeal R`. Each such sequence
-- has length at most `Module.supportDim R M` by
-- `Module.supportDim_add_length_eq_supportDim_of_isRegular`, since the quotient by a regular
-- sequence is nontrivial.
/-- Lemma 10.72.3: if `(R, 𝔪)` is a Noetherian local ring and `M` is a nonzero finite
`R`-module, then `depth(M) ≤ dim (Supp(M))`. -/
theorem depth_le_supportDim :
    WithBot.some (moduleDepth R M : ℕ∞) ≤ Module.supportDim R M := by
  change WithBot.some (Ideal.depth (maximalIdeal R) M : ℕ∞) ≤ Module.supportDim R M
  have hsmul :
      maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    by
      simpa [ne_comm] using
        (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
          (maximalIdeal_le_jacobson (Module.annihilator R M)))
  have hdim :
      Module.supportDim R M ≠ ⊥ :=
    Module.supportDim_ne_bot_of_nontrivial R M
  rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) M hsmul]
  refine (WithBot.coe_le_iff).2 ⟨(Module.supportDim R M).unbot hdim, ?_, ?_⟩
  · exact (WithBot.coe_unbot _ _).symm
  · refine sSup_le fun d hd ↦ ?_
    rcases hd with ⟨rs, hreg, -, rfl⟩
    have hquot :
        Module.supportDim R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) ≠ ⊥ :=
      by
        letI : Nontrivial (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) :=
          Quotient.nontrivial_iff.2 <| by
            simpa [ne_comm] using hreg.top_ne_smul
        exact Module.supportDim_ne_bot_of_nontrivial R _
    have hlen : (((rs.length : ℕ∞) : WithBot ℕ∞)) ≤ Module.supportDim R M := by
      rw [← Module.supportDim_add_length_eq_supportDim_of_isRegular rs hreg]
      simpa [add_comm] using WithBot.le_add_self hquot (((rs.length : ℕ∞) : WithBot ℕ∞))
    rw [← WithBot.coe_unbot (Module.supportDim R M) hdim] at hlen
    exact WithBot.coe_le_coe.mp hlen

end

/-! ### Lemma_10_72_4 (from Chap10) -/
universe u v

open RingTheory.Sequence
open IsLocalRing
open scoped ENat

namespace Ideal

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- 
Source/core/bridge triage:
* primary domain: commutative algebra of depth, regular sequences, and localization at primes;
* sampled owner API: `Ideal.depth`, `Ideal.regularSequenceLengths`,
  `Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top` from the local chapter owner file, together
  with mathlib's `Module.supportDim_add_length_eq_supportDim_of_isRegular`;
* layer: `source-facing`, since this item is a finiteness consequence for the existing owner
  object `Ideal.depth`, not a new definition of depth data;
* primitive vs derived split: the primitive data are only the ideal `I`, the finite module `M`,
  and the owner predicate `Sequence.IsRegular M rs`; finiteness is a derived theorem, so this file
  should stay a thin companion to the owner abstraction instead of introducing a parallel wrapper.
-/

-- Proof sketch: `I • ⊤ ≠ ⊤` already forces `M` to be nontrivial; otherwise `⊤ = ⊥`, hence
-- `I • ⊤ = ⊤`. The quotient `M ⧸ I • ⊤` is then nonzero, so choose a prime in its support and
-- localize there. Any `M`-regular sequence in `I` localizes to an `M_𝔭`-regular sequence in
-- `I_𝔭`, so `depth I M` is bounded by the depth of the localized module, which is finite by
-- Lemma 10.72.3.
omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.72.4: a prime in the support of `M / IM` also lies in the support of `M`
and contains `I`. -/
private lemma support_quotient_prime_contains_ideal (I : Ideal R) {p : PrimeSpectrum R}
    (hp : p ∈ Module.support R (M ⧸ I • (⊤ : Submodule R M))) :
    p ∈ Module.support R M ∧ I ≤ p.asIdeal := by
  -- Rewrite `Supp(M / IM)` as `Supp(M) ∩ V(I)` and read off the two pieces of data we need.
  have hp' : p ∈ Module.support R M ∩ PrimeSpectrum.zeroLocus I := by
    simpa [Module.support_quotient] using hp
  refine ⟨hp'.1, ?_⟩
  simpa [PrimeSpectrum.mem_zeroLocus] using hp'.2

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.72.4: every `I`-regular sequence on `M` remains regular after localizing
at a prime in `Supp(M)` that contains `I`, now inside the maximal ideal of the local ring. -/
private lemma regularSequenceLengths_subset_localizationAtPrime (I : Ideal R) (p : PrimeSpectrum R)
    (hpM : p ∈ Module.support R M) (hIp : I ≤ p.asIdeal) :
    Ideal.regularSequenceLengths I M ⊆
      Ideal.regularSequenceLengths (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule.AtPrime p.asIdeal M) := by
  -- Localize a witness sequence and transport both regularity and ideal membership termwise.
  intro d hd
  rcases hd with ⟨rs, hreg, hI, rfl⟩
  let Rp := Localization.AtPrime p.asIdeal
  let Mp := LocalizedModule.AtPrime p.asIdeal M
  letI : Nontrivial Mp := Module.mem_support_iff.mp hpM
  have hmem : ∀ r ∈ rs, r ∈ p.asIdeal := by
    intro r hr
    exact hIp (hI (Ideal.subset_span hr))
  have hreg_loc : IsRegular Mp (rs.map (algebraMap R Rp)) := by
    simpa [Mp, Rp] using
      hreg.1.isRegular_of_isLocalizedModule_of_mem
        (S := Rp) (p := p.asIdeal)
        (N := Mp) (f := LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) hmem
  have hI_loc :
      Ideal.ofList (rs.map (algebraMap R Rp)) ≤ maximalIdeal Rp := by
    -- The localized ideal lands in the unique maximal ideal because all terms lie in `p`.
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)]
    simpa [Rp, Ideal.map_ofList] using
      (Ideal.map_mono (f := algebraMap R (Localization.AtPrime p.asIdeal)) (le_trans hI hIp))
  exact ⟨rs.map (algebraMap R Rp), hreg_loc, hI_loc, by simp⟩

/-- Helper for Lemma 10.72.4: if `p` lies in `Supp(M)`, then the depth of the localized module
`Mₚ` over the local ring `Rₚ` is finite. -/
private lemma moduleDepth_localizationAtPrime_lt_top_of_mem_support (p : PrimeSpectrum R)
    (hpM : p ∈ Module.support R M) :
    moduleDepth (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) < ⊤ := by
  let Rp := Localization.AtPrime p.asIdeal
  let Mp := LocalizedModule.AtPrime p.asIdeal M
  letI : Nontrivial Mp := Module.mem_support_iff.mp hpM
  -- Compare the localized depth to the support dimension and then to the finite span-rank bound.
  have hdepth_le :
      WithBot.some (moduleDepth Rp Mp : ℕ∞) ≤ Module.supportDim Rp Mp :=
    depth_le_supportDim (R := Rp) (M := Mp)
  have hsupport_le : Module.supportDim Rp Mp ≤ ringKrullDim Rp :=
    Module.supportDim_le_ringKrullDim (R := Rp) (M := Mp)
  have hkrull_le : ringKrullDim Rp ≤ (maximalIdeal Rp).spanFinrank := by
    simpa [Rp] using ringKrullDim_le_spanFinrank_maximalIdeal (R := Rp)
  have hle :
      WithBot.some (moduleDepth Rp Mp : ℕ∞) ≤ (maximalIdeal Rp).spanFinrank := by
    exact le_trans hdepth_le (le_trans hsupport_le hkrull_le)
  have hle_nat : moduleDepth Rp Mp ≤ (maximalIdeal Rp).spanFinrank := by
    exact_mod_cast hle
  exact lt_of_le_of_lt hle_nat (ENat.coe_lt_top _)

/-- Lemma 10.72.4: if `R` is Noetherian, `I ⊆ R` is an ideal, and `M` is a finite `R`-module
with `IM ≠ M`, then the `I`-depth of `M` is finite. -/
theorem depth_lt_top_of_smul_top_ne_top (I : Ideal R)
    (hIM : I • (⊤ : Submodule R M) ≠ ⊤) :
    I.depth M < ⊤ := by
  letI : Nontrivial M := by
    by_contra hM
    letI : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
    have htop : (⊤ : Submodule R M) = ⊥ := (⊤ : Submodule R M).eq_bot_of_subsingleton
    exact hIM <| by rw [htop, Submodule.smul_bot]
  letI : Nontrivial (M ⧸ I • (⊤ : Submodule R M)) := by
    simpa using hIM
  -- Choose a prime of `Supp(M / IM)` and extract the support/containment information from it.
  obtain ⟨p, hp⟩ := Module.nonempty_support_of_nontrivial
    (R := R) (M := M ⧸ I • (⊤ : Submodule R M))
  rcases support_quotient_prime_contains_ideal (R := R) (M := M) I (p := p) hp
    with ⟨hpM, hIp⟩
  let Rp := Localization.AtPrime p.asIdeal
  let Mp := LocalizedModule.AtPrime p.asIdeal M
  have hdepth_le_local : I.depth M ≤ moduleDepth Rp Mp := by
    -- Every global `I`-regular sequence localizes to a maximal-ideal regular sequence on `Mₚ`.
    rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I M hIM]
    by_cases hlocal : maximalIdeal Rp • (⊤ : Submodule Rp Mp) = ⊤
    · rw [show moduleDepth Rp Mp = ⊤ from Ideal.depth_eq_top_of_smul_top (maximalIdeal Rp) Mp hlocal]
      exact le_top
    · rw [show moduleDepth Rp Mp =
          sSup (Ideal.regularSequenceLengths (maximalIdeal Rp) Mp) from
          Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal Rp) Mp hlocal]
      refine sSup_le ?_
      intro d hd
      exact le_sSup (regularSequenceLengths_subset_localizationAtPrime
        (R := R) (M := M) I p hpM hIp hd)
  -- The localized depth is finite, so the original depth is finite as well.
  exact lt_of_le_of_lt hdepth_le_local <|
    moduleDepth_localizationAtPrime_lt_top_of_mem_support (R := R) (M := M) p hpM

end Ideal

/-! ### Lemma_10_72_5 (from Chap10) -/
universe u

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open IsLocalRing
open RingTheory
open RingTheory.Sequence
open scoped ENat Pointwise

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]

/- Domain triage:
* primary domain: local commutative algebra of module depth and residue-field Ext groups;
* sampled owner declarations of the same kind: `Ideal.depth`, the chapter-local bridge
  `moduleDepth`, and `Abelian.Ext` on `ModuleCat`;
* best owner abstraction: `Ideal.depth`, with `moduleDepth R M` as the canonical local bridge for
  the main theorem surface, while `Abelian.Ext` is the owner of the residue-field `Ext` groups
  whose first nonvanishing degree is the source-facing content here;
* layer: `moduleDepth` remains the owner-facing bridge reused downstream, while the least
  nonvanishing residue-field `Ext` degree is source-facing derived data in this file.
* primitive vs derived split: the primitive data here are the groups `Ext^i_R(k, M)` themselves;
  nonvanishing in degree `i` and the first such degree are derived API and should be built from
  that owner rather than encoded by repeated raw existential statements.
-/

/-- The residue-field `Ext` group `Ext^i_R(ResidueField R, M)`. -/
abbrev residueFieldExt (i : ℕ) :=
  Abelian.Ext (ModuleCat.of R (ResidueField R)) (ModuleCat.of R M) i

/-- Degree `i` is the first kind of datum used in this file: `Ext^i_R(ResidueField R, M)` is
nonzero. -/
def residueFieldExtNonzero (i : ℕ) : Prop :=
  ∃ e : residueFieldExt R M i, e ≠ 0

/-- Helper for Lemma 10.72.5: the maximal ideal cannot generate a nonzero finite module over a
local ring. This lets us rewrite `moduleDepth` as a supremum of regular-sequence lengths. -/
lemma maximalIdeal_smul_top_ne_top :
    maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ := by
  -- A Jacobson-ideal version of Nakayama rules out `𝔪 M = M` for a nonzero finite module.
  simpa [ne_comm] using
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator R M)))

/-- Helper for Lemma 10.72.5: over a Noetherian local ring, depth zero is equivalent to the
absence of an `M`-regular element in the maximal ideal. -/
lemma moduleDepth_eq_zero_iff_no_maximalIdeal_regular :
    moduleDepth R M = 0 ↔ ¬ ∃ x ∈ maximalIdeal R, IsSMulRegular M x := by
  have hsmul :
      maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top (R := R) (M := M)
  rw [show moduleDepth R M = sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) from
    Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) M hsmul]
  constructor
  · intro hdepth hreg
    rcases hreg with ⟨x, hx, hxreg⟩
    -- A single regular element in `𝔪` gives a length-one regular sequence, forcing positive depth.
    have hge : (1 : ℕ∞) ≤ sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) := by
      refine le_sSup ?_
      refine ⟨[x], ?_, ?_, by simp⟩
      · exact IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal M
          (by
            intro r hr
            simpa [List.mem_singleton.mp hr] using hx)
          ((isWeaklyRegular_singleton_iff M x).2 hxreg)
      · simpa using hx
    exact (ENat.one_le_iff_ne_zero.1 hge) hdepth
  · intro hno
    apply le_antisymm
    · refine sSup_le ?_
      intro d hd
      rcases hd with ⟨rs, hreg, hmem, rfl⟩
      cases rs with
      | nil =>
          simp
      | cons x xs =>
          exfalso
          have hx : x ∈ maximalIdeal R := by
            exact hmem (Ideal.subset_span (by simp))
          have hxreg : IsSMulRegular M x :=
            ((isRegular_cons_iff M x xs).1 hreg).1
          exact hno ⟨x, hx, hxreg⟩
    · exact bot_le

/-- Helper for Lemma 10.72.5: the residue field is annihilated exactly by the maximal ideal. -/
lemma module_annihilator_residueField_eq_maximalIdeal :
    Module.annihilator R (ResidueField R) = maximalIdeal R := by
  ext x
  constructor
  · intro hx
    -- Evaluating at `1` identifies annihilators with the kernel of `R → κ(R)`.
    have hx0 : algebraMap R (ResidueField R) x = 0 := by
      simpa [Algebra.smul_def] using (Module.mem_annihilator.mp hx (1 : ResidueField R))
    exact (IsLocalRing.residue_eq_zero_iff (R := R) x).mp <| by
      simpa [IsLocalRing.ResidueField.algebraMap_eq] using hx0
  · intro hx
    -- Once `x` maps to zero in the residue field, it kills every residue-class scalar.
    have hx0 : algebraMap R (ResidueField R) x = 0 := by
      simpa [IsLocalRing.ResidueField.algebraMap_eq] using
        (IsLocalRing.residue_eq_zero_iff (R := R) x).mpr hx
    exact Module.mem_annihilator.mpr fun y ↦ by
      rw [Algebra.smul_def, hx0, zero_mul]

/-- Helper for Lemma 10.72.5: nonvanishing of `Ext⁰_R(k, M)` is the same as the existence of a
nonzero `R`-linear map `k → M`. -/
lemma residueFieldExtNonzero_zero_iff_exists_nonzero_linearMap :
    residueFieldExtNonzero R M 0 ↔ ∃ f : ResidueField R →ₗ[R] M, f ≠ 0 := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨(CategoryTheory.Abelian.Ext.addEquiv₀ e).hom, ?_⟩
    intro hf
    apply he
    apply (CategoryTheory.Abelian.Ext.addEquiv₀).injective
    exact ModuleCat.hom_injective (by simpa using hf)
  · rintro ⟨f, hf⟩
    refine ⟨(CategoryTheory.Abelian.Ext.addEquiv₀).symm (ModuleCat.ofHom f), ?_⟩
    intro heq
    have hmor : ModuleCat.ofHom f = 0 := by
      simpa using congrArg (fun e ↦ CategoryTheory.Abelian.Ext.addEquiv₀ e) heq
    have hf0 : f = 0 := by
      simpa using congrArg ModuleCat.Hom.hom hmor
    exact hf hf0

/-- Helper for Lemma 10.72.5: a nonzero linear map from the residue field exists exactly when the
space of such maps is not subsingleton. -/
lemma exists_nonzero_linearMap_iff_not_subsingleton :
    (∃ f : ResidueField R →ₗ[R] M, f ≠ 0) ↔
      ¬ Subsingleton (ResidueField R →ₗ[R] M) := by
  constructor
  · rintro ⟨f, hf⟩ hsub
    exact hf (Subsingleton.elim _ _)
  · intro hsub
    classical
    by_cases hlin : Subsingleton (ResidueField R →ₗ[R] M)
    · exact False.elim (hsub hlin)
    · letI : Nontrivial (ResidueField R →ₗ[R] M) :=
        not_subsingleton_iff_nontrivial.mp hlin
      obtain ⟨f, hf⟩ := exists_ne (0 : ResidueField R →ₗ[R] M)
      exact ⟨f, hf⟩

/-- Helper for Lemma 10.72.5: `Ext⁰_R(k, M)` is nonzero exactly in the depth-zero case. -/
lemma residueFieldExtNonzero_zero_iff_moduleDepth_eq_zero :
    residueFieldExtNonzero R M 0 ↔ moduleDepth R M = 0 := by
  have hsub :
      Subsingleton (ResidueField R →ₗ[R] M) ↔
        ∃ x ∈ maximalIdeal R, IsSMulRegular M x := by
    constructor
    · intro hlin
      rcases
          (IsSMulRegular.subsingleton_linearMap_iff (R := R) (M := M)
            (N := ResidueField R)).1 hlin with
        ⟨x, hx, hxreg⟩
      refine ⟨x, ?_, hxreg⟩
      simpa [module_annihilator_residueField_eq_maximalIdeal (R := R)] using hx
    · rintro ⟨x, hx, hxreg⟩
      exact
        (IsSMulRegular.subsingleton_linearMap_iff (R := R) (M := M)
          (N := ResidueField R)).2
          ⟨x, by simpa [module_annihilator_residueField_eq_maximalIdeal (R := R)] using hx, hxreg⟩
  -- The degree-zero Ext group is `Hom(k, M)`, and depth zero is the negation of the same
  -- regular-element criterion that controls subsingularity of `Hom(k, M)`.
  rw [residueFieldExtNonzero_zero_iff_exists_nonzero_linearMap (R := R) (M := M),
    exists_nonzero_linearMap_iff_not_subsingleton (R := R) (M := M),
    moduleDepth_eq_zero_iff_no_maximalIdeal_regular (R := R) (M := M)]
  simpa [hsub]

/-- Helper for Lemma 10.72.5: positive depth yields a nonzerodivisor in the maximal ideal. -/
lemma exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero
    (hdepth : moduleDepth R M ≠ 0) :
    ∃ x ∈ maximalIdeal R, IsSMulRegular M x := by
  by_contra hno
  exact hdepth ((moduleDepth_eq_zero_iff_no_maximalIdeal_regular (R := R) (M := M)).2 hno)

/-- Helper for Lemma 10.72.5: when the depth is the natural number `n`, some regular sequence in
the maximal ideal realizes that exact length. -/
lemma exists_regularSequence_of_length_eq_moduleDepth {n : ℕ}
    (hdepth : moduleDepth R M = n) :
    ∃ rs : List R, IsRegular M rs ∧ Ideal.ofList rs ≤ maximalIdeal R ∧ rs.length = n := by
  have hsmul :
      maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top (R := R) (M := M)
  have hsSup :
      sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) = n := by
    rw [← Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) M hsmul]
    exact hdepth
  by_cases hn : n = 0
  · refine ⟨[], ?_, by simp, by simpa [hn]⟩
    simpa using (IsRegular.nil R M)
  · by_contra hno
    have hsSup_le : sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) ≤ n - 1 := by
      refine sSup_le ?_
      intro d hd
      rcases hd with ⟨rs, hreg, hmem, rfl⟩
      have hrs_le :
          (rs.length : ℕ∞) ≤ sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) := by
        refine le_sSup ?_
        exact ⟨rs, hreg, hmem, rfl⟩
      have hrs_le_nat : rs.length ≤ n := by
        simpa [hsSup] using hrs_le
      have hrs_ne : rs.length ≠ n := by
        intro hrs_eq
        exact hno ⟨rs, hreg, hmem, hrs_eq⟩
      have hrs_lt : rs.length < n := lt_of_le_of_ne hrs_le_nat hrs_ne
      exact_mod_cast Nat.le_pred_of_lt hrs_lt
    have hnot_le : ¬ sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) ≤ n - 1 := by
      rw [hsSup]
      have hlt_nat : n - 1 < n := by
        omega
      have hlt : ((n - 1 : ℕ) : ℕ∞) < n := by
        exact_mod_cast hlt_nat
      exact not_le_of_gt hlt
    exact hnot_le hsSup_le

/-- Helper for Lemma 10.72.5: if `depth(M) = n + 1`, then one can choose a maximal-ideal
nonzerodivisor whose quotient has depth exactly `n`. -/
lemma exists_mem_maximalIdeal_isSMulRegular_and_depth_drop_of_eq_succ {n : ℕ}
    (hdepth : moduleDepth R M = n + 1) :
    ∃ x ∈ maximalIdeal R, IsSMulRegular M x ∧ moduleDepth R (QuotSMulTop x M) = n := by
  obtain ⟨rs, hreg, hmem, hlen⟩ :=
    exists_regularSequence_of_length_eq_moduleDepth (R := R) (M := M) hdepth
  cases rs with
  | nil =>
      cases Nat.succ_ne_zero n (by simpa using hlen)
  | cons x xs =>
      have hx : x ∈ maximalIdeal R := by
        exact hmem (Ideal.subset_span (by simp))
      rcases (isRegular_cons_iff (M := M) x xs).1 hreg with ⟨hxreg, hxsreg⟩
      have hxs_len : xs.length = n := by
        simpa using hlen
      refine ⟨x, hx, hxreg, le_antisymm ?_ ?_⟩
      · -- Any longer regular sequence on the quotient would prepend to a too-long one on `M`.
        have hquot_smul :
            maximalIdeal R • (⊤ : Submodule R (QuotSMulTop x M)) ≠ ⊤ := by
          letI : Nontrivial (QuotSMulTop x M) :=
            nontrivial_quotSMulTop_of_mem_maximalIdeal (R := R) (L := M) hx
          simpa using maximalIdeal_smul_top_ne_top (R := R) (M := QuotSMulTop x M)
        rw [show moduleDepth R (QuotSMulTop x M) =
            sSup (Ideal.regularSequenceLengths (maximalIdeal R) (QuotSMulTop x M)) from
            Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) (QuotSMulTop x M)
              hquot_smul]
        refine sSup_le ?_
        intro d hd
        rcases hd with ⟨ys, hysreg, hysmem, rfl⟩
        have hx_single : IsRegular M [x] := by
          letI : Nontrivial (QuotSMulTop x M) :=
            nontrivial_quotSMulTop_of_mem_maximalIdeal (R := R) (L := M) hx
          exact IsRegular.cons hxreg (by simpa using (IsRegular.nil R (QuotSMulTop x M)))
        have hsingleton :
            Ideal.ofList [x] • (⊤ : Submodule R M) = x • (⊤ : Submodule R M) := by
          simp [Submodule.ideal_span_singleton_smul]
        have hysreg' : IsRegular (M ⧸ (Ideal.ofList [x] • (⊤ : Submodule R M))) ys := by
          exact ((Submodule.quotEquivOfEq _ _ hsingleton).isRegular_congr ys).2 hysreg
        have hcons_reg : IsRegular M ([x] ++ ys) := by
          simpa using RingTheory.Sequence.isRegular_append_of_isRegular_of_quotient_isRegular
            (M := M) hx_single hysreg'
        have hcons_mem : Ideal.ofList ([x] ++ ys) ≤ maximalIdeal R := by
          refine Ideal.span_le.mpr ?_
          intro r hr
          rcases (by simpa [List.mem_append] using hr : r = x ∨ r ∈ ys) with rfl | hyr
          · exact hx
          · exact hysmem (Ideal.subset_span hyr)
        have hcons_le :
            (([x] ++ ys).length : ℕ∞) ≤ moduleDepth R M := by
          have hsmul :
              maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
            maximalIdeal_smul_top_ne_top (R := R) (M := M)
          rw [show moduleDepth R M =
              sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) from
              Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) M hsmul]
          refine le_sSup ?_
          exact ⟨[x] ++ ys, hcons_reg, hcons_mem, rfl⟩
        have hlength_le : ([x] ++ ys).length ≤ n + 1 := by
          simpa [hdepth] using hcons_le
        have hys_le : ys.length ≤ n := by
          simpa using hlength_le
        exact_mod_cast hys_le
      · -- The tail of a depth-realizing regular sequence gives the lower bound on the quotient depth.
        have hquot_smul :
            maximalIdeal R • (⊤ : Submodule R (QuotSMulTop x M)) ≠ ⊤ := by
          letI : Nontrivial (QuotSMulTop x M) :=
            nontrivial_quotSMulTop_of_mem_maximalIdeal (R := R) (L := M) hx
          simpa using maximalIdeal_smul_top_ne_top (R := R) (M := QuotSMulTop x M)
        rw [show moduleDepth R (QuotSMulTop x M) =
            sSup (Ideal.regularSequenceLengths (maximalIdeal R) (QuotSMulTop x M)) from
            Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) (QuotSMulTop x M)
              hquot_smul]
        have hxs_le :
            ((xs.length : ℕ∞) ≤
              sSup (Ideal.regularSequenceLengths (maximalIdeal R) (QuotSMulTop x M))) := by
          refine le_sSup ?_
          refine ⟨xs, hxsreg, ?_, ?_⟩
          · refine Ideal.span_le.mpr ?_
            intro r hr
            exact hmem (Ideal.subset_span (List.mem_cons_of_mem _ hr))
          · rfl
        simpa [hxs_len] using hxs_le

/-- Helper for Lemma 10.72.5: an element of the maximal ideal annihilates the residue field. -/
lemma smul_residueField_eq_zero_of_mem_maximalIdeal {x : R}
    (hx : x ∈ maximalIdeal R) :
    ∀ y : ResidueField R, x • y = 0 := by
  intro y
  -- Rewrite maximal-ideal membership as an annihilator statement and apply it to `y`.
  have hx_ann : x ∈ Module.annihilator R (ResidueField R) := by
    simpa [module_annihilator_residueField_eq_maximalIdeal (R := R)] using hx
  exact Module.mem_annihilator.mp hx_ann y

/-- Helper for Lemma 10.72.5: in the long exact sequence for `0 → M --x→ M → M/xM → 0`, the
endomorphism of `Ext^i_R(k, M)` induced by multiplication by `x ∈ 𝔪` is zero. -/
lemma residueFieldExt_self_map_zero_of_mem_maximalIdeal {x : R} {i : ℕ}
    (hx : x ∈ maximalIdeal R) (e : residueFieldExt R M i) :
    e.comp (mk₀ (ModuleCat.smulShortComplex (ModuleCat.of R M) x).f) (add_zero i) = 0 := by
  -- Route correction: normalize the categorical self-map to scalar multiplication by `x`
  -- before using Lemma 10.71.8, instead of fighting the long exact sequence API directly.
  have hsmul : x • e = 0 := by
    exact
      smul_ext_eq_zero_of_annihilates_target_or_source
        (R := R) (M := ResidueField R) (N := M)
        (x := x)
        (hx := Or.inr (smul_residueField_eq_zero_of_mem_maximalIdeal (R := R) (x := x) hx))
        (i := i) (e := e)
  -- The first map in `smulShortComplex` is multiplication by `x` on `M`.
  rw [smul_eq_comp_mk₀] at hsmul
  simpa [ModuleCat.smulShortComplex] using hsmul

/-- Helper for Lemma 10.72.5: once `Ext^i_R(k, M)` vanishes, the long exact sequence for
`0 → M --x→ M → M/xM → 0` identifies nonvanishing of `Ext^i_R(k, M/xM)` with nonvanishing of
`Ext^(i+1)_R(k, M)`. -/
lemma residueFieldExt_profile_step_of_prev_vanishing {x : R} {i : ℕ}
    (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x)
    (hprev : ¬ residueFieldExtNonzero R M i) :
    residueFieldExtNonzero R (QuotSMulTop x M) i ↔ residueFieldExtNonzero R M (i + 1) := by
  let S := ModuleCat.smulShortComplex (ModuleCat.of R M) x
  let hS : S.ShortExact :=
    IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of R M) hreg
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e.comp hS.extClass rfl, ?_⟩
    intro hzero
    -- Exactness identifies the kernel of the connecting morphism with the image of `Ext^i(k, M)`.
    obtain ⟨e', he'⟩ :=
      covariant_sequence_exact₃ (ModuleCat.of R (ResidueField R)) hS e rfl hzero
    have he'zero : e' = 0 := by
      by_contra he'zero
      exact hprev ⟨e', he'zero⟩
    have hcomp_zero : e'.comp (mk₀ S.g) (add_zero i) = 0 := by
      simp [he'zero]
    have heq0 : e = 0 := by
      calc
        e = e'.comp (mk₀ S.g) (add_zero i) := he'.symm
        _ = 0 := hcomp_zero
    exact he heq0
  · rintro ⟨e, he⟩
    -- The self-map on `Ext^(i+1)(k, M)` is zero because `x` annihilates the residue field.
    have hself : e.comp (mk₀ S.f) (add_zero (i + 1)) = 0 := by
      simpa [S] using
        residueFieldExt_self_map_zero_of_mem_maximalIdeal
          (R := R) (M := M) (x := x) (i := i + 1) hx e
    obtain ⟨e', he'⟩ :=
      covariant_sequence_exact₁ (ModuleCat.of R (ResidueField R)) hS e hself (n₀ := i) rfl
    refine ⟨e', ?_⟩
    intro he'zero
    have hcomp_zero : e'.comp hS.extClass rfl = 0 := by
      rw [he'zero]
      exact
        zero_comp
          (X := ModuleCat.of R (ResidueField R))
          (Y := S.X₃) (Z := S.X₁) (n := i) hS.extClass (i + 1) rfl
    have heq0 : e = 0 := by
      calc
        e = e'.comp hS.extClass rfl := he'.symm
        _ = 0 := hcomp_zero
    exact he heq0

/-- Helper for Lemma 10.72.5: depth `n` determines the first nonzero residue-field `Ext` group and
forces vanishing in smaller degrees. -/
lemma residueFieldExt_profile_of_depth_eq {n : ℕ}
    (hdepth : moduleDepth R M = n) :
    residueFieldExtNonzero R M n ∧ ∀ i < n, ¬ residueFieldExtNonzero R M i := by
  induction n generalizing M with
  | zero =>
      refine ⟨?_, ?_⟩
      · -- In depth zero, the source criterion is exactly the nonvanishing of `Ext⁰(k, M)`.
        exact (residueFieldExtNonzero_zero_iff_moduleDepth_eq_zero (R := R) (M := M)).2 hdepth
      · intro i hi
        exact (Nat.not_lt_zero _ hi).elim
  | succ n ih =>
      obtain ⟨x, hx, hreg, hquotdepth⟩ :=
        exists_mem_maximalIdeal_isSMulRegular_and_depth_drop_of_eq_succ
          (R := R) (M := M) (n := n) hdepth
      letI : Nontrivial (QuotSMulTop x M) :=
        nontrivial_quotSMulTop_of_mem_maximalIdeal (R := R) (L := M) hx
      have hquot_profile :=
        ih (M := QuotSMulTop x M) hquotdepth
      have hzero_vanish : ¬ residueFieldExtNonzero R M 0 := by
        intro hzero
        have hdepth_zero :
            moduleDepth R M = 0 :=
          (residueFieldExtNonzero_zero_iff_moduleDepth_eq_zero (R := R) (M := M)).1 hzero
        have hsucc_ne_zero : (((n + 1 : ℕ) : WithTop ℕ) ≠ 0) := by
          exact_mod_cast Nat.succ_ne_zero n
        exact hsucc_ne_zero (hdepth.symm.trans hdepth_zero)
      have hvanish_lt : ∀ i < n + 1, ¬ residueFieldExtNonzero R M i := by
        intro i hi
        induction' i with i ih_i
        · exact hzero_vanish
        · have hprev : ¬ residueFieldExtNonzero R M i := by
            apply ih_i
            exact Nat.lt_trans (Nat.lt_succ_self i) hi
          have hquot_vanish : ¬ residueFieldExtNonzero R (QuotSMulTop x M) i := by
            exact hquot_profile.2 i (Nat.lt_of_succ_lt_succ hi)
          intro hnonzero
          exact hquot_vanish <|
            (residueFieldExt_profile_step_of_prev_vanishing
              (R := R) (M := M) (x := x) (i := i) hx hreg hprev).mpr hnonzero
      have hprev_n : ¬ residueFieldExtNonzero R M n :=
        hvanish_lt n (Nat.lt_succ_self n)
      refine ⟨?_, hvanish_lt⟩
      -- After proving vanishing below `n + 1`, the quotient nonvanishing in degree `n`
      -- transfers across the long exact sequence to `Ext^(n+1)(k, M)`.
      exact
        (residueFieldExt_profile_step_of_prev_vanishing
          (R := R) (M := M) (x := x) (i := n) hx hreg hprev_n).mp hquot_profile.1

/-- Some residue-field Ext group of a nonzero finite module over a Noetherian local ring is
nonzero. -/
-- Proof sketch: finite depth gives a natural number `n = depth(M)`, and the profile theorem shows
-- that `Ext^n_R(ResidueField R, M)` is already nonzero.
theorem exists_nonzero_residueFieldExt :
    ∃ i : ℕ, residueFieldExtNonzero R M i := by
  have hsmul :
      maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top (R := R) (M := M)
  have hfiniteDepth : moduleDepth R M < ⊤ := by
    simpa [moduleDepth] using
      Ideal.depth_lt_top_of_smul_top_ne_top (R := R) (I := maximalIdeal R) (M := M) hsmul
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hfiniteDepth)
  refine ⟨n, ?_⟩
  exact
    (residueFieldExt_profile_of_depth_eq (R := R) (M := M) (n := n) <|
      by simpa using hn.symm).1

/-- The least index for which `Ext^i_R(ResidueField R, M)` is nonzero. -/
noncomputable def firstNonzeroResidueFieldExtIndex : ℕ :=
  let _ : DecidablePred (residueFieldExtNonzero R M) := Classical.decPred _
  Nat.find <| exists_nonzero_residueFieldExt R M

/-- The first nonvanishing residue-field Ext group of `M` is nonzero in the defining degree. -/
-- Proof sketch: this is the defining property of `Nat.find` applied to
-- `exists_nonzero_residueFieldExt`.
theorem firstNonzeroResidueFieldExtIndex_spec :
    residueFieldExtNonzero R M (firstNonzeroResidueFieldExtIndex R M) := by
  -- `Nat.find` returns a witness for the existential used in the definition.
  classical
  simpa [firstNonzeroResidueFieldExtIndex] using
    Nat.find_spec (exists_nonzero_residueFieldExt R M)

-- Proof sketch: let `i(M)` be `firstNonzeroResidueFieldExtIndex M`. When `moduleDepth M = 0`, the
-- zeroth Ext group is `Hom_R(ResidueField R, M)`, and its nonvanishing is equivalent to
-- `maximalIdeal R ∈ associatedPrimes R M`. For positive depth, choose a nonzerodivisor
-- `x ∈ maximalIdeal R`, apply the long exact Ext sequence for `0 → M --x→ M → M / xM → 0`, use
-- that `x` acts trivially on residue-field Ext groups, deduce `i(M / xM) = i(M) - 1`, and combine
-- this with the depth drop `moduleDepth (M / xM) = moduleDepth M - 1`.
/-- Lemma 10.72.5: for a nonzero finite module `M` over a Noetherian local ring `R`, the depth of
`M` is the least integer `i` such that `Ext^i_R(ResidueField R, M)` is nonzero. -/
theorem moduleDepth_eq_firstNonzeroResidueFieldExtIndex :
    moduleDepth R M = (firstNonzeroResidueFieldExtIndex R M : WithTop ℕ) := by
  classical
  have hsmul :
      maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top (R := R) (M := M)
  have hfiniteDepth : moduleDepth R M < ⊤ := by
    simpa [moduleDepth] using
      Ideal.depth_lt_top_of_smul_top_ne_top (R := R) (I := maximalIdeal R) (M := M) hsmul
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hfiniteDepth)
  have hdepth : moduleDepth R M = n := by
    simpa using hn.symm
  have hprofile :=
    residueFieldExt_profile_of_depth_eq (R := R) (M := M) (n := n) hdepth
  have hfind_le : firstNonzeroResidueFieldExtIndex R M ≤ n := by
    exact Nat.find_min' (exists_nonzero_residueFieldExt R M) hprofile.1
  have hfind_ge : n ≤ firstNonzeroResidueFieldExtIndex R M := by
    by_contra hlt
    exact
      (hprofile.2 _ (lt_of_not_ge hlt))
        (firstNonzeroResidueFieldExtIndex_spec (R := R) (M := M))
  rw [hdepth, le_antisymm hfind_le hfind_ge]
  rfl

end

/-! ### Lemma_10_72_6 (from Chap10) -/
universe u

namespace CategoryTheory
namespace ShortComplex
namespace ShortExact

section

variable {R : Type u} [Ring R]
variable {S : ShortComplex (ModuleCat.{u} R)}
variable [Module.Finite R S.X₁] [Module.Finite R S.X₃]

/-- In a short exact sequence of finite modules, the middle term is finite. -/
instance finite_X₂ (hS : S.ShortExact) : Module.Finite R S.X₂ :=
  Module.Finite.of_exact
    ((moduleCat_exact_iff_function_exact S).mp hS.exact)
    hS.moduleCat_surjective_g

end

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {S : ShortComplex (ModuleCat.{u} R)}
variable [Module.Finite R S.X₁] [Module.Finite R S.X₃]

open CategoryTheory.Abelian.Ext
open IsLocalRing
open scoped ENat

/- Domain-style sampling:
* primary domain: local commutative algebra of module depth in short exact sequences of finite
  modules, with the proof route passing through the canonical covariant long exact `Ext` sequence;
* sampled owner declarations of the same kind:
  `moduleDepth`,
  `Module.Finite.of_exact`,
  `CategoryTheory.ShortComplex.ShortExact`,
  `CategoryTheory.Abelian.Ext.covariantSequence_exact`;
* best owner abstraction: `moduleDepth` is the chapter owner surface for local depth, while
  `S : ShortComplex (ModuleCat R)` with `hS : S.ShortExact` is the canonical owner for the short
  exact sequence data;
* source/core/bridge triage: this file is `source-facing`. No upstream theorem already packages
  the depth-lemma inequalities themselves, so the refinement should keep these three inequalities
  as the public owner statements rather than introducing a parallel wrapper or a fake recall;
* primitive vs derived split: the primitive data are just the short exact sequence `S` and the
  chapter owner `moduleDepth` on its three terms. The comparisons below are derived theorems from
  Lemma `10.72.5` and the recalled long exact `Ext` owner of Lemma `10.71.6`, so no extra public
  data/package structure belongs here. In particular, finite generation of `S.X₂` is itself a
  derived owner instance `hS.finite_X₂`, while any zero-endpoint case splits needed to use
  Lemma `10.72.5`
  belong in the proof rather than in the public theorem hypotheses.
-/

/-- Helper for Lemma 10.72.6: a linear equivalence preserves the set of regular-sequence lengths
with entries in a fixed ideal. -/
private theorem regularSequenceLengths_eq_of_linearEquiv {M N : Type u} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (I : Ideal R) (e : M ≃ₗ[R] N) :
    Ideal.regularSequenceLengths I M = Ideal.regularSequenceLengths I N := by
  -- Transport each regular sequence across the equivalence and then reverse the argument.
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).1 hreg, hI, rfl⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).2 hreg, hI, rfl⟩

/-- Helper for Lemma 10.72.6: depth is invariant under a linear equivalence of finite modules. -/
private theorem idealDepth_eq_of_linearEquiv {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N] (I : Ideal R)
    (e : M ≃ₗ[R] N) :
    Ideal.depth I M = Ideal.depth I N := by
  -- The `IM = M` branch is preserved by the equivalence, and otherwise the same regular-sequence
  -- lengths compute the depth on both sides.
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
      regularSequenceLengths_eq_of_linearEquiv (R := R) (M := M) (N := N) I e]

/-- Helper for Lemma 10.72.6: isomorphic finite `R`-modules have the same depth. -/
private theorem moduleDepth_eq_of_moduleIso {M N : ModuleCat.{u} R}
    [Module.Finite R M] [Module.Finite R N] (e : M ≅ N) :
    moduleDepth R M = moduleDepth R N := by
  -- Forget the module isomorphism to a linear equivalence and reuse depth invariance.
  simpa [moduleDepth] using
    idealDepth_eq_of_linearEquiv (R := R) (M := M) (N := N) (maximalIdeal R) e.toLinearEquiv

/-- Helper for Lemma 10.72.6: a finite subsingleton module has infinite depth. -/
private theorem moduleDepth_eq_top_of_subsingleton (M : ModuleCat.{u} R) [Module.Finite R M]
    [Subsingleton M] :
    moduleDepth R M = ⊤ := by
  -- For a zero module, `𝔪 • M = M`, so the depth definition lands in the `⊤` branch.
  have htopbot : (⊤ : Submodule R M) = ⊥ := by
    ext x
    simp [Subsingleton.elim x 0]
  have hsmul_bot : maximalIdeal R • (⊥ : Submodule R M) = ⊥ := by
    ext x
    simp
  have hsmul : maximalIdeal R • (⊤ : Submodule R M) = ⊤ := by
    rw [htopbot, hsmul_bot]
  change Ideal.depth (maximalIdeal R) M = ⊤
  simpa using Ideal.depth_eq_top_of_smul_top (maximalIdeal R) M hsmul

section ExtTransport

variable [Module.Finite R S.X₂]
variable [Nontrivial S.X₁] [Nontrivial S.X₂] [Nontrivial S.X₃]

/-- Helper for Lemma 10.72.6: if the residue-field `Ext^n` groups of the two endpoints vanish,
then the middle `Ext^n` group also vanishes. -/
private lemma residueFieldExt_vanish_middle_of_end_vanish (hS : S.ShortExact) {n : ℕ}
    (hleft : ¬ residueFieldExtNonzero R S.X₁ n)
    (hright : ¬ residueFieldExtNonzero R S.X₃ n) :
    ¬ residueFieldExtNonzero R S.X₂ n := by
  rintro ⟨e, he⟩
  by_cases hg : e.comp (mk₀ S.g) (add_zero n) = 0
  · -- Exactness at `Ext^n(k, S.X₂)` then lifts `e` to the left endpoint.
    obtain ⟨e₁, he₁⟩ := covariant_sequence_exact₂ (ModuleCat.of R (ResidueField R)) hS e hg
    have he₁_ne : e₁ ≠ 0 := by
      intro he₁_zero
      apply he
      calc
        e = e₁.comp (mk₀ S.f) (add_zero n) := he₁.symm
        _ = 0 := by simp [he₁_zero]
    exact hleft ⟨e₁, he₁_ne⟩
  · -- Otherwise the image of `e` in the right endpoint is already a nonzero class.
    exact hright ⟨e.comp (mk₀ S.g) (add_zero n), hg⟩

/-- Helper for Lemma 10.72.6: vanishing in the middle degree and in the next left degree forces
vanishing on the right. -/
private lemma residueFieldExt_vanish_right_of_middle_vanish_of_left_succ_vanish (hS : S.ShortExact)
    {n : ℕ} (hmiddle : ¬ residueFieldExtNonzero R S.X₂ n)
    (hleft_succ : ¬ residueFieldExtNonzero R S.X₁ (n + 1)) :
    ¬ residueFieldExtNonzero R S.X₃ n := by
  rintro ⟨e, he⟩
  by_cases hδ : e.comp hS.extClass rfl = 0
  · -- Exactness at `Ext^n(k, S.X₃)` lifts a zero boundary class back to the middle term.
    obtain ⟨e₂, he₂⟩ :=
      covariant_sequence_exact₃ (ModuleCat.of R (ResidueField R)) hS e rfl hδ
    have he₂_ne : e₂ ≠ 0 := by
      intro he₂_zero
      apply he
      calc
        e = e₂.comp (mk₀ S.g) (add_zero n) := he₂.symm
        _ = 0 := by simp [he₂_zero]
    exact hmiddle ⟨e₂, he₂_ne⟩
  · -- A nonzero boundary produces the forbidden left-side class in degree `n + 1`.
    exact hleft_succ ⟨e.comp hS.extClass rfl, hδ⟩

/-- Helper for Lemma 10.72.6: at degree `0`, vanishing in the middle forces vanishing on the
left because `Hom(k, -)` preserves monomorphisms. -/
private lemma residueFieldExt_vanish_left_zero_of_middle_vanish (hS : S.ShortExact)
    (hmiddle : ¬ residueFieldExtNonzero R S.X₂ 0) :
    ¬ residueFieldExtNonzero R S.X₁ 0 := by
  let _ : Mono S.f := hS.mono_f
  rintro ⟨e, he⟩
  have himage_ne : e.comp (mk₀ S.f) (add_zero 0) ≠ 0 := by
    intro hzero
    apply he
    have himage_eq :
        ((mk₀ S.f).postcomp (ModuleCat.of R (ResidueField R)) (add_zero 0)) e =
          ((mk₀ S.f).postcomp (ModuleCat.of R (ResidueField R)) (add_zero 0)) 0 := by
      simpa using hzero
    exact (postcomp_mk₀_injective_of_mono (ModuleCat.of R (ResidueField R)) S.f) himage_eq
  -- Injectivity of the degree-zero map sends a nonzero left class to a nonzero middle class.
  exact hmiddle ⟨e.comp (mk₀ S.f) (add_zero 0), himage_ne⟩

/-- Helper for Lemma 10.72.6: vanishing in the middle degree `n + 1` and on the right in degree
`n` forces vanishing on the left in degree `n + 1`. -/
private lemma residueFieldExt_vanish_left_succ_of_middle_vanish_of_right_vanish (hS : S.ShortExact)
    {n : ℕ} (hmiddle_succ : ¬ residueFieldExtNonzero R S.X₂ (n + 1))
    (hright : ¬ residueFieldExtNonzero R S.X₃ n) :
    ¬ residueFieldExtNonzero R S.X₁ (n + 1) := by
  rintro ⟨e, he⟩
  by_cases hf : e.comp (mk₀ S.f) (add_zero (n + 1)) = 0
  · -- Exactness at `Ext^(n+1)(k, S.X₁)` lifts a zero image to a right-side class.
    obtain ⟨e₃, he₃⟩ :=
      covariant_sequence_exact₁ (ModuleCat.of R (ResidueField R)) hS e hf (n₀ := n) rfl
    have he₃_ne : e₃ ≠ 0 := by
      intro he₃_zero
      apply he
      calc
        e = e₃.comp hS.extClass rfl := he₃.symm
        _ = 0 := by simp [he₃_zero]
    exact hright ⟨e₃, he₃_ne⟩
  · -- Otherwise the image of `e` in the middle term is already a forbidden nonzero class.
    exact hmiddle_succ ⟨e.comp (mk₀ S.f) (add_zero (n + 1)), hf⟩

end ExtTransport

-- Proof sketch: first dispose of the degenerate cases where `S.X₁ = 0` or `S.X₃ = 0`, in which
-- the short exact sequence identifies `S.X₂` with one endpoint and the inequality is immediate.
-- In the nonzero case, identify each depth with the least degree of a nonvanishing residue-field
-- `Ext` group using Lemma `10.72.5`, apply the covariant long exact `Ext` sequence from
-- Lemma `10.71.6` to the short exact sequence `S`, and compare the first nonvanishing degrees.
/-- Lemma 10.72.6 (1): in a short exact sequence of finite modules over a Noetherian local ring,
the depth of the middle module is at least the minimum of the depths of the two end modules. -/
theorem moduleDepth_middle_ge_min (hS : S.ShortExact) :
    letI : Module.Finite R S.X₂ := hS.finite_X₂
    moduleDepth R S.X₂ ≥ min (moduleDepth R S.X₁) (moduleDepth R S.X₃) := by
  letI : Module.Finite R S.X₂ := hS.finite_X₂
  by_cases hX₁ : Subsingleton S.X₁
  · -- If the left term vanishes, short exactness identifies the middle term with the right term.
    let _ : IsIso S.g := (ShortExact.isIso_g_iff hS).2 (ModuleCat.isZero_of_subsingleton S.X₁)
    have hdepth₁ : moduleDepth R S.X₁ = ⊤ :=
      moduleDepth_eq_top_of_subsingleton (R := R) S.X₁
    have hdepth₂₃ : moduleDepth R S.X₂ = moduleDepth R S.X₃ :=
      moduleDepth_eq_of_moduleIso (R := R) (asIso S.g)
    simpa [hdepth₁, hdepth₂₃]
  by_cases hX₃ : Subsingleton S.X₃
  · -- If the right term vanishes, short exactness identifies the middle term with the left term.
    let _ : IsIso S.f := (ShortExact.isIso_f_iff hS).2 (ModuleCat.isZero_of_subsingleton S.X₃)
    have hdepth₃ : moduleDepth R S.X₃ = ⊤ :=
      moduleDepth_eq_top_of_subsingleton (R := R) S.X₃
    have hdepth₁₂ : moduleDepth R S.X₁ = moduleDepth R S.X₂ :=
      moduleDepth_eq_of_moduleIso (R := R) (asIso S.f)
    simpa [hdepth₃, hdepth₁₂]
  -- In the nondegenerate case, compare the first nonvanishing residue-field `Ext` degrees.
  letI : Nontrivial S.X₁ := not_subsingleton_iff_nontrivial.mp hX₁
  letI : Nontrivial S.X₃ := not_subsingleton_iff_nontrivial.mp hX₃
  letI : Nontrivial S.X₂ := Function.Injective.nontrivial hS.moduleCat_injective_f
  let i₁ := firstNonzeroResidueFieldExtIndex R S.X₁
  let i₂ := firstNonzeroResidueFieldExtIndex R S.X₂
  let i₃ := firstNonzeroResidueFieldExtIndex R S.X₃
  have hdepth₁ : moduleDepth R S.X₁ = (i₁ : WithTop ℕ) := by
    simpa [i₁] using moduleDepth_eq_firstNonzeroResidueFieldExtIndex (R := R) (M := S.X₁)
  have hdepth₂ : moduleDepth R S.X₂ = (i₂ : WithTop ℕ) := by
    simpa [i₂] using moduleDepth_eq_firstNonzeroResidueFieldExtIndex (R := R) (M := S.X₂)
  have hdepth₃ : moduleDepth R S.X₃ = (i₃ : WithTop ℕ) := by
    simpa [i₃] using moduleDepth_eq_firstNonzeroResidueFieldExtIndex (R := R) (M := S.X₃)
  have hprofile₁ :=
    residueFieldExt_profile_of_depth_eq (R := R) (M := S.X₁) (n := i₁) hdepth₁
  have hprofile₂ :=
    residueFieldExt_profile_of_depth_eq (R := R) (M := S.X₂) (n := i₂) hdepth₂
  have hprofile₃ :=
    residueFieldExt_profile_of_depth_eq (R := R) (M := S.X₃) (n := i₃) hdepth₃
  have hnat : min i₁ i₃ ≤ i₂ := by
    by_contra hlt
    have hi₂_lt_min : i₂ < min i₁ i₃ := lt_of_not_ge hlt
    have hi₂_lt_i₁ : i₂ < i₁ := lt_of_lt_of_le hi₂_lt_min (Nat.min_le_left _ _)
    have hi₂_lt_i₃ : i₂ < i₃ := lt_of_lt_of_le hi₂_lt_min (Nat.min_le_right _ _)
    have hvanish₂ :
        ¬ residueFieldExtNonzero R S.X₂ i₂ :=
      residueFieldExt_vanish_middle_of_end_vanish (R := R) (S := S) hS
        (hprofile₁.2 i₂ hi₂_lt_i₁)
        (hprofile₃.2 i₂ hi₂_lt_i₃)
    exact hvanish₂ hprofile₂.1
  -- The index comparison is exactly the desired depth inequality after rewriting.
  rw [hdepth₁, hdepth₂, hdepth₃]
  have hcastcases : ((i₁ : WithTop ℕ) ≤ (i₂ : WithTop ℕ)) ∨
      ((i₃ : WithTop ℕ) ≤ (i₂ : WithTop ℕ)) := by
    rcases min_le_iff.mp hnat with hi₁_le_i₂ | hi₃_le_i₂
    · left
      exact_mod_cast hi₁_le_i₂
    · right
      exact_mod_cast hi₃_le_i₂
  change min (i₁ : WithTop ℕ) (i₃ : WithTop ℕ) ≤ (i₂ : WithTop ℕ)
  rw [min_le_iff]
  exact hcastcases

-- Proof sketch: as above, handle the zero-endpoint cases internally using the isomorphisms forced
-- by short exactness. Otherwise use Lemma `10.72.5` to rewrite depths as first nonvanishing
-- residue-field `Ext` degrees, then analyze the long exact `Ext` sequence of Lemma `10.71.6` for
-- `S` to show that the first nonvanishing degree of `S.X₃` is bounded below by the minimum of the
-- corresponding degrees for `S.X₂` and `S.X₁ - 1`.
/-- Lemma 10.72.6 (2): in a short exact sequence of finite modules over a Noetherian local ring,
the depth of the quotient module is at least the minimum of the depth of the middle module and one
less than the depth of the submodule. -/
theorem moduleDepth_right_ge_min (hS : S.ShortExact) :
    letI : Module.Finite R S.X₂ := hS.finite_X₂
    moduleDepth R S.X₃ ≥ min (moduleDepth R S.X₂) (moduleDepth R S.X₁ - 1) := by
  letI : Module.Finite R S.X₂ := hS.finite_X₂
  by_cases hX₁ : Subsingleton S.X₁
  · -- If the left term vanishes, `g` is an isomorphism and the estimate becomes equality.
    let _ : IsIso S.g := (ShortExact.isIso_g_iff hS).2 (ModuleCat.isZero_of_subsingleton S.X₁)
    have hdepth₁ : moduleDepth R S.X₁ = ⊤ :=
      moduleDepth_eq_top_of_subsingleton (R := R) S.X₁
    have hdepth₂₃ : moduleDepth R S.X₂ = moduleDepth R S.X₃ :=
      moduleDepth_eq_of_moduleIso (R := R) (asIso S.g)
    simpa [hdepth₁, hdepth₂₃]
  by_cases hX₃ : Subsingleton S.X₃
  · -- If the quotient vanishes, its depth is `⊤`, so the inequality is automatic.
    have hdepth₃ : moduleDepth R S.X₃ = ⊤ :=
      moduleDepth_eq_top_of_subsingleton (R := R) S.X₃
    simpa [hdepth₃]
  -- In the nondegenerate case, use exactness to compare the first nonvanishing `Ext` indices.
  letI : Nontrivial S.X₁ := not_subsingleton_iff_nontrivial.mp hX₁
  letI : Nontrivial S.X₃ := not_subsingleton_iff_nontrivial.mp hX₃
  letI : Nontrivial S.X₂ := Function.Injective.nontrivial hS.moduleCat_injective_f
  let i₁ := firstNonzeroResidueFieldExtIndex R S.X₁
  let i₂ := firstNonzeroResidueFieldExtIndex R S.X₂
  let i₃ := firstNonzeroResidueFieldExtIndex R S.X₃
  have hdepth₁ : moduleDepth R S.X₁ = (i₁ : WithTop ℕ) := by
    simpa [i₁] using moduleDepth_eq_firstNonzeroResidueFieldExtIndex (R := R) (M := S.X₁)
  have hdepth₂ : moduleDepth R S.X₂ = (i₂ : WithTop ℕ) := by
    simpa [i₂] using moduleDepth_eq_firstNonzeroResidueFieldExtIndex (R := R) (M := S.X₂)
  have hdepth₃ : moduleDepth R S.X₃ = (i₃ : WithTop ℕ) := by
    simpa [i₃] using moduleDepth_eq_firstNonzeroResidueFieldExtIndex (R := R) (M := S.X₃)
  have hprofile₁ :=
    residueFieldExt_profile_of_depth_eq (R := R) (M := S.X₁) (n := i₁) hdepth₁
  have hprofile₂ :=
    residueFieldExt_profile_of_depth_eq (R := R) (M := S.X₂) (n := i₂) hdepth₂
  have hprofile₃ :=
    residueFieldExt_profile_of_depth_eq (R := R) (M := S.X₃) (n := i₃) hdepth₃
  have hcases_nat : i₂ ≤ i₃ ∨ i₁ ≤ i₃ + 1 := by
    by_contra hnot
    have hi₃_lt_i₂ : i₃ < i₂ := lt_of_not_ge (not_or.mp hnot).1
    have hi₃_succ_lt_i₁ : i₃ + 1 < i₁ := lt_of_not_ge (not_or.mp hnot).2
    have hvanish₃ :
        ¬ residueFieldExtNonzero R S.X₃ i₃ :=
      residueFieldExt_vanish_right_of_middle_vanish_of_left_succ_vanish
        (R := R) (S := S) hS
        (hprofile₂.2 i₃ hi₃_lt_i₂)
        (hprofile₁.2 (i₃ + 1) hi₃_succ_lt_i₁)
    exact hvanish₃ hprofile₃.1
  -- Once the depths are rewritten to indices, the proved nat inequality is the claim.
  rw [hdepth₁, hdepth₂, hdepth₃]
  have hcastcases : ((i₂ : WithTop ℕ) ≤ (i₃ : WithTop ℕ)) ∨
      ((i₁ : WithTop ℕ) ≤ (i₃ : WithTop ℕ) + 1) := by
    rcases hcases_nat with hi₂_le_i₃ | hi₁_le_i₃_succ
    · left
      exact_mod_cast hi₂_le_i₃
    · right
      exact_mod_cast hi₁_le_i₃_succ
  change min (i₂ : WithTop ℕ) ((i₁ : WithTop ℕ) - 1) ≤ (i₃ : WithTop ℕ)
  rw [min_le_iff]
  have hcastcases' : ((i₂ : WithTop ℕ) ≤ (i₃ : WithTop ℕ)) ∨
      (((i₁ : WithTop ℕ) - 1) ≤ (i₃ : WithTop ℕ)) := by
    rcases hcastcases with hi₂_le_i₃ | hi₁_le_i₃_succ
    · exact Or.inl hi₂_le_i₃
    · exact Or.inr <| (tsub_le_iff_right).2 hi₁_le_i₃_succ
  exact hcastcases'

-- Proof sketch: rewrite the three depths via Lemma `10.72.5` after the same internal zero-case
-- reductions, apply the long exact covariant `Ext` sequence from Lemma `10.71.6`, and compare the
-- first nonvanishing degrees to bound the depth of `S.X₁` below by the minimum of the depth of
-- `S.X₂` and the shifted depth of `S.X₃`.
/-- Lemma 10.72.6 (3): in a short exact sequence of finite modules over a Noetherian local ring,
the depth of the submodule is at least the minimum of the depth of the middle module and one more
than the depth of the quotient module. -/
theorem moduleDepth_left_ge_min (hS : S.ShortExact) :
    letI : Module.Finite R S.X₂ := hS.finite_X₂
    moduleDepth R S.X₁ ≥ min (moduleDepth R S.X₂) (moduleDepth R S.X₃ + 1) := by
  letI : Module.Finite R S.X₂ := hS.finite_X₂
  by_cases hX₁ : Subsingleton S.X₁
  · -- If the submodule vanishes, its depth is `⊤`, so the inequality is automatic.
    have hdepth₁ : moduleDepth R S.X₁ = ⊤ :=
      moduleDepth_eq_top_of_subsingleton (R := R) S.X₁
    simpa [hdepth₁]
  by_cases hX₃ : Subsingleton S.X₃
  · -- If the quotient vanishes, `f` is an isomorphism and the inequality becomes equality.
    let _ : IsIso S.f := (ShortExact.isIso_f_iff hS).2 (ModuleCat.isZero_of_subsingleton S.X₃)
    have hdepth₃ : moduleDepth R S.X₃ = ⊤ :=
      moduleDepth_eq_top_of_subsingleton (R := R) S.X₃
    have hdepth₁₂ : moduleDepth R S.X₁ = moduleDepth R S.X₂ :=
      moduleDepth_eq_of_moduleIso (R := R) (asIso S.f)
    simpa [hdepth₃, hdepth₁₂]
  -- In the nondegenerate case, exactness bounds the first nonzero left index from below.
  letI : Nontrivial S.X₁ := not_subsingleton_iff_nontrivial.mp hX₁
  letI : Nontrivial S.X₃ := not_subsingleton_iff_nontrivial.mp hX₃
  letI : Nontrivial S.X₂ := Function.Injective.nontrivial hS.moduleCat_injective_f
  let i₁ := firstNonzeroResidueFieldExtIndex R S.X₁
  let i₂ := firstNonzeroResidueFieldExtIndex R S.X₂
  let i₃ := firstNonzeroResidueFieldExtIndex R S.X₃
  have hdepth₁ : moduleDepth R S.X₁ = (i₁ : WithTop ℕ) := by
    simpa [i₁] using moduleDepth_eq_firstNonzeroResidueFieldExtIndex (R := R) (M := S.X₁)
  have hdepth₂ : moduleDepth R S.X₂ = (i₂ : WithTop ℕ) := by
    simpa [i₂] using moduleDepth_eq_firstNonzeroResidueFieldExtIndex (R := R) (M := S.X₂)
  have hdepth₃ : moduleDepth R S.X₃ = (i₃ : WithTop ℕ) := by
    simpa [i₃] using moduleDepth_eq_firstNonzeroResidueFieldExtIndex (R := R) (M := S.X₃)
  have hprofile₁ :=
    residueFieldExt_profile_of_depth_eq (R := R) (M := S.X₁) (n := i₁) hdepth₁
  have hprofile₂ :=
    residueFieldExt_profile_of_depth_eq (R := R) (M := S.X₂) (n := i₂) hdepth₂
  have hprofile₃ :=
    residueFieldExt_profile_of_depth_eq (R := R) (M := S.X₃) (n := i₃) hdepth₃
  have hcases_nat : i₂ ≤ i₁ ∨ i₃ + 1 ≤ i₁ := by
    by_contra hnot
    have hi₁_lt_i₂ : i₁ < i₂ := lt_of_not_ge (not_or.mp hnot).1
    have hi₁_lt_i₃_succ : i₁ < i₃ + 1 := lt_of_not_ge (not_or.mp hnot).2
    by_cases hi₁_zero : i₁ = 0
    · have hzero_lt_i₂ : 0 < i₂ := by
        simpa [hi₁_zero] using hi₁_lt_i₂
      have hvanish₁ :
          ¬ residueFieldExtNonzero R S.X₁ 0 :=
        residueFieldExt_vanish_left_zero_of_middle_vanish (R := R) (S := S) hS
          (hprofile₂.2 0 hzero_lt_i₂)
      have hnonzero₁ : residueFieldExtNonzero R S.X₁ 0 := by
        simpa [hi₁_zero] using hprofile₁.1
      exact hvanish₁ hnonzero₁
    · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hi₁_zero
      have hn_succ_lt_i₂ : n + 1 < i₂ := by
        simpa [hn] using hi₁_lt_i₂
      have hn_succ_lt_i₃_succ : n + 1 < i₃ + 1 := by
        simpa [hn] using hi₁_lt_i₃_succ
      have hn_lt_i₃ : n < i₃ := Nat.lt_of_succ_lt_succ hn_succ_lt_i₃_succ
      have hvanish₁ :
          ¬ residueFieldExtNonzero R S.X₁ (n + 1) :=
        residueFieldExt_vanish_left_succ_of_middle_vanish_of_right_vanish
          (R := R) (S := S) hS
          (hprofile₂.2 (n + 1) hn_succ_lt_i₂)
          (hprofile₃.2 n hn_lt_i₃)
      have hnonzero₁ : residueFieldExtNonzero R S.X₁ (n + 1) := by
        simpa [hn] using hprofile₁.1
      exact hvanish₁ hnonzero₁
  -- Rewriting the depths reduces the claim to the natural-number inequality above.
  rw [hdepth₁, hdepth₂, hdepth₃]
  have hcastcases : ((i₂ : WithTop ℕ) ≤ (i₁ : WithTop ℕ)) ∨
      ((i₃ : WithTop ℕ) + 1 ≤ (i₁ : WithTop ℕ)) := by
    rcases hcases_nat with hi₂_le_i₁ | hi₃_succ_le_i₁
    · left
      exact_mod_cast hi₂_le_i₁
    · right
      exact_mod_cast hi₃_succ_le_i₁
  change min (i₂ : WithTop ℕ) ((i₃ : WithTop ℕ) + 1) ≤ (i₁ : WithTop ℕ)
  rw [min_le_iff]
  exact hcastcases

end

end ShortExact
end ShortComplex
end CategoryTheory
