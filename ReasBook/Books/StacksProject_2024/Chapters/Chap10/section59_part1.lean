import Mathlib
import Mathlib.RingTheory.Ideal.IsPrimary
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_59_1 (from Chap10) -/
universe u v

open scoped Pointwise

section

variable {R : Type u} [CommRing R]

namespace Ideal

section

variable (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

-- Domain-style sampling for the Hilbert-Samuel owners in this file:
-- * primary domain: Hilbert-Samuel functions attached to an ideal and a module in local
--   commutative algebra;
-- * relevant owner APIs in the surrounding ecosystem: `Module.length`,
--   `Ideal.isPrimary_of_isMaximal_radical`, `IsLocalRing.eq_maximalIdeal`,
--   and Proposition `10.59.5`'s numerical-polynomial bridge for rational-valued eventual
--   polynomial statements;
-- * source-facing primitive data: the length-valued functions
--   `hilbertSamuelChi` and `hilbertSamuelPhi`;
-- * derived bridge data: later files pass from these `ℕ∞`-valued owners to `ℚ` by applying
--   `ENat.toNat` under the extra finiteness hypotheses needed there.

/-- The Hilbert-Samuel `χ`-function attached to an ideal `I` and an `R`-module `M`, given by
the lengths of the quotients `M / I^(n + 1) M`. -/
noncomputable def hilbertSamuelChi (n : ℕ) : ℕ∞ :=
  Module.length R (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M))

/-- The Hilbert-Samuel `φ`-function of `M` with respect to the ideal `I`. -/
noncomputable def hilbertSamuelPhi (n : ℕ) : ℕ∞ :=
  Module.length R
    ((I ^ n • ⊤ : Submodule R M) ⧸ (I • ⊤ : Submodule R (I ^ n • ⊤ : Submodule R M)))

end

end Ideal

/-- Source-facing notation for the Hilbert-Samuel `χ`-function. -/
scoped[Ideal] prefix:max "χ_" => Ideal.hilbertSamuelChi

/-- Source-facing notation for the Hilbert-Samuel `φ`-function. -/
scoped[Ideal] prefix:max "φ_" => Ideal.hilbertSamuelPhi

end

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

namespace Ideal

variable (I : Ideal R)

-- Source/core/bridge triage:
-- * source-facing: `Ideal.IsIdealOfDefinition` records the Stacks definition `√I = 𝔪`;
-- * core/canonical: the owner abstraction for the ideal-theoretic consequences is the mathlib
--   predicate `(I.radical).IsMaximal`, which feeds directly into `Ideal.isPrimary_of_isMaximal_radical`;
-- * bridge/view: `isIdealOfDefinition_iff_isMaximal_radical`,
--   `IsIdealOfDefinition.isMaximal_radical`, and `IsIdealOfDefinition.isPrimary` connect the
--   source predicate to that owner API.
/-- Definition 10.59.1: an ideal of a local ring is an ideal of definition if its
radical is the maximal ideal. -/
def IsIdealOfDefinition : Prop :=
  I.radical = maximalIdeal R

/-- In a local ring, the source-facing condition `√I = 𝔪` is exactly the canonical owner
statement that `√I` is maximal. -/
theorem isIdealOfDefinition_iff_isMaximal_radical {I : Ideal R} :
    I.IsIdealOfDefinition ↔ I.radical.IsMaximal := by
  rw [IsIdealOfDefinition, IsLocalRing.isMaximal_iff]

/-- An ideal of definition has maximal radical. -/
theorem IsIdealOfDefinition.isMaximal_radical {I : Ideal R} (hI : I.IsIdealOfDefinition) :
    I.radical.IsMaximal :=
  isIdealOfDefinition_iff_isMaximal_radical.1 hI

/-- An ideal of definition is primary, viewed through mathlib's canonical primary-ideal API. -/
theorem IsIdealOfDefinition.isPrimary {I : Ideal R} (hI : I.IsIdealOfDefinition) : I.IsPrimary := by
  exact isPrimary_of_isMaximal_radical hI.isMaximal_radical

/-- The maximal ideal of a local ring is an ideal of definition. -/
@[simp] theorem maximalIdeal_isIdealOfDefinition :
    (maximalIdeal R).IsIdealOfDefinition := by
  simpa [IsIdealOfDefinition] using (maximalIdeal.isMaximal R).isPrime.radical

end Ideal

end

/-! ### Lemma_10_59_2 (from Chap10) -/
universe u v

open IsLocalRing
open scoped Ideal

section

variable {R : Type u} {M : Type v}
variable [CommRing R]
variable [AddCommGroup M] [Module R M]

namespace Ideal

variable [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M]

-- Domain-style sampling for this file:
-- * primary domain: Hilbert-Samuel functions in local commutative algebra, compared along a
--   finite-colength submodule;
-- * relevant owner APIs in the surrounding ecosystem: `Ideal.hilbertSamuelChi`,
--   `Ideal.exists_pos_pow_inf_eq_pow_smul`, `Module.length_eq_add_of_exact`, and
--   `IsFiniteLength`;
-- * best owner abstraction: the source-facing owner is already `Ideal.hilbertSamuelChi`, so this
--   file should provide only comparison lemmas for that owner rather than a parallel wrapper;
-- * primitive data: the ideal of definition `I`, the submodule `N`, and the finite-length
--   quotient `M ⧸ N`;
-- * derived API: an eventual `atTop` reformulation of the cutoff inequality for later polynomial
--   arguments.

-- Proof sketch: because `I` is an ideal of definition and `M ⧸ N` has finite length, some power
-- of `I` annihilates `M ⧸ N`, equivalently `I ^ c₂ • ⊤ ≤ N`. Then use the short exact sequence
-- `0 → N / (I^(n + 1) M ∩ N) → M / I^(n + 1) M → (M ⧸ N) → 0` and additivity of module length for
-- the upper bound, while the containment `I^(n + 1) M ≤ I^(n + 1 - c₂) N` for `n ≥ c₂` gives the
-- lower bound.
/-- Helper for Lemma 10.59.2: if `M ⧸ N` has finite length, then a power of `I` sends `M` into `N`.
-/
lemma exists_pow_smul_top_le_of_isFiniteLength_quotient
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (N : Submodule R M)
    (hquot : IsFiniteLength R (M ⧸ N)) :
    ∃ c : ℕ, (I ^ c • ⊤ : Submodule R M) ≤ N := by
  -- First kill the quotient by a power of the maximal ideal.
  obtain ⟨c, hc⟩ :=
    exists_pow_maximalIdeal_smul_eq_bot_of_isFiniteLength (R := R) (M := M ⧸ N) hquot
  refine ⟨c, ?_⟩
  have hIle : I ≤ maximalIdeal R := by
    calc
      I ≤ I.radical := Ideal.le_radical
      _ = maximalIdeal R := hI
  -- Then the same exponent works for `I`, since `I ≤ maximalIdeal R`.
  have hkill : (I ^ c • (⊤ : Submodule R (M ⧸ N))) = ⊥ := by
    apply le_antisymm
    · calc
        I ^ c • (⊤ : Submodule R (M ⧸ N)) ≤ (maximalIdeal R) ^ c • ⊤ := by
          exact Submodule.smul_mono_left (Ideal.pow_right_mono hIle c)
        _ = ⊥ := hc
    · exact bot_le
  have hmap : ((I ^ c • (⊤ : Submodule R M)).map N.mkQ) = ⊥ := by
    simpa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] using hkill
  have hmaple : ((I ^ c • (⊤ : Submodule R M)).map N.mkQ) ≤ ⊥ := by
    simpa [hmap]
  exact by
    simpa [Submodule.ker_mkQ] using (Submodule.map_le_iff_le_comap.mp hmaple)

/-- Helper for Lemma 10.59.2: if `J ≤ N`, then `M ⧸ J` has length equal to the sum of the lengths
of `M ⧸ N` and `N ⧸ J`.
-/
lemma length_quotient_eq_add_length_submodule_quotient_of_le
    {J N : Submodule R M} (hJN : J ≤ N) :
    Module.length R (M ⧸ J) =
      Module.length R (M ⧸ N) + Module.length R (N ⧸ J.submoduleOf N) := by
  -- Decompose `M ⧸ J` by the image of `N` inside it.
  have hsplit :
      Module.length R (M ⧸ J) =
        Module.length R (N.map J.mkQ) + Module.length R ((M ⧸ J) ⧸ N.map J.mkQ) := by
    simpa using
      (Module.length_eq_add_of_exact
        (Submodule.subtype (N.map J.mkQ))
        (Submodule.mkQ (N.map J.mkQ))
        (Submodule.subtype_injective _)
        (Submodule.mkQ_surjective _)
        (LinearMap.exact_subtype_mkQ (N.map J.mkQ)))
  -- Identify the image of `N` with the quotient `N ⧸ J`.
  have himage :
      Module.length R (N.map J.mkQ) = Module.length R (N ⧸ J.submoduleOf N) := by
    let f : N →ₗ[R] M ⧸ J := J.mkQ.comp N.subtype
    have hker : LinearMap.ker f = J.submoduleOf N := by
      ext x
      simp [f, Submodule.submoduleOf]
    have hrange : LinearMap.range f = N.map J.mkQ := by
      simp [f, LinearMap.range_comp, Submodule.range_subtype]
    have hequiv :
        Module.length R (N ⧸ J.submoduleOf N) = Module.length R (LinearMap.range f) := by
      simpa [hker] using
        ((Submodule.quotEquivOfEq (J.submoduleOf N) (LinearMap.ker f) hker.symm).trans
          (LinearMap.quotKerEquivRange f)).length_eq
    calc
      Module.length R (N.map J.mkQ) = Module.length R (LinearMap.range f) := by
        rw [hrange]
      _ = Module.length R (N ⧸ J.submoduleOf N) := hequiv.symm
  -- Identify the remaining quotient with `M ⧸ N`.
  have hquot :
      Module.length R ((M ⧸ J) ⧸ N.map J.mkQ) = Module.length R (M ⧸ N) := by
    simpa using (Submodule.quotientQuotientEquivQuotient J N hJN).length_eq
  calc
    Module.length R (M ⧸ J) =
        Module.length R (N.map J.mkQ) + Module.length R ((M ⧸ J) ⧸ N.map J.mkQ) := hsplit
    _ = Module.length R (N ⧸ J.submoduleOf N) + Module.length R (M ⧸ N) := by
      rw [himage, hquot]
    _ = Module.length R (M ⧸ N) + Module.length R (N ⧸ J.submoduleOf N) := by
      rw [add_comm]

/-- Helper for Lemma 10.59.2: quotienting `N` by a larger denominator only decreases its length,
compared with the Hilbert-Samuel quotient at the same index.
-/
lemma length_submodule_quotient_le_hilbertSamuelChi
    (I : Ideal R) {N J : Submodule R M} {n : ℕ}
    (hpow : (I ^ (n + 1) • ⊤ : Submodule R N) ≤ J.submoduleOf N) :
    Module.length R (N ⧸ J.submoduleOf N) ≤ χ_ I N n := by
  -- The quotient map induced by enlarging the denominator is surjective.
  simpa [Ideal.hilbertSamuelChi] using
    (Module.length_le_of_surjective
      (g := (Submodule.factor hpow :
        N ⧸ (I ^ (n + 1) • ⊤ : Submodule R N) →ₗ[R] N ⧸ J.submoduleOf N))
      (Submodule.factor_surjective hpow))

/-- Helper for Lemma 10.59.2: after the cutoff containment `I ^ c M ≤ N`, the shifted
Hilbert-Samuel value of `N` is bounded above by the intermediate quotient inside `N`.
-/
lemma hilbertSamuelChi_shift_le_length_submodule_quotient
    (I : Ideal R) {N : Submodule R M} {c : ℕ}
    (hc : (I ^ c • ⊤ : Submodule R M) ≤ N) {n : ℕ} (hn : c ≤ n) :
    χ_ I N (n - c) ≤ Module.length R (N ⧸ (I ^ (n + 1) • ⊤ : Submodule R M).submoduleOf N) := by
  -- Rewrite the ambient power through the cutoff containment.
  have hambient :
      (I ^ (n + 1) • ⊤ : Submodule R M) ≤ I ^ ((n - c) + 1) • N := by
    have hsplit : (n - c + 1) + c = n + 1 := by
      omega
    calc
      (I ^ (n + 1) • ⊤ : Submodule R M) = I ^ ((n - c + 1) + c) • ⊤ := by
        rw [hsplit]
      _ = I ^ (n - c + 1) • (I ^ c • ⊤ : Submodule R M) := by
        rw [pow_add, mul_smul]
      _ ≤ I ^ (n - c + 1) • N := smul_mono_right _ hc
  -- Pull the ambient containment back to a containment of submodules of `N`.
  have hpow :
      (I ^ (n + 1) • ⊤ : Submodule R M).submoduleOf N ≤
        (I ^ ((n - c) + 1) • ⊤ : Submodule R N) := by
    have hcomap :
        Submodule.comap N.subtype (I ^ (n - c + 1) • N) =
          (I ^ (n - c + 1) • ⊤ : Submodule R N) := by
      simpa [Submodule.range_subtype] using
        (Submodule.comap_smul'' (f := N.subtype) N.subtype_injective
          (p := N) (I := I ^ (n - c + 1)) (by simpa [Submodule.range_subtype]))
    simpa [Submodule.submoduleOf, hcomap] using
      (Submodule.comap_mono hambient :
        Submodule.comap N.subtype (I ^ (n + 1) • ⊤ : Submodule R M) ≤
          Submodule.comap N.subtype (I ^ (n - c + 1) • N))
  -- Now compare lengths using the surjective factor map.
  simpa [Ideal.hilbertSamuelChi] using
    (Module.length_le_of_surjective
      (g := (Submodule.factor hpow :
        N ⧸ (I ^ (n + 1) • ⊤ : Submodule R M).submoduleOf N →ₗ[R]
          N ⧸ (I ^ ((n - c) + 1) • ⊤ : Submodule R N)))
      (Submodule.factor_surjective hpow))

/-- Lemma 10.59.2: if `N ⊆ M` has finite-length quotient, then the Hilbert-Samuel `χ`-functions
of `N` and `M` with respect to an ideal of definition `I` differ only by an additive constant and
an eventual shift in the index. This is the source-facing cutoff formulation. -/
theorem exists_hilbertSamuelChi_bounds_of_isFiniteLength_quotient
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (N : Submodule R M)
    (hquot : IsFiniteLength R (M ⧸ N)) :
    ∃ c : ℕ, ∀ n ≥ c,
      Module.length R (M ⧸ N) + χ_ I N (n - c) ≤
          χ_ I M n ∧
        χ_ I M n ≤
          Module.length R (M ⧸ N) + χ_ I N n := by
  -- Choose the cutoff power that sends `M` into `N`.
  rcases exists_pow_smul_top_le_of_isFiniteLength_quotient I hI N hquot with ⟨c, hc⟩
  refine ⟨c, fun n hn ↦ ?_⟩
  let J : Submodule R M := I ^ (n + 1) • ⊤
  have hJN : J ≤ N := by
    -- For `n ≥ c`, the denominator in `M` is already inside `N`.
    calc
      J = (I ^ (n + 1) • ⊤ : Submodule R M) := rfl
      _ ≤ I ^ c • (⊤ : Submodule R M) := by
        exact Submodule.pow_smul_top_le I M (le_trans hn n.le_succ)
      _ ≤ N := hc
  have hdecomp :
      χ_ I M n = Module.length R (M ⧸ N) + Module.length R (N ⧸ J.submoduleOf N) := by
    -- Rewrite `χ_ I M n` using the exact sequence `N / J → M / J → M / N`.
    simpa [Ideal.hilbertSamuelChi, J] using
      (length_quotient_eq_add_length_submodule_quotient_of_le (R := R) (M := M) hJN)
  have hupper :
      Module.length R (N ⧸ J.submoduleOf N) ≤ χ_ I N n := by
    -- Compare the intermediate quotient with the usual Hilbert-Samuel quotient of `N`.
    apply length_submodule_quotient_le_hilbertSamuelChi (R := R) (I := I) (N := N) (J := J)
    have hmap :
        ((I ^ (n + 1) • ⊤ : Submodule R N).map N.subtype) ≤ J := by
      simpa [J, Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] using
        (smul_mono_right (I ^ (n + 1)) (show N ≤ (⊤ : Submodule R M) by exact le_top))
    simpa [Submodule.submoduleOf] using (Submodule.map_le_iff_le_comap.mp hmap)
  have hlower :
      χ_ I N (n - c) ≤ Module.length R (N ⧸ J.submoduleOf N) := by
    -- The cutoff lets us compare `J` with a shifted power of `I` acting on `N`.
    simpa [J] using
      (hilbertSamuelChi_shift_le_length_submodule_quotient
        (R := R) (I := I) (N := N) hc hn)
  constructor
  · calc
      Module.length R (M ⧸ N) + χ_ I N (n - c) ≤
          Module.length R (M ⧸ N) + Module.length R (N ⧸ J.submoduleOf N) :=
        by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hlower (Module.length R (M ⧸ N))
      _ = χ_ I M n := hdecomp.symm
  · calc
      χ_ I M n = Module.length R (M ⧸ N) + Module.length R (N ⧸ J.submoduleOf N) := hdecomp
      _ ≤ Module.length R (M ⧸ N) + χ_ I N n := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hupper (Module.length R (M ⧸ N))

/-- Canonical eventual reformulation of Lemma 10.59.2: for a finite-colength submodule
`N ⊆ M`, the Hilbert-Samuel `χ`-function of `M` is eventually squeezed between a translate of the
Hilbert-Samuel `χ`-function of `N` and the same function shifted only by the quotient length. -/
theorem exists_eventually_hilbertSamuelChi_bounds_of_isFiniteLength_quotient
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (N : Submodule R M)
    (hquot : IsFiniteLength R (M ⧸ N)) :
    ∃ c : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
      Module.length R (M ⧸ N) + χ_ I N (n - c) ≤
          χ_ I M n ∧
        χ_ I M n ≤
          Module.length R (M ⧸ N) + χ_ I N n := by
  rcases exists_hilbertSamuelChi_bounds_of_isFiniteLength_quotient I hI N hquot with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop c] with n hn
  exact hc n hn

end Ideal

end

/-! ### Lemma_10_59_3 (from Chap10) -/
universe u v

section

variable {R : Type u} [CommRing R]
variable {I : Ideal R}

open CategoryTheory
open IsLocalRing
open scoped Ideal

variable [IsLocalRing R] [IsNoetherianRing R]

variable {S : ShortComplex (ModuleCat.{v} R)}
variable [Module.Finite R S.X₂]

namespace Ideal

/-- Helper for Lemma 10.59.3: viewing an ideal multiple of a submodule inside the ambient module
agrees with the intrinsic ideal multiple in the submodule itself. -/
private lemma submoduleOf_smul_eq_smul_top {M : Type v} [AddCommGroup M] [Module R M]
    (J : Ideal R) (N : Submodule R M) :
    (J • N).submoduleOf N = (J • (⊤ : Submodule R N)) := by
  -- Pull the ambient scalar multiple back along the subtype of `N`.
  simpa [Submodule.range_subtype] using
    (Submodule.comap_smul'' (f := N.subtype) N.subtype_injective
      (p := N) (I := J) (by simpa [Submodule.range_subtype]))

/-- Helper for Lemma 10.59.3: every quotient by a power of an ideal of definition has finite
length. -/
private lemma isFiniteLength_quotient_pow_smul_top_of_isIdealOfDefinition
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (n : ℕ) :
    IsFiniteLength R (M ⧸ (I ^ n • (⊤ : Submodule R M))) := by
  -- Compare a power of the maximal ideal with the chosen ideal of definition.
  have hleRad : maximalIdeal R ≤ I.radical := by
    rw [hI]
  obtain ⟨c, hc⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hleRad
    (Ideal.fg_of_isNoetherianRing (maximalIdeal R))
  let Q : Type v := M ⧸ (I ^ n • (⊤ : Submodule R M))
  -- The quotient is killed by `I ^ n`, hence also by a power of the maximal ideal.
  have hQtors : Module.IsTorsionBySet R Q (I ^ n : Ideal R) := by
    rw [Module.isTorsionBySet_quotient_iff]
    intro x r hr
    change r • x ∈ (I ^ n • (⊤ : Submodule R M))
    exact Submodule.smul_mem_smul hr (show x ∈ (⊤ : Submodule R M) by simp)
  have hQann : (maximalIdeal R) ^ (c * n) ≤ Module.annihilator R Q := by
    have hpow : (maximalIdeal R) ^ (c * n) ≤ I ^ n := by
      simpa [pow_mul] using Ideal.pow_right_mono hc n
    exact hpow.trans <| (Module.isTorsionBySet_iff_subset_annihilator R Q).mp hQtors
  have hpowQ : ((maximalIdeal R) ^ (c * n)) • (⊤ : Submodule R Q) = ⊥ := by
    refine (Submodule.le_annihilator_iff).mp ?_
    simpa [Submodule.annihilator_top] using hQann
  -- Finite generation of the quotient lets us apply the nilpotent maximal-ideal criterion.
  exact isFiniteLength_of_pow_smul_eq_bot (m := maximalIdeal R)
    (Ideal.fg_of_isNoetherianRing (maximalIdeal R)) hpowQ

/-- Helper for Lemma 10.59.3: Artin-Rees on the image of the left map translates into the expected
power formula for the source-side preimages. -/
private lemma comap_pow_smul_eq_pow_smul_cutoff
    (I : Ideal R) (hS : S.ShortExact) {c n : ℕ}
    (hcut :
      LinearMap.range S.f.hom ⊓ I ^ n • (⊤ : Submodule R S.X₂) =
        I ^ (n - c) • (LinearMap.range S.f.hom ⊓ I ^ c • (⊤ : Submodule R S.X₂))) :
    Submodule.comap S.f.hom (I ^ n • (⊤ : Submodule R S.X₂)) =
      I ^ (n - c) • Submodule.comap S.f.hom (I ^ c • (⊤ : Submodule R S.X₂)) := by
  -- Compare both source-side submodules after mapping them into `S.X₂`.
  apply (Submodule.map_injective_of_injective hS.moduleCat_injective_f)
  calc
    (Submodule.comap S.f.hom (I ^ n • (⊤ : Submodule R S.X₂))).map S.f.hom =
        LinearMap.range S.f.hom ⊓ I ^ n • (⊤ : Submodule R S.X₂) := by
      rw [Submodule.map_comap_eq, inf_comm]
    _ = I ^ (n - c) •
        (LinearMap.range S.f.hom ⊓ I ^ c • (⊤ : Submodule R S.X₂)) := hcut
    _ = I ^ (n - c) •
        ((Submodule.comap S.f.hom (I ^ c • (⊤ : Submodule R S.X₂))).map S.f.hom) := by
      rw [Submodule.map_comap_eq, inf_comm]
    _ =
        (I ^ (n - c) • Submodule.comap S.f.hom
          (I ^ c • (⊤ : Submodule R S.X₂))).map S.f.hom := by
      rw [Submodule.map_smul'']

/-- Helper for Lemma 10.59.3: quotienting a surjective linear map by compatible submodules preserves
surjectivity. -/
private lemma mapQ_surjective_of_surjective
    {M : Type*} [AddCommGroup M] [Module R M]
    {M' : Type*} [AddCommGroup M'] [Module R M']
    (φ : M →ₗ[R] M')
    (hφ : Function.Surjective φ)
    (p : Submodule R M)
    (q : Submodule R M')
    (hpq : p ≤ Submodule.comap φ q) :
    Function.Surjective (p.mapQ q φ hpq) := by
  -- Lift a quotient representative in the target back along the original surjection.
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective q y
  obtain ⟨x, rfl⟩ := hφ y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- Helper for Lemma 10.59.3: the short exact sequence remains exact after quotienting by
`I ^ n`. -/
private lemma mapQ_exact_of_shortExact_pow_smul
    (I : Ideal R) (hS : S.ShortExact) (n : ℕ) :
    Function.Exact
      ((Submodule.comap S.f.hom (I ^ n • (⊤ : Submodule R S.X₂))).mapQ
        (I ^ n • (⊤ : Submodule R S.X₂)) S.f.hom le_rfl)
      ((I ^ n • (⊤ : Submodule R S.X₂)).mapQ
        (I ^ n • (⊤ : Submodule R S.X₃)) S.g.hom
        (Submodule.smul_top_le_comap_smul_top (I ^ n) S.g.hom)) := by
  let J₂ : Submodule R S.X₂ := I ^ n • (⊤ : Submodule R S.X₂)
  let J₃ : Submodule R S.X₃ := I ^ n • (⊤ : Submodule R S.X₃)
  have hExact : Function.Exact S.f.hom S.g.hom := by
    simpa using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  -- Route correction: descend exactness through the quotient API directly, rather than by a
  -- representative chase inside the quotient modules.
  refine
    (Function.Exact.exact_mapQ_iff hExact le_rfl
      (Submodule.smul_top_le_comap_smul_top (I ^ n) S.g.hom)).2 ?_
  -- Surjectivity of `S.g` identifies the target quotient denominator with the image of the middle
  -- denominator.
  simpa [J₂, J₃, Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr hS.moduleCat_surjective_g]

/-- Helper for Lemma 10.59.3: the quotient map induced from the left term is injective. -/
private lemma mapQ_injective_of_comap
    (J : Submodule R S.X₂) :
    Function.Injective ((Submodule.comap S.f.hom J).mapQ J S.f.hom le_rfl) := by
  -- Compute the kernel of the quotient map and collapse it to `⊥`.
  rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
  simp

/-- Helper for Lemma 10.59.3: quotienting the short exact sequence by `I ^ n` gives the expected
length identity for the predecessor-indexed Hilbert-Samuel `χ`-function. -/
private lemma hilbertSamuelChi_pred_eq_target_add_source_quotient_length
    (I : Ideal R) (hS : S.ShortExact) {n : ℕ} (hn : 0 < n) :
    χ_ I S.X₂ (n - 1) =
      χ_ I S.X₃ (n - 1) +
        Module.length R
          (S.X₁ ⧸ Submodule.comap S.f.hom (I ^ n • (⊤ : Submodule R S.X₂))) := by
  let J₁ : Submodule R S.X₁ := Submodule.comap S.f.hom (I ^ n • (⊤ : Submodule R S.X₂))
  let J₂ : Submodule R S.X₂ := I ^ n • (⊤ : Submodule R S.X₂)
  let J₃ : Submodule R S.X₃ := I ^ n • (⊤ : Submodule R S.X₃)
  let fQ : S.X₁ ⧸ J₁ →ₗ[R] S.X₂ ⧸ J₂ := J₁.mapQ J₂ S.f.hom le_rfl
  let gQ : S.X₂ ⧸ J₂ →ₗ[R] S.X₃ ⧸ J₃ :=
    J₂.mapQ J₃ S.g.hom (Submodule.smul_top_le_comap_smul_top (I ^ n) S.g.hom)
  have hfQ : Function.Injective fQ := by
    -- The descended left map has trivial kernel.
    dsimp [fQ, J₁, J₂]
    exact mapQ_injective_of_comap (S := S) (J := I ^ n • (⊤ : Submodule R S.X₂))
  have hgQ : Function.Surjective gQ := by
    -- The descended right map stays surjective because `S.g` is surjective.
    dsimp [gQ, J₂, J₃]
    exact mapQ_surjective_of_surjective S.g.hom hS.moduleCat_surjective_g
      (I ^ n • (⊤ : Submodule R S.X₂))
      (I ^ n • (⊤ : Submodule R S.X₃))
      (Submodule.smul_top_le_comap_smul_top (I ^ n) S.g.hom)
  have hExactQ : Function.Exact fQ gQ := by
    -- Exactness descends to the quotient sequence.
    dsimp [fQ, gQ, J₁, J₂, J₃]
    exact mapQ_exact_of_shortExact_pow_smul (S := S) I hS n
  have hlen :
      Module.length R (S.X₂ ⧸ J₂) =
        Module.length R (S.X₁ ⧸ J₁) + Module.length R (S.X₃ ⧸ J₃) := by
    -- Apply additivity of length to the quotient short exact sequence.
    simpa [fQ, gQ] using Module.length_eq_add_of_exact fQ gQ hfQ hgQ hExactQ
  -- Rewrite the quotient lengths back into the predecessor-indexed `χ` values.
  calc
    χ_ I S.X₂ (n - 1) = Module.length R (S.X₂ ⧸ J₂) := by
      rw [Ideal.hilbertSamuelChi, show n - 1 + 1 = n by omega]
    _ = Module.length R (S.X₁ ⧸ J₁) + Module.length R (S.X₃ ⧸ J₃) := hlen
    _ = Module.length R (S.X₃ ⧸ J₃) + Module.length R (S.X₁ ⧸ J₁) := by rw [add_comm]
    _ = χ_ I S.X₃ (n - 1) +
          Module.length R (S.X₁ ⧸ Submodule.comap S.f.hom (I ^ n • (⊤ : Submodule R S.X₂))) := by
      rw [Ideal.hilbertSamuelChi, show n - 1 + 1 = n by omega]

/-- Helper for Lemma 10.59.3: the Artin-Rees cutoff submodule has finite colength in the source. -/
private lemma isFiniteLength_quotient_cutoff_comap
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (hS : S.ShortExact) (c : ℕ) :
    IsFiniteLength R
      (S.X₁ ⧸ Submodule.comap S.f.hom (I ^ c • (⊤ : Submodule R S.X₂))) := by
  letI : Module.Finite R S.X₁ := Module.Finite.of_injective S.f.hom hS.moduleCat_injective_f
  let J₂ : Submodule R S.X₂ := I ^ c • (⊤ : Submodule R S.X₂)
  let fQ : S.X₁ ⧸ Submodule.comap S.f.hom J₂ →ₗ[R] S.X₂ ⧸ J₂ :=
    (Submodule.comap S.f.hom J₂).mapQ J₂ S.f.hom le_rfl
  have hmiddle :
      IsFiniteLength R (S.X₂ ⧸ J₂) :=
    isFiniteLength_quotient_pow_smul_top_of_isIdealOfDefinition
      (R := R) (M := S.X₂) I hI c
  -- Inject the cutoff quotient into the finite-length middle quotient.
  exact IsFiniteLength.of_injective hmiddle <| by
    dsimp [fQ, J₂]
    exact mapQ_injective_of_comap (S := S) (J := I ^ c • (⊤ : Submodule R S.X₂))

/-- Helper for Lemma 10.59.3: the source-proof decomposition is most stable in predecessor form,
before reindexing the public `χ`-statement. -/
private lemma exists_hilbertSamuelChi_predecessor_decomposition_of_shortExact
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (hS : S.ShortExact) :
    ∃ (N : Submodule R S.X₁) (c : ℕ),
      0 < c ∧
        IsFiniteLength R (S.X₁ ⧸ N) ∧
          ∀ n ≥ c + 1,
            χ_ I S.X₂ (n - 1) =
              χ_ I S.X₃ (n - 1) +
                χ_ I N (n - c - 1) +
                  Module.length R (S.X₁ ⧸ N) := by
  obtain ⟨c, hcpos, hAR⟩ :=
    Ideal.exists_pos_pow_inf_eq_pow_smul (R := R) (M := S.X₂) I (LinearMap.range S.f.hom)
  let N : Submodule R S.X₁ := Submodule.comap S.f.hom (I ^ c • (⊤ : Submodule R S.X₂))
  have hfinite : IsFiniteLength R (S.X₁ ⧸ N) := by
    simpa [N] using isFiniteLength_quotient_cutoff_comap (S := S) I hI hS c
  refine ⟨N, c, hcpos, hfinite, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  have hχ :=
    hilbertSamuelChi_pred_eq_target_add_source_quotient_length (S := S) I hS (n := n) hnpos
  have hcut :
      LinearMap.range S.f.hom ⊓ I ^ n • (⊤ : Submodule R S.X₂) =
        I ^ (n - c) • (LinearMap.range S.f.hom ⊓ I ^ c • (⊤ : Submodule R S.X₂)) :=
    by simpa [inf_comm] using hAR n (by omega)
  have hcomap :
      Submodule.comap S.f.hom (I ^ n • (⊤ : Submodule R S.X₂)) = I ^ (n - c) • N := by
    simpa [N] using comap_pow_smul_eq_pow_smul_cutoff (S := S) I hS hcut
  rw [hcomap] at hχ
  letI : Module.Finite R S.X₁ := Module.Finite.of_injective S.f.hom hS.moduleCat_injective_f
  have hpow_le : (I ^ (n - c) • N : Submodule R S.X₁) ≤ N := by
    -- Any ideal multiple of `N` still lies in `N`.
    exact Submodule.smul_le.mpr fun r hr x hx => N.smul_mem r hx
  have hlen :
      Module.length R (S.X₁ ⧸ (I ^ (n - c) • N : Submodule R S.X₁)) =
        Module.length R (S.X₁ ⧸ N) +
          Module.length R
            (N ⧸ (I ^ (n - c) • N : Submodule R S.X₁).submoduleOf N) := by
    -- Split the source quotient into the finite-colength quotient by `N` and the shifted
    -- Hilbert-Samuel quotient inside `N`.
    simpa using
      (length_quotient_eq_add_length_submodule_quotient_of_le
        (R := R) (M := S.X₁) hpow_le)
  have hχN :
      Module.length R
          (N ⧸ (I ^ (n - c) • N : Submodule R S.X₁).submoduleOf N) =
        χ_ I N (n - c - 1) := by
    -- Reinterpret the intrinsic quotient of `N` as its Hilbert-Samuel quotient at index
    -- `n - c - 1`.
    rw [Ideal.hilbertSamuelChi, show n - c - 1 + 1 = n - c by omega]
    rw [submoduleOf_smul_eq_smul_top (R := R) (J := I ^ (n - c)) (N := N)]
  calc
    χ_ I S.X₂ (n - 1) =
        χ_ I S.X₃ (n - 1) +
          Module.length R (S.X₁ ⧸ (I ^ (n - c) • N : Submodule R S.X₁)) := hχ
    _ = χ_ I S.X₃ (n - 1) +
          (Module.length R (S.X₁ ⧸ N) +
            Module.length R
              (N ⧸ (I ^ (n - c) • N : Submodule R S.X₁).submoduleOf N)) := by
      rw [hlen]
    _ = χ_ I S.X₃ (n - 1) + Module.length R (S.X₁ ⧸ N) +
          Module.length R
            (N ⧸ (I ^ (n - c) • N : Submodule R S.X₁).submoduleOf N) := by
      rw [add_assoc]
    _ = χ_ I S.X₃ (n - 1) +
          Module.length R
            (N ⧸ (I ^ (n - c) • N : Submodule R S.X₁).submoduleOf N) +
          Module.length R (S.X₁ ⧸ N) := by
      rw [add_right_comm]
    _ = χ_ I S.X₃ (n - 1) +
          χ_ I N (n - c - 1) +
          Module.length R (S.X₁ ⧸ N) := by
      rw [hχN]

/-- Helper for Lemma 10.59.3: the Hilbert-Samuel `φ`-value is the length of the successive quotient
`I^k N / I^(k + 1) N`. -/
private lemma hilbertSamuelPhi_eq_length_smul_quotient
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (N : Submodule R M) (k : ℕ) :
    φ_ I N k =
      Module.length R
        ((I ^ k • N : Submodule R M) ⧸
          (I ^ (k + 1) • N : Submodule R M).submoduleOf (I ^ k • N)) := by
  let A : Submodule R M := I ^ k • N
  let B : Submodule R M := I ^ (k + 1) • N
  let A₀ : Submodule R N := I ^ k • (⊤ : Submodule R N)
  let D₀ : Submodule R A₀ := I • (⊤ : Submodule R A₀)
  let D₁ : Submodule R (A.submoduleOf N) := I • (⊤ : Submodule R (A.submoduleOf N))
  have hA : A ≤ N := by
    -- Ideal multiples of `N` remain inside `N`.
    dsimp [A]
    exact Submodule.smul_le.mpr fun r hr x hx => N.smul_mem r hx
  have hB : B = I • A := by
    -- The next power is one more multiplication by `I`.
    dsimp [A, B]
    simp [pow_succ', mul_smul]
  have hnum : A.submoduleOf N = A₀ := by
    -- View `I ^ k N` intrinsically as a submodule of `N`.
    dsimp [A, A₀]
    exact submoduleOf_smul_eq_smul_top (I ^ k) N
  let e₀ : A₀ ≃ₗ[R] A.submoduleOf N := LinearEquiv.ofEq _ _ hnum.symm
  have hmap₀ : D₀.map (e₀ : A₀ →ₗ[R] A.submoduleOf N) = D₁ := by
    -- The transport from `A₀` to `A.submoduleOf N` preserves the intrinsic `I`-multiple.
    ext x
    simp [D₀, D₁, e₀]
  let e₁ : A.submoduleOf N ≃ₗ[R] A := Submodule.submoduleOfEquivOfLe hA
  have hmap₁ : D₁.map (e₁ : A.submoduleOf N →ₗ[R] A) = B.submoduleOf A := by
    -- After identifying `A.submoduleOf N` with `A`, the denominator becomes `I • A`.
    calc
      D₁.map (e₁ : A.submoduleOf N →ₗ[R] A) = I • (⊤ : Submodule R A) := by
        dsimp [D₁]
        rw [Submodule.map_smul'', Submodule.map_top,
          LinearMap.range_eq_top.mpr e₁.surjective]
      _ = (I • A).submoduleOf A := (submoduleOf_smul_eq_smul_top I A).symm
      _ = B.submoduleOf A := by rw [hB]
  -- Pass from the intrinsic quotient in `N` to the ambient successive quotient `I^k N / I^(k+1) N`.
  calc
    φ_ I N k = Module.length R (A₀ ⧸ D₀) := by
      rfl
    _ = Module.length R ((A.submoduleOf N) ⧸ D₁) := by
      simpa [A₀, D₀, D₁] using (Submodule.Quotient.equiv D₀ D₁ e₀ hmap₀).length_eq
    _ = Module.length R (A ⧸ B.submoduleOf A) := by
      simpa [D₁] using (Submodule.Quotient.equiv D₁ (B.submoduleOf A) e₁ hmap₁).length_eq
    _ = Module.length R
          ((I ^ k • N : Submodule R M) ⧸
            (I ^ (k + 1) • N : Submodule R M).submoduleOf (I ^ k • N)) := by
      rfl

/-- Helper for Lemma 10.59.3: positive-index Hilbert-Samuel `χ` is the sum of the corresponding
`φ`-value and the predecessor `χ`-value. -/
private lemma hilbertSamuelChi_eq_hilbertSamuelPhi_add_pred_of_pos
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) {n : ℕ} (hn : 0 < n) :
    χ_ I M n = φ_ I M n + χ_ I M (n - 1) := by
  let J : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
  let N : Submodule R M := I ^ n • (⊤ : Submodule R M)
  have hJN : J ≤ N := by
    -- The next ideal power gives a smaller denominator.
    simpa [J, N] using (Submodule.pow_smul_top_le I M n.le_succ)
  have hJI : J = I • N := by
    -- The denominator is one more ideal multiple of the numerator submodule.
    dsimp [J, N]
    simp [pow_succ', mul_smul]
  -- Decompose the quotient by `I^(n+1)` through the intermediate quotient by `I^n`.
  calc
    χ_ I M n = Module.length R (M ⧸ J) := by
      simp [Ideal.hilbertSamuelChi, J]
    _ = Module.length R (M ⧸ N) + Module.length R (N ⧸ J.submoduleOf N) := by
      simpa [J, N] using
        (length_quotient_eq_add_length_submodule_quotient_of_le
          (R := R) (M := M) hJN)
    _ = χ_ I M (n - 1) + Module.length R (N ⧸ J.submoduleOf N) := by
      rw [Ideal.hilbertSamuelChi, show n - 1 + 1 = n by omega]
    _ = χ_ I M (n - 1) + φ_ I M n := by
      congr 1
      calc
        Module.length R (N ⧸ J.submoduleOf N) =
            Module.length R (N ⧸ (I • N).submoduleOf N) := by rw [hJI]
        _ = Module.length R (N ⧸ (I • (⊤ : Submodule R N))) := by
          rw [submoduleOf_smul_eq_smul_top I N]
        _ = φ_ I M n := by
          simp [Ideal.hilbertSamuelPhi, N]
    _ = φ_ I M n + χ_ I M (n - 1) := by rw [add_comm]

/-- Helper for Lemma 10.59.3: replacing `N` by `I • N` shifts the Hilbert-Samuel `φ`-function by
one. -/
private lemma hilbertSamuelPhi_smul_submodule_shift
    {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (N : Submodule R M) (k : ℕ) :
    φ_ I (I • N : Submodule R M) k = φ_ I N (k + 1) := by
  -- Identify both sides with the same successive quotient in the ambient module.
  calc
    φ_ I (I • N : Submodule R M) k =
        Module.length R
          ((I ^ k • (I • N) : Submodule R M) ⧸
            (I ^ (k + 1) • (I • N) : Submodule R M).submoduleOf
              (I ^ k • (I • N) : Submodule R M)) := by
      rw [hilbertSamuelPhi_eq_length_smul_quotient (R := R) (I := I)
        (N := (I • N : Submodule R M)) k]
    _ = Module.length R
          ((I ^ (k + 1) • N : Submodule R M) ⧸
            (I ^ (k + 2) • N : Submodule R M).submoduleOf
              (I ^ (k + 1) • N : Submodule R M)) := by
      have hnum : (I ^ k • (I • N) : Submodule R M) = I ^ (k + 1) • N := by
        rw [← mul_smul, pow_succ]
      rw [hnum]
      have hden : (I ^ (k + 1) • (I • N) : Submodule R M) = I ^ (k + 2) • N := by
        rw [show I ^ (k + 2) = I ^ (k + 1) * I by rw [pow_succ]]
        rw [← mul_smul]
      rw [hden]
    _ = φ_ I N (k + 1) := by
      rw [hilbertSamuelPhi_eq_length_smul_quotient (R := R) (I := I)
        (N := N) (k := k + 1)]

-- Proof sketch: apply Artin-Rees to the submodule `LinearMap.range S.f.hom ⊆ S.X₂` to obtain a
-- shift `c` with `S.X₁ ∩ I^n S.X₂ = I^(n - c) (S.X₁ ∩ I^c S.X₂)` for `n ≥ c`, set
-- `N = S.X₁ ∩ I^c S.X₂`, and use additivity of `Module.length` on the short exact sequence
-- `0 → S.X₁ / (S.X₁ ∩ I^n S.X₂) → S.X₂ / I^n S.X₂ → S.X₃ / I^n S.X₃ → 0`.
/-- Lemma 10.59.3: if `I` is an ideal of definition of the Noetherian local ring `R` and
`S : ShortComplex (ModuleCat R)` is a short exact sequence of finite `R`-modules, then there
exist a submodule `N ⊆ S.X₁` of finite colength and an integer shift `c` carrying the shifted
Hilbert-Samuel decomposition for the `χ`-function. This is the primitive source-facing content;
the `φ`-decomposition is its standard finite-difference companion. -/
theorem exists_hilbertSamuelChi_decomposition_of_shortExact
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (hS : S.ShortExact) :
    ∃ (N : Submodule R S.X₁) (c : ℕ),
      IsFiniteLength R (S.X₁ ⧸ N) ∧
        ∀ n ≥ c,
          χ_ I S.X₂ n =
            χ_ I S.X₃ n +
              χ_ I N (n - c) +
                Module.length R (S.X₁ ⧸ N) := by
  rcases exists_hilbertSamuelChi_predecessor_decomposition_of_shortExact
      (S := S) I hI hS with ⟨N, c, hcpos, hfinite, hpred⟩
  refine ⟨N, c, hfinite, ?_⟩
  intro n hn
  -- Reindex the predecessor formula by substituting `n + 1` for `n`.
  have hpred' : χ_ I S.X₂ ((n + 1) - 1) =
      χ_ I S.X₃ ((n + 1) - 1) +
        χ_ I N (n + 1 - c - 1) +
          Module.length R (S.X₁ ⧸ N) := hpred (n + 1) (by omega)
  simpa [show (n + 1) - 1 = n by omega, show n + 1 - c - 1 = n - c by omega,
    add_assoc] using hpred'

/-- Companion to Lemma 10.59.3: under the same hypotheses, one may choose a finite-colength
submodule of `S.X₁` and a shift giving the corresponding shifted Hilbert-Samuel decomposition for
the `φ`-function. -/
theorem exists_hilbertSamuelPhi_decomposition_of_shortExact
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (hS : S.ShortExact) :
    ∃ (N : Submodule R S.X₁) (c : ℕ),
      IsFiniteLength R (S.X₁ ⧸ N) ∧
        ∀ n ≥ c,
          φ_ I S.X₂ n =
            φ_ I S.X₃ n +
              φ_ I N (n - c) := by
  letI : Module.Finite R S.X₁ := Module.Finite.of_injective S.f.hom hS.moduleCat_injective_f
  letI : Module.Finite R S.X₃ := Module.Finite.of_surjective S.g.hom hS.moduleCat_surjective_g
  rcases exists_hilbertSamuelChi_predecessor_decomposition_of_shortExact
      (S := S) I hI hS with ⟨N, c, hcpos, hfinite, hpred⟩
  let N' : Submodule R S.X₁ := I • N
  have hfiniteStep : IsFiniteLength R (N ⧸ (I • (⊤ : Submodule R N))) := by
    have hpow :
        IsFiniteLength R (N ⧸ (I ^ 1 • (⊤ : Submodule R N))) :=
      isFiniteLength_quotient_pow_smul_top_of_isIdealOfDefinition
        (R := R) (M := N) I hI 1
    have htop : (I ^ 1 • (⊤ : Submodule R N)) = I • (⊤ : Submodule R N) := by
      simp [pow_one]
    exact htop ▸ hpow
  have hfiniteShift : IsFiniteLength R (S.X₁ ⧸ N') := by
    have hle : N' ≤ N := by
      -- The shifted submodule remains inside `N`.
      exact Submodule.smul_le.mpr fun r hr x hx => N.smul_mem r hx
    have hlen :
        Module.length R (S.X₁ ⧸ N') =
          Module.length R (S.X₁ ⧸ N) + Module.length R (N ⧸ N'.submoduleOf N) := by
      -- Split the quotient by `I • N` through the intermediate quotient by `N`.
      simpa [N'] using
        (length_quotient_eq_add_length_submodule_quotient_of_le
          (R := R) (M := S.X₁) hle)
    have hlen_ne_top : Module.length R (S.X₁ ⧸ N') ≠ ⊤ := by
      rw [hlen]
      refine WithTop.add_ne_top.2 ⟨?_, ?_⟩
      · exact Module.length_ne_top_iff.mpr hfinite
      · have hsub : N'.submoduleOf N = I • (⊤ : Submodule R N) := by
          simpa [N'] using
            (submoduleOf_smul_eq_smul_top (R := R) (J := I) (N := N))
        exact hsub ▸ (Module.length_ne_top_iff.mpr hfiniteStep)
    exact Module.length_ne_top_iff.mp hlen_ne_top
  refine ⟨N', c + 1, hfiniteShift, ?_⟩
  intro n hn
  have hn_ge : c + 1 ≤ n := hn
  have hnpos : 0 < n := by omega
  have hχsucc :
      χ_ I S.X₂ n =
        χ_ I S.X₃ n + χ_ I N (n - c) + Module.length R (S.X₁ ⧸ N) := by
    -- Reindex the predecessor decomposition at `n + 1`.
    have hpred' : χ_ I S.X₂ ((n + 1) - 1) =
        χ_ I S.X₃ ((n + 1) - 1) +
          χ_ I N (n + 1 - c - 1) +
            Module.length R (S.X₁ ⧸ N) := hpred (n + 1) (by omega)
    simpa [show (n + 1) - 1 = n by omega, show n + 1 - c - 1 = n - c by omega,
      add_assoc] using hpred'
  have hχpred :
      χ_ I S.X₂ (n - 1) =
        χ_ I S.X₃ (n - 1) + χ_ I N (n - c - 1) + Module.length R (S.X₁ ⧸ N) :=
    hpred n hn_ge
  have hsplit₂ :=
    hilbertSamuelChi_eq_hilbertSamuelPhi_add_pred_of_pos (R := R) (M := S.X₂) I hnpos
  have hsplit₃ :=
    hilbertSamuelChi_eq_hilbertSamuelPhi_add_pred_of_pos (R := R) (M := S.X₃) I hnpos
  have hsplitN :
      χ_ I N (n - c) = φ_ I N (n - c) + χ_ I N (n - c - 1) := by
    have hposShift : 0 < n - c := by omega
    simpa using
      hilbertSamuelChi_eq_hilbertSamuelPhi_add_pred_of_pos
        (R := R) (M := N) I (n := n - c) hposShift
  have hsum :
      φ_ I S.X₂ n + χ_ I S.X₂ (n - 1) =
        (φ_ I S.X₃ n + φ_ I N (n - c)) + χ_ I S.X₂ (n - 1) := by
    -- Expand `χ(n)` into `φ(n)` plus the predecessor term and then collapse the common
    -- predecessor decomposition from the source-faithful `χ` statement.
    calc
      φ_ I S.X₂ n + χ_ I S.X₂ (n - 1) = χ_ I S.X₂ n := hsplit₂.symm
      _ = χ_ I S.X₃ n + χ_ I N (n - c) + Module.length R (S.X₁ ⧸ N) := hχsucc
      _ = (φ_ I S.X₃ n + χ_ I S.X₃ (n - 1)) +
            (φ_ I N (n - c) + χ_ I N (n - c - 1)) +
            Module.length R (S.X₁ ⧸ N) := by
        rw [hsplit₃, hsplitN]
      _ = φ_ I S.X₃ n + φ_ I N (n - c) +
            (χ_ I S.X₃ (n - 1) + χ_ I N (n - c - 1) + Module.length R (S.X₁ ⧸ N)) := by
        ac_rfl
      _ = φ_ I S.X₃ n + φ_ I N (n - c) + χ_ I S.X₂ (n - 1) := by
        rw [hχpred]
      _ = (φ_ I S.X₃ n + φ_ I N (n - c)) + χ_ I S.X₂ (n - 1) := by
        ac_rfl
  have hχpred_ne_top : χ_ I S.X₂ (n - 1) ≠ ⊤ := by
    rw [Ideal.hilbertSamuelChi, show n - 1 + 1 = n by omega, Module.length_ne_top_iff]
    exact isFiniteLength_quotient_pow_smul_top_of_isIdealOfDefinition
      (R := R) (M := S.X₂) I hI n
  have hφcore : φ_ I S.X₂ n = φ_ I S.X₃ n + φ_ I N (n - c) :=
    WithTop.add_right_cancel hχpred_ne_top hsum
  have hshift :
      φ_ I N (n - c) = φ_ I N' (n - (c + 1)) := by
    have hk : n - (c + 1) + 1 = n - c := by omega
    calc
      φ_ I N (n - c) = φ_ I N (n - (c + 1) + 1) := by rw [hk]
      _ = φ_ I (I • N : Submodule R S.X₁) (n - (c + 1)) := by
        symm
        exact hilbertSamuelPhi_smul_submodule_shift (R := R) (I := I) N (n - (c + 1))
  calc
    φ_ I S.X₂ n = φ_ I S.X₃ n + φ_ I N (n - c) := hφcore
    _ = φ_ I S.X₃ n + φ_ I N' (n - (c + 1)) := by rw [hshift]

end Ideal

end

/-! ### Lemma_10_59_4 (from Chap10) -/
universe u v

open Filter
open scoped Ideal

section

variable {R : Type u}
variable [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

namespace Ideal

variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {I I' : Ideal R}

/-- Helper for Lemma 10.59.4: two ideals of definition in a Noetherian local ring compare by a
positive power inclusion. -/
private theorem exists_pos_pow_le_of_isIdealOfDefinition
    (hI : I.IsIdealOfDefinition) (hI' : I'.IsIdealOfDefinition) :
    ∃ d : ℕ, 1 ≤ d ∧ I' ^ d ≤ I := by
  -- The common radical description puts `I'` inside `√I`, so a power of `I'` lands in `I`.
  have hleRad : I' ≤ I.radical := by
    calc
      I' ≤ I'.radical := Ideal.le_radical
      _ = IsLocalRing.maximalIdeal R := hI'
      _ = I.radical := hI.symm
  obtain ⟨c, hc⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hleRad I'.fg_of_isNoetherianRing
  refine ⟨c + 1, Nat.succ_le_succ (Nat.zero_le c), ?_⟩
  -- Replacing `c` by `c + 1` packages the witness as a positive exponent.
  calc
    I' ^ (c + 1) ≤ I' ^ c := Ideal.pow_le_pow_right (Nat.le_succ c)
    _ ≤ I := hc

/-- Helper for Lemma 10.59.4: the linear reindexing `n ↦ (2d - 1) n` makes the `I'`-power
quotient map surject onto the `I`-power quotient. -/
private theorem pow_smul_top_le_of_reindex
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {I I' : Ideal R} {d n : ℕ} (hd : I' ^ d ≤ I) (hdpos : 1 ≤ d) (hn : 1 ≤ n) :
    (I' ^ (((2 * d - 1) * n) + 1) • (⊤ : Submodule R M)) ≤ I ^ (n + 1) • ⊤ := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hdpos)
  -- The arithmetic bound converts the positive-power containment into the exact smul inclusion
  -- needed for the quotient factor map.
  have hdecomp : 2 * Nat.succ c - 1 = 2 * c + 1 := by
    omega
  have hcn : c ≤ c * n := by
    simpa [Nat.one_mul] using Nat.mul_le_mul_left c hn
  have hlast : c + 1 ≤ c * n + 1 := Nat.add_le_add_right hcn 1
  have hexp : Nat.succ c * (n + 1) ≤ ((2 * Nat.succ c - 1) * n) + 1 := by
    rw [hdecomp]
    calc
      Nat.succ c * (n + 1) = c * n + n + (c + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.succ_mul]
      _ ≤ c * n + n + (c * n + 1) := Nat.add_le_add_left hlast (c * n + n)
      _ = (2 * c + 1) * n + 1 := by
        calc
          c * n + n + (c * n + 1) = c * n + c * n + n + 1 := by
            ac_rfl
          _ = (c + c) * n + n + 1 := by rw [Nat.add_mul]
          _ = (2 * c) * n + n + 1 := by rw [two_mul]
          _ = (2 * c + 1) * n + 1 := by
            rw [Nat.add_mul, Nat.one_mul]
  have hpow : I' ^ (((2 * Nat.succ c - 1) * n) + 1) ≤ I ^ (n + 1) := by
    calc
      I' ^ (((2 * Nat.succ c - 1) * n) + 1) ≤ I' ^ (Nat.succ c * (n + 1)) :=
        Ideal.pow_le_pow_right hexp
      _ = (I' ^ Nat.succ c) ^ (n + 1) := by rw [pow_mul]
      _ ≤ I ^ (n + 1) := Ideal.pow_right_mono hd (n + 1)
  exact Submodule.smul_mono_left hpow

/-- Helper for Lemma 10.59.4: quotient length decreases when the quotient submodule gets larger. -/
private theorem length_quotient_le_of_submodule_le
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {N N' : Submodule R M} (h : N ≤ N') :
    Module.length R (M ⧸ N') ≤ Module.length R (M ⧸ N) := by
  -- The factor map `M ⧸ N → M ⧸ N'` is surjective, so module length can only decrease.
  exact Module.length_le_of_surjective
    (g := Submodule.factor h) (Submodule.factor_surjective h)

-- Proof sketch: since `I` and `I'` are ideals of definition, their radicals agree with the
-- maximal ideal, so mathlib's owner theorem `Ideal.exists_pow_le_of_le_radical_of_fg` gives a
-- power of `I'` contained in `I`. Then the quotient maps
-- `M / (I')^(c * (n + 1)) M → M / I^(n + 1) M`
-- compare the two `χ`-functions by surjectivity of the induced map on quotients. Rewriting
-- `c * (n + 1)` as `(2 * c - 1) * n + 1` for `n ≥ 1` gives the stated linear reindexing, with a
-- positive reindexing constant `a = 2 * c - 1`.
/-- Lemma 10.59.4: if `I` and `I'` are ideals of definition of the Noetherian local ring `R` and
`M` is a finite `R`-module, then the Hilbert-Samuel `χ`-function for `I` is eventually bounded
above by the Hilbert-Samuel `χ`-function for `I'` after multiplication by a positive integer. -/
theorem exists_reindex_hilbertSamuelChi_le_of_isIdealOfDefinition
    (hI : I.IsIdealOfDefinition) (hI' : I'.IsIdealOfDefinition) :
    ∃ a : ℕ, 0 < a ∧ ∀ ⦃n : ℕ⦄, 1 ≤ n →
      χ_ I M n ≤ χ_ I' M (a * n) := by
  -- First compare the two ideals of definition by a positive power containment.
  rcases exists_pos_pow_le_of_isIdealOfDefinition (I := I) (I' := I') hI hI'
    with ⟨d, hdpos, hd⟩
  refine ⟨2 * d - 1, ?_, ?_⟩
  · -- The source reindexing constant is positive because the witness exponent is positive.
    omega
  · intro n hn
    -- The quotient by the larger `I`-power is a quotient of the corresponding `I'`-power quotient.
    have hsmul :
        (I' ^ (((2 * d - 1) * n) + 1) • (⊤ : Submodule R M)) ≤ I ^ (n + 1) • ⊤ :=
      pow_smul_top_le_of_reindex (M := M) (I := I) (I' := I') hd hdpos hn
    -- Compare the Hilbert-Samuel lengths through the induced surjective factor map.
    calc
      χ_ I M n = Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) := rfl
      _ ≤ Module.length R (M ⧸ (I' ^ (((2 * d - 1) * n) + 1) • (⊤ : Submodule R M))) :=
        length_quotient_le_of_submodule_le (M := M) hsmul
      _ = χ_ I' M ((2 * d - 1) * n) := rfl

/-- Canonical `atTop` reformulation of Lemma 10.59.4: after multiplying the index by a fixed
positive integer, the Hilbert-Samuel `χ`-function for one ideal of definition is eventually
bounded above by that for the other. This is the bridge from the source-facing `n ≥ 1`
formulation to the chapter's eventual-value API. -/
theorem exists_eventually_reindex_hilbertSamuelChi_le_of_isIdealOfDefinition
    (hI : I.IsIdealOfDefinition) (hI' : I'.IsIdealOfDefinition) :
    ∃ a : ℕ, 0 < a ∧ ∀ᶠ n : ℕ in atTop,
      χ_ I M n ≤ χ_ I' M (a * n) := by
  rcases exists_reindex_hilbertSamuelChi_le_of_isIdealOfDefinition M hI hI' with
    ⟨a, ha, hle⟩
  refine ⟨a, ha, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact hle hn

end Ideal

end
