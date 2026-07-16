import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_59_1
import stacks_proof.stacks_project.Chap10.Lemma_10_52_4

-- Declarations for this item will be appended below by the statement pipeline.

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
@[stacks 00K5]
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
