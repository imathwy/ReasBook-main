import Mathlib
import StacksProject_2024.Chap10.Lemma_10_52_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section Length

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable (m : Ideal R) [m.IsMaximal] [Module.Finite R M]

private theorem isFiniteLength_of_pow_smul_eq_bot_aux
    (hfg : m.FG) :
    ∀ {n : ℕ}, (m ^ n) • (⊤ : Submodule R M) = ⊥ → IsFiniteLength R M := by
  intro n
  induction n generalizing M with
  | zero =>
      intro hpow
      have htop : (⊤ : Submodule R M) = ⊥ := by simpa using hpow
      haveI : Subsingleton M := by
        have hsub : Subsingleton (Submodule R M) :=
          subsingleton_of_bot_eq_top <| by simpa [eq_comm] using htop
        exact (Submodule.subsingleton_iff R).mp hsub
      exact .of_subsingleton
  | succ n ih =>
      intro hpow
      let N : Submodule R M := (m ^ n) • (⊤ : Submodule R M)
      have hNfg : N.FG := by
        have htopfg : (⊤ : Submodule R M).FG := Module.Finite.fg_top
        dsimp [N]
        exact Submodule.FG.smul (Ideal.FG.pow hfg) htopfg
      letI : Module.Finite R N := .of_fg_top ((Submodule.fg_top N).2 hNfg)
      have hsmulN : m • N = (⊥ : Submodule R M) := by
        dsimp [N]
        simpa [pow_succ', mul_smul] using hpow
      have hNtors : Module.IsTorsionBySet R N m := by
        intro x a
        apply Subtype.ext
        have hx : (a : R) • (x : M) ∈ m • N := Submodule.smul_mem_smul a.2 x.2
        have hx0 : (a : R) • (x : M) ∈ (⊥ : Submodule R M) := by
          simpa [hsmulN] using hx
        simpa using hx0
      have hN : IsFiniteLength R N := by
        exact (isFiniteLength_iff_finite_of_isTorsionBySet hNtors).2 inferInstance
      have hQpow : (m ^ n) • (⊤ : Submodule R (M ⧸ N)) = ⊥ := by
        have hQann : m ^ n ≤ Module.annihilator R (M ⧸ N) := by
          exact (Module.isTorsionBySet_iff_subset_annihilator R (M ⧸ N)).mp <| by
            rw [Module.isTorsionBySet_quotient_iff]
            intro x r hr
            change r • x ∈ N
            exact Submodule.smul_mem_smul hr (show x ∈ (⊤ : Submodule R M) by simp)
        refine (Submodule.le_annihilator_iff).mp ?_
        simpa [Submodule.annihilator_top] using hQann
      have hQ : IsFiniteLength R (M ⧸ N) := ih hQpow
      rw [isFiniteLength_iff_isNoetherian_isArtinian]
      exact ⟨(isNoetherian_iff_submodule_quotient N).mpr
          ⟨(isFiniteLength_iff_isNoetherian_isArtinian.mp hN).1,
            (isFiniteLength_iff_isNoetherian_isArtinian.mp hQ).1⟩,
        (isArtinian_iff_submodule_quotient N).mpr
          ⟨(isFiniteLength_iff_isNoetherian_isArtinian.mp hN).2,
            (isFiniteLength_iff_isNoetherian_isArtinian.mp hQ).2⟩⟩

-- Proof sketch: use the finite filtration
-- `⊥ = m ^ n • ⊤ ⊆ m ^ (n - 1) • ⊤ ⊆ ⋯ ⊆ m • ⊤ ⊆ ⊤`. Since `m` is finitely generated and `M` is
-- finite, every submodule `m ^ i • ⊤` is finite, so each successive quotient is a finite module
-- annihilated by `m`; apply Lemma 10.52.6 to those quotients, then add the lengths with Lemma
-- 10.52.3.
/-
The owner abstraction for finite module length in mathlib is `IsFiniteLength R M`; the textbook
formulation `Module.length R M < ⊤` is the corresponding numerical specialization.
-/
/-- Lemma 10.52.8: if `m` is a finitely generated maximal ideal and a finite `R`-module `M` is
killed by a power of `m`, then `M` has finite length. This is the owner-level form of the
textbook statement `Module.length R M < ⊤`. -/
theorem isFiniteLength_of_pow_smul_eq_bot
    (hfg : m.FG) {n : ℕ} (hpow : (m ^ n) • (⊤ : Submodule R M) = ⊥) :
    IsFiniteLength R M := by
  exact isFiniteLength_of_pow_smul_eq_bot_aux m hfg hpow

end Length
