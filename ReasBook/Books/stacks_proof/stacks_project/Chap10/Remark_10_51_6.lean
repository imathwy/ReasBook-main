import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap10.Lemma_10_51_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open scoped Pointwise

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-
Remark 10.51.6, first clause: for a non-unit ideal `I` in a Noetherian local ring,
Krull's intersection theorem gives `⨅ n : ℕ, I ^ n = ⊥`. This is exactly the canonical
mathlib theorem `Ideal.iInf_pow_eq_bot_of_isLocalRing`.
-/
recall Ideal.iInf_pow_eq_bot_of_isLocalRing

-- Proof sketch: apply Lemma 10.51.5 to the finite `R`-module `R`, so the `I`-adic intersection
-- ideal localizes to zero away from some `g ∉ p`. Since `f` lies in that intersection ideal, its
-- image in `Localization.Away g` belongs to the zero ideal, hence is zero.
/-- Remark 10.51.6, general clause: if `f ∈ ⋂ n I^n`, then for every prime ideal `p` containing
`I` there exists `g ∉ p` such that `f` maps to zero in `R_g = Localization.Away g`. -/
@[stacks 00IR]
theorem exists_notMem_prime_and_map_eq_zero_of_mem_iInf_pow
    (I p : Ideal R) [p.IsPrime] (hp : I ≤ p) (f : R) (hf : f ∈ ⨅ n : ℕ, (I ^ n : Ideal R)) :
    ∃ g ∉ p, algebraMap R (Localization.Away g) f = 0 := by
  let J : Ideal R := ⨅ n : ℕ, I ^ n
  have howner :
      ∃ g ∉ p, (⨅ n : ℕ, I ^ n • ⊤ : Submodule R R).localized (.powers g) = ⊥ :=
    exists_notMem_prime_and_localized_iInf_pow_smul_eq_bot R I p hp
  obtain ⟨g, hgp, hg⟩ : ∃ g ∉ p, J.localized (.powers g) = ⊥ := by
    simpa [J, smul_eq_mul, ← Ideal.one_eq_top, mul_one] using howner
  have hmem : LocalizedModule.mk f (1 : Submonoid.powers g) ∈ J.localized (.powers g) := by
    rw [Submodule.mem_localized']
    exact ⟨f, hf, 1, by simp [LocalizedModule.mkLinearMap_apply]⟩
  have hzero : LocalizedModule.mk f (1 : Submonoid.powers g) = 0 := by
    simpa [hg] using hmem
  refine ⟨g, hgp, ?_⟩
  simpa using congrArg
    (IsLocalizedModule.iso (.powers g) (Algebra.linearMap R (Localization.Away g))) hzero

end
