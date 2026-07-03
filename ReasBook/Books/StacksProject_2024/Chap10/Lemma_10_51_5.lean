import Mathlib.RingTheory.Support
import StacksProject_2024.Chap10.Lemma_10_51_4_Krull_s_intersection_theorem

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open scoped Pointwise

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

-- Proof sketch: set `N := ⨅ n, I ^ n • ⊤`. For a prime `p` containing `I`, localize at `p`.
-- The image of `I` in `R_p` lies in the Jacobson radical, so Krull intersection over the local
-- ring `R_p` gives `N_p = 0`. Then invoke the owner theorem
-- `LocalizedModule.exists_subsingleton_away` for the finite module `N` to descend that vanishing
-- to some basic open `D(f)` with `f ∉ p`.
/-- Lemma 10.51.5 (1): for the `I`-adic intersection submodule `⋂ n, I^n M` of a finite module
over a Noetherian ring, every prime ideal containing `I` admits an element outside the prime whose
localization annihilates that intersection. -/
theorem exists_notMem_prime_and_localized_iInf_pow_smul_eq_bot
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I p : Ideal R) [p.IsPrime] (hp : I ≤ p) :
    ∃ f ∉ p,
      (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M).localized (Submonoid.powers f) = ⊥ := by
  let N : Submodule R M := ⨅ n : ℕ, I ^ n • ⊤
  let Rp := Localization p.primeCompl
  have hmap :
      Ideal.map (algebraMap R Rp) I ≤ Ideal.jacobson (⊥ : Ideal Rp) := by
    calc
      Ideal.map (algebraMap R Rp) I ≤ Ideal.map (algebraMap R Rp) p := Ideal.map_mono hp
      _ = IsLocalRing.maximalIdeal Rp := by
        simpa [Rp] using IsLocalization.AtPrime.map_eq_maximalIdeal p Rp
      _ ≤ Ideal.jacobson (⊥ : Ideal Rp) := IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal Rp)
  have hNp : N.localized p.primeCompl = ⊥ := by
    have hlocal :
        (⨅ n : ℕ, (Ideal.map (algebraMap R Rp) I) ^ n • ⊤ : Submodule Rp (LocalizedModule p.primeCompl M)) =
          ⊥ :=
      Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (Ideal.map (algebraMap R Rp) I) hmap
    refine le_antisymm ?_ bot_le
    have hle :
        N.localized p.primeCompl ≤
          (⨅ n : ℕ, (Ideal.map (algebraMap R Rp) I) ^ n • ⊤ :
            Submodule Rp (LocalizedModule p.primeCompl M)) := by
      refine le_iInf fun n ↦ ?_
      change N.localized' Rp p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) ≤
        (Ideal.map (algebraMap R Rp) I) ^ n • ⊤
      refine le_trans
        ((Submodule.localized'gi Rp p.primeCompl
          (LocalizedModule.mkLinearMap p.primeCompl M)).gc.monotone_l (iInf_le _ n)) ?_
      rw [Submodule.localized'_smul, Ideal.localized'_eq_map, Ideal.map_pow, Submodule.localized'_top]
    rw [hlocal] at hle
    simpa [Rp] using hle
  have hsub : Subsingleton (LocalizedModule p.primeCompl N) := by
    let _ : Subsingleton ↥(N.localized p.primeCompl) := Submodule.subsingleton_iff_eq_bot.mpr hNp
    exact (N.localizedEquiv p.primeCompl).symm.injective.subsingleton
  let _ : Subsingleton (LocalizedModule p.primeCompl N) := hsub
  obtain ⟨f, hf, hsubf⟩ : ∃ f ∉ p, Subsingleton (LocalizedModule (.powers f) N) :=
    LocalizedModule.exists_subsingleton_away p
  let _ : Subsingleton (LocalizedModule (Submonoid.powers f) N) := hsubf
  refine ⟨f, hf, Submodule.subsingleton_iff_eq_bot.mp ?_⟩
  exact (N.localizedEquiv (Submonoid.powers f)).injective.subsingleton

/- Lemma 10.51.5 (2): if `I` is contained in the Jacobson radical of `R`, then the `I`-adic
intersection `⋂ n, I^n M` is zero. This is exactly the canonical mathlib theorem
`Ideal.iInf_pow_smul_eq_bot_of_le_jacobson`; the Jacobson radical of the ring is expressed
canonically as `(⊥ : Ideal R).jacobson`. -/
recall Ideal.iInf_pow_smul_eq_bot_of_le_jacobson

end
