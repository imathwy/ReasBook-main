import StacksProject_2024.Chap10.Definition_10_59_8
import StacksProject_2024.Chap10.Lemma_10_59_10
import StacksProject_2024.Chap10.Lemma_10_62_7
import StacksProject_2024.Chap10.Proposition_10_60_9
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open CategoryTheory.ShortComplex
open IsLocalRing
open scoped Ideal

private theorem cast_hilbertSamuelPolynomialDegree_eq_supportDim_of_prime_quotient
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (p : PrimeSpectrum R) :
    Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R (R ⧸ p.asIdeal)) =
      Module.supportDim R (R ⧸ p.asIdeal) := by
  let S := R ⧸ p.asIdeal
  letI : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p.asIdeal) Ideal.Quotient.mk_surjective
  have hsurj : Function.Surjective (algebraMap R S) := by
    simpa [S, Ideal.Quotient.algebraMap_eq] using
      (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk p.asIdeal))
  have hmap :
      Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S := by
    exact IsLocalRing.map_maximalIdeal_of_surjective (algebraMap R S) hsurj
  have hchi :
      ∀ n : ℕ,
        χ_(maximalIdeal R) S n =
          χ_(maximalIdeal S) S n := by
    intro n
    simp only [Ideal.hilbertSamuelChi]
    let J : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R ^ (n + 1))
    have hJ :
        (maximalIdeal R ^ (n + 1) • (⊤ : Submodule R S)) = J.restrictScalars R := by
      simp [J, Ideal.smul_top_eq_map, Ideal.map_pow]
    calc
      Module.length R (S ⧸ (maximalIdeal R ^ (n + 1) • (⊤ : Submodule R S))) =
          Module.length R (S ⧸ J.restrictScalars R) := by
            rw [hJ]
      _ = Module.length R (S ⧸ J) := by
            exact LinearEquiv.length_eq (Submodule.Quotient.restrictScalarsEquiv R J)
      _ = Module.length S (S ⧸ J) := by
            rw [Module.length_eq_of_surjective hsurj]
      _ = Module.length S (S ⧸ (maximalIdeal S ^ (n + 1) : Ideal S)) := by
            have hJ' : J = maximalIdeal S ^ (n + 1) := by
              change
                Ideal.map (algebraMap R S) (maximalIdeal R ^ (n + 1)) =
                  maximalIdeal S ^ (n + 1)
              rw [Ideal.map_pow, hmap]
            rw [hJ']
      _ = Module.length S (S ⧸ (maximalIdeal S ^ (n + 1) • (⊤ : Submodule S S))) := by
            rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have hdeg :
      hilbertSamuelPolynomialDegree R S = hilbertSamuelPolynomialDegree S S := by
    let P := hilbertSamuelChiPolynomial S S
    have hP :
        ∀ᶠ n : ℕ in Filter.atTop,
          P.eval (n : ℚ) = ((χ_(maximalIdeal S) S n).toNat : ℚ) :=
        hilbertSamuelChiPolynomial_eventuallyEq S S
    have hPR :
        ∀ᶠ n : ℕ in Filter.atTop,
          P.eval (n : ℚ) = ((χ_(maximalIdeal R) S n).toNat : ℚ) := by
      filter_upwards [hP] with n hn
      simpa [hchi n] using hn
    rw [hilbertSamuelPolynomialDegree_eq_degree R S hPR, hilbertSamuelPolynomialDegree]
  have hbot : ringKrullDim S ≠ ⊥ := by
    exact ringKrullDim_ne_bot
  have htop : ringKrullDim S ≠ ⊤ := by
    exact ringKrullDim_ne_top
  let d : ℕ := ((ringKrullDim S).unbot hbot).toNat
  have hdim : ringKrullDim S = d := by
    have hneTop : (ringKrullDim S).unbot hbot ≠ ⊤ := by
      intro h
      exact htop (by
        simpa [WithBot.coe_unbot] using
          congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) h)
    have hdim' : ((ringKrullDim S).unbot hbot : WithBot ℕ∞) = d := by
      simpa [d] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
    calc
      ringKrullDim S = (ringKrullDim S).unbot hbot := by
        exact (WithBot.coe_unbot (ringKrullDim S) hbot).symm
      _ = d := hdim'
  have htfae :
      List.TFAE [ringKrullDim S = d, hilbertSamuelPolynomialDegree S S = d, _] :=
    local_noetherian_ring_dimension_tfae d
  have hdegS : hilbertSamuelPolynomialDegree S S = d :=
    (htfae.out 0 1).mp hdim
  calc
    Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R S) =
        Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree S S) := by
          rw [hdeg]
    _ = ringKrullDim S := by
          simp [hdegS, hdim]
    _ = Module.supportDim R S := by
          simpa [S] using (Module.supportDim_quotient_eq_ringKrullDim p.asIdeal).symm

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]

-- Source/core/bridge triage:
-- * source-facing: Lemma 10.62.6 identifies the textbook invariant `d(M)` with the Krull
--   dimension of `Supp(M)`;
-- * core/canonical: the owner abstractions are `hilbertSamuelPolynomialDegree` and
--   `Module.supportDim`;
-- * bridge/view: the proof reduces to prime quotients via the Noetherian filtration induction, then
--   compares the quotient-ring Hilbert-Samuel degree with `ringKrullDim` using
--   `local_noetherian_ring_dimension_tfae`.
-- Proof sketch: use a finite prime-cyclic filtration of `M` from Lemma 10.62.1. Lemma 10.59.10
-- expresses `d(M)` as the maximum of the degrees of the cyclic factors `R ⧸ 𝔭ᵢ`, and Proposition
-- 10.60.9 identifies each such degree with `ringKrullDim (R ⧸ 𝔭ᵢ)`, hence with the dimension of
-- the closed set `V(𝔭ᵢ)`. Lemma 10.62.5 identifies the minimal primes of `Supp(M)` with the
-- minimal primes occurring in the filtration, so the maximum is exactly the Krull dimension of the
-- support.
/-- Lemma 10.62.6: if `R` is a Noetherian local ring and `M` is a finite `R`-module, then the
invariant `d(M)` from Definition 10.59.8 equals the Krull dimension of `Supp(M)`, written
canonically via the lifted owner map `Nat.castOrderEmbedding.withBotMap`. -/
@[stacks 00L8]
theorem hilbertSamuelPolynomialDegree_eq_supportDim :
    Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R M) =
      Module.supportDim R M := by
  classical
  induction ‹Module.Finite R M› using
      IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
  | subsingleton N =>
      simpa using (Module.supportDim_eq_bot_of_subsingleton R N).symm
  | quotient N q e =>
      calc
        Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R N) =
            Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R (R ⧸ q.asIdeal)) := by
              rw [hilbertSamuelPolynomialDegree_eq_of_linearEquiv R N e]
        _ = Module.supportDim R (R ⧸ q.asIdeal) :=
            cast_hilbertSamuelPolynomialDegree_eq_supportDim_of_prime_quotient q
        _ = Module.supportDim R N := by
              rw [Module.supportDim_eq_of_equiv e]
  | exact N₁ N₂ N₃ f g hf hg hfg hN₁ hN₃ =>
      let S : ShortComplex (ModuleCat.{v} R) := moduleCatMk f g hfg.linearMap_comp_eq_zero
      let _ : Module.Finite R S.X₁ := by
        change Module.Finite R N₁
        infer_instance
      let _ : Module.Finite R S.X₂ := by
        change Module.Finite R N₂
        infer_instance
      let _ : Module.Finite R S.X₃ := by
        change Module.Finite R N₃
        infer_instance
      have hS : S.ShortExact := by
        refine
          { exact := (ShortExact.moduleCat_exact_iff_function_exact S).2 hfg
            mono_f := (ModuleCat.mono_iff_injective _).2 hf
            epi_g := (ModuleCat.epi_iff_surjective _).2 hg }
      have hdeg0 :
          hilbertSamuelPolynomialDegree R N₂ =
            max (hilbertSamuelPolynomialDegree R N₁) (hilbertSamuelPolynomialDegree R N₃) := by
        simpa [S] using hilbertSamuelPolynomialDegree_eq_max_of_shortExact hS
      have hdegS :
          Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R N₂) =
            max (Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R N₁) : WithBot ℕ∞)
              (Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R N₃)) := by
        simpa using
          congrArg (fun x : WithBot ℕ ↦ (Nat.castOrderEmbedding.withBotMap x : WithBot ℕ∞)) hdeg0
      have hsupS :
          Module.supportDim R N₂ =
            max (Module.supportDim R N₁ : WithBot ℕ∞) (Module.supportDim R N₃) := by
        simpa [S] using supportDim_eq_max_of_shortExact hS
      calc
        Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R N₂) =
            max (Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R N₁) : WithBot ℕ∞)
              (Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R N₃)) := hdegS
        _ = max (Module.supportDim R N₁ : WithBot ℕ∞) (Module.supportDim R N₃) := by
              rw [hN₁, hN₃]
        _ = Module.supportDim R N₂ := by
              exact hsupS.symm

end
