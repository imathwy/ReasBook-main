import Mathlib
import StacksProject_2024.Chap10.Lemma_10_65_1
import StacksProject_2024.Chap10.Lemma_10_65_3

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type x} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/- Domain triage:
* primary domain: associated primes under flat base change along `R → S`;
* source-facing layer: the chapter owner `relativeAssassin R S N` together with the textbook
  exact-annihilator set `associatedPrimesOfModule`;
* core/canonical layer: mathlib's Noetherian owner `associatedPrimes`;
* bridge/view: the contraction description of the fiberwise union coming from Lemma 10.65.1 and
  Remark 10.18.5.

This item stays at the source-facing layer. The Noetherian equality is stated for
`associatedPrimesOfModule`, and any owner-form restatement via `associatedPrimes` belongs in a
later bridge file.
-/

/-- Helper for Lemma 10.65.5: reducing `N` modulo `pS` agrees with tensoring `N` by the prime
quotient `R ⧸ p`, viewed as an `S`-module. -/
noncomputable def relativeAssassinPrimeQuotientTensorQuotientLinearEquiv (p : Ideal R) :
    relativeAssassinPrimeQuotient R S N p ≃ₗ[S] N ⊗[R] (R ⧸ p) :=
  (TensorProduct.quotTensorEquivQuotSMul N (p.map (algebraMap R S))).symm.trans <|
    (TensorProduct.congr (Ideal.qoutMapEquivTensorQout (R := R) (S := S) (I := p))
      (LinearEquiv.refl S N)).trans <|
    (TensorProduct.comm S _ N).trans <|
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N (R ⧸ p)

/-- Helper for Lemma 10.65.5: for a flat `R`-module `N`, any associated prime of the prime
quotient module `N / pN` contracts back to the fixed prime `p`. -/
theorem under_eq_of_mem_associated_primes_relative_assassin_prime_quotient_of_flat
    [Module.Flat R N] {p : PrimeSpectrum R} {q : PrimeSpectrum S}
    (hq : q.asIdeal ∈ associatedPrimesOfModule S
      (relativeAssassinPrimeQuotient R S N p.asIdeal)) :
    q.asIdeal.under R = p.asIdeal := by
  let I : Ideal S := p.asIdeal.map (algebraMap R S)
  -- Read the associated-prime witness through the quotient model `N / pN`.
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hq
  rcases hq with ⟨hqPrime, m, hm⟩
  have hp_le : p.asIdeal ≤ q.asIdeal.under R := by
    have hqbar_mem :
        q.asIdeal ∈ Ideal.comap (Ideal.Quotient.mk I) ''
          associatedPrimesOfModule (S ⧸ I)
            (relativeAssassinPrimeQuotient R S N p.asIdeal) := by
      -- The quotient presentation forces every associated prime of `N / pN` to contain `pS`.
      rw [associatedPrimesOfModule_quotient_image_comap_eq
        (R := S) (I := I) (M := relativeAssassinPrimeQuotient R S N p.asIdeal)]
      exact ⟨hqPrime, m, hm⟩
    rcases hqbar_mem with ⟨qbar, hqbar, hcomap⟩
    intro r hr
    rw [Ideal.under_def, Ideal.mem_comap]
    rw [← hcomap, Ideal.mem_comap]
    have hzero : Ideal.Quotient.mk I (algebraMap R S r) = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
    have hzero_mem : (0 : S ⧸ I) ∈ qbar := by
      simp
    simpa [hzero] using hzero_mem
  have hunder_le : q.asIdeal.under R ≤ p.asIdeal := by
    intro r hr
    by_contra hr_not_mem
    have hrbar_ne_zero : (Ideal.Quotient.mk p.asIdeal r : R ⧸ p.asIdeal) ≠ 0 := by
      simpa [Ideal.Quotient.eq_zero_iff_mem] using hr_not_mem
    have hrbar_nz :
        (Ideal.Quotient.mk p.asIdeal r : R ⧸ p.asIdeal) ∈ nonZeroDivisors (R ⧸ p.asIdeal) :=
      mem_nonZeroDivisors_iff_ne_zero.mpr hrbar_ne_zero
    let _ : Module.Flat (R ⧸ p.asIdeal) ((R ⧸ p.asIdeal) ⊗[R] N) :=
      Module.Flat.baseChange (R := R) (S := R ⧸ p.asIdeal) (M := N)
    have hreg_left_bar :
        IsSMulRegular
          ((R ⧸ p.asIdeal) ⊗[R] N) (Ideal.Quotient.mk p.asIdeal r : R ⧸ p.asIdeal) :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors hrbar_nz
    have hreg_left :
        IsSMulRegular ((R ⧸ p.asIdeal) ⊗[R] N) r :=
      hreg_left_bar.of_map (Ideal.Quotient.mk p.asIdeal) fun _ ↦ rfl
    have hreg_tensor :
        IsSMulRegular (N ⊗[R] (R ⧸ p.asIdeal)) r := by
      -- Move to the tensor model that exposes the `R ⧸ p`-regularity directly.
      exact ((TensorProduct.comm R (R ⧸ p.asIdeal) N).isSMulRegular_congr r).1 hreg_left
    have hreg_quot :
        IsSMulRegular (relativeAssassinPrimeQuotient R S N p.asIdeal) r := by
      -- Route correction: read regularity on `N / pN` through the quotient-tensor comparison
      -- before applying the associated-prime witness.
      exact
        ((LinearEquiv.restrictScalars R
          (relativeAssassinPrimeQuotientTensorQuotientLinearEquiv
            (R := R) (S := S) (N := N) p.asIdeal)).isSMulRegular_congr r).2 hreg_tensor
    have hr_torsion :
        algebraMap R S r ∈ Ideal.torsionOf S
          (relativeAssassinPrimeQuotient R S N p.asIdeal) m := by
      simpa [Ideal.under_def, hm] using hr
    have hsmul_zero : (algebraMap R S r) • m = 0 := by
      simpa [Ideal.mem_torsionOf_iff] using hr_torsion
    have hm_zero : m = 0 := hreg_quot <| by
      simpa using hsmul_zero
    have htop : q.asIdeal = ⊤ := by
      rw [hm, hm_zero, Ideal.torsionOf_zero]
    exact hqPrime.ne_top htop
  exact le_antisymm hunder_le hp_le

-- Proof sketch: rewrite the fiberwise union from the source as
-- `relativeAssassin R S N ∩ {q | q.asIdeal.under R ∈ associatedPrimesOfModule R M}` using
-- Lemma 10.65.1 together with the fiber-spectrum identification from Remark 10.18.5, then apply
-- Lemma 10.65.3(1) to the contracted prime quotient modules `N / pN`.
/-- Lemma 10.65.5 (1): if `N` is flat over `R`, then every associated prime of a fiber module
`κ(𝔭) ⊗[R] N`, viewed as a prime of `S` by the canonical map
`Spec (κ(𝔭) ⊗[R] S) → Spec S`, for `𝔭 ∈ Ass_R(M)`, is an associated prime of the base-changed
module `M ⊗[R] N`. In Lean the canonically `S`-linear tensor model is written `N ⊗[R] M`. -/
theorem fiberAssociatedPrimes_subset_associatedPrimesOfModule_tensorProduct
    [Module.Flat R N] :
    relativeAssassin R S N ∩
        { q : PrimeSpectrum S | q.asIdeal.under R ∈ associatedPrimesOfModule R M } ⊆
      { q : PrimeSpectrum S | q.asIdeal ∈ associatedPrimesOfModule S (N ⊗[R] M) } := by
  intro q hq
  rcases hq with ⟨hqA, hqM⟩
  -- Rewrite the fiberwise condition through the fixed contracted-prime quotient from Lemma 10.65.1.
  have hqAfin : q ∈ relativeAssassinAfin R S N := by
    rw [← relativeAssassinA_eq_relativeAssassinAfin_of_flat (R := R) (S := S) (N := N)]
    exact hqA
  have hqQuot :
      q.asIdeal ∈ associatedPrimesOfModule S
        (relativeAssassinPrimeQuotient R S N (q.asIdeal.under R)) := by
    simpa using hqAfin
  -- Insert the contracted prime `q ∩ R` into the union from Lemma 10.65.3(1).
  have hqUnion :
      q.asIdeal ∈ ⋃ p : Ideal R, ⋃ _ : p ∈ associatedPrimesOfModule R M,
        associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p) := by
    exact Set.mem_iUnion.mpr ⟨q.asIdeal.under R, Set.mem_iUnion.mpr ⟨hqM, hqQuot⟩⟩
  exact
    associatedPrimesOfModule_iUnion_primeQuotients_subset_tensorProduct
      (R := R) (S := S) (M := M) (N := N) hqUnion

-- Proof sketch: combine the source-facing inclusion above with the Noetherian converse furnished
-- by Lemma 10.65.3(2), again rewriting the fiberwise union through the contraction description
-- from Lemma 10.65.1 and Remark 10.18.5.
/-- Lemma 10.65.5 (2): if `R` is Noetherian and `N` is flat over `R`, then the associated primes
of `M ⊗[R] N` over `S` are exactly the fiberwise associated primes over those
`𝔭 ∈ Ass_R(M)`, viewed inside `Spec S` by the canonical maps from the fiber spectra. In Lean this
is expressed by equality with
`relativeAssassin R S N ∩ { q | q.asIdeal.under R ∈ associatedPrimesOfModule R M }`. -/
theorem associatedPrimesOfModule_tensorProduct_eq_fiberAssociatedPrimes_of_isNoetherianRing
    [Module.Flat R N] [IsNoetherianRing R] :
    { q : PrimeSpectrum S | q.asIdeal ∈ associatedPrimesOfModule S (N ⊗[R] M) } =
      relativeAssassin R S N ∩
        { q : PrimeSpectrum S | q.asIdeal.under R ∈ associatedPrimesOfModule R M } := by
  ext q
  constructor
  · intro hq
    -- Expand the Noetherian equality from Lemma 10.65.3(2) to recover a prime-quotient witness.
    have hqUnion :
        q.asIdeal ∈ ⋃ p : Ideal R, ⋃ _ : p ∈ associatedPrimesOfModule R M,
          associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p) := by
      rw [← associatedPrimesOfModule_tensorProduct_eq_iUnion_primeQuotients_of_isNoetherianRing
        (R := R) (S := S) (M := M) (N := N)]
      exact hq
    rcases Set.mem_iUnion.mp hqUnion with ⟨p, hqUnion⟩
    rcases Set.mem_iUnion.mp hqUnion with ⟨hp_assoc, hqQuot⟩
    have hp_assoc' : p ∈ associatedPrimesOfModule R M := hp_assoc
    have hp_prime : p.IsPrime := by
      rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hp_assoc
      exact hp_assoc.1
    let pSpec : PrimeSpectrum R := ⟨p, hp_prime⟩
    -- Force the branch index to be the contraction `q ∩ R`.
    have hunder :
        q.asIdeal.under R = pSpec.asIdeal := by
      exact under_eq_of_mem_associated_primes_relative_assassin_prime_quotient_of_flat
        (R := R) (S := S) (N := N) (p := pSpec) (q := q) hqQuot
    -- Rewrite the same witness back into the defining condition for `relativeAssassin`.
    have hqAfin : q ∈ relativeAssassinAfin R S N := by
      rw [mem_relativeAssassinAfin_iff, hunder]
      simpa [pSpec] using hqQuot
    have hqA : q ∈ relativeAssassin R S N := by
      rw [relativeAssassinA_eq_relativeAssassinAfin_of_flat (R := R) (S := S) (N := N)]
      exact hqAfin
    refine ⟨hqA, ?_⟩
    simpa [Set.mem_setOf_eq, pSpec] using (hunder.symm ▸ hp_assoc')
  · intro hq
    exact
      fiberAssociatedPrimes_subset_associatedPrimesOfModule_tensorProduct
        (R := R) (S := S) (M := M) (N := N) hq

end
