import Mathlib
import stacks_project.Chap10.Definition_10_72_1
import stacks_project.Chap10.Lemma_10_63_18
import stacks_project.Chap10.Lemma_10_72_5
import stacks_project.Chap10.Lemma_10_72_7
import stacks_project.Chap10.Lemma_10_72_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ENat
open IsLocalRing
open RingTheory.Sequence

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable (p : Ideal R) [p.IsPrime]

local notation "Rₚ" => Localization.AtPrime p
local notation "Mₚ" => LocalizedModule.AtPrime p M

/- Domain-style sampling:
* primary domain: depth for finite modules over Noetherian local rings and its behavior under
  localization at a prime;
* sampled owner declarations of the same kind:
  `moduleDepth`,
  `Localization.AtPrime`,
  `LocalizedModule.AtPrime`,
  `moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes`;
* best owner abstraction: the chapter owner surface for local depth is `moduleDepth`, while the
  localized ring/module are the canonical owner constructions `Localization.AtPrime` and
  `LocalizedModule.AtPrime`;
* source/core/bridge triage:
  `source-facing`: the depth inequality relating `M`, `Mₚ`, and `R / p`;
  `core/canonical`: `moduleDepth` together with the owner localization objects `Rₚ` and `Mₚ`;
  `bridge/view`: the quotient ring `R ⧸ p`.

Primitive data are only the local ring, the finite module, and the prime ideal. The localized ring
and module are derived from the owner localization constructions, so the public theorem surface
should name those owner objects directly instead of repeating the full expressions inline.
-/

/-- Helper for Lemma 10.72.10: a finite subsingleton module over a Noetherian local ring has
infinite depth. -/
private theorem moduleDepth_eq_top_of_subsingleton
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N] [Subsingleton N] :
    moduleDepth A N = ⊤ := by
  -- A subsingleton module already satisfies `𝔪N = N`, so the depth is infinite by definition.
  have htop_eq_bot : (⊤ : Submodule A N) = ⊥ := by
    ext n
    simp [Subsingleton.elim n 0]
  have hsmul_bot : maximalIdeal A • (⊥ : Submodule A N) = ⊥ := by
    ext n
    simp
  have hsmul_top : maximalIdeal A • (⊤ : Submodule A N) = ⊤ := by
    rw [htop_eq_bot, hsmul_bot, ← htop_eq_bot]
  change Ideal.depth (maximalIdeal A) N = ⊤
  simpa using Ideal.depth_eq_top_of_smul_top (maximalIdeal A) N hsmul_top

/-- Helper for Lemma 10.72.10: the maximal ideal of a Noetherian local ring cannot generate a
nonzero finite module. -/
private theorem maximalIdeal_smul_top_ne_top_for_entry
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N] [Nontrivial N] :
    maximalIdeal A • (⊤ : Submodule A N) ≠ ⊤ := by
  -- This is the Jacobson-ideal form of Nakayama's lemma.
  simpa [ne_comm] using
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator A N)))

/-- Helper for Lemma 10.72.10: a regular element in the maximal ideal forces positive depth. -/
private lemma one_le_moduleDepth_of_mem_maximalIdeal_of_isSMulRegular
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N] [Nontrivial N] {x : A}
    (hx : x ∈ maximalIdeal A) (hreg : IsSMulRegular N x) :
    (1 : ℕ∞) ≤ moduleDepth A N := by
  -- The singleton regular sequence `[x]` already contributes one to the depth.
  have hsingleton_reg : IsRegular N [x] := by
    exact IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal N
      (by
        intro r hr
        simpa [List.mem_singleton.mp hr] using hx)
      ((isWeaklyRegular_singleton_iff N x).2 hreg)
  have hsingleton_mem : Ideal.ofList [x] ≤ maximalIdeal A := by
    simpa using (Ideal.span_singleton_le_iff_mem (I := maximalIdeal A) (x := x)).2 hx
  have hsmul :
      maximalIdeal A • (⊤ : Submodule A N) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top_for_entry
  rw [show moduleDepth A N = sSup (Ideal.regularSequenceLengths (maximalIdeal A) N) from
    Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) N hsmul]
  refine le_sSup ?_
  exact ⟨[x], hsingleton_reg, hsingleton_mem, by simp⟩

/-- Helper for Lemma 10.72.10: linear equivalences preserve the set of regular-sequence
lengths. -/
private theorem regularSequenceLengths_eq_of_linearEquiv
    {A : Type*} [CommRing A] (I : Ideal A)
    {N₁ : Type*} [AddCommGroup N₁] [Module A N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module A N₂]
    (e : N₁ ≃ₗ[A] N₂) :
    Ideal.regularSequenceLengths I N₁ = Ideal.regularSequenceLengths I N₂ := by
  -- Transport each witness sequence across the linear equivalence.
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).1 hreg, hI, rfl⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).2 hreg, hI, rfl⟩

/-- Helper for Lemma 10.72.10: linear equivalences preserve ideal depth. -/
private theorem idealDepth_eq_of_linearEquiv
    {A : Type*} [CommRing A] (I : Ideal A)
    {N₁ : Type*} [AddCommGroup N₁] [Module A N₁] [Module.Finite A N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module A N₂] [Module.Finite A N₂]
    (e : N₁ ≃ₗ[A] N₂) :
    Ideal.depth I N₁ = Ideal.depth I N₂ := by
  -- Compare the two presentations of depth depending on whether `IN = N`.
  have htop :
      I • (⊤ : Submodule A N₁) = ⊤ ↔ I • (⊤ : Submodule A N₂) = ⊤ := by
    constructor
    · intro h
      have hmap := congrArg (Submodule.map e.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using hmap
    · intro h
      have hmap := congrArg (Submodule.map e.symm.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using hmap
  by_cases hN₁ : I • (⊤ : Submodule A N₁) = ⊤
  · rw [Ideal.depth_eq_top_of_smul_top I N₁ hN₁,
      Ideal.depth_eq_top_of_smul_top I N₂ (htop.mp hN₁)]
  · rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N₁ hN₁,
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N₂ (mt htop.mpr hN₁),
      regularSequenceLengths_eq_of_linearEquiv I e]

/-- Helper for Lemma 10.72.10: linear equivalences preserve module depth over a local ring. -/
private theorem moduleDepth_eq_of_linearEquiv
    {A : Type*} [CommRing A] [IsLocalRing A]
    {N₁ : Type*} [AddCommGroup N₁] [Module A N₁] [Module.Finite A N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module A N₂] [Module.Finite A N₂]
    (e : N₁ ≃ₗ[A] N₂) :
    moduleDepth A N₁ = moduleDepth A N₂ :=
  idealDepth_eq_of_linearEquiv (maximalIdeal A) e

/-- Helper for Lemma 10.72.10: the quotient by a prime ideal has nonnegative Krull dimension. -/
private lemma zero_le_ringKrullDim_quotient :
    (0 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  -- Prime quotients are nontrivial rings, so their Krull dimension is nonnegative.
  letI : Nontrivial (R ⧸ p) := (Ideal.Quotient.nontrivial_iff).2 (Ideal.IsPrime.ne_top inferInstance)
  exact ringKrullDim_nonneg_of_nontrivial

/-- Helper for Lemma 10.72.10: if `depth(M)` is larger than `dim(R / p)`, then no associated
prime of `M` lies above `p`. -/
private lemma associated_prime_not_above_of_ringKrullDim_quotient_lt_moduleDepth
    {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hlt : ringKrullDim (R ⧸ p) < (.some (moduleDepth R N) : WithBot ℕ∞)) :
    ∀ {q : Ideal R}, q ∈ associatedPrimes R N → ¬ p ≤ q := by
  intro q hq hpq
  -- Compare `R / q` with `R / p` through the canonical quotient map.
  have hdepth_le :
      (.some (moduleDepth R N) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q) :=
    moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes (R := R) (M := N) q hq
  have hdim_le :
      ringKrullDim (R ⧸ q) ≤ ringKrullDim (R ⧸ p) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hpq)
      (Ideal.Quotient.factor_surjective hpq)
  exact not_lt_of_ge (le_trans hdepth_le hdim_le) hlt

/-- Helper for Lemma 10.72.10: a regular element remains regular after localizing at the same
prime. -/
private theorem localizedModule_atPrime_isSMulRegular_of_isSMulRegular
    {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Nontrivial (LocalizedModule.AtPrime p N)] {x : R}
    (hx : x ∈ p) (hreg : IsSMulRegular N x) :
    IsSMulRegular (LocalizedModule.AtPrime p N) (algebraMap R (Localization.AtPrime p) x) := by
  -- Localize the singleton regular sequence `[x]` inside the maximal ideal of `Rₚ`.
  have hmem : ∀ r ∈ [x], r ∈ p := by
    intro r hr
    simpa [List.mem_singleton.mp hr] using hx
  have hreg_loc :
      IsRegular (LocalizedModule.AtPrime p N) [algebraMap R (Localization.AtPrime p) x] := by
    simpa using
      ((isWeaklyRegular_singleton_iff N x).2 hreg).isRegular_of_isLocalizedModule_of_mem
        (S := Localization.AtPrime p)
        (p := p)
        (N := LocalizedModule.AtPrime p N)
        (f := LocalizedModule.mkLinearMap p.primeCompl N)
        hmem
  exact
    ((isRegular_cons_iff
      (M := LocalizedModule.AtPrime p N)
      (algebraMap R (Localization.AtPrime p) x) []).1
      (by simpa using hreg_loc)).1

/-- Helper for Lemma 10.72.10: localizing the quotient by `x` agrees with quotienting the
localized module by the image of `x`. -/
private noncomputable def localizedModule_atPrime_quotSMulTop_equiv
    {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N] (x : R) :
    LocalizedModule.AtPrime p (QuotSMulTop x N) ≃ₗ[Localization.AtPrime p]
      QuotSMulTop (algebraMap R (Localization.AtPrime p) x) (LocalizedModule.AtPrime p N) :=
  let e₁ := LocalizedModule.equivTensorProduct (R := R) p.primeCompl (QuotSMulTop x N)
  let e₂ := (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop
    (R := R) (r := x) (M := N) (Localization.AtPrime p)).symm
  let e₃ := QuotSMulTop.congr (algebraMap R (Localization.AtPrime p) x)
    (LocalizedModule.equivTensorProduct (R := R) p.primeCompl N).symm
  e₁.trans (e₂.trans e₃)

/-- Helper for Lemma 10.72.10: after localizing at `p`, quotienting by a `p`-regular element
lowers the localized depth by one. -/
private theorem moduleDepth_localized_quotSMulTop_eq_sub_one_of_regular
    {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N] {x : R}
    (hx : x ∈ p) (hreg : IsSMulRegular N x) :
    moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p (QuotSMulTop x N)) =
      moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N) - 1 := by
  -- First transport the localized quotient to the canonical quotient of the localized module.
  let e := localizedModule_atPrime_quotSMulTop_equiv (R := R) (p := p) (N := N) x
  have hx_loc :
      algebraMap R (Localization.AtPrime p) x ∈ maximalIdeal (Localization.AtPrime p) := by
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p x).2 hx
  by_cases hsub : Subsingleton (LocalizedModule.AtPrime p N)
  · letI : Subsingleton (LocalizedModule.AtPrime p N) := hsub
    -- In the zero-localization case both localized depths are infinite.
    have hdepth_local :
        moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N) = ⊤ :=
      moduleDepth_eq_top_of_subsingleton
    have hdepth_quot :
        moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p (QuotSMulTop x N)) = ⊤ := by
      letI :
          Subsingleton
            (QuotSMulTop (algebraMap R (Localization.AtPrime p) x)
              (LocalizedModule.AtPrime p N)) := by
        infer_instance
      letI : Subsingleton (LocalizedModule.AtPrime p (QuotSMulTop x N)) := by
        exact e.injective.subsingleton
      exact moduleDepth_eq_top_of_subsingleton
    simpa [hdepth_local, hdepth_quot]
  · letI : Nontrivial (LocalizedModule.AtPrime p N) := not_subsingleton_iff_nontrivial.mp hsub
    have hreg_loc :
        IsSMulRegular (LocalizedModule.AtPrime p N) (algebraMap R (Localization.AtPrime p) x) :=
      localizedModule_atPrime_isSMulRegular_of_isSMulRegular
        (R := R) (p := p) (N := N) hx hreg
    calc
      moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p (QuotSMulTop x N))
          =
            moduleDepth (Localization.AtPrime p)
              (QuotSMulTop (algebraMap R (Localization.AtPrime p) x)
                (LocalizedModule.AtPrime p N)) := by
              simpa using
                moduleDepth_eq_of_linearEquiv
                  (A := Localization.AtPrime p) e
      _ =
          moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N) - 1 := by
            exact IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one
              (R := Localization.AtPrime p)
              (M := LocalizedModule.AtPrime p N)
              hreg_loc
              hx_loc

/-- Helper for Lemma 10.72.10: once the global depth is the natural number `n`, the source-faithful
induction on `n` proves the localized depth inequality at the fixed prime `p`. -/
private theorem
    moduleDepth_localizedModule_atPrime_add_ringKrullDim_quotient_ge_of_moduleDepth_eq_nat
    (n : ℕ) :
    ∀ {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N]
      [Nontrivial N] [Nontrivial (LocalizedModule.AtPrime p N)],
        moduleDepth R N = n →
          .some (moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N)) +
              ringKrullDim (R ⧸ p) ≥
            (.some n : WithBot ℕ∞) := by
  induction n with
  | zero =>
      intro N _ _ _ _ _ hdepth
      -- In depth `0`, nonnegativity of both summands gives the claim immediately.
      have hlocal_nonneg :
          (0 : WithBot ℕ∞) ≤
            (.some (moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N)) :
              WithBot ℕ∞) := by
        simp
      have hsum_nonneg :
          (0 : WithBot ℕ∞) ≤
            .some (moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N)) +
              ringKrullDim (R ⧸ p) := by
        calc
          (0 : WithBot ℕ∞) = (0 : WithBot ℕ∞) + 0 := by simp
          _ ≤
              .some (moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N)) +
                ringKrullDim (R ⧸ p) := by
                  exact add_le_add hlocal_nonneg (zero_le_ringKrullDim_quotient (R := R) (p := p))
      simpa [hdepth] using hsum_nonneg
  | succ n ih =>
      intro N _ _ _ _ _ hdepth
      by_cases hdim :
          (.some (n + 1 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p)
      · -- If the quotient dimension is already large enough, the localized depth term is extra slack.
        have hlocal_nonneg :
            (0 : WithBot ℕ∞) ≤
              (.some (moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N)) :
                WithBot ℕ∞) := by
          simp
        have hdim_le :
            ringKrullDim (R ⧸ p) ≤
              .some (moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N)) +
                ringKrullDim (R ⧸ p) := by
          simpa [zero_add, add_comm] using
            add_le_add_left hlocal_nonneg (ringKrullDim (R ⧸ p))
        exact le_trans hdim hdim_le
      · -- Route correction: keep the same prime `p` and pass from `N` to `N / xN`.
        have hlt :
            ringKrullDim (R ⧸ p) <
              (.some (moduleDepth R N) : WithBot ℕ∞) := by
          rw [hdepth]
          exact lt_of_not_ge hdim
        have hforall :
            ∀ q ∈ associatedPrimes R N, ¬ p ≤ q :=
          by
            intro q hq
            exact associated_prime_not_above_of_ringKrullDim_quotient_lt_moduleDepth
              (R := R) (p := p) hlt hq
        obtain ⟨x, hx, hreg⟩ :=
          (exists_mem_isSMulRegular_iff_forall_not_le_associatedPrimes
            (R := R) (M := N) (I := p)).2 hforall
        have hx_max : x ∈ maximalIdeal R := by
          exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance) hx
        letI : Nontrivial (QuotSMulTop x N) :=
          nontrivial_quotSMulTop_of_mem_maximalIdeal (R := R) (L := N) hx_max
        have hx_loc :
            algebraMap R (Localization.AtPrime p) x ∈ maximalIdeal (Localization.AtPrime p) := by
          exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
            (Localization.AtPrime p) p x).2 hx
        have hreg_loc :
            IsSMulRegular (LocalizedModule.AtPrime p N) (algebraMap R (Localization.AtPrime p) x) :=
          localizedModule_atPrime_isSMulRegular_of_isSMulRegular
            (R := R) (p := p) (N := N) hx hreg
        letI :
            Nontrivial
              (QuotSMulTop (algebraMap R (Localization.AtPrime p) x)
                (LocalizedModule.AtPrime p N)) :=
          nontrivial_quotSMulTop_of_mem_maximalIdeal
            (R := Localization.AtPrime p)
            (L := LocalizedModule.AtPrime p N)
            hx_loc
        let e := localizedModule_atPrime_quotSMulTop_equiv (R := R) (p := p) (N := N) x
        letI : Nontrivial (LocalizedModule.AtPrime p (QuotSMulTop x N)) := e.nontrivial
        have hdepth_quot :
            moduleDepth R (QuotSMulTop x N) = n := by
          calc
            moduleDepth R (QuotSMulTop x N) = moduleDepth R N - 1 := by
              exact IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one
                (R := R) (M := N) hreg hx_max
            _ = n := by
              rw [hdepth]
              simpa using
                (tsub_add_cancel_of_le (show (1 : ℕ∞) ≤ (n : ℕ∞) + 1 by simp))
        have hih :
            .some (moduleDepth (Localization.AtPrime p)
                (LocalizedModule.AtPrime p (QuotSMulTop x N))) +
                ringKrullDim (R ⧸ p) ≥
              (.some n : WithBot ℕ∞) :=
          ih hdepth_quot
        have hlocal_drop :
            moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p (QuotSMulTop x N)) =
              moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N) - 1 :=
          moduleDepth_localized_quotSMulTop_eq_sub_one_of_regular
            (R := R) (p := p) (N := N) hx hreg
        have hone :
            (1 : ℕ∞) ≤
              moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N) :=
          one_le_moduleDepth_of_mem_maximalIdeal_of_isSMulRegular
            (A := Localization.AtPrime p)
            (N := LocalizedModule.AtPrime p N)
            hx_loc
            hreg_loc
        have hlocal_succ :
            moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N) =
              moduleDepth (Localization.AtPrime p)
                (LocalizedModule.AtPrime p (QuotSMulTop x N)) + 1 := by
          rw [hlocal_drop]
          exact (tsub_add_cancel_of_le hone).symm
        -- Add back the one-step depth drop on the localized side.
        calc
          (.some (n + 1 : ℕ∞) : WithBot ℕ∞)
              = (.some n : WithBot ℕ∞) + 1 := by
                  simp
          _ ≤
              (.some (moduleDepth (Localization.AtPrime p)
                  (LocalizedModule.AtPrime p (QuotSMulTop x N))) +
                    ringKrullDim (R ⧸ p)) + 1 := by
                      have hih_add :
                          1 + (.some n : WithBot ℕ∞) ≤
                            1 + (.some (moduleDepth (Localization.AtPrime p)
                                (LocalizedModule.AtPrime p (QuotSMulTop x N))) +
                                  ringKrullDim (R ⧸ p)) :=
                        add_le_add_right hih 1
                      simpa [add_assoc, add_left_comm, add_comm] using hih_add
          _ =
              .some (moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N)) +
                ringKrullDim (R ⧸ p) := by
                  rw [hlocal_succ]
                  simp [add_left_comm, add_comm]

-- Proof sketch: argue by induction on the finite global depth. If `LocalizedModule.AtPrime p M`
-- is zero, its depth is `∞`, so the inequality is immediate. Otherwise the source proof keeps the
-- same prime `p`: if `depth(M) > dim(R / p)`, use Lemma `10.72.9` and prime avoidance to choose a
-- regular element `x ∈ p`, apply Lemma `10.72.7` to both `M` and `Mₚ`, and recurse on `M / xM`.
/-- Lemma 10.72.10: for a prime ideal `p` of a local Noetherian ring `R` and a finite
`R`-module `M`, the local depth `moduleDepth Rₚ Mₚ` of the localization `Mₚ` plus the Krull
dimension of `R / p` is at least the local depth `moduleDepth R M` of `M`. -/
theorem moduleDepth_localizedModule_atPrime_add_ringKrullDim_quotient_ge_moduleDepth :
    .some (moduleDepth Rₚ Mₚ) + ringKrullDim (R ⧸ p) ≥ .some (moduleDepth R M) := by
  by_cases hMp : Subsingleton Mₚ
  · letI : Subsingleton Mₚ := hMp
    -- If the localization is zero, its depth is infinite and dominates any finite global depth.
    have hdepth_local : moduleDepth Rₚ Mₚ = ⊤ :=
      moduleDepth_eq_top_of_subsingleton
    have htop_le :
        (.some (⊤ : ℕ∞) : WithBot ℕ∞) ≤
          (.some (⊤ : ℕ∞) : WithBot ℕ∞) + ringKrullDim (R ⧸ p) := by
      calc
        (.some (⊤ : ℕ∞) : WithBot ℕ∞) = (.some (⊤ : ℕ∞) : WithBot ℕ∞) + 0 := by
          simp
        _ ≤ (.some (⊤ : ℕ∞) : WithBot ℕ∞) + ringKrullDim (R ⧸ p) := by
          exact add_le_add_right (zero_le_ringKrullDim_quotient (R := R) (p := p))
            (.some (⊤ : ℕ∞) : WithBot ℕ∞)
    calc
      (.some (moduleDepth R M) : WithBot ℕ∞) ≤ (.some (⊤ : ℕ∞) : WithBot ℕ∞) := by
        simp
      _ = (.some (moduleDepth Rₚ Mₚ) : WithBot ℕ∞) := by
        rw [hdepth_local]
      _ ≤ .some (moduleDepth Rₚ Mₚ) + ringKrullDim (R ⧸ p) := by
        simpa [hdepth_local] using htop_le
  · letI : Nontrivial Mₚ := not_subsingleton_iff_nontrivial.mp hMp
    have hM_not_subsingleton : ¬ Subsingleton M := by
      intro hM
      letI : Subsingleton M := hM
      letI : Subsingleton Mₚ := by infer_instance
      exact hMp inferInstance
    letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM_not_subsingleton
    -- Once both modules are nonzero, the global depth is finite and the induction helper applies.
    have hfiniteDepth : moduleDepth R M < ⊤ := by
      simpa [moduleDepth] using
        Ideal.depth_lt_top_of_smul_top_ne_top
          (R := R) (I := maximalIdeal R) (M := M)
          (maximalIdeal_smul_top_ne_top_for_entry (A := R) (N := M))
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hfiniteDepth)
    have hdepth : moduleDepth R M = n := by
      simpa using hn.symm
    simpa [hdepth] using
      moduleDepth_localizedModule_atPrime_add_ringKrullDim_quotient_ge_of_moduleDepth_eq_nat
        (R := R) (p := p) n hdepth

end
