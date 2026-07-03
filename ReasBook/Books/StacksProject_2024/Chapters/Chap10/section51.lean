import Mathlib
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Support
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_51_1 (from Chap10) -/
universe u v

/- Domain triage: this item is in the commutative algebra of Noetherian modules.
- `source-facing`: finite presentation of finite modules, finiteness of submodules, and the
  ascending chain condition on submodules.
- `core/canonical`: the owner predicate `IsNoetherian R M`, together with mathlib's canonical
  bridges `Module.finitePresentation_of_finite`,
  `isNoetherian_of_submodule_of_noetherian`, and
  `monotone_stabilizes_iff_noetherian`.
- `bridge/view`: the source-facing finiteness statement for a submodule is the derived instance
  `Module.Finite R N`, not extra primitive data; the ACC clause is the specialized forward
  implication of `monotone_stabilizes_iff_noetherian`, not the equivalence itself.
Primitive data are just the ambient ring, module, and chosen submodule. -/

/- Lemma 10.51.1 (1): over a Noetherian ring, every finite `R`-module is finitely presented.
This is exactly the canonical theorem `Module.finitePresentation_of_finite`. -/
section FiniteOverNoetherianRing

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
variable [IsNoetherianRing R] [Module.Finite R M]

recall Module.finitePresentation_of_finite

variable (N : Submodule R M)

/- Lemma 10.51.1 (2): every submodule of a finite `R`-module is finite over a Noetherian ring.
The owner theorem is `isNoetherian_of_submodule_of_noetherian`, and the source-facing finiteness
statement is the derived instance `Module.Finite R N`. -/
recall isNoetherian_of_submodule_of_noetherian
#check (inferInstance : Module.Finite R N)

end FiniteOverNoetherianRing

section NoetherianModule

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
variable [IsNoetherian R M]

/- Lemma 10.51.1 (3): a Noetherian module satisfies the ascending chain condition on submodules.
This is the source-facing ACC consequence of the owner equivalence
`monotone_stabilizes_iff_noetherian`. -/
theorem submodule_monotone_stabilizes (f : ℕ →o Submodule R M) :
    ∃ n, ∀ m, n ≤ m → f n = f m :=
  monotone_stabilizes_iff_noetherian.mpr ‹IsNoetherian R M› f

end NoetherianModule

/-! ### Lemma_10_51_2_Artin_Rees (from Chap10) -/
universe u v

section

open scoped Pointwise

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable [IsNoetherianRing R] [Module.Finite R M]

namespace Ideal

-- Proof sketch: apply the canonical owner theorem `exists_pow_inf_eq_pow_smul`, then replace the
-- index `k` by `k + 1` so the same equality holds with a strictly positive constant.
/-- Lemma 10.51.2 (Artin-Rees): for a finite `R`-module `M` over a Noetherian ring, an ideal `I`,
and a submodule `N`, there is a positive integer `c` such that `I^n M ∩ N = I^(n - c) (I^c M ∩ N)`
for all `n ≥ c`. -/
theorem exists_pos_pow_inf_eq_pow_smul (I : Ideal R) (N : Submodule R M) :
    ∃ c > 0, ∀ n ≥ c,
      I ^ n • ⊤ ⊓ N = I ^ (n - c) • (I ^ c • ⊤ ⊓ N) := by
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul N
  have hk_succ : I ^ (k + 1) • ⊤ ⊓ N = I • (I ^ k • ⊤ ⊓ N) := by
    simpa using hk (k + 1) (Nat.le_succ k)
  refine ⟨k + 1, Nat.succ_pos _, ?_⟩
  intro n hn
  have hkn : k ≤ n := Nat.le_trans (Nat.le_succ k) hn
  calc
    I ^ n • ⊤ ⊓ N = I ^ (n - k) • (I ^ k • ⊤ ⊓ N) :=
      hk n hkn
    _ = I ^ ((n - (k + 1)) + 1) • (I ^ k • ⊤ ⊓ N) := by
      rw [show n - k = (n - (k + 1)) + 1 by omega]
    _ = I ^ (n - (k + 1)) • (I ^ (k + 1) • ⊤ ⊓ N) := by
      rw [pow_add, pow_one, ← smul_smul, ← hk_succ]

end Ideal

end

/-! ### Lemma_10_51_3 (from Chap10) -/
universe u v w

section

open scoped Pointwise

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace LinearMap

/-- A fixed Artin-Rees bound for a linear map with respect to an ideal `I`. -/
def IsArtinReesBound (f : M →ₗ[R] N) (I : Ideal R) (c : ℕ) : Prop :=
  ∀ n ≥ c,
    f.range ⊓ I ^ n • ⊤ ≤ Submodule.map f (I ^ (n - c) • ⊤)

-- Proof sketch: if `y ∈ f(M) ∩ I^n N`, choose `x` with `f x = y`. Then
-- `x ∈ f ⁻¹(I^n N)`, so the preimage equality writes `x = k + x'` with
-- `k ∈ ker f` and `x' ∈ I^(n - c) f ⁻¹(I^c N)`. Applying `f` kills `k`
-- and places `y = f x'` inside `f(I^(n - c) M)`.
/-- Any Artin-Rees equality for the preimages `f ⁻¹(I^n N)` yields an Artin-Rees bound for `f`. -/
theorem isArtinReesBound_of_preimage_pow_smul_eq
    (I : Ideal R) {f : M →ₗ[R] N} {c : ℕ}
    (hc : ∀ n ≥ c,
      Submodule.comap f (I ^ n • ⊤) =
        LinearMap.ker f ⊔ I ^ (n - c) • Submodule.comap f (I ^ c • ⊤)) :
    f.IsArtinReesBound I c := by
  intro n hn
  -- Map the source-side cutoff formula forward along `f`.
  calc
    f.range ⊓ I ^ n • (⊤ : Submodule R N) =
        Submodule.map f (Submodule.comap f (I ^ n • (⊤ : Submodule R N))) := by
      rw [Submodule.map_comap_eq]
    _ = Submodule.map f
          (LinearMap.ker f ⊔ I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N))) := by
      rw [hc n hn]
    _ = Submodule.map f
          (LinearMap.ker f) ⊔
            Submodule.map f
              (I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N))) := by
      rw [Submodule.map_sup]
    _ = Submodule.map f
          (I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N))) := by
      have hmap_ker : Submodule.map f (LinearMap.ker f) = ⊥ := by
        rw [← LinearMap.le_ker_iff_map]
      simp [hmap_ker]
    _ ≤ Submodule.map f (I ^ (n - c) • (⊤ : Submodule R M)) := by
      -- Then enlarge the cutoff submodule in the source to all of `M`.
      exact Submodule.map_mono (smul_mono_right _ le_top)

end LinearMap

namespace Ideal

/-- Helper for Lemma 10.51.3: an Artin-Rees cutoff on `f.range` pulls back to the corresponding
cutoff formula for the preimages of the powers of `I`. -/
lemma comap_pow_smul_eq_of_range_cutoff
    (I : Ideal R) {f : M →ₗ[R] N} {c n : ℕ}
    (hcut :
      I ^ n • (⊤ : Submodule R N) ⊓ f.range =
        I ^ (n - c) • (I ^ c • (⊤ : Submodule R N) ⊓ f.range)) :
    Submodule.comap f (I ^ n • (⊤ : Submodule R N)) =
      LinearMap.ker f ⊔ I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N)) := by
  -- Rewrite the preimage as the pullback of its image in the range of `f`.
  calc
    Submodule.comap f (I ^ n • (⊤ : Submodule R N)) =
        Submodule.comap f
          (Submodule.map f (Submodule.comap f (I ^ n • (⊤ : Submodule R N)))) := by
      rw [Submodule.comap_map_eq_self (LinearMap.ker_le_comap f)]
    _ = Submodule.comap f (I ^ n • (⊤ : Submodule R N) ⊓ f.range) := by
      rw [Submodule.map_comap_eq, inf_comm]
    _ = Submodule.comap f (I ^ (n - c) • (I ^ c • (⊤ : Submodule R N) ⊓ f.range)) := by
      rw [hcut]
    _ = Submodule.comap f
          (I ^ (n - c) •
            Submodule.map f (Submodule.comap f (I ^ c • (⊤ : Submodule R N)))) := by
      rw [Submodule.map_comap_eq, inf_comm]
    _ = Submodule.comap f
          (Submodule.map f
            (I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N)))) := by
      rw [← Submodule.map_smul'']
    _ = LinearMap.ker f ⊔ I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N)) := by
      simpa [sup_comm] using
        (Submodule.comap_map_eq f
          (I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N))))

-- Proof sketch: apply Lemma 10.51.2 to `f.range ≤ N`; this gives the inclusion
-- `f.range ⊓ I^n N ≤ I^(n - c) • f.range`. Pulling the powers of `I` back
-- along `f` gives the corresponding equality for `f ⁻¹(I^n N)`, and `Submodule.map_smul''`
-- identifies `I^(n - c) • f.range` with `f(I^(n - c) M)`.
/-- A linear map into a finite module over a Noetherian ring has an Artin-Rees constant for the
inverse images of the powers of `I`. -/
theorem exists_exact_preimage_pow_smul_eq [IsNoetherianRing R] [Module.Finite R N]
    (I : Ideal R) (f : M →ₗ[R] N) :
    ∃ c : ℕ, ∀ n ≥ c,
      Submodule.comap f (I ^ n • ⊤) =
        LinearMap.ker f ⊔ I ^ (n - c) • Submodule.comap f (I ^ c • ⊤) := by
  obtain ⟨c, _hc_pos, hc⟩ := I.exists_pos_pow_inf_eq_pow_smul f.range
  refine ⟨c, ?_⟩
  intro n hn
  -- Apply Artin-Rees to the image submodule and pull the cutoff back along `f`.
  exact comap_pow_smul_eq_of_range_cutoff (I := I) (f := f) (c := c) (n := n) <| by
    simpa [inf_comm] using hc n hn

-- Proof sketch: specialize the owner theorem above to the exact sequence
-- `0 → K → M → N`, then rewrite `LinearMap.ker f` as `K` using exactness.
/-- Lemma 10.51.3: if `0 → K → M → N` is an exact sequence of finite modules over a Noetherian
ring and `I` is an ideal of `R`, then there is a single Artin-Rees constant controlling both the
preimages `f ⁻¹(I^n N)` and the intersections `f(M) ∩ I^n N`. -/
theorem exists_artin_rees_constant_of_exact [IsNoetherianRing R] [Module.Finite R N]
    (I : Ideal R) {K : Submodule R M} {f : M →ₗ[R] N}
    (h_exact : Function.Exact K.subtype f) :
    ∃ c : ℕ,
      (∀ n ≥ c,
        Submodule.comap f (I ^ n • ⊤) = K ⊔ I ^ (n - c) • Submodule.comap f (I ^ c • ⊤)) ∧
        f.IsArtinReesBound I c := by
  obtain ⟨c, hc⟩ := exists_exact_preimage_pow_smul_eq (I := I) (f := f)
  refine ⟨c, ?_⟩
  refine ⟨?_, LinearMap.isArtinReesBound_of_preimage_pow_smul_eq (I := I) (f := f) hc⟩
  intro n hn
  -- Exactness identifies the kernel term with the given submodule `K`.
  simpa [h_exact.linearMap_ker_eq, Submodule.range_subtype] using hc n hn

end Ideal

end

/-! ### Lemma_10_51_4_Krull_s_intersection_theorem (from Chap10) -/
universe u v

section

variable {R : Type u} {M : Type v}
variable [CommRing R] [AddCommGroup M] [Module R M]
variable [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]

/- Lemma 10.51.4 (Krull's intersection theorem): let `R` be a Noetherian local ring, let `I` be
a proper ideal of `R`, and let `M` be a finite `R`-module. Then
`⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) = ⊥`. This is the canonical mathlib theorem
`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`. -/
recall Ideal.iInf_pow_smul_eq_bot_of_isLocalRing

end

/-! ### Lemma_10_51_5 (from Chap10) -/
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

/-! ### Remark_10_51_6 (from Chap10) -/
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

/-! ### Lemma_10_51_7_Artin_Tate (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [Algebra.FiniteType R S]

/-
Lemma 10.51.7 (Artin-Tate) is a `bridge/view` item in the finite-type / finite-module algebra-tower
domain. The owner abstraction is `fg_of_fg_of_fg`, and the textbook finite-type formulation for an
intermediate `R`-subalgebra is the derived bridge below via `Subalgebra.fg_iff_finiteType`.
-/
recall fg_of_fg_of_fg

/-- Lemma 10.51.7 (Artin-Tate): if `T` is an `R`-subalgebra of a finite type `R`-algebra `S` and
`S` is finite as a `T`-module, then `T` is finite type over the Noetherian ring `R`. -/
theorem Subalgebra.finiteType_of_finite (T : Subalgebra R S) [Module.Finite T S] :
    Algebra.FiniteType R T := by
  exact (Subalgebra.fg_iff_finiteType T).mp <|
    (T.fg_top).mp <|
      fg_of_fg_of_fg R T S Algebra.FiniteType.out Module.Finite.fg_top Subtype.val_injective

end
