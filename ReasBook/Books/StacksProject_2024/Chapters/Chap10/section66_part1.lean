import Mathlib
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_66_1 (from Chap10) -/
universe u v

section

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

namespace Ideal

/-
Domain triage: this file is in commutative algebra of weakly associated primes of modules.

* `source-facing`: `Ideal.IsWeaklyAssociatedToModule R M 𝔭`, which matches the textbook condition
  that `𝔭` is minimal over the annihilator of some element of `M`.
* `core/canonical` owner in this chapter: the set-valued declaration `weaklyAssociatedPrimes R M`,
  parallel to mathlib's `associatedPrimes`.
* `bridge/view`: `mem_weaklyAssociatedPrimes_iff`, turning the owner set back into the pointwise
  predicate.

Primitive data are only the witness `m : M` and the canonical annihilator ideal
`Ideal.torsionOf R M m`; primality is derived from membership in `minimalPrimes`.
-/
/-- Definition 10.66.1: a prime ideal `𝔭` of `R` is weakly associated to the `R`-module `M`
if `𝔭` is minimal among the prime ideals containing the annihilator of some element of `M`. -/
def IsWeaklyAssociatedToModule (𝔭 : Ideal R) : Prop :=
  ∃ m : M, 𝔭 ∈ (Ideal.torsionOf R M m).minimalPrimes

/-- A weakly associated ideal of `M` is prime. -/
theorem IsWeaklyAssociatedToModule.isPrime {𝔭 : Ideal R}
    (h𝔭 : IsWeaklyAssociatedToModule R M 𝔭) : 𝔭.IsPrime := by
  rcases h𝔭 with ⟨m, hm⟩
  exact Ideal.minimalPrimes_isPrime hm

end Ideal

/-- The set `WeakAss_R(M)` of weakly associated primes of the `R`-module `M`. -/
def weaklyAssociatedPrimes : Set (Ideal R) :=
  Ideal.IsWeaklyAssociatedToModule R M

@[simp] theorem mem_weaklyAssociatedPrimes_iff (𝔭 : Ideal R) :
    𝔭 ∈ weaklyAssociatedPrimes R M ↔ Ideal.IsWeaklyAssociatedToModule R M 𝔭 :=
  Iff.rfl

instance (𝔭 : weaklyAssociatedPrimes R M) : 𝔭.1.IsPrime :=
  𝔭.2.isPrime

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace Ideal

private theorem torsionOf_linearEquiv_eq
    {A : Type*} {N : Type*} {N' : Type*} [CommRing A]
    [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    (e : N ≃ₗ[A] N') (x : N) :
    Ideal.torsionOf A N' (e x) = Ideal.torsionOf A N x := by
  ext a
  rw [Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  constructor
  · intro ha
    apply e.injective
    simpa using ha
  · intro ha
    simpa using congrArg e ha

end Ideal

namespace LinearEquiv

/-- Weakly associated primes are preserved by an `R`-linear equivalence of `R`-modules. -/
theorem weaklyAssociatedPrimes_eq
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    {N' : Type*} [AddCommGroup N'] [Module A N']
    (e : N ≃ₗ[A] N') :
    weaklyAssociatedPrimes A N = weaklyAssociatedPrimes A N' := by
  ext p
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨e x, ?_⟩
    simpa [Ideal.torsionOf_linearEquiv_eq e x] using hx
  · rintro ⟨x, hx⟩
    refine ⟨e.symm x, ?_⟩
    simpa [Ideal.torsionOf_linearEquiv_eq e.symm x] using hx

end LinearEquiv

namespace weaklyAssociatedPrimes

theorem eq_empty_of_subsingleton [Subsingleton M] : weaklyAssociatedPrimes R M = ∅ := by
  ext 𝔭
  constructor
  · rintro ⟨m, hm⟩
    have htop : Ideal.torsionOf R M m = ⊤ := by
      simp [Subsingleton.elim m 0]
    simp [htop, Ideal.minimalPrimes_top] at hm
  · simp

theorem nonempty [Nontrivial M] : (weaklyAssociatedPrimes R M).Nonempty := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have hne_top : Ideal.torsionOf R M m ≠ ⊤ := by
    intro htop
    exact hm ((Ideal.torsionOf_eq_top_iff R m).mp htop)
  obtain ⟨𝔭, h𝔭⟩ := Ideal.nonempty_minimalPrimes hne_top
  exact ⟨𝔭, ⟨m, h𝔭⟩⟩

end weaklyAssociatedPrimes

end

end

/-! ### Lemma_10_66_2 (from Chap10) -/
open IsLocalRing Submodule
open scoped TensorProduct

universe u v

section

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable (𝔭 : Ideal R) [𝔭.IsPrime]

local notation "Rₚ" => Localization.AtPrime 𝔭
local notation "Mₚ" => LocalizedModule.AtPrime 𝔭 M

/- Domain triage: this file is `source-facing` for weakly associated primes under localization.
The owner abstraction is mathlib's `IsAssociatedPrime`, and the project predicate
`Ideal.IsWeaklyAssociatedToModule` is the source-facing view. Primitive data: none. Derived API:
the three public equivalences in Lemma `10.66.2`. The local annihilator-radical reformulation is
kept internal and derived directly from the owner definition. -/

private theorem torsionOf_eq_bot_colon_singleton
    {A : Type*} {N : Type*} [CommRing A] [AddCommGroup N] [Module A N] (x : N) :
    Ideal.torsionOf A N x = colon (⊥ : Submodule A N) ({x} : Set N) := by
  calc
    Ideal.torsionOf A N x = (Submodule.span A ({x} : Set N)).annihilator := by
      simpa [Ideal.torsionOf] using (Submodule.annihilator_span_singleton x).symm
    _ = colon (⊥ : Submodule A N) ({x} : Set N) := by
      rw [Submodule.bot_colon']

private theorem torsionOf_linearEquiv_eq
    {A : Type*} {N : Type*} {N' : Type*} [CommRing A]
    [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    (e : N ≃ₗ[A] N') (x : N) :
    Ideal.torsionOf A N' (e x) = Ideal.torsionOf A N x := by
  ext a
  rw [Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  constructor
  · intro ha
    apply e.injective
    simpa using ha
  · intro ha
    simpa using congrArg e ha

private theorem torsionOf_smul_eq
    {A : Type*} {N : Type*} [CommRing A] [AddCommGroup N] [Module A N]
    {u : A} (hu : IsUnit u) (x : N) :
    Ideal.torsionOf A N (u • x) = Ideal.torsionOf A N x := by
  ext a
  rw [Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
    (hu.smul_eq_zero : u • (a • x) = 0 ↔ a • x = 0)

private theorem map_torsionOf_atPrime_eq_torsionOf (m : M) :
    Ideal.map (algebraMap R Rₚ) (Ideal.torsionOf R M m) =
      Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m (1 : 𝔭.primeCompl)) := by
  calc
    Ideal.map (algebraMap R Rₚ) (Ideal.torsionOf R M m) =
        Ideal.torsionOf Rₚ (Rₚ ⊗[R] M) ((1 : Rₚ) ⊗ₜ[R] m) := by
          simpa using Ideal.map_torsionOf_eq_torsionOf_baseChange_of_flat m
    _ =
        Ideal.torsionOf Rₚ Mₚ
          (((LocalizedModule.equivTensorProduct 𝔭.primeCompl M).symm)
            ((1 : Rₚ) ⊗ₜ[R] m)) := by
          simpa using
            torsionOf_linearEquiv_eq
              ((LocalizedModule.equivTensorProduct 𝔭.primeCompl M).symm)
              ((1 : Rₚ) ⊗ₜ[R] m) |>.symm
    _ = Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m (1 : 𝔭.primeCompl)) := by
          simp

private theorem weaklyAssociatedToModule_maximalIdeal_atPrime_iff_isAssociatedPrime :
    Ideal.IsWeaklyAssociatedToModule Rₚ Mₚ (maximalIdeal Rₚ) ↔
      IsAssociatedPrime (maximalIdeal Rₚ) Mₚ := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨show (maximalIdeal Rₚ).IsPrime by infer_instance, x, ?_⟩
    have hminimal :
        (Ideal.torsionOf Rₚ Mₚ x).minimalPrimes = {maximalIdeal Rₚ} := by
      ext q
      constructor
      · intro hq
        have hq_le : q ≤ maximalIdeal Rₚ := IsLocalRing.le_maximalIdeal hq.1.1.ne_top
        exact Set.mem_singleton_iff.mpr <| le_antisymm hq_le (hx.2 hq.1 hq_le)
      · rintro rfl
        exact hx
    have hrad :
        (Ideal.torsionOf Rₚ Mₚ x).radical = maximalIdeal Rₚ := by
      rw [← Ideal.sInf_minimalPrimes, hminimal, sInf_singleton]
    calc
      maximalIdeal Rₚ = (Ideal.torsionOf Rₚ Mₚ x).radical := hrad.symm
      _ = (colon (⊥ : Submodule Rₚ Mₚ) ({x} : Set Mₚ)).radical := by
        rw [torsionOf_eq_bot_colon_singleton]
  · intro h
    exact h.isWeaklyAssociatedToModule

private theorem weaklyAssociatedToModule_iff_isAssociatedPrime_maximalIdeal_atPrime :
    Ideal.IsWeaklyAssociatedToModule R M 𝔭 ↔
      IsAssociatedPrime (maximalIdeal Rₚ) Mₚ := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨show (maximalIdeal Rₚ).IsPrime by infer_instance,
      LocalizedModule.mk m (1 : 𝔭.primeCompl), ?_⟩
    have hrad :
        (Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m (1 : 𝔭.primeCompl))).radical =
          maximalIdeal Rₚ := by
      rw [← map_torsionOf_atPrime_eq_torsionOf]
      simpa [Localization.AtPrime.map_eq_maximalIdeal] using
        IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes Rₚ 𝔭
          (Ideal.torsionOf R M m) hm
    calc
      maximalIdeal Rₚ =
          (Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m (1 : 𝔭.primeCompl))).radical :=
        hrad.symm
      _ = (colon (⊥ : Submodule Rₚ Mₚ)
            ({LocalizedModule.mk m (1 : 𝔭.primeCompl)} : Set Mₚ)).radical := by
          rw [torsionOf_eq_bot_colon_singleton]
  · intro h
    rcases h.2 with ⟨x, hx⟩
    obtain ⟨⟨m, s⟩, rfl⟩ :=
      IsLocalizedModule.mk'_surjective 𝔭.primeCompl
        (LocalizedModule.mkLinearMap 𝔭.primeCompl M) x
    have hunit : IsUnit (Localization.mk (1 : R) s : Rₚ) := by
      simpa [Localization.mk_eq_mk'] using
        (show IsUnit (IsLocalization.mk' Rₚ (1 : R) s) from isUnit_of_invertible _)
    have htorsion :
        Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m s) =
          Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m (1 : 𝔭.primeCompl)) := by
      calc
        Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m s) =
            Ideal.torsionOf Rₚ Mₚ
              ((Localization.mk (1 : R) s : Rₚ) •
                LocalizedModule.mk m (1 : 𝔭.primeCompl)) := by
                  congr 1
                  simpa using
                    (LocalizedModule.mk_smul_mk (1 : R) m s (1 : 𝔭.primeCompl)).symm
        _ = Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m (1 : 𝔭.primeCompl)) :=
          torsionOf_smul_eq hunit (LocalizedModule.mk m (1 : 𝔭.primeCompl))
    have hx' :
        maximalIdeal Rₚ =
          (Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m s)).radical := by
      calc
        maximalIdeal Rₚ =
            (colon (⊥ : Submodule Rₚ Mₚ)
              ({Function.uncurry
                  (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap 𝔭.primeCompl M))
                  (m, s)} : Set Mₚ)).radical := hx
        _ = (colon (⊥ : Submodule Rₚ Mₚ) ({LocalizedModule.mk m s} : Set Mₚ)).radical := by
              simp [IsLocalizedModule.mk_eq_mk']
        _ = (Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m s)).radical := by
              rw [← torsionOf_eq_bot_colon_singleton]
    have hlocal :
        maximalIdeal Rₚ ∈
          (Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m (1 : 𝔭.primeCompl))).minimalPrimes := by
      haveI :
          (Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m s)).radical.IsPrime := by
        simpa [hx'] using (show (maximalIdeal Rₚ).IsPrime by infer_instance)
      rw [← htorsion, hx', ← Ideal.radical_minimalPrimes, Ideal.minimalPrimes_eq_subsingleton_self]
      simp
    have hmap :
        maximalIdeal Rₚ ∈
          (Ideal.map (algebraMap R Rₚ) (Ideal.torsionOf R M m)).minimalPrimes := by
      simpa [map_torsionOf_atPrime_eq_torsionOf] using hlocal
    rw [IsLocalization.minimalPrimes_map 𝔭.primeCompl Rₚ (Ideal.torsionOf R M m)] at hmap
    exact ⟨m, by simpa [Localization.AtPrime.comap_maximalIdeal] using hmap⟩

/-- Lemma 10.66.2, clauses `(1) ↔ (2)`: weak association descends and ascends along localization at
`𝔭`. -/
theorem isWeaklyAssociatedToModule_iff_isWeaklyAssociatedToModule_maximalIdeal_atPrime :
    Ideal.IsWeaklyAssociatedToModule R M 𝔭 ↔
      Ideal.IsWeaklyAssociatedToModule Rₚ Mₚ (maximalIdeal Rₚ) := by
  exact
    (weaklyAssociatedToModule_iff_isAssociatedPrime_maximalIdeal_atPrime 𝔭).trans
      (weaklyAssociatedToModule_maximalIdeal_atPrime_iff_isAssociatedPrime 𝔭).symm

/-- Lemma 10.66.2, clauses `(1) ↔ (3)`: a prime `𝔭` is weakly associated to `M` exactly when the
maximal ideal of `R_𝔭` is an associated prime of `M_𝔭`. -/
theorem isWeaklyAssociatedToModule_iff_isAssociatedPrime_maximalIdeal_atPrime :
    Ideal.IsWeaklyAssociatedToModule R M 𝔭 ↔
      IsAssociatedPrime (maximalIdeal Rₚ) Mₚ := by
  exact weaklyAssociatedToModule_iff_isAssociatedPrime_maximalIdeal_atPrime 𝔭

/-- Lemma 10.66.2, clauses `(2) ↔ (3)`: over the local ring `R_𝔭`, weak association of the
maximal ideal is equivalent to the canonical predicate `IsAssociatedPrime`. -/
theorem isWeaklyAssociatedToModule_maximalIdeal_atPrime_iff_isAssociatedPrime :
    Ideal.IsWeaklyAssociatedToModule Rₚ Mₚ (maximalIdeal Rₚ) ↔
      IsAssociatedPrime (maximalIdeal Rₚ) Mₚ := by
  exact weaklyAssociatedToModule_maximalIdeal_atPrime_iff_isAssociatedPrime 𝔭

end

/-! ### Lemma_10_66_3 (from Chap10) -/
universe u v

section

variable {R : Type u} [CommRing R] [IsReduced R]

/- Domain triage:
* `source-facing`: the textbook statement is the set equality
  `weaklyAssociatedPrimes R R = minimalPrimes R`.
* `core/canonical`: the chapter owner abstraction is the set-valued declaration
  `weaklyAssociatedPrimes R R`.
* `bridge/view`: membership in that owner set is the pointwise predicate
  `Ideal.IsWeaklyAssociatedToModule R R p` via `mem_weaklyAssociatedPrimes_iff`.

Primitive data are only the witness `x : R` in the definition of weak association. The pointwise
equivalence below is kept private and used only to recover the source-facing set equality. -/

private theorem isWeaklyAssociatedToModule_ring_iff_mem_minimalPrimes (p : Ideal R) :
    Ideal.IsWeaklyAssociatedToModule R R p ↔ p ∈ minimalPrimes R := by
  constructor
  · rintro ⟨x, hx⟩
    have hx_not_mem : x ∉ p := by
      intro hxp
      obtain ⟨y, hy, hxy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hx hxp
      have hkill : (x * y) * x = 0 := by
        rw [Ideal.mem_torsionOf_iff] at hxy
        simpa [mul_comm, mul_left_comm, mul_assoc] using hxy
      have hxy_sq : (x * y) ^ 2 = 0 := by
        calc
          (x * y) ^ 2 = ((x * y) * x) * y := by ring
          _ = 0 := by simp [hkill]
      have hxy_zero : x * y = 0 := by
        exact isNilpotent_iff_eq_zero.mp ⟨2, hxy_sq⟩
      exact hy <| by
        rw [Ideal.mem_torsionOf_iff]
        simpa [mul_comm] using hxy_zero
    change p ∈ (⊥ : Ideal R).minimalPrimes
    refine ⟨⟨hx.1.1, bot_le⟩, ?_⟩
    intro q hq hqp
    have hx_not_mem_q : x ∉ q := fun hxq ↦ hx_not_mem (hqp hxq)
    have htorsion_le : Ideal.torsionOf R R x ≤ q := by
      intro a ha
      rw [Ideal.mem_torsionOf_iff] at ha
      have hax : a * x = 0 := by
        simpa using ha
      exact (hq.1.mem_or_mem <| hax ▸ q.zero_mem).resolve_right hx_not_mem_q
    exact hx.2 ⟨hq.1, htorsion_le⟩ hqp
  · intro hp
    letI : p.IsPrime := Ideal.minimalPrimes_isPrime hp
    letI : Ring.KrullDimLE 0 (Localization.AtPrime p) :=
      Ring.KrullDimLE.of_isLocalization p hp (Localization.AtPrime p)
    let hField : IsField (Localization.AtPrime p) :=
      Ring.KrullDimLE.isField_of_isReduced
    letI : Field (Localization.AtPrime p) := hField.toField
    have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime p) = ⊥ := by
      exact IsLocalRing.isField_iff_maximalIdeal_eq.mp hField
    have hlocal :
        Ideal.IsWeaklyAssociatedToModule
          (Localization.AtPrime p) (Localization.AtPrime p)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p)) := by
      rw [hmax]
      refine ⟨1, ?_⟩
      have htorsion :
          Ideal.torsionOf (Localization.AtPrime p) (Localization.AtPrime p)
            (1 : Localization.AtPrime p) = ⊥ := by
        ext a
        rw [Ideal.mem_torsionOf_iff, Ideal.mem_bot]
        simp
      simpa [htorsion] using
        (show (⊥ : Ideal (Localization.AtPrime p)) ∈ (⊥ : Ideal (Localization.AtPrime p)).minimalPrimes by
          haveI : (⊥ : Ideal (Localization.AtPrime p)).IsPrime := Ideal.isPrime_bot
          rw [Ideal.minimalPrimes_eq_subsingleton_self]
          simp)
    exact
      (isWeaklyAssociatedToModule_iff_isWeaklyAssociatedToModule_maximalIdeal_atPrime p).mpr hlocal

/-- Lemma 10.66.3: for a reduced ring `R`, the weakly associated primes of `R` as an `R`-module
are exactly the minimal prime ideals of `R`. -/
-- Proof sketch: if `p` is weakly associated via `x`, then `p` is minimal over `ann(x)`. In a
-- reduced ring this forces `x ∉ p`: otherwise minimal-prime avoidance produces `y ∉ ann(x)` with
-- `xy ∈ ann(x)`, but then `(xy)^2 = 0`, hence `xy = 0`, contradiction. Once `x ∉ p`, any prime
-- ideal `q ≤ p` also contains `ann(x)`, so minimality over `ann(x)` gives `p ≤ q`, proving that
-- `p` is a minimal prime of `R`. Conversely, if `p` is minimal, then the localization `R_p` has
-- Krull dimension `0`; since reducedness localizes, `R_p` is a field, so its maximal ideal is
-- `(0)`, which is weakly associated to `R_p` via `1`. Lemma `10.66.2` then descends weak
-- association back to `R`.
theorem weaklyAssociatedPrimes_ring_eq_minimalPrimes :
    weaklyAssociatedPrimes R R = minimalPrimes R := by
  ext p
  simpa [mem_weaklyAssociatedPrimes_iff] using
    (isWeaklyAssociatedToModule_ring_iff_mem_minimalPrimes p :
      Ideal.IsWeaklyAssociatedToModule R R p ↔ p ∈ minimalPrimes R)

end

/-! ### Lemma_10_66_4 (from Chap10) -/
universe u v w x

section

variable {R : Type u} [CommRing R]
variable {M' : Type v} [AddCommGroup M'] [Module R M']
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {M'' : Type x} [AddCommGroup M''] [Module R M'']
variable {f : M' →ₗ[R] M} {g : M →ₗ[R] M''}

/-
Domain triage:
- primary domain: commutative algebra of weakly associated primes under injective maps and exact
  sequences;
- sampled owner-style declarations of the same kind:
  `associatedPrimes.subset_of_injective`,
  `associatedPrimes.subset_union_of_exact`,
  `associatedPrimesOfModule.subset_of_injective`,
  `associatedPrimesOfModule.subset_union_of_exact`;
- owner abstraction: the chapter declaration `weaklyAssociatedPrimes R M`, parallel to mathlib's
  owner set `associatedPrimes`;
- primitive data: modules and linear maps in an injective map or exact sequence;
- derived API: inclusions between the owner sets attached to those modules.

This file therefore belongs at the `core/canonical` layer, with no additional source-facing
wrapper or packaging declaration.
-/
namespace weaklyAssociatedPrimes

namespace Ideal

/-- Helper for Lemma 10.66.4: an injective linear map preserves the torsion ideal of a chosen
element. -/
lemma torsionOf_map_eq_of_injective (hf : Function.Injective f) (m : M') :
    Ideal.torsionOf R M (f m) = Ideal.torsionOf R M' m := by
  -- Compare membership in the two torsion ideals pointwise via injectivity of `f`.
  ext a
  rw [Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  constructor
  · intro ha
    apply hf
    simpa using ha
  · intro ha
    simpa using congrArg f ha

end Ideal

/-- Helper for Lemma 10.66.4: an associated-prime witness at the maximal ideal of the localization
at `p` descends to a weakly associated prime over the original ring. -/
lemma localized_maximalIdeal_weakAss_of_associated
    (p : Ideal R) [p.IsPrime] {X : Type*} [AddCommGroup X] [Module R X]
    (hp :
      IsAssociatedPrime (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (LocalizedModule.AtPrime p X)) :
    p ∈ weaklyAssociatedPrimes R X := by
  -- Lemma `10.66.2` identifies weak association at `p` with association of the maximal ideal
  -- after localizing at `p`.
  rw [mem_weaklyAssociatedPrimes_iff]
  exact
    (isWeaklyAssociatedToModule_iff_isAssociatedPrime_maximalIdeal_atPrime
      (R := R) (M := X) p).2 hp

/-- Canonical owner-form of Lemma 10.66.4 (1): an injective linear map sends weakly associated
primes into weakly associated primes. -/
theorem subset_of_injective (hf : Function.Injective f) :
    weaklyAssociatedPrimes R M' ⊆ weaklyAssociatedPrimes R M := by
  intro p hp
  rw [mem_weaklyAssociatedPrimes_iff] at hp ⊢
  rcases hp with ⟨m, hm⟩
  -- Preserve the witness element and rewrite its torsion ideal through the injective map.
  refine ⟨f m, ?_⟩
  simpa [Ideal.torsionOf_map_eq_of_injective (R := R) (f := f) hf m] using hm

-- Proof sketch: if `𝔭` is weakly associated to `M'`, localize at `𝔭` and use the exact sequence
-- `0 → M'_𝔭 → M_𝔭 → M''_𝔭`. An element of `M_𝔭` whose annihilator has radical `𝔭R_𝔭` either comes
-- from `M'_𝔭` or has nonzero image in `M''_𝔭`, yielding weak association to `M'_𝔭` or `M''_𝔭`.
/-- Canonical owner-form of Lemma 10.66.4 (2): if `0 → M' → M → M''` is exact, then every weakly
associated prime of `M` is weakly associated to `M'` or to `M''`. -/
theorem subset_union_of_exact (hf : Function.Injective f) (hfg : Function.Exact f g) :
    weaklyAssociatedPrimes R M ⊆ weaklyAssociatedPrimes R M' ∪ weaklyAssociatedPrimes R M'' :=
  by
    intro p hp
    rw [mem_weaklyAssociatedPrimes_iff] at hp
    have hp_prime : p.IsPrime := hp.isPrime
    letI : p.IsPrime := hp_prime
    -- Localize at the weakly associated prime `p` and convert to an associated-prime statement.
    have hp_assoc :
        IsLocalRing.maximalIdeal (Localization.AtPrime p) ∈
          associatedPrimes (Localization.AtPrime p) (LocalizedModule.AtPrime p M) := by
      rw [AssociatedPrimes.mem_iff]
      exact
        (isWeaklyAssociatedToModule_iff_isAssociatedPrime_maximalIdeal_atPrime
          (R := R) (M := M) p).1 hp
    have hf_loc : Function.Injective (LocalizedModule.map p.primeCompl f) :=
      LocalizedModule.map_injective p.primeCompl f hf
    have hfg_loc :
        Function.Exact (LocalizedModule.map p.primeCompl f) (LocalizedModule.map p.primeCompl g) :=
      LocalizedModule.map_exact p.primeCompl f g hfg
    -- Exactness survives localization, so the associated-prime union theorem applies upstairs.
    have hp_union :
        IsLocalRing.maximalIdeal (Localization.AtPrime p) ∈
          associatedPrimes (Localization.AtPrime p) (LocalizedModule.AtPrime p M') ∪
            associatedPrimes (Localization.AtPrime p) (LocalizedModule.AtPrime p M'') :=
      associatedPrimes.subset_union_of_exact
        (R := Localization.AtPrime p)
        (M := LocalizedModule.AtPrime p M')
        (M' := LocalizedModule.AtPrime p M)
        (M'' := LocalizedModule.AtPrime p M'')
        (f := LocalizedModule.map p.primeCompl f)
        (g := LocalizedModule.map p.primeCompl g)
        hf_loc hfg_loc hp_assoc
    rw [Set.mem_union]
    rcases hp_union with hp_left | hp_right
    · -- Descend the localized associated-prime conclusion back to a weakly associated prime of `M'`.
      left
      exact localized_maximalIdeal_weakAss_of_associated
        (R := R) (X := M') p (AssociatedPrimes.mem_iff.mp hp_left)
    · -- The same descent works for the quotient module `M''`.
      right
      exact localized_maximalIdeal_weakAss_of_associated
        (R := R) (X := M'') p (AssociatedPrimes.mem_iff.mp hp_right)

end weaklyAssociatedPrimes

/- Lemma 10.66.4 (1): the source states this for a short exact sequence
`0 → M' → M → M'' → 0`; the owner theorem is the more general
`weaklyAssociatedPrimes.subset_of_injective`. -/
recall weaklyAssociatedPrimes.subset_of_injective

/- Lemma 10.66.4 (2): the source states this for a short exact sequence
`0 → M' → M → M'' → 0`; the owner theorem is the more general
`weaklyAssociatedPrimes.subset_union_of_exact`. -/
recall weaklyAssociatedPrimes.subset_union_of_exact

end

/-! ### Lemma_10_66_5 (from Chap10) -/
universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage: this item lies in commutative algebra of weakly associated primes of modules.
The owner abstraction is the project declaration `weaklyAssociatedPrimes R M` from
`Definition_10_66_1`, modeled on mathlib's `associatedPrimes`. The owner-level API
`weaklyAssociatedPrimes.eq_empty_of_subsingleton` and `weaklyAssociatedPrimes.nonempty` now lives
with that owner declaration, and the theorem below is the source-facing bridge identifying
vanishing of the owner set with triviality of the module. -/

/-- Lemma 10.66.5: an `R`-module `M` is the zero module if and only if its set of weakly
associated primes is empty. -/
-- Proof sketch: if `M` is subsingleton, every element is zero, so there is no annihilator of a
-- nonzero element from which a weakly associated prime could arise. Conversely, if `M` is not
-- subsingleton, choose a nonzero element `m : M`; then `R / ann(m)` embeds into `M`, so Lemma
-- 10.66.4 reduces the claim to finding a minimal prime over `ann(m)`, which exists because
-- `ann(m) ≠ ⊤` and hence `Spec (R / ann(m))` is nonempty by Lemmas 10.17.2 and 10.17.7.
theorem subsingleton_iff_weaklyAssociatedPrimes_eq_empty :
    Subsingleton M ↔ weaklyAssociatedPrimes R M = ∅ := by
  constructor
  · intro h
    letI := h
    simpa using
      (weaklyAssociatedPrimes.eq_empty_of_subsingleton : weaklyAssociatedPrimes R M = ∅)
  · intro h
    by_contra hM
    letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    exact (weaklyAssociatedPrimes.nonempty : (weaklyAssociatedPrimes R M).Nonempty).ne_empty h

end

/-! ### Lemma_10_66_6 (from Chap10) -/
universe u v

section

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

theorem IsAssociatedPrime.isWeaklyAssociatedToModule {𝔭 : Ideal R}
    (h𝔭 : IsAssociatedPrime 𝔭 M) :
    Ideal.IsWeaklyAssociatedToModule R M 𝔭 := by
  rcases h𝔭.eq_radical_colon with ⟨m, hm⟩
  have htorsion : Ideal.torsionOf R M m = (⊥ : Submodule R M).colon ({m} : Set M) := by
    calc
      Ideal.torsionOf R M m = (Submodule.span R ({m} : Set M)).annihilator := by
        simpa [Ideal.torsionOf] using (Submodule.annihilator_span_singleton m).symm
      _ = (⊥ : Submodule R M).colon ({m} : Set M) := by
        rw [Submodule.bot_colon']
  have hp : (Ideal.torsionOf R M m).radical.IsPrime := by
    simpa [htorsion, hm] using h𝔭.isPrime
  letI := hp
  refine ⟨m, ?_⟩
  rw [← Ideal.radical_minimalPrimes, Ideal.minimalPrimes_eq_subsingleton_self]
  simp [htorsion, hm]

namespace Ideal

/-- Source-facing pointwise form of the first inclusion in Lemma 10.66.6. -/
theorem IsAssociatedToModule.isWeaklyAssociatedToModule {𝔭 : Ideal R}
    (h𝔭 : IsAssociatedToModule R M 𝔭) :
    IsWeaklyAssociatedToModule R M 𝔭 := by
  exact h𝔭.isAssociatedPrime.isWeaklyAssociatedToModule

end Ideal

namespace Ideal

/-- Canonical pointwise form of the second inclusion in Lemma 10.66.6. -/
theorem IsWeaklyAssociatedToModule.mem_support {𝔭 : Ideal R}
    (h𝔭 : Ideal.IsWeaklyAssociatedToModule R M 𝔭) :
    (⟨𝔭, h𝔭.isPrime⟩ : PrimeSpectrum R) ∈ Module.support R M := by
  rcases h𝔭 with ⟨m, hm⟩
  rw [Module.mem_support_iff_exists_annihilator]
  exact ⟨m, by simpa [Ideal.torsionOf, Submodule.annihilator_span_singleton] using hm.1.2⟩

end Ideal

namespace associatedPrimesOfModule

/-- Lemma 10.66.6 (1): every textbook-associated prime of `M` is weakly associated to `M`. -/
theorem subset_weaklyAssociatedPrimes :
    associatedPrimesOfModule R M ⊆ weaklyAssociatedPrimes R M := by
  intro 𝔭 h𝔭
  exact (associatedPrimesOfModule_subset_associatedPrimes R M h𝔭).isWeaklyAssociatedToModule

end associatedPrimesOfModule

namespace associatedPrimes

/-- Lemma 10.66.6 (2): every associated prime of `M` is weakly associated to `M`. -/
theorem subset_weaklyAssociatedPrimes :
    associatedPrimes R M ⊆ weaklyAssociatedPrimes R M := by
  intro 𝔭 h𝔭
  exact (AssociatedPrimes.mem_iff.mp h𝔭).isWeaklyAssociatedToModule

end associatedPrimes

namespace weaklyAssociatedPrimes

/-- Lemma 10.66.6 (3): a weakly associated prime of `M`, viewed as a point of `Spec R`, lies in the
support of `M`. -/
theorem subset_support :
    PrimeSpectrum.asIdeal ⁻¹' weaklyAssociatedPrimes R M ⊆ Module.support R M := by
  intro 𝔭 h𝔭
  simpa using (show Ideal.IsWeaklyAssociatedToModule R M 𝔭.asIdeal from h𝔭).mem_support

end weaklyAssociatedPrimes

end

/-! ### Lemma_10_66_7 (from Chap10) -/
universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage: this item lies in commutative algebra of weakly associated primes of modules.
The owner abstraction in the chapter is the set-valued declaration `weaklyAssociatedPrimes R M`,
parallel to mathlib's `associatedPrimes R M`.

Sampled owner-style declarations in the same domain:
- `associatedPrimes R M`
- `biUnion_associatedPrimes_eq_zero_divisors`
- `associatedPrimes.subset_of_injective`
- `weaklyAssociatedPrimes.subset_of_injective`

This file is therefore `core/canonical` owner API: it identifies the union of the owner set with
the textbook zerodivisor set, and derives the regular-element reformulation from that owner
statement. Primitive data are only the ring, module, and owner set; there is no extra wrapper
structure to keep. -/

namespace weaklyAssociatedPrimes

/-- Helper for Lemma 10.66.7: an element lying in a weakly associated prime annihilates some
nonzero module element. -/
lemma exists_smul_eq_zero_of_mem_weaklyAssociatedPrime {𝔮 : Ideal R} {f : R}
    (h𝔮 : 𝔮 ∈ weaklyAssociatedPrimes R M) (hf : f ∈ 𝔮) :
    ∃ m : M, m ≠ 0 ∧ f • m = 0 := by
  rw [mem_weaklyAssociatedPrimes_iff] at h𝔮
  rcases h𝔮 with ⟨m, hm⟩
  -- Minimal-prime avoidance produces a coefficient outside `torsionOf m` whose product with `f`
  -- lies inside `torsionOf m`.
  obtain ⟨g, hg, hfg⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hm hf
  refine ⟨g • m, ?_, ?_⟩
  · -- Since `g` avoids the torsion ideal, the scaled element `g • m` is nonzero.
    intro hgm
    have hg_mem : g ∈ Ideal.torsionOf R M m := by
      rw [Ideal.mem_torsionOf_iff]
      exact hgm
    exact hg hg_mem
  · -- Membership of `f * g` in the torsion ideal says exactly that `f` kills `g • m`.
    rw [Ideal.mem_torsionOf_iff] at hfg
    simpa [smul_smul, mul_comm] using hfg

/-- Helper for Lemma 10.66.7: every element of the kernel of multiplication by `f` is annihilated
by `f` inside that kernel module. -/
lemma mem_torsionOf_ker_lsmul {f : R}
    (n : LinearMap.ker (LinearMap.lsmul R M f)) :
    f ∈ Ideal.torsionOf R (LinearMap.ker (LinearMap.lsmul R M f)) n := by
  -- Rewrite the torsion condition in the kernel module to the defining kernel equation.
  rw [Ideal.mem_torsionOf_iff]
  apply Subtype.ext
  simpa [LinearMap.mem_ker, LinearMap.lsmul_apply] using n.2

/-- Helper for Lemma 10.66.7: a zerodivisor on `M` lies in some weakly associated prime of `M`. -/
lemma exists_weaklyAssociatedPrime_of_smul_eq_zero {f : R}
    (hf : ∃ m : M, m ≠ 0 ∧ f • m = 0) :
    ∃ 𝔮 : Ideal R, 𝔮 ∈ weaklyAssociatedPrimes R M ∧ f ∈ 𝔮 := by
  let N : Submodule R M := LinearMap.ker (LinearMap.lsmul R M f)
  rcases hf with ⟨m, hm_ne, hfm⟩
  have hm_mem : m ∈ N := by
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply]
    exact hfm
  let n : N := ⟨m, hm_mem⟩
  have hn_ne : n ≠ 0 := by
    intro hn
    have hm_zero : m = 0 := by
      simpa [n] using congrArg Subtype.val hn
    exact hm_ne hm_zero
  have hN_not_subsingleton : ¬ Subsingleton N := by
    intro hN
    exact hn_ne (Subsingleton.elim n 0)
  have hN_nontrivial : Nontrivial N := not_subsingleton_iff_nontrivial.mp hN_not_subsingleton
  letI : Nontrivial N := hN_nontrivial
  -- The nontrivial kernel has a weakly associated prime by Lemma `10.66.5`.
  obtain ⟨𝔮, h𝔮N⟩ : (weaklyAssociatedPrimes R N).Nonempty := weaklyAssociatedPrimes.nonempty
  have h𝔮M : 𝔮 ∈ weaklyAssociatedPrimes R M := by
    -- Lemma `10.66.4` transports weak association along the injective subtype map.
    exact
      weaklyAssociatedPrimes.subset_of_injective
        (R := R) (M' := N) (M := M) (f := N.subtype) N.subtype_injective h𝔮N
  rw [mem_weaklyAssociatedPrimes_iff] at h𝔮N
  rcases h𝔮N with ⟨x, hx⟩
  have hf_torsion : f ∈ Ideal.torsionOf R N x :=
    mem_torsionOf_ker_lsmul (R := R) (M := M) x
  have hf_mem : f ∈ 𝔮 := hx.1.2 hf_torsion
  exact ⟨𝔮, h𝔮M, hf_mem⟩

/-- Lemma 10.66.7: the union of the weakly associated primes of the `R`-module `M` is exactly the
set of zerodivisors on `M`. This is the weakly associated analogue of the canonical mathlib theorem
`biUnion_associatedPrimes_eq_zero_divisors`. -/
-- Proof sketch: if `f ∈ 𝔮 ∈ WeakAss(M)`, choose `m : M` such that `𝔮` is minimal over
-- `Ann(m)`. Minimality gives some `g ∉ 𝔮` and `n > 0` with `f ^ n • (g • m) = 0`; taking `n`
-- minimal shows `f` kills a nonzero element of `M`, so `f` is a zerodivisor. Conversely, if `f`
-- kills a nonzero element, the submodule `N = {m | f • m = 0}` is nontrivial, so Lemma 10.66.5
-- gives a weakly associated prime of `N`, and Lemma 10.66.4 carries it to a weakly associated
-- prime of `M` containing `f`.
theorem biUnion_eq_zero_divisors :
    ⋃ 𝔮 ∈ weaklyAssociatedPrimes R M, 𝔮 =
      { f : R | ∃ m : M, m ≠ 0 ∧ f • m = 0 } := by
  ext f
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨𝔮, h𝔮, hf⟩
    -- An element inside a weakly associated prime annihilates a nonzero vector.
    exact exists_smul_eq_zero_of_mem_weaklyAssociatedPrime h𝔮 hf
  · intro hf
    -- A zerodivisor yields a nontrivial kernel of multiplication, hence a weakly associated prime.
    rcases exists_weaklyAssociatedPrime_of_smul_eq_zero hf with ⟨𝔮, h𝔮, hf𝔮⟩
    exact ⟨𝔮, h𝔮, hf𝔮⟩

/-- Equivalent regular-element form of Lemma 10.66.7, parallel to
`biUnion_associatedPrimes_eq_compl_regular`. -/
theorem biUnion_eq_compl_regular :
    ⋃ 𝔮 ∈ weaklyAssociatedPrimes R M, 𝔮 =
      { f : R | IsSMulRegular M f }ᶜ :=
  biUnion_eq_zero_divisors.trans <| by
    simp_rw [Set.compl_setOf, isSMulRegular_iff_right_eq_zero_of_smul,
      not_forall, exists_prop, and_comm]

end weaklyAssociatedPrimes

end

/-! ### Lemma_10_66_8 (from Chap10) -/
universe u v

open PrimeSpectrum Localization

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage:
* primary domain: commutative algebra of module support, localization at a prime, and weakly
  associated primes;
* sampled owner abstractions: `Module.support`, `Module.support_subset_preimage_comap`,
  `weaklyAssociatedPrimes`, and
  `isWeaklyAssociatedToModule_iff_isWeaklyAssociatedToModule_maximalIdeal_atPrime`;
* layer: `bridge/view`, since the target theorem translates a minimal-support point into membership
  in the owner set `weaklyAssociatedPrimes R M`.

Primitive data are only the original module, its prime localization, and the canonical owner sets.
The local support-descent helper below remains private because the sampled upstream support API does
not provide this exact `IsLocalizedModule` descent statement. -/

private theorem mem_support_comap_of_mem_support_of_isLocalizedModule
    (S : Submonoid R) {R' : Type*} [CommRing R'] [Algebra R R']
    {M' : Type*} [AddCommGroup M'] [Module R' M'] [Module R M'] [IsScalarTower R R' M']
    (f : M →ₗ[R] M') [IsLocalizedModule S f] {q : PrimeSpectrum R'}
    (hq : q ∈ Module.support R' M') :
    PrimeSpectrum.comap (algebraMap R R') q ∈ Module.support R M := by
  rw [Module.mem_support_iff_exists_annihilator] at hq ⊢
  obtain ⟨x, hx⟩ := hq
  obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
  refine ⟨m, fun r hr ↦ ?_⟩
  rw [Submodule.mem_annihilator_span_singleton] at hr
  exact hx <| by
    rw [Submodule.mem_annihilator_span_singleton]
    simpa [algebraMap_smul] using
      (show r • IsLocalizedModule.mk' f m s = 0 by
        rw [← IsLocalizedModule.mk'_smul, hr, IsLocalizedModule.mk'_zero])

/-- Lemma 10.66.8: if a prime point `𝔭` is minimal in the support of an `R`-module `M`, then its
underlying ideal is a weakly associated prime of `M`. -/
-- Proof sketch: localize at `𝔭`. Minimality in the support forces the support of the localized
-- module to be the singleton closed point, so the localization is nonzero. Lemma 10.66.5 then
-- gives a weakly associated prime of the localized module; Lemma 10.66.6 shows it must be the
-- maximal ideal of the localization, and Lemma 10.66.2 descends this weak association back to
-- `M`.
theorem minimal_support_mem_weaklyAssociatedPrimes
    (𝔭 : PrimeSpectrum R)
    (h𝔭 : Minimal (· ∈ Module.support R M) 𝔭) :
    𝔭.asIdeal ∈ weaklyAssociatedPrimes R M := by
  let Rₚ := Localization.AtPrime 𝔭.asIdeal
  let Mₚ := LocalizedModule.AtPrime 𝔭.asIdeal M
  haveI : Nontrivial Mₚ := Module.mem_support_iff.mp h𝔭.1
  obtain ⟨q, hq⟩ : (weaklyAssociatedPrimes Rₚ Mₚ).Nonempty := weaklyAssociatedPrimes.nonempty
  let q' : PrimeSpectrum Rₚ := ⟨q, hq.isPrime⟩
  have hq_support : q' ∈ Module.support Rₚ Mₚ := by
    simpa [q'] using hq.mem_support
  have hq_comap_support : PrimeSpectrum.comap (algebraMap R Rₚ) q' ∈ Module.support R M := by
    exact
      mem_support_comap_of_mem_support_of_isLocalizedModule
        𝔭.asIdeal.primeCompl (LocalizedModule.mkLinearMap 𝔭.asIdeal.primeCompl M) hq_support
  have hq_comap_le : PrimeSpectrum.comap (algebraMap R Rₚ) q' ≤ 𝔭 := by
    change ((IsLocalization.AtPrime.primeSpectrumOrderIso Rₚ 𝔭.asIdeal q').1 ≤ 𝔭)
    exact (IsLocalization.AtPrime.primeSpectrumOrderIso Rₚ 𝔭.asIdeal q').2
  have hq_comap_eq : Ideal.comap (algebraMap R Rₚ) q = 𝔭.asIdeal := by
    have : PrimeSpectrum.comap (algebraMap R Rₚ) q' = 𝔭 :=
      le_antisymm hq_comap_le (h𝔭.2 hq_comap_support hq_comap_le)
    simpa [PrimeSpectrum.comap_asIdeal, q'] using congrArg PrimeSpectrum.asIdeal this
  have hq_eq : q = IsLocalRing.maximalIdeal Rₚ := by
    exact AtPrime.eq_maximalIdeal_iff_comap_eq.mp hq_comap_eq
  exact
    (isWeaklyAssociatedToModule_iff_isWeaklyAssociatedToModule_maximalIdeal_atPrime
      𝔭.asIdeal).2 <|
      hq_eq ▸ hq

end

/-! ### Lemma_10_66_9 (from Chap10) -/
universe u v

open IsLocalRing

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage:
* `source-facing`: Stacks Lemma 10.66.9 compares the chapter predicate
  `Ideal.IsAssociatedToModule` with `Ideal.IsWeaklyAssociatedToModule` for a finitely generated
  prime ideal.
* `core/canonical`: mathlib's owner abstraction is `IsAssociatedPrime`.
* `bridge/view`: the owner-level equivalence and owner-set equality are derived from the
  source-facing theorem below. Primitive data: none. -/

private theorem isAssociatedToModule_maximalIdeal_of_fg_of_isWeaklyAssociatedToModule
    {A : Type*} [CommRing A] [IsLocalRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (hfg : (maximalIdeal A).FG)
    (h : Ideal.IsWeaklyAssociatedToModule A N (maximalIdeal A)) :
    Ideal.IsAssociatedToModule A N (maximalIdeal A) := by
  rcases h with ⟨x, hx⟩
  have hminimal : (Ideal.torsionOf A N x).minimalPrimes = {maximalIdeal A} := by
    ext q
    constructor
    · intro hq
      have hq_le : q ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal hq.1.1.ne_top
      exact Set.mem_singleton_iff.mpr <| le_antisymm hq_le (hx.2 hq.1 hq_le)
    · rintro rfl
      exact hx
  have hrad : (Ideal.torsionOf A N x).radical = maximalIdeal A := by
    rw [← Ideal.sInf_minimalPrimes, hminimal, sInf_singleton]
  have htorsion_ne_top : Ideal.torsionOf A N x ≠ ⊤ := by
    intro htop
    exact (maximalIdeal.isMaximal A).ne_top <| by
      simpa [htop, Ideal.radical_top] using hrad.symm
  have hpow : ∃ n : ℕ, maximalIdeal A ^ n ≤ Ideal.torsionOf A N x := by
    exact
      Ideal.exists_pow_le_of_le_radical_of_fg
        (by simp [hrad]) hfg
  classical
  let n := Nat.find hpow
  have hn : maximalIdeal A ^ n ≤ Ideal.torsionOf A N x := Nat.find_spec hpow
  have hn_ne_zero : n ≠ 0 := by
    intro hn_zero
    exact htorsion_ne_top <| top_le_iff.mp <| by simpa [n, hn_zero] using hn
  have hnot : ¬ maximalIdeal A ^ (n - 1) ≤ Ideal.torsionOf A N x := by
    intro hle
    have hfind : n ≤ n - 1 := Nat.find_min' hpow hle
    omega
  rw [Ideal.isAssociatedToModule_iff_exists_torsionOf]
  rw [SetLike.not_le_iff_exists] at hnot
  rcases hnot with ⟨a, ha_mem, ha_not_mem⟩
  refine ⟨(maximalIdeal.isMaximal A).isPrime, a • x, ?_⟩
  apply le_antisymm
  · intro b hb
    rw [Ideal.mem_torsionOf_iff, smul_smul]
    have hba : b * a ∈ maximalIdeal A ^ n := by
      have hba' : b * a ∈ maximalIdeal A ^ (n - 1) * maximalIdeal A := by
        simpa [mul_comm] using Ideal.mul_mem_mul_rev ha_mem hb
      have hba'' : b * a ∈ maximalIdeal A ^ (n - 1 + 1) := by
        simpa [pow_succ] using hba'
      have hn_eq : n - 1 + 1 = n := by
        exact Nat.sub_add_cancel <| Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn_ne_zero)
      simpa [hn_eq] using hba''
    simpa [Ideal.mem_torsionOf_iff, mul_comm, mul_left_comm, mul_assoc] using hn hba
  · have hproper : Ideal.torsionOf A N (a • x) ≠ ⊤ := by
      intro htop
      have ha_zero : a • x = 0 := by
        simpa [Ideal.mem_torsionOf_iff, one_smul] using
          (show (1 : A) ∈ Ideal.torsionOf A N (a • x) by simp [htop])
      exact ha_not_mem <| by simp [Ideal.mem_torsionOf_iff, ha_zero]
    exact IsLocalRing.le_maximalIdeal hproper

/-- Lemma 10.66.9: for a finitely generated ideal `𝔭`, textbook-associated and weakly associated
primes of `M` coincide. -/
theorem isAssociatedToModule_iff_isWeaklyAssociatedToModule_of_fg
    (𝔭 : Ideal R) (h𝔭fg : 𝔭.FG) :
    Ideal.IsAssociatedToModule R M 𝔭 ↔ Ideal.IsWeaklyAssociatedToModule R M 𝔭 := by
  constructor
  · intro h
    exact h.isWeaklyAssociatedToModule
  · intro h
    by_cases h𝔭prime : 𝔭.IsPrime
    · letI : 𝔭.IsPrime := h𝔭prime
      have hloc :
          Ideal.IsAssociatedToModule (Localization.AtPrime 𝔭) (LocalizedModule.AtPrime 𝔭 M)
            (maximalIdeal (Localization.AtPrime 𝔭)) := by
        exact
          isAssociatedToModule_maximalIdeal_of_fg_of_isWeaklyAssociatedToModule
            (by simpa [Localization.AtPrime.map_eq_maximalIdeal] using h𝔭fg.map (algebraMap R (Localization.AtPrime 𝔭)))
            ((isWeaklyAssociatedToModule_iff_isWeaklyAssociatedToModule_maximalIdeal_atPrime 𝔭).mp h)
      exact Ideal.isAssociatedToModule_of_isAssociatedToModule_maximalIdeal_atPrime_of_fg hloc h𝔭fg
    · exact (h𝔭prime h.isPrime).elim

/-- Companion owner-form of Lemma 10.66.9: for a finitely generated ideal `𝔭`, the mathlib
predicate `IsAssociatedPrime 𝔭 M` is equivalent to weak association. -/
theorem isAssociatedPrime_iff_isWeaklyAssociatedToModule_of_fg
    (𝔭 : Ideal R) (h𝔭fg : 𝔭.FG) :
    IsAssociatedPrime 𝔭 M ↔ Ideal.IsWeaklyAssociatedToModule R M 𝔭 := by
  constructor
  · intro h
    exact h.isWeaklyAssociatedToModule
  · intro h
    exact
      ((isAssociatedToModule_iff_isWeaklyAssociatedToModule_of_fg 𝔭 h𝔭fg).mpr h).isAssociatedPrime

/-- In a Noetherian ring, textbook-associated primes and weakly associated primes of a module
coincide in mathlib's owner API. -/
theorem associatedPrimes_eq_weaklyAssociatedPrimes [IsNoetherianRing R] :
    associatedPrimes R M = weaklyAssociatedPrimes R M := by
  ext 𝔭
  rw [AssociatedPrimes.mem_iff, mem_weaklyAssociatedPrimes_iff]
  exact
    isAssociatedPrime_iff_isWeaklyAssociatedToModule_of_fg 𝔭
      (Ideal.fg_of_isNoetherianRing 𝔭)

end

/-! ### Remark_10_66_10 (from Chap10) -/
open MvPolynomial

attribute [local instance high] Semiring.toModule Algebra.toModule

universe u

noncomputable section

/-
Domain triage: this remark is in commutative algebra of weakly associated primes under scalar
restriction along a polynomial-ring map. The owner abstraction is the chapter declaration
`weaklyAssociatedPrimes R M`. The primitive data are the relation ideal defining the quotient ring
and the explicit source-facing ideal `q = Σ xᵢ S` in that quotient. The algebra structure from
`k[x₁, x₂, …]` is derived from the canonical `MvPolynomial.rename` map and the owner quotient
algebra instance, so it should stay local rather than as a parallel public wrapper.
-/

/-- The ideal `(xᵢ yᵢ \mid i \ge 0)` in
`k[x₁, x₂, x₃, \ldots, y₁, y₂, y₃, \ldots]`. -/
def pairwiseZeroProductRelationIdeal (k : Type u) [CommRing k] :
    Ideal (MvPolynomial (Sum ℕ ℕ) k) :=
  Ideal.span (Set.range fun n : ℕ ↦ X (Sum.inl n) * X (Sum.inr n))

/-- The quotient ring
`k[x₁, x₂, x₃, \ldots, y₁, y₂, y₃, \ldots] / (x₁ y₁, x₂ y₂, x₃ y₃, \ldots)`. -/
abbrev pairwiseZeroProductQuotient (k : Type u) [CommRing k] :=
  MvPolynomial (Sum ℕ ℕ) k ⧸ pairwiseZeroProductRelationIdeal k

/-- The ideal `q = Σ xᵢ S` in the quotient ring of Remark 10.66.10. -/
def pairwiseZeroProductXIdeal (k : Type u) [CommRing k] : Ideal (pairwiseZeroProductQuotient k) :=
  Ideal.span (Set.range fun n : ℕ ↦
    Ideal.Quotient.mk (pairwiseZeroProductRelationIdeal k) (X (Sum.inl n)))

/-- The ideal `(x₁, x₂, x₃, \ldots)` in `k[x₁, x₂, x₃, \ldots]`. -/
def infiniteVariableIdeal (k : Type u) [CommRing k] : Ideal (MvPolynomial ℕ k) :=
  Ideal.span (Set.range fun n : ℕ ↦ (X n : MvPolynomial ℕ k))

section

variable (k : Type u) [Field k]

local notation "R∞" => MvPolynomial ℕ k
local notation "S∞" => pairwiseZeroProductQuotient k

local instance : Algebra R∞ (MvPolynomial (Sum ℕ ℕ) k) :=
  RingHom.toAlgebra (rename Sum.inl).toRingHom

local instance : Algebra R∞ S∞ :=
  Ideal.Quotient.algebra R∞

/-- The source-facing ideal `q = Σ xᵢ S` is a prime ideal of the counterexample ring. -/
theorem pairwiseZeroProductXIdeal_isPrime :
    (pairwiseZeroProductXIdeal k).IsPrime := sorry

/-- The source-facing ideal `q = Σ xᵢ S` is weakly associated to `S` as an `S`-module. -/
theorem pairwiseZeroProductXIdeal_mem_weaklyAssociatedPrimes_self :
    pairwiseZeroProductXIdeal k ∈ weaklyAssociatedPrimes S∞ S∞ := sorry

/-- Contracting `q = Σ xᵢ S` along `k[x₁, x₂, x₃, \ldots] → S` gives `(x₁, x₂, x₃, \ldots)`. -/
theorem comap_pairwiseZeroProductXIdeal :
    Ideal.comap (algebraMap R∞ S∞) (pairwiseZeroProductXIdeal k) = infiniteVariableIdeal k := sorry

/-- The contracted ideal `(x₁, x₂, x₃, \ldots)` is not weakly associated to `S` as an
`k[x₁, x₂, x₃, \ldots]`-module. -/
theorem infiniteVariableIdeal_not_mem_weaklyAssociatedPrimes :
    infiniteVariableIdeal k ∉ weaklyAssociatedPrimes R∞ S∞ := sorry

/-- Remark 10.66.10: for the ring map
`k[x₁, x₂, x₃, \ldots] → k[x₁, x₂, x₃, \ldots, y₁, y₂, y₃, \ldots] / (x₁ y₁, x₂ y₂, x₃ y₃, \ldots)`
and `M = S`, the image of `WeakAss_S(M)` in `Spec(R)` need not lie in `WeakAss_R(M)`. This shows
the finite-map hypothesis in Lemma `10.66.13` is essential. -/
-- Proof sketch: let `q = Σ xᵢ S`. The remark explains that `q` is a minimal prime of `S`, hence a
-- weakly associated prime of `S` over itself, while its contraction `(x₁, x₂, x₃, \ldots)` is not
-- weakly associated to `S` as an `R`-module because annihilators of nonzero elements over `R` are
-- finitely generated.
theorem weaklyAssociatedPrimes_comap_image_not_subset_for_pairwiseZeroProductQuotient
    :
    ¬ Ideal.comap (algebraMap R∞ S∞) '' weaklyAssociatedPrimes S∞ S∞ ⊆
      weaklyAssociatedPrimes R∞ S∞ := by
  intro hsubset
  have hq :
      Ideal.comap (algebraMap R∞ S∞) (pairwiseZeroProductXIdeal k) ∈
        Ideal.comap (algebraMap R∞ S∞) '' weaklyAssociatedPrimes S∞ S∞ := by
    exact ⟨pairwiseZeroProductXIdeal k, pairwiseZeroProductXIdeal_mem_weaklyAssociatedPrimes_self k,
      rfl⟩
  have hmem :
      Ideal.comap (algebraMap R∞ S∞) (pairwiseZeroProductXIdeal k) ∈ weaklyAssociatedPrimes R∞ S∞ :=
    hsubset hq
  rw [comap_pairwiseZeroProductXIdeal k] at hmem
  exact infiniteVariableIdeal_not_mem_weaklyAssociatedPrimes k hmem

end

end

/-! ### Lemma_10_66_11 (from Chap10) -/
universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/- Domain triage:
* `source-facing`: the textbook statement is the image inclusion for `weaklyAssociatedPrimes`
  under restriction of scalars.
 * `core/canonical`: the owner object is the set-valued declaration `weaklyAssociatedPrimes R M`,
  with the ambient `R`-module structure carried by `[Module R M] [IsScalarTower R S M]` rather
  than rebuilt ad hoc by repeated `Module.compHom`.
 * `bridge/view`: the pointwise lifting of one weakly associated prime is kept internal and the
  set-theoretic inclusion remains the only public theorem. -/

namespace weaklyAssociatedPrimes

/-- Helper for Lemma 10.66.11: restricting scalars from `S` to `R` contracts the annihilator ideal
of an element of `M` to its annihilator over `R`. -/
private theorem comap_torsionOf_eq (m : M) :
    Ideal.comap (algebraMap R S) (Ideal.torsionOf S M m) = Ideal.torsionOf R M m := by
  -- Membership in both annihilator ideals is the same scalar-annihilation equation on `m`.
  ext r
  rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  simp [algebraMap_smul]

/- Internal pointwise lifting used to derive Lemma 10.66.11. Every weakly associated prime of `M`
over `R` lifts to a weakly associated prime of `M` over `S` whose contraction along
`algebraMap R S` is the given prime. -/
-- Proof sketch: let `𝔭 ∈ WeakAss_R(M)`. After localizing at `𝔭`, Lemma 10.66.2 gives an element
-- of the localized module whose annihilator has radical the maximal ideal. Regard the same element
-- over the localized `S`-algebra, choose a minimal prime over its annihilator there, and apply
-- Lemma 10.66.2 again to obtain a weakly associated prime of `M` over `S` contracting to `𝔭`.
private theorem exists_mem_comap_eq_of_mem
    (S : Type v) [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    {𝔭 : Ideal R}
    (h𝔭 : 𝔭 ∈ weaklyAssociatedPrimes R M) :
    ∃ 𝔮 ∈ weaklyAssociatedPrimes S M, Ideal.comap (algebraMap R S) 𝔮 = 𝔭 := by
  rcases h𝔭 with ⟨m, hm⟩
  -- Re-express the weak-association witness over `R` as a minimal prime over the contracted
  -- `S`-annihilator of the same element.
  have hminimal :
      𝔭 ∈ (Ideal.comap (algebraMap R S) (Ideal.torsionOf S M m)).minimalPrimes := by
    simpa [comap_torsionOf_eq (R := R) (S := S) (M := M) m] using hm
  -- Lift this minimal prime through contraction to a minimal prime over the `S`-annihilator.
  obtain ⟨𝔮, h𝔮, hcomap⟩ :=
    Ideal.exists_minimalPrimes_comap_eq (algebraMap R S) 𝔭 hminimal
  exact ⟨𝔮, ⟨m, h𝔮⟩, hcomap⟩

/-- Lemma 10.66.11: under the map `Spec(algebraMap R S)`, the weakly associated primes of the
`R`-module `M` are contained in the image of the weakly associated primes of `M` over `S`. -/
theorem subset_comap_image :
    weaklyAssociatedPrimes R M ⊆
      Ideal.comap (algebraMap R S) '' weaklyAssociatedPrimes S M := by
  intro 𝔭 h𝔭
  rcases exists_mem_comap_eq_of_mem S h𝔭 with ⟨𝔮, h𝔮, hcomap⟩
  exact ⟨𝔮, h𝔮, hcomap⟩

end weaklyAssociatedPrimes

end

/-! ### Remark_10_66_12 (from Chap10) -/
universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- Remark 10.66.12: under the map `Spec S → Spec R`, the image of `Ass_S(M)` is contained in
`Ass_R(M)`, which is contained in `WeakAss_R(M)`, which is contained in the image of
`WeakAss_S(M)`. -/
-- Proof sketch: combine the restriction-of-scalars inclusion for textbook associated primes, the
-- inclusion `Ass_R(M) ⊆ WeakAss_R(M)`, and the restriction-of-scalars inclusion for weakly
-- associated primes.
theorem restrictScalars_associatedPrimes_weaklyAssociatedPrimes_chain :
    List.IsChain (· ⊆ ·)
      [ Ideal.comap (algebraMap R S) '' associatedPrimesOfModule S M,
        associatedPrimesOfModule R M,
        weaklyAssociatedPrimes R M,
        Ideal.comap (algebraMap R S) '' weaklyAssociatedPrimes S M ] := by
  refine List.IsChain.cons_cons ?_ ?_
  · simpa using associatedPrimesOfModule_image_comap_subset
  · refine List.IsChain.cons_cons ?_ ?_
    · simpa using associatedPrimesOfModule.subset_weaklyAssociatedPrimes
    · simpa [List.isChain_pair] using weaklyAssociatedPrimes.subset_comap_image

/-- If `S` is Noetherian, then all inclusions in the restriction-of-scalars chain for associated
and weakly associated primes are equalities. -/
-- Proof sketch: if `S` is Noetherian, then `associatedPrimesOfModule S M = weaklyAssociatedPrimes
-- S M`. The first theorem gives a chain of inclusions whose outer two terms are therefore equal,
-- forcing all adjacent inclusions to be equalities.
theorem restrictScalars_associatedPrimes_weaklyAssociatedPrimes_eq_chain_of_isNoetherianRing
    [IsNoetherianRing S] :
    List.IsChain (· = ·)
      [ Ideal.comap (algebraMap R S) '' associatedPrimesOfModule S M,
        associatedPrimesOfModule R M,
        weaklyAssociatedPrimes R M,
        Ideal.comap (algebraMap R S) '' weaklyAssociatedPrimes S M ] := by
  let A : Set (Ideal R) := Ideal.comap (algebraMap R S) '' associatedPrimesOfModule S M
  let B : Set (Ideal R) := associatedPrimesOfModule R M
  let C : Set (Ideal R) := weaklyAssociatedPrimes R M
  let D : Set (Ideal R) := Ideal.comap (algebraMap R S) '' weaklyAssociatedPrimes S M
  change List.IsChain (· = ·) [A, B, C, D]
  have hAB : A ⊆ B := by
    simpa [A, B] using associatedPrimesOfModule_image_comap_subset
  have hBC : B ⊆ C := by
    simpa [B, C] using associatedPrimesOfModule.subset_weaklyAssociatedPrimes
  have hCD : C ⊆ D := by
    simpa [C, D] using weaklyAssociatedPrimes.subset_comap_image
  have hAD : A = D := by
    simp [A, D, associatedPrimesOfModule_eq_associatedPrimes, associatedPrimes_eq_weaklyAssociatedPrimes]
  have hAB_eq : A = B := Set.Subset.antisymm hAB fun p hp ↦ hAD.symm ▸ hCD (hBC hp)
  have hBC_eq : B = C := Set.Subset.antisymm hBC fun p hp ↦ hAB_eq ▸ (hAD.symm ▸ hCD hp)
  have hCD_eq : C = D := Set.Subset.antisymm hCD fun p hp ↦ hBC (hAB_eq ▸ (hAD.symm ▸ hp))
  refine List.IsChain.cons_cons hAB_eq ?_
  refine List.IsChain.cons_cons hBC_eq ?_
  simpa [List.isChain_pair] using hCD_eq

end

/-! ### Lemma_10_66_13 (from Chap10) -/
universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-
Domain triage:
* `source-facing`: the textbook item identifies the image of `WeakAss_S(M)` in `Spec R` under a
  finite ring map.
* `core/canonical`: the owner abstraction in this chapter is the set-valued declaration
  `weaklyAssociatedPrimes R M`.
* `bridge/view`: the only primitive module-theoretic datum needed pointwise is the annihilator
  ideal `Ideal.torsionOf _ _ m`; the set-level equality should be expressed directly in terms of
  the owner set rather than by a parallel wrapper declaration.
-/

namespace weaklyAssociatedPrimes

omit [Module.Finite R S] in
private theorem comap_torsionOf_eq (m : M) :
    Ideal.comap (algebraMap R S) (Ideal.torsionOf S M m) = Ideal.torsionOf R M m := by
  ext r
  rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  simp [algebraMap_smul]

/-- Helper for Lemma 10.66.13: in an integral extension, minimal primes contract to
minimal primes. -/
private theorem comap_mem_minimalPrimes_of_isIntegral_zero
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] {𝔮 : Ideal B} (h𝔮 : 𝔮 ∈ minimalPrimes B) :
    Ideal.comap (algebraMap A B) 𝔮 ∈ minimalPrimes A := by
  -- TODO: localize at `𝔭 := Ideal.comap (algebraMap A B) 𝔮` and `𝔮`, use lying over in the
  -- induced local integral map `A_𝔭 → B_𝔮` to produce a prime below `𝔮`, then use minimality of
  -- `𝔮` over `0` to force equality and conclude that every prime below `𝔭` is equal to `𝔭`.
  sorry

/-- Helper for Lemma 10.66.13: reduce contraction of minimal primes over arbitrary ideals to the
zero-ideal case in the quotient rings. -/
private theorem comap_mem_minimalPrimes_of_isIntegral [Algebra.IsIntegral R S]
    {I : Ideal S} {𝔮 : Ideal S} (h𝔮 : 𝔮 ∈ I.minimalPrimes) :
    Ideal.comap (algebraMap R S) 𝔮 ∈ (Ideal.comap (algebraMap R S) I).minimalPrimes := by
  let Icomap : Ideal R := Ideal.comap (algebraMap R S) I
  rw [Ideal.minimalPrimes_eq_comap] at h𝔮
  rcases h𝔮 with ⟨𝔮bar, h𝔮bar, h𝔮bar_eq⟩
  letI : Algebra (R ⧸ Icomap) (S ⧸ I) := inferInstance
  have h𝔭bar :
      Ideal.comap (algebraMap (R ⧸ Icomap) (S ⧸ I)) 𝔮bar ∈ minimalPrimes (R ⧸ Icomap) :=
    comap_mem_minimalPrimes_of_isIntegral_zero
      (A := R ⧸ Icomap) (B := S ⧸ I) h𝔮bar
  rw [Ideal.minimalPrimes_eq_comap]
  refine ⟨Ideal.comap (algebraMap (R ⧸ Icomap) (S ⧸ I)) 𝔮bar, h𝔭bar, ?_⟩
  -- Compose the quotient contractions to recover the original contracted prime of `𝔮`.
  calc
    Ideal.comap (Ideal.Quotient.mk Icomap)
        (Ideal.comap (algebraMap (R ⧸ Icomap) (S ⧸ I)) 𝔮bar)
      = Ideal.comap (algebraMap R (S ⧸ I)) 𝔮bar := by
          rw [Ideal.comap_comap]
          rfl
    _ = Ideal.comap (algebraMap R S) (Ideal.comap (Ideal.Quotient.mk I) 𝔮bar) := by
          rw [Ideal.comap_comap]
          rfl
    _ = Ideal.comap (algebraMap R S) 𝔮 := by
          simpa [h𝔮bar_eq]

/-- Helper for Lemma 10.66.13: once minimal primes contract correctly under an integral map, a
weakly associated prime of `M` over `S` contracts to a weakly associated prime over `R`. -/
private theorem comap_mem_weaklyAssociatedPrimes_of_mem
    {𝔮 : Ideal S} (h𝔮 : 𝔮 ∈ weaklyAssociatedPrimes S M) :
    Ideal.comap (algebraMap R S) 𝔮 ∈ weaklyAssociatedPrimes R M := by
  rcases h𝔮 with ⟨m, hm⟩
  -- Contract the minimal-prime witness for the `S`-annihilator of `m`.
  have hminimal :
      Ideal.comap (algebraMap R S) 𝔮 ∈
        (Ideal.comap (algebraMap R S) (Ideal.torsionOf S M m)).minimalPrimes :=
    comap_mem_minimalPrimes_of_isIntegral (R := R) (S := S) hm
  -- The contracted annihilator is exactly the annihilator of the same element over `R`.
  refine ⟨m, ?_⟩
  simpa [comap_torsionOf_eq (R := R) (S := S) (M := M) m] using hminimal

/-- Lemma 10.66.13: let `f : Spec S → Spec R` be induced by `algebraMap R S`. If `R → S` is a
finite ring map, then the image of the weakly associated primes of `M` over `S` under `f` is
exactly the weakly associated primes of `M` over `R`. -/
-- Proof sketch: the inclusion `weaklyAssociatedPrimes R M ⊆ Ideal.comap (algebraMap R S) ''
-- weaklyAssociatedPrimes S M` is the restriction-of-scalars inclusion proved earlier. For the
-- reverse inclusion, start with `𝔮 ∈ weaklyAssociatedPrimes S M`, choose an element of `M` whose
-- annihilator has `𝔮` as a minimal prime, and use finiteness of `R → S`, prime avoidance, and the
-- semilocal structure of `S` over the contraction `𝔭` to produce an element whose annihilator over
-- `R` has `𝔭` as a minimal prime.
theorem restrictScalars_eq_image_comap_of_finite :
    Ideal.comap (algebraMap R S) '' weaklyAssociatedPrimes S M =
      weaklyAssociatedPrimes R M := by
  -- The earlier item already proves the inclusion from `R` to the image from `S`.
  refine Set.Subset.antisymm ?_ subset_comap_image
  rintro 𝔭 ⟨𝔮, h𝔮, rfl⟩
  -- For the reverse inclusion, contract a weakly associated prime witness along the finite map.
  exact comap_mem_weaklyAssociatedPrimes_of_mem (R := R) (S := S) (M := M) h𝔮

end weaklyAssociatedPrimes

end

/-! ### Lemma_10_66_14 (from Chap10) -/
universe u v

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)
variable {M : Type v} [AddCommGroup M] [Module (R ⧸ I) M] [Module R M]
variable [IsScalarTower R (R ⧸ I) M]

/- Domain triage:
* primary domain: weakly associated primes under restriction of scalars in commutative algebra;
* `core/canonical` owner: the set-valued declaration `weaklyAssociatedPrimes R M`;
* `bridge/view`: the quotient-map specialization `R → R ⧸ I`.

This item adds no new primitive data: it is exactly the quotient specialization of the owner
theorem `weaklyAssociatedPrimes.restrictScalars_eq_image_comap_of_finite`, so the file should
reuse that theorem directly rather than keeping a parallel local shell. -/

/- Lemma 10.66.14: via the canonical map `Spec (R ⧸ I) → Spec R`, the weakly associated primes of
the `R ⧸ I`-module `M` are exactly the weakly associated primes of `M` viewed as an `R`-module. -/
#check
  (by
    simpa [Ideal.Quotient.algebraMap_eq] using
      (weaklyAssociatedPrimes.restrictScalars_eq_image_comap_of_finite :
        Ideal.comap (algebraMap R (R ⧸ I)) '' weaklyAssociatedPrimes (R ⧸ I) M =
          weaklyAssociatedPrimes R M))

end
