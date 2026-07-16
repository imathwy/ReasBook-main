import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import StacksProject_2024.stacks_project.Chap10.Definition_10_63_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open IsLocalRing

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage: this item is in commutative algebra of associated primes under localization.
The owner abstraction in mathlib is `Module.associatedPrimes`, but the chapter's public notion in
this section is the source-facing exact-annihilator predicate `Ideal.IsAssociatedToModule` and the
derived set `associatedPrimesOfModule`. This file therefore stays at the `source-facing` layer and
uses the owner-style localization argument only as an internal bridge. Primitive data: a prime
ideal `p`, its localization `Localization.AtPrime p`, and the localized module
`LocalizedModule.AtPrime p M`. Derived API: the set-membership reformulations below. -/

namespace Ideal

/-- Lemma 10.63.15 (1), predicate form: if `p` is associated to `M` in the textbook
exact-annihilator sense, then the maximal ideal of `R_p` is associated to `M_p` in the same
exact-annihilator sense. -/
theorem isAssociatedToModule_maximalIdeal_atPrime
    {p : Ideal R} [p.IsPrime] (hp : IsAssociatedToModule R M p) :
    IsAssociatedToModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)
      (maximalIdeal (Localization.AtPrime p)) := by
  rw [isAssociatedToModule_iff_exists_torsionOf] at hp ⊢
  rcases hp with ⟨hp, m, hm⟩
  let f : M →ₗ[R] LocalizedModule.AtPrime p M := LocalizedModule.mkLinearMap p.primeCompl M
  refine ⟨(maximalIdeal.isMaximal _).isPrime, f m, ?_⟩
  ext t
  rcases IsLocalization.exists_mk'_eq p.primeCompl t with ⟨r, s, rfl⟩
  rw [IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime p) p]
  constructor
  · intro hr
    have hrm : r • m = 0 := by
      simpa [Ideal.mem_torsionOf_iff] using (show r ∈ Ideal.torsionOf R M m from hm.symm ▸ hr)
    rw [Ideal.mem_torsionOf_iff, ← IsLocalizedModule.mk'_one p.primeCompl f,
      IsLocalizedModule.mk'_smul_mk', mul_one, hrm, IsLocalizedModule.mk'_zero]
  · intro ht
    rw [Ideal.mem_torsionOf_iff, ← IsLocalizedModule.mk'_one p.primeCompl f,
      IsLocalizedModule.mk'_smul_mk', mul_one, IsLocalizedModule.mk'_eq_zero'] at ht
    rcases ht with ⟨s', hs'⟩
    have hs'r_zero : (r * (s' : R)) • m = 0 := by
      calc
        (r * (s' : R)) • m = (s' : R) • (r • m) := by
          simp [smul_smul, mul_comm]
        _ = 0 := hs'
    have hs'r_torsion : (r * (s' : R)) ∈ Ideal.torsionOf R M m := by
      simpa [Ideal.mem_torsionOf_iff] using hs'r_zero
    have hs'r : r * (s' : R) ∈ p := by
      exact hm.symm ▸ hs'r_torsion
    exact (hp.mem_or_mem hs'r).resolve_right s'.2

/-- Lemma 10.63.15 (2), predicate form: if `p` is finitely generated and the maximal ideal of
`R_p` is associated to `M_p` in the textbook exact-annihilator sense, then `p` is associated to
`M`. -/
theorem isAssociatedToModule_of_isAssociatedToModule_maximalIdeal_atPrime_of_fg
    {p : Ideal R} [p.IsPrime]
    (hp :
      IsAssociatedToModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)
        (maximalIdeal (Localization.AtPrime p)))
    (hfg : p.FG) :
    IsAssociatedToModule R M p := by
  rw [isAssociatedToModule_iff_exists_torsionOf] at hp ⊢
  rcases hp with ⟨hpmax, x, hx⟩
  rcases hfg with ⟨T, hT⟩
  let f : M →ₗ[R] LocalizedModule.AtPrime p M := LocalizedModule.mkLinearMap p.primeCompl M
  rcases IsLocalizedModule.mk'_surjective p.primeCompl f x with ⟨⟨m, s⟩, rfl⟩
  simp only [Function.uncurry_apply_pair] at hx
  have mem (a : T) : algebraMap R (Localization.AtPrime p) a ∈ maximalIdeal (Localization.AtPrime p) := by
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p a).2 <|
      by simpa [← hT] using Ideal.subset_span a.2
  simp only [hx, Ideal.mem_torsionOf_iff, algebraMap_smul, ← IsLocalizedModule.mk'_smul,
    IsLocalizedModule.mk'_eq_zero' f] at mem
  choose g hg using mem
  let G : p.primeCompl := ∏ a, g a
  refine ⟨‹p.IsPrime›, G.1 • m, le_antisymm ?_ ?_⟩
  · have hspan : Ideal.span ↑T ≤ Ideal.torsionOf R M (G.1 • m) := by
      rw [Ideal.span_le]
      intro a ha
      let aT : T := ⟨a, ha⟩
      obtain ⟨u, hu⟩ : g aT ∣ G := by
        apply Finset.dvd_prod_of_mem g
        exact Finset.mem_univ aT
      change a ∈ Ideal.torsionOf R M (G.1 • m)
      rw [Ideal.mem_torsionOf_iff]
      have hga : ((g aT).1 * a) • m = 0 := by
        calc
          ((g aT).1 * a) • m = (g aT).1 • (a • m) := by
            simp [smul_smul]
          _ = 0 := by simpa [aT] using hg aT
      calc
        a • (G.1 • m) = u.1 • (((g aT).1 * a) • m) := by
          rw [show G = g aT * u by exact hu, Submonoid.coe_mul]
          simp [smul_smul, mul_comm, mul_left_comm]
        _ = 0 := by rw [hga, smul_zero]
    simpa [hT] using hspan
  · intro r hr
    have hr0 : (r * G.1) • m = 0 := by
      simpa [G, Ideal.mem_torsionOf_iff, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hr
    have hrG_loc : algebraMap R (Localization.AtPrime p) (r * G.1) ∈ maximalIdeal (Localization.AtPrime p) := by
      rw [hx, Ideal.mem_torsionOf_iff, algebraMap_smul, ← IsLocalizedModule.mk'_smul, hr0,
        IsLocalizedModule.mk'_zero]
    have hrG : r * G.1 ∈ p :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p (r * G.1)).1 hrG_loc
    exact (‹p.IsPrime›.mem_or_mem hrG).resolve_right G.2

end Ideal

/-- Lemma 10.63.15 (1): if `p` is associated to `M` in the textbook exact-annihilator sense, then
the maximal ideal of `R_p` is associated to `M_p` in the same exact-annihilator sense. -/
theorem mem_associatedPrimesOfModule_atPrime_of_mem_associatedPrimesOfModule
    {p : Ideal R} [p.IsPrime] (hp : p ∈ associatedPrimesOfModule R M) :
    maximalIdeal (Localization.AtPrime p) ∈
      associatedPrimesOfModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M) := by
  rw [mem_associatedPrimesOfModule_iff] at hp ⊢
  exact Ideal.isAssociatedToModule_maximalIdeal_atPrime hp

/-- Lemma 10.63.15 (2): if `p` is finitely generated and the maximal ideal of `R_p` is associated
to `M_p` in the textbook exact-annihilator sense, then `p` is associated to `M`. -/
theorem mem_associatedPrimesOfModule_of_mem_associatedPrimesOfModule_atPrime_of_fg
    {p : Ideal R} [p.IsPrime]
    (hp :
      maximalIdeal (Localization.AtPrime p) ∈
        associatedPrimesOfModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M))
    (hfg : p.FG) :
    p ∈ associatedPrimesOfModule R M := by
  rw [mem_associatedPrimesOfModule_iff] at hp ⊢
  exact Ideal.isAssociatedToModule_of_isAssociatedToModule_maximalIdeal_atPrime_of_fg hp hfg

end
