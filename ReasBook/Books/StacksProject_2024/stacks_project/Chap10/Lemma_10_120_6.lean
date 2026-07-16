import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_120_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]

open Ideal

/- Lemma 10.120.6 lies in the commutative-algebra domain of UFDs, height-one prime ideals, and
Krull height theory.

Domain-style sampling:
- `UniqueFactorizationMonoid` is the `core/canonical` owner abstraction for factoriality.
- `UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime` is the owner bridge from UFDs to
  prime elements inside nonzero prime ideals.
- `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes` and
  `Ideal.mem_minimalPrimes_of_height_eq` are the canonical height/minimal-prime tools for the
  principal-ideal theorem step.
- `Ideal.span_singleton_prime` and `Ideal.span_singleton_generator` are the canonical bridge from a
  prime principal ideal back to a prime element.

Layer triage:
- `source-facing`: the textbook equivalence between UFDs and principal height-one primes.
- `core/canonical`: `UniqueFactorizationMonoid`.
- `bridge/view`: the proof passes through prime elements in prime ideals and through minimal-prime
  height control, but introduces no extra wrapper API.

Primitive data are only the ambient ring hypotheses and the `UniqueFactorizationMonoid R`
structure when present. The height-one-principal condition and the principal generators used in the
proof are derived API, so this file should remain a short source-facing theorem built directly from
the owner abstractions rather than introducing local wrappers. -/
/-- Lemma 10.120.6: a Noetherian domain is a unique factorization domain if and only if every
prime ideal of height `1` is principal. -/
-- Proof sketch: if `R` is a UFD and `p` has height `1`, choose a nonzero element of `p`, factor it
-- into irreducibles, and use primality of `p` together with `Lemma 10.120.5` to find a prime
-- irreducible whose principal ideal equals `p`. Conversely, assume every height-one prime is
-- principal. By Noetherianity every nonzero nonunit factors into irreducibles, so by
-- `Lemma 10.120.5` it is enough to show irreducibles are prime. For an irreducible `x`, choose a
-- prime minimal over `(x)`, apply Krull's principal ideal theorem to see that this prime has
-- height `1`, use the hypothesis to make it principal, and conclude that `(x)` itself is prime.
theorem uniqueFactorizationMonoid_iff_forall_height_one_prime_isPrincipal :
    UniqueFactorizationMonoid R ↔
      ∀ p : Ideal R, p.IsPrime → p.height = 1 → p.IsPrincipal := by
  have hbot_height : (⊥ : Ideal R).height = 0 := by
    rw [Ideal.height_eq_primeHeight, Ideal.primeHeight_eq_zero_iff,
      IsDomain.minimalPrimes_eq_singleton_bot]
    simp
  have hbot_primeHeight : (⊥ : Ideal R).primeHeight = 0 := by
    simpa [Ideal.height_eq_primeHeight] using hbot_height
  constructor
  · intro hufd p hp hheight
    letI := hufd
    have hp_ne_bot : p ≠ ⊥ := by
      intro hbot
      simp [hbot, hbot_height] at hheight
    obtain ⟨x, hxmem, hxprime⟩ := hp.exists_mem_prime_of_ne_bot hp_ne_bot
    have hxp : Ideal.span {x} ≤ p := (Ideal.span_singleton_le_iff_mem p).2 hxmem
    have hxspan_prime : (Ideal.span {x}).IsPrime :=
      (Ideal.span_singleton_prime hxprime.ne_zero).2 hxprime
    letI : (Ideal.span {x}).IsPrime := hxspan_prime
    have hxspan_mem : Ideal.span {x} ∈ (Ideal.span {x}).minimalPrimes := by
      simp [Ideal.minimalPrimes_eq_subsingleton_self]
    have hxspan_height_le : (Ideal.span {x}).height ≤ 1 :=
      Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) (Ideal.span {x})
        hxspan_mem
    have hbot_lt : (⊥ : Ideal R) < Ideal.span {x} := by
      refine bot_lt_iff_ne_bot.2 ?_
      simpa [Ideal.span_singleton_eq_bot] using hxprime.ne_zero
    have hxspan_height_ge : 1 ≤ (Ideal.span {x}).height := by
      have := Ideal.primeHeight_add_one_le_of_lt hbot_lt
      simpa [hbot_primeHeight, Ideal.height_eq_primeHeight] using this
    have hxspan_height : (Ideal.span {x}).height = 1 :=
      le_antisymm hxspan_height_le hxspan_height_ge
    haveI : p.FiniteHeight := by
      rw [Ideal.finiteHeight_iff]
      right
      rw [hheight]
      simp
    have hp_min : p ∈ (Ideal.span {x}).minimalPrimes :=
      Ideal.mem_minimalPrimes_of_height_eq hxp (by simp [hheight, hxspan_height])
    have hp_eq : p = Ideal.span {x} := by
      simpa [Ideal.minimalPrimes_eq_subsingleton_self] using hp_min
    exact hp_eq ▸ inferInstance
  · intro hprincipal
    refine
      (uniqueFactorizationMonoid_iff_forall_irreducible_prime_of_exists_irreducible_factorization
        ?_).2 ?_
    · intro a ha0 haunit
      let _ : WfDvdMonoid R :=
        WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt Ideal.setOf_isPrincipal_wellFoundedOn_gt
      obtain ⟨f, hf, hprod, _⟩ := (WfDvdMonoid.not_unit_iff_exists_factors_eq a ha0).1 haunit
      exact ⟨f, hf, hprod⟩
    · intro x hx
      have hspan_ne_top : Ideal.span {x} ≠ ⊤ := Ideal.span_singleton_ne_top hx.not_isUnit
      obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hspan_ne_top
      have hp_prime : p.IsPrime := Ideal.minimalPrimes_isPrime hp
      letI : p.IsPrime := hp_prime
      have hx_mem_p : x ∈ p := hp.1.2 (Ideal.mem_span_singleton_self x)
      have hp_ne_bot : p ≠ ⊥ := by
        intro hbot
        exact hx.ne_zero (by simpa [hbot] using hx_mem_p)
      have hbot_lt : (⊥ : Ideal R) < p := bot_lt_iff_ne_bot.2 hp_ne_bot
      have hp_height_le : p.height ≤ 1 :=
        Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) p hp
      have hp_height_ge : 1 ≤ p.height := by
        have := Ideal.primeHeight_add_one_le_of_lt hbot_lt
        simpa [hbot_primeHeight, Ideal.height_eq_primeHeight] using this
      have hp_height : p.height = 1 := le_antisymm hp_height_le hp_height_ge
      letI : p.IsPrincipal := hprincipal p hp_prime hp_height
      let y : R := Submodule.IsPrincipal.generator p
      have hy_span : Ideal.span {y} = p := Ideal.span_singleton_generator p
      have hy_ne_zero : y ≠ 0 := by
        intro hy0
        apply hp_ne_bot
        rw [← hy_span, Ideal.span_singleton_eq_bot.2 hy0]
      have hy_prime : Prime y :=
        (Ideal.span_singleton_prime hy_ne_zero).1 (hy_span ▸ hp_prime)
      have hy_dvd_x : y ∣ x := by
        rw [← Ideal.mem_span_singleton, hy_span]
        exact hx_mem_p
      have hxy : Associated y x := hy_prime.irreducible.associated_of_dvd hx hy_dvd_x
      have hx_span_prime : (Ideal.span {x}).IsPrime := by
        rw [Ideal.span_singleton_eq_span_singleton.2 hxy.symm]
        exact hy_span ▸ hp_prime
      exact (Ideal.span_singleton_prime hx.ne_zero).1 hx_span_prime

end
