import Mathlib
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_120_1 (from Chap10) -/
/- Domain triage:
- primary domain: commutative algebra of associated, irreducible, and prime elements, together
  with the principal-ideal reformulation of primality;
- sampled owner declarations: `Associated`, `Irreducible`, `Prime`,
  and `Ideal.span_singleton_prime`;
- best owner abstraction: the mathlib owners `Associated`, `Irreducible`, and `Prime`, with the
  bridge to prime principal ideals given by `Ideal.span_singleton_prime`;
- layer: `core/canonical`, since Definition 10.120.1 is only recalling standard owner notions
  already present in mathlib;
- primitive data: an ambient monoid or commutative monoid with zero element;
- derived API: the principal-ideal characterization of prime elements.
-/

/- Definition 10.120.1 is a `core/canonical` recall item: the textbook notions of associated
elements, irreducible elements, and prime elements are already owned in mathlib by
`Associated`, `Irreducible`, and `Prime`, and the principal-ideal reformulation of prime elements
is the canonical theorem `Ideal.span_singleton_prime`. -/
recall Associated
recall Irreducible
recall Prime
recall Ideal.span_singleton_prime

/-! ### Lemma_10_120_2 (from Chap10) -/
/- Lemma 10.120.2: for a domain `R` and elements `x y : R`, the elements `x` and `y` are
associates if and only if the principal ideals `(x)` and `(y)` coincide. In Lean this is the
canonical theorem `Ideal.span_singleton_eq_span_singleton`, where `(x)` is written as
`Ideal.span ({x} : Set R)`. -/
recall Ideal.span_singleton_eq_span_singleton

/-! ### Lemma_10_120_3 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R] [IsDomain R]

/- Lemma 10.120.3 lives in factorization theory for domains with ACCP.

Domain-style sampling:
- `WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt` is the owner bridge from ACCP on principal
  ideals to the canonical `WfDvdMonoid` abstraction.
- `WfDvdMonoid.not_unit_iff_exists_factors_eq` is the owner theorem producing irreducible
  factorizations.
- `Ideal.setOf_isPrincipal_wellFoundedOn_gt` is the converse translation back to principal ideals.

Layer triage:
- `source-facing`: this lemma is the textbook ACCP specialization for domains.
- `core/canonical`: `WfDvdMonoid` and its factorization API.
- `bridge/view`: the ACCP hypothesis is converted to the owner abstraction; the output should stay
  in the owner theorem's canonical `Multiset` form rather than a local subtype wrapper. -/
/-- Lemma 10.120.3: if a domain satisfies the ascending chain condition on principal ideals,
then every nonzero nonunit element admits a factorization into irreducible elements whose
nonemptiness is forced by the nonunit hypothesis. -/
-- Proof sketch: use `WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt` to turn the ACC
-- hypothesis on principal ideals into a `WfDvdMonoid R` structure, then apply
-- `WfDvdMonoid.not_unit_iff_exists_factors_eq` to the given nonzero nonunit element; the
-- resulting factor multiset is automatically nonempty, since the empty product is a unit.
theorem exists_irreducible_factorization_of_accp
    (hacc : {I : Ideal R | I.IsPrincipal}.WellFoundedOn (· > ·))
    {a : R} (ha0 : a ≠ 0) (ha : ¬ IsUnit a) :
    ∃ f : Multiset R, (∀ b ∈ f, Irreducible b) ∧ f.prod = a := by
  -- Convert the ACCP hypothesis into the canonical well-founded divisibility structure.
  let _ : WfDvdMonoid R := WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt hacc
  -- Apply the owner factorization theorem and drop the extra nonemptiness conclusion.
  obtain ⟨f, hf, hprod, _⟩ := (WfDvdMonoid.not_unit_iff_exists_factors_eq a ha0).1 ha
  exact ⟨f, hf, hprod⟩

end

/-! ### Definition_10_120_4 (from Chap10) -/
/- Definition 10.120.4 is a `core/canonical` recall item: the textbook notion of a unique
factorization domain is owned in mathlib by `UniqueFactorizationMonoid`. For a domain `R`, this
packages existence and uniqueness of irreducible factorizations up to reordering and associates. -/
recall UniqueFactorizationMonoid

/- Companion recall: `UniqueFactorizationMonoid.exists_prime_factors` is derived API from the owner
class; it produces prime factors whose product is associated to the given nonzero element. -/
recall UniqueFactorizationMonoid.exists_prime_factors

/- Companion recall: `UniqueFactorizationMonoid.factors_unique` is the derived uniqueness theorem
comparing two irreducible factorizations via `Multiset.Rel Associated`. -/
recall UniqueFactorizationMonoid.factors_unique

/-! ### Lemma_10_120_5 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R] [IsDomain R]

/- Lemma 10.120.5 lives in commutative factorization theory for domains.

Domain-style sampling:
- `UniqueFactorizationMonoid` is the `core/canonical` owner abstraction for unique factorization.
- `UniqueFactorizationMonoid.irreducible_iff_prime` is the owner theorem identifying
  irreducibles with primes inside a UFD.
- `UniqueFactorizationMonoid.of_exists_prime_factors` is the owner constructor from existence of
  prime factorizations.
- `exists_irreducible_factorization_of_accp` is the earlier chapter bridge producing the
  source-facing factorization hypothesis used here.

Layer triage:
- `source-facing`: the hypothesis that every nonzero nonunit factors into irreducibles.
- `core/canonical`: `UniqueFactorizationMonoid`.
- `bridge/view`: this lemma upgrades the source-facing factorization hypothesis to the owner
  abstraction once irreducibles are known to be prime. -/
/-- A domain has irreducible factorizations if every nonzero nonunit element is a product of
irreducible elements. -/
def HasIrreducibleFactorizations (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∀ a : R, a ≠ 0 → ¬ IsUnit a →
    ∃ f : Multiset R, (∀ b ∈ f, Irreducible b) ∧ f.prod = a

/-- Lemma 10.120.5: in an integral domain where every nonzero nonunit admits a
factorization into irreducibles, being a unique factorization domain is equivalent to every
irreducible element being prime. -/
-- Proof sketch: for the forward implication, use
-- `UniqueFactorizationMonoid.irreducible_iff_prime`. For the reverse implication, turn the given
-- irreducible factorization of each nonzero nonunit into a prime factorization using the
-- hypothesis that irreducibles are prime, then apply
-- `UniqueFactorizationMonoid.of_exists_prime_factors`.
theorem uniqueFactorizationMonoid_iff_forall_irreducible_prime_of_exists_irreducible_factorization
    (hfactor : HasIrreducibleFactorizations R) :
    UniqueFactorizationMonoid R ↔ ∀ a : R, Irreducible a → Prime a := by
  constructor
  · intro hufd a ha
    letI := hufd
    exact UniqueFactorizationMonoid.irreducible_iff_prime.mp ha
  · intro hirrPrime
    exact UniqueFactorizationMonoid.of_exists_prime_factors fun a ha ↦ by
      by_cases hua : IsUnit a
      · exact ⟨∅, by simpa using (associated_one_iff_isUnit.2 hua).symm⟩
      · obtain ⟨f, hf, hprod⟩ := hfactor a ha hua
        refine ⟨f, ?_, ?_⟩
        · intro b hb
          exact hirrPrime b (hf b hb)
        · simp [hprod]

end

/-! ### Lemma_10_120_6 (from Chap10) -/
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

/-! ### Lemma_10_120_7_Nagata_s_criterion_for_factoriality (from Chap10) -/
universe u

/-
Lemma 10.120.7 lies in commutative factorization theory for domains and their localizations.

Domain-style sampling:
- `UniqueFactorizationMonoid` is the `core/canonical` owner abstraction for factoriality.
- `Submonoid.closure` is the canonical owner abstraction for a submonoid generated by a set.
- `Submonoid.exists_multiset_of_mem_closure` is the derived bridge from closure-membership to a
  finite product expression.
- `uniqueFactorizationMonoid_iff_forall_irreducible_prime_of_exists_irreducible_factorization` is
  the earlier chapter bridge from source-facing irreducible factorizations to the owner
  abstraction.

Layer triage:
- `source-facing`: the localization comparison lemmas and Nagata criterion below.
- `core/canonical`: `UniqueFactorizationMonoid` together with `Submonoid.closure {p | Prime p}`.
- `bridge/view`: the finite prime-factorization lemma for an element of the given submonoid. -/

namespace Submonoid

/-- If a submonoid is generated by prime elements, every element of it admits a factorization into
prime elements. -/
-- Proof sketch: apply the canonical closure-to-product bridge
-- `Submonoid.exists_multiset_of_mem_closure` to the inclusion
-- `S ≤ Submonoid.closure {p : A | Prime p}`.
theorem exists_prime_factorization {A : Type u} [CommRing A] {S : Submonoid A}
    (hS : S ≤ Submonoid.closure {p : A | Prime p}) (s : S) :
    ∃ f : Multiset A, (∀ p ∈ f, Prime p) ∧ ↑s = f.prod := by
  simpa [eq_comm] using Submonoid.exists_multiset_of_mem_closure (hS s.2)

end Submonoid

section

variable {A : Type u} [CommRing A] [IsDomain A] {S : Submonoid A}

/-- Helper for Lemma 10.120.7 (Nagata's criterion for factoriality): every element of a
multiplicative set generated by prime elements is a non-zero-divisor. -/
-- We first factor an element of `S` into prime elements. Since prime elements are nonzero in a
-- domain, their product is nonzero, hence belongs to `nonZeroDivisors A`.
lemma submonoid_le_nonZeroDivisors_of_prime_closure
    (hS : S ≤ Submonoid.closure {p : A | Prime p}) :
    S ≤ nonZeroDivisors A := by
  intro s hs
  obtain ⟨f, hfprime, hprod⟩ := Submonoid.exists_prime_factorization hS ⟨s, hs⟩
  have hs_ne_zero : s ≠ 0 := by
    have h0_not_mem : (0 : A) ∉ f := by
      intro h0
      exact (hfprime 0 h0).ne_zero rfl
    have hf_ne_zero : f.prod ≠ 0 := Multiset.prod_ne_zero h0_not_mem
    intro hs0
    have hprod_zero : f.prod = 0 := by
      simpa [hs0] using hprod.symm
    exact hf_ne_zero hprod_zero
  exact mem_nonZeroDivisors_of_ne_zero hs_ne_zero

/-- Helper for Lemma 10.120.7 (Nagata's criterion for factoriality): a localized fraction is a
unit whenever its numerator divides an element of the multiplicative set. -/
-- The image of a divisor of an element of `S` is a unit by the localization criterion, and the
-- denominator part `1 / s` is also a unit. Their product is the given fraction.
lemma isUnit_mk'_of_dvd_submonoid {a : A} {s : S}
    (ha : ∃ t : S, a ∣ (t : A)) :
    IsUnit (IsLocalization.mk' (Localization S) a s) := by
  rcases ha with ⟨t, ht⟩
  have ha_unit : IsUnit (algebraMap A (Localization S) a) := by
    exact (IsLocalization.algebraMap_isUnit_iff (M := S) (S := Localization S)).2 ⟨t, t.2, ht⟩
  have hs_unit : IsUnit (IsLocalization.mk' (Localization S) 1 s) := by
    refine isUnit_iff_exists_inv.mpr ?_
    refine ⟨IsLocalization.mk' (Localization S) (s : A) (1 : S), ?_⟩
    simpa using IsLocalization.mk'_mul_mk'_eq_one (S := Localization S) (1 : S) s
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  exact ha_unit.mul hs_unit

/-- Helper for Lemma 10.120.7 (Nagata's criterion for factoriality): after clearing a product of
prime denominators, one can peel those prime factors off the two sides of the equality. -/
-- We induct on the multiset of prime denominators. At each step, primality of the head factor
-- tells us which side it divides, and cancellation reduces the remaining product.
lemma split_product_after_clearing_prime_denominators :
    ∀ (f : Multiset A) {x a b : A},
      (∀ p ∈ f, Prime p) →
      f.prod * x = a * b →
      ∃ d₁ d₂ a' b' : A,
        f.prod = d₁ * d₂ ∧
        a = d₁ * a' ∧
        b = d₂ * b' ∧
        x = a' * b' := by
  intro f x a b
  revert x a b
  induction f using Multiset.induction_on with
  | empty =>
      intro x a b _ hEq
      -- With no denominator primes, the cleared equality already is the desired factorization.
      refine ⟨1, 1, a, b, by simp, by simp, by simp, ?_⟩
      simpa using hEq
  | @cons p f ih =>
      intro x a b hf hEq
      have hp : Prime p := hf p (Multiset.mem_cons_self _ _)
      have hf_tail : ∀ q ∈ f, Prime q := fun q hq => hf q (Multiset.mem_cons_of_mem hq)
      -- The head prime divides one of the two factors after clearing denominators.
      rw [Multiset.prod_cons, mul_assoc] at hEq
      have hp_dvd : p ∣ a * b := ⟨f.prod * x, by simpa [mul_assoc] using hEq.symm⟩
      rcases hp.dvd_or_dvd hp_dvd with hpa | hpb
      · rcases hpa with ⟨a₁, rfl⟩
        -- If the head prime divides `a`, cancel it and recurse on the tail product.
        have hcancel : f.prod * x = a₁ * b := by
          apply mul_left_cancel₀ hp.ne_zero
          simpa [mul_assoc, mul_left_comm, mul_comm] using hEq
        obtain ⟨d₁, d₂, a', b', hprod, ha, hb, hx⟩ := ih hf_tail hcancel
        refine ⟨p * d₁, d₂, a', b', ?_, ?_, hb, hx⟩
        · calc
            (p ::ₘ f).prod = p * f.prod := by simp [Multiset.prod_cons]
            _ = p * (d₁ * d₂) := by rw [hprod]
            _ = (p * d₁) * d₂ := by simp [mul_assoc]
        · calc
            p * a₁ = p * (d₁ * a') := by rw [ha]
            _ = (p * d₁) * a' := by simp [mul_assoc]
      · rcases hpb with ⟨b₁, rfl⟩
        -- If the head prime divides `b`, cancel it on that side and recurse symmetrically.
        have hcancel : f.prod * x = a * b₁ := by
          apply mul_left_cancel₀ hp.ne_zero
          simpa [mul_assoc, mul_left_comm, mul_comm] using hEq
        obtain ⟨d₁, d₂, a', b', hprod, ha, hb, hx⟩ := ih hf_tail hcancel
        refine ⟨d₁, p * d₂, a', b', ?_, ha, ?_, hx⟩
        · calc
            (p ::ₘ f).prod = p * f.prod := by simp [Multiset.prod_cons]
            _ = p * (d₁ * d₂) := by rw [hprod]
            _ = d₁ * (p * d₂) := by simp [mul_assoc, mul_left_comm, mul_comm]
        · calc
            p * b₁ = p * (d₂ * b') := by rw [hb]
            _ = (p * d₂) * b' := by simp [mul_assoc]

/-- Helper for Lemma 10.120.7 (Nagata's criterion for factoriality): from a cleared denominator
relation `s * a = x * y`, either one denominator prime is associated to the irreducible `x`, or
`x` already divides `a`. -/
-- Route correction: the induction carries an associated-prime witness, not `Prime x` itself.
-- If the head prime divides `x`, irreducibility identifies it with `x`; otherwise it divides `y`,
-- so we cancel it from the right side and recurse on the tail denominator product.
lemma associated_prime_factor_or_dvd_of_cleared_denominator_relation
    {x : A} (hx : Irreducible x) :
    ∀ (f : Multiset A) {a y : A},
      (∀ p ∈ f, Prime p) →
      f.prod * a = x * y →
      (∃ p ∈ f, Associated p x) ∨ x ∣ a := by
  intro f a y
  revert a y
  induction f using Multiset.induction_on with
  | empty =>
      intro a y _ hEq
      -- With no denominator primes left, the cleared equality directly shows `x ∣ a`.
      right
      refine ⟨y, ?_⟩
      simpa using hEq
  | @cons p f ih =>
      intro a y hf hEq
      have hp : Prime p := hf p (Multiset.mem_cons_self _ _)
      have hf_tail : ∀ q ∈ f, Prime q := fun q hq => hf q (Multiset.mem_cons_of_mem hq)
      -- The head prime divides the right-hand product `x * y`.
      rw [Multiset.prod_cons, mul_assoc] at hEq
      have hp_dvd : p ∣ x * y := ⟨f.prod * a, by simpa [mul_assoc] using hEq.symm⟩
      rcases hp.dvd_or_dvd hp_dvd with hpx | hpy
      · -- If the head prime divides `x`, irreducibility forces it to be associated to `x`.
        left
        exact ⟨p, Multiset.mem_cons_self _ _, hp.irreducible.associated_of_dvd hx hpx⟩
      · rcases hpy with ⟨y₁, rfl⟩
        -- Otherwise the head prime divides `y`, so cancel it and recurse on the tail.
        have hcancel : f.prod * a = x * y₁ := by
          apply mul_left_cancel₀ hp.ne_zero
          simpa [mul_assoc, mul_left_comm, mul_comm] using hEq
        rcases ih hf_tail hcancel with hAssoc | hdiv
        · left
          rcases hAssoc with ⟨q, hq, hqx⟩
          exact ⟨q, Multiset.mem_cons_of_mem hq, hqx⟩
        · right
          exact hdiv

/-- Helper for Lemma 10.120.7 (Nagata's criterion for factoriality): an element associated to a
prime element is itself prime. -/
-- The `Associated.prime_iff` bridge lets us postpone converting an associated witness to `Prime`
-- until the theorem-level endgame.
lemma prime_of_associated_prime_factor {x p : A} (hpx : Associated p x) (hp : Prime p) :
    Prime x := by
  simpa using (hpx.prime_iff).mp hp

/-- Helper for Lemma 10.120.7 (Nagata's criterion for factoriality): a localization factorization
of `x` clears to a ring equality once the localization map is known to be injective. -/
-- Route correction: the earlier adapter without a non-zero-divisor hypothesis was false for
-- trivial localizations. We first rewrite the factorization as an equality of two `mk'` terms, and
-- then use injectivity of the localization map to descend the cleared equality back to `A`.
lemma localization_factorization_clears_to_ring_equality
    (hNZ : S ≤ nonZeroDivisors A) {x a b : A} {s t : S}
    (h :
      algebraMap A (Localization S) x =
        IsLocalization.mk' (Localization S) a s * IsLocalization.mk' (Localization S) b t) :
    ((s : A) * t) * x = a * b := by
  -- Clear both denominators in the localization and then descend along injectivity.
  have hmk :
      IsLocalization.mk' (Localization S) x (1 : S) =
        IsLocalization.mk' (Localization S) (a * b) (s * t) := by
    rw [IsLocalization.mk'_one, IsLocalization.mk'_mul]
    exact h
  have hmap' :
      algebraMap A (Localization S) ((↑(s * t) : A) * x) =
        algebraMap A (Localization S) ((1 : A) * (a * b)) :=
    (IsLocalization.mk'_eq_iff_eq (S := Localization S)).1 hmk
  have hmap :
      algebraMap A (Localization S) (((s : A) * t) * x) =
        algebraMap A (Localization S) (a * b) := by
    simpa only [Submonoid.coe_mul, one_mul] using hmap'
  exact IsLocalization.injective (S := Localization S) hNZ hmap

/-- Helper for Lemma 10.120.7 (Nagata's criterion for factoriality): a prime element stays prime
after localization unless the localized principal ideal becomes the whole ring. -/
-- We split exactly as in the source proof's `S⁻¹(A/(x))` argument: either `(x)` is disjoint from
-- `S`, in which case its extension is prime, or `S` meets `(x)`, in which case the image of `x`
-- becomes a unit.
lemma prime_localizes_or_becomes_unit_of_prime
    (hS : S ≤ Submonoid.closure {p : A | Prime p}) {x : A} (hx : Prime x) :
    Prime (algebraMap A (Localization S) x) ∨ IsUnit (algebraMap A (Localization S) x) := by
  let hNZ : S ≤ nonZeroDivisors A := submonoid_le_nonZeroDivisors_of_prime_closure hS
  let I : Ideal A := Ideal.span ({x} : Set A)
  have hIprime : I.IsPrime := by
    simpa [I] using (Ideal.span_singleton_prime hx.ne_zero).2 hx
  by_cases hdisj : Disjoint (S : Set A) ↑I
  · -- When `S` misses `(x)`, localization preserves primality of the principal ideal.
    left
    have hx_map_ne_zero : algebraMap A (Localization S) x ≠ 0 := by
      intro hx0
      apply hx.ne_zero
      exact IsLocalization.injective (S := Localization S) hNZ (by simpa using hx0)
    have hmapPrime : (Ideal.map (algebraMap A (Localization S)) I).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint S (Localization S) I hIprime hdisj
    rw [← Ideal.span_singleton_prime hx_map_ne_zero]
    simpa [I, Ideal.map_span, Set.image_singleton] using hmapPrime
  · -- When `S` meets `(x)`, some denominator is divisible by `x`, so the image of `x` is a unit.
    right
    obtain ⟨s, hsS, hsI⟩ := Set.not_disjoint_iff.1 hdisj
    exact (IsLocalization.algebraMap_isUnit_iff (M := S) (S := Localization S)).2
      ⟨s, hsS, Ideal.mem_span_singleton.1 hsI⟩

/-- If `A` is a domain and `S` is a multiplicative subset generated by prime elements, then the
image of every irreducible `x : A` in `S⁻¹A` is irreducible or a unit. -/
-- Proof sketch: write a factorization of the image of `x` as fractions, clear denominators using
-- an element of `S`, factor that denominator into primes, and divide out the prime factors to
-- reduce to a factorization of `x` in `A`.
theorem localization_irreducible_or_isUnit_of_irreducible
    (hS : S ≤ Submonoid.closure {p : A | Prime p}) {x : A} (hx : Irreducible x) :
    Irreducible (algebraMap A (Localization S) x) ∨
      IsUnit (algebraMap A (Localization S) x) := by
  let hNZ : S ≤ nonZeroDivisors A := submonoid_le_nonZeroDivisors_of_prime_closure hS
  by_cases hu : IsUnit (algebraMap A (Localization S) x)
  · exact Or.inr hu
  · left
    refine ⟨hu, ?_⟩
    intro α β hmul
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq S α
    obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq S β
    -- Clear the localization equality back to an equality in `A`.
    have hclear :
        ((s : A) * t) * x = a * b := localization_factorization_clears_to_ring_equality
          (S := S) hNZ (x := x) (a := a) (b := b) (s := s) (t := t) (by
            simpa [IsLocalization.mk'_one] using hmul)
    obtain ⟨f, hfprime, hfprod⟩ := Submonoid.exists_prime_factorization hS (s * t)
    have hsplitEq : f.prod * x = a * b := by
      calc
        f.prod * x = (((s * t : S) : A)) * x := by rw [hfprod.symm]
        _ = a * b := by simpa [Submonoid.coe_mul] using hclear
    obtain ⟨d₁, d₂, a', b', hprod, ha, hb, hx'⟩ :=
      split_product_after_clearing_prime_denominators (x := x) (a := a) (b := b) f hfprime hsplitEq
    -- Descend to a factorization of `x` in `A`, then lift the unit factor back to the localization.
    rcases hx.isUnit_or_isUnit hx' with hua | hub
    · left
      have ha_dvd_d₁ : a ∣ d₁ := by
        rw [ha]
        exact (IsUnit.mul_right_dvd hua).2 (dvd_refl d₁)
      have hd₁_dvd_st : d₁ ∣ (((s * t : S) : A)) := ⟨d₂, by rw [hfprod, hprod]⟩
      exact isUnit_mk'_of_dvd_submonoid (S := S) (a := a) (s := s)
        ⟨s * t, dvd_trans ha_dvd_d₁ hd₁_dvd_st⟩
    · right
      have hb_dvd_d₂ : b ∣ d₂ := by
        rw [hb]
        exact (IsUnit.mul_right_dvd hub).2 (dvd_refl d₂)
      have hd₂_dvd_st : d₂ ∣ (((s * t : S) : A)) := by
        refine ⟨d₁, ?_⟩
        calc
          ((s * t : S) : A) = d₁ * d₂ := by rw [hfprod, hprod]
          _ = d₂ * d₁ := by simp [mul_comm]
      exact isUnit_mk'_of_dvd_submonoid (S := S) (a := b) (s := t)
        ⟨s * t, dvd_trans hb_dvd_d₂ hd₂_dvd_st⟩

/-- If `A` is a domain and `S` is a multiplicative subset generated by prime elements, then for
every irreducible `x : A`, the element `x` is prime if and only if its image in `S⁻¹A` is prime or
a unit. -/
-- Proof sketch: for the forward implication, localize the quotient criterion for primality; for
-- the reverse implication, use the previous denominator-clearing argument applied to relations
-- witnessing divisibility after localization.
theorem prime_iff_localization_prime_or_isUnit_of_irreducible
    (hS : S ≤ Submonoid.closure {p : A | Prime p}) {x : A} (hx : Irreducible x) :
    Prime x ↔ Prime (algebraMap A (Localization S) x) ∨
      IsUnit (algebraMap A (Localization S) x) := by
  let hNZ : S ≤ nonZeroDivisors A := submonoid_le_nonZeroDivisors_of_prime_closure hS
  constructor
  · intro hxPrime
    exact prime_localizes_or_becomes_unit_of_prime (S := S) hS hxPrime
  · rintro (hmapPrime | hmapUnit)
    · refine ⟨hx.ne_zero, hx.not_isUnit, ?_⟩
      intro a b hxab
      have hmap_dvd :
          algebraMap A (Localization S) x ∣
            algebraMap A (Localization S) a * algebraMap A (Localization S) b := by
        rcases hxab with ⟨y, hy⟩
        refine ⟨algebraMap A (Localization S) y, ?_⟩
        simpa [map_mul] using congrArg (algebraMap A (Localization S)) hy
      rcases hmapPrime.dvd_or_dvd hmap_dvd with hdivA | hdivB
      · rcases hdivA with ⟨z, hz⟩
        obtain ⟨y, s, rfl⟩ := IsLocalization.exists_mk'_eq S z
        -- Clear the localization divisibility witness `map a = map x * y / s`.
        have hclear :
            (s : A) * a = x * y := by
          have hclear' :
              ((((1 : S) : A) * s) * a) = x * y := localization_factorization_clears_to_ring_equality
                (S := S) hNZ (x := a) (a := x) (b := y) (s := (1 : S)) (t := s) (by
                  simpa [IsLocalization.mk'_one, map_mul, mul_comm, mul_left_comm, mul_assoc]
                    using hz)
          simpa using hclear'
        obtain ⟨f, hfprime, hfprod⟩ := Submonoid.exists_prime_factorization hS s
        have hsplitEq : f.prod * a = x * y := by
          calc
            f.prod * a = ((s : A) * a) := by rw [hfprod.symm]
            _ = x * y := by simpa using hclear
        rcases associated_prime_factor_or_dvd_of_cleared_denominator_relation
            (x := x) hx f hfprime hsplitEq with hAssoc | hxa
        · rcases hAssoc with ⟨p, hp_mem, hpx⟩
          have hp_dvd_s : p ∣ (s : A) := dvd_trans (Multiset.dvd_prod hp_mem) (dvd_of_eq hfprod.symm)
          have hx_dvd_s : x ∣ (s : A) := dvd_trans hpx.symm.dvd hp_dvd_s
          have hx_unit : IsUnit (algebraMap A (Localization S) x) :=
            (IsLocalization.algebraMap_isUnit_iff (M := S) (S := Localization S)).2 ⟨s, s.2, hx_dvd_s⟩
          exact False.elim (hmapPrime.not_unit hx_unit)
        · exact Or.inl hxa
      · rcases hdivB with ⟨z, hz⟩
        obtain ⟨y, s, rfl⟩ := IsLocalization.exists_mk'_eq S z
        -- The `b` branch is the symmetric cleared-denominator argument.
        have hclear :
            (s : A) * b = x * y := by
          have hclear' :
              ((((1 : S) : A) * s) * b) = x * y := localization_factorization_clears_to_ring_equality
                (S := S) hNZ (x := b) (a := x) (b := y) (s := (1 : S)) (t := s) (by
                  simpa [IsLocalization.mk'_one, map_mul, mul_comm, mul_left_comm, mul_assoc]
                    using hz)
          simpa using hclear'
        obtain ⟨f, hfprime, hfprod⟩ := Submonoid.exists_prime_factorization hS s
        have hsplitEq : f.prod * b = x * y := by
          calc
            f.prod * b = ((s : A) * b) := by rw [hfprod.symm]
            _ = x * y := by simpa using hclear
        rcases associated_prime_factor_or_dvd_of_cleared_denominator_relation
            (x := x) hx f hfprime hsplitEq with hAssoc | hxb
        · rcases hAssoc with ⟨p, hp_mem, hpx⟩
          have hp_dvd_s : p ∣ (s : A) := dvd_trans (Multiset.dvd_prod hp_mem) (dvd_of_eq hfprod.symm)
          have hx_dvd_s : x ∣ (s : A) := dvd_trans hpx.symm.dvd hp_dvd_s
          have hx_unit : IsUnit (algebraMap A (Localization S) x) :=
            (IsLocalization.algebraMap_isUnit_iff (M := S) (S := Localization S)).2 ⟨s, s.2, hx_dvd_s⟩
          exact False.elim (hmapPrime.not_unit hx_unit)
        · exact Or.inr hxb
    · -- If the localization image is a unit, `x` is associated to a denominator prime and hence prime.
      obtain ⟨s, hsS, hxs⟩ :=
        (IsLocalization.algebraMap_isUnit_iff (M := S) (S := Localization S)).1 hmapUnit
      obtain ⟨f, hfprime, hfprod⟩ := Submonoid.exists_prime_factorization hS ⟨s, hsS⟩
      rcases hxs with ⟨y, hy⟩
      have hclear : f.prod * (1 : A) = x * y := by
        calc
          f.prod * (1 : A) = s * 1 := by simpa using congrArg (fun z : A => z * (1 : A)) hfprod.symm
          _ = x * y := by simpa [hy, mul_comm, mul_left_comm, mul_assoc]
      rcases associated_prime_factor_or_dvd_of_cleared_denominator_relation
          (x := x) hx f hfprime hclear with hAssoc | hdivOne
      · rcases hAssoc with ⟨p, hp_mem, hpx⟩
        exact prime_of_associated_prime_factor hpx (hfprime p hp_mem)
      · exact False.elim (hx.not_isUnit (isUnit_of_dvd_one hdivOne))

/-- Helper for Lemma 10.120.7 (Nagata's criterion for factoriality): a nonzero element of `A`
admits a prime factorization after localization when `A` is a UFD. -/
-- We follow the source route on the numerator: induct on a prime factorization in `A`, and at
-- each prime step either keep the localized prime or discard it when it becomes a unit.
lemma localization_prime_factorization_of_nonzero
    (hS : S ≤ Submonoid.closure {p : A | Prime p}) [UniqueFactorizationMonoid A]
    {a : A} (ha : a ≠ 0) :
    ∃ g : Multiset (Localization S),
      (∀ q ∈ g, Prime q) ∧
      Associated g.prod (algebraMap A (Localization S) a) := by
  refine
    (UniqueFactorizationMonoid.induction_on_prime
      (P := fun a : A ↦ a ≠ 0 →
        ∃ g : Multiset (Localization S),
          (∀ q ∈ g, Prime q) ∧
          Associated g.prod (algebraMap A (Localization S) a))
      (a := a)
      ?_
      ?_
      ?_) ha
  · intro h0
    exact (h0 rfl).elim
  · intro x hxunit _
    -- A unit contributes no prime factors, and the empty product stays associated to its image.
    refine ⟨∅, by simp, ?_⟩
    simpa using
      (associated_one_iff_isUnit.2 (IsUnit.map (algebraMap A (Localization S)) hxunit)).symm
  · intro b p hb0 hp ih _
    obtain ⟨g, hgprime, hgassoc⟩ := ih hb0
    -- Route correction: at each prime step we use the earlier prime/unit comparison theorem
    -- instead of rebuilding a separate localization divisibility argument.
    have hp_local :
        Prime (algebraMap A (Localization S) p) ∨
          IsUnit (algebraMap A (Localization S) p) :=
      (prime_iff_localization_prime_or_isUnit_of_irreducible (S := S) hS hp.irreducible).1 hp
    rcases hp_local with hp_local_prime | hp_local_unit
    · refine ⟨algebraMap A (Localization S) p ::ₘ g, ?_, ?_⟩
      · intro q hq
        rcases Multiset.mem_cons.1 hq with rfl | hq
        · exact hp_local_prime
        · exact hgprime q hq
      · -- Keeping the localized prime prefixes the associated factorization by one prime factor.
        simpa [Multiset.prod_cons, map_mul, mul_assoc] using
          (Associated.mul_left (algebraMap A (Localization S) p) hgassoc)
    · refine ⟨g, hgprime, ?_⟩
      -- If the localized prime is a unit, the source proof discards it from the product.
      simpa [map_mul] using
        hgassoc.trans
          (associated_unit_mul_right
            (algebraMap A (Localization S) b)
            (algebraMap A (Localization S) p)
            hp_local_unit)

/-- Helper for Lemma 10.120.7 (Nagata's criterion for factoriality): every nonzero element of the
localization has a prime factorization up to associates when `A` is a UFD. -/
-- We represent a localization element by `a / s`, factor the numerator using the previous helper,
-- and discard the denominator because `1 / s` is a unit.
lemma localization_prime_factorization_up_to_associated
    (hS : S ≤ Submonoid.closure {p : A | Prime p}) [UniqueFactorizationMonoid A]
    {z : Localization S} (hz0 : z ≠ 0) :
    ∃ f : Multiset (Localization S), (∀ p ∈ f, Prime p) ∧ Associated f.prod z := by
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq S z
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hz0
    exact (IsLocalization.mk'_eq_zero_iff (S := Localization S) a s).2 ⟨1, by simpa [ha0]⟩
  obtain ⟨f, hfprime, hfassoc⟩ :=
    localization_prime_factorization_of_nonzero (S := S) hS ha0
  refine ⟨f, hfprime, ?_⟩
  have hs_unit : IsUnit (IsLocalization.mk' (Localization S) (1 : A) s) :=
    isUnit_mk'_of_dvd_submonoid (S := S) (a := (1 : A)) (s := s) ⟨s, one_dvd _⟩
  -- The denominator contributes only a unit factor, so the numerator factorization already
  -- controls the localization element up to associates.
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  exact (associated_mul_isUnit_right_iff hs_unit).2 hfassoc

/-- Lemma 10.120.7 (Nagata's criterion for factoriality): if `A` is a domain and `S` is a
multiplicative subset generated by prime elements, then `A` is a unique factorization domain if and
only if every nonzero nonunit of `A` factors into irreducibles and the localization `S⁻¹A` is a
unique factorization domain. -/
-- Proof sketch: combine parts (1) and (2) with Lemma 10.120.5, which identifies unique
-- factorization with existence of irreducible factorizations together with primality of
-- irreducibles.
theorem nagataCriterionForFactoriality
    (hS : S ≤ Submonoid.closure {p : A | Prime p}) :
    UniqueFactorizationMonoid A ↔
      HasIrreducibleFactorizations A ∧
      UniqueFactorizationMonoid (Localization S) := by
  constructor
  · intro hUFD
    letI := hUFD
    constructor
    · intro a ha hua
      -- The UFD structure gives an exact irreducible factorization of every nonzero nonunit.
      obtain ⟨f, hfirr, hprod, _⟩ :=
        (WfDvdMonoid.not_unit_iff_exists_factors_eq (a := a) ha).1 hua
      exact ⟨f, hfirr, hprod⟩
    · -- The forward localization step uses the source proof's numerator factorization helper.
      exact UniqueFactorizationMonoid.of_exists_prime_factors fun z hz0 ↦
        localization_prime_factorization_up_to_associated (S := S) hS hz0
  · rintro ⟨hfactor, hLocalizationUFD⟩
    refine
      (uniqueFactorizationMonoid_iff_forall_irreducible_prime_of_exists_irreducible_factorization
        (R := A) hfactor).2 ?_
    intro x hx
    -- The reverse direction packages the earlier localization comparison theorems through
    -- Lemma 10.120.5: localized irreducibles are prime in the localization or units, hence `x`
    -- itself is prime.
    have hx_local_irreducible_or_unit :
        Irreducible (algebraMap A (Localization S) x) ∨
          IsUnit (algebraMap A (Localization S) x) :=
      localization_irreducible_or_isUnit_of_irreducible (S := S) hS hx
    have hx_local_prime_or_unit :
        Prime (algebraMap A (Localization S) x) ∨
          IsUnit (algebraMap A (Localization S) x) := by
      rcases hx_local_irreducible_or_unit with hx_local_irreducible | hx_local_unit
      · left
        letI := hLocalizationUFD
        exact UniqueFactorizationMonoid.irreducible_iff_prime.mp hx_local_irreducible
      · exact Or.inr hx_local_unit
    exact
      (prime_iff_localization_prime_or_isUnit_of_irreducible (S := S) hS hx).2
        hx_local_prime_or_unit

end

/-! ### Lemma_10_120_8 (from Chap10) -/
/- Lemma 10.120.8 lies in the ACCP / factorization-theory domain for integral domains.

Domain-style sampling:
- `UniqueFactorizationMonoid` is the source hypothesis.
- `WfDvdMonoid` is the core owner abstraction for well-founded strict divisibility.
- `Ideal.setOf_isPrincipal_wellFoundedOn_gt` is the canonical bridge from that owner abstraction to
  the ascending chain condition on principal ideals.
- `WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt` is the converse bridge already used earlier
  in the chapter.

Layer triage:
- `source-facing`: the UFD implies ACCP corollary below.
- `core/canonical`: `WfDvdMonoid`.
- `bridge/view`: `Ideal.setOf_isPrincipal_wellFoundedOn_gt`.

Primitive data are exactly the `UniqueFactorizationMonoid R` instance; the principal-ideal
well-foundedness statement is derived API, so this file should reuse the owner bridge directly
rather than keep a parallel local proof wrapper. -/
/- Lemma 10.120.8: a unique factorization domain satisfies the ascending chain condition on
principal ideals. Mathlib's owner bridge is the more canonical theorem
`Ideal.setOf_isPrincipal_wellFoundedOn_gt`, stated for any `WfDvdMonoid` domain; the textbook UFD
case is its direct specialization via the canonical `UniqueFactorizationMonoid.toWfDvdMonoid`
instance. -/
recall Ideal.setOf_isPrincipal_wellFoundedOn_gt

/-! ### Lemma_10_120_9 (from Chap10) -/
open scoped Polynomial

universe u

section

variable {R : Type u} [CommRing R] [IsDomain R]

/- Lemma 10.120.9 lies in the ACCP / factorization-theory domain for integral domains.

Domain-style sampling:
- `WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt` is the owner bridge turning ACCP on
  principal ideals into the canonical well-founded divisibility abstraction.
- `Polynomial.wfDvdMonoid` is the canonical polynomial-ring instance for that owner abstraction.
- `Ideal.setOf_isPrincipal_wellFoundedOn_gt` transports the owner abstraction back to ACCP on
  principal ideals.

Layer triage:
- `source-facing`: the polynomial-stability statement below.
- `core/canonical`: `WfDvdMonoid`.
- `bridge/view`: the two principal-ideal well-foundedness theorems above.

Primitive data are just the ACCP hypothesis on `R`; the ACCP statement for `R[X]` is derived API
through the owner abstraction, so this file should reuse that owner bridge directly. -/
/-- Lemma 10.120.9: if a domain satisfies the ascending chain condition on principal ideals,
then the same property holds for its polynomial ring. -/
-- Proof sketch: convert the ACCP hypothesis on principal ideals in `R` into the canonical
-- `WfDvdMonoid R` structure using
-- `WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt`; then use the polynomial-ring instance
-- `Polynomial.wfDvdMonoid` and translate back to ACCP on principal ideals of `R[X]` via
-- `Ideal.setOf_isPrincipal_wellFoundedOn_gt`.
theorem polynomial_accp_of_accp
    (hacc : {I : Ideal R | I.IsPrincipal}.WellFoundedOn (· > ·)) :
    {I : Ideal R[X] | I.IsPrincipal}.WellFoundedOn (· > ·) := by
  -- Convert the ACCP hypothesis on `R` into the canonical well-founded divisibility structure.
  let hR : WfDvdMonoid R := WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt hacc
  -- Build the polynomial `WfDvdMonoid` instance explicitly to avoid broad typeclass search.
  let hRX : WfDvdMonoid R[X] := @Polynomial.wfDvdMonoid R inferInstance inferInstance hR
  -- Translate the owner abstraction back to ACCP on principal ideals of `R[X]`.
  exact @Ideal.setOf_isPrincipal_wellFoundedOn_gt (R[X]) inferInstance hRX inferInstance

end

/-! ### Lemma_10_120_10 (from Chap10) -/
universe u

/-
Domain-style sampling:
- primary domain: factorization theory for polynomial and multivariable polynomial rings over
  unique factorization domains;
- sampled owner API:
  `Polynomial.uniqueFactorizationMonoid`,
  `MvPolynomial.uniqueFactorizationMonoid`,
  `UniqueFactorizationMonoid.toWfDvdMonoid`,
  `PrincipalIdealRing.to_uniqueFactorizationMonoid`;
- source-facing: the textbook polynomial and finite-variable polynomial UFD statements below;
- core/canonical: the mathlib `UniqueFactorizationMonoid` instances on `Polynomial` and
  `MvPolynomial`;
- bridge/view: the second statement is the `Fin n` and `Field` specialization of the multivariable
  owner instance.

Primitive data are only the base-ring factorization hypotheses. The polynomial UFD structures are
derived API owned upstream, so this file should recall those owner instances directly and not keep
parallel local wrappers.
-/

section Polynomial

variable (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/- Lemma 10.120.10: a polynomial ring over a unique factorization domain is again a unique
factorization domain. This is exactly the canonical mathlib instance
`Polynomial.uniqueFactorizationMonoid`. -/
recall Polynomial.uniqueFactorizationMonoid

end Polynomial

section MvPolynomialField

variable (k : Type u) [Field k] (n : ℕ)

/- If `k` is a field, then `k[x_1, \ldots, x_n]`, formalized as `MvPolynomial (Fin n) k`, is a
unique factorization domain. This is the specialization of the canonical mathlib instance
`MvPolynomial.uniqueFactorizationMonoid` to a finite set of variables. -/
recall MvPolynomial.uniqueFactorizationMonoid

end MvPolynomialField

/-! ### Lemma_10_120_11 (from Chap10) -/
universe u

variable (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/- Lemma 10.120.11: a unique factorization domain is normal, i.e. it is integrally closed in
its fraction field. This is exactly the canonical mathlib instance
`UniqueFactorizationMonoid.instIsIntegrallyClosed`. -/
recall UniqueFactorizationMonoid.instIsIntegrallyClosed

/-! ### Definition_10_120_12 (from Chap10) -/
universe u

variable (R : Type u) [CommRing R]

/- Definition 10.120.12 is a `source-facing` item presented through the canonical mathlib owner:
there is no separate PID class in mathlib, and the textbook notion that `R` is a principal ideal
domain is expressed by the combined proposition `IsDomain R ∧ IsPrincipalIdealRing R`, usually
used via the typeclass context `[IsDomain R] [IsPrincipalIdealRing R]`. -/
#check (IsDomain R ∧ IsPrincipalIdealRing R)

section

variable [IsDomain R] [IsPrincipalIdealRing R]

/- Companion recall: the principal-ideal part of the PID hypothesis is owned by the canonical
mathlib class `IsPrincipalIdealRing R`. -/
recall IsPrincipalIdealRing

end

/-! ### Lemma_10_120_13 (from Chap10) -/
universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/- 
Domain-style sampling:
- primary domain: factorization theory for principal ideal domains and unique factorization domains;
- sampled owner API:
  `IsPrincipalIdealRing`,
  `UniqueFactorizationMonoid`,
  `PrincipalIdealRing.to_uniqueFactorizationMonoid`,
  `IsPrincipalIdealRing.isDedekindDomain`;
- source-facing: the textbook implication that a principal ideal domain is a unique factorization
  domain;
- core/canonical: the mathlib owner classes `IsPrincipalIdealRing` and `UniqueFactorizationMonoid`;
- bridge/view: the instance `PrincipalIdealRing.to_uniqueFactorizationMonoid`.

Primitive data are exactly the PID hypotheses `[IsDomain R] [IsPrincipalIdealRing R]`. The UFD
structure is derived API owned upstream, so this file should recall that owner instance directly
and not introduce any parallel wrapper or local restatement.
-/

/- Lemma 10.120.13: a principal ideal domain is a unique factorization domain. This is exactly the
canonical mathlib instance `PrincipalIdealRing.to_uniqueFactorizationMonoid`. -/
recall PrincipalIdealRing.to_uniqueFactorizationMonoid
