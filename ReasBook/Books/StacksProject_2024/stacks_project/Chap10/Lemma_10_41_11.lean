import Mathlib
import StacksProject_2024.Chap10.Definition_10_41_1

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {p : Ideal R} [p.IsPrime] {q : Ideal S} [q.IsPrime] [q.LiesOver p]

local notation "Sₚ" => Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
local notation "T" => Algebra.algebraMapSubmonoid S p.primeCompl

/- Domain triage:
* primary domain: localization at primes in a commutative-algebra extension, with prime fibers
  controlled by going up / going down;
* owner abstractions: `IsLocalization.AtPrime` for the target local ring structure, together with
  `Ideal.LiesOver`, `Ideal.primesOver`, `SpecializingMap (PrimeSpectrum.comap (algebraMap R S))`,
  and `Algebra.HasGoingDown R S` for the prime-lifting hypotheses;
* sampled canonical declarations:
  `Definition_10_41_1`'s recall shape for going up,
  `Ideal.exists_ideal_le_liesOver_of_le`,
  `IsLocalization.of_le_of_exists_dvd`,
  and `Ideal.primesOver`;
* layer: `bridge/view`, since this item proves that the localization of `S` away from `p`
  coincides with the canonical owner object `IsLocalization.AtPrime ... q` under unique lifting
  hypotheses, without introducing new source-facing data.

Primitive-vs-derived split:
* primitive data: the ambient algebra `R → S`, the chosen primes `p` and `q`, and the localization
  ring `Sₚ`;
* derived API: the comparison lemmas showing `Sₚ` is the localization of `S` at `q` under the
  going-up or going-down uniqueness hypotheses.
-/

omit [p.IsPrime] in
private theorem eq_of_subsingleton_primesOver
    (hunique : Subsingleton (p.primesOver S)) {Q Q' : Ideal S} [Q.IsPrime] [Q'.IsPrime]
    [Q.LiesOver p] [Q'.LiesOver p] :
    Q = Q' := by
  exact congrArg Subtype.val <|
    show (primesOver.mk p Q : p.primesOver S) = primesOver.mk p Q' from
      Subsingleton.elim _ _

private theorem le_of_under_le_of_unique_liesOver_of_goingUp
    (hgu : SpecializingMap (PrimeSpectrum.comap (algebraMap R S)))
    (hunique : Subsingleton (p.primesOver S)) {Q : Ideal S} [Q.IsPrime] (hQp : Q.under R ≤ p) :
    Q ≤ q := by
  have hspec :
      PrimeSpectrum.comap (algebraMap R S) ⟨Q, inferInstance⟩ ⤳
        (⟨p, inferInstance⟩ : PrimeSpectrum R) := by
    rw [← PrimeSpectrum.le_iff_specializes]
    simpa [Ideal.under_def] using hQp
  obtain ⟨Q', hQQ', hQ'p⟩ := hgu hspec
  letI : Q'.asIdeal.LiesOver p := (Ideal.liesOver_iff _ _).2 <| by
    simpa [Ideal.under_def] using (congrArg PrimeSpectrum.asIdeal hQ'p).symm
  have hQ'q : Q'.asIdeal = q := eq_of_subsingleton_primesOver hunique
  have hQle : Q ≤ Q'.asIdeal := by
    simpa using (PrimeSpectrum.le_iff_specializes _ _).mpr hQQ'
  simpa [hQ'q] using hQle

private theorem le_of_under_le_of_unique_liesOver_of_goingDown
    [Algebra.HasGoingDown R S]
    (hunique : ∀ p' : Ideal R, p'.IsPrime → Subsingleton (p'.primesOver S))
    {Q : Ideal S} [Q.IsPrime] (hQp : Q.under R ≤ p) :
    Q ≤ q := by
  let p' : Ideal R := Q.under R
  letI : p'.IsPrime := inferInstance
  obtain ⟨Q', hQ'q, hQ'⟩ := Ideal.exists_ideal_le_liesOver_of_le q hQp
  rcases hQ' with ⟨hQ'prime, hQ'p'⟩
  letI : Q'.IsPrime := hQ'prime
  letI : Q'.LiesOver p' := hQ'p'
  letI : Q.LiesOver p' := Ideal.over_under Q
  have hQ'Q : Q' = Q := eq_of_subsingleton_primesOver (hunique p' inferInstance)
  simpa [hQ'Q] using hQ'q

omit [q.IsPrime] [q.LiesOver p] in
private theorem exists_mem_T_dvd_of_notMem_of_under_le
    (hle : ∀ {Q : Ideal S}, Q.IsPrime → Q.under R ≤ p → Q ≤ q) {x : S} (hx : x ∉ q) :
    ∃ t ∈ T, x ∣ t := by
  by_contra! h
  have hdisj : Disjoint ((Ideal.span {x} : Ideal S) : Set S) T := by
    rw [Set.disjoint_left]
    intro y hyx hyT
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hyx
    exact h _ hyT ⟨c, mul_comm _ _⟩
  obtain ⟨Q, hQprime, hxQ, hQdisj⟩ :=
    Ideal.exists_le_prime_disjoint (.span {x}) T hdisj
  letI : Q.IsPrime := hQprime
  have hQp : Q.under R ≤ p := by
    intro r hrQ
    by_contra hrp
    exact Set.subset_compl_iff_disjoint_right.mpr hQdisj hrQ ⟨r, hrp, rfl⟩
  exact hx <| hle hQprime hQp <| hxQ (Ideal.mem_span_singleton_self x)

private theorem isLocalization_primeCompl_of_under_le
    (hle : ∀ {Q : Ideal S}, Q.IsPrime → Q.under R ≤ p → Q ≤ q) :
    IsLocalization.AtPrime Sₚ q := by
  have hTq : T ≤ q.primeCompl := by
    intro y hy hyq
    exact (Set.disjoint_left.mp <| Ideal.disjoint_primeCompl_of_liesOver q p) hy hyq
  refine IsLocalization.of_le_of_exists_dvd T q.primeCompl hTq ?_
  intro y hy
  exact exists_mem_T_dvd_of_notMem_of_under_le hle hy

/-- Lemma 10.41.11 (1): if the fiber `p.primesOver S` is a subsingleton and `R → S` satisfies
going up, then localizing `S` away from `p` is the localization of `S` at `q`. -/
-- Proof sketch: every prime of `Sₚ` contracts to a prime below `p`; apply going up to lift it to
-- a prime of `S` over `p`, then use uniqueness of the prime above `p` to identify that lift with
-- `q`. This forces every prime of `Sₚ` to lie under `q`, which is the criterion for localizing at
-- `q.primeCompl`.
theorem isLocalization_primeCompl_of_unique_liesOver_of_goingUp
    (hgu : SpecializingMap (PrimeSpectrum.comap (algebraMap R S)))
    (hunique : Subsingleton (p.primesOver S)) :
    IsLocalization.AtPrime Sₚ q := by
  refine isLocalization_primeCompl_of_under_le ?_
  intro Q hQprime hQp
  letI : Q.IsPrime := hQprime
  exact le_of_under_le_of_unique_liesOver_of_goingUp hgu hunique hQp

/-- Lemma 10.41.11 (2): if `q` lies over `p`, `R → S` satisfies going down, and every prime of
`R` has at most one prime of `S` lying over it, then localizing `S` away from `p` is the
localization of `S` at `q`. -/
-- Proof sketch: for a prime of `Sₚ`, view its corresponding prime of `S` and contract it to
-- `R`. Use going down from `q` to produce a prime of `S` over that contraction contained in `q`;
-- fiberwise uniqueness then identifies this descended prime with the given one, so the latter lies
-- under `q`. Hence `Sₚ` localizes `S` at `q.primeCompl`.
theorem isLocalization_primeCompl_of_unique_liesOver_of_goingDown
    [Algebra.HasGoingDown R S]
    (hunique : ∀ p' : Ideal R, p'.IsPrime → Subsingleton (p'.primesOver S)) :
    IsLocalization.AtPrime Sₚ q := by
  refine isLocalization_primeCompl_of_under_le ?_
  intro Q hQprime hQp
  letI : Q.IsPrime := hQprime
  exact le_of_under_le_of_unique_liesOver_of_goingDown hunique hQp

end
