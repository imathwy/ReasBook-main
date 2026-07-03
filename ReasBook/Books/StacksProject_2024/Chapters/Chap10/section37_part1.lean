import Mathlib
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.Pi
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_37_1 (from Chap10) -/
universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/- Domain-style sampling for normal domains:
- primary domain: integrally closed domains in commutative algebra
- sampled owner declarations:
  `IsIntegrallyClosed`,
  `isIntegrallyClosed_iff_isIntegrallyClosedIn`,
  `IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn`,
  `isIntegrallyClosed_of_isLocalization`
- canonical owner abstraction: `IsIntegrallyClosed`
- primitive data: the ambient commutative-domain structure on `R`
- derived API: alternate fraction-field formulations, localization stability, and integral-closure
  transfer lemmas

Layer triage:
- `source-facing`: the Stacks definition that a domain is normal
- `core/canonical`: mathlib's `IsIntegrallyClosed`
- `bridge/view`: fraction-field and localization reformulations of integrally closedness

This numbered item adds no new data beyond the canonical owner, so keeping a chapter-local alias or
an `_iff` theorem as the main public entry would only duplicate the upstream API.
-/
/- Definition 10.37.1: a domain `R` is normal if it is integrally closed in its field of
fractions. This source-facing item is a direct recall of the mathlib owner predicate
`IsIntegrallyClosed R`; the primitive ambient data are just the commutative ring/domain
assumptions. -/
recall IsIntegrallyClosed

/-! ### Lemma_10_37_2 (from Chap10) -/
section

universe u v

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable [IsDomain S] [IsIntegrallyClosed S]

/- Lemma 10.37.2: if `S` is a normal domain, then the integral closure of `R` in `S` is a
normal domain. The primitive data here are only the canonical `R`-subalgebra
`integralClosure R S ⊆ S` and its inherited domain structure; the integrally closed conclusion is
derived, not packaged separately, and is exactly the owner theorem
`IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn` specialized to
`integralClosure R S ⊆ S`. Thus this item remains a direct canonical use of the upstream API,
rather than a parallel local wrapper. -/
#check IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn (integralClosure R S) S

end

/-! ### Definition_10_37_3 (from Chap10) -/
universe u v

section

variable {R : Type u} [CommRing R]
variable {K : Type v} [CommRing K] [Algebra R K]

/- Canonical reference: for an `R`-algebra `K`, the predicate `IsAlmostIntegral R : K → Prop`
expresses that an element of `K` is almost integral over `R`, meaning that some nonzero element
of `R` sends all powers of that element back into the image of `R`. -/
#check (IsAlmostIntegral R : K → Prop)

/- Definition 10.37.3: the owner object for complete normality is the canonical subalgebra
`completeIntegralClosure R K`. In the intended fraction-ring case, complete normality is the
assertion that this subalgebra is `⊥`, i.e. that every almost integral element already lies in the
image of `algebraMap R K`. -/
#check (completeIntegralClosure R K = ⊥)

-- Proof sketch: use `mem_completeIntegralClosure` to rewrite almost integrality as membership in
-- `completeIntegralClosure R K`, then rewrite the defining equality to `⊥` and use
-- `Algebra.mem_bot` to identify membership in `⊥` with lying in the image of `algebraMap`.
/-
Bridge/view: in any `R`-algebra `K`, the condition `completeIntegralClosure R K = ⊥` says exactly
that every almost integral element of `K` comes from the algebra map `R → K`. Applied to a
fraction ring of a domain, this is the source-facing definition of complete normality.
-/
theorem isCompletelyNormal_iff :
    completeIntegralClosure R K = ⊥ ↔
      ∀ x : K, IsAlmostIntegral R x → ∃ y : R, algebraMap R K y = x := by
  rw [eq_bot_iff]
  constructor
  · intro h x hx
    have hx' : x ∈ (⊥ : Subalgebra R K) := h <| by
      simpa [mem_completeIntegralClosure] using hx
    simpa [Algebra.mem_bot, Set.mem_range] using hx'
  · intro h x hx
    simpa [Algebra.mem_bot, Set.mem_range] using
      h x (by simpa [mem_completeIntegralClosure] using hx)

section

variable [IsFractionRing R K]

/-- In the intended domain setting, a completely normal ring is integrally closed. -/
theorem isIntegrallyClosed_of_isCompletelyNormal
    (h : completeIntegralClosure R K = ⊥) : IsIntegrallyClosed R := by
  refine (IsIntegrallyClosed.integralClosure_eq_bot_iff K).mp ?_
  apply le_bot_iff.mp
  simpa [h] using
    (show integralClosure R K ≤ completeIntegralClosure R K from
      integralClosure_le_completeIntegralClosure)

end
end

/-! ### Lemma_10_37_4 (from Chap10) -/
section

universe u v

variable {R : Type u} [CommRing R]
variable {K : Type v} [Field K] [Algebra R K]

/- Layering for this item:
* source-facing: closure of almost integral elements in the fraction field, together with the
  comparison between integral and almost integral elements;
* core/canonical owner: the subalgebra `completeIntegralClosure R K` and the predicates
  `IsAlmostIntegral R` and `IsIntegral R`;
* bridge/view: `mem_completeIntegralClosure`, which identifies the source-facing predicate with
  membership in the owner subalgebra.
-/

section

variable [IsDomain R] [IsFractionRing R K]

/- Lemma 10.37.4 (1): the sum of two almost integral elements is again almost integral. This is
the additive closure of the canonical owner object `completeIntegralClosure R K`. -/
#check
  (show ∀ u v : K, IsAlmostIntegral R u → IsAlmostIntegral R v → IsAlmostIntegral R (u + v) from
    fun _ _ ↦ (completeIntegralClosure R K).add_mem)

/- Lemma 10.37.4 (2): the product of two almost integral elements is again almost integral. This
is the multiplicative closure of the canonical owner object `completeIntegralClosure R K`. -/
#check
  (show ∀ u v : K, IsAlmostIntegral R u → IsAlmostIntegral R v → IsAlmostIntegral R (u * v) from
    fun _ _ ↦ (completeIntegralClosure R K).mul_mem)

end

/- Lemma 10.37.4 (3): an element of the fraction field that is integral over `R` is almost
integral over `R`. This is exactly the canonical mathlib theorem
`IsIntegral.isAlmostIntegral`, specialized to a domain `R` and its fraction field `K`. -/
recall IsIntegral.isAlmostIntegral

/- Lemma 10.37.4 (4): if `R` is Noetherian, then an element of the fraction field is almost
integral over `R` only if it is integral over `R`. This is exactly the canonical mathlib theorem
`IsAlmostIntegral.isIntegral`, specialized to a Noetherian domain `R` and its fraction field `K`.
-/
recall IsAlmostIntegral.isIntegral

end

/-! ### Lemma_10_37_5 (from Chap10) -/
/- Lemma 10.37.5: any localization of a normal domain is again normal. Since
`Definition 10.37.1` identifies normal domains with integrally closed domains, the owner
abstraction here is `IsIntegrallyClosed`; `IsLocalization M S` with `hM : M ≤ R⁰` is the
primitive localization data, and the normality/domain conclusions are derived canonically. -/
recall isIntegrallyClosed_of_isLocalization

/- Companion recall: under the same non-zero-divisor hypothesis, the localization is also a
domain via the canonical theorem `IsLocalization.isDomain_of_le_nonZeroDivisors`. -/
recall IsLocalization.isDomain_of_le_nonZeroDivisors

/-! ### Lemma_10_37_6 (from Chap10) -/
universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/- Lemma 10.37.6: a principal ideal domain is normal, i.e. it is integrally closed in its
fraction field. The owner abstraction here is the canonical typeclass `IsIntegrallyClosed R`,
while the primitive source data are just the PID hypotheses. A PID canonically carries a
`GCDMonoid` structure, so this is the direct upstream bridge `GCDMonoid.toIsIntegrallyClosed`. -/
recall GCDMonoid.toIsIntegrallyClosed

/-! ### Lemma_10_37_7 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Lemma 10.37.7 (1): if a polynomial `f ∈ K[X]` is integral over `R[X]`, then every coefficient
`αᵢ = f.coeff i` is integral over `R`. The owner abstraction is the canonical predicate
`IsIntegral R[X] f`, and the coefficientwise conclusion is exactly the derived theorem
`IsIntegral.coeff`; the textbook fraction-field case is its specialization. -/
recall IsIntegral.coeff

/- Lemma 10.37.7 (2): if a polynomial `f ∈ K[X]` is almost integral over `R[X]`, then every
coefficient `αᵢ = f.coeff i` is almost integral over `R`. Here the owner abstraction is
`IsAlmostIntegral R[X] f`, and the coefficient statement is exactly the canonical derived theorem
`IsAlmostIntegral.coeff`. -/
recall IsAlmostIntegral.coeff

end

/-! ### Lemma_10_37_8 (from Chap10) -/
universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]

/- Domain-style sampling for Lemma 10.37.8:
- primary domain: integrally closed domains and polynomial extensions in commutative algebra
- sampled owner declarations:
  `IsIntegrallyClosed`,
  `isIntegrallyClosed_iff_isIntegrallyClosedIn`,
  `IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn`,
  `instIsIntegrallyClosedPolynomialOfIsDomain`
- canonical owner abstraction: `IsIntegrallyClosed`
- primitive data: the ambient commutative-domain structure on `R` together with
  `[IsIntegrallyClosed R]`
- derived API: the induced integrally closed instance on `R[X]`

Layer triage:
- `source-facing`: the textbook assertion that a polynomial ring over a normal domain is normal
- `core/canonical`: the mathlib instance `instIsIntegrallyClosedPolynomialOfIsDomain`
- `bridge/view`: none; the source statement is already exactly owner-shaped

This numbered item adds no new data beyond the canonical owner instance, so a local theorem or
alias would only duplicate the upstream API.
-/
/- Lemma 10.37.8: if `R` is a normal domain, then the polynomial ring `R[X]` is again a normal
domain. By Definition 10.37.1, the owner notion of normality is `IsIntegrallyClosed`, and the
polynomial-ring conclusion is exactly the canonical derived instance
`instIsIntegrallyClosedPolynomialOfIsDomain : IsIntegrallyClosed (Polynomial R)`. -/
recall instIsIntegrallyClosedPolynomialOfIsDomain

/-! ### Lemma_10_37_9 (from Chap10) -/
open scoped PowerSeries

universe u

variable {R : Type u} [CommRing R]

section

variable [IsNoetherianRing R]

/- Lemma 10.37.9 (Noetherian part): if `R` is a Noetherian normal domain, then `R⟦X⟧` is
Noetherian. This is exactly the canonical mathlib instance on `R⟦X⟧`; the textbook's normality
assumptions are stronger than needed for this part. -/
recall PowerSeries.instIsNoetherianRing

end

section

variable [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

/- Layer triage for Lemma 10.37.9:
- the Noetherian statement above is a `core/canonical` recall from mathlib;
- the normal statement below is still `source-facing`, but its owner abstraction is the chapter
  notion `IsIntegrallyClosed` on the power series ring.

The primitive data are exactly the domain, Noetherian, and integrally closed hypotheses on `R`;
normality of `R⟦X⟧` is derived API. -/
/- Lemma 10.37.9 (normal part): if `R` is a Noetherian normal domain, then `R⟦X⟧` is normal.
By Definition 10.37.1, the canonical formulation of this part is the typeclass fact
`IsIntegrallyClosed R⟦X⟧`. -/
-- Proof sketch: write an integral element of the fraction field of `R⟦X⟧` as a Laurent
-- series, use almost integrality over the coefficient ring to show its lowest coefficient lies in
-- `R`, and iterate on higher coefficients to prove every coefficient lies in `R`.
instance : IsIntegrallyClosed R⟦X⟧ := sorry

end

/-! ### Lemma_10_37_10 (from Chap10) -/
universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-
Lemma 10.37.10 is a `source-facing` TFAE statement. Its `core/canonical` owner abstractions are
`IsIntegrallyClosed` for the global normal-domain clause and `IsNormalRing` for the all-prime
localization clause; the maximal-localization clause is the corresponding `bridge/view`.
-/
/-- Lemma 10.37.10: for a domain `R`, the following are equivalent: `R` is a normal domain, every
localization `Rₚ` at a prime ideal is a normal domain, and every localization `Rₘ` at a maximal
ideal is a normal domain. Using `Definition 10.37.1` and `Definition 10.37.11`, these are
expressed by `IsIntegrallyClosed R`, `IsNormalRing R`, and the corresponding maximal
localizations. -/
-- Proof sketch: the implication from `R` to all prime localizations is the canonical instance
-- `IsIntegrallyClosed R → IsNormalRing R`; maximal ideals are prime for the middle-to-last
-- implication; and the converse is the owner theorem
-- `IsIntegrallyClosed.of_isLocalization_maximal`.
theorem isIntegrallyClosed_tfae :
    List.TFAE
      [ IsIntegrallyClosed R
      , IsNormalRing R
      , ∀ m : MaximalSpectrum R, IsIntegrallyClosed (Localization.AtPrime m.asIdeal)
      ] := by
  tfae_have 1 → 2 := fun h ↦ by
    letI : IsIntegrallyClosed R := h
    infer_instance
  tfae_have 2 → 3 := fun h m ↦ by
    letI : IsNormalRing R := h
    exact isIntegrallyClosed_localizationAtPrime m.toPrimeSpectrum
  tfae_have 3 → 1 := fun h ↦
    IsIntegrallyClosed.of_isLocalization_maximal
      (fun p _ ↦ Localization.AtPrime p)
      fun p _ ↦ by
        simpa using h ⟨p, inferInstance⟩
  tfae_finish

/-! ### Definition_10_37_11 (from Chap10) -/
universe u

variable {R : Type u} [CommRing R]

/-
Definition 10.37.11 is `source-facing`: the chapter needs a ring-level owner predicate saying
that every prime localization is a normal domain. For each localization, the `core/canonical`
owner abstractions are mathlib's `IsDomain` and `IsIntegrallyClosed`; this file packages those
local conditions over all primes. The prime-spectrum and prime-ideal consequences below are
derived `bridge/view` API.
-/
/-- Definition 10.37.11: a commutative ring is normal if for every prime ideal `p`, the
localization `Localization.AtPrime p` is a normal domain. -/
class IsNormalRing (R : Type u) [CommRing R] : Prop where
  isNormalLocalizationAtPrime :
    ∀ p : PrimeSpectrum R,
      IsDomain (Localization.AtPrime p.asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime p.asIdeal)

/-- An integrally closed domain is a normal ring. -/
instance [IsDomain R] [IsIntegrallyClosed R] : IsNormalRing R where
  isNormalLocalizationAtPrime := fun p ↦ by
    refine ⟨?_, ?_⟩
    · exact IsLocalization.isDomain_of_atPrime (Localization.AtPrime p.asIdeal) p.asIdeal
    · letI : IsDomain (Localization.AtPrime p.asIdeal) :=
        IsLocalization.isDomain_of_atPrime (Localization.AtPrime p.asIdeal) p.asIdeal
      exact isIntegrallyClosed_of_isLocalization (Localization.AtPrime p.asIdeal)
        p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors

/-- A normal ring has domain localizations at all points of `PrimeSpectrum R`. -/
theorem isDomain_localizationAtPrime (p : PrimeSpectrum R) [IsNormalRing R] :
    IsDomain (Localization.AtPrime p.asIdeal) :=
  (IsNormalRing.isNormalLocalizationAtPrime p).1

/-- A normal ring has integrally closed localizations at all points of `PrimeSpectrum R`. -/
theorem isIntegrallyClosed_localizationAtPrime (p : PrimeSpectrum R) [IsNormalRing R] :
    IsIntegrallyClosed (Localization.AtPrime p.asIdeal) :=
  (IsNormalRing.isNormalLocalizationAtPrime p).2

instance [IsNormalRing R] : IsReduced R := by
  refine isReduced_ofLocalizationMaximal R fun p _ ↦ ?_
  let q : PrimeSpectrum R := ⟨p, inferInstance⟩
  letI : IsDomain (Localization.AtPrime p) := by
    simpa using isDomain_localizationAtPrime q
  infer_instance

attribute [instance] isDomain_localizationAtPrime isIntegrallyClosed_localizationAtPrime

/-- A normal ring has normal localizations at all prime ideals. -/
instance (p : Ideal R) [p.IsPrime] [IsNormalRing R] :
    IsDomain (Localization.AtPrime p) := by
  let q : PrimeSpectrum R := ⟨p, inferInstance⟩
  simpa using isDomain_localizationAtPrime q

/-- A normal ring has integrally closed localizations at all prime ideals. -/
instance (p : Ideal R) [p.IsPrime] [IsNormalRing R] :
    IsIntegrallyClosed (Localization.AtPrime p) := by
  let q : PrimeSpectrum R := ⟨p, inferInstance⟩
  simpa using isIntegrallyClosed_localizationAtPrime q

/-! ### Lemma_10_37_12 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R] [IsNormalRing R]

/- Lemma 10.37.12: a normal ring is integrally closed in its total ring of fractions.

This is a `bridge/view` item: the source-facing hypothesis is the project notion
`IsNormalRing R`, while the canonical owner abstraction for the conclusion is mathlib's
`IsIntegrallyClosed R`. The primitive data are the prime-localization normality conditions
packaged by `IsNormalRing`; integrally closedness in the total fraction ring is derived API. -/
-- Proof sketch: let `x` lie in the total ring of fractions of `R` and be integral over `R`.
-- For each prime ideal `p`, its image in `Localization.AtPrime p` is integral over that
-- localization, hence belongs to it because `IsNormalRing R` gives a normal domain there. The
-- corresponding denominator ideal is therefore not contained in any prime ideal, so it is the
-- unit ideal and `x` already lies in `R`.
/-- Helper for Lemma 10.37.12: a nonzerodivisor of `R` does not vanish in a prime localization. -/
lemma map_ne_zero_atPrime_of_mem_nonZeroDivisors (P : Ideal R) [P.IsPrime] {y : R}
    (hy : y ∈ nonZeroDivisors R) : algebraMap R (Localization.AtPrime P) y ≠ 0 := by
  intro hy0
  have hy0' : algebraMap R (Localization.AtPrime P) y = algebraMap R (Localization.AtPrime P) 0 := by
    simpa only [map_zero] using hy0
  obtain ⟨z, hz⟩ := (IsLocalization.eq_iff_exists P.primeCompl (Localization.AtPrime P)).mp hy0'
  have hzy : z.1 * y = 0 := by
    simp only [mul_zero] at hz
    exact hz
  have hz0 : z.1 = 0 := (mem_nonZeroDivisors_iff.mp hy).2 z.1 hzy
  exact z.2 <| by
    simpa [hz0] using (Ideal.zero_mem P)

/-- Helper for Lemma 10.37.12: package the denominator ideal of an element of the total
ring of fractions. -/
lemma denominator_ideal_spec (x : FractionRing R) :
    ∃ I : Ideal R, ∀ r : R,
      r ∈ I ↔ ∃ a : R,
        algebraMap R (FractionRing R) a =
          algebraMap R (FractionRing R) r * x := by
  let carrier : Set R := { r : R | ∃ a : R,
    algebraMap R (FractionRing R) a = algebraMap R (FractionRing R) r * x }
  have hzero : (0 : R) ∈ carrier := by
    -- The zero multiple of `x` is represented by zero.
    use 0
    simp
  have hadd : ∀ {r s : R}, r ∈ carrier → s ∈ carrier → r + s ∈ carrier := by
    intro r s hr hs
    rcases hr with ⟨a, ha⟩
    rcases hs with ⟨b, hb⟩
    -- The denominator ideal is closed under addition by adding numerators.
    use a + b
    calc
      algebraMap R (FractionRing R) (a + b)
          = algebraMap R (FractionRing R) a + algebraMap R (FractionRing R) b := by
              simp
      _ = algebraMap R (FractionRing R) r * x + algebraMap R (FractionRing R) s * x := by
            rw [ha, hb]
      _ = algebraMap R (FractionRing R) (r + s) * x := by
            simp [add_mul]
  have hsmul : ∀ {c r : R}, r ∈ carrier → c * r ∈ carrier := by
    intro c r hr
    rcases hr with ⟨a, ha⟩
    -- Multiplying a denominator witness by a scalar multiplies the numerator as well.
    use c * a
    calc
      algebraMap R (FractionRing R) (c * a)
          = algebraMap R (FractionRing R) c * algebraMap R (FractionRing R) a := by
              simp
      _ = algebraMap R (FractionRing R) c *
            (algebraMap R (FractionRing R) r * x) := by
              rw [ha]
      _ = algebraMap R (FractionRing R) (c * r) * x := by
            simp [mul_assoc]
  refine ⟨
    { carrier := carrier
      zero_mem' := hzero
      add_mem' := fun {a b} h₁ h₂ ↦ hadd h₁ h₂
      smul_mem' := fun {c r} h ↦ hsmul h },
    ?_⟩
  intro r
  rfl

/-- Helper for Lemma 10.37.12: the iterated localization of `Q(R)` at `P.primeCompl`
is also the localization of `R_P` at the image of `nonZeroDivisors R`. -/
lemma atPrime_totalFraction_isLocalization (P : Ideal R) [P.IsPrime] :
    IsLocalization (Algebra.algebraMapSubmonoid (Localization.AtPrime P) (nonZeroDivisors R))
      (Localization (Algebra.algebraMapSubmonoid (FractionRing R) P.primeCompl)) := by
  -- The canonical iterated localization object already carries both localization structures.
  exact IsLocalization.commutes (Localization.AtPrime P) (FractionRing R)
    (Localization (Algebra.algebraMapSubmonoid (FractionRing R) P.primeCompl))
    P.primeCompl (nonZeroDivisors R)

/-- Helper for Lemma 10.37.12: every global nonzerodivisor stays a nonzerodivisor after localizing
at a prime. -/
lemma atPrime_nonZeroDivisors_le (P : Ideal R) [P.IsPrime] :
    Algebra.algebraMapSubmonoid (Localization.AtPrime P) (nonZeroDivisors R) ≤
      nonZeroDivisors (Localization.AtPrime P) := by
  intro z hz
  rcases hz with ⟨y, hy, rfl⟩
  -- In the domain `R_P`, nonzerodivisors are exactly the nonzero elements.
  rw [mem_nonZeroDivisors_iff_ne_zero]
  exact map_ne_zero_atPrime_of_mem_nonZeroDivisors P hy

/-- Helper for Lemma 10.37.12: the localization subalgebra of `Frac(R_P)` obtained by inverting
the images of global nonzerodivisors is integrally closed. -/
lemma atPrime_totalFraction_subalgebra_isIntegrallyClosed (P : Ideal R) [P.IsPrime] :
    IsIntegrallyClosed
      (Localization.subalgebra (FractionRing (Localization.AtPrime P))
        (Algebra.algebraMapSubmonoid (Localization.AtPrime P) (nonZeroDivisors R))
        (atPrime_nonZeroDivisors_le (R := R) P)) := by
  -- Once the image submonoid is known to consist of nonzerodivisors, integrally closedness
  -- localizes from `R_P` to the corresponding subalgebra of its fraction ring.
  exact isIntegrallyClosed_of_isLocalization
    (R := Localization.AtPrime P)
    (S := Localization.subalgebra (FractionRing (Localization.AtPrime P))
      (Algebra.algebraMapSubmonoid (Localization.AtPrime P) (nonZeroDivisors R))
      (atPrime_nonZeroDivisors_le (R := R) P))
    (Algebra.algebraMapSubmonoid (Localization.AtPrime P) (nonZeroDivisors R))
    (atPrime_nonZeroDivisors_le (R := R) P)

/-- Helper for Lemma 10.37.12: equality in the iterated localization can be cleared by a
multiplier outside the prime. -/
lemma exists_multiple_outside_prime_of_totalFraction_eq (P : Ideal R) [P.IsPrime]
    {u v : FractionRing R}
    (h :
      algebraMap (FractionRing R)
          (Localization (Algebra.algebraMapSubmonoid (FractionRing R) P.primeCompl)) u =
        algebraMap (FractionRing R)
          (Localization (Algebra.algebraMapSubmonoid (FractionRing R) P.primeCompl)) v) :
    ∃ t : R, t ∈ P.primeCompl ∧
      algebraMap R (FractionRing R) t * u = algebraMap R (FractionRing R) t * v := by
  -- Clear equality in the explicit localization of `Q(R)` at `P.primeCompl`.
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists
    (Algebra.algebraMapSubmonoid (FractionRing R) P.primeCompl)
    (Localization (Algebra.algebraMapSubmonoid (FractionRing R) P.primeCompl))).mp h
  rcases c.2 with ⟨t, ht, hct⟩
  refine ⟨t, ht, ?_⟩
  simpa [hct, mul_assoc, mul_left_comm] using hc

/-- Helper for Lemma 10.37.12: after localizing at a prime, an integral element of the total
fraction ring already comes from the prime localization itself. -/
lemma exists_atPrime_preimage_in_totalFraction {x : FractionRing R}
    (hx : IsIntegral R x) (P : Ideal R) [P.IsPrime] :
    let Tp := Localization (Algebra.algebraMapSubmonoid (FractionRing R) P.primeCompl)
    ∃ z : Localization.AtPrime P,
      algebraMap (FractionRing R) Tp x =
        algebraMap (Localization.AtPrime P) Tp z := by
  -- TODO: keep the source-faithful route through `Tp → Frac(R_P)` defined by `IsLocalization.lift`,
  -- then use integrally closedness of `R_P` inside `Frac(R_P)` and pull the equality back by
  -- injectivity of that lift. The current blocker is the canonical `Frac(R_P)` instance bundle:
  -- `Algebra (Localization.AtPrime P) _`, `IsFractionRing _ _`, and the induced scalar tower still
  -- trigger deterministic elaboration/typeclass timeouts when assembled locally in this file.
  sorry

/-- Helper for Lemma 10.37.12: an integral element of the total fraction ring has a denominator
outside any chosen prime ideal. -/
lemma exists_denominator_outside_prime_of_integral {x : FractionRing R}
    (hx : IsIntegral R x) (P : Ideal R) [P.IsPrime] :
    ∃ r : R, r ∈ P.primeCompl ∧ ∃ a : R,
      algebraMap R (FractionRing R) a = algebraMap R (FractionRing R) r * x := by
  -- TODO: once `exists_atPrime_preimage_in_totalFraction` is available, write the local element
  -- as `a / s` in `R_P`, map `mk'_spec'` into the explicit iterated localization `Tp`, and then
  -- apply `exists_multiple_outside_prime_of_totalFraction_eq` to clear the remaining equality back
  -- in `FractionRing R`, exactly as in the source proof.
  sorry

/-- Lemma 10.37.12: a normal ring is integrally closed in its total ring of fractions. -/
theorem isIntegrallyClosed_of_isNormalRing : IsIntegrallyClosed R := by
  rw [isIntegrallyClosed_iff (K := FractionRing R)]
  intro x hx
  obtain ⟨I, hI⟩ := denominator_ideal_spec x
  have hlocal :
      ∀ (P : Ideal R) (_ : P.IsMaximal),
        algebraMap R (Localization.AtPrime P) (1 : R) ∈
          Ideal.map (algebraMap R (Localization.AtPrime P)) I := by
    intro P hP
    have hprime : P.IsPrime := Ideal.IsMaximal.isPrime hP
    letI : P.IsPrime := hprime
    obtain ⟨r, hrP, a, ha⟩ := exists_denominator_outside_prime_of_integral hx P
    have hrI : r ∈ I := (hI r).2 ⟨a, ha⟩
    have hrMap :
        algebraMap R (Localization.AtPrime P) r ∈
          Ideal.map (algebraMap R (Localization.AtPrime P)) I :=
      Ideal.mem_map_of_mem _ hrI
    have hunit : IsUnit (algebraMap R (Localization.AtPrime P) r) :=
      IsLocalization.map_units (Localization.AtPrime P) ⟨r, hrP⟩
    have htop :
        Ideal.map (algebraMap R (Localization.AtPrime P)) I = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ hrMap hunit
    simpa [htop]
  have h1I : (1 : R) ∈ I := Ideal.mem_of_localization_maximal hlocal
  obtain ⟨a, ha⟩ := (hI 1).1 h1I
  -- Once `1` lies in the denominator ideal, the original element already comes from `R`.
  refine ⟨a, ?_⟩
  simpa using ha

instance : IsIntegrallyClosed R := isIntegrallyClosed_of_isNormalRing

end

/-! ### Lemma_10_37_13 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable (M : Submonoid R)

/- Lemma 10.37.13 is `source-facing`: it asserts that the chapter owner predicate
`IsNormalRing` is stable under localization. The primitive data are just the ambient
localization witness `[IsLocalization M S]`. The `core/canonical` ingredients are the
prime-localization API from `Definition 10.37.11` together with mathlib's standard
identification of a prime localization of `S` with the corresponding prime localization of `R`. -/
/-- Lemma 10.37.13: a localization of a normal ring is again a normal ring. -/
theorem isNormalRing_of_isLocalization [IsLocalization M S] [IsNormalRing R] :
    IsNormalRing S := by
  refine ⟨fun q ↦ ?_⟩
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  letI : IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) p.asIdeal :=
    by
      simpa [p] using
        (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
          (Localization.AtPrime q.asIdeal) q.asIdeal)
  let e : Localization.AtPrime p.asIdeal ≃ₐ[R] Localization.AtPrime q.asIdeal :=
    IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal)
  exact ⟨Function.Injective.isDomain e.symm e.symm.injective,
    (isIntegrallyClosed_localizationAtPrime p).of_equiv e.toRingEquiv⟩

instance [IsNormalRing R] : IsNormalRing (Localization M) :=
  isNormalRing_of_isLocalization M

end

/-! ### Lemma_10_37_14 (from Chap10) -/
universe u

section

open Polynomial

variable {R : Type u} [CommRing R] [IsNormalRing R]

private theorem isNormalLocalizationAtPrime_polynomial
    (q : PrimeSpectrum (Polynomial R)) :
    IsDomain (Localization.AtPrime q.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime q.asIdeal) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap C q
  let I : Ideal R := p.asIdeal
  let Rₚ := Localization.AtPrime I
  let S := Polynomial Rₚ
  let M : Submonoid (Polynomial R) := I.primeCompl.map C
  letI : Algebra (Polynomial R) S :=
    (Polynomial.mapRingHom (algebraMap R Rₚ)).toAlgebra
  letI : IsLocalization M S := Polynomial.isLocalization I.primeCompl Rₚ
  let q' : Ideal S := Ideal.map (algebraMap (Polynomial R) S) q.asIdeal
  have hdisj : Disjoint (M : Set (Polynomial R)) q.asIdeal := by
    refine Set.disjoint_left.mpr fun f hf hfq ↦ ?_
    rcases hf with ⟨g, hg, rfl⟩
    exact hg (by simpa [p, I] using hfq)
  have hq' : Ideal.comap (algebraMap (Polynomial R) S) q' = q.asIdeal := by
    simpa [q'] using
      IsLocalization.comap_map_of_isPrime_disjoint M S q.2 hdisj
  letI : q'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M S q.asIdeal q.2 hdisj
  letI : IsLocalization.AtPrime (Localization.AtPrime q') q.asIdeal := by
    simpa [hq'] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        M _ q')
  let e : Localization.AtPrime q.asIdeal ≃ₐ[Polynomial R] Localization.AtPrime q' :=
    IsLocalization.algEquiv q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q')
  letI : IsDomain Rₚ := isDomain_localizationAtPrime p
  letI : IsIntegrallyClosed Rₚ := isIntegrallyClosed_localizationAtPrime p
  letI : IsNormalRing S := inferInstance
  letI : IsNormalRing (Localization.AtPrime q') := inferInstance
  exact ⟨MulEquiv.isDomain _ e.toMulEquiv,
    (show IsIntegrallyClosed (Localization.AtPrime q') from inferInstance).of_equiv
      e.symm.toRingEquiv⟩

-- Proof sketch: for a prime ideal `q` of `Polynomial R`, let `p` be its contraction to `R`.
-- Then `Localization.AtPrime p` is a normal domain because `R` is a normal ring. By
-- `Lemma 10.37.8`, the polynomial ring over that normal domain is normal, and by
-- `Lemma 10.37.5` the further localization at `q` is again a normal domain.
/-- Lemma 10.37.14: if `R` is a normal ring, then the polynomial ring `Polynomial R` is a normal
ring. -/
theorem isNormalRing_polynomial : IsNormalRing (Polynomial R) := by
  exact ⟨isNormalLocalizationAtPrime_polynomial⟩

/-- Polynomial rings over normal rings carry the canonical normal-ring instance. -/
instance : IsNormalRing (Polynomial R) := isNormalRing_polynomial

end

/-! ### Lemma_10_37_15 (from Chap10) -/
universe u v

section

variable {ι : Type u} [Finite ι]
variable {R : ι → Type v} [∀ i, CommRing (R i)] [∀ i, IsNormalRing (R i)]

open Localization.AtPrime

private theorem isNormalLocalizationAtPrime_pi
    (p : PrimeSpectrum (Π i, R i)) :
    IsDomain (Localization.AtPrime p.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := by
  obtain ⟨i, q, rfl⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq p
  letI := isDomain_localizationAtPrime q
  letI := isIntegrallyClosed_localizationAtPrime q
  let e :
      Localization.AtPrime (Ideal.comap (Pi.evalRingHom R i) q.asIdeal) ≃+*
        Localization.AtPrime q.asIdeal :=
    RingEquiv.ofBijective (mapPiEvalRingHom q.asIdeal) (mapPiEvalRingHom_bijective q.asIdeal)
  exact ⟨Function.Injective.isDomain e e.injective, IsIntegrallyClosed.of_equiv e.symm⟩

/-- Lemma 10.37.15: a finite product of normal rings is normal. -/
theorem isNormalRing_pi : IsNormalRing (Π i, R i) :=
  ⟨isNormalLocalizationAtPrime_pi⟩

/-- A finite product of normal rings carries the canonical normal-ring instance. -/
instance : IsNormalRing (Π i, R i) := isNormalRing_pi

end

/-! ### Lemma_10_37_16 (from Chap10) -/
universe u

section

variable (R : Type u) [CommRing R]

variable [IsReduced R]
variable [Finite (minimalPrimes R)]

/-- Helper for Lemma 10.37.16: every minimal prime carries its canonical prime-ideal instance. -/
local instance minimalPrime_isPrime (p : minimalPrimes R) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

/-- Helper for Lemma 10.37.16: in a reduced ring, the radical of `⊥` is `⊥`. -/
lemma radical_bot_eq_bot : (⊥ : Ideal R).radical = ⊥ := by
  -- Reducedness identifies the nilradical with the zero ideal.
  simpa [nilradical, Ideal.zero_eq_bot] using nilradical_eq_zero R

/-- Helper for Lemma 10.37.16: the union of the minimal primes of a reduced ring is exactly the
complement of the nonzerodivisors. -/
lemma iUnion_minimalPrimes_eq_setOf_notMem_nonZeroDivisors :
    (⋃ p : minimalPrimes R, (p.1 : Set R)) = { x : R | x ∉ nonZeroDivisors R } := by
  -- Specialize the standard zerodivisor description to `I = ⊥`.
  rw [show (⋃ p : minimalPrimes R, (p.1 : Set R)) = (⋃ p ∈ minimalPrimes R, (p : Set R)) by
    ext x
    simp]
  rw [show minimalPrimes R = (⊥ : Ideal R).minimalPrimes by rfl]
  rw [Ideal.iUnion_minimalPrimes]
  ext x
  have hx :
      x ∉ nonZeroDivisors R ↔ { y : R | x * y = 0 ∧ y ≠ 0 }.Nonempty :=
    notMem_nonZeroDivisors_iff_left
  simpa [radical_bot_eq_bot (R := R), Set.nonempty_def, and_comm] using hx.symm

/-- Helper for Lemma 10.37.16: localizing a reduced ring at a minimal prime produces a field. -/
theorem minimalPrime_localization_isField (p : minimalPrimes R) :
    IsField (Localization.AtPrime p.1) := by
  haveI : Ring.KrullDimLE 0 (Localization.AtPrime p.1) :=
    Ring.KrullDimLE.of_isLocalization p.1 p.2 (Localization.AtPrime p.1)
  exact Ring.KrullDimLE.isField_of_isReduced

/-- Helper for Lemma 10.37.16: every idempotent element is integral over the base ring. -/
lemma isIntegral_of_isIdempotentElem {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {x : B} (hx : IsIdempotentElem x) : IsIntegral A x := by
  -- The monic polynomial `X * (X - 1)` vanishes on any idempotent.
  refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C (1 : A)), ?_, ?_⟩
  · exact Polynomial.Monic.mul Polynomial.monic_X (Polynomial.monic_X_sub_C 1)
  · simpa [hx.eq, sub_eq_add_neg, mul_add]

/-- Helper for Lemma 10.37.16: normality transports across ring equivalences. -/
theorem isNormalRing_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) [IsNormalRing A] : IsNormalRing B := by
  refine ⟨fun p ↦ ?_⟩
  let q : PrimeSpectrum A := PrimeSpectrum.comap e.toRingHom p
  let eLoc :
      Localization.AtPrime q.asIdeal ≃+* Localization.AtPrime p.asIdeal :=
    Localization.localRingEquiv _ _ e (PrimeSpectrum.comap_asIdeal (f := e.toRingHom) p)
  have hDomain : IsDomain (Localization.AtPrime q.asIdeal) := isDomain_localizationAtPrime q
  have hIntegrallyClosed : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) :=
    isIntegrallyClosed_localizationAtPrime q
  refine ⟨?_, ?_⟩
  · -- The localized equivalence transfers the domain structure.
    simpa [eLoc] using
      ((eLoc : Localization.AtPrime q.asIdeal ≃* Localization.AtPrime p.asIdeal).isDomain_iff).mp
        hDomain
  · -- The same equivalence transports integrally closedness.
    exact IsIntegrallyClosed.of_equiv eLoc

/-- Helper for Lemma 10.37.16: if an element of `R` maps to zero in the localization at a minimal
prime, then it already lies in that minimal prime. -/
lemma minimalPrime_mem_of_localization_zero (p : minimalPrimes R) {x : R}
    (hx : algebraMap R (Localization.AtPrime p.1) x = 0) :
    x ∈ p.1 := by
  have hxmem :
      algebraMap R (Localization.AtPrime p.1) x ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime p.1) := by
    rw [IsLocalRing.mem_maximalIdeal]
    simpa [hx]
  exact
    (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (S := Localization.AtPrime p.1) p.1 x).1 hxmem

/-- Helper for Lemma 10.37.16: every element of a minimal prime vanishes in the corresponding
localization. -/
lemma minimalPrime_maps_to_zero_in_localization (p : minimalPrimes R) {x : R}
    (hx : x ∈ p.1) :
    algebraMap R (Localization.AtPrime p.1) x = 0 := by
  letI : Field (Localization.AtPrime p.1) :=
    (minimalPrime_localization_isField (R := R) p).toField
  have hxmem :
      algebraMap R (Localization.AtPrime p.1) x ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime p.1) := by
    exact
      (IsLocalization.AtPrime.to_map_mem_maximal_iff
        (S := Localization.AtPrime p.1) p.1 x).2 hx
  simpa [IsLocalRing.maximalIdeal_eq_bot] using hxmem

/-- Helper for Lemma 10.37.16: the quotient by a minimal prime maps canonically to the
corresponding localization. -/
noncomputable abbrev minimalPrimeQuotientToLocalization (p : minimalPrimes R) :
    R ⧸ p.1 →+* Localization.AtPrime p.1 :=
  Ideal.Quotient.lift p.1 (algebraMap R (Localization.AtPrime p.1)) fun x hx ↦
    minimalPrime_maps_to_zero_in_localization (R := R) p hx

/-- Helper for Lemma 10.37.16: on quotient representatives, the canonical quotient-to-localization
map is just the original localization map. -/
@[simp]
lemma minimalPrimeQuotientToLocalization_mk (p : minimalPrimes R) (x : R) :
    minimalPrimeQuotientToLocalization (R := R) p (Ideal.Quotient.mk p.1 x) =
      algebraMap R (Localization.AtPrime p.1) x := by
  -- The quotient lift was defined to agree with the localization map on representatives.
  rfl

/-- Helper for Lemma 10.37.16: the quotient by a minimal prime embeds into the corresponding
localization. -/
lemma minimalPrimeQuotientToLocalization_injective (p : minimalPrimes R) :
    Function.Injective (minimalPrimeQuotientToLocalization (R := R) p) := by
  -- Compute the localization kernel exactly as the minimal prime and then invoke the quotient
  -- injectivity criterion.
  rw [Ideal.injective_lift_iff]
  ext x
  constructor
  · intro hx
    exact minimalPrime_mem_of_localization_zero (R := R) p hx
  · intro hx
    exact minimalPrime_maps_to_zero_in_localization (R := R) p hx

/-- Helper for Lemma 10.37.16: the canonical quotient-to-localization map provides the
`R / p`-algebra structure on `R_p`. -/
noncomputable local instance minimalPrimeQuotientToLocalization_algebra (p : minimalPrimes R) :
    Algebra (R ⧸ p.1) (Localization.AtPrime p.1) :=
  RingHom.toAlgebra (minimalPrimeQuotientToLocalization (R := R) p)

/-- Helper for Lemma 10.37.16: for a minimal prime `p`, the localization `R_p` is the fraction
field of `R / p`. -/
theorem minimalPrime_quotient_isFractionRing (p : minimalPrimes R) :
    IsFractionRing (R ⧸ p.1) (Localization.AtPrime p.1) := by
  -- TODO: package `Localization.AtPrime p.1` as the fraction field of `R ⧸ p.1` by reusing the
  -- injective quotient map above, adding the induced `FaithfulSMul` instance, and then expressing
  -- each localization element via `IsLocalization.exists_mk'_eq p.1.primeCompl`.
  sorry

/-- Helper for Lemma 10.37.16: integrally closedness lifts the coordinate idempotents in
`Q(R) ≃ ∏ R_p` back to a complete orthogonal family in `R`. -/
lemma lifted_minimalPrime_idempotents_complete [IsIntegrallyClosed R] :
    ∃ e : minimalPrimes R → R,
      CompleteOrthogonalIdempotents e ∧
        ∀ p : minimalPrimes R,
          fractionRing_equiv_pi_minimalPrimeLocalizations R
              (iUnion_minimalPrimes_eq_setOf_notMem_nonZeroDivisors (R := R))
              (algebraMap R (FractionRing R) (e p)) =
            Pi.single p 1 := by
  -- TODO: pull back the coordinate idempotents along
  -- `Q(R) ≃ ∏_{p ∈ MinSpec R} R_p`, then use injectivity of `R → Q(R)` to show the lifted family
  -- is complete orthogonal.
  sorry

/-- Helper for Lemma 10.37.16: the splitting ideal attached to the lifted `p`-th idempotent is
exactly the minimal prime `p`. -/
lemma span_one_sub_lifted_idempotent_eq_minimalPrime {e : minimalPrimes R → R}
    (he :
      ∀ p : minimalPrimes R,
        fractionRing_equiv_pi_minimalPrimeLocalizations R
            (iUnion_minimalPrimes_eq_setOf_notMem_nonZeroDivisors (R := R))
            (algebraMap R (FractionRing R) (e p)) =
          Pi.single p 1)
    (p : minimalPrimes R) :
    Ideal.span ({1 - e p} : Set R) = p.1 := by
  -- TODO: compare the `p`-coordinate of the product embedding to show
  -- `span(1 - e_p) ⊆ p`, then use injectivity of the global embedding and the vanishing of `p`
  -- in `R_p` to prove the reverse inclusion.
  sorry

/-- Helper for Lemma 10.37.16: the lifted complete orthogonal idempotents split `R` as the
product of the minimal-prime quotients. -/
noncomputable def minimalPrime_quotient_pi_ringEquiv [IsIntegrallyClosed R] :
    R ≃+* ∀ p : minimalPrimes R, R ⧸ p.1 :=
  -- TODO: combine `CompleteOrthogonalIdempotents.bijective_pi` with the ideal identifications
  -- from `span_one_sub_lifted_idempotent_eq_minimalPrime`.
  sorry

/-- Helper for Lemma 10.37.16: every minimal-prime quotient is integrally closed. -/
theorem minimalPrime_quotient_isIntegrallyClosed [IsIntegrallyClosed R]
    (p : minimalPrimes R) :
    IsIntegrallyClosed (R ⧸ p.1) := by
  -- TODO: transport global integrally closedness to the product of minimal-prime quotients,
  -- apply `isIntegrallyClosedIn_pi_iff`, and then use
  -- `minimalPrime_quotient_isFractionRing` to pass from integrally closed maps to the owner
  -- predicate `IsIntegrallyClosed`.
  sorry

/-- Lemma 10.37.16: for a reduced ring with finitely many minimal primes, the following are
equivalent: `R` is a normal ring, `R` is integrally closed in its total ring of fractions, and
`R` is a finite product of normal domains. -/
-- Proof sketch: combine the normal-ring criterion from the previous lemmas with the description
-- of the total quotient ring as the product of the localizations at the minimal primes. The
-- idempotents in that product split `R` as a finite product of the quotients by its minimal
-- primes. For the domain factors, the chapter's owner predicate for "normal domain" is the
-- canonical `IsIntegrallyClosed`, so the finite-product clause is stated directly with that API.
theorem normalRing_tfae_isIntegrallyClosed_isFiniteProductOfNormalDomains :
    List.TFAE
      [ IsNormalRing R
      , IsIntegrallyClosed R
      , ∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (_ : ∀ i, CommRing (S i))
          (_ : R ≃+* ∀ i, S i),
          (∀ i, IsDomain (S i)) ∧ ∀ i, IsIntegrallyClosed (S i)
      ] := by
  tfae_have 1 → 2 := fun h ↦ by
    -- A normal ring is integrally closed in its total quotient ring by Lemma 10.37.12.
    letI : IsNormalRing R := h
    exact isIntegrallyClosed_of_isNormalRing (R := R)
  tfae_have 2 → 3 := fun h ↦ by
    classical
    letI : IsIntegrallyClosed R := h
    -- Lift the coordinate idempotents of `Q(R) ≃ ∏ R_p` and split `R` into the minimal-prime
    -- quotients, which are domains and remain integrally closed.
    refine ⟨minimalPrimes R, inferInstance, fun p ↦ R ⧸ p.1, ?_, ?_, ?_⟩
    · intro p
      infer_instance
    · exact minimalPrime_quotient_pi_ringEquiv (R := R)
    · constructor
      · intro p
        haveI : p.1.IsPrime := Ideal.minimalPrimes_isPrime p.2
        infer_instance
      · intro p
        exact minimalPrime_quotient_isIntegrallyClosed (R := R) p
  tfae_have 3 → 1 := fun h ↦ by
    classical
    obtain ⟨ι, hι, S, hS, e, hDomain, hClosed⟩ := h
    letI : Finite ι := hι
    letI : ∀ i, CommRing (S i) := hS
    letI : ∀ i, IsNormalRing (S i) := fun i ↦ by
      letI : IsDomain (S i) := hDomain i
      letI : IsIntegrallyClosed (S i) := hClosed i
      infer_instance
    -- A finite product of normal domains is normal, and ring equivalence transports normality.
    letI : IsNormalRing (∀ i, S i) := isNormalRing_pi
    exact isNormalRing_of_ringEquiv (A := ∀ i, S i) (B := R) e.symm
  tfae_finish

end
