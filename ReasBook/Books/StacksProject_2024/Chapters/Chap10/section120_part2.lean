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


/-! ### Definition_10_120_14 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R]

namespace Ideal

/- A multiset factorization of an ideal is source-facing data: the factor ideals themselves and
their product. The canonical owner abstractions governing existence and uniqueness are upstream. -/
/-- A multiset `f` is a prime-ideal factorization of `I` if its entries are nonzero prime ideals
and its product is `I`. Equality of multisets records uniqueness up to permutation. -/
def IsPrimeFactorization (I : Ideal R) (f : Multiset (Ideal R)) : Prop :=
  (∀ P ∈ f, P ≠ ⊥ ∧ P.IsPrime) ∧ f.prod = I

end Ideal

end

section

variable (R : Type u) [CommRing R]

/-
Domain-style sampling:
- primary domain: Dedekind domains and factorization of ideals in commutative algebra;
- sampled owner API:
  `IsDedekindDomain`,
  `Ideal.uniqueFactorizationMonoid`,
  `UniqueFactorizationMonoid.factors_unique`,
  `Ideal.finprod_heightOneSpectrum_factorization`;
- source-facing: `IsDedekindDomainByFactorization R`, a domain whose nonzero ideals factor as a
  finite product of nonzero prime ideals, uniquely up to permutation;
- core/canonical: `IsDedekindDomain`;
- bridge/view: `HasUniquePrimeIdealFactorization R`, which isolates just the ideal-factorization
  clause from the full source-facing notion.

Primitive data are the prime-ideal factorizations themselves. The unique-factorization monoid
structure on ideals and the height-one-spectrum factorization formula are derived upstream API and
should remain companion canonical tools rather than replacing the source-facing statement. The
domain hypothesis belongs in the main source-facing owner, not in the bridge predicate alone.
-/

/-- Bridge predicate: every nonzero ideal admits a finite
factorization into nonzero prime ideals, uniquely up to permutation. -/
def HasUniquePrimeIdealFactorization : Prop :=
  ∀ I : Ideal R, I ≠ ⊥ → ∃! f : Multiset (Ideal R), I.IsPrimeFactorization f

/-- Definition 10.120.14, source-facing owner: a Dedekind domain is a domain whose nonzero ideals
factor uniquely into nonzero prime ideals. -/
def IsDedekindDomainByFactorization : Prop :=
  IsDomain R ∧ HasUniquePrimeIdealFactorization R

end

section

variable (R : Type u) [CommRing R] [IsDedekindDomain R]

open UniqueFactorizationMonoid

private theorem isPrimeFactorization_factors (R : Type u) [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} (hI : I ≠ ⊥) :
    I.IsPrimeFactorization (factors I) := by
  refine ⟨?_, associated_iff_eq.mp ?_⟩
  · intro P hP
    have hprime : Prime P := prime_of_factor P hP
    exact ⟨by simpa [Ideal.zero_eq_bot] using hprime.ne_zero, Ideal.isPrime_of_prime hprime⟩
  · exact factors_prod (by simpa [Ideal.zero_eq_bot] using hI)

private theorem irreducible_of_mem_isPrimeFactorization
    (R : Type u) [CommRing R] [IsDedekindDomain R] {I : Ideal R} {f : Multiset (Ideal R)}
    (hf : I.IsPrimeFactorization f) {P : Ideal R} (hP : P ∈ f) : Irreducible P := by
  exact (Ideal.prime_of_isPrime (hf.1 P hP).1 (hf.1 P hP).2).irreducible

/-- In a Dedekind domain, every nonzero ideal admits a unique factorization into nonzero prime
ideals. This is the source-facing ideal-factorization bridge from the canonical owner
`IsDedekindDomain`. -/
theorem hasUniquePrimeIdealFactorization_of_isDedekindDomain :
    HasUniquePrimeIdealFactorization R := by
  intro I hI
  refine ⟨factors I, ?_, ?_⟩
  · exact isPrimeFactorization_factors R hI
  · intro g hg
    have hfactors : I.IsPrimeFactorization (factors I) := isPrimeFactorization_factors R hI
    have hrel : Multiset.Rel Associated (factors I) g := by
      apply factors_unique
      · intro P hP
        exact irreducible_of_mem_isPrimeFactorization R hfactors hP
      · intro P hP
        exact irreducible_of_mem_isPrimeFactorization R hg hP
      · exact associated_iff_eq.mpr (hfactors.2.trans hg.2.symm)
    have hfg : factors I = g := by
      simpa only [← Multiset.rel_eq, ← associated_eq_eq] using hrel
    exact hfg.symm

/-- A Dedekind domain satisfies the textbook factorization characterization of
Definition 10.120.14. -/
theorem isDedekindDomainByFactorization_of_isDedekindDomain :
    IsDedekindDomainByFactorization R :=
  ⟨inferInstance, hasUniquePrimeIdealFactorization_of_isDedekindDomain R⟩

variable (R : Type u) [CommRing R]

/-- Helper for Definition 10.120.14: a nonzero prime ideal already gives the singleton
prime-ideal factorization of itself. -/
lemma isPrimeFactorization_singleton_of_isPrime {P : Ideal R} (hP0 : P ≠ ⊥) (hP : P.IsPrime) :
    P.IsPrimeFactorization ({P} : Multiset (Ideal R)) := by
  -- The singleton multiset records exactly one nonzero prime factor and multiplies back to `P`.
  refine ⟨?_, by simp⟩
  intro Q hQ
  simpa [Multiset.mem_singleton.mp hQ, hP0] using And.intro hP0 hP

/-- Helper for Definition 10.120.14: if a prime ideal contains the ideal represented by a
prime-ideal factorization, then one factor is contained in that prime ideal. -/
lemma exists_factor_le_of_isPrimeFactorization_le {I P : Ideal R} {f : Multiset (Ideal R)}
    (hf : I.IsPrimeFactorization f) (hP : P.IsPrime) (hIP : I ≤ P) :
    ∃ Q ∈ f, Q ≤ P := by
  -- Rewrite the containment using the recorded factorization and apply primeness of `P`.
  have hprod : f.prod ≤ P := by simpa [hf.2] using hIP
  exact hP.multiset_prod_le.mp hprod

section FactorizationToInverse

variable [IsDomain R]

/-- Helper for Definition 10.120.14: a multiset product of unit fractional ideals is again a
unit. This packages the induction needed to multiply the prime-factor unit witnesses. -/
lemma multiset_prod_isUnit_of_forall
    (f : Multiset (Ideal R))
    (hunit :
      ∀ P ∈ f, IsUnit (P : FractionalIdeal (nonZeroDivisors R) (FractionRing R))) :
    IsUnit
      ((f.map
          fun P : Ideal R => (P : FractionalIdeal (nonZeroDivisors R) (FractionRing R))).prod) := by
  -- Multiply the unit witnesses one factor at a time along the multiset product.
  induction f using Multiset.induction_on with
  | empty =>
      simp
  | @cons P f ih =>
      have hP :
          IsUnit (P : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) := hunit P (by simp)
      have hf :
          ∀ Q ∈ f, IsUnit (Q : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) := by
        intro Q hQ
        exact hunit Q (by simp [hQ])
      simpa [Multiset.map_cons] using hP.mul (ih hf)

/-- Helper for Definition 10.120.14: once each nonzero prime ideal is a unit as a fractional
ideal, any nonzero ideal with a prime-ideal factorization is a unit as well. -/
lemma ideal_isUnit_of_isPrimeFactorization {I : Ideal R} {f : Multiset (Ideal R)}
    (hf : I.IsPrimeFactorization f)
    (hprime :
      ∀ {P : Ideal R}, P ≠ ⊥ → P.IsPrime →
        IsUnit (P : FractionalIdeal (nonZeroDivisors R) (FractionRing R))) :
    IsUnit (I : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) := by
  -- First transport the ideal product into the fractional-ideal product.
  have hcoe :
      (I : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) =
        (f.map
          fun P : Ideal R => (P : FractionalIdeal (nonZeroDivisors R) (FractionRing R))).prod := by
    rw [← hf.2]
    simpa using
      (map_multiset_prod
        (FractionalIdeal.coeIdealHom (nonZeroDivisors R) (FractionRing R)) f)
  -- Then combine the unit witnesses for each prime factor.
  rw [hcoe]
  refine multiset_prod_isUnit_of_forall R f ?_
  intro P hP
  exact hprime (hf.1 P hP).1 (hf.1 P hP).2

/-- Helper for Definition 10.120.14: if every nonzero integral ideal becomes a unit fractional
ideal, then the ring satisfies the invertibility formulation of Dedekind domains. -/
lemma isDedekindDomainInv_of_nonzero_ideal_isUnit
    (hIdeal :
      ∀ I : Ideal R, I ≠ ⊥ →
        IsUnit (I : FractionalIdeal (nonZeroDivisors R) (FractionRing R))) :
    IsDedekindDomainInv R := by
  intro I hI
  -- Decompose the fractional ideal into a principal part times an integral ideal factor.
  obtain ⟨a, J, ha, hIJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hmap0 : algebraMap R (FractionRing R) a ≠ 0 := by
    intro h0
    apply ha
    exact (IsFractionRing.injective R (FractionRing R)) (by simpa using h0)
  have hmap : (algebraMap R (FractionRing R) a)⁻¹ ≠ 0 := inv_ne_zero hmap0
  have hPrincipal :
      IsUnit
        (FractionalIdeal.spanSingleton (nonZeroDivisors R) ((algebraMap R (FractionRing R) a)⁻¹ :
          FractionRing R)) := by
  -- The principal factor is invertible with the obvious inverse principal ideal.
    exact (FractionalIdeal.mul_inv_cancel_iff_isUnit (K := FractionRing R)).mp
      (FractionalIdeal.spanSingleton_mul_inv (R₁ := R) (K := FractionRing R) hmap)
  have hJ :
      IsUnit (J : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) :=
    hIdeal J (FractionalIdeal.ideal_factor_ne_zero hI hIJ)
  have hUnit : IsUnit I := by
    -- Reassemble the decomposition and multiply the two unit witnesses.
    rw [hIJ]
    exact hPrincipal.mul hJ
  exact (FractionalIdeal.mul_inv_cancel_iff_isUnit (K := FractionRing R)).mpr hUnit

/-- Helper for Definition 10.120.14: under unique prime factorization of nonzero ideals, a
nonzero prime ideal cannot equal its square. -/
lemma prime_sq_ne_self_of_hasUniquePrimeIdealFactorization
    (hfac : HasUniquePrimeIdealFactorization R) {P : Ideal R} (hP0 : P ≠ ⊥) (hP : P.IsPrime) :
    P ^ 2 ≠ P := by
  intro hsq
  obtain ⟨f, -, huniq⟩ := hfac P hP0
  have hsingle : P.IsPrimeFactorization ({P} : Multiset (Ideal R)) :=
    isPrimeFactorization_singleton_of_isPrime R hP0 hP
  have hdouble : P.IsPrimeFactorization (({P} : Multiset (Ideal R)) + {P}) := by
    refine ⟨?_, ?_⟩
    · intro Q hQ
      have hQP : Q = P := by
        simpa using hQ
      simpa [hQP, hP0] using And.intro hP0 hP
    · -- The duplicated singleton multiset multiplies to `P ^ 2`, hence to `P` by the assumption.
      simpa [pow_two] using hsq
  have hsame :
      (({P} : Multiset (Ideal R)) + {P}) = ({P} : Multiset (Ideal R)) := by
    calc
      (({P} : Multiset (Ideal R)) + {P}) = f := huniq _ hdouble
      _ = ({P} : Multiset (Ideal R)) := (huniq _ hsingle).symm
  have hcard := congrArg Multiset.card hsame
  norm_num at hcard

/-- Helper for Definition 10.120.14: a nonzero prime ideal contains an element outside its square
once nonzero ideals admit unique prime factorization. -/
lemma exists_mem_prime_not_mem_sq_of_hasUniquePrimeIdealFactorization
    (hfac : HasUniquePrimeIdealFactorization R) {P : Ideal R} (hP0 : P ≠ ⊥) (hP : P.IsPrime) :
    ∃ x : R, x ∈ P ∧ x ∉ P ^ 2 := by
  have hlt : P ^ 2 < P := by
    refine lt_of_le_of_ne (by simpa [pow_two] using (Ideal.mul_le_right : P * P ≤ P)) ?_
    exact prime_sq_ne_self_of_hasUniquePrimeIdealFactorization R hfac hP0 hP
  -- Strict containment of `P ^ 2` in `P` provides the source element `x ∈ P \ P^2`.
  exact SetLike.exists_of_lt hlt

/-- Helper for Definition 10.120.14: in a prime-ideal factorization of `Ideal.span ({x, y} : Set R)`,
there is at most one factor contained in `P` when `x ∈ P \ P^2`. -/
lemma span_pair_factorization_has_no_second_factor_le_prime
    {P : Ideal R} {x y : R} {f : Multiset (Ideal R)}
    (hf : (Ideal.span ({x, y} : Set R)).IsPrimeFactorization f)
    (_hxP : x ∈ P) (hxP_sq : x ∉ P ^ 2) :
    ∀ {Q : Ideal R}, Q ∈ f → Q ≤ P → ∀ {Q' : Ideal R}, Q' ∈ f.erase Q → ¬ Q' ≤ P := by
  classical
  intro Q hQf hQP Q' hQ'f hQ'P
  have herase_le : (f.erase Q).prod ≤ Q' := by
    -- Rewrite the erased product so that `Q'` appears as the leading factor.
    calc
      (f.erase Q).prod = (Q' ::ₘ (f.erase Q).erase Q').prod := by
        rw [Multiset.cons_erase hQ'f]
      _ = Q' * ((f.erase Q).erase Q').prod := by rw [Multiset.prod_cons]
      _ ≤ Q' := Ideal.mul_le_right
  have hspan_le_sq : Ideal.span ({x, y} : Set R) ≤ P ^ 2 := by
    -- Two distinct factors below `P` force the whole product ideal into `P ^ 2`.
    calc
      Ideal.span ({x, y} : Set R) = f.prod := hf.2.symm
      _ = (Q ::ₘ f.erase Q).prod := by rw [Multiset.cons_erase hQf]
      _ = Q * (f.erase Q).prod := by rw [Multiset.prod_cons]
      _ ≤ P * Q' := Ideal.mul_mono hQP herase_le
      _ ≤ P * P := Ideal.mul_mono le_rfl hQ'P
      _ = P ^ 2 := by rw [pow_two]
  have hx_span : x ∈ Ideal.span ({x, y} : Set R) := by
    -- The generator `x` lies in the pair ideal by construction.
    exact Ideal.subset_span (by simp)
  exact hxP_sq (hspan_le_sq hx_span)

/-- Helper for Definition 10.120.14: if every factor in a multiset of ideals maps to `⊤` in the
localization at `P`, then their product maps to `⊤` as well. -/
lemma map_multiset_prod_eq_top_of_forall
    {P : Ideal R} (hP : P.IsPrime) (f : Multiset (Ideal R))
    (hmap :
      ∀ Q ∈ f, Ideal.map (algebraMap R (Localization.AtPrime P)) Q = ⊤) :
    Ideal.map (algebraMap R (Localization.AtPrime P)) f.prod = ⊤ := by
  letI : P.IsPrime := hP
  -- Expand the multiset product one factor at a time and collapse each mapped factor to `⊤`.
  induction f using Multiset.induction_on with
  | empty =>
      simpa using (Ideal.map_top (algebraMap R (Localization.AtPrime P)))
  | @cons Q f ih =>
      have hQ :
          Ideal.map (algebraMap R (Localization.AtPrime P)) Q = ⊤ := hmap Q (by simp)
      have hf :
          ∀ J ∈ f, Ideal.map (algebraMap R (Localization.AtPrime P)) J = ⊤ := by
        intro J hJ
        exact hmap J (by simp [hJ])
      calc
        Ideal.map (algebraMap R (Localization.AtPrime P)) (Q ::ₘ f).prod
            = Ideal.map (algebraMap R (Localization.AtPrime P)) (Q * f.prod) := by
                rw [Multiset.prod_cons]
        _ = Ideal.map (algebraMap R (Localization.AtPrime P)) Q *
              Ideal.map (algebraMap R (Localization.AtPrime P)) f.prod := by
              rw [Ideal.map_mul]
        _ = ⊤ * ⊤ := by rw [hQ, ih hf]
        _ = ⊤ := by simp

/-- Helper for Definition 10.120.14: after localizing at `P`, the ideal generated by `x` and
`y ^ 2` is prime when `x ∈ P \ P ^ 2` and nonzero ideals factor uniquely into prime ideals. -/
lemma span_pair_sq_map_isPrime_of_mem_prime_not_mem_sq
    (hfac : HasUniquePrimeIdealFactorization R) {P : Ideal R} (hP0 : P ≠ ⊥) (hP : P.IsPrime)
    {x y : R} (hxP : x ∈ P) (hxP_sq : x ∉ P ^ 2) (hyP : y ∈ P) :
    (Ideal.map (algebraMap R (Localization.AtPrime P)) (Ideal.span ({x, y ^ 2} : Set R))).IsPrime := by
  letI : P.IsPrime := hP
  have hx0 : x ≠ 0 := by
    intro hx0
    exact hxP_sq (by simpa [hx0])
  let I : Ideal R := Ideal.span ({x, y ^ 2} : Set R)
  have hxI : x ∈ I := by
    -- The chosen element `x` is one of the generators of the pair ideal.
    exact Ideal.subset_span (by simp [I])
  have hI0 : I ≠ ⊥ := by
    -- The pair ideal is nonzero because it contains the nonzero element `x`.
    intro hI0
    exact hx0 (by simpa [hI0] using (show x ∈ (⊥ : Ideal R) from hI0 ▸ hxI))
  have hIP : I ≤ P := by
    -- Both generators lie in `P`, so the pair ideal lies in `P`.
    refine Ideal.span_le.2 ?_
    intro z hz
    rcases hz with rfl | rfl
    · exact hxP
    · simpa [pow_two] using P.mul_mem_left y hyP
  obtain ⟨f, hf, -⟩ := hfac I hI0
  obtain ⟨Q, hQf, hQP⟩ := exists_factor_le_of_isPrimeFactorization_le R hf hP hIP
  have hQprime : Q.IsPrime := (hf.1 Q hQf).2
  have hno_second :
      ∀ {Q' : Ideal R}, Q' ∈ f.erase Q → ¬ Q' ≤ P := by
    -- The existing bookkeeping lemma rules out a second factor below `P`.
    exact span_pair_factorization_has_no_second_factor_le_prime R hf hxP hxP_sq hQf hQP
  have hmap_erase_top :
      Ideal.map (algebraMap R (Localization.AtPrime P)) (f.erase Q).prod = ⊤ := by
    -- Every erased factor fails to lie under `P`, so it localizes to `⊤`.
    refine map_multiset_prod_eq_top_of_forall R hP (f.erase Q) ?_
    intro Q' hQ'
    exact IsLocalization.AtPrime.map_eq_top_of_not_le
      (S := Localization.AtPrime P) (p := P) (I := Q') (hno_second hQ')
  have hmap_eq :
      Ideal.map (algebraMap R (Localization.AtPrime P)) I =
        Ideal.map (algebraMap R (Localization.AtPrime P)) Q := by
    -- Only the distinguished factor survives after localization at `P`.
    calc
      Ideal.map (algebraMap R (Localization.AtPrime P)) I
          = Ideal.map (algebraMap R (Localization.AtPrime P)) f.prod := by rw [hf.2]
      _ = Ideal.map (algebraMap R (Localization.AtPrime P)) (Q * (f.erase Q).prod) := by
            rw [← Multiset.prod_cons, Multiset.cons_erase hQf]
      _ = Ideal.map (algebraMap R (Localization.AtPrime P)) Q *
            Ideal.map (algebraMap R (Localization.AtPrime P)) (f.erase Q).prod := by
            rw [Ideal.map_mul]
      _ = Ideal.map (algebraMap R (Localization.AtPrime P)) Q * ⊤ := by rw [hmap_erase_top]
      _ = Ideal.map (algebraMap R (Localization.AtPrime P)) Q := by simp
  letI : Q.IsPrime := hQprime
  -- The surviving localized factor is prime, and the previous equality identifies the mapped pair
  -- ideal with it.
  rw [hmap_eq]
  exact Ideal.isPrime_map_of_isLocalizationAtPrime (S := Localization.AtPrime P) (q := P) hQP

/-- Helper for Definition 10.120.14: if the localized ideal generated by `x` and `y ^ 2` is
prime, then `y` already lies in the localized principal ideal generated by `x`. -/
lemma to_map_mem_map_span_singleton_of_pair_sq_map_isPrime
    {P : Ideal R} {x y : R} (hP : P.IsPrime) (hyP : y ∈ P)
    (hprime :
      (Ideal.map (algebraMap R (Localization.AtPrime P))
        (Ideal.span ({x, y ^ 2} : Set R))).IsPrime) :
    algebraMap R (Localization.AtPrime P) y ∈
      Ideal.map (algebraMap R (Localization.AtPrime P)) (Ideal.span ({x} : Set R)) := by
  letI : P.IsPrime := hP
  have hy_max :
      algebraMap R (Localization.AtPrime P) y ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    -- Membership in `P` translates directly into membership in the maximal ideal of `R_P`.
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P y).2 hyP
  have hy_sq_mem :
      (algebraMap R (Localization.AtPrime P) y) ^ 2 ∈
        Ideal.map (algebraMap R (Localization.AtPrime P)) (Ideal.span ({x, y ^ 2} : Set R)) := by
    -- The generator `y ^ 2` maps into the localized pair ideal.
    simpa [map_pow] using
      (Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime P))
        (Ideal.subset_span (by simp : y ^ 2 ∈ ({x, y ^ 2} : Set R))))
  have hy_mem_pair :
      algebraMap R (Localization.AtPrime P) y ∈
        Ideal.map (algebraMap R (Localization.AtPrime P)) (Ideal.span ({x, y ^ 2} : Set R)) :=
    hprime.mem_of_pow_mem 2 hy_sq_mem
  have hy_mem_pair' :
      algebraMap R (Localization.AtPrime P) y ∈
        Ideal.span
          ({algebraMap R (Localization.AtPrime P) x,
            (algebraMap R (Localization.AtPrime P) y) ^ 2} :
            Set (Localization.AtPrime P)) := by
    simpa [Ideal.map_span, Set.image_pair, map_pow, smul_eq_mul] using hy_mem_pair
  rw [Ideal.mem_span_pair] at hy_mem_pair'
  rcases hy_mem_pair' with ⟨a, b, hab⟩
  have hby_nonunits :
      b * algebraMap R (Localization.AtPrime P) y ∈ nonunits (Localization.AtPrime P) := by
    -- Multiplying an element of the maximal ideal keeps it in the maximal ideal.
    rw [← IsLocalRing.mem_maximalIdeal]
    exact (IsLocalRing.maximalIdeal (Localization.AtPrime P)).mul_mem_left b hy_max
  obtain ⟨u, hu⟩ :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
      (b * algebraMap R (Localization.AtPrime P) y) hby_nonunits
  have hmul :
      (1 - b * algebraMap R (Localization.AtPrime P) y) *
          algebraMap R (Localization.AtPrime P) y =
        a * algebraMap R (Localization.AtPrime P) x := by
    -- Rearranging the spanning relation isolates a unit times `y` as a multiple of `x`.
    calc
      (1 - b * algebraMap R (Localization.AtPrime P) y) *
          algebraMap R (Localization.AtPrime P) y
          = algebraMap R (Localization.AtPrime P) y -
              b * (algebraMap R (Localization.AtPrime P) y) ^ 2 := by
                rw [sub_mul, one_mul, mul_assoc, pow_two]
      _ = a * algebraMap R (Localization.AtPrime P) x := by
            calc
              algebraMap R (Localization.AtPrime P) y -
                  b * (algebraMap R (Localization.AtPrime P) y) ^ 2
                  = (a * algebraMap R (Localization.AtPrime P) x +
                      b * (algebraMap R (Localization.AtPrime P) y) ^ 2) -
                      b * (algebraMap R (Localization.AtPrime P) y) ^ 2 := by rw [hab]
              _ = a * algebraMap R (Localization.AtPrime P) x := by ring
  rw [Ideal.map_span, Set.image_singleton]
  refine Ideal.mem_span_singleton'.2 ?_
  refine ⟨↑u⁻¹ * a, ?_⟩
  have hu_inv :
      (↑u⁻¹ : Localization.AtPrime P) *
          (1 - b * algebraMap R (Localization.AtPrime P) y) = 1 := by
    simpa [hu] using Units.val_inv_mul u
  -- Multiply the isolated relation by the inverse unit to express `y` as a multiple of `x`.
  calc
    (↑u⁻¹ * a) * algebraMap R (Localization.AtPrime P) x
        = (↑u⁻¹ : Localization.AtPrime P) *
            (a * algebraMap R (Localization.AtPrime P) x) := by ring
    _ = (↑u⁻¹ : Localization.AtPrime P) *
          ((1 - b * algebraMap R (Localization.AtPrime P) y) *
            algebraMap R (Localization.AtPrime P) y) := by rw [hmul]
    _ = ((↑u⁻¹ : Localization.AtPrime P) *
          (1 - b * algebraMap R (Localization.AtPrime P) y)) *
            algebraMap R (Localization.AtPrime P) y := by ring
    _ = algebraMap R (Localization.AtPrime P) y := by rw [hu_inv, one_mul]

/-- Helper for Definition 10.120.14: localizing the principal ideal generated by `x ∈ P \ P ^ 2`
at `P` yields the localized prime ideal `P`. -/
lemma map_span_singleton_eq_map_prime_of_mem_prime_not_mem_sq
    (hfac : HasUniquePrimeIdealFactorization R) {P : Ideal R} (hP0 : P ≠ ⊥) (hP : P.IsPrime)
    {x : R} (hxP : x ∈ P) (hxP_sq : x ∉ P ^ 2) :
    Ideal.map (algebraMap R (Localization.AtPrime P)) (Ideal.span ({x} : Set R)) =
      Ideal.map (algebraMap R (Localization.AtPrime P)) P := by
  letI : P.IsPrime := hP
  apply le_antisymm
  · -- The generator `x` already lies in `P`, so the localized principal ideal is contained in
    -- the localized prime ideal.
    exact Ideal.map_mono
      ((Ideal.span_singleton_le_iff_mem (I := P) (x := x)).2 hxP)
  · -- For the reverse inclusion, check generator membership after localizing at `P`.
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    exact to_map_mem_map_span_singleton_of_pair_sq_map_isPrime R hP hy
      (span_pair_sq_map_isPrime_of_mem_prime_not_mem_sq R hfac hP0 hP hxP hxP_sq hy)

/-- Helper for Definition 10.120.14: the remaining source-faithful step is to show that a
nonzero prime ideal contains an element whose principal ideal has that prime ideal as a factor. -/
lemma exists_span_singleton_eq_mul_of_mem_prime
    (hfac : HasUniquePrimeIdealFactorization R) {P : Ideal R} (hP0 : P ≠ ⊥) (hP : P.IsPrime)
    {x : R} (hxP : x ∈ P) (hxP_sq : x ∉ P ^ 2) :
    ∃ J : Ideal R, Ideal.span ({x} : Set R) = P * J := by
  letI : P.IsPrime := hP
  have hx0 : x ≠ 0 := by
    intro hx0
    exact hxP_sq (by simpa [hx0])
  let I : Ideal R := Ideal.span ({x} : Set R)
  have hxI : x ∈ I := by
    -- The principal ideal contains its generator.
    exact Ideal.mem_span_singleton_self x
  have hI0 : I ≠ ⊥ := by
    -- The principal ideal is nonzero because `x ≠ 0`.
    exact mt Ideal.span_singleton_eq_bot.mp hx0
  have hIP : I ≤ P := by
    -- Since `x ∈ P`, the principal ideal generated by `x` lies in `P`.
    exact (Ideal.span_singleton_le_iff_mem (I := P) (x := x)).2 hxP
  obtain ⟨f, hf, -⟩ := hfac I hI0
  obtain ⟨Q, hQf, hQP⟩ := exists_factor_le_of_isPrimeFactorization_le R hf hP hIP
  have hno_second :
      ∀ {Q' : Ideal R}, Q' ∈ f.erase Q → ¬ Q' ≤ P := by
    intro Q' hQ' hQ'P
    have herase_le : (f.erase Q).prod ≤ Q' := by
      -- Rewrite the erased product so that `Q'` appears as the leading factor.
      calc
        (f.erase Q).prod = (Q' ::ₘ (f.erase Q).erase Q').prod := by
          rw [Multiset.cons_erase hQ']
        _ = Q' * ((f.erase Q).erase Q').prod := by rw [Multiset.prod_cons]
        _ ≤ Q' := Ideal.mul_le_right
    have hI_le_sq : I ≤ P ^ 2 := by
      -- Two factors below `P` would force the principal ideal into `P ^ 2`.
      calc
        I = f.prod := hf.2.symm
        _ = (Q ::ₘ f.erase Q).prod := by rw [Multiset.cons_erase hQf]
        _ = Q * (f.erase Q).prod := by rw [Multiset.prod_cons]
        _ ≤ P * Q' := Ideal.mul_mono hQP herase_le
        _ ≤ P * P := Ideal.mul_mono le_rfl hQ'P
        _ = P ^ 2 := by rw [pow_two]
    exact hxP_sq (hI_le_sq hxI)
  have hmap_erase_top :
      Ideal.map (algebraMap R (Localization.AtPrime P)) (f.erase Q).prod = ⊤ := by
    -- All factors except `Q` disappear after localizing at `P`.
    refine map_multiset_prod_eq_top_of_forall R hP (f.erase Q) ?_
    intro Q' hQ'
    exact IsLocalization.AtPrime.map_eq_top_of_not_le
      (S := Localization.AtPrime P) (p := P) (I := Q') (hno_second hQ')
  have hmap_I_Q :
      Ideal.map (algebraMap R (Localization.AtPrime P)) I =
        Ideal.map (algebraMap R (Localization.AtPrime P)) Q := by
    -- The distinguished factor `Q` is the only one that survives localization.
    calc
      Ideal.map (algebraMap R (Localization.AtPrime P)) I
          = Ideal.map (algebraMap R (Localization.AtPrime P)) f.prod := by rw [hf.2]
      _ = Ideal.map (algebraMap R (Localization.AtPrime P)) (Q * (f.erase Q).prod) := by
            rw [← Multiset.prod_cons, Multiset.cons_erase hQf]
      _ = Ideal.map (algebraMap R (Localization.AtPrime P)) Q *
            Ideal.map (algebraMap R (Localization.AtPrime P)) (f.erase Q).prod := by
            rw [Ideal.map_mul]
      _ = Ideal.map (algebraMap R (Localization.AtPrime P)) Q * ⊤ := by rw [hmap_erase_top]
      _ = Ideal.map (algebraMap R (Localization.AtPrime P)) Q := by simp
  have hmap_I_P :
      Ideal.map (algebraMap R (Localization.AtPrime P)) I =
        Ideal.map (algebraMap R (Localization.AtPrime P)) P := by
    -- The `y ^ 2` argument identifies the localized principal ideal with `P R_P`.
    simpa [I] using
      map_span_singleton_eq_map_prime_of_mem_prime_not_mem_sq R hfac hP0 hP hxP hxP_sq
  have hmap_Q_P :
      Ideal.map (algebraMap R (Localization.AtPrime P)) Q =
        Ideal.map (algebraMap R (Localization.AtPrime P)) P := by
    exact hmap_I_Q.symm.trans hmap_I_P
  have hQprime : Q.IsPrime := (hf.1 Q hQf).2
  letI : Q.IsPrime := hQprime
  have hQeq : Q = P := by
    -- Compare the surviving localized factor with `P`, then pull back along localization.
    calc
      Q = (Ideal.map (algebraMap R (Localization.AtPrime P)) Q).under R := by
            symm
            exact Ideal.under_map_of_isLocalizationAtPrime
              (S := Localization.AtPrime P) (q := P) hQP
      _ = (Ideal.map (algebraMap R (Localization.AtPrime P)) P).under R := by rw [hmap_Q_P]
      _ = P := by
            exact Ideal.under_map_of_isLocalizationAtPrime
              (S := Localization.AtPrime P) (q := P) (le_rfl : P ≤ P)
  refine ⟨(f.erase Q).prod, ?_⟩
  -- Erasing the identified factor `P` from the multiset factorization gives the desired cofactor.
  calc
    Ideal.span ({x} : Set R) = I := by rfl
    _ = f.prod := hf.2.symm
    _ = (Q ::ₘ f.erase Q).prod := by rw [Multiset.cons_erase hQf]
    _ = Q * (f.erase Q).prod := by rw [Multiset.prod_cons]
    _ = P * (f.erase Q).prod := by rw [hQeq]

/-- Helper for Definition 10.120.14: the remaining source-faithful step is to show that a
nonzero prime ideal becomes a unit fractional ideal from the textbook factorization hypothesis. -/
lemma nonzero_prime_isUnit_of_hasUniquePrimeIdealFactorization
    (hfac : HasUniquePrimeIdealFactorization R) {P : Ideal R} (hP0 : P ≠ ⊥) (hP : P.IsPrime) :
    IsUnit (P : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) := by
  -- Pick the source-faithful element `x ∈ P \ P ^ 2` and factor the principal ideal it generates.
  obtain ⟨x, hxP, hxP_sq⟩ :=
    exists_mem_prime_not_mem_sq_of_hasUniquePrimeIdealFactorization R hfac hP0 hP
  have hx0 : x ≠ 0 := by
    intro hx0
    apply hxP_sq
    simp [hx0]
  obtain ⟨J, hspan⟩ :=
    exists_span_singleton_eq_mul_of_mem_prime R hfac hP0 hP hxP hxP_sq
  -- The extracted factorization gives an explicit divisor of `1`, hence a unit witness.
  refine isUnit_iff_dvd_one.mpr ?_
  refine ⟨(J : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) *
      (Ideal.span ({x} : Set R) : FractionalIdeal (nonZeroDivisors R) (FractionRing R))⁻¹, ?_⟩
  symm
  calc
    (P : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) *
        ((J : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) *
          (Ideal.span ({x} : Set R) :
            FractionalIdeal (nonZeroDivisors R) (FractionRing R))⁻¹)
        = ((P : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) *
            (J : FractionalIdeal (nonZeroDivisors R) (FractionRing R))) *
            (Ideal.span ({x} : Set R) :
              FractionalIdeal (nonZeroDivisors R) (FractionRing R))⁻¹ := by
            rw [mul_assoc]
    _ = (Ideal.span ({x} : Set R) : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) *
          (Ideal.span ({x} : Set R) :
            FractionalIdeal (nonZeroDivisors R) (FractionRing R))⁻¹ := by
          rw [← FractionalIdeal.coeIdeal_mul, hspan]
    _ = 1 := FractionalIdeal.coe_ideal_span_singleton_mul_inv (K := FractionRing R) hx0

/-- Helper for Definition 10.120.14: unique prime factorization of nonzero integral ideals
implies the invertibility characterization of Dedekind domains. -/
lemma isDedekindDomainInv_of_hasUniquePrimeIdealFactorization
    (hfac : HasUniquePrimeIdealFactorization R) :
    IsDedekindDomainInv R := by
  -- Reduce to integral ideals, then use factorization to multiply the prime-ideal unit witnesses.
  refine isDedekindDomainInv_of_nonzero_ideal_isUnit R ?_
  intro I hI
  obtain ⟨f, hf, -⟩ := hfac I hI
  exact ideal_isUnit_of_isPrimeFactorization R hf
    (fun {P} hP0 hP =>
      nonzero_prime_isUnit_of_hasUniquePrimeIdealFactorization R hfac hP0 hP)

end FactorizationToInverse

/-- Definition 10.120.14 is equivalent to the canonical owner `IsDedekindDomain`, but the
textbook factorization characterization remains the main public entry of this file. -/
theorem isDedekindDomain_iff_isDedekindDomainByFactorization :
    IsDedekindDomain R ↔ IsDedekindDomainByFactorization R := by
  constructor
  · intro hDed
    letI := hDed
    exact isDedekindDomainByFactorization_of_isDedekindDomain R
  · intro hfactor
    letI : IsDomain R := hfactor.1
    -- Use the factorization hypothesis to pass through the invertibility formulation.
    exact (isDedekindDomain_iff_isDedekindDomainInv).mpr
      (isDedekindDomainInv_of_hasUniquePrimeIdealFactorization R hfactor.2)

end

/-! ### Lemma_10_120_15 (from Chap10) -/
universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/- 
Domain-style sampling:
- primary domain: principal ideal domains and Dedekind domains;
- sampled owner API:
  `IsDedekindDomain`,
  `IsPrincipalIdealRing`,
  `IsPrincipalIdealRing.isDedekindDomain`,
  `isDedekindDomain_iff`;
- source-facing: the textbook implication that a principal ideal domain is a Dedekind domain;
- core/canonical: the owner class `IsDedekindDomain`;
- bridge/view: the instance `IsPrincipalIdealRing.isDedekindDomain`.

Primitive data are exactly the PID hypotheses `[IsDomain R] [IsPrincipalIdealRing R]`. The
Dedekind-domain structure is derived API already owned upstream, so this file should recall that
owner instance directly and not introduce any parallel local wrapper or restatement.
-/

/- Lemma 10.120.15: a principal ideal domain is a Dedekind domain. This is exactly the canonical
mathlib instance `IsPrincipalIdealRing.isDedekindDomain`. -/
recall IsPrincipalIdealRing.isDedekindDomain

/-! ### Lemma_10_120_16 (from Chap10) -/
universe u

section

open scoped Pointwise

variable {A : Type u} [CommRing A]

/-- Helper for Lemma 10.120.16: if `I * J` is generated by `x * y` with `y` regular and
`x ∈ I`, `y ∈ J`, then `I` is the principal ideal generated by `x`. -/
lemma ideal_eq_span_singleton_of_mul_eq_span_singleton_right_regular
    {S : Type*} [CommRing S] (I J : Ideal S) (x y : S)
    (hx : x ∈ I) (hy : y ∈ J) (hyreg : IsRegular y)
    (hIJ : I * J = Ideal.span ({x * y} : Set S)) :
    I = Ideal.span ({x} : Set S) := by
  refine le_antisymm ?_ ?_
  · -- Multiply an arbitrary element of `I` by the chosen `y ∈ J`, use the principal-product
    -- description, and then cancel the regular factor `y`.
    intro z hz
    have hz_mul : z * y ∈ I * J := Ideal.mul_mem_mul hz hy
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (hIJ ▸ hz_mul)
    have hcancel : z = a * x := by
      apply sub_eq_zero.mp
      have hzero : (z - a * x) * y = 0 := by
        calc
          (z - a * x) * y = z * y - (a * x) * y := by ring
          _ = z * y - a * (x * y) := by ring
          _ = 0 := by rw [ha, sub_self]
      exact hyreg.2.mul_right_eq_zero_iff.mp hzero
    exact Ideal.mem_span_singleton'.mpr ⟨a, by simpa [hcancel]⟩
  · -- The generator `x` already lies in `I`, so its principal ideal is contained in `I`.
    refine Ideal.span_le.mpr ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    simpa [hz] using hx

/-- Helper for Lemma 10.120.16: if `I * J` is generated by `x * y` with `x` and `y` regular and
`x ∈ I`, `y ∈ J`, then `I` and `J` are exactly the principal ideals generated by `x` and `y`. -/
lemma ideal_pair_eq_span_singletons_of_mul_eq_span_singleton_regular
    {S : Type*} [CommRing S] (I J : Ideal S) (x y : S)
    (hx : x ∈ I) (hy : y ∈ J) (hxreg : IsRegular x) (hyreg : IsRegular y)
    (hIJ : I * J = Ideal.span ({x * y} : Set S)) :
    I = Ideal.span ({x} : Set S) ∧ J = Ideal.span ({y} : Set S) := by
  constructor
  · -- Cancel the regular factor `y` to identify `I`.
    exact ideal_eq_span_singleton_of_mul_eq_span_singleton_right_regular
      I J x y hx hy hyreg hIJ
  · -- Swap the two factors and cancel the regular factor `x` to identify `J`.
    have hmul : J * I = Ideal.span ({y * x} : Set S) := by
      simpa [Ideal.mul_comm, mul_comm] using hIJ
    exact ideal_eq_span_singleton_of_mul_eq_span_singleton_right_regular
      J I y x hy hx hxreg hmul

/-- Helper for Lemma 10.120.16: a principal ideal generated by a regular element is free of
rank `1`. -/
lemma ideal_span_singleton_linearEquiv_fin_one_of_isRegular
    {S : Type*} [CommRing S] (x : S) (hx : IsRegular x) :
    Nonempty (((Ideal.span ({x} : Set S)) : Submodule S S) ≃ₗ[S] (Fin 1 → S)) := by
  let φ : S →ₗ[S] S := LinearMap.toSpanSingleton S S x
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    apply sub_eq_zero.mp
    have hsub : φ (a - b) = 0 := by
      simpa [LinearMap.map_sub] using sub_eq_zero.mpr hab
    have hzero : (a - b) * x = 0 := by
      simpa [φ, smul_eq_mul, mul_comm] using hsub
    exact hx.2.mul_right_eq_zero_iff.mp hzero
  let eRange : S ≃ₗ[S] LinearMap.range φ := LinearEquiv.ofInjective φ hφ_inj
  let eSpan : LinearMap.range φ ≃ₗ[S] ((Ideal.span ({x} : Set S)) : Submodule S S) :=
    LinearEquiv.ofEq _ _ (LinearMap.range_toSpanSingleton x)
  -- First identify the principal ideal with the range of multiplication by `x`, then use the
  -- unique rank-one free model `(Fin 1 → S)`.
  exact ⟨eSpan.symm.trans eRange.symm |>.trans
    (LinearEquiv.funUnique (Fin 1) S S).symm⟩

/-- Helper for Lemma 10.120.16: from `f ∈ I * J`, extract a finite family of products
`xᵢ * yᵢ` summing to `f`, together with the standard-open cover coefficients relating each term to
the principal generator `f`. -/
lemma mul_eq_span_singleton_regular_cover_data
    (I J : Ideal A) (f : A) (hf : IsRegular f)
    (hIJ : I * J = Ideal.span ({f} : Set A)) :
    ∃ (s : Finset A) (x y a : s → A),
      (∀ i, x i ∈ I) ∧
      (∀ i, y i ∈ J) ∧
      f = ∑ i : s, x i * y i ∧
      (∀ i, x i * y i = a i * f) ∧
      Ideal.span (Set.range a) = ⊤ := by
  classical
  have hf_mem_mul : f ∈ I * J := by
    rw [hIJ]
    exact Ideal.subset_span (by simp)
  have hmul_span : I * J = Ideal.span ((I : Set A) * (J : Set A)) := by
    simpa [I.span_eq, J.span_eq] using (Ideal.span_mul_span' (I : Set A) (J : Set A))
  have hf_span : f ∈ Ideal.span ((I : Set A) * (J : Set A)) := by
    exact hmul_span ▸ hf_mem_mul
  -- First shrink the source expression for `f` to a finite set of pairwise products.
  obtain ⟨s, hs, hf_s⟩ := Submodule.mem_span_finite_of_mem_span hf_span
  obtain ⟨c, hc⟩ := (Submodule.mem_span_finset').mp hf_s
  have hs_prod : ∀ z : s, ∃ u ∈ I, ∃ v ∈ J, u * v = z.1 := by
    intro z
    exact hs z.2
  choose u huI v hvJ huv using hs_prod
  let x : s → A := fun z ↦ c z * u z
  let y : s → A := fun z ↦ v z
  have hx_mem : ∀ z : s, x z ∈ I := by
    intro z
    dsimp [x]
    exact I.mul_mem_left _ (huI z)
  have hy_mem : ∀ z : s, y z ∈ J := hvJ
  have hsum : f = ∑ z : s, x z * y z := by
    -- Absorb each linear-combination coefficient into the `I`-factor.
    calc
      f = ∑ z : s, c z * z.1 := by
        simpa [smul_eq_mul] using hc.symm
      _ = ∑ z : s, x z * y z := by
        apply Finset.sum_congr rfl
        intro z hz
        dsimp [x, y]
        rw [← huv z]
        ring
  have hterm_mem : ∀ z : s, x z * y z ∈ Ideal.span ({f} : Set A) := by
    intro z
    rw [← hIJ]
    exact Ideal.mul_mem_mul (hx_mem z) (hy_mem z)
  choose a ha using fun z : s ↦ Ideal.mem_span_singleton'.mp (hterm_mem z)
  have hsum_mul : (∑ z : s, a z) * f = f := by
    -- Summing the individual scalar multiples reconstructs `f`.
    calc
      (∑ z : s, a z) * f = ∑ z : s, a z * f := by
        rw [Finset.sum_mul]
      _ = ∑ z : s, x z * y z := by
        apply Finset.sum_congr rfl
        intro z hz
        exact ha z
      _ = f := hsum.symm
  have hsuma : ∑ z : s, a z = 1 := by
    apply sub_eq_zero.mp
    have hzero : ((∑ z : s, a z) - 1) * f = 0 := by
      calc
        ((∑ z : s, a z) - 1) * f = (∑ z : s, a z) * f - 1 * f := by ring
        _ = 0 := by rw [hsum_mul, one_mul, sub_self]
    exact hf.2.mul_right_eq_zero_iff.mp hzero
  have hcover : Ideal.span (Set.range a) = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    have hone_mem : ∑ z : s, a z ∈ Ideal.span (Set.range a) := by
      exact (Ideal.span (Set.range a)).sum_mem fun z hz ↦ Ideal.subset_span ⟨z, rfl⟩
    rw [hsuma] at hone_mem
    simpa using hone_mem
  exact ⟨s, x, y, a, hx_mem, hy_mem, hsum, fun z ↦ (ha z).symm, hcover⟩

/-- Helper for Lemma 10.120.16: after localizing away from one cover coefficient, the two mapped
ideals become principal and are generated by regular elements. -/
lemma localized_pair_eq_span_singletons_of_cover_component
    (I J : Ideal A) (f a x y : A)
    (hx : x ∈ I) (hy : y ∈ J) (hxy : x * y = a * f)
    (hf : IsRegular f) (hIJ : I * J = Ideal.span ({f} : Set A)) :
    ∃ x' y' : Localization.Away a,
      x' ∈ Ideal.map (algebraMap A (Localization.Away a)) I ∧
      y' ∈ Ideal.map (algebraMap A (Localization.Away a)) J ∧
      IsRegular x' ∧
      IsRegular y' ∧
      Ideal.map (algebraMap A (Localization.Away a)) I = Ideal.span ({x'} : Set (Localization.Away a)) ∧
      Ideal.map (algebraMap A (Localization.Away a)) J = Ideal.span ({y'} : Set (Localization.Away a)) := by
  let S := Localization.Away a
  let aUnit : Units S :=
    (IsLocalization.map_units S (⟨a, 1, by simp⟩ : Submonoid.powers a)).unit
  let x' : S := algebraMap A S x
  let y' : S := ((aUnit⁻¹ : Units S) : S) * algebraMap A S y
  have hx'_mem : x' ∈ Ideal.map (algebraMap A S) I := by
    dsimp [x']
    exact Ideal.mem_map_of_mem _ hx
  have hy'_mem : y' ∈ Ideal.map (algebraMap A S) J := by
    dsimp [y']
    exact Ideal.mul_mem_left (a := ((aUnit⁻¹ : Units S) : S)) (I := Ideal.map (algebraMap A S) J)
      (Ideal.mem_map_of_mem _ hy)
  have hprod : x' * y' = algebraMap A S f := by
    -- Inverting `a` turns the displayed relation into a genuine factorization of `f`.
    calc
      x' * y' = ((aUnit⁻¹ : Units S) : S) * (algebraMap A S x * algebraMap A S y) := by
        dsimp [x', y']
        ring
      _ = ((aUnit⁻¹ : Units S) : S) * (algebraMap A S a * algebraMap A S f) := by
        rw [← map_mul, hxy, map_mul]
      _ = ((aUnit⁻¹ : Units S) : S) * ((aUnit : S) * algebraMap A S f) := by
        rfl
      _ = algebraMap A S f := by
        simp
  have hmapf : IsRegular (algebraMap A S f) := by
    rw [isRegular_iff_mem_nonZeroDivisors]
    exact IsLocalization.map_nonZeroDivisors_le (M := Submonoid.powers a) (S := S)
      ⟨f, isRegular_iff_mem_nonZeroDivisors.mp hf, rfl⟩
  have hprod_mem : x' * y' ∈ nonZeroDivisors S := by
    rw [hprod]
    exact isRegular_iff_mem_nonZeroDivisors.mp hmapf
  have hx'_reg : IsRegular x' := by
    rw [isRegular_iff_mem_nonZeroDivisors]
    exact (mul_mem_nonZeroDivisors.mp hprod_mem).1
  have hy'_reg : IsRegular y' := by
    rw [isRegular_iff_mem_nonZeroDivisors]
    exact (mul_mem_nonZeroDivisors.mp hprod_mem).2
  have hmap :
      Ideal.map (algebraMap A S) I * Ideal.map (algebraMap A S) J =
        Ideal.span ({algebraMap A S f} : Set S) := by
    -- Localize the product equality before applying the cancellation lemma.
    rw [← Ideal.map_mul, hIJ, Ideal.map_span, Set.image_singleton]
  have hpair :
      Ideal.map (algebraMap A S) I = Ideal.span ({x'} : Set S) ∧
        Ideal.map (algebraMap A S) J = Ideal.span ({y'} : Set S) := by
    exact ideal_pair_eq_span_singletons_of_mul_eq_span_singleton_regular
      (Ideal.map (algebraMap A S) I) (Ideal.map (algebraMap A S) J) x' y'
      hx'_mem hy'_mem hx'_reg hy'_reg (by simpa [hprod] using hmap)
  exact ⟨x', y', hx'_mem, hy'_mem, hx'_reg, hy'_reg, hpair.1, hpair.2⟩

/-- Helper for Lemma 10.120.16: if the away-localized ideal map is principal with a regular
generator, then the localized ideal module is the standard rank-one free module. -/
lemma localizedModuleAway_equiv_fin_one_of_map_span_singleton_regular
    (a : A) (I : Ideal A) (x : Localization.Away a)
    (hx : IsRegular x)
    (hI : Ideal.map (algebraMap A (Localization.Away a)) I =
      Ideal.span ({x} : Set (Localization.Away a))) :
    Nonempty (LocalizedModule.Away a I ≃ₗ[Localization.Away a] (Fin 1 → Localization.Away a)) := by
  let S := Localization.Away a
  -- Route correction: use the canonical submodule-localization comparison instead of introducing a
  -- bespoke owner-level transport between `LocalizedModule.Away a I` and `Ideal.map ... I`.
  let eLocalized :
      I.localized' S (.powers a) (Algebra.linearMap A S) ≃ₗ[S] LocalizedModule.Away a I :=
    (IsLocalizedModule.linearEquiv (.powers a)
      (Submodule.toLocalized' S (.powers a) (Algebra.linearMap A S) I)
      (LocalizedModule.mkLinearMap (.powers a) I)).extendScalarsOfIsLocalization (.powers a) S
  let eMap :
      I.localized' S (.powers a) (Algebra.linearMap A S) ≃ₗ[S]
        Ideal.map (algebraMap A S) I :=
    LinearEquiv.ofEq _ _ (Ideal.localized'_eq_map S (.powers a) I)
  obtain ⟨ePrincipal⟩ := ideal_span_singleton_linearEquiv_fin_one_of_isRegular x hx
  -- First rewrite the localized submodule as the mapped ideal, then compose with the principal
  -- rank-one model.
  exact ⟨(eMap.symm.trans eLocalized).symm.trans
    ((LinearEquiv.ofEq _ _ hI).trans ePrincipal)⟩

/- Domain triage:
- primary domain: commutative algebra of locally principal ideals and finite locally free modules;
- sampled owner declarations:
  `Ideal.FG`,
  `Module.FiniteLocallyFreeOfRank`,
  `Module.finiteLocallyFree_ofRank`,
  `Submodule.FG.of_finite`,
  `module_finite_projective_tfae`;
- owner abstraction: the source-facing conclusion naturally lives in the paired owner predicates
  `I.FG` and `Module.FiniteLocallyFreeOfRank A I 1` for an ideal viewed as an `A`-module;
- primitive data: the ideals `I`, `J`, the regular element `f`, and the factorization
  `I * J = Ideal.span ({f} : Set A)`;
- derived API: the finite-generation half is obtained from rank-one local freeness through the
  canonical bridge `Module.finiteLocallyFree_ofRank`, `module_finite_projective_tfae`, and
  `Submodule.FG.of_finite`.

The numbered theorem is `source-facing`; the rank-one statement is a thin `bridge/view` companion
reusing the chapter owner abstraction.
-/

-- Proof sketch: localize at a standard-open cover obtained from a finite expression
-- `f = ∑ xᵢ yᵢ` with `xᵢ ∈ I` and `yᵢ ∈ J`. On each localized piece one has a factorization
-- `f = x * y` with `x ∈ I` and `y ∈ J`, and regularity of `f` shows `I` and `J` become the
-- principal ideals `(x)` and `(y)`, so the canonical local condition
-- `Module.FiniteLocallyFreeOfRank A _ 1` holds for both ideals.
/-- A companion rank-one local freeness statement for the two factors in a principal product. -/
theorem ideal_finiteLocallyFreeOfRank_one_of_mul_eq_span_singleton_regular
    (I J : Ideal A) (f : A) (hf : IsRegular f)
    (hIJ : I * J = Ideal.span ({f} : Set A)) :
    Module.FiniteLocallyFreeOfRank A I 1 ∧ Module.FiniteLocallyFreeOfRank A J 1 := by
  rcases mul_eq_span_singleton_regular_cover_data I J f hf hIJ with
    ⟨s, x, y, a, hx, hy, _hsum, hxy, hcover⟩
  constructor
  · refine ⟨⟨Set.range a, hcover, ?_⟩⟩
    intro b hb
    rcases hb with ⟨i, rfl⟩
    -- Localize along the chosen cover coefficient and principalize the mapped ideal there.
    rcases localized_pair_eq_span_singletons_of_cover_component
      I J f (a i) (x i) (y i) (hx i) (hy i) (hxy i) hf hIJ with
      ⟨x', y', hx'_mem, hy'_mem, hx'_reg, hy'_reg, hIspan, hJspan⟩
    exact localizedModuleAway_equiv_fin_one_of_map_span_singleton_regular
      (a := a i) (I := I) (x := x') hx'_reg hIspan
  · refine ⟨⟨Set.range a, hcover, ?_⟩⟩
    intro b hb
    rcases hb with ⟨i, rfl⟩
    -- The same localized factorization simultaneously principalizes the `J`-factor.
    rcases localized_pair_eq_span_singletons_of_cover_component
      I J f (a i) (x i) (y i) (hx i) (hy i) (hxy i) hf hIJ with
      ⟨x', y', hx'_mem, hy'_mem, hx'_reg, hy'_reg, hIspan, hJspan⟩
    exact localizedModuleAway_equiv_fin_one_of_map_span_singleton_regular
      (a := a i) (I := J) (x := y') hy'_reg hJspan

-- Proof sketch: deduce local freeness of rank `1` for `I` from the companion theorem, and then
-- pass from finite locally free to finite generation for ideals over a commutative ring.
/-- Lemma 10.120.16 (1): if ideals `I` and `J` satisfy `I * J = (f)` for a nonzerodivisor `f`,
then the ideal `I` is finitely generated. -/
theorem ideal_left_fg_of_mul_eq_span_singleton_regular
    (I J : Ideal A) (f : A) (hf : IsRegular f)
    (hIJ : I * J = Ideal.span ({f} : Set A)) : I.FG := by
  -- First obtain the source-faithful rank-one local-freeness statement.
  have hloc :
      Module.FiniteLocallyFreeOfRank A I 1 :=
    (ideal_finiteLocallyFreeOfRank_one_of_mul_eq_span_singleton_regular I J f hf hIJ).1
  let _ : Module.FiniteLocallyFreeOfRank A I 1 := hloc
  let _ : Module.FiniteLocallyFree A I := Module.finiteLocallyFree_ofRank (R := A) (M := I) 1
  let _ : Module.Finite A I := Module.finite_of_finiteLocallyFree (R := A) (M := I)
  -- Finite generation of the ideal follows from finite generation of the underlying module.
  exact Submodule.FG.of_finite

-- Proof sketch: this is the `I`-component of the companion rank-one local freeness theorem.
/-- Lemma 10.120.16 (2): if ideals `I` and `J` satisfy `I * J = (f)` for a nonzerodivisor `f`,
then the ideal `I` is finite locally free of rank `1` as an `A`-module. -/
theorem ideal_left_finiteLocallyFreeOfRank_one_of_mul_eq_span_singleton_regular
    (I J : Ideal A) (f : A) (hf : IsRegular f)
    (hIJ : I * J = Ideal.span ({f} : Set A)) :
    Module.FiniteLocallyFreeOfRank A I 1 := by
  -- Project the `I`-component from the companion rank-one local-freeness theorem.
  exact (ideal_finiteLocallyFreeOfRank_one_of_mul_eq_span_singleton_regular I J f hf hIJ).1

-- Proof sketch: deduce local freeness of rank `1` for `J` from the companion theorem, and then
-- pass from finite locally free to finite generation for ideals over a commutative ring.
/-- Lemma 10.120.16 (3): if ideals `I` and `J` satisfy `I * J = (f)` for a nonzerodivisor `f`,
then the ideal `J` is finitely generated. -/
theorem ideal_right_fg_of_mul_eq_span_singleton_regular
    (I J : Ideal A) (f : A) (hf : IsRegular f)
    (hIJ : I * J = Ideal.span ({f} : Set A)) : J.FG := by
  -- First obtain the source-faithful rank-one local-freeness statement.
  have hloc :
      Module.FiniteLocallyFreeOfRank A J 1 :=
    (ideal_finiteLocallyFreeOfRank_one_of_mul_eq_span_singleton_regular I J f hf hIJ).2
  let _ : Module.FiniteLocallyFreeOfRank A J 1 := hloc
  let _ : Module.FiniteLocallyFree A J := Module.finiteLocallyFree_ofRank (R := A) (M := J) 1
  let _ : Module.Finite A J := Module.finite_of_finiteLocallyFree (R := A) (M := J)
  -- Finite generation of the ideal follows from finite generation of the underlying module.
  exact Submodule.FG.of_finite

-- Proof sketch: this is the `J`-component of the companion rank-one local freeness theorem.
/-- Lemma 10.120.16 (4): if ideals `I` and `J` satisfy `I * J = (f)` for a nonzerodivisor `f`,
then the ideal `J` is finite locally free of rank `1` as an `A`-module. -/
theorem ideal_right_finiteLocallyFreeOfRank_one_of_mul_eq_span_singleton_regular
    (I J : Ideal A) (f : A) (hf : IsRegular f)
    (hIJ : I * J = Ideal.span ({f} : Set A)) :
    Module.FiniteLocallyFreeOfRank A J 1 := by
  -- Project the `J`-component from the companion rank-one local-freeness theorem.
  exact (ideal_finiteLocallyFreeOfRank_one_of_mul_eq_span_singleton_regular I J f hf hIJ).2

end

/-! ### Lemma_10_120_17 (from Chap10) -/
universe u

section

variable (R : Type u) [CommRing R]

/-
Domain-style sampling:
- primary domain: Dedekind domains in commutative algebra, viewed through the source-facing
  factorization criterion and the canonical local-DVR owner;
- sampled owner declarations:
  `IsDedekindDomainByFactorization`,
  `isDedekindDomain_iff_isDedekindDomainByFactorization`,
  `IsDedekindDomainDvr`,
  `isDedekindDomain_iff`,
  `isIntegrallyClosed_iff`;
- source-facing: `IsDedekindDomainByFactorization R`;
- core/canonical: `IsDedekindDomain R` and `IsDedekindDomainDvr R`;
- bridge/view: the passages from the factorization criterion to the canonical local-DVR owner and
  to the canonical Noetherian plus dimension-`≤ 1` plus integrally-closed characterization.

Primitive data belong to the source-facing factorization owner from Definition `10.120.14`.
Noetherianity, the local DVR criterion, Krull dimension `≤ 1`, and integral closedness are
derived owner-level API, so this file should expose them by reusing the canonical owners and
their equivalence theorems rather than by publishing a new `List.TFAE` wrapper.
-/

/-- Lemma 10.120.17: the factorization criterion from Definition `10.120.14` is equivalent to the
canonical Noetherian, dimension-`≤ 1`, and integrally-closed characterization of a Dedekind
domain. This is the source-facing bridge to `isDedekindDomain_iff`. -/
theorem isDedekindDomainByFactorization_iff :
    IsDedekindDomainByFactorization R ↔
      IsDomain R ∧ IsNoetherianRing R ∧ Ring.DimensionLEOne R ∧ IsIntegrallyClosed R := by
  rw [← isDedekindDomain_iff_isDedekindDomainByFactorization R,
    isDedekindDomain_iff R (FractionRing R),
    isIntegrallyClosed_iff (FractionRing R)]

section

variable [IsDomain R]

/-- Under the ambient domain hypothesis needed to speak about `IsDedekindDomainDvr`, the
source-facing factorization criterion is equivalent to the canonical local-DVR owner. -/
theorem isDedekindDomainByFactorization_iff_isDedekindDomainDvr :
    IsDedekindDomainByFactorization R ↔ IsDedekindDomainDvr R := by
  constructor
  · intro h
    letI : IsDedekindDomain R :=
      (isDedekindDomain_iff_isDedekindDomainByFactorization R).mpr h
    infer_instance
  · intro h
    letI : IsDedekindDomainDvr R := h
    exact (isDedekindDomain_iff_isDedekindDomainByFactorization R).mp inferInstance

end

/-- A ring satisfying the factorization criterion for Dedekind domains is Noetherian. -/
theorem isNoetherianRing_of_isDedekindDomainByFactorization
    (h : IsDedekindDomainByFactorization R) : IsNoetherianRing R := by
  obtain ⟨-, hNoetherian, -, -⟩ := (isDedekindDomainByFactorization_iff R).mp h
  exact hNoetherian

/-- A ring satisfying the factorization criterion for Dedekind domains has Krull dimension at most
`1`. -/
theorem ringDimensionLEOne_of_isDedekindDomainByFactorization
    (h : IsDedekindDomainByFactorization R) : Ring.DimensionLEOne R := by
  obtain ⟨-, -, hDimensionLEOne, -⟩ := (isDedekindDomainByFactorization_iff R).mp h
  exact hDimensionLEOne

/-- A ring satisfying the factorization criterion for Dedekind domains is integrally closed. -/
theorem isIntegrallyClosed_of_isDedekindDomainByFactorization
    (h : IsDedekindDomainByFactorization R) : IsIntegrallyClosed R := by
  obtain ⟨-, -, -, hIntegrallyClosed⟩ := (isDedekindDomainByFactorization_iff R).mp h
  exact hIntegrallyClosed

end

/-! ### Lemma_10_120_18 (from Chap10) -/
universe u v

section

open PrimeSpectrum

variable {A : Type u} {L : Type v}
variable [CommRing A] [IsDomain A] [IsNoetherianRing A]
variable [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]

local notation "B" => integralClosure A L

/- Domain-style sampling:
- primary domain: integral closures in finite extensions of fraction fields of one-dimensional
  Noetherian domains, together with the induced prime-spectrum and residue-field behavior;
- sampled canonical/project owners:
  `IsDedekindDomain`,
  `Algebra.IsIntegral.comap_surjective`,
  `Ideal.primesOver`,
  `Ideal.primesOver_finite`,
  `moduleFinite_residueField_of_primeOver_maximalIdeal_of_finite_fractionField_extension`;
- best owner abstraction: the integral-closure owner `B = integralClosure A L`, with
  `IsDedekindDomain B` as the canonical ambient owner once Lemma `10.120.18` proves it;
- primitive data: the ambient extension tower `A ⊆ FractionRing A ⊆ L` and the owner ring `B`;
- derived API: surjectivity of `Spec(B) → Spec(A)`, finiteness of the fibers `p.primesOver B`,
  and finiteness of the residue-field extensions.

Source/core/bridge triage:
- `source-facing`: the Dedekind-domain, finite-fiber, and residue-field-finiteness statements
  specialized to `B = integralClosure A L` under the source hypothesis `ringKrullDim A = 1`;
- `core/canonical`: `IsDedekindDomain`, `Algebra.IsIntegral.comap_surjective`,
  `Ideal.primesOver_finite`, and the local one-dimensional fiber theorem from
  `Lemma_10_119_10`;
- `bridge/view`: the present file should only keep the source-facing bridges that add the
  dimension-one input. The spectrum-surjectivity clause is an exact canonical recall and should
  not survive as a parallel local theorem.
-/

-- Proof sketch: apply Krull-Akizuki to get that `B` is Noetherian, use integrality of
-- `A → B` to identify `ringKrullDim B = 1`, and then invoke the Dedekind-domain
-- characterization from Lemma `10.120.17`, noting that `B` is integrally closed by construction.
/-- Lemma 10.120.18: if `A` is a one-dimensional Noetherian domain and `L` is a finite extension
of `FractionRing A`, then the integral closure of `A` in `L` is a Dedekind domain. -/
theorem integralClosure_isDedekindDomain_of_ringKrullDim_eq_one
    (hdim : ringKrullDim A = 1) :
    IsDedekindDomain B := sorry

/- The map `Spec(integralClosure A L) → Spec(A)` induced by the inclusion
`A → integralClosure A L` is exactly the canonical integral-spectrum-surjectivity theorem
`Algebra.IsIntegral.comap_surjective`; the dimension-one hypothesis is redundant here and is
therefore removed from the public API. -/
recall Algebra.IsIntegral.comap_surjective

-- Proof sketch: if `p = 0`, then `B` is a domain and the only prime of `B` over `0` is `0`.
-- If `p ≠ 0`, then `p` is maximal because `A` has Krull dimension `1`; localize at `p` and apply
-- Lemma `10.119.10 (2)` to the resulting one-dimensional Noetherian local domain.
/-- For each `p : Spec(A)`, only finitely many prime ideals of `integralClosure A L` lie over
`p`. -/
theorem integralClosure_primesOver_finite_of_ringKrullDim_eq_one
    (hdim : ringKrullDim A = 1) (p : PrimeSpectrum A) :
    (p.asIdeal.primesOver B).Finite := sorry

-- Proof sketch: localize at the contraction of `q`, identify the localized extension of fraction
-- fields with a finite extension, and apply Lemma `10.119.10 (3)` to obtain finiteness of the
-- induced residue-field extension.
/-- For each `q : Spec(integralClosure A L)`, the residue field extension
`κ(comap q) → κ(q)` is finite. -/
theorem integralClosure_residueField_finite_of_ringKrullDim_eq_one
    (hdim : ringKrullDim A = 1) (q : PrimeSpectrum B) :
    Module.Finite (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.ResidueField
      q.asIdeal.ResidueField := sorry

end
