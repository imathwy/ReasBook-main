import stacks_project.Chap10.Definition_10_37_11

-- Declarations for this item will be appended below by the statement pipeline.

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
