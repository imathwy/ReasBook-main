import StacksProject_2024.Chap10.Definition_10_37_11
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]

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
@[stacks 034M]
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
lemma atPrime_nonZeroDivisors_le [IsNormalRing R] (P : Ideal R) [P.IsPrime] :
    Algebra.algebraMapSubmonoid (Localization.AtPrime P) (nonZeroDivisors R) ≤
      nonZeroDivisors (Localization.AtPrime P) := by
  intro z hz
  rcases hz with ⟨y, hy, rfl⟩
  -- In the domain `R_P`, nonzerodivisors are exactly the nonzero elements.
  rw [mem_nonZeroDivisors_iff_ne_zero]
  exact map_ne_zero_atPrime_of_mem_nonZeroDivisors P hy

/-- Helper for Lemma 10.37.12: the localization subalgebra of `Frac(R_P)` obtained by inverting
the images of global nonzerodivisors is integrally closed. -/
lemma atPrime_totalFraction_subalgebra_isIntegrallyClosed [IsNormalRing R]
    (P : Ideal R) [P.IsPrime] :
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
lemma exists_atPrime_preimage_in_totalFraction [IsNormalRing R] {x : FractionRing R}
    (hx : IsIntegral R x) (P : Ideal R) [P.IsPrime] :
    let Tp := Localization (Algebra.algebraMapSubmonoid (FractionRing R) P.primeCompl)
    ∃ z : Localization.AtPrime P,
      algebraMap (FractionRing R) Tp x =
        algebraMap (Localization.AtPrime P) Tp z := by
  -- Route correction: the direct `Frac(R_P)` route is stable once the localization algebra
  -- instances are named explicitly instead of left to typeclass search.
  let M := Algebra.algebraMapSubmonoid (Localization.AtPrime P) (nonZeroDivisors R)
  let Tp := Localization (Algebra.algebraMapSubmonoid (FractionRing R) P.primeCompl)
  letI : Algebra (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) :=
    OreLocalization.instAlgebra
  have hFracAtPrime :
      IsFractionRing (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) := by
    exact inferInstanceAs (IsLocalization (nonZeroDivisors (Localization.AtPrime P))
      (FractionRing (Localization.AtPrime P)))
  letI : IsFractionRing (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) :=
    hFracAtPrime
  have hRToAtPrime :
      nonZeroDivisors R ≤
        Submonoid.comap (algebraMap R (Localization.AtPrime P))
          (nonZeroDivisors (Localization.AtPrime P)) := by
    -- Global nonzerodivisors remain nonzerodivisors in the prime localization.
    intro y hy
    exact atPrime_nonZeroDivisors_le (R := R) P ⟨y, hy, rfl⟩
  let mapToAtPrimeFraction :
      FractionRing R →+* FractionRing (Localization.AtPrime P) :=
    IsLocalization.map (S := FractionRing R)
      (Q := FractionRing (Localization.AtPrime P))
      (algebraMap R (Localization.AtPrime P)) hRToAtPrime
  have hIntegralAtPrime :
      IsIntegral (Localization.AtPrime P) (mapToAtPrimeFraction x) := by
    -- Transport integrality from `R` to `R_P` along the canonical map of fraction rings.
    refine IsIntegral.map_of_comp_eq (algebraMap R (Localization.AtPrime P))
      mapToAtPrimeFraction ?_ hx
    exact (IsLocalization.map_comp (S := FractionRing R)
      (Q := FractionRing (Localization.AtPrime P)) hRToAtPrime).symm
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hIntegralAtPrime
  refine ⟨z, ?_⟩
  have hM : M ≤ nonZeroDivisors (Localization.AtPrime P) :=
    atPrime_nonZeroDivisors_le (R := R) P
  have hTp : IsLocalization M Tp := atPrime_totalFraction_isLocalization (R := R) P
  letI : IsLocalization M Tp := hTp
  let mapTpToFraction :
      Tp →+* FractionRing (Localization.AtPrime P) :=
    IsLocalization.lift (S := Tp) (P := FractionRing (Localization.AtPrime P))
      (fun y : M => IsLocalization.map_units (FractionRing (Localization.AtPrime P))
        ⟨(y : Localization.AtPrime P), hM y.2⟩)
  have hcompAtPrime :
      mapTpToFraction.comp (algebraMap (Localization.AtPrime P) Tp) =
        algebraMap (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) := by
    -- The lift from `Tp` to `Frac(R_P)` is chosen to commute with `R_P`.
    exact IsLocalization.lift_comp (M := M) (S := Tp)
      (P := FractionRing (Localization.AtPrime P))
      (g := algebraMap (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)))
      (fun y : M => IsLocalization.map_units (FractionRing (Localization.AtPrime P))
        ⟨(y : Localization.AtPrime P), hM y.2⟩)
  have hcompFraction :
      mapTpToFraction.comp (algebraMap (FractionRing R) Tp) =
        mapToAtPrimeFraction := by
    -- The two maps out of `FractionRing R` agree after checking the original ring generators.
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    ext r
    simp only [RingHom.coe_comp, Function.comp_apply]
    have hleft :
        mapTpToFraction
            ((algebraMap (FractionRing R) Tp) ((algebraMap R (FractionRing R)) r)) =
          mapTpToFraction
            ((algebraMap (Localization.AtPrime P) Tp)
              ((algebraMap R (Localization.AtPrime P)) r)) := by
      rw [← IsScalarTower.algebraMap_apply R (FractionRing R) Tp r]
      rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime P) Tp r]
    calc
      mapTpToFraction
          ((algebraMap (FractionRing R) Tp) ((algebraMap R (FractionRing R)) r))
          = mapTpToFraction
              ((algebraMap (Localization.AtPrime P) Tp)
                ((algebraMap R (Localization.AtPrime P)) r)) := hleft
      _ = (algebraMap (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)))
            ((algebraMap R (Localization.AtPrime P)) r) := DFunLike.congr_fun hcompAtPrime _
      _ = mapToAtPrimeFraction ((algebraMap R (FractionRing R)) r) :=
          (IsLocalization.map_eq (S := FractionRing R)
            (Q := FractionRing (Localization.AtPrime P)) hRToAtPrime r).symm
  let algTp : Algebra Tp (FractionRing (Localization.AtPrime P)) :=
    mapTpToFraction.toAlgebra
  letI : Algebra Tp (FractionRing (Localization.AtPrime P)) := algTp
  letI : SMul Tp (FractionRing (Localization.AtPrime P)) := algTp.toSMul
  have hTower :
      IsScalarTower (Localization.AtPrime P) Tp
        (FractionRing (Localization.AtPrime P)) := by
    -- This scalar tower records that the explicit lift is the algebra map from `Tp`.
    refine IsScalarTower.of_algebraMap_eq' ?_
    rw [RingHom.algebraMap_toAlgebra]
    exact hcompAtPrime.symm
  letI : IsScalarTower (Localization.AtPrime P) Tp
      (FractionRing (Localization.AtPrime P)) := hTower
  have hFraction :
      @IsFractionRing Tp _ (FractionRing (Localization.AtPrime P)) _ algTp := by
    exact IsFractionRing.isFractionRing_of_isLocalization M Tp
      (FractionRing (Localization.AtPrime P)) hM
  have hinj : Function.Injective mapTpToFraction := by
    -- Since `Frac(R_P)` is a fraction ring of `Tp`, the canonical map from `Tp` is injective.
    have hinjAlg : Function.Injective
        ((@algebraMap Tp (FractionRing (Localization.AtPrime P)) _ _ algTp) :
          Tp → FractionRing (Localization.AtPrime P)) :=
      @IsFractionRing.injective Tp _ (FractionRing (Localization.AtPrime P)) _ algTp hFraction
    simpa [RingHom.algebraMap_toAlgebra, algTp] using hinjAlg
  apply hinj
  calc
    mapTpToFraction (algebraMap (FractionRing R) Tp x)
        = mapToAtPrimeFraction x := by
          exact DFunLike.congr_fun hcompFraction x
    _ = algebraMap (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) z :=
        hz.symm
    _ = mapTpToFraction (algebraMap (Localization.AtPrime P) Tp z) := by
          exact (DFunLike.congr_fun hcompAtPrime z).symm

/-- Helper for Lemma 10.37.12: an integral element of the total fraction ring has a denominator
outside any chosen prime ideal. -/
lemma exists_denominator_outside_prime_of_integral [IsNormalRing R] {x : FractionRing R}
    (hx : IsIntegral R x) (P : Ideal R) [P.IsPrime] :
    ∃ r : R, r ∈ P.primeCompl ∧ ∃ a : R,
      algebraMap R (FractionRing R) a = algebraMap R (FractionRing R) r * x := by
  let Tp := Localization (Algebra.algebraMapSubmonoid (FractionRing R) P.primeCompl)
  obtain ⟨z, hz⟩ := exists_atPrime_preimage_in_totalFraction (R := R) hx P
  obtain ⟨⟨a, s⟩, hzs⟩ := IsLocalization.surj P.primeCompl z
  have hmap := congrArg (algebraMap (Localization.AtPrime P) Tp) hzs
  have hAeq :
      algebraMap (FractionRing R) Tp (algebraMap R (FractionRing R) a) =
        algebraMap (Localization.AtPrime P) Tp
          (algebraMap R (Localization.AtPrime P) a) := by
    rw [← IsScalarTower.algebraMap_apply R (FractionRing R) Tp a]
    rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime P) Tp a]
  have hSeq :
      algebraMap (FractionRing R) Tp (algebraMap R (FractionRing R) s) =
        algebraMap (Localization.AtPrime P) Tp
          (algebraMap R (Localization.AtPrime P) s) := by
    rw [← IsScalarTower.algebraMap_apply R (FractionRing R) Tp s]
    rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime P) Tp s]
  have hLocal :
      algebraMap (FractionRing R) Tp (algebraMap R (FractionRing R) a) =
        algebraMap (FractionRing R) Tp (algebraMap R (FractionRing R) s) *
          algebraMap (Localization.AtPrime P) Tp z := by
    -- The representation of `z` in `R_P` becomes a denominator relation in `Tp`.
    calc
      algebraMap (FractionRing R) Tp (algebraMap R (FractionRing R) a)
          = algebraMap (Localization.AtPrime P) Tp
              (algebraMap R (Localization.AtPrime P) a) := hAeq
      _ = algebraMap (Localization.AtPrime P) Tp z *
            algebraMap (Localization.AtPrime P) Tp
              (algebraMap R (Localization.AtPrime P) s) := by
          simpa [map_mul] using hmap.symm
      _ = algebraMap (FractionRing R) Tp (algebraMap R (FractionRing R) s) *
            algebraMap (Localization.AtPrime P) Tp z := by
          rw [hSeq]
          ring
  have hEq :
      algebraMap (FractionRing R) Tp (algebraMap R (FractionRing R) a) =
        algebraMap (FractionRing R) Tp
          (algebraMap R (FractionRing R) s * x) := by
    -- Substitute the local preimage equality, so the two fractions become equal in `Tp`.
    calc
      algebraMap (FractionRing R) Tp (algebraMap R (FractionRing R) a)
          = algebraMap (FractionRing R) Tp (algebraMap R (FractionRing R) s) *
              algebraMap (Localization.AtPrime P) Tp z := hLocal
      _ = algebraMap (FractionRing R) Tp (algebraMap R (FractionRing R) s) *
              algebraMap (FractionRing R) Tp x := by rw [← hz]
      _ = algebraMap (FractionRing R) Tp
              (algebraMap R (FractionRing R) s * x) := by simp [map_mul]
  obtain ⟨t, htP, htclear⟩ :=
    exists_multiple_outside_prime_of_totalFraction_eq (R := R) P hEq
  refine ⟨t * s, mul_mem htP s.2, t * a, ?_⟩
  -- The clearing multiplier and the local denominator combine to a denominator outside `P`.
  calc
    algebraMap R (FractionRing R) (t * a)
        = algebraMap R (FractionRing R) t * algebraMap R (FractionRing R) a := by simp
    _ = algebraMap R (FractionRing R) t *
          (algebraMap R (FractionRing R) s * x) := htclear
    _ = algebraMap R (FractionRing R) (t * s) * x := by
        simp [map_mul, mul_assoc]

/-- Chap10 Lemma 10 37 12: a normal ring is integrally closed in its total ring of
fractions. -/
@[stacks 034M]
theorem isIntegrallyClosed_of_isNormalRing [IsNormalRing R] : IsIntegrallyClosed R := by
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

instance [IsNormalRing R] : IsIntegrallyClosed R := isIntegrallyClosed_of_isNormalRing

end
