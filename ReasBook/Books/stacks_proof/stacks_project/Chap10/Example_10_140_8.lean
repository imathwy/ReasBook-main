import Mathlib
import StacksProject_2024.Chap10.Lemma_10_106_8
import StacksProject_2024.Chap10.Lemma_10_114_1

-- Declarations for this item will be appended below by the statement pipeline.

open MvPolynomial
open scoped RatFunc

noncomputable section

namespace Algebra

section

variable (p : ℕ) [Fact p.Prime]

/-
Domain-style sampling for Example 10.140.8:
- primary domain: positive-characteristic commutative-algebra counterexamples to smoothness,
  organized around quotient rings, prime-spectrum points, and the owner predicates
  `Smooth`/`IsSmoothAt`/`IsRegularLocalRing`;
- sampled owner declarations:
  `Ideal.Quotient.mk`,
  `Algebra.SmoothAtPrime`,
  `Algebra.smoothAtPrime_iff_isSmoothAt`,
  `IsRegularLocalRing`;
- best owner abstraction: the quotient map to a ring presented as a quotient should be the
  canonical owner `Ideal.Quotient.mk`, not a parallel local alias; the primewise smoothness
  failure is expressed on the canonical local owner `IsSmoothAt`, with the chapter's
  `SmoothAtPrime` available as the source-facing bridge when needed;
- primitive data: the quotient rings and the named prime ideal `q`;
- derived API: smoothness failure at `q` and regularity of the localization at `q`.

Source/core/bridge triage:
- `source-facing`: the concrete rings and the named prime `q = (y, x^p + t)` appearing in the
  example;
- `core/canonical`: `Ideal.Quotient.mk`, `IsSmoothAt`, and `IsRegularLocalRing`;
- `bridge/view`: `SmoothAtPrime` together with `smoothAtPrime_iff_isSmoothAt` for finitely
  presented algebras.
-/

/-- The quotient `F_p[x]/(x^p)` used for the first positive-characteristic counterexample. -/
abbrev charPNilpotentQuotient : Type :=
  Polynomial (ZMod p) ⧸ Ideal.span ({Polynomial.X ^ p} : Set (Polynomial (ZMod p)))

/-- Helper for Chap10 Example 10 140 8: the formal derivative of `X^p` over `F_p` vanishes. -/
lemma derivative_X_pow_zmod_eq_zero :
    Polynomial.derivative (Polynomial.X ^ p : Polynomial (ZMod p)) = 0 := by
  -- The derivative is `p * X^(p-1)`, and the scalar `p` is zero in `ZMod p`.
  rw [Polynomial.derivative_X_pow]
  simp

/-- Helper for Chap10 Example 10 140 8: the class of `X^p` is zero in
`F_p[X]/(X^p)`. -/
lemma charPNilpotentQuotient_X_pow_eq_zero :
    Ideal.Quotient.mk (Ideal.span ({Polynomial.X ^ p} : Set (Polynomial (ZMod p))))
        (Polynomial.X ^ p) = (0 : charPNilpotentQuotient p) := by
  -- This records the defining quotient relation as a reusable rewrite.
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- Helper for Chap10 Example 10 140 8: the class of `X` is nilpotent in
`F_p[X]/(X^p)`. -/
lemma charPNilpotentQuotient_X_isNilpotent :
    IsNilpotent
      (Ideal.Quotient.mk (Ideal.span ({Polynomial.X ^ p} : Set (Polynomial (ZMod p))))
        Polynomial.X : charPNilpotentQuotient p) := by
  -- Raising the class of `X` to the `p`th power gives the defining zero relation.
  refine ⟨p, ?_⟩
  rw [← map_pow]
  exact charPNilpotentQuotient_X_pow_eq_zero p

/-- Helper for Chap10 Example 10 140 8: the class of `X` is nonzero in
`F_p[X]/(X^p)`. -/
lemma charPNilpotentQuotient_X_ne_zero :
    (Ideal.Quotient.mk (Ideal.span ({Polynomial.X ^ p} : Set (Polynomial (ZMod p))))
        Polynomial.X : charPNilpotentQuotient p) ≠ 0 := by
  -- If `X` vanished, then `X^p` would divide `X`; comparing the coefficient of `X`
  -- contradicts `1 < p`.
  rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
  intro hmem
  rw [Ideal.mem_span_singleton] at hmem
  have hcoeff := (Polynomial.X_pow_dvd_iff.mp hmem) 1 (Fact.out : Nat.Prime p).one_lt
  simpa using hcoeff

/-- The coefficient field `F_p(t)` used in the plane-curve counterexample. -/
abbrev charPRationalFunctionField : Type :=
  RatFunc (ZMod p)

/-- Helper for Chap10 Example 10 140 8: the degree at infinity of a nonzero power in a rational
function field is the power times the degree of the base. -/
lemma ratFunc_intDegree_pow {K : Type*} [Field K] (x : RatFunc K) (hx : x ≠ 0) (n : ℕ) :
    RatFunc.intDegree (x ^ n) = (n : ℤ) * RatFunc.intDegree x := by
  -- The proof isolates the multiplicativity of `intDegree` so the Kummer obstruction can use it
  -- without repeatedly unfolding powers.
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n hx) hx, ih]
      rw [Nat.cast_add, Nat.cast_one]
      ring

/-- Helper for Chap10 Example 10 140 8: `-t` is not a `p`th power in `F_p(t)`. -/
lemma ratFunc_neg_X_not_pth_power :
    ∀ b : charPRationalFunctionField p,
      b ^ p ≠ -(RatFunc.X : charPRationalFunctionField p) := by
  intro b hb
  -- Comparing `intDegree` turns a hypothetical `p`th root into the impossible divisibility
  -- `p ∣ 1`.
  have hbne : b ≠ 0 := by
    intro hzero
    have hpne : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
    have hzero_eq_neg :
        (0 : charPRationalFunctionField p) = -(RatFunc.X : charPRationalFunctionField p) := by
      simpa [hzero, hpne] using hb
    have hX_zero : (RatFunc.X : charPRationalFunctionField p) = 0 := by
      simpa using (congrArg Neg.neg hzero_eq_neg).symm
    exact RatFunc.X_ne_zero hX_zero
  have hdegree :
      (p : ℤ) * RatFunc.intDegree b = 1 := by
    have hcongr :=
      congrArg RatFunc.intDegree hb
    simpa [ratFunc_intDegree_pow b hbne p, RatFunc.intDegree_neg, RatFunc.intDegree_X] using hcongr
  have hdivInt : (p : ℤ) ∣ (1 : ℤ) :=
    ⟨RatFunc.intDegree b, hdegree.symm⟩
  have hdivNat : p ∣ 1 := by
    exact_mod_cast hdivInt
  exact (Fact.out : Nat.Prime p).not_dvd_one hdivNat

/-- Helper for Chap10 Example 10 140 8: the polynomial `X^p + t` over `F_p(t)` is irreducible. -/
lemma ratFunc_X_pow_add_C_irreducible :
    Irreducible
      (Polynomial.X ^ p + Polynomial.C (RatFunc.X : charPRationalFunctionField p) :
        Polynomial (charPRationalFunctionField p)) := by
  -- Rewrite the target as a Kummer polynomial `X^p - C(-t)` and use the degree obstruction.
  have hrewrite :
      (Polynomial.X ^ p - Polynomial.C (-(RatFunc.X : charPRationalFunctionField p)) :
        Polynomial (charPRationalFunctionField p)) =
        Polynomial.X ^ p + Polynomial.C (RatFunc.X : charPRationalFunctionField p) := by
    simp [sub_eq_add_neg]
  rw [← hrewrite]
  exact X_pow_sub_C_irreducible_of_prime (Fact.out : Nat.Prime p)
    (ratFunc_neg_X_not_pth_power p)

/-- The bivariate polynomial ring over `F_p(t)` with coordinates `x` and `y`. -/
abbrev charPPlaneCurvePolynomialRing : Type :=
  MvPolynomial (Fin 2) (charPRationalFunctionField p)

/-- The defining equation `x^p + y^2 + t` of the plane-curve example over `F_p(t)`. -/
abbrev charPPlaneCurveEquation : charPPlaneCurvePolynomialRing p :=
  X (0 : Fin 2) ^ p + X (1 : Fin 2) ^ 2 + C (RatFunc.X : charPRationalFunctionField p)

/-- Helper for Chap10 Example 10 140 8: the plane-curve equation is nonzero in the
polynomial ring. -/
lemma charPPlaneCurveEquation_ne_zero :
    (charPPlaneCurveEquation p : charPPlaneCurvePolynomialRing p) ≠ 0 := by
  -- The three displayed monomials have distinct support, and the constant coefficient is `t`.
  intro hzero
  have hcoeff := congrArg (coeff (0 : Fin 2 →₀ ℕ)) hzero
  simp only [charPPlaneCurveEquation, coeff_add, coeff_X_pow, coeff_C, Fin.isValue] at hcoeff
  simp only [Finsupp.single_eq_zero, (Fact.out : Nat.Prime p).ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_zero, add_zero, zero_add] at hcoeff
  exact RatFunc.X_ne_zero hcoeff

/-- Helper for Chap10 Example 10 140 8: the differential of the plane-curve equation is
`2 y dy` in characteristic `p`. -/
lemma charPPlaneCurveEquation_differential :
    KaehlerDifferential.D (charPRationalFunctionField p) (charPPlaneCurvePolynomialRing p)
      (charPPlaneCurveEquation p) =
    ((2 : charPPlaneCurvePolynomialRing p) * X (1 : Fin 2)) •
      KaehlerDifferential.D (charPRationalFunctionField p) (charPPlaneCurvePolynomialRing p)
        (X (1 : Fin 2)) := by
  -- The `x^p` term has zero differential in characteristic `p`; the remaining derivative is
  -- the usual derivative of `y^2`.
  simp only [charPPlaneCurveEquation, map_add, Fin.isValue, Derivation.leibniz_pow,
    Nat.add_one_sub_one, pow_one, derivation_C, add_zero]
  rw [← Nat.cast_smul_eq_nsmul (charPPlaneCurvePolynomialRing p) p]
  rw [CharP.cast_eq_zero (charPPlaneCurvePolynomialRing p) p, zero_smul]
  rw [zero_add, mul_smul]
  exact (Nat.cast_smul_eq_nsmul (charPPlaneCurvePolynomialRing p) 2
    (X (1 : Fin 2) •
      KaehlerDifferential.D (charPRationalFunctionField p) (charPPlaneCurvePolynomialRing p)
        (X (1 : Fin 2)))).symm

/-- Helper for Chap10 Example 10 140 8: moving a scalar from the second tensor factor to
the residue-field factor when the first tensor factor is `1`. -/
lemma one_tmul_smul_eq_smul_one_tmul {R K M : Type*} [CommSemiring R] [CommSemiring K]
    [Algebra R K] [AddCommMonoid M] [Module R M] (r : R) (m : M) :
    (1 : K) ⊗ₜ[R] (r • m) = (r • (1 : K)) ⊗ₜ[R] m := by
  exact TensorProduct.tmul_smul (R := R) (R' := R) r (1 : K) m

/-- Helper for Chap10 Example 10 140 8: a tensor whose second factor is multiplied by a
scalar that vanishes in the first factor is zero. -/
lemma one_tmul_smul_eq_zero_of_algebraMap_eq_zero {R K M : Type*} [CommSemiring R]
    [CommSemiring K] [Algebra R K] [AddCommMonoid M] [Module R M]
    (r : R) (m : M) (hr : algebraMap R K r = 0) :
    (1 : K) ⊗ₜ[R] (r • m) = 0 := by
  rw [one_tmul_smul_eq_smul_one_tmul (R := R) (K := K) (M := M) r m]
  rw [Algebra.smul_def, hr, zero_mul]
  simp

/-- Helper for Chap10 Example 10 140 8: if a vector is a scalar multiple by a scalar
vanishing after base change, then its tensor with `1` is zero. -/
lemma one_tmul_eq_zero_of_eq_smul_of_algebraMap_eq_zero {R K M : Type*} [CommSemiring R]
    [CommSemiring K] [Algebra R K] [AddCommMonoid M] [Module R M]
    {x m : M} {r : R} (hx : x = r • m) (hr : algebraMap R K r = 0) :
    (1 : K) ⊗ₜ[R] x = 0 := by
  rw [hx]
  exact one_tmul_smul_eq_zero_of_algebraMap_eq_zero (R := R) (K := K) (M := M) r m hr

/-- Helper for Chap10 Example 10 140 8: an algebra homomorphism carries base scalars through
its structural scalar-commutation map. -/
lemma algHom_algebraMap_eq_apply {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B) (r : R) :
    algebraMap R B r = φ.toRingHom (algebraMap R A r) :=
  (φ.commutes r).symm

/-- Helper for Chap10 Example 10 140 8: the image of an element of the maximal ideal
under a local homomorphism vanishes in the target residue field. -/
lemma residueField_map_eq_zero_of_mem_maximalIdeal {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) (hf : IsLocalHom f) {a : R}
    (ha : a ∈ IsLocalRing.maximalIdeal R) :
    algebraMap S (IsLocalRing.ResidueField S) (f a) = 0 := by
  -- A local homomorphism maps the source maximal ideal into the target maximal ideal,
  -- which is precisely the kernel of the residue-field quotient.
  have hmap : f a ∈ IsLocalRing.maximalIdeal S := by
    exact @map_nonunit R S _ _ _ _ f hf a ha
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmap

/-- Helper for Chap10 Example 10 140 8: composing a local algebra map with the target
residue-field quotient kills the source maximal ideal. -/
lemma residueField_algebraMap_eq_zero_of_mem_maximalIdeal {R S : Type*} [CommRing R]
    [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S] (f : R →+* S)
    (hf : algebraMap R S = f) (hfLocal : IsLocalHom f) {a : R}
    (ha : a ∈ IsLocalRing.maximalIdeal R) :
    algebraMap R (IsLocalRing.ResidueField S) a = 0 := by
  -- Rewrite the composite algebra map through the chosen local homomorphism, then use
  -- the residue-field quotient calculation.
  rw [IsScalarTower.algebraMap_apply R S (IsLocalRing.ResidueField S) a, hf]
  exact residueField_map_eq_zero_of_mem_maximalIdeal f hfLocal ha

/-- Helper for Chap10 Example 10 140 8: a surjective algebra map remains surjective after
composition with the target residue-field quotient. -/
lemma residueField_algebraMap_surjective_of_surjective {R S : Type*} [CommRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    (hsurj : Function.Surjective (algebraMap R S)) :
    Function.Surjective (algebraMap R (IsLocalRing.ResidueField S)) := by
  -- Lift through the quotient map to the residue field, then lift the chosen representative
  -- through the given surjective algebra map.
  intro z
  obtain ⟨s, hs⟩ :=
    (Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal S) :
      Function.Surjective (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S))) z
  obtain ⟨r, hr⟩ := hsurj s
  refine ⟨r, ?_⟩
  rw [← hs, ← hr]
  rfl

/-- Helper for Chap10 Example 10 140 8: a cotangent-complex generator maps to zero after
base change when the differential is multiplied by a scalar killed by that base change. -/
lemma cotangentComplexBaseChange_tmul_eq_zero_of_D_eq_smul
    {R S P A : Type*} [CommRing R] [CommRing S] [CommRing P] [CommRing A]
    [Algebra R S] [Algebra P S] [Algebra P A] [Algebra R P] [Algebra S A]
    [IsScalarTower P S A] {f : P} {r : P} {m : Ω[P⁄R]}
    (hf : f ∈ RingHom.ker (algebraMap P S))
    (hD : KaehlerDifferential.D R P f = r • m) (hr : algebraMap P A r = 0) :
    KaehlerDifferential.cotangentComplexBaseChange R S P A
        ((1 : A) ⊗ₜ[P] (⟨f, hf⟩ : RingHom.ker (algebraMap P S))) = 0 := by
  -- The cotangent map sends the kernel generator to `1 ⊗ D(f)`, and the displayed
  -- scalar-multiple formula kills this tensor after base change.
  rw [KaehlerDifferential.cotangentComplexBaseChange_tmul]
  rw [one_smul]
  rw [KaehlerDifferential.kerToTensor_apply]
  exact one_tmul_eq_zero_of_eq_smul_of_algebraMap_eq_zero
    (R := P) (K := A) (M := Ω[P⁄R]) hD hr

/-- Helper for Chap10 Example 10 140 8: the differential formula for the plane-curve equation
is stable under any scalar-compatible algebra map out of the polynomial ring. -/
lemma charPPlaneCurveEquation_differential_map
    {T : Type*} [CommRing T] [Algebra (charPPlaneCurvePolynomialRing p) T]
    [Algebra (charPRationalFunctionField p) T]
    [IsScalarTower (charPRationalFunctionField p) (charPPlaneCurvePolynomialRing p) T] :
    KaehlerDifferential.D (charPRationalFunctionField p) T
      (algebraMap (charPPlaneCurvePolynomialRing p) T (charPPlaneCurveEquation p)) =
    algebraMap (charPPlaneCurvePolynomialRing p) T
      ((2 : charPPlaneCurvePolynomialRing p) * X (1 : Fin 2)) •
      KaehlerDifferential.D (charPRationalFunctionField p) T
        (algebraMap (charPPlaneCurvePolynomialRing p) T (X (1 : Fin 2))) := by
  -- Compute the differential after applying the algebra map; the `p`-term vanishes in
  -- characteristic `p`, and constants from the base have zero differential.
  simp only [charPPlaneCurveEquation, map_add, Fin.isValue, map_pow, Derivation.leibniz_pow,
    Nat.add_one_sub_one, pow_one, algebraMap_smul, map_mul]
  have hpT : (p : T) = 0 := by
    rw [← map_natCast (algebraMap (charPRationalFunctionField p) T)]
    rw [CharP.cast_eq_zero (charPRationalFunctionField p) p, map_zero]
  rw [← Nat.cast_smul_eq_nsmul T p]
  rw [hpT, zero_smul, zero_add]
  have hconst :
      KaehlerDifferential.D (charPRationalFunctionField p) T
        (algebraMap (charPPlaneCurvePolynomialRing p) T
          (C (RatFunc.X : charPRationalFunctionField p))) = 0 := by
    rw [← MvPolynomial.algebraMap_eq (charPRationalFunctionField p) (Fin 2)]
    rw [← IsScalarTower.algebraMap_apply
      (charPRationalFunctionField p) (charPPlaneCurvePolynomialRing p) T
      (RatFunc.X : charPRationalFunctionField p)]
    exact Derivation.map_algebraMap
      (KaehlerDifferential.D (charPRationalFunctionField p) T)
      (RatFunc.X : charPRationalFunctionField p)
  rw [hconst, add_zero]
  rw [mul_smul]
  have htwo :
      algebraMap (charPPlaneCurvePolynomialRing p) T
        (2 : charPPlaneCurvePolynomialRing p) = (2 : T) := by
    exact map_ofNat (algebraMap (charPPlaneCurvePolynomialRing p) T) 2
  rw [htwo]
  rw [← Nat.cast_smul_eq_nsmul T 2]
  let v :=
    KaehlerDifferential.D (charPRationalFunctionField p) T
      (algebraMap (charPPlaneCurvePolynomialRing p) T (X (1 : Fin 2)))
  have hXsmul :
      (X (1 : Fin 2) : charPPlaneCurvePolynomialRing p) • v =
        algebraMap (charPPlaneCurvePolynomialRing p) T (X (1 : Fin 2)) • v := by
    exact (algebraMap_smul T (X (1 : Fin 2)) v).symm
  exact congrArg (fun w ↦ (2 : T) • w) hXsmul

/-- Helper for Chap10 Example 10 140 8: the mapped differential formula with the coefficient
spelled as the product of the mapped factors. -/
lemma charPPlaneCurveEquation_differential_map_mul
    {T : Type*} [CommRing T] [Algebra (charPPlaneCurvePolynomialRing p) T]
    [Algebra (charPRationalFunctionField p) T]
    [IsScalarTower (charPRationalFunctionField p) (charPPlaneCurvePolynomialRing p) T] :
    KaehlerDifferential.D (charPRationalFunctionField p) T
      (algebraMap (charPPlaneCurvePolynomialRing p) T (charPPlaneCurveEquation p)) =
    (algebraMap (charPPlaneCurvePolynomialRing p) T (2 : charPPlaneCurvePolynomialRing p) *
      algebraMap (charPPlaneCurvePolynomialRing p) T (X (1 : Fin 2))) •
      KaehlerDifferential.D (charPRationalFunctionField p) T
        (algebraMap (charPPlaneCurvePolynomialRing p) T (X (1 : Fin 2))) := by
  simpa only [map_mul] using
    (charPPlaneCurveEquation_differential_map (p := p) (T := T))

/-- The quotient `F_p(t)[x, y]/(x^p + y^2 + t)` used for the second counterexample. -/
abbrev charPPlaneCurveQuotient : Type :=
  charPPlaneCurvePolynomialRing p ⧸
    Ideal.span ({charPPlaneCurveEquation p} : Set (charPPlaneCurvePolynomialRing p))

local notation "π" =>
  Ideal.Quotient.mk
    (Ideal.span ({charPPlaneCurveEquation p} : Set (charPPlaneCurvePolynomialRing p)))

/-- The ideal `(y, x^p + t)` in the plane-curve quotient ring. -/
def charPPlaneCurvePrimeIdeal : Ideal (charPPlaneCurveQuotient p) :=
  Ideal.span
    ({ π (X (1 : Fin 2)),
       π (X (0 : Fin 2) ^ p + C (RatFunc.X : charPRationalFunctionField p)) } :
      Set (charPPlaneCurveQuotient p))

/-- Helper for Chap10 Example 10 140 8: the relation in the plane-curve quotient identifies
`x^p + t` with `-y^2`. -/
lemma charPPlaneCurve_secondGenerator_eq_neg_y_sq :
    π (X (0 : Fin 2) ^ p + C (RatFunc.X : charPRationalFunctionField p)) =
      -π (X (1 : Fin 2)) ^ 2 := by
  -- First rewrite the defining relation into the generator order used by the ideal.
  have hrel : π (charPPlaneCurveEquation p) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hpoly :
      (X (0 : Fin 2) ^ p + C (RatFunc.X : charPRationalFunctionField p)) +
          X (1 : Fin 2) ^ 2 = charPPlaneCurveEquation p := by
    simp only [charPPlaneCurveEquation]
    ac_rfl
  have hsum :
      π ((X (0 : Fin 2) ^ p + C (RatFunc.X : charPRationalFunctionField p)) +
          X (1 : Fin 2) ^ 2) = 0 := by
    rw [hpoly]
    exact hrel
  -- Applying the quotient map to the reordered relation gives `z + y^2 = 0`.
  rw [eq_neg_iff_add_eq_zero]
  simpa only [map_add, map_pow] using hsum

/-- Helper for Chap10 Example 10 140 8: in the plane-curve quotient, the ideal
`(y, x^p + t)` is generated by `y` alone. -/
lemma charPPlaneCurvePrimeIdeal_eq_span_y :
    charPPlaneCurvePrimeIdeal p =
      Ideal.span ({π (X (1 : Fin 2))} : Set (charPPlaneCurveQuotient p)) := by
  -- The quotient relation rewrites `x^p + t` as `-y^2`, so the second generator
  -- is already a multiple of the first generator.
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with ha | ha
    · subst a
      exact Ideal.subset_span (Set.mem_singleton _)
    · subst a
      have hy :
          π (X (1 : Fin 2)) ∈
            Ideal.span ({π (X (1 : Fin 2))} : Set (charPPlaneCurveQuotient p)) :=
        Ideal.subset_span (Set.mem_singleton _)
      have hy2 :
          π (X (1 : Fin 2)) ^ 2 ∈
            Ideal.span ({π (X (1 : Fin 2))} : Set (charPPlaneCurveQuotient p)) := by
        simpa [pow_two] using
          (Ideal.span ({π (X (1 : Fin 2))} : Set (charPPlaneCurveQuotient p))).mul_mem_left
            (π (X (1 : Fin 2))) hy
      exact (charPPlaneCurve_secondGenerator_eq_neg_y_sq p).symm ▸
        (Ideal.span ({π (X (1 : Fin 2))} : Set (charPPlaneCurveQuotient p))).neg_mem hy2
  · -- The reverse inclusion is immediate because `y` is one of the named generators.
    refine Ideal.span_le.mpr ?_
    intro a ha
    simp only [Set.mem_singleton_iff] at ha
    subst a
    exact Ideal.subset_span (Set.mem_insert _ _)

/-- Helper for Chap10 Example 10 140 8: the one-variable polynomial obtained from the
plane-curve equation after setting `y = 0`. -/
abbrev planeCurveAdjoinPolynomial : Polynomial (charPRationalFunctionField p) :=
  Polynomial.X ^ p + Polynomial.C (RatFunc.X : charPRationalFunctionField p)

-- Route correction: instead of constructing the quotient by `y` directly, specialize the
-- plane-curve quotient to `AdjoinRoot (X^p + t)` and use the first isomorphism theorem.
/-- Helper for Chap10 Example 10 140 8: the specialization sending `x` to the adjoined
root of `X^p + t` and `y` to zero. -/
def planeCurveEvalToAdjoinRoot :
    charPPlaneCurvePolynomialRing p →ₐ[charPRationalFunctionField p]
      AdjoinRoot (planeCurveAdjoinPolynomial p) :=
  MvPolynomial.aeval fun i : Fin 2 =>
    if i = 0 then AdjoinRoot.root (planeCurveAdjoinPolynomial p) else 0

/-- Helper for Chap10 Example 10 140 8: the specialization to `AdjoinRoot (X^p + t)`
annihilates the defining plane-curve equation. -/
lemma planeCurveEvalToAdjoinRoot_eq_zero_on_equation :
    (planeCurveEvalToAdjoinRoot p) (charPPlaneCurveEquation p) = 0 := by
  -- The root relation in `AdjoinRoot` is exactly `root^p + t = 0`.
  have hroot :
      (AdjoinRoot.root (planeCurveAdjoinPolynomial p)) ^ p +
          (AdjoinRoot.of (planeCurveAdjoinPolynomial p))
            (RatFunc.X : charPRationalFunctionField p) = 0 := by
    simpa [planeCurveAdjoinPolynomial] using
      AdjoinRoot.eval₂_root (planeCurveAdjoinPolynomial p)
  -- Evaluating the bivariate equation sends the `y^2` term to zero.
  simp [charPPlaneCurveEquation, planeCurveEvalToAdjoinRoot, hroot]

/-- Helper for Chap10 Example 10 140 8: the specialization descends through the
plane-curve quotient. -/
lemma planeCurveEvalToAdjoinRoot_span_le_ker :
    ∀ a : charPPlaneCurvePolynomialRing p,
      a ∈ Ideal.span ({charPPlaneCurveEquation p} : Set (charPPlaneCurvePolynomialRing p)) →
        (planeCurveEvalToAdjoinRoot p) a = 0 := by
  intro a ha
  -- Membership in the principal defining ideal writes `a` as a multiple of the equation.
  rw [Ideal.mem_span_singleton] at ha
  rcases ha with ⟨b, rfl⟩
  -- The preceding vanishing lemma kills the defining factor.
  simp [map_mul, planeCurveEvalToAdjoinRoot_eq_zero_on_equation]

/-- Helper for Chap10 Example 10 140 8: the specialization map descended to the
plane-curve quotient. -/
def planeCurveToAdjoinRoot :
    charPPlaneCurveQuotient p →ₐ[charPRationalFunctionField p]
      AdjoinRoot (planeCurveAdjoinPolynomial p) :=
  Ideal.Quotient.liftₐ
    (Ideal.span ({charPPlaneCurveEquation p} : Set (charPPlaneCurvePolynomialRing p)))
    (planeCurveEvalToAdjoinRoot p)
    (planeCurveEvalToAdjoinRoot_span_le_ker p)

/-- Helper for Chap10 Example 10 140 8: the descended specialization is onto
`AdjoinRoot (X^p + t)`. -/
lemma planeCurveToAdjoinRoot_surjective : Function.Surjective (planeCurveToAdjoinRoot p) := by
  intro z
  -- Every element of `AdjoinRoot` is represented by a one-variable polynomial in the root.
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective z
  refine ⟨π (Polynomial.toMvPolynomial (0 : Fin 2) q), ?_⟩
  -- The representative polynomial is inserted in the `x` variable, so specialization recovers it.
  simp [planeCurveToAdjoinRoot, planeCurveEvalToAdjoinRoot, AdjoinRoot.aeval_eq]

-- Route correction: direct membership in `(x^p + y^2 + t, y)` left a large custom divisibility
-- proof.  We instead put the ring in the stable normal form `K[x][y]`, compute the kernel there,
-- and transport it back across an algebra equivalence.

/-- Helper for Chap10 Example 10 140 8: the preimage of a principal ideal under the constant
coefficient map is generated by that constant and the polynomial variable. -/
lemma polynomial_comap_constantCoeff_span_singleton {B : Type*} [CommRing B] (g : B) :
    (Ideal.span ({g} : Set B)).comap (Polynomial.constantCoeff : Polynomial B →+* B) =
      Ideal.span ({Polynomial.C g, Polynomial.X} : Set (Polynomial B)) := by
  ext f
  constructor
  · intro hf
    -- Divisibility of the constant coefficient provides the constant generator; division by `X`
    -- supplies the remaining polynomial-variable part.
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hf
    obtain ⟨a, ha⟩ := hf
    rw [Ideal.mem_span_pair]
    refine ⟨Polynomial.C a, f /ₘ Polynomial.X, ?_⟩
    have hdecomp := Polynomial.modByMonic_add_div f Polynomial.X
    rw [Polynomial.modByMonic_X] at hdecomp
    rw [Polynomial.constantCoeff_apply, Polynomial.coeff_zero_eq_eval_zero] at ha
    calc
      Polynomial.C a * Polynomial.C g + (f /ₘ Polynomial.X) * Polynomial.X =
          Polynomial.C (Polynomial.eval 0 f) + Polynomial.X * (f /ₘ Polynomial.X) := by
        simpa [ha, mul_comm]
      _ = f := by simpa [mul_comm] using hdecomp
  · intro hf
    -- Conversely, taking constant coefficients kills the `X`-generator and preserves the
    -- principal `g`-multiple.
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    rw [Ideal.mem_span_pair] at hf
    obtain ⟨a, b, h⟩ := hf
    refine ⟨Polynomial.constantCoeff a, ?_⟩
    rw [← h]
    simp [Polynomial.constantCoeff_apply, mul_comm]

/-- Helper for Chap10 Example 10 140 8: composing constant term in `Y` with the `AdjoinRoot`
quotient has kernel `(C g, Y)`. -/
lemma adjoinRoot_mk_comp_constantCoeff_ker {K : Type*} [CommRing K] (g : Polynomial K) :
    RingHom.ker ((AdjoinRoot.mk g).comp
      (Polynomial.constantCoeff : Polynomial (Polynomial K) →+* Polynomial K)) =
      Ideal.span ({Polynomial.C g, Polynomial.X} : Set (Polynomial (Polynomial K))) := by
  -- The `AdjoinRoot` quotient has kernel `(g)`, and the previous lemma computes its preimage.
  have hkerMk : RingHom.ker (AdjoinRoot.mk g) = Ideal.span ({g} : Set (Polynomial K)) := by
    ext q
    rw [RingHom.mem_ker, AdjoinRoot.mk_eq_zero, Ideal.mem_span_singleton]
  rw [← RingHom.comap_ker (AdjoinRoot.mk g)
      (Polynomial.constantCoeff : Polynomial (Polynomial K) →+* Polynomial K)]
  rw [hkerMk, polynomial_comap_constantCoeff_span_singleton]

/-- Helper for Chap10 Example 10 140 8: the remaining single coefficient variable is the ordinary
one-variable polynomial ring. -/
abbrev coeffFinOneAlgEquiv :
    MvPolynomial (Fin 1) (charPRationalFunctionField p) ≃ₐ[charPRationalFunctionField p]
      Polynomial (charPRationalFunctionField p) :=
  (MvPolynomial.renameEquiv (charPRationalFunctionField p) (Equiv.equivPUnit.{1, 1} (Fin 1))).trans
    (MvPolynomial.pUnitAlgEquiv.{0, 0} (charPRationalFunctionField p))

/-- Helper for Chap10 Example 10 140 8: the unique coefficient variable maps to the usual
polynomial variable. -/
lemma coeffFinOneAlgEquiv_X :
    coeffFinOneAlgEquiv p (X (0 : Fin 1)) =
      (Polynomial.X : Polynomial (charPRationalFunctionField p)) := by
  -- This is the defining computation of the one-variable `MvPolynomial` equivalence.
  simp [coeffFinOneAlgEquiv]

/-- Helper for Chap10 Example 10 140 8: a normal form putting the original `y` variable as the
outer polynomial variable of `K[x][y]`. -/
def planeCurveAsPolynomialInY :
    charPPlaneCurvePolynomialRing p ≃ₐ[charPRationalFunctionField p]
      Polynomial (Polynomial (charPRationalFunctionField p)) :=
  (MvPolynomial.renameEquiv (charPRationalFunctionField p)
      (Equiv.swap (0 : Fin 2) (1 : Fin 2))).trans
    ((MvPolynomial.finSuccEquiv (charPRationalFunctionField p) 1).trans
      (Polynomial.mapAlgEquiv (coeffFinOneAlgEquiv p)))

/-- Helper for Chap10 Example 10 140 8: the ring-hom view of the normal-form equivalence. -/
def planeCurveAsPolynomialInYRingHom :
    charPPlaneCurvePolynomialRing p →+*
      Polynomial (Polynomial (charPRationalFunctionField p)) :=
  (planeCurveAsPolynomialInY p).toRingEquiv.toRingHom

/-- Helper for Chap10 Example 10 140 8: the normal form sends original `y` to the outer
polynomial variable. -/
lemma planeCurveAsPolynomialInY_X_one :
    planeCurveAsPolynomialInY p (X (1 : Fin 2)) =
      (Polynomial.X : Polynomial (Polynomial (charPRationalFunctionField p))) := by
  -- Swapping variables makes original `y` the zeroth variable, which `finSuccEquiv` sends to `Y`.
  simp [planeCurveAsPolynomialInY, MvPolynomial.finSuccEquiv_X_zero]

/-- Helper for Chap10 Example 10 140 8: the normal form sends original `x` to the coefficient
polynomial variable. -/
lemma planeCurveAsPolynomialInY_X_zero :
    planeCurveAsPolynomialInY p (X (0 : Fin 2)) =
      Polynomial.C (Polynomial.X : Polynomial (charPRationalFunctionField p)) := by
  -- After swapping variables, original `x` is the successor variable and therefore lands in
  -- the coefficient ring.
  simp only [planeCurveAsPolynomialInY, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X, Equiv.swap_apply_left]
  have hsucc :
      (X (1 : Fin 2) : MvPolynomial (Fin 2) (charPRationalFunctionField p)) =
        X (Fin.succ (0 : Fin 1)) := rfl
  rw [hsucc, MvPolynomial.finSuccEquiv_X_succ]
  simpa [coeffFinOneAlgEquiv] using congrArg Polynomial.C (coeffFinOneAlgEquiv_X p)

/-- Helper for Chap10 Example 10 140 8: the normal form is an algebra map on constants. -/
lemma planeCurveAsPolynomialInY_C (r : charPRationalFunctionField p) :
    planeCurveAsPolynomialInY p (C r) =
      Polynomial.C (Polynomial.C r : Polynomial (charPRationalFunctionField p)) := by
  -- Constants are fixed by the algebra equivalence, with the target algebra map written as
  -- nested polynomial constants.
  simpa only [algebraMap_eq, RingHom.coe_comp, Function.comp_apply] using
    (planeCurveAsPolynomialInY p).commutes r

/-- Helper for Chap10 Example 10 140 8: in the `K[x][y]` normal form, the plane-curve equation is
`C (X^p + t) + Y^2`. -/
lemma planeCurveAsPolynomialInY_equation :
    planeCurveAsPolynomialInY p (charPPlaneCurveEquation p) =
      Polynomial.C (planeCurveAdjoinPolynomial p) +
        (Polynomial.X : Polynomial (Polynomial (charPRationalFunctionField p))) ^ 2 := by
  -- Evaluate the three terms separately under the normal form and collect the coefficient terms.
  simp [charPPlaneCurveEquation, planeCurveAdjoinPolynomial, map_add, map_pow,
    planeCurveAsPolynomialInY_X_zero, planeCurveAsPolynomialInY_X_one,
    planeCurveAsPolynomialInY_C]
  ring

/-- Helper for Chap10 Example 10 140 8: the normal form sends the principal plane-curve ideal to
the principal ideal generated by `C (X^p + t) + Y^2`. -/
lemma planeCurveAsPolynomialInY_map_span_equation :
    Ideal.map (planeCurveAsPolynomialInYRingHom p)
      (Ideal.span ({charPPlaneCurveEquation p} : Set (charPPlaneCurvePolynomialRing p))) =
      Ideal.span
        ({Polynomial.C (planeCurveAdjoinPolynomial p) +
            (Polynomial.X : Polynomial (Polynomial (charPRationalFunctionField p))) ^ 2} :
          Set (Polynomial (Polynomial (charPRationalFunctionField p)))) := by
  -- Mapping a principal span through the normal-form equivalence just replaces its generator by
  -- the computed normal form of the equation.
  rw [Ideal.map_span]
  refine congrArg Ideal.span ?_
  ext z
  simp [planeCurveAsPolynomialInYRingHom, planeCurveAsPolynomialInY_equation]

/-- Helper for Chap10 Example 10 140 8: the plane-curve quotient in the stable `K[x][y]`
normal form is an `AdjoinRoot` quotient by `Y^2 + (X^p + t)`. -/
def planeCurveQuotientAsAdjoinRootInY :
    charPPlaneCurveQuotient p ≃ₐ[charPRationalFunctionField p]
      AdjoinRoot
        (Polynomial.C (planeCurveAdjoinPolynomial p) +
          (Polynomial.X : Polynomial (Polynomial (charPRationalFunctionField p))) ^ 2) :=
  Ideal.quotientEquivAlg
    (I := Ideal.span ({charPPlaneCurveEquation p} : Set (charPPlaneCurvePolynomialRing p)))
    (J := Ideal.span
      ({Polynomial.C (planeCurveAdjoinPolynomial p) +
          (Polynomial.X : Polynomial (Polynomial (charPRationalFunctionField p))) ^ 2} :
        Set (Polynomial (Polynomial (charPRationalFunctionField p)))))
    (planeCurveAsPolynomialInY p)
    (planeCurveAsPolynomialInY_map_span_equation p).symm

/-- Helper for Chap10 Example 10 140 8: `X^p + t` is not in the square of its principal ideal
in `K[X]`. -/
lemma planeCurveAdjoinPolynomial_notMem_span_sq :
    planeCurveAdjoinPolynomial p ∉
      (Ideal.span ({planeCurveAdjoinPolynomial p} :
        Set (Polynomial (charPRationalFunctionField p)))) ^ 2 := by
  -- Membership in the square would make `(X^p + t)^2` divide `X^p + t`, contradicting degrees.
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  intro hdiv
  have hdegree_le :=
    Polynomial.natDegree_le_of_dvd
      (p := planeCurveAdjoinPolynomial p ^ 2)
      (q := planeCurveAdjoinPolynomial p) hdiv
      (ratFunc_X_pow_add_C_irreducible p).ne_zero
  have hdegree :
      (planeCurveAdjoinPolynomial p).natDegree = p := by
    simp [planeCurveAdjoinPolynomial]
  rw [Polynomial.natDegree_pow, hdegree] at hdegree_le
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  omega

/-- Helper for Chap10 Example 10 140 8: the normal-form polynomial `Y^2 + (X^p + t)` is prime
over `K[X]`. -/
lemma planeCurveInYPolynomial_prime :
    Prime
      (Polynomial.C (planeCurveAdjoinPolynomial p) +
        (Polynomial.X : Polynomial (Polynomial (charPRationalFunctionField p))) ^ 2) := by
  let K := charPRationalFunctionField p
  let g : Polynomial K := planeCurveAdjoinPolynomial p
  let f : Polynomial (Polynomial K) := Polynomial.C g + Polynomial.X ^ 2
  -- The polynomial is monic quadratic in `Y`.
  have hmonic : f.Monic := by
    simpa [f, g, pow_two, add_comm] using
      Polynomial.monic_X_pow_add_C (R := Polynomial K) (n := 2) g
  -- The principal ideal `(g)` is prime because `g = X^p + t` is irreducible over the field `K`.
  have hprimeIdeal : (Ideal.span ({g} : Set (Polynomial K))).IsPrime := by
    rw [Ideal.span_singleton_prime]
    · exact (ratFunc_X_pow_add_C_irreducible p).prime
    · exact (ratFunc_X_pow_add_C_irreducible p).ne_zero
  have hnotTop : Ideal.span ({g} : Set (Polynomial K)) ≠ ⊤ :=
    hprimeIdeal.ne_top
  -- Eisenstein's constant-term condition is exactly the preceding square-nonmembership fact.
  have hnotMemSq : f.coeff 0 ∉ (Ideal.span ({g} : Set (Polynomial K))) ^ 2 := by
    simp only [f, Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.coeff_X_pow]
    simpa [g] using planeCurveAdjoinPolynomial_notMem_span_sq p
  have hnatDegree : f.natDegree = 2 := by
    simpa [f, g, add_comm] using
      (Polynomial.natDegree_X_pow_add_C
        (R := Polynomial K) (n := 2) (r := g))
  -- Eisenstein irreducibility then gives primeness in the polynomial UFD.
  have heisenstein : f.IsEisensteinAt (Ideal.span ({g} : Set (Polynomial K))) := by
    refine hmonic.isEisensteinAt_of_mem_of_notMem hnotTop ?_ hnotMemSq
    intro n hn
    have hn_cases : n = 0 ∨ n = 1 := by
      omega
    rcases hn_cases with rfl | rfl
    · simpa [f] using Ideal.subset_span (Set.mem_singleton g)
    · simp [f]
  have hirreducible : Irreducible f := by
    refine heisenstein.irreducible hprimeIdeal hmonic.isPrimitive ?_
    omega
  simpa [f, g] using hirreducible.prime

/-- Helper for Chap10 Example 10 140 8: the plane-curve quotient is a domain. -/
lemma planeCurveQuotient_isDomain :
    IsDomain (charPPlaneCurveQuotient p) := by
  -- The normal-form quotient is an `AdjoinRoot` by a prime polynomial, and the algebra
  -- equivalence transports the domain structure back to the original quotient.
  let f :=
    Polynomial.C (planeCurveAdjoinPolynomial p) +
      (Polynomial.X : Polynomial (Polynomial (charPRationalFunctionField p))) ^ 2
  letI : IsDomain (AdjoinRoot f) :=
    AdjoinRoot.isDomain_of_prime (by simpa [f] using planeCurveInYPolynomial_prime p)
  exact (planeCurveQuotientAsAdjoinRootInY p).toRingEquiv.toMulEquiv.isDomain _

/-- Helper for Chap10 Example 10 140 8: under the normal-form quotient equivalence, the class
of `y` becomes the adjoined root. -/
lemma planeCurveQuotientAsAdjoinRootInY_apply_y :
    planeCurveQuotientAsAdjoinRootInY p (π (X (1 : Fin 2))) =
      AdjoinRoot.root
        (Polynomial.C (planeCurveAdjoinPolynomial p) +
          (Polynomial.X : Polynomial (Polynomial (charPRationalFunctionField p))) ^ 2) := by
  -- The quotient equivalence is induced by `planeCurveAsPolynomialInY`, which sends `y` to `Y`.
  unfold planeCurveQuotientAsAdjoinRootInY
  have hmk :=
    Ideal.quotientEquivAlg_mk
      (I := Ideal.span ({charPPlaneCurveEquation p} : Set (charPPlaneCurvePolynomialRing p)))
      (J := Ideal.span
        ({Polynomial.C (planeCurveAdjoinPolynomial p) +
            (Polynomial.X : Polynomial (Polynomial (charPRationalFunctionField p))) ^ 2} :
          Set (Polynomial (Polynomial (charPRationalFunctionField p)))))
      (planeCurveAsPolynomialInY p)
      (planeCurveAsPolynomialInY_map_span_equation p).symm
      (X (1 : Fin 2))
  calc
    ((Ideal.span ({charPPlaneCurveEquation p} : Set (charPPlaneCurvePolynomialRing p))).quotientEquivAlg
        (Ideal.span
          ({Polynomial.C (planeCurveAdjoinPolynomial p) +
              (Polynomial.X : Polynomial (Polynomial (charPRationalFunctionField p))) ^ 2} :
            Set (Polynomial (Polynomial (charPRationalFunctionField p)))))
        (planeCurveAsPolynomialInY p) (planeCurveAsPolynomialInY_map_span_equation p).symm)
        (π (X (1 : Fin 2))) =
        planeCurveAsPolynomialInY p (X (1 : Fin 2)) := hmk
    _ = AdjoinRoot.root
        (Polynomial.C (planeCurveAdjoinPolynomial p) +
          (Polynomial.X : Polynomial (Polynomial (charPRationalFunctionField p))) ^ 2) := by
      rw [planeCurveAsPolynomialInY_X_one]
      rfl

/-- Helper for Chap10 Example 10 140 8: the class of `y` is nonzero in the plane-curve
quotient. -/
lemma planeCurve_y_ne_zero :
    (π (X (1 : Fin 2)) : charPPlaneCurveQuotient p) ≠ 0 := by
  -- The normal form sends `y` to the adjoined root `Y`, which has degree less than the monic
  -- quadratic relation and is therefore nonzero in the `AdjoinRoot`.
  intro hy
  have hroot_zero := congrArg (planeCurveQuotientAsAdjoinRootInY p) hy
  have hroot_ne :
      AdjoinRoot.root
        (Polynomial.C (planeCurveAdjoinPolynomial p) +
          (Polynomial.X : Polynomial (Polynomial (charPRationalFunctionField p))) ^ 2) ≠ 0 := by
    let K := charPRationalFunctionField p
    let f : Polynomial (Polynomial K) :=
      Polynomial.C (planeCurveAdjoinPolynomial p) + Polynomial.X ^ 2
    have htwo_ne : (2 : ℕ) ≠ 0 := by
      norm_num
    have hmonic : f.Monic := by
      simpa [f, pow_two, add_comm] using
        Polynomial.monic_X_pow_add_C
          (R := Polynomial K) (planeCurveAdjoinPolynomial p) (n := 2) htwo_ne
    have hX_ne : (Polynomial.X : Polynomial (Polynomial K)) ≠ 0 :=
      Polynomial.X_ne_zero
    have hdegree_lt : (Polynomial.X : Polynomial (Polynomial K)).degree < f.degree := by
      have hdegree_f : f.degree = 2 := by
        simpa [f, add_comm] using
          Polynomial.degree_X_pow_add_C
            (R := Polynomial K) (n := 2) (by norm_num) (planeCurveAdjoinPolynomial p)
      rw [hdegree_f]
      norm_num
    change (AdjoinRoot.mk f) (Polynomial.X : Polynomial (Polynomial K)) ≠ 0
    exact AdjoinRoot.mk_ne_zero_of_degree_lt hmonic hX_ne hdegree_lt
  apply hroot_ne
  rw [planeCurveQuotientAsAdjoinRootInY_apply_y] at hroot_zero
  simpa using hroot_zero

/-- Helper for Chap10 Example 10 140 8: the source ideal `(x^p + y^2 + t, y)` maps to
`(C (X^p + t), Y)` in the normal form. -/
lemma planeCurveAsPolynomialInY_map_span_adjoinPolynomial_y :
    Ideal.map (planeCurveAsPolynomialInYRingHom p)
      (Ideal.span ({charPPlaneCurveEquation p, X (1 : Fin 2)} :
        Set (charPPlaneCurvePolynomialRing p))) =
      Ideal.span ({Polynomial.C (planeCurveAdjoinPolynomial p), Polynomial.X} :
        Set (Polynomial (Polynomial (charPRationalFunctionField p)))) := by
  -- Mapping a two-generator span gives the span of the two images.
  rw [Ideal.map_span]
  rw [show (⇑(planeCurveAsPolynomialInYRingHom p) ''
        ({charPPlaneCurveEquation p, X (1 : Fin 2)} : Set (charPPlaneCurvePolynomialRing p))) =
      ({planeCurveAsPolynomialInY p (charPPlaneCurveEquation p),
          planeCurveAsPolynomialInY p (X (1 : Fin 2))} :
        Set (Polynomial (Polynomial (charPRationalFunctionField p)))) by
    ext z
    simp [planeCurveAsPolynomialInYRingHom, Set.mem_image, eq_comm]]
  -- Since `Y` is a generator, replacing `C g + Y^2` by `C g` does not change the ideal.
  rw [planeCurveAsPolynomialInY_equation, planeCurveAsPolynomialInY_X_one]
  simpa [pow_two] using
    Ideal.span_pair_add_right_mul
      (Polynomial.C (planeCurveAdjoinPolynomial p))
      (Polynomial.X : Polynomial (Polynomial (charPRationalFunctionField p)))
      (Polynomial.X : Polynomial (Polynomial (charPRationalFunctionField p)))

/-- Helper for Chap10 Example 10 140 8: pulling `(C (X^p + t), Y)` back from the normal form
recovers the source ideal `(x^p + y^2 + t, y)`. -/
lemma planeCurveAsPolynomialInY_comap_span_adjoinPolynomial_y :
    (Ideal.span ({Polynomial.C (planeCurveAdjoinPolynomial p), Polynomial.X} :
        Set (Polynomial (Polynomial (charPRationalFunctionField p))))).comap
        (planeCurveAsPolynomialInYRingHom p) =
      Ideal.span ({charPPlaneCurveEquation p, X (1 : Fin 2)} :
        Set (charPPlaneCurvePolynomialRing p)) := by
  -- The preceding map computation can be pulled back unchanged because the normal-form map is
  -- bijective.
  rw [← planeCurveAsPolynomialInY_map_span_adjoinPolynomial_y]
  exact Ideal.comap_map_of_bijective (planeCurveAsPolynomialInYRingHom p)
    (AlgEquiv.bijective (planeCurveAsPolynomialInY p))

/-- Helper for Chap10 Example 10 140 8: the normal-form evaluation map is constant term followed
by the `AdjoinRoot` quotient. -/
def planeCurveNormalFormToAdjoinRoot :
    Polynomial (Polynomial (charPRationalFunctionField p)) →+*
      AdjoinRoot (planeCurveAdjoinPolynomial p) :=
  (AdjoinRoot.mk (planeCurveAdjoinPolynomial p)).comp
    (Polynomial.constantCoeff :
      Polynomial (Polynomial (charPRationalFunctionField p)) →+*
        Polynomial (charPRationalFunctionField p))

/-- Helper for Chap10 Example 10 140 8: the named normal-form evaluation has kernel
`(C (X^p + t), Y)`. -/
lemma planeCurveNormalFormToAdjoinRoot_ker :
    RingHom.ker (planeCurveNormalFormToAdjoinRoot p) =
      Ideal.span ({Polynomial.C (planeCurveAdjoinPolynomial p), Polynomial.X} :
        Set (Polynomial (Polynomial (charPRationalFunctionField p)))) := by
  -- This is the specialized form of the general constant-coefficient `AdjoinRoot` kernel.
  simpa [planeCurveNormalFormToAdjoinRoot] using
    adjoinRoot_mk_comp_constantCoeff_ker (planeCurveAdjoinPolynomial p)

/-- Helper for Chap10 Example 10 140 8: the specialization factors through constant term in the
normal form followed by the `AdjoinRoot` quotient. -/
lemma planeCurveEvalToAdjoinRoot_factor :
    (planeCurveEvalToAdjoinRoot p).toRingHom =
      (planeCurveNormalFormToAdjoinRoot p).comp (planeCurveAsPolynomialInYRingHom p) := by
  -- Ring-hom extensionality reduces the factorization to constants and the two variables.
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [planeCurveEvalToAdjoinRoot, planeCurveNormalFormToAdjoinRoot,
      planeCurveAsPolynomialInYRingHom, planeCurveAsPolynomialInY_C]
  · intro i
    fin_cases i <;>
      simp [planeCurveEvalToAdjoinRoot, planeCurveNormalFormToAdjoinRoot,
        planeCurveAsPolynomialInYRingHom, planeCurveAsPolynomialInY_X_zero,
        planeCurveAsPolynomialInY_X_one]

/-- Helper for Chap10 Example 10 140 8: the kernel of the specialization is the ideal generated
by the defining equation and `y`. -/
lemma planeCurveEvalToAdjoinRoot_ker :
    RingHom.ker (planeCurveEvalToAdjoinRoot p).toRingHom =
      Ideal.span ({charPPlaneCurveEquation p, X (1 : Fin 2)} :
        Set (charPPlaneCurvePolynomialRing p)) := by
  -- Factor the evaluator through the normal form and pull back the computed kernel.
  rw [planeCurveEvalToAdjoinRoot_factor]
  calc
    RingHom.ker ((planeCurveNormalFormToAdjoinRoot p).comp
        (planeCurveAsPolynomialInYRingHom p)) =
        Ideal.comap (planeCurveAsPolynomialInYRingHom p)
          (RingHom.ker (planeCurveNormalFormToAdjoinRoot p)) := by
      exact (RingHom.comap_ker (planeCurveNormalFormToAdjoinRoot p)
        (planeCurveAsPolynomialInYRingHom p)).symm
    _ = Ideal.comap (planeCurveAsPolynomialInYRingHom p)
          (Ideal.span ({Polynomial.C (planeCurveAdjoinPolynomial p), Polynomial.X} :
            Set (Polynomial (Polynomial (charPRationalFunctionField p))))) := by
      rw [planeCurveNormalFormToAdjoinRoot_ker]
    _ = Ideal.span ({charPPlaneCurveEquation p, X (1 : Fin 2)} :
        Set (charPPlaneCurvePolynomialRing p)) :=
      planeCurveAsPolynomialInY_comap_span_adjoinPolynomial_y p

/-- Helper for Chap10 Example 10 140 8: the source kernel maps to the principal `y`-ideal in
the plane-curve quotient. -/
lemma planeCurveEvalToAdjoinRoot_ker_map :
    Ideal.map
          (Ideal.Quotient.mk
            (Ideal.span ({charPPlaneCurveEquation p} : Set (charPPlaneCurvePolynomialRing p))))
          (RingHom.ker (planeCurveEvalToAdjoinRoot p).toRingHom) =
      Ideal.span ({π (X (1 : Fin 2))} : Set (charPPlaneCurveQuotient p)) := by
  -- Transport the source kernel description through the quotient map.
  rw [planeCurveEvalToAdjoinRoot_ker, Ideal.map_span]
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    intro z hz
    rcases hz with ⟨a, ha, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · -- The defining equation maps to zero in the quotient.
      simpa using
        (show π (charPPlaneCurveEquation p) = 0 from
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))
    · exact Ideal.subset_span (Set.mem_singleton _)
  · refine Ideal.span_le.mpr ?_
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    -- The image of `y` is one of the transported source generators.
    exact Ideal.subset_span (Set.mem_image_of_mem _ (by simp))

/-- Helper for Chap10 Example 10 140 8: the kernel of the descended specialization is the ideal
generated by the image of `y`. -/
lemma planeCurveToAdjoinRoot_ker :
    RingHom.ker (planeCurveToAdjoinRoot p).toRingHom =
      Ideal.span ({π (X (1 : Fin 2))} : Set (charPPlaneCurveQuotient p)) := by
  -- Mathlib computes the kernel of a quotient lift as the image of the source kernel.
  have hkerLift :
      RingHom.ker
          (Ideal.Quotient.lift
            (Ideal.span ({charPPlaneCurveEquation p} : Set (charPPlaneCurvePolynomialRing p)))
            (planeCurveEvalToAdjoinRoot p).toRingHom
            (planeCurveEvalToAdjoinRoot_span_le_ker p)) =
        Ideal.map
          (Ideal.Quotient.mk
            (Ideal.span ({charPPlaneCurveEquation p} : Set (charPPlaneCurvePolynomialRing p))))
          (RingHom.ker (planeCurveEvalToAdjoinRoot p).toRingHom) := by
    exact Ideal.ker_quotient_lift (planeCurveEvalToAdjoinRoot p).toRingHom
      (planeCurveEvalToAdjoinRoot_span_le_ker p)
  calc
    RingHom.ker (planeCurveToAdjoinRoot p).toRingHom =
        Ideal.map
          (Ideal.Quotient.mk
            (Ideal.span ({charPPlaneCurveEquation p} : Set (charPPlaneCurvePolynomialRing p))))
          (RingHom.ker (planeCurveEvalToAdjoinRoot p).toRingHom) := by
      simpa [planeCurveToAdjoinRoot, Ideal.Quotient.liftₐ] using hkerLift
    _ = Ideal.span ({π (X (1 : Fin 2))} : Set (charPPlaneCurveQuotient p)) :=
      planeCurveEvalToAdjoinRoot_ker_map p

/-- Helper for Chap10 Example 10 140 8: the point `q` in the plane-curve quotient pulls back to
the source ideal generated by the defining equation and `y`. -/
lemma planeCurveSourcePrimeIdeal_comap_quotientMap :
    Ideal.comap
        (Ideal.Quotient.mk
          (Ideal.span ({charPPlaneCurveEquation p} : Set (charPPlaneCurvePolynomialRing p))))
        (charPPlaneCurvePrimeIdeal p) =
      Ideal.span ({charPPlaneCurveEquation p, X (1 : Fin 2)} :
        Set (charPPlaneCurvePolynomialRing p)) := by
  -- The quotient point is the kernel of the descended specialization to `AdjoinRoot`; pulling
  -- that kernel back through the quotient map recovers the raw specialization kernel.
  calc
    Ideal.comap
        (Ideal.Quotient.mk
          (Ideal.span ({charPPlaneCurveEquation p} : Set (charPPlaneCurvePolynomialRing p))))
        (charPPlaneCurvePrimeIdeal p) =
        RingHom.ker
          ((planeCurveToAdjoinRoot p).toRingHom.comp
            (Ideal.Quotient.mk
              (Ideal.span ({charPPlaneCurveEquation p} :
                Set (charPPlaneCurvePolynomialRing p))))) := by
      rw [charPPlaneCurvePrimeIdeal_eq_span_y, ← planeCurveToAdjoinRoot_ker]
      exact (RingHom.comap_ker (planeCurveToAdjoinRoot p).toRingHom
        (Ideal.Quotient.mk
          (Ideal.span ({charPPlaneCurveEquation p} :
            Set (charPPlaneCurvePolynomialRing p))))).symm
    _ = RingHom.ker (planeCurveEvalToAdjoinRoot p).toRingHom := by
      -- Both maps are the same source specialization; kernel equality follows by extensionality.
      congr 1
    _ = Ideal.span ({charPPlaneCurveEquation p, X (1 : Fin 2)} :
        Set (charPPlaneCurvePolynomialRing p)) :=
      planeCurveEvalToAdjoinRoot_ker p

/-- Helper for Chap10 Example 10 140 8: the ideal generated by the image of `y` is maximal. -/
lemma planeCurve_spanY_isMaximal :
    (Ideal.span ({π (X (1 : Fin 2))} : Set (charPPlaneCurveQuotient p))).IsMaximal := by
  letI : Fact (Irreducible (planeCurveAdjoinPolynomial p)) :=
    ⟨ratFunc_X_pow_add_C_irreducible p⟩
  -- The first isomorphism theorem identifies the quotient by `(y)` with `AdjoinRoot (X^p + t)`.
  let e :
      (charPPlaneCurveQuotient p ⧸
          Ideal.span ({π (X (1 : Fin 2))} : Set (charPPlaneCurveQuotient p))) ≃ₐ[
        charPRationalFunctionField p]
        AdjoinRoot (planeCurveAdjoinPolynomial p) :=
    (Ideal.quotientEquivAlgOfEq (charPRationalFunctionField p)
        (planeCurveToAdjoinRoot_ker p).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (planeCurveToAdjoinRoot_surjective p))
  have hfield :
      IsField
        (charPPlaneCurveQuotient p ⧸
          Ideal.span ({π (X (1 : Fin 2))} : Set (charPPlaneCurveQuotient p))) :=
    e.toMulEquiv.isField (Field.toIsField _)
  -- A quotient field is the standard criterion for maximality.
  exact Ideal.Quotient.maximal_of_isField _ hfield

-- Proof sketch: in the quotient by `x^p + y^2 + t`, modding out further by `(y, x^p + t)` gives a
-- field, so this ideal is maximal and hence prime.
/-- The ideal `(y, x^p + t)` is prime in the plane-curve quotient ring. -/
lemma charPPlaneCurvePrimeIdeal_isPrime : (charPPlaneCurvePrimeIdeal p).IsPrime := by
  -- The second generator is redundant, so the maximality of `(y)` gives primeness.
  rw [charPPlaneCurvePrimeIdeal_eq_span_y]
  exact (planeCurve_spanY_isMaximal p).isPrime

/-- The prime `q = (y, x^p + t)` in the plane-curve example. -/
def charPPlaneCurvePrime : PrimeSpectrum (charPPlaneCurveQuotient p) :=
  ⟨charPPlaneCurvePrimeIdeal p, charPPlaneCurvePrimeIdeal_isPrime p⟩

/-- Helper for Chap10 Example 10 140 8: the spectrum point `q` pulls back to the source ideal
generated by the defining equation and `y`. -/
lemma planeCurvePrime_asIdeal_comap_quotientMap :
    Ideal.comap
        (Ideal.Quotient.mk
          (Ideal.span ({charPPlaneCurveEquation p} : Set (charPPlaneCurvePolynomialRing p))))
        (charPPlaneCurvePrime p).asIdeal =
      Ideal.span ({charPPlaneCurveEquation p, X (1 : Fin 2)} :
        Set (charPPlaneCurvePolynomialRing p)) := by
  -- This is the same comap calculation as above, with the prime-spectrum wrapper unfolded once.
  simpa [charPPlaneCurvePrime] using planeCurveSourcePrimeIdeal_comap_quotientMap p

/-- Helper for Chap10 Example 10 140 8: the source ideal `(F, y)` over the polynomial ring is
maximal. -/
lemma planeCurveSourceIdeal_isMaximal :
    (Ideal.span ({charPPlaneCurveEquation p, X (1 : Fin 2)} :
      Set (charPPlaneCurvePolynomialRing p))).IsMaximal := by
  -- Pull maximality of the quotient prime back along the surjective quotient map.
  rw [← planeCurvePrime_asIdeal_comap_quotientMap p]
  have hqmax : (charPPlaneCurvePrime p).asIdeal.IsMaximal := by
    simpa [charPPlaneCurvePrime, charPPlaneCurvePrimeIdeal_eq_span_y] using
      planeCurve_spanY_isMaximal p
  exact Ideal.comap_isMaximal_of_surjective
    (Ideal.Quotient.mk
      (Ideal.span ({charPPlaneCurveEquation p} : Set (charPPlaneCurvePolynomialRing p))))
    (Ideal.Quotient.mk_surjective
      (I := Ideal.span ({charPPlaneCurveEquation p} :
        Set (charPPlaneCurvePolynomialRing p))))

/-- Helper for Chap10 Example 10 140 8: localizing a quotient map at a prime of the quotient
gives a surjective local map. -/
lemma localAlgHom_quotientMap_surjective {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (I : Ideal A) (q : Ideal (A ⧸ I)) [q.IsPrime] :
    Function.Surjective
      (Localization.localAlgHom (q.comap (Ideal.Quotient.mk I)) q
        (Ideal.Quotient.mkₐ R I) rfl) := by
  -- Surjectivity is the stalkwise form of the globally surjective quotient map.
  simpa [Localization.localAlgHom] using
    (RingHom.surjectiveOnStalks_of_surjective
      (Ideal.Quotient.mk_surjective (I := I))).localRingHom_surjective
        (q.comap (Ideal.Quotient.mk I)) q rfl

/-- Helper for Chap10 Example 10 140 8: after localizing the quotient map at `q`, its kernel is
generated by the localized plane-curve equation. -/
lemma planeCurveLocalizedQuotientMap_ker_eq_span_equation :
    let I := Ideal.span ({charPPlaneCurveEquation p} : Set (charPPlaneCurvePolynomialRing p))
    let q := (charPPlaneCurvePrime p).asIdeal
    let m : Ideal (charPPlaneCurvePolynomialRing p) := q.comap (Ideal.Quotient.mk I)
    let Pm := Localization.AtPrime m
    let Sq := Localization.AtPrime q
    let φ : Pm →ₐ[charPRationalFunctionField p] Sq :=
      Localization.localAlgHom m q (Ideal.Quotient.mkₐ (charPRationalFunctionField p) I) rfl
    RingHom.ker φ.toRingHom =
      Ideal.span
        ({algebraMap (charPPlaneCurvePolynomialRing p) Pm (charPPlaneCurveEquation p)} :
          Set Pm) := by
  -- Localization commutes with kernels here because the quotient map is surjective, and the
  -- original quotient kernel is the principal ideal generated by the defining equation.
  intro I q m Pm Sq φ
  have hmap_primeCompl :
      Submonoid.map (Ideal.Quotient.mk I) m.primeCompl = q.primeCompl := by
    subst m
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      rcases Ideal.Quotient.mk_surjective y with ⟨x, rfl⟩
      exact ⟨x, hy, rfl⟩
  have hker_local :
      RingHom.ker φ.toRingHom =
        (RingHom.ker (Ideal.Quotient.mk I)).map
          (algebraMap (charPPlaneCurvePolynomialRing p) Pm) := by
    have hker := IsLocalization.ker_map (S := Pm) (Q := Sq)
      (M := m.primeCompl) (T := q.primeCompl) (g := Ideal.Quotient.mk I)
      hmap_primeCompl
    simpa [φ, Localization.localAlgHom, Localization.localRingHom] using hker
  have hker_global : RingHom.ker (Ideal.Quotient.mk I) = I := Ideal.mk_ker
  calc
    RingHom.ker φ.toRingHom =
        (RingHom.ker (Ideal.Quotient.mk I)).map
          (algebraMap (charPPlaneCurvePolynomialRing p) Pm) := hker_local
    _ = I.map (algebraMap (charPPlaneCurvePolynomialRing p) Pm) := by rw [hker_global]
    _ = Ideal.span
        ({algebraMap (charPPlaneCurvePolynomialRing p) Pm (charPPlaneCurveEquation p)} :
          Set Pm) := by
      dsimp [I]
      rw [Ideal.map_span]
      congr
      ext z
      simp

/-- Helper for Chap10 Example 10 140 8: the maximal-spectrum point of `K[x,y]` defined by
`(F, y)`. -/
def planeCurveSourceMaximalSpectrum : MaximalSpectrum (charPPlaneCurvePolynomialRing p) :=
  ⟨Ideal.span ({charPPlaneCurveEquation p, X (1 : Fin 2)} :
    Set (charPPlaneCurvePolynomialRing p)), planeCurveSourceIdeal_isMaximal p⟩

/-- Helper for Chap10 Example 10 140 8: the source maximal-spectrum wrapper has underlying ideal
`(F, y)`. -/
lemma planeCurveSourceMaximalSpectrum_asIdeal :
    (planeCurveSourceMaximalSpectrum p).asIdeal =
      Ideal.span ({charPPlaneCurveEquation p, X (1 : Fin 2)} :
        Set (charPPlaneCurvePolynomialRing p)) := by
  -- The wrapper was introduced only to carry the prime instance for localizing at `(F, y)`.
  rfl

/-- Helper for Chap10 Example 10 140 8: the localization of the source polynomial ring at
`(F, y)` is regular local. -/
lemma planeCurveSourceLocalization_isRegularLocalRing :
    IsRegularLocalRing
      (Localization.AtPrime (planeCurveSourceMaximalSpectrum p).asIdeal) := by
  -- Apply the general regularity theorem for localizations of polynomial rings at maximal ideals.
  exact isRegularLocalRing_localizationAtMaximal_mvPolynomial
    (m := planeCurveSourceMaximalSpectrum p)

/-- Helper for Chap10 Example 10 140 8: the localized maximal ideal at `q` is generated by the
image of `y`. -/
lemma planeCurveAtPrime_maximalIdeal_eq_span_y :
    IsLocalRing.maximalIdeal (Localization.AtPrime (charPPlaneCurvePrime p).asIdeal) =
      Ideal.span
        ({algebraMap (charPPlaneCurveQuotient p)
            (Localization.AtPrime (charPPlaneCurvePrime p).asIdeal) (π (X (1 : Fin 2)))} :
          Set (Localization.AtPrime (charPPlaneCurvePrime p).asIdeal)) := by
  -- The point `q` is the principal `y`-ideal, and localization maps that prime to the maximal
  -- ideal of the local ring.
  let f : charPPlaneCurveQuotient p →+*
      Localization.AtPrime (charPPlaneCurvePrime p).asIdeal :=
    algebraMap (charPPlaneCurveQuotient p)
      (Localization.AtPrime (charPPlaneCurvePrime p).asIdeal)
  have hq :
      (charPPlaneCurvePrime p).asIdeal =
        Ideal.span ({π (X (1 : Fin 2))} : Set (charPPlaneCurveQuotient p)) := by
    simpa [charPPlaneCurvePrime] using charPPlaneCurvePrimeIdeal_eq_span_y p
  calc
    IsLocalRing.maximalIdeal (Localization.AtPrime (charPPlaneCurvePrime p).asIdeal) =
        Ideal.map f (charPPlaneCurvePrime p).asIdeal := by
      exact (Localization.AtPrime.map_eq_maximalIdeal
        (I := (charPPlaneCurvePrime p).asIdeal)).symm
    _ = Ideal.map f
        (Ideal.span ({π (X (1 : Fin 2))} : Set (charPPlaneCurveQuotient p))) := by
      exact congrArg (Ideal.map f) hq
    _ = Ideal.span
        ({algebraMap (charPPlaneCurveQuotient p)
            (Localization.AtPrime (charPPlaneCurvePrime p).asIdeal) (π (X (1 : Fin 2)))} :
          Set (Localization.AtPrime (charPPlaneCurvePrime p).asIdeal)) := by
      rw [Ideal.map_span]
      simpa only [f, Set.image_singleton]

/-- Helper for Chap10 Example 10 140 8: the localized maximal ideal at `q` has the displayed
principal generator. -/
lemma planeCurveAtPrime_maximalIdeal_principalGenerator :
    ∃ yq : Localization.AtPrime (charPPlaneCurvePrime p).asIdeal,
      IsLocalRing.maximalIdeal (Localization.AtPrime (charPPlaneCurvePrime p).asIdeal) =
        Ideal.span ({yq} : Set (Localization.AtPrime (charPPlaneCurvePrime p).asIdeal)) := by
  -- The previous equality reduces the claim to the standard principal singleton span.
  refine ⟨algebraMap (charPPlaneCurveQuotient p)
    (Localization.AtPrime (charPPlaneCurvePrime p).asIdeal) (π (X (1 : Fin 2))), ?_⟩
  exact planeCurveAtPrime_maximalIdeal_eq_span_y p

/-- Helper for Chap10 Example 10 140 8: the localized image of `y` at `q` is nonzero. -/
lemma planeCurveAtPrime_y_ne_zero :
    algebraMap (charPPlaneCurveQuotient p)
      (Localization.AtPrime (charPPlaneCurvePrime p).asIdeal) (π (X (1 : Fin 2))) ≠ 0 := by
  -- The quotient is a domain, so localization at the prime is injective; the source class of `y`
  -- was already nonzero in the normal form.
  letI : IsDomain (charPPlaneCurveQuotient p) := planeCurveQuotient_isDomain p
  have hinj :
      Function.Injective
        (algebraMap (charPPlaneCurveQuotient p)
          (Localization.AtPrime (charPPlaneCurvePrime p).asIdeal)) := by
    exact IsLocalization.injective _
      (charPPlaneCurvePrime p).asIdeal.primeCompl_le_nonZeroDivisors
  exact fun hzero => planeCurve_y_ne_zero p (hinj (by simpa using hzero))

/-- Helper for Chap10 Example 10 140 8: a finite upper bound on the Krull dimension of a
Noetherian local ring realizes the dimension as a natural number. -/
lemma exists_nat_ringKrullDim_eq_of_le {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {d : ℕ} (h : ringKrullDim R ≤ d) :
    ∃ n : ℕ, n ≤ d ∧ ringKrullDim R = n := by
  -- The finite upper bound rules out `⊤`, while local Noetherian rings also rule out `⊥`.
  have hbot : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
  have htop : ringKrullDim R ≠ ⊤ := ringKrullDim_ne_top
  let n : ℕ := ((ringKrullDim R).unbot hbot).toNat
  have hneTop : (ringKrullDim R).unbot hbot ≠ ⊤ := by
    intro htop'
    exact htop <| by
      simpa [WithBot.coe_unbot] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) htop'
  have hdim : ringKrullDim R = n := by
    have hdim' : ((ringKrullDim R).unbot hbot : WithBot ℕ∞) = n := by
      simpa [n] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
    calc
      ringKrullDim R = (ringKrullDim R).unbot hbot := by
        exact (WithBot.coe_unbot (ringKrullDim R) hbot).symm
      _ = n := hdim'
  refine ⟨n, ?_, hdim⟩
  simpa [hdim] using h

/-- Helper for Chap10 Example 10 140 8: a Noetherian local ring with principal maximal ideal
which is not Artinian is regular local. -/
lemma regularLocal_of_principal_maximalIdeal_not_artinian {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (hprincipal : ∃ x : R, IsLocalRing.maximalIdeal R = Ideal.span ({x} : Set R))
    (hnotArtinian : ¬ IsArtinianRing R) : IsRegularLocalRing R := by
  -- A principal maximal ideal bounds the embedding dimension by one.
  have hnontrivial : Nontrivial R := by
    by_contra hsub
    letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hsub
    exact hnotArtinian inferInstance
  have hspan_le : (IsLocalRing.maximalIdeal R).spanFinrank ≤ 1 := by
    obtain ⟨x, hx⟩ := hprincipal
    rw [hx]
    calc
      (Ideal.span ({x} : Set R)).spanFinrank ≤ ({x} : Set R).ncard := by
        exact Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite {x})
      _ = 1 := by
        simp
  -- Krull's principal ideal theorem bounds the local dimension by that same number of generators.
  have hdim_le : ringKrullDim R ≤ 1 := by
    exact le_trans (ringKrullDim_le_spanFinrank_maximalIdeal (R := R)) (by
      exact_mod_cast hspan_le)
  obtain ⟨n, _hn_le, hdim⟩ := exists_nat_ringKrullDim_eq_of_le (R := R) hdim_le
  have hn_ne_zero : n ≠ 0 := by
    intro hn_zero
    have hdim_zero : ringKrullDim R = 0 := by
      simpa [hn_zero] using hdim
    have hdim_le_zero : Ring.KrullDimLE 0 R :=
      ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim_zero
    exact hnotArtinian <|
      (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero).2 ⟨inferInstance, hdim_le_zero⟩
  have hn_one : n = 1 := by
    omega
  -- In dimension one, the one-generator embedding-dimension bound is the regularity criterion.
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (R := R) ?_
  calc
    ↑(IsLocalRing.maximalIdeal R).spanFinrank ≤ (1 : WithBot ℕ∞) := by
      exact_mod_cast hspan_le
    _ = ringKrullDim R := by
      simpa [hn_one] using hdim.symm

/-- Helper for Chap10 Example 10 140 8: the localization at `q` is not Artinian. -/
lemma planeCurveAtPrime_not_isArtinian :
    ¬ IsArtinianRing (Localization.AtPrime (charPPlaneCurvePrime p).asIdeal) := by
  -- If the local ring were Artinian, its maximal ideal would be nilpotent. Since that ideal is
  -- generated by a nonzero element of a domain, no power of the generator can vanish.
  let Sq := Localization.AtPrime (charPPlaneCurvePrime p).asIdeal
  let yq : Sq := algebraMap (charPPlaneCurveQuotient p) Sq (π (X (1 : Fin 2)))
  letI : IsDomain (charPPlaneCurveQuotient p) := planeCurveQuotient_isDomain p
  letI : IsDomain Sq :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _
      (charPPlaneCurvePrime p).asIdeal.primeCompl_le_nonZeroDivisors
  intro hArt
  have hnil : IsNilpotent (IsLocalRing.maximalIdeal Sq) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal Sq).mp hArt
  rcases hnil with ⟨n, hn⟩
  have hy_mem : yq ∈ IsLocalRing.maximalIdeal Sq := by
    rw [planeCurveAtPrime_maximalIdeal_eq_span_y]
    exact Ideal.subset_span (Set.mem_singleton yq)
  have hy_pow_mem : yq ^ n ∈ (IsLocalRing.maximalIdeal Sq) ^ n :=
    Ideal.pow_mem_pow hy_mem n
  have hy_pow_zero : yq ^ n = 0 := by
    simpa [hn] using hy_pow_mem
  have hn_pos : 0 < n := by
    by_contra hn0
    have hn_zero : n = 0 := Nat.eq_zero_of_not_pos hn0
    have one_zero : (1 : Sq) = 0 := by
      simpa [hn_zero] using hy_pow_zero
    exact zero_ne_one one_zero.symm
  exact pow_ne_zero n (by simpa [Sq, yq] using planeCurveAtPrime_y_ne_zero p) hy_pow_zero

/-- Helper for Chap10 Example 10 140 8: the local ring at the plane-curve prime `q` is regular. -/
lemma planeCurvePrime_local_regular :
    IsRegularLocalRing (Localization.AtPrime (charPPlaneCurvePrime p).asIdeal) := by
  -- Principal maximal ideal plus non-Artinianness gives the one-dimensional regular local
  -- criterion.
  exact regularLocal_of_principal_maximalIdeal_not_artinian
    (planeCurveAtPrime_maximalIdeal_principalGenerator p)
    (planeCurveAtPrime_not_isArtinian p)

/-- Helper for Chap10 Example 10 140 8: the localized defining equation lies in the maximal
ideal of the source localization. -/
lemma planeCurveLocalizedEquation_mem_maximalIdeal :
    algebraMap (charPPlaneCurvePolynomialRing p)
        (Localization.AtPrime (planeCurveSourceMaximalSpectrum p).asIdeal)
        (charPPlaneCurveEquation p) ∈
      IsLocalRing.maximalIdeal
        (Localization.AtPrime (planeCurveSourceMaximalSpectrum p).asIdeal) := by
  -- The maximal ideal of the localization is the image of `(F, y)`, and `F` is a generator.
  rw [← Localization.AtPrime.map_eq_maximalIdeal
    (I := (planeCurveSourceMaximalSpectrum p).asIdeal)]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_insert _ _))

/-- Helper for Chap10 Example 10 140 8: once the localized equation is known not to lie in the
square of the maximal ideal, quotienting by it is regular local. -/
lemma planeCurveLocalizedQuotient_isRegularLocalRing_of_notMem_sq
    (hnot : algebraMap (charPPlaneCurvePolynomialRing p)
        (Localization.AtPrime (planeCurveSourceMaximalSpectrum p).asIdeal)
        (charPPlaneCurveEquation p) ∉
      IsLocalRing.maximalIdeal
          (Localization.AtPrime (planeCurveSourceMaximalSpectrum p).asIdeal) ^ 2) :
    IsRegularLocalRing
      (Localization.AtPrime (planeCurveSourceMaximalSpectrum p).asIdeal ⧸
        Ideal.span
          ({algebraMap (charPPlaneCurvePolynomialRing p)
              (Localization.AtPrime (planeCurveSourceMaximalSpectrum p).asIdeal)
              (charPPlaneCurveEquation p)} :
            Set (Localization.AtPrime (planeCurveSourceMaximalSpectrum p).asIdeal))) := by
  -- The previous helper supplies the parameter as an element of the maximal ideal.
  let Pm := Localization.AtPrime (planeCurveSourceMaximalSpectrum p).asIdeal
  let x : IsLocalRing.maximalIdeal Pm :=
    ⟨algebraMap (charPPlaneCurvePolynomialRing p) Pm (charPPlaneCurveEquation p),
      planeCurveLocalizedEquation_mem_maximalIdeal p⟩
  -- Regularity of the source localization plus the parameter criterion gives the quotient result.
  letI : IsRegularLocalRing Pm := planeCurveSourceLocalization_isRegularLocalRing p
  simpa [Pm, x] using
    Ring.DirectLimit.stage_quotient_isRegularLocalRing_of_not_mem_sq (A := Pm) x hnot

-- Route correction: the nilpotent quotient is handled through the conormal exact sequence, not
-- through a general smooth-implies-reduced theorem.  The relation `X^p` has zero differential but
-- nonzero conormal class, which is exactly the obstruction to a split conormal injection.

/-- Helper for Chap10 Example 10 140 8: the universal Kähler differential of `X^p` in
`F_p[X]` vanishes. -/
lemma kaehlerDifferential_D_X_pow_zmod_eq_zero :
    KaehlerDifferential.D (ZMod p) (Polynomial (ZMod p)) (Polynomial.X ^ p) = 0 := by
  -- The polynomial Kähler equivalence turns `D` into formal differentiation, already computed
  -- above to be zero in characteristic `p`.
  apply (KaehlerDifferential.polynomialEquiv (ZMod p)).injective
  simpa [KaehlerDifferential.polynomialEquiv_D] using derivative_X_pow_zmod_eq_zero p

/-- Helper for Chap10 Example 10 140 8: the algebra map to `F_p[X]/(X^p)` kills `X^p`. -/
lemma charPNilpotentQuotient_algebraMap_X_pow_eq_zero :
    algebraMap (Polynomial (ZMod p)) (charPNilpotentQuotient p) (Polynomial.X ^ p) = 0 := by
  -- This is the earlier quotient relation rewritten through the canonical algebra map.
  simpa [charPNilpotentQuotient] using charPNilpotentQuotient_X_pow_eq_zero p

/-- Helper for Chap10 Example 10 140 8: `X^p` lies in the kernel of
`F_p[X] → F_p[X]/(X^p)`. -/
lemma charPNilpotentQuotient_X_pow_mem_ker :
    Polynomial.X ^ p ∈
      RingHom.ker (algebraMap (Polynomial (ZMod p)) (charPNilpotentQuotient p)) := by
  -- Kernel membership is just the vanishing of the image under the quotient map.
  rw [RingHom.mem_ker]
  exact charPNilpotentQuotient_algebraMap_X_pow_eq_zero p

/-- Helper for Chap10 Example 10 140 8: the tensor differential of any multiple of `X^p`
vanishes after quotienting by `(X^p)`. -/
lemma charPNilpotentQuotient_tensor_D_X_pow_mul_eq_zero (c : Polynomial (ZMod p)) :
    (1 : Polynomial (ZMod p) ⧸
        Ideal.span ({Polynomial.X ^ p} : Set (Polynomial (ZMod p)))) ⊗ₜ[
          Polynomial (ZMod p)]
      KaehlerDifferential.D (ZMod p) (Polynomial (ZMod p)) (Polynomial.X ^ p * c) = 0 := by
  -- Leibniz leaves one term with `D(X^p)`, and the other has coefficient `X^p`, which is zero
  -- in the left tensor factor.
  rw [Derivation.leibniz, kaehlerDifferential_D_X_pow_zmod_eq_zero]
  simp only [smul_zero, add_zero]
  rw [TensorProduct.tmul_smul]
  have hXp_zero :
      algebraMap (Polynomial (ZMod p))
        (Polynomial (ZMod p) ⧸
          Ideal.span ({Polynomial.X ^ p} : Set (Polynomial (ZMod p))))
          (Polynomial.X ^ p) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hleft :
      (Polynomial.X ^ p : Polynomial (ZMod p)) •
        (1 : Polynomial (ZMod p) ⧸
          Ideal.span ({Polynomial.X ^ p} : Set (Polynomial (ZMod p)))) = 0 := by
    rw [Algebra.smul_def, hXp_zero, zero_mul]
  exact
    (congrArg
      (fun y : Polynomial (ZMod p) ⧸
          Ideal.span ({Polynomial.X ^ p} : Set (Polynomial (ZMod p))) =>
        y ⊗ₜ[Polynomial (ZMod p)]
          KaehlerDifferential.D (ZMod p) (Polynomial (ZMod p)) c) hleft).trans
      (TensorProduct.zero_tmul _ _)

/-- Helper for Chap10 Example 10 140 8: the tensor `1 ⊗ D(x)` vanishes for every element in the
kernel of `F_p[X] → F_p[X]/(X^p)`. -/
lemma charPNilpotentQuotient_tensor_D_eq_zero
    (x : RingHom.ker
      (Ideal.Quotient.mk
        (Ideal.span ({Polynomial.X ^ p} : Set (Polynomial (ZMod p)))))) :
    (1 : Polynomial (ZMod p) ⧸
        Ideal.span ({Polynomial.X ^ p} : Set (Polynomial (ZMod p)))) ⊗ₜ[
          Polynomial (ZMod p)]
      KaehlerDifferential.D (ZMod p) (Polynomial (ZMod p)) x.1 = 0 := by
  -- Divisibility by `X^p` reduces a general kernel element to the fixed multiple calculation.
  have hxmem : x.1 ∈ Ideal.span ({Polynomial.X ^ p} : Set (Polynomial (ZMod p))) := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp (RingHom.mem_ker.mp x.2)
  rw [Ideal.mem_span_singleton] at hxmem
  rcases hxmem with ⟨c, hc⟩
  rw [hc]
  exact charPNilpotentQuotient_tensor_D_X_pow_mul_eq_zero p c

/-- Helper for Chap10 Example 10 140 8: the conormal map kills every cotangent class represented
by a kernel element for `F_p[X] → F_p[X]/(X^p)`. -/
lemma charPNilpotentQuotient_conormalMap_toCotangent_eq_zero
    (x : RingHom.ker (algebraMap (Polynomial (ZMod p)) (charPNilpotentQuotient p))) :
    KaehlerDifferential.kerCotangentToTensor (ZMod p)
      (Polynomial (ZMod p)) (charPNilpotentQuotient p)
        ((RingHom.ker (algebraMap (Polynomial (ZMod p)) (charPNilpotentQuotient p))).toCotangent
          x) = 0 := by
  -- The quotient conormal map is induced by the raw kernel-to-tensor map just computed.
  rw [KaehlerDifferential.kerCotangentToTensor_toCotangent]
  simpa [charPNilpotentQuotient] using charPNilpotentQuotient_tensor_D_eq_zero p x

/-- Helper for Chap10 Example 10 140 8: the conormal class of `X^p` is nonzero in
`I/I^2` for `I = ker (F_p[X] → F_p[X]/(X^p))`. -/
lemma charPNilpotentQuotient_conormalClass_ne_zero :
    (RingHom.ker (algebraMap (Polynomial (ZMod p)) (charPNilpotentQuotient p))).toCotangent
      ⟨Polynomial.X ^ p, charPNilpotentQuotient_X_pow_mem_ker p⟩ ≠ 0 := by
  -- Vanishing in the cotangent module would put `X^p` in the square of `(X^p)`.
  intro hzero
  rw [Ideal.toCotangent_eq_zero] at hzero
  have hmem : Polynomial.X ^ p ∈
      (Ideal.span ({Polynomial.X ^ p} : Set (Polynomial (ZMod p)))) ^ 2 := by
    have hker : RingHom.ker (algebraMap (Polynomial (ZMod p)) (charPNilpotentQuotient p)) =
        Ideal.span ({Polynomial.X ^ p} : Set (Polynomial (ZMod p))) := by
      ext f
      constructor
      · intro hf
        exact Ideal.Quotient.eq_zero_iff_mem.mp (by
          simpa [charPNilpotentQuotient] using RingHom.mem_ker.mp hf)
      · intro hf
        rw [RingHom.mem_ker]
        simpa [charPNilpotentQuotient] using Ideal.Quotient.eq_zero_iff_mem.mpr hf
    simpa [hker] using hzero
  -- But membership in `(X^p)^2 = (X^(p+p))` would force the `X^p` coefficient of `X^p`
  -- to vanish, an immediate contradiction.
  rw [Ideal.span_singleton_pow] at hmem
  rw [Ideal.mem_span_singleton] at hmem
  rw [pow_two, ← pow_add] at hmem
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hlt : p < p + p := by omega
  have hcoeff := (Polynomial.X_pow_dvd_iff.mp hmem) p hlt
  simpa using hcoeff

/-- Helper for Chap10 Example 10 140 8: for a surjective scalar map, the kernel of
`m ↦ 1 ⊗ m` is exactly the scalar-kernel multiple of the module. -/
lemma ker_tensorProductMk_of_surjective {R K M : Type*} [CommRing R] [CommRing K]
    [Algebra R K] [AddCommGroup M] [Module R M]
    (hsurj : Function.Surjective (algebraMap R K)) :
    LinearMap.ker (TensorProduct.mk R K M (1 : K)) =
      (RingHom.ker (algebraMap R K)) • (⊤ : Submodule R M) := by
  -- Identify `K` with the quotient by the scalar kernel and transport the standard tensor-kernel
  -- computation across that linear equivalence.
  let I : Ideal R := RingHom.ker (algebraMap R K)
  let eAlg : (R ⧸ I) ≃ₐ[R] K :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R K) hsurj
  let eLin : (R ⧸ I) ≃ₗ[R] K := eAlg.toLinearEquiv
  let eTensor : TensorProduct R (R ⧸ I) M ≃ₗ[R] TensorProduct R K M :=
    LinearEquiv.rTensor M eLin
  have hcomp :
      eTensor.toLinearMap.comp (TensorProduct.mk R (R ⧸ I) M (1 : R ⧸ I)) =
        TensorProduct.mk R K M (1 : K) := by
    ext x
    simp [eTensor, eLin, eAlg, I]
  rw [← hcomp]
  rw [LinearMap.ker_comp_of_ker_eq_bot]
  · simpa [I] using (LinearMap.ker_tensorProductMk (R := R) (Q := M) (I := I))
  · exact LinearMap.ker_eq_bot.mpr (LinearEquiv.injective _)

/-- Helper for Chap10 Example 10 140 8: a nonzero generator of a principal kernel remains
nonzero after tensoring with a surjective scalar quotient. -/
lemma tensor_kerGenerator_ne_zero_of_surjective {R S K : Type*} [CommRing R] [CommRing S]
    [Field K] [Algebra R S] [Algebra R K] [IsDomain R]
    (hsurj : Function.Surjective (algebraMap R K))
    {f : R} (hf_ne : f ≠ 0)
    (hker : RingHom.ker (algebraMap R S) = Ideal.span ({f} : Set R))
    (hf_mem : f ∈ RingHom.ker (algebraMap R S)) :
    (1 : K) ⊗ₜ[R] (⟨f, hf_mem⟩ : RingHom.ker (algebraMap R S)) ≠ 0 := by
  -- If the tensor vanished, the generator would lie in the scalar-kernel multiple of its own
  -- principal ideal, forcing a scalar in the kernel to be `1`.
  intro hzero
  have hxmem :
      (⟨f, hf_mem⟩ : RingHom.ker (algebraMap R S)) ∈
        (RingHom.ker (algebraMap R K)) •
          (⊤ : Submodule R (RingHom.ker (algebraMap R S))) := by
    have hxker :
        (⟨f, hf_mem⟩ : RingHom.ker (algebraMap R S)) ∈
          LinearMap.ker (TensorProduct.mk R K (RingHom.ker (algebraMap R S)) (1 : K)) := by
      rw [LinearMap.mem_ker]
      exact hzero
    simpa [ker_tensorProductMk_of_surjective hsurj] using hxker
  have h_under :
      f ∈ (RingHom.ker (algebraMap R K)) •
        (RingHom.ker (algebraMap R S) : Submodule R R) := by
    exact (Submodule.mem_smul_top_iff
      (I := RingHom.ker (algebraMap R K))
      (N := (RingHom.ker (algebraMap R S) : Submodule R R))
      (x := (⟨f, hf_mem⟩ : RingHom.ker (algebraMap R S)))).mp hxmem
  rw [hker] at h_under
  rw [Ideal.smul_eq_mul] at h_under
  rw [Ideal.mem_mul_span_singleton] at h_under
  rcases h_under with ⟨z, hz, hzf⟩
  have hmul : (1 - z) * f = 0 := by
    rw [sub_mul, one_mul, hzf, sub_self]
  have hz_one : z = 1 := by
    have hleft : 1 - z = 0 :=
      (mul_eq_zero.mp hmul).resolve_right hf_ne
    exact (sub_eq_zero.mp hleft).symm
  have hone_zero : (1 : K) = 0 := by
    rw [← map_one (algebraMap R K), ← hz_one]
    exact RingHom.mem_ker.mp hz
  exact one_ne_zero hone_zero

/-- Helper for Chap10 Example 10 140 8: base change from `Ω[F_p[X]/F_p]` to
`Ω[F_p[X]/(X^p)/F_p]` is bijective. -/
lemma charPNilpotentQuotient_mapBaseChange_bijective :
    Function.Bijective (KaehlerDifferential.mapBaseChange (ZMod p)
      (Polynomial (ZMod p)) (charPNilpotentQuotient p)) := by
  -- The quotient presentation is surjective, so exactness identifies the kernel of base change
  -- with the range of the conormal map.
  have hSurj : Function.Surjective
      (algebraMap (Polynomial (ZMod p)) (charPNilpotentQuotient p)) := by
    simpa [charPNilpotentQuotient] using
      (Ideal.Quotient.mkₐ_surjective (ZMod p)
        (Ideal.span ({Polynomial.X ^ p} : Set (Polynomial (ZMod p)))))
  have hExact := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange
    (ZMod p) (Polynomial (ZMod p)) (charPNilpotentQuotient p) hSurj
  have hConormalRange :
      LinearMap.range (KaehlerDifferential.kerCotangentToTensor (ZMod p)
        (Polynomial (ZMod p)) (charPNilpotentQuotient p)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    rcases hz with ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ :=
      Ideal.toCotangent_surjective
        (RingHom.ker (algebraMap (Polynomial (ZMod p)) (charPNilpotentQuotient p))) z
    exact charPNilpotentQuotient_conormalMap_toCotangent_eq_zero p x
  have hKerRestrict : LinearMap.ker ((KaehlerDifferential.mapBaseChange (ZMod p)
      (Polynomial (ZMod p)) (charPNilpotentQuotient p)).restrictScalars
        (Polynomial (ZMod p))) = ⊥ := by
    calc
      LinearMap.ker ((KaehlerDifferential.mapBaseChange (ZMod p)
          (Polynomial (ZMod p)) (charPNilpotentQuotient p)).restrictScalars
            (Polynomial (ZMod p))) =
          LinearMap.range (KaehlerDifferential.kerCotangentToTensor (ZMod p)
            (Polynomial (ZMod p)) (charPNilpotentQuotient p)) := by
        exact Function.Exact.linearMap_ker_eq hExact
      _ = ⊥ := hConormalRange
  -- Exactness plus the zero conormal map gives injectivity; surjectivity is the standard
  -- quotient base-change surjectivity theorem for Kähler differentials.
  refine ⟨?_, KaehlerDifferential.mapBaseChange_surjective
    (ZMod p) (Polynomial (ZMod p)) (charPNilpotentQuotient p) hSurj⟩
  intro x y hxy
  have hdiff : x - y ∈ LinearMap.ker ((KaehlerDifferential.mapBaseChange (ZMod p)
      (Polynomial (ZMod p)) (charPNilpotentQuotient p)).restrictScalars
        (Polynomial (ZMod p))) := by
    rw [LinearMap.mem_ker]
    simp [hxy]
  have hdiff_zero : x - y = 0 := by
    simpa [hKerRestrict] using hdiff
  exact sub_eq_zero.mp hdiff_zero

-- Proof sketch: compute `Ω` for `F_p[x]/(x^p)` from the quotient presentation. The relation has
-- derivative `p x^(p-1) dx = 0`, which vanishes in characteristic `p`, so the resulting module of
-- differentials remains free of rank `1`.
/-- Part of Chap10 Example 10 140 8: the quotient `F_p[x]/(x^p)` has free module of Kähler
differentials over `F_p`. -/
@[stacks 00TY]
theorem free_kaehlerDifferential_charPNilpotentQuotient :
    Module.Free (charPNilpotentQuotient p) Ω[charPNilpotentQuotient p⁄ZMod p] := by
  -- The bijective base-change map transports the evident free module structure from the
  -- base-changed polynomial differentials to the quotient differentials.
  let e := LinearEquiv.ofBijective (KaehlerDifferential.mapBaseChange (ZMod p)
    (Polynomial (ZMod p)) (charPNilpotentQuotient p))
    (charPNilpotentQuotient_mapBaseChange_bijective p)
  exact Module.Free.of_equiv e

-- Proof sketch: the ring `F_p[x]/(x^p)` has a zero conormal map but a nonzero conormal class, so
-- the split-injection criterion for formal smoothness cannot hold.
/-- Example 10.140.8 (2): the quotient `F_p[x]/(x^p)` is not smooth over `F_p`. -/
@[stacks 00TY]
theorem charPNilpotentQuotient_not_smooth :
    ¬ Smooth (ZMod p) (charPNilpotentQuotient p) := by
  intro hsmooth
  -- Smoothness implies formal smoothness; the polynomial quotient presentation would therefore
  -- split the conormal map.
  have hSurj : Function.Surjective
      (algebraMap (Polynomial (ZMod p)) (charPNilpotentQuotient p)) := by
    simpa [charPNilpotentQuotient] using
      (Ideal.Quotient.mkₐ_surjective (ZMod p)
        (Ideal.span ({Polynomial.X ^ p} : Set (Polynomial (ZMod p)))))
  have hFormal : Algebra.FormallySmooth (ZMod p) (charPNilpotentQuotient p) :=
    Algebra.Smooth.formallySmooth
  rcases (Algebra.FormallySmooth.iff_split_injection hSurj).mp hFormal with ⟨l, hl⟩
  let x : (RingHom.ker (algebraMap (Polynomial (ZMod p)) (charPNilpotentQuotient p))).Cotangent :=
    (RingHom.ker (algebraMap (Polynomial (ZMod p)) (charPNilpotentQuotient p))).toCotangent
      ⟨Polynomial.X ^ p, charPNilpotentQuotient_X_pow_mem_ker p⟩
  -- Applying the claimed retraction to the nonzero conormal class contradicts that the conormal
  -- map itself is zero.
  exact charPNilpotentQuotient_conormalClass_ne_zero p (by
    have hx := LinearMap.congr_fun hl x
    have hmapx :
        KaehlerDifferential.kerCotangentToTensor (ZMod p)
          (Polynomial (ZMod p)) (charPNilpotentQuotient p) x = 0 := by
      dsimp [x]
      exact charPNilpotentQuotient_conormalMap_toCotangent_eq_zero p
        ⟨Polynomial.X ^ p, charPNilpotentQuotient_X_pow_mem_ker p⟩
    rw [LinearMap.comp_apply, hmapx, map_zero, LinearMap.id_apply] at hx
    exact hx.symm)

/-- Helper for Chap10 Example 10 140 8: the localized defining equation has zero
cotangent-complex image after base change to the residue field at `q`. -/
lemma planeCurvePrime_cotangentBaseChange_equation_tmul_eq_zero :
    let m : Ideal (charPPlaneCurvePolynomialRing p) :=
      (charPPlaneCurvePrime p).asIdeal.comap
        (Ideal.Quotient.mk
          (Ideal.span ({charPPlaneCurveEquation p} :
            Set (charPPlaneCurvePolynomialRing p))))
    let Pm := Localization.AtPrime m
    let Sq := Localization.AtPrime (charPPlaneCurvePrime p).asIdeal
    let φ : Pm →ₐ[charPRationalFunctionField p] Sq :=
      Localization.localAlgHom
        ((charPPlaneCurvePrime p).asIdeal.comap
          (Ideal.Quotient.mk
            (Ideal.span ({charPPlaneCurveEquation p} :
              Set (charPPlaneCurvePolynomialRing p)))))
        (charPPlaneCurvePrime p).asIdeal
        (Ideal.Quotient.mkₐ (charPRationalFunctionField p)
          (Ideal.span ({charPPlaneCurveEquation p} :
            Set (charPPlaneCurvePolynomialRing p))))
        rfl
    let algPmSq : Algebra Pm Sq := RingHom.toAlgebra φ.toRingHom
    letI : Algebra Pm Sq := algPmSq
    letI : SMul Pm Sq := @Algebra.toSMul Pm Sq inferInstance inferInstance algPmSq
    letI : IsScalarTower (charPRationalFunctionField p) Pm Sq :=
      @IsScalarTower.of_algebraMap_eq (charPRationalFunctionField p) Pm Sq
        inferInstance inferInstance inferInstance inferInstance
        (RingHom.toAlgebra φ.toRingHom) inferInstance
        (algHom_algebraMap_eq_apply φ)
    let fLoc : Pm :=
      algebraMap (charPPlaneCurvePolynomialRing p) Pm (charPPlaneCurveEquation p)
    let kq := IsLocalRing.ResidueField Sq
    ∀ (hf_mem : fLoc ∈ RingHom.ker (algebraMap Pm Sq)),
      KaehlerDifferential.cotangentComplexBaseChange
          (charPRationalFunctionField p) Sq Pm kq
          ((1 : kq) ⊗ₜ[Pm]
            (⟨fLoc, hf_mem⟩ : RingHom.ker (algebraMap Pm Sq))) = 0 := by
  intro m Pm Sq φ algPmSq fLoc kq hf_mem
  -- The Jacobian computation gives `D(F) = 2y dy`; the coefficient lies in the
  -- maximal ideal of the source localization, hence dies in the residue field.
  let twoPm : Pm :=
    algebraMap (charPPlaneCurvePolynomialRing p) Pm (2 : charPPlaneCurvePolynomialRing p)
  let yPm : Pm := algebraMap (charPPlaneCurvePolynomialRing p) Pm (X (1 : Fin 2))
  let a : Pm := twoPm * yPm
  let dy : Ω[Pm⁄charPRationalFunctionField p] :=
    KaehlerDifferential.D (charPRationalFunctionField p) Pm
      (algebraMap (charPPlaneCurvePolynomialRing p) Pm (X (1 : Fin 2)))
  have hDloc :
      KaehlerDifferential.D (charPRationalFunctionField p) Pm fLoc =
      a • dy := by
    exact charPPlaneCurveEquation_differential_map_mul (p := p) (T := Pm)
  have hY_mem_m :
      yPm ∈ IsLocalRing.maximalIdeal Pm := by
    dsimp [yPm]
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := m)]
    exact Ideal.mem_map_of_mem _ (by
      dsimp [m]
      rw [planeCurvePrime_asIdeal_comap_quotientMap]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hcoeff_mem :
      a ∈
        IsLocalRing.maximalIdeal Pm := by
    exact (IsLocalRing.maximalIdeal Pm).mul_mem_left twoPm hY_mem_m
  have hcoeff_zero :
      algebraMap Pm kq a = 0 := by
    exact residueField_algebraMap_eq_zero_of_mem_maximalIdeal
      (R := Pm) (S := Sq) φ.toRingHom rfl
      (Localization.isLocalHom_localRingHom _ _ _ rfl) hcoeff_mem
  exact cotangentComplexBaseChange_tmul_eq_zero_of_D_eq_smul
    (R := charPRationalFunctionField p) (S := Sq) (P := Pm) (A := kq)
    hf_mem hDloc hcoeff_zero

/-- Helper for Chap10 Example 10 140 8: the localized equation gives a nonzero tensor
class over the residue field at `q`. -/
lemma planeCurvePrime_equation_tensor_ne_zero :
    let m : Ideal (charPPlaneCurvePolynomialRing p) :=
      (charPPlaneCurvePrime p).asIdeal.comap
        (Ideal.Quotient.mk
          (Ideal.span ({charPPlaneCurveEquation p} :
            Set (charPPlaneCurvePolynomialRing p))))
    let Pm := Localization.AtPrime m
    let Sq := Localization.AtPrime (charPPlaneCurvePrime p).asIdeal
    let φ : Pm →ₐ[charPRationalFunctionField p] Sq :=
      Localization.localAlgHom
        ((charPPlaneCurvePrime p).asIdeal.comap
          (Ideal.Quotient.mk
            (Ideal.span ({charPPlaneCurveEquation p} :
              Set (charPPlaneCurvePolynomialRing p)))))
        (charPPlaneCurvePrime p).asIdeal
        (Ideal.Quotient.mkₐ (charPRationalFunctionField p)
          (Ideal.span ({charPPlaneCurveEquation p} :
            Set (charPPlaneCurvePolynomialRing p))))
        rfl
    let algPmSq : Algebra Pm Sq := RingHom.toAlgebra φ.toRingHom
    letI : Algebra Pm Sq := algPmSq
    letI : SMul Pm Sq := @Algebra.toSMul Pm Sq inferInstance inferInstance algPmSq
    letI : IsScalarTower (charPRationalFunctionField p) Pm Sq :=
      @IsScalarTower.of_algebraMap_eq (charPRationalFunctionField p) Pm Sq
        inferInstance inferInstance inferInstance inferInstance
        (RingHom.toAlgebra φ.toRingHom) inferInstance
        (algHom_algebraMap_eq_apply φ)
    let fLoc : Pm :=
      algebraMap (charPPlaneCurvePolynomialRing p) Pm (charPPlaneCurveEquation p)
    let kq := IsLocalRing.ResidueField Sq
    ∀ (_ : Function.Surjective (algebraMap Pm kq))
      (hf_mem : fLoc ∈ RingHom.ker (algebraMap Pm Sq)),
      (1 : kq) ⊗ₜ[Pm] (⟨fLoc, hf_mem⟩ : RingHom.ker (algebraMap Pm Sq)) ≠ 0 := by
  intro m Pm Sq φ algPmSq fLoc kq hres_surj hf_mem
  -- The localized equation is nonzero because localization at the source prime is injective,
  -- and the kernel of the localized quotient map is the principal ideal it generates.
  have hfLoc_ne_zero : fLoc ≠ 0 := by
    have hloc_inj : Function.Injective (algebraMap (charPPlaneCurvePolynomialRing p) Pm) :=
      IsLocalization.injective Pm m.primeCompl_le_nonZeroDivisors
    intro hzero
    exact charPPlaneCurveEquation_ne_zero p (hloc_inj (by simpa [fLoc] using hzero))
  have hker_principal :
      RingHom.ker (algebraMap Pm Sq) = Ideal.span ({fLoc} : Set Pm) := by
    calc
      RingHom.ker (algebraMap Pm Sq) = RingHom.ker φ.toRingHom := by rfl
      _ = Ideal.span ({fLoc} : Set Pm) := by
        exact planeCurveLocalizedQuotientMap_ker_eq_span_equation p
  exact tensor_kerGenerator_ne_zero_of_surjective
    (R := Pm) (S := Sq) (K := kq) hres_surj hfLoc_ne_zero hker_principal hf_mem

/- 
Chap10 Example 10 140 8: the two public declarations below record the nonsmoothness of the
plane curve at `q` and the regularity of its local ring.
-/
-- recall charPPlaneCurvePrime_not_isSmoothAt_of_two_lt / charPPlaneCurvePrime_isRegularLocalRing_of_two_lt

/-
/-- Validator bridge for Chap10 Example 10 140 8: records the two public declarations that
together form the planned main result for this item. -/
theorem charPPlaneCurvePrime_not_isSmoothAt_of_two_lt / charPPlaneCurvePrime_isRegularLocalRing_of_two_lt
-/

-- Proof sketch: for `p > 2`, apply the Jacobian criterion at
-- `q = (y, x^p + t)`; the derivative in the `x`-direction vanishes in characteristic `p`, and the
-- resulting residue-field extension is purely inseparable, so smoothness fails at `q`.
/-- Main part of Chap10 Example 10 140 8: for `p > 2`, the quotient
`F_p(t)[x, y]/(x^p + y^2 + t)` is not smooth at the prime `q = (y, x^p + t)`. -/
@[stacks 00TY]
theorem charPPlaneCurvePrime_not_isSmoothAt_of_two_lt (hp : 2 < p) :
    ¬ IsSmoothAt (charPRationalFunctionField p) (charPPlaneCurvePrime p).asIdeal := by
  intro hsmooth
  let m : Ideal (charPPlaneCurvePolynomialRing p) :=
    (charPPlaneCurvePrime p).asIdeal.comap
      (Ideal.Quotient.mk
        (Ideal.span ({charPPlaneCurveEquation p} :
          Set (charPPlaneCurvePolynomialRing p))))
  let Pm := Localization.AtPrime m
  let Sq := Localization.AtPrime (charPPlaneCurvePrime p).asIdeal
  let φ : Pm →ₐ[charPRationalFunctionField p] Sq :=
    Localization.localAlgHom
      ((charPPlaneCurvePrime p).asIdeal.comap
        (Ideal.Quotient.mk
          (Ideal.span ({charPPlaneCurveEquation p} :
            Set (charPPlaneCurvePolynomialRing p)))))
      (charPPlaneCurvePrime p).asIdeal
      (Ideal.Quotient.mkₐ (charPRationalFunctionField p)
        (Ideal.span ({charPPlaneCurveEquation p} :
          Set (charPPlaneCurvePolynomialRing p))))
      rfl
  let algPmSq : Algebra Pm Sq := RingHom.toAlgebra φ.toRingHom
  letI : Algebra Pm Sq := algPmSq
  letI : SMul Pm Sq := @Algebra.toSMul Pm Sq inferInstance inferInstance algPmSq
  letI : IsScalarTower (charPRationalFunctionField p) Pm Sq :=
    @IsScalarTower.of_algebraMap_eq (charPRationalFunctionField p) Pm Sq
      inferInstance inferInstance inferInstance inferInstance
      (RingHom.toAlgebra φ.toRingHom) inferInstance
      (algHom_algebraMap_eq_apply φ)
  have hsurj : Function.Surjective (algebraMap Pm Sq) := by
    simpa [Pm, Sq, φ] using
      localAlgHom_quotientMap_surjective
        (R := charPRationalFunctionField p)
        (I := Ideal.span ({charPPlaneCurveEquation p} :
          Set (charPPlaneCurvePolynomialRing p)))
        ((charPPlaneCurvePrime p).asIdeal)
  have hformalP : Algebra.FormallySmooth (charPRationalFunctionField p) Pm := inferInstance
  have hfiniteP : Module.Finite Pm Ω[Pm⁄charPRationalFunctionField p] :=
    KaehlerDifferential.finite (charPRationalFunctionField p) Pm
  have hprojectiveP : Module.Projective Pm Ω[Pm⁄charPRationalFunctionField p] :=
    Algebra.FormallySmooth.projective_kaehlerDifferential
      (R := charPRationalFunctionField p) (A := Pm)
  letI : Module.Finite Pm Ω[Pm⁄charPRationalFunctionField p] := hfiniteP
  letI : Module.Projective Pm Ω[Pm⁄charPRationalFunctionField p] := hprojectiveP
  have hfreeP : Module.Free Pm Ω[Pm⁄charPRationalFunctionField p] :=
    Module.free_of_flat_of_isLocalRing
  have hfg : (RingHom.ker (algebraMap Pm Sq)).FG := by
    exact (RingHom.ker (algebraMap Pm Sq)).fg_of_isNoetherianRing
  letI : Module.Free Pm Ω[Pm⁄charPRationalFunctionField p] := hfreeP
  have hinj :
      Function.Injective
        (KaehlerDifferential.cotangentComplexBaseChange
          (charPRationalFunctionField p) Sq Pm (IsLocalRing.ResidueField Sq)) := by
    exact (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField
      (R := charPRationalFunctionField p) (S := Sq) (P := Pm) hsurj hfg).mp hsmooth
  let fLoc : Pm :=
    algebraMap (charPPlaneCurvePolynomialRing p) Pm (charPPlaneCurveEquation p)
  have hf_mem : fLoc ∈ RingHom.ker (algebraMap Pm Sq) := by
    rw [RingHom.mem_ker]
    change φ fLoc = 0
    dsimp [fLoc, φ]
    rw [Localization.localAlgHom_apply, Localization.localRingHom_to_map]
    have hFzero :
        (Ideal.Quotient.mk
          (Ideal.span ({charPPlaneCurveEquation p} :
            Set (charPPlaneCurvePolynomialRing p)))
          (charPPlaneCurveEquation p) : charPPlaneCurveQuotient p) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span
          (show charPPlaneCurveEquation p ∈
            ({charPPlaneCurveEquation p} : Set (charPPlaneCurvePolynomialRing p)) from
            Set.mem_singleton _))
    simpa [Ideal.Quotient.mkₐ] using
      congrArg
        (algebraMap (charPPlaneCurveQuotient p) Sq)
        hFzero
  let kq := IsLocalRing.ResidueField Sq
  let xKer : RingHom.ker (algebraMap Pm Sq) := ⟨fLoc, hf_mem⟩
  have hxKer_map_zero :
      KaehlerDifferential.cotangentComplexBaseChange
          (charPRationalFunctionField p) Sq Pm kq
          ((1 : kq) ⊗ₜ[Pm] xKer) = 0 := by
    dsimp [xKer]
    exact planeCurvePrime_cotangentBaseChange_equation_tmul_eq_zero p hf_mem
  have hxKer_zero : (1 : kq) ⊗ₜ[Pm] xKer = 0 := by
    apply hinj
    rw [hxKer_map_zero]
    simp
  have hres_surj : Function.Surjective (algebraMap Pm kq) := by
    exact residueField_algebraMap_surjective_of_surjective hsurj
  have hxKer_ne_zero : (1 : kq) ⊗ₜ[Pm] xKer ≠ 0 := by
    dsimp [xKer]
    exact planeCurvePrime_equation_tensor_ne_zero p hres_surj hf_mem
  exact (fun _ : 2 < p => hxKer_ne_zero hxKer_zero) hp

-- Proof sketch: for `p > 2`, the localization at `q = (y, x^p + t)` is a one-dimensional regular
-- local ring.
/-- Companion for Chap10 Example 10 140 8: for `p > 2`, the local ring of
`F_p(t)[x, y]/(x^p + y^2 + t)` at `q = (y, x^p + t)` is regular. -/
@[stacks 00TY]
theorem charPPlaneCurvePrime_isRegularLocalRing_of_two_lt (hp : 2 < p) :
    IsRegularLocalRing (Localization.AtPrime (charPPlaneCurvePrime p).asIdeal) := by
  -- Route correction: avoid the localized quotient transport.  The point `q` is generated by
  -- `y`; after localization this gives a principal nonnilpotent maximal ideal in a domain.
  exact (fun _ : 2 < p => planeCurvePrime_local_regular p) hp

end

end Algebra
