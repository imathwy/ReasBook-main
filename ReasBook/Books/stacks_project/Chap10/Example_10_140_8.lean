import Mathlib

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

/-- The coefficient field `F_p(t)` used in the plane-curve counterexample. -/
abbrev charPRationalFunctionField : Type :=
  RatFunc (ZMod p)

/-- The bivariate polynomial ring over `F_p(t)` with coordinates `x` and `y`. -/
abbrev charPPlaneCurvePolynomialRing : Type :=
  MvPolynomial (Fin 2) (charPRationalFunctionField p)

/-- The defining equation `x^p + y^2 + t` of the plane-curve example over `F_p(t)`. -/
abbrev charPPlaneCurveEquation : charPPlaneCurvePolynomialRing p :=
  X (0 : Fin 2) ^ p + X (1 : Fin 2) ^ 2 + C (RatFunc.X : charPRationalFunctionField p)

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

-- Proof sketch: in the quotient by `x^p + y^2 + t`, modding out further by `(y, x^p + t)` gives a
-- field, so this ideal is maximal and hence prime.
/-- The ideal `(y, x^p + t)` is prime in the plane-curve quotient ring. -/
lemma charPPlaneCurvePrimeIdeal_isPrime : (charPPlaneCurvePrimeIdeal p).IsPrime := sorry

/-- The prime `q = (y, x^p + t)` in the plane-curve example. -/
def charPPlaneCurvePrime : PrimeSpectrum (charPPlaneCurveQuotient p) :=
  ⟨charPPlaneCurvePrimeIdeal p, charPPlaneCurvePrimeIdeal_isPrime p⟩

-- Proof sketch: compute `Ω` for `F_p[x]/(x^p)` from the quotient presentation. The relation has
-- derivative `p x^(p-1) dx = 0`, which vanishes in characteristic `p`, so the resulting module of
-- differentials remains free of rank `1`.
/-- Example 10.140.8 (1): the quotient `F_p[x]/(x^p)` has free module of Kähler differentials over
`F_p`. -/
theorem free_kaehlerDifferential_charPNilpotentQuotient :
    Module.Free (charPNilpotentQuotient p) Ω[charPNilpotentQuotient p⁄ZMod p] := sorry

-- Proof sketch: the ring `F_p[x]/(x^p)` has a nonzero nilpotent class, so it is not smooth over
-- `F_p`.
/-- Example 10.140.8 (2): the quotient `F_p[x]/(x^p)` is not smooth over `F_p`. -/
theorem charPNilpotentQuotient_not_smooth :
    ¬ Smooth (ZMod p) (charPNilpotentQuotient p) := sorry

-- Proof sketch: for `p > 2`, apply the Jacobian criterion at
-- `q = (y, x^p + t)`; the derivative in the `x`-direction vanishes in characteristic `p`, and the
-- resulting residue-field extension is purely inseparable, so smoothness fails at `q`.
/-- Example 10.140.8 (3): for `p > 2`, the quotient `F_p(t)[x, y]/(x^p + y^2 + t)` is not smooth
at the prime `q = (y, x^p + t)`. -/
theorem charPPlaneCurvePrime_not_isSmoothAt_of_two_lt (hp : 2 < p) :
    ¬ IsSmoothAt (charPRationalFunctionField p) (charPPlaneCurvePrime p).asIdeal := sorry

-- Proof sketch: for `p > 2`, the localization at `q = (y, x^p + t)` is a one-dimensional regular
-- local ring.
/-- Example 10.140.8 (4): for `p > 2`, the local ring of
`F_p(t)[x, y]/(x^p + y^2 + t)` at `q = (y, x^p + t)` is regular. -/
theorem charPPlaneCurvePrime_isRegularLocalRing_of_two_lt (hp : 2 < p) :
    IsRegularLocalRing (Localization.AtPrime (charPPlaneCurvePrime p).asIdeal) := sorry

end

end Algebra
