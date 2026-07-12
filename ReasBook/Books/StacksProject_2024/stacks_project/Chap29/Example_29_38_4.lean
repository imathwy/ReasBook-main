import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Basic

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the canonical projective-spectrum owner `AlgebraicGeometry.Proj`;
- the current mathlib `AlgebraicGeometry` source tree in this workspace exposes `Proj` and its
  basic-open affine charts, but it does not expose a scheme-theoretic `Ample`/`VeryAmple` owner;
- this file therefore records the explicit graded algebra and the affine-chart finite-type
  obstruction from the source, which is the source-visible content available on the current API.
-/

-- Example 29.38.4: the explicit graded algebra and its affine chart used for the source
-- obstruction to relative very ampleness.
namespace Example29384

open MvPolynomial

/-- The variables `U`, `V`, and `Z_(n + 1)` used in the graded polynomial presentation of the
source algebra in Example 29.38.4. The constructor `Z n` corresponds to the textbook variable
`Z_(n + 1)`. -/
inductive Var where
  | U
  | V
  | Z : ℕ → Var
deriving DecidableEq

/-- The polynomial ring `k[U, V, Z_1, Z_2, Z_3, \ldots]` used before quotienting in
Example 29.38.4. -/
abbrev PolynomialRing (k : Type u) [CommRing k] := MvPolynomial Var k

/-- The distinguished variable `U` in the polynomial presentation of Example 29.38.4. -/
abbrev U (k : Type u) [CommRing k] : PolynomialRing k :=
  X Var.U

/-- The distinguished variable `V` in the polynomial presentation of Example 29.38.4. -/
abbrev V (k : Type u) [CommRing k] : PolynomialRing k :=
  X Var.V

/-- The variable `Z_(n + 1)` in the polynomial presentation of Example 29.38.4. -/
abbrev Z (k : Type u) [CommRing k] (n : ℕ) : PolynomialRing k :=
  X (Var.Z n)

/-- The grading weight on the generators of the polynomial presentation in Example 29.38.4:
`deg(U) = deg(V) = 1` and `deg(Z_(n + 1)) = n + 1`. -/
def weight : Var → ℕ
  | .U => 1
  | .V => 1
  | .Z n => n + 1

section

variable (k : Type u) [CommRing k]

/-- The `n`-th defining relation `U^(2(n + 1)) - Z_(n + 1)^2` from Example 29.38.4. -/
def relation (n : ℕ) : PolynomialRing k :=
  U k ^ (2 * (n + 1)) - Z k n ^ 2

/-- The ideal
`I = (U^2 - Z_1^2, U^4 - Z_2^2, U^6 - Z_3^2, \ldots)` from Example 29.38.4. -/
def ideal : Ideal (PolynomialRing k) :=
  Ideal.span (Set.range (relation k))

/-- The graded `k`-algebra
`A = k[U, V, Z_1, Z_2, Z_3, \ldots] / I`
from Example 29.38.4, forgetting the grading structure but keeping the explicit quotient ring. -/
abbrev Ring := PolynomialRing k ⧸ ideal k

/-- The quotient map onto the explicit ring presentation from Example 29.38.4. -/
def quotientMap : PolynomialRing k →ₐ[k] Ring k :=
  Ideal.Quotient.mkₐ k (ideal k)

/-- Each defining relation of Example 29.38.4 vanishes in the explicit quotient ring
presentation. -/
@[simp] theorem quotientMap_relation_eq_zero (n : ℕ) :
    quotientMap k (relation k n) = 0 := by
  exact Ideal.Quotient.eq_zero_iff_mem.2 <| Ideal.subset_span ⟨n, rfl⟩

/-- In the explicit quotient ring from Example 29.38.4, the source relation
`U^(2(n + 1)) = Z_(n + 1)^2` holds. -/
theorem quotientMap_u_pow_eq_z_sq (n : ℕ) :
    quotientMap k (U k ^ (2 * (n + 1))) = quotientMap k (Z k n ^ 2) := by
  have h := quotientMap_relation_eq_zero (k := k) n
  simpa [relation, map_sub] using sub_eq_zero.mp h

/-- The variables `t` and `t_(n + 1)` used in the explicit affine chart
`k[t, t_1, t_2, t_3, \ldots]` from Example 29.38.4. The constructor `T n` corresponds to the
textbook variable `t_(n + 1)`. -/
inductive ChartVar where
  | t
  | T : ℕ → ChartVar
deriving DecidableEq

/-- The polynomial ring `k[t, t_1, t_2, t_3, \ldots]` used for the `D_+(V)`-chart in
Example 29.38.4. -/
abbrev VChartPolynomialRing := MvPolynomial ChartVar k

/-- The distinguished variable `t` in the affine chart ring from Example 29.38.4. -/
abbrev t : VChartPolynomialRing k :=
  X ChartVar.t

/-- The variable `t_(n + 1)` in the affine chart ring from Example 29.38.4. -/
abbrev T (n : ℕ) : VChartPolynomialRing k :=
  X (ChartVar.T n)

/-- The `n`-th affine-chart relation `t^(2(n + 1)) - t_(n + 1)^2` from Example 29.38.4. -/
def vChartRelation (n : ℕ) : VChartPolynomialRing k :=
  t k ^ (2 * (n + 1)) - T k n ^ 2

/-- The ideal
`(t^2 - t_1^2, t^4 - t_2^2, t^6 - t_3^2, \ldots)`
from the affine chart `D_+(V)` in Example 29.38.4. -/
def vChartIdeal : Ideal (VChartPolynomialRing k) :=
  Ideal.span (Set.range (vChartRelation k))

/-- The explicit affine ring
`k[t, t_1, t_2, t_3, \ldots] / (t^2 - t_1^2, t^4 - t_2^2, t^6 - t_3^2, \ldots)`
appearing as the `D_+(V)`-chart in Example 29.38.4. -/
abbrev VChartRing := VChartPolynomialRing k ⧸ vChartIdeal k

/-- The quotient map onto the `D_+(V)` affine chart ring from Example 29.38.4. -/
def vChartQuotientMap :
    VChartPolynomialRing k →ₐ[k] VChartRing k :=
  Ideal.Quotient.mkₐ k (vChartIdeal k)

/-- Each affine-chart defining relation of Example 29.38.4 vanishes in the explicit `D_+(V)`
quotient ring. -/
@[simp] theorem vChartQuotientMap_relation_eq_zero (n : ℕ) :
    vChartQuotientMap k (vChartRelation k n) = 0 := by
  exact Ideal.Quotient.eq_zero_iff_mem.2 <| Ideal.subset_span ⟨n, rfl⟩

/-- In the explicit `D_+(V)` chart ring from Example 29.38.4, the source relation
`t^(2(n + 1)) = t_(n + 1)^2` holds. -/
theorem vChartQuotientMap_t_pow_eq_T_sq (n : ℕ) :
    vChartQuotientMap k (t k ^ (2 * (n + 1))) = vChartQuotientMap k (T k n ^ 2) := by
  have h := vChartQuotientMap_relation_eq_zero (k := k) n
  simpa [vChartRelation, map_sub] using sub_eq_zero.mp h

variable [Field k]

/-- Example 29.38.4: the explicit affine ring
`k[t, t_1, t_2, t_3, \ldots] / (t^2 - t_1^2, t^4 - t_2^2, t^6 - t_3^2, \ldots)`
appearing on the basic open `D_+(V)` is not of finite type over `k`.

This is the ring-theoretic obstruction used in the source to conclude that no power of the
tautological invertible sheaf on the associated `Proj` is relatively very ample. -/
theorem vChartRing_not_finiteType :
    ¬ Algebra.FiniteType k (VChartRing k) := sorry

end

end Example29384
