import Mathlib
import stacks_project.Chap10.EqualEndpointRing

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open IsLocalRing
open Polynomial
open PrimeSpectrum
open Topology
open scoped Polynomial.Bivariate

local notation "R" => equal_endpoint_poly_subring ℚ

private theorem equal_endpoint_C_mem (q : ℚ) : C q ∈ R := by
  rw [mem_equal_endpoint_poly_subring_iff]
  simp

instance : Algebra ℚ R :=
  (C.codRestrict R equal_endpoint_C_mem).toAlgebra

private theorem equal_endpoint_quad_mem : (X ^ 2 - X : Polynomial ℚ) ∈ R := by
  rw [mem_equal_endpoint_poly_subring_iff]
  norm_num

private theorem equal_endpoint_cubic_mem : (X ^ 3 - X ^ 2 : Polynomial ℚ) ∈ R := by
  rw [mem_equal_endpoint_poly_subring_iff]
  norm_num

private def equal_endpoint_quad : R :=
  ⟨X ^ 2 - X, equal_endpoint_quad_mem⟩

private def equal_endpoint_cubic : R :=
  ⟨X ^ 3 - X ^ 2, equal_endpoint_cubic_mem⟩

/-- The relation `A^3 - B^2 + AB` from the quotient presentation of Example 10.27.4, modeled in
`ℚ[X][Y]` with `A = C X` and `B = Y`. -/
def equal_endpoint_relation : ℚ[X][Y] :=
  C (X ^ 3) - Y ^ 2 + C X * Y

/-- The map `φ : ℚ[A, B] → R` from Example 10.27.4, modeled as a bivariate polynomial map
`ℚ[X][Y] →ₐ[ℚ] R` sending `A` to `z^2 - z` and `B` to `z^3 - z^2`. -/
def equal_endpoint_presentation : ℚ[X][Y] →ₐ[ℚ] R :=
  Polynomial.aevalAeval equal_endpoint_quad equal_endpoint_cubic

/-- The presentation map from Example 10.27.4 is surjective. -/
-- Proof sketch: every polynomial `f` with `f(0) = f(1)` factors through the parameterization
-- `A = z^2 - z`, `B = z^3 - z^2`, so `f` lies in the image of `equal_endpoint_presentation`.
theorem equal_endpoint_presentation_surjective :
    Function.Surjective equal_endpoint_presentation := sorry

/-- Example 10.27.4 (1): the kernel of `φ` is the principal ideal
`(A^3 - B^2 + AB)`. -/
-- Proof sketch: the displayed relation vanishes under `A = z^2 - z`, `B = z^3 - z^2`, and the
-- example shows that this single relation generates all polynomial relations among those two
-- generators.
theorem equal_endpoint_presentation_ker :
    RingHom.ker equal_endpoint_presentation =
      Ideal.span ({equal_endpoint_relation} : Set ℚ[X][Y]) := sorry

private theorem equal_endpoint_presentation_range_eq_top :
    equal_endpoint_presentation.range = (⊤ : Subalgebra ℚ R) := by
  rw [eq_top_iff]
  intro x _
  rcases equal_endpoint_presentation_surjective x with ⟨f, rfl⟩
  exact equal_endpoint_presentation.mem_range_self f

/-- Hence `R ≃ ℚ[A, B] / (A^3 - B^2 + AB)`; in Lean, `ℚ[A, B]` is modeled by `ℚ[X][Y]`. -/
noncomputable def equal_endpoint_presentation_quotientEquiv :
    (ℚ[X][Y] ⧸ Ideal.span ({equal_endpoint_relation} : Set ℚ[X][Y])) ≃ₐ[ℚ] R := by
  exact
    (Ideal.quotientEquivAlgOfEq ℚ equal_endpoint_presentation_ker.symm).trans <|
      (Ideal.quotientKerEquivRange equal_endpoint_presentation).trans <|
        (Subalgebra.equivOfEq _ _ equal_endpoint_presentation_range_eq_top).trans
          Subalgebra.topEquiv

private theorem evalAt_X_sub_C_isUnit (a r : ℚ) (h : a ≠ r) :
    IsUnit (evalRingHom r (X - C a)) := sorry

/-- The evaluation map on `ℚ[z, 1 / (z - a)]` induced by `z ↦ r`, defined when `a ≠ r`. -/
private noncomputable def awayEval (a r : ℚ) (h : a ≠ r) :
    Localization.Away (X - C a) →ₐ[ℚ] ℚ where
  toRingHom := Localization.awayLift (evalRingHom r) (X - C a) (evalAt_X_sub_C_isUnit a r h)
  commutes' q := by simp

@[simp] private theorem awayEval_algebraMap (a r : ℚ) (h : a ≠ r) (f : Polynomial ℚ) :
    awayEval a r h (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) f) =
      evalRingHom r f :=
  by simp [awayEval, Localization.awayLift]

/-- The ring `R_a = {f ∈ ℚ[z, 1 / (z - a)] | f(0) = f(1)}` from the example, realized as the
equalizer of the two extended evaluation maps as a `ℚ`-subalgebra. -/
noncomputable def equal_endpoint_away (a : ℚ) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    Subalgebra ℚ (Localization.Away (X - C a)) :=
  AlgHom.equalizer (awayEval a 0 h0) (awayEval a 1 h1)

/-- A polynomial in `R` maps into `R_a` under the localization map. -/
-- Proof sketch: the two localized evaluations of the image reduce to the evaluations at `0` and
-- `1` on the original polynomial via `awayEval_algebraMap`, and these agree
-- because `f ∈ R`.
private theorem algebraMap_mem_equal_endpoint_away (a : ℚ) (h0 : a ≠ 0) (h1 : a ≠ 1)
    (f : R) :
    algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) f.1 ∈
      equal_endpoint_away a h0 h1 := by
  change awayEval a 0 h0 (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) f.1) =
      awayEval a 1 h1 (algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) f.1)
  simpa [awayEval_algebraMap, Polynomial.coeff_zero_eq_eval_zero] using
    (mem_equal_endpoint_poly_subring_iff ℚ f.1).mp f.2

/-- The point of `Spec(R)` corresponding to the evaluation ideal `m_r`. -/
def equal_endpoint_eval_point (r : ℚ) : PrimeSpectrum R :=
  comap ((evalRingHom r).comp (equal_endpoint_poly_subring ℚ).subtype) (closedPoint ℚ)

/-- The localized equal-endpoint ring carries its canonical algebra structure over `R`. -/
instance (a : ℚ) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    Algebra R (equal_endpoint_away a h0 h1) :=
  (((algebraMap (Polynomial ℚ) (Localization.Away (X - C a))).comp
        (equal_endpoint_poly_subring ℚ).subtype).codRestrict
      (equal_endpoint_away a h0 h1)
      (algebraMap_mem_equal_endpoint_away a h0 h1)).toAlgebra

/-- The element `z^2 - z` of `R_a`. -/
noncomputable def equal_endpoint_away_quadratic (a : ℚ) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    equal_endpoint_away a h0 h1 :=
  ⟨algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 2 - X),
    algebraMap_mem_equal_endpoint_away a h0 h1 equal_endpoint_quad⟩

private theorem equal_endpoint_cube_minus_linear_mem :
    (X ^ 3 - X : Polynomial ℚ) ∈ R := by
  rw [mem_equal_endpoint_poly_subring_iff]
  norm_num

private def equal_endpoint_cube_minus_linear : R :=
  ⟨X ^ 3 - X, equal_endpoint_cube_minus_linear_mem⟩

/-- The element `z^3 - z` of `R_a`. -/
noncomputable def equal_endpoint_away_cubicMinusLinear
    (a : ℚ) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    equal_endpoint_away a h0 h1 :=
  ⟨algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) (X ^ 3 - X),
    algebraMap_mem_equal_endpoint_away a h0 h1 equal_endpoint_cube_minus_linear⟩

private theorem equal_endpoint_away_linearFractional_mem (a : ℚ)
    (h0 : a ≠ 0) (h1 : a ≠ 1) :
    algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) X +
        algebraMap ℚ (Localization.Away (X - C a)) (a ^ 2 - a) *
          IsLocalization.Away.invSelf (X - C a) ∈
      equal_endpoint_away a h0 h1 := by
  sorry

/-- The element `(a^2 - a)/(z - a) + z` of `R_a`. -/
noncomputable def equal_endpoint_away_linearFractional
    (a : ℚ) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    equal_endpoint_away a h0 h1 :=
  ⟨algebraMap (Polynomial ℚ) (Localization.Away (X - C a)) X +
      algebraMap ℚ (Localization.Away (X - C a)) (a ^ 2 - a) *
        IsLocalization.Away.invSelf (X - C a),
    equal_endpoint_away_linearFractional_mem a h0 h1⟩

/-- Example 10.27.4 (2): for `a ≠ 0, 1`, the ring `R_a` is generated as a `ℚ`-algebra by the three
displayed elements `z^2 - z`, `z^3 - z`, and `(a^2 - a)/(z - a) + z`. -/
theorem equal_endpoint_away_adjoin_eq_top (a : ℚ) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    Algebra.adjoin ℚ
        ({ equal_endpoint_away_quadratic a h0 h1
         , equal_endpoint_away_cubicMinusLinear a h0 h1
         , equal_endpoint_away_linearFractional a h0 h1 } :
          Set (equal_endpoint_away a h0 h1)) =
      ⊤ := by
  sorry

/-- Example 10.27.4 (3): for `a ≠ 0, 1`, the ring `R_a` is a finitely generated `ℚ`-algebra. -/
theorem equal_endpoint_away_finiteType (a : ℚ) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    Algebra.FiniteType ℚ (equal_endpoint_away a h0 h1) := by
  let s : Set (equal_endpoint_away a h0 h1) :=
    { equal_endpoint_away_quadratic a h0 h1
    , equal_endpoint_away_cubicMinusLinear a h0 h1
    , equal_endpoint_away_linearFractional a h0 h1 }
  have hs : s.Finite := by
    simp [s]
  let hft : Algebra.FiniteType ℚ (Algebra.adjoin ℚ s) :=
    Algebra.FiniteType.adjoin_of_finite hs
  let e : Algebra.adjoin ℚ s ≃ₐ[ℚ] equal_endpoint_away a h0 h1 :=
    (Subalgebra.equivOfEq _ _ (equal_endpoint_away_adjoin_eq_top a h0 h1)).trans
      Subalgebra.topEquiv
  exact hft.equiv e

instance (a : ℚ) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    Algebra.FiniteType ℚ (equal_endpoint_away a h0 h1) :=
  equal_endpoint_away_finiteType a h0 h1

/-- Example 10.27.4 (4): for `a ∈ ℚ \ {0, 1/2, 1}`, the inclusion `R ⊆ R_a` induces a
map on prime spectra that is an open embedding, and its image is the complement of the point
corresponding to the evaluation ideal `m_a`. -/
-- Proof sketch: cover `Spec(R_a)` by the two distinguished opens described in the example,
-- identify each restriction with a localization of `R` via Lemma `10.17.5`, and glue the
-- resulting local open embeddings; the image calculation is exactly the statement that only `m_a`
-- is omitted.
theorem equal_endpoint_away_prime_spectrum_openEmbedding_range_eq (a : ℚ)
    (h0 : a ≠ 0) (hhalf : a ≠ (1 / 2 : ℚ)) (h1 : a ≠ 1) :
    IsOpenEmbedding
        (comap (algebraMap R (equal_endpoint_away a h0 h1))) ∧
      Set.range
          (comap (algebraMap R (equal_endpoint_away a h0 h1))) =
        ({equal_endpoint_eval_point a} : Set (PrimeSpectrum R))ᶜ :=
  sorry

/-- The ring `R_a` is not a localization of `R` at any multiplicative subset. -/
-- Proof sketch: as explained in the example, every localization of `R` introduces additional
-- units, while the units of `R_a` are still exactly the nonzero rationals because
-- `a ≠ 0, 1, 1/2`.
theorem equal_endpoint_away_not_isLocalization (a : ℚ)
    (h0 : a ≠ 0) (hhalf : a ≠ (1 / 2 : ℚ)) (h1 : a ≠ 1)
    (S : Submonoid R) :
    ¬ IsLocalization S (equal_endpoint_away a h0 h1) := sorry
