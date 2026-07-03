import Mathlib
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.Integral
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_36_24 (from Chap10) -/
universe u

open scoped nonZeroDivisors
open CategoryTheory

section

variable {R : Type u} [CommRing R]

private abbrev away_xy (x y : R) :=
  Localization.Away (x * y)

private noncomputable def x_over_y (x y : R) : away_xy x y :=
  IsLocalization.mk' (away_xy x y) (x * x)
    (⟨x * y, Submonoid.mem_powers (x * y)⟩ : Submonoid.powers (x * y))

private noncomputable def y_over_x (x y : R) : away_xy x y :=
  IsLocalization.mk' (away_xy x y) (y * y)
    (⟨x * y, Submonoid.mem_powers (x * y)⟩ : Submonoid.powers (x * y))

private noncomputable abbrev x_over_y_subalgebra (x y : R) : Subalgebra R (away_xy x y) :=
  Algebra.adjoin R ({x_over_y x y} : Set (away_xy x y))

private noncomputable abbrev y_over_x_subalgebra (x y : R) : Subalgebra R (away_xy x y) :=
  Algebra.adjoin R ({y_over_x x y} : Set (away_xy x y))

private noncomputable abbrev x_over_y_neg_diagonal (x y : R) :
    R →ₗ[R] x_over_y_subalgebra x y × y_over_x_subalgebra x y :=
  (-Algebra.linearMap R (x_over_y_subalgebra x y)).prod
    (Algebra.linearMap R (y_over_x_subalgebra x y))

private noncomputable abbrev x_over_y_sum_to_adjoin (x y : R) :
    x_over_y_subalgebra x y × y_over_x_subalgebra x y →ₗ[R]
      ((x_over_y_subalgebra x y ⊔ y_over_x_subalgebra x y : Subalgebra R (away_xy x y))) :=
  LinearMap.coprod
    ((Subalgebra.inclusion le_sup_left).toLinearMap)
    ((Subalgebra.inclusion le_sup_right).toLinearMap)

private theorem x_over_y_neg_diagonal_range_le_ker (x y : R) :
    LinearMap.range (x_over_y_neg_diagonal x y) ≤
      LinearMap.ker (x_over_y_sum_to_adjoin x y) := by
  rw [LinearMap.range_le_ker_iff]
  ext
  simp [x_over_y_neg_diagonal, x_over_y_sum_to_adjoin]

/-- Helper for Lemma 10.36.24: the numerator in the product `(x / y) * (y / x)` is exactly
`(xy)^2`. -/
private theorem x_square_mul_y_square_eq_xy_square (x y : R) :
    ((x * x) * (y * y) : R) = (x * y) * (x * y) := by
  -- Reassociate and commute the factors so both sides are the same product.
  ring

/-- Helper for Lemma 10.36.24: in the common localization `R_{xy}`, the fractions `x / y` and
`y / x` multiply to `1`. -/
private theorem x_over_y_mul_y_over_x (x y : R) :
    x_over_y x y * y_over_x x y = 1 := by
  let s : Submonoid.powers (x * y) := ⟨x * y, Submonoid.mem_powers (x * y)⟩
  -- Rewrite the product as a single localization fraction whose numerator and denominator agree.
  rw [x_over_y, y_over_x, ← IsLocalization.mk'_mul]
  change IsLocalization.mk' (away_xy x y) ((x * x) * (y * y)) (s * s) = 1
  -- Commute the factors so that the fraction is visibly of the form `u / u`.
  rw [x_square_mul_y_square_eq_xy_square x y]
  simpa [s, mul_assoc, mul_left_comm, mul_comm] using
    (IsLocalization.mk'_self' (S := away_xy x y) (M := Submonoid.powers (x * y)) (x := s * s))

/-- Helper for Lemma 10.36.24: the reverse product `(y / x) * (x / y)` also equals `1`. -/
private theorem y_over_x_mul_x_over_y (x y : R) :
    y_over_x x y * x_over_y x y = 1 := by
  -- Commute the factors and reuse the basic cancellation identity.
  simpa [mul_comm] using x_over_y_mul_y_over_x x y

/-- Helper for Lemma 10.36.24: localizing away `xy` is injective when both `x` and `y` are
nonzerodivisors. -/
private theorem away_xy_algebraMap_injective (x y : R) (hx : x ∈ R⁰) (hy : y ∈ R⁰) :
    Function.Injective (algebraMap R (away_xy x y)) := by
  have hxy : x * y ∈ R⁰ := mul_mem_nonZeroDivisors.mpr ⟨hx, hy⟩
  -- Every power of `xy` is a nonzerodivisor, so the localization map is injective.
  exact IsLocalization.injective (away_xy x y)
    (Submonoid.powers_le.mpr hxy)

/-- Helper for Lemma 10.36.24: the left map `R → R[x/y] ⊕ R[y/x]` is injective once localization
away `xy` is injective. -/
private theorem x_over_y_neg_diagonal_injective (x y : R) (hx : x ∈ R⁰) (hy : y ∈ R⁰) :
    Function.Injective (x_over_y_neg_diagonal x y) := by
  intro r s hrs
  have hmap : algebraMap R (away_xy x y) r = algebraMap R (away_xy x y) s := by
    -- The second component is the plain algebra map into `R[y/x]`.
    simpa [x_over_y_neg_diagonal] using congrArg Subtype.val (congrArg Prod.snd hrs)
  exact away_xy_algebraMap_injective x y hx hy hmap

/-- Helper for Lemma 10.36.24: every element coming from `R[x/y]` already lies in the range of the
sum map into `R[x/y, y/x]`. -/
private theorem left_mem_range_x_over_y_sum_to_adjoin (x y : R) (a : x_over_y_subalgebra x y) :
    (Subalgebra.inclusion le_sup_left a) ∈ LinearMap.range (x_over_y_sum_to_adjoin x y) := by
  -- Use the obvious preimage `(a, 0)`.
  refine ⟨(a, 0), ?_⟩
  simp [x_over_y_sum_to_adjoin]

/-- Helper for Lemma 10.36.24: every element coming from `R[y/x]` already lies in the range of the
sum map into `R[x/y, y/x]`. -/
private theorem right_mem_range_x_over_y_sum_to_adjoin (x y : R) (b : y_over_x_subalgebra x y) :
    (Subalgebra.inclusion le_sup_right b) ∈ LinearMap.range (x_over_y_sum_to_adjoin x y) := by
  -- Use the obvious preimage `(0, b)`.
  refine ⟨(0, b), ?_⟩
  simp [x_over_y_sum_to_adjoin]

/-- Helper for Lemma 10.36.24: the bounded-power generating set contains the powers of `x / y`
up to degree `N` and the powers of `y / x` up to degree `N`. -/
private def bounded_power_set (x y : R) (N : ℕ) : Set (away_xy x y) :=
  Set.range (fun n : Fin (N + 1) ↦ x_over_y x y ^ (n : ℕ)) ∪
    Set.range (fun n : Fin (N + 1) ↦ y_over_x x y ^ (n : ℕ))

/-- Helper for Lemma 10.36.24: the finite `R`-submodule generated by the bounded powers of
`x / y` and `y / x`. -/
private def bounded_power_submodule (x y : R) (N : ℕ) : Submodule R (away_xy x y) :=
  Submodule.span R (bounded_power_set x y N)

/-- Helper for Lemma 10.36.24: every bounded power of `x / y` lies in the bounded-power
submodule. -/
private theorem x_over_y_pow_mem_bounded_power_submodule (x y : R) {N i : ℕ} (hi : i ≤ N) :
    x_over_y x y ^ i ∈ bounded_power_submodule x y N := by
  -- Insert the required power directly among the spanning generators.
  refine Submodule.subset_span ?_
  exact Or.inl ⟨⟨i, Nat.lt_succ_iff.mpr hi⟩, rfl⟩

/-- Helper for Lemma 10.36.24: every bounded power of `y / x` lies in the bounded-power
submodule. -/
private theorem y_over_x_pow_mem_bounded_power_submodule (x y : R) {N i : ℕ} (hi : i ≤ N) :
    y_over_x x y ^ i ∈ bounded_power_submodule x y N := by
  -- Insert the required power directly among the spanning generators.
  refine Submodule.subset_span ?_
  exact Or.inr ⟨⟨i, Nat.lt_succ_iff.mpr hi⟩, rfl⟩

/-- Helper for Lemma 10.36.24: the bounded-power submodule is finitely generated. -/
private theorem bounded_power_submodule_fg (x y : R) (N : ℕ) :
    (bounded_power_submodule x y N).FG := by
  -- The spanning set is the union of two finite ranges.
  refine Submodule.fg_span ?_
  exact (Set.finite_range (fun n : Fin (N + 1) ↦ x_over_y x y ^ (n : ℕ))).union
    (Set.finite_range (fun n : Fin (N + 1) ↦ y_over_x x y ^ (n : ℕ)))

/-- Helper for Lemma 10.36.24: the bounded-power submodule contains `1`. -/
private theorem one_mem_bounded_power_submodule (x y : R) (N : ℕ) :
    (1 : away_xy x y) ∈ bounded_power_submodule x y N := by
  -- The zeroth power of `x / y` is one of the generators.
  simpa using x_over_y_pow_mem_bounded_power_submodule x y (N := N) (i := 0) (Nat.zero_le _)

/-- Helper for Lemma 10.36.24: when the exponent of `y / x` is at most the exponent of `x / y`,
the mixed monomial collapses to a pure power of `x / y`. -/
private theorem x_over_y_pow_mul_y_over_x_pow_eq (x y : R) {i j : ℕ} (h : j ≤ i) :
    x_over_y x y ^ i * y_over_x x y ^ j = x_over_y x y ^ (i - j) := by
  -- Cancel `j` copies of `(x / y) * (y / x) = 1`.
  calc
    x_over_y x y ^ i * y_over_x x y ^ j
        = x_over_y x y ^ ((i - j) + j) * y_over_x x y ^ j := by
            rw [Nat.sub_add_cancel h]
    _ = x_over_y x y ^ (i - j) * (x_over_y x y ^ j * y_over_x x y ^ j) := by
          rw [pow_add, mul_assoc]
    _ = x_over_y x y ^ (i - j) * (x_over_y x y * y_over_x x y) ^ j := by
          rw [← mul_pow]
    _ = x_over_y x y ^ (i - j) := by
          simp [x_over_y_mul_y_over_x]

/-- Helper for Lemma 10.36.24: when the exponent of `x / y` is at most the exponent of `y / x`,
the mixed monomial collapses to a pure power of `y / x`. -/
private theorem x_over_y_pow_mul_y_over_x_pow_eq' (x y : R) {i j : ℕ} (h : i ≤ j) :
    x_over_y x y ^ i * y_over_x x y ^ j = y_over_x x y ^ (j - i) := by
  -- Rewrite `j` as `i + (j - i)`, then cancel the common factor
  -- `(x / y)^i * (y / x)^i = ((x / y) * (y / x))^i`.
  calc
    x_over_y x y ^ i * y_over_x x y ^ j
        = x_over_y x y ^ i * y_over_x x y ^ (i + (j - i)) := by
            rw [Nat.add_sub_of_le h]
    _ = x_over_y x y ^ i * (y_over_x x y ^ i * y_over_x x y ^ (j - i)) := by
          rw [pow_add]
    _ = (x_over_y x y ^ i * y_over_x x y ^ i) * y_over_x x y ^ (j - i) := by
          rw [mul_assoc]
    _ = ((x_over_y x y * y_over_x x y) ^ i) * y_over_x x y ^ (j - i) := by
          rw [← mul_pow]
    _ = y_over_x x y ^ (j - i) := by
          simp [x_over_y_mul_y_over_x]

/-- Helper for Lemma 10.36.24: every mixed bounded monomial lies in the bounded-power submodule. -/
private theorem mixed_power_mem_bounded_power_submodule (x y : R) {N i j : ℕ}
    (hi : i ≤ N) (hj : j ≤ N) :
    x_over_y x y ^ i * y_over_x x y ^ j ∈ bounded_power_submodule x y N := by
  -- Reduce the mixed monomial to a bounded pure power by canceling the overlap.
  by_cases hji : j ≤ i
  · rw [x_over_y_pow_mul_y_over_x_pow_eq x y hji]
    exact x_over_y_pow_mem_bounded_power_submodule x y (N := N)
      (i := i - j) (le_trans (Nat.sub_le _ _) hi)
  · have hij : i ≤ j := Nat.le_of_not_ge hji
    rw [x_over_y_pow_mul_y_over_x_pow_eq' x y hij]
    exact y_over_x_pow_mem_bounded_power_submodule x y (N := N)
      (i := j - i) (le_trans (Nat.sub_le _ _) hj)

/-- Helper for Lemma 10.36.24: a polynomial in `x / y`, multiplied by a bounded power of `y / x`,
still lands in the bounded-power submodule. -/
private theorem aeval_x_over_y_mul_y_over_x_pow_mem_bounded_power_submodule (x y : R)
    {N j : ℕ} (hj : j ≤ N) (p : Polynomial R) (hp : p.natDegree ≤ N) :
    Polynomial.aeval (x_over_y x y) p * y_over_x x y ^ j ∈ bounded_power_submodule x y N := by
  -- Expand the polynomial evaluation into a bounded finite sum indexed by powers of `x / y`.
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul]
  refine Submodule.sum_mem _ ?_
  intro i hi
  -- Each summand is a scalar multiple of a mixed monomial, so the bounded-power lemma applies.
  have hi' : i ≤ N := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hp
  -- Record the explicit coefficient so the summand matches the `aeval` expansion exactly.
  simpa [Algebra.smul_def, smul_mul_assoc, mul_assoc] using
    (Submodule.smul_mem (bounded_power_submodule x y N) (p.coeff i)
      (mixed_power_mem_bounded_power_submodule x y (N := N) (i := i) (j := j) hi' hj))

/-- Helper for Lemma 10.36.24: a polynomial in `y / x`, multiplied by a bounded power of `x / y`,
still lands in the bounded-power submodule. -/
private theorem aeval_y_over_x_mul_x_over_y_pow_mem_bounded_power_submodule (x y : R)
    {N i : ℕ} (hi : i ≤ N) (p : Polynomial R) (hp : p.natDegree ≤ N) :
    Polynomial.aeval (y_over_x x y) p * x_over_y x y ^ i ∈ bounded_power_submodule x y N := by
  -- Expand the polynomial evaluation into a bounded finite sum indexed by powers of `y / x`.
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul]
  refine Submodule.sum_mem _ ?_
  intro j hj
  -- Commute the mixed product to match the canonical `x / y` then `y / x` order.
  have hj' : j ≤ N := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hp
  -- Again make the coefficient explicit before commuting the mixed monomial.
  simpa [Algebra.smul_def, smul_mul_assoc, mul_assoc, mul_left_comm, mul_comm] using
    (Submodule.smul_mem (bounded_power_submodule x y N) (p.coeff j)
      (mixed_power_mem_bounded_power_submodule x y (N := N) (i := i) (j := j) hi hj'))

/-- Helper for Lemma 10.36.24: membership in `R[x / y]` gives a polynomial expression in the
generator `x / y`. -/
private theorem exists_aeval_x_over_y_of_mem (x y : R) {a : away_xy x y}
    (ha : a ∈ x_over_y_subalgebra x y) :
    ∃ p : Polynomial R, Polynomial.aeval (x_over_y x y) p = a := by
  -- Unpack the singleton adjoin via the polynomial evaluation description.
  simpa [x_over_y_subalgebra] using Algebra.adjoin_mem_exists_aeval R (x_over_y x y) ha

/-- Helper for Lemma 10.36.24: membership in `R[y / x]` gives a polynomial expression in the
generator `y / x`. -/
private theorem exists_aeval_y_over_x_of_mem (x y : R) {a : away_xy x y}
    (ha : a ∈ y_over_x_subalgebra x y) :
    ∃ p : Polynomial R, Polynomial.aeval (y_over_x x y) p = a := by
  -- Unpack the singleton adjoin via the polynomial evaluation description.
  simpa [y_over_x_subalgebra] using Algebra.adjoin_mem_exists_aeval R (y_over_x x y) ha

/-- Helper for Lemma 10.36.24: the canonical comparison map `R_x → R_{xy}`. -/
private noncomputable def away_xy_from_away_x (x y : R) :
    Localization.Away x →+* away_xy x y :=
  IsLocalization.Away.awayToAwayRight (S := Localization.Away x) (P := away_xy x y) x y

/-- Helper for Lemma 10.36.24: the comparison map `R_x → R_{xy}` respects the original
coefficients from `R`. -/
private theorem away_xy_from_away_x_commutes (x y r : R) :
    away_xy_from_away_x x y (algebraMap R (Localization.Away x) r) =
      algebraMap R (away_xy x y) r := by
  -- The comparison map agrees with the ambient localization map on coefficients.
  simpa [away_xy_from_away_x] using
    (IsLocalization.Away.awayToAwayRight_eq
      (S := Localization.Away x) (P := away_xy x y) (x := x) (y := y) r)

/-- Helper for Lemma 10.36.24: the comparison map `R_x → R_{xy}` as an `R`-algebra hom. -/
private noncomputable def away_xy_from_away_x_algHom (x y : R) :
    Localization.Away x →ₐ[R] away_xy x y :=
  ⟨away_xy_from_away_x x y, away_xy_from_away_x_commutes x y⟩

/-- Helper for Lemma 10.36.24: the canonical comparison map `R_y → R_{xy}`. -/
private noncomputable def away_xy_from_away_y (x y : R) :
    Localization.Away y →+* away_xy x y :=
  IsLocalization.Away.awayToAwayLeft (S := Localization.Away y) (P := away_xy x y) y x

/-- Helper for Lemma 10.36.24: the comparison map `R_y → R_{xy}` respects the original
coefficients from `R`. -/
private theorem away_xy_from_away_y_commutes (x y r : R) :
    away_xy_from_away_y x y (algebraMap R (Localization.Away y) r) =
      algebraMap R (away_xy x y) r := by
  -- The comparison map agrees with the ambient localization map on coefficients.
  simpa [away_xy_from_away_y] using
    (IsLocalization.Away.awayToAwayLeft_eq
      (S := Localization.Away y) (P := away_xy x y) (x := y) (y := x) r)

/-- Helper for Lemma 10.36.24: the comparison map `R_y → R_{xy}` as an `R`-algebra hom. -/
private noncomputable def away_xy_from_away_y_algHom (x y : R) :
    Localization.Away y →ₐ[R] away_xy x y :=
  ⟨away_xy_from_away_y x y, away_xy_from_away_y_commutes x y⟩

/-- Helper for Lemma 10.36.24: in `R_x`, the source generator `y / x` satisfies the expected
cross-multiplication relation with `x`. -/
private theorem source_y_over_x_mul_algebraMap_x (x y : R) :
    (IsLocalization.mk' (Localization.Away x) y
      (⟨x, Submonoid.mem_powers x⟩ : Submonoid.powers x)) *
      algebraMap R (Localization.Away x) x = algebraMap R (Localization.Away x) y := by
  -- This is the defining localization relation for the fraction `y / x`.
  simpa using
    (IsLocalization.mk'_eq_iff_eq_mul
      (S := Localization.Away x)
      (x := y)
      (y := (⟨x, Submonoid.mem_powers x⟩ : Submonoid.powers x))
      (z := IsLocalization.mk' (Localization.Away x) y
        (⟨x, Submonoid.mem_powers x⟩ : Submonoid.powers x))).1 rfl

/-- Helper for Lemma 10.36.24: in `R_{xy}`, the target generator `y / x` satisfies the same
cross-multiplication relation with `x`. -/
private theorem target_y_over_x_mul_algebraMap_x (x y : R) :
    y_over_x x y * algebraMap R (away_xy x y) x = algebraMap R (away_xy x y) y := by
  -- Rewrite `y / x` as the explicit localization fraction and clear the denominator.
  rw [mul_comm, y_over_x, IsLocalization.mul_mk'_eq_mk'_of_mul]
  apply (IsLocalization.mk'_eq_iff_eq_mul).2
  simp [mul_left_comm]

/-- Helper for Lemma 10.36.24: the comparison map `R_x → R_{xy}` sends the source generator
`y / x` to the target generator `y / x`. -/
private theorem awayToAwayRight_mk_y_eq (x y : R) :
    away_xy_from_away_x x y
      (IsLocalization.mk' (Localization.Away x) y
        (⟨x, Submonoid.mem_powers x⟩ : Submonoid.powers x)) = y_over_x x y := by
  let t : Localization.Away x :=
    IsLocalization.mk' (Localization.Away x) y
      (⟨x, Submonoid.mem_powers x⟩ : Submonoid.powers x)
  have hmap :
      away_xy_from_away_x x y t * algebraMap R (away_xy x y) x =
        algebraMap R (away_xy x y) y := by
    have hxcoeff :
        away_xy_from_away_x x y ((algebraMap R (Localization.Away x)) x) =
          algebraMap R (away_xy x y) x :=
      away_xy_from_away_x_commutes x y x
    -- Map the source cross-multiplication relation into `R_{xy}`.
    calc
      away_xy_from_away_x x y t * algebraMap R (away_xy x y) x
          = away_xy_from_away_x x y (t * algebraMap R (Localization.Away x) x) := by
              rw [map_mul]
              rw [hxcoeff]
      _ = algebraMap R (away_xy x y) y := by
            rw [source_y_over_x_mul_algebraMap_x]
            exact away_xy_from_away_x_commutes x y y
  have hxunit : IsUnit (algebraMap R (away_xy x y) x) :=
    IsLocalization.Away.isUnit_of_dvd (R := R) (S := away_xy x y) (x := x * y) (r := x)
      (dvd_mul_right x y)
  -- Cancel the unit `x` in `R_{xy}` to identify the two fractions.
  exact (IsUnit.mul_left_inj hxunit).1 <|
    hmap.trans (target_y_over_x_mul_algebraMap_x x y).symm

/-- Helper for Lemma 10.36.24: the comparison map `R_x → R_{xy}` carries a polynomial witness in
the source generator `y / x` to the corresponding polynomial in the target generator. -/
private theorem awayToAwayRight_aeval_y_over_x_eq (x y : R) (q : Polynomial R) :
    away_xy_from_away_x x y
      (Polynomial.aeval
        (IsLocalization.mk' (Localization.Away x) y
          (⟨x, Submonoid.mem_powers x⟩ : Submonoid.powers x)) q)
      = Polynomial.aeval (y_over_x x y) q := by
  let t : Localization.Away x :=
    IsLocalization.mk' (Localization.Away x) y
      (⟨x, Submonoid.mem_powers x⟩ : Submonoid.powers x)
  have ht : (away_xy_from_away_x_algHom x y) t = y_over_x x y := by
    -- First identify the image of the source generator itself.
    simpa [t] using awayToAwayRight_mk_y_eq x y
  -- Then functoriality of `aeval` transports the whole polynomial witness.
  calc
    (away_xy_from_away_x_algHom x y) (Polynomial.aeval t q)
        = Polynomial.aeval ((away_xy_from_away_x_algHom x y) t) q := by
            simpa using
              ((Polynomial.aeval_algHom_apply (away_xy_from_away_x_algHom x y) t q)).symm
    _ = Polynomial.aeval (y_over_x x y) q := by rw [ht]

/-- Helper for Lemma 10.36.24: in `R_y`, the source generator `x / y` satisfies the expected
cross-multiplication relation with `y`. -/
private theorem source_x_over_y_mul_algebraMap_y (x y : R) :
    (IsLocalization.mk' (Localization.Away y) x
      (⟨y, Submonoid.mem_powers y⟩ : Submonoid.powers y)) *
      algebraMap R (Localization.Away y) y = algebraMap R (Localization.Away y) x := by
  -- This is the defining localization relation for the fraction `x / y`.
  simpa using
    (IsLocalization.mk'_eq_iff_eq_mul
      (S := Localization.Away y)
      (x := x)
      (y := (⟨y, Submonoid.mem_powers y⟩ : Submonoid.powers y))
      (z := IsLocalization.mk' (Localization.Away y) x
        (⟨y, Submonoid.mem_powers y⟩ : Submonoid.powers y))).1 rfl

/-- Helper for Lemma 10.36.24: in `R_{xy}`, the target generator `x / y` satisfies the same
cross-multiplication relation with `y`. -/
private theorem target_x_over_y_mul_algebraMap_y (x y : R) :
    x_over_y x y * algebraMap R (away_xy x y) y = algebraMap R (away_xy x y) x := by
  -- Rewrite `x / y` as the explicit localization fraction and clear the denominator.
  rw [mul_comm, x_over_y, IsLocalization.mul_mk'_eq_mk'_of_mul]
  apply (IsLocalization.mk'_eq_iff_eq_mul).2
  simp [map_mul, mul_left_comm, mul_comm]

/-- Helper for Lemma 10.36.24: the comparison map `R_y → R_{xy}` sends the source generator
`x / y` to the target generator `x / y`. -/
private theorem awayToAwayLeft_mk_x_eq (x y : R) :
    away_xy_from_away_y x y
      (IsLocalization.mk' (Localization.Away y) x
        (⟨y, Submonoid.mem_powers y⟩ : Submonoid.powers y)) = x_over_y x y := by
  let t : Localization.Away y :=
    IsLocalization.mk' (Localization.Away y) x
      (⟨y, Submonoid.mem_powers y⟩ : Submonoid.powers y)
  have hmap :
      away_xy_from_away_y x y t * algebraMap R (away_xy x y) y =
        algebraMap R (away_xy x y) x := by
    have hycoeff :
        away_xy_from_away_y x y ((algebraMap R (Localization.Away y)) y) =
          algebraMap R (away_xy x y) y :=
      away_xy_from_away_y_commutes x y y
    -- Map the source cross-multiplication relation into `R_{xy}`.
    calc
      away_xy_from_away_y x y t * algebraMap R (away_xy x y) y
          = away_xy_from_away_y x y (t * algebraMap R (Localization.Away y) y) := by
              rw [map_mul]
              rw [hycoeff]
      _ = algebraMap R (away_xy x y) x := by
            rw [source_x_over_y_mul_algebraMap_y]
            exact away_xy_from_away_y_commutes x y x
  have hy_dvd_xy : y ∣ x * y := by
    -- The element `y` divides `xy` with quotient `x`.
    refine ⟨x, ?_⟩
    simp [mul_comm]
  have hyunit : IsUnit (algebraMap R (away_xy x y) y) :=
    IsLocalization.Away.isUnit_of_dvd (R := R) (S := away_xy x y) (x := x * y) (r := y) hy_dvd_xy
  -- Cancel the unit `y` in `R_{xy}` to identify the two fractions.
  rw [← IsUnit.mul_left_inj hyunit]
  exact hmap.trans (target_x_over_y_mul_algebraMap_y x y).symm

/-- Helper for Lemma 10.36.24: the comparison map `R_y → R_{xy}` carries a polynomial witness in
the source generator `x / y` to the corresponding polynomial in the target generator. -/
private theorem awayToAwayLeft_aeval_x_over_y_eq (x y : R) (p : Polynomial R) :
    away_xy_from_away_y x y
      (Polynomial.aeval
        (IsLocalization.mk' (Localization.Away y) x
          (⟨y, Submonoid.mem_powers y⟩ : Submonoid.powers y)) p)
      = Polynomial.aeval (x_over_y x y) p := by
  let t : Localization.Away y :=
    IsLocalization.mk' (Localization.Away y) x
      (⟨y, Submonoid.mem_powers y⟩ : Submonoid.powers y)
  have ht : (away_xy_from_away_y_algHom x y) t = x_over_y x y := by
    -- First identify the image of the source generator itself.
    simpa [t] using awayToAwayLeft_mk_x_eq x y
  -- Then functoriality of `aeval` transports the whole polynomial witness.
  calc
    (away_xy_from_away_y_algHom x y) (Polynomial.aeval t p)
        = Polynomial.aeval ((away_xy_from_away_y_algHom x y) t) p := by
            simpa using
              ((Polynomial.aeval_algHom_apply (away_xy_from_away_y_algHom x y) t p)).symm
    _ = Polynomial.aeval (x_over_y x y) p := by rw [ht]

/-- Helper for Lemma 10.36.24: every element of `R[y / x]` comes from a concrete element of
`R_x`. -/
private theorem exists_preimage_in_away_x_of_mem_y_over_x_subalgebra (x y : R) {a : away_xy x y}
    (ha : a ∈ y_over_x_subalgebra x y) :
    ∃ b : Localization.Away x, away_xy_from_away_x x y b = a := by
  obtain ⟨q, hq⟩ := exists_aeval_y_over_x_of_mem x y ha
  refine ⟨Polynomial.aeval
    (IsLocalization.mk' (Localization.Away x) y
      (⟨x, Submonoid.mem_powers x⟩ : Submonoid.powers x)) q, ?_⟩
  -- Transport the polynomial witness from `R_x` into the common localization.
  simpa [hq] using awayToAwayRight_aeval_y_over_x_eq x y q

/-- Helper for Lemma 10.36.24: every element of `R[x / y]` comes from a concrete element of
`R_y`. -/
private theorem exists_preimage_in_away_y_of_mem_x_over_y_subalgebra (x y : R) {a : away_xy x y}
    (ha : a ∈ x_over_y_subalgebra x y) :
    ∃ b : Localization.Away y, away_xy_from_away_y x y b = a := by
  obtain ⟨p, hp⟩ := exists_aeval_x_over_y_of_mem x y ha
  refine ⟨Polynomial.aeval
    (IsLocalization.mk' (Localization.Away y) x
      (⟨y, Submonoid.mem_powers y⟩ : Submonoid.powers y)) p, ?_⟩
  -- Transport the polynomial witness from `R_y` into the common localization.
  simpa [hp] using awayToAwayLeft_aeval_x_over_y_eq x y p

/-- Helper for Lemma 10.36.24: the comparison map `R_x → R_{xy}` is injective because it is
already injective on coefficients from `R`. -/
private theorem away_xy_from_away_x_injective (x y : R) (hx : x ∈ R⁰) (hy : y ∈ R⁰) :
    Function.Injective (away_xy_from_away_x x y) := by
  -- The localization source is generated by coefficients from `R`, so it suffices to test those.
  refine IsLocalization.injective_of_map_algebraMap_zero
    (M := Submonoid.powers x) (S := Localization.Away x) (f := away_xy_from_away_x x y) ?_
  intro r hr
  have hr' : algebraMap R (away_xy x y) r = 0 := by
    -- On coefficients, the comparison map agrees with the ambient localization map.
    calc
      algebraMap R (away_xy x y) r
          = away_xy_from_away_x x y (algebraMap R (Localization.Away x) r) := by
              symm
              simpa [away_xy_from_away_x] using
                (IsLocalization.Away.awayToAwayRight_eq
                  (S := Localization.Away x) (P := away_xy x y) (x := x) (y := y) r)
      _ = 0 := hr
  have hzero_image : algebraMap R (away_xy x y) r = algebraMap R (away_xy x y) 0 := by
    simpa using hr'
  have hzero : r = 0 := away_xy_algebraMap_injective x y hx hy hzero_image
  simpa [hzero]

/-- Helper for Lemma 10.36.24: the comparison map `R_y → R_{xy}` is injective for the symmetric
reason. -/
private theorem away_xy_from_away_y_injective (x y : R) (hx : x ∈ R⁰) (hy : y ∈ R⁰) :
    Function.Injective (away_xy_from_away_y x y) := by
  -- Again reduce injectivity to the coefficient ring `R`.
  refine IsLocalization.injective_of_map_algebraMap_zero
    (M := Submonoid.powers y) (S := Localization.Away y) (f := away_xy_from_away_y x y) ?_
  intro r hr
  have hr' : algebraMap R (away_xy x y) r = 0 := by
    -- On coefficients, the comparison map agrees with the ambient localization map.
    calc
      algebraMap R (away_xy x y) r
          = away_xy_from_away_y x y (algebraMap R (Localization.Away y) r) := by
              symm
              simpa [away_xy_from_away_y] using
                (IsLocalization.Away.awayToAwayLeft_eq
                  (S := Localization.Away y) (P := away_xy x y) (x := y) (y := x) r)
      _ = 0 := hr
  have hzero_image : algebraMap R (away_xy x y) r = algebraMap R (away_xy x y) 0 := by
    simpa using hr'
  have hzero : r = 0 := away_xy_algebraMap_injective x y hx hy hzero_image
  simpa [hzero]

/-- Helper for Lemma 10.36.24: an element in the intersection `R[x / y] ∩ R[y / x]` stabilizes a
finite bounded-power submodule of `R_{xy}`. -/
private theorem intersection_element_stabilizes_bounded_power_submodule (x y : R)
    {a : away_xy x y} (ha₁ : a ∈ x_over_y_subalgebra x y) (ha₂ : a ∈ y_over_x_subalgebra x y) :
    ∃ M : Submodule R (away_xy x y), M.FG ∧ (1 : away_xy x y) ∈ M ∧ ∀ m ∈ M, a * m ∈ M := by
  obtain ⟨p, hp_eval⟩ := exists_aeval_x_over_y_of_mem x y ha₁
  obtain ⟨q, hq_eval⟩ := exists_aeval_y_over_x_of_mem x y ha₂
  let N := max p.natDegree q.natDegree
  refine ⟨bounded_power_submodule x y N, bounded_power_submodule_fg x y N,
    one_mem_bounded_power_submodule x y N, ?_⟩
  intro m hm
  -- The source proof uses the span of bounded pure powers, so it suffices to check the generators.
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hm
  · intro z hz
    rcases hz with hz | hz
    · rcases hz with ⟨i, rfl⟩
      -- On an `x / y`-power generator, rewrite `a` using the `R[y / x]` polynomial witness.
      have hi : (i : ℕ) ≤ N := Nat.lt_succ_iff.mp i.2
      have hqN : q.natDegree ≤ N := le_max_right _ _
      simpa [N, hq_eval] using
        aeval_y_over_x_mul_x_over_y_pow_mem_bounded_power_submodule x y hi q hqN
    · rcases hz with ⟨j, rfl⟩
      -- On a `y / x`-power generator, rewrite `a` using the `R[x / y]` polynomial witness.
      have hj : (j : ℕ) ≤ N := Nat.lt_succ_iff.mp j.2
      have hpN : p.natDegree ≤ N := le_max_left _ _
      simpa [N, hp_eval] using
        aeval_x_over_y_mul_y_over_x_pow_mem_bounded_power_submodule x y hj p hpN
  · -- The stable-span property is vacuous on zero.
    simpa using
      (Submodule.zero_mem (bounded_power_submodule x y N) :
        (0 : away_xy x y) ∈ bounded_power_submodule x y N)
  · intro u v hu hv hu_mem hv_mem
    -- Stability is preserved under addition because left multiplication distributes.
    simpa [mul_add] using Submodule.add_mem (bounded_power_submodule x y N) hu_mem hv_mem
  · intro r z hz hz_mem
    -- Stability is preserved under scalar multiplication because `R_{xy}` is a commutative `R`-algebra.
    simpa [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm] using
      Submodule.smul_mem (bounded_power_submodule x y N) r hz_mem

/-- Helper for Lemma 10.36.24: an element lying in both singleton adjoins is integral over `R`. -/
private theorem isIntegral_of_mem_x_over_y_inter (x y : R) {a : away_xy x y}
    (ha₁ : a ∈ x_over_y_subalgebra x y) (ha₂ : a ∈ y_over_x_subalgebra x y) :
    IsIntegral R a := by
  -- Apply Lemma 10.36.2 to the finite stable submodule furnished by the textbook argument.
  exact isIntegral_of_exists_fg_submodule_of_one_mem_of_mul_mem
    (intersection_element_stabilizes_bounded_power_submodule x y ha₁ ha₂)

/-- Helper for Lemma 10.36.24: if an element lies in both singleton adjoins, then under the
integrally closed hypothesis it already comes from `R`. -/
private theorem algebraMap_eq_of_mem_x_over_y_inter (x y : R) (hx : x ∈ R⁰) (hy : y ∈ R⁰)
    (hclosed : IsIntegrallyClosedIn R (Localization.Away x) ∨
      IsIntegrallyClosedIn R (Localization.Away y))
    {a : away_xy x y} (ha₁ : a ∈ x_over_y_subalgebra x y) (ha₂ : a ∈ y_over_x_subalgebra x y) :
    ∃ r : R, algebraMap R (away_xy x y) r = a := by
  have ha_integral : IsIntegral R a := isIntegral_of_mem_x_over_y_inter x y ha₁ ha₂
  rcases hclosed with hclosed_x | hclosed_y
  · obtain ⟨b, hb⟩ := exists_preimage_in_away_x_of_mem_y_over_x_subalgebra x y ha₂
    have hb_integral_image : IsIntegral R ((away_xy_from_away_x_algHom x y) b) := by
      -- Replace `a` by the chosen `R_x` preimage in the integral statement.
      simpa [away_xy_from_away_x_algHom, hb] using ha_integral
    have hb_integral : IsIntegral R b :=
      (isIntegral_algHom_iff (away_xy_from_away_x_algHom x y)
        (away_xy_from_away_x_injective x y hx hy)).mp hb_integral_image
    letI : IsIntegrallyClosedIn R (Localization.Away x) := hclosed_x
    obtain ⟨r, hr⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hb_integral
    refine ⟨r, ?_⟩
    -- Map the one-sided equality forward to recover the original element of `R_{xy}`.
    calc
      algebraMap R (away_xy x y) r
          = away_xy_from_away_x x y (algebraMap R (Localization.Away x) r) := by
              symm
              simpa [away_xy_from_away_x] using
                (IsLocalization.Away.awayToAwayRight_eq
                  (S := Localization.Away x) (P := away_xy x y) (x := x) (y := y) r)
      _ = away_xy_from_away_x x y b := by rw [hr]
      _ = a := hb
  · obtain ⟨b, hb⟩ := exists_preimage_in_away_y_of_mem_x_over_y_subalgebra x y ha₁
    have hb_integral_image : IsIntegral R ((away_xy_from_away_y_algHom x y) b) := by
      -- Replace `a` by the chosen `R_y` preimage in the integral statement.
      simpa [away_xy_from_away_y_algHom, hb] using ha_integral
    have hb_integral : IsIntegral R b :=
      (isIntegral_algHom_iff (away_xy_from_away_y_algHom x y)
        (away_xy_from_away_y_injective x y hx hy)).mp hb_integral_image
    letI : IsIntegrallyClosedIn R (Localization.Away y) := hclosed_y
    obtain ⟨r, hr⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hb_integral
    refine ⟨r, ?_⟩
    -- Map the one-sided equality forward to recover the original element of `R_{xy}`.
    calc
      algebraMap R (away_xy x y) r
          = away_xy_from_away_y x y (algebraMap R (Localization.Away y) r) := by
              symm
              simpa [away_xy_from_away_y] using
                (IsLocalization.Away.awayToAwayLeft_eq
                  (S := Localization.Away y) (P := away_xy x y) (x := y) (y := x) r)
      _ = away_xy_from_away_y x y b := by rw [hr]
      _ = a := hb

/-- Helper for Lemma 10.36.24: multiplying an element of `R[x / y]` by an element of `R[y / x]`
lands in the additive sum of the two singleton-generated subalgebras. -/
private theorem mixed_product_mem_sum_singleton_adjoins (x y : R) {a b : away_xy x y}
    (ha : a ∈ x_over_y_subalgebra x y) (hb : b ∈ y_over_x_subalgebra x y) :
    a * b ∈ (x_over_y_subalgebra x y).toSubmodule ⊔
      (y_over_x_subalgebra x y).toSubmodule := by
  let U : Submodule R (away_xy x y) :=
    (x_over_y_subalgebra x y).toSubmodule ⊔ (y_over_x_subalgebra x y).toSubmodule
  have hxgen_mem : x_over_y x y ∈ ({x_over_y x y} : Set (away_xy x y)) := by
    simp
  have hxgen : x_over_y x y ∈ x_over_y_subalgebra x y := by
    exact Algebra.subset_adjoin hxgen_mem
  have hygen_mem : y_over_x x y ∈ ({y_over_x x y} : Set (away_xy x y)) := by
    simp
  have hygen : y_over_x x y ∈ y_over_x_subalgebra x y := by
    exact Algebra.subset_adjoin hygen_mem
  obtain ⟨p, rfl⟩ := exists_aeval_x_over_y_of_mem x y ha
  obtain ⟨q, rfl⟩ := exists_aeval_y_over_x_of_mem x y hb
  have hmem :
      Polynomial.aeval (x_over_y x y) p * Polynomial.aeval (y_over_x x y) q ∈ U := by
    -- Expand both polynomial evaluations so every summand is a mixed monomial.
    rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Finset.sum_mul]
    refine Submodule.sum_mem U ?_
    intro i hi
    rw [Finset.mul_sum]
    refine Submodule.sum_mem U ?_
    intro j hj
    have hmixed : x_over_y x y ^ i * y_over_x x y ^ j ∈ U := by
      -- Collapse the mixed monomial to a pure power in one of the two singleton adjoins.
      by_cases hji : j ≤ i
      · rw [x_over_y_pow_mul_y_over_x_pow_eq x y hji]
        have hpure : x_over_y x y ^ (i - j) ∈ (x_over_y_subalgebra x y).toSubmodule :=
          (x_over_y_subalgebra x y).pow_mem hxgen _
        exact Submodule.mem_sup_left hpure
      · have hij : i ≤ j := Nat.le_of_not_ge hji
        rw [x_over_y_pow_mul_y_over_x_pow_eq' x y hij]
        have hpure : y_over_x x y ^ (j - i) ∈ (y_over_x_subalgebra x y).toSubmodule :=
          (y_over_x_subalgebra x y).pow_mem hygen _
        exact Submodule.mem_sup_right hpure
    -- Coefficients from `R` only rescale the mixed monomial inside the same `R`-submodule.
    simpa [U, Algebra.smul_def, smul_mul_assoc, mul_assoc, mul_left_comm, mul_comm] using
      (Submodule.smul_mem U (p.coeff i) (Submodule.smul_mem U (q.coeff j) hmixed))
  simpa [U] using hmem

/-- Helper for Lemma 10.36.24: every element of `R[x / y, y / x]` lies in the additive sum of
`R[x / y]` and `R[y / x]` inside the common localization. -/
private theorem sup_subalgebra_val_mem_sum_singleton_adjoins (x y : R)
    (z : (x_over_y_subalgebra x y ⊔ y_over_x_subalgebra x y :
      Subalgebra R (away_xy x y))) :
    (z : away_xy x y) ∈ (x_over_y_subalgebra x y).toSubmodule ⊔
      (y_over_x_subalgebra x y).toSubmodule := by
  let U : Submodule R (away_xy x y) :=
    (x_over_y_subalgebra x y).toSubmodule ⊔ (y_over_x_subalgebra x y).toSubmodule
  have hz :
      (z : away_xy x y) ∈ Algebra.adjoin R
        (((x_over_y_subalgebra x y : Set (away_xy x y)) ∪
          (y_over_x_subalgebra x y : Set (away_xy x y)))) := by
    simpa using z.2
  have hmem : (z : away_xy x y) ∈ U := by
    -- Induct on the sup of the two one-generator subalgebras viewed via `Subalgebra.sup_def`.
    refine Algebra.adjoin_induction
      (p := fun a _ ↦ a ∈ U) ?_ ?_ ?_ ?_ hz
    · intro a ha
      -- A generator is now literally an element of the left or right subalgebra.
      rw [Set.mem_union] at ha
      rcases ha with ha | ha
      · exact Submodule.mem_sup_left ha
      · exact Submodule.mem_sup_right ha
    · intro r
      -- Coefficients already lie in each subalgebra, so in particular in the left summand.
      have hcoeff : algebraMap R (away_xy x y) r ∈ (x_over_y_subalgebra x y).toSubmodule :=
        algebraMap_mem (x_over_y_subalgebra x y) r
      exact Submodule.mem_sup_left hcoeff
    · intro a b _ _ ha hb
      -- The additive sup is closed under addition.
      exact Submodule.add_mem U ha hb
    · intro a b _ _ ha hb
      obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp hb
      have haa : a₁ * a₂ ∈ U := by
        -- Pure `x / y` terms stay on the left side.
        have hleftmul : a₁ * a₂ ∈ (x_over_y_subalgebra x y).toSubmodule :=
          (x_over_y_subalgebra x y).mul_mem ha₁ ha₂
        exact Submodule.mem_sup_left hleftmul
      have hab : a₁ * b₂ ∈ U :=
        mixed_product_mem_sum_singleton_adjoins x y ha₁ hb₂
      have hba : b₁ * a₂ ∈ U := by
        -- Commute the cross term to reuse the same mixed-product lemma.
        simpa [mul_comm] using mixed_product_mem_sum_singleton_adjoins x y ha₂ hb₁
      have hbb : b₁ * b₂ ∈ U := by
        -- Pure `y / x` terms stay on the right side.
        have hrightmul : b₁ * b₂ ∈ (y_over_x_subalgebra x y).toSubmodule :=
          (y_over_x_subalgebra x y).mul_mem hb₁ hb₂
        exact Submodule.mem_sup_right hrightmul
      have hleft : a₁ * a₂ + a₁ * b₂ ∈ U := Submodule.add_mem U haa hab
      have hright : b₁ * a₂ + b₁ * b₂ ∈ U := Submodule.add_mem U hba hbb
      -- Expanding the product of the two decompositions gives four admissible summands.
      simpa [add_mul, mul_add, add_assoc, add_left_comm, add_comm] using
        (Submodule.add_mem U hleft hright)
  simpa [U] using hmem

/-- The short complex `0 → R → R[x/y] ⊕ R[y/x] → R[x/y, y/x] → 0` formed in the common
localization `R_{xy}`. -/
noncomputable def x_over_y_shortComplex (x y : R) : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMkOfKerLERange
    (ModuleCat.ofHom (x_over_y_neg_diagonal x y))
    (ModuleCat.ofHom (x_over_y_sum_to_adjoin x y))
    (x_over_y_neg_diagonal_range_le_ker x y)

/-- Helper for Lemma 10.36.24: the sum map onto `R[x/y, y/x]` is surjective. -/
private theorem x_over_y_sum_to_adjoin_surjective (x y : R) :
    Function.Surjective (x_over_y_sum_to_adjoin x y) := by
  intro z
  have hz :
      (z : away_xy x y) ∈ (x_over_y_subalgebra x y).toSubmodule ⊔
        (y_over_x_subalgebra x y).toSubmodule :=
    sup_subalgebra_val_mem_sum_singleton_adjoins x y z
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hz
  refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), ?_⟩
  -- Convert the ambient additive decomposition into an actual equality in the codomain subtype.
  ext
  exact hab

/-- Helper for Lemma 10.36.24: if `a` is the image of `r` and `a + b = 0`, then `(a, b)` is the
image of `-r` under the negative diagonal map. -/
private theorem neg_diagonal_eq_pair_of_algebraMap_eq_and_add_eq_zero (x y : R)
    (a : x_over_y_subalgebra x y) (b : y_over_x_subalgebra x y) (r : R)
    (hr : algebraMap R (away_xy x y) r = (a : away_xy x y))
    (hsum : (a : away_xy x y) + (b : away_xy x y) = 0) :
    x_over_y_neg_diagonal x y (-r) = (a, b) := by
  have hneg : algebraMap R (away_xy x y) (-r) = (b : away_xy x y) := by
    calc
      algebraMap R (away_xy x y) (-r) = -algebraMap R (away_xy x y) r := by simp
      _ = -(a : away_xy x y) := by rw [hr]
      _ = (b : away_xy x y) := by
        simpa using (neg_eq_iff_add_eq_zero.mpr hsum)
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    simpa [x_over_y_neg_diagonal] using hr
  · apply Subtype.ext
    simpa [x_over_y_neg_diagonal] using hneg

/-- Helper for Lemma 10.36.24: every kernel element of the sum map lies in the range of the
negative diagonal map. -/
private theorem ker_le_range_x_over_y_neg_diagonal (x y : R) (hx : x ∈ R⁰) (hy : y ∈ R⁰)
    (hclosed : IsIntegrallyClosedIn R (Localization.Away x) ∨
      IsIntegrallyClosedIn R (Localization.Away y))
    (z : x_over_y_subalgebra x y × y_over_x_subalgebra x y)
    (hz : z ∈ LinearMap.ker (x_over_y_sum_to_adjoin x y)) :
    z ∈ LinearMap.range (x_over_y_neg_diagonal x y) := by
  rcases z with ⟨a, b⟩
  have hz_zero : x_over_y_sum_to_adjoin x y (a, b) = 0 := LinearMap.mem_ker.mp hz
  change
      (((Subalgebra.inclusion le_sup_left).toLinearMap).coprod
        ((Subalgebra.inclusion le_sup_right).toLinearMap) (a, b) = 0) at hz_zero
  rw [LinearMap.coprod_apply, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply] at hz_zero
  -- TODO: from this normalized subtype equality, extract the ambient relation
  -- `(a : away_xy x y) + (b : away_xy x y) = 0`, then show the left component lies in
  -- `R[y / x]`, invoke `algebraMap_eq_of_mem_x_over_y_inter x y hx hy hclosed`, and finish with
  -- `neg_diagonal_eq_pair_of_algebraMap_eq_and_add_eq_zero`. Lean currently hits a deterministic
  -- kernel timeout already at the step that forgets the codomain subtype to obtain `a + b = 0`.
  sorry

/-- Lemma 10.36.24: if `x` and `y` are nonzerodivisors and `R` is integrally closed in `R_x` or
`R_y`, then the sequence `0 → R → R[x/y] ⊕ R[y/x] → R[x/y, y/x] → 0` is short exact as a sequence
of `R`-modules. -/
-- Proof sketch: surjectivity of the second map comes from `(x / y) * (y / x) = 1`, so the two
-- one-generator subalgebras generate `R[x/y, y/x]`. For exactness in the middle, an element in
-- the intersection `R[x/y] ∩ R[y/x]` stabilizes the finite `R`-submodule spanned by bounded powers
-- of `x / y` and `y / x`; Lemma 10.36.2 then shows it is integral over `R`, and the hypothesis
-- that `R` is integrally closed in `R_x` or `R_y` forces it to lie in the image of `R`.
theorem x_over_y_shortComplex_shortExact (x y : R) (hx : x ∈ R⁰) (hy : y ∈ R⁰)
    (hclosed : IsIntegrallyClosedIn R (Localization.Away x) ∨
      IsIntegrallyClosedIn R (Localization.Away y)) :
    (x_over_y_shortComplex x y).ShortExact := by
  -- Route correction: keep the source-faithful bounded-power intersection argument for middle
  -- exactness, but package the remaining theorem-level coercions with small adapters instead of
  -- rebuilding larger range lemmas.
  have hExact : Function.Exact (x_over_y_neg_diagonal x y) (x_over_y_sum_to_adjoin x y) := by
    apply LinearMap.exact_of_comp_eq_zero_of_ker_le_range
    · refine LinearMap.ext fun t ↦ ?_
      simp [x_over_y_neg_diagonal, x_over_y_sum_to_adjoin]
    · intro z hz
      exact ker_le_range_x_over_y_neg_diagonal x y hx hy hclosed z hz
  exact ModuleCat.shortComplex_shortExact (x_over_y_shortComplex x y)
    (by simpa [x_over_y_shortComplex] using hExact)
    (x_over_y_neg_diagonal_injective x y hx hy)
    (by simpa [x_over_y_shortComplex] using x_over_y_sum_to_adjoin_surjective x y)

end
