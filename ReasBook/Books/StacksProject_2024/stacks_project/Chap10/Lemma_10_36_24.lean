import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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

/-- The short complex `0 → R → R[x/y] ⊕ R[y/x] → R[x/y, y/x] → 0` formed in the common
localization `R_{xy}`. -/
noncomputable def x_over_y_shortComplex (x y : R) : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMkOfKerLERange
    (ModuleCat.ofHom (x_over_y_neg_diagonal x y))
    (ModuleCat.ofHom (x_over_y_sum_to_adjoin x y))
    (x_over_y_neg_diagonal_range_le_ker x y)

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
    (x_over_y_shortComplex x y).ShortExact := sorry

end
