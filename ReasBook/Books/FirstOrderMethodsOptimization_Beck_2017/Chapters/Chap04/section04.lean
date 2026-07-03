

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_4 (from Chap04) -/
open Matrix

universe u

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "E" => ι → ℝ

/- Definition 4.4 is `source-facing`: it specializes the chapter owner
`conjugate_function` to the explicit quadratic-affine map on a finite real product `ι → ℝ`,
specializing to `ℝ^n` when `ι = Fin n`. The primitive data here is the quadratic-affine function
itself; its Fenchel-conjugate supremum formula and the algebraic rewrite of that formula are
derived `bridge/view` API. -/

/-- Definition 4.4: the quadratic-affine function
`x ↦ (1 / 2) xᵀ A x + bᵀ x + c` on a finite real product, specializing to `ℝ^n` for
`ι = Fin n`. -/
def quadratic_affine_function (A : Matrix ι ι ℝ) (b : E) (c : ℝ) : E → ℝ :=
  fun x ↦ (1 / 2 : ℝ) * dotProduct x (A *ᵥ x) + dotProduct b x + c

/-- Evaluating `quadratic_affine_function A b c` at `x` gives
`(1 / 2) xᵀ A x + bᵀ x + c`. -/
@[simp] theorem quadratic_affine_function_apply (A : Matrix ι ι ℝ) (b x : E) (c : ℝ) :
    quadratic_affine_function A b c x =
      (1 / 2 : ℝ) * dotProduct x (A *ᵥ x) + dotProduct b x + c :=
  rfl

-- Proof sketch: apply `conjugate_function_apply` to the `EReal`-valued lift of
-- `quadratic_affine_function A b c`. The coordinate pairing identified by `dotProductEquiv`
-- evaluates to `dotProduct y x`, yielding the displayed supremum formula.
/-- Definition 4.4: for the quadratic-affine function `f(x) = (1 / 2) xᵀ A x + bᵀ x + c` on
`ι → ℝ`, hence on `ℝ^n` when `ι = Fin n`, the conjugate at `y` is the supremum, and in the
positive-definite setting the maximum, of the values
`yᵀ x - (1 / 2) xᵀ A x - bᵀ x - c` from equation (4.4.7). -/
theorem quadratic_affine_function_conjugate_apply (A : Matrix ι ι ℝ)
    (b y : E) (c : ℝ) :
    conjugate_function (fun x : E ↦ (quadratic_affine_function A b c x : EReal))
        (dotProductEquiv ℝ ι y) =
      sSup (Set.range fun x : E ↦
        ((dotProduct y x - quadratic_affine_function A b c x : ℝ) : EReal)) := sorry

-- Proof sketch: start from `quadratic_affine_function_conjugate_apply` and regroup the real
-- integrand by distributivity to rewrite `yᵀ x - bᵀ x` as `-(b - y)ᵀ x`.
/-- The quadratic-affine conjugate integrand can also be written as
`-(1 / 2) xᵀ A x - (b - y)ᵀ x - c`. -/
theorem quadratic_affine_function_conjugate_apply_rewrite (A : Matrix ι ι ℝ)
    (b y : E) (c : ℝ) :
    conjugate_function (fun x : E ↦ (quadratic_affine_function A b c x : EReal))
        (dotProductEquiv ℝ ι y) =
      sSup (Set.range fun x : E ↦
        (((-(1 / 2 : ℝ)) * dotProduct x (A *ᵥ x) - dotProduct (b - y) x - c : ℝ) :
          EReal)) := sorry

end

/-! ### Proposition_4_4 (from Chap04) -/
open Matrix

noncomputable section

/- Proposition 4.4 is `source-facing`. Its owner abstractions already exist upstream in the
project: `extendedIndicator` from Chapter 2, `support_function` from Chapter 2,
`conjugate_function` from Definition 4.1, and the coordinatewise max function
`coordinatewiseMax` from Chapter 3. This file keeps only the simplex-support bridge for that max
function and the resulting conjugate statement. -/

-- Proof sketch: `support_function_unit_simplex_eq_coordinate_max` already identifies the support
-- function of the standard simplex with the coordinate supremum. Rewrite that supremum using the
-- project owner `coordinatewiseMax`.
/-- The coordinatewise maximum is the support function of the standard simplex. -/
theorem coordinatewiseMax_eq_support_function_stdSimplex {n : ℕ} [Nonempty (Fin n)]
    (x : Fin n → ℝ) :
    (coordinatewiseMax x : EReal) =
      support_function (stdSimplex ℝ (Fin n)) (dotProductEquiv ℝ (Fin n) x) := sorry

-- Proof sketch: rewrite `fun x ↦ (coordinatewiseMax x : EReal)` as the support function of the
-- standard simplex using `coordinatewiseMax_eq_support_function_stdSimplex`. Then identify the
-- conjugate of that support function with the indicator of the simplex; because the standard
-- simplex is closed and convex, the general support-function conjugacy formula specializes to
-- `extendedIndicator (stdSimplex ℝ (Fin n))`.
/-- Proposition 4.4: for the function `f(x) = max {x_1, x_2, ..., x_n}` on `R^n`, the Fenchel
conjugate, expressed on `R^n` through the Euclidean pairing `dotProductEquiv`, is the indicator
function of the standard simplex `Δ_n`. -/
theorem conjugate_coordinatewiseMax_eq_extendedIndicator_stdSimplex {n : ℕ}
    [Nonempty (Fin n)] :
    (fun y : Fin n → ℝ ↦
      conjugate_function (fun x : Fin n → ℝ ↦ (coordinatewiseMax x : EReal))
        (dotProductEquiv ℝ (Fin n) y)) =
      extendedIndicator (stdSimplex ℝ (Fin n)) := sorry

/-! ### Theorem_4_4 (from Chap04) -/
universe u v

section

variable {V : Type u} {E : Type v}
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup E] [Module ℝ E]

/- Theorem 4.4 is `source-facing` in the chapter conjugacy API. Its primitive owner is
`conjugate_function` from Definition 4.1, while the inverse transpose in the textbook formula is
the canonical mathlib dual equivalence `A.dualMap.symm`. -/

-- Proof sketch: expand the conjugate by its defining supremum, make the change of variables
-- `z = A (x - a)` so that `x = A.symm z + a`, and rewrite the pairing term by the dual pullback
-- identity `A.dualMap φ x = φ (A x)`. The remaining affine constants factor out of the supremum,
-- leaving the conjugate of `f` evaluated at `A.dualMap.symm (y - b)`.
/-- Theorem 4.4: for `g(x) = f (A (x - a)) + ⟨b, x⟩ + c`, the conjugate of `g` at `y` is the
conjugate of `f` at the inverse transpose pullback `A.dualMap.symm (y - b)`, shifted by the affine
term `(y a) - c - (b a)`. This is the item's formula (4.13) in the chapter owner notation. -/
theorem conjugate_function_affine_change_of_variables
    (f : E → EReal) (A : V ≃ₗ[ℝ] E) (a : V) (b y : Module.Dual ℝ V) (c : ℝ) :
    conjugate_function (fun x : V ↦ f (A (x - a)) + (b x : EReal) + (c : EReal)) y =
      conjugate_function f (A.dualMap.symm (y - b)) +
        ((y a - c - b a : ℝ) : EReal) := sorry

end
