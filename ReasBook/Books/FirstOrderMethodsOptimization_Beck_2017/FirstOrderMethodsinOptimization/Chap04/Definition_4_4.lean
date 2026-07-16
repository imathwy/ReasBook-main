import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

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
