import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Proposition_10_58
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Definition_10_43
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Definition_10_60

noncomputable section

section

variable {m n p : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)

variable (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
variable (D : Matrix (Fin p) (Fin n) ℝ) (lam : ℝ)

variable (Lf : NNReal) (α : PosReal)
variable
  [hgProper : IsProperExtendedRealFunction (Function.toExtendedReal (ambient_l1_regularizer n lam))]
  [hgClosed : Fact (LowerSemicontinuous (Function.toExtendedReal (ambient_l1_regularizer n lam)))]
  [hgConvex : Fact (is_convex_function (Function.toExtendedReal (ambient_l1_regularizer n lam)))]

local instance gRegProper :
    IsProperExtendedRealFunction (Function.toExtendedReal (ambient_l1_regularizer n lam)) :=
  hgProper

local instance gRegLowerSemicontinuous :
    Fact (LowerSemicontinuous (Function.toExtendedReal (ambient_l1_regularizer n lam))) :=
  hgClosed

local instance gRegConvex :
    Fact (is_convex_function (Function.toExtendedReal (ambient_l1_regularizer n lam))) :=
  hgConvex

/- Algorithm 10.60 is a `bridge/view` item.

Domain sampling in the Chapter 10 smoothing API identifies the owner layers:
- `source-facing`: the concrete Definition 10.60 least-squares analysis-`ℓ¹` objective, with
  data-fit term `least_squares_loss A b`, analysis penalty `analysis_l1_penalty D`, and ambient
  `ℓ¹` regularizer `ambient_l1_regularizer n lam`;
- `core/canonical`: the recursive algorithm owners `s_fista`, `s_fista_x`, and `s_fista_y`
  from Proposition 10.58;
- `bridge/view`: the specialization of those canonical owners to the concrete Definition 10.60
  data together with a chosen smoothing term `hμ`.

Primitive data are the concrete three-term model, the S-FISTA problem parameters
`L_f`, `α`, a chosen smoothing term `h_μ`, the smoothing parameter `μ`, the initial point `x⁰`,
and the proper/closed/convex regularity needed for the concrete regularizer. The proof that `h_μ`
smooths `analysis_l1_penalty D` belongs to later convergence statements, not to this owner-level
specialization surface, so the bridge here should reuse the Definition 10.60 owners directly. -/

recall s_fista_curvature_bound
recall s_fista
recall s_fista_x
recall s_fista_y
recall fista_momentum_sequence

section

variable (μ : PosReal)

set_option linter.hashCommand false

/- Algorithm 10.60: once a smoothing term `h_μ` is fixed, the least-squares analysis-`ℓ¹`
S-FISTA recursion is the Chapter 10 owner `s_fista` specialized to the Definition 10.60 model. -/
#check
  fun (hμ : X → ℝ) (x0 : X) ↦
    s_fista
      (least_squares_loss A b)
      hμ
      (Function.toExtendedReal (ambient_l1_regularizer n lam))
      Lf α μ x0

/- The associated primal-iterate and extrapolated-point sequences are the corresponding
specializations of `s_fista_x` and `s_fista_y`. -/
#check
  fun (hμ : X → ℝ) (x0 : X) ↦
    s_fista_x
      (least_squares_loss A b)
      hμ
      (Function.toExtendedReal (ambient_l1_regularizer n lam))
      Lf α μ x0

#check
  fun (hμ : X → ℝ) (x0 : X) ↦
    s_fista_y
      (least_squares_loss A b)
      hμ
      (Function.toExtendedReal (ambient_l1_regularizer n lam))
      Lf α μ x0

/- The effective curvature parameter is the canonical S-FISTA curvature bound
`L̃ = L_f + α / μ`. -/
#check s_fista_curvature_bound Lf α μ

/- The specialized theorem surface reuses the canonical base-step and successor-step formulas
directly. -/
#check
  fun (hμ : X → ℝ) (x0 : X) ↦
    (s_fista_x_zero
      (least_squares_loss A b)
      hμ
      (Function.toExtendedReal (ambient_l1_regularizer n lam))
      Lf α μ x0 :
      s_fista_x
        (least_squares_loss A b)
        hμ
        (Function.toExtendedReal (ambient_l1_regularizer n lam))
        Lf α μ x0 0 = x0)

#check
  fun (hμ : X → ℝ) (x0 : X) ↦
    (s_fista_y_zero
      (least_squares_loss A b)
      hμ
      (Function.toExtendedReal (ambient_l1_regularizer n lam))
      Lf α μ x0 :
      s_fista_y
        (least_squares_loss A b)
        hμ
        (Function.toExtendedReal (ambient_l1_regularizer n lam))
        Lf α μ x0 0 = x0)

#check
  fun (hμ : X → ℝ) (x0 : X) (k : ℕ) ↦
    s_fista_x_succ
      (least_squares_loss A b)
      hμ
      (Function.toExtendedReal (ambient_l1_regularizer n lam))
      Lf α μ x0 k

#check
  fun (hμ : X → ℝ) (x0 : X) (k : ℕ) ↦
    s_fista_y_succ
      (least_squares_loss A b)
      hμ
      (Function.toExtendedReal (ambient_l1_regularizer n lam))
      Lf α μ x0 k

end

end
