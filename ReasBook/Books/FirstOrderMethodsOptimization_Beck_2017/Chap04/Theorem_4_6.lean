import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 4.6 is `source-facing` in the chapter Fenchel-duality API. Its owner declarations are
already upstream: `effective_domain` from Definition 2.1, `IsProperExtendedRealFunction` from
Definition 2.5, `is_convex_function` from Definition 2.6, and the Chapter 4 dual objects
`conjugate_function`, `fenchel_dual_objective`, and `fenchel_dual_problem_value` from
Definitions 4.1 and 4.8. This file therefore keeps only the duality and attainment statements,
reusing those owners directly instead of repeating parallel local copies. -/

recall effective_domain
recall IsProperExtendedRealFunction
recall is_convex_function
recall conjugate_function
recall conjugate_function_apply
recall fenchel_dual_objective
recall fenchel_dual_problem_value
recall fenchel_dual_problem_value_eq_sSup

-- Proof sketch: apply Fenchel--Rockafellar duality to the separable objective on `E × E` composed
-- with the diagonal map `x ↦ (x, x)`. The relative-interior qualification is exactly the standard
-- constraint qualification for this formulation, and the resulting dual problem value is the
-- supremum of `y ↦ -f*(y) - g*(-y)`.
/-- Theorem 4.6: Fenchel's duality. For proper convex extended-real-valued functions on a
finite-dimensional real normed space whose effective domains have intersecting relative interiors,
the primal infimum of `f + g` equals Fenchel's dual problem value, equivalently the supremum of
`y ↦ -f*(y) - g*(-y)`. -/
theorem fenchel_duality_value_eq (f g : E → EReal)
    (hf_proper : IsProperExtendedRealFunction f)
    (hg_proper : IsProperExtendedRealFunction g)
    (hf_convex : is_convex_function f)
    (hg_convex : is_convex_function g)
    (hqual :
      (intrinsicInterior ℝ (effective_domain f) ∩
        intrinsicInterior ℝ (effective_domain g)).Nonempty) :
    sInf (Set.range fun x : E ↦ f x + g x) = fenchel_dual_problem_value f g := sorry

-- Proof sketch: under the same qualification, Fenchel--Rockafellar duality gives existence of a
-- dual maximizer whenever the dual problem value is a real number. Rephrase the attained maximum
-- as an `IsGreatest` statement for the range of `fenchel_dual_objective`.
/-- If Fenchel's dual problem value is finite, then the dual optimization problem attains its
maximum. -/
theorem exists_isGreatest_fenchel_dual_objective_of_finite_value (f g : E → EReal)
    (hf_proper : IsProperExtendedRealFunction f)
    (hg_proper : IsProperExtendedRealFunction g)
    (hf_convex : is_convex_function f)
    (hg_convex : is_convex_function g)
    (hqual :
      (intrinsicInterior ℝ (effective_domain f) ∩
        intrinsicInterior ℝ (effective_domain g)).Nonempty)
    (hfinite : ∃ r : ℝ, fenchel_dual_problem_value f g = (r : EReal)) :
    ∃ y : Module.Dual ℝ E,
      IsGreatest (Set.range (fenchel_dual_objective f g)) (fenchel_dual_objective f g y) := sorry

end
