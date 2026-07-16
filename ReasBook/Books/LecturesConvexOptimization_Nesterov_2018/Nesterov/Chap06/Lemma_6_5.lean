import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Definition_6_18

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Lemma 6.5 lies in the affine variational-inequality / gap-function domain.

Sampled owner-style declarations:
- `AffineVariationalInequalityProblem.IsSolution` in `Chap06/Definition_6_17`, the chapter owner
  for the source-facing variational-inequality predicate;
- `AffineVariationalInequalityProblem.gapFunction` in `Chap06/Definition_6_18`, the chapter owner
  for the associated gap function on the feasible subtype;
- `IsMinOn` and `isMinOn_iff` in mathlib, the canonical minimizer owner used across the project;
- `argmin[Q]` in `Chap01/Definition_1_3_3`, the chapter minimizer-set owner derived from
  `IsMinOn`.

Best owner abstraction:
- source-facing: `problem.IsSolution wStar`;
- core/canonical: `problem.gapFunction` together with `IsMinOn`;
- bridge/view: the equivalence between the source-facing solution predicate and minimizing the
  canonical gap function on the feasible subtype.

Primitive data:
- `problem : AffineVariationalInequalityProblem E`.

Derived API:
- the minimization statement `IsMinOn problem.gapFunction Set.univ wStar`;
- the zero-gap consequence at a solution or a minimizer.

Source/core/bridge triage:
- source-facing: Lemma 6.5 itself, relating the textbook variational inequality to gap
  minimization;
- core/canonical: `AffineVariationalInequalityProblem E`, `gapFunction`, and `IsMinOn`;
- bridge/view: the theorem below, written on the feasible subtype rather than rebuilding an
  ambient supremum functional.

The previous revision introduced a parallel ambient `ℝ`-valued gap-supremum owner. This file now
states Lemma 6.5 directly on the chapter owner `AffineVariationalInequalityProblem`, keeping only
the canonical gap-function minimization surface and its zero-gap consequences.
-/

namespace AffineVariationalInequalityProblem

/-- Lemma 6.5: a feasible point solves the affine variational inequality problem exactly when it
minimizes the associated canonical gap function on the feasible subtype. -/
theorem isSolution_iff_isMinOn_gapFunction
    (problem : AffineVariationalInequalityProblem E) (wStar : problem.feasibleSet) :
    problem.IsSolution wStar ↔ IsMinOn problem.gapFunction Set.univ wStar := sorry

/-- Every minimizer of the canonical gap function has gap value `0`. -/
theorem gapFunction_eq_zero_of_isMinOn
    (problem : AffineVariationalInequalityProblem E) (wStar : problem.feasibleSet)
    (hmin : IsMinOn problem.gapFunction Set.univ wStar) :
    problem.gapFunction wStar = 0 := sorry

/-- Every solution of an affine variational inequality problem has gap value `0`. -/
theorem gapFunction_eq_zero_of_isSolution
    (problem : AffineVariationalInequalityProblem E) (wStar : problem.feasibleSet)
    (hsol : problem.IsSolution wStar) :
    problem.gapFunction wStar = 0 := sorry

end AffineVariationalInequalityProblem

end
