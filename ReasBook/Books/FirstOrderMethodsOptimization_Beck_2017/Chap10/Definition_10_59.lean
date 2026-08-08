import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 10.59 is `source-facing`: it fixes the standing assumptions for the constrained
problem `min {h(x) | x ∈ C}` used in the S-FISTA subsection. The relevant mathlib owners are the
standard predicates `C.Nonempty`, `IsClosed C`, `Convex ℝ C`, `ConvexOn ℝ Set.univ h`, and
`LipschitzWith ℓh h`. Following the project pattern for problem data in Chapter 10, the clean
public interface is therefore a small `Prop`-valued class on the objective, the feasible set, and
the given Lipschitz constant, rather than a new packaged optimization object. -/

/-- Definition 10.59: the constrained problem `min {h(x) | x ∈ C}` has a nonempty closed convex
feasible set `C`, and its objective `h : E → ℝ` is globally convex and `ℓ_h`-Lipschitz. -/
class IsConvexLipschitzConstrainedMinimizationProblem
    (h : E → ℝ) (C : Set E) (ℓh : NNReal) : Prop where
  constraint_nonempty : C.Nonempty
  constraint_closed : IsClosed C
  constraint_convex : Convex ℝ C
  objective_convex : ConvexOn ℝ Set.univ h
  objective_lipschitz : LipschitzWith ℓh h

/-- A constrained convex Lipschitz minimization problem exposes nonemptiness of the feasible set
to typeclass search. -/
instance instFactConstraintNonemptyOfIsConvexLipschitzConstrainedMinimizationProblem
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    Fact C.Nonempty :=
  ⟨hproblem.constraint_nonempty⟩

/-- A constrained convex Lipschitz minimization problem exposes closedness of the feasible set to
typeclass search. -/
instance instFactIsClosedOfIsConvexLipschitzConstrainedMinimizationProblem
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    Fact (IsClosed C) :=
  ⟨hproblem.constraint_closed⟩

/-- A constrained convex Lipschitz minimization problem exposes convexity of the feasible set to
typeclass search. -/
instance instFactConvexOfIsConvexLipschitzConstrainedMinimizationProblem
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    Fact (Convex ℝ C) :=
  ⟨hproblem.constraint_convex⟩

/-- A constrained convex Lipschitz minimization problem exposes convexity of the objective to
typeclass search. -/
instance instFactConvexOnOfIsConvexLipschitzConstrainedMinimizationProblem
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    Fact (ConvexOn ℝ Set.univ h) :=
  ⟨hproblem.objective_convex⟩

/-- A constrained convex Lipschitz minimization problem exposes the global Lipschitz bound of the
objective to typeclass search. -/
instance instFactLipschitzWithOfIsConvexLipschitzConstrainedMinimizationProblem
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    Fact (LipschitzWith ℓh h) :=
  ⟨hproblem.objective_lipschitz⟩

/-- A constrained convex Lipschitz minimization problem canonically makes the real-valued
objective proper after coercion to `EReal`. -/
theorem IsConvexLipschitzConstrainedMinimizationProblem.objective_toEReal_proper
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    IsProperExtendedRealFunction h.toExtendedReal := by
  rcases hproblem.constraint_nonempty with ⟨x, hx⟩
  let _ : Nonempty E := ⟨x⟩
  simpa using Function.toExtendedReal_isProper h

/-- A constrained convex Lipschitz minimization problem makes the real-valued objective
lower semicontinuous after coercion to `EReal`. -/
theorem IsConvexLipschitzConstrainedMinimizationProblem.objective_toEReal_lowerSemicontinuous
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    LowerSemicontinuous h.toExtendedReal :=
  Function.toExtendedReal_lowerSemicontinuous_of_lipschitz hproblem.objective_lipschitz

/-- A constrained convex Lipschitz minimization problem makes the real-valued objective convex
after coercion to `EReal`. -/
theorem IsConvexLipschitzConstrainedMinimizationProblem.objective_toEReal_convex
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    is_convex_function h.toExtendedReal :=
  Function.toExtendedReal_isConvexFunction hproblem.objective_convex

/-- The real-valued objective of a constrained convex Lipschitz minimization problem is proper
after coercion to `EReal`. -/
instance instIsProperExtendedRealFunctionToERealOfIsConvexLipschitzConstrainedMinimizationProblem
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    IsProperExtendedRealFunction h.toExtendedReal :=
  hproblem.objective_toEReal_proper

/-- The real-valued objective of a constrained convex Lipschitz minimization problem is lower
semicontinuous after coercion to `EReal`. -/
instance instLowerSemicontinuousToERealOfIsConvexLipschitzConstrainedMinimizationProblem
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    LowerSemicontinuous h.toExtendedReal :=
  hproblem.objective_toEReal_lowerSemicontinuous

/-- A constrained convex Lipschitz minimization problem exposes lower semicontinuity of the
real-valued objective after coercion to `EReal` through `Fact`. -/
instance instFactLowerSemicontinuousToERealOfIsConvexLipschitzConstrainedMinimizationProblem
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    Fact (LowerSemicontinuous h.toExtendedReal) :=
  ⟨hproblem.objective_toEReal_lowerSemicontinuous⟩

/-- The real-valued objective of a constrained convex Lipschitz minimization problem is convex
after coercion to `EReal`. -/
instance instIsConvexFunctionToERealOfIsConvexLipschitzConstrainedMinimizationProblem
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    is_convex_function h.toExtendedReal :=
  hproblem.objective_toEReal_convex

/-- A constrained convex Lipschitz minimization problem exposes convexity of the real-valued
objective after coercion to `EReal` through `Fact`. -/
instance instFactIsConvexFunctionToERealOfIsConvexLipschitzConstrainedMinimizationProblem
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    Fact (is_convex_function h.toExtendedReal) :=
  ⟨hproblem.objective_toEReal_convex⟩

end
