import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap09.ProductL2Scope
import BauschkeLean.Chap29.Definition_29_40

-- Declarations for this item will be appended below by the statement pipeline.

open SetValuedOperator
open scoped ERealFunction.ProductL2 InnerProductSpace Pointwise

universe u

namespace ERealFunction

noncomputable section

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (f : H → ℝ)

-- Semantic recall: `lean_leansearch` surfaced the canonical mathlib epigraph owners
-- `ConvexOn.convex_epigraph` and `IsClosed.epigraph`; this item keeps the Chapter 29 projector
-- notation `P[C, hC]` and the canonical subdifferential fiber `(∂ f.toEReal) x`.

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- A real pair belongs to `epigraph f.toEReal.asEReal` exactly when its second coordinate lies
above `f x`. -/
@[simp] theorem mem_epigraph_toEReal_iff (x : H) (ξ : ℝ) :
    (x, ξ) ∈ epigraph f.toEReal.asEReal ↔ f x ≤ ξ := by
  simp [Function.asEReal_apply, Function.toEReal_apply]

/-- The epigraph of a continuous convex real-valued function is a Chebyshev set in `H × ℝ`. -/
theorem isChebyshev_epigraph_of_continuous_convex
    (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f) :
    IsChebyshev (epigraph f.toEReal.asEReal) := by
  apply isChebyshev_of_nonempty_isClosed_convex
  · refine ⟨((0 : H), f 0), ?_⟩
    simp
  · simpa [epigraph, Function.asEReal_apply, Function.toEReal_apply] using
      (IsClosed.epigraph isClosed_univ hcont.continuousOn)
  · simpa [epigraph, Function.asEReal_apply, Function.toEReal_apply] using
      hconv.convex_epigraph

/-- Proposition 29.35: if `f : H → ℝ` is convex and continuous, if
`C = epigraph f.toEReal.asEReal = {(x, ξ) | f x ≤ ξ}`, and if `(z, ζ) ∉ C`, then the inclusion
`z ∈ x + (f x - ζ) ∂ f(x)` has a unique solution `xbar`, and the metric projection of `(z, ζ)`
onto `C` is `(xbar, f xbar)`. -/
theorem existsUnique_subgradient_solution_and_projection_eq_of_not_mem_epigraph
    (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (z : H) (ζ : ℝ) (hz : (z, ζ) ∉ epigraph f.toEReal.asEReal) :
    ∃! xbar : H,
      z ∈ ({xbar} : Set H) + (f xbar - ζ) • ((∂ f.toEReal) xbar) ∧
        P[epigraph f.toEReal.asEReal,
          isChebyshev_epigraph_of_continuous_convex f hcont hconv] (z, ζ) = (xbar, f xbar) := sorry

/-- Proposition 29.35: the first coordinate of the metric projection of `(z, ζ)` onto
`epigraph f.toEReal.asEReal` satisfies the source subgradient inclusion. -/
theorem projection_fst_mem_subgradient_translate_of_not_mem_epigraph
    (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (z : H) (ζ : ℝ) (hz : (z, ζ) ∉ epigraph f.toEReal.asEReal) :
    z ∈
      ({(P[epigraph f.toEReal.asEReal,
          isChebyshev_epigraph_of_continuous_convex f hcont hconv] (z, ζ)).1} : Set H) +
        (f ((P[epigraph f.toEReal.asEReal,
            isChebyshev_epigraph_of_continuous_convex f hcont hconv]
            (z, ζ)).1) - ζ) •
          ((∂ f.toEReal)
            ((P[epigraph f.toEReal.asEReal,
                isChebyshev_epigraph_of_continuous_convex f hcont hconv]
              (z, ζ)).1)) := by
  let p :=
    P[epigraph f.toEReal.asEReal,
      isChebyshev_epigraph_of_continuous_convex f hcont hconv] (z, ζ)
  rcases ExistsUnique.exists
      (existsUnique_subgradient_solution_and_projection_eq_of_not_mem_epigraph
        f hcont hconv z ζ hz) with
    ⟨xbar, hsub, hproj⟩
  have hfst : xbar = p.1 := by
    simpa [p] using (congrArg Prod.fst hproj).symm
  simpa [p, hfst] using hsub

/-- Proposition 29.35: the metric projection of `(z, ζ)` onto `epigraph f.toEReal.asEReal` lies on
the graph of `f`. -/
theorem projection_eq_fst_and_value_of_not_mem_epigraph
    (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (z : H) (ζ : ℝ) (hz : (z, ζ) ∉ epigraph f.toEReal.asEReal) :
    P[epigraph f.toEReal.asEReal,
      isChebyshev_epigraph_of_continuous_convex f hcont hconv] (z, ζ) =
      ((P[epigraph f.toEReal.asEReal,
          isChebyshev_epigraph_of_continuous_convex f hcont hconv]
          (z, ζ)).1,
        f ((P[epigraph f.toEReal.asEReal,
            isChebyshev_epigraph_of_continuous_convex f hcont hconv]
            (z, ζ)).1)) := by
  let p :=
    P[epigraph f.toEReal.asEReal,
      isChebyshev_epigraph_of_continuous_convex f hcont hconv] (z, ζ)
  rcases ExistsUnique.exists
      (existsUnique_subgradient_solution_and_projection_eq_of_not_mem_epigraph
        f hcont hconv z ζ hz) with
    ⟨xbar, _, hproj⟩
  have hfst : xbar = p.1 := by
    simpa [p] using (congrArg Prod.fst hproj).symm
  calc
    p = (xbar, f xbar) := by simpa [p] using hproj
    _ = (p.1, f p.1) := by rw [hfst]

/-- Proposition 29.35: the ordinate of the metric projection of `(z, ζ)` onto
`epigraph f.toEReal.asEReal` is the value of `f` at its abscissa. -/
theorem projection_snd_eq_value_of_not_mem_epigraph
    (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (z : H) (ζ : ℝ) (hz : (z, ζ) ∉ epigraph f.toEReal.asEReal) :
    (P[epigraph f.toEReal.asEReal,
        isChebyshev_epigraph_of_continuous_convex f hcont hconv] (z, ζ)).2 =
      f ((P[epigraph f.toEReal.asEReal,
          isChebyshev_epigraph_of_continuous_convex f hcont hconv]
          (z, ζ)).1) := by
  simpa using
    congrArg Prod.snd
      (projection_eq_fst_and_value_of_not_mem_epigraph f hcont hconv z ζ hz)

end

end

end ERealFunction
