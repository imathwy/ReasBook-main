import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Lemma_3_1_14
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Theorem_3_1_8
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Theorem_3_44

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

local notation:max "∂[" Q "] " f:arg "(" x:arg ")" => subdifferentialWithin Q f x

universe u v w

/- Theorem 3.1.31 lies in the chapter's minimax / active-subgradient domain.

Mandatory domain-style sampling before refinement:
- `pointwiseSupremumOn` in `Chap03/Theorem_3_1_8`, the chapter owner for subset-indexed upper
  envelopes on the `WithTop ℝ` side;
- `activePointwiseSupremumOnIndices` in `Chap03/Lemma_3_1_14`, the canonical active-set owner for
  pointwise suprema;
- the source-facing notation `∂[P] f(x)`, together with the bridge
  `subdifferentialWithin` and `mem_subdifferentialWithin_iff` in `Chap03/Theorem_3_44`, the
  chapter owner surface for real-valued relative subgradients;
- mathlib `IsMinOn` and `StdSimplex`, the canonical owners for minimizers on a set and simplex
  weights.

Best owner abstraction:
- source-facing: the minimax equality theorem below;
- core/canonical: `pointwiseSupremumOn`, `activePointwiseSupremumOnIndices`, `IsMinOn`,
  `∂[P] f(x)`, and `StdSimplex`;
- bridge/view: the real-valued objective `f` on `P`, together with its equality to the
  `WithTop ℝ` owner `pointwiseSupremumOn`.

Primitive data:
- the primal set `P`, parameter set `S`, and kernel `Ψ`;
- the real-valued primal objective `f`;
- the minimizing primal point `xStar`;
- the active slice parameters `u i` and their relative subgradients `g i`;
- the simplex weights and their barycenter in the parameter space.

Derived API:
- the faithful `WithTop ℝ` upper-envelope owner `pointwiseSupremumOn`;
- the faithful active-set owner `activePointwiseSupremumOnIndices`;
- the minimax theorem phrased on the canonical `IsMinOn` / `∂[P] f(x)` owners, with
  real-valued lower slices exposed only under explicit bounded-below hypotheses.

Source/core/bridge triage:
- source-facing: `minimax_eq_of_activeSubgradientRepresentation_at_minimizer`;
- core/canonical: `pointwiseSupremumOn`, `activePointwiseSupremumOnIndices`, `IsMinOn`,
  `∂[P] f(x)`, `StdSimplex`;
- bridge/view: the objective bridge
  `(f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x`.

The previous version installed new real-valued public owners
`sectionSupremumOn` / `sectionInfimumOn` by unconditional `Real.sSup` / `Real.sInf`. That loses
the mathematical semantics on empty or unbounded slices. This refinement therefore deletes those
duplicate owners, reuses the faithful chapter owner `pointwiseSupremumOn` on the upper side,
reuses `activePointwiseSupremumOnIndices` for activity, and exposes real-valued lower slices only
through theorem hypotheses that guarantee the relevant slice infima are genuine. -/

section Minimax

variable {X : Type u} {U : Type v} {ι : Type w}

variable [Fintype ι]

variable [SeminormedAddCommGroup X] [InnerProductSpace ℝ X]
variable [AddCommGroup U] [Module ℝ U]

-- Proof sketch: use the constrained subgradient inequality for `gStar` together with the
-- optimality relation `⟪gStar, x - xStar⟫ = 0` on `P`. Rewrite `gStar` as the simplex-weighted sum
-- of the active section subgradients `g i`, combine their section inequalities, and use the
-- barycenter inequality
-- `∑ i, weights.weights i * Ψ(x, u i) ≤ Ψ(x, (Finset.univ).centerMass weights.weights u)` to show
-- that `f xStar ≤ sInf ((fun x ↦ Ψ x uBar) '' P)` for the barycenter parameter
-- `uBar = (Finset.univ).centerMass weights.weights u`. The faithful upper-owner bridge and weak
-- duality then yield the minimax equality `(3.1.78)`.
/-- Theorem 3.1.31: let `f : X → ℝ` be a real-valued objective on `P` whose `WithTop ℝ` lift
agrees with the faithful upper-envelope owner
`pointwiseSupremumOn S (fun x u ↦ (Ψ x u : WithTop ℝ))` on `P`. If `xStar` minimizes `f` on `P`,
if some relative subgradient `gStar ∈ ∂_P f(xStar)` satisfying the first-order optimality
relation `⟪gStar, x - xStar⟫ = 0` on `P` admits a simplex representation by active section
subgradients `g i ∈ ∂_P (Ψ(·, u_i))(xStar)`, and if the real lower slices
`x ↦ Ψ(x, u)` are exposed only under bounded-below hypotheses on `P`, then the minimax relation
`(3.1.78)` holds:
`min_{x ∈ P} f(x) = max_{u ∈ S} inf_{x ∈ P} Ψ(x, u)`. -/
theorem minimax_eq_of_activeSubgradientRepresentation_at_minimizer
    {P : Set X} {S : Set U} {Ψ : X → U → ℝ} {f : X → ℝ}
    {xStar gStar : X}
    (hf_eq :
      ∀ ⦃x : X⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    (hxStar_min : IsMinOn f P xStar)
    (hgStar_mem : gStar ∈ ∂[P] f(xStar))
    (horth : ∀ ⦃x : X⦄, x ∈ P → inner ℝ gStar (x - xStar) = 0)
    (weights : StdSimplex ℝ ι)
    (u : ι → U) (g : ι → X)
    (hu_active :
      ∀ i : ι,
        u i ∈ activePointwiseSupremumOnIndices S
          (fun x u ↦ (Ψ x u : WithTop ℝ)) xStar)
    (hg_mem :
      ∀ i : ι, g i ∈ ∂[P] (fun x ↦ Ψ x (u i)) (xStar))
    (hgStar_repr : gStar = ∑ i, weights.weights i • g i)
    (hΨ_bddBelow :
      ∀ ⦃u : U⦄, u ∈ S → BddBelow ((fun x ↦ Ψ x u) '' P))
    (hu_bar_mem :
      (Finset.univ).centerMass weights.weights u ∈ S)
    (hbar_domination :
      ∀ ⦃x : X⦄, x ∈ P →
        (∑ i, weights.weights i * Ψ x (u i)) ≤
          Ψ x ((Finset.univ).centerMass weights.weights u)) :
    sInf (f '' P) =
      sSup ((fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) '' S) := sorry

end Minimax
