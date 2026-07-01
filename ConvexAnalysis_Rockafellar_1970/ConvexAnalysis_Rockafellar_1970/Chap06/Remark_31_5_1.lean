import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_10
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_2
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_31_5

noncomputable section

open scoped Gradient PolarCone RealInnerProductSpace Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "IsClosedProperConvex[ℝ]" => @Function.IsClosedProperConvex ℝ
local notation "w" => (fun z : E ↦ (((1 / 2 : ℝ) * ‖z‖ ^ 2 : ℝ) : WithBotTop ℝ))

/-!
Source/core/bridge triage for this item.

- `source-facing`: Remark 31.5.1 introduces the proximation operator of a closed proper convex
  function as the unique minimizer of the quadratic perturbation from Theorem 31.5, then records
  Moreau's decomposition through the canonical dual Moreau minimizer, together with the
  closed-convex-set / cone / subspace specializations.
- `core/canonical`: the relevant existing owners are `Function.IsClosedProperConvex`,
  `IsMinOn`, Fenchel conjugation `f⋆`, the subdifferential owner
  `∂ᵥ` / `Function.subdifferentialAt`, the indicator notation `δ[ℝ](· | C)`, and the polar
  notation `Kᵒ`, plus the Chapter 31 gradient/minimizer owners for the primal and dual Moreau
  envelopes.
- `bridge/view`: the new source-facing owner in this file is the proximal map itself; the cone and
  subspace remarks stay as companion theorems rather than as a new wrapper package.

Domain-style sampling used here:
- `existsUnique_primal_moreau_minimizer`;
- `primal_and_dual_moreau_minimizers_iff_euclidean`;
- `gradient_dual_moreau_envelope_is_primal_minimizer`;
- `gradient_primal_moreau_envelope_is_dual_minimizer`;
- `indicatorFunction_isClosedProperConvex_of_nonempty`;
- `convexConjugate_indicatorFunction_eq_indicatorFunction_polarCone`;
- `polarCone_eq_orthogonal`.

Primitive data vs derived API:
- primitive inputs: a closed proper convex function `f`, represented by
  `hf : f.IsClosedProperConvex`, and a point `z`;
- derived API: the canonical minimizer `Function.prox f hf z`, its variational specification, the
  Moreau decomposition through the canonical dual Moreau gradient, and the geometric
  specializations to projections onto a closed convex set, to cone/polar decompositions, and to
  orthogonal decompositions of subspaces.

Layer target: `source-facing`, with the public owner `Function.prox` built from the canonical
unique-minimizer owner already proved in Theorem 31.5.

Notation decision:
- no additional textbook notation is introduced here, because the canonical owner depends on the
  non-inferable hypothesis `hf : f.IsClosedProperConvex`; keeping `hf` explicit is part of the
  correct public API for this file.
-/

namespace Function

/-- Remark 31.5.1: for a closed proper convex function `f`, the proximation operator sends `z` to
the unique minimizer of `x ↦ f x + (1 / 2) ‖z - x‖^2`. This is Rockafellar's
`prox(z | f)`. -/
noncomputable def prox (f : E → WithBotTop ℝ) (hf : IsClosedProperConvex[ℝ] f) (z : E) : E :=
  Classical.choose (existsUnique_primal_moreau_minimizer hf z)

-- Proof sketch: `Function.prox f hf z` is the unique primal Moreau minimizer supplied by
-- `existsUnique_primal_moreau_minimizer hf z`.
/-- The proximation operator realizes the unique minimizer in Theorem 31.5. -/
theorem prox_isMinOn (f : E → WithBotTop ℝ) (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    IsMinOn (fun x : E ↦ f x + w (z - x)) Set.univ (prox f hf z) := sorry

-- Proof sketch: uniqueness in `existsUnique_primal_moreau_minimizer hf z` identifies any other
-- minimizer of the same quadratic perturbation with the chosen point `prox f hf z`.
/-- Any minimizer of the primal Moreau objective is equal to the proximation point. -/
theorem eq_prox_of_isMinOn (f : E → WithBotTop ℝ) (hf : IsClosedProperConvex[ℝ] f) (z x : E)
    (hx : IsMinOn (fun y : E ↦ f y + w (z - y)) Set.univ x) :
    x = prox f hf z := sorry

-- Proof sketch: combine `prox_isMinOn` with
-- `gradient_primal_moreau_envelope_is_dual_minimizer hf z`, then apply
-- `primal_and_dual_moreau_minimizers_iff_euclidean`. The resulting identity is Moreau's
-- decomposition, with the gradient of the primal Moreau envelope realizing the dual proximation
-- point.
/-- Moreau's decomposition: `z` is the sum of the proximation point `prox(z | f)` and the
gradient of the primal Moreau envelope `((f □ w).realBranch)`, and that gradient lies in
`∂f (prox(z | f))`. -/
theorem prox_add_dual_moreau_gradient_mem_subdifferential
    (f : E → WithBotTop ℝ) (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    z = prox f hf z + ∇ (Function.realBranch ((f □ w) : E → WithBotTop ℝ)) z ∧
      ∇ (Function.realBranch ((f □ w) : E → WithBotTop ℝ)) z ∈ ∂ᵥf(prox f hf z) := sorry

-- Proof sketch: take the decomposition identity from
-- `prox_add_dual_moreau_gradient_mem_subdifferential` and solve for the dual Moreau gradient.
/-- The dual Moreau gradient is the residual `z - prox(z | f)`. In Remark 31.5.1 this is the
dual proximation point corresponding to `f⋆`. -/
theorem dual_moreau_gradient_eq_sub
    (f : E → WithBotTop ℝ) (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    ∇ (Function.realBranch ((f □ w) : E → WithBotTop ℝ)) z = z - prox f hf z := sorry

-- Proof sketch: for `f = δ[ℝ](· | C)`, the objective defining `prox f z` is finite exactly on
-- `C`, where it reduces to `(1 / 2) ‖z - x‖^2`. Thus the proximation point lies in `C` and is
-- the nearest point of `C` to `z`.
/-- For the indicator of a nonempty closed convex set, the proximation point is the closest point
of the set. -/
theorem prox_indicator_isClosestPoint
    {C : Set E} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (z : E) :
    prox (δ[ℝ](· | C) : E → WithBotTop ℝ)
        (indicatorFunction_isClosedProperConvex_of_nonempty hC_nonempty hC_closed hC_convex) z ∈
      C ∧
      IsMinOn (fun x : E ↦ ‖z - x‖) C
        (prox (δ[ℝ](· | C) : E → WithBotTop ℝ)
          (indicatorFunction_isClosedProperConvex_of_nonempty hC_nonempty hC_closed hC_convex)
          z) := sorry

end Function

-- Proof sketch: specialize the Moreau decomposition theorem to the indicator of `K`. Theorem 14.1
-- identifies the conjugate with the indicator of `Kᵒ`, so the two proximation points belong to
-- `K` and `Kᵒ`; the subgradient characterization of Theorem 31.5 yields the complementary
-- slackness condition `⟪x, xStar⟫ = 0`.
/-- For the indicator of a nonempty closed convex cone `K`, every `z` has a unique decomposition
`z = x + xStar` with `x ∈ K`, `xStar ∈ Kᵒ[ℝ]`, and `⟪x, xStar⟫ = 0`. -/
theorem existsUnique_cone_polar_decomposition
    {K : Set E} (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK : Set.IsConvexCone ℝ K)
    (z : E) :
    ∃! p : E × E,
      z = p.1 + p.2 ∧
        p.1 ∈ K ∧
        p.2 ∈ Kᵒ[ℝ] ∧
        ⟪p.1, p.2⟫ = (0 : ℝ) := sorry

section FiniteDimensional

variable [FiniteDimensional ℝ E]

-- Proof sketch: apply the cone/polar decomposition theorem to the subspace `L`, then rewrite its
-- polar cone by `Submodule.polarCone_eq_orthogonal`. The resulting pair is exactly the orthogonal
-- decomposition of `z` with respect to `L`.
/-- For a subspace `L`, the cone/polar decomposition from Remark 31.5.1 becomes the orthogonal
decomposition of `z` into a component of `L` and a component of `Lᗮ`. -/
theorem existsUnique_submodule_orthogonal_decomposition
    (L : Submodule ℝ E) (z : E) :
    ∃! p : E × E,
      z = p.1 + p.2 ∧
        p.1 ∈ L ∧
        p.2 ∈ L.orthogonal := sorry

end FiniteDimensional

end
