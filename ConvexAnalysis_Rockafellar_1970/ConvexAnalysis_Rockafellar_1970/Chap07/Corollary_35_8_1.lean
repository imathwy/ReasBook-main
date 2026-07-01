import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_25_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem_35_8

noncomputable section

open scoped Rockafellar Topology
open Function

universe u v

namespace Bifunction

section

variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [NormedSpace ℝ U]
variable [SeminormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]

/-!
Source/core/bridge triage:

- `source-facing`: this corollary characterizes differentiability of the finite real branch of a
  concave-convex saddle-function at an interior point of the saddle effective domain by linearity
  of the mixed directional derivative, and then gives the corresponding basis-line criterion and
  its product-coordinate-line specialization under that same interior-domain hypothesis.
- `core/canonical`: the surrounding chapter already owns the relevant notions as
  `DifferentiableAt ℝ (uncurry K).realBranch (u, v)`,
  `directionalDerivativeAt (uncurry K) (u, v)`, the Chapter 25 owner
  `(uncurry K).HasLinearDirectionalDerivativeAt (u, v)`, the product-space basis owner
  `Module.Basis ι ℝ (U × V)`, and the Chapter 34/35 domain owner `dom K`.
- `bridge/view`: the source wording “finite on a neighborhood of `(u, v)`” is canonically rendered
  by the owner condition `(u, v) ∈ interior (dom K)`, while the source wording “the directional
  derivative function is linear” is rendered directly by the canonical Chapter 25 owner on the
  product directional derivative. The coordinate-line version is a specialization through the
  canonical product basis `bU.prod bV`.

Domain-style sampling used here:

- `Module.Basis.prod` from mathlib for the owner-level product basis on `U × V`;
- `Function.differentiableAt_iff_hasLinearDirectionalDerivativeAt` from
  `Chap05.Theorem_25_2`;
- `Bifunction.differentiableAt_uncurry_iff_existsUnique_mem_subdifferentialAt` and
  `Bifunction.subdifferentialAt_eq_prod_singleton_fderiv_of_differentiableAt`
  from `Chap07.Theorem_35_8`;
- `Function.directionalDerivativeAt` from `Chap05.Lemma_23_0_1`;
- `SaddleFunction.dom` and `SaddleFunction.mem_interior_dom` from
  `Chap07.Defn_34_3` / `Chap07.Text_35_5_5`;
- `SaddleFunction.bot_lt_and_lt_top_of_mem_dom` from `Chap07.Text_34_1_6`.

Primitive data vs derived API:

- primitive source data: the concave-convex saddle-function `K`, the point `(u, v)`, and the
  local-finiteness owner hypothesis `(u, v) ∈ interior (dom K)`;
- primitive ambient assumptions: finite-dimensionality of each factor space `U` and `V`;
- primitive bridge data for the sufficient criterion: a basis `b : Module.Basis ι ℝ (U × V)` and
  line differentiability of `(uncurry K).realBranch` at `(u, v)` along each `b i`;
- derived API: the interior-point differentiability criterion and the coordinate-line sufficient
  condition obtained from `Module.Basis.prod`.

Layer target: `source-facing`, stated directly on the canonical Chapter 25/35 owners.
-/

-- Proof sketch: the interior-domain hypothesis is the chapter owner for Rockafellar's local
-- finiteness hypothesis, so it replaces the incorrect attempt to infer interiority from
-- differentiability of the totalized branch `realBranch`. Use interiority to recover the finite
-- point data needed for Theorem 35.8, then combine Theorem 35.8 with the Chapter 25 criterion on
-- the product real branch.
/-- Corollary 35.8.1: at an interior point of the effective domain of a concave-convex
saddle-function `K`, the finite real branch `(uncurry K).realBranch` is differentiable if and
only if the mixed directional-derivative owner
`d ↦ directionalDerivativeAt (uncurry K) (u, v) d` is linear in Rockafellar's Chapter 25 sense,
i.e. `(uncurry K).HasLinearDirectionalDerivativeAt (u, v)`. -/
theorem differentiableAt_realBranch_uncurry_iff_hasLinearDirectionalDerivativeAt_of_mem_interior_dom
    {K : U → V → WithBotTop ℝ} (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    {u : U} {v : V} (huv : (u, v) ∈ interior (dom K)) :
    DifferentiableAt ℝ (uncurry K).realBranch (u, v) ↔
      (uncurry K).HasLinearDirectionalDerivativeAt (u, v) := sorry

end

section

variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [NormedSpace ℝ U]
variable [SeminormedAddCommGroup V] [NormedSpace ℝ V]

-- Proof sketch: keep the local-finiteness owner `(u, v) ∈ interior (dom K)` explicit, since
-- line differentiability of the totalized branch `realBranch` does not force interiority of
-- `dom K`. A finite basis of `U × V` supplies the coordinate data and the needed
-- finite-dimensionality locally for linearity of the mixed directional-derivative owner.
/-- Basis-line criterion: at an interior point `(u, v)` of `dom K`, if the finite real branch is
line-differentiable along every vector of a finite basis of the product space `U × V`, then the
mixed directional derivative is linear at `(u, v)`. -/
theorem hasLinearDirectionalDerivativeAt_of_mem_interior_dom_of_lineDifferentiableAt_basis
    {ι : Type*} [Finite ι]
    {K : U → V → WithBotTop ℝ}
    (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    {u : U} {v : V} (huv : (u, v) ∈ interior (dom K))
    (b : Module.Basis ι ℝ (U × V))
    (hline : ∀ i : ι, LineDifferentiableAt ℝ (uncurry K).realBranch (u, v) (b i)) :
    (uncurry K).HasLinearDirectionalDerivativeAt (u, v) :=
  sorry

-- Proof sketch: apply the basis-line theorem to the canonical product basis `bU.prod bV`; the
-- first-variable and second-variable coordinate hypotheses are exactly the `Sum.inl` and
-- `Sum.inr` cases.
/-- Product-coordinate-line criterion: at an interior point `(u, v)` of `dom K`, if the finite
real branch is line-differentiable along all directions `(bU i, 0)` and `(0, bV j)` from finite
bases `bU`, `bV`, then the mixed directional derivative is linear at `(u, v)`. -/
theorem hasLinearDirectionalDerivativeAt_of_mem_interior_dom_of_coordLineDifferentiableAt
    {ιU : Type*} [Finite ιU] {ιV : Type*} [Finite ιV]
    {K : U → V → WithBotTop ℝ}
    (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    {u : U} {v : V} (huv : (u, v) ∈ interior (dom K))
    (bU : Module.Basis ιU ℝ U) (bV : Module.Basis ιV ℝ V)
    (hpartial₁ :
      ∀ i : ιU, LineDifferentiableAt ℝ (uncurry K).realBranch (u, v) (bU i, 0))
    (hpartial₂ :
      ∀ j : ιV, LineDifferentiableAt ℝ (uncurry K).realBranch (u, v) (0, bV j)) :
    (uncurry K).HasLinearDirectionalDerivativeAt (u, v) :=
  hasLinearDirectionalDerivativeAt_of_mem_interior_dom_of_lineDifferentiableAt_basis
    hK_shape huv (bU.prod bV)
      (fun ij ↦ by
        cases ij
        · rename_i i
          simpa [Module.Basis.prod_apply, Function.comp] using hpartial₁ i
        · rename_i j
          simpa [Module.Basis.prod_apply, Function.comp] using hpartial₂ j)

end

end Bifunction
