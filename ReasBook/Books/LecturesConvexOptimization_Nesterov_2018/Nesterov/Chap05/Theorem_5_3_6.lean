import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap01.Definition_1_3_3
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_0_18
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_3_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Theorem_5_1_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin ConvexAnalysis

noncomputable section

universe u₁ u₂

variable {E₁ : Type u₁} {E₂ : Type u₂}
variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

local notation "Z" => WithLp 2 (E₁ × E₂)

/- Theorem 5.3.6 lies in the chapter's self-concordant-barrier / partial-minimization domain.

Sampled owner-style declarations in this domain:
- `partialInfProjection` in `Chap03/Theorem_3_1_2_3`, the chapter owner for constrained
  fiberwise infima;
- `extendedRealRealPart` and
  `extendedRealRealPart_partialInfProjection_eq_sInf_image` in `Definition_5_0_18`, the
  canonical real surface of that owner on its finite-value domain;
- `argmin[Q] f` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project owner
  for chosen constrained minimizers;
- the frozen-slice Hessian `hessian (Φ ∘ Prod.mk x) (y x)` and
  `partialMinimizationObjective_isSelfConcordantOnWith` in `Theorem_5_1_11`, the chapter bridge
  and owner theorem for self-concordance of the partial minimization objective;
- mathlib `WithLp 2 (E₁ × E₂)` together with `z ↦ z.ofLp`, the canonical ambient `L²` product
  owner for the barrier data on `E₁ × E₂`;
- `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the Chapter 5 owner for quantitative
  self-concordant barriers.

Best owner abstraction:
- source-facing: the partial-minimization barrier obtained from minimizing `Φ (x, ·)` on the
  feasible fiber above `x`;
- core/canonical: `partialInfProjection Q (Real.toEReal ∘ Φ)` together with its real surface
  `extendedRealRealPart` on `dom`, plus the ambient barrier owner
  `IsSelfConcordantBarrierOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' Q) ν
    (Φ ∘ WithLp.ofLp)`;
- bridge/view: the fiberwise minimizer selection
  `y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x)` together with evaluation of the frozen-slice
  Hessian `hessian (Φ ∘ Prod.mk x) (y x)` at the minimizer.

Primitive data:
- the feasible set `Q : Set (E₁ × E₂)`;
- the barrier objective `Φ : E₁ × E₂ → ℝ`;
- the minimizing branch `y : E₁ → E₂`;
- the ambient barrier owner witness
  `hΦ : IsSelfConcordantBarrierOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' Q) ν
    (Φ ∘ WithLp.ofLp)`;
- the pointwise positive-definite frozen-slice `yy` Hessian hypothesis on
  `hessian (Φ ∘ Prod.mk x) (y x)`.

Derived API:
- the natural domain `dom (partialInfProjection Q (Real.toEReal ∘ Φ))`;
- the real-valued partial-minimization objective
  `extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))`.

Source/core/bridge triage:
- source-facing: Theorem 5.3.6 and its barrier conclusion for the partial minimization objective;
- core/canonical: `partialInfProjection`, `extendedRealRealPart`, and
  `IsSelfConcordantBarrierOnWith`;
- bridge/view: the canonical fiberwise `argmin` owner and the chosen evaluation point `y x` for
  the frozen slice.

This refinement deletes the local fiber/domain/value-function wrappers and states the theorem
directly on the existing Chapter 3 and Chapter 5 owner surface. It keeps only the source-faithful
extra bridge data not already packaged by the barrier owner: the chosen fiber minimizer and the
positive-definite frozen-slice `yy` Hessian hypothesis needed by the chapter's canonical
partial-minimization self-concordance theorem. -/

-- Proof sketch: first apply the Chapter 5 owner theorem
-- `partialMinimizationObjective_isSelfConcordantOnWith` to the canonical infimal-projection owner
-- surface. The needed interior-attainment hypothesis is derived from `hy_argmin` together with
-- openness of `Q`, supplied by the barrier owner, while the nondegeneracy input is kept as the
-- explicit frozen-slice Hessian hypothesis. Then combine that self-concordance
-- result with the barrier-parameter inequality inherited from the ambient barrier on `Q` to
-- obtain the barrier conclusion for the partial infimal projection with the same parameter `ν`.
section PartialMinimizationBarrier

variable {Q : Set (E₁ × E₂)} {ν : NNReal} {Φ : E₁ × E₂ → ℝ} {y : E₁ → E₂}

local notation "QZ" => ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' Q)
local notation "ψ" => partialInfProjection Q (Real.toEReal ∘ Φ)
local notation "D" => dom ψ
local notation "f" => extendedRealRealPart ψ

/-- Theorem 5.3.6: if `Φ` is a `ν`-self-concordant barrier on `Q ⊆ E₁ × E₂`, and if for every
`x ∈ D`, where `D = dom (partialInfProjection Q (Real.toEReal ∘ Φ))`, the explicit barrier
witness `hΦ` on `Q` is given, the fiber problem `min_y Φ(x, y)` over `(Prod.mk x) ⁻¹' Q` is
attained at `y x`, and the frozen-slice `yy` Hessian there is positive definite, then the
canonical real surface of the partial infimal projection is a `ν`-self-concordant barrier on its
natural domain. -/
theorem partialMinimizationObjective_isSelfConcordantBarrierOnWith_of_argmin
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp))
    (hy_argmin : ∀ ⦃x : E₁⦄, x ∈ D → y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hyy_pos : ∀ ⦃x : E₁⦄, x ∈ D → ∀ v : E₂, v ≠ 0 →
        0 < inner ℝ v ((hessian (Φ ∘ Prod.mk x) (y x)) v)) :
    IsSelfConcordantBarrierOnWith D ν f := by
  letI : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp) := hΦ
  sorry

end PartialMinimizationBarrier

end
