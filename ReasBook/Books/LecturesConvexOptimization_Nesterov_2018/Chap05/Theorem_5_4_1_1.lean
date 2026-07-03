import Mathlib
import Nesterov.Chap05.Lemma_5_4_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.4.1.1 lies in the Chapter 5 self-concordant-barrier / no-affine-line domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for the
  self-concordant barrier on an open convex domain;
* `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap` from `Theorem_5_3_3`, the canonical
  owner-level affine pullback of the self-concordant-with-parameter data;
* `IsSelfConcordantOn.hasPositiveDefiniteHessianOn_of_no_affine_line` from `Theorem_5_1_6`,
  together with `HasPositiveDefiniteHessianOn.posdef` from `Definition_5_0_23`, the chapter
  owner-level positivity bridge for the no-affine-line hypothesis on a domain;
* `scalarBarrierInterval` from `Lemma_5_4_1_1`, the source-facing scalar interval owner used for
  the one-dimensional reduction;
* `selfConcordantBarrier_one_le_kappa_and_kappa_le_parameter` from `Lemma_5_4_1_1`, the canonical
  scalar owner theorem already proving the lower and upper bounds on the textbook ratio `κ`.

Best owner abstraction:
* source-facing: the lower bound `1 ≤ ν` for a `ν`-self-concordant barrier on `interior Q`
  once that domain is nonempty and contains no affine line;
* core/canonical: the pair `IsSelfConcordantBarrierOnWith dom ν F` and the no-affine-line owner
  `∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom`;
* bridge/view: identifying the line preimage of `interior Q` with a scalar interval
  `scalarBarrierInterval α β`.

Primitive data:
* the nonempty open domain `dom`;
* the no-affine-line hypothesis on `dom`;
* the self-concordant barrier owner `IsSelfConcordantBarrierOnWith dom ν F`.

Derived API:
* a continuous affine line map `g : ℝ →ᴬ[ℝ] E`;
* the pulled-back scalar self-concordant barrier owner for `F ∘ g`;
* the scalar interval presentation of `g ⁻¹' interior Q`;
* the scalar lower bound `1 ≤ ν`, reused directly from the imported scalar owner theorem.

The previous revision was semantically too weak: nonempty interior together with the relative
barrier and self-concordant-barrier owners still allows affine-line domains such as `Set.univ`.
The refined theorem therefore keeps the canonical self-concordant-barrier owner and adds the
missing no-affine-line hypothesis on the same domain. Its core statement now lives directly at the
owner level on an arbitrary domain `dom`, while the original `interior Q` formulation is retained
only as a thin source-facing bridge. -/

-- Proof sketch: choose a point `x ∈ interior Q` and a nonzero direction through `x`. The
-- no-affine-line hypothesis on `interior Q` forces the line slice to leave the domain, so the
-- preimage of `interior Q` along the corresponding continuous affine line map
-- `g : ℝ →ᴬ[ℝ] E` is a nonempty scalar interval `scalarBarrierInterval α β` with finite upper
-- endpoint. Pull back the self-concordant-barrier owner along `g` using
-- `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap`.
private theorem exists_scalarBarrierInterval_affinePullback
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hdom : dom.Nonempty)
    (hdom_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom)
    (hself : IsSelfConcordantBarrierOnWith dom ν F) :
    ∃ (α : WithBot ℝ) (β : ℝ) (g : ℝ →ᴬ[ℝ] E),
      Set.Nonempty (scalarBarrierInterval α β) ∧
        IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν (F ∘ g) := by
  sorry

namespace IsSelfConcordantBarrierOnWith

-- Proof sketch: reduce along an affine line to a nonempty scalar interval. The pulled-back
-- function is still a `ν`-self-concordant barrier there, so the imported scalar owner theorem
-- `selfConcordantBarrier_one_le_kappa_and_kappa_le_parameter` yields `1 ≤ ν`.
/-- Theorem 5.4.1.1, owner-level form: if `dom` is nonempty, contains no affine line, and `F`
is a `ν`-self-concordant barrier on `dom`, then the barrier parameter satisfies `ν ≥ 1`. -/
theorem one_le_parameter_of_nonempty_no_affine_line
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hself : IsSelfConcordantBarrierOnWith dom ν F)
    (hdom : dom.Nonempty)
    (hdom_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom) :
    1 ≤ ν := by
  obtain ⟨α, β, g, hI, hsliceSelf⟩ :=
    exists_scalarBarrierInterval_affinePullback hdom hdom_noAffineLine hself
  have hκ :
      1 ≤ selfConcordantBarrierKappa α β (F ∘ g) ∧
        selfConcordantBarrierKappa α β (F ∘ g) ≤ (ν : ℝ) :=
    selfConcordantBarrier_one_le_kappa_and_kappa_le_parameter hI hsliceSelf
  have hν : (1 : ℝ) ≤ (ν : ℝ) :=
    hκ.1.trans hκ.2
  exact_mod_cast hν

end IsSelfConcordantBarrierOnWith

-- The owner theorem above already matches the mathematical content. The original textbook
-- `interior Q` phrasing is just its source-facing specialization.
/-- Theorem 5.4.1.1: if `Q ⊆ E` has nonempty interior, `interior Q` contains no affine line, and
`F` is a `ν`-self-concordant barrier on `interior Q`, then the barrier parameter satisfies
`ν ≥ 1`. -/
theorem one_le_selfConcordantBarrierParameter_of_nonempty_interior
    {Q : Set E} {ν : NNReal} {F : E → ℝ}
    (hQ : (interior Q).Nonempty)
    (hQ_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ interior Q)
    (hself : IsSelfConcordantBarrierOnWith (interior Q) ν F) :
    1 ≤ ν :=
  hself.one_le_parameter_of_nonempty_no_affine_line hQ hQ_noAffineLine

end
