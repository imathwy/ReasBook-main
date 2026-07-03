import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_5_4_1_1 (from Chap05) -/
noncomputable section

open scoped Gradient

/- Lemma 5.4.1.1 lies in the scalar self-concordant-barrier domain.

Relevant owner-style declarations sampled before refinement:
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for a
  `ν`-self-concordant barrier on a domain;
* `_root_.barrier_parameter_bound_iff_gradient_inner_sq_le` in `Proposition_5_3_3`, the
  canonical pointwise bridge turning the barrier inequality into a squared
  gradient / local-norm estimate;
* `IsBarrierFunctionOn` in `Chap01/Definition_1_10_18`, the canonical frontier-blow-up owner
  needed for the source-faithful lower bound `1 ≤ κ`;
* `gradient_eq_deriv'` in mathlib, the one-dimensional bridge from the Euclidean gradient to the
  usual derivative.

Best owner abstraction:
* source-facing: the scalar interval barrier statement itself, namely
  `1 ≤ κ ≤ ν` for `κ = sup_t (f'(t))^2 / f''(t)`;
* core/canonical: `IsSelfConcordantBarrierOnWith I ν f` together with
  `_root_.barrier_parameter_bound_iff_gradient_inner_sq_le`;
* bridge/view: the ratio supremum `κ`, derived from the barrier owner rather than introduced with
  separate frontier-growth data.

Primitive data:
* the interval domain `I = {t : ℝ | α < (t : WithBot ℝ) ∧ t < β}`;
* interval nonemptiness when the lower bound `1 ≤ κ` is asserted;
* the barrier owner `IsSelfConcordantBarrierOnWith I ν f`.

Derived API:
* the pointwise inequality `(f'(t))^2 ≤ ν ‖1‖[f; t]^2`, then its scalar second-derivative
  reformulation `(f'(t))^2 ≤ ν f''(t)`;
* the barrier-derived positivity bridge `0 < f''(t)` on the interval;
* the ratio owner `selfConcordantBarrierRatio α β f t` and its supremum
  `selfConcordantBarrierKappa α β f`;
* the canonical barrier-function owner on `closure I`, derived from the barrier owner together with
  interval nonemptiness;
* the supremum ratio bounds on `κ`, with Hessian positivity and frontier blow-up recovered from
  the owner hypotheses.
-/

section

variable {α : WithBot ℝ} {β : ℝ}

/-- The scalar open interval `(\alpha, \beta)` used in Lemma 5.4.1.1. The lower endpoint is
allowed to be `-∞`, matching the source half-line variants. -/
abbrev scalarBarrierInterval (α : WithBot ℝ) (β : ℝ) : Set ℝ :=
  {t : ℝ | α < (t : WithBot ℝ) ∧ t < β}

-- Proof sketch: specialize
-- `_root_.barrier_parameter_bound_iff_gradient_inner_sq_le` to the scalar
-- interval owner `hself` at the point `t` and to the direction `u = 1`. On `ℝ`, the gradient is
-- the ordinary derivative, and `hessianLocalNorm_def` together with `Real.sq_sqrt` rewrites
-- `‖1‖[f; t]^2` as the second derivative. The owner inequality therefore becomes
-- `(f'(t))^2 ≤ ν f''(t)`.
/-- The canonical scalar specialization of the barrier-parameter owner inequality:
for every `t ∈ (\alpha, \beta)`, a `ν`-self-concordant barrier satisfies
`(f'(t))^2 ≤ ν f''(t)`. This is the core owner statement behind the textbook ratio `κ`. -/
theorem selfConcordantBarrier_deriv_sq_le_parameter_mul_secondDeriv
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f)
    (t : scalarBarrierInterval α β) :
    deriv f t ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 f t := sorry

-- Proof sketch: the barrier owner supplies the Chapter 1 frontier-blow-up theorem on `closure I`,
-- and `I` contains no affine line because of the finite upper endpoint `β`. Applying the chapter
-- no-affine-line positivity bridge to the scalar direction `1` yields `0 < f''(t)` at every
-- interior point.
/-- On the scalar barrier interval `(\alpha, \beta)`, the second derivative is strictly positive.
This removes the implementation artifact of totalized real division from the source-facing ratio
`κ`. -/
theorem selfConcordantBarrier_secondDeriv_pos
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f)
    (t : scalarBarrierInterval α β) :
    0 < iteratedDeriv 2 f t := sorry

/-- The source-facing scalar barrier ratio at `t`, expressed through the canonical positive
second-derivative theorem supplied by the barrier owner. -/
def selfConcordantBarrierRatio
    (α : WithBot ℝ) (β : ℝ) (f : ℝ → ℝ) (t : scalarBarrierInterval α β) : ℝ :=
  deriv f t ^ (2 : ℕ) / iteratedDeriv 2 f t

/-- Expanding `selfConcordantBarrierRatio α β f t` recovers the textbook scalar formula
`(f'(t))^2 / f''(t)`. -/
@[simp] theorem selfConcordantBarrierRatio_def
    (f : ℝ → ℝ) (t : scalarBarrierInterval α β) :
    selfConcordantBarrierRatio α β f t =
      deriv f t ^ (2 : ℕ) / iteratedDeriv 2 f t :=
  rfl

/-- The source-facing scalar barrier ratio supremum
`κ = sup_{t ∈ (\alpha, \beta)} (f'(t))^2 / f''(t)`. Nonemptiness is only needed for the lower
bound theorem `1 ≤ κ`, not for the owner itself or the upper bound `κ ≤ ν`. -/
def selfConcordantBarrierKappa
    (α : WithBot ℝ) (β : ℝ) (f : ℝ → ℝ) : ℝ :=
  sSup (Set.range (selfConcordantBarrierRatio α β f))

-- Proof sketch: divide
-- `selfConcordantBarrier_deriv_sq_le_parameter_mul_secondDeriv hself t`
-- by the positive scalar `iteratedDeriv 2 f t`.
/-- Every scalar barrier ratio value is bounded above by the barrier parameter. -/
theorem selfConcordantBarrierRatio_le_parameter
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f)
    (t : scalarBarrierInterval α β) :
    selfConcordantBarrierRatio α β f t ≤ (ν : ℝ) := sorry

-- Proof sketch: `κ` is the least upper bound of the pointwise ratio owner
-- `selfConcordantBarrierRatio α β f`.
/-- For a scalar `ν`-self-concordant barrier on `(\alpha, \beta)`, the source-facing ratio
`κ = sup_t (f'(t))^2 / f''(t)` is bounded above by the barrier parameter. -/
theorem selfConcordantBarrierKappa_le_parameter
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f) :
    selfConcordantBarrierKappa α β f ≤ (ν : ℝ) := sorry

-- Proof sketch: from interval nonemptiness, the barrier owner `hself` canonically supplies the
-- frontier-blow-up owner on `closure I`. Combining that barrier growth with the one-dimensional
-- convexity/Hessian positivity consequences of `hself`, the auxiliary ratio owner
-- `selfConcordantBarrierRatio α β f` cannot stay below `1` everywhere, so its supremum is at
-- least `1`.
/-- If `(\alpha, \beta)` is nonempty and `f` is a scalar `ν`-self-concordant barrier on it, then
the source-facing ratio supremum satisfies `1 ≤ κ`.

The frontier-growth and positivity input are derived from the barrier owner rather than passed as
separate public hypotheses. -/
theorem one_le_selfConcordantBarrierKappa
    {ν : NNReal} {f : ℝ → ℝ}
    (hI : Set.Nonempty (scalarBarrierInterval α β))
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f) :
    1 ≤ selfConcordantBarrierKappa α β f := sorry

/-- Lemma 5.4.1.1: for a scalar `ν`-self-concordant barrier on `(\alpha, \beta)`,
the barrier parameter dominates `κ = sup_t (f'(t))^2 / f''(t)`, and for a nonempty interval this
supremum is at least `1`. Both assertions are expressed directly at the scalar barrier owner
surface. -/
theorem selfConcordantBarrier_one_le_kappa_and_kappa_le_parameter
    {ν : NNReal} {f : ℝ → ℝ}
    (hI : Set.Nonempty (scalarBarrierInterval α β))
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f) :
    1 ≤ selfConcordantBarrierKappa α β f ∧
      selfConcordantBarrierKappa α β f ≤ (ν : ℝ) := sorry

end

end

/-! ### Theorem_5_4_1_1 (from Chap05) -/
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

/-! ### Theorem_5_4_1_2 (from Chap05) -/
open scoped BigOperators

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.4.1.2 lies in the Chapter 5 self-concordant-barrier / recession-direction domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for a
  `ν`-self-concordant barrier;
* `IsSelfConcordantBarrierOnWith.hessianLocalNorm_le_neg_gradient_inner_of_recession_direction`
  in `Corollary_5_3_2`, the owner-level recession-direction estimate used for each `p i`;
* `hessianLocalNorm` and the notation `‖u‖[F; x]` in `Definition_5_1_1`, the canonical Chapter 5
  owner for the Hessian local norm;
* the project’s generic finite-family pattern, for example `Theorem_3_38`, where a finite sum
  lives over `ι : Type*` with `[Fintype ι]` instead of the display model `Fin k`.

Source/core/bridge triage:
* source-facing: the textbook lower bound `∑ i, αᵢ / βᵢ ≤ ν`;
* core/canonical: `IsSelfConcordantBarrierOnWith (interior Q) ν F`;
* bridge/view: the recession-direction lower bounds for each `p i` and the combined gradient
  estimate at `xBar`.

Primitive data:
* the barrier owner `hF : IsSelfConcordantBarrierOnWith (interior Q) ν F`;
* the convex set `Q`, base point `xBar ∈ interior Q`, and recession directions `p i`;
* the finite index owner `[Fintype ι]`, since the theorem uses only finite summation and no order
  or adjacency on the indices;
* the nonnegative scalars `α i`, the positive scalars `β i`, the backward-exit hypotheses, and
  the final point
  `xBar - ∑ i, α i • p i ∈ Q`.

Derived API:
* for each `i`, the owner-level recession-direction estimate
  `1 / β i ≤ ‖p i‖[F; xBar] ≤ ⟪-∇ F xBar, p i⟫`;
* the summed source-facing inequality `∑ i, α i / β i ≤ ν`.

The previous file fixed the ambient space to `EuclideanSpace ℝ (Fin n)` and the finite family to
`Fin k` even though the theorem uses only the real inner-product-space barrier owner and finite
summation. The refined statement keeps the same mathematical semantics while moving the public
surface to the canonical owner namespace, deleting the unnecessary concrete model layer, and
placing the finite family at the generic `[Fintype ι]` owner level. -/

namespace IsSelfConcordantBarrierOnWith

-- Proof sketch: for each recession direction `p i`, apply the recession-direction gradient bound
-- for self-concordant barriers at `xBar` together with the finite backward-step hypothesis
-- `xBar - β i • p i ∉ interior Q` to obtain
-- `1 / β i ≤ ‖p i‖[F; xBar] ≤ ⟪-∇ F xBar, p i⟫`.
-- Then use the basic barrier-parameter inequality with
-- `y = xBar - ∑ i, α i • p i ∈ Q` to get
-- `∑ i α i / β i ≤ ⟪∇ F xBar, xBar - y⟫ ≤ ν`.
/-- Theorem 5.4.1.2: if `Q ⊆ E` is a convex set in a real Hilbert space, `xBar ∈ interior Q`,
`(p i)` is a finite family of recession directions of `Q`, each backward step
`xBar - βᵢ • p i` leaves `interior Q`, and `xBar - ∑ i, α i • p i ∈ Q` for nonnegative scalars
`α i` and positive scalars `β i`, then every `ν`-self-concordant barrier `F` on `interior Q`
satisfies
`∑ i, αᵢ / βᵢ ≤ ν`. -/
theorem barrierParameter_ge_sum_alpha_div_beta_of_recession_directions
    {ι : Type v} [Fintype ι] {Q : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hQ_convex : Convex ℝ Q)
    {xBar : E} (hxBar : xBar ∈ interior Q)
    (p : ι → E)
    (hrecession :
      ∀ i, ∀ ⦃x⦄, x ∈ Q → ∀ t : ℝ, 0 ≤ t → x + t • p i ∈ Q)
    (β α : ι → ℝ)
    (hβ_pos : ∀ i, 0 < β i)
    (hβ_exit : ∀ i, xBar - β i • p i ∉ interior Q)
    (hα_nonneg : ∀ i, 0 ≤ α i)
    (hy : xBar - ∑ i, α i • p i ∈ Q) :
    ∑ i, α i / β i ≤ (ν : ℝ) := sorry

end IsSelfConcordantBarrierOnWith

end

/-! ### Definition_5_4_2_1 (from Chap05) -/
universe u

open scoped PolarSet

/- Definition 5.4.2.1 lies in the chapter's based-polar-set domain.

Sampled declarations before refinement:
- project `polarSet`
- project `mem_polarSet_iff`
- mathlib `StrongDual.polar`
- mathlib `StrongDual.mem_polar_iff`

Best owner abstraction:
- the chapter owner `polarSet`

Primitive data:
- a set `Q`
- a base point `xBar`

Derived API:
- the textbook based polar as the polar of the displacement set `Q -ᵥ {xBar}`

Source/core/bridge triage:
- source-facing: the textbook based polar `P(xBar)`
- core/canonical: `polarSet`
- bridge/view: `polarSetAt`

The strong-dual mathlib polar is not the exact owner here because it uses the absolute-value bound
on continuous linear functionals rather than the one-sided real inner-product inequality from the
chapter. The correct refinement is therefore to keep the chapter owner `polarSet` and express the
based variant as its displacement-set bridge. No extra notation is introduced here: the recurring
owner notation already lives on `Qᵒ`, while the based object is a view depending on `xBar`.
-/

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Definition 5.4.2.1, generalized from the textbook Euclidean setting: the polar set of `Q`
with respect to the base point `xBar` is the chapter polar of the displacement set
`Q -ᵥ ({xBar} : Set E)`. Specializing to `E = EuclideanSpace ℝ (Fin n)` recovers the textbook
definition. -/
abbrev polarSetAt (Q : Set E) (xBar : E) : Set E :=
  (Q -ᵥ ({xBar} : Set E))ᵒ

/-- Membership in `polarSetAt Q xBar` is exactly the defining uniform inner-product inequality over
the displacement vectors from `xBar` to points of `Q`. -/
theorem mem_polarSetAt_iff {Q : Set E} {xBar s : E} :
    s ∈ polarSetAt Q xBar ↔ ∀ x ∈ Q, inner ℝ s (x - xBar) ≤ 1 := by
  rw [polarSetAt, mem_polarSet_iff]
  simp

/-! ### Definition_5_4_2_2 (from Chap05) -/
noncomputable section

open MeasureTheory

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceDefinition5422 : MeasurableSpace E := borel E
local instance instBorelSpaceDefinition5422 : BorelSpace E := ⟨rfl⟩

/- Definition 5.4.2.2 lies in the chapter's based-polar-set / intrinsic volume domain.

Sampled owner-style declarations:
- project `polarSet`
- project `polarSetAt`
- mathlib `MeasureTheory.volume`
- project `volumetricBarrier`

Best owner abstraction:
- the source-facing Chapter 5 owner `universalBarrierVolume`

Primitive data:
- a set `Q : Set E`
- an interior point `x : interior Q`

Derived API:
- the based polar body `polarSetAt Q (x : E)`
- its volume `(volume (polarSetAt Q (x : E))).toReal`

Source/core/bridge triage:
- source-facing: `universalBarrierVolume`
- core/canonical: `polarSetAt` and `MeasureTheory.volume`

Unlike `polarSetAt`, this definition is genuinely new source-facing content: it combines the
chapter's based polar owner with the ambient finite-dimensional real volume owner. There is
therefore no upstream owner to recall directly, so the refined file keeps only this owner and
reuses those canonical ingredients verbatim. Specializing to `E = EuclideanSpace ℝ (Fin n)`
recovers the textbook `ℝⁿ` formulation.
-/

/-- Definition 5.4.2.2, stated at the intrinsic owner level: for an interior point `x` of a set
`Q` in a finite-dimensional real inner-product space, `universalBarrierVolume Q x` is the volume
of the associated based polar body `P(x) = {s | ∀ y ∈ Q, ⟪s, y - x⟫ ≤ 1}`. Specializing to
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook Lebesgue-volume definition on `ℝⁿ`. In the
textbook application, `Q` is later assumed proper and convex. -/
def universalBarrierVolume (Q : Set E) (x : interior Q) : ℝ :=
  (volume (polarSetAt Q x)).toReal

end

/-! ### Theorem_5_4_2_1 (from Chap05) -/
noncomputable section

universe u

/- Theorem 5.4.2.1 lies in the chapter's based-polar-set / finite-dimensional convex-geometry
domain.

Sampled owner-style declarations:
- project `polarSet`
- project `mem_polarSetAt_iff`
- mathlib `NormedSpace.isClosed_polar`
- mathlib `NormedSpace.isBounded_polar_of_mem_nhds_zero`

Best owner abstraction:
- source-facing: the compact-convex conclusion for the based polar body `polarSetAt Q xBar`
- core/canonical: the chapter owner `polarSet`
- bridge/view: the based displacement-set owner `polarSetAt`

Primitive data:
- a set `Q : Set E`
- a base point `xBar : E`
- for compactness and boundedness: `xBar ∈ interior Q`
- for the separate interior-nonemptiness companion: `Convex ℝ Q` together with the chapter
  no-affine-line hypothesis on `Q`

Derived API:
- unconditional closedness and convexity of `polarSetAt Q xBar`
- compactness and boundedness from the interior-point hypothesis
- nonempty interior under the extra source-facing convex/no-affine-line assumptions
- the trivial base-point-free fact `0 ∈ polarSetAt Q xBar`

This theorem file should not be tied to the display model `EuclideanSpace ℝ (Fin n)`: the owner
`polarSetAt` already lives on real inner-product spaces, and the proof sketch only uses finite
dimensionality. The correct public surface is therefore a finite-dimensional real inner-product
space. The owner-level geometry also separates cleanly into two layers: `polarSetAt Q xBar` is
always an intersection of closed convex half-spaces, so its closedness and convexity are
unconditional, while compactness and boundedness use only the interior ball around `xBar`. The
chapter’s convexity and no-affine-line assumptions remain only on the separate interior-nonempty
companion theorem, where they belong.
-/

section RealInnerProduct

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Q : Set E} {xBar : E}

-- Proof sketch: each defining inequality `inner ℝ s (x - xBar) ≤ 1` cuts out a convex
-- half-space, and arbitrary intersections of convex sets are convex.
/-- The based polar set is convex. -/
theorem polarSetAt_convex :
    Convex ℝ (polarSetAt Q xBar) := sorry

-- Proof sketch: each defining inequality `inner ℝ s (x - xBar) ≤ 1` cuts out a closed
-- half-space, and arbitrary intersections of closed sets are closed.
/-- The based polar set is closed. -/
theorem polarSetAt_isClosed :
    IsClosed (polarSetAt Q xBar) := sorry

-- Proof sketch: if `xBar ∈ interior Q`, then some ball around `xBar` lies in `Q`; evaluating the
-- defining inequalities on that ball gives a uniform norm bound on every `s ∈ polarSetAt Q xBar`.
/-- The polar set of an interior point is bounded. -/
theorem polarSetAt_isBounded
    (hxBar : xBar ∈ interior Q) :
    Bornology.IsBounded (polarSetAt Q xBar) := sorry

-- Proof sketch: for every `x ∈ Q`, the defining inequality for `polarSetAt Q xBar` at `s = 0`
-- reduces to `0 ≤ 1`.
/-- The origin belongs to every polar set. -/
theorem zero_mem_polarSetAt {Q : Set E} {xBar : E} :
    (0 : E) ∈ polarSetAt Q xBar := by
  rw [polarSetAt, mem_polarSet_iff]
  intro x hx
  simp

end RealInnerProduct

section FiniteDimensionalReal

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {Q : Set E} {xBar : E}

-- Proof sketch: `polarSetAt Q xBar` is convex unconditionally. If `xBar ∈ interior Q`, the
-- interior ball around `xBar` gives boundedness, and in finite-dimensional real inner-product
-- space boundedness plus closedness gives compactness by Heine-Borel.
/-- Theorem 5.4.2.1, at the intrinsic owner level: if `xBar` is an interior point of `Q`, then
the based polar set `P(xBar) = polarSetAt Q xBar` is compact and convex. The textbook convexity
and no-affine-line assumptions are redundant for this conclusion. -/
theorem polarSetAt_isCompact_convex
    (hxBar : xBar ∈ interior Q) :
    IsCompact (polarSetAt Q xBar) ∧ Convex ℝ (polarSetAt Q xBar) := sorry

-- Proof sketch: use the interior ball around `xBar` together with the absence of affine lines in
-- `Q` to show that a small Euclidean ball around the origin satisfies the defining inequalities of
-- `polarSetAt Q xBar`.
/-- The polar set of an interior point has nonempty interior. -/
theorem polarSetAt_interior_nonempty
    (hQ_convex : Convex ℝ Q)
    (hQ_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q)
    (hxBar : xBar ∈ interior Q) :
    (interior (polarSetAt Q xBar)).Nonempty := sorry

end FiniteDimensionalReal

end

/-! ### Theorem_5_4_2_2 (from Chap05) -/
open scoped Gradient

noncomputable section

/-- Classical decidability for propositions, used to evaluate the interior-membership branch in
`universalBarrierAmbient`. -/
local instance {p : Prop} : Decidable p := Classical.propDecidable p

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 5.4.2.2 lies in the chapter's universal-barrier / finite-dimensional convex-geometry
domain.

Sampled owner-style declarations:
* `universalBarrierVolume` from `Definition_5_4_2_2`, the source-facing owner of the volume term
  `V(x)`;
* `polarSetAt` and `mem_polarSetAt_iff` from `Definition_5_4_2_1`, the geometric owner behind
  that volume term;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for self-concordant
  barriers on open convex domains;
* `polarSetAt_isCompact_convex` from `Theorem_5_4_2_1`, the preceding subsection's intrinsic
  finite-dimensional geometry theorem for the same based-polar construction.

Best owner abstraction:
* source-facing: the intrinsic universal barrier
  `universalBarrier c₁ Q : interior Q → ℝ`;
* core/canonical: `universalBarrierVolume Q x` together with
  `IsSelfConcordantBarrierOnWith (interior Q) ν F`;
* bridge/view: the ambient totalization
  `universalBarrierAmbient c₁ Q : E → ℝ`, used only to feed the Chapter 5 barrier owner.

Primitive data:
* a finite-dimensional real inner-product space `E`;
* a set `Q : Set E`;
* the proper-convex regime on `Q`: convexity together with the absence of affine lines;
* a scaling constant `c₁`.

Derived API:
* the positivity bridge `universalBarrierVolume_pos`;
* the intrinsic barrier owner
  `universalBarrier c₁ Q : interior Q → ℝ`;
* the source-facing identity `universalBarrier_eq_log_volume`;
* the ambient bridge `universalBarrierAmbient c₁ Q : E → ℝ`;
* the Chapter 5 barrier owner
  `IsSelfConcordantBarrierOnWith (interior Q) ν (universalBarrierAmbient c₁ Q)`;
* the intrinsic dimension factor `Module.finrank ℝ E`, which recovers the textbook dimension `n`
  on `EuclideanSpace ℝ (Fin n)`.

The previous version unnecessarily fixed the ambient space to `EuclideanSpace ℝ (Fin n)`. The
based-polar volume owner and the source formula `x ↦ c₁ log V(x)` are already intrinsic, so the
refined file keeps the same source mathematics while moving the public API to the canonical
finite-dimensional real inner-product owner level. The proper-convex/no-affine-line hypotheses are
kept only on the positivity bridge `universalBarrierVolume_pos` and on the final
self-concordance theorem, where they actually matter; the owner itself is just the source formula
`x ↦ c₁ log V(x)`. The ambient zero-extension is retained only as a thin bridge because
`IsSelfConcordantBarrierOnWith` is formulated for ambient maps `E → ℝ`. The theorem-level
positive constants are exposed on the canonical `NNRealˣ` surface rather than as ad hoc
positive-real subtypes. The main theorem still drops the redundant nonempty-interior and
positive-dimensional guards: the owner-level conclusion is already vacuous when `interior Q = ∅`
or `Module.finrank ℝ E = 0`, so those source-mirroring hypotheses do not belong in the public
API.
-/

-- Proof sketch: by Theorem 5.4.2.1 the based polar `polarSetAt Q x` is compact and has nonempty
-- interior under the proper-convex/no-affine-line hypotheses, so its finite-dimensional volume is
-- strictly positive.
/-- For a proper convex set `Q`, every interior based-polar body has strictly positive volume. This
positivity is the bridge that makes `log (universalBarrierVolume Q x)` the actual universal-barrier
formula rather than Lean's junk-value extension outside the proper-convex regime. -/
theorem universalBarrierVolume_pos
    (Q : Set E)
    (hQ_convex : Convex ℝ Q)
    (hQ_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q)
    (x : interior Q) :
    0 < universalBarrierVolume Q x := sorry

/-- The universal barrier attached to a proper convex set `Q` with scaling constant `c₁`, defined
on `interior Q` by the textbook formula `x ↦ c₁ * log V(x)`. Specializing to
`E = EuclideanSpace ℝ (Fin n)` recovers the usual `ℝⁿ` formula. -/
def universalBarrier
    (c₁ : ℝ) (Q : Set E) :
    interior Q → ℝ :=
  fun x ↦ c₁ * Real.log (universalBarrierVolume Q x)

/- Evaluating `universalBarrier c₁ Q` gives the scaled logarithm of
`universalBarrierVolume Q`. -/
@[simp] theorem universalBarrier_eq_log_volume
    (c₁ : ℝ) (Q : Set E) (x : interior Q) :
    universalBarrier c₁ Q x =
      c₁ * Real.log (universalBarrierVolume Q x) := by
  simp [universalBarrier]

/-- The ambient zero-extension of `universalBarrier c₁ Q`, used only to
state the Chapter 5 self-concordant-barrier owner on the open set `interior Q`. -/
def universalBarrierAmbient
    (c₁ : ℝ) (Q : Set E) :
    E → ℝ :=
  fun x ↦
    if hx : x ∈ interior Q then
      universalBarrier c₁ Q ⟨x, hx⟩
    else
      0

/- On interior points of `Q`, the ambient bridge
`universalBarrierAmbient c₁ Q` agrees with the intrinsic owner `universalBarrier c₁ Q`. -/
@[simp] theorem universalBarrierAmbient_eq_universalBarrier
    {c₁ : ℝ} {Q : Set E} {x : E} (hx : x ∈ interior Q) :
    universalBarrierAmbient c₁ Q x = universalBarrier c₁ Q ⟨x, hx⟩ := by
  simp [universalBarrierAmbient, hx]

-- Proof sketch: use the universal-barrier volume definition from Definition 5.4.2.2 and the
-- sharp one-dimensional marginal moment inequalities from the preceding subsection. These yield
-- standard self-concordance for `x ↦ c₁ log V(x)` on `interior Q` together with the barrier
-- gradient bound of order `n`, uniformly for absolute positive constants `c₁` and `c₂`. The
-- intrinsic formulation expresses this parameter as `c₂ * Module.finrank ℝ E`, which
-- specializes to the textbook `c₂ * n` on `EuclideanSpace ℝ (Fin n)`. Empty-interior and
-- zero-dimensional cases are already covered vacuously by the same owner-level statement, so
-- they do not need extra public guards.
/-- Theorem 5.4.2.2, stated with the intrinsic owner and its ambient bridge: there exist absolute
positive constants `c₁` and `c₂` such that for every proper convex set `Q` in a finite-dimensional
real inner-product space `E`, the ambient bridge of the universal barrier
`x ↦ c₁ * log (V(x))` is a `((c₂ : NNReal) * Module.finrank ℝ E)`-self-concordant barrier on
`interior Q`. Specializing to `E = EuclideanSpace ℝ (Fin n)` recovers the textbook
`(c₂ * n)` parameter. The textbook nonempty-interior and `n ≥ 1` regime are the nonvacuous
special cases, but they are redundant for the intrinsic owner-level conclusion itself. -/
theorem exists_absolute_constants_universalBarrier_isSelfConcordantBarrierOnWith :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E}
        (hQ_convex : Convex ℝ Q)
        (hQ_noAffineLine :
          ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q),
        IsSelfConcordantBarrierOnWith (interior Q)
          ((c₂ : NNReal) * Module.finrank ℝ E)
          (universalBarrierAmbient (c₁ : ℝ) Q) := sorry

end

/-! ### Definition_5_4_3_1 (from Chap05) -/
noncomputable section

open scoped EuclideanOrthant

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

/-- Definition 5.4.3.1: for `A ∈ ℝ^{m × n}`, `b ∈ ℝ^m`, and `c ∈ ℝ^n` with `m < n`, the linear
optimization problem with nonnegativity constraints is the minimization of the linear functional
`x ↦ ⟪c, x⟫` over the nonnegative orthant subject to the linear equality constraint `A x = b`. -/
def linearOptimizationProblemWithNonnegativityConstraints
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Eₘ) (c : Eₙ) :
    PrimalEqualityConstrainedProblem Eₙ Eₘ :=
  SetConstrainedMinimizationProblem.toPrimalEqualityConstrainedProblem
    ({ feasibleSet := ℝ₊^n
       objective := fun x ↦ inner ℝ c x } : SetConstrainedMinimizationProblem Eₙ)
    A.toEuclideanLin b

-- Proof sketch: unfold
-- `linearOptimizationProblemWithNonnegativityConstraints`; its ambient feasible set is the Chapter
-- 1 owner `nonnegativeOrthant n`, so membership is exactly coordinatewise nonnegativity.
/-- Membership in the ambient feasible set of the nonnegativity-constrained linear optimization
problem is exactly coordinatewise nonnegativity. -/
@[simp] theorem mem_linearOptimizationProblemWithNonnegativityConstraints_ambientFeasibleSet_iff
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Eₘ) (c : Eₙ) {x : Eₙ} :
    x ∈ (linearOptimizationProblemWithNonnegativityConstraints A b c).feasibleSet ↔
      ∀ i : Fin n, 0 ≤ x i := by
  rw [linearOptimizationProblemWithNonnegativityConstraints]
  simp

-- Proof sketch: the equality-problem owner already packages the intrinsic feasible set
-- `Q ∩ {x | A x = b}` as `equalityFeasibleSet`; expand that owner lemma and rewrite
-- `A.toEuclideanLin x` as the matrix action `A.mulVec x`.
/-- Membership in the equality-feasible set of the nonnegativity-constrained linear optimization
problem is exactly coordinatewise nonnegativity together with the equation `A x = b`. -/
theorem mem_linearOptimizationProblemWithNonnegativityConstraints_equalityFeasibleSet_iff
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Eₘ) (c : Eₙ) {x : Eₙ} :
    x ∈ (linearOptimizationProblemWithNonnegativityConstraints A b c).equalityFeasibleSet ↔
      (∀ i : Fin n, 0 ≤ x i) ∧ A.mulVec x = b := by
  rw [linearOptimizationProblemWithNonnegativityConstraints]
  rw [PrimalEqualityConstrainedProblem.mem_equalityFeasibleSet_iff]
  constructor
  · rintro ⟨hx, hxEq⟩
    exact ⟨by simpa using hx, by
      rw [Matrix.toEuclideanLin, Matrix.toLpLin] at hxEq
      simpa using congrArg WithLp.ofLp hxEq⟩
  · rintro ⟨hx, hxEq⟩
    exact ⟨by simpa using hx, by
      simpa [Matrix.toEuclideanLin, Matrix.toLpLin] using congrArg (WithLp.toLp 2) hxEq⟩

/-- The strict feasible set `{x | A x = b ∧ x ∈ \mathbb{R}^n_{++}}` of the
nonnegativity-constrained linear optimization problem. The objective vector does not enter this
owner because strict feasibility depends only on the constraints. -/
def linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Eₘ) : Set Eₙ :=
  linearEqualityFeasibleSet (ℝ₊₊^n : Set Eₙ) A.toEuclideanLin b

/-- Membership in the strict feasible set of the nonnegativity-constrained linear optimization
problem means satisfying the equality constraint and lying in the strict positive orthant. -/
@[simp] theorem mem_linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet_iff
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Eₘ) {x : Eₙ} :
    x ∈ linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet A b ↔
      A.mulVec x = b ∧ x ∈ ℝ₊₊^n := by
  rw [linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet]
  rw [mem_linearEqualityFeasibleSet_iff]
  constructor
  · rintro ⟨hx, hxEq⟩
    exact ⟨by
      rw [Matrix.toEuclideanLin, Matrix.toLpLin] at hxEq
      simpa using congrArg WithLp.ofLp hxEq, hx⟩
  · rintro ⟨hxEq, hx⟩
    exact ⟨hx, by
      simpa [Matrix.toEuclideanLin, Matrix.toLpLin] using congrArg (WithLp.toLp 2) hxEq⟩

-- Proof sketch: the equality-constrained owner coerces to its objective on the ambient feasible
-- and that objective is defined to be the linear functional `x ↦ ⟪c, x⟫`.
/-- Evaluating the nonnegativity-constrained linear optimization problem returns the inner product
with the cost vector `c`. -/
theorem linearOptimizationProblemWithNonnegativityConstraints_objective_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Eₘ) (c : Eₙ)
    (x : Eₙ) :
    linearOptimizationProblemWithNonnegativityConstraints A b c x = inner ℝ c x := by
  rw [linearOptimizationProblemWithNonnegativityConstraints]
  rfl

end

/-! ### Definition_5_4_3_2 (from Chap05) -/
open scoped BigOperators EuclideanOrthant

noncomputable section

variable (n : ℕ)

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => ℝ₊₊^n

noncomputable local instance : Fintype (Fin n) := Fintype.ofFinite (Fin n)
local instance : CoeFun Xₙ (fun _ ↦ Fin n → ℝ) where
  coe x := fun i ↦ x.1 i

/- Definition 5.4.3.2 lies in the Chapter 1/5 logarithmic-barrier-on-strict-domain domain.

Sampled owner declarations in this domain:
* `EuclideanSpace.positiveOrthant` and `EuclideanSpace.mem_positiveOrthant_iff` from
  `Chap01/Definition_1_10_2`, the intrinsic strict positive orthant owner;
* `strictConstraintSet`, `logarithmicBarrier`, and `logarithmicBarrier_apply` from
  `Chap01/Proposition_1_10_17`, the canonical strict-domain logarithmic-barrier owner for finite
  continuous inequality families;
* `universalBarrier` and `universalBarrierAmbient` from `Chap05/Theorem_5_4_2_2`, the chapter
  owner/ambient-bridge split for barriers on intrinsic open domains;
* `QuadraticallyConstrainedQuadraticOptimizationProblem.epigraphLogarithmicBarrier` and
  `...Ambient` from `Chap05/Definition_5_4_3_5`, the same split for a later Chapter 5
  logarithmic barrier.

Best owner abstraction:
* source-facing: the standard logarithmic barrier on the strict positive orthant
  `positiveOrthant n`;
* core/canonical: `logarithmicBarrier` on the coordinate slack family `x ↦ -x i`;
* bridge/view: the ambient formula `standardLogarithmicBarrierAmbient : Eₙ → ℝ`.

Primitive data:
* the dimension `n`;
* the intrinsic strict positive orthant `positiveOrthant n`.

Derived API:
* the coordinate slack family `positiveOrthantConstraints n`;
* the intrinsic owner `standardLogarithmicBarrier : C(Xₙ, ℝ)`;
* the ambient bridge `standardLogarithmicBarrierAmbient : Eₙ → ℝ`.

The previous version reversed this layering by making the ambient formula the primary owner and by
adding a redundant subtype wrapper. The refined file keeps the source-facing owner on the strict
positive orthant and exposes the ambient formula only as the thin bridge needed by downstream
Chapter 5 barrier APIs. -/

private def positiveOrthantConstraints : Fin n → C(Eₙ, ℝ) :=
  fun i ↦
    { toFun := fun x ↦ -x i
      continuous_toFun := (PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) i).neg }

private theorem positiveOrthant_subset_strictConstraintSet_positiveOrthantConstraints :
    ℝ₊₊^n ⊆ strictConstraintSet (positiveOrthantConstraints n) := by
  intro x hx j
  exact neg_lt_zero.mpr (hx j)

@[simp] private theorem coe_inclusion_positiveOrthantConstraints (x : Xₙ) :
    ((ContinuousMap.inclusion
        (positiveOrthant_subset_strictConstraintSet_positiveOrthantConstraints n)) x :
      Eₙ) = x.1 :=
  rfl

/-- Definition 5.4.3.2: the standard logarithmic barrier for the strict positive orthant
`\mathbb{R}^n_{++}` is the canonical logarithmic barrier on that intrinsic domain. -/
abbrev standardLogarithmicBarrier : C(Xₙ, ℝ) :=
  (logarithmicBarrier (positiveOrthantConstraints n)).comp
    (ContinuousMap.inclusion
      (positiveOrthant_subset_strictConstraintSet_positiveOrthantConstraints n))

-- Proof sketch: unfold `standardLogarithmicBarrier`; this is the canonical logarithmic barrier on
-- the positive-orthant constraint family, precomposed with the subtype inclusion.
/-- Evaluating `standardLogarithmicBarrier` gives the textbook formula
`-\sum_{i=1}^n \log x^{(i)}` on the strict positive orthant. -/
@[simp] theorem standardLogarithmicBarrier_apply (x : Xₙ) :
    standardLogarithmicBarrier n x =
      -∑ i : Fin n, Real.log (x i) := by
  rw [standardLogarithmicBarrier, ContinuousMap.comp_apply, logarithmicBarrier_apply]
  simp [positiveOrthantConstraints]

/-- The ambient formula underlying `standardLogarithmicBarrier`. This is only a bridge view for
Chapter 5 APIs formulated on ambient maps `Eₙ → ℝ`. -/
def standardLogarithmicBarrierAmbient : Eₙ → ℝ :=
  fun x ↦ -∑ i : Fin n, Real.log (x i)

/-- Evaluating `standardLogarithmicBarrierAmbient` gives the textbook ambient formula
`-\sum_{i=1}^n \log x^{(i)}`. -/
@[simp] theorem standardLogarithmicBarrierAmbient_apply (x : Eₙ) :
    standardLogarithmicBarrierAmbient n x =
      -∑ i : Fin n, Real.log (x i) :=
  rfl

/-- On the strict positive orthant, the ambient bridge agrees with the intrinsic owner. -/
@[simp] theorem standardLogarithmicBarrierAmbient_eq_standardLogarithmicBarrier (x : Xₙ) :
    standardLogarithmicBarrierAmbient n x = standardLogarithmicBarrier n x := by
  simpa [standardLogarithmicBarrierAmbient] using
    (standardLogarithmicBarrier_apply n x).symm

end

/-! ### Definition_5_4_3_3 (from Chap05) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
Definition 5.4.3.3 lies in the Chapter 5 logarithmic-homogeneity / cone-barrier domain.

Sampled owner-style declarations in the same domain:
* mathlib `ConvexCone ℝ E`, the canonical owner for convex cone domains;
* mathlib `ConvexCone.convex`, which derives convexity from that owner instead of storing it as
  parallel data;
* mathlib `ConvexCone.Pointed.of_nonempty_of_isClosed`, which recovers `0 ∈ K` for a closed
  nonempty cone and supports the nonnegative-scalar bridge;
* `IsBarrierFunctionOn` in `Chap01/Definition_1_10_18`, which carries closedness canonically as a
  parent `Fact`;
* `IsSelfConcordantBarrierOnWith` in `Chap05/Definition_5_3_2`, which keeps the source-facing
  owner while shrinking primitive data to the actual mathematical content.

Best owner abstraction:
* source-facing: `IsLogarithmicallyHomogeneousOnWith K ν F`;
* core/canonical ambient owner: `ConvexCone ℝ E`, with closedness carried separately as
  `Fact (IsClosed (K : Set E))`;
* bridge/view: the set-level `isClosed`, `pointed`, and nonnegative-scalar `smul_mem` lemmas.

Primitive data:
* a cone owner `K : ConvexCone ℝ E`;
* closedness of `K`;
* nonempty interior of `K`;
* `C²` regularity of `F` on `interior K`;
* the source-facing logarithmic scaling law on `interior K` for positive real scalars.

Derived API:
* convexity of `K` from `K.convex`;
* origin membership from closedness plus nonempty interior;
* the nonnegative real-scalar cone-closure bridge `smul_mem`.

Source/core/bridge triage:
* source-facing: logarithmic homogeneity with parameter `ν`;
* core/canonical: `ConvexCone ℝ E` together with the parent closedness assumption;
* bridge/view: the set-level closure/pointedness lemmas.

There is no earlier project or mathlib owner for this full logarithmic-homogeneity notion, so the
file keeps a source-facing owner declaration. The refinement here is therefore not to delete the
owner, but to organize it around the chapter's canonical cone owner and keep only the genuinely
source-facing extra data. -/

/-- Definition 5.4.3.3: a function `F : E → ℝ` is logarithmically homogeneous on a closed convex
cone `K` with nonempty interior and logarithmic homogeneity parameter `ν` when `F` is twice
continuously differentiable on `interior K` and `F (τ • x) = F x - ν log τ` for every
`x ∈ interior K` and every `τ > 0`. The cone structure itself is carried by the canonical owner
`K : ConvexCone ℝ E`, while closedness remains part of the source-facing notion; sign conditions on
`ν` belong to later barrier layers when they are actually needed, not to logarithmic homogeneity
itself. -/
class IsLogarithmicallyHomogeneousOnWith (K : ConvexCone ℝ E) (ν : ℝ) (F : E → ℝ) : Prop
    extends Fact (IsClosed (K : Set E)) where
  /-- The cone `K` has nonempty interior. -/
  interior_nonempty : (interior (K : Set E)).Nonempty
  /-- The function `F` is twice continuously differentiable on `interior K`. -/
  contDiffOn : ContDiffOn ℝ 2 F (interior (K : Set E))
  /-- The logarithmic scaling identity holds on `interior K` for every positive scalar. -/
  logarithmic_scaling {x : E} (hx : x ∈ interior (K : Set E)) {τ : ℝ} (hτ : 0 < τ) :
    F (τ • x) = F x - ν * Real.log τ

attribute [instance] IsLogarithmicallyHomogeneousOnWith.toFact

namespace IsLogarithmicallyHomogeneousOnWith

/-- A logarithmic-homogeneity hypothesis canonically supplies the closedness of its cone. -/
theorem isClosed
    {K : ConvexCone ℝ E} {ν : ℝ} {F : E → ℝ} (h : IsLogarithmicallyHomogeneousOnWith K ν F) :
    IsClosed (K : Set E) := by
  let _ : IsLogarithmicallyHomogeneousOnWith K ν F := h
  exact Fact.out

/-- A logarithmic-homogeneity hypothesis canonically supplies the owner property `K.Pointed`. -/
theorem pointed
    {K : ConvexCone ℝ E} {ν : ℝ} {F : E → ℝ} (h : IsLogarithmicallyHomogeneousOnWith K ν F) :
    K.Pointed :=
  ConvexCone.Pointed.of_nonempty_of_isClosed (h.interior_nonempty.mono interior_subset) h.isClosed

/-- A logarithmic-homogeneity hypothesis gives the usual real-scalar cone-closure statement for
nonnegative scalars. -/
theorem smul_mem
    {K : ConvexCone ℝ E} {ν : ℝ} {F : E → ℝ}
    (h : IsLogarithmicallyHomogeneousOnWith K ν F)
    {x : E} (hx : x ∈ K) {τ : ℝ} (hτ : 0 ≤ τ) :
    τ • x ∈ K := by
  rcases lt_or_eq_of_le hτ with hτ' | rfl
  · exact K.smul_mem hτ' hx
  · simpa [ConvexCone.Pointed] using h.pointed

end IsLogarithmicallyHomogeneousOnWith

end

/-! ### Definition_5_4_3_4 (from Chap05) -/
noncomputable section

variable {n m : ℕ}

/- Definition 5.4.3.4 lies in the Chapter 5 QCQP / convex inequality optimization domain.

Sampled owner declarations in this domain:
* `quadraticObjective` from `Chap01/Definition_1_9_1`, the chapter owner for Euclidean
  quadratic-affine functions;
* `Matrix.PosSemidef.convexOn_quadraticObjective` from `Chap02/Example_2_1_1_2`, the derived
  convexity owner for quadratic objectives with positive-semidefinite Hessian;
* `LagrangianProblem` from `Chap01/Definition_1_10_2`, the canonical owner for whole-space
  `≤ 0` constraints;
* `ConvexInequalityConstrainedMinimizationProblem` from `Definition_5_0_1`, the Chapter 5 owner
  for convex whole-space inequality minimization;
* `SetConstrainedMinimizationProblem` from `Chap01/Definition_1_3_3`, the Chapter 1 owner for a
  feasible set together with its objective;
* `constrainedEpigraph` from `Chap03/Definition_3_3`, the chapter owner for epigraph regions.

Source/core/bridge triage:
* source-facing: `QuadraticallyConstrainedQuadraticOptimizationProblem n m`;
* core/canonical: `LagrangianProblem Eₙ m`,
  `ConvexInequalityConstrainedMinimizationProblem n m`,
  `SetConstrainedMinimizationProblem (Eₙ × ℝ)`, and `constrainedEpigraph`;
* bridge/view: the derived function family `quadraticFunction`, the owner bridges
  `toLagrangianProblem` / `toConvexInequalityConstrainedMinimizationProblem`, and the
  epigraph optimization owner together with its feasible-set view.

Primitive data:
* the scalar terms `αᵢ`;
* the linear coefficients `aᵢ`;
* the quadratic matrices `Aᵢ`;
* the positive-semidefinite witnesses for `Aᵢ`;
* the constraint bounds `βᵢ`.

Derived API:
* the textbook quadratic family `qᵢ`;
* the objective and constraint functions;
* convexity of those derived functions;
* the canonical owner bridges and feasible-set API;
* the epigraph optimization owner and its feasible-set view via `constrainedEpigraph`.

The refinement keeps the source-facing QCQP data as the owner, but removes the lower-level
`GeneralMinimizationProblem` packaging and exposes the epigraph reformulation through the exact
Chapter 1/5 owners already used elsewhere in the chapter. -/

/-- Definition 5.4.3.4: A quadratically constrained quadratic optimization problem on `ℝⁿ`
consists of quadratic functions `q₀, …, q_m` with positive-semidefinite quadratic parts and
constraint bounds `β₁, …, β_m`; the problem is to minimize `q₀` subject to `qᵢ(x) ≤ βᵢ` for
`i = 1, …, m`, and it admits the equivalent epigraph reformulation using an auxiliary scalar
variable `τ`. -/
structure QuadraticallyConstrainedQuadraticOptimizationProblem (n m : ℕ) where
  α : Fin (m + 1) → ℝ
  a : Fin (m + 1) → EuclideanSpace ℝ (Fin n)
  A : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ
  A_posSemidef : ∀ i : Fin (m + 1), (A i).PosSemidef
  β : Fin m → ℝ

namespace QuadraticallyConstrainedQuadraticOptimizationProblem

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/-- The `i`-th quadratic function `qᵢ` of a QCQP. -/
abbrev quadraticFunction (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m)
    (i : Fin (m + 1)) : Eₙ → ℝ :=
  quadraticObjective (problem.α i) (problem.a i) (problem.A i)

/-- The objective function `q₀` of a QCQP. -/
abbrev objective (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    Eₙ → ℝ :=
  problem.quadraticFunction 0

/-- The `i`-th constraint function `q_{i+1}` of a QCQP. -/
abbrev constraintFunction (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m)
    (i : Fin m) : Eₙ → ℝ :=
  problem.quadraticFunction i.succ

/-- A QCQP can be used as its objective function `q₀`. -/
instance : CoeFun (QuadraticallyConstrainedQuadraticOptimizationProblem n m)
    (fun _ ↦ Eₙ → ℝ) where
  coe problem := problem.objective

/-- Evaluating a QCQP returns its objective value `q₀(x)`. -/
@[simp] theorem coe_apply (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m)
    (x : Eₙ) :
    problem x = problem.objective x :=
  rfl

/-- Each quadratic function of a QCQP is convex on all of `ℝⁿ`. -/
theorem quadraticFunction_convex
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (i : Fin (m + 1)) :
    ConvexOn ℝ Set.univ (problem.quadraticFunction i) :=
  (problem.A_posSemidef i).convexOn_quadraticObjective (problem.α i) (problem.a i)

/-- The objective function `q₀` of a QCQP is convex on all of `ℝⁿ`. -/
theorem objective_convex
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    ConvexOn ℝ Set.univ problem.objective := by
  simpa [objective] using problem.quadraticFunction_convex 0

/-- Each constraint function `q_{i+1}` of a QCQP is convex on all of `ℝⁿ`. -/
theorem constraintFunction_convex
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (i : Fin m) :
    ConvexOn ℝ Set.univ (problem.constraintFunction i) := by
  simpa [constraintFunction] using problem.quadraticFunction_convex i.succ

/-- The canonical Chapter 1 Lagrangian owner attached to a QCQP. -/
def toLagrangianProblem
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    LagrangianProblem Eₙ m where
  objective := problem.objective
  constraints := fun i x ↦ problem.constraintFunction i x - problem.β i

/-- A QCQP coerces to its canonical Chapter 1 Lagrangian owner. -/
instance : Coe (QuadraticallyConstrainedQuadraticOptimizationProblem n m)
    (LagrangianProblem Eₙ m) where
  coe := toLagrangianProblem

/-- The Chapter 1 owner evaluates to the QCQP objective `q₀`. -/
@[simp] theorem toLagrangianProblem_apply
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (x : Eₙ) :
    problem.toLagrangianProblem x = problem.objective x :=
  rfl

@[simp] theorem toLagrangianProblem_constraints_apply
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m)
    (i : Fin m) (x : Eₙ) :
    (problem : LagrangianProblem Eₙ m).constraints i x =
      problem.constraintFunction i x - problem.β i :=
  rfl

/-- The canonical Chapter 5 convex inequality owner attached to a QCQP. -/
def toConvexInequalityConstrainedMinimizationProblem
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    ConvexInequalityConstrainedMinimizationProblem n m where
  objective := problem.objective
  constraints := fun i x ↦ problem.constraintFunction i x - problem.β i
  objective_convex := problem.objective_convex
  constraints_convex i := by
    simpa [sub_eq_add_neg] using (problem.constraintFunction_convex i).add_const (-problem.β i)

/-- A QCQP coerces to its canonical Chapter 5 convex inequality owner. -/
instance : Coe (QuadraticallyConstrainedQuadraticOptimizationProblem n m)
    (ConvexInequalityConstrainedMinimizationProblem n m) where
  coe := toConvexInequalityConstrainedMinimizationProblem

/-- The Chapter 5 owner evaluates to the QCQP objective `q₀`. -/
@[simp] theorem toConvexInequalityConstrainedMinimizationProblem_apply
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (x : Eₙ) :
    problem.toConvexInequalityConstrainedMinimizationProblem x = problem.objective x :=
  rfl

@[simp] theorem toConvexInequalityConstrainedMinimizationProblem_constraints_apply
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m)
    (i : Fin m) (x : Eₙ) :
    (problem : ConvexInequalityConstrainedMinimizationProblem n m).constraints i x =
      problem.constraintFunction i x - problem.β i :=
  rfl

/-- The feasible set `\{x : qᵢ(x) ≤ βᵢ \text{ for } i = 1, …, m\}` of a QCQP. -/
def feasibleSet (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    Set Eₙ :=
  problem.toLagrangianProblem.feasibleSet

/-- Membership in the feasible set of a QCQP is exactly the family of constraint inequalities
`qᵢ(x) ≤ βᵢ`. -/
@[simp] theorem mem_feasibleSet_iff
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (x : Eₙ) :
    x ∈ problem.feasibleSet ↔ ∀ i : Fin m, problem.constraintFunction i x ≤ problem.β i := by
  constructor
  · intro hx i
    exact sub_nonpos.mp ((problem.toLagrangianProblem.mem_feasibleSet_iff).1 hx i)
  · intro hx
    exact (problem.toLagrangianProblem.mem_feasibleSet_iff).2
      (fun i ↦ sub_nonpos.mpr (hx i))

/-- The canonical Chapter 1 epigraph reformulation of a QCQP in the variables `(x, τ)`, whose
objective is the auxiliary scalar `τ`. -/
def epigraphOptimizationProblem
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    SetConstrainedMinimizationProblem (Eₙ × ℝ) where
  feasibleSet := constrainedEpigraph problem.feasibleSet
    fun x ↦ (problem.objective x : WithTop ℝ)
  objective := Prod.snd

/-- Evaluating the QCQP epigraph owner returns the auxiliary variable `τ`. -/
@[simp] theorem epigraphOptimizationProblem_apply
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (x : Eₙ) (τ : ℝ) :
    problem.epigraphOptimizationProblem (x, τ) = τ :=
  rfl

/-- The feasible set of the equivalent epigraph formulation of a QCQP in the variables `(x, τ)`. -/
def epigraphFeasibleSet (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    Set (Eₙ × ℝ) :=
  problem.epigraphOptimizationProblem.feasibleSet

/-- The epigraph owner preserves the QCQP epigraph feasible set. -/
theorem epigraphOptimizationProblem_feasibleSet
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    problem.epigraphOptimizationProblem.feasibleSet = problem.epigraphFeasibleSet :=
  rfl

/-- Membership in the feasible set of the QCQP epigraph optimization owner is the objective
epigraph inequality together with feasibility of the base point. -/
@[simp] theorem mem_epigraphOptimizationProblem_feasibleSet_iff
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (xτ : Eₙ × ℝ) :
    xτ ∈ problem.epigraphOptimizationProblem.feasibleSet ↔
      problem.objective xτ.1 ≤ xτ.2 ∧
        ∀ i : Fin m, problem.constraintFunction i xτ.1 ≤ problem.β i := by
  change xτ ∈ constrainedEpigraph problem.feasibleSet
      (fun x ↦ (problem.objective x : WithTop ℝ)) ↔
    problem.objective xτ.1 ≤ xτ.2 ∧
      ∀ i : Fin m, problem.constraintFunction i xτ.1 ≤ problem.β i
  rw [mem_constrainedEpigraph_iff]
  constructor
  · rintro ⟨hx, hτ⟩
    exact ⟨by simpa using hτ, (problem.mem_feasibleSet_iff xτ.1).1 hx⟩
  · rintro ⟨hτ, hx⟩
    exact ⟨(problem.mem_feasibleSet_iff xτ.1).2 hx, by simpa using hτ⟩

/-- Membership in the QCQP epigraph feasible set is the objective epigraph inequality together
with feasibility of the base point. -/
@[simp] theorem mem_epigraphFeasibleSet_iff
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (xτ : Eₙ × ℝ) :
    xτ ∈ problem.epigraphFeasibleSet ↔
      problem.objective xτ.1 ≤ xτ.2 ∧
        ∀ i : Fin m, problem.constraintFunction i xτ.1 ≤ problem.β i := by
  simpa [epigraphFeasibleSet] using problem.mem_epigraphOptimizationProblem_feasibleSet_iff xτ

end QuadraticallyConstrainedQuadraticOptimizationProblem

/-! ### Definition_5_4_3_5 (from Chap05) -/
open scoped BigOperators

noncomputable section

variable {n m : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Definition 5.4.3.5 lies in the Chapter 5 QCQP / logarithmic-barrier domain.

Sampled owner declarations in this domain:
* `strictConstraintSet` and `logarithmicBarrier` from `Chap01/Proposition_1_10_17`, the
  canonical finite-constraint strict-domain barrier owners;
* `analyticBarrierDomain`, `AnalyticBarrierPoint`, `analyticBarrier`, and
  `analyticBarrierAmbient` from `Chap03/Definition_3_62`, the chapter precedent for keeping the
  barrier on its strict-domain subtype and any raw formula only as a bridge;
* `QuadraticallyConstrainedQuadraticOptimizationProblem.feasibleSet` and
  `QuadraticallyConstrainedQuadraticOptimizationProblem.epigraphFeasibleSet` from
  `Definition_5_4_3_4`, the chapter QCQP owner and its nonstrict feasible-region API.

Source/core/bridge triage:
* source-facing: the strict QCQP feasible set, the strict QCQP epigraph feasible set, and the
  textbook QCQP epigraph logarithmic barrier;
* core/canonical: `strictConstraintSet` and `logarithmicBarrier` on the QCQP-induced slack
  families;
* bridge/view: the ambient formula `epigraphLogarithmicBarrierAmbient`.

Primitive data:
* the QCQP owner `problem`.

Derived API:
* the internal continuous slack families induced by `problem`;
* strict feasibility and strict epigraph feasibility;
* the strict-domain barrier
  `epigraphLogarithmicBarrier :
    C(problem.StrictEpigraphFeasiblePoint, ℝ)`;
* the raw-pair ambient bridge `epigraphLogarithmicBarrierAmbient`.

This file therefore extends the existing QCQP owner directly, rather than introducing a parallel
public raw barrier API in terms of arbitrary `q₀`, `q`, and `β`. -/

namespace QuadraticallyConstrainedQuadraticOptimizationProblem

private theorem quadraticFunction_continuous
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (i : Fin (m + 1)) :
    Continuous (problem.quadraticFunction i) := by
  have hsymm : (problem.A i).IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using (problem.A_posSemidef i).isHermitian
  exact
    (symmetric_quadratic_contDiff_and_gradient_lipschitz
      (problem.α i) (problem.a i) (problem.A i) hsymm).1.continuous

private theorem objective_continuous
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    Continuous problem.objective :=
  problem.quadraticFunction_continuous 0

private theorem constraintFunction_continuous
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (i : Fin m) :
    Continuous (problem.constraintFunction i) :=
  problem.quadraticFunction_continuous i.succ

private def strictFeasibleConstraints
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    Fin m → C(Eₙ, ℝ) :=
  fun i ↦
    { toFun := problem.constraintFunction i
      continuous_toFun := problem.constraintFunction_continuous i } -
      ContinuousMap.const Eₙ (problem.β i)

/-- The strict feasible set `{x | qᵢ(x) < βᵢ}` of the QCQP constraints. -/
def strictFeasibleSet
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) : Set Eₙ :=
  strictConstraintSet problem.strictFeasibleConstraints

/-- Membership in `problem.strictFeasibleSet` is exactly the family of strict constraint
inequalities `qᵢ(x) < βᵢ`. -/
@[simp] theorem mem_strictFeasibleSet_iff
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (x : Eₙ) :
    x ∈ problem.strictFeasibleSet ↔ ∀ i : Fin m, problem.constraintFunction i x < problem.β i := by
  simp [strictFeasibleSet, strictFeasibleConstraints]

private def strictEpigraphConstraints
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    Fin (m + 1) → C(Eₙ × ℝ, ℝ) :=
  Fin.cases
    { toFun := fun p ↦ problem.objective p.1 - p.2
      continuous_toFun := (problem.objective_continuous.comp continuous_fst).sub continuous_snd }
    (fun i ↦
      { toFun := fun p ↦ problem.constraintFunction i p.1 - problem.β i
        continuous_toFun :=
          ((problem.constraintFunction_continuous i).comp continuous_fst).sub continuous_const })

/-- The strict feasible region of the QCQP epigraph formulation, cut out by the positive slacks
`τ - q₀(x)` and `βᵢ - qᵢ(x)`. -/
def strictEpigraphFeasibleSet
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) : Set (Eₙ × ℝ) :=
  strictConstraintSet problem.strictEpigraphConstraints

/-- The subtype of points in the strict QCQP epigraph barrier domain. This is the natural owner
carrier for the QCQP epigraph barrier. -/
abbrev StrictEpigraphFeasiblePoint
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :=
  {p : Eₙ × ℝ // p ∈ problem.strictEpigraphFeasibleSet}

-- Proof sketch: unfold `strictEpigraphFeasibleSet`; membership is exactly the conjunction of the
-- strict epigraph slack inequality for `q₀` and the strict slack inequalities for each `qᵢ`.
/-- Membership in the QCQP strict epigraph feasible region means that all defining slacks are
strictly positive. -/
theorem mem_strictEpigraphFeasibleSet_iff
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) (p : Eₙ × ℝ) :
    p ∈ problem.strictEpigraphFeasibleSet ↔
      0 < p.2 - problem.objective p.1 ∧
        ∀ i : Fin m, 0 < problem.β i - problem.constraintFunction i p.1 := by
  simp [strictEpigraphFeasibleSet, strictEpigraphConstraints, Fin.forall_fin_succ, sub_pos]

/-- Definition 5.4.3.5: the logarithmic barrier for the QCQP epigraph feasible region
`{(x, τ) | 0 < τ - q₀(x) ∧ ∀ i, 0 < βᵢ - qᵢ(x)}` is
`(x, τ) ↦ -log (τ - q₀(x)) - ∑ i, log (βᵢ - qᵢ(x))`. -/
def epigraphLogarithmicBarrier
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) :
    C(problem.StrictEpigraphFeasiblePoint, ℝ) :=
  logarithmicBarrier problem.strictEpigraphConstraints

/-- The ambient formula underlying `problem.epigraphLogarithmicBarrier`. It is only a bridge
view; the owner barrier is `problem.epigraphLogarithmicBarrier` on
`problem.StrictEpigraphFeasiblePoint`. -/
def epigraphLogarithmicBarrierAmbient
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m) : Eₙ × ℝ → ℝ :=
  fun p ↦
    -Real.log (p.2 - problem.objective p.1) -
      ∑ i : Fin m, Real.log (problem.β i - problem.constraintFunction i p.1)

-- Proof sketch: unfold `epigraphLogarithmicBarrier`; the displayed expression is exactly its
-- defining formula.
/-- Evaluating the QCQP epigraph logarithmic barrier reproduces the sum of the negative
logarithms of the strict slacks. -/
@[simp] theorem epigraphLogarithmicBarrier_apply
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m)
    (p : problem.StrictEpigraphFeasiblePoint) :
    problem.epigraphLogarithmicBarrier p =
      problem.epigraphLogarithmicBarrierAmbient p := by
  sorry

-- Proof sketch: rewrite the pair `p` as `(x, τ)` and unfold
-- `epigraphLogarithmicBarrierAmbient`; this is exactly the textbook formula.
/-- The QCQP epigraph logarithmic barrier has the textbook coordinate formula
`F(x, τ) = -log (τ - q₀(x)) - \sum_i log (βᵢ - qᵢ(x))`. -/
theorem epigraphLogarithmicBarrier_apply_pair
    (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m)
    (x : Eₙ) (τ : ℝ)
    (h : (x, τ) ∈ problem.strictEpigraphFeasibleSet) :
    problem.epigraphLogarithmicBarrier ⟨(x, τ), h⟩ =
      -Real.log (τ - problem.objective x) -
        ∑ i : Fin m, Real.log (problem.β i - problem.constraintFunction i x) := by
  simpa [epigraphLogarithmicBarrierAmbient] using
    problem.epigraphLogarithmicBarrier_apply ⟨(x, τ), h⟩

end QuadraticallyConstrainedQuadraticOptimizationProblem

end

/-! ### Lemma_5_4_3_1 (from Chap05) -/
open Set Topology
open EuclideanSpace (single)
open scoped BigOperators EuclideanOrthant

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Lemma 5.4.3.1 lies in the Chapter 5 self-concordant-barrier / recession-direction domain.

Sampled owner-style declarations in this domain:
* `EuclideanSpace.nonnegativeOrthant` in `Chap01/Definition_1_10_2`, the project owner for the
  orthant `ℝ₊ⁿ`;
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the Chapter 5 owner for
  `ν`-self-concordant barriers;
* `IsSelfConcordantBarrierOnWith.barrierParameter_ge_sum_alpha_div_beta_of_recession_directions`
  in `Theorem_5_4_1_2`, the canonical owner theorem for lower bounds on the barrier parameter;
* `convex_pi` together with `convex_Ici`, the canonical mathlib convexity owner for coordinatewise
  orthant constraints.

Source/core/bridge triage:
* source-facing: the orthant specialization `ν ≥ n`;
* core/canonical: the general recession-direction owner theorem for
  `IsSelfConcordantBarrierOnWith`;
* bridge/view: the standard-basis recession directions of `ℝ₊ⁿ` and the coordinatewise orthant
  facts used to instantiate the owner theorem.

Primitive data:
* the orthant owner `nonnegativeOrthant n`;
* the barrier owner instance on `interior (nonnegativeOrthant n)`;
* the base point `(1, …, 1)` and the standard basis directions.

Derived API:
* the lower bound `(n : ℝ) ≤ (ν : ℝ)`, obtained by specializing the owner theorem with
  `αᵢ = βᵢ = 1`.

This file is therefore a source-facing specialization of the Chapter 5 owner theorem, not a
second owner abstraction. The refinement removes the isolated local proof sketch surface and
states the lemma directly as a canonical specialization of the existing owner theorem. -/

-- Proof sketch: apply
-- `barrierParameter_ge_sum_alpha_div_beta_of_recession_directions` to the convex set
-- `nonnegativeOrthant n`, with base point `xBar = (1, …, 1)`, recession directions the standard
-- basis vectors `eᵢ`, and coefficients `αᵢ = βᵢ = 1`. Then `xBar - ∑ i, αᵢ • eᵢ = 0` belongs to
-- the orthant, each backward step `xBar - eᵢ` lies on the boundary, and the left-hand side
-- becomes `∑ i, 1 = n`.
/-- Lemma 5.4.3.1: every `ν`-self-concordant barrier for the nonnegative orthant `ℝ₊ⁿ` has
barrier parameter at least `n`. -/
theorem nonnegativeOrthant_barrierParameter_ge_dimension
    {ν : NNReal} {F : Eₙ → ℝ}
    (hF : IsSelfConcordantBarrierOnWith (ℝ₊₊^n : Set Eₙ) ν F) :
    (n : ℝ) ≤ (ν : ℝ) := by
  let xBar : Eₙ := ∑ i : Fin n, single i (1 : ℝ)
  let p : Fin n → Eₙ := fun i ↦ single i (1 : ℝ)
  let e : Eₙ ≃ₜ (Fin n → ℝ) :=
    (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph
  have hnonnegativeOrthant :
      (ℝ₊^n : Set Eₙ) =
        e ⁻¹' Set.pi Set.univ (fun _ : Fin n ↦ Set.Ici (0 : ℝ)) := by
    ext x
    simp [Pi.le_def, e, EuclideanSpace.nonnegativeOrthant]
  have hpositiveOrthant :
      (ℝ₊₊^n : Set Eₙ) =
        e ⁻¹' Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioi (0 : ℝ)) := by
    ext x
    simp [e, EuclideanSpace.positiveOrthant]
  have hinterior : interior (ℝ₊^n : Set Eₙ) = (ℝ₊₊^n : Set Eₙ) := by
    rw [hnonnegativeOrthant, ← e.preimage_interior, interior_pi_set Set.finite_univ,
      hpositiveOrthant]
    simp
  have hF' : IsSelfConcordantBarrierOnWith (interior (ℝ₊^n : Set Eₙ)) ν F := by
    simpa [hinterior] using hF
  have hQ_convex : Convex ℝ (ℝ₊^n : Set Eₙ) := by
    rw [hnonnegativeOrthant]
    exact (convex_pi fun _ _ ↦ convex_Ici (0 : ℝ)).linear_preimage
      (EuclideanSpace.equiv (Fin n) ℝ).toLinearMap
  have hxBar : xBar ∈ interior (ℝ₊^n : Set Eₙ) := by
    rw [hinterior]
    simp [xBar, EuclideanSpace.mem_positiveOrthant_iff]
  have hp :
      ∀ i : Fin n,
        ∀ ⦃x : Eₙ⦄, x ∈ (ℝ₊^n : Set Eₙ) → ∀ t : ℝ, 0 ≤ t → x + t • p i ∈ (ℝ₊^n : Set Eₙ) := by
    intro i x hx t ht
    have hx' : ∀ j : Fin n, 0 ≤ x j := by
      simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using hx
    rw [EuclideanSpace.mem_nonnegativeOrthant_iff]
    intro j
    by_cases hji : j = i
    · subst j
      simpa [p, single] using add_nonneg (hx' i) ht
    · simpa [p, single, hji] using hx' j
  have hβ_pos : ∀ i : Fin n, 0 < (1 : ℝ) := by
    intro i
    norm_num
  have hβ_exit : ∀ i : Fin n, xBar - (1 : ℝ) • p i ∉ interior (ℝ₊^n : Set Eₙ) := by
    intro i
    rw [hinterior, EuclideanSpace.mem_positiveOrthant_iff]
    intro hx
    have hxi := hx i
    simp [xBar, p, single] at hxi
  have hα_nonneg : ∀ i : Fin n, 0 ≤ (1 : ℝ) := by
    intro i
    norm_num
  have hy : xBar - ∑ i, (1 : ℝ) • p i ∈ (ℝ₊^n : Set Eₙ) := by
    simp [EuclideanSpace.mem_nonnegativeOrthant_iff, p, xBar, single]
  have hbound : ∑ i : Fin n, (1 : ℝ) / 1 ≤ (ν : ℝ) :=
    hF'.barrierParameter_ge_sum_alpha_div_beta_of_recession_directions
      hQ_convex hxBar p
      hp
      (fun _ : Fin n ↦ (1 : ℝ)) (fun _ : Fin n ↦ (1 : ℝ))
      hβ_pos hβ_exit hα_nonneg hy
  simpa [xBar, p] using hbound

end
