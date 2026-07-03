import Mathlib.Analysis.Convex.Strong
import Mathlib.Tactic.Recall
import Mathlib.Tactic.Ring

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_38 (from Chap03) -/
/-
Definition 3.38 lies in the Chapter 3 pointwise-growth / local-modulus domain.

Primary domain:
- supremal growth profiles of a real-valued function around a base point on `ℝⁿ`.

Sampled owner-style declarations:
- `pointwiseGrowthFunction` in `Lemma_3_2_1`, the chapter owner for `ω_f(xBar; t)`
- `pointwiseGrowthFunction_eq_zero_of_neg` in `Lemma_3_2_1`, the owner-level negative-radius
  branch simplification
- `sub_le_pointwiseGrowthFunction_of_localizationMeasure` in `Lemma_3_2_1`, the first comparison
  theorem built from the same owner
- `pointwiseGrowthFunction_monotone` in `Proposition_3_34`, the radius-monotonicity theorem for
  the same owner profile

Best owner abstraction:
- `pointwiseGrowthFunction`

Primitive data:
- a real-valued function `f`
- a base point `xBar`
- a radius parameter `t`

Derived API:
- the owner-level negative-radius simplification `pointwiseGrowthFunction_eq_zero_of_neg`
- the localization-measure comparison
  `sub_le_pointwiseGrowthFunction_of_localizationMeasure`
- the monotonicity and radius-evaluation consequences developed downstream in
  `Proposition_3_34`

Source/core/bridge triage:
- source-facing: the textbook growth function `ω_f(xBar; t)`
- core/canonical: `pointwiseGrowthFunction`
- bridge/view: the branch simplifications and comparison lemmas obtained by unfolding the owner

The owner declaration `pointwiseGrowthFunction` in `Lemma_3_2_1` already carries the exact
mathematical content of Definition 3.38. This file therefore recalls that owner directly instead
of keeping a parallel local copy such as `pointwise_growth_function`. The negative-radius branch
theorem stays with the owner file instead of being re-exported from this definition-only recall.
-/

recall pointwiseGrowthFunction

/-! ### Lemma_3_38 (from Chap03) -/
universe u

/-
Lemma 3.38 lies in the chapter's set-constrained scalar parametric max-value-function domain.

Sampled owner-style declarations:
- `parametricValueFunction` in `Chap03/Lemma_3_3_6`, the chapter owner for the feasible-set
  infimum of `x ↦ max (f x - t) (barf x)`;
- `parametricValueFunction_sub_le_shift` in `Chap03/Lemma_3_3_6`, the owner shift bound for one
  model `f`;
- `Definition_3_75` in `Chap03/Definition_3_75`, where the textbook approximate value
  `\hat f_k^*(X; ·)` is already identified with the specialization
  `parametricValueFunction Q (hatModel xSeq k) (checkModel xSeq k)`;
- `LagrangianProblem.constrainedAuxiliaryOptimalValue_shift_bounds` in `Chap02/Lemma_2_22`, the
  matching owner-style shift bound for the same max-type infimum pattern in the Chapter 2
  constrained auxiliary-value setting.

Best owner abstraction:
- `parametricValueFunction Q f barf`

Primitive data:
- feasible set `Q`;
- exact model `f`;
- stage model pair `(hatModel xSeq k, checkModel xSeq k)`;
- parameters `t` and `Δ`.

Derived API:
- the owner shift theorem `parametricValueFunction_sub_le_shift`;
- the textbook approximate case is the stage-`k` specialization already recognized in
  `Definition_3_75`.

Source/core/bridge triage:
- source-facing: the exact-value shift inequality together with its stage-`k` approximate-model
  specialization;
- core/canonical: `parametricValueFunction_sub_le_shift`;
- bridge/view: the `Definition_3_75` stage-`k` specialization of the textbook approximate
  notation.

This file therefore reuses the exact-value statement by direct recall of the owner theorem and
keeps only the stage-`k` specialization as a separate bridge theorem.
-/

/- Lemma 3.38, exact-value part: direct reuse of the chapter owner shift theorem. -/
recall parametricValueFunction_sub_le_shift

section

variable {X : Type u}
variable (Q : Set X)
variable (hatModel checkModel : (ℕ → X) → ℕ → X → ℝ) (xSeq : ℕ → X) (k : ℕ)

/-- Lemma 3.38, approximate-value part: the stage-`k` model value from `Definition_3_75`
satisfies the same parameter-shift bound as the exact owner value. -/
theorem stageParametricValueFunction_sub_le_shift
    {Δ t : ℝ} (hΔ : 0 ≤ Δ) :
    parametricValueFunction Q (hatModel xSeq k) (checkModel xSeq k) t - Δ ≤
      parametricValueFunction Q (hatModel xSeq k) (checkModel xSeq k) (t + Δ) :=
  parametricValueFunction_sub_le_shift Q (hatModel xSeq k) (checkModel xSeq k) Δ t hΔ

end

/-! ### Proposition_3_38 (from Chap03) -/
universe u

/- Primary domain: weighted-sum closure for strong convexity on a fixed feasible set in a real
normed space.

Sampled owner-style declarations before refining this file:
* mathlib `StrongConvexOn`
* mathlib `UniformConvexOn.add`
* project `StrongConvexOn.add_convexOn` in `Chap02/Proposition_2_3`
* project `StrongConvexOnWith.nonneg_combo_inter` in `Chap02/Definition_2_14`

Best owner abstraction:
* `StrongConvexOn Q μ f`

Primitive data:
* the common feasible set `Q`
* the two strong-convexity owner hypotheses
* the nonnegative scalar weights

Derived API:
* strong convexity of the weighted sum with modulus `α₁ * μ₁ + α₂ * μ₂`

Source/core/bridge triage:
* bridge/view: this proposition is the same-domain weighted-sum closure rule for the canonical
  owner `StrongConvexOn`; it is not a second owner declaration
-/

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace StrongConvexOn

/-- Proposition 3.38: a nonnegative linear combination of two strongly convex functions on the
same convex domain is strongly convex, with strong-convexity parameter
`α₁ * μ₁ + α₂ * μ₂`. -/
-- Proof sketch: `StrongConvexOn` is the canonical `UniformConvexOn` owner with quadratic modulus.
-- Multiply the two owner inequalities by the nonnegative weights `α₁`, `α₂`, add them, and
-- collect the quadratic terms.
theorem nonneg_weighted_add
    {Q : Set E} {f₁ f₂ : E → ℝ} {μ₁ μ₂ α₁ α₂ : ℝ}
    (hf₁ : StrongConvexOn Q μ₁ f₁)
    (hf₂ : StrongConvexOn Q μ₂ f₂)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂) :
    StrongConvexOn Q (α₁ * μ₁ + α₂ * μ₂) (α₁ • f₁ + α₂ • f₂) := by
  refine ⟨hf₁.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have h₁ := mul_le_mul_of_nonneg_left (hf₁.2 hx hy ha hb hab) hα₁
  have h₂ := mul_le_mul_of_nonneg_left (hf₂.2 hx hy ha hb hab) hα₂
  have h := add_le_add h₁ h₂
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
  ring_nf at h ⊢
  exact h

end StrongConvexOn

/-! ### Theorem_3_38 (from Chap03) -/
noncomputable section

open scoped BigOperators WithTopConvexAnalysis

universe u v w

/- Theorem 3.38 lies in the chapter's max-type active-subgradient saddle domain.

Sampled owner-style declarations:
- `pointwiseSupremumOn` in `Chap03/Theorem_3_1_8` and
  `activePointwiseSupremumOnIndices` in `Chap03/Lemma_3_1_14`, the chapter owners for the
  faithful upper envelope and active parameters;
- `subdifferentialWithin` and the source-facing notation `∂[P] f(x)` in `Chap03/Theorem_3_44`,
  the chapter owner surface for relative subgradients;
- `IsSaddlePointOn` in `Mathlib/Order/SaddlePoint`, the canonical saddle-point owner on
  `P × S`;
- `minimax_eq_of_activeSubgradientRepresentation_at_minimizer` in `Chap03/Theorem_3_1_31`, the
  stronger barycentric minimax theorem from which the present source-facing result is a more
  general abstract-parameter variant.

Best owner abstraction:
- source-facing: existence of a saddle parameter produced from an active-subgradient
  representation;
- core/canonical: `pointwiseSupremumOn`, `activePointwiseSupremumOnIndices`, `∂[P] f(x)`,
  together with `IsSaddlePointOn`;
- bridge/view: the raw aggregation hypothesis
  `∃ uBar ∈ S, ∀ x ∈ P, ∑ i, λ i * Ψ x (u i) ≤ Ψ x uBar`, which keeps the source's abstract
  parameter `uBar : U` instead of imposing additive structure on `U`.

Primitive data:
- the feasible primal set `P` and parameter set `S`;
- the kernel `Ψ`;
- the minimizing primal point `xStar` and its active-slice subgradient representation.

Derived API:
- the real-valued objective `f` together with its faithful upper-envelope bridge on `P`;
- the owner active set `activePointwiseSupremumOnIndices S (fun x u ↦ (Ψ x u : WithTop ℝ)) xStar`;
- the canonical saddle predicate `IsSaddlePointOn P S Ψ xStar`.

The previous version duplicated the subgradient owner locally and treated the real-valued upper
envelope as a primitive owner. This refinement deletes the duplicate wheel, reuses the faithful
`WithTop ℝ` upper-envelope owner through an explicit real-valued bridge `f`, removes the one-off
saddle and aggregation wrappers, and phrases the source-facing result directly on the chapter
owner API. The active-family surface also lives at the canonical finite-index layer
`ι : Type*` with `[Fintype ι]`, not the over-concrete display model `Fin k`. -/

variable {E : Type u} {U : Type v} {ι : Type w}

variable [Fintype ι]

variable [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Theorem 3.38: if `f : E → ℝ` is a real-valued objective on `P` whose `WithTop ℝ` lift agrees
with the faithful upper-envelope owner
`pointwiseSupremumOn S (fun x u ↦ (Ψ x u : WithTop ℝ))`, if `xStar` minimizes `f` on `P`, if a
relative subgradient `gStar ∈ ∂[P] f(xStar)` annihilates every feasible
displacement `x - xStar`, and if `gStar` is a simplex-weighted combination of relative
subgradients `g i ∈ ∂[P] (fun x ↦ Ψ x (u i)) (xStar)` of active slices
`x ↦ Ψ(x, u i)` at `xStar` whose weighted slice values can be
aggregated by one parameter `uBar ∈ S`, then that aggregated parameter is a saddle point of `Ψ`
on `P × S` with first coordinate `xStar`; equivalently, it realizes the same lower-envelope value
as the primal optimum at `xStar`. -/
-- Proof sketch: use the representation
-- `gStar = ∑ i, weights.weights i • g i` and the orthogonality assumption to rewrite
-- `f xStar` as a weighted sum of the pairings `⟪g i, x - xStar⟫`. Apply the
-- relative subgradient inequality for each active slice `Ψ(·, u i)` and use activity at `xStar`
-- to get `f xStar ≤ ∑ i, weights.weights i * Ψ x (u i)` for every `x ∈ P`.
-- The aggregation hypothesis upgrades this to `f xStar ≤ Ψ x uBar` on `P`,
-- so `f xStar` is a lower bound for the image of `x ↦ Ψ x uBar` on `P`. The
-- faithful upper-envelope bridge gives `Ψ xStar uBar ≤ f xStar`, and for
-- every `u ∈ S` we also have `Ψ xStar u ≤ f xStar`. Combining these two
-- bounds yields `Ψ xStar u ≤ Ψ x uBar` for all `x ∈ P` and `u ∈ S`, i.e. the canonical saddle
-- relation `IsSaddlePointOn P S Ψ xStar uBar`.
theorem exists_saddle_parameter_of_active_subgradient_representation
    {P : Set E} {S : Set U} {Ψ : E → U → ℝ} {f : E → ℝ}
    {xStar gStar : E}
    (hf_eq :
      ∀ ⦃x : E⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    (hxStar_min : IsMinOn f P xStar)
    (hgStar_mem : gStar ∈ ∂[P] f(xStar))
    (horth : ∀ ⦃x : E⦄, x ∈ P → inner ℝ gStar (x - xStar) = 0)
    (weights : StdSimplex ℝ ι)
    (u : ι → U) (g : ι → E)
    (hu_active :
      ∀ i : ι,
        u i ∈ activePointwiseSupremumOnIndices S
          (fun x u ↦ (Ψ x u : WithTop ℝ)) xStar)
    (hg_mem :
      ∀ i : ι, g i ∈ ∂[P] ((fun x ↦ Ψ x (u i)) : E → ℝ) (xStar))
    (hgStar_repr : gStar = ∑ i, weights.weights i • g i)
    (haggregate :
      ∃ uBar ∈ S,
        ∀ ⦃x : E⦄, x ∈ P →
          ∑ i, weights.weights i * Ψ x (u i) ≤ Ψ x uBar) :
    ∃ uBar ∈ S, IsSaddlePointOn P S Ψ xStar uBar := by
  -- The feasible membership of `xStar` comes from the relative-subgradient hypothesis.
  rw [mem_subdifferentialWithin_iff] at hgStar_mem
  rcases hgStar_mem with ⟨hxStar, -⟩
  rcases haggregate with ⟨uBar, huBar, huBar_dom⟩
  have hsum : ∑ i, weights.weights i = 1 := by
    simpa [Finsupp.sum_fintype] using weights.total
  -- Active indices lie in `S` and realize the objective value at `xStar`.
  have hactive_value : ∀ i : ι, u i ∈ S ∧ Ψ xStar (u i) = f xStar := by
    intro i
    rcases (mem_activePointwiseSupremumOnIndices_iff.mp (hu_active i)) with ⟨huS, huEq⟩
    refine ⟨huS, ?_⟩
    apply WithTop.coe_injective
    calc
      (Ψ xStar (u i) : WithTop ℝ)
          = pointwiseSupremumOn S (fun x u ↦ (Ψ x u : WithTop ℝ)) xStar := huEq
      _ = (f xStar : WithTop ℝ) := by
        symm
        exact hf_eq hxStar
  -- Every slice at `xStar` lies below the upper-envelope value `f xStar`.
  have hslice_le : ∀ ⦃y : U⦄, y ∈ S → Ψ xStar y ≤ f xStar := by
    intro y hy
    have hySup :
        (Ψ xStar y : WithTop ℝ) ≤
          pointwiseSupremumOn S (fun x u ↦ (Ψ x u : WithTop ℝ)) xStar := by
      rw [pointwiseSupremumOn_apply]
      refine le_csSup ?_ ?_
      · exact ⟨⊤, fun _ _ ↦ le_top⟩
      · exact ⟨y, hy, rfl⟩
    have hySup' : (Ψ xStar y : WithTop ℝ) ≤ (f xStar : WithTop ℝ) := by
      simpa [hf_eq hxStar] using hySup
    exact_mod_cast hySup'
  refine ⟨uBar, huBar, ?_⟩
  intro x hx y hy
  -- Sum the active-slice subgradient inequalities with the simplex weights.
  have hweighted_gap :
      ∑ i, weights.weights i * inner ℝ (g i) (x - xStar) ≤
        ∑ i, weights.weights i * (Ψ x (u i) - Ψ xStar (u i)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hsubgrad_i :
        inner ℝ (g i) (x - xStar) ≤ Ψ x (u i) - Ψ xStar (u i) := by
      rcases (mem_subdifferentialWithin_iff.mp (hg_mem i)) with ⟨-, hminorant⟩
      have hminorant_x := hminorant hx
      linarith
    exact mul_le_mul_of_nonneg_left hsubgrad_i (weights.nonneg i)
  have horth_sum :
      ∑ i, weights.weights i * inner ℝ (g i) (x - xStar) = 0 := by
    have hrepr :
        inner ℝ gStar (x - xStar) =
          ∑ i, weights.weights i * inner ℝ (g i) (x - xStar) := by
      calc
        inner ℝ gStar (x - xStar)
            = inner ℝ (∑ i, weights.weights i • g i) (x - xStar) := by
                rw [hgStar_repr]
        _ = ∑ i, inner ℝ (weights.weights i • g i) (x - xStar) := by
          rw [sum_inner]
        _ = ∑ i, weights.weights i * inner ℝ (g i) (x - xStar) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa using
            (inner_smul_left_eq_smul (x := g i) (y := x - xStar) (r := weights.weights i))
    rw [← hrepr, horth hx]
  have hgap_nonneg :
      0 ≤ ∑ i, weights.weights i * (Ψ x (u i) - Ψ xStar (u i)) := by
    simpa [horth_sum] using hweighted_gap
  have hactive_sum :
      ∑ i, weights.weights i * Ψ xStar (u i) = f xStar := by
    calc
      ∑ i, weights.weights i * Ψ xStar (u i)
          = ∑ i, weights.weights i * f xStar := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [(hactive_value i).2]
      _ = (∑ i, weights.weights i) * f xStar := by
        rw [Finset.sum_mul]
      _ = f xStar := by
        rw [hsum, one_mul]
  have hobjective_le_weighted :
      f xStar ≤ ∑ i, weights.weights i * Ψ x (u i) := by
    have hrewrite :
        ∑ i, weights.weights i * (Ψ x (u i) - Ψ xStar (u i)) =
          ∑ i, weights.weights i * Ψ x (u i) - f xStar := by
      calc
        ∑ i, weights.weights i * (Ψ x (u i) - Ψ xStar (u i))
            = ∑ i, (weights.weights i * Ψ x (u i) - weights.weights i * Ψ xStar (u i)) := by
                simp_rw [mul_sub]
        _ = (∑ i, weights.weights i * Ψ x (u i)) -
              ∑ i, weights.weights i * Ψ xStar (u i) := by
                rw [Finset.sum_sub_distrib]
        _ = ∑ i, weights.weights i * Ψ x (u i) - f xStar := by
          rw [hactive_sum]
    rw [hrewrite] at hgap_nonneg
    linarith
  -- The aggregation witness upgrades the weighted lower bound to a single parameter `uBar`.
  have hobjective_le_uBar : f xStar ≤ Ψ x uBar := by
    exact le_trans hobjective_le_weighted (huBar_dom hx)
  -- Sandwich both sides through `f xStar` to obtain the saddle inequality.
  exact le_trans (hslice_le hy) hobjective_le_uBar

end
