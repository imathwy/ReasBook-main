import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_0
import ConvexAnalysis_Rockafellar_1970.Chap04.Corollary_19_3_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_8
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_19_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section PairSumPrimitive

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]

variable {f₁ f₂ : E → WithTopBot 𝕜}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 19.3.4 states that the infimal convolution of two proper polyhedral
  convex functions on `R^n` is again polyhedral convex, and that when this infimal convolution is
  proper its defining infimum is attained pointwise.
- `core/canonical`: the existing owner declarations are `infimal_convolution`,
  `Function.linearImage` and `Function.HasPolyhedralEpigraph` at
  codomain `WithTopBot 𝕜`.
- `bridge/view`: the textbook infimal convolution is the linear image of the pair-space sum
  `(u, v) ↦ f₁ u + f₂ v` on the intrinsic product space `E × E` under the canonical addition map
  `(u, v) ↦ u + v`. The attainment clause is then the owner-side linear-image attainment theorem,
  rewritten in the textbook variable order `f₁ (x - y) + f₂ y`.

Domain-style sampling used here:
- `infimal_convolution`;
- `Function.linearImage`;
- `infimal_convolution_eq_sInf_decompositions`;
- `Function.HasPolyhedralEpigraph.comp_linearMap`;
- `Function.HasPolyhedralEpigraph`;
- `Function.HasPolyhedralEpigraph.add_of_ne_bot`.

Primitive data vs derived API:
- primitive owner inputs: the two functions `f₁`, `f₂`;
- source hypotheses: each input has polyhedral epigraph and never takes the value `⊥`; the
  separate textbook convexity adjective is not kept as primitive data because the Chapter 19 owner
  `Function.HasPolyhedralEpigraph` already encodes the relevant epigraph-side convexity;
- derived API: the pair-space sum function on `E × E`, the linear-image
  identification of `f₁ □ f₂`, polyhedrality of `f₁ □ f₂`, and its pointwise attainment under the
  primitive output-side assumption that `f₁ □ f₂` never takes `⊥`.

Layer target: `source-facing`, expressed directly with the Chapter 19 owners
`Function.HasPolyhedralEpigraph` and `infimal_convolution` on an arbitrary finite-dimensional
Hausdorff topological module over an ordered topological field. The textbook
`R^n`
formulation is recovered by specialization, and the pair-space `Function.linearImage`
presentation is kept internal as the canonical bridge via the intrinsic product owner rather than
through Euclidean coordinates.
-/

/-- Pulling back along the two product-coordinate projections and then adding gives the pair-space
sum function `(u, v) ↦ f₁ u + f₂ v` a polyhedral epigraph. -/
private theorem hasPolyhedralEpigraph_pairSum
    (hf₁ : f₁.HasPolyhedralEpigraph)
    (hf₁_ne_bot : ∀ x : E, f₁ x ≠ ⊥)
    (hf₂ : f₂.HasPolyhedralEpigraph)
    (hf₂_ne_bot : ∀ x : E, f₂ x ≠ ⊥) :
    (fun p : E × E ↦ f₁ p.1 + f₂ p.2).HasPolyhedralEpigraph := by
  have hfst : (fun p : E × E ↦ f₁ p.1).HasPolyhedralEpigraph := by
    simpa [Function.comp] using hf₁.comp_linearMap (LinearMap.fst 𝕜 E E)
  have hsnd : (fun p : E × E ↦ f₂ p.2).HasPolyhedralEpigraph := by
    simpa [Function.comp] using hf₂.comp_linearMap (LinearMap.snd 𝕜 E E)
  exact
    Function.HasPolyhedralEpigraph.add_of_ne_bot hfst hsnd
      (fun p ↦ hf₁_ne_bot p.1)
      (fun p ↦ hf₂_ne_bot p.2)

end PairSumPrimitive

section Main

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E] [T2Space E]

variable {f₁ f₂ : E → WithTopBot 𝕜}

namespace Function.HasPolyhedralEpigraph

-- Proof sketch: pull `f₁` and `f₂` back along the two product-coordinate projections on
-- `E × E`, use `Function.HasPolyhedralEpigraph.add_of_ne_bot` on those pullbacks to show that the
-- pair-space sum has polyhedral epigraph, and then apply Corollary 19.3.1 (1) to the
-- addition map `(u, v) ↦ u + v`.
/-- The infimal convolution of two functions with polyhedral epigraphs and no `⊥` values
again has polyhedral epigraph. -/
theorem infimal_convolution
    (hf₁ : f₁.HasPolyhedralEpigraph)
    (hf₁_ne_bot : ∀ x : E, f₁ x ≠ ⊥)
    (hf₂ : f₂.HasPolyhedralEpigraph)
    (hf₂_ne_bot : ∀ x : E, f₂ x ≠ ⊥) :
    (f₁ □ f₂).HasPolyhedralEpigraph := by
  let A : E × E →ₗ[𝕜] E := LinearMap.fst 𝕜 E E + LinearMap.snd 𝕜 E E
  have hpair :
      (fun p : E × E ↦ f₁ p.1 + f₂ p.2).HasPolyhedralEpigraph :=
    hasPolyhedralEpigraph_pairSum hf₁ hf₁_ne_bot hf₂ hf₂_ne_bot
  exact Function.HasPolyhedralEpigraph.linearImage hpair A

-- Proof sketch: apply Corollary 19.3.1 (2) to the pair-space sum function under the addition
-- map `(u, v) ↦ u + v`. The output-side hypothesis `∀ x, (f₁ □ f₂) x ≠ ⊥` rules out the value
-- `⊥`; when
-- `(f₁ □ f₂) x = ⊤`, the decomposition `(x, 0)` already forces the value `f₁ x + f₂ 0` to be
-- `⊤`, so the infimum is attained trivially. Otherwise Corollary 19.3.1 (2) gives a minimizing
-- decomposition in pair form.
/-- If `f₁` and `f₂` have polyhedral epigraphs and no `⊥` values, and if `(f₁ □ f₂)` is nowhere
`⊥`, then for each `x` there is an attained minimizing decomposition in intrinsic pair form. -/
theorem exists_pair_eq_infimal_convolution_of_ne_bot
    (hf₁ : f₁.HasPolyhedralEpigraph)
    (hf₁_ne_bot : ∀ x : E, f₁ x ≠ ⊥)
    (hf₂ : f₂.HasPolyhedralEpigraph)
    (hf₂_ne_bot : ∀ x : E, f₂ x ≠ ⊥)
    (hconv_ne_bot : ∀ x : E, (f₁ □ f₂) x ≠ ⊥) :
    ∀ x : E, ∃ p : E × E, p.1 + p.2 = x ∧ (f₁ □ f₂) x = f₁ p.1 + f₂ p.2 := by
  let A : E × E →ₗ[𝕜] E := LinearMap.fst 𝕜 E E + LinearMap.snd 𝕜 E E
  have hpair :
      (fun p : E × E ↦ f₁ p.1 + f₂ p.2).HasPolyhedralEpigraph :=
    hasPolyhedralEpigraph_pairSum hf₁ hf₁_ne_bot hf₂ hf₂_ne_bot
  intro x
  by_cases htop : (f₁ □ f₂) x = ⊤
  · refine ⟨(x, 0), by simp, ?_⟩
    have hx_le : (f₁ □ f₂) x ≤ f₁ x + f₂ 0 := by
      rw [infimal_convolution_eq_sInf_decompositions]
      exact sInf_le ⟨(x, 0), by simp, rfl⟩
    have htop_le_sum : (⊤ : WithTopBot 𝕜) ≤ f₁ x + f₂ 0 := by
      exact htop ▸ hx_le
    have hsum_top : f₁ x + f₂ 0 = ⊤ := by
      exact top_le_iff.mp htop_le_sum
    simpa [htop, hsum_top]
  · have hfinite : ⊥ < (f₁ □ f₂) x ∧ (f₁ □ f₂) x < ⊤ := by
      exact ⟨WithTopBot.bot_lt_iff_ne_bot.mpr (hconv_ne_bot x), lt_of_le_of_ne le_top htop⟩
    have hlinear_dom :
        x ∈ dom(Function.linearImage A (fun p : E × E ↦ f₁ p.1 + f₂ p.2)) := by
      change (f₁ □ f₂) x < ⊤
      exact hfinite.2
    have hlinear_ne_bot :
        Function.linearImage A (fun p : E × E ↦ f₁ p.1 + f₂ p.2) x ≠ ⊥ := by
      change (f₁ □ f₂) x ≠ ⊥
      exact ne_of_gt hfinite.1
    rcases
      Function.HasPolyhedralEpigraph.linearImage_attains_of_ne_bot_of_mem_dom
        hpair A x hlinear_dom hlinear_ne_bot with ⟨p, hp, hpval⟩
    have hsum : p.1 + p.2 = x := by
      simpa [A, LinearMap.add_apply] using hp
    have hvalue : (f₁ □ f₂) x = f₁ p.1 + f₂ p.2 := by
      change Function.linearImage A (fun p : E × E ↦ f₁ p.1 + f₂ p.2) x = f₁ p.1 + f₂ p.2
      exact hpval.symm
    exact ⟨p, hsum, hvalue⟩

/-- Bridge form of attainment in the textbook variable order `f₁ (x - y) + f₂ y`. -/
theorem exists_argmin_infimal_convolution_of_ne_bot
    (hf₁ : f₁.HasPolyhedralEpigraph)
    (hf₁_ne_bot : ∀ x : E, f₁ x ≠ ⊥)
    (hf₂ : f₂.HasPolyhedralEpigraph)
    (hf₂_ne_bot : ∀ x : E, f₂ x ≠ ⊥)
    (hconv_ne_bot : ∀ x : E, (f₁ □ f₂) x ≠ ⊥) :
    ∀ x : E, ∃ y : E, (f₁ □ f₂) x = f₁ (x - y) + f₂ y := by
  intro x
  rcases
    hf₁.exists_pair_eq_infimal_convolution_of_ne_bot
      hf₁_ne_bot hf₂ hf₂_ne_bot hconv_ne_bot x with
    ⟨p, hp_sum, hp_value⟩
  refine ⟨p.2, ?_⟩
  have hp₁ : x - p.2 = p.1 := by
    rw [sub_eq_iff_eq_add]
    simpa [add_comm, add_left_comm, add_assoc] using hp_sum.symm
  simpa [hp₁] using hp_value

end Function.HasPolyhedralEpigraph

/-- Corollary 19.3.4: if `f₁` and `f₂` have polyhedral epigraphs and never take the value
`⊥`, then their infimal convolution `f₁ □ f₂` has polyhedral epigraph; moreover, if
`f₁ □ f₂` is nowhere `⊥`, then for each `x` the infimum in the definition of `(f₁ □ f₂) x` is
attained. This keeps the attainment side on primitive codomain data rather than a stronger derived
owner. -/
theorem polyhedral_infimalConvolution_and_attainment_of_hasPolyhedralEpigraph
    (hf₁_poly : f₁.HasPolyhedralEpigraph)
    (hf₁_ne_bot : ∀ x : E, f₁ x ≠ ⊥)
    (hf₂_poly : f₂.HasPolyhedralEpigraph)
    (hf₂_ne_bot : ∀ x : E, f₂ x ≠ ⊥) :
    (f₁ □ f₂).HasPolyhedralEpigraph ∧
      ((∀ x : E, (f₁ □ f₂) x ≠ ⊥) →
        ∀ x : E, ∃ y : E, (f₁ □ f₂) x = f₁ (x - y) + f₂ y) := by
  constructor
  · exact hf₁_poly.infimal_convolution hf₁_ne_bot hf₂_poly hf₂_ne_bot
  · intro hconv_ne_bot x
    exact
      hf₁_poly.exists_argmin_infimal_convolution_of_ne_bot
        hf₁_ne_bot hf₂_poly hf₂_ne_bot hconv_ne_bot x

end Main
