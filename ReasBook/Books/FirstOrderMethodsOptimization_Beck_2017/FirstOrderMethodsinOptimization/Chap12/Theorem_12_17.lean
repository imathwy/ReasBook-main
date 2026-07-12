import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_30
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_14
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_15
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_17
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_15
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Lemma_12_7
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Lemma_12_15

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Metric

section

variable {E : Type u} {p : ℕ}
variable [NeZero p]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- `prompt_add/` is absent in this workspace, so the owner-abstraction review is done against
mathlib and nearby project files. This item is `source-facing`: it is the cyclic-order `O(1 / k)`
rate statement for the Chapter 12 dual block proximal-gradient method. Domain sampling against the
local API shows that the right owner surface is:
- `IsDualBlockProximalGradientProblem` for the standing Assumption 12.14 data;
- `is_dual_block_proximal_gradient_primal_trajectory` together with
  `dual_block_proximal_gradient_cyclic_block_index` for the cyclic DBPG iterates;
- `dual_block_proximal_gradient_dual_objective` and
  `dual_block_proximal_gradient_dual_optimal_set` for the block dual objective `q` and optimal set
  `Λ*`;
- `dual_block_proximal_gradient_dual_problem_value` for the canonical dual optimum `q_opt`,
  together with `finite_domain q` and the canonical one-sided finiteness hypothesis
  `q_opt ≠ ⊤` for the explicit `.toReal` dual-gap constants; and
- `composite_model_objective f (finite_sum_objective g)` for the primal minimizer `x*`.

The bridge/view owner for the rate estimate itself is the Chapter 11 cyclic CBPG theorem
`cbpg_objective_gap_le_max_geometric_or_sublinear_of_initial_sublevel_radius`, specialized to the
dual block objective `-q`; the present file keeps only the Chapter 12 source-facing restatement in
dual-gap and primal-distance form. The stronger bounded-superlevel package
`IsDualBlockProximalGradientSuperlevelDistanceBoundedProblem` from Definition 12.18 remains only an
upstream bridge for producing the explicit theorem hypotheses `(Λ*(f, g)).Nonempty`, a witness
`R`, and the corresponding initial-superlevel distance-to-`Λ*` bound `hR`; once those are
explicit, it is not part of the main theorem surface.

The source has two independent conclusions, so the item is split into two atomic theorems. -/

section

variable (σ : PosReal) (f : E → EReal) (g : Fin p → E → EReal)
variable (y0 : Fin p → E) (x : ℕ → E) (y : ℕ → Fin p → E)

local notation "F" => composite_model_objective f (finite_sum_objective g)
local notation "x[" k "]" => x (p * k)
local notation "y[" k "]" => y (p * k)

-- Proof sketch: identify the cyclic DBPG iterates with one outer step of cyclic block proximal
-- gradient on the block dual objective `-q`, specialize the Chapter 11 cyclic objective-gap
-- estimate with `L_min = L_max = 1 / σ` and `L_f = p / σ`, and then rewrite the resulting
-- objective bound back into the dual-gap form for `q`. The radius hypothesis `hR` is the
-- canonical initial-superlevel distance-to-`Λ*` bound at level `q(y⁰)`, as provided for example
-- by Definition 12.18's derived API, while `hLambda_nonempty` keeps the source-faithful
-- nonemptiness of the optimal dual set visible on the theorem surface.

/-- Helper for Theorem 12.17: the Chapter 11 minimization surface built from the smooth dual term
`(f∗) (∑ i, y_i)` and the separable nonsmooth term `∑ i, g_i∗(-y_i)` is exactly the negation of
the source-facing block dual objective `q`. -/
lemma dual_block_dual_minimization_view_apply
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    (v : Fin p → E) :
    composite_model_objective
        (fun w : Fin p → E ↦ (f∗) (∑ i : Fin p, w i))
        (separableSum (fun i z ↦ ((g i)∗) (-z)))
        v =
      - q(f, g) v := by
  let a : EReal := (f∗) (∑ i : Fin p, v i)
  let b : EReal := ∑ i : Fin p, ((g i)∗) (-v i)
  have ha_ne_bot : a ≠ ⊥ := by
    -- Strong convexity makes the smooth conjugate term finite at every aggregated dual sum.
    have hfin :=
      conjugate_function_finite_of_proper_closed_strongConvexOn
        (σ : ℝ)
        σ.2
        f
        h_problem.toIsProperExtendedRealFunction.ne_bot
        h_problem.toIsProperExtendedRealFunction.effective_domain_nonempty
        h_problem.f_closed
        h_problem.f_strongly_convex
        (InnerProductSpace.toDual ℝ E (∑ i : Fin p, v i))
    simpa [a, conjugate_function_strongDual, conjugate_function_primal_apply,
      conjugate_function] using hfin.1
  have hb_ne_bot : b ≠ ⊥ := by
    -- Properness of each conjugate block term keeps the separable sum away from `⊥`.
    refine ereal_sum_ne_bot Finset.univ (fun i ↦ ((g i)∗) (-v i)) ?_
    intro i _
    have hg_conj_proper :
        IsProperExtendedRealFunction (conjugate_function (g i)) :=
      isProperExtendedRealFunction_conjugate_function
        (g i)
        (h_problem.g_proper i)
        (h_problem.g_convex i)
    simpa [conjugate_function_primal_apply] using
      hg_conj_proper.ne_bot (InnerProductSpace.toDualMap ℝ E (-v i))
  have ha_top : -a ≠ ⊤ := by
    -- Negating a non-`⊥` extended-real value cannot produce `⊤`.
    intro ha_top
    have : a = ⊥ := by
      simpa [a] using congrArg Neg.neg ha_top
    exact ha_ne_bot this
  have hneg : -(-a - b) = a + b := by
    -- Once the mixed `⊤/⊥` cases are excluded, the outer negation distributes through
    -- subtraction exactly as in the source formula.
    have hraw : -(-a - b) = -(-a) + b := by
      exact EReal.neg_sub (Or.inr hb_ne_bot) (Or.inl ha_top)
    simpa [a, b] using hraw
  -- Unfold the Chapter 11 composite objective and the Chapter 12 dual objective, then identify
  -- the two formulas term-by-term.
  rw [composite_model_objective_apply, separableSum_apply,
    dual_block_proximal_gradient_dual_objective_apply]
  change a + b = -(-a - b)
  simpa [a, b] using hneg.symm

/-- Helper for Theorem 12.17: finiteness of the source-facing dual value `q(v)` forces each block
dual term `g_i^*(-v_i)` to be finite above. This is the coordinatewise domain bridge needed to
feed the Chapter 11 block-separable owner from the theorem's `finite_domain (q(f, g))`
hypothesis. -/
lemma block_dual_term_mem_effective_domain_of_mem_finite_domain
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    {v : Fin p → E} (hv : v ∈ finite_domain (q(f, g))) (i : Fin p) :
    v i ∈ effective_domain (fun z : E ↦ ((g i)∗) (-z)) := by
  let a : EReal := (f∗) (∑ j : Fin p, v j)
  let G : Fin p → E → EReal := fun j z ↦ ((g j)∗) (-z)
  have hfin :=
    conjugate_function_finite_of_proper_closed_strongConvexOn
      (σ : ℝ)
      σ.2
      f
      h_problem.toIsProperExtendedRealFunction.ne_bot
      h_problem.toIsProperExtendedRealFunction.effective_domain_nonempty
      h_problem.f_closed
      h_problem.f_strongly_convex
      (InnerProductSpace.toDual ℝ E (∑ j : Fin p, v j))
  have ha_ne_bot : a ≠ ⊥ := by
    -- The smooth conjugate term is finite at the aggregated dual sum.
    simpa [a, conjugate_function_strongDual, conjugate_function_primal_apply,
      conjugate_function] using hfin.1
  have ha_ne_top : a ≠ ⊤ := by
    -- Strong convexity also rules out `⊤` for the smooth conjugate term.
    exact (lt_top_iff_ne_top.mp (by
      simpa [a, conjugate_function_strongDual, conjugate_function_primal_apply,
        conjugate_function] using hfin.2))
  have hG_proper : ∀ j : Fin p, IsProperExtendedRealFunction (G j) := by
    intro j
    let hconj :=
      isProperExtendedRealFunction_conjugate_function (g j) (h_problem.g_proper j)
        (h_problem.g_convex j)
    refine
      { ne_bot := ?_
        effective_domain_nonempty := ?_ }
    · intro z
      -- Each negated block conjugate remains proper after the sign flip.
      simpa [G, conjugate_function_primal_apply] using
        hconj.ne_bot (InnerProductSpace.toDualMap ℝ E (-z))
    · rcases hconj.effective_domain_nonempty with ⟨φ, hφ⟩
      let φc : StrongDual ℝ E := ⟨φ, φ.continuous_of_finiteDimensional⟩
      have hφ_repr :
          (InnerProductSpace.toDualMap ℝ E ((InnerProductSpace.toDual ℝ E).symm φc) :
            Module.Dual ℝ E) = φ := by
        ext x
        change (((InnerProductSpace.toDual ℝ E) ((InnerProductSpace.toDual ℝ E).symm φc)) :
            StrongDual ℝ E) x = φ x
        have hsymm := (InnerProductSpace.toDual ℝ E).apply_symm_apply φc
        simpa [φc] using congrArg (fun ψ : StrongDual ℝ E => ψ x) hsymm
      refine ⟨-((InnerProductSpace.toDual ℝ E).symm φc), ?_⟩
      simpa [G, mem_effective_domain, conjugate_function_primal_apply, hφ_repr] using hφ
  have hview :
      a + separableSum G v = - q(f, g) v := by
    -- Rewrite the Chapter 11 minimization view back to the source dual objective.
    simpa [a, G, composite_model_objective_apply] using
      (dual_block_dual_minimization_view_apply
        (σ := σ) (f := f) (g := g) h_problem v)
  have hobj_ne_top : a + separableSum G v ≠ ⊤ := by
    -- Finiteness of `q(v)` rules out `⊤` for the minimization-view objective value.
    rw [hview]
    simpa using (mem_finite_domain.mp hv).2
  have hsep_ne_top : separableSum G v ≠ ⊤ := by
    -- Remove the finite smooth conjugate term and keep the separable sum finite above.
    exact (EReal.add_ne_top_iff_ne_top_right ha_ne_bot ha_ne_top).1 hobj_ne_top
  have hsep_mem : v ∈ effective_domain (separableSum G) := by
    -- The separable block-dual regularizer is therefore finite at `v`.
    simpa [mem_effective_domain, lt_top_iff_ne_top] using hsep_ne_top
  -- Project the separable-sum finite-domain fact back to the active block `i`.
  simpa [G] using
    (block_mem_effective_domain_of_mem_separableSum_effective_domain G hG_proper hsep_mem i)

/-- Helper for Theorem 12.17: finiteness of the Chapter 11 separable dual regularizer at `v`
forces the full source-facing dual value `q(v)` to be finite. This is the forward domain bridge
from the minimization-view owner back to the theorem surface `finite_domain (q(f, g))`. -/
lemma dual_value_mem_finite_domain_of_mem_effective_domain_separable_dual
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    {v : Fin p → E}
    (hv : v ∈ effective_domain (separableSum (fun i z ↦ ((g i)∗) (-z)))) :
    v ∈ finite_domain (q(f, g)) := by
  let a : EReal := (f∗) (∑ i : Fin p, v i)
  let G : Fin p → E → EReal := fun i z ↦ ((g i)∗) (-z)
  have hfin :=
    conjugate_function_finite_of_proper_closed_strongConvexOn
      (σ : ℝ)
      σ.2
      f
      h_problem.toIsProperExtendedRealFunction.ne_bot
      h_problem.toIsProperExtendedRealFunction.effective_domain_nonempty
      h_problem.f_closed
      h_problem.f_strongly_convex
      (InnerProductSpace.toDual ℝ E (∑ i : Fin p, v i))
  have ha_ne_bot : a ≠ ⊥ := by
    -- Strong convexity makes the smooth conjugate term finite at the aggregated dual sum.
    simpa [a, conjugate_function_strongDual, conjugate_function_primal_apply,
      conjugate_function] using hfin.1
  have ha_ne_top : a ≠ ⊤ := by
    -- The same finiteness statement excludes `⊤` for the smooth conjugate term.
    exact (lt_top_iff_ne_top.mp (by
      simpa [a, conjugate_function_strongDual, conjugate_function_primal_apply,
        conjugate_function] using hfin.2))
  have hG_proper : ∀ i : Fin p, IsProperExtendedRealFunction (G i) := by
    intro i
    let hconj :=
      isProperExtendedRealFunction_conjugate_function (g i) (h_problem.g_proper i)
        (h_problem.g_convex i)
    refine
      { ne_bot := ?_
        effective_domain_nonempty := ?_ }
    · intro z
      -- Precomposing the conjugate with negation preserves properness of each block term.
      simpa [G, conjugate_function_primal_apply] using
        hconj.ne_bot (InnerProductSpace.toDualMap ℝ E (-z))
    · rcases hconj.effective_domain_nonempty with ⟨φ, hφ⟩
      let φc : StrongDual ℝ E := ⟨φ, φ.continuous_of_finiteDimensional⟩
      have hφ_repr :
          (InnerProductSpace.toDualMap ℝ E ((InnerProductSpace.toDual ℝ E).symm φc) :
            Module.Dual ℝ E) = φ := by
        ext x
        change (((InnerProductSpace.toDual ℝ E) ((InnerProductSpace.toDual ℝ E).symm φc)) :
            StrongDual ℝ E) x = φ x
        have hsymm := (InnerProductSpace.toDual ℝ E).apply_symm_apply φc
        simpa using congrArg (fun ψ : StrongDual ℝ E => ψ x) hsymm
      refine ⟨-((InnerProductSpace.toDual ℝ E).symm φc), ?_⟩
      simpa [G, mem_effective_domain, conjugate_function_primal_apply, hφ_repr] using hφ
  have hb_ne_bot : separableSum G v ≠ ⊥ := by
    -- Proper block conjugates keep the separable dual regularizer away from `⊥`.
    simpa [G, separableSum_apply] using
      (ereal_sum_ne_bot Finset.univ (fun i ↦ G i (v i))
        (fun i _ ↦ (hG_proper i).ne_bot (v i)))
  have hb_ne_top : separableSum G v ≠ ⊤ := by
    -- The Chapter 11 effective-domain hypothesis is exactly finiteness above for the separable
    -- dual regularizer.
    simpa [G, mem_effective_domain, lt_top_iff_ne_top] using hv
  have hview :
      a + separableSum G v = - q(f, g) v := by
    -- Rewrite the minimization view back to the source-facing dual objective `q`.
    simpa [a, G, composite_model_objective_apply] using
      (dual_block_dual_minimization_view_apply
        (σ := σ) (f := f) (g := g) h_problem v)
  -- With both summands finite, `-q(v)` is finite and therefore so is `q(v)`.
  rw [mem_finite_domain, mem_effective_domain, lt_top_iff_ne_top]
  constructor
  · intro hq_top
    have hab_ne_bot : a + separableSum G v ≠ ⊥ := by
      simpa [EReal.add_ne_bot_iff, ha_ne_top, hb_ne_bot] using And.intro ha_ne_bot hb_ne_bot
    have hab_eq_bot : a + separableSum G v = ⊥ := by
      rw [hview]
      simpa [hq_top]
    exact hab_ne_bot hab_eq_bot
  · intro hq_bot
    have hab_eq_top : a + separableSum G v = ⊤ := by
      rw [hview]
      simpa [hq_bot]
    exact (EReal.add_ne_top ha_ne_top hb_ne_top) hab_eq_top

/-- Helper for Theorem 12.17: the theorem hypothesis phrased as an initial superlevel radius bound
for `q` is exactly the initial sublevel radius bound for the Chapter 11 minimization view
`Hdual = -q`. -/
lemma dual_block_initial_sublevel_radius_on_minimization_view
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    (R : PosReal)
    (hR :
      ∀ ⦃yBar : Fin p → E⦄,
        q(f, g) y0 ≤ q(f, g) yBar →
          infDist yBar (Λ*(f, g)) ≤ (R : ℝ))
    {yBar : Fin p → E}
    (hyBar :
      composite_model_objective
          (fun w : Fin p → E ↦ (f∗) (∑ i : Fin p, w i))
          (separableSum (fun i z ↦ ((g i)∗) (-z)))
          yBar ≤
        composite_model_objective
          (fun w : Fin p → E ↦ (f∗) (∑ i : Fin p, w i))
          (separableSum (fun i z ↦ ((g i)∗) (-z)))
          y0) :
    infDist yBar (Λ*(f, g)) ≤ (R : ℝ) := by
  have hq :
      q(f, g) y0 ≤ q(f, g) yBar := by
    -- Rewrite `Hdual = -q` on both sides, then negate the minimization-view inequality.
    rw [dual_block_dual_minimization_view_apply
        (σ := σ) (f := f) (g := g) h_problem yBar,
      dual_block_dual_minimization_view_apply
        (σ := σ) (f := f) (g := g) h_problem y0] at hyBar
    simpa using (EReal.neg_le_neg_iff.mp hyBar)
  -- Return to the source-facing radius hypothesis on the dual objective `q`.
  exact hR hq

/-- Helper for Theorem 12.17: relative-interior points in two finite-dimensional sets combine into
the relative interior of their Cartesian product. -/
private theorem mem_intrinsicInterior_prod
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {S : Set E} {T : Set V} {x : E} {z : V}
    (hx : x ∈ intrinsicInterior ℝ S)
    (hz : z ∈ intrinsicInterior ℝ T) :
    (x, z) ∈ intrinsicInterior ℝ (S ×ˢ T) := by
  -- Push the source witnesses through the closed-ball characterization of intrinsic interior.
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hx with
    ⟨hx_span, εS, hεS, hballS⟩
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hz with
    ⟨hz_span, εT, hεT, hballT⟩
  refine (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).2 ?_
  refine ⟨subset_affineSpan ℝ (S ×ˢ T) ⟨intrinsicInterior_subset hx, intrinsicInterior_subset hz⟩,
    min εS εT, lt_min hεS hεT, ?_⟩
  intro uv huv
  rcases uv with ⟨u, v⟩
  rcases huv with ⟨huv_ball, huv_span⟩
  have huv_dist : max (dist u x) (dist v z) ≤ min εS εT := by
    simpa [Prod.dist_eq, max_comm, max_left_comm, max_assoc] using huv_ball
  have hu_ball : u ∈ Metric.closedBall x εS := by
    exact Metric.mem_closedBall.2 <|
      le_trans ((max_le_iff.1 huv_dist).1) (min_le_left εS εT)
  have hv_ball : v ∈ Metric.closedBall z εT := by
    exact Metric.mem_closedBall.2 <|
      le_trans ((max_le_iff.1 huv_dist).2) (min_le_right εS εT)
  have hu_span_prod :
      u ∈ affineSpan ℝ (((LinearMap.fst ℝ E V).toAffineMap) '' (S ×ˢ T)) := by
    have hmem_map :
        u ∈ (affineSpan ℝ (S ×ˢ T)).map ((LinearMap.fst ℝ E V).toAffineMap) := by
      simpa using
        (AffineSubspace.mem_map_of_mem (f := (LinearMap.fst ℝ E V).toAffineMap) huv_span)
    rw [AffineSubspace.map_span] at hmem_map
    exact hmem_map
  have hv_span_prod :
      v ∈ affineSpan ℝ (((LinearMap.snd ℝ E V).toAffineMap) '' (S ×ˢ T)) := by
    have hmem_map :
        v ∈ (affineSpan ℝ (S ×ˢ T)).map ((LinearMap.snd ℝ E V).toAffineMap) := by
      simpa using
        (AffineSubspace.mem_map_of_mem (f := (LinearMap.snd ℝ E V).toAffineMap) huv_span)
    rw [AffineSubspace.map_span] at hmem_map
    exact hmem_map
  have hu_span : u ∈ affineSpan ℝ S := by
    refine (affineSpan_mono ℝ ?_) hu_span_prod
    intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    exact hp.1
  have hv_span : v ∈ affineSpan ℝ T := by
    refine (affineSpan_mono ℝ ?_) hv_span_prod
    intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    exact hp.2
  exact ⟨hballS ⟨hu_ball, hu_span⟩, hballT ⟨hv_ball, hv_span⟩⟩

/-- Helper for Theorem 12.17: the `PiLp` separable-sum effective domain is the pullback of the
raw coordinatewise effective-domain product through the canonical coordinate equivalence. -/
lemma effective_domain_piLp_separableSum_eq_preimage_raw_product
    (hg_proper : ∀ i : Fin p, IsProperExtendedRealFunction (g i)) :
    let e := PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E)
    effective_domain (PiLp.separableSum g) =
      e ⁻¹' Set.pi Set.univ (fun i => effective_domain (g i)) := by
  let e := PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E)
  -- Rewrite `PiLp.separableSum` coordinatewise and read off the coordinatewise domain condition.
  ext z
  constructor
  · intro hz
    rw [Set.mem_preimage, Set.mem_univ_pi]
    intro i
    have hz_raw : e z ∈ effective_domain (separableSum g) := by
      simpa [mem_effective_domain, PiLp.separableSum_apply, e] using hz
    exact
      block_mem_effective_domain_of_mem_separableSum_effective_domain
        g hg_proper hz_raw i
  · intro hz
    rw [Set.mem_preimage, Set.mem_univ_pi] at hz
    rw [mem_effective_domain, PiLp.separableSum_apply]
    exact
      ereal_sum_lt_top Finset.univ
        (fun i ↦ g i (z.ofLp i))
        (fun i _ ↦ mem_effective_domain.mp (hz i))

/-- Helper for Theorem 12.17: intrinsic-interior membership pulls back along a continuous linear
equivalence. -/
lemma mem_intrinsicInterior_preimage_of_continuousLinearEquiv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (e : V ≃L[ℝ] W) {s : Set W} {x : V}
    (hx : e x ∈ intrinsicInterior ℝ s) :
    x ∈ intrinsicInterior ℝ (e ⁻¹' s) := by
  let eA : V ≃ᵃ[ℝ] W := e.toContinuousAffineEquiv.toAffineEquiv
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hx with
    ⟨hx_span, ε, hε, hball⟩
  have hx_mem_preimage : x ∈ e ⁻¹' s := by
    simpa using intrinsicInterior_subset hx
  have hx_preimage : x ∈ affineSpan ℝ (e ⁻¹' s) := by
    exact subset_affineSpan ℝ (e ⁻¹' s) hx_mem_preimage
  have hnhds :
      e ⁻¹' Metric.ball (e x) ε ∈ nhds x := by
    exact e.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
  rcases Metric.mem_nhds_iff.1 hnhds with ⟨δ, hδ, hδball⟩
  refine (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).2 ?_
  refine ⟨hx_preimage, δ / 2, by positivity, ?_⟩
  intro u hu
  rcases hu with ⟨hu_ball, hu_span⟩
  have hu_ball' : u ∈ Metric.ball x δ := by
    refine Metric.closedBall_subset_ball ?_ hu_ball
    linarith
  have heu_ball : e u ∈ Metric.ball (e x) ε := hδball hu_ball'
  have heu_span_map :
      e u ∈ (affineSpan ℝ (e ⁻¹' s)).map eA.toAffineMap := by
    simpa [eA] using
      (AffineSubspace.mem_map_of_mem (f := eA.toAffineMap) hu_span)
  have heu_span :
      e u ∈ affineSpan ℝ s := by
    rw [AffineSubspace.map_span] at heu_span_map
    exact (affineSpan_mono ℝ (Set.image_preimage_subset e s)) heu_span_map
  exact hball ⟨Metric.mem_closedBall.2 (le_of_lt heu_ball), heu_span⟩

/-- Helper for Theorem 12.17: coordinatewise intrinsic-interior membership places the full block
vector in the intrinsic interior of the raw coordinate product. -/
lemma mem_intrinsicInterior_univ_pi_of_forall
    {s : Fin p → Set E} {v : Fin p → E}
    (hv : ∀ i : Fin p, v i ∈ intrinsicInterior ℝ (s i)) :
    v ∈ intrinsicInterior ℝ (Set.pi Set.univ s) := by
  classical
  induction p with
  | zero =>
      have hpi : Set.pi Set.univ s = (Set.univ : Set (Fin 0 → E)) := by
        ext w
        constructor
        · intro _
          trivial
        · intro _
          rw [Set.mem_pi]
          intro i hi
          exact Fin.elim0 i
      have huniv : v ∈ intrinsicInterior ℝ (Set.univ : Set (Fin 0 → E)) := by
        simp [intrinsicInterior]
      simpa [hpi, intrinsicInterior] using huniv
  | succ p ih =>
      let e : (Fin (p + 1) → E) ≃L[ℝ] E × (Fin p → E) :=
        (Fin.consLinearEquiv ℝ (fun _ : Fin (p + 1) ↦ E)).symm.toContinuousLinearEquiv
      have hhead : v 0 ∈ intrinsicInterior ℝ (s 0) := hv 0
      have htail :
          (fun i : Fin p ↦ v i.succ) ∈
            intrinsicInterior ℝ (Set.pi Set.univ (fun i : Fin p ↦ s i.succ)) :=
        ih (fun i ↦ hv i.succ)
      have hprod :
          e v ∈
            intrinsicInterior ℝ
              (s 0 ×ˢ Set.pi Set.univ (fun i : Fin p ↦ s i.succ)) := by
        -- Split the finite product into its head coordinate and the remaining tail family.
        simpa [e, Fin.tail] using
          (mem_intrinsicInterior_prod (x := v 0) (z := fun i : Fin p ↦ v i.succ) hhead htail)
      have hpre :
          v ∈ intrinsicInterior ℝ (e ⁻¹' (s 0 ×ˢ Set.pi Set.univ (fun i : Fin p ↦ s i.succ))) :=
        mem_intrinsicInterior_preimage_of_continuousLinearEquiv (e := e) hprod
      have hset :
          e ⁻¹' (s 0 ×ˢ Set.pi Set.univ (fun i : Fin p ↦ s i.succ)) = Set.pi Set.univ s := by
        ext w
        constructor
        · intro hw
          have hw' : w 0 ∈ s 0 ∧ ∀ i : Fin p, w i.succ ∈ s i.succ := by
            simpa [e, Fin.tail] using hw
          rw [Set.mem_pi]
          intro i hi
          refine Fin.cases ?_ ?_ i
          · simpa using hw'.1
          · intro j
            simpa using hw'.2 j
        · intro hw
          rw [Set.mem_pi] at hw
          have hmem0 : (0 : Fin (p + 1)) ∈ Set.univ := by
            simp
          have hhead' : w 0 ∈ s 0 := hw 0 hmem0
          have htail' : ∀ i : Fin p, w i.succ ∈ s i.succ := by
            intro i
            have hmemsucc : i.succ ∈ Set.univ := by
              simp
            exact hw i.succ hmemsucc
          simpa [e, Fin.tail] using And.intro hhead' htail'
      rwa [hset] at hpre

/-- Helper for Theorem 12.17: the duplicated block vector inherits a `PiLp` intrinsic-interior
witness from the coordinatewise block qualification. -/
lemma piLp_separableSum_qualification_of_block_qualification
    (hg_proper : ∀ i : Fin p, IsProperExtendedRealFunction (g i))
    {xHat : E}
    (hxHat_g : ∀ i : Fin p, xHat ∈ intrinsicInterior ℝ (effective_domain (g i))) :
    (dual_block_duplication E p).toLinearMap xHat ∈
      intrinsicInterior ℝ (effective_domain (PiLp.separableSum g)) := by
  let e := PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E)
  have hraw :
      e ((dual_block_duplication E p).toLinearMap xHat) ∈
        intrinsicInterior ℝ (Set.pi Set.univ (fun i => effective_domain (g i))) := by
    -- First build the raw product witness from the coordinatewise qualification assumptions.
    simpa [e, dual_block_duplication_apply] using
      (mem_intrinsicInterior_univ_pi_of_forall
        (s := fun i => effective_domain (g i))
        (v := fun _ : Fin p ↦ xHat)
        hxHat_g)
  -- Then pull that witness back to the `PiLp` owner through the coordinate equivalence.
  rw [effective_domain_piLp_separableSum_eq_preimage_raw_product (g := g) hg_proper]
  exact mem_intrinsicInterior_preimage_of_continuousLinearEquiv (e := e) hraw

/-- Helper for Theorem 12.17: Assumption 12.14 should induce the Chapter 12.1 owner for the
duplicated `PiLp` block-space model used in Lemma 12.7. -/
lemma dual_block_problem_to_duplicated_dual_based_problem
    (h_problem : IsDualBlockProximalGradientProblem f g σ) :
    IsDualBasedProximalGradientProblem
      f
      (PiLp.separableSum g)
      (dual_block_duplication E p).toLinearMap
      σ := by
  -- Populate the duplicated Chapter 12.1 owner directly from the block assumptions. The only
  -- nontrivial step is transporting the coordinatewise qualification witness to `PiLp`.
  let e := PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E)
  have hsum_proper :
      IsProperExtendedRealFunction (separableSum g) :=
    separableSum_proper g h_problem.g_proper
  have hsum_closed :
      LowerSemicontinuous (separableSum g) :=
    separableSum_closed g h_problem.g_closed
  have hsum_convex :
      is_convex_function (separableSum g) :=
    separableSum_convex g h_problem.g_convex
  refine
    { toIsProperExtendedRealFunction := h_problem.toIsProperExtendedRealFunction
      f_closed := h_problem.f_closed
      f_strongly_convex := h_problem.f_strongly_convex
      g_proper := by
        refine
          { ne_bot := ?_
            effective_domain_nonempty := ?_ }
        · intro z
          simpa [PiLp.separableSum, e] using hsum_proper.ne_bot (e z)
        · rcases hsum_proper.effective_domain_nonempty with ⟨z, hz⟩
          refine ⟨e.symm z, ?_⟩
          simpa [PiLp.separableSum, e, mem_effective_domain] using hz
      g_closed := by
        -- Lower semicontinuity transports along the coordinate equivalence to the duplicated
        -- `PiLp` owner.
        simpa [Function.comp, PiLp.separableSum, e] using hsum_closed.comp e.continuous
      g_convex := by
        -- Convexity is preserved by precomposition with the coordinate linear equivalence.
        simpa [PiLp.separableSum, e] using
          is_convex_function_precompose_linearMap_add hsum_convex e.toLinearMap 0
      qualification := ?_ }
  rcases IsDualBlockProximalGradientProblem.exists_mem_intrinsicInterior h_problem with
    ⟨xHat, hxHat_f, hxHat_g⟩
  refine ⟨xHat, hxHat_f, ?_⟩
  exact
    piLp_separableSum_qualification_of_block_qualification
      (g := g) h_problem.g_proper (xHat := xHat) hxHat_g

/-- Helper for Theorem 12.17: the duplicated-model Chapter 12 primal argmax condition should be
equivalent to the source block-sum argmax condition at the same block vector. -/
lemma dual_primal_x_argmax_duplication_iff_sum_local
    {xBar : E} {v : Fin p → E} :
    xBar ∈
        dual_proximal_gradient_primal_x_argmax
          f
          (dual_block_duplication E p).toLinearMap
          (WithLp.toLp 2 v) ↔
      xBar ∈ dual_proximal_gradient_primal_x_argmax f LinearMap.id (∑ i : Fin p, v i) := by
  -- Rewrite both owners to the canonical `IsMaxOn` condition and normalize the duplication
  -- adjoint to the block sum.
  rw [mem_dual_proximal_gradient_primal_x_argmax_iff,
    mem_dual_proximal_gradient_primal_x_argmax_iff]
  have hadj := by
    -- The adjoint of the duplication operator is exactly the block sum on `PiLp`.
    simpa using
      (dual_block_duplication_linear_adjoint_apply
        (E := E) (p := p) (y := WithLp.toLp 2 v))
  constructor <;> intro hx <;> simpa [dual_block_duplication, hadj] using hx

/-- Helper for Theorem 12.17: the duplicated Chapter 12 dual problem value on `PiLp` agrees with
the source-facing block dual value `q_opt`. -/
lemma dual_block_problem_value_eq_duplicated_dual_problem_value
    (h_problem : IsDualBlockProximalGradientProblem f g σ) :
    dual_based_proximal_gradient_lagrange_dual_problem_value
        f
        (PiLp.separableSum g)
        (dual_block_duplication E p) =
      q_opt(f, g) := by
  let Y := PiLp (2 : ENNReal) (fun _ : Fin p ↦ E)
  -- Compare the two optimal values as suprema of the same pointwise objective, viewed once on the
  -- dual space and once on the primal block space through the Riesz identification.
  rw [dual_based_proximal_gradient_lagrange_dual_problem_value,
    dual_block_proximal_gradient_dual_problem_value_eq_sSup]
  apply le_antisymm
  · refine sSup_le ?_
    rintro z ⟨φ, rfl⟩
    let φc : StrongDual ℝ Y := LinearMap.toContinuousLinearMap φ
    rcases (InnerProductSpace.toDual ℝ Y).surjective φc with ⟨v, hv⟩
    have hφ : φ = InnerProductSpace.toDualMap ℝ Y v := by
      ext w
      have hw := congrArg (fun ψ : StrongDual ℝ Y => ψ w) hv.symm
      simpa [φc, Y, InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hw
    -- Rewrite the dual-space witness as a primal-space block vector, then use the source-facing
    -- block-dual objective formula from Definition 12.17.
    rw [hφ]
    have hobj :
        dual_based_proximal_gradient_lagrange_dual_objective_primal
            f
            (PiLp.separableSum g)
            (dual_block_duplication E p)
            v =
          q(f, g) v := by
      simpa [Y] using
        (dual_block_proximal_gradient_lagrange_dual_objective_primal_eq_dual_objective
          (f := f) (g := g)
          (h_ne_bot := fun i x ↦ (h_problem.g_proper i).ne_bot x)
          v)
    have hs :
        q(f, g) v ≤ sSup (Set.range (q(f, g))) :=
      le_sSup ⟨v, rfl⟩
    exact hobj.le.trans hs
  · refine sSup_le ?_
    rintro z ⟨v, rfl⟩
    have hobj :
        dual_based_proximal_gradient_lagrange_dual_objective_primal
            f
            (PiLp.separableSum g)
            (dual_block_duplication E p)
            (WithLp.toLp 2 v) =
          q(f, g) v := by
      simpa [PiLp.toLp_apply] using
        (dual_block_proximal_gradient_lagrange_dual_objective_primal_eq_dual_objective
          (f := f) (g := g)
          (h_ne_bot := fun i x ↦ (h_problem.g_proper i).ne_bot x)
          (WithLp.toLp 2 v))
    -- Every source block vector is already a primal-space witness for the Chapter 12 dual value.
    have hsSup :
        dual_based_proximal_gradient_lagrange_dual_objective_primal
            f
            (PiLp.separableSum g)
            (dual_block_duplication E p)
            (WithLp.toLp 2 v) ≤
          sSup
            (Set.range
              (dual_based_proximal_gradient_lagrange_dual_objective
                f
                (PiLp.separableSum g)
                (dual_block_duplication E p))) :=
      le_sSup ⟨InnerProductSpace.toDualMap ℝ Y (WithLp.toLp 2 v), rfl⟩
    exact hobj.symm.le.trans hsSup

/-- Helper for Theorem 12.17: Lemma 12.7 on the duplicated block model bounds the primal squared
distance at the outer iterate `x[pk]` by the source-facing block dual gap at `y[pk]`. -/
lemma cyclic_dbpg_outer_primal_sqdist_le_dual_gap
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    (h_traj :
      is_dual_block_proximal_gradient_primal_trajectory
        f g σ (dual_block_proximal_gradient_cyclic_block_index p) y0 x y)
    (k : ℕ)
    (xStar : E) (hxStar : IsMinOn F Set.univ xStar) :
    ((((σ : ℝ) / 2) * ‖x[k] - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
      q_opt(f, g) - q(f, g) y[k] := by
  have h_problem_dup :
      IsDualBasedProximalGradientProblem
        f
        (PiLp.separableSum g)
        (dual_block_duplication E p).toLinearMap
        σ :=
    dual_block_problem_to_duplicated_dual_based_problem
      (σ := σ) (f := f) (g := g) h_problem
  have hx_argmax_sum :
      x[k] ∈ dual_proximal_gradient_primal_x_argmax
        f LinearMap.id (∑ j : Fin p, y[k] j) :=
    (is_dual_block_proximal_gradient_primal_trajectory_step h_traj (p * k)).1
  have hx_argmax_dup :
      x[k] ∈ dual_proximal_gradient_primal_x_argmax
        f
        (dual_block_duplication E p).toLinearMap
        (WithLp.toLp 2 y[k]) := by
    -- Transport the trajectory argmax condition to the duplicated `PiLp` owner used by
    -- Lemma 12.7.
    exact
      (dual_primal_x_argmax_duplication_iff_sum_local
        (f := f) (p := p) (xBar := x[k]) (v := y[k])).2 hx_argmax_sum
  have hdup_gap :
      ((((σ : ℝ) / 2) * ‖x[k] - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        dual_based_proximal_gradient_lagrange_dual_problem_value
            f
            (PiLp.separableSum g)
            (dual_block_duplication E p) -
          dual_based_proximal_gradient_lagrange_dual_objective_primal
            f
            (PiLp.separableSum g)
            (dual_block_duplication E p)
            (WithLp.toLp 2 y[k]) := by
    -- Apply Lemma 12.7 exactly on the duplicated block-space model.
    exact
      half_sigma_sqdist_le_dual_gap_of_primal_argmax
        (σ := σ)
        (f := f)
        (g := PiLp.separableSum g)
        (A := dual_block_duplication E p)
        h_problem_dup
        (WithLp.toLp 2 y[k])
        x[k]
        xStar
        hx_argmax_dup
        hxStar
  -- Rewrite the duplicated-model dual gap back to the source-facing `q_opt - q(y[ k ])`.
  calc
    ((((σ : ℝ) / 2) * ‖x[k] - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        dual_based_proximal_gradient_lagrange_dual_problem_value
            f
            (PiLp.separableSum g)
            (dual_block_duplication E p) -
          dual_based_proximal_gradient_lagrange_dual_objective_primal
            f
            (PiLp.separableSum g)
            (dual_block_duplication E p)
            (WithLp.toLp 2 y[k]) :=
      hdup_gap
    _ = q_opt(f, g) - q(f, g) y[k] := by
      rw [dual_block_problem_value_eq_duplicated_dual_problem_value
        (σ := σ) (f := f) (g := g) h_problem]
      simpa [PiLp.toLp_apply] using
        congrArg
          (fun t : EReal =>
            q_opt(f, g) - t)
          (dual_block_proximal_gradient_lagrange_dual_objective_primal_eq_dual_objective
            (f := f) (g := g)
            (h_ne_bot := fun i x ↦ (h_problem.g_proper i).ne_bot x)
            (WithLp.toLp 2 y[k]))

/-- Helper for Theorem 12.17: every source-facing dual value is bounded above by the canonical
dual optimum `q_opt`. -/
lemma dual_objective_le_dual_problem_value
    (v : Fin p → E) :
    q(f, g) v ≤ q_opt(f, g) := by
  -- Unfold `q_opt` as the supremum of the dual-objective range and insert the concrete point `v`.
  rw [dual_block_proximal_gradient_dual_problem_value_eq_sSup]
  exact le_sSup ⟨v, rfl⟩

/-- Helper for Theorem 12.17: a single finite dual point already rules out the degenerate value
`q_opt = ⊥`. -/
lemma dual_problem_value_ne_bot_of_finite_witness
    {v : Fin p → E} (hv : v ∈ finite_domain (q(f, g))) :
    q_opt(f, g) ≠ ⊥ := by
  have hv_le : q(f, g) v ≤ q_opt(f, g) :=
    dual_objective_le_dual_problem_value (f := f) (g := g) v
  intro hqOpt_bot
  have hv_bot : q(f, g) v = ⊥ := by
    exact le_bot_iff.mp (by simpa [hqOpt_bot] using hv_le)
  exact (mem_finite_domain.mp hv).2 hv_bot

/-- Helper for Theorem 12.17: once `q_opt` is finite above, every optimal dual point lies in the
finite domain of `q`. -/
lemma optimal_dual_point_mem_finite_domain_of_finite_witness
    {v yStar : Fin p → E}
    (hv : v ∈ finite_domain (q(f, g)))
    (hyStar : yStar ∈ Λ*(f, g))
    (hqOpt_ne_top : q_opt(f, g) ≠ ⊤) :
    yStar ∈ finite_domain (q(f, g)) := by
  -- Rewrite the optimal value at `yStar` to `q_opt`, then use the witness `v` to exclude `⊥`.
  rw [mem_finite_domain, mem_effective_domain,
    dual_block_proximal_gradient_dual_objective_eq_dual_problem_value_of_mem_optimal_set
      f g hyStar]
  refine ⟨lt_top_iff_ne_top.mpr hqOpt_ne_top, ?_⟩
  exact dual_problem_value_ne_bot_of_finite_witness (f := f) (g := g) hv

/-- Helper for Theorem 12.17: once the optimal value and the comparison dual point are finite, the
source-facing `EReal` dual gap rewrites to the corresponding scalar gap after `toReal`. -/
lemma dual_gap_toReal_eq_of_mem_finite_domain
    {v yBar yStar : Fin p → E}
    (hv : v ∈ finite_domain (q(f, g)))
    (hyStar : yStar ∈ Λ*(f, g))
    (hyBar_finite : yBar ∈ finite_domain (q(f, g)))
    (hqOpt_ne_top : q_opt(f, g) ≠ ⊤) :
    (q_opt(f, g) - q(f, g) yBar).toReal =
      EReal.toReal (q_opt(f, g)) - (q(f, g) yBar).toReal := by
  have hyStar_finite :
      yStar ∈ finite_domain (q(f, g)) :=
    optimal_dual_point_mem_finite_domain_of_finite_witness
      (f := f) (g := g) hv hyStar hqOpt_ne_top
  have hqOpt_ne_bot : q_opt(f, g) ≠ ⊥ := by
    -- Evaluate the optimum at the finite optimal witness `yStar`.
    rw [← dual_block_proximal_gradient_dual_objective_eq_dual_problem_value_of_mem_optimal_set
      f g hyStar]
    exact (mem_finite_domain.mp hyStar_finite).2
  have hyBar_ne_top : q(f, g) yBar ≠ ⊤ := by
    exact (mem_effective_domain.mp (mem_finite_domain.mp hyBar_finite).1).ne
  have hyBar_ne_bot : q(f, g) yBar ≠ ⊥ := by
    exact (mem_finite_domain.mp hyBar_finite).2
  -- With both endpoints finite, `EReal.toReal_sub` gives the scalar dual-gap identity directly.
  rw [EReal.toReal_sub hqOpt_ne_top hqOpt_ne_bot hyBar_ne_top hyBar_ne_bot]

/-- Helper for Theorem 12.17: every iterate of the cyclic dual block proximal-gradient trajectory
stays in the finite domain of the source-facing dual objective `q`. -/
lemma cyclic_dbpg_dual_iterate_mem_finite_domain
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    (h_traj :
      is_dual_block_proximal_gradient_primal_trajectory
        f g σ (dual_block_proximal_gradient_cyclic_block_index p) y0 x y)
    (hy0_finite : y0 ∈ finite_domain (q(f, g))) :
    ∀ n : ℕ, y n ∈ finite_domain (q(f, g))
  | 0 => by
      -- The trajectory starts from `y0`, so the base case is exactly the theorem hypothesis.
      simpa [is_dual_block_proximal_gradient_primal_trajectory_zero h_traj] using hy0_finite
  | n + 1 => by
      let i : Fin p := dual_block_proximal_gradient_cyclic_block_index p n
      have hv : y n ∈ finite_domain (q(f, g)) :=
        cyclic_dbpg_dual_iterate_mem_finite_domain h_problem h_traj hy0_finite n
      have hprimal_step :
          y (n + 1) ∈ dual_block_proximal_gradient_primal_y_step g σ (x n) (y n) i := by
        -- Read the source trajectory at step `n` and keep only the block-update clause.
        simpa [i] using (is_dual_block_proximal_gradient_primal_trajectory_step h_traj n).2
      have hdual_step :
          y (n + 1) ∈
            dual_block_proximal_gradient_dual_step
              (fun j z ↦ ((g j)∗) (-z))
              (∇ fun z : E ↦ (((f∗) z).toReal))
              σ
              i
              (y n) := by
        -- Route correction: pass through Lemma 12.15 so the active block is controlled by the
        -- canonical dual-step owner on the minimization view.
        exact
          (dual_block_proximal_gradient_dual_step_iff_mem_dual_block_proximal_gradient_primal_y_step
            (f := f)
            (g := g)
            (σ := σ)
            (hf_proper := h_problem.toIsProperExtendedRealFunction)
            (hf_closed := h_problem.f_closed)
            (hf_strong := h_problem.f_strongly_convex)
            (hg_proper := h_problem.g_proper)
            (hg_closed := h_problem.g_closed)
            (hg_convex := h_problem.g_convex)
            i
            (y (n + 1))
            (y n)).2 hprimal_step
      have hstep :
          y (n + 1) i ∈
              prox[(((σ : ℝ) : EReal) • (fun z : E ↦ ((g i)∗) (-z)))]
                (y n i -
                  (σ : ℝ) • ((∇ fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, y n j))) ∧
            ∀ j : Fin p, j ≠ i → y (n + 1) j = y n j := by
        -- Unfold the one-block dual owner into the active proximal membership plus the unchanged
        -- off-block coordinates.
        simpa [i] using
          (mem_dual_block_proximal_gradient_dual_step_iff.mp hdual_step)
      have hi_mem :
          y (n + 1) i ∈ effective_domain (fun z : E ↦ ((g i)∗) (-z)) := by
        -- The active block is produced by a positive scaled proximal step of `g_i^* ∘ (-id)`,
        -- hence it lies in that block effective domain.
        exact
          mem_effective_domain_of_mem_scaled_prox_of_pos
            (f := fun z : E ↦ ((g i)∗) (-z))
            (hf_proper :=
              dual_based_proximal_gradient_dual_G_primal_proper
                (g := g i)
                (h_problem.g_proper i)
                (h_problem.g_convex i))
            (x := y n i -
              (σ : ℝ) • ((∇ fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, y n j)))
            (lam := σ)
            hstep.1
      have hdual_eff :
          y (n + 1) ∈ effective_domain (separableSum (fun j z ↦ ((g j)∗) (-z))) := by
        -- Combine the freshly updated active block with the unchanged finite blocks from the
        -- previous iterate.
        rw [mem_effective_domain, separableSum_apply]
        refine ereal_sum_lt_top Finset.univ (fun j ↦ ((g j)∗) (-y (n + 1) j)) ?_
        intro j _
        by_cases hji : j = i
        · subst j
          exact mem_effective_domain.mp hi_mem
        · have hj_mem :
              y n j ∈ effective_domain (fun z : E ↦ ((g j)∗) (-z)) :=
            block_dual_term_mem_effective_domain_of_mem_finite_domain
              (σ := σ)
              (f := f)
              (g := g)
              h_problem
              hv
              j
          have hj_eq : y (n + 1) j = y n j := hstep.2 j hji
          simpa [hj_eq] using mem_effective_domain.mp hj_mem
      -- Return from the separable minimization-view domain to the source-facing `finite_domain q`.
      exact
        dual_value_mem_finite_domain_of_mem_effective_domain_separable_dual
          (σ := σ)
          (f := f)
          (g := g)
          h_problem
          hdual_eff

/-- Helper for Theorem 12.17: every outer-cycle iterate `y[pk] = y (p * k)` is in the finite
domain of the source-facing dual objective `q`. -/
lemma cyclic_dbpg_outer_iterate_mem_finite_domain
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    (h_traj :
      is_dual_block_proximal_gradient_primal_trajectory
        f g σ (dual_block_proximal_gradient_cyclic_block_index p) y0 x y)
    (hy0_finite : y0 ∈ finite_domain (q(f, g)))
    (k : ℕ) :
    y[k] ∈ finite_domain (q(f, g)) := by
  -- The outer iterate is just the trajectory sampled at the cycle index `p * k`.
  simpa using
    cyclic_dbpg_dual_iterate_mem_finite_domain
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (x := x)
      (y := y)
      h_problem
      h_traj
      hy0_finite
      (p * k)

-- Proof sketch: identify the cyclic DBPG iterates with one outer step of cyclic block proximal
-- gradient on the block dual objective `-q`, specialize the Chapter 11 cyclic objective-gap
-- estimate with `L_min = L_max = 1 / σ` and `L_f = p / σ`, and then rewrite the resulting
-- objective bound back into the dual-gap form for `q`. The radius hypothesis `hR` is the
-- canonical initial-superlevel distance-to-`Λ*` bound at level `q(y⁰)`, as provided for example
-- by Definition 12.18's derived API, while `hLambda_nonempty` keeps the source-faithful
-- nonemptiness of the optimal dual set visible on the theorem surface.
/-- Theorem 12.17 (1): under Assumption 12.14, if `(x^k, y^k)` is generated by the dual block
proximal-gradient method with cyclic block order, the optimal dual set `Λ*(f, g)` is nonempty,
`R` bounds the initial superlevel set `{y | q(y) ≥ q(y⁰)}` in the canonical distance-to-`Λ*`
form, `q(y⁰)` is finite, and `q_opt ≠ ⊤` (so `q_opt` is finite once `q(y⁰) ≤ q_opt` is used
internally), then every outer-cycle iterate `y^(pk)` with `k ≥ 2` satisfies the dual-gap estimate
`q_opt - q(y^(pk)) ≤ max { (1 / 2)^((k - 1) / 2) (q_opt - q(y⁰)),
  8 p (p + 1)^2 R^2 / (σ (k - 1)) }`. -/
theorem cyclic_dual_block_proximal_gradient_dual_gap_le_max_geometric_or_sublinear
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    (h_traj :
      is_dual_block_proximal_gradient_primal_trajectory
        f g σ (dual_block_proximal_gradient_cyclic_block_index p) y0 x y)
    (R : PosReal)
    (hLambda_nonempty : (Λ*(f, g)).Nonempty)
    (hR :
      ∀ ⦃yBar : Fin p → E⦄,
        q(f, g) y0 ≤ q(f, g) yBar →
          infDist yBar (Λ*(f, g)) ≤ (R : ℝ))
    (hy0_finite : y0 ∈ finite_domain (q(f, g)))
    (hqOpt_ne_top : q_opt(f, g) ≠ ⊤)
    (k : ℕ)
    (hk : 2 ≤ k)
    :
    q_opt(f, g) - q(f, g) y[k] ≤
      ((max
          (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) *
            (q_opt(f, g) - q(f, g) y0).toReal)
          ((8 * (p : ℝ) * ((p + 1 : ℝ) ^ (2 : ℕ)) * ((R : ℝ) ^ (2 : ℕ))) /
            ((σ : ℝ) * ((k - 1 : ℕ) : ℝ))) : ℝ) : EReal) := by
  have hyk_finite : y[k] ∈ finite_domain (q(f, g)) := by
    -- The earlier source trajectory already keeps every outer iterate finite for `q`.
    exact
      cyclic_dbpg_outer_iterate_mem_finite_domain
        (σ := σ)
        (f := f)
        (g := g)
        (y0 := y0)
        (x := x)
        (y := y)
        h_problem
        h_traj
        hy0_finite
        k
  -- Route correction: the file-local transport lemmas above settle the finiteness side-conditions,
  -- so the only remaining source-facing gap is the split Chapter 11 CBPG-rate bridge on `Hdual=-q`.
  -- TODO: package the dual CBPG owner, identify its cyclic inner stages with `y (p * k + i)`,
  -- apply the fixed-initial-radius Chapter 11 rate theorem on the minimization view using
  -- `dual_block_initial_sublevel_radius_on_minimization_view`, and then rewrite the resulting
  -- scalar estimate back to the displayed `EReal` dual-gap bound with
  -- `dual_gap_toReal_eq_of_mem_finite_domain`. The newly verified finite-domain fact
  -- `hyk_finite` reduces the remaining blocker to the Chapter 11 owner/rate transport only.
  clear hyk_finite
  sorry

-- Proof sketch: apply Lemma 12.7 to the primal point `x^(pk)` attached to the dual iterate
-- `y^(pk)` by `h_traj`, obtaining
-- `‖x^(pk) - x*‖² ≤ (2 / σ) (q_opt - q(y^(pk)))`. Then substitute the dual-gap bound from part
-- (1) and simplify the constants.
/-- Theorem 12.17 (2): under the same hypotheses, every outer-cycle primal iterate `x^(pk)` with
`k ≥ 2` satisfies
`‖x^(pk) - x*‖² ≤ (2 / σ) max { (1 / 2)^((k - 1) / 2) (q_opt - q(y⁰)),
  8 p (p + 1)^2 R^2 / (σ (k - 1)) }`
for every primal minimizer `x*`; in particular, the theorem keeps the nonemptiness of `Λ*(f, g)`
explicit alongside the weaker `infDist` radius bound, with the finiteness of `q_opt` encoded by
the canonical hypothesis `q_opt ≠ ⊤`. -/
theorem cyclic_dual_block_proximal_gradient_primal_sqdist_le_max_geometric_or_sublinear
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    (h_traj :
      is_dual_block_proximal_gradient_primal_trajectory
        f g σ (dual_block_proximal_gradient_cyclic_block_index p) y0 x y)
    (R : PosReal)
    (hLambda_nonempty : (Λ*(f, g)).Nonempty)
    (hR :
      ∀ ⦃yBar : Fin p → E⦄,
        q(f, g) y0 ≤ q(f, g) yBar →
          infDist yBar (Λ*(f, g)) ≤ (R : ℝ))
    (hy0_finite : y0 ∈ finite_domain (q(f, g)))
    (hqOpt_ne_top : q_opt(f, g) ≠ ⊤)
    (k : ℕ)
    (hk : 2 ≤ k)
    (xStar : E) (hxStar : IsMinOn F Set.univ xStar) :
    ‖x[k] - xStar‖ ^ (2 : ℕ) ≤
      (2 / (σ : ℝ)) *
        max
          (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) *
            (q_opt(f, g) - q(f, g) y0).toReal)
          ((8 * (p : ℝ) * ((p + 1 : ℝ) ^ (2 : ℕ)) * ((R : ℝ) ^ (2 : ℕ))) /
            ((σ : ℝ) * ((k - 1 : ℕ) : ℝ))) := by
  set B : ℝ :=
    max
      (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) *
        (q_opt(f, g) - q(f, g) y0).toReal)
      ((8 * (p : ℝ) * ((p + 1 : ℝ) ^ (2 : ℕ)) * ((R : ℝ) ^ (2 : ℕ))) /
        ((σ : ℝ) * ((k - 1 : ℕ) : ℝ)))
  have hgap :
      ((((σ : ℝ) / 2) * ‖x[k] - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        q_opt(f, g) - q(f, g) y[k] :=
    cyclic_dbpg_outer_primal_sqdist_le_dual_gap
      (σ := σ) (f := f) (g := g) (y0 := y0) (x := x) (y := y)
      h_problem h_traj k xStar hxStar
  have hdual_gap :
      q_opt(f, g) - q(f, g) y[k] ≤ (B : EReal) := by
    -- Part (1) already provides the source-facing dual-gap estimate at the same outer iterate.
    simpa [B] using
      cyclic_dual_block_proximal_gradient_dual_gap_le_max_geometric_or_sublinear
        (σ := σ) (f := f) (g := g) (y0 := y0) (x := x) (y := y)
        h_problem h_traj R hLambda_nonempty hR hy0_finite hqOpt_ne_top k hk
  have hscaled :
      ((σ : ℝ) / 2) * ‖x[k] - xStar‖ ^ (2 : ℕ) ≤ B := by
    exact_mod_cast le_trans hgap hdual_gap
  -- Clear the positive scalar `(σ / 2)` to recover the squared-distance estimate.
  have htarget : ‖x[k] - xStar‖ ^ (2 : ℕ) ≤ (2 / (σ : ℝ)) * B := by
    have hσ_half : 0 < (σ : ℝ) / 2 := by
      exact div_pos σ.2 (by norm_num)
    have hdiv : ‖x[k] - xStar‖ ^ (2 : ℕ) ≤ B / ((σ : ℝ) / 2) := by
      exact (le_div_iff₀ hσ_half).2 (by simpa [mul_comm] using hscaled)
    have hσ_ne : (σ : ℝ) ≠ 0 := ne_of_gt σ.2
    have hrewrite : B / ((σ : ℝ) / 2) = (2 / (σ : ℝ)) * B := by
      field_simp [hσ_ne]
    simpa [hrewrite] using hdiv
  simpa [B] using htarget

end

end
