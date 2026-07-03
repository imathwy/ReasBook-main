import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_2 (from Chap12) -/
universe u v

open Set

noncomputable section

section

variable {E : Type u} {Y : Type v}

/- Definition 12.2 is `bridge/view`: it rewrites the Chapter 12 primal objective into a split
optimization problem on pairs `(x, z)` constrained by `z = A x`.

Domain sampling identifies the owner abstractions already present upstream:
- `source-facing`: the split reformulation of the primal infimum;
- `core/canonical`: Chapter 10's `composite_model_objective` for pointwise sums, Chapter 12's
  `dual_based_proximal_gradient_primal_optimal_value` for the primal infimum, and mathlib's
  `Set.graphOn` for the graph constraint;
- `bridge/view`: restricting the canonical product objective
  `composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)` to `univ.graphOn A`, which recovers
  the canonical primal objective `composite_model_objective f (g ∘ A)`.

Primitive data are only the summands `f`, `g`, and the map `A`; the product-space objective and
feasible set should therefore be thin specializations of those owners rather than bespoke wrapper
definitions. -/
recall composite_model_objective
recall composite_model_objective_apply
recall dual_based_proximal_gradient_primal_optimal_value_eq_sInf

-- Proof sketch: identify the feasible set with the graph of `A`; every feasible pair has the form
-- `(x, A x)`, and on that graph the canonical product objective
-- `composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)` coincides with the Chapter 12 primal
-- objective `composite_model_objective f (g ∘ A)`, so the split infimum is exactly the canonical
-- primal optimal value.
/-- Definition 12.2: the primal problem `min_x (f x + g (A x))` can equivalently be rewritten as
minimizing the split objective `(x, z) ↦ f x + g z` over the graph-feasible pairs satisfying
`A x = z`. -/
theorem dual_based_proximal_gradient_primal_optimal_value_eq_split_infimum
    (f : E → EReal) (g : Y → EReal) (A : E → Y) :
    dual_based_proximal_gradient_primal_optimal_value f g A =
      sInf (Set.image (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (univ.graphOn A)) := by
  rw [dual_based_proximal_gradient_primal_optimal_value_eq_sInf]
  have himage :
      Set.image (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) (univ.graphOn A) =
        Set.range (composite_model_objective f (g ∘ A)) := by
    ext r
    constructor
    · rintro ⟨⟨x, z⟩, hxz, rfl⟩
      have hz : A x = z := by
        simpa using hxz
      subst z
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨(x, A x), by simp, rfl⟩
  exact congrArg sInf himage.symm

end

/-! ### Theorem_12_2 (from Chap12) -/
universe u v

noncomputable section

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

section

variable (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) (σ : PosReal)

/- Theorem 12.2 is `source-facing`: it asserts strong duality and dual attainment for the Chapter
12 primal/dual pair. Domain sampling for this file identifies the Chapter 4 owner theorems
`fenchel_duality_value_eq` and `exists_isGreatest_fenchel_dual_objective_of_finite_value` as the
`core/canonical` duality layer, while the Chapter 12 owners
`dual_based_proximal_gradient_primal_optimal_value`,
`dual_based_proximal_gradient_lagrange_dual_objective`, and
`dual_based_proximal_gradient_lagrange_dual_problem_value` provide the problem-specific
`bridge/view` surface for the source statement. The primitive data are only `f`, `g`, `A`, `σ`,
and the assumption package `IsDualBasedProximalGradientProblem`; dual attainment is derived API.
The source writes the dual variable in `V`, but the canonical project API records it in the
continuous dual `Module.Dual ℝ V`, which is the right owner layer for the `Aᵀ y` term. -/

recall fenchel_duality_value_eq
recall exists_isGreatest_fenchel_dual_objective_of_finite_value
recall fenchel_dual_objective_apply
recall fenchel_dual_problem_value_eq_sSup
recall conjugate_function_extendedIndicator_apply_eq_support_function
recall support_function_eq_indicatorFunction_polarCone

local notation "pOpt" => dual_based_proximal_gradient_primal_optimal_value f g A
local notation "q" => dual_based_proximal_gradient_lagrange_dual_objective f g A
local notation "qOpt" => dual_based_proximal_gradient_lagrange_dual_problem_value f g A

/-- Helper for Theorem 12.2: the Chapter 12 primal value is the infimum of the split objective
with infeasible pairs outside the graph `z = A x` sent to `⊤`. -/
private theorem split_constrained_primal_value_eq
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) :
    dual_based_proximal_gradient_primal_optimal_value f g A =
      sInf
        (Set.range
          (constrained_problem_objective
            (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
            (Set.univ.graphOn A))) := by
  -- First rewrite the primal owner to the split infimum over graph-feasible pairs.
  rw [dual_based_proximal_gradient_primal_optimal_value_eq_split_infimum]
  -- Then compare the feasible-value image with the constrained-objective range.
  rw [show
      sInf
          (Set.image
            (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
            (Set.univ.graphOn A)) =
        sInf
          (Set.range
            (constrained_problem_objective
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
              (Set.univ.graphOn A))) by
      apply le_antisymm
      · apply le_sInf
        rintro r ⟨xz, rfl⟩
        by_cases hxz : xz ∈ Set.univ.graphOn A
        · exact sInf_le ⟨xz, hxz, by
            simpa using
              (constrained_problem_objective_of_mem
                (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) hxz).symm⟩
        · simp [constrained_problem_objective_of_not_mem
            (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) hxz]
      · apply le_sInf
        rintro r ⟨xz, hxz, rfl⟩
        exact sInf_le ⟨xz, by
          simpa using
            constrained_problem_objective_of_mem
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) hxz⟩]

/-- Helper for Theorem 12.2: the graph of a linear map is convex in the product space. -/
private theorem graphOn_convex
    (A : E →ₗ[ℝ] V) :
    Convex ℝ (Set.univ.graphOn A) := by
  intro x hx y hy a b ha hb hab
  rcases x with ⟨x₁, z₁⟩
  rcases y with ⟨x₂, z₂⟩
  have hz₁ : A x₁ = z₁ := by
    simpa using hx
  have hz₂ : A x₂ = z₂ := by
    simpa using hy
  -- Linear combinations preserve the defining graph relation.
  simp [Set.mem_graphOn, hz₁, hz₂, map_add]

/-- Helper for Theorem 12.2: the indicator of the graph constraint is proper. -/
private theorem graphIndicator_proper
    (A : E →ₗ[ℝ] V) :
    IsProperExtendedRealFunction (extendedIndicator (Set.univ.graphOn A)) := by
  refine
    { ne_bot := ?_
      effective_domain_nonempty := ?_ }
  · intro xz
    by_cases hxz : xz ∈ Set.univ.graphOn A <;> simp [extendedIndicator, hxz]
  · refine ⟨(0, 0), ?_⟩
    simpa [effective_domain_extendedIndicator]

/-- Helper for Theorem 12.2: the indicator of the graph constraint is convex because the graph is
convex. -/
private theorem graphIndicator_convex
    (A : E →ₗ[ℝ] V) :
    is_convex_function (extendedIndicator (Set.univ.graphOn A)) := by
  have h_zero_convex : is_convex_function (0 : E × V → EReal) := by
    refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
    · intro x hx
      simp
    · simpa [effective_domain] using
        (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set (E × V))))
  have h_constrained_convex :
      is_convex_function
        (constrained_problem_objective (0 : E × V → EReal) (Set.univ.graphOn A)) :=
    is_convex_function_constrained_problem_objective h_zero_convex (graphOn_convex A)
  -- Rewrite the constrained zero objective as `0 + δ_graph` and cancel the zero summand.
  rw [constrained_problem_objective_eq_add_extendedIndicator
    (0 : E × V → EReal) (Set.univ.graphOn A) (fun _ _ ↦ by simp)] at h_constrained_convex
  simpa [composite_model_objective] using h_constrained_convex

/-- Helper for Theorem 12.2: the graph of a linear map is a cone. -/
private theorem graphOn_isCone
    (A : E →ₗ[ℝ] V) :
    IsCone (Set.univ.graphOn A) := by
  rw [isCone_iff_smul_mem]
  intro a ha x hx
  rcases x with ⟨x, z⟩
  have hz : A x = z := by
    simpa using hx
  -- Scaling a graph point preserves the relation `z = A x`.
  simp [Set.mem_graphOn, hz, map_smul]

/-- Helper for Theorem 12.2: the graph-compatible dual vector attached to `y` annihilates
graph-feasible pairs `(x, A x)`. -/
private def graphDual
    (A : E →ₗ[ℝ] V) (y : Module.Dual ℝ V) :
    Module.Dual ℝ (E × V) :=
  (A.dualMap y).comp (LinearMap.fst ℝ E V) -
    y.comp (LinearMap.snd ℝ E V)

/-- Helper for Theorem 12.2: evaluating the graph-compatible dual vector gives
`⟨Aᵀ y, x⟩ - ⟨y, z⟩`. -/
@[simp] private theorem graphDual_apply
    (A : E →ₗ[ℝ] V) (y : Module.Dual ℝ V) (xz : E × V) :
    graphDual A y xz = ((A.dualMap y) xz.1 : ℝ) - y xz.2 := by
  -- Expand the product projections once so later graph identities simplify deterministically.
  simp [graphDual, sub_eq_add_neg]

/-- Helper for Theorem 12.2: the graph-compatible dual vector vanishes on the graph of `A`. -/
private theorem graphDual_graph_eq_zero
    (A : E →ₗ[ℝ] V) (y : Module.Dual ℝ V) (x : E) :
    graphDual A y (x, A x) = 0 := by
  -- On a feasible split pair `(x, A x)`, the two pairing terms cancel exactly.
  simp [graphDual_apply]

/-- Helper for Theorem 12.2: the polar cone of the graph consists exactly of graph-compatible
dual vectors. -/
private theorem mem_polar_cone_graphOn_iff_exists_graph_dual_vector
    (A : E →ₗ[ℝ] V) (ψ : Module.Dual ℝ (E × V)) :
    ψ ∈ polar_cone (Set.univ.graphOn A) ↔ ∃ y : Module.Dual ℝ V, ψ = graphDual A y := by
  constructor
  · intro hψ
    have hψ_mem : ∀ x ∈ Set.univ.graphOn A, ψ x ≤ 0 :=
      (mem_polar_cone (Set.univ.graphOn A) ψ).1 hψ
    let y : Module.Dual ℝ V :=
      -(ψ.comp (LinearMap.inr ℝ E V))
    refine ⟨y, ?_⟩
    apply LinearMap.ext
    intro xz
    rcases xz with ⟨x, z⟩
    have hgraph_le : ψ (x, A x) ≤ 0 := hψ_mem (x, A x) (by simp)
    have hgraph_ge : 0 ≤ ψ (x, A x) := by
      have hneg_graph : ψ (-x, A (-x)) ≤ 0 := hψ_mem (-x, A (-x)) (by simp)
      have hneg_eval : ψ (-x, A (-x)) = -ψ (x, A x) := by
        calc
          ψ (-x, A (-x)) = ψ (-(x, A x)) := by simp
          _ = -ψ (x, A x) := by rw [map_neg]
      have hneg : -(ψ (x, A x)) ≤ 0 := by
        rw [← hneg_eval]
        exact hneg_graph
      exact neg_nonpos.mp hneg
    have hgraph_eq : ψ (x, A x) = 0 := le_antisymm hgraph_le hgraph_ge
    have hsplit : (x, z) = (x, A x) + (0, z - A x) := by
      ext <;> simp
    -- Decompose an arbitrary pair into a graph component plus a vertical correction.
    calc
      ψ (x, z) = ψ (x, A x) + ψ (0, z - A x) := by
        rw [hsplit, map_add]
      _ = ψ (0, z - A x) := by simp [hgraph_eq]
      _ = ψ (0, z) - ψ (0, A x) := by
        simpa using map_sub ψ (0, z) (0, A x)
      _ = ((A.dualMap y) x : ℝ) - y z := by
        change ψ (0, z) - ψ (0, A x) = y (A x) - y z
        simp [y, sub_eq_add_neg, add_comm]
  · rintro ⟨y, rfl⟩
    rw [mem_polar_cone]
    intro x hx
    rcases x with ⟨u, z⟩
    have hz : A u = z := by
      simpa using hx
    -- A graph-compatible dual vector evaluates to zero on every graph-feasible pair.
    simp [graphDual_apply, hz]

/-- Helper for Theorem 12.2: Assumption 12.1 provides a graph-feasible relative-interior witness
for the split formulation. -/
private theorem split_graph_qualification_witness
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    ∃ xHat zHat,
      xHat ∈ intrinsicInterior ℝ (effective_domain f) ∧
        zHat ∈ intrinsicInterior ℝ (effective_domain g) ∧
          (xHat, zHat) ∈ Set.univ.graphOn A := by
  -- Repackage the source qualification witness as a point on the graph of `A`.
  rcases h_problem.exists_mem_intrinsicInterior_map_eq with
    ⟨xHat, hxHat, zHat, hzHat, hAz⟩
  refine ⟨xHat, zHat, hxHat, hzHat, ?_⟩
  simp [hAz]

/-- Helper for Theorem 12.2: negating an affine perturbation turns its infimum into the negative
Fenchel conjugate. -/
private theorem ereal_sInf_range_sub_pairing_eq_neg_conjugate
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (h : W → EReal) (η : Module.Dual ℝ W) :
    sInf (Set.range fun x : W ↦ h x - (η x : EReal)) = -conjugate_function h η := by
  -- Rewrite the affine-perturbation range as the negation of the conjugate-defining range.
  have hrange :
      Set.range (fun x : W ↦ h x - (η x : EReal)) =
        -Set.range (fun x : W ↦ (η x : EReal) - h x) := by
    ext r
    constructor
    · rintro ⟨x, rfl⟩
      rw [Set.mem_neg]
      refine ⟨x, ?_⟩
      have hneg : -(h x - (η x : EReal)) = ((η x : EReal) - h x) := by
        have hraw : -(h x - (η x : EReal)) = -h x + (η x : EReal) := by
          exact EReal.neg_sub (Or.inr (by simp)) (Or.inr (by simp))
        simpa [sub_eq_add_neg, add_comm] using hraw
      simpa using hneg.symm
    · rw [Set.mem_neg]
      rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      have hneg : -(h x - (η x : EReal)) = -r := by
        calc
          -(h x - (η x : EReal)) = ((η x : EReal) - h x) := by
            have hraw : -(h x - (η x : EReal)) = -h x + (η x : EReal) := by
              exact EReal.neg_sub (Or.inr (by simp)) (Or.inr (by simp))
            simpa [sub_eq_add_neg, add_comm] using hraw
          _ = -r := by simpa using hx
      have hr : -(-(h x - (η x : EReal))) = -(-r) := congrArg Neg.neg hneg
      simpa using hr
  -- Translate the infimum of the negated range into the negative supremum from the conjugate.
  rw [hrange]
  have hsInf_neg : sInf (-Set.range (fun x : W ↦ (η x : EReal) - h x)) =
      -sSup (Set.range fun x : W ↦ (η x : EReal) - h x) := by
    refine le_antisymm ?_ ?_
    · have hsSup :
        sSup (Set.range fun x : W ↦ (η x : EReal) - h x) ≤
          -sInf (-Set.range fun x : W ↦ (η x : EReal) - h x) := by
        refine sSup_le ?_
        intro x hx
        have hsInf :
            sInf (-Set.range fun x : W ↦ (η x : EReal) - h x) ≤ -x := by
          exact sInf_le
            (by
              simpa [Set.mem_neg] using hx :
                -x ∈ -Set.range fun x : W ↦ (η x : EReal) - h x)
        exact EReal.le_neg.mp hsInf
      exact EReal.le_neg.mpr hsSup
    · refine le_sInf ?_
      intro z hz
      exact EReal.neg_le.mpr
        (le_sSup
          (by
            simpa [Set.mem_neg] using hz :
              -z ∈ Set.range fun x : W ↦ (η x : EReal) - h x))
  rw [hsInf_neg, conjugate_function_apply]

/-- Helper for Theorem 12.2: every point of an affine subspace lies in the intrinsic interior of
its carrier set. -/
private theorem mem_intrinsicInterior_affineSubspace
    {W : Type*} {P : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MetricSpace P] [NormedAddTorsor W P]
    (s : AffineSubspace ℝ P) {x : P} (hx : x ∈ (s : Set P)) :
    x ∈ intrinsicInterior ℝ (s : Set P) := by
  -- Unfold the intrinsic interior inside the affine span, which is the affine subspace itself.
  rw [intrinsicInterior]
  refine ⟨⟨x, ?_⟩, ?_, rfl⟩
  · simpa [AffineSubspace.affineSpan_coe] using hx
  · have hpre :
        ((↑) : affineSpan ℝ (s : Set P) → P) ⁻¹' (s : Set P) = Set.univ := by
      ext y
      change (↑y ∈ (s : Set P)) ↔ True
      constructor
      · intro _
        trivial
      · intro _
        simpa [AffineSubspace.affineSpan_coe] using y.property
    rw [hpre]
    simp

/-- Helper for Theorem 12.2: the relative interiors of two sets combine to the relative interior
of their Cartesian product. -/
private theorem mem_intrinsicInterior_prod
    {S : Set E} {T : Set V} {x : E} {z : V}
    (hx : x ∈ intrinsicInterior ℝ S)
    (hz : z ∈ intrinsicInterior ℝ T) :
    (x, z) ∈ intrinsicInterior ℝ (S ×ˢ T) := by
  -- Route correction: use the closed-ball characterization from Definition 3.7, then project the
  -- product affine-span condition to each coordinate before applying the source witnesses.
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
    rintro _ ⟨p, hp, rfl⟩
    exact hp.1
  have hv_span : v ∈ affineSpan ℝ T := by
    refine (affineSpan_mono ℝ ?_) hv_span_prod
    rintro _ ⟨p, hp, rfl⟩
    exact hp.2
  exact ⟨hballS ⟨hu_ball, hu_span⟩, hballT ⟨hv_ball, hv_span⟩⟩

/-- Helper for Theorem 12.2: the split objective never takes the value `-∞`. -/
private theorem splitObjective_ne_bot
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (xz : E × V) :
    composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd) xz ≠ ⊥ := by
  rcases xz with ⟨x, z⟩
  -- Each summand avoids `⊥`, so the product objective avoids `⊥` as well.
  simpa [composite_model_objective_apply, EReal.add_ne_bot_iff] using
    And.intro (h_problem.ne_bot x) (h_problem.g_proper.ne_bot z)

/-- Helper for Theorem 12.2: the split objective is finite exactly on the product of the two
effective domains. -/
private theorem effective_domain_splitObjective
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    effective_domain (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) =
      effective_domain f ×ˢ effective_domain g := by
  ext xz
  rcases xz with ⟨x, z⟩
  -- Turn finiteness of the split sum into coordinatewise finiteness using the `ne_bot` owners.
  simp [effective_domain, lt_top_iff_ne_top, composite_model_objective_apply,
    EReal.add_ne_top_iff_ne_top₂, h_problem.ne_bot x, h_problem.g_proper.ne_bot z]

/-- Helper for Theorem 12.2: the pointwise sum of two convex extended-real-valued functions is
convex. -/
private theorem is_convex_function_add
    {W : Type*} [AddCommMonoid W] [Module ℝ W]
    (h₁ h₂ : W → EReal) (hh₁ : is_convex_function h₁) (hh₂ : is_convex_function h₂) :
    is_convex_function (h₁ + h₂) := by
  let F : Fin 2 → W → EReal := fun i ↦ if i = 0 then h₁ else h₂
  let α : Fin 2 → NNReal := fun _ ↦ 1
  have hconv :
      is_convex_function (fun x ↦ ∑ i : Fin 2, (((α i : ℝ) : EReal) * F i x)) := by
    refine is_convex_function_finset_nonneg_weighted_sum ?_ α
    intro i
    fin_cases i
    · simpa [F] using hh₁
    · simpa [F] using hh₂
  simpa [F, α, Fin.sum_univ_two] using hconv

/-- Helper for Theorem 12.2: strong convexity of `f` and convexity of `g` make the split objective
convex on `E × V`. -/
private theorem splitObjective_convex
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    is_convex_function (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) := by
  have hf_convex_toReal :
      ConvexOn ℝ (effective_domain f) (fun x : E ↦ (f x).toReal) := by
    exact (h_problem.f_strongly_convex.strictConvexOn σ.2).convexOn
  have hf_convex : is_convex_function f := by
    rw [is_convex_function_iff_convexOn_toReal (fun x _ ↦ h_problem.ne_bot x)]
    exact hf_convex_toReal
  have hf_fst : is_convex_function (fun xz : E × V ↦ f xz.1) := by
    -- Pull the convexity of `f` back along the first-coordinate linear projection.
    simpa using
      is_convex_function_precompose_linearMap_add
        (f := f) hf_convex (LinearMap.fst ℝ E V) (0 : E)
  have hg_snd : is_convex_function (fun xz : E × V ↦ g xz.2) := by
    -- Pull the convexity of `g` back along the second-coordinate linear projection.
    simpa using
      is_convex_function_precompose_linearMap_add
        (f := g) h_problem.g_convex (LinearMap.snd ℝ E V) (0 : V)
  -- The split objective is the pointwise sum of those two pullbacks.
  simpa [composite_model_objective_eq_add] using
    is_convex_function_add (h₁ := f ∘ Prod.fst) (h₂ := g ∘ Prod.snd) hf_fst hg_snd

/-- Helper for Theorem 12.2: the split objective is proper. -/
private theorem splitObjective_proper
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    IsProperExtendedRealFunction (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) := by
  rcases h_problem.effective_domain_nonempty with ⟨x₀, hx₀⟩
  rcases h_problem.g_proper.effective_domain_nonempty with ⟨z₀, hz₀⟩
  refine
    { ne_bot := splitObjective_ne_bot (f := f) (g := g) (A := A) (σ := σ) h_problem
      effective_domain_nonempty := ?_ }
  refine ⟨(x₀, z₀), ?_⟩
  simpa [effective_domain_splitObjective (f := f) (g := g) (A := A) (σ := σ) h_problem]
    using And.intro hx₀ hz₀

/-- Helper for Theorem 12.2: the set-theoretic graph agrees with the carrier of the linear-map
graph submodule. -/
private theorem graphOn_eq_linearMap_graph
    (A : E →ₗ[ℝ] V) :
    Set.univ.graphOn A = (LinearMap.graph A : Set (E × V)) := by
  ext xz
  rcases xz with ⟨x, z⟩
  -- Compare the two graph presentations pointwise and flip the equality orientation once.
  simp [Set.mem_graphOn, LinearMap.mem_graph_iff, eq_comm]

/-- Helper for Theorem 12.2: every graph-feasible pair lies in the intrinsic interior of the graph
constraint set. -/
private theorem mem_intrinsicInterior_graphOn
    {xz : E × V} (hxz : xz ∈ Set.univ.graphOn A) :
    xz ∈ intrinsicInterior ℝ (Set.univ.graphOn A) := by
  -- Route correction: use the graph submodule as the canonical owner, rather than unfolding the
  -- graph constraint directly inside the intrinsic-interior definition.
  have hgraph_set :
      (LinearMap.graph A : Set (E × V)) =
        (((LinearMap.graph A).toAffineSubspace : AffineSubspace ℝ (E × V)) : Set (E × V)) := by
    -- The linear graph submodule and its associated affine subspace have the same carrier set.
    ext yz
    simp
  have hmem :
      xz ∈
        (((LinearMap.graph A).toAffineSubspace : AffineSubspace ℝ (E × V)) : Set (E × V)) := by
    -- Rewrite the set-theoretic graph as the carrier of the linear graph submodule.
    simpa [graphOn_eq_linearMap_graph (A := A), hgraph_set] using hxz
  -- Rewrite the target set to the affine-subspace carrier and then apply the owner lemma.
  rw [graphOn_eq_linearMap_graph (A := A), hgraph_set]
  exact mem_intrinsicInterior_affineSubspace ((LinearMap.graph A).toAffineSubspace) hmem

/-- Helper for Theorem 12.2: the Chapter 12 qualification witness is exactly the Chapter 4
relative-interior qualification for the split graph-constrained pair. -/
private theorem split_graph_fenchel_qualification_nonempty
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    (intrinsicInterior ℝ
        (effective_domain (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))) ∩
      intrinsicInterior ℝ
        (effective_domain (extendedIndicator (Set.univ.graphOn A)))).Nonempty := by
  rcases split_graph_qualification_witness (f := f) (g := g) (A := A) (σ := σ) h_problem with
    ⟨xHat, zHat, hxHat, hzHat, hgraph⟩
  refine ⟨(xHat, zHat), ?_⟩
  constructor
  · -- First place the witness in the product relative interior of the split effective domain.
    simpa [effective_domain_splitObjective (f := f) (g := g) (A := A) (σ := σ) h_problem] using
      mem_intrinsicInterior_prod (x := xHat) (z := zHat) hxHat hzHat
  · -- Then rewrite the graph indicator domain to the graph itself and use the affine owner lemma.
    simpa [effective_domain_extendedIndicator] using
      mem_intrinsicInterior_graphOn (A := A) hgraph

/-- Helper for Theorem 12.2: the Chapter 12 primal value is the Chapter 4 primal infimum for the
split objective plus the graph indicator. -/
private theorem split_primal_value_eq_fenchel_primal_infimum
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    pOpt =
      sInf (Set.range
        (composite_model_objective
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A)))) := by
  have hconstrained_eq :
      constrained_problem_objective
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (Set.univ.graphOn A) =
        composite_model_objective
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A)) := by
    -- Rewrite the constrained split objective as `splitObjective + δ_graph`; the only side
    -- condition is that the split objective never takes the value `⊥`.
    simpa [composite_model_objective_eq_add] using
      constrained_problem_objective_eq_add_extendedIndicator
        (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (Set.univ.graphOn A)
        (fun xz _ ↦ splitObjective_ne_bot (f := f) (g := g) (A := A) (σ := σ) h_problem xz)
  -- Substitute the canonical `splitObjective + δ_graph` owner into the already-normalized primal
  -- infimum.
  simpa [hconstrained_eq] using split_constrained_primal_value_eq (f := f) (g := g) (A := A)

/-- Helper for Theorem 12.2: negating the graph-compatible dual vector corresponds to negating the
underlying dual variable. -/
@[simp] private theorem graphDual_neg
    (A : E →ₗ[ℝ] V) (y : Module.Dual ℝ V) :
    graphDual A (-y) = -graphDual A y := by
  apply LinearMap.ext
  intro xz
  -- Expand both graph-dual evaluations pointwise and regroup the real terms.
  simp [graphDual_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 12.2: the support function of the graph constraint is exactly the indicator
of the graph-dual range. -/
private theorem support_function_graphOn_eq_extendedIndicator_graphDual_range
    (A : E →ₗ[ℝ] V) :
    support_function (Set.univ.graphOn A) =
      extendedIndicator (Set.range (graphDual A)) := by
  funext ψ
  -- Route correction: collapse the graph indicator through the polar-cone owner, then rewrite the
  -- polar membership test by the already-proved graph-dual characterization.
  have hpolar :
      ψ ∈ polar_cone (Set.univ.graphOn A) ↔ ψ ∈ Set.range (graphDual A) := by
    have hpolar_raw :=
      mem_polar_cone_graphOn_iff_exists_graph_dual_vector (A := A) ψ
    constructor
    · intro hmem
      rcases hpolar_raw.mp hmem with ⟨y, hy⟩
      exact ⟨y, hy.symm⟩
    · rintro ⟨y, hy⟩
      exact hpolar_raw.mpr ⟨y, hy.symm⟩
  have hsupport :
      support_function (Set.univ.graphOn A) ψ =
        extendedIndicator (polar_cone (Set.univ.graphOn A)) ψ := by
    simpa using
      congrArg (fun h : Module.Dual ℝ (E × V) → EReal ↦ h ψ)
        (support_function_eq_indicatorFunction_polarCone
          (Set.univ.graphOn A) (graphOn_isCone A) (by simp))
  by_cases hψ : ψ ∈ Set.range (graphDual A)
  · have hpolar_mem : ψ ∈ polar_cone (Set.univ.graphOn A) := hpolar.mpr hψ
    simpa [extendedIndicator, hψ, hpolar_mem] using hsupport
  · have hpolar_not_mem : ψ ∉ polar_cone (Set.univ.graphOn A) := by
      intro hmem
      exact hψ (hpolar.mp hmem)
    simpa [extendedIndicator, hψ, hpolar_not_mem] using hsupport

/-- Helper for Theorem 12.2: membership in the graph-dual range is invariant under negation. -/
private theorem neg_mem_graphDual_range_iff
    (A : E →ₗ[ℝ] V) (ψ : Module.Dual ℝ (E × V)) :
    -ψ ∈ Set.range (graphDual A) ↔ ψ ∈ Set.range (graphDual A) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨-y, ?_⟩
    calc
      graphDual A (-y) = -(graphDual A y) := by
        simpa using (graphDual_neg (A := A) y)
      _ = -(-ψ) := by simpa [hy]
      _ = ψ := by simp
  · intro hψ
    rcases hψ with ⟨y, hy⟩
    refine ⟨-y, ?_⟩
    calc
      graphDual A (-y) = -(graphDual A y) := by
        simpa using (graphDual_neg (A := A) y)
      _ = -ψ := by simpa [hy]

/-- Helper for Theorem 12.2: evaluating the split objective minus `graphDual A y` is exactly the
Chapter 12 Lagrangian integrand. -/
private theorem splitObjective_sub_graphDual_eq_lagrangian
    (y : Module.Dual ℝ V) (xz : E × V) :
    composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd) xz -
        ((graphDual A y) xz : EReal) =
      dual_based_proximal_gradient_lagrangian f g A xz.1 xz.2 y := by
  rcases xz with ⟨x, z⟩
  -- Normalize the graph-dual pairing into the same affine split used by the Lagrangian owner.
  rw [dual_based_proximal_gradient_lagrangian_eq_affine_split, graphDual_apply,
    composite_model_objective_apply]
  have hs :
      -((((A.dualMap y) x - y z : ℝ) : EReal)) =
        -(((A.dualMap y) x : EReal)) + (y z : EReal) := by
    change (((-(((A.dualMap y) x - y z)) : ℝ)) : EReal) =
        (((-((A.dualMap y) x) + y z : ℝ)) : EReal)
    norm_num [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [sub_eq_add_neg, hs]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 12.2: the negative conjugate of the split objective on `graphDual A y`
matches the Chapter 12 dual objective. -/
private theorem neg_conjugate_function_splitObjective_graphDual_eq_dual_objective
    (y : Module.Dual ℝ V) :
    -conjugate_function (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) (graphDual A y) =
      dual_based_proximal_gradient_lagrange_dual_objective f g A y := by
  -- Rewrite the conjugate via the split affine-perturbation infimum, then identify it with the
  -- Chapter 12 Lagrangian infimum formula.
  calc
    -conjugate_function (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (graphDual A y)
        =
        sInf (Set.range fun xz : E × V ↦
          composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd) xz -
            ((graphDual A y) xz : EReal)) := by
          symm
          exact ereal_sInf_range_sub_pairing_eq_neg_conjugate
            (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) (graphDual A y)
    _ =
        sInf (Set.range fun xz : E × V ↦
          dual_based_proximal_gradient_lagrangian f g A xz.1 xz.2 y) := by
          congr 1
          ext r
          constructor
          · rintro ⟨xz, rfl⟩
            exact ⟨xz, by
              simpa using splitObjective_sub_graphDual_eq_lagrangian
                (f := f) (g := g) (A := A) y xz⟩
          · rintro ⟨xz, rfl⟩
            exact ⟨xz, by
              simpa using splitObjective_sub_graphDual_eq_lagrangian
                (f := f) (g := g) (A := A) y xz⟩
    _ = dual_based_proximal_gradient_lagrange_dual_objective f g A y := by
      symm
      exact dual_based_proximal_gradient_lagrange_dual_objective_eq_sInf_lagrangian_formula
        f g A y

/-- Helper for Theorem 12.2: on the graph-dual range, the unrestricted Fenchel dual objective
agrees with the Chapter 12 dual objective `q`. -/
private theorem split_graph_fenchel_dual_objective_on_graphDual
    (y : Module.Dual ℝ V) :
    fenchel_dual_objective
        (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (extendedIndicator (Set.univ.graphOn A))
        (graphDual A y) =
      dual_based_proximal_gradient_lagrange_dual_objective f g A y := by
  -- Combine the split-objective conjugate bridge with the graph-support rewrite, then the
  -- indicator term vanishes because `-graphDual A y` still lies in the graph-dual range.
  rw [fenchel_dual_objective_apply, conjugate_function_extendedIndicator_apply_eq_support_function,
    support_function_graphOn_eq_extendedIndicator_graphDual_range,
    neg_conjugate_function_splitObjective_graphDual_eq_dual_objective]
  have hneg_mem : -graphDual A y ∈ Set.range (graphDual A) := by
    refine ⟨-y, ?_⟩
    simpa using (graphDual_neg (A := A) y)
  simp [extendedIndicator, hneg_mem]

/-- Helper for Theorem 12.2: away from the graph-dual range, the unrestricted Fenchel dual
objective collapses to `-∞`. -/
private theorem split_graph_fenchel_dual_objective_eq_bot_of_not_mem_graphDual_range
    (ψ : Module.Dual ℝ (E × V))
    (hψ : ψ ∉ Set.range (graphDual A)) :
    fenchel_dual_objective
        (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (extendedIndicator (Set.univ.graphOn A))
        ψ = ⊥ := by
  -- Negating preserves graph-dual non-membership, so the graph-support indicator becomes `⊤`,
  -- and subtracting `⊤` collapses the Fenchel dual objective to `⊥`.
  have hneg : -ψ ∉ Set.range (graphDual A) := by
    intro hmem
    exact hψ ((neg_mem_graphDual_range_iff (A := A) ψ).mp hmem)
  rw [fenchel_dual_objective_apply, conjugate_function_extendedIndicator_apply_eq_support_function,
    support_function_graphOn_eq_extendedIndicator_graphDual_range]
  simp [extendedIndicator, hneg]

/-- Helper for Theorem 12.2: the unrestricted Fenchel dual value of the split graph formulation is
exactly the Chapter 12 dual problem value `qOpt`. -/
private theorem split_graph_fenchel_dual_problem_value_eq_lagrange_dual_problem_value :
    fenchel_dual_problem_value
        (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (extendedIndicator (Set.univ.graphOn A)) =
      dual_based_proximal_gradient_lagrange_dual_problem_value f g A := by
  -- Compare the two suprema pointwise using the graph-dual on-range rewrite and the off-range
  -- collapse.
  rw [fenchel_dual_problem_value_eq_sSup, dual_based_proximal_gradient_lagrange_dual_problem_value]
  apply le_antisymm
  · refine sSup_le ?_
    intro r hr
    rcases hr with ⟨ψ, rfl⟩
    by_cases hψ : ψ ∈ Set.range (graphDual A)
    · rcases hψ with ⟨y, rfl⟩
      rw [split_graph_fenchel_dual_objective_on_graphDual (f := f) (g := g) (A := A) y]
      exact le_sSup ⟨y, rfl⟩
    · rw [split_graph_fenchel_dual_objective_eq_bot_of_not_mem_graphDual_range
        (f := f) (g := g) (A := A) ψ hψ]
      exact bot_le
  · refine sSup_le ?_
    intro r hr
    rcases hr with ⟨y, rfl⟩
    rw [← split_graph_fenchel_dual_objective_on_graphDual (f := f) (g := g) (A := A) y]
    exact le_sSup ⟨graphDual A y, rfl⟩

/-- Helper for Theorem 12.2: algebraic and continuous-dual conjugates agree after promoting an
algebraic functional to the continuous dual in finite dimension. -/
private theorem conjugate_function_eq_conjugate_function_strongDual
    (h : E → EReal) (ψ : Module.Dual ℝ E) :
    conjugate_function h ψ =
      conjugate_function_strongDual h ⟨ψ, ψ.continuous_of_finiteDimensional⟩ := by
  -- Both owners are the same supremum formula once the finite-dimensional continuity witness is
  -- packaged into `StrongDual`.
  rfl

/-- Helper for Theorem 12.2: strong convexity makes the algebraic-dual conjugate of `f` finite at
every dual vector. -/
private theorem conjugate_function_finite_of_problem_strong_convex
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (ψ : Module.Dual ℝ E) :
    conjugate_function f ψ ≠ ⊥ ∧ conjugate_function f ψ < ⊤ := by
  let ψc : StrongDual ℝ E := ⟨ψ, ψ.continuous_of_finiteDimensional⟩
  have hfin :=
    conjugate_function_finite_of_proper_closed_strongConvexOn
      (σ : ℝ) σ.2 f h_problem.ne_bot h_problem.effective_domain_nonempty
      h_problem.f_closed h_problem.f_strongly_convex ψc
  simpa [conjugate_function_eq_conjugate_function_strongDual (h := f) ψ] using hfin

/-- Helper for Theorem 12.2: the Chapter 12 dual problem value is finite, hence represented by a
real number. -/
private theorem lagrange_dual_problem_value_is_real
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    ∃ r : ℝ, qOpt = (r : EReal) := by
  have hpq :
      pOpt = qOpt := by
    -- Apply Chapter 4 value duality to the split objective plus graph indicator, then rewrite the
    -- unrestricted Fenchel dual value back to the Chapter 12 owner `qOpt`.
    calc
      pOpt =
          sInf (Set.range
            (composite_model_objective
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
              (extendedIndicator (Set.univ.graphOn A)))) :=
        split_primal_value_eq_fenchel_primal_infimum
          (f := f) (g := g) (A := A) (σ := σ) h_problem
      _ =
          fenchel_dual_problem_value
            (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
            (extendedIndicator (Set.univ.graphOn A)) :=
        fenchel_duality_value_eq
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A))
          (splitObjective_proper (f := f) (g := g) (A := A) (σ := σ) h_problem)
          (graphIndicator_proper (A := A))
          (splitObjective_convex (f := f) (g := g) (A := A) (σ := σ) h_problem)
          (graphIndicator_convex (A := A))
          (split_graph_fenchel_qualification_nonempty
            (f := f) (g := g) (A := A) (σ := σ) h_problem)
      _ = qOpt :=
        split_graph_fenchel_dual_problem_value_eq_lagrange_dual_problem_value
          (f := f) (g := g) (A := A)
  rcases h_problem.exists_mem_intrinsicInterior_map_eq with
    ⟨xHat, hxHat, zHat, hzHat, hAz⟩
  have hxHat_eff : xHat ∈ effective_domain f := intrinsicInterior_subset hxHat
  have hzHat_eff : zHat ∈ effective_domain g := intrinsicInterior_subset hzHat
  have hxHat_value_lt_top :
      composite_model_objective f (g ∘ A) xHat < ⊤ := by
    -- The qualification witness lies in both effective domains, so the sampled primal value is
    -- finite above.
    have hfx_ne_bot : f xHat ≠ ⊥ := h_problem.ne_bot xHat
    have hgAx_ne_bot : (g ∘ A) xHat ≠ ⊥ := by
      simpa [hAz] using h_problem.g_proper.ne_bot zHat
    rw [composite_model_objective_apply, lt_top_iff_ne_top,
      EReal.add_ne_top_iff_ne_top₂ hfx_ne_bot hgAx_ne_bot]
    simpa [hAz] using
      (show f xHat ≠ ⊤ ∧ g zHat ≠ ⊤ from
        ⟨(mem_effective_domain.mp hxHat_eff).ne, (mem_effective_domain.mp hzHat_eff).ne⟩)
  have hqOpt_ne_top : qOpt ≠ ⊤ := by
    rw [← hpq, dual_based_proximal_gradient_primal_optimal_value_eq_sInf]
    exact
      (lt_of_le_of_lt
        (sInf_le
          (show composite_model_objective f (g ∘ A) xHat ∈
              Set.range (composite_model_objective f (g ∘ A)) from
            ⟨xHat, rfl⟩))
        hxHat_value_lt_top).ne
  let hconj_g :=
    isProperExtendedRealFunction_conjugate_function g h_problem.g_proper h_problem.g_convex
  rcases hconj_g.effective_domain_nonempty with ⟨η, hη_eff⟩
  let y0 : Module.Dual ℝ V := -η
  have hf0_finite :
      conjugate_function f (A.dualMap y0) ≠ ⊥ ∧ conjugate_function f (A.dualMap y0) < ⊤ :=
    conjugate_function_finite_of_problem_strong_convex
      (f := f) (g := g) (A := A) (σ := σ) h_problem (A.dualMap y0)
  have hg0_ne_bot : conjugate_function g (-y0) ≠ ⊥ := by
    simpa [y0] using hconj_g.ne_bot η
  have hg0_lt_top : conjugate_function g (-y0) < ⊤ := by
    simpa [y0] using (mem_effective_domain.mp hη_eff)
  have hq0_ne_bot : q y0 ≠ ⊥ := by
    -- The witness `y0` makes both negated conjugate terms avoid `⊥`, so their sum is not `⊥`.
    have hleft_ne_bot : -conjugate_function f (A.dualMap y0) ≠ ⊥ := by
      intro hbot
      have htop : conjugate_function f (A.dualMap y0) = ⊤ := by
        simpa using congrArg Neg.neg hbot
      exact (lt_top_iff_ne_top.mp hf0_finite.2) htop
    have hright_ne_bot : -conjugate_function g (-y0) ≠ ⊥ := by
      intro hbot
      have htop : conjugate_function g (-y0) = ⊤ := by
        simpa using congrArg Neg.neg hbot
      exact (lt_top_iff_ne_top.mp hg0_lt_top) htop
    simpa [dual_based_proximal_gradient_lagrange_dual_objective_apply, sub_eq_add_neg] using
      (EReal.add_ne_bot_iff.mpr ⟨hleft_ne_bot, hright_ne_bot⟩)
  have hqOpt_ne_bot : qOpt ≠ ⊥ := by
    have hq0_lt : (⊥ : EReal) < q y0 := by
      exact bot_lt_iff_ne_bot.mpr hq0_ne_bot
    have hqOpt_lt : (⊥ : EReal) < qOpt := lt_of_lt_of_le hq0_lt (le_sSup ⟨y0, rfl⟩)
    exact bot_lt_iff_ne_bot.mp hqOpt_lt
  refine ⟨(dual_based_proximal_gradient_lagrange_dual_problem_value f g A).toReal, ?_⟩
  exact (EReal.coe_toReal hqOpt_ne_top hqOpt_ne_bot).symm

-- Proof sketch: rewrite the primal objective into the split equality-constrained formulation from
-- Definitions 12.2 and 12.3, apply the Chapter 4 Fenchel/Rockafellar strong-duality theorem under
-- the qualification packaged by `h_problem`, and then identify the resulting dual objective with
-- `y ↦ -f*(Aᵀ y) - g*(-y)` from Definition 12.4. The same duality theorem yields a maximizer of
-- the dual objective, so the optimal value is attained.
/-- Theorem 12.2: under Assumption 12.1, the primal problem
`min_x {f x + g (A x)}` and the dual problem `max_y {-f*(Aᵀ y) - g*(-y)}` have the same optimal
value, and the dual objective attains this maximum. -/
theorem dual_based_proximal_gradient_strong_duality_with_dual_attainment
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    ∃ y : Module.Dual ℝ V, pOpt = qOpt ∧ IsGreatest (Set.range q) (q y) := by
  have hpq :
      pOpt = qOpt := by
    -- Reuse the split-graph Fenchel value theorem and the already-packaged primal normalization.
    calc
      pOpt =
          sInf (Set.range
            (composite_model_objective
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
              (extendedIndicator (Set.univ.graphOn A)))) :=
        split_primal_value_eq_fenchel_primal_infimum
          (f := f) (g := g) (A := A) (σ := σ) h_problem
      _ =
          fenchel_dual_problem_value
            (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
            (extendedIndicator (Set.univ.graphOn A)) :=
        fenchel_duality_value_eq
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A))
          (splitObjective_proper (f := f) (g := g) (A := A) (σ := σ) h_problem)
          (graphIndicator_proper (A := A))
          (splitObjective_convex (f := f) (g := g) (A := A) (σ := σ) h_problem)
          (graphIndicator_convex (A := A))
          (split_graph_fenchel_qualification_nonempty
            (f := f) (g := g) (A := A) (σ := σ) h_problem)
      _ = qOpt :=
        split_graph_fenchel_dual_problem_value_eq_lagrange_dual_problem_value
          (f := f) (g := g) (A := A)
  have hsplit_finite :
      ∃ r : ℝ,
        fenchel_dual_problem_value
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A)) = (r : EReal) := by
    rcases lagrange_dual_problem_value_is_real
        (f := f) (g := g) (A := A) (σ := σ) h_problem with
      ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rw [split_graph_fenchel_dual_problem_value_eq_lagrange_dual_problem_value
      (f := f) (g := g) (A := A), hr]
  rcases exists_isGreatest_fenchel_dual_objective_of_finite_value
      (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
      (extendedIndicator (Set.univ.graphOn A))
      (splitObjective_proper (f := f) (g := g) (A := A) (σ := σ) h_problem)
      (graphIndicator_proper (A := A))
      (splitObjective_convex (f := f) (g := g) (A := A) (σ := σ) h_problem)
      (graphIndicator_convex (A := A))
      (split_graph_fenchel_qualification_nonempty
        (f := f) (g := g) (A := A) (σ := σ) h_problem)
      hsplit_finite with
    ⟨ψ, hψ_greatest⟩
  have hψ_mem_range : ψ ∈ Set.range (graphDual A) := by
    by_contra hψ_not_mem
    have hsplit_ne_bot :
        fenchel_dual_problem_value
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A)) ≠ ⊥ := by
      rcases hsplit_finite with ⟨r, hr⟩
      rw [hr]
      exact EReal.coe_ne_bot r
    have hψ_value :
        fenchel_dual_problem_value
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A)) =
        fenchel_dual_objective
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A))
          ψ := by
      rw [fenchel_dual_problem_value_eq_sSup]
      exact hψ_greatest.csSup_eq
    rw [split_graph_fenchel_dual_objective_eq_bot_of_not_mem_graphDual_range
      (f := f) (g := g) (A := A) ψ hψ_not_mem] at hψ_value
    exact hsplit_ne_bot hψ_value
  rcases hψ_mem_range with ⟨y, rfl⟩
  refine ⟨y, hpq, ?_⟩
  refine ⟨⟨y, rfl⟩, ?_⟩
  intro r hr
  rcases hr with ⟨y', rfl⟩
  have hle :
      fenchel_dual_objective
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A))
          (graphDual A y') ≤
        fenchel_dual_objective
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A))
          (graphDual A y) :=
    hψ_greatest.2
      (show
        fenchel_dual_objective
            (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
            (extendedIndicator (Set.univ.graphOn A))
            (graphDual A y') ∈
          Set.range
            (fenchel_dual_objective
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
              (extendedIndicator (Set.univ.graphOn A))) from
        ⟨graphDual A y', rfl⟩)
  -- Restrict the global Fenchel maximizer to the graph-dual range and rewrite both endpoints back
  -- to the Chapter 12 dual objective `q`.
  rw [split_graph_fenchel_dual_objective_on_graphDual
    (f := f) (g := g) (A := A) y',
    split_graph_fenchel_dual_objective_on_graphDual
      (f := f) (g := g) (A := A) y] at hle
  exact hle

-- Proof sketch: apply Theorem 12.2 and project out the equality clause. This keeps the stronger
-- source-facing theorem as the owner and exposes Proposition 12.1 as a direct companion theorem
-- instead of a separate wrapper file.
/-- Proposition 12.1: under the standing dual-based proximal-gradient assumptions, the primal
optimal value of `min_x {f(x) + g(Ax)}` equals the optimal value of the Lagrange dual problem
`max_y {-f*(Aᵀ y) - g*(-y)}`. -/
theorem dual_based_proximal_gradient_problem_strong_duality
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    pOpt = qOpt := by
  rcases dual_based_proximal_gradient_strong_duality_with_dual_attainment f g A σ h_problem with
    ⟨_, hEq, _⟩
  exact hEq

-- Proof sketch: apply Theorem 12.2 and project out the `IsGreatest` clause. This keeps the
-- source-facing bundled theorem as the main statement while exposing the canonical owner-level
-- attainment claim as a separate reusable lemma.
/-- Under Assumption 12.1, the Chapter 12 Lagrange dual objective attains its maximum. -/
theorem exists_isGreatest_dual_based_proximal_gradient_lagrange_dual_objective
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    ∃ y : Module.Dual ℝ V, IsGreatest (Set.range q) (q y) := by
  rcases dual_based_proximal_gradient_strong_duality_with_dual_attainment f g A σ h_problem with
    ⟨y, _, hy⟩
  exact ⟨y, hy⟩

end

end
