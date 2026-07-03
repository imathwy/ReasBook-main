import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_19 (from Chap03) -/
open scoped WithTopConvexAnalysis

universe u

/-
Definition 3.19 is a recall-only bridge in the chapter's extended-valued positive-homogeneity API.

Primary domain:
- positive homogeneity for `WithTop ℝ`-valued functions via their effective domains.

Relevant owner-style declarations sampled before refinement:
- `IsPositivelyHomogeneousOn` in `Definition_3_1_7`, the chapter owner for positive homogeneity on
  a cone;
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter bridge from `WithTop ℝ` values to
  the effective-domain real part;
- `euler_homogeneous_function_theorem` in `Theorem_3_1_21`;
- `subgradient_inner_eq_degree_mul_withTopRealPart_of_homogeneous` in `Theorem_3_26`.

Best owner abstraction:
- `IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f)`.

Primitive data:
- an extended-real-valued function `f : E → WithTop ℝ`;
- a degree `p : ℝ`.

Derived API:
- closure of `dom f` under nonnegative scaling;
- the scaling law for `withTopRealPart f` on `dom f`;
- the downstream homogeneous-subgradient theorems in `Theorem_3_1_21` and `Theorem_3_26`.

Source/core/bridge triage:
- source-facing: Definition 3.19's positive homogeneity on the effective domain of an
  `ℝ ∪ {+∞}`-valued function;
- core/canonical: `IsPositivelyHomogeneousOn`;
- bridge/view: `dom f` and `withTopRealPart f`.

The previous file recalled only the raw generic owner and thereby dropped the chapter's canonical
effective-domain specialization already used downstream. This file now recalls the source-facing
bridge directly.

The source writes the side condition `0 ≤ p`. That inequality is not primitive owner data in this
project: the owner already restricts scaling parameters to `τ : NNReal`, and `Real.rpow (τ : ℝ) p`
is defined for every real exponent on that nonnegative base. The canonical notion is therefore the
specialized predicate below; later results can keep `0 ≤ p` as a separate theorem hypothesis when
the mathematics genuinely uses it.
-/
section

variable {E : Type u} [SMul NNReal E]
variable (p : ℝ) (f : E → WithTop ℝ)

/-- Definition 3.19: an `ℝ ∪ {+∞}`-valued function is positively homogeneous of degree `p` when
its effective domain is closed under nonnegative scaling and its finite real part scales with
degree `p` on that domain. -/
abbrev IsPositivelyHomogeneous (p : ℝ) (f : E → WithTop ℝ) : Prop :=
  IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f)

/-- Helper for Definition 3.19: the source-facing abbreviation is definitionally the chapter owner
on `dom f` and `withTopRealPart f`. -/
theorem isPositivelyHomogeneous_iff_owner {p : ℝ} {f : E → WithTop ℝ} :
    IsPositivelyHomogeneous p f ↔ IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f) :=
  Iff.rfl

/-- Helper for Definition 3.19: the effective domain of a positively homogeneous function is
closed under nonnegative scaling. -/
theorem homogeneous_dom_smul_mem {p : ℝ} {f : E → WithTop ℝ}
    (hhom : IsPositivelyHomogeneous p f) {x : E} (hx : x ∈ dom f) (τ : NNReal) :
    τ • x ∈ dom f := by
  -- The source-facing predicate is just the owner specialized to the effective domain.
  exact hhom.smul_mem hx τ

/-- Helper for Definition 3.19: on the effective domain, the finite real part of a positively
homogeneous function satisfies the expected scaling identity. -/
theorem homogeneous_withTopRealPart_map_smul {p : ℝ} {f : E → WithTop ℝ}
    (hhom : IsPositivelyHomogeneous p f) {x : E} (hx : x ∈ dom f) (τ : NNReal) :
    withTopRealPart f (τ • x) = Real.rpow (τ : ℝ) p • withTopRealPart f x := by
  -- Project the scaling law directly from the specialized owner predicate.
  exact hhom.map_smul hx τ

end

/-! ### Lemma_3_19 (from Chap03) -/
open scoped Pointwise TangentCone Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Lemma 3.19 is a source-facing specialization in the chapter's first-order optimality /
tangent-cone domain.

Primary domain:
- directional derivatives and tangent-cone optimality conditions for convex feasible sets in
  real normed spaces.

Relevant owner-style declarations sampled before refinement:
- `posTangentConeAt`
- `𝒯[Q] xStar` from `Definition_3_23`, the chapter's source-facing tangent-cone surface
- `lineDerivWithin`
- `LineDifferentiableWithinAt`
- `IsMinOn.localize`
- `IsPositivelyHomogeneousOn`
- `directionalDerivative_nonneg_on_posTangentCone_of_isLocalMinOn`

Best owner abstraction:
- the chapter theorem `directionalDerivative_nonneg_on_posTangentCone_of_isLocalMinOn`, whose
  ambient owner objects are `IsLocalMinOn`, `posTangentConeAt`, and `lineDerivWithin`

Primitive data:
- the feasible set `Q`
- the objective `f`
- the minimizer `xStar`
- continuity of `lineDerivWithin ℝ f Q xStar`
- the positive-homogeneity owner witness
  `IsPositivelyHomogeneousOn 1 Set.univ (lineDerivWithin ℝ f Q xStar)`
- the directionwise existence owner witnesses `LineDifferentiableWithinAt ℝ f Q xStar d`

Derived API:
- nonnegativity of `lineDerivWithin ℝ f Q xStar` on `𝒯[Q] xStar`

Source/core/bridge triage:
- source-facing: the global constrained-optimum first-order consequence with hypothesis
  `IsMinOn f Q xStar`
- core/canonical: `IsLocalMinOn`, `posTangentConeAt`, and the owner theorem
  `directionalDerivative_nonneg_on_posTangentCone_of_isLocalMinOn`
- bridge/view: the standard global-to-local owner implication `IsMinOn.localize`, which yields the
  source-facing global specialization

The owner theorem file is not available as a compiled dependency in this item-per-file context, so
this file proves the same source-facing statement directly from the feasible-ray, cone-hull, and
closure steps used in the textbook argument. On this source-facing theorem surface, the tangent
cone is written in the chapter's established notation `𝒯[Q] xStar`. -/

/-- Helper for Lemma 3.19: any direction whose positive ray stays feasible near `xStar` has
nonnegative intrinsic line derivative at a global minimizer. -/
lemma line_deriv_within_nonneg_of_eventually_feasible
    {Q : Set E} {f : E → ℝ} {xStar d : E}
    (hmin : IsMinOn f Q xStar)
    (hd : ∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), xStar + β • d ∈ Q)
    (hline : LineDifferentiableWithinAt ℝ f Q xStar d) :
    0 ≤ lineDerivWithin ℝ f Q xStar d := by
  let T : Set ℝ := ((fun t : ℝ ↦ xStar + t • d) ⁻¹' Q)
  let g : ℝ → ℝ := fun t ↦ f (xStar + t • d)
  have hminT : IsMinOn g T 0 := by
    -- Restrict the global minimum to the scalar slice through `xStar` in direction `d`.
    intro t ht
    simpa [T, g] using hmin ht
  have hone : (1 : ℝ) ∈ posTangentConeAt T (0 : ℝ) := by
    -- Eventual positive feasibility says that the right half-line direction belongs to the slice
    -- tangent cone at the origin.
    apply mem_posTangentConeAt_of_frequently_mem
    simpa [T] using hd.frequently
  have hderiv : HasDerivWithinAt g (lineDerivWithin ℝ f Q xStar d) T 0 := by
    -- The within-set line derivative is exactly the one-dimensional derivative of the slice.
    simpa [T, g, one_smul] using hline.hasLineDerivWithinAt
  -- Apply the one-sided Fermat rule on the scalar slice.
  simpa [hasDerivWithinAt_iff_hasFDerivWithinAt] using
    hminT.localize.hasFDerivWithinAt_nonneg hderiv.hasFDerivWithinAt hone

/-- Helper for Lemma 3.19: every feasible displacement from `xStar` has nonnegative intrinsic line
derivative. -/
lemma line_deriv_within_nonneg_on_feasible_displacements
    {Q : Set E} {f : E → ℝ} {xStar x : E}
    (hxStar : xStar ∈ Q) (hQ_convex : Convex ℝ Q) (hmin : IsMinOn f Q xStar)
    (hline :
      ∀ d : E,
        (∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), xStar + β • d ∈ Q) →
          LineDifferentiableWithinAt ℝ f Q xStar d)
    (hx : x ∈ Q) :
    0 ≤ lineDerivWithin ℝ f Q xStar (x - xStar) := by
  have h01 : (0 : ℝ) < 1 := by
    norm_num
  have hlt : Set.Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) := by
    exact nhdsWithin_le_nhds (Iio_mem_nhds h01)
  have hd : ∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), xStar + β • (x - xStar) ∈ Q := by
    -- Convexity keeps the whole segment from `xStar` to `x` feasible for `0 < β < 1`.
    filter_upwards [self_mem_nhdsWithin, hlt] with β hβpos hβlt
    have hseg : xStar + β • (x - xStar) ∈ segment ℝ xStar x := by
      rw [segment_eq_image']
      exact ⟨β, ⟨le_of_lt hβpos, le_of_lt hβlt⟩, rfl⟩
    exact hQ_convex.segment_subset hxStar hx hseg
  exact line_deriv_within_nonneg_of_eventually_feasible hmin hd (hline (x - xStar) hd)

/-- Helper for Lemma 3.19: nonnegativity on feasible displacements extends to the pointed cone hull
generated by `Q - xStar`. -/
lemma line_deriv_within_nonneg_on_pointed_cone_hull_vsub_singleton
    {Q : Set E} {f : E → ℝ} {xStar p : E}
    (hxStar : xStar ∈ Q) (hQ_convex : Convex ℝ Q) (hmin : IsMinOn f Q xStar)
    (hline_hom : IsPositivelyHomogeneousOn 1 Set.univ (lineDerivWithin ℝ f Q xStar))
    (hline :
      ∀ d : E,
        (∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), xStar + β • d ∈ Q) →
          LineDifferentiableWithinAt ℝ f Q xStar d)
    (hp : p ∈ PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set E))) :
    0 ≤ lineDerivWithin ℝ f Q xStar p := by
  let S : Set E := Q -ᵥ ({xStar} : Set E)
  have hS_convex : Convex ℝ S := by
    simpa [S, Set.vsub_singleton, vsub_eq_sub] using hQ_convex.sub (convex_singleton xStar)
  have hxSingleton : xStar ∈ ({xStar} : Set E) := by
    simp
  have hz : xStar -ᵥ xStar = (0 : E) := by
    simp [vsub_eq_sub]
  have hS_zero : (0 : E) ∈ S := by
    -- The zero displacement belongs to the displacement set because `xStar ∈ Q`.
    exact ⟨xStar, hxStar, xStar, hxSingleton, hz⟩
  have hconvexHull_pointed : (ConvexCone.hull ℝ S).Pointed :=
    ConvexCone.subset_hull hS_zero
  have hpointedHull_eq_convexHull : (PointedCone.hull ℝ S : Set E) = ConvexCone.hull ℝ S := by
    -- For a convex set containing `0`, the pointed hull agrees with the convex cone hull.
    ext v
    constructor
    · intro hv
      let C : PointedCone ℝ E := (ConvexCone.hull ℝ S).toPointedCone hconvexHull_pointed
      have hspan : PointedCone.hull ℝ S ≤ C := by
        refine Submodule.span_le.2 ?_
        intro y hy
        exact ConvexCone.subset_hull hy
      exact hspan hv
    · intro hv
      have hconvexHull_le : ConvexCone.hull ℝ S ≤ (PointedCone.hull ℝ S : ConvexCone ℝ E) := by
        exact ConvexCone.hull_min (fun y hy ↦ PointedCone.subset_hull hy)
      exact hconvexHull_le hv
  have hpS : p ∈ (PointedCone.hull ℝ S : Set E) := by
    simpa [S] using hp
  have hp' : p ∈ ConvexCone.hull ℝ S := by
    simpa [hpointedHull_eq_convexHull] using hpS
  rcases (ConvexCone.mem_hull_of_convex hS_convex).mp hp' with ⟨r, hr, y, hy, rfl⟩
  have hy' : y ∈ (fun z ↦ z - xStar) '' Q := by
    simpa [S, Set.vsub_singleton] using hy
  rcases hy' with ⟨x, hx, rfl⟩
  have hdisp :
      0 ≤ lineDerivWithin ℝ f Q xStar (x - xStar) :=
    line_deriv_within_nonneg_on_feasible_displacements hxStar hQ_convex hmin hline hx
  have hmap :
      lineDerivWithin ℝ f Q xStar (r • (x - xStar)) =
        r * lineDerivWithin ℝ f Q xStar (x - xStar) := by
    -- Positive homogeneity converts the displacement estimate into a conical estimate.
    simpa [Real.rpow_one, smul_eq_mul] using
      hline_hom.map_smul (by simp : x - xStar ∈ Set.univ) ⟨r, hr.le⟩
  rw [hmap]
  exact mul_nonneg hr.le hdisp

/-- Lemma 3.19: if `xStar` minimizes `f` on the convex feasible set `Q`, then the intrinsic
within-set directional-derivative map `lineDerivWithin ℝ f Q xStar` is nonnegative on the tangent
cone `𝒯[Q] xStar`. -/
theorem directionalDerivative_nonneg_on_posTangentCone_of_isMinOn
    {Q : Set E} {f : E → ℝ} {xStar : E}
    (hxStar : xStar ∈ Q) (hQ_convex : Convex ℝ Q) (hmin : IsMinOn f Q xStar)
    (hline_cont : Continuous (lineDerivWithin ℝ f Q xStar))
    (hline_hom : IsPositivelyHomogeneousOn 1 Set.univ (lineDerivWithin ℝ f Q xStar))
    (hline :
      ∀ d : E,
        (∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), xStar + β • d ∈ Q) →
          LineDifferentiableWithinAt ℝ f Q xStar d)
    (p : E) (hp : p ∈ 𝒯[Q] xStar) :
    0 ≤ lineDerivWithin ℝ f Q xStar p := by
  -- Route correction: the unavailable compiled owner wrapper is replaced by the textbook proof
  -- route: feasible rays, then the pointed cone hull of feasible displacements, then closure.
  let C : Set E := {q : E | 0 ≤ lineDerivWithin ℝ f Q xStar q}
  have hclosed : IsClosed C := by
    -- Continuity of the derivative map makes the nonnegative half-space preimage closed.
    simpa [C] using isClosed_Ici.preimage hline_cont
  have hsubset :
      (PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set E)) : Set E) ⊆ C := by
    -- The cone-hull helper covers the dense generating cone of the tangent cone.
    intro q hq
    exact line_deriv_within_nonneg_on_pointed_cone_hull_vsub_singleton
      hxStar hQ_convex hmin hline_hom hline hq
  have hp' : p ∈ closure ((PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set E)) : Set E)) := by
    -- Lemma 3.1.18 identifies the tangent cone with the closure of that pointed hull.
    rw [posTangentConeAt_eq_closure_pointedConeHull_vsub_singleton Q hQ_convex xStar hxStar] at hp
    simpa using hp
  have hclosure : closure ((PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set E)) : Set E)) ⊆ C := by
    exact hclosed.closure_subset_iff.2 hsubset
  exact hclosure hp'

/-! ### Proposition_3_19 (from Chap03) -/
noncomputable section

open scoped WithTopConvexAnalysis

universe u

/- Proposition 3.19 lies in the chapter's real-valued subdifferential / positive-homogeneity
domain.

Primary domain:
- subdifferentials of positively homogeneous convex functions on finite-dimensional real
  inner-product spaces, together with the ambient touching identity that is valid on arbitrary real
  inner-product spaces once a subgradient is given.

Sampled owner-style declarations:
- `IsSubgradientAt`, `subdifferential`, and `mem_subdifferential_iff` in `Definition_3_1_5`, the
  chapter owners for unconstrained subgradients of `WithTop ℝ`-valued functions;
- `IsPositivelyHomogeneousOn` in `Definition_3_1_7`, the chapter owner for positive homogeneity;
- `subdifferential_eq_subdifferential_zero_of_posHomogeneous` in `Lemma_3_15`, the existing
  one-homogeneous source-facing bridge identifying `∂f(x)` with the touching slice of `∂f(0)`;
- `convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior` in
  `Theorem_3_21`, the nearby canonical max-formula owner for convex subgradients.

Best owner abstraction:
- primitive owner predicate `IsSubgradientAt` on `fun y ↦ (f y : WithTop ℝ)`;
- derived owner set `∂ (fun y ↦ (f y : WithTop ℝ))(x)`;
- positive-homogeneity owner `IsPositivelyHomogeneousOn 1 Set.univ f`.

Primitive data:
- a real inner-product space `E`;
- a real-valued function `f : E → ℝ`;
- convexity of `f` on `Set.univ`;
- positive homogeneity of `f` on `Set.univ`.
- for the main `IsGreatest` proposition, finite-dimensionality of `E`, which is the source-faithful
  setting in which the chapter's vector-valued subgradient owner matches the Riesz-representable
  supporting functionals.

Derived API:
- Proposition 3.19's `IsGreatest` max formula over the origin subdifferential.

Source/core/bridge triage:
- source-facing: Proposition 3.19's max formula for convex positively homogeneous functions;
- core/canonical: `IsSubgradientAt`, `subdifferential`, and `IsPositivelyHomogeneousOn`;
- bridge/view: the coercion `fun y ↦ (f y : WithTop ℝ)` and the earlier bridge
  `subdifferential_eq_subdifferential_zero_of_posHomogeneous`.

The previous version duplicated a real-valued subgradient predicate, a real-valued subdifferential
set, and the exact membership theorem that the chapter already owns in `Definition_3_1_5`. This
refinement deletes that parallel API and reuses the existing one-homogeneous bridge from
`Lemma_3_15` together with the interior-point nonemptiness owner from `Theorem_3_1_15`. The main
source-facing Proposition 3.19 theorem stays in the finite-dimensional setting needed for
vector-valued subgradients to capture all continuous supporting functionals.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Proposition 3.19: for a convex positively `1`-homogeneous function on a finite-dimensional real
inner-product space, the value at `x` is the maximum of the pairings `⟪g, x⟫` over all
subgradients `g ∈ ∂f(0)`, expressed as an `IsGreatest` statement for the image of the origin
subdifferential. -/
-- Proof sketch: every `g ∈ ∂f(0)` satisfies `⟪g, x⟫ ≤ f x` by the subgradient inequality at the
-- origin. For the reverse bound, use convexity together with the canonical interior-point
-- nonemptiness theorem to obtain some `g ∈ ∂f(x)`, then apply
-- `subdifferential_eq_subdifferential_zero_of_posHomogeneous` to identify the same `g` with an
-- element of `∂f(0)` satisfying `⟪g, x⟫ = f x`.
theorem isGreatest_pairing_image_subdifferential_zero_of_convex_posHomogeneous
    {f : E → ℝ} (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    [FiniteDimensional ℝ E] (x : E) :
    IsGreatest ((fun g : E ↦ inner ℝ g x) '' ∂ (fun y ↦ (f y : WithTop ℝ))(0)) (f x) := by
  let fTop : E → WithTop ℝ := fun y ↦ (f y : WithTop ℝ)
  have hf_top : ConvexOn ℝ (dom fTop) (withTopRealPart fTop) := by
    change ConvexOn ℝ (dom (fun y ↦ (f y : WithTop ℝ)))
      (withTopRealPart (fun y ↦ (f y : WithTop ℝ)))
    simpa [withTopEffectiveDomain, withTopRealPart] using hf_convex
  have hx_mem : x ∈ interior (dom fTop) := by
    change x ∈ interior (dom (fun y ↦ (f y : WithTop ℝ)))
    simp [withTopEffectiveDomain]
  obtain ⟨g, hgx⟩ :=
    (subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior
      hf_top hx_mem).1
  refine ⟨?_, ?_⟩
  · rw [subdifferential_eq_subdifferential_zero_of_posHomogeneous hf_hom x] at hgx
    exact ⟨g, hgx.1, hgx.2⟩
  · intro y hy
    rcases hy with ⟨g, hg0, rfl⟩
    have hg0' : IsSubgradientAt fTop 0 g := mem_subdifferential_iff.mp hg0
    have hx : x ∈ dom fTop := by
      change x ∈ dom (fun y ↦ (f y : WithTop ℝ))
      simp [withTopEffectiveDomain]
    have hineq : (f x : WithTop ℝ) ≥ f 0 + (inner ℝ g (x - 0) : WithTop ℝ) := hg0'.2 hx
    have h0 : f 0 = 0 := by
      simpa using hf_hom.map_smul (show (0 : E) ∈ Set.univ by simp) (0 : NNReal)
    have hreal : f x ≥ f 0 + inner ℝ g (x - 0) := by
      exact_mod_cast hineq
    simpa [fTop, h0] using hreal

end

/-! ### Theorem_3_19 (from Chap03) -/
/- Theorem 3.19 is a recall-only surface in the chapter's extended-valued convex-subdifferential
domain.

Primary domain:
- convex analysis of `ℝ ∪ {+∞}`-valued functions on Euclidean space.

Sampled owner-style declarations:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain
  and finite-value representative;
- `IsSubgradientAt` and `subdifferential` in `Definition_3_1_5`, the chapter owners for
  extended-valued subgradients;
- `subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior` in
  `Theorem_3_1_15`, the canonical chapter theorem on that owner surface.

Best owner abstraction:
- `subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior`.

Primitive data:
- none in this file; the theorem already lives upstream on the canonical chapter owners.

Derived API:
- this recall-only source-facing entry point.

Source/core/bridge triage:
- source-facing: Theorem 3.19's nonempty-and-bounded subdifferential statement;
- core/canonical: the upstream theorem in `Theorem_3_1_15` on `dom`, `withTopRealPart`, and
  `subdifferential`;
- bridge/view: this recall surface.

The previous file rebuilt local copies of the effective domain, subgradient predicate, and
subdifferential set even though those notions are already owned upstream, and it duplicated the
same theorem already present in `Theorem_3_1_15`. This refinement removes that parallel local API
and reuses the canonical chapter theorem directly.
-/

recall subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior
