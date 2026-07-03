import Mathlib
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_3_1_18 (from Chap03) -/
section

open scoped WithTopConvexAnalysis

universe u

/- Theorem 3.1.18 lies in the chapter's extended-valued convex-analysis / subdifferential domain.

Relevant owner-style declarations sampled before refinement:
- `IsSubgradientAt` in `Definition_3_1_5`, the primitive owner predicate
- `subdifferential` and `mem_subdifferential_iff` in `Definition_3_1_5`, the set-valued view
- `IsSubgradientAt.mem_dom` in `Definition_3_1_5`, the owner finiteness lemma
- no matching mathlib owner for this exact `WithTop ℝ`-valued subgradient interface

Best owner abstraction:
- `IsSubgradientAt`, with `∂ f(x0)` as derived API

Primitive data:
- an extended-real-valued function `f`
- a base point `x0`, a vector `g`, and the owner hypothesis `IsSubgradientAt f x0 g`
- a comparison point `x` satisfying the sublevel inequality `f x ≤ f x0`

Derived API:
- the lower-sublevel pairing inequality `0 ≤ inner ℝ g (x0 - x)`
- its source-facing wrapper under the owner notation `g ∈ ∂ f(x0)`

Source/core/bridge triage:
- source-facing: Theorem 3.1.18's statement for a subgradient `g ∈ ∂ f(x0)`
- core/canonical: `IsSubgradientAt`
- bridge/view: `mem_subdifferential_iff`

The refined file therefore proves the inequality first at the owner level `IsSubgradientAt` and
keeps the textbook set-valued theorem as the thin bridge from `g ∈ ∂ f(x0)` to that owner
statement. -/
variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A subgradient supports every point whose value lies below the base value. -/
theorem IsSubgradientAt.nonneg_inner_sub_of_le
    {f : V → WithTop ℝ} {x0 g : V} (hg : IsSubgradientAt f x0 g)
    {x : V} (hx : f x ≤ f x0) :
    0 ≤ inner ℝ g (x0 - x) := by
  have hx0_dom : x0 ∈ dom f := hg.mem_dom
  have hx_dom : x ∈ dom f := lt_of_le_of_lt hx hx0_dom
  have hsupport : f x0 + (inner ℝ g (x - x0) : WithTop ℝ) ≤ f x0 :=
    le_trans (hg.2 hx_dom) hx
  have hreal : inner ℝ g (x - x0) ≤ 0 := by
    rw [← coe_withTopRealPart hx0_dom] at hsupport
    have hreal' : withTopRealPart f x0 + inner ℝ g (x - x0) ≤ withTopRealPart f x0 := by
      exact_mod_cast hsupport
    linarith
  simpa [inner_sub_right] using hreal

/-- Theorem 3.1.18: every subgradient `g ∈ ∂f(x₀)` supports the lower level set
`𝓛_f(f(x₀)) = {x ∈ dom f | f x ≤ f x₀}` in the sense that
`⟪g, x₀ - x⟫ ≥ 0` for every point of that set. -/
-- Proof sketch: unpack `g ∈ ∂ f(x₀)` into the defining affine lower-support
-- inequality. If `f x ≤ f x₀`, then applying the subgradient inequality at `x` gives
-- `f x₀ + ⟪g, x - x₀⟫ ≤ f x ≤ f x₀`; rearranging yields `⟪g, x₀ - x⟫ ≥ 0`.
theorem subgradient_nonneg_on_sublevelSet_of_mem_subdifferential
    {f : V → WithTop ℝ} {x0 g : V}
    (hg : g ∈ ∂ f(x0)) {x : V} (hx : f x ≤ f x0) :
    0 ≤ inner ℝ g (x0 - x) :=
  (show IsSubgradientAt f x0 g from hg).nonneg_inner_sub_of_le hx

end

/-! ### Lemma_3_1_19 (from Chap03) -/
noncomputable section

open scoped Pointwise Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Lemma 3.1.19 is the chapter owner theorem in the constrained directional-derivative /
tangent-cone optimality domain.

Primary domain:
- first-order necessary optimality conditions on convex feasible sets in real normed spaces,
  expressed through positive tangent cones and intrinsic within-set directional derivatives.

Relevant owner-style declarations sampled before refinement:
- mathlib `posTangentConeAt`, the ambient owner for feasible infinitesimal directions;
- mathlib `lineDerivWithin`, the intrinsic directional-derivative map on a constraint set;
- mathlib `LineDifferentiableWithinAt`, the owner predicate asserting existence of that
  directional derivative in a fixed direction;
- mathlib `HasLineDerivWithinAt`, the witness-level bridge recovered from
  `LineDifferentiableWithinAt`;
- chapter `IsPositivelyHomogeneousOn` in `Definition_3_1_7`, the owner predicate for the
  nonnegative scaling law satisfied by the intrinsic directional-derivative map.

Best owner abstraction:
- `posTangentConeAt Q xStar` for feasible directions;
- `lineDerivWithin ℝ f Q xStar : E → ℝ` for the directional-derivative object `p ↦ f'(xStar; p)`.

Primitive data:
- the feasible set `Q`, objective `f`, and local minimizer `xStar`;
- continuity of the intrinsic directional-derivative map `lineDerivWithin ℝ f Q xStar`;
- positive homogeneity of that intrinsic map;
- directionwise existence of the within-set directional derivative, expressed by
  `LineDifferentiableWithinAt`.

Derived API:
- nonnegativity of `lineDerivWithin ℝ f Q xStar` on `posTangentConeAt Q xStar`.

Source/core/bridge triage:
- source-facing: the textbook first-order necessary condition on the tangent cone;
- core/canonical: `posTangentConeAt` and `lineDerivWithin`;
- bridge/view: `LineDifferentiableWithinAt` together with the recovered witness
  `HasLineDerivWithinAt`.

This refinement removes the non-canonical auxiliary parameter `f' : E → ℝ` from the public API.
The theorem is now stated directly on the intrinsic owner `lineDerivWithin ℝ f Q xStar`, while
existence data remains in the bridge layer `LineDifferentiableWithinAt`.
-/

/-- Helper for Lemma 3.1.19: any direction whose positive ray stays feasible near `xStar` has
nonnegative intrinsic line derivative at a local minimizer. -/
lemma line_deriv_within_nonneg_of_eventually_feasible
    {Q : Set E} {f : E → ℝ} {xStar d : E}
    (hxStar : xStar ∈ Q)
    (hmin : IsLocalMinOn f Q xStar)
    (hd : ∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), xStar + β • d ∈ Q)
    (hline : LineDifferentiableWithinAt ℝ f Q xStar d) :
    0 ≤ lineDerivWithin ℝ f Q xStar d := by
  let T : Set ℝ := ((fun t : ℝ ↦ xStar + t • d) ⁻¹' Q)
  let φ : ℝ → E := fun t ↦ xStar + t • d
  let g : ℝ → ℝ := fun t ↦ f (φ t)
  have hφ_cont : ContinuousOn φ T := by
    -- The line map is continuous on the scalar slice.
    simpa [φ] using (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
  have hminT : IsLocalMinOn g T 0 := by
    -- Restrict the local minimum of `f` to the feasible scalar slice through `xStar`.
    have hminφ : IsLocalMinOn f Q (φ 0) := by
      simpa [φ] using hmin
    have hpre : T ⊆ φ ⁻¹' Q := by
      intro t ht
      simpa [T, φ] using ht
    have hzero : (0 : ℝ) ∈ T := by
      simpa [T, φ] using hxStar
    simpa [g] using hminφ.comp_continuousOn hpre hφ_cont hzero
  have hone : (1 : ℝ) ∈ posTangentConeAt T (0 : ℝ) := by
    -- Eventual positive feasibility places the rightward scalar direction in the slice tangent cone.
    apply mem_posTangentConeAt_of_frequently_mem
    simpa [T] using hd.frequently
  have hderiv : HasDerivWithinAt g (lineDerivWithin ℝ f Q xStar d) T 0 := by
    -- The intrinsic line derivative is the derivative of the one-dimensional slice.
    simpa [T, φ, g, one_smul] using hline.hasLineDerivWithinAt
  -- Apply the local Fermat rule on the scalar slice.
  simpa [hasDerivWithinAt_iff_hasFDerivWithinAt] using
    hminT.hasFDerivWithinAt_nonneg hderiv.hasFDerivWithinAt hone

/-- Helper for Lemma 3.1.19: every feasible displacement from `xStar` has nonnegative intrinsic
line derivative. -/
lemma line_deriv_within_nonneg_on_feasible_displacements
    {Q : Set E} {f : E → ℝ} {xStar x : E}
    (hxStar : xStar ∈ Q) (hQ_convex : Convex ℝ Q) (hmin : IsLocalMinOn f Q xStar)
    (hline :
      ∀ (d : E) (_hd : ∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), xStar + β • d ∈ Q),
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
  exact
    line_deriv_within_nonneg_of_eventually_feasible
      hxStar hmin hd (hline (x - xStar) hd)

/-- Helper for Lemma 3.1.19: nonnegativity on feasible displacements extends to the pointed cone
hull generated by `Q - xStar`. -/
lemma line_deriv_within_nonneg_on_pointed_cone_hull_vsub_singleton
    {Q : Set E} {f : E → ℝ} {xStar p : E}
    (hxStar : xStar ∈ Q) (hQ_convex : Convex ℝ Q) (hmin : IsLocalMinOn f Q xStar)
    (hline_hom : IsPositivelyHomogeneousOn 1 Set.univ (lineDerivWithin ℝ f Q xStar))
    (hline :
      ∀ (d : E) (_hd : ∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), xStar + β • d ∈ Q),
        LineDifferentiableWithinAt ℝ f Q xStar d)
    (hp : p ∈ PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set E))) :
    0 ≤ lineDerivWithin ℝ f Q xStar p := by
  let S : Set E := Q -ᵥ ({xStar} : Set E)
  have hS_convex : Convex ℝ S := by
    -- Translating a convex feasible set by `-xStar` preserves convexity.
    simpa [S, Set.vsub_singleton, vsub_eq_sub] using hQ_convex.sub (convex_singleton xStar)
  have hxSingleton : xStar ∈ ({xStar} : Set E) := by
    simp
  have hz : xStar -ᵥ xStar = (0 : E) := by
    simp [vsub_eq_sub]
  have hS_zero : (0 : E) ∈ S := by
    -- The zero displacement is feasible because `xStar` itself is feasible.
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

-- Proof sketch: for each feasible direction `d`, local optimality of `xStar` forces every
-- sufficiently small forward difference quotient of `f` along `d` to be nonnegative, so the
-- corresponding within-set directional derivative is nonnegative. Any tangent direction is a
-- limit of positive rescalings of such feasible displacements; positive homogeneity and
-- continuity of `lineDerivWithin ℝ f Q xStar` then pass the inequality to the limit.
/-- Lemma 3.1.19: if `xStar` is a local minimizer of `f` on `Q`, then the intrinsic constrained
directional-derivative map `lineDerivWithin ℝ f Q xStar` is nonnegative on the tangent cone
`posTangentConeAt Q xStar`. The textbook `ℝⁿ` statement is the specialization to
`E = EuclideanSpace ℝ (Fin n)`. -/
theorem directionalDerivative_nonneg_on_posTangentCone_of_isLocalMinOn
    {Q : Set E} {f : E → ℝ} {xStar : E}
    (hxStar : xStar ∈ Q) (hQ_convex : Convex ℝ Q) (hmin : IsLocalMinOn f Q xStar)
    (hline_cont : Continuous (lineDerivWithin ℝ f Q xStar))
    (hline_hom : IsPositivelyHomogeneousOn 1 Set.univ (lineDerivWithin ℝ f Q xStar))
    (hline :
      ∀ (d : E) (_hd : ∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), xStar + β • d ∈ Q),
        LineDifferentiableWithinAt ℝ f Q xStar d)
    (p : E) (hp : p ∈ posTangentConeAt Q xStar) :
    0 ≤ lineDerivWithin ℝ f Q xStar p := by
  let C : Set E := {q : E | 0 ≤ lineDerivWithin ℝ f Q xStar q}
  have hclosed : IsClosed C := by
    -- Continuity of the derivative map makes the nonnegative half-space preimage closed.
    simpa [C] using isClosed_Ici.preimage hline_cont
  have hsubset :
      (PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set E)) : Set E) ⊆ C := by
    -- The cone-hull helper covers the dense generating cone of the tangent cone.
    intro q hq
    exact
      line_deriv_within_nonneg_on_pointed_cone_hull_vsub_singleton
        hxStar hQ_convex hmin hline_hom hline hq
  have hp' : p ∈ closure ((PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set E)) : Set E)) := by
    -- Lemma 3.1.18 identifies the tangent cone with the closure of that pointed hull.
    rw [posTangentConeAt_eq_closure_pointedConeHull_vsub_singleton Q hQ_convex xStar hxStar] at hp
    simpa using hp
  have hclosure : closure ((PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set E)) : Set E)) ⊆ C := by
    -- Closedness upgrades the cone-hull estimate to its closure.
    exact hclosed.closure_subset_iff.2 hsubset
  exact hclosure hp'

end

/-! ### Theorem_3_1_19 (from Chap03) -/
noncomputable section

open scoped WithTopConvexAnalysis

universe u

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/- Theorem 3.1.19 lies in the same common-subdifferential owner domain as
`Definition_3_1_5` and `Definition_3_1_5_4`.

Relevant owner-style declarations sampled before refinement:
- `IsSubgradientAt` in `Definition_3_1_5`
- `commonRegularSubdifferential` in `Definition_3_1_5_4`
- `mem_commonRegularSubdifferential_iff` in `Definition_3_1_5_4`
- `commonRegularSubdifferentialOn` in `Definition_3_1_5_4`
- `mem_commonRegularSubdifferentialOn_iff` in `Definition_3_1_5_4`
- `mem_subdifferential_coe_real_iff` in `Definition_3_1_5`

Best owner abstraction:
- `commonRegularSubdifferential` on an arbitrary real inner-product space

Primitive data:
- a set `X : Set V`
- a real-valued convex function `f : V → ℝ`
- either a common regular subgradient `g ∈ ∂̂ f(X)` or the nonemptiness of that set

Derived API:
- the affine increment identity induced by a common regular subgradient
- the affine-on-segments consequence when the common regular subdifferential is nonempty

Source/core/bridge triage:
- source-facing: the two textbook consequences of a common regular subgradient
- core/canonical: `commonRegularSubdifferential`
- bridge/view: `commonRegularSubdifferentialOn`

The earlier version fixed the ambient space to `EuclideanSpace ℝ (Fin n)`, but neither statement
uses coordinates, finite indexing, or finite-dimensional structure. Since the owner notion
`commonRegularSubdifferential` already lives on arbitrary real inner-product spaces, the canonical
owner theorems should live there as well, with the textbook Euclidean statement recovered by
specialization. -/

/-- Theorem 3.1.19 (2): every common subgradient `g ∈ ∂̂f(X)` gives the affine increment formula
`f x₁ = f x₀ + ⟪g, x₁ - x₀⟫` for all `x₀, x₁ ∈ X`. -/
-- Proof sketch: apply the subgradient inequality furnished by `hg` at the base point `x₀` and
-- evaluation point `x₁`, then again at the base point `x₁` and evaluation point `x₀`. The two
-- resulting inequalities are reverse bounds on the same quantity, so they collapse to equality.
theorem eq_add_inner_of_mem_commonRegularSubdifferential
    {X : Set V} {f : V → ℝ}
    {g x0 x1 : V} (hg : g ∈ ∂̂ f(X))
    (hx0 : x0 ∈ X) (hx1 : x1 ∈ X) :
    f x1 = f x0 + inner ℝ g (x1 - x0) := by
  have hgX := mem_commonRegularSubdifferentialOn_iff.mp hg
  have hg0 : ∀ y : V, f y ≥ f x0 + inner ℝ g (y - x0) := hgX x0 hx0
  have hg1 : ∀ y : V, f y ≥ f x1 + inner ℝ g (y - x1) := hgX x1 hx1
  have h01 : f x0 + inner ℝ g (x1 - x0) ≤ f x1 := by
    simpa [ge_iff_le] using hg0 x1
  have hinv : inner ℝ g (x0 - x1) = -inner ℝ g (x1 - x0) := by
    rw [show x0 - x1 = -(x1 - x0) by abel, inner_neg_right]
  have h10 : f x1 ≤ f x0 + inner ℝ g (x1 - x0) := by
    have h : f x1 + inner ℝ g (x0 - x1) ≤ f x0 := by
      simpa [ge_iff_le] using hg1 x0
    have h' : f x1 + (-inner ℝ g (x1 - x0)) ≤ f x0 := by
      simpa [hinv] using h
    linarith
  linarith

/-- Theorem 3.1.19 (1): if a convex set `X` admits a common subgradient of a real-valued function
`f`, then `f` is affine on every segment contained in `X`. -/
-- Proof sketch: choose a common subgradient `g` from `hfacet_nonempty`. Convexity of `X` places
-- `(1 - α) • x₀ + α • x₁` back in `X`, so the affine increment identity from part `(2)` applies
-- both to `(x₀, (1 - α) • x₀ + α • x₁)` and to `(x₀, x₁)`, and the two identities combine into
-- the segment formula.
theorem map_segment_eq_of_commonRegularSubdifferential_nonempty
    {X : Set V} {f : V → ℝ}
    (hX_convex : Convex ℝ X)
    (hfacet_nonempty : (∂̂ f(X)).Nonempty)
    {x0 x1 : V} (hx0 : x0 ∈ X) (hx1 : x1 ∈ X) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    f ((1 - α) • x0 + α • x1) = (1 - α) * f x0 + α * f x1 := by
  rcases hfacet_nonempty with ⟨g, hg⟩
  let z : V := (1 - α) • x0 + α • x1
  have hα0 : 0 ≤ 1 - α := by
    linarith [hα.2]
  have hsum : (1 - α) + α = 1 := by
    ring
  have hz : z ∈ X := by
    dsimp [z]
    exact hX_convex hx0 hx1 hα0 hα.1 hsum
  have hz0 : f z = f x0 + inner ℝ g (z - x0) :=
    eq_add_inner_of_mem_commonRegularSubdifferential hg hx0 hz
  have h10 : f x1 = f x0 + inner ℝ g (x1 - x0) :=
    eq_add_inner_of_mem_commonRegularSubdifferential hg hx0 hx1
  have hzsub : z - x0 = α • (x1 - x0) := by
    dsimp [z]
    calc
      ((1 - α) • x0 + α • x1) - x0 = α • x1 + (-x0 + (1 - α) • x0) := by
        abel
      _ = α • x1 + (((-1 : ℝ) + (1 - α)) • x0) := by
        congr 1
        rw [show -x0 = (-1 : ℝ) • x0 by simp, ← add_smul]
      _ = α • x1 + (-(α • x0)) := by
        congr 1
        ring_nf
        simp
      _ = α • (x1 - x0) := by
        rw [sub_eq_add_neg, smul_add, smul_neg]
  rw [hz0, h10, hzsub, inner_smul_right]
  ring

end

/-! ### Lemma_3_1_20 (from Chap03) -/
noncomputable section

open scoped InnerProduct
open scoped EllipsoidNotation

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- 
Lemma 3.1.20 lies in the chapter's centered-ellipsoid / support-value domain.

Sampled owner-style declarations:
- `affineEllipsoid` in `Lemma_3_2_7`, the chapter owner for the textbook ellipsoid `E(H, x̄)`;
- `isGreatest_inner_image_spdEllipsoid` in `Lemma_3_20`, the exact maximum-attainment theorem on
  that owner ellipsoid;
- `IsGreatest.csSup_eq`, the generic order-theoretic bridge from an explicit maximum statement to
  the corresponding supremum equality.

Best owner abstraction:
- source-facing/core owner: `isGreatest_inner_image_spdEllipsoid`;
- bridge/view: `hmax.csSup_eq`.

Primitive data:
- `A : Mat` with `hA : A.PosDef`;
- `c : E`.

Derived API:
- the centered ellipsoid `affineEllipsoid A⁻¹ 0`;
- the image set `((fun x : E ↦ inner ℝ c x) '' affineEllipsoid A⁻¹ 0)`;
- the companion supremum equality supplied canonically by `hmax.csSup_eq`.

Source/core/bridge triage:
- source-facing: the textbook maximum of `⟪c, x⟫` over the centered ellipsoid;
- core/canonical: the earlier owner theorem `isGreatest_inner_image_spdEllipsoid`;
- bridge/view: the generic companion `IsGreatest.csSup_eq`.

This file is recall-only: once `Lemma_3_20` is stated directly on the chapter ellipsoid owner,
there is no reason to keep a second theorem name with the exact same interface.
-/

recall isGreatest_inner_image_spdEllipsoid
    (A : Mat) (hA : A.PosDef) (c : E) :
    IsGreatest ((fun x : E ↦ inner ℝ c x) '' E(A⁻¹, (0 : E)))
      (Real.sqrt (inner ℝ c ((A⁻¹).toEuclideanLin c)))

/-
The supremum reformulation of Lemma 3.1.20 is the generic companion consequence of the
maximum-attainment statement
`isGreatest_inner_image_spdEllipsoid`. -/
section

variable {A : Mat} {c : E}

local notation "E₀" => E(A⁻¹, (0 : E))
local notation "supportImage" => (fun x : E ↦ inner ℝ c x) '' E₀
local notation "supportMax" => Real.sqrt (inner ℝ c ((Matrix.toEuclideanLin A⁻¹) c))

variable (hmax : IsGreatest supportImage supportMax)

/- The supremum reformulation is not a second source-facing theorem: it is the generic
order-theoretic companion `hmax.csSup_eq`. -/
#check hmax.csSup_eq

end

end

/-! ### Theorem_3_1_20 (from Chap03) -/
open scoped ConstrainedArgmin WithTopConvexAnalysis

universe u

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/- Theorem 3.1.20 lies in the chapter's minimizer/common-subdifferential domain.

Relevant owner-style declarations sampled before refinement:
- `constrainedArgmin` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project
  owner API for minimizers on a set;
- `withTopEffectiveDomain` and the notation `dom f` in `Definition_3_3`, the chapter owner for
  the effective domain of an `ℝ ∪ {+∞}`-valued function;
- `subdifferential` and `mem_subdifferential_iff` in `Definition_3_1_5`, the chapter owner API
  for extended-valued subgradients;
- `commonRegularSubdifferential` and `mem_commonRegularSubdifferential_iff` in
  `Definition_3_1_5_4`, the owner API for common subdifferentials.

Best owner abstraction:
- `argmin[dom f] f` together with `commonRegularSubdifferential`.

Primitive data:
- an extended-valued function `f`;
- a set `XStar`.

Derived API:
- membership in `argmin[dom f] f`, via `mem_constrainedArgmin_iff`;
- membership in `∂̂ f(XStar)`, via `mem_commonRegularSubdifferential_iff`.

Source/core/bridge triage:
- source-facing: the textbook criterion identifying sets of global minimizers by the common
  regular subdifferential;
- core/canonical: `argmin[dom f] f` and `commonRegularSubdifferential`;
- bridge/view: the theorem below relating these two owner objects.

The previous version introduced a second owner `globalMinimizers` for the exact Chapter 1 object
`argmin[dom f] f`. This file now deletes that duplicate wheel and states the theorem
directly with the canonical minimizer-set owner. -/

/-- Theorem 3.1.20: a set `X_*` is contained in
`arg min_{x ∈ dom f} f(x)` if and only if the zero vector lies in the common
subdifferential `∂̂ f(X_*)`. -/
-- Proof sketch: if `X_* ⊆ argmin[dom f] f`, then for each `x ∈ X_*` the minimizer
-- property on `dom f` is exactly the subgradient inequality with slope `0`, so `0 ∈ ∂f(x)` and
-- hence `0 ∈ ∂̂ f(X_*)`. Conversely, if `0 ∈ ∂̂ f(X_*)`, then at each `x ∈ X_*` the defining
-- inequality for `0 ∈ ∂f(x)` says `f x ≤ f y` for every `y ∈ dom f`, so
-- `x ∈ argmin[dom f] f`.
theorem subset_constrainedArgmin_effectiveDomain_iff_zero_mem_commonRegularSubdifferential
    {f : V → WithTop ℝ} {XStar : Set V} :
    XStar ⊆ argmin[dom f] f ↔ (0 : V) ∈ ∂̂ f(XStar) := by
  rw [mem_commonRegularSubdifferential_iff]
  constructor
  · intro h x hx
    rw [mem_subdifferential_iff]
    rcases mem_constrainedArgmin_iff.mp (h hx) with ⟨hx_dom, hx_min⟩
    exact ⟨hx_dom, fun y hy ↦ by simpa using (isMinOn_iff.mp hx_min y hy)⟩
  · intro h x hx
    rw [mem_constrainedArgmin_iff]
    have hx_zero : (0 : V) ∈ ∂ f(x) := h x hx
    rw [mem_subdifferential_iff] at hx_zero
    rcases hx_zero with ⟨hx_dom, hx_subgrad⟩
    refine ⟨hx_dom, isMinOn_iff.mpr ?_⟩
    intro y hy
    simpa using hx_subgrad hy

/-! ### Lemma_3_1_21 (from Chap03) -/
/- Lemma 3.1.21 lies in the chapter's finite-dimensional Lagrangian-duality domain.

Primary domain:
- inequality-constrained Lagrangian duality with complementary slackness

Sampled owner-style declarations:
- `LagrangianProblem.lagrangian` and `LagrangianProblem.lagrangianMinimizers` in
  `Chap01/Definition_1_10_2`
- `LagrangianProblem.dualOptimalValue_le_primalOptimalValue` in
  `Chap01/Proposition_1_10_8`
- `objective_gap_ge_weighted_constraint_violation_of_lagrangian_minimizer` in
  `Chap03/Lemma_3_21`

Best owner abstraction:
- the existing Chapter 3 theorem
  `objective_gap_ge_weighted_constraint_violation_of_lagrangian_minimizer`, stated using the
  owner `problem : LagrangianProblem Q m` together with the derived API
  `problem.lagrangianMinimizers`

Primitive data:
- the Lagrangian owner `problem : LagrangianProblem Q m`
- the points `xStar`, `xBar`
- the multiplier vector `lambdaStar`

Derived API:
- the owner Lagrangian-minimizer fiber `problem.lagrangianMinimizers lambdaStar`
- complementary slackness at `xStar`

Source/core/bridge triage:
- source-facing: the textbook objective-gap inequality derived from a Lagrangian minimizer and
  complementary slackness
- core/canonical: the Chapter 1 owner `LagrangianProblem` and its `IsMinOn` Lagrangian-minimizer
  interface
- bridge/view: the previous local theorem name, which duplicated `Lemma_3_21` without adding new
  mathematics

The former file introduced a second public theorem name with exactly the same interface as the
existing chapter theorem in `Lemma_3_21`. This refinement keeps Lemma 3.1.21 as direct canonical
recall/use instead of a parallel wrapper theorem.
-/
recall objective_gap_ge_weighted_constraint_violation_of_lagrangian_minimizer

/-! ### Theorem_3_1_21 (from Chap03) -/
noncomputable section

open scoped WithTopConvexAnalysis

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 3.1.21 lies in the chapter's extended-valued homogeneous-subdifferential domain.

Primary domain:
- convex analysis of `ℝ ∪ {+∞}`-valued functions on real inner-product spaces, with effective
  domains and subgradients.

Relevant owner-style declarations sampled before refinement:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain and
  finite real part of a `WithTop ℝ`-valued function;
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`, the chapter owner API for
  unconstrained subgradients;
- `IsPositivelyHomogeneousOn` in `Definition_3_1_7`, the chapter owner for positive homogeneity on
  a cone;
- `SMulMemClass.smul_mem`, the canonical closure API on cone-shaped domains.

Best owner abstraction:
- `IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f)`.

Primitive data:
- an extended-valued function `f : E → WithTop ℝ`;
- a degree `p : ℝ`;
- the source-facing homogeneity owner on the effective domain;
- a subgradient witness `hg : g ∈ ∂ f(x)`.

Derived API:
- closure of `dom f` under nonnegative scaling from `hhom.smul_mem`;
- the rescaling identity for `withTopRealPart f` from `hhom.map_smul`.

Source/core/bridge triage:
- source-facing: Euler's identity for subgradients of an extended-valued homogeneous function;
- core/canonical: the chapter owners `subdifferential` and `IsPositivelyHomogeneousOn`;
- bridge/view: `dom f` and `withTopRealPart f` from `Definition_3_3`.

The previous version introduced a second public homogeneity predicate specialized to effective
domains, together with projection lemmas that duplicated the already canonical owner
`IsPositivelyHomogeneousOn`. This file now states the theorem directly on the chapter owner
abstraction, leaving the effective-domain view as the canonical specialization
`s = dom f, f = withTopRealPart f` rather than as a parallel API root.
-/

-- The theorem uses the standard ray argument, so the dedicated helpers below first rewrite the
-- homogeneous scaling law and then package the right- and left-slope estimates separately.
/-- Helper for Theorem 3.1.21: nonnegative rescaling on the effective domain rewrites
`withTopRealPart f` exactly by the homogeneous degree law. -/
lemma withTopRealPart_map_smul_of_nonneg
    {f : E → WithTop ℝ} {p : ℝ}
    (hhom : IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f))
    {x : E} (hx : x ∈ dom f) {τ : ℝ} (hτ : 0 ≤ τ) :
    withTopRealPart f (τ • x) = τ ^ p * withTopRealPart f x := by
  -- Repackage the scalar as an `NNReal` so the owner homogeneity API applies verbatim.
  simpa using hhom.map_smul hx ⟨τ, hτ⟩

/-- Helper for Theorem 3.1.21: evaluating the subgradient inequality at the ray point `τ • x`
produces the scalar inequality that drives Euler's identity. -/
lemma subgradient_ray_inequality
    {f : E → WithTop ℝ} {p : ℝ}
    (hhom : IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f))
    {x g : E} (hg : g ∈ ∂ f(x)) {τ : ℝ} (hτ : 0 ≤ τ) :
    τ ^ p * withTopRealPart f x ≥ withTopRealPart f x + (τ - 1) * inner ℝ g x := by
  have hx_dom : x ∈ dom f := (mem_subdifferential_iff.mp hg).mem_dom
  have hτx_dom : τ • x ∈ dom f := hhom.smul_mem hx_dom ⟨τ, hτ⟩
  have hsub :
      f (τ • x) ≥ f x + (inner ℝ g (τ • x - x) : WithTop ℝ) :=
    (mem_subdifferential_iff.mp hg).2 hτx_dom
  -- Convert the owner inequality from `WithTop ℝ` back to the finite real part on the domain.
  rw [← coe_withTopRealPart hτx_dom, ← coe_withTopRealPart hx_dom] at hsub
  have hmap : withTopRealPart f (τ • x) = τ ^ p * withTopRealPart f x :=
    withTopRealPart_map_smul_of_nonneg hhom hx_dom hτ
  have hinner : inner ℝ g (τ • x - x) = (τ - 1) * inner ℝ g x := by
    -- Along the ray, the displacement from `x` is the scalar multiple `(τ - 1) • x`.
    calc
      inner ℝ g (τ • x - x) = inner ℝ g ((τ - 1) • x) := by
        congr 1
        simpa [sub_eq_add_neg, one_smul] using (add_smul τ (-1 : ℝ) x).symm
      _ = (τ - 1) * inner ℝ g x := by
        simp [inner_smul_right]
  rw [hmap, hinner] at hsub
  exact_mod_cast hsub

/-- Helper for Theorem 3.1.21: the shifted power profile `t ↦ (1 + t)^p * fx` has derivative
`p * fx` at `t = 0`. -/
lemma one_add_rpow_mul_hasDerivAt_zero {p fx : ℝ} :
    HasDerivAt (fun t : ℝ ↦ (1 + t) ^ p * fx) (p * fx) 0 := by
  have hshift : HasDerivAt (fun t : ℝ ↦ t + 1) 1 0 := by
    -- The shift `t ↦ t + 1` moves the source limit from `τ = 1` to `t = 0`.
    simpa using (hasDerivAt_id 0).add_const (1 : ℝ)
  have hpow : HasDerivAt (fun t : ℝ ↦ (1 + t) ^ p) p 0 := by
    -- Differentiate the power function at `1` and compose with the shift.
    have hcomp :
        HasDerivAt ((fun s : ℝ ↦ s ^ p) ∘ fun t : ℝ ↦ t + 1)
          (p * 1 ^ (p - 1) * 1) 0 := by
      exact HasDerivAt.comp_of_eq
        (x := 0)
        (y := (1 : ℝ))
        (h := fun t : ℝ ↦ t + 1)
        (h₂ := fun s : ℝ ↦ s ^ p)
        (h' := (1 : ℝ))
        (h₂' := p * 1 ^ (p - 1))
        (hh₂ := Real.hasDerivAt_rpow_const (x := 1) (p := p) (Or.inl one_ne_zero))
        (hh := hshift)
        (by simp)
    simpa [Function.comp, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc] using hcomp
  -- Multiplying by the constant finite value `fx` gives the scalar profile used in the slope
  -- limits.
  simpa [mul_comm, mul_left_comm, mul_assoc] using hpow.mul_const fx

/-- Helper for Theorem 3.1.21: the `τ > 1` side of the ray inequality gives the upper bound
`⟪g, x⟫ ≤ p * withTopRealPart f x`. -/
lemma inner_le_degree_mul_value
    {f : E → WithTop ℝ} {p : ℝ}
    (hhom : IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f))
    {x g : E} (hg : g ∈ ∂ f(x)) :
    inner ℝ g x ≤ p * withTopRealPart f x := by
  let w : ℝ → ℝ := fun t ↦ (1 + t) ^ p * withTopRealPart f x
  have hw : HasDerivAt w (p * withTopRealPart f x) 0 := by
    -- Shift the quotient from `τ = 1` to `t = 0` so the right-hand derivative theorem applies.
    simpa [w] using one_add_rpow_mul_hasDerivAt_zero (p := p) (fx := withTopRealPart f x)
  have hslope :
      ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        inner ℝ g x ≤ t⁻¹ * (w (0 + t) - w 0) := by
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have hτ : 0 ≤ 1 + t := by
      nlinarith [ht.1]
    have hineq : w t ≥ w 0 + t * inner ℝ g x := by
      -- Reuse the ray inequality at `τ = 1 + t`.
      have := subgradient_ray_inequality hhom hg hτ
      simpa [w] using this
    have hdiff : t * inner ℝ g x ≤ w t - w 0 := by
      linarith
    have hquot : inner ℝ g x ≤ (w t - w 0) / t := by
      exact (le_div_iff₀ ht.1).2 (by simpa [mul_comm] using hdiff)
    simpa [div_eq_mul_inv, sub_eq_add_neg, add_comm, mul_comm, mul_left_comm, mul_assoc] using
      hquot
  exact ge_of_tendsto hw.tendsto_slope_zero_right hslope

/-- Helper for Theorem 3.1.21: the `τ < 1` side of the ray inequality gives the lower bound
`p * withTopRealPart f x ≤ ⟪g, x⟫`. -/
lemma degree_mul_value_le_inner
    {f : E → WithTop ℝ} {p : ℝ}
    (hhom : IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f))
    {x g : E} (hg : g ∈ ∂ f(x)) :
    p * withTopRealPart f x ≤ inner ℝ g x := by
  let w : ℝ → ℝ := fun t ↦ (1 + t) ^ p * withTopRealPart f x
  have hw : HasDerivAt w (p * withTopRealPart f x) 0 := by
    -- The same shifted profile controls the left-hand slope as `t ↑ 0`.
    simpa [w] using one_add_rpow_mul_hasDerivAt_zero (p := p) (fx := withTopRealPart f x)
  have hslope :
      ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Iio 0),
        t⁻¹ * (w (0 + t) - w 0) ≤ inner ℝ g x := by
    filter_upwards [Ico_mem_nhdsLT (show (-1 : ℝ) < 0 by norm_num)] with t ht
    have hτ : 0 ≤ 1 + t := by
      nlinarith [ht.1]
    have hineq : w t ≥ w 0 + t * inner ℝ g x := by
      -- Reuse the same ray inequality, now with a negative increment `t`.
      have := subgradient_ray_inequality hhom hg hτ
      simpa [w] using this
    have hdiff : t * inner ℝ g x ≤ w t - w 0 := by
      linarith
    have hquot : (w t - w 0) / t ≤ inner ℝ g x := by
      exact (div_le_iff_of_neg ht.2).2 (by simpa [mul_comm] using hdiff)
    simpa [div_eq_mul_inv, sub_eq_add_neg, add_comm, mul_comm, mul_left_comm, mul_assoc] using
      hquot
  exact le_of_tendsto hw.tendsto_slope_zero_left hslope

/-- Theorem 3.1.21: if an `ℝ ∪ {+∞}`-valued function is homogeneous of degree `p` on its
effective domain, then every subgradient `g ∈ ∂ f(x)` satisfies `⟪g, x⟫ = p f(x)` on the finite
real part of `f`. -/
-- Proof sketch: apply the subgradient inequality to the points `τ • x` along the ray through
-- `x`, then rewrite the function values using the homogeneity assumption. Dividing by `τ - 1` for
-- `τ > 1` and `0 ≤ τ < 1` yields opposite inequalities for `inner ℝ g x`; passing to the limit
-- `τ → 1` gives `inner ℝ g x = p * withTopRealPart f x`.
theorem euler_homogeneous_function_theorem
    {f : E → WithTop ℝ} {p : ℝ}
    (hhom : IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f))
    {x g : E} (hg : g ∈ ∂ f(x)) :
    inner ℝ g x = p * withTopRealPart f x := by
  -- The right- and left-hand slope limits give matching upper and lower bounds.
  exact le_antisymm (inner_le_degree_mul_value hhom hg) (degree_mul_value_le_inner hhom hg)

end

/-! ### Lemma_3_1_22 (from Chap03) -/
/- Lemma 3.1.22 lies in the chapter's parametric minimax / convex-analysis domain.

Sampled owner-style declarations:
- the slice-infimum value function `u ↦ sInf ((fun x ↦ Ψ x u) '' P)`
- `ClosedConvexOn.max_inter`
- `exists_minimax_parameter_of_bounded_constrainedSublevelSets`
- `exists_isMinOn_parametricMaximumObjective_eq_valueFunction_of_valueFunction_maximizer`

Best owner abstraction:
- source-facing: the attained minimum of the two-slice maximum together with its value-function
  identification at a maximizing parameter;
- core/canonical: the Chapter 3 owner theorem
  `exists_isMinOn_parametricMaximumObjective_eq_valueFunction_of_valueFunction_maximizer`;
- bridge/view: the internal `WithTop` lift used only in the theorem's slice-geometry hypotheses.

Primitive data:
- the feasible set `P`
- the parameter set `S`
- the real-valued kernel `Ψ`
- nonemptiness of `P`, which lets the dual closed-concavity owner recover `Convex ℝ S`
- closed-convexity and bounded constrained sublevel sets of the primal slices
- closed-concavity of the dual slices, encoded canonically by closed convexity of `u ↦ -Ψ(x, u)`
- the canonical maximizing-parameter datum
  `uStar ∈ S ∧ IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar`

Derived API:
- the attained minimizer of `x ↦ max (Ψ x u) (Ψ x uStar)`
- the equality of that minimum value with `sInf ((fun x ↦ Ψ x uStar) '' P)`

Source/core/bridge triage:
- source-facing: the textbook minimum-attainment statement for the maximum of two parameter
  slices of a convex-concave kernel;
- core/canonical: the earlier Chapter 3 theorem above;
- bridge/view: the internal `WithTop` lift used by the closed-convex owner API.

The previous file introduced a second public theorem stated through the later wrapper
`maximinLowerValue`, weakened the conclusion to a bare `sInf` equality, and kept redundant convexity
data in the local API. This refinement removes that duplicate wrapper layer and makes the numbered
item a direct recall of the canonical owner theorem from `Lemma_3_22`.
-/

recall exists_isMinOn_parametricMaximumObjective_eq_valueFunction_of_valueFunction_maximizer

/-! ### Theorem_3_1_22 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped SupportFunction

/-
Theorem 3.1.22 lies in the chapter's support-function intersection domain.

Relevant sampled owner declarations:
- `supportFunction` / `supportFunction_apply` in `Definition_3_9`, the source-facing owner for
  `ξ[Q]`
- `supportFunction_dom_eq_univ_of_nonempty_bounded` in `Proposition_3_11`, the earlier bounded
  support-function finiteness theorem in the same owner language
- `supportFunction_eq_on_common_domain_implies_eq` in `Theorem_3_17`, the chapter comparison
  theorem for support functions of closed convex sets
- downstream recall `Theorem_3_27`, which uses this theorem as the owner declaration for the
  intersection formula

Best owner abstraction:
- this theorem itself, stated directly in the chapter owner language `ξ[Q]`; no smaller upstream
  owner theorem for the support function of an intersection as an attained translated-sum infimum
  was found in the sampled project/mathlib domain

Primitive data:
- the sets `Q₁`, `Q₂`
- boundedness and convexity of each set
- nonempty interior of `Q₁ ∩ Q₂`
- the evaluation point `x`

Derived API:
- the attained-infimum statement that `ξ[Q₁ ∩ Q₂] x` is the least value of
  `y ↦ ξ[Q₁] (x + y) + ξ[Q₂] (-y)`
- the direct recall in `Theorem_3_27`

Source/core/bridge triage:
- source-facing: the textbook support-function formula for intersections
- core/canonical: this theorem, expressed directly with the owner `supportFunction`
- bridge/view: the canonical attained-infimum interface `IsLeast` for the translated-sum value set

The textbook states the result on `ℝⁿ`, but the public owner data here are the support functions of
bounded convex sets together with finite-dimensionality and the nonempty-interior intersection
hypothesis. Closedness is proof-route data rather than owner data, because support functions are
closure-invariant and the common-interior hypothesis identifies the closure of `Q₁ ∩ Q₂` with the
intersection of the closures. The theorem therefore lives at the intrinsic finite-dimensional real
inner-product-space layer, with `ℝⁿ` available as a downstream specialization. -/

/-- Theorem 3.1.22: for bounded convex sets `Q₁` and `Q₂` with nonempty interior intersection in a
finite-dimensional real inner-product space, the support function of `Q₁ ∩ Q₂` at `x` is the
minimum over all `y` of
`ξ_{Q₁}(x + y) + ξ_{Q₂}(-y)`, expressed here as the least element of the translated-sum value set.
-/
-- Proof sketch: first show the translated-sum objective
-- `y ↦ supportFunction Q₁ (x + y) + supportFunction Q₂ (-y)` attains its infimum using
-- boundedness, convexity, and the nonempty interior of `Q₁ ∩ Q₂`, after replacing `Q₁` and `Q₂`
-- by their closures. The inequality
-- `supportFunction (Q₁ ∩ Q₂) x ≤ ...` comes from testing against common points of the
-- intersection, and equality follows from the optimality condition for a minimizer together with
-- the subdifferential sum rule and the support-point characterization of the subdifferential of a
-- support function.
theorem supportFunction_inter_isLeast_add_supportFunction
    [FiniteDimensional ℝ E]
    {Q₁ Q₂ : Set E}
    (hQ₁_bounded : Bornology.IsBounded Q₁) (hQ₁_convex : Convex ℝ Q₁)
    (hQ₂_bounded : Bornology.IsBounded Q₂) (hQ₂_convex : Convex ℝ Q₂)
    (hQ_int : (interior (Q₁ ∩ Q₂)).Nonempty) (x : E) :
    IsLeast
      (Set.range fun y : E ↦ ξ[Q₁] (x + y) + ξ[Q₂] (-y))
      (ξ[Q₁ ∩ Q₂] x) := sorry

end

/-! ### Lemma_3_1_23 (from Chap03) -/
universe u v

section

variable {E : Type u} {U : Type v} {α : Type*} [AddCommGroup α] [Preorder α]
  [AddLeftMono α] [AddRightMono α]

/- Lemma 3.1.23 lies in the chapter's primal-dual gap domain.

Primary domain:
- one-step primal-dual gap estimates in an ordered additive value type under primal lower bounds,
  dual upper bounds, and weak duality

Sampled owner-style declarations:
- `Set.Icc` / `Set.mem_Icc` in mathlib, the canonical closed-interval owner for the target bound
- `sub_nonneg` and `sub_nonpos` in mathlib, the canonical ordered-additive owners for the two
  primitive gap comparisons
- `primal_dual_decomposition_mem_Icc_and_gap_le_of_averaged_affine_lower_model` in
  `Chap03/Lemma_3_23`
- `primal_dual_decomposition_mem_Icc_and_gap_le_of_gap_le_sSup_delta` in `Chap03/Lemma_3_1_24`

Best owner abstraction:
- this theorem itself is the source-facing owner for the generic one-step decomposition interval;
  its primitive inputs are the local primal and dual comparison inequalities at the chosen pair,
  and later Chapter 3 results derive those inequalities from concrete lower-value and certificate
  constructions

Primitive data:
- the functions `f`, `φ`
- the points `xN`, `uHat`
- the comparison values `fStar`, `φStar`, `rN`
- the local comparison bounds `fStar ≤ f xN` and `φ uHat ≤ φStar`

Derived API:
- weak duality `φStar ≤ fStar`
- the residual estimate `f xN - φ uHat ≤ rN`
- any set-based or optimal-value owners used later only to derive the two local comparison bounds

Source/core/bridge triage:
- source-facing: the textbook interval estimate for the decomposition at a residual-controlled pair
- core/canonical: the order/arithmetic comparison between the decomposition and the raw
  primal-dual gap under local primal and dual comparison bounds together with weak duality
- bridge/view: the Chapter 3 certificate and affine-lower-model specializations in
  `Lemma_3_1_24` and `Lemma_3_23`

There is no stricter upstream theorem with the same generic interface. This file therefore keeps
the generic source-facing owner itself, but reduces its public inputs to the primitive local
inequalities actually used by the arithmetic instead of carrying ambient sets and global
lower/upper-bound hypotheses that direct downstream files immediately specialize back to the chosen
pair `(xN, uHat)`.
-/

/-- Lemma 3.1.23: if `x_N` satisfies the residual estimate `(3.1.85)`, written here as
`f(x_N) - φ(\hat u_N) ≤ r_N`, then the decomposition
`(f(x_N) - f^*) + (φ^* - φ(\hat u_N))` lies between `0` and the primal-dual gap
`f(x_N) - φ(\hat u_N)`, and that gap is itself bounded above by `r_N`. -/
-- Proof sketch: the local primal and dual comparison bounds give
-- `0 ≤ f(x_N) - f^*` and `0 ≤ φ^* - φ(\hat u_N)`, so the decomposition is nonnegative. The
-- difference between the primal-dual gap and the decomposition is `f^* - φ^*`, which is
-- nonnegative by weak duality. The final upper bound is exactly the assumed residual estimate
-- `(3.1.85)`.
theorem primal_dual_decomposition_mem_Icc_of_gap_le
    {f : E → α} {φ : U → α} {xN : E} {uHat : U} {fStar φStar rN : α}
    (h_primal : fStar ≤ f xN) (h_dual : φ uHat ≤ φStar)
    (h_weak_duality : φStar ≤ fStar)
    (h_gap : f xN - φ uHat ≤ rN) :
    (f xN - fStar) + (φStar - φ uHat) ∈ Set.Icc 0 (f xN - φ uHat) ∧
      f xN - φ uHat ≤ rN := by
  have h_primal_gap : 0 ≤ f xN - fStar := sub_nonneg.mpr h_primal
  have h_dual_gap : 0 ≤ φStar - φ uHat := sub_nonneg.mpr h_dual
  have h_nonneg : 0 ≤ (f xN - fStar) + (φStar - φ uHat) :=
    add_nonneg h_primal_gap h_dual_gap
  have h_le_gap : (f xN - fStar) + (φStar - φ uHat) ≤ f xN - φ uHat := by
    calc
      (f xN - fStar) + (φStar - φ uHat) = (f xN - φ uHat) + (φStar - fStar) := by
        abel
      _ ≤ (f xN - φ uHat) + 0 := by
        exact add_le_add_right (sub_nonpos.mpr h_weak_duality) (f xN - φ uHat)
      _ = f xN - φ uHat := by simp
  refine ⟨?_, h_gap⟩
  rw [Set.mem_Icc]
  exact ⟨h_nonneg, h_le_gap⟩

end

/-! ### Theorem_3_1_23 (from Chap03) -/
open scoped Gradient WithTopConvexAnalysis

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 3.1.23 lies in the chapter's convex composite first-order optimality domain.

Sampled owner-style declarations:
- `ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt` in `Chap02/Theorem_2_29`
- `constrainedSubdifferential` and `mem_constrainedSubdifferential_iff` in
  `Chap03/Definition_3_1_5`
- mathlib `ConvexOn.add`

Best owner abstraction:
- `ConvexOn.isMinOn_add_iff_neg_hasGradient_mem_constrainedSubdifferential`; it extends the
  Chapter 2 constrained first-order owner from a single convex differentiable term to a convex
  composite `f + Ψ`, and expresses the nonsmooth term through the chapter's existing constrained
  subdifferential owner instead of a second raw inequality wrapper.

Primitive data:
- a convex feasible set `Q`, already packaged by `ConvexOn ℝ Q f` and `ConvexOn ℝ Q Ψ`
- a smooth convex term `f`
- a convex term `Ψ`
- a feasible candidate minimizer `xStar`
- an explicit gradient witness `HasGradientAt f g xStar`

Derived API:
- the raw inequality bridge
  `ConvexOn.isMinOn_add_iff_variational_inequality_of_hasGradientAt`
- the source-facing gradient specialization
  `isMinOn_add_convex_iff_forall_inner_gradient_add_ge`

Source/core/bridge triage:
- source-facing: the textbook gradient inequality for minimizing `x ↦ f x + Ψ x` on `Q`
- core/canonical: `constrainedSubdifferential` together with
  `ConvexOn.isMinOn_add_iff_neg_hasGradient_mem_constrainedSubdifferential`
- bridge/view: the raw variational inequality and the specialization replacing an explicit
  gradient witness by `∇ f xStar` via `DifferentiableAt.hasGradientAt`

The earlier version fixed the ambient space to `EuclideanSpace ℝ (Fin n)`, repeated the redundant
set-convexity hypothesis `Convex ℝ Q`, and required `DifferentiableOn ℝ f Q` although only the
gradient data at `xStar` enters the optimality criterion. The refined owner theorem below lifts
the statement to the chapter's real inner-product-space setting, keeps the pointwise gradient
witness as primitive data, and reuses the earlier constrained-subdifferential owner for `Ψ`; the
textbook displayed inequality and `∇ f xStar` form remain as thin bridges. -/

namespace ConvexOn

variable {Q : Set E} {f Ψ : E → ℝ} {xStar g : E}

/-- A feasible point minimizes the convex composite `f + Ψ` on `Q` exactly when the negative
gradient witness of `f` belongs to the constrained subdifferential of `Ψ` on `Q` at `xStar`. -/
-- Proof sketch: use the Chapter 2 owner theorem for minimizing `f` on `Q` together with the
-- defining inequality of the constrained subdifferential of `Ψ`; the two affine lower-support
-- inequalities add to the minimizing condition for `f + Ψ`.
theorem isMinOn_add_iff_neg_hasGradient_mem_constrainedSubdifferential
    (hf_conv : ConvexOn ℝ Q f) (hΨ_conv : ConvexOn ℝ Q Ψ)
    (hxStar : xStar ∈ Q) (hf_grad : HasGradientAt f g xStar) :
    IsMinOn (f + Ψ) Q xStar ↔
      -g ∈ ∂[Q] (fun x ↦ (Ψ x : WithTop ℝ))(xStar) := by
  rw [mem_constrainedSubdifferential_iff]
  constructor
  · intro hmin
    refine ⟨hxStar, by simp, ?_⟩
    intro x hx
    let γ : ℝ →ᵃ[ℝ] E := AffineMap.lineMap xStar x
    let u : ℝ → ℝ := fun t ↦ f (γ t)
    let w : ℝ → ℝ := fun t ↦ u t + t * (Ψ x - Ψ xStar)
    have hγ_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : γ t ∈ Q := by
      simpa [γ] using hf_conv.1.lineMap_mem hxStar hx ht
    have hu :
        HasDerivAt u (inner ℝ g (x - xStar)) 0 := by
      have hline : HasDerivAt γ (x - xStar) 0 := by
        simpa [γ] using γ.hasDerivAt
      have hgrad :
          HasFDerivAt f ((InnerProductSpace.toDual ℝ E) g) (γ 0) := by
        simpa [γ] using hf_grad.hasFDerivAt
      simpa [u, γ, hf_grad.fderiv_apply] using hgrad.comp_hasDerivAt 0 hline
    have hw :
        HasDerivAt w (inner ℝ g (x - xStar) + (Ψ x - Ψ xStar)) 0 := by
      simpa [w, u, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm,
        mul_assoc] using hu.add ((hasDerivAt_id (0 : ℝ)).const_mul (Ψ x - Ψ xStar))
    have hslope_nonneg :
        ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 ≤ slope w 0 t := by
      filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
      have hmin_t : f xStar + Ψ xStar ≤ f (γ t) + Ψ (γ t) := by
        simpa [γ] using (isMinOn_iff.mp hmin (γ t) (hγ_mem htIcc))
      have hΨ_t :
          Ψ (γ t) ≤ Ψ xStar + t * (Ψ x - Ψ xStar) := by
        have hconv_t :
            Ψ (γ t) ≤ (1 - t) * Ψ xStar + t * Ψ x := by
          simpa [γ, AffineMap.lineMap_apply_module] using
            hΨ_conv.2 hxStar hx (sub_nonneg.mpr ht.2) ht.1.le (by ring)
        linarith
      have hw0le : w 0 ≤ w t := by
        have hbound : f xStar ≤ u t + t * (Ψ x - Ψ xStar) := by
          linarith
        simpa [w, u, γ] using hbound
      have : 0 ≤ (w t - w 0) / (t - 0) := by
        exact div_nonneg (sub_nonneg.mpr hw0le) (sub_nonneg.mpr ht.1.le)
      simpa [slope_def_field, ht.1.ne'] using this
    have hslope_nonneg' :
        ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 ≤ t⁻¹ * (w (0 + t) - w 0) := by
      filter_upwards [hslope_nonneg, self_mem_nhdsWithin] with t ht htpos
      have ht0 : 0 < t := htpos
      have hquot : 0 ≤ (w t - w 0) / t := by
        simpa [slope_def_field, ht0.ne'] using ht
      simpa [div_eq_mul_inv, sub_eq_add_neg, mul_comm, add_comm] using hquot
    have hderiv_nonneg : 0 ≤ inner ℝ g (x - xStar) + (Ψ x - Ψ xStar) := by
      exact ge_of_tendsto hw.tendsto_slope_zero_right hslope_nonneg'
    have hreal' : Ψ xStar - inner ℝ g (x - xStar) ≤ Ψ x := by
      linarith
    have hreal : Ψ xStar + inner ℝ (-g) (x - xStar) ≤ Ψ x := by
      simpa using hreal'
    exact_mod_cast hreal
  · rintro ⟨-, -, hsub⟩
    have hgradWithin : HasGradientWithinAt f g Q xStar := by
      exact (hasGradientWithinAt_iff_hasFDerivWithinAt).2 hf_grad.hasFDerivAt.hasFDerivWithinAt
    refine isMinOn_iff.mpr ?_
    intro x hx
    have hf_lower :
        f xStar + inner ℝ g (x - xStar) ≤ f x := by
      exact hf_conv.lower_tangent_plane_of_hasGradientWithinAt xStar hxStar g hgradWithin x hx
    have hΨ_lower_cast :
        (((Ψ xStar + inner ℝ (-g) (x - xStar) : ℝ) : WithTop ℝ) ≤ (Ψ x : WithTop ℝ)) := by
      simpa [ge_iff_le] using hsub hx
    have hΨ_lower :
        Ψ xStar + inner ℝ (-g) (x - xStar) ≤ Ψ x := by
      exact_mod_cast hΨ_lower_cast
    have hΨ_lower' :
        Ψ xStar - inner ℝ g (x - xStar) ≤ Ψ x := by
      simpa using hΨ_lower
    change f xStar + Ψ xStar ≤ f x + Ψ x
    linarith

/-- A feasible point minimizes the convex composite `f + Ψ` on `Q` exactly when every feasible
displacement satisfies the corresponding raw variational inequality against an explicit gradient
witness for `f` at `xStar`. -/
theorem isMinOn_add_iff_variational_inequality_of_hasGradientAt
    (hf_conv : ConvexOn ℝ Q f) (hΨ_conv : ConvexOn ℝ Q Ψ)
    (hxStar : xStar ∈ Q) (hf_grad : HasGradientAt f g xStar) :
    IsMinOn (f + Ψ) Q xStar ↔
      ∀ x ∈ Q, inner ℝ g (x - xStar) + Ψ x ≥ Ψ xStar := by
  rw [hf_conv.isMinOn_add_iff_neg_hasGradient_mem_constrainedSubdifferential
    hΨ_conv hxStar hf_grad, mem_constrainedSubdifferential_iff]
  constructor
  · intro h x hx
    have hcast : Ψ xStar + inner ℝ (-g) (x - xStar) ≤ Ψ x := by
      exact_mod_cast h.2.2 hx
    have hineq : Ψ xStar + -inner ℝ g (x - xStar) ≤ Ψ x := by
      simpa using hcast
    linarith
  · intro h
    refine ⟨hxStar, by simp, ?_⟩
    intro x hx
    have hineq : inner ℝ g (x - xStar) + Ψ x ≥ Ψ xStar := h x hx
    have hreal : Ψ xStar + -inner ℝ g (x - xStar) ≤ Ψ x := by
      linarith
    have hcast : Ψ xStar + inner ℝ (-g) (x - xStar) ≤ Ψ x := by
      simpa using hreal
    exact_mod_cast hcast

end ConvexOn

/-- Theorem 3.1.23: a point `xStar ∈ Q` solves the convex composite minimization problem
`min_{x ∈ Q} (f x + Ψ x)` if and only if it satisfies the variational inequality
`⟪∇ f xStar, x - xStar⟫ + Ψ x ≥ Ψ xStar` for every feasible point `x ∈ Q`. -/
-- Proof sketch: specialize the owner theorem above with the canonical gradient witness
-- `hf_diff.hasGradientAt`.
theorem isMinOn_add_convex_iff_forall_inner_gradient_add_ge
    {Q : Set E} {f Ψ : E → ℝ}
    (hf_conv : ConvexOn ℝ Q f)
    (hΨ_conv : ConvexOn ℝ Q Ψ)
    {xStar : E} (hxStar : xStar ∈ Q) (hf_diff : DifferentiableAt ℝ f xStar) :
    IsMinOn (f + Ψ) Q xStar ↔
      ∀ x ∈ Q, inner ℝ (∇ f xStar) (x - xStar) + Ψ x ≥ Ψ xStar :=
  hf_conv.isMinOn_add_iff_variational_inequality_of_hasGradientAt hΨ_conv hxStar
    hf_diff.hasGradientAt

end

/-! ### Lemma_3_1_24 (from Chap03) -/
open Filter

universe u v

section

variable {E : Type u} {U : Type v}

/- Lemma 3.1.24 lies in the chapter's primal-dual gap domain.

Primary domain:
- stagewise primal-dual gap bounds from certificate maxima and weak duality

Sampled owner-style declarations:
- `primal_dual_decomposition_mem_Icc_of_gap_le` in `Chap03/Lemma_3_1_23`, the generic
  interval owner for one primal-dual gap value;
- `primal_dual_decomposition_mem_Icc_and_gap_le_of_gapFunctionCertificate_max` in
  `Chap03/Lemma_3_24`, the neighboring source-facing max-attainment specialization of that
  interval owner;
- `primal_dual_decomposition_mem_Icc_and_gap_le_of_gapFunctionCertificate_sSup` in
  `Chap03/Lemma_3_24`, the corresponding canonical `sSup` companion theorem;
- `IsGreatest.csSup_eq` in mathlib, the canonical bridge from an explicit maximum-attainment
  statement to the corresponding supremum equality.

Best owner abstraction:
- source-facing: the stagewise primal-dual interval bound under an attained certificate maximum
  `δMax N`;
- core/canonical: `primal_dual_decomposition_mem_Icc_of_gap_le`;
- bridge/view: the canonical `sSup (δ N '' P)` reformulations obtained from `(hδMax N).csSup_eq`.

Primitive data:
- the certificate family `δ`
- the set `P`
- the scalar sequences `hatf`, `uHat`, `r`
- the comparison values `fStar`, `φStar`
- the source-facing maximum values `δMax`

Derived API:
- the local primal comparison `fStar ≤ hatf N`
- the stagewise dual comparison `φ (uHat N) ≤ φStar`
- weak duality `φStar ≤ fStar`
- the canonical supremum view `sSup (δ N '' P)` of the attained maxima

Source/core/bridge triage:
- source-facing: the textbook stagewise estimate and its convergence consequence expressed through
  an attained maximum `δMax N`;
- core/canonical: `primal_dual_decomposition_mem_Icc_of_gap_le`
- bridge/view: the companion `sSup` interval and convergence reformulations

The interval/decomposition owner already lives in `Lemma_3_1_23`, so this file keeps the
attained-maximum statement primary and retains the `sSup` formulations only as companion
canonical views. -/

section

variable {P : Set E}
variable (δ : ℕ → E → ℝ) (hatf : ℕ → ℝ) (φ : U → ℝ) (uHat : ℕ → U)
variable (fStar φStar : ℝ) (r : ℕ → ℝ)
variable
    (h_primal_lower : ∀ N, fStar ≤ hatf N)
    (h_dual_upper_uHat : ∀ N, φ (uHat N) ≤ φStar)
    (h_weak_duality : φStar ≤ fStar)

include h_primal_lower h_dual_upper_uHat h_weak_duality

local notation "gap" =>
  fun N ↦ hatf N - φ (uHat N)

local notation "decomposition" =>
  fun N ↦ (hatf N - fStar) + (φStar - φ (uHat N))

/-- Helper for Lemma 3.1.24: the canonical `sSup` bounds imply both the interval control for the
stagewise decomposition and the stagewise `r_N` bound on the primal-dual gap. -/
-- Proof sketch: combine the two `sSup` inequalities into `gap N ≤ r N`, then invoke the generic
-- owner theorem from Lemma 3.1.23 for the fixed stage `N`.
private theorem primal_dual_decomposition_mem_Icc_and_gap_le_of_gap_le_sSup_delta_aux
    (h_gap_le_sSup_delta : ∀ N, hatf N - φ (uHat N) ≤ sSup (δ N '' P))
    (h_sSup_delta_le : ∀ N, sSup (δ N '' P) ≤ r N)
    (N : ℕ) :
    decomposition N ∈ Set.Icc 0 (gap N) ∧ gap N ≤ r N := by
  simpa using
    (primal_dual_decomposition_mem_Icc_of_gap_le
      (h_primal_lower N)
      (h_dual_upper_uHat N)
      h_weak_duality
      (le_trans (h_gap_le_sSup_delta N) (h_sSup_delta_le N)))

/-- Lemma 3.1.24: if the stagewise gap is bounded by an attained certificate maximum `δMax N`,
and these maxima satisfy `δMax N ≤ r_N`, then for every stage `N` the decomposition
`(\hat f_N - f^*) + (\phi^* - φ(\hat u_N))` lies in the interval
`[0, \hat f_N - φ(\hat u_N)]` and the gap itself is bounded by `r_N`. -/
-- Proof sketch: rewrite the attained maxima as the canonical suprema `sSup (δ N '' P)` via
-- `(hδMax N).csSup_eq`, then apply the generic interval owner
-- `primal_dual_decomposition_mem_Icc_of_gap_le` at each single stage `N`.
theorem primal_dual_decomposition_mem_Icc_and_gap_le_of_gap_le_max_delta
    (δMax : ℕ → ℝ)
    (hδMax : ∀ N, IsGreatest (δ N '' P) (δMax N))
    (h_gap_le_δMax : ∀ N, hatf N - φ (uHat N) ≤ δMax N)
    (h_δMax_le : ∀ N, δMax N ≤ r N)
    (N : ℕ) :
    decomposition N ∈ Set.Icc 0 (gap N) ∧ gap N ≤ r N := by
  have h_gap_le_sSup_delta : ∀ n, hatf n - φ (uHat n) ≤ sSup (δ n '' P) := by
    intro n
    simpa [(hδMax n).csSup_eq] using h_gap_le_δMax n
  have h_sSup_delta_le : ∀ n, sSup (δ n '' P) ≤ r n := by
    intro n
    simpa [(hδMax n).csSup_eq] using h_δMax_le n
  simpa using
    (primal_dual_decomposition_mem_Icc_and_gap_le_of_gap_le_sSup_delta_aux
      δ hatf φ uHat fStar φStar r h_primal_lower h_dual_upper_uHat h_weak_duality
      h_gap_le_sSup_delta h_sSup_delta_le N)

/-- Companion canonical `sSup` reformulation of Lemma 3.1.24. -/
-- Proof sketch: combine the stagewise supremum control with the supremum upper bound to get
-- `gap N ≤ r N`, then apply the owner theorem `primal_dual_decomposition_mem_Icc_of_gap_le`
-- at each single stage `N`.
theorem primal_dual_decomposition_mem_Icc_and_gap_le_of_gap_le_sSup_delta
    (h_gap_le_sSup_delta : ∀ N, hatf N - φ (uHat N) ≤ sSup (δ N '' P))
    (h_sSup_delta_le : ∀ N, sSup (δ N '' P) ≤ r N)
    (N : ℕ) :
    decomposition N ∈ Set.Icc 0 (gap N) ∧ gap N ≤ r N := by
  simpa using
    (primal_dual_decomposition_mem_Icc_and_gap_le_of_gap_le_sSup_delta_aux
      δ hatf φ uHat fStar φStar r h_primal_lower h_dual_upper_uHat h_weak_duality
      h_gap_le_sSup_delta h_sSup_delta_le N)

/-- Companion canonical `sSup` convergence reformulation of Lemma 3.1.24. -/
-- Proof sketch: apply
-- `primal_dual_decomposition_mem_Icc_and_gap_le_of_gap_le_sSup_delta` to get
-- `0 ≤ hatf N - φ(\hat u_N) ≤ r_N` for every `N`, then use `squeeze_zero`.
theorem primal_dual_gap_tendsto_zero_of_gap_le_sSup_delta
    (h_gap_le_sSup_delta : ∀ N, hatf N - φ (uHat N) ≤ sSup (δ N '' P))
    (h_sSup_delta_le : ∀ N, sSup (δ N '' P) ≤ r N)
    (hr_tendsto : Tendsto r atTop (nhds 0)) :
    Tendsto gap atTop (nhds 0) := by
  have h_step (N : ℕ) :
      decomposition N ∈ Set.Icc 0 (gap N) ∧ gap N ≤ r N :=
    primal_dual_decomposition_mem_Icc_and_gap_le_of_gap_le_sSup_delta
      δ hatf φ uHat fStar φStar r h_primal_lower h_dual_upper_uHat h_weak_duality
      h_gap_le_sSup_delta h_sSup_delta_le N
  have h_gap_nonneg : ∀ N, 0 ≤ gap N := by
    intro N
    have h_mem := Set.mem_Icc.mp (h_step N).1
    exact le_trans h_mem.1 h_mem.2
  have h_gap_le_r : ∀ N, gap N ≤ r N := by
    intro N
    exact (h_step N).2
  refine squeeze_zero ?_ ?_ hr_tendsto
  · exact h_gap_nonneg
  · exact h_gap_le_r

/-- If the stagewise gap in Lemma 3.1.24 is controlled by attained certificate maxima `δMax N`
bounded by a sequence `r_N` converging to `0`, then the primal-dual gap itself converges to `0`. -/
-- Proof sketch: rewrite the attained maxima as the canonical suprema `sSup (δ N '' P)` via
-- `(hδMax N).csSup_eq`, then apply the companion `sSup` convergence theorem.
theorem primal_dual_gap_tendsto_zero_of_gap_le_max_delta
    (δMax : ℕ → ℝ)
    (hδMax : ∀ N, IsGreatest (δ N '' P) (δMax N))
    (h_gap_le_δMax : ∀ N, hatf N - φ (uHat N) ≤ δMax N)
    (h_δMax_le : ∀ N, δMax N ≤ r N)
    (hr_tendsto : Tendsto r atTop (nhds 0)) :
    Tendsto gap atTop (nhds 0) := by
  have h_gap_le_sSup_delta : ∀ N, hatf N - φ (uHat N) ≤ sSup (δ N '' P) := by
    intro N
    simpa [(hδMax N).csSup_eq] using h_gap_le_δMax N
  have h_sSup_delta_le : ∀ N, sSup (δ N '' P) ≤ r N := by
    intro N
    simpa [(hδMax N).csSup_eq] using h_δMax_le N
  simpa using
    primal_dual_gap_tendsto_zero_of_gap_le_sSup_delta
      δ hatf φ uHat fStar φStar r h_primal_lower h_dual_upper_uHat h_weak_duality
      h_gap_le_sSup_delta h_sSup_delta_le hr_tendsto

end

end
