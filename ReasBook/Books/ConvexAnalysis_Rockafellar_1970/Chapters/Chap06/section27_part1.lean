import Mathlib
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Set.Prod
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_6_27_1 (from Chap06) -/
open Bornology
open Filter
open scoped Topology Rockafellar

universe u

section

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.27.1 says that any sequence along which a closed proper convex
  function tends to its infimum is bounded when the function has no recession direction, and that
  every cluster point of such a sequence belongs to the minimum set of the function.
- `core/canonical`: the relevant owner abstractions already present are the primitive convexity,
  properness, and lower-semicontinuity owners (`Function.IsConvex`, `Function.IsProper`,
  `LowerSemicontinuous`) together with `Function.RecedesInDirection` for the boundedness clause,
  the Chapter 6 minimum-set owner `minimumSet`, the bornological boundedness owner `IsBounded`,
  and the sequence-cluster owner `MapClusterPt`.
- `bridge/view`: the textbook sequence statement is split into two atomic declarations, one for
  boundedness of the range and one for membership of cluster points in `minimumSet f`, instead of
  a single conjunction.

Domain-style sampling used here:
- `minimumSet` from `Definition_6_27_3`;
- `Function.RecedesInDirection` from `Definition_6_27_4`;
- primitive owners `Function.IsConvex`, `Function.IsProper`, and `LowerSemicontinuous`;
- `LowerSemicontinuous.isClosed_preimage` from mathlib's semicontinuity API;
- `IsBounded` and `MapClusterPt` from the canonical mathlib topology/bornology API.

Primitive data vs derived API:
- primitive inputs: a sequence `x : ℕ → E`, convergence of the scalar sequence `f ∘ x` to the
  infimum `⨅ y, f y`, and then either convexity/properness/lower-semicontinuity of `f` for the
  boundedness clause or just `LowerSemicontinuous f` for the cluster-point clause;
- extra source-side hypothesis for the boundedness clause: `f` has no recession direction;
- derived outputs: boundedness of `Set.range x` and membership of every cluster point in
  `minimumSet f`.

Layer target: `source-facing`, stated directly on the canonical sequence and minimum-set owners
rather than through a packaged asymptotic-minimization structure.
-/

omit [OrderTopology 𝕜]
  [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)] [FiniteDimensional 𝕜 E] in
private theorem functionRecessionCone_eq_singleton_zero_of_no_recession_direction
    {f : E → WithBotTop 𝕜}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hno_recession : ¬ ∃ y : E, f.RecedesInDirection 𝕜 y) :
    Function.recessionCone ((f)₀⁺) = ({0} : Set E) := by
  ext y
  constructor
  · intro hy
    by_cases hy0 : y = 0
    · simp [hy0]
    · exact False.elim <| hno_recession ⟨y,
        Function.RecedesInDirection.of_mem_recessionCone hf_convex hf_proper hy0 hy⟩
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    rw [Function.mem_recessionCone_iff, Function.recessionFunction_apply]
    refine sSup_le ?_
    rintro r ⟨u, _, rfl⟩
    simpa using (WithBotTop.sub_self_le_zero : f u - f u ≤ (0 : WithBotTop 𝕜))

private theorem isBounded_sublevelSet_of_no_recession_direction
    {f : E → WithBotTop 𝕜}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) (hf_closed : LowerSemicontinuous f)
    (hno_recession : ¬ ∃ y : E, f.RecedesInDirection 𝕜 y)
    {a : 𝕜} (ha_nonempty : (f ⁻¹' Set.Iic a).Nonempty) :
    IsBounded (f ⁻¹' Set.Iic a) := by
  have hsublevel_recession :
      0⁺[𝕜] (f ⁻¹' Set.Iic a) = ({0} : Set E) := by
    calc
      0⁺[𝕜] (f ⁻¹' Set.Iic a) = Function.recessionCone ((f)₀⁺) := by
        simpa using
          hf_convex.recessionCone_sublevelSet_eq_functionRecessionCone
            hf_proper hf_closed a ha_nonempty
      _ = ({0} : Set E) :=
        functionRecessionCone_eq_singleton_zero_of_no_recession_direction
          hf_convex hf_proper hno_recession
  exact
    ((hf_convex.convex_le (a : WithBotTop 𝕜)).isBounded_iff_recessionCone_eq_singleton_zero
      ((lowerSemicontinuous_iff_isClosed_sublevel_withBotTop.1 hf_closed) a)
      ha_nonempty).mpr hsublevel_recession

-- Proof sketch: pick a finite minimizer value `m = ⨅ y, f y` from Theorem 6.27.2 and consider the
-- fixed scalar sublevel set `{u | f u ≤ m + 1}`. Its recession cone agrees with the function
-- recession cone and is therefore `{0}` by the no-recession hypothesis, so Theorem 8.4 gives
-- boundedness of that sublevel set. Convergence of `f (x n)` to `⨅ y, f y` puts the tail of `x`
-- in this bounded set, and adjoining finitely many initial terms preserves boundedness of
-- `Set.range x`.
/-- Corollary 6.27.1 (1): if a closed proper convex function has no recession direction, then any
sequence along which the function values converge to the infimum is bounded. -/
theorem isBounded_range_of_tendsto_infimum_of_no_recession_direction
    {f : E → WithBotTop 𝕜} {x : ℕ → E}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) (hf_closed : LowerSemicontinuous f)
    (hno_recession : ¬ ∃ y : E, f.RecedesInDirection 𝕜 y)
    (hx : Tendsto (fun n ↦ f (x n)) atTop (𝓝 (⨅ y : E, f y))) :
    IsBounded (Set.range x) := by
  obtain ⟨x0, hx0, hx0_dom⟩ :=
    exists_mem_minimumSet_dom_of_no_recession_direction
      hf_convex hf_proper hf_closed hno_recession
  have hx0_top : f x0 < ⊤ := mem_effectiveDomain.mp hx0_dom
  have hx0_bot : ⊥ < f x0 := hf_proper.bot_lt x0
  lift f x0 to 𝕜 using ⟨ne_of_lt hx0_top, ne_of_gt hx0_bot⟩ with m hm
  have hiInf_eq : (⨅ y : E, f y) = (m : WithBotTop 𝕜) := by
    have hx0_eq_iInf : f x0 = ⨅ y : E, f y :=
      le_antisymm (mem_minimumSet_iff_le_iInf.mp hx0) (iInf_le f x0)
    simpa [hm] using hx0_eq_iInf.symm
  let S : Set E := f ⁻¹' Set.Iic (m + 1)
  have hS_bounded : IsBounded S := by
    refine isBounded_sublevelSet_of_no_recession_direction
      hf_convex hf_proper hf_closed hno_recession ?_
    refine ⟨x0, ?_⟩
    calc
      f x0 = (m : WithBotTop 𝕜) := hm.symm
      _ ≤ ((m + 1 : 𝕜) : WithBotTop 𝕜) :=
        WithBotTop.coe_le_coe.mpr (le_add_of_nonneg_right zero_le_one)
  have htail : ∀ᶠ n in atTop, x n ∈ S := by
    have hlt : (⨅ y : E, f y) < ((m + 1 : 𝕜) : WithBotTop 𝕜) := by
      rw [hiInf_eq]
      exact WithBotTop.coe_lt_coe.mpr (lt_add_of_pos_right m zero_lt_one)
    simpa [S] using hx (Iic_mem_nhds hlt)
  rcases Filter.eventually_atTop.1 htail with ⟨N, hN⟩
  have hinitial : IsBounded (x '' Set.Iic N) :=
    (Set.finite_Iic N).image x |>.isBounded
  refine (hinitial.union hS_bounded).subset ?_
  rintro y ⟨n, rfl⟩
  by_cases hn : n ≤ N
  · exact Or.inl ⟨n, hn, rfl⟩
  · exact Or.inr <| hN n (Nat.le_of_not_ge hn)

end

section

variable {E : Type u} [TopologicalSpace E]
variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜]
variable [DenselyOrdered 𝕜] [NoBotOrder 𝕜] [NoTopOrder 𝕜] [Nonempty 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]

-- Proof sketch: choose a finite threshold `a` strictly between `⨅ y, f y` and `f x₀`. Convergence
-- of `f ∘ x` to the infimum makes the map eventually stay in the closed sublevel set
-- `f ⁻¹' Set.Iic a`, and lower semicontinuity makes that set closed. A cluster point must
-- therefore belong to that sublevel set, contradicting `a < f x₀`.
/-- Corollary 6.27.1 (2): every cluster point (along any filter) of points whose function values
converge to the infimum belongs to the minimum set. For the textbook
closed-proper-convex hypothesis, this clause uses only lower semicontinuity, so it is stated on
that weaker canonical owner. -/
theorem mapClusterPt_mem_minimumSet_of_tendsto_infimum
    {ι : Type*} {l : Filter ι} {f : E → WithBotTop 𝕜} {x : ι → E} {x0 : E}
    (hf : LowerSemicontinuous f)
    (hx : Tendsto (fun i ↦ f (x i)) l (𝓝 (⨅ y : E, f y)))
    (hx0 : MapClusterPt x0 l x) :
    x0 ∈ minimumSet f := by
  rw [mem_minimumSet_iff_le_iInf]
  by_contra hx0_not_mem
  obtain ⟨a, ha_left, ha_right⟩ :=
    WithBotTop.exists_between_coe_of_lt (lt_of_not_ge hx0_not_mem)
  have hmem : ∀ᶠ i in l, x i ∈ f ⁻¹' Set.Iic a := by
    exact hx (Iic_mem_nhds ha_left)
  have hx0_mem : x0 ∈ f ⁻¹' Set.Iic a :=
    (hf.isClosed_preimage a).mem_of_mapClusterPt hx0 hmem
  exact (not_le.mpr ha_right) hx0_mem

end

/-! ### Definition_6_27_1 (from Chap06) -/
open Function

/-!
Source/core/bridge triage:
- `source-facing`: despite the filename, this item is the Section 27 summary theorem on minima of
  a closed proper convex function, already split upstream into the chapter-local atomic clause
  family in `Theorem_6_27_1.lean`.
- `core/canonical`: the owner abstraction for this recap is that local source-facing theorem
  family itself, together with the standing hypothesis package `IsClosedProperConvex`.
- `bridge/view`: the earlier Chapter 3 support-function, recession-function, and effective-domain
  theorems are proof ingredients for those local Section 27 clauses, not the right main public
  recall surface for this item.

Domain-style sampling used here:
- `infimum_eq_neg_convexConjugate_zero`;
- `minimumSet_eq_subdifferentialAt_convexConjugate_zero`;
- the clause-(f) polar-cone bridge for recession cones of nonempty sublevel sets;
- `no_recessionDirections_imp_zero_mem_riDom_convexConjugate`;
- `supportFunction_sublevelSet_eq_closure_sublinearHull_convexConjugate_add`.

Primitive data vs derived API:
- primitive data: none; this file introduces no new construction;
- derived API: the full source-facing Section 27 clause family already exposed upstream.

Layer target: `source-facing`, recall-shaped. This file should recall the canonical local theorem
family directly rather than a proper subset of lower-level Chapter 3 bridge declarations.
Clause `(a)` is recalled at the pairing-generic `E`/`Y` dual-side `WithTopBot 𝕜` layer,
while clauses `(b)`–`(i)`
stay at the canonical codomain `WithTopBot ℝ` inherited from Section 27, with intrinsic-topology
surfaces (`riDom`, `intrinsicClosure`) preferred whenever they are equivalent or canonical
consequences of the ambient statements. Ambient `interior` bridges remain available upstream in
`Theorem_6_27_1.lean`, but this recap keeps the intrinsic-primary theorem surface.
-/

/- Definition 6.27.1 / Theorem 27.1: the standing hypothesis package is the existing owner
`IsClosedProperConvex`. -/
recall IsClosedProperConvex

/- Clause (a): the infimum of `f` is `-f⋆(0)` at the dual-side origin. -/
recall infimum_eq_neg_convexConjugate_zero

/- Clause (a), bounded-below reformulation: `f` is bounded below exactly when the dual-side
origin belongs to `dom(f⋆)`. -/
recall boundedBelow_iff_zero_mem_effectiveDomain_convexConjugate

/- Clause (b): the minimum set of `f` is the subdifferential of `f⋆` at the origin. -/
recall minimumSet_eq_subdifferentialAt_convexConjugate_zero

/- Clause (b), attainment reformulation: `f` attains its infimum exactly when `f⋆` is
subdifferentiable at `0`. -/
recall minimumSet_nonempty_iff_subdifferentialAt_convexConjugate_zero_nonempty

/- Clause (b), relative-interior sufficient condition: `0 ∈ riDom(f⋆)` implies nonempty minimum
set. -/
recall zero_mem_riDom_convexConjugate_imp_minimumSet_nonempty

/- Clause (b), relative-interior characterization: `0 ∈ riDom(f⋆)` exactly when recession
directions of `f` are constancy directions. -/
recall zero_mem_riDom_convexConjugate_iff_recessionDirections_are_constancyDirections

/- Clause (c): the finite unattained-infimum case is equivalent to finite `f⋆(0)` together with a
direction of derivative `-∞` for `f⋆` at `0`. -/
recall finiteInfimum_unattained_iff_convexConjugate_zero_finite_and_exists_bot_directionalDerivative

/- Clause (d), intrinsic-primary form: bounded attainment forces `0 ∈ riDom(f⋆)`. -/
recall minimumSet_nonempty_bounded_imp_zero_mem_riDom_convexConjugate

/- Clause `(d')`, intrinsic-primary no-recession consequence: no recession direction implies
`0 ∈ riDom(f⋆)`. -/
recall no_recessionDirections_imp_zero_mem_riDom_convexConjugate

/- Clause (e), pairing-primary form: for any candidate minimizer `x`, the minimum set is the
singleton `{x}` exactly when the subdifferential of `f⋆` at `0` is `{x}`. -/
recall minimumSet_eq_singleton_iff_subdifferentialAt_convexConjugate_zero_eq_singleton

/- Clause (e), Euclidean bridge: in finite-dimensional real inner-product spaces, the singleton
minimum-set criterion is equivalent to differentiability of `f⋆` at `0`, with minimizer equal to
the gradient. -/
recall minimumSet_eq_singleton_iff_differentiableAt_convexConjugate_zero

/- Clause (f): any two nonempty real sublevel sets of `f` have the same recession cone, namely
the recession cone of `f`. -/
recall recessionCone_sublevelSet_eq_recessionCone_sublevelSet

/- Clause (f), polar-cone identification: every nonempty real sublevel set of `f` has recession
cone equal to both `Function.recessionCone (f0⁺)` and the polar of the cone generated by
`dom(f⋆)`. -/
recall recessionCone_sublevelSet_eq_recessionCone_and_polarCone_cone_dom_convexConjugate

/- Clause (g): for every real `α`, the support function of the `α`-sublevel set of `f` is the
closure of the generated positively homogeneous convex function of `f⋆ + α`. -/
recall supportFunction_sublevelSet_eq_closure_sublinearHull_convexConjugate_add

/- Clause (g), minimum-set specialization: when `f` is bounded below, the support function of the
minimum set is the closure of the directional-derivative profile of `f⋆` at `0`. -/
recall supportFunction_minimumSet_eq_closure_directionalDerivativeAt_convexConjugate_zero

/- Clause (h): if `inf f` is finite, the support functions of the sublevel sets
`{x | f x ≤ inf f + ε}` converge as `ε ↓ 0` to the directional derivative of `f⋆` at `0`. -/
recall tendsto_supportFunction_sublevelSet_to_directionalDerivativeAt_convexConjugate_zero

/- Clause (i), intrinsic-closure form: `0 ∈ intrinsicClosure ℝ (dom(f⋆))` exactly when the
recession function of `f` is nonnegative in every direction. -/
recall zero_mem_intrinsicClosure_effectiveDomain_convexConjugate_iff_nonneg_recessionFunction

/- Clause (i), intrinsic-closure negation form: `0 ∉ intrinsicClosure ℝ (dom(f⋆))` exactly when
`f` admits a strict descent direction with uniform positive linear rate. -/
recall
  zero_not_mem_intrinsicClosure_effectiveDomain_convexConjugate_iff_exists_strict_descent_direction

/-! ### Proposition_6_27_1 (from Chap06) -/
/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.27.1 says that for a convex function
  `f : ℝ^n → (-∞, +∞]`, each real closed sublevel set `{x | f x ≤ α}` is convex.
- `core/canonical`: the project owner theorem for this statement is
  `Function.IsConvex.convex_le`, already stated at the natural abstraction level of a convex
  `WithBotTop α`-valued function on a module.
- `bridge/view`: the textbook `ℝ^n` statement is the real finite-dimensional specialization of
  that owner theorem; no extra local wrapper or renamed specialization is mathematically needed.

Domain-style sampling used here:
- `Function.IsConvex` from `Chap01.Theorem_4_2`;
- `Function.IsConvex.convex_le` from `Chap01.Theorem_4_6`;
- `Function.IsConvex.convex_lt` from `Chap01.Theorem_4_6`;
- `Function.IsConvex.quasiconvexOn` from `Chap01.Theorem_4_6`.

Primitive data vs derived API:
- primitive input: a convex function in the owner sense `Function.IsConvex`;
- derived conclusion: convexity of its closed sublevel set at a chosen level.

Layer target: `core/canonical`. This item is a direct reuse of the existing owner theorem rather
than a new declaration.
-/

/- Proposition 6.27.1: for a convex function, every closed sublevel set `{x | f x ≤ α}` is
convex. This is exactly the canonical owner theorem `Function.IsConvex.convex_le`, specialized in
the book to `f : ℝ^n → (-∞, +∞]` and `α : ℝ`. -/
recall Function.IsConvex.convex_le

/-! ### Theorem_6_27_1 (from Chap06) -/
noncomputable section

open Bornology
open Filter
open Function
open scoped Gradient PolarCone RealInnerProductSpace Rockafellar

universe u v
local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

section

variable {𝕜 : Type v} [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsOrderedAddMonoid 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]
variable {Y : Type u} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing E Y 𝕜]
variable {f : E → WithTopBot 𝕜}

/- Theorem 6.27.1: the summary theorem on minima of a closed proper convex function is split into
atomic clause-level declarations below. Clauses `(1)` and `(2)` are the `y = 0` specialization of
the chapter conjugate formula, so their public surface belongs to the weaker pairing-valued
`WithTopBot` layer rather than to the later closed/proper/convex Euclidean specialization. -/

-- Proof sketch: this is the origin specialization of the Fenchel conjugate infimum formula
-- `convexConjugate_eq_neg_iInf_sub_pairing`.
/-- Theorem 6.27.1 (1), clause (a): the infimum of `f` is the negative of the value of its
Fenchel conjugate at the dual-side origin. -/
theorem infimum_eq_neg_convexConjugate_zero
    :
    (⨅ x : E, f x) = -(f⋆ (0 : Y)) := sorry

-- Proof sketch: combine the infimum formula from clause `(a)` with the defining description
-- `0 ∈ dom(f⋆) ↔ f⋆ 0 < ⊤`, then rewrite a real lower bound on `f` as finiteness of `f⋆ 0`.
/-- Theorem 6.27.1 (2), clause (a): `f` is bounded below exactly when the dual-side origin
belongs to the effective domain of its conjugate. -/
theorem boundedBelow_iff_zero_mem_effectiveDomain_convexConjugate
    :
    (∃ a : 𝕜, ∀ x : E, (a : WithTopBot 𝕜) ≤ f x) ↔
      (0 : Y) ∈ dom(f⋆) := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Y : Type u} [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [HasLinearPairing E Y ℝ] [HasPairing Y E ℝ]
variable {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f)

-- Proof sketch: apply the Fenchel-Young subgradient equivalence at the dual base point `0`; the
-- zero-subgradient criterion for a minimum is exactly `argmin(f)`-membership.
/-- Theorem 6.27.1 (3), clause (b): `argmin(f)` is the pairing-level subdifferential
of `f⋆` at the origin. -/
theorem minimumSet_eq_subdifferentialAt_convexConjugate_zero
    :
    argmin(f) = (∂[E]f⋆((0 : Y))) := sorry

-- Proof sketch: rewrite attainment of the infimum as nonemptiness of `argmin(f)`, then use the
-- set identity from the previous clause.
/-- Theorem 6.27.1 (4), clause (b): the infimum of `f` is attained exactly when `f⋆` is
subdifferentiable at the origin. -/
theorem minimumSet_nonempty_iff_subdifferentialAt_convexConjugate_zero_nonempty
    :
    (argmin(f)).Nonempty ↔
      (∂[E]f⋆((0 : Y))).Nonempty := sorry

-- Proof sketch: this is the singleton refinement of the set identity in clause `(3)`, kept on the
-- pairing-level subdifferential owner without any inner-product bridge.
/-- Clause `(e)`, pairing-primary form: `argmin(f)` is a singleton exactly when the
subdifferential of `f⋆` at the origin is that singleton. -/
theorem minimumSet_eq_singleton_iff_subdifferentialAt_convexConjugate_zero_eq_singleton
    (x : E) :
    argmin(f) = {x} ↔
      (∂[E]f⋆((0 : Y))) = {x} := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [FiniteDimensional ℝ E]
variable [HasLinearPairing E Y ℝ] [HasPairing Y E ℝ]
variable {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f)

-- Proof sketch: specialize the Chapter 13 relative-interior criterion for `dom(f⋆)` to `x⋆ = 0`
-- and translate the positivity condition into existence of a minimizer.
/-- Theorem 6.27.1 (5), clause (b): if the origin lies in the relative interior of `dom(f⋆)`,
then `argmin(f)` is nonempty. -/
theorem zero_mem_riDom_convexConjugate_imp_minimumSet_nonempty
    (h0 : (0 : Y) ∈ riDom(f⋆)) :
    (argmin(f)).Nonempty := sorry

-- Proof sketch: combine the relative-interior characterization at the origin with the recession
-- direction owner from Definition 6.27.4 and identify the zero-value directions with the
-- constancy directions of `f`.
/-- Theorem 6.27.1 (6), clause (b): the origin lies in `ri(dom(f⋆))` exactly when every recession
direction of `f` lies in the function lineality space `lineal f`. -/
theorem zero_mem_riDom_convexConjugate_iff_recessionDirections_are_constancyDirections
    :
    (0 : Y) ∈ riDom(f⋆) ↔
      ∀ y : E, f.RecedesInDirection ℝ y → y ∈ lineal f := sorry

-- Proof sketch: finite but unattained infimum is equivalent to finite conjugate value at `0`
-- together with failure of subdifferential nonemptiness there; Theorem 23.2 translates that
-- failure into a direction where the directional derivative drops to `⊥ = -∞`.
/-- Theorem 6.27.1 (7), clause (c): the infimum of `f` is finite and unattained exactly when
`f⋆ 0` is finite and the directional derivative of `f⋆` at `0` is `-∞` in some direction. -/
theorem
    finiteInfimum_unattained_iff_convexConjugate_zero_finite_and_exists_bot_directionalDerivative
    :
    (⊥ < (⨅ x : E, f x) ∧ (⨅ x : E, f x) < ⊤ ∧ argmin(f) = ∅) ↔
      (f⋆ (0 : Y) < ⊤ ∧
        ∃ y : Y, directionalDerivativeAt (f⋆) (0 : Y) y = ⊥) :=
  sorry

-- Proof sketch: bounded attainment implies the ambient-interior criterion in clause `(d')`,
-- and ambient interior always lies in intrinsic interior.
/-- Theorem 6.27.1 (8), clause (d), intrinsic-primary form: if `argmin(f)` is
nonempty and bounded, then the origin belongs to `riDom(f⋆)`. -/
theorem minimumSet_nonempty_bounded_imp_zero_mem_riDom_convexConjugate
    (hmin : (argmin(f)).Nonempty ∧ IsBounded (argmin(f))) :
    (0 : Y) ∈ riDom(f⋆) := sorry

-- Proof sketch: combine the `argmin(f)`/subdifferential identification with the Chapter 14
-- interior-domain boundedness criterion and the Section 27 minimum-set existence theorem.
/-- Clause `(d')`, ambient strengthening used downstream: `argmin(f)` is nonempty and
bounded exactly when the origin lies in the ambient interior of `dom(f⋆)`. -/
theorem minimumSet_nonempty_bounded_iff_zero_mem_interior_effectiveDomain_convexConjugate
    :
    (argmin(f)).Nonempty ∧ IsBounded (argmin(f)) ↔
      (0 : Y) ∈ interior dom(f⋆) := sorry

-- Proof sketch: use the ambient interior-domain characterization of bounded sublevel sets
-- together with the source-facing recession-direction owner from Definition 6.27.4.
/-- Clause `(d')`, ambient no-recession reformulation: `0 ∈ int(dom(f⋆))` exactly when `f`
has no direction of recession. -/
theorem zero_mem_interior_effectiveDomain_convexConjugate_iff_no_recessionDirections
    :
    (0 : Y) ∈ interior dom(f⋆) ↔
      ¬ ∃ y : E, f.RecedesInDirection ℝ y := sorry

-- Proof sketch: first move from the no-recession condition to ambient interior via the previous
-- theorem, then pass to relative interior through `interior_subset_intrinsicInterior`.
/-- Clause `(d')`, intrinsic-primary consequence: if `f` has no recession direction, then the
dual-side origin belongs to `riDom(f⋆)`. -/
theorem no_recessionDirections_imp_zero_mem_riDom_convexConjugate
    (hno : ¬ ∃ y : E, f.RecedesInDirection ℝ y) :
    (0 : Y) ∈ riDom(f⋆) := by
  have h0int : (0 : Y) ∈ interior dom(f⋆) :=
    (zero_mem_interior_effectiveDomain_convexConjugate_iff_no_recessionDirections
      (f := f)).2 hno
  exact interior_subset_intrinsicInterior (𝕜 := ℝ) h0int

-- Proof sketch: Theorem 8.7 identifies the recession cone of each nonempty real sublevel set
-- with the common owner `recessionCone (f0⁺)`, so any two nonempty real sublevel sets
-- have the same recession cone.
/-- Theorem 6.27.1 (11), clause (f): any two nonempty real sublevel sets of `f` have the same
recession cone, namely the recession cone of `f`. -/
theorem recessionCone_sublevelSet_eq_recessionCone_sublevelSet
    {α β : ℝ}
    (hα_nonempty : {x : E | f x ≤ (α : WithTopBot ℝ)}.Nonempty)
    (hβ_nonempty : {x : E | f x ≤ (β : WithTopBot ℝ)}.Nonempty) :
    0⁺[ℝ] {x : E | f x ≤ (α : WithTopBot ℝ)} =
      0⁺[ℝ] {x : E | f x ≤ (β : WithTopBot ℝ)} := sorry

-- Proof sketch: combine the common-cone identification from Theorem 8.7 with the Chapter 14 owner
-- theorem for the polar of the generated cone of `dom(f⋆)`, then use biconjugacy to rewrite the
-- resulting recession cone of `(f⋆)⋆` back to the recession cone of `f`.
/-- Theorem 6.27.1 (12), clause (f): every nonempty real sublevel set of `f` has recession cone
equal to the recession cone of `f`, and this common cone is the polar of the convex cone
generated by `dom(f⋆)`. -/
theorem
    recessionCone_sublevelSet_eq_recessionCone_and_polarCone_cone_dom_convexConjugate
    [HasLinearPairing Y E ℝ]
    (α : ℝ)
    (hα_nonempty : {x : E | f x ≤ (α : WithTopBot ℝ)}.Nonempty) :
    0⁺[ℝ] {x : E | f x ≤ (α : WithTopBot ℝ)} = recessionCone (f₀⁺) ∧
      0⁺[ℝ] {x : E | f x ≤ (α : WithTopBot ℝ)} =
        ((cone[ℝ] dom(f⋆))ᵒ[ℝ] : Set E) := sorry

-- Proof sketch: shift the zero-sublevel support-function theorem from Chapter 13 by the level
-- parameter `α`, so that the `α`-sublevel set of `f` becomes the zero sublevel set of
-- `x ↦ f x - α`.
/-- Theorem 6.27.1 (13), clause (g): for each real `α`, the support function of the `α`-sublevel
set of `f` is the closure `cl(·)` of the positively homogeneous convex function generated by
`f⋆ + α`. -/
theorem supportFunction_sublevelSet_eq_closure_sublinearHull_convexConjugate_add
    (α : ℝ) :
    (δᵛ[WithTopBot ℝ](· | {x : E | f x ≤ (α : WithTopBot ℝ)})) =
      cl(sublinearHull fun xStar : Y ↦ f⋆ xStar + (α : WithTopBot ℝ)) :=
  sorry

-- Proof sketch: after normalizing by the infimum value, `argmin(f)` is the zero sublevel set
-- of the translated function, and the first part of clause `(h)` reduces its support function to
-- the closure of the directional-derivative profile of `f⋆` at the origin.
/-- Theorem 6.27.1 (14), clause (g): if `f` is bounded below, the support function of `argmin(f)`
is the closure `cl(·)` of the directional-derivative function of `f⋆` at the origin. -/
theorem supportFunction_minimumSet_eq_closure_directionalDerivativeAt_convexConjugate_zero
    (hboundedBelow : ∃ a : ℝ, ∀ x : E, (a : WithTopBot ℝ) ≤ f x) :
    (δᵛ[WithTopBot ℝ](· | argmin(f))) =
      cl(directionalDerivativeAt (f⋆) (0 : Y)) :=
  sorry

-- Proof sketch: rewrite the approaching level `α ↓ inf f` as the positive parameter
-- `ε ↓ 0` in the translated sublevel family `{x | f x ≤ inf f + ε}`, then apply the support
-- function formula from clause `(h)` and pass to the limit.
/-- Theorem 6.27.1 (15), clause (h): if the infimum of `f` is finite, then the support functions
of the sublevel sets `{x | f x ≤ inf f + ε}` converge as `ε ↓ 0` to the directional derivative of
`f⋆` at the origin. -/
theorem tendsto_supportFunction_sublevelSet_to_directionalDerivativeAt_convexConjugate_zero
    (hfiniteInf : (⊥ : WithTopBot ℝ) < (⨅ x : E, f x) ∧ (⨅ x : E, f x) < ⊤)
    (y : Y) :
    Tendsto
      (fun ε : ℝ ↦ δᵛ[WithTopBot ℝ](y | {x : E | f x ≤ (⨅ z : E, f z) + ε}))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (directionalDerivativeAt (f⋆) (0 : Y) y)) := sorry

-- Proof sketch: specialize the Chapter 13 closure criterion for `dom(f⋆)` to `x⋆ = 0`, where the
-- translated recession function is just the recession function of `f` itself.
/-- Theorem 6.27.1 (16), clause (i): the origin lies in the closure of `dom(f⋆)` exactly when the
recession function of `f` is nonnegative in every direction. -/
theorem zero_mem_closure_effectiveDomain_convexConjugate_iff_nonneg_recessionFunction
    :
    (0 : Y) ∈ closure (dom(f⋆)) ↔
      ∀ y : E, 0 ≤ recessionFunction f y := sorry

-- Proof sketch: negate the closure criterion from the previous clause and use the directional
-- recession owner to rewrite strict negativity of the recession function as a uniform affine
-- descent estimate along one nonzero ray direction.
/-- Theorem 6.27.1 (17), clause (i): the origin fails to belong to `cl(dom(f⋆))` exactly when
there is a nonzero direction along which `f` decreases at a uniform positive linear rate on every
forward ray from `dom(f)`. -/
theorem zero_not_mem_closure_effectiveDomain_convexConjugate_iff_exists_strict_descent_direction
    :
    (0 : Y) ∉ closure (dom(f⋆)) ↔
      ∃ y : E, y ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧
        ∀ t : ℝ, 0 ≤ t → ∀ x ∈ dom(f),
          f (x + t • y) ≤ f x - (t * ε : WithTopBot ℝ) := sorry

-- Proof sketch: in finite-dimensional real normed spaces, intrinsic closure equals ambient
-- closure, so clause `(i)` is unchanged when rewritten on `intrinsicClosure`.
/-- Clause `(i)`, intrinsic-topology form: the origin belongs to `intrinsicClosure ℝ (dom(f⋆))`
exactly when the recession function of `f` is nonnegative in every direction. -/
theorem zero_mem_intrinsicClosure_effectiveDomain_convexConjugate_iff_nonneg_recessionFunction
    [FiniteDimensional ℝ Y]
    :
    (0 : Y) ∈ intrinsicClosure ℝ (dom(f⋆)) ↔
      ∀ y : E, 0 ≤ recessionFunction f y := by
  simpa [intrinsicClosure_eq_closure (𝕜 := ℝ) (s := dom(f⋆))] using
    zero_mem_closure_effectiveDomain_convexConjugate_iff_nonneg_recessionFunction

-- Proof sketch: same intrinsic-closure rewrite as above, applied to the strict-descent
-- negation formulation.
/-- Clause `(i)`, intrinsic-topology negation form: the origin fails to belong to
`intrinsicClosure ℝ (dom(f⋆))` exactly when `f` has a strict uniform linear descent direction. -/
theorem
zero_not_mem_intrinsicClosure_effectiveDomain_convexConjugate_iff_exists_strict_descent_direction
    [FiniteDimensional ℝ Y]
    :
    (0 : Y) ∉ intrinsicClosure ℝ (dom(f⋆)) ↔
      ∃ y : E, y ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧
        ∀ t : ℝ, 0 ≤ t → ∀ x ∈ dom(f),
          f (x + t • y) ≤ f x - (t * ε : WithTopBot ℝ) := by
  simpa [intrinsicClosure_eq_closure (𝕜 := ℝ) (s := dom(f⋆))] using
    zero_not_mem_closure_effectiveDomain_convexConjugate_iff_exists_strict_descent_direction

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f)

-- Proof sketch: identify `argmin(f)` with `∂f⋆(0)`, then use the singleton-subdifferential
-- criterion supplied by differentiability of the real branch of `f⋆` at the origin.
/-- Theorem 6.27.1 (10), clause (e): `argmin(f)` is the singleton `{x}` exactly when
the real branch of `f⋆` is differentiable at the origin and `x` is its gradient there. -/
theorem minimumSet_eq_singleton_iff_differentiableAt_convexConjugate_zero
    (x : E) :
    argmin(f) = {x} ↔
      DifferentiableAt ℝ (f⋆).realBranch (0 : E) ∧
        x = ∇ (f⋆).realBranch (0 : E) := sorry

end

/-! ### Corollary_6_27_2 (from Chap06) -/
open Filter
open Function.RecedesInDirection
open scoped Topology

universe u
section

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E] [ProperSpace E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 6.27.2 says that if a convex proper lower-semicontinuous function
  has a unique
  minimizer `x`, then every sequence whose function values converge to the infimum actually
  converges to `x`.
- `core/canonical`: the chapter-local owner `minimumSet`, the primitive convex/proper/closed
  owners `Function.IsConvex`, `Function.IsProper`, `LowerSemicontinuous`, and the canonical
  convergence/cluster owners `Tendsto` and `MapClusterPt`.
- `bridge/view`: the uniqueness hypothesis is stated directly as `minimumSet f = {x}` rather than
  via a packaged argmin object or an existential uniqueness wrapper.

Domain-style sampling used here:
- the Chapter 6 minimum-set owner `minimumSet` from `Definition_6_27_3`;
- primitive owners `Function.IsConvex`, `Function.IsProper`, and `LowerSemicontinuous`;
- the source-facing recession-direction owner `Function.RecedesInDirection` from
  `Definition_6_27_4`;
- the no-recession boundedness bridge
  `isBounded_range_of_tendsto_infimum_of_no_recession_direction`;
- the cluster-point minimum-set bridge `mapClusterPt_mem_minimumSet_of_tendsto_infimum`.

Primitive data vs derived API:
- primitive inputs: the function `f`, its unique minimizer `x`, and a sequence `xSeq` along which
  `f (xSeq n)` tends to `⨅ y, f y`;
- derived API: the no-recession consequence of singleton minimality, boundedness of `xSeq`, and
  the cluster-point consequence that every subsequential limit belongs to `minimumSet f`.

Layer target: `source-facing`, stated directly on the canonical minimum-set owner and sequence
convergence owner rather than through a separate asymptotic-minimizer structure.
-/

-- Proof sketch: singleton minimality rules out nonzero recession directions (the ray from a
-- minimizer stays in `minimumSet f`, contradicting `minimumSet f = {x}`). Then Corollary 6.27.1
-- gives boundedness of the sequence. If the sequence did not converge to `x`, one could extract a
-- subsequence staying at distance at least `ε` from `x`; boundedness plus properness gives a
-- convergent sub-subsequence. Its limit is a cluster point of the original
-- sequence, hence belongs to `minimumSet f = {x}`, contradicting the uniform `ε`-separation.
/-- Corollary 6.27.2: if a convex proper lower-semicontinuous function has the singleton
minimum set `{x}`, then
every sequence whose function values converge to the infimum converges to `x`. -/
theorem tendsto_of_tendsto_infimum_of_minimumSet_eq_singleton
    {f : E → WithBotTop 𝕜} (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f) {x : E}
    (hminimum : minimumSet f = {x}) {xSeq : ℕ → E}
    (hxSeq : Tendsto (fun n ↦ f (xSeq n)) atTop (𝓝 (⨅ y : E, f y))) :
    Tendsto xSeq atTop (𝓝 x) := by
  have hx_min : x ∈ minimumSet f := by simp [hminimum]
  have hx_le : f x ≤ ⨅ y : E, f y := mem_minimumSet_iff_le_iInf.mp hx_min
  rcases hf_proper.nonempty_dom with ⟨y, hy_dom⟩
  have hx_top : f x < ⊤ := by
    exact lt_of_le_of_lt (le_trans hx_le (iInf_le f y)) (mem_effectiveDomain.mp hy_dom)
  have hx_dom : x ∈ dom(f) := mem_effectiveDomain.mpr hx_top
  have hno_recession : ¬ ∃ y : E, f.RecedesInDirection 𝕜 y := by
    rintro ⟨y, hy⟩
    have hxy_min : x + y ∈ minimumSet f := by
      rw [mem_minimumSet_iff_le_iInf]
      have h01 : (0 : 𝕜) ≤ 1 := zero_le_one
      simpa [one_smul] using le_trans (ray_le hy hx_dom h01) hx_le
    have hxy : x + y = x := by simpa [hminimum, one_smul] using hxy_min
    have hy_zero : y = 0 := by
      have hsub := congrArg (fun z ↦ z - x) hxy
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsub
    exact hy.ne_zero hy_zero
  have hbounded : Bornology.IsBounded (Set.range xSeq) :=
    isBounded_range_of_tendsto_infimum_of_no_recession_direction
      hf_convex hf_proper hf_closed hno_recession hxSeq
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra htail
  push Not at htail
  have hfar : ∃ᶠ n in atTop, ε ≤ dist (xSeq n) x := by
    exact frequently_atTop.2 htail
  rcases extraction_of_frequently_atTop hfar with ⟨φ, hφmono, hφfar⟩
  have hbounded_subseq : Bornology.IsBounded (Set.range (xSeq ∘ φ)) := by
    refine hbounded.subset ?_
    rintro y ⟨n, rfl⟩
    exact ⟨φ n, rfl⟩
  obtain ⟨a, -, ψ, hψmono, hconv⟩ :=
    tendsto_subseq_of_bounded hbounded_subseq (fun n ↦ Set.mem_range_self n)
  have hcluster_subsub : MapClusterPt a atTop (((xSeq ∘ φ) ∘ ψ)) :=
    (Filter.Tendsto.mapClusterPt hconv)
  have hcluster_sub : MapClusterPt a atTop (xSeq ∘ φ) :=
    hcluster_subsub.of_comp hψmono.tendsto_atTop
  have hcluster : MapClusterPt a atTop xSeq :=
    hcluster_sub.of_comp hφmono.tendsto_atTop
  have ha_min : a ∈ minimumSet f :=
    mapClusterPt_mem_minimumSet_of_tendsto_infimum hf_closed hxSeq hcluster
  have ha_eq : a = x := by simpa [hminimum] using ha_min
  have hclosed_far : IsClosed ({y : E | ε ≤ dist y x} : Set E) := by
    exact isClosed_le continuous_const (continuous_id.dist continuous_const)
  have ha_far : ε ≤ dist a x := by
    refine hclosed_far.mem_of_tendsto hconv ?_
    exact Filter.Eventually.of_forall fun n ↦ hφfar (ψ n)
  exact (not_le_of_gt hε) (by simpa [ha_eq] using ha_far)

end

/-! ### Definition_6_27_2 (from Chap06) -/
/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.27.2 introduces the infimum `inf f` of an extended-order-valued
  function as the greatest lower bound of its values.
- `core/canonical`: the primitive expression owner is the indexed infimum `⨅ x, f x`; equivalently,
  the infimum of the value set `sInf (Set.range f)`.
- `bridge/view`: the theorem `sInf_range` is the exact bridge from the source's set-of-values
  presentation to the indexed-infimum owner form already used elsewhere in the project.

Domain-style sampling used here:
- the indexed-infimum owner surface `⨅ x, f x`;
- `sInf (Set.range f)` and the mathlib bridge theorem `sInf_range`;
- chapter-facing specializations such as codomain `WithTopBot α` obtained by direct
  instantiation.

Primitive data vs derived API:
- primitive data: only the function `f : E → β`;
- primitive owner: the indexed infimum `⨅ x, f x`;
- derived API: the equivalent source-facing set formula `sInf (Set.range f)` and the
  greatest-lower-bound owner `IsGLB (Set.range f) (⨅ x, f x)`.

Layer target: `core/canonical`, recall-shaped. The source item adds no new mathematics beyond the
existing canonical infimum owner layer, so the faithful refinement is direct reuse of mathlib's
indexed infimum and `IsGLB` interfaces rather than a local `infimum` wrapper.
-/

universe u v

section Primitive

variable {E : Sort u} {β : Type v}
variable [InfSet β]

/- Definition 6.27.2: the infimum of a chapter-facing function is already the canonical
indexed-infimum expression `⨅ x : E, f x`. -/
recall iInf

/- The source's equivalent set-of-values formula `inf {f(x) | x ∈ E}` is already the canonical
bridge theorem `sInf_range`. -/
recall sInf_range

end Primitive

section OrderSemantics

variable {E : Sort u} {β : Type v}
variable [CompleteSemilatticeInf β]

/-- Source semantic owner for Definition 6.27.2: the indexed infimum of `f` is the greatest lower
bound of the value set `Set.range f`. -/
theorem isGLB_range_iInf (f : E → β) : IsGLB (Set.range f) (⨅ x, f x) := by
  simpa [sInf_range] using (isGLB_sInf (s := Set.range f))

/-- Every value of `f` is above the infimum. -/
theorem iInf_le_apply (f : E → β) (x : E) : (⨅ y, f y) ≤ f x :=
  (isGLB_range_iInf f).1 ⟨x, rfl⟩

/-- Any common lower bound of all values of `f` lies below the infimum. -/
theorem le_iInf_of_forall_le_range {f : E → β} {a : β}
    (ha : ∀ y ∈ Set.range f, a ≤ y) :
    a ≤ (⨅ y, f y) :=
  (isGLB_range_iInf f).2 ha

end OrderSemantics

/-! ### Proposition_6_27_2 (from Chap06) -/
universe u v

section

variable {E : Type u} {α : Type v}
variable [TopologicalSpace E] [LinearOrder α] [NoMinOrder α] [Nonempty α]

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.27.2 says that every finite-height sublevel set
  `{x | f x ≤ a}` is closed.
- `core/canonical`: the chapter owner theorem for that statement is
  `lowerSemicontinuous_iff_isClosed_sublevel`.
- `bridge/view`: the lower-level mathlib mechanism is
  `LowerSemicontinuous.isClosed_preimage`, while the Chapter 3 bundle
  `Function.IsClosedProperConvex` supplies lower semicontinuity only as a downstream bridge.

Domain-style sampling used here:
- `lowerSemicontinuous_iff_isClosed_sublevel` from `Chap02.Theorem_7_1`;
- `lowerSemicontinuous_iff_isClosed_preimage` from the same lower-semicontinuity owner layer;
- `LowerSemicontinuous.isClosed_preimage` from mathlib's semicontinuity API;
- `Function.IsClosedProperConvex.lowerSemicontinuous` from `Chap03.Text_12_3_6`.

Primitive data vs derived API:
- primitive data: a function `f : E → WithBotTop α` and the owner hypothesis
  `LowerSemicontinuous f`;
- derived API: closedness of the scalar sublevel sets `{x | f x ≤ a}`;
- this file keeps the proposition on the owner surface `LowerSemicontinuous` and derives it from
  the Chapter 2 characterization theorem, rather than recalling the stronger biconditional as the
  main entry.

Layer target: `source-facing`, with the main theorem stated as the forward-direction specialization
of the Chapter 2 owner theorem on the canonical owner namespace.
-/

namespace LowerSemicontinuous

/-- Proposition 6.27.2: every finite-height scalar sublevel set of a lower semicontinuous
function is closed. This is the forward-direction specialization of
`lowerSemicontinuous_iff_isClosed_sublevel`. -/
theorem isClosed_sublevel {f : E → WithBotTop α} (hf : LowerSemicontinuous f) (a : α) :
    IsClosed {x : E | f x ≤ a} :=
  (lowerSemicontinuous_iff_isClosed_sublevel_withBotTop.1 hf) a

end LowerSemicontinuous

end

/-! ### Theorem_6_27_2 (from Chap06) -/
universe u

open scoped Rockafellar

section Attainment

variable {E : Type u}
variable {𝕜 : Type*}
variable [Field 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]
variable {f : E → WithBotTop 𝕜}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.27.2 combines an attained finite infimum for a convex proper lower-
  semicontinuous function with no recession direction and a later metric proximity statement for
  sufficiently low sublevel sets. The attainment companion below already lives on the weaker
  finite-dimensional scalar-generic topological vector-space layer reused from Theorem 6.27.3,
  while the boundedness and distance clauses below use normed-space structure.
- `core/canonical`: the owner abstractions are the source-facing Chapter 6 minimum-set owner
  `minimumSet`, the recession-direction predicate `Function.RecedesInDirection`, the primitive
  owners `Function.IsConvex`, `Function.IsProper`, and `LowerSemicontinuous`, the unconstrained
  attainment owner
  `exists_mem_isMinOn_of_no_common_recession_direction`, the common-sublevel recession-cone owner
  `recessionCone_sublevelSet_eq_functionRecessionCone`, and the closed-convex boundedness owner
  `Convex.isBounded_iff_recessionCone_eq_singleton_zero`.
- `bridge/view`: the main public theorem is stated directly on the source-facing owner
  `minimumSet f`, while the attained-minimum and minimum-set geometry clauses are kept as separate
  companion theorems instead of being bundled into one long conjunction.

Domain-style sampling used here:
- `minimumSet` from `Definition_6_27_3`;
- `Function.RecedesInDirection` from `Definition_6_27_4`;
- primitive `Function.IsConvex` / `Function.IsProper` assumptions and `LowerSemicontinuous`;
- `exists_mem_isMinOn_of_no_common_recession_direction` from `Theorem_6_27_3`;
- `recessionCone_sublevelSet_eq_functionRecessionCone` from `Chap02/Theorem_8_7`;
- `Convex.isBounded_iff_recessionCone_eq_singleton_zero` from `Chap02/Theorem_8_4`.

Primitive data vs derived API:
- primitive inputs: the function `f : E → WithBotTop 𝕜`, convexity/properness/lower-
  semicontinuity assumptions, and the source-facing no-recession hypothesis
  `¬ ∃ y, f.RecedesInDirection 𝕜 y`;
- derived API in this file: the first clause is a source-facing bridge from the canonical owner
  `IsMinOn` to `minimumSet`, and it already lives on the weaker finite-dimensional scalar-generic
  topological vector-space layer of Theorem 6.27.3; the second clause is the corresponding
  boundedness bridge obtained by rewriting `minimumSet f` as the attained real sublevel set and
  applying the Chapter 8 recession owners in the normed finite-dimensional setting; the third
  clause is the genuinely new source-facing quantitative proximity statement.

Layer target: `source-facing`, reusing the existing minimum-set owner rather than replacing the
theorem by a packaged minimization structure or a purely `IsMinOn`-based wrapper.
-/

-- Proof sketch: specialize the canonical unconstrained-attainment theorem
-- `exists_mem_isMinOn_of_no_common_recession_direction` to `Set.univ` and convert the obtained
-- minimizer to the source-facing owner `minimumSet`. Properness supplies a finite point in
-- `dom(f)`, so the minimizer is finite as well in the canonical owner `dom(f)`.
/-- A convex proper lower-semicontinuous function with no recession direction on a finite-
dimensional topological vector space has a minimizer in the canonical finite-value owner
`dom(f)`. This attainment clause already lives on the same scalar-generic owner layer as the
upstream theorem. -/
theorem exists_mem_minimumSet_dom_of_no_recession_direction
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) (hf_closed : LowerSemicontinuous f)
    (hno_recession : ¬ ∃ y : E, f.RecedesInDirection 𝕜 y)
    : ∃ x ∈ minimumSet f, x ∈ dom(f) := by
  obtain ⟨x, -, hxmin⟩ :=
    exists_mem_isMinOn_of_no_common_recession_direction
      Set.univ_nonempty isClosed_univ convex_univ hf_convex hf_proper hf_closed
      (by
        rintro ⟨y, -, hy⟩
        exact hno_recession ⟨y, hy⟩)
  refine ⟨x, by simpa [minimumSet] using hxmin, ?_⟩
  exact hxmin.mem_dom_of_nonempty_dom hf_proper.nonempty_dom

end Attainment

section BoundedGeometry

open Bornology
open Filter

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {f : E → WithBotTop 𝕜}

omit [FiniteDimensional 𝕜 E] [OrderTopology 𝕜]
  [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)] in
private theorem functionRecessionCone_eq_singleton_zero_of_no_recession_direction
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hno_recession : ¬ ∃ y : E, f.RecedesInDirection 𝕜 y) :
    Function.recessionCone ((f)₀⁺) = ({0} : Set E) := by
  ext y
  constructor
  · intro hy
    by_cases hy0 : y = 0
    · simp [hy0]
    · exact False.elim <| hno_recession ⟨y,
        Function.RecedesInDirection.of_mem_recessionCone hf_convex hf_proper hy0 hy⟩
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    rw [Function.mem_recessionCone_iff, Function.recessionFunction_apply]
    refine sSup_le ?_
    rintro r ⟨u, hu, rfl⟩
    simpa using (WithBotTop.sub_self_le_zero : f u - f u ≤ (0 : WithBotTop 𝕜))

private theorem isBounded_sublevelSet_of_no_recession_direction
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) (hf_closed : LowerSemicontinuous f)
    (hno_recession : ¬ ∃ y : E, f.RecedesInDirection 𝕜 y)
    {a : 𝕜} (ha_nonempty : (f ⁻¹' Set.Iic a).Nonempty) :
    IsBounded (f ⁻¹' Set.Iic a) := by
  have hsublevel_recession :
      0⁺[𝕜] (f ⁻¹' Set.Iic a) = ({0} : Set E) := by
    calc
      0⁺[𝕜] (f ⁻¹' Set.Iic a) = Function.recessionCone ((f)₀⁺) := by
        simpa using
          hf_convex.recessionCone_sublevelSet_eq_functionRecessionCone
            hf_proper hf_closed a ha_nonempty
      _ = ({0} : Set E) :=
        functionRecessionCone_eq_singleton_zero_of_no_recession_direction
          hf_convex hf_proper hno_recession
  exact
    ((hf_convex.convex_le (a : WithBotTop 𝕜)).isBounded_iff_recessionCone_eq_singleton_zero
      ((lowerSemicontinuous_iff_isClosed_sublevel_withBotTop.1 hf_closed) a)
      ha_nonempty).mpr hsublevel_recession

-- Proof sketch: first obtain a minimizer `x` in `dom(f)`. Its value is a scalar level `a`, and
-- `minimumSet f` is exactly the sublevel set `{u | f u ≤ a}`. The Chapter 8 theorem
-- `recessionCone_sublevelSet_eq_functionRecessionCone` identifies the recession cone of that
-- nonempty sublevel set with the function recession cone. The no-recession hypothesis forces the
-- latter to be `{0}`, so Theorem 8.4 yields boundedness of `minimumSet f`.
/-- Under the no-recession hypothesis, the minimum set of a convex proper lower-semicontinuous
function is bounded. -/
theorem minimumSet_isBounded_of_no_recession_direction
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) (hf_closed : LowerSemicontinuous f)
    (hno_recession : ¬ ∃ y : E, f.RecedesInDirection 𝕜 y)
    : IsBounded (minimumSet f) := by
  obtain ⟨x, hx, hx_dom⟩ :=
    exists_mem_minimumSet_dom_of_no_recession_direction
      hf_convex hf_proper hf_closed hno_recession
  have hx_top : f x < ⊤ := mem_effectiveDomain.mp hx_dom
  have hx_bot : ⊥ < f x := hf_proper.bot_lt x
  lift f x to 𝕜 using ⟨ne_of_lt hx_top, ne_of_gt hx_bot⟩ with a ha
  have hx_eq_iInf : f x = ⨅ y : E, f y := by
    exact le_antisymm (mem_minimumSet_iff_le_iInf.mp hx) (iInf_le f x)
  have hminimumSet : minimumSet f = f ⁻¹' Set.Iic a := by
    ext u
    rw [Set.mem_preimage, Set.mem_Iic, mem_minimumSet_iff_le_iInf, ← hx_eq_iInf]
    simp [ha]
  have hsublevel_nonempty : (f ⁻¹' Set.Iic a).Nonempty := by
    refine ⟨x, ?_⟩
    rw [Set.mem_preimage, Set.mem_Iic]
    simp [ha]
  rw [hminimumSet]
  exact isBounded_sublevelSet_of_no_recession_direction
    hf_convex hf_proper hf_closed hno_recession hsublevel_nonempty

end BoundedGeometry

section MetricGeometry

open Bornology
open Filter

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [Archimedean 𝕜] [LocallyCompactSpace 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {f : E → WithBotTop 𝕜}

-- Proof sketch: argue by contradiction with the closed bounded sets obtained by removing the
-- `ε`-neighborhood of `minimumSet f` from successively lower sublevel sets
-- `{x | f x ≤ inf f + δ}`. If every such truncated set were nonempty, compactness in finite
-- dimension would produce a point outside the `ε`-neighborhood but still in `minimumSet f`, a
-- contradiction.
/-- Theorem 6.27.2: for a convex proper lower-semicontinuous function with no recession direction,
every
sufficiently low sublevel point lies within any prescribed distance of the minimum set. -/
theorem sublevel_exists_mem_minimumSet_dist_lt_of_no_recession_direction
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) (hf_closed : LowerSemicontinuous f)
    (hno_recession : ¬ ∃ y : E, f.RecedesInDirection 𝕜 y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : 𝕜, 0 < δ ∧
      ∀ x : E, f x ≤ (⨅ y : E, f y) + δ → ∃ z ∈ minimumSet f, dist x z < ε := by
  by_contra h
  push Not at h
  let δ : ℕ → 𝕜 := fun n ↦ ((n : 𝕜) + 1)⁻¹
  let x : ℕ → E := fun n ↦
    Classical.choose (h (δ n) (by
      dsimp [δ]
      positivity))
  have hx_sub : ∀ n, f (x n) ≤ (⨅ y : E, f y) + δ n := by
    intro n
    exact (Classical.choose_spec (h (δ n) (by
      dsimp [δ]
      positivity))).1
  have hx_far : ∀ n z, z ∈ minimumSet f → ε ≤ dist (x n) z := by
    intro n z hz
    exact (Classical.choose_spec (h (δ n) (by
      dsimp [δ]
      positivity))).2 z hz
  obtain ⟨x0, hx0, hx0_dom⟩ :=
    exists_mem_minimumSet_dom_of_no_recession_direction
      hf_convex hf_proper hf_closed hno_recession
  have hx0_top : f x0 < ⊤ := mem_effectiveDomain.mp hx0_dom
  have hx0_bot : ⊥ < f x0 := hf_proper.bot_lt x0
  lift f x0 to 𝕜 using ⟨ne_of_lt hx0_top, ne_of_gt hx0_bot⟩ with m hm
  have hx0_eq_iInf : f x0 = ⨅ y : E, f y := by
    exact le_antisymm (mem_minimumSet_iff_le_iInf.mp hx0) (iInf_le f x0)
  have hiInf_eq : (⨅ y : E, f y) = (m : WithBotTop 𝕜) := by
    simpa [hm] using hx0_eq_iInf.symm
  let S : Set E := {u : E | f u ≤ ((m + 1 : 𝕜) : WithBotTop 𝕜)}
  have hS_bdd : IsBounded S := by
    refine isBounded_sublevelSet_of_no_recession_direction
      hf_convex hf_proper hf_closed hno_recession ?_
    refine ⟨x0, ?_⟩
    calc
      f x0 = (m : WithBotTop 𝕜) := hm.symm
      _ ≤ ((m + 1 : 𝕜) : WithBotTop 𝕜) :=
        WithBotTop.coe_le_coe.mpr (le_add_of_nonneg_right zero_le_one)
  have hx_memS : ∀ n, x n ∈ S := by
    intro n
    change f (x n) ≤ ((m + 1 : 𝕜) : WithBotTop 𝕜)
    have hx' :
        f (x n) ≤ ((m + δ n : 𝕜) : WithBotTop 𝕜) := by
      simpa [hiInf_eq] using hx_sub n
    refine le_trans hx' ?_
    have hdiv_le : δ n ≤ 1 := by
      have hle : (1 : 𝕜) ≤ (n : 𝕜) + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      simpa [δ, one_div] using
        (one_div_le_one_div_of_le (show (0 : 𝕜) < 1 by positivity) hle)
    simpa [add_comm, add_left_comm, add_assoc] using
      (WithBotTop.coe_le_coe.mpr (add_le_add_right hdiv_le m))
  letI : ProperSpace E := FiniteDimensional.proper 𝕜 E
  obtain ⟨a, haS_closure, φ, hφ, hconv⟩ := tendsto_subseq_of_bounded hS_bdd hx_memS
  have hS_closed : IsClosed S := by
    simpa [S] using (lowerSemicontinuous_iff_isClosed_sublevel_withBotTop.1 hf_closed) (m + 1)
  have haS : a ∈ S := by
    rwa [hS_closed.closure_eq] at haS_closure
  let T : Set E := (Metric.thickening ε (minimumSet f))ᶜ
  have hT_closed : IsClosed T := Metric.isOpen_thickening.isClosed_compl
  have hxφ_memT : ∀ n, x (φ n) ∈ T := by
    intro n
    have hx_not_thick : x (φ n) ∉ Metric.thickening ε (minimumSet f) := by
      rw [Metric.mem_thickening_iff]
      rintro ⟨z, hz, hzdist⟩
      exact (not_lt_of_ge (hx_far (φ n) z hz)) hzdist
    simpa [T] using hx_not_thick
  have haT : a ∈ T :=
    hT_closed.mem_of_tendsto hconv (Filter.Eventually.of_forall hxφ_memT)
  have haS' : f a ≤ ((m + 1 : 𝕜) : WithBotTop 𝕜) := by
    simpa [S] using haS
  have ha_top_f : f a < ⊤ :=
    lt_of_le_of_lt haS' (WithBotTop.coe_lt_top (m + 1))
  have ha_bot_f : ⊥ < f a := hf_proper.bot_lt a
  lift f a to 𝕜 using ⟨ne_of_lt ha_top_f, ne_of_gt ha_bot_f⟩ with r hr
  have ha_sublevel (k : ℕ) :
      ((r : 𝕜) : WithBotTop 𝕜) ≤ ((m + δ k : 𝕜) : WithBotTop 𝕜) := by
    let Sk : Set E := {u : E | f u ≤ ((m + δ k : 𝕜) : WithBotTop 𝕜)}
    have hSk_closed : IsClosed Sk := by
      simpa [Sk] using
        (lowerSemicontinuous_iff_isClosed_sublevel_withBotTop.1 hf_closed) (m + δ k)
    have hSk_eventually : ∀ᶠ n in atTop, x (φ n) ∈ Sk := by
      refine Filter.eventually_atTop.2 ⟨k, ?_⟩
      intro n hn
      change f (x (φ n)) ≤
        ((m + δ k : 𝕜) : WithBotTop 𝕜)
      have hx' :
          f (x (φ n)) ≤
            ((m + δ (φ n) : 𝕜) : WithBotTop 𝕜) := by
        simpa [hiInf_eq] using hx_sub (φ n)
      refine le_trans hx' ?_
      have hdiv_le : δ (φ n) ≤ δ k := by
        have hle : (k : 𝕜) + 1 ≤ (φ n : 𝕜) + 1 := by
          exact_mod_cast Nat.succ_le_succ (le_trans hn (hφ.id_le n))
        simpa [δ, one_div] using
          (one_div_le_one_div_of_le (show (0 : 𝕜) < (k : 𝕜) + 1 by positivity) hle)
      simpa [add_comm, add_left_comm, add_assoc] using
        (WithBotTop.coe_le_coe.mpr (add_le_add_right hdiv_le m))
    have : a ∈ Sk := hSk_closed.mem_of_tendsto hconv hSk_eventually
    simpa [Sk, hr] using this
  have haS' : ((r : 𝕜) : WithBotTop 𝕜) ≤ ((m + 1 : 𝕜) : WithBotTop 𝕜) := by
    simpa [S, hr] using haS
  have ha_top : ((r : 𝕜) : WithBotTop 𝕜) < ⊤ :=
    lt_of_le_of_lt haS' (WithBotTop.coe_lt_top (m + 1))
  have hr_le : r ≤ m := by
    rw [le_iff_forall_pos_lt_add]
    intro η hη
    rcases exists_nat_one_div_lt hη with ⟨k, hk⟩
    have hak : ((r : 𝕜) : WithBotTop 𝕜) ≤
        ((m + δ k : 𝕜) : WithBotTop 𝕜) := ha_sublevel k
    have hr_le' : r ≤ m + (1 : 𝕜) / ((k : 𝕜) + 1) := by
      simpa [δ] using WithBotTop.coe_le_coe.mp hak
    nlinarith
  have ha_minimum : a ∈ minimumSet f := by
    rw [mem_minimumSet_iff_le_iInf]
    simpa [hiInf_eq, hr] using (WithBotTop.coe_le_coe.mpr hr_le :
      ((r : 𝕜) : WithBotTop 𝕜) ≤ (m : WithBotTop 𝕜))
  have ha_thick : a ∈ Metric.thickening ε (minimumSet f) := by
    rw [Metric.mem_thickening_iff]
    exact ⟨a, ha_minimum, by simpa using hε⟩
  have ha_not_thick : a ∉ Metric.thickening ε (minimumSet f) := by
    simpa [T] using haT
  exact ha_not_thick ha_thick

end MetricGeometry

/-! ### Corollary_6_27_3 (from Chap06) -/
noncomputable section

universe u

open scoped Rockafellar

section RecessionDirectionBridge

variable {𝕜 : Type*}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [AddRightMono 𝕜]
variable {E : Type u}
variable [AddCommGroup E] [Module 𝕜 E]

-- Proof sketch: `Set.RecedesInDirection` is by definition nonzero membership in `0⁺[𝕜]C`, while
-- `Function.RecedesInDirection` is equivalent (under convex/proper hypotheses) to nonzero
-- membership in `((h)₀⁺).recessionCone`.
/-- Bridge equivalence between the cone-owner common-direction hypothesis and the
source-facing common-recession-direction hypothesis. This bridge lives on the weaker
ordered-module layer and does not require any finite-dimensional topological assumptions. -/
theorem common_recessionCone_lineal_iff_common_recessionDirections_lineal
    {C : Set E} {h : E → WithBotTop 𝕜}
    (hh_convex : h.IsConvex 𝕜) (hh_proper : h.IsProper) :
    (∀ ⦃y : E⦄, y ∈ 0⁺[𝕜]C → y ∈ ((h)₀⁺).recessionCone → y ≠ 0 →
      y ∈ Function.lineal h) ↔
      (∀ ⦃y : E⦄, C.RecedesInDirection 𝕜 y → h.RecedesInDirection 𝕜 y →
        y ∈ Function.lineal h) := by
  constructor
  · intro hlineal y hyC hyh
    have hy_mem : y ∈ ((h)₀⁺).recessionCone :=
      Function.RecedesInDirection.mem_recessionCone hyh hh_convex hh_proper
    exact hlineal hyC.2 hy_mem hyC.1
  · intro hlineal y hyC hyh hy_ne
    have hyC' : C.RecedesInDirection 𝕜 y := ⟨hy_ne, hyC⟩
    have hyh' : h.RecedesInDirection 𝕜 y :=
      Function.RecedesInDirection.of_mem_recessionCone hh_convex hh_proper hy_ne hyh
    exact hlineal hyC' hyh'

end RecessionDirectionBridge

section

variable {𝕜 : Type*}
variable [Field 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
variable [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: the corollary says that a closed proper convex function attains its infimum on
  any polyhedral convex set where it is bounded below, provided every recession direction of the
  function is a direction along which the function is affine.
- `core/canonical`: the relevant project owners already present are
  `Function.IsConvex`, `Function.IsProper`, `LowerSemicontinuous`,
  `0⁺[𝕜]C`, `((h)₀⁺).recessionCone`,
  `Function.HasTranslationSlope`, `Function.lineal`, `Set.IsPolyhedral`, `BddBelow`,
  and the minimizer owner `IsMinOn`.
  the upstream owner `∃ v, h.HasTranslationSlope 𝕜 y v`, while the chapter's canonical owner for
  harmless common recession directions is `y ∈ Function.lineal h`.

Domain-style sampling used here:
- `Function.IsConvex`, `Function.IsProper`, `LowerSemicontinuous`;
- `Set.recessionCone` / `0⁺[𝕜]C`;
- `((h)₀⁺).recessionCone`;
- `Function.RecedesInDirection` from Definition 6.27.4;
- `Function.HasTranslationSlope` from Theorem 8.8;
- `Function.lineal` from Definition 8.9.0 and
  `ConvexERealFunction.mem_lineal_iff_forall_translate_profile_constant` from Definition 8.9.1;
- `Set.IsPolyhedral`, together with its derived convexity/closedness API;
- `IsMinOn` from mathlib's order-extrema layer.

Primitive data vs derived API:
- primitive inputs for the core owner theorem: the function `h`, the polyhedral set `C`,
  bounded-below data on `h '' C`, and the common-direction hypothesis in cone-owner form
  `y ∈ 0⁺[𝕜]C → y ∈ ((h)₀⁺).recessionCone → y ≠ 0 → y ∈ Function.lineal h`;
- source-facing bridge companion: the common-direction hypothesis phrased through
  `Set.RecedesInDirection` and `Function.RecedesInDirection`;
- derived output: existence of a minimizer in the canonical owner form `∃ x ∈ C, IsMinOn h C x`.

Layer target:
- `core/canonical` companion: common directions are stated on cone owners
  `0⁺[𝕜]C` and `((h)₀⁺).recessionCone`, with harmlessness in `Function.lineal h`;
- `source-facing` main theorem: the textbook affine-direction hypothesis is preserved and exposed
  through `Function.HasTranslationSlope`, rather than through a new wrapper for attained
  constrained infima.

Nonemptiness note: the textbook phrase "attains its infimum on `C`" is rendered by an existential
minimizer statement, so the set `C` is kept explicitly nonempty on the Lean theorem surface.
-/

-- Proof sketch: this source-facing theorem is the attainment step at recession-direction owner
-- level. The cone-owner variant below is a bridge corollary of this statement.
/-- Source-facing bridge companion: if every common recession direction of `C` and `h` lies in
`Function.lineal h`, then `h` attains its infimum on `C`. -/
theorem exists_mem_isMinOn_of_polyhedral_of_bddBelow_of_common_recessionDirections_lineal
    {C : Set E} {h : E → WithBotTop 𝕜}
    (hC_nonempty : C.Nonempty) (hC_poly : C.IsPolyhedral 𝕜)
    (hh_convex : h.IsConvex 𝕜) (hh_proper : h.IsProper) (hh_closed : LowerSemicontinuous h)
    (hlineal :
      ∀ ⦃y : E⦄, C.RecedesInDirection 𝕜 y → h.RecedesInDirection 𝕜 y →
        y ∈ Function.lineal h)
    (hbounded : BddBelow (h '' C)) :
    ∃ x ∈ C, IsMinOn h C x := sorry

-- Proof sketch: rewrite the cone-owner hypothesis to the source-facing recession-direction
-- hypothesis using the bridge theorem above, then apply the source-facing attainment theorem.
/-- Core owner companion: if `h` is a closed proper convex function, `C` is a nonempty
polyhedral convex set, `h` is bounded below on `C`, and every nonzero vector common to the set
recession cone `0⁺[𝕜]C` and to the function recession cone `((h)₀⁺).recessionCone` lies
in `Function.lineal h`, then `h` attains its infimum on `C`. The conclusion is stated in the
canonical minimizer owner form `∃ x ∈ C, IsMinOn h C x`. -/
theorem exists_mem_isMinOn_of_polyhedral_of_bddBelow_of_common_recessionCone_lineal
    {C : Set E} {h : E → WithBotTop 𝕜}
    (hC_nonempty : C.Nonempty) (hC_poly : C.IsPolyhedral 𝕜)
    (hh_convex : h.IsConvex 𝕜) (hh_proper : h.IsProper) (hh_closed : LowerSemicontinuous h)
    (hlineal :
      ∀ ⦃y : E⦄, y ∈ 0⁺[𝕜]C → y ∈ ((h)₀⁺).recessionCone → y ≠ 0 →
        y ∈ Function.lineal h)
    (hbounded : BddBelow (h '' C)) :
    ∃ x ∈ C, IsMinOn h C x := by
  have hlineal' :
      ∀ ⦃y : E⦄, C.RecedesInDirection 𝕜 y → h.RecedesInDirection 𝕜 y →
        y ∈ Function.lineal h :=
    (common_recessionCone_lineal_iff_common_recessionDirections_lineal
      (C := C) (h := h) hh_convex hh_proper).1 hlineal
  exact
    exists_mem_isMinOn_of_polyhedral_of_bddBelow_of_common_recessionDirections_lineal
      hC_nonempty hC_poly hh_convex hh_proper hh_closed hlineal' hbounded

-- Proof sketch: first pass from the source affine-direction hypothesis to the source-facing
-- harmless-common-direction condition on `Function.lineal h`; then apply the bridge theorem above.
-- This keeps the textbook affine wording on the public theorem surface while delegating the
-- canonical cone-owner abstraction to the core theorem.
/-- Corollary 6.27.3: if `h` is a closed proper convex function and every recession direction of
`h` is a direction along which `h` is affine, then `h` attains its infimum on any nonempty
polyhedral convex set `C` on which it is bounded below. The conclusion is stated in the canonical
minimizer owner form `∃ x ∈ C, IsMinOn h C x`. -/
theorem exists_mem_isMinOn_of_polyhedral_of_bddBelow_of_recessionDirections_affine
    {C : Set E} {h : E → WithBotTop 𝕜}
    (hC_nonempty : C.Nonempty) (hC_poly : C.IsPolyhedral 𝕜)
    (hh_convex : h.IsConvex 𝕜) (hh_proper : h.IsProper) (hh_closed : LowerSemicontinuous h)
    (hrecession_affine :
      ∀ ⦃y : E⦄, h.RecedesInDirection 𝕜 y → ∃ v, h.HasTranslationSlope 𝕜 y v)
    (hbounded : BddBelow (h '' C)) :
    ∃ x ∈ C, IsMinOn h C x := by
  sorry

end

/-! ### Definition_6_27_3 (from Chap06) -/
universe u v

section

variable {X : Type u} {β : Type v} [Preorder β]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.27.3 introduces the minimum set of an extended-order-valued
  function as the sublevel set at its infimum.
- `core/canonical`: the project already uses mathlib's extrema owner `IsMinOn` for global
  minimizers, while Definition 6.27.2 supplies the canonical infimum owner `⨅ x, f x`.
- `bridge/view`: the source minimum set is implemented as the set of global minimizers and then
  rewritten back to the textbook sublevel-set formula `f ⁻¹' Set.Iic (⨅ x, f x)`.

Domain-style sampling used here:
- `IsMinOn` and `isMinOn_univ_iff` from mathlib's extrema owner layer;
- the Chapter 6 infimum owner `⨅ x, f x` from `Definition_6_27_2`;
- the project sublevel-set pattern `f ⁻¹' Set.Iic a`, used for source-facing sublevel-set owners.

Primitive data vs derived API:
- primitive datum: only the function `f : X → β`;
- primitive owner: the set of points `x` with `IsMinOn f Set.univ x`;
- derived API: the source sublevel-set description at `⨅ x, f x` and the pointwise membership
  inequality `f x ≤ ⨅ y, f y`.
-/

/-- Definition 6.27.3: the minimum set of `f` is the set of global minimizers of `f`. -/
def minimumSet (f : X → β) : Set X :=
  {x | IsMinOn f Set.univ x}

end

scoped[Rockafellar] notation "argmin(" f ")" => minimumSet f

open scoped Rockafellar

section

variable {X : Type u} {β : Type v} [Preorder β]

/-- Textbook notation for Definition 6.27.3: `argmin(f)` is the minimum set of `f`. -/
@[simp] theorem argmin_eq_minimumSet (f : X → β) :
    argmin(f) = minimumSet f :=
  rfl

/-- Primitive membership criterion: `x` belongs to `argmin(f)` iff `f x` is below every value
of `f`. This keeps the theorem surface at the preorder layer. -/
@[simp] theorem mem_minimumSet_iff {f : X → β} {x : X} :
    x ∈ argmin(f) ↔ ∀ y, f x ≤ f y := by
  simpa [minimumSet] using (isMinOn_univ_iff (f := f) (a := x))

end

section

variable {X : Type u} {β : Type v} [CompleteSemilatticeInf β]

/-- The minimum set is exactly the sublevel-set owner of `f` at its infimum. -/
theorem minimumSet_def (f : X → β) :
    argmin(f) = f ⁻¹' Set.Iic (⨅ x, f x) := by
  ext x
  change IsMinOn f Set.univ x ↔ f x ≤ sInf (Set.range f)
  rw [isMinOn_univ_iff]
  constructor
  · intro hx
    exact le_sInf fun _ hy ↦ by
      rcases hy with ⟨y, rfl⟩
      exact hx y
  · intro hx y
    exact hx.trans (sInf_le ⟨y, rfl⟩)

/-- Derived infimum bridge: membership in `argmin(f)` can be rewritten as comparison
with `⨅ y, f y`. -/
theorem mem_minimumSet_iff_le_iInf {f : X → β} {x : X} :
    x ∈ argmin(f) ↔ f x ≤ ⨅ y, f y := by
  rw [minimumSet_def]
  rfl

end

section

variable {E : Type u} {β : Type v} [Preorder β] [Top β]

namespace IsMinOn

/-- Primitive bridge: if `x` is a global minimizer of `f` and `f` has a finite point, then `x`
is finite as well. -/
theorem mem_dom_of_nonempty_dom {f : E → β} {x : E}
    (hx : IsMinOn f Set.univ x) (hf : dom(f).Nonempty) :
    x ∈ dom(f) := by
  rcases hf with ⟨y, hy⟩
  rw [mem_effectiveDomain]
  exact lt_of_le_of_lt (isMinOn_univ_iff.mp hx y) (mem_effectiveDomain.mp hy)

end IsMinOn

/-- Canonical owner bridge: if `f` has a finite point, every point in `argmin(f)` is finite.
-/
theorem mem_dom_of_mem_minimumSet_of_nonempty_dom {f : E → β} {x : E}
    (hx : x ∈ argmin(f)) (hf : dom(f).Nonempty) :
    x ∈ dom(f) := by
  exact (show IsMinOn f Set.univ x from by simpa [minimumSet] using hx).mem_dom_of_nonempty_dom hf

/-- If `f` has some point strictly below `⊤`, then every point of its minimum set is below `⊤`. -/
theorem minimumSet_subset_dom_of_nonempty_dom {f : E → β} (hf : dom(f).Nonempty) :
    argmin(f) ⊆ dom(f) := by
  intro x hx
  exact mem_dom_of_mem_minimumSet_of_nonempty_dom hx hf

end

/-! ### Proposition_6_27_3 (from Chap06) -/
universe u v

open Set

section

variable {E : Type u} {α : Type v} [Preorder α] [Nonempty α]

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.27.3 identifies the union of all finite-height sublevel sets of a
  function with its effective domain.
- `core/canonical`: the owner abstraction is `dom(·)` with membership bridge
  `mem_effectiveDomain`; finite-height sublevel sets are the raw sets
  `{x | f x ≤ (a : WithBotTop α)}`.
- `bridge/view`: the textbook properness hypothesis is redundant once `α` is inhabited, because the
  value `⊥` already lies in every finite-height sublevel set. The primitive ambient datum is only
  the existence of a finite level.

Domain-style sampling used here:
- `dom(·)` and `mem_effectiveDomain` from `Chap01.Definition_4_4`;
- `WithBotTop.canLift_iff_ne_top_ne_bot` from `Chap01.EOrder.Basic`;
- `WithBotTop.coe_lt_top` from the ambient extended-order API.

Primitive data vs derived API:
- primitive data: a function `f : E → WithBotTop α` and an inhabited finite layer `α`;
- derived API: the union-of-sublevel-set description of `dom(f)`.

Layer target: `source-facing`, stated directly on the canonical owner `dom(f)` with the redundant
properness binder removed.
-/

namespace Function

-- Proof sketch: rewrite pointwise using `mem_effectiveDomain`. If `f x ≤ a` for some finite
-- `a`, then automatically `f x < ⊤`. Conversely, if `f x < ⊤`, then either `f x = ⊥`, in which
-- case `x` lies in every finite sublevel set, or `f x` is an actual finite value and
-- `WithBotTop.canLift_iff_ne_top_ne_bot` supplies the needed level.
/-- Proposition 6.27.3: if the finite codomain layer `α` is inhabited, then the union of all
finite-height sublevel sets of a `WithBotTop α`-valued function is exactly the effective domain
`dom(f)`. Specializing to `α = ℝ` recovers the textbook statement for
`f : ℝ^n → (-∞, +∞]`; the textbook properness hypothesis is redundant for this set identity. -/
theorem iUnion_sublevel_eq_dom (f : E → WithBotTop α) :
    (⋃ a : α, {x : E | f x ≤ (a : WithBotTop α)}) = dom(f) := by
  ext x
  rw [mem_effectiveDomain]
  simp only [mem_iUnion, mem_setOf_eq]
  constructor
  · rintro ⟨a, hxa⟩
    exact lt_of_le_of_lt hxa (WithBotTop.coe_lt_top a)
  · intro hx_top
    by_cases hx_bot : f x = ⊥
    · obtain ⟨a⟩ := ‹Nonempty α›
      exact ⟨a, by simp [hx_bot]⟩
    · rcases (WithBotTop.canLift_iff_ne_top_ne_bot).mpr ⟨ne_of_lt hx_top, hx_bot⟩ with ⟨a, ha⟩
      exact ⟨a, by simp [ha]⟩

end Function

end
