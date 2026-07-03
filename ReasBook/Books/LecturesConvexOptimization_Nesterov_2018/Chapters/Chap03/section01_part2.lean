import Mathlib
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_3_1 (from Chap03) -/
noncomputable section

open scoped BigOperators

universe u v w z

variable {𝕜 : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {ι : Type v}
variable {E : Type w} [AddCommGroup E] [Module 𝕜 E]
variable {β : Type z} [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β]
  [Module 𝕜 β] [IsStrictOrderedModule 𝕜 β]

local notation "convexCombination" =>
  @ConvexSpace.convexCombination 𝕜 E inferInstance inferInstance inferInstance inferInstance

/- Theorem 3.1 lies in the finite convex-combination / convex-hull maximum-principle domain.

Sampled owner-style declarations:
- `is_convex_combination_of`
- `StdSimplex.convexCombination_map_eq_sum`
- `ConvexOn.exists_ge_of_mem_convexHull`
- `ConvexOn.le_sup_of_mem_convexHull`

Best owner abstraction:
- the chapter owner `is_convex_combination_of 𝕜 points x`, bridged to the canonical convex-hull
  maximum-principle theorems

Primitive data:
- a convex-on-set witness `hf : ConvexOn 𝕜 C f`
- a family `points : ι → E`
- a point `x : E`
- the owner witness `hx : is_convex_combination_of 𝕜 points x`

Derived API:
- the convex-hull membership bridge `hx.mem_convexHull`
- the attainment statement `∃ i, f x ≤ f (points i)`
- the finite maximum bound over `Finset.univ`
- the coefficient bridge `StdSimplex.convexCombination_map_eq_sum`

Source/core/bridge triage:
- source-facing: the maximum principle for the value of a convex function at a finite convex
  combination
- core/canonical: `ConvexOn.exists_ge_of_mem_convexHull` and
  `ConvexOn.le_sup_of_mem_convexHull`
- bridge/view: `is_convex_combination_of.mem_convexHull` and the coefficient-display companion
  theorem

This file therefore centers its public theorem surface on the earlier chapter owner
`is_convex_combination_of`. The coefficient formula remains only as a companion bridge, while the
main proofs reuse the canonical convex-hull maximum principle.
-/

/-- A finite convex combination belongs to the convex hull of the participating family. -/
theorem is_convex_combination_of.mem_convexHull {points : ι → E} {x : E}
    (hx : is_convex_combination_of 𝕜 points x) :
    x ∈ convexHull 𝕜 (Set.range points) := by
  rcases hx with ⟨w, rfl⟩
  let s := w.weights.support
  have hsum : ∑ i ∈ s, w.weights i = 1 := by
    simpa [s, Finsupp.sum] using w.total
  have hcomb : convexCombination (w.map points) = s.centerMass w.weights points := by
    have hs_center : s.centerMass w.weights points = ∑ i ∈ s, w.weights i • points i := by
      rw [Finset.centerMass, hsum]
      simp
    calc
      convexCombination (w.map points) = ∑ i ∈ s, w.weights i • points i := by
        rw [convexCombination_eq_sum, StdSimplex.map]
        rw [Finsupp.sum_mapDomain_index (fun _ ↦ by simp) (fun _ _ _ ↦ add_smul _ _ _)]
        rfl
      _ = s.centerMass w.weights points := by
        simpa using hs_center.symm
  rw [hcomb]
  exact s.centerMass_mem_convexHull
    (fun i _ ↦ w.nonneg i)
    (by
      rw [hsum]
      exact zero_lt_one)
    (fun i _ ↦ ⟨i, rfl⟩)

/-- A nontrivial finite convex combination requires a nonempty index type. -/
theorem is_convex_combination_of.nonempty {points : ι → E} {x : E}
    (hx : is_convex_combination_of 𝕜 points x) : Nonempty ι := by
  rcases hx with ⟨w, _⟩
  have hw : w.weights ≠ 0 := by
    intro hw_zero
    have : (0 : 𝕜) = 1 := by
      simpa [hw_zero] using w.total
    exact zero_ne_one this
  obtain ⟨i, _hi⟩ := Finsupp.support_nonempty_iff.2 hw
  exact ⟨i⟩

/-- Theorem 3.1, owner form: if `x` is a convex combination of `points` and all those points lie in
`C`, then a convex function on `C` takes at `x` a value bounded above by one of the endpoint
values. -/
theorem convexOn_exists_ge_of_convex_combination
    {C : Set E} {f : E → β} (hf : ConvexOn 𝕜 C f) {points : ι → E} {x : E}
    (hx : is_convex_combination_of 𝕜 points x) (hpoints : Set.range points ⊆ C) :
    ∃ i, f x ≤ f (points i) := by
  obtain ⟨y, hy, hxy⟩ := hf.exists_ge_of_mem_convexHull hpoints hx.mem_convexHull
  rcases hy with ⟨i, rfl⟩
  exact ⟨i, hxy⟩

/-- Theorem 3.1: if `x` is a convex combination of a finite family `points` contained in `C`,
then a convex function on `C` takes at `x` a value bounded above by the maximum of its values on
that family. -/
theorem convexOn_value_le_max_of_convex_combination
    [Fintype ι] {C : Set E} {f : E → β} (hf : ConvexOn 𝕜 C f) {points : ι → E} {x : E}
    (hx : is_convex_combination_of 𝕜 points x) (hpoints : ∀ i, points i ∈ C) :
    letI : Nonempty ι := hx.nonempty
    f x ≤ Finset.univ.sup' Finset.univ_nonempty (fun i ↦ f (points i)) := by
  letI : Nonempty ι := hx.nonempty
  obtain ⟨i, hi_le⟩ := convexOn_exists_ge_of_convex_combination hf hx <| by
    rintro _ ⟨j, rfl⟩
    exact hpoints j
  exact hi_le.trans <| Finset.le_sup' (fun j ↦ f (points j)) (Finset.mem_univ i)

section Coefficients

variable [Fintype ι]
variable {C : Set E} {f : E → β} {points : ι → E}

/-- A finite coefficient family with total mass `1` has a nonempty nonzero support. -/
theorem nonzeroWeightSupport_nonempty (α : ι → 𝕜) (hαsum : ∑ i, α i = 1) :
    (Finset.univ.filter fun i ↦ α i ≠ 0).Nonempty := by
  refine Finset.nonempty_iff_ne_empty.mpr ?_
  intro hzero
  have hsum_zero : ∑ i, α i = 0 := by
    rw [← Finset.sum_filter_ne_zero]
    simp [hzero]
  exact one_ne_zero <| by rw [← hαsum, hsum_zero]

/-- Theorem 3.1, coefficient form: a weighted sum with nonnegative coefficients summing to `1`
is bounded above by the maximum of the endpoint values on the nonzero-weight support. -/
theorem convexOn_value_le_max_of_convex_combination_of_coefficients
    (hf : ConvexOn 𝕜 C f) (α : ι → 𝕜)
    (hαnonneg : ∀ i, 0 ≤ α i)
    (hαsum : ∑ i, α i = 1) (hpoints : ∀ i, α i ≠ 0 → points i ∈ C) :
    f (∑ i, α i • points i) ≤
      (Finset.univ.filter fun i ↦ α i ≠ 0).sup'
        (nonzeroWeightSupport_nonempty α hαsum) (fun i ↦ f (points i)) := by
  let w : StdSimplex 𝕜 ι :=
    ⟨Finsupp.equivFunOnFinite.symm α,
      by simpa using hαnonneg,
      by simpa using (Finsupp.equivFunOnFinite_symm_sum α).trans hαsum⟩
  let s := w.weights.support
  have hsupport : w.weights.support = Finset.univ.filter fun i ↦ α i ≠ 0 := by
    ext i
    simp [w]
  have hsum : ∑ i ∈ s, w.weights i = 1 := by
    simpa [s, Finsupp.sum] using w.total
  have hpos : 0 < ∑ i ∈ s, w.weights i := by
    rw [hsum]
    exact zero_lt_one
  have h :
      ∃ i ∈ s, f (convexCombination (w.map points)) ≤ f (points i) := by
    have hcenter :
        ∃ i ∈ s, f (s.centerMass w.weights points) ≤ f (points i) := by
      simpa [s] using
        (hf.exists_ge_of_centerMass
          (fun i _ ↦ w.nonneg i)
          hpos
          (fun i hi ↦
            hpoints i <| by
              have hi' : w.weights i ≠ 0 := by
                simpa [s, Finsupp.mem_support_iff] using hi
              simpa [w] using hi'))
    rcases hcenter with ⟨i, hi, hi_le⟩
    have hcomb : s.centerMass w.weights points = convexCombination (w.map points) := by
      have hs_center : s.centerMass w.weights points = ∑ i ∈ s, w.weights i • points i := by
        rw [Finset.centerMass, hsum]
        simp
      calc
        s.centerMass w.weights points = ∑ i ∈ s, w.weights i • points i :=
          hs_center
        _ = convexCombination (w.map points) := by
          rw [convexCombination_eq_sum, StdSimplex.map]
          rw [Finsupp.sum_mapDomain_index (fun _ ↦ by simp) (fun _ _ _ ↦ add_smul _ _ _)]
          rfl
    exact ⟨i, hi, by simpa [hcomb] using hi_le⟩
  obtain ⟨i, hi, hi_le⟩ := h
  have hmax :
      f (convexCombination (w.map points)) ≤ s.sup' ⟨i, hi⟩ (fun j ↦ f (points j)) :=
    hi_le.trans <| Finset.le_sup' (fun j ↦ f (points j)) hi
  rw [StdSimplex.convexCombination_map_eq_sum 𝕜 w points] at hmax
  simpa [s, hsupport] using hmax

end Coefficients

/-! ### Theorem_3_1_1 (from Chap03) -/
universe u

open scoped WithTopConvexAnalysis

section

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-
Primary domain: convex analysis for `WithTop ℝ`-valued functions via their finite-value part.

Owner abstractions sampled before refining:
* chapter `dom f` and `withTopRealPart f` in `Definition_3_3`, the canonical owner bridge for
  `WithTop ℝ`-valued convex functions;
* mathlib `ConvexOn`, the canonical convexity owner;
* chapter `convexOn_iff_affine_ray_inequality` in `Theorem_3_2`, the owner affine-ray criterion on
  a convex set.

Best owner abstraction:
* `ConvexOn ℝ (dom f) (withTopRealPart f)`.

Primitive data:
* the function `f : X → WithTop ℝ`.

Derived API:
* convexity of `dom f`;
* the affine-ray lower bound on `withTopRealPart f` over `dom f`.

Source/core/bridge triage:
* source-facing: the textbook affine-ray criterion for an extended-real-valued function;
* core/canonical: `ConvexOn ℝ (dom f) (withTopRealPart f)`;
* bridge/view: the specialization of `convexOn_iff_affine_ray_inequality` to the effective domain.

This file therefore keeps only the source-facing `WithTop` specialization and reuses the earlier
chapter owner surface instead of rebuilding the effective domain as `{x | f x < ⊤}` or the finite
real part as `fun x ↦ (f x).untopD 0`.
-/

/-- Theorem 3.1.1: an `ℝ ∪ {+∞}`-valued function on `ℝⁿ` is convex on its effective domain if and
only if its effective domain is convex and every forward affine extrapolation point
`y + β • (y - x)` that remains in that domain satisfies the secant-line lower bound determined by
`x` and `y`. The statement is generalized from the textbook `ℝⁿ` setting to an arbitrary real
module. -/
-- Proof sketch: apply the owner-level bridge
-- `convexOn_iff_affine_ray_inequality` to the canonical owner
-- `ConvexOn ℝ (dom f) (withTopRealPart f)`, and separate the domain-convexity component.
theorem convexOn_effectiveDomain_iff_affine_ray_inequality
    (f : X → WithTop ℝ) :
    ConvexOn ℝ (dom f) (withTopRealPart f) ↔
      Convex ℝ (dom f) ∧
      ∀ ⦃x y : X⦄, x ∈ dom f → y ∈ dom f →
        ∀ ⦃β : ℝ⦄, 0 ≤ β →
          y + β • (y - x) ∈ dom f →
            withTopRealPart f (y + β • (y - x)) ≥
              withTopRealPart f y + β * (withTopRealPart f y - withTopRealPart f x) := by
  constructor
  · intro hf
    refine ⟨hf.1, ?_⟩
    exact (convexOn_iff_affine_ray_inequality (dom f) (withTopRealPart f) hf.1).mp hf
  · rintro ⟨hdom, hray⟩
    exact (convexOn_iff_affine_ray_inequality (dom f) (withTopRealPart f) hdom).mpr hray

end

/-! ### Theorem_3_1_1_1 (from Chap03) -/
universe u

noncomputable section

open scoped ConvexAnalysis

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/- Theorem 3.1.1.1 lies in the chapter's `EReal`-valued convex-analysis domain.

Relevant owner-style declarations sampled before refinement:
- chapter `dom f` and `extendedRealRealPart f` in `Definition_3_1_1_3`, the canonical owner bridge
  from an `EReal`-valued function to its finite real part on the effective domain;
- mathlib `ConvexOn`, the canonical convexity owner;
- chapter `convexOn_iff_affine_ray_inequality` in `Theorem_3_2`, the owner affine-ray criterion
  on a convex set.

Best owner abstraction:
- `ConvexOn ℝ (dom f) (extendedRealRealPart f)`.

Primitive data:
- the function `f : X → EReal`.

Derived API:
- convexity of `dom f`;
- the affine-ray lower bound for `extendedRealRealPart f` on `dom f`.

Source/core/bridge triage:
- source-facing: the textbook affine-ray criterion for an extended-real-valued function;
- core/canonical: `ConvexOn ℝ (dom f) (extendedRealRealPart f)`;
- bridge/view: the specialization of `convexOn_iff_affine_ray_inequality` to the effective domain.

This file therefore keeps only the source-facing `EReal` specialization and reuses the earlier
chapter owner surface directly, instead of rebuilding a parallel convexity owner for the
finite-real-part model.
-/

/-- Theorem 3.1.1.1: an extended-real-valued function on a real additive module is convex exactly
when its effective domain is convex and every forward affine extrapolation point `y + β • (y - x)`
in that domain satisfies the supporting-line inequality determined by the secant through `x` and
`y`. Specializing `X` to `EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` statement. -/
-- Proof sketch: apply the owner-level bridge
-- `convexOn_iff_affine_ray_inequality` from `Theorem_3_2` to the canonical owner
-- `ConvexOn ℝ (dom f) (extendedRealRealPart f)`, then split off the domain-convexity component.
theorem isConvexExtendedRealFunction_iff_affine_ray_inequality
    (f : X → EReal) :
    ConvexOn ℝ (dom f) (extendedRealRealPart f) ↔
      Convex ℝ (dom f) ∧
      ∀ ⦃x y : X⦄, x ∈ dom f → y ∈ dom f →
        ∀ ⦃β : ℝ⦄, 0 ≤ β →
          y + β • (y - x) ∈ dom f →
            extendedRealRealPart f (y + β • (y - x)) ≥
              extendedRealRealPart f y +
                β * (extendedRealRealPart f y - extendedRealRealPart f x) := by
  constructor
  · intro hf
    refine ⟨hf.1, ?_⟩
    exact (convexOn_iff_affine_ray_inequality (dom f) (extendedRealRealPart f) hf.1).mp hf
  · rintro ⟨hdom, hray⟩
    exact (convexOn_iff_affine_ray_inequality (dom f) (extendedRealRealPart f) hdom).mpr hray

end

/-! ### Theorem_3_1_1_2 (from Chap03) -/
universe u

noncomputable section

open scoped ConvexAnalysis

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]

/-
Theorem 3.1.1.2 lives in the chapter's extended-real convex-analysis bridge.

Primary domain:
- convexity of the finite real part of an `EReal`-valued function on its effective domain
- convexity of the corresponding effective epigraph subset of `X × ℝ`

Sampled owner-style declarations before refinement:
- chapter `dom` from `Definition_3_1_1_2`
- chapter `extendedRealRealPart` from `Definition_3_1_1_3`
- chapter `effectiveEpigraph` from `Definition_3_1_1_3`
- mathlib `ConvexOn.convex_epigraph`
- mathlib `convexOn_iff_convex_epigraph`

Best owner abstraction:
- source-facing owner: `effectiveEpigraph f`
- core/canonical: `ConvexOn ℝ (dom f) (extendedRealRealPart f)`
- bridge/view: the definitional identification of `effectiveEpigraph f` with the real epigraph of
  `extendedRealRealPart f` over `dom f`

Primitive data:
- the source-facing owner data `dom f`
- the finite real part `extendedRealRealPart f`
- the effective epigraph owner `effectiveEpigraph f`

Derived API:
- the epigraph-convexity equivalence below

Source/core/bridge triage:
- source-facing: the textbook effective-epigraph convexity criterion on `effectiveEpigraph f`
- core/canonical: mathlib `ConvexOn` and `convexOn_iff_convex_epigraph`
- bridge/view: `dom f`, `extendedRealRealPart f`, and the definitional expansion of
  `effectiveEpigraph f`

The textbook states the result on `ℝⁿ`, but the owner theorem and both imported bridge
constructions use no coordinate, topological, or finite-dimensional structure. The public theorem
therefore lives at the intrinsic real-module level; `ℝⁿ` is a downstream specialization.
-/
/-- Theorem 3.1.1.2: the owner `ConvexOn` formulation for the finite real part of an
extended-real-valued function is equivalent to convexity of its textbook effective epigraph in
`X × ℝ`. -/
-- Proof sketch: apply mathlib's `convexOn_iff_convex_epigraph` to `extendedRealRealPart f` on
-- `dom f`, then unfold the source-facing owner `effectiveEpigraph`.
theorem isConvexExtendedRealFunction_iff_convex_epigraph
    (f : X → EReal) :
    ConvexOn ℝ (dom f) (extendedRealRealPart f) ↔
      Convex ℝ (effectiveEpigraph f) := by
  simpa [effectiveEpigraph] using
    (convexOn_iff_convex_epigraph :
      ConvexOn ℝ (dom f) (extendedRealRealPart f) ↔
        Convex ℝ {p : X × ℝ | p.1 ∈ dom f ∧ extendedRealRealPart f p.1 ≤ p.2})

end

/-! ### Theorem_3_1_1_3 (from Chap03) -/
universe u

noncomputable section

open scoped ConvexAnalysis

/-
Theorem 3.1.1.3 lies in the chapter's extended-real convex-analysis bridge domain.

Relevant owner-style declarations sampled before refinement:
- mathlib `ConvexOn.convex_le`
- project `mem_levelSet_iff` and `levelSet_eq_setOf` in `Chap01/Definition_1_4_8`, which record
  the chapter’s lower-level-set owner surface
- mathlib `ConvexOn`
- chapter `extendedRealRealPart` in `Definition_3_1_1_3`
- chapter notation `dom f` for `extendedRealEffectiveDomain f`

Best owner abstraction:
- the canonical owner theorem `ConvexOn.convex_le`, specialized to the finite-real-part bridge
  `ConvexOn ℝ (dom f) (extendedRealRealPart f)`

Primitive data:
- `dom f`
- `extendedRealRealPart f`

Derived API:
- the owner sublevel set `{x ∈ dom f | extendedRealRealPart f x ≤ β}`
- the source-facing set-builder `{x ∈ dom f | f x ≤ β}`
- the bridge `extendedRealSublevelSet_dom_eq`, identifying that source-facing sublevel set with
  the owner one
- the convexity statement, which is only direct recall/use of the owner theorem above

Source/core/bridge triage:
- source-facing: the textbook real sublevel-set surface `{x ∈ dom f | f x ≤ β}`
- core/canonical: `ConvexOn.convex_le`
- bridge/view: the identification of the source-facing surface with the owner sublevel set
  `{x ∈ dom f | extendedRealRealPart f x ≤ β}` via `extendedRealRealPart_le_iff`

The textbook states the theorem on `ℝⁿ`, but the bridge object and the owner theorem use only the
ambient `ℝ`-module structure already fixed in `Definition_3_1_1_3`. This file therefore deletes
the duplicate sublevel-set wrapper, records the minimal source-facing bridge theorem, and presents
the numbered item itself as the chapter-specialized owner theorem at `dom f` and
`extendedRealRealPart f`.
-/

/-- On the effective domain, the source-facing `EReal` sublevel set is exactly the owner sublevel
set of the finite real part. -/
theorem extendedRealSublevelSet_dom_eq {X : Type u} (f : X → EReal) (β : ℝ) :
    {x ∈ dom f | f x ≤ β} = {x ∈ dom f | extendedRealRealPart f x ≤ β} := by
  ext x
  constructor
  · rintro ⟨hx, hxβ⟩
    exact ⟨hx, (extendedRealRealPart_le_iff hx).2 hxβ⟩
  · rintro ⟨hx, hxβ⟩
    exact ⟨hx, (extendedRealRealPart_le_iff hx).1 hxβ⟩

section Convexity

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]
variable (f : X → EReal)

/- Theorem 3.1.1.3: if `f` is convex, then each sublevel set
`{x ∈ dom f | extendedRealRealPart f x ≤ β}` is convex. This is exactly the canonical owner
theorem `ConvexOn.convex_le`, specialized to the chapter bridge `extendedRealRealPart`; the
source-facing sublevel set `{x ∈ dom f | f x ≤ β}` is identified with this owner surface by
`extendedRealSublevelSet_dom_eq f`. -/
#check
  (ConvexOn.convex_le :
    ConvexOn ℝ (dom f) (extendedRealRealPart f) →
      ∀ β : ℝ, Convex ℝ {x ∈ dom f | extendedRealRealPart f x ≤ β})

end Convexity

end

/-! ### Theorem_3_1_1_4 (from Chap03) -/
/- Theorem 3.1.1.4 lies in the chapter's closed-convex-function domain.

Primary domain:
- closed convex `WithTop ℝ`-valued functions on real topological modules.

Sampled owner-style declarations:
- `ClosedConvexOn` and `ClosedConvexFunction` in `Definition_3_1_1_5`
- `ClosedConvexOn.isClosed_constrainedEpigraph`
- `ClosedConvexOn.convex_constrainedEpigraph`
- `constrainedEpigraph` in `Definition_3_3`

Best owner abstraction:
- `ClosedConvexFunction f`

Primitive data:
- the effective domain `withTopEffectiveDomain f`
- the closedness and convexity of the constrained epigraph packaged by
  `ClosedConvexFunction f`

Derived API:
- the closedness and convexity of the real sublevel sets `{x | f x ≤ β}`

Source/core/bridge triage:
- source-facing: Theorem 3.1.1.4 itself, the sublevel-set consequence of closed convexity
- core/canonical: `ClosedConvexFunction`
- bridge/view: `constrainedEpigraph`

This item is therefore kept at the owner-theorem layer and reduced to the actual source-facing
sublevel-set statement, without introducing separate set owners or additional minimizer/existence
results under the numbered theorem. -/

universe u

open scoped WithTopConvexAnalysis

section

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/-- Theorem 3.1.1.4: every real sublevel set of a closed convex function is closed and convex. -/
-- Proof sketch: identify `{x | f x ≤ β}` with the horizontal slice of the closed convex epigraph
-- of `f` at height `β`; closedness and convexity are inherited from that slice.
theorem ClosedConvexFunction.isClosed_convex_sublevelSet
    {f : X → WithTop ℝ} (hf : ClosedConvexFunction f) (β : ℝ) :
    IsClosed {x | f x ≤ β} ∧ Convex ℝ {x | f x ≤ β} := by
  have hβ_top : (((β : ℝ) : WithTop ℝ) < ⊤) := by simp
  have hclosed_set :
      {x | f x ≤ β} = (fun x : X ↦ (x, β)) ⁻¹' constrainedEpigraph (dom f) f := by
    ext x
    constructor
    · intro hx
      have hxdom : x ∈ dom f := lt_of_le_of_lt hx hβ_top
      exact ⟨hxdom, hx⟩
    · rintro ⟨_, hx⟩
      exact hx
  have hconvex_set :
      {x | f x ≤ β} = {x ∈ dom f | withTopRealPart f x ≤ β} := by
    ext x
    constructor
    · intro hx
      have hxdom : x ∈ dom f := lt_of_le_of_lt hx hβ_top
      exact ⟨hxdom, (withTopRealPart_le_iff hxdom).2 hx⟩
    · rintro ⟨hxdom, hxβ⟩
      exact (withTopRealPart_le_iff hxdom).1 hxβ
  refine ⟨?_, ?_⟩
  · rw [hclosed_set]
    exact IsClosed.preimage (by continuity) hf.isClosed_constrainedEpigraph
  · rw [hconvex_set]
    exact hf.convexOn_withTopRealPart.convex_le β

end

/-! ### Corollary_3_1_2 (from Chap03) -/
/-
Corollary 3.1.2 lies in the convex-analysis domain of finite convex-hull maximum principles.

 Sampled owner-style declarations:
- `ConvexOn.exists_ge_of_mem_convexHull`
- `ConvexOn.le_sup_of_mem_convexHull`
- `ConvexOn.inf_le_of_mem_convexHull`

Best owner abstraction:
- `ConvexOn.exists_ge_of_mem_convexHull`

Primitive data:
- a vertex set `t : Set E`, or equivalently a finite vertex family viewed through `Set.range`
- a set `s` and a convex function `hf : ConvexOn ℝ s f`
- the inclusion `t ⊆ s`
- a point `x ∈ convexHull ℝ t`

Derived API:
- a vertex `y ∈ t` with `f x ≤ f y`

Source/core/bridge triage:
- source-facing: the corollary that the maximum of a convex function on a simplex is attained at a
  vertex once the vertices lie in the convex domain
- core/canonical: `ConvexOn.exists_ge_of_mem_convexHull`
- bridge/view: the finite-sup theorem `ConvexOn.le_sup_of_mem_convexHull` and coefficient or
  index-level attainment formulations derived from the owner theorem

The chapter theorem `convexOn_value_le_max_of_convex_combination` is a bridge/view reformulation.
This file keeps only the canonical witness-level convex-hull maximum-principle recall.
-/

recall ConvexOn.exists_ge_of_mem_convexHull

/-! ### Corollary_3_1_2_1 (from Chap03) -/
noncomputable section

universe u v

open scoped BigOperators

variable {ι : Type v} [Fintype ι] [Nonempty ι]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- Helper for Corollary 3.1.2.1: a continuous linear functional on a finite product `ι → ℝ` is
determined by its values on the standard coordinate vectors `Pi.single i 1`. -/
theorem strongDual_apply_fintype
    [DecidableEq ι]
    (g : StrongDual ℝ (ι → ℝ)) (z : ι → ℝ) :
    g z = ∑ i, z i * g (Pi.single i 1) := by
  -- Expand `z` in the standard basis and then use linearity termwise.
  have hdecomp :
      z = ∑ i, Pi.single i (z i) := by
    ext j
    simp
  rw [hdecomp, map_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hsingle :
      Pi.single i (z i) = z i • (Pi.single (M := fun _ ↦ ℝ) i 1) := by
    ext j
    by_cases h : i = j
    · subst h
      simp
    · simp [Pi.single_eq_of_ne (Ne.symm h)]
  rw [hsingle, map_smul]
  simp [smul_eq_mul]

/-- Helper for Corollary 3.1.2.1: if `Q` is nonempty and the constrained sublevel sets of the
finite maximum are bounded, then that maximum attains its minimum on `Q`. -/
theorem exists_isMinOn_familyMaximum_of_bounded_sublevels
    {Q : Set E} {fs : ι → E → ℝ}
    (hfs : ∀ i, ClosedConvexOn Q (fun x ↦ (fs i x : WithTop ℝ)))
    (hbounded :
      ∀ α : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet Q (fun x ↦ ((maxTypeObjective fs x : ℝ) : WithTop ℝ)) α))
    (hQ_nonempty : Q.Nonempty) :
    ∃ xStar : Q, IsMinOn (fun x : Q ↦ maxTypeObjective fs x) Set.univ xStar := by
  classical
  let β₀ : ℝ := maxTypeObjective fs hQ_nonempty.some
  let S : Set E :=
    constrainedSublevelSet Q
      (fun x ↦ ((maxTypeObjective fs x : ℝ) : WithTop ℝ)) β₀
  have hsome_memS : hQ_nonempty.some ∈ S := by
    -- The reference feasible point lies in its own max-sublevel slice.
    refine mem_constrainedSublevelSet_iff.2 ?_
    exact ⟨hQ_nonempty.some_mem, le_rfl⟩
  have hS_subset : S ⊆ Q := by
    -- Membership in the constrained sublevel set already records feasibility.
    intro x hx
    exact (mem_constrainedSublevelSet_iff.mp hx).1
  have hS_closed : IsClosed S := by
    -- The max-sublevel slice is the finite intersection of the component sublevel slices.
    have hEq :
        S = ⋂ i : ι, constrainedSublevelSet Q (fun x ↦ (fs i x : WithTop ℝ)) β₀ := by
      ext x
      constructor
      · intro hx
        rcases mem_constrainedSublevelSet_iff.mp hx with ⟨hxQ, hxβ⟩
        have hxβ' : maxTypeObjective fs x ≤ β₀ := by
          exact_mod_cast hxβ
        rw [Set.mem_iInter]
        intro i
        refine mem_constrainedSublevelSet_iff.2 ⟨hxQ, ?_⟩
        exact_mod_cast (maxTypeObjective_le_iff fs x β₀).mp hxβ' i
      · intro hx
        have hxQ : x ∈ Q := by
          exact (mem_constrainedSublevelSet_iff.mp ((Set.mem_iInter.mp hx) (Classical.choice ‹Nonempty ι›))).1
        refine mem_constrainedSublevelSet_iff.2 ⟨hxQ, ?_⟩
        exact_mod_cast (maxTypeObjective_le_iff fs x β₀).mpr fun i ↦ by
          exact_mod_cast (mem_constrainedSublevelSet_iff.mp ((Set.mem_iInter.mp hx) i)).2
    rw [hEq]
    refine isClosed_iInter ?_
    intro i
    exact (hfs i).isClosed_constrainedSublevelSet β₀
  have hS_convex : Convex ℝ S := by
    -- The same finite-intersection description transfers convexity to the max-sublevel slice.
    have hEq :
        S = ⋂ i : ι, constrainedSublevelSet Q (fun x ↦ (fs i x : WithTop ℝ)) β₀ := by
      ext x
      constructor
      · intro hx
        rcases mem_constrainedSublevelSet_iff.mp hx with ⟨hxQ, hxβ⟩
        have hxβ' : maxTypeObjective fs x ≤ β₀ := by
          exact_mod_cast hxβ
        rw [Set.mem_iInter]
        intro i
        refine mem_constrainedSublevelSet_iff.2 ⟨hxQ, ?_⟩
        exact_mod_cast (maxTypeObjective_le_iff fs x β₀).mp hxβ' i
      · intro hx
        have hxQ : x ∈ Q := by
          exact (mem_constrainedSublevelSet_iff.mp ((Set.mem_iInter.mp hx) (Classical.choice ‹Nonempty ι›))).1
        refine mem_constrainedSublevelSet_iff.2 ⟨hxQ, ?_⟩
        exact_mod_cast (maxTypeObjective_le_iff fs x β₀).mpr fun i ↦ by
          exact_mod_cast (mem_constrainedSublevelSet_iff.mp ((Set.mem_iInter.mp hx) i)).2
    rw [hEq]
    refine convex_iInter ?_
    intro i
    exact (hfs i).convex_constrainedSublevelSet β₀
  have hS_bounded : Bornology.IsBounded S := by
    -- The bounded-slice hypothesis applies directly at the reference value `β₀`.
    simpa [S, β₀] using hbounded β₀
  have hS_compact : IsCompact S :=
    Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded
  have hS_nonempty : S.Nonempty := ⟨hQ_nonempty.some, hsome_memS⟩
  have hfsS : ∀ i, ClosedConvexOn S (fun x ↦ (fs i x : WithTop ℝ)) := by
    -- Restrict each component to the compact slice.
    intro i
    exact (hfs i).restrict hS_closed hS_convex hS_subset
  have hmax_lower :
      LowerSemicontinuousOn (maxTypeObjective fs) S := by
    -- Finite maxima of lower-semicontinuous slice restrictions remain lower semicontinuous.
    have hiSup_lower : LowerSemicontinuousOn (fun x : E ↦ ⨆ i, fs i x) S :=
      lowerSemicontinuousOn_ciSup
        (fun x hx ↦ Finite.bddAbove_range (fun i : ι ↦ fs i x))
        fun i ↦
          (hfsS i).lowerSemicontinuousOn_real hS_closed
    have hmax_eq : maxTypeObjective fs = fun x : E ↦ ⨆ i, fs i x := by
      ext x
      rw [maxTypeObjective_apply, Finset.sup'_univ_eq_ciSup]
    simpa [hmax_eq] using hiSup_lower
  obtain ⟨xStar, hxStarS, hxStarMinS⟩ :=
    hmax_lower.exists_isMinOn hS_nonempty hS_compact
  have hxStarQ : xStar ∈ Q := hS_subset hxStarS
  have hxStar_beta : maxTypeObjective fs xStar ≤ β₀ := by
    exact_mod_cast (mem_constrainedSublevelSet_iff.mp hxStarS).2
  have hxStarMinQ : IsMinOn (maxTypeObjective fs) Q xStar := by
    -- Outside the compact slice the objective is forced above `β₀`, so `xStar` still minimizes on `Q`.
    intro y hyQ
    by_cases hyS : y ∈ S
    · exact hxStarMinS hyS
    · have hy_not_le : ¬ maxTypeObjective fs y ≤ β₀ := by
        intro hyβ
        exact hyS (mem_constrainedSublevelSet_iff.2 ⟨hyQ, by exact_mod_cast hyβ⟩)
      exact le_trans hxStar_beta (le_of_lt (lt_of_not_ge hy_not_le))
  refine ⟨⟨xStar, hxStarQ⟩, ?_⟩
  -- Repackage the ambient minimizer as a minimizer on the subtype `Q`.
  rw [isMinOn_univ_iff]
  intro x
  rw [isMinOn_iff] at hxStarMinQ
  exact hxStarMinQ x x.property

/-- Helper for Corollary 3.1.2.1: the upper image attached to a minimizer of the family maximum is
convex, has nonempty interior, contains the minimizing diagonal point, and that diagonal point lies
on its boundary. -/
theorem upperImage_boundary_of_familyMaximum_minimizer
    {Q : Set E} {fs : ι → E → ℝ} (xStar : Q)
    (hfs : ∀ i, ClosedConvexOn Q (fun x ↦ (fs i x : WithTop ℝ)))
    (hxStarMin : IsMinOn (fun x : Q ↦ maxTypeObjective fs x) Set.univ xStar) :
    let fStar := maxTypeObjective fs xStar
    let U : Set (ι → ℝ) := {p | ∃ x ∈ Q, ∀ i, fs i x ≤ p i}
    Convex ℝ U ∧
      (fun _ ↦ fStar) ∈ U ∧
      (interior U).Nonempty ∧
      (fun _ ↦ fStar) ∉ interior U := by
  classical
  let fStar : ℝ := maxTypeObjective fs xStar
  let U : Set (ι → ℝ) := {p | ∃ x ∈ Q, ∀ i, fs i x ≤ p i}
  have hconv : ∀ i, ConvexOn ℝ Q (fs i) := by
    -- Each component inherits ordinary real-valued convexity from its lifted closed-convex hypothesis.
    intro i
    exact (hfs i).convexOn_real
  have hU_convex : Convex ℝ U := by
    -- The upper image is stable under convex combinations because each coordinate is.
    intro p hp q hq a b ha hb hab
    rcases hp with ⟨x, hxQ, hx⟩
    rcases hq with ⟨y, hyQ, hy⟩
    refine ⟨a • x + b • y, (hfs (Classical.choice ‹Nonempty ι›)).convex hxQ hyQ ha hb hab, ?_⟩
    intro i
    change fs i (a • x + b • y) ≤ a * p i + b * q i
    have hcv : fs i (a • x + b • y) ≤ a * fs i x + b * fs i y := by
      simpa [smul_eq_mul] using (hconv i).2 hxQ hyQ ha hb hab
    have hxmul : a * fs i x ≤ a * p i := mul_le_mul_of_nonneg_left (hx i) ha
    have hymul : b * fs i y ≤ b * q i := mul_le_mul_of_nonneg_left (hy i) hb
    exact hcv.trans (add_le_add hxmul hymul)
  have hdStar_mem : (fun _ ↦ fStar) ∈ U := by
    -- At the minimizing point, every component lies below the family maximum.
    refine ⟨xStar, xStar.property, ?_⟩
    intro i
    exact (maxTypeObjective_le_iff fs xStar fStar).mp le_rfl i
  have hU_int_nonempty : (interior U).Nonempty := by
    -- Any feasible point provides an open orthant contained in the upper image.
    let p0 : ι → ℝ := fun i ↦ fs i xStar + 1
    let V : Set (ι → ℝ) := Set.pi Set.univ (fun i ↦ Set.Ioi (fs i xStar))
    have hp0_memV : p0 ∈ V := by
      simp [p0, V]
    have hV_open : IsOpen V := by
      refine isOpen_set_pi Set.finite_univ ?_
      intro i hi
      exact isOpen_Ioi
    have hV_subset : V ⊆ U := by
      intro p hp
      refine ⟨xStar, xStar.property, ?_⟩
      intro i
      exact (Set.mem_pi.mp hp i (by simp)).le
    refine ⟨p0, mem_interior_iff_mem_nhds.2 ?_⟩
    exact Filter.mem_of_superset (hV_open.mem_nhds hp0_memV) hV_subset
  have hdStar_not_mem_interior : (fun _ ↦ fStar) ∉ interior U := by
    -- A full neighborhood inside `U` would contain a strictly smaller constant vector, violating minimality.
    intro hdStar_int
    rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hdStar_int) with ⟨ε, hε, hεball⟩
    let pDown : ι → ℝ := fun _ ↦ fStar - ε / 2
    have hpDown_dist : dist pDown (fun _ ↦ fStar) < ε := by
      rw [dist_pi_lt_iff hε]
      intro i
      simpa [pDown, abs_of_pos hε] using (show ε / 2 < ε by linarith)
    have hpDown_memU : pDown ∈ U := interior_subset (hεball hpDown_dist)
    rcases hpDown_memU with ⟨x, hxQ, hx⟩
    have hxle : maxTypeObjective fs x ≤ fStar - ε / 2 := by
      exact (maxTypeObjective_le_iff fs x (fStar - ε / 2)).2 fun i ↦ by
        simpa [pDown] using hx i
    have hxlt : maxTypeObjective fs x < fStar := by
      linarith
    rw [isMinOn_univ_iff] at hxStarMin
    exact (not_lt_of_ge (hxStarMin ⟨x, hxQ⟩)) hxlt
  exact ⟨hU_convex, hdStar_mem, hU_int_nonempty, hdStar_not_mem_interior⟩

/- Corollary 3.1.2.1 lies in the chapter's convex-analysis/minimax-linearization domain.

Relevant owner-style declarations sampled in this domain:
- `ClosedConvexOn` from `Definition_3_1_1_5`, the chapter owner for closed convexity on a
  feasible set
- `maxTypeObjective` and `maxTypeObjective_apply` from `Chap02/Lemma_2_18`, the project owner for
  the finite maximum of a nonempty real-valued family
- `constrainedSublevelSet` from `Definition_3_3`, the chapter owner for bounded feasible
  sublevel families of `WithTop ℝ`-valued objectives
- `exists_minimax_parameter_of_bounded_constrainedSublevelSets` from `Theorem_3_1_2_6`, the
  two-function owner theorem used by the recursive proof strategy
- `StdSimplex`, `ConvexSpace.convexCombination`, and the bridge theorem
  `StdSimplex.convexCombination_map_eq_sum` from `Definition_3_1_1_4`, the chapter's canonical
  simplex packaging for finite convex combinations on arbitrary finite index types

Best owner abstraction:
- source-facing: this finite-family minimax-linearization theorem
- core/canonical: `maxTypeObjective fs` for the finite maximum, the bounded feasible sublevel
  owner `constrainedSublevelSet Q (fun x ↦ ((maxTypeObjective fs x : ℝ) : WithTop ℝ)) α`, and
  `StdSimplex ℝ ι` for the coefficient data
- bridge/view: the recursive reduction to the two-function owner theorem
  `exists_minimax_parameter_of_bounded_constrainedSublevelSets`, together with the textbook
  weighted objective `∑ i, coeffs.weights i * fs i x`, recovered from the simplex owner by
  `StdSimplex.convexCombination_map_eq_sum`

Primitive data:
- a nonempty finite family `fs : ι → E → ℝ`
- closed convexity of each component on `Q`
- boundedness of the constrained sublevel sets of the canonical `WithTop` lift of the owner
  maximum `maxTypeObjective fs`

Derived API:
- the owner finite maximum `maxTypeObjective fs`
- the simplex coefficient vector `coeffs : StdSimplex ℝ ι`
- the textbook weighted objective `∑ i, coeffs.weights i * fs i x`

The theorem is genuinely source-facing and not a bridge to an earlier m-ary owner theorem, but its
ambient space and coefficient data are kept at the chapter's canonical owner level: an arbitrary
proper real normed space `E` and the simplex owner type `StdSimplex ℝ ι`, rather than the
over-concrete textbook presentation `EuclideanSpace ℝ (Fin n)` with indices `Fin m`. -/

/-- Helper for Corollary 3.1.2.1: a supporting functional on the upper image has nonnegative
coordinate coefficients, and those coefficients have positive total mass. -/
theorem supporting_functional_coordinates_nonnegative
    [DecidableEq ι]
    {Q : Set E} {fs : ι → E → ℝ} (xStar : Q)
    {g : StrongDual ℝ (ι → ℝ)} (hg_ne : g ≠ 0)
    (hg_support :
      ∀ p : ι → ℝ, (∃ x ∈ Q, ∀ i, fs i x ≤ p i) →
        g (fun _ ↦ maxTypeObjective fs xStar) ≤ g p) :
    (∀ i, 0 ≤ g (Pi.single i 1)) ∧ 0 < ∑ i, g (Pi.single i 1) := by
  classical
  have hcoord_nonneg : ∀ i, 0 ≤ g (Pi.single i 1) := by
    intro i
    let dStar : ι → ℝ := fun _ ↦ maxTypeObjective fs xStar
    let pShift : ι → ℝ := dStar + Pi.single i 1
    have hpShift_mem : ∃ x ∈ Q, ∀ j, fs j x ≤ pShift j := by
      refine ⟨xStar, xStar.property, ?_⟩
      intro j
      by_cases hij : j = i
      · have hjle :
            fs j xStar ≤ maxTypeObjective fs xStar := by
          exact (maxTypeObjective_le_iff fs xStar (maxTypeObjective fs xStar)).mp le_rfl j
        have hjle' : fs j xStar ≤ maxTypeObjective fs xStar + 1 := by
          linarith
        simpa [pShift, dStar, Pi.single_apply, hij] using hjle'
      · have hjle :
            fs j xStar ≤ maxTypeObjective fs xStar := by
          exact (maxTypeObjective_le_iff fs xStar (maxTypeObjective fs xStar)).mp le_rfl j
        simpa [pShift, dStar, Pi.single_eq_of_ne hij] using hjle
    have hineq := hg_support pShift hpShift_mem
    -- The shifted feasible point changes only the `i`-th coordinate, so support monotonicity
    -- forces the `i`-th coefficient to be nonnegative.
    rw [show pShift = dStar + Pi.single i 1 by rfl, map_add] at hineq
    linarith
  refine ⟨hcoord_nonneg, ?_⟩
  by_contra hsum_nonpos
  have hsum_eq_zero : ∑ i, g (Pi.single i 1) = 0 := by
    have hsum_nonneg : 0 ≤ ∑ i, g (Pi.single i 1) :=
      Finset.sum_nonneg fun i hi ↦ hcoord_nonneg i
    linarith
  have hcoord_zero :
      ∀ i, g (Pi.single i 1) = 0 := by
    intro i
    exact
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ hcoord_nonneg j)).1 hsum_eq_zero i (by simp)
  have hg_zero : g = 0 := by
    -- Vanishing on the coordinate vectors forces vanishing on every point of the finite product.
    apply ContinuousLinearMap.ext
    intro z
    rw [strongDual_apply_fintype g z]
    simp [hcoord_zero]
  exact hg_ne hg_zero

/-- Helper for Corollary 3.1.2.1: after normalizing the supporting-functional coordinates, the
resulting coefficient family gives a global lower bound for the weighted objective. -/
theorem supporting_functional_weighted_lower_bound
    [DecidableEq ι]
    {Q : Set E} {fs : ι → E → ℝ} (xStar : Q)
    {g : StrongDual ℝ (ι → ℝ)}
    (hg_support :
      ∀ p : ι → ℝ, (∃ x ∈ Q, ∀ i, fs i x ≤ p i) →
        g (fun _ ↦ maxTypeObjective fs xStar) ≤ g p)
    (hσ_pos : 0 < ∑ i, g (Pi.single i 1)) :
    ∀ x : Q,
      maxTypeObjective fs xStar ≤
        ∑ i, ((g (Pi.single i 1)) / (∑ j, g (Pi.single j 1))) * fs i x := by
  classical
  intro x
  let dStar : ι → ℝ := fun _ ↦ maxTypeObjective fs xStar
  have hxU : ∃ y ∈ Q, ∀ i, fs i y ≤ (fun j ↦ fs j x) i := by
    refine ⟨x, x.property, ?_⟩
    intro i
    exact le_rfl
  have hineq := hg_support (fun i ↦ fs i x) hxU
  have hdStar_eval :
      g dStar =
        (∑ i, g (Pi.single i 1)) * maxTypeObjective fs xStar := by
    calc
      g dStar = ∑ i, dStar i * g (Pi.single i 1) := strongDual_apply_fintype g dStar
      _ = ∑ i, maxTypeObjective fs xStar * g (Pi.single i 1) := by simp [dStar]
      _ = (∑ i, g (Pi.single i 1)) * maxTypeObjective fs xStar := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        ring
  have hx_eval :
      g (fun i ↦ fs i x) = ∑ i, fs i x * g (Pi.single i 1) := by
    simpa using (strongDual_apply_fintype g (fun i ↦ fs i x))
  have hmul :
      (∑ i, g (Pi.single i 1)) * maxTypeObjective fs xStar ≤
        (∑ i, g (Pi.single i 1)) *
          ∑ i, (g (Pi.single i 1) / ∑ j, g (Pi.single j 1)) * fs i x := by
    -- Route correction: divide only once after rewriting both evaluations into coordinate sums.
    calc
      (∑ i, g (Pi.single i 1)) * maxTypeObjective fs xStar = g dStar := by
        rw [hdStar_eval]
      _ ≤ g (fun i ↦ fs i x) := hineq
      _ = ∑ i, fs i x * g (Pi.single i 1) := hx_eval
      _ = (∑ i, g (Pi.single i 1)) *
            ∑ i, (g (Pi.single i 1) / ∑ j, g (Pi.single j 1)) * fs i x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        field_simp [hσ_pos.ne']
  have hfinal :
      maxTypeObjective fs xStar ≤
        ∑ i, (g (Pi.single i 1) / ∑ j, g (Pi.single j 1)) * fs i x :=
    (mul_le_mul_iff_of_pos_left hσ_pos).mp hmul
  simpa using hfinal

/-- Helper for Corollary 3.1.2.1: the supporting functional at a minimizer produces simplex
coefficients whose weighted objective has the same attained value at that minimizer. -/
theorem supporting_coeffs_of_familyMaximum_minimizer
    [DecidableEq ι]
    {Q : Set E} {fs : ι → E → ℝ} (xStar : Q)
    (hfs : ∀ i, ClosedConvexOn Q (fun x ↦ (fs i x : WithTop ℝ)))
    (hxStarMin : IsMinOn (fun x : Q ↦ maxTypeObjective fs x) Set.univ xStar) :
    ∃ coeffs : StdSimplex ℝ ι,
      (∀ x : Q, maxTypeObjective fs xStar ≤ ∑ i, coeffs.weights i * fs i x) ∧
      ∑ i, coeffs.weights i * fs i xStar = maxTypeObjective fs xStar := by
  classical
  let fStar : ℝ := maxTypeObjective fs xStar
  let U : Set (ι → ℝ) := {p | ∃ x ∈ Q, ∀ i, fs i x ≤ p i}
  have hboundary :
      Convex ℝ U ∧
        (fun _ ↦ fStar) ∈ U ∧
        (interior U).Nonempty ∧
        (fun _ ↦ fStar) ∉ interior U := by
    simpa [fStar, U] using
      (upperImage_boundary_of_familyMaximum_minimizer xStar hfs hxStarMin)
  rcases hboundary with ⟨hU_convex, hdStar_memU, hU_int_nonempty, hdStar_not_mem_interior⟩
  obtain ⟨f, hf_ne, hf_support⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point hU_convex hdStar_not_mem_interior
      hU_int_nonempty
  let g : StrongDual ℝ (ι → ℝ) := -f
  have hg_ne : g ≠ 0 := by
    intro hg_zero
    exact hf_ne (by simpa [g] using hg_zero)
  have hg_support :
      ∀ p : ι → ℝ, (∃ x ∈ Q, ∀ i, fs i x ≤ p i) → g (fun _ ↦ fStar) ≤ g p := by
    intro p hp
    have hpU : p ∈ U := hp
    -- Negating the separating functional turns the boundary support inequality into a lower bound.
    simpa [g, fStar] using neg_le_neg (hf_support p hpU)
  obtain ⟨hcoord_nonneg, hσ_pos⟩ :=
    supporting_functional_coordinates_nonnegative xStar hg_ne hg_support
  let coeffFn : ι → ℝ := fun i ↦ g (Pi.single i 1) / ∑ j, g (Pi.single j 1)
  have hcoeff_nonneg : ∀ i, 0 ≤ coeffFn i := by
    intro i
    exact div_nonneg (hcoord_nonneg i) hσ_pos.le
  have hcoeff_sum : ∑ i, coeffFn i = 1 := by
    -- The normalized coordinate weights sum to one by construction.
    rw [show (∑ i, coeffFn i) = (∑ i, g (Pi.single i 1)) / (∑ j, g (Pi.single j 1)) by
      simp [coeffFn, Finset.sum_div]]
    field_simp [hσ_pos.ne']
  let coeffs : StdSimplex ℝ ι :=
    ⟨Finsupp.equivFunOnFinite.symm coeffFn,
      by simpa [coeffFn] using hcoeff_nonneg,
      by
        simpa [coeffFn] using (Finsupp.equivFunOnFinite_symm_sum coeffFn).trans hcoeff_sum⟩
  have hweighted_lower :
      ∀ x : Q, fStar ≤ ∑ i, coeffs.weights i * fs i x := by
    -- The normalized support inequality gives the lower bound for every feasible point.
    intro x
    simpa [coeffs, coeffFn, fStar] using
      (supporting_functional_weighted_lower_bound xStar hg_support hσ_pos x)
  have hweights_sum : ∑ i, coeffs.weights i = 1 := by
    simpa [Finsupp.sum_fintype] using coeffs.total
  have hweighted_xStar_le : ∑ i, coeffs.weights i * fs i xStar ≤ fStar := by
    -- Each component value at the minimizer is bounded above by the family maximum.
    calc
      ∑ i, coeffs.weights i * fs i xStar ≤ ∑ i, coeffs.weights i * fStar := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        exact mul_le_mul_of_nonneg_left
          ((maxTypeObjective_le_iff fs xStar fStar).mp le_rfl i)
          (coeffs.nonneg i)
      _ = fStar := by
        rw [← Finset.sum_mul, hweights_sum, one_mul]
  have hweighted_xStar_eq : ∑ i, coeffs.weights i * fs i xStar = fStar := by
    exact le_antisymm hweighted_xStar_le (hweighted_lower xStar)
  exact ⟨coeffs, hweighted_lower, by simpa [fStar] using hweighted_xStar_eq⟩

/-- Corollary 3.1.2.1: if `f₁, …, f_m` are closed convex real-valued functions on `Q` and every
constrained level set of their finite pointwise maximum is bounded, then there exists a
coefficient vector in the standard simplex `StdSimplex ℝ ι` whose canonical convex
combination of the family values has the same constrained minimum value as that finite maximum; in
Lean the boundedness hypothesis is expressed through the chapter owner
`constrainedSublevelSet Q (fun x ↦ ((maxTypeObjective fs x : ℝ) : WithTop ℝ)) α`, and the
conclusion is recorded as an equality of `EReal` infima over the subtype `Q` between
`maxTypeObjective fs` and the textbook simplex-weighted objective
`fun x ↦ ∑ i, coeffs.weights i * fs i x`. This weighted formula is the chapter bridge view of the
canonical simplex combination supplied by `StdSimplex.convexCombination_map_eq_sum`, and the
textbook `ℝⁿ` / `m`-indexed statement is recovered by specializing to
`E = EuclideanSpace ℝ (Fin n)` and `ι = Fin m`, using the canonical proper-space instance on that
finite-dimensional model. -/
-- Route correction: the naive tail-max recursion does not preserve the bounded-sublevel
-- hypothesis on the residual maxima. The verified route now first constructs a primal minimizer
-- for `maxTypeObjective fs`, then proves that the associated upper image in `ι → ℝ` is convex
-- with nonempty interior and has the minimizing diagonal point on its boundary. The remaining
-- blocker is to turn the supporting functional from Hahn-Banach into normalized simplex weights.
theorem exists_stdSimplex_minimax_linearization_of_bounded_familyMaximumSublevelSets
    {Q : Set E} {fs : ι → E → ℝ}
    (hfs : ∀ i, ClosedConvexOn Q (fun x ↦ (fs i x : WithTop ℝ)))
    (hbounded :
      ∀ α : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet Q (fun x ↦ ((maxTypeObjective fs x : ℝ) : WithTop ℝ)) α)) :
    ∃ coeffs : StdSimplex ℝ ι,
      sInf (Set.range fun x : Q ↦ (maxTypeObjective fs x : EReal)) =
        sInf (Set.range fun x : Q ↦
          ((∑ i, coeffs.weights i * fs i x : ℝ) : EReal)) := by
  classical
  rcases Q.eq_empty_or_nonempty with rfl | hQ_nonempty
  · let coeffs : StdSimplex ℝ ι := StdSimplex.single (Classical.choice ‹Nonempty ι›)
    have hrange_max :
        Set.range (fun x : (∅ : Set E) ↦ (maxTypeObjective fs x : EReal)) = ∅ := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact x.property.elim
      · simp
    have hrange_weighted :
        Set.range (fun x : (∅ : Set E) ↦
          ((∑ i, coeffs.weights i * fs i x : ℝ) : EReal)) = ∅ := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact x.property.elim
      · simp
    refine ⟨coeffs, ?_⟩
    rw [hrange_max, hrange_weighted]
  · obtain ⟨xStar, hxStarMin⟩ :=
      exists_isMinOn_familyMaximum_of_bounded_sublevels hfs hbounded hQ_nonempty
    obtain ⟨coeffs, hweighted_lower, hweighted_xStar_eq⟩ :=
      supporting_coeffs_of_familyMaximum_minimizer xStar hfs hxStarMin
    let fStar : ℝ := maxTypeObjective fs xStar
    have hweighted_min :
        IsMinOn (fun x : Q ↦ ∑ i, coeffs.weights i * fs i x) Set.univ xStar := by
      -- The weighted objective is globally bounded below by the attained value at `xStar`.
      rw [isMinOn_univ_iff]
      intro x
      simpa [hweighted_xStar_eq] using hweighted_lower x
    have hsInf_max :
        sInf (Set.range fun x : Q ↦ (maxTypeObjective fs x : EReal)) = (fStar : EReal) := by
      -- The primal minimizer rewrites the infimum of the family maximum to its attained value.
      have hopt :
          (SetConstrainedMinimizationProblem.unconstrained
            (fun x : Q ↦ maxTypeObjective fs x)).optimalValue = (fStar : EReal) := by
        simpa [fStar] using
          (SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn
            (problem := SetConstrainedMinimizationProblem.unconstrained
              (fun x : Q ↦ maxTypeObjective fs x))
            (x := xStar) (by simp) hxStarMin)
      simpa [SetConstrainedMinimizationProblem.optimalValue] using hopt
    have hsInf_weighted :
        sInf (Set.range fun x : Q ↦ ((∑ i, coeffs.weights i * fs i x : ℝ) : EReal)) =
          (fStar : EReal) := by
      -- The same attained-value rewrite applies to the supported weighted objective.
      have hopt :
          (SetConstrainedMinimizationProblem.unconstrained
            (fun x : Q ↦ ∑ i, coeffs.weights i * fs i x)).optimalValue =
              (((∑ i, coeffs.weights i * fs i xStar : ℝ) : EReal)) := by
        simpa using
          (SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn
            (problem := SetConstrainedMinimizationProblem.unconstrained
              (fun x : Q ↦ ∑ i, coeffs.weights i * fs i x))
            (x := xStar) (by simp) hweighted_min)
      calc
        sInf (Set.range fun x : Q ↦ ((∑ i, coeffs.weights i * fs i x : ℝ) : EReal))
            = (SetConstrainedMinimizationProblem.unconstrained
                (fun x : Q ↦ ∑ i, coeffs.weights i * fs i x)).optimalValue := by
                  simp [SetConstrainedMinimizationProblem.optimalValue]
        _ = (((∑ i, coeffs.weights i * fs i xStar : ℝ) : EReal)) := hopt
        _ = (fStar : EReal) := by
          exact_mod_cast hweighted_xStar_eq
    exact ⟨coeffs, hsInf_max.trans hsInf_weighted.symm⟩

end

/-! ### Definition_3_1_2_1 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 3.1.2.1 is a `bridge/view` recall in the chapter's Fenchel-conjugacy domain.

Primary domain:
- Fenchel conjugates of `ℝ ∪ {+∞}`-valued functions on real inner-product spaces.

Sampled owner-style declarations:
- project `fenchelConjugate`
- project `fenchelConjugate_apply`
- mathlib `innerₗ`
- mathlib `innerₗ_apply_apply`

Best owner abstraction:
- the source-facing owner `fenchelDual`

Primitive data:
- `f : E → WithTop ℝ`

Derived API:
- the source-facing notation `f⋆`
- the definitional supremum formula `fenchelDual_apply`

Source/core/bridge triage:
- source-facing: the textbook Fenchel conjugate for `ℝ ∪ {+∞}`-valued functions
- core/canonical: `fenchelConjugate`
- bridge/view: the canonical coercion `((↑) : WithTop ℝ → EReal)` together with
  evaluation at `innerₗ E s`

Definition 3.1.2.1 is source-facing only after specializing the dual-space owner to the
`WithTop ℝ` setting and then viewing vectors as dual functionals through `innerₗ`. The textbook
`ℝⁿ` statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. This file therefore owns the
reusable source-facing bridge `fenchelDual`, equips it with the textbook notation `f⋆`, and
derives the supremum formula from the canonical owner evaluation theorem.
-/

/-- Definition 3.1.2.1: the Fenchel dual of an `ℝ ∪ {+∞}`-valued function on a real inner-product
space, obtained by evaluating `fenchelConjugate` along the Riesz map `innerₗ`. -/
abbrev fenchelDual (f : E → WithTop ℝ) : E → EReal :=
  fenchelConjugate (withTopToEReal ∘ f) ∘ innerₗ E

/- Lean spelling `f⋆` for the source-facing Fenchel dual `fenchelDual f`. -/
scoped[ConvexAnalysis] postfix:max "⋆" => fenchelDual

open scoped ConvexAnalysis

/-- Evaluating `fenchelDual f` gives the textbook supremum formula. -/
theorem fenchelDual_apply (f : E → WithTop ℝ) (s : E) :
    (f⋆) s =
      ⨆ x : E, (inner ℝ s x : EReal) - withTopToEReal (f x) := by
  rfl

end

/-! ### Definition_3_1_2_2 (from Chap03) -/
universe u

open scoped SupportFunction

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 3.1.2.2 is a recall-only item in the chapter's support-function domain.

Primary domain:
- support functions of subsets of a real inner-product space.

Sampled owner-style declarations:
- `supportFunction` from `LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_9`
- `supportFunction_apply`
- `supportFunction_convexHull_eq`

Best owner abstraction:
- the chapter source-facing owner declaration `supportFunction`.

Primitive data:
- none; this is a recall-only item.

Derived API:
- the owner declaration `supportFunction`
- the defining bridge `supportFunction_apply`

Source/core/bridge triage:
- source-facing: the textbook support function of a set
- core/canonical: the owner declaration `supportFunction`
- bridge/view: the defining evaluation lemma `supportFunction_apply`

No exact mathlib owner for this `EReal`-valued support function was found in the sampled domain,
so this file recalls the chapter owner declarations directly instead of keeping a parallel local
copy of the same supremum construction. The textbook `ℝⁿ` statement is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/

recall supportFunction

/- The defining evaluation formula is recalled through the canonical companion theorem. -/
recall supportFunction_apply

/-! ### Definition_3_1_2_3 (from Chap03) -/
universe u

variable {Q : Type u}

/- Definition 3.1.2.3 lies in the chapter's two-function minimax-linearization domain.

Sampled owner-style declarations:
- mathlib `unitInterval`, the canonical owner of the parameter set `[0, 1]`
- mathlib `AffineMap.lineMap`, the canonical affine-combination owner
- mathlib `AffineMap.lineMap_apply_ring`, the textbook scalar formula
- mathlib `sInf`, the canonical infimum owner for the corresponding `EReal` value sets

Best owner abstraction:
- source-facing owner: `IsMinimaxLinearizationParameter`

Primitive data:
- a common domain `Q`
- two real-valued functions `f₁ f₂ : Q → ℝ`
- a parameter `lam : unitInterval`

Derived API:
- the companion specification theorem `isMinimaxLinearizationParameter_iff`

Source/core/bridge triage:
- source-facing: the textbook minimax-linearization parameter condition
- core/canonical: `unitInterval`, `AffineMap.lineMap`, and `sInf`
- bridge/view: the displayed `EReal`-infimum equality recorded by the companion theorem

No earlier chapter owner packages this notion more canonically, so this file keeps the
source-facing predicate as the owner and reuses mathlib's affine-combination surface inside that
owner instead of duplicating the scalar formula directly. -/

/-- Definition 3.1.2.3: a minimax linearization parameter for `f₁, f₂ : Q → ℝ` is a scalar
`lam ∈ [0, 1]` such that the extended-real infimum of the pointwise maximum
`x ↦ max (f₁ x) (f₂ x)` equals the extended-real infimum of the affine combination
`x ↦ lam * f₁ x + (1 - lam) * f₂ x`. -/
def IsMinimaxLinearizationParameter
    (f₁ f₂ : Q → ℝ) (lam : unitInterval) : Prop :=
  sInf (Set.range fun x ↦ ((max (f₁ x) (f₂ x) : ℝ) : EReal)) =
    sInf (Set.range fun x ↦ ((AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ) : ℝ) : EReal))

/-- Unfolding the minimax-linearization predicate gives the displayed equality of extended-real
infima. -/
-- Proof sketch: this is the defining specification of `IsMinimaxLinearizationParameter`, so the
-- result follows by unfolding the definition.
@[simp] theorem isMinimaxLinearizationParameter_iff
    (f₁ f₂ : Q → ℝ) (lam : unitInterval) :
    IsMinimaxLinearizationParameter f₁ f₂ lam ↔
      sInf (Set.range fun x ↦ ((max (f₁ x) (f₂ x) : ℝ) : EReal)) =
        sInf (Set.range fun x ↦ ((AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ) : ℝ) : EReal)) :=
  Iff.rfl

/-! ### Lemma_3_1_2 (from Chap03) -/
universe u

section

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/- Lemma 3.1.2 is a source-facing recall in the chapter's `WithTop`-valued convex-analysis
domain.

Primary domain:
- restriction of a closed convex extended-real-valued function to a closed convex subset.

Sampled owner-style declarations in this domain:
- `ClosedConvexOn` from `Definition_3_1_1_5`
- `ClosedConvexOn.restrict` from `Definition_3_1_1_5`
- `ClosedConvexOn.subset_withTopEffectiveDomain`
- `ClosedConvexOn.isClosed_constrainedEpigraph`
- `ClosedConvexOn.convex_constrainedEpigraph`

Best owner abstraction:
- `ClosedConvexOn`

Primitive data:
- the owner witness `hf : ClosedConvexOn Q f`
- the subset, closedness, and convexity data for `Q₁ ⊆ Q`

Derived API:
- the canonical owner theorem `ClosedConvexOn.restrict`

Source/core/bridge triage:
- source-facing: `ClosedConvexOn.restrict`
- core/canonical: `ClosedConvexOn`
- bridge/view: `constrainedEpigraph`, together with the closed/convex cylinder intersection proof
  internalized in the owner theorem

This file is recall-only: the owner theorem now lives where `ClosedConvexOn` itself is defined,
so the later chapter item reuses that exact owner theorem instead of introducing a duplicate
specialized copy.
-/

recall ClosedConvexOn.restrict
    {f : X → WithTop ℝ} {Q Q₁ : Set X}
    (hf : ClosedConvexOn Q f)
    (hQ₁_closed : IsClosed Q₁)
    (hQ₁_convex : Convex ℝ Q₁)
    (hQ₁Q : Q₁ ⊆ Q) :
    ClosedConvexOn Q₁ f

end

/-! ### Lemma_3_1_2_1 (from Chap03) -/
/- Lemma 3.1.2.1 lies in the chapter's support-function domain.

Primary domain:
- support functions of subsets of a real inner-product space and their behavior under convex hulls
  of two-set unions.

Sampled owner-style declarations:
- `supportFunction` from `Definition_3_9`
- `supportFunction_apply`
- `supportFunction_convexHull_union_eq_max` from `Lemma_3_3`
- the duplicate local theorem shell in `Lemma_3_1_3`

Best owner abstraction:
- the exact upstream theorem `supportFunction_convexHull_union_eq_max` from `Lemma_3_3`, stated at
  the same ambient owner level as `supportFunction`

Primitive data:
- two sets `Q₁ Q₂ : Set E`
- a direction `x : E`

Derived API:
- the support function of `convexHull ℝ (Q₁ ∪ Q₂)`
- its identification with the pointwise maximum of the two support functions

Source/core/bridge triage:
- source-facing: this two-set convex-hull support-function identity
- core/canonical: the exact upstream theorem `supportFunction_convexHull_union_eq_max`
- bridge/view: none needed; the target interface already exists upstream

This file previously repeated the exact upstream theorem already present in `Lemma_3_3` and again
in `Lemma_3_1_3`. Since the project already has the precise owner interface, this numbered item is
now a direct recall rather than a third parallel theorem shell. The textbook `ℝⁿ` statement is a
specialization of that generalized owner theorem.
-/

recall supportFunction_convexHull_union_eq_max

/-! ### Lemma_3_1_2_2 (from Chap03) -/
/- Lemma 3.1.2.2 is a source-facing recall in the chapter's univariate closed-convex continuity
domain.

Primary domain:
- relative continuity of univariate closed convex `WithTop ℝ`-valued functions on their effective
  domain.

Sampled owner-style declarations:
- `ClosedConvexFunction` from `Definition_3_1_1_5`
- `ClosedConvexFunction.continuousOn_effectiveDomain_one_dimensional`
- mathlib `ConvexOn.continuousOn`
- mathlib `ConvexOn.continuousOn_interior`

Best owner abstraction:
- the chapter owner `ClosedConvexFunction`, together with its exact univariate continuity theorem
  `ClosedConvexFunction.continuousOn_effectiveDomain_one_dimensional`

Primitive data:
- the effective domain `dom f`
- the constrained-epigraph data packaged by `ClosedConvexFunction f`

Derived API:
- `ClosedConvexFunction.continuousOn_effectiveDomain_one_dimensional`

Source/core/bridge triage:
- source-facing: the one-dimensional continuity consequence stated in this lemma
- core/canonical: `ClosedConvexFunction`
- bridge/view: `dom f`, `withTopRealPart f`, and the ambient `ConvexOn` continuity lemmas sampled
  for domain style

The previous file kept a second public theorem
`ClosedConvexFunction.continuousOn_effectiveDomain_univariate` with the exact same interface as
the upstream owner theorem. That shell carried no new mathematics, so this file now recalls the
canonical chapter theorem directly instead of maintaining a parallel local copy. -/

recall ClosedConvexFunction.continuousOn_effectiveDomain_one_dimensional
