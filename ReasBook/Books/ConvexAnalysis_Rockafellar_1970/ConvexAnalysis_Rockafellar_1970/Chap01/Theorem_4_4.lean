import ConvexAnalysis_Rockafellar_1970.Chap01.DerivConvexGeneric

-- Declarations for this item will be appended below by the statement pipeline.

section

open Set
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-
Source/core/bridge triage:
- `source-facing`: Theorem 4.4 identifies convexity of a scalar-valued function on an open
  interval `(α, β)` with pointwise nonnegativity of its second derivative on that interval.
- `core/canonical`: the owner abstraction is first stated on an arbitrary open convex set
  `s : Set 𝕜`; the primary theorem surface is intrinsic/relative via
  `derivWithin (derivWithin f s) s`, with ambient `deriv^[2]` as an open-set bridge.
- `bridge/view`: the forward implication uses the owner-side monotonicity theorem
  `ConvexOn.monotoneOn_deriv`; the scalar-generic reverse implication uses
  `ConvexAnalysis.convexOn_of_deriv2_nonneg'`.
- Primitive data vs derived API: the primitive inputs are the interval endpoints `α, β` and the
  function `f : 𝕜 → 𝕜` together with differentiability of `f` and `deriv f` on `Ioo α β`;
  convexity on `Ioo α β` and the pointwise sign condition on
  `derivWithin (derivWithin f (Ioo α β)) (Ioo α β)` are the canonical equivalent views.
- Domain-style sampling: this item is aligned with
  `ConvexAnalysis.convexOn_of_deriv2_nonneg'`,
  `ConvexOn.monotoneOn_deriv`, `MonotoneOn.derivWithin_nonneg`, and
  `DifferentiableOn`.
- Layer target: mixed `core/canonical` plus `source-facing`; the theorem surface is scalar-general
  over ordered normed fields with the order completeness needed for the mean value theorem.
-/

/- Primitive local bridge: if `s` is a neighborhood of `x`, the intrinsic second derivative
agrees at `x` with ambient `deriv^[2]`. -/
theorem derivWithin2_eq_deriv2_of_mem_nhds {s : Set 𝕜} {f : 𝕜 → 𝕜} {x : 𝕜}
    (hs_nhds : s ∈ 𝓝 x) :
    derivWithin (derivWithin f s) s x = deriv^[2] f x := by
  rcases mem_nhds_iff.mp hs_nhds with ⟨t, ht_sub, ht_open, hxt⟩
  have ht_nhds : t ∈ 𝓝 x := ht_open.mem_nhds hxt
  have hderivWithin_eq_deriv : derivWithin f s =ᶠ[𝓝 x] deriv f := by
    filter_upwards [ht_nhds] with y hy
    exact derivWithin_of_mem_nhds <|
      Filter.mem_of_superset (ht_open.mem_nhds hy) ht_sub
  calc
    derivWithin (derivWithin f s) s x = deriv (derivWithin f s) x :=
      derivWithin_of_mem_nhds hs_nhds
    _ = deriv (deriv f) x := hderivWithin_eq_deriv.deriv_eq
    _ = deriv^[2] f x := by simp [Function.iterate_succ_apply']

/- Open-set pointwise bridge, derived from the primitive local neighborhood form. -/
theorem IsOpen.derivWithin2_eq_deriv2 {s : Set 𝕜} {f : 𝕜 → 𝕜}
    (hs_open : IsOpen s) {x : 𝕜} (hx : x ∈ s) :
    derivWithin (derivWithin f s) s x = deriv^[2] f x :=
  derivWithin2_eq_deriv2_of_mem_nhds (hs_open.mem_nhds hx)

section OrderedDiff

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]

private lemma convexOn_derivWithin_le_slope_generic {s : Set 𝕜} {f : 𝕜 → 𝕜} {x y f' : 𝕜}
    (hconv : ConvexOn 𝕜 s f) (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y)
    (hf' : HasDerivWithinAt f f' s x) :
    f' ≤ slope f x y := by
  apply le_of_tendsto <| (hasDerivWithinAt_iff_tendsto_slope' (show x ∉ Ioi x by simp)).mp <|
    hf'.mono_of_mem_nhdsWithin <| hconv.1.ordConnected.mem_nhdsGT hx hy hxy
  simp_rw [eventually_nhdsWithin_iff, slope_def_field]
  filter_upwards [eventually_lt_nhds hxy] with t ht ht'
  refine hconv.secant_mono hx (?_ : t ∈ s) hy ht'.ne' hxy.ne' ht.le
  exact hconv.1.ordConnected.out hx hy ⟨ht'.le, ht.le⟩

private lemma convexOn_slope_le_derivWithin_generic {s : Set 𝕜} {f : 𝕜 → 𝕜} {x y f' : 𝕜}
    (hconv : ConvexOn 𝕜 s f) (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y)
    (hf' : HasDerivWithinAt f f' s y) :
    slope f x y ≤ f' := by
  apply ge_of_tendsto <| (hasDerivWithinAt_iff_tendsto_slope' (show y ∉ Iio y by simp)).mp <|
    hf'.mono_of_mem_nhdsWithin <| hconv.1.ordConnected.mem_nhdsLT hx hy hxy
  simp_rw [eventually_nhdsWithin_iff, slope_comm f x y, slope_def_field]
  filter_upwards [eventually_gt_nhds hxy] with t ht ht'
  refine hconv.secant_mono hy hx (?_ : t ∈ s) hxy.ne ht'.ne ht.le
  exact hconv.1.ordConnected.out hx hy ⟨ht.le, ht'.le⟩

private lemma convexOn_monotoneOn_derivWithin_generic {s : Set 𝕜} {f : 𝕜 → 𝕜}
    (hconv : ConvexOn 𝕜 s f) (hfd : DifferentiableOn 𝕜 f s) :
    MonotoneOn (derivWithin f s) s := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (convexOn_derivWithin_le_slope_generic hconv hx hy hxy' (hfd x hx).hasDerivWithinAt).trans
    (convexOn_slope_le_derivWithin_generic hconv hx hy hxy' (hfd y hy).hasDerivWithinAt)

/-- Intrinsic second-derivative monotonicity on a convex set: if `f` is convex and differentiable
on `s`, then the relative second derivative `derivWithin (derivWithin f s) s` is pointwise
nonnegative on `s`. -/
theorem ConvexOn.nonneg_derivWithin2 {s : Set 𝕜} {f : 𝕜 → 𝕜}
    (hconv : ConvexOn 𝕜 s f) (hfd : DifferentiableOn 𝕜 f s) :
    ∀ x ∈ s, 0 ≤ derivWithin (derivWithin f s) s x := by
  have hmono : MonotoneOn (derivWithin f s) s := convexOn_monotoneOn_derivWithin_generic hconv hfd
  intro x hx
  exact hmono.derivWithin_nonneg

/-- On an open set, the intrinsic second-derivative condition from
`ConvexOn.nonneg_derivWithin2` specializes to the ambient second derivative `deriv^[2]`. -/
theorem ConvexOn.nonneg_deriv2_of_isOpen {s : Set 𝕜} {f : 𝕜 → 𝕜}
    (hconv : ConvexOn 𝕜 s f) (hs_open : IsOpen s) (hfd : DifferentiableOn 𝕜 f s) :
    ∀ x ∈ s, 0 ≤ deriv^[2] f x := by
  have hmonoWithin : MonotoneOn (derivWithin f s) s :=
    convexOn_monotoneOn_derivWithin_generic hconv hfd
  have hmono : MonotoneOn (deriv f) s := by
    intro x hx y hy hxy
    rw [← derivWithin_of_isOpen hs_open hx, ← derivWithin_of_isOpen hs_open hy]
    exact hmonoWithin hx hy hxy
  intro x hx
  have hnonneg : 0 ≤ derivWithin (deriv f) s x := hmono.derivWithin_nonneg
  simpa [derivWithin_of_isOpen hs_open hx, Function.iterate_succ_apply'] using hnonneg

/-
On an open set, nonnegativity of the intrinsic second derivative is equivalent to
nonnegativity of the ambient second derivative.
-/
omit [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] in
theorem IsOpen.nonneg_derivWithin2_iff_nonneg_deriv2 {s : Set 𝕜} {f : 𝕜 → 𝕜}
    (hs_open : IsOpen s) :
    (∀ x ∈ s, 0 ≤ derivWithin (derivWithin f s) s x) ↔ ∀ x ∈ s, 0 ≤ deriv^[2] f x := by
  constructor <;> intro h x hx
  · simpa [derivWithin2_eq_deriv2_of_mem_nhds (f := f) (hs_open.mem_nhds hx)] using h x hx
  · simpa [derivWithin2_eq_deriv2_of_mem_nhds (f := f) (hs_open.mem_nhds hx)] using h x hx

end OrderedDiff

section OrderedConvex

variable [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
  [DenselyOrdered 𝕜]

/-- Open-set owner criterion at the intrinsic/relative layer: on an open convex set, a function
with `DifferentiableOn` hypotheses for both `f` and `deriv f` is convex iff
`derivWithin (derivWithin f s) s` is pointwise nonnegative. -/
theorem IsOpen.convexOn_iff_nonneg_derivWithin2 {s : Set 𝕜} {f : 𝕜 → 𝕜}
    (hs_open : IsOpen s) (hs_convex : Convex 𝕜 s)
    (hfd : DifferentiableOn 𝕜 f s) (hderiv : DifferentiableOn 𝕜 (deriv f) s) :
    ConvexOn 𝕜 s f ↔ ∀ x ∈ s, 0 ≤ derivWithin (derivWithin f s) s x := by
  constructor
  · intro hconv
    exact hconv.nonneg_derivWithin2 hfd
  · intro hnonneg
    have hnonneg_deriv2 : ∀ x ∈ s, 0 ≤ deriv^[2] f x := by
      simpa [hs_open.nonneg_derivWithin2_iff_nonneg_deriv2] using hnonneg
    exact ConvexAnalysis.convexOn_of_deriv2_nonneg'
      hs_convex hfd hderiv hnonneg_deriv2

/-- Open-set ambient bridge: the intrinsic owner criterion
`IsOpen.convexOn_iff_nonneg_derivWithin2` specializes to ambient `deriv^[2]`. -/
theorem IsOpen.convexOn_iff_nonneg_deriv2 {s : Set 𝕜} {f : 𝕜 → 𝕜}
    (hs_open : IsOpen s) (hs_convex : Convex 𝕜 s)
    (hfd : DifferentiableOn 𝕜 f s) (hderiv : DifferentiableOn 𝕜 (deriv f) s) :
    ConvexOn 𝕜 s f ↔ ∀ x ∈ s, 0 ≤ deriv^[2] f x := by
  simpa [hs_open.nonneg_derivWithin2_iff_nonneg_deriv2] using
    (hs_open.convexOn_iff_nonneg_derivWithin2 hs_convex hfd hderiv)

-- Proof sketch: apply the owner-level open-convex-set intrinsic criterion with `s = Ioo α β`.
/-- Theorem 4.4 at the intrinsic/relative owner layer: a twice differentiable scalar-valued
function on `(α, β)` is convex on that interval iff
`derivWithin (derivWithin f (Ioo α β)) (Ioo α β)` is pointwise nonnegative. -/
theorem convexOn_Ioo_iff_nonneg_derivWithin2 {α β : 𝕜} {f : 𝕜 → 𝕜}
    (hfd : DifferentiableOn 𝕜 f (Ioo α β))
    (hderiv : DifferentiableOn 𝕜 (deriv f) (Ioo α β)) :
    ConvexOn 𝕜 (Ioo α β) f ↔
      ∀ x ∈ Ioo α β, 0 ≤ derivWithin (derivWithin f (Ioo α β)) (Ioo α β) x := by
  simpa using
    (isOpen_Ioo.convexOn_iff_nonneg_derivWithin2 (convex_Ioo α β) hfd hderiv)

/-- Theorem 4.4 ambient bridge: on the open interval `(α, β)`, the intrinsic second-derivative
criterion is equivalent to pointwise nonnegativity of `deriv^[2]`. -/
theorem convexOn_Ioo_iff_nonneg_deriv2 {α β : 𝕜} {f : 𝕜 → 𝕜}
    (hfd : DifferentiableOn 𝕜 f (Ioo α β))
    (hderiv : DifferentiableOn 𝕜 (deriv f) (Ioo α β)) :
    ConvexOn 𝕜 (Ioo α β) f ↔ ∀ x ∈ Ioo α β, 0 ≤ deriv^[2] f x := by
  simpa using
    (isOpen_Ioo.convexOn_iff_nonneg_deriv2 (convex_Ioo α β) hfd hderiv)

end OrderedConvex

end
