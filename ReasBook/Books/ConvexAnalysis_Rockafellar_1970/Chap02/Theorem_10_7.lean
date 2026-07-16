import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_6
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8

-- Declarations for this item will be appended below by the statement pipeline.

section

open Function Set Metric
open scoped Rockafellar

universe u v w

variable {𝕜 : Type w} {E : Type u} {T : Type v}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [CompleteSpace 𝕜]
variable [ClosedIciTopology 𝕜] [ClosedIicTopology 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] [TopologicalSpace T]

variable (f : E → T → 𝕜) {C : Set E}
variable (hC_open : IsRelativelyOpen 𝕜 C)

variable (hf_convex : ∀ t, ConvexOn 𝕜 C (fun x ↦ f x t))

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 10.7 asserts joint continuity on `C × T` for a `𝕜`-valued family
  `f(x,t)` that is convex in the finite-dimensional normed variable and continuous in the
  topological parameter,
  together with the variant where continuity in `t` is only assumed on a dense subset of `C`.
- `core/canonical`: the owner abstractions are the chapter predicate `IsRelativelyOpen`, the
  sectionwise convexity predicate `∀ t, ConvexOn 𝕜 C (fun x ↦ f x t)`,
  the pointwise continuity predicate
  `Continuous`, the joint continuity predicate `ContinuousOn`, the Chapter 10 owner theorem
  `PointwiseBoundedOn.uniformlyBoundedOn_and_equiLipschitzOn`, and product continuity
  theorems `continuousOn_prod_of_continuousOn_lipschitzOnWith` and
  `continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith`.
- `bridge/view`: Rockafellar's “continuous on `C × T`” is rendered canonically as
  `ContinuousOn (Function.uncurry f) (C ×ˢ (Set.univ : Set T))`, while the source phrase
  “dense subset of `C`” is expressed by `C' ⊆ C` together with
  `C ⊆ intrinsicClosure 𝕜 C'`.

Domain-style sampling used here:
- `IsRelativelyOpen` from `Text_6_11`;
- `∀ t, ConvexOn 𝕜 C (fun x ↦ f x t)` for convexity of each `x`-section;
- `Continuous` and `ContinuousOn` for separate and joint continuity;
- `PointwiseBoundedOn.uniformlyBoundedOn_and_equiLipschitzOn` from Theorem 10.6 for
  the owner Lipschitz control on compact subsets;
- `continuousOn_prod_of_continuousOn_lipschitzOnWith` for the source-facing theorem when
  continuity in `t` is available on all of `C`;
- `continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith` for the canonical product
  continuity mechanism combining dense-fiber continuity with a common Lipschitz bound;
- `WeaklyLocallyCompactSpace` for the ambient spaces `E` and `T`, giving compact neighborhoods
  used with Theorem 10.6 to obtain local common Lipschitz control in `x`.

Primitive data vs derived API:
- primitive inputs: the relatively open set `C`, the topological parameter space `T`, the
  function `f`, the ambient finite-dimensional normed-space structure on `E`, the weak local
  compactness hypotheses on `E` and `T`, convexity of each section `x ↦ f x t`, and one of the
  two source continuity hypotheses in `t`;
- in the dense-subset variant, the additional primitive source data are theorem-level: a subset
  `C' ⊆ C` whose intrinsic closure contains `C`, together with continuity of each section `f x`
  on `T` for `x ∈ C'`;
- derived API: continuity of the uncurried map `(x,t) ↦ f x t` on `C × T`.

Layer target: the main labeled theorem stays `source-facing`, expressed directly with the canonical
owner predicates `ConvexOn`, `Continuous`, and `ContinuousOn`. The stronger dense-subset
variant is kept only as a companion generalization, since the original first sentence is the
source-facing statement of the theorem.
-/

include hC_open hf_convex

variable [WeaklyLocallyCompactSpace T]
variable [WeaklyLocallyCompactSpace E]

-- Proof sketch: for a fixed compact neighborhood `T₀` of `t₀`, the family `x ↦ f x t` indexed by
-- `t ∈ T₀` is pointwise bounded on `C'` because each `f x` is continuous on `T₀` for `x ∈ C'`,
-- and the inclusion `C' ⊆ C` keeps these bounded fibers inside the convex domain. Apply Theorem
-- 10.6 on a compact neighborhood of `x₀` intersected with the local relative-ball patch inside
-- `C` to obtain a common Lipschitz bound in the finite-dimensional normed variable over `𝕜`, then
-- use the canonical product theorem
-- `continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith` with the dense subset
-- `C' ⊆ C` to combine that bound with continuity in `t` along `C'` and conclude joint continuity
-- near `(x₀, t₀)`. Only compact neighborhoods of points of `E` and `T` are used, so the minimal
-- ambient compactness hypotheses are `WeaklyLocallyCompactSpace E` and
-- `WeaklyLocallyCompactSpace T`.
/-- Companion strengthening of Theorem 10.7: it is enough to assume continuity in `t` on a dense
subset of `C`. -/
theorem continuousOn_uncurry_of_convexOn_of_continuous_dense_subset
    (C' : Set E) (hC'_subset : C' ⊆ C) (hdense : C ⊆ intrinsicClosure 𝕜 C')
    (hf_cont : ∀ x ∈ C', Continuous (f x)) :
    ContinuousOn (uncurry f) (C ×ˢ univ) := by
  rw [_root_.continuousOn_iff]
  rintro ⟨x0, t0⟩ hx0t0 U hU hx0t0U
  have hx0 : x0 ∈ C := hx0t0.1
  have hx0ri : x0 ∈ ri[𝕜](C) := by
    simpa [hC_open] using hx0
  rcases
      (mem_ri_iff_mem_affineSpan_and_exists_pos_closedBall_inter_subset).1 hx0ri with
    ⟨hx0A, ε, hε, hεC⟩
  obtain ⟨Kx, hKxcompact, hKxnhds⟩ := exists_compact_mem_nhds x0
  obtain ⟨Vx, hVxKx, hVxopen, hx0Vx⟩ := _root_.mem_nhds_iff.mp hKxnhds
  obtain ⟨K, hKcompact, hKnhds⟩ := exists_compact_mem_nhds t0
  obtain ⟨V, hVK, hVopen, ht0V⟩ := mem_nhds_iff.mp hKnhds
  have ht0K : t0 ∈ K := mem_of_mem_nhds hKnhds
  let g : K → E → 𝕜 := fun t x ↦ f x t
  let S : Set E := Kx ∩ (closedBall x0 ε ∩ affineSpan 𝕜 C)
  let X : Set E := (Vx ∩ ball x0 ε) ∩ C
  let X' : Set E := (Vx ∩ ball x0 ε) ∩ C'
  have hcompactFiber {x : E} (hx : Continuous (f x)) :
      IsCompact (range fun t : K ↦ f x t) := by
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
    simpa using (isCompact_univ.image (hx.comp continuous_subtype_val))
  have hS_compact : IsCompact S := by
    dsimp [S]
    exact hKxcompact.inter_right
      (isClosed_closedBall.inter (affineSpan 𝕜 C).closed_of_finiteDimensional)
  have hS_subset : S ⊆ C := by
    intro x hx
    exact hεC hx.2
  have hupper :
      ∃ C'' ⊆ C, C ⊆ convexHull 𝕜 (intrinsicClosure 𝕜 C'') ∧
        ∀ x : C'', BddAbove (range fun t ↦ g t x) := by
    refine ⟨C', hC'_subset, ?_, ?_⟩
    · intro x hx
      exact subset_convexHull 𝕜 (intrinsicClosure 𝕜 C') (hdense hx)
    · intro x
      simpa [g] using (hcompactFiber (hf_cont x x.2)).bddAbove
  have hx0cl : x0 ∈ closure C' :=
    intrinsicClosure_subset_closure (hdense hx0)
  have hX'_nonempty : X'.Nonempty := by
    have hx0VxBall : x0 ∈ Vx ∩ ball x0 ε := ⟨hx0Vx, mem_ball_self hε⟩
    rcases (_root_.mem_closure_iff.mp hx0cl) (Vx ∩ ball x0 ε) (hVxopen.inter isOpen_ball)
      hx0VxBall with ⟨x1, hx1VxBall, hx1C'⟩
    exact ⟨x1, ⟨hx1VxBall, hx1C'⟩⟩
  rcases hX'_nonempty with ⟨x1, ⟨hx1VxBall, hx1C'⟩⟩
  have hlower : ∃ x : C, BddBelow (range fun t ↦ g t x) := by
    refine ⟨⟨x1, hC'_subset hx1C'⟩, ?_⟩
    simpa [g] using (hcompactFiber (hf_cont x1 hx1C')).bddBelow
  have hequi : EquiLipschitzOn g S :=
    (uniformlyBoundedOn_and_equiLipschitzOn_of_generating_upper_and_one_lower_bound
      (f := g) (C := C) (S := S)
      (hC_ri := hC_open) (hf_convex := fun t ↦ hf_convex t)
      (hS_compact := hS_compact) (hS_subset := hS_subset)
      (hupper := hupper) (hlower := hlower)).2
  rcases EquiLipschitzOn.exists_forall_lipschitzOnWith hequi with ⟨α, hα⟩
  have hX_subset_S : X ⊆ S := by
    intro x hx
    refine ⟨hVxKx hx.1.1, ?_⟩
    exact ⟨mem_closedBall.2 (le_of_lt hx.1.2), subset_affineSpan 𝕜 C hx.2⟩
  have hX'_subset : X' ⊆ X := by
    intro x hx
    exact ⟨hx.1, hC'_subset hx.2⟩
  have hX_dense : X ⊆ closure X' := by
    intro x hx
    rw [_root_.mem_closure_iff]
    intro o ho hxo
    have hxcl : x ∈ closure C' :=
      intrinsicClosure_subset_closure (hdense hx.2)
    have hoVxBall : IsOpen ((o ∩ Vx) ∩ ball x0 ε) := (ho.inter hVxopen).inter isOpen_ball
    have hxoVxBall : x ∈ ((o ∩ Vx) ∩ ball x0 ε) := ⟨⟨hxo, hx.1.1⟩, hx.1.2⟩
    rcases (_root_.mem_closure_iff.mp hxcl) ((o ∩ Vx) ∩ ball x0 ε) hoVxBall hxoVxBall with
      ⟨y, hyoVxBall, hyC'⟩
    exact ⟨y, hyoVxBall.1.1, ⟨⟨hyoVxBall.1.2, hyoVxBall.2⟩, hyC'⟩⟩
  have ha : ∀ x ∈ X', ContinuousOn (fun t ↦ f x t) K := by
    intro x hx
    exact (hf_cont x hx.2).continuousOn
  have hb : ∀ t ∈ K, LipschitzOnWith α (fun x ↦ f x t) X := by
    intro t ht
    simpa [g, X] using (hα ⟨t, ht⟩).mono hX_subset_S
  have hlocal : ContinuousOn (uncurry f) (X ×ˢ K) :=
    continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith
      (uncurry f) hX'_subset hX_dense α ha hb
  have hx0X : x0 ∈ X := ⟨⟨hx0Vx, mem_ball_self hε⟩, hx0⟩
  rcases
      (_root_.continuousOn_iff.mp hlocal) (x0, t0) ⟨hx0X, ht0K⟩ U hU hx0t0U
    with ⟨W, hWopen, hx0t0W, hWU⟩
  refine ⟨W ∩ ((Vx ∩ ball x0 ε) ×ˢ V), hWopen.inter ((hVxopen.inter isOpen_ball).prod hVopen),
    ?_, ?_⟩
  · exact ⟨hx0t0W, mem_prod.2 ⟨⟨hx0Vx, mem_ball_self hε⟩, ht0V⟩⟩
  · intro y hy
    have hyW : y ∈ W := hy.1.1
    have hyVxBall : y.1 ∈ Vx ∩ ball x0 ε := hy.1.2.1
    have hyV : y.2 ∈ V := hy.1.2.2
    have hyC : y.1 ∈ C := hy.2.1
    exact hWU ⟨hyW, ⟨⟨hyVxBall, hyC⟩, hVK hyV⟩⟩

/-- If each `t`-section is continuous at every point of `C`, then `(x, t) ↦ f(x, t)` is jointly
continuous on `C × T`. This is the original first sentence of Rockafellar's theorem, under its
ambient compact-neighborhood hypotheses on `E` and `T`; the textbook `R^n` case is the
specialization to `𝕜 := ℝ` and `E := EuclideanSpace ℝ (Fin n)`. -/
theorem continuousOn_uncurry_of_convexOn_of_continuous
    (hf_cont : ∀ x ∈ C, Continuous (f x)) :
    ContinuousOn (uncurry f) (C ×ˢ univ) := by
  simpa using
    continuousOn_uncurry_of_convexOn_of_continuous_dense_subset
      f hC_open hf_convex C Subset.rfl subset_intrinsicClosure hf_cont

omit hC_open hf_convex

end
