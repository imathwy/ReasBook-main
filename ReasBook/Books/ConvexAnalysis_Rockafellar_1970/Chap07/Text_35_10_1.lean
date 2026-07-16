import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_14
import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem_35_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem_35_10

noncomputable section

open Filter Function Set
open scoped Gradient Topology

universe u v

namespace Bifunction

section DensePointwiseLimit

variable {𝕜 : Type*} {U : Type u} {V : Type v}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [FiniteDimensional 𝕜 (U × V)]

variable {C C' : Set U} {D D' : Set V}
variable {K : U → V → 𝕜} {KSeq : ℕ → U → V → 𝕜}

/-!
Source/core/bridge triage for the value-convergence layer in Text 35.10.1.

- `source-facing`: Text 35.10.1 upgrades the dense-product hypothesis `(A)` to full pointwise
  convergence `(B)` on all of `C × D`.
- `core/canonical`: the chapter owners are `SaddleFunction.IsConcaveConvexOn 𝕜 C D` for the
  saddle shape and `TendstoLocallyUniformlyOn` / `Tendsto` for convergence of the product view
  `uncurry`.
- `bridge/view`: the proof route is exactly the composition of Theorem 35.4 with Theorem 35.1 to
  identify the dense-subset limit with the prescribed bifunction `K`.

Domain-style sampling used here:
- `exists_concaveConvexOn_tendstoLocallyUniformlyOn_of_dense_pointwise` from `Theorem_35_4`;
- `IsConcaveConvexOn.continuousOn_uncurry` from `Theorem_35_1`;
- `TendstoLocallyUniformlyOn.tendsto_at` from the canonical convergence API.

Primitive data vs derived API:
- primitive source data: the relatively open factors `C`, `D`, the dense subsets `C'`, `D'`, the
  limit bifunction `K`, and the approximating sequence `KSeq`;
- primitive source hypotheses: concave-convexity of each `KSeq i`, pointwise convergence on
  `C' × D'`, and continuity of the prescribed `K`
  whenever the dense-subset limit must be identified with that prescribed bifunction;
- derived API: local uniform convergence on `C ×ˢ D`, then its global pointwise consequence on
  `C × D`.

Ambient-assumption minimization:
- separate convexity assumptions on `C` and `D` are not primitive for these declarations. The
  source-facing saddle-shape owners already force convexity whenever the opposite factor is
  inhabited, and the empty-factor cases make the product-domain conclusions vacuous.

Layer target: `source-facing` for the value extension from a dense product subset, phrased over
the same relative-open finite-dimensional normed-space ambient used by Theorem 35.4 and
Theorem 35.1 rather than the later Euclidean gradient specialization.
-/

-- Proof sketch: apply Theorem 35.4 to the dense-product convergence hypothesis after rewriting it
-- on the product view `uncurry (KSeq i)` and using `closure_prod_eq` to obtain the required dense
-- subset of `C ×ˢ D`. This gives a finite concave-convex limit `Klim` with local uniform
-- convergence on `C ×ˢ D`. Theorem 35.1 makes `uncurry Klim` continuous on `C ×ˢ D`; if the
-- prescribed bifunction `K` is also continuous there, then the two product views agree on the
-- dense subset `C' ×ˢ D'`, hence on all of `C ×ˢ D`. This identifies the owner local-uniform
-- limit with `K`.
/-- Canonical owner-level bridge for Text 35.10.1: if finite concave-convex bifunctions `KSeq i`
converge to a continuous bifunction `K` on a dense product subset `C' × D'` of a relatively open
product domain `C × D`, then `uncurry (KSeq i)` converges locally uniformly to `uncurry K` on
`C ×ˢ D`. The continuity of `K` is the minimal extra data needed to identify the dense-subset
limit with the prescribed bifunction. -/
  theorem tendstoLocallyUniformlyOn_uncurry_of_dense_pointwiseLimit_concaveConvexOn_relativelyOpen
    (hC_open : IsRelativelyOpen 𝕜 C) (hD_open : IsRelativelyOpen 𝕜 D)
    (hK_cont : ContinuousOn (uncurry K) (C ×ˢ D))
    (hKSeq_concaveConvex : ∀ i, SaddleFunction.IsConcaveConvexOn 𝕜 C D (KSeq i))
    (hC'_subset : C' ⊆ C) (hD'_subset : D' ⊆ D)
    (hC'_dense : C ⊆ intrinsicClosure 𝕜 C') (hD'_dense : D ⊆ intrinsicClosure 𝕜 D')
    (hlimit_dense :
      ∀ u ∈ C', ∀ v ∈ D', Tendsto (fun i ↦ KSeq i u v) atTop (𝓝 (K u v))) :
    TendstoLocallyUniformlyOn (fun i ↦ uncurry (KSeq i)) (uncurry K) atTop (C ×ˢ D) := by
  have hCD'_subset : C' ×ˢ D' ⊆ C ×ˢ D := Set.prod_mono hC'_subset hD'_subset
  have hprod_dense : C ×ˢ D ⊆ closure (C' ×ˢ D') := by
    intro p hp
    have hp1 : p.1 ∈ closure C' :=
      intrinsicClosure_subset_closure (hC'_dense hp.1)
    have hp2 : p.2 ∈ closure D' :=
      intrinsicClosure_subset_closure (hD'_dense hp.2)
    simpa [closure_prod_eq] using And.intro hp1 hp2
  obtain ⟨Klim, hKlim_concaveConvex, hKlim_loc⟩ :=
    exists_concaveConvexOn_tendstoLocallyUniformlyOn_of_dense_pointwise_curried
      KSeq hC_open hD_open hKSeq_concaveConvex
      hC'_subset hD'_subset hC'_dense hD'_dense
      (fun u hu v hv ↦ ⟨K u v, hlimit_dense u hu v hv⟩)
  have hKlim_cont : ContinuousOn (uncurry Klim) (C ×ˢ D) :=
    IsConcaveConvexOn.continuousOn_uncurry
      (hK_shape := hKlim_concaveConvex) hC_open hD_open
  have hEq_dense : (C' ×ˢ D').EqOn (uncurry Klim) (uncurry K) := by
    intro p hp
    exact tendsto_nhds_unique
      (hKlim_loc.tendsto_at (hCD'_subset hp))
      (by simpa [uncurry] using hlimit_dense p.1 hp.1 p.2 hp.2)
  have hEq : (C ×ˢ D).EqOn (uncurry Klim) (uncurry K) :=
    hEq_dense.of_subset_closure hKlim_cont hK_cont hCD'_subset hprod_dense
  exact hKlim_loc.congr_right hEq

-- Proof sketch: apply the owner-level local-uniform theorem above, then evaluate the resulting
-- owner convergence at the chosen product point `(u, v)`.
/-- Text 35.10.1, pointwise companion form: if finite concave-convex bifunctions `KSeq i`
converge pointwise to a continuous bifunction `K` on the dense product subset `C' × D'` of a
relatively open product domain `C × D`, then the same convergence holds on all of `C × D`. -/
theorem tendsto_on_product_of_dense_pointwiseLimit_concaveConvexOn_relativelyOpen
    (hC_open : IsRelativelyOpen 𝕜 C) (hD_open : IsRelativelyOpen 𝕜 D)
    (hK_cont : ContinuousOn (uncurry K) (C ×ˢ D))
    (hKSeq_concaveConvex : ∀ i, SaddleFunction.IsConcaveConvexOn 𝕜 C D (KSeq i))
    (hC'_subset : C' ⊆ C) (hD'_subset : D' ⊆ D)
    (hC'_dense : C ⊆ intrinsicClosure 𝕜 C') (hD'_dense : D ⊆ intrinsicClosure 𝕜 D')
    (hlimit_dense :
      ∀ u ∈ C', ∀ v ∈ D', Tendsto (fun i ↦ KSeq i u v) atTop (𝓝 (K u v)))
    (u : U) (hu : u ∈ C) (v : V) (hv : v ∈ D) :
    Tendsto (fun i ↦ KSeq i u v) atTop (𝓝 (K u v)) := by
  have hloc :
      TendstoLocallyUniformlyOn (fun i ↦ uncurry (KSeq i)) (uncurry K) atTop (C ×ˢ D) :=
    tendstoLocallyUniformlyOn_uncurry_of_dense_pointwiseLimit_concaveConvexOn_relativelyOpen
      hC_open hD_open hK_cont hKSeq_concaveConvex hC'_subset hD'_subset hC'_dense hD'_dense
      hlimit_dense
  simpa [uncurry] using hloc.tendsto_at (show (u, v) ∈ C ×ˢ D from ⟨hu, hv⟩)

end DensePointwiseLimit

section StrongDualDensePointwiseLimit

variable {𝕜 : Type*} {U : Type u} {V : Type v}
variable [NontriviallyNormedField 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable [CompleteSpace 𝕜]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [FiniteDimensional 𝕜 (U × V)]

variable {C C' : Set U} {D D' : Set V}
variable {K : U → V → 𝕜} {KSeq : ℕ → U → V → 𝕜}

/-!
Source/core/bridge triage for the strong-dual owner layer in Text 35.10.1.

- `source-facing`: dense-product value convergence first upgrades to local uniform convergence on
  `C ×ˢ D`, then Theorem 35.10 upgrades this to convergence of the canonical derivative owner
  `prodFDeriv`.
- `core/canonical`: the derivative owner is `prodFDeriv : U × V → StrongDual 𝕜 U × StrongDual 𝕜 V`.
- `bridge/view`: Euclidean `gradient` convergence remains a downstream bridge, handled in the next
  section.
-/

/-- Canonical derivative-owner form of Text 35.10.1 at the strong-dual layer: dense-product
pointwise value convergence of finite differentiable concave-convex bifunctions identifies a
locally uniform value limit on `C ×ˢ D`, hence yields locally uniform convergence of
`prodFDeriv`. -/
theorem tendstoLocallyUniformlyOn_prodFDeriv_of_dense_pointwiseLimit_concaveConvexOn_relativelyOpen
    (hC_open : IsRelativelyOpen 𝕜 C) (hD_open : IsRelativelyOpen 𝕜 D)
    (hK_diff : DifferentiableOn 𝕜 (uncurry K) (C ×ˢ D))
    (hKSeq_concaveConvex : ∀ i, SaddleFunction.IsConcaveConvexOn 𝕜 C D (KSeq i))
    (hKSeq_diff : ∀ i, DifferentiableOn 𝕜 (uncurry (KSeq i)) (C ×ˢ D))
    (hC'_subset : C' ⊆ C) (hD'_subset : D' ⊆ D)
    (hC'_dense : C ⊆ intrinsicClosure 𝕜 C') (hD'_dense : D ⊆ intrinsicClosure 𝕜 D')
    (hlimit_dense :
      ∀ u ∈ C', ∀ v ∈ D', Tendsto (fun i ↦ KSeq i u v) atTop (𝓝 (K u v))) :
    TendstoLocallyUniformlyOn (fun i ↦ prodFDeriv (KSeq i)) (prodFDeriv K) atTop (C ×ˢ D) := by
  have hloc :
      TendstoLocallyUniformlyOn (fun i ↦ uncurry (KSeq i)) (uncurry K) atTop (C ×ˢ D) :=
    tendstoLocallyUniformlyOn_uncurry_of_dense_pointwiseLimit_concaveConvexOn_relativelyOpen
      hC_open hD_open hK_diff.continuousOn hKSeq_concaveConvex
      hC'_subset hD'_subset hC'_dense hD'_dense hlimit_dense
  exact
    tendstoLocallyUniformlyOn_prodFDeriv_of_tendstoLocallyUniformlyOn_uncurry_on_relativelyOpen
      hC_open hD_open hK_diff hKSeq_concaveConvex hKSeq_diff hloc

/-- Pointwise strong-dual derivative consequence of the dense-product value extension theorem
above. -/
theorem prodFDeriv_tendsto_of_dense_pointwiseLimit_concaveConvexOn_relativelyOpen
    (hC_open : IsRelativelyOpen 𝕜 C) (hD_open : IsRelativelyOpen 𝕜 D)
    (hK_diff : DifferentiableOn 𝕜 (uncurry K) (C ×ˢ D))
    (hKSeq_concaveConvex : ∀ i, SaddleFunction.IsConcaveConvexOn 𝕜 C D (KSeq i))
    (hKSeq_diff : ∀ i, DifferentiableOn 𝕜 (uncurry (KSeq i)) (C ×ˢ D))
    (hC'_subset : C' ⊆ C) (hD'_subset : D' ⊆ D)
    (hC'_dense : C ⊆ intrinsicClosure 𝕜 C') (hD'_dense : D ⊆ intrinsicClosure 𝕜 D')
    (hlimit_dense :
      ∀ u ∈ C', ∀ v ∈ D', Tendsto (fun i ↦ KSeq i u v) atTop (𝓝 (K u v)))
    (p : U × V) (hp : p ∈ C ×ˢ D) :
    Tendsto (fun i ↦ prodFDeriv (KSeq i) p) atTop (𝓝 (prodFDeriv K p)) := by
  have hprodFDeriv_loc :
      TendstoLocallyUniformlyOn (fun i ↦ prodFDeriv (KSeq i)) (prodFDeriv K) atTop (C ×ˢ D) :=
    tendstoLocallyUniformlyOn_prodFDeriv_of_dense_pointwiseLimit_concaveConvexOn_relativelyOpen
      hC_open hD_open hK_diff hKSeq_concaveConvex hKSeq_diff
      hC'_subset hD'_subset hC'_dense hD'_dense hlimit_dense
  exact hprodFDeriv_loc.tendsto_at hp

/-- Closed-bounded uniform strong-dual derivative consequence of the dense-product value extension
theorem above. -/
theorem prodFDeriv_tendstoUniformlyOn_closed_bounded_of_dense_pointwise_relativelyOpen
    [ProperSpace (U × V)]
    (hC_open : IsRelativelyOpen 𝕜 C) (hD_open : IsRelativelyOpen 𝕜 D)
    (hK_diff : DifferentiableOn 𝕜 (uncurry K) (C ×ˢ D))
    (hKSeq_concaveConvex : ∀ i, SaddleFunction.IsConcaveConvexOn 𝕜 C D (KSeq i))
    (hKSeq_diff : ∀ i, DifferentiableOn 𝕜 (uncurry (KSeq i)) (C ×ˢ D))
    (hC'_subset : C' ⊆ C) (hD'_subset : D' ⊆ D)
    (hC'_dense : C ⊆ intrinsicClosure 𝕜 C') (hD'_dense : D ⊆ intrinsicClosure 𝕜 D')
    (hlimit_dense :
      ∀ u ∈ C', ∀ v ∈ D', Tendsto (fun i ↦ KSeq i u v) atTop (𝓝 (K u v)))
    {S : Set (U × V)} (hS_closed : IsClosed S) (hS_bounded : Bornology.IsBounded S)
    (hS_subset : S ⊆ C ×ˢ D) :
    TendstoUniformlyOn (fun i ↦ prodFDeriv (KSeq i)) (prodFDeriv K) atTop S := by
  have hprodFDeriv_loc :
      TendstoLocallyUniformlyOn (fun i ↦ prodFDeriv (KSeq i)) (prodFDeriv K) atTop (C ×ˢ D) :=
    tendstoLocallyUniformlyOn_prodFDeriv_of_dense_pointwiseLimit_concaveConvexOn_relativelyOpen
      hC_open hD_open hK_diff hKSeq_concaveConvex hKSeq_diff
      hC'_subset hD'_subset hC'_dense hD'_dense hlimit_dense
  exact
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded)).1 <|
      hprodFDeriv_loc.mono hS_subset

end StrongDualDensePointwiseLimit

section GradientDensePointwiseLimit

variable {U : Type u} {V : Type v}
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ (U × V)]

variable {C C' : Set U} {D D' : Set V}
variable {K : U → V → ℝ} {KSeq : ℕ → U → V → ℝ}

/-!
Source/core/bridge triage for the gradient layer in Text 35.10.1.

- `source-facing`: after extending value convergence from `C' × D'` to all of `C × D`, the text
  applies Theorem 35.10 to obtain convergence of `Bifunction.gradient`.
- `core/canonical`: the value extension is owned by the generalized relative-open theorems above,
  while the Euclidean gradient convergence owner is
  `tendstoLocallyUniformlyOn_gradient_of_tendstoLocallyUniformlyOn_uncurry_on_relativelyOpen` from
  `Theorem_35_10`.
- `bridge/view`: these declarations are Euclidean/relatively-open-product specializations that
  combine those two owner layers.
-/

-- Proof sketch: first use the owner-level local-uniform theorem above to identify the dense
-- product limit with `K` on all of `C ×ˢ D`. Then apply the local-uniform gradient bridge from
-- Theorem 35.10 and specialize it at the chosen point `p`.
/-- Local-uniform Euclidean-gradient bridge consequence of the dense-product value extension owner
theorem above. -/
theorem tendstoLocallyUniformlyOn_gradient_of_dense_pointwiseLimit_concaveConvexOn_relativelyOpen
    (hC_open : IsRelativelyOpen ℝ C) (hD_open : IsRelativelyOpen ℝ D)
    (hK_diff : DifferentiableOn ℝ (uncurry K) (C ×ˢ D))
    (hKSeq_concaveConvex : ∀ i, SaddleFunction.IsConcaveConvexOn ℝ C D (KSeq i))
    (hKSeq_diff : ∀ i, DifferentiableOn ℝ (uncurry (KSeq i)) (C ×ˢ D))
    (hC'_subset : C' ⊆ C) (hD'_subset : D' ⊆ D)
    (hC'_dense : C ⊆ intrinsicClosure ℝ C') (hD'_dense : D ⊆ intrinsicClosure ℝ D')
    (hlimit_dense :
      ∀ u ∈ C', ∀ v ∈ D', Tendsto (fun i ↦ KSeq i u v) atTop (𝓝 (K u v))) :
    TendstoLocallyUniformlyOn (fun i ↦ gradient (KSeq i)) (gradient K) atTop (C ×ˢ D) := by
  have hloc :
      TendstoLocallyUniformlyOn (fun i ↦ uncurry (KSeq i)) (uncurry K) atTop (C ×ˢ D) :=
    tendstoLocallyUniformlyOn_uncurry_of_dense_pointwiseLimit_concaveConvexOn_relativelyOpen
      hC_open hD_open hK_diff.continuousOn hKSeq_concaveConvex
      hC'_subset hD'_subset hC'_dense hD'_dense hlimit_dense
  exact
    tendstoLocallyUniformlyOn_gradient_of_tendstoLocallyUniformlyOn_uncurry_on_relativelyOpen
      hC_open hD_open hK_diff hKSeq_concaveConvex hKSeq_diff hloc

/-- Companion pointwise gradient consequence of the dense-product extension theorem above. -/
theorem gradient_tendsto_of_dense_pointwiseLimit_concaveConvexOn_relativelyOpen
    (hC_open : IsRelativelyOpen ℝ C) (hD_open : IsRelativelyOpen ℝ D)
    (hK_diff : DifferentiableOn ℝ (uncurry K) (C ×ˢ D))
    (hKSeq_concaveConvex : ∀ i, SaddleFunction.IsConcaveConvexOn ℝ C D (KSeq i))
    (hKSeq_diff : ∀ i, DifferentiableOn ℝ (uncurry (KSeq i)) (C ×ˢ D))
    (hC'_subset : C' ⊆ C) (hD'_subset : D' ⊆ D)
    (hC'_dense : C ⊆ intrinsicClosure ℝ C') (hD'_dense : D ⊆ intrinsicClosure ℝ D')
    (hlimit_dense :
      ∀ u ∈ C', ∀ v ∈ D', Tendsto (fun i ↦ KSeq i u v) atTop (𝓝 (K u v)))
    (p : U × V) (hp : p ∈ C ×ˢ D) :
    Tendsto (fun i ↦ gradient (KSeq i) p) atTop (𝓝 (gradient K p)) := by
  have hgrad_loc :
      TendstoLocallyUniformlyOn (fun i ↦ gradient (KSeq i)) (gradient K) atTop (C ×ˢ D) :=
    tendstoLocallyUniformlyOn_gradient_of_dense_pointwiseLimit_concaveConvexOn_relativelyOpen
      hC_open hD_open hK_diff hKSeq_concaveConvex hKSeq_diff
      hC'_subset hD'_subset hC'_dense hD'_dense hlimit_dense
  exact hgrad_loc.tendsto_at hp

-- Proof sketch: first use the owner-level local-uniform theorem above, then apply the local
-- uniform gradient bridge from Theorem 35.10. Restrict that locally uniform gradient convergence
-- to the chosen closed bounded subset `S` and convert it to uniform convergence on `S` through
-- compactness in finite-dimensional Euclidean space.
/-- Companion uniform-on-closed-bounded gradient consequence of the dense-product extension
theorem above. -/
theorem
    gradient_tendstoUniformlyOn_closed_bounded_of_dense_pointwise_relativelyOpen
    (hC_open : IsRelativelyOpen ℝ C) (hD_open : IsRelativelyOpen ℝ D)
    (hK_diff : DifferentiableOn ℝ (uncurry K) (C ×ˢ D))
    (hKSeq_concaveConvex : ∀ i, SaddleFunction.IsConcaveConvexOn ℝ C D (KSeq i))
    (hKSeq_diff : ∀ i, DifferentiableOn ℝ (uncurry (KSeq i)) (C ×ˢ D))
    (hC'_subset : C' ⊆ C) (hD'_subset : D' ⊆ D)
    (hC'_dense : C ⊆ intrinsicClosure ℝ C') (hD'_dense : D ⊆ intrinsicClosure ℝ D')
    (hlimit_dense :
      ∀ u ∈ C', ∀ v ∈ D', Tendsto (fun i ↦ KSeq i u v) atTop (𝓝 (K u v)))
    {S : Set (U × V)} (hS_closed : IsClosed S) (hS_bounded : Bornology.IsBounded S)
    (hS_subset : S ⊆ C ×ˢ D) :
    TendstoUniformlyOn (fun i ↦ gradient (KSeq i)) (gradient K) atTop S := by
  have hgrad_loc :
      TendstoLocallyUniformlyOn (fun i ↦ gradient (KSeq i)) (gradient K) atTop (C ×ˢ D) :=
    tendstoLocallyUniformlyOn_gradient_of_dense_pointwiseLimit_concaveConvexOn_relativelyOpen
      hC_open hD_open hK_diff hKSeq_concaveConvex hKSeq_diff
      hC'_subset hD'_subset hC'_dense hD'_dense hlimit_dense
  exact
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded)).1 <|
      hgrad_loc.mono hS_subset

end GradientDensePointwiseLimit

end Bifunction
