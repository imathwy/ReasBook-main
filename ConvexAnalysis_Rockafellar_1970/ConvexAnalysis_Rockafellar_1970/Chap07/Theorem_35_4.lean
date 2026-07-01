import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_11
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1

section

universe u v w

open scoped Topology
open Function Set Filter

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]

variable (KSeq : ℕ → U → X → 𝕜)
variable {C C' : Set U} {D D' : Set X}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 35.4 is the saddle-function analogue of Theorem 10.8. It starts with a
  sequence of finite concave-convex functions on `C × D`, assumes pointwise convergence on a dense
  product subset `C' × D' ⊆ C × D` through the canonical product view, and concludes existence of a
  finite concave-convex limit on all of `C × D` together with locally uniform convergence on
  `C × D`; compact-subset uniform convergence is the intrinsic topological bridge, and the
  closed-bounded form is a properness bridge corollary.
- `core/canonical`: the correct shape owner is
  `Bifunction.IsConcaveConvexOn 𝕜 C D`, while the canonical convergence owner is
  `TendstoLocallyUniformlyOn` for the product view `Function.uncurry`.
- `bridge/view`: the family boundedness input needed in the proof is supplied by Theorem 35.2 on
  the same product view, and the curried dense-convergence hypothesis is a thin companion bridge
  obtained by rewriting through `uncurry`.

Domain-style sampling used here:
- `Bifunction.IsConcaveConvexOn` from `Definition33_0_1`;
- `PointwiseBoundedOn.uniformlyBoundedOn_and_equiLipschitzOn_of_convexOn_of_generating_product`
  from `Theorem_35_2`;
- `TendstoLocallyUniformlyOn` from the Chapter 10 convergence API;
- `Function.uncurry` as the canonical owner-level passage from bifunctions to functions on the
  product.

Primitive data vs derived API:
- primitive source data: the relatively open sets `C` and `D`, the sequence `KSeq`, the dense
  product subset `C' × D'` encoded by one product inclusion and one intrinsic-density hypothesis,
  and pointwise convergence on that subset in the canonical product view;
- primitive source-facing shape assumption: each `KSeq i` is concave-convex on `C × D`;
- derived API: a `𝕜`-valued limit bifunction `K` that is concave-convex on `C × D`, converges
  pointwise everywhere on `C × D`, and is the local-uniform limit on the product domain; the
  compact-subset uniform convergence bridge and the textbook closed-bounded properness bridge are
  then derived from this canonical owner form.

Layer target: `source-facing`, stated directly with the local domain owner
`Bifunction.IsConcaveConvexOn 𝕜 C D` and the canonical product convergence owner rather than
through a new Chapter 7 wrapper; a curried dense-hypothesis form is kept only as a companion
bridge.

Ambient-assumption minimization:
- the core theorem below is stated at the factorwise finite-dimensional layer
  `[FiniteDimensional 𝕜 U] [FiniteDimensional 𝕜 X]`, which is the primitive bifunction ambient
  data;
- a bridge theorem then recovers the original product-ambient surface
  `[FiniteDimensional 𝕜 (U × X)]` through canonical injections `LinearMap.inl` and
  `LinearMap.inr`;
- the scalar/codomain layer remains `𝕜`-valued with
  `[NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [CompleteSpace 𝕜]` because the reused Chapter 10/35
  owner stack is currently available in this project exactly at that level.
-/

-- Proof sketch: pointwise convergence on `C' × D'` gives pointwise boundedness there. Apply
-- Theorem 35.2 on each compact subset of `C ×ˢ D` to obtain one common Lipschitz constant for the
-- whole sequence on that subset. Then repeat the compact finite-net argument from Theorem 10.8 on
-- the product space `U × X`: dense-subset convergence plus equi-Lipschitz control yields a
-- uniformly Cauchy sequence on each compact subset, hence a locally uniform limit on `C ×ˢ D`.
-- Passing to the limit in the slice-wise concavity and convexity inequalities shows that the
-- limit bifunction is again concave-convex.
/-- Theorem 35.4: if `C` and `D` are relatively open and `KSeq` is a sequence of finite
concave-convex functions on `C × D` whose product-view values `uncurry (KSeq i)` converge at every
point of a dense product subset `C' × D'`, then there is a finite concave-convex limit bifunction
`K` on `C × D` such that `uncurry (KSeq i)` converges locally uniformly to `uncurry K` on `C ×ˢ D`;
the induced pointwise convergence on all of `C × D` then follows from the canonical owner lemma
`TendstoLocallyUniformlyOn.tendsto_at`. Compact-subset and closed-bounded uniform convergence
consequences are provided below as bridge forms. -/
theorem exists_concaveConvexOn_tendstoLocallyUniformlyOn_of_dense_pointwise_of_factorwiseFiniteDimensional
    [FiniteDimensional 𝕜 U] [FiniteDimensional 𝕜 X]
    (hC_open : IsRelativelyOpen 𝕜 C)
    (hD_open : IsRelativelyOpen 𝕜 D)
    (hshape : ∀ i, Bifunction.IsConcaveConvexOn 𝕜 C D (KSeq i))
    (hCD'_subset : C' ×ˢ D' ⊆ C ×ˢ D)
    (hdense : C ×ˢ D ⊆ intrinsicClosure 𝕜 (C' ×ˢ D'))
    (hlimit_dense :
      ∀ p ∈ C' ×ˢ D', ∃ l : 𝕜, Tendsto (fun i ↦ uncurry (KSeq i) p) atTop (𝓝 l)) :
    ∃ K : U → X → 𝕜,
      Bifunction.IsConcaveConvexOn 𝕜 C D K ∧
      TendstoLocallyUniformlyOn (fun i ↦ uncurry (KSeq i)) (uncurry K) atTop (C ×ˢ D) := sorry

/-- Product-ambient bridge form of Theorem 35.4: this is the same conclusion as
`exists_concaveConvexOn_tendstoLocallyUniformlyOn_of_dense_pointwise_of_factorwiseFiniteDimensional`,
re-expressed with `[FiniteDimensional 𝕜 (U × X)]`. -/
theorem exists_concaveConvexOn_tendstoLocallyUniformlyOn_of_dense_pointwise
    [FiniteDimensional 𝕜 (U × X)]
    (hC_open : IsRelativelyOpen 𝕜 C)
    (hD_open : IsRelativelyOpen 𝕜 D)
    (hshape : ∀ i, Bifunction.IsConcaveConvexOn 𝕜 C D (KSeq i))
    (hCD'_subset : C' ×ˢ D' ⊆ C ×ˢ D)
    (hdense : C ×ˢ D ⊆ intrinsicClosure 𝕜 (C' ×ˢ D'))
    (hlimit_dense :
      ∀ p ∈ C' ×ˢ D', ∃ l : 𝕜, Tendsto (fun i ↦ uncurry (KSeq i) p) atTop (𝓝 l)) :
    ∃ K : U → X → 𝕜,
      Bifunction.IsConcaveConvexOn 𝕜 C D K ∧
      TendstoLocallyUniformlyOn (fun i ↦ uncurry (KSeq i)) (uncurry K) atTop (C ×ˢ D) := by
  letI : FiniteDimensional 𝕜 U :=
    FiniteDimensional.of_injective (LinearMap.inl 𝕜 U X) LinearMap.inl_injective
  letI : FiniteDimensional 𝕜 X :=
    FiniteDimensional.of_injective (LinearMap.inr 𝕜 U X) LinearMap.inr_injective
  simpa using
    exists_concaveConvexOn_tendstoLocallyUniformlyOn_of_dense_pointwise_of_factorwiseFiniteDimensional
      (KSeq := KSeq) hC_open hD_open hshape hCD'_subset hdense hlimit_dense

-- Proof sketch: first apply the owner theorem above to obtain the concave-convex limit `K` and
-- locally uniform convergence on `C ×ˢ D`. Restrict to a compact subset `S ⊆ C ×ˢ D`, then apply
-- the standard compact bridge from local uniform to uniform convergence on `S`.
/-- Compact-subset bridge form of Theorem 35.4: the canonical locally uniform conclusion upgrades
to uniform convergence on every compact subset `S ⊆ C ×ˢ D`. -/
theorem exists_concaveConvexOn_tendstoUniformlyOn_on_compact_of_dense_pointwise
    [FiniteDimensional 𝕜 (U × X)]
    (hC_open : IsRelativelyOpen 𝕜 C)
    (hD_open : IsRelativelyOpen 𝕜 D)
    (hshape : ∀ i, Bifunction.IsConcaveConvexOn 𝕜 C D (KSeq i))
    (hCD'_subset : C' ×ˢ D' ⊆ C ×ˢ D)
    (hdense : C ×ˢ D ⊆ intrinsicClosure 𝕜 (C' ×ˢ D'))
    (hlimit_dense :
      ∀ p ∈ C' ×ˢ D', ∃ l : 𝕜, Tendsto (fun i ↦ uncurry (KSeq i) p) atTop (𝓝 l))
    {S : Set (U × X)} (hS_compact : IsCompact S) (hS_subset : S ⊆ C ×ˢ D) :
    ∃ K : U → X → 𝕜,
      Bifunction.IsConcaveConvexOn 𝕜 C D K ∧
      TendstoUniformlyOn (fun i ↦ uncurry (KSeq i)) (uncurry K) atTop S := by
  obtain ⟨K, hK_shape, hK_loc⟩ :=
    exists_concaveConvexOn_tendstoLocallyUniformlyOn_of_dense_pointwise
      KSeq hC_open hD_open hshape hCD'_subset hdense hlimit_dense
  refine ⟨K, hK_shape, ?_⟩
  have hK_loc_S :
      TendstoLocallyUniformlyOn (fun i ↦ uncurry (KSeq i)) (uncurry K) atTop S :=
    hK_loc.mono hS_subset
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hS_compact).1 hK_loc_S

-- Proof sketch: apply the compact-subset bridge theorem above with compactness obtained from the
-- closed/bounded hypotheses via `[ProperSpace (U × X)]`.
/-- Closed-bounded bridge form of Theorem 35.4: under `[ProperSpace (U × X)]`, compactness of
closed bounded sets converts the compact-subset bridge above into the textbook closed-bounded
uniform-convergence conclusion on `S ⊆ C ×ˢ D`. -/
theorem exists_concaveConvexOn_tendstoUniformlyOn_on_closed_bounded_of_dense_pointwise
    [FiniteDimensional 𝕜 (U × X)]
    [ProperSpace (U × X)]
    (hC_open : IsRelativelyOpen 𝕜 C)
    (hD_open : IsRelativelyOpen 𝕜 D)
    (hshape : ∀ i, Bifunction.IsConcaveConvexOn 𝕜 C D (KSeq i))
    (hCD'_subset : C' ×ˢ D' ⊆ C ×ˢ D)
    (hdense : C ×ˢ D ⊆ intrinsicClosure 𝕜 (C' ×ˢ D'))
    (hlimit_dense :
      ∀ p ∈ C' ×ˢ D', ∃ l : 𝕜, Tendsto (fun i ↦ uncurry (KSeq i) p) atTop (𝓝 l))
    {S : Set (U × X)} (hS_closed : IsClosed S) (hS_bounded : Bornology.IsBounded S)
    (hS_subset : S ⊆ C ×ˢ D) :
    ∃ K : U → X → 𝕜,
      Bifunction.IsConcaveConvexOn 𝕜 C D K ∧
      TendstoUniformlyOn (fun i ↦ uncurry (KSeq i)) (uncurry K) atTop S := by
  simpa using
    exists_concaveConvexOn_tendstoUniformlyOn_on_compact_of_dense_pointwise
      KSeq hC_open hD_open hshape hCD'_subset hdense hlimit_dense
      (Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded) hS_subset

/-- Curried-coordinate companion form of Theorem 35.4 with factorwise subset and intrinsic-density
inputs (`C' ⊆ C`, `D' ⊆ D`, `C ⊆ intrinsicClosure 𝕜 C'`, `D ⊆ intrinsicClosure 𝕜 D'`). -/
theorem exists_concaveConvexOn_tendstoLocallyUniformlyOn_of_dense_pointwise_curried
    [FiniteDimensional 𝕜 (U × X)]
    (hC_open : IsRelativelyOpen 𝕜 C)
    (hD_open : IsRelativelyOpen 𝕜 D)
    (hshape : ∀ i, Bifunction.IsConcaveConvexOn 𝕜 C D (KSeq i))
    (hC'_subset : C' ⊆ C)
    (hD'_subset : D' ⊆ D)
    (hC'_dense : C ⊆ intrinsicClosure 𝕜 C')
    (hD'_dense : D ⊆ intrinsicClosure 𝕜 D')
    (hlimit_dense : ∀ u ∈ C', ∀ v ∈ D', ∃ l : 𝕜, Tendsto (fun i ↦ KSeq i u v) atTop (𝓝 l)) :
    ∃ K : U → X → 𝕜,
      Bifunction.IsConcaveConvexOn 𝕜 C D K ∧
      TendstoLocallyUniformlyOn (fun i ↦ uncurry (KSeq i)) (uncurry K) atTop (C ×ˢ D) := by
  have hCD'_subset : C' ×ˢ D' ⊆ C ×ˢ D := Set.prod_mono hC'_subset hD'_subset
  have hdense : C ×ˢ D ⊆ intrinsicClosure 𝕜 (C' ×ˢ D') := by
    intro p hp
    have hp1 : p.1 ∈ closure C' :=
      intrinsicClosure_subset_closure (hC'_dense hp.1)
    have hp2 : p.2 ∈ closure D' :=
      intrinsicClosure_subset_closure (hD'_dense hp.2)
    have hp_closure : p ∈ closure (C' ×ˢ D') := by
      simpa [closure_prod_eq] using And.intro hp1 hp2
    simpa [intrinsicClosure_eq_closure] using hp_closure
  refine exists_concaveConvexOn_tendstoLocallyUniformlyOn_of_dense_pointwise
    KSeq hC_open hD_open hshape hCD'_subset hdense ?_
  intro p hp
  obtain ⟨l, hl⟩ := hlimit_dense p.1 hp.1 p.2 hp.2
  exact ⟨l, by simpa [Function.uncurry] using hl⟩

end
