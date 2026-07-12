import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_10_5_6
import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem_35_4

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v w

open scoped Topology
open Function Set Filter SaddleFunction

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜] [LinearOrder 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [FiniteDimensional 𝕜 U] [FiniteDimensional 𝕜 X]

variable (KSeq : ℕ → U → X → 𝕜)
variable {C C' : Set U} {D D' : Set X}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 35.5 starts with a sequence of finite concave-convex functions on
  `C × D`, assumes pointwise boundedness on a dense product subset `C' × D' ⊆ C × D`, and
  concludes existence of a subsequence converging uniformly on each closed bounded subset of
  `C × D` to a finite concave-convex limit.
- `core/canonical`: the shape owner is `IsConcaveConvexOn 𝕜 C D`, the boundedness owner is
  `PointwiseBoundedOn (fun i ↦ uncurry (KSeq i))` on `C' ×ˢ D'`, the subsequence is canonically
  represented, as elsewhere in Chapter 10, by a reindexing map `φ : ℕ → ℕ` together with
  `StrictMono φ`, and the convergence owner is `TendstoLocallyUniformlyOn` on `C ×ˢ D` for the
  reindexed product-view family `fun i ↦ uncurry (KSeq (φ i))`.
- `bridge/view`: Theorem 35.4 upgrades dense-subset pointwise convergence of a saddle sequence to
  a concave-convex locally uniform limit, so Theorem 35.5 should only add the subsequence
  extraction layer and then feed the reindexed sequence into that owner theorem, not introduce a
  second product-family wrapper.

Domain-style sampling used here:
- `SaddleFunction.IsConcaveConvexOn` from `Definition33_0_1`;
- `PointwiseBoundedOn` on the owner family `fun i ↦ uncurry (KSeq i)`;
- `TendstoLocallyUniformlyOn` as the canonical convergence owner on `C ×ˢ D`;
- `exists_subsequence_tendstoLocallyUniformlyOn_of_convexOn_of_pointwise_bounded` from
  `Theorem_10_9` for the chapter-standard diagonal Bolzano-Weierstrass ambient layer on the scalar
  field;
- `exists_concaveConvexOn_tendstoLocallyUniformlyOn_of_dense_pointwise` from `Theorem_35_4`.

Primitive data vs derived API:
- primitive inputs: the relatively open sets `C` and `D`, the sequence `KSeq`, the dense product
  subset inclusion `C' ×ˢ D' ⊆ C ×ˢ D`, density of `C' ×ˢ D'` in `C ×ˢ D`, and pointwise
  boundedness of the owner product family `fun i ↦ uncurry (KSeq i)` on `C' ×ˢ D'`;
- primitive source-facing shape hypothesis: every `KSeq i` is concave-convex on `C × D`;
- derived API: a subsequence chosen by a strictly monotone reindexing `φ`, a finite
  concave-convex limit
  bifunction `K`, and local uniform convergence of the reindexed owner family
  `fun i ↦ uncurry (KSeq (φ i))` on `C ×ˢ D`; compact-subset and closed-bounded uniform
  convergence forms are then provided as bridge theorems in this file.

Layer target: `source-facing`, using the Chapter 35 shape owner and the canonical local-uniform
convergence owner, with subsequences represented by the chapter-standard `StrictMono`
reindexing surface.
-/

-- Proof sketch: choose a countable dense subset of `C' ×ˢ D'`, enumerate it, and apply the
-- diagonal Bolzano-Weierstrass extraction argument to the bounded scalar fibers
-- `(fun i ↦ uncurry (KSeq i)) i p_j`. This yields a strictly monotone reindexing `φ : ℕ → ℕ`
-- for which the
-- reindexed sequence `KSeq ∘ φ` converges pointwise on a dense subset of `C ×ˢ D`. Then invoke
-- Theorem 35.4 on `KSeq ∘ φ` to obtain a finite concave-convex limit `K` and local uniform
-- convergence of `fun i ↦ uncurry (KSeq (φ i))` on `C ×ˢ D`, hence uniform convergence on every
-- closed
-- bounded subset of `C × D`. As in Theorem 10.9, the bounded scalar-fiber subsequence extraction
-- uses `LocallyCompactSpace 𝕜` via `ProperSpace.of_locallyCompactSpace` to make the relevant
-- closed bounded subsets of `𝕜` compact.
/-- Theorem 35.5: if `C` and `D` are relatively open and `K₁, K₂, …` is a sequence of finite
concave-convex functions on `C × D` whose value sequence is bounded at every point of a dense
product subset `C' × D' ⊆ C × D`, then some subsequence converges locally uniformly on `C × D`,
hence uniformly on every closed bounded subset of `C × D`, to a finite concave-convex function.
The textbook `ℝ^m × ℝ^n` statement is the specialization `𝕜 := ℝ`
to Euclidean spaces; the scalar ambient hypothesis `[LocallyCompactSpace 𝕜]` is the
chapter-canonical compactness input for the diagonal extraction step (via
`ProperSpace.of_locallyCompactSpace`). -/
theorem exists_subsequence_tendstoLocallyUniformlyOn_of_concaveConvexOn_of_dense_pointwiseBoundedOn
    (hC_open : IsRelativelyOpen 𝕜 C)
    (hD_open : IsRelativelyOpen 𝕜 D)
    (hshape : ∀ i, IsConcaveConvexOn 𝕜 C D (KSeq i))
    (hCD'_subset : C' ×ˢ D' ⊆ C ×ˢ D)
    (hdense : C ×ˢ D ⊆ intrinsicClosure 𝕜 (C' ×ˢ D'))
    (hbounded : PointwiseBoundedOn (fun i ↦ uncurry (KSeq i)) (C' ×ˢ D')) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ K : U → X → 𝕜,
      IsConcaveConvexOn 𝕜 C D K ∧
        TendstoLocallyUniformlyOn (fun i ↦ uncurry (KSeq (φ i))) (uncurry K) atTop (C ×ˢ D) :=
  sorry

-- Proof sketch: apply the core owner theorem above to obtain the reindexing `φ`, the
-- concave-convex limit `K`, and local uniform convergence on `C ×ˢ D`; then restrict to the
-- compact subset `S` and use the standard compact bridge from local uniform to uniform
-- convergence.
/-- Compact-subset bridge form of Theorem 35.5: under the same hypotheses, one extracted
subsequence converges uniformly on each compact `S ⊆ C ×ˢ D`. -/
theorem
    exists_subsequence_tendstoUniformlyOn_on_compact_of_concaveConvexOn_of_dense_pointwiseBoundedOn
    (hC_open : IsRelativelyOpen 𝕜 C)
    (hD_open : IsRelativelyOpen 𝕜 D)
    (hshape : ∀ i, IsConcaveConvexOn 𝕜 C D (KSeq i))
    (hCD'_subset : C' ×ˢ D' ⊆ C ×ˢ D)
    (hdense : C ×ˢ D ⊆ intrinsicClosure 𝕜 (C' ×ˢ D'))
    (hbounded : PointwiseBoundedOn (fun i ↦ uncurry (KSeq i)) (C' ×ˢ D'))
    {S : Set (U × X)} (hS_compact : IsCompact S) (hS_subset : S ⊆ C ×ˢ D) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ K : U → X → 𝕜,
      IsConcaveConvexOn 𝕜 C D K ∧
        TendstoUniformlyOn (fun i ↦ uncurry (KSeq (φ i))) (uncurry K) atTop S := by
  obtain ⟨φ, hφ, K, hK_shape, hK_loc⟩ :=
    exists_subsequence_tendstoLocallyUniformlyOn_of_concaveConvexOn_of_dense_pointwiseBoundedOn
      KSeq hC_open hD_open hshape hCD'_subset hdense hbounded
  refine ⟨φ, hφ, K, hK_shape, ?_⟩
  have hK_loc_S :
      TendstoLocallyUniformlyOn (fun i ↦ uncurry (KSeq (φ i))) (uncurry K) atTop S :=
    hK_loc.mono hS_subset
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hS_compact).1 hK_loc_S

-- Proof sketch: combine the compact-subset bridge above with compactness of closed bounded sets.
-- The needed properness of `U × X` is canonically derived from finite-dimensionality and
-- local compactness of `𝕜`.
/-- Closed-bounded bridge form of Theorem 35.5: one extracted subsequence converges uniformly on
each closed bounded `S ⊆ C ×ˢ D`; compactness of closed bounded sets is obtained from the ambient
finite-dimensional layer over the locally compact scalar field `𝕜`. -/
theorem
    exists_subsequence_tendstoUniformlyOn_on_closed_bounded_of_concaveConvexOn_of_dense_pointwiseBoundedOn
    (hC_open : IsRelativelyOpen 𝕜 C)
    (hD_open : IsRelativelyOpen 𝕜 D)
    (hshape : ∀ i, IsConcaveConvexOn 𝕜 C D (KSeq i))
    (hCD'_subset : C' ×ˢ D' ⊆ C ×ˢ D)
    (hdense : C ×ˢ D ⊆ intrinsicClosure 𝕜 (C' ×ˢ D'))
    (hbounded : PointwiseBoundedOn (fun i ↦ uncurry (KSeq i)) (C' ×ˢ D'))
    {S : Set (U × X)} (hS_closed : IsClosed S) (hS_bounded : Bornology.IsBounded S)
    (hS_subset : S ⊆ C ×ˢ D) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ K : U → X → 𝕜,
      IsConcaveConvexOn 𝕜 C D K ∧
        TendstoUniformlyOn (fun i ↦ uncurry (KSeq (φ i))) (uncurry K) atTop S := by
  letI : ProperSpace 𝕜 := .of_locallyCompactSpace 𝕜
  letI : ProperSpace (U × X) := FiniteDimensional.proper (𝕜 := 𝕜) (E := U × X)
  simpa using
    exists_subsequence_tendstoUniformlyOn_on_compact_of_concaveConvexOn_of_dense_pointwiseBoundedOn
      KSeq hC_open hD_open hshape hCD'_subset hdense hbounded
      (Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded) hS_subset

end
