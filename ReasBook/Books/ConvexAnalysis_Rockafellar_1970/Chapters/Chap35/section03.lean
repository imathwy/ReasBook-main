import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_35_3 (from Chap07) -/
section

open Function Set

universe u v w z

variable {𝕜 : Type z} {U : Type u} {V : Type v} {T : Type w}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [CompleteSpace 𝕜]
variable [ClosedIciTopology 𝕜] [ClosedIicTopology 𝕜]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [FiniteDimensional 𝕜 (U × V)]
variable [WeaklyLocallyCompactSpace (U × V)]
variable [TopologicalSpace T] [WeaklyLocallyCompactSpace T]

variable {K : U → V → T → 𝕜}
variable {C C' : Set U} {D D' : Set V}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 35.3 is the joint-continuity theorem for a saddle family
  `K(u, v, t)`, with `u` in a relatively open set `C`, `v` in a relatively open set `D`, and
  `t` in a weakly locally compact parameter space `T`. The source has two clauses: the first
  assumes continuity in `t` for every `u ∈ C` and `v ∈ D`; the second weakens this to continuity on
  a dense product `C' × D'`.
- `core/canonical`: the saddle-shape hypotheses are owned by
  `Bifunction.IsConcaveConvexOn`, the relative-domain hypotheses by `IsRelativelyOpen`, and
  the joint continuity conclusion by canonical owners on product views, namely
  `ContinuousOn` for `Function.uncurry (Function.uncurry K)` on the full product domain, while the
  source continuity hypothesis is kept on the canonical product index `(u, v)`.
- `bridge/view`: Theorem 35.2 is the saddle-family replacement for the Chapter 10 equi-Lipschitz
  estimate, and Theorem 10.7 supplies the canonical product-continuity surface at the
  order-closed scalar-topology layer (`ClosedIciTopology`/`ClosedIicTopology`). The dense-product
  clause is therefore kept as a source-facing companion statement rather than replaced by a new
  wrapper owner.

Domain-style sampling used here:
- `uniformlyBoundedOn_and_equiLipschitzOn_of_generating_product` from
  Theorem 35.2;
- `continuousOn_uncurry_of_convexOn_of_continuous` and
  `continuousOn_uncurry_of_convexOn_of_continuous_dense_subset` from Theorem 10.7 as the
  one-space continuity template;
- `Bifunction.IsConcaveConvexOn`, `Continuous`, and `ContinuousOn` as canonical owners.

Primitive data vs derived API:
- primitive source data: the relatively open sets `C` and `D`, the parameter space `T`, the
  saddle family `K`, the slice-wise shape owner
  `Bifunction.IsConcaveConvexOn 𝕜 C D (K · · t)` for each `t`, and either
  continuity of every `t`-section on `C ×ˢ D` or continuity only on a dense product subset
  `C' ×ˢ D'`;
- derived API: joint continuity of the canonical product view
  `Function.uncurry (Function.uncurry K)` on `((C ×ˢ D) ×ˢ univ)`.

Layer target: `source-facing`, but written on the canonical product-space owner surface.
-/

-- Proof sketch: on a compact neighborhood of `t₀`, continuity of the dense-product fibers
-- `K u v` for `(u, v) ∈ C' ×ˢ D'` gives pointwise boundedness on that dense product subset. Use
-- Theorem 35.2 to obtain a common local Lipschitz bound in `(u, v)` for the family
-- `t ↦ K(·, ·, t)`, then approximate `(u₀, v₀)` by a point of `C' ×ˢ D'` and combine the three
-- resulting estimates exactly as in Rockafellar's proof to deduce continuity at
-- `(u₀, v₀, t₀)`.
/-- Theorem 35.3 (2): the same joint continuity conclusion holds if continuity of `K u v` on `T`
is assumed only for points of a dense product subset `C' × D'` of `C × D`, expressed
intrinsically as `C ×ˢ D ⊆ intrinsicClosure 𝕜 (C' ×ˢ D')`. -/
theorem continuousOn_uncurry_of_continuous_sections_dense_product
    (hC_open : IsRelativelyOpen 𝕜 C)
    (hD_open : IsRelativelyOpen 𝕜 D)
    (hK_shape : ∀ t, Bifunction.IsConcaveConvexOn 𝕜 C D (K · · t))
    (hCD'_subset : C' ×ˢ D' ⊆ C ×ˢ D)
    (hCD'_dense : C ×ˢ D ⊆ intrinsicClosure 𝕜 (C' ×ˢ D'))
    (hK_cont : ∀ p ∈ C' ×ˢ D', Continuous (K p.1 p.2)) :
    ContinuousOn (uncurry (uncurry K)) ((C ×ˢ D) ×ˢ univ) := sorry

/-- Theorem 35.3 (1): if `C` and `D` are relatively open, each `t`-section `(u, v) ↦ K u v t`
is concave-convex on `C × D`, and every fiber `K u v` with `u ∈ C` and `v ∈ D` is continuous on
`T`, then `K` is jointly continuous on `C × D × T`, expressed canonically as continuity of
`Function.uncurry (Function.uncurry K)` on `((C ×ˢ D) ×ˢ univ)`. -/
theorem continuousOn_uncurry_of_continuous_sections
    (hC_open : IsRelativelyOpen 𝕜 C)
    (hD_open : IsRelativelyOpen 𝕜 D)
    (hK_shape : ∀ t, Bifunction.IsConcaveConvexOn 𝕜 C D (K · · t))
    (hK_cont : ∀ p ∈ C ×ˢ D, Continuous (K p.1 p.2)) :
    ContinuousOn (uncurry (uncurry K)) ((C ×ˢ D) ×ˢ univ) := by
  simpa using
    continuousOn_uncurry_of_continuous_sections_dense_product
      (K := K) hC_open hD_open hK_shape Subset.rfl subset_intrinsicClosure hK_cont

end
