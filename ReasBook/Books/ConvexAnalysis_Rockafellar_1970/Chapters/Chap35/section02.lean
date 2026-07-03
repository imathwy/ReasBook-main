

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_35_2 (from Chap07) -/
section

universe u v w z

open Function Set
open scoped Rockafellar

variable {𝕜 : Type w} {ι : Type u} {U : Type v} {X : Type z}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [FiniteDimensional 𝕜 (U × X)]

variable {K : ι → U → X → 𝕜}
variable {C C' : Set U} {D D' : Set X} {P : Set (U × X)}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 35.2 is a family theorem for finite concave-convex functions on
  `C × D`, with a generating product subset `C' × D'` lying in `C × D`, on which the family is
  pointwise bounded, and with the conclusion that the family is uniformly bounded and
  equi-Lipschitz on every compact subset of `C × D` (with closed/bounded phrasing as a bridge
  corollary).
- `core/canonical`: the owner conclusions already exist upstream in Chapter 10 as
  `UniformlyBoundedOn` and `EquiLipschitzOn` for families of `𝕜`-valued functions on one space.
  For a saddle family, the correct owner-level ambient space is the product `U × X`, and the
  canonical family there is `Function.uncurry ∘ K`.
- `bridge/view`: the saddle hypotheses stay source-facing through
  `Bifunction.IsConcaveConvexOn 𝕜 C D` on each family member, while the conclusion is stated
  directly through the Chapter 10 family owners on the uncurried family.

Domain-style sampling used here:
- `PointwiseBoundedOn.uniformlyBoundedOn_and_equiLipschitzOn` from Chapter 10 as the
  owner theorem for uniformly bounded and equi-Lipschitz families;
- `PointwiseBoundedOn`, `UniformlyBoundedOn`, and `EquiLipschitzOn` from Chapter 10;
- `Bifunction.IsConcaveConvexOn` from Definition 33.0.1 as the local saddle-shape owner;
- `uncurry` as the canonical passage from a bifunction family to an ordinary family on
  the product space.

Primitive data vs derived API:
- primitive source data: the relative-openness owners
  `IsRelativelyOpen 𝕜 C` and `IsRelativelyOpen 𝕜 D`, the saddle family `K`,
  the product subset inclusion
  `C' ×ˢ D' ⊆ C ×ˢ D`, the product-generating subset hypothesis
  `C ×ˢ D ⊆ convexHull 𝕜 (intrinsicClosure 𝕜 (C' ×ˢ D'))`, and the pointwise boundedness
  hypothesis on `C' ×ˢ D'`;
- primitive source-facing shape assumptions: for each `i`,
  `Bifunction.IsConcaveConvexOn 𝕜 C D (K i)`;
- derived API: the owner conclusions `UniformlyBoundedOn (Function.uncurry ∘ K) P` and
  `EquiLipschitzOn (Function.uncurry ∘ K) P` on any compact `P ⊆ C ×ˢ D`.

Layer target: `source-facing`, expressed through the canonical Chapter 10 owner conclusions rather
than through a new Chapter 7 family wrapper.

Ambient minimization note:
- the family owner conclusions live on the product ambient space, so this item keeps the
  finite-dimensional assumption at the same canonical layer:
  `[FiniteDimensional 𝕜 (U × X)]`, rather than separate factor assumptions.
-/

-- Proof sketch: enclose the compact subset `P ⊆ C ×ˢ D` in a product `S ×ˢ T` of compact
-- subsets with `S ⊆ C` and `T ⊆ D`. For each `u ∈ C'`, apply Theorem 10.6 to the convex
-- family `fun i ↦ K i u` on `D`, using the projection consequences of
-- `C' ×ˢ D' ⊆ C ×ˢ D`, the generating hypothesis
-- `D ⊆ convexHull 𝕜 (intrinsicClosure 𝕜 D')` coming from the product assumption, and pointwise
-- boundedness on `D'`; this yields a uniform bound on `T`. That bound turns the `v`-slices into a
-- pointwise bounded family of concave functions on `C`, again using the product-subset inclusion,
-- so a second application of
-- Theorem 10.6 gives a common bound and Lipschitz constant on `S`. Repeating the argument in the
-- second variable yields separate Lipschitz control in each coordinate, and the product norm
-- estimate gives one common Lipschitz constant on `S ×ˢ T`, hence on `P`.
/-- Theorem 35.2: a family of finite concave-convex functions on `C × D` that is pointwise
bounded on a generating product subset `C' × D'` contained in `C × D` is uniformly bounded and
equi-Lipschitz on every compact subset of `C × D`. -/
theorem uniformlyBoundedOn_and_equiLipschitzOn_of_generating_product
    (hC_open : IsRelativelyOpen 𝕜 C)
    (hD_open : IsRelativelyOpen 𝕜 D)
    (hK_shape : ∀ i, Bifunction.IsConcaveConvexOn 𝕜 C D (K i))
    (hCD'_subset : C' ×ˢ D' ⊆ C ×ˢ D)
    (hgen : C ×ˢ D ⊆ convexHull 𝕜 (intrinsicClosure 𝕜 (C' ×ˢ D')))
    (hpointwise : PointwiseBoundedOn (Function.uncurry ∘ K) (C' ×ˢ D'))
    (hP_compact : IsCompact P)
    (hP_subset : P ⊆ C ×ˢ D) :
    UniformlyBoundedOn (Function.uncurry ∘ K) P ∧
      EquiLipschitzOn (Function.uncurry ∘ K) P := by
  sorry

/-- Closed/bounded bridge form of Theorem 35.2. -/
theorem
    uniformlyBoundedOn_and_equiLipschitzOn_of_generating_product_of_closed_bounded
    [ProperSpace (U × X)]
    (hC_open : IsRelativelyOpen 𝕜 C)
    (hD_open : IsRelativelyOpen 𝕜 D)
    (hK_shape : ∀ i, Bifunction.IsConcaveConvexOn 𝕜 C D (K i))
    (hCD'_subset : C' ×ˢ D' ⊆ C ×ˢ D)
    (hgen : C ×ˢ D ⊆ convexHull 𝕜 (intrinsicClosure 𝕜 (C' ×ˢ D')))
    (hpointwise : PointwiseBoundedOn (Function.uncurry ∘ K) (C' ×ˢ D'))
    (hP_closed : IsClosed P)
    (hP_bounded : Bornology.IsBounded P)
    (hP_subset : P ⊆ C ×ˢ D) :
    UniformlyBoundedOn (Function.uncurry ∘ K) P ∧
      EquiLipschitzOn (Function.uncurry ∘ K) P := by
  exact uniformlyBoundedOn_and_equiLipschitzOn_of_generating_product
    hC_open hD_open hK_shape hCD'_subset hgen hpointwise
    (Metric.isCompact_of_isClosed_isBounded hP_closed hP_bounded) hP_subset

end
