import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_35_1 (from Chap07) -/
noncomputable section

open Function Set

section

variable {𝕜 : Type*} {U : Type*} {V : Type*}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable {K : U → V → 𝕜} {C : Set U} {D : Set V}

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 35.1 says that a finite concave-convex function on a product
  `C × D` of relatively open convex sets is continuous relative to `C × D`, and in fact is
  Lipschitzian on every compact subset of `C × D` (with closed/bounded phrasing as a bridge).
- `core/canonical`: the local shape data are canonically owned by
  `IsConcaveConvexOn 𝕜 C D K`, while the regularity conclusions are
  `LipschitzOnWith` and `ContinuousOn` for the product view `Function.uncurry K`.
- `bridge/view`: passing from the curried bifunction `K : U → V → 𝕜` to
  `Function.uncurry K : U × V → 𝕜` is only the standard product view, not a second owner.

Domain-style sampling used here:
- `IsConcaveConvexOn` from Definition 33.0.1 as the local saddle-shape owner;
- `PointwiseBoundedOn.uniformlyBoundedOn_and_equiLipschitzOn` from Theorem 10.6;
- `LipschitzOnWith` and `ContinuousOn` as the canonical regularity owners.

Primitive data vs derived API:
- primitive source data: the relatively open sets `C`, `D`, the `𝕜`-valued bifunction `K`,
  and the local saddle-shape owner `IsConcaveConvexOn 𝕜 C D K`;
- derived API: the Lipschitz control on compact subsets of `C ×ˢ D` (and its closed/bounded
  bridge corollary), and the continuity conclusion on `C ×ˢ D`.

Layer target: `source-facing`. The global Chapter 34 predicate `SaddleFunction.IsConcaveConvex`
is not the main owner here, because Theorem 35.1 is local on the specific source domains `C`
and `D`, whereas `IsConcaveConvex` is a whole-space notion that does not encode those local
domains.

Ambient layer note:
- this file keeps the same ambient typeclass layer as the reused Chapter 10 bridge
  `PointwiseBoundedOn.uniformlyBoundedOn_and_equiLipschitzOn`;
- the closed/bounded bridge uses `[ProperSpace (U × V)]` as the ambient compactness bridge
  from `IsClosed` + `Bornology.IsBounded` to `IsCompact`.
-/

namespace IsConcaveConvexOn

/-- Theorem 35.1, canonical compact-subset Lipschitz clause: if `C` and `D` are relatively open
and `K` is concave-convex on `C × D` in the canonical owner sense
`IsConcaveConvexOn 𝕜 C D K`, then every compact subset of `C ×ˢ D` admits one Lipschitz constant
for the canonical product view `uncurry K`. -/
-- Proof sketch: given a compact `S ⊆ C ×ˢ D`, project it to compact subsets of `C` and `D`. The
-- two slice hypotheses extracted from `hK_shape` provide the concavity/convexity inputs needed for
-- the two one-variable applications of Theorem 10.6, yielding coordinatewise Lipschitz control;
-- combining those bounds gives one Lipschitz constant on `S`.
theorem exists_lipschitzOnWith_uncurry
    [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 (U × V)]
    (hK_shape : IsConcaveConvexOn 𝕜 C D K)
    (hC_open : IsRelativelyOpen 𝕜 C) (hD_open : IsRelativelyOpen 𝕜 D)
    {S : Set (U × V)}
    (hS_compact : IsCompact S)
    (hS_subset : S ⊆ C ×ˢ D) :
    ∃ α : NNReal, LipschitzOnWith α (uncurry K) S := by
  sorry

/-- Closed/bounded bridge form of the Lipschitz clause in Theorem 35.1. -/
theorem exists_lipschitzOnWith_uncurry_of_isClosed_isBounded
    [CompleteSpace 𝕜]
    [ProperSpace (U × V)]
    [FiniteDimensional 𝕜 (U × V)]
    (hK_shape : IsConcaveConvexOn 𝕜 C D K)
    (hC_open : IsRelativelyOpen 𝕜 C) (hD_open : IsRelativelyOpen 𝕜 D)
    {S : Set (U × V)}
    (hS_closed : IsClosed S) (hS_bounded : Bornology.IsBounded S)
    (hS_subset : S ⊆ C ×ˢ D) :
    ∃ α : NNReal, LipschitzOnWith α (uncurry K) S := by
  simpa using
    IsConcaveConvexOn.exists_lipschitzOnWith_uncurry
      (hK_shape := hK_shape)
      hC_open hD_open
      (Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded) hS_subset

/-- Theorem 35.1: if `C` and `D` are relatively open and the bifunction `K` is concave on `C` in
its first variable and convex on `D` in its second variable (equivalently:
`IsConcaveConvexOn 𝕜 C D K`), then `K` is continuous relative to `C ×ˢ D`,
expressed canonically as continuity of `uncurry K` on `C ×ˢ D`. -/
-- Proof sketch: for each point `(u, v) ∈ C ×ˢ D`, relative openness yields a local neighborhood
-- inside `C ×ˢ D` whose compact closure stays in `C ×ˢ D`. The compact-subset theorem above gives
-- a Lipschitz bound on that closure, hence continuity near `(u, v)`. Since every point of
-- `C ×ˢ D` admits such a neighborhood, the product view `uncurry K` is continuous on `C ×ˢ D`.
theorem continuousOn_uncurry
    [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 (U × V)]
    (hK_shape : IsConcaveConvexOn 𝕜 C D K)
    (hC_open : IsRelativelyOpen 𝕜 C) (hD_open : IsRelativelyOpen 𝕜 D)
    : ContinuousOn (uncurry K) (C ×ˢ D) := by
  sorry

end IsConcaveConvexOn

end Bifunction

end
