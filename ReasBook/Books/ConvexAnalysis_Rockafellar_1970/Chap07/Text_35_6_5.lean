import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_6_3

noncomputable section

open scoped Rockafellar

universe u v

namespace Bifunction

section

variable {𝕜 : Type*} [NormedField 𝕜] [PartialOrder 𝕜]
variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.5 states that for each base point `(u, v)`, the saddle
  subdifferential `∂K(u, v)` is a possibly empty closed convex subset of the product space.
- `core/canonical`: the chapter already owns this set as `Bifunction.subdifferentialAt`.
- `bridge/view`: the canonical carrier for this regularity statement is the strong-dual product
  `StrongDual 𝕜 U × StrongDual 𝕜 V`; the Euclidean vector-valued bridge is downstream-only and
  should not be the main theorem surface here.

Primary mathematical domain:
- convex analysis of saddle bifunctions and their canonical dual-valued subdifferentials.

Domain-style sampling used here:
- `Bifunction.subdifferential1At` from `Text_35_5_1`;
- `Bifunction.subdifferential2At` from `Text_35_5_2`;
- `Bifunction.subdifferentialAt` and `Bifunction.mem_subdifferentialAt` from `Text_35_6_3`;
- product lemmas for `IsClosed` and `Convex` on set products.

Primitive data vs derived API:
- primitive owner data already exist upstream: the two partial strong-dual subdifferentials and
  their product owner `∂ₛ K(u, v)`;
- derived API here: the closedness and convexity regularity statement for that canonical product
  owner.

Layer target: `source-facing`.

Ambient-assumption minimization:
- the source is written on `ℝ^m × ℝ^n`, but the regularity argument only needs the normed-space
  structure required by the chapter's canonical strong-dual subdifferential owners;
- inner-product, completeness, and finite-dimensional assumptions belong only to the Euclidean
  bridge files, not to this owner-level theorem.
-/

-- Proof sketch: write the saddle subdifferential as the product of the already-owned first and
-- second partial strong-dual subdifferentials, and combine the two partial regularity hypotheses
-- with the product lemmas for closed and convex sets.
/-- Text 35.6.5: for every base point `(u, v)`, the saddle subdifferential is a possibly empty
closed convex subset of the canonical dual product `StrongDual 𝕜 U × StrongDual 𝕜 V`. -/
theorem isClosed_and_convex_subdifferentialAt
    (K : U → V → WithTopBot 𝕜) (u : U) (v : V)
    (h₁_isClosed : IsClosed (∂₁K(u, v))) (h₂_isClosed : IsClosed (∂₂K(u, v)))
    (h₁_convex : Convex 𝕜 (∂₁K(u, v))) (h₂_convex : Convex 𝕜 (∂₂K(u, v))) :
    IsClosed (∂ₛ K(u, v)) ∧ Convex 𝕜 (∂ₛ K(u, v)) := by
  simpa [subdifferentialAtDual, subdifferentialAt] using
    (show
        IsClosed (∂₁K(u, v) ×ˢ ∂₂K(u, v)) ∧
          Convex 𝕜 (∂₁K(u, v) ×ˢ ∂₂K(u, v)) from
      ⟨h₁_isClosed.prod h₂_isClosed, h₁_convex.prod h₂_convex⟩)

theorem subdifferentialAt_isClosed
    (K : U → V → WithTopBot 𝕜) (u : U) (v : V)
    (h₁_isClosed : IsClosed (∂₁K(u, v))) (h₂_isClosed : IsClosed (∂₂K(u, v))) :
    IsClosed (∂ₛ K(u, v)) :=
  by
    simpa [subdifferentialAtDual, subdifferentialAt] using h₁_isClosed.prod h₂_isClosed

theorem subdifferentialAt_convex
    (K : U → V → WithTopBot 𝕜) (u : U) (v : V)
    (h₁_convex : Convex 𝕜 (∂₁K(u, v))) (h₂_convex : Convex 𝕜 (∂₂K(u, v))) :
    Convex 𝕜 (∂ₛ K(u, v)) :=
  by
    simpa [subdifferentialAtDual, subdifferentialAt] using h₁_convex.prod h₂_convex

end

end Bifunction
