import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_5

noncomputable section

universe u v

open scoped Rockafellar

namespace Bifunction

section

variable {𝕜 : Type*} [Add 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [Sub U]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.5.1 introduces the first partial subdifferential of a bifunction,
  namely the concave subgradients of the first-variable slice `fun u' ↦ K u' v` at `u`.
- `core/canonical`: the owner abstraction already present upstream is
  `_root_.concaveSubdifferentialAt`, together with its pointwise characterization
  `_root_.mem_concaveSubdifferentialAt`.
- `bridge/view`: this file's chapter owner is exactly that canonical owner specialized to a fixed
  second-variable slice.

Domain-style sampling used here:
- `_root_.concaveSubdifferentialAt` from `Chap06.Definition_6_30_5`;
- `_root_.mem_concaveSubdifferentialAt` from the same file.

Primitive data vs derived API:
- primitive owner data: the canonical dual-valued slice owner
  `_root_.concaveSubdifferentialAt (fun u' ↦ K u' v) u`;
- derived API: the chapter bridge owner `subdifferential1At` and its pointwise membership
  theorem.

Layer target: `bridge/view` on the intrinsic dual-pairing owner. The vector-valued first partial
subdifferential is intentionally demoted to a downstream inner-product bridge module.

Notation evaluation:
- the first partial owner recurs throughout Chapter 35, so this file keeps the explicit-codomain
  bridge form `∂₁[Y]K(u, v)` for the pairing-level view and keeps the plain surface
  `∂₁ K(u, v)` as notation-level specialization to the strong-dual carrier.
-/

/-- Text 35.5.1: the first partial subdifferential of a bifunction `K` at `(u, v)` is the
concave subdifferential of the first-variable slice `fun u' ↦ K u' v` at `u`, on the canonical
pairing owner layer. -/
abbrev subdifferential1At (K : U → V → WithTopBot 𝕜) (u : U) (v : V)
    (Y : Type*) [HasPairing U Y 𝕜] : Set Y :=
  (∂⁺[Y] (fun u' ↦ K u' v)(u))

scoped[Rockafellar] notation "∂₁[" Y "]" K "(" u ", " v ")" =>
  Bifunction.subdifferential1At K u v Y

/-- Pairing-level membership form of the first partial subdifferential. -/
@[simp] theorem mem_subdifferential1At_pairing
    {K : U → V → WithTopBot 𝕜} {u : U} {Y : Type*} [HasPairing U Y 𝕜] {uStar : Y} {v : V} :
    uStar ∈ (∂₁[Y]K(u, v)) ↔
      ∀ u', K u' v ≤ K u v + ((⟪u' - u, uStar⟫ₚ : 𝕜) : WithTopBot 𝕜) :=
  by
    simpa only [Bifunction.subdifferential1At] using
      (_root_.mem_concaveSubdifferentialAt_pairing
        (g := fun u' ↦ K u' v) (x := u) (xStar := uStar) (Y := Y))

end

section

variable {𝕜 : Type*} [NormedField 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]

/- Canonical strong-dual bridge for Text 35.5.1. The plain notation `∂₁ K(u, v)` uses this
strong-dual carrier, while `∂₁[Y]K(u, v)` remains the explicit pairing-level view. -/

/-- Canonical strong-dual bridge for Text 35.5.1. -/
abbrev subdifferential1AtDual (K : U → V → WithTopBot 𝕜) (u : U) (v : V) :
    Set (StrongDual 𝕜 U) :=
  subdifferential1At K u v (StrongDual 𝕜 U)

scoped[Rockafellar] notation "∂₁" K "(" u ", " v ")" =>
  Bifunction.subdifferential1AtDual K u v

/-- A continuous functional belongs to the first partial subdifferential of `K` at `(u, v)`
exactly when it gives the source affine-support inequality for the first-variable slice. -/
@[simp] theorem mem_subdifferential1At
    {K : U → V → WithTopBot 𝕜} {u : U} {uStar : StrongDual 𝕜 U} {v : V} :
    uStar ∈ (∂₁ K(u, v)) ↔
      ∀ u', K u' v ≤ K u v + ((uStar (u' - u) : 𝕜) : WithTopBot 𝕜) := by
  simpa only [Bifunction.subdifferential1AtDual, Bifunction.subdifferential1At] using
    (_root_.mem_concaveSubdifferentialAt
      (g := fun u' ↦ K u' v) (x := u) (xStar := uStar))

end

end Bifunction
