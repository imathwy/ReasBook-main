import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6

noncomputable section

universe u v w

open scoped Rockafellar

namespace Bifunction

section

variable {𝕜 : Type w} [Add 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [Sub V]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.5.2 introduces the second partial subdifferential `d₂ K(u, v)`,
  i.e. the subgradients in the second variable of a bifunction.
- `core/canonical`: the owner abstraction already exists upstream as
  `_root_.subdifferentialAt`, together with its pointwise characterization
  `_root_.mem_subdifferentialAt`.
- `bridge/view`: the source notion is exactly the Chapter 23 owner applied to the second-variable
  slice `K u`.

Domain-style sampling used here:
- `_root_.subdifferentialAt` from `Chap05.Definition_23_0_6`;
- `_root_.mem_subdifferentialAt_pairing` and `_root_.mem_subdifferentialAt` from the same file.

Primitive data vs derived API:
- primitive data: a bifunction `K : U → V → WithTopBot 𝕜` and a base point `(u, v)`;
- primitive owner: the canonical one-variable owner `_root_.subdifferentialAt` on the
  second-variable slice `K u` at `v`;
- derived API: the source-facing bridge name `subdifferential2At` and its pointwise membership
  theorem.

Layer target: `bridge/view`. This file owns the chapter-level bifunction bridge, not a second
primitive subgradient object.

Scalar/codomain boundary:
- this bridge is stated directly at the primitive pairing layer (`Add` + `LE`) and keeps
  strong-dual specialization as a downstream view.

Notation evaluation:
- the second partial owner recurs throughout Chapter 35, so this file exposes the source-facing
  surface `∂₂ K(u, v)` and the explicit-codomain form `∂₂[Y]K(u, v)` instead of forcing later
  theorem surfaces to spell the raw bridge name.
-/

/-- Text 35.5.2: the second partial subdifferential of a bifunction `K` at `(u, v)` is the
subdifferential of the second-variable slice `K(u, ·)` at `v`, on the canonical pairing
owner layer. -/
abbrev subdifferential2At (K : U → V → WithTopBot 𝕜) (u : U) (v : V)
    (Y : Type*) [HasPairing V Y 𝕜] : Set Y :=
  (_root_.subdifferentialAt (Y := Y) (K u) v : Set Y)

scoped[Rockafellar] notation "∂₂[" Y "]" K "(" u ", " v ")" =>
  Bifunction.subdifferential2At K u v Y

/-- Pairing-level membership form of the second partial subdifferential. -/
@[simp] theorem mem_subdifferential2At_pairing
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V}
    {Y : Type*} [HasPairing V Y 𝕜] {vStar : Y} :
    vStar ∈ ∂₂[Y]K(u, v) ↔
      ∀ v', K u v' ≥ K u v + ((⟪v' - v, vStar⟫ₚ : 𝕜) : WithTopBot 𝕜) :=
  by
    change vStar ∈ (_root_.subdifferentialAt (Y := Y) (K u) v) ↔
        ∀ v', K u v' ≥ K u v + ((⟪v' - v, vStar⟫ₚ : 𝕜) : WithTopBot 𝕜)
    exact _root_.mem_subdifferentialAt_pairing (f := K u) (x := v) (Y := Y) (xStar := vStar)

/-- Under the primitive owner layer, `∂₂[Y]K(u, v)` is definitionally the one-variable
subdifferential owner of the second-variable slice `K u` at `v`. -/
@[simp] theorem subdifferential2At_eq_subdifferentialAt
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V}
    {Y : Type*} [HasPairing V Y 𝕜] :
    (∂₂[Y]K(u, v)) = (_root_.subdifferentialAt (Y := Y) (K u) v) :=
  rfl

/-- Notation-surface variant of `subdifferential2At_eq_subdifferentialAt`, keeping the bridge on
the short canonical owner notation used in chapter statements. -/
@[simp] theorem subdifferential2At_eq_subdifferentialAt_notation
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V}
    {Y : Type*} [HasPairing V Y 𝕜] :
    (∂₂[Y]K(u, v)) = (∂[Y](K u)(v)) :=
  rfl

end

section

variable {𝕜 : Type w} [NormedField 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Canonical strong-dual bridge for Text 35.5.2. The plain notation `∂₂ K(u, v)` uses this
strong-dual carrier, while `∂₂[Y]K(u, v)` remains the explicit pairing-level view. -/
abbrev subdifferential2AtDual (K : U → V → WithTopBot 𝕜) (u : U) (v : V) :
    Set (StrongDual 𝕜 V) :=
  subdifferential2At K u v (StrongDual 𝕜 V)

scoped[Rockafellar] notation "∂₂" K "(" u ", " v ")" =>
  Bifunction.subdifferential2AtDual K u v

/-- A continuous linear functional belongs to the second partial subdifferential of `K` at
`(u, v)` exactly when it gives the source affine-support inequality for the second-variable
slice. -/
@[simp] theorem mem_subdifferential2At
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V} {vStar : StrongDual 𝕜 V} :
    vStar ∈ ∂₂ K(u, v) ↔
      ∀ v', K u v' ≥ K u v + ((vStar (v' - v) : 𝕜) : WithTopBot 𝕜) :=
  by
    change vStar ∈ (_root_.subdifferentialAt (Y := StrongDual 𝕜 V) (K u) v) ↔
        ∀ v', K u v' ≥ K u v + ((vStar (v' - v) : 𝕜) : WithTopBot 𝕜)
    exact _root_.mem_subdifferentialAt (f := K u) (x := v) (xStar := vStar)

end

end Bifunction
