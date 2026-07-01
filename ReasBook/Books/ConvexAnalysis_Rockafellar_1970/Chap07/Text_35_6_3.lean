import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_5_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_5_2

noncomputable section

open scoped Rockafellar

universe u v w

namespace Bifunction

section

variable {𝕜 : Type w} [Add 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [Sub U] [Sub V]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.3 defines the saddle subdifferential `∂K(u, v)` of a
  concave-convex bifunction at `(u, v)` as the product of the first and second partial
  subdifferentials.
- `core/canonical`: the owner abstraction in this chapter is the pointwise set-valued map
  `Bifunction.subdifferentialAt`, together with its coordinate-membership theorem
  `Bifunction.mem_subdifferentialAt`.
- `bridge/view`: the notation `d(K ; u, v)` is the source-facing surface notation for that owner;
  the explicit-carrier form `d(K ; u, v | YU, YV)` is the thin ambient-parameter bridge when
  inference needs help.

Primary mathematical domain:
- convex analysis of saddle bifunctions and their partial subdifferentials.

Domain-style sampling used here:
- `Bifunction.subdifferential1At` from `Text_35_5_1`;
- `Bifunction.subdifferential2At` from `Text_35_5_2`;
- the one-variable owner pattern `_root_.subdifferentialAt` from `Chap05.Definition_23_0_6`;
- the one-variable concave owner pattern `_root_.concaveSubdifferentialAt` from
  `Chap06.Definition_6_30_5`.

Primitive data vs derived API:
- primitive source data: the two already-owned partial subdifferentials
  `subdifferential1At K u v` and `subdifferential2At K u v`;
- primitive owner defined here: their product `subdifferentialAt K u v`;
- derived API: the pairing-level notation `d(K ; u, v)` (with inferred pairings), its explicit
  carrier form `d(K ; u, v | YU, YV)`, the canonical strong-dual bridge
  `subdifferentialAtDual` with notation `∂ₛ K(u, v)`, and the coordinate membership theorems
  `mem_subdifferentialAt` / `mem_subdifferentialAtDual`.

Layer target: `source-facing`.

Notation evaluation:
- the source-facing pairing-level notation is `d(K ; u, v)` and infers carriers from context;
- the pairing-parametric owner remains available as `d(K ; u, v | YU, YV)` when needed;
- the strong-dual theorem surface needs its own inference-stable notation, parallel to
  `∂₁ K(u, v)` and `∂₂ K(u, v)`, so this file exposes the canonical bridge as `∂ₛ K(u, v)`.
-/

/-- Text 35.6.3: the saddle subdifferential of a concave-convex bifunction `K` at `(u, v)` is
the product of the already-owned first and second partial subdifferentials. -/
def subdifferentialAt (K : U → V → WithTopBot 𝕜) (u : U) (v : V)
    (YU : Type*) [HasPairing U YU 𝕜]
    (YV : Type*) [HasPairing V YV 𝕜] : Set (YU × YV) :=
  ∂₁[YU]K(u, v) ×ˢ ∂₂[YV]K(u, v)

/- Explicit dual-carrier variant of the Rockafellar saddle-subdifferential notation. -/
scoped[Rockafellar] notation "d(" k " ; " u ", " v " | " yu ", " yv ")" =>
  Bifunction.subdifferentialAt k u v yu yv

/- Source-facing notation with inferred pairing carriers. -/
scoped[Rockafellar] notation "d(" k " ; " u ", " v ")" =>
  Bifunction.subdifferentialAt k u v _ _

/-- Coordinate membership form of the saddle subdifferential product owner. -/
@[simp] theorem mem_subdifferentialAt
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V}
    {YU : Type*} [HasPairing U YU 𝕜]
    {YV : Type*} [HasPairing V YV 𝕜]
    {p : YU × YV} :
    p ∈ d(K ; u, v) ↔
      p.1 ∈ ∂₁[YU]K(u, v) ∧ p.2 ∈ ∂₂[YV]K(u, v) :=
  Iff.rfl

end

section

variable {𝕜 : Type w} [NormedField 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Canonical strong-dual bridge for Text 35.6.3. The notation `∂ₛ K(u, v)` uses the intrinsic
continuous-dual product, while `d(K ; u, v | YU, YV)` remains the explicit pairing-level view
when type inference needs help. -/
abbrev subdifferentialAtDual (K : U → V → WithTopBot 𝕜) (u : U) (v : V) :
    Set (StrongDual 𝕜 U × StrongDual 𝕜 V) :=
  subdifferentialAt K u v (StrongDual 𝕜 U) (StrongDual 𝕜 V)

scoped[Rockafellar] notation "∂ₛ" K "(" u ", " v ")" =>
  Bifunction.subdifferentialAtDual K u v

/-- Strong-dual membership form of the saddle subdifferential product owner. -/
@[simp] theorem mem_subdifferentialAtDual
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V}
    {p : StrongDual 𝕜 U × StrongDual 𝕜 V} :
    p ∈ ∂ₛ K(u, v) ↔ p.1 ∈ ∂₁ K(u, v) ∧ p.2 ∈ ∂₂ K(u, v) :=
  Iff.rfl

end

end Bifunction
