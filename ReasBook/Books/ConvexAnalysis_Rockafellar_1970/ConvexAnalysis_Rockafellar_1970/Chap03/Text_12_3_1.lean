import ConvexAnalysis_Rockafellar_1970.Chap01.Text_1_13
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

section Graph

variable {𝕜 X Y : Type*}
  [Ring 𝕜]
  [AddCommGroup X] [Module 𝕜 X]
  [AddCommGroup Y] [Module 𝕜 Y]

local notation "X⋆" => Module.Dual 𝕜 X
local notation "Y⋆" => Module.Dual 𝕜 Y
local notation "P" => X × Y
local notation "P⋆" => X⋆ × Y⋆

/-!
Abstraction checks:
- codomain/ambient layer: the support-cut owner is the chapter-canonical
  `Function.toWithTopBotOn`, so theorem surfaces stay on `WithTopBot 𝕜` without exposing raw
  piecewise plumbing.
- scalar structure: `LinearMap.dualMap`, affine-map algebra, and subtraction only require
  `[Ring 𝕜]`; no commutativity assumption is used.
- owner choice: declarations are exposed under `AffineMap` (intrinsic owner of the graph data),
  not under the over-concrete namespace `ConvexERealFunction`.
- topology/intrinsic language: this item is affine-pairing algebraic; no ambient topology owner is
  needed.
- naming/notation: the existing conjugate notation `f⋆` and graph owner `AffineMap.graph` already
  give the source-facing surface without extra custom notation.

Source/core/bridge triage for this item.

- `source-facing`: Text 12.3.1 gives the conjugate formula for a partial affine function with
  finite locus cut out by an affine graph.
- `core/canonical`: the owner operations are `convexConjugate` for Fenchel conjugation,
  the intrinsic support-cut owner `Function.toWithTopBotOn` for the finite-domain cut, and
  `AffineMap.graph` for the affine graph on which the function is finite.
- `bridge/view`: concrete coordinate specializations are downstream bridges. The core theorem
  itself lives at the pairing layer with dual variables in `Module.Dual`.

Domain-style sampling used here:
- `convexConjugate`;
- `Function.toWithTopBotOn`;
- `AffineMap.graph`;
- `AffineSubspace.map` (with `AffineEquiv.prodComm`);
- `LinearMap.dualMap`;
- the indicator/support-cut bridge language from Chapter 1.

Primitive data vs derived API:
- primitive inputs here: the affine functional `g : X →ᵃ[𝕜] 𝕜` and the affine graph map
  `T : X →ᵃ[𝕜] Y`;
- the intrinsic source-facing owner is the partial-affine support cut
  `realBranch.toWithTopBotOn support` on an affine graph;
- the affine-dual graph map `conjugateGraphMap g T` is derived API from those primitives.

Layer target: `core/canonical`. The main theorem is stated on the primal/dual pairing layer
`(X × Y, X⋆ × Y⋆)` and keeps concrete coordinate specializations as downstream bridges.
-/

namespace AffineMap

/-- The affine map cutting out the dual graph support in the conjugate of a partial-affine
support cut along `T.graph`. -/
def conjugateGraphMap (g : X →ᵃ[𝕜] 𝕜) (T : X →ᵃ[𝕜] Y) : Y⋆ →ᵃ[𝕜] X⋆ :=
  (-(LinearMap.dualMap T.linear)).toAffineMap +
    AffineMap.const 𝕜 Y⋆ g.linear

section Conjugate

variable [SupSet (WithTopBot 𝕜)]

/-- Text 12.3.1 in intrinsic affine-support form: the conjugate of a partial affine support cut on
the graph of `T` is again partial affine, now supported on the graph of the canonical dual affine
map `conjugateGraphMap g T`. -/
theorem convexConjugate_partialAffine_on_graph
    (g : X →ᵃ[𝕜] 𝕜) (T : X →ᵃ[𝕜] Y) :
    ((fun z : P ↦ g z.1).toWithTopBotOn T.graph)⋆ =
      (fun zStar : P⋆ ↦ ⟪T 0, zStar.2⟫ₚ - g 0).toWithTopBotOn
        (((conjugateGraphMap g T).graph).map (AffineEquiv.prodComm 𝕜 Y⋆ X⋆)) := sorry

end Conjugate

end AffineMap

end Graph
