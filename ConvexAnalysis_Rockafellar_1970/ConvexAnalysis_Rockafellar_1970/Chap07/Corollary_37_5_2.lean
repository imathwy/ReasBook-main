import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_7
import ConvexAnalysis_Rockafellar_1970.Chap07.Corollary_37_5_1

noncomputable section

open scoped Rockafellar SetRel

universe u v w

namespace Bifunction

section

variable {𝕜 : Type w} [Add 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [Sub U] [Sub V]
variable {YU : Type*} {YV : Type*}
variable [HasPairing U YU 𝕜] [HasPairing V YV 𝕜]
variable [Neg YU]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 37.5.2 gives monotonicity (and later maximal monotonicity) for the
  saddle-subdifferential after the standard sign flip on the first dual coordinate.
- `core/canonical`: the underlying graph owner is already
  `subdifferentialGraphPairing : SetRel (U × V) (YU × YV)` from Corollary 37.5.1, and monotonicity
  is owned by `SetRel.Monotone`.
- `bridge/view`: this file introduces the dedicated sign-flip graph owner
  `subdifferentialGraphPairingSignFlip` with source-facing notation
  `gphdsf[YU, YV](K)`, i.e. the canonical pullback view of `gphd[YU, YV](K)` under the
  first-dual-coordinate sign map.

Domain-style sampling used here:
- `Bifunction.subdifferentialGraphPairing` and
  `Bifunction.mem_subdifferentialGraphPairing` from `Chap07.Corollary_37_5_1`;
- `SetRel.Monotone` from `Chap05.Definition_5_24_7`.

Primitive data vs derived API:
- primitive source data: `K` and `subdifferentialGraphPairing K`;
- primitive bridge map: `(u⋆, v⋆) ↦ (-u⋆, v⋆)`;
- derived API: the sign-flip graph owner and notation `gphdsf[_, _](·)`, plus pointwise membership
  and monotonicity.

Layer target: `bridge/view`.

Abstraction boundary notes:
- the scalar/codomain layer is upstream-owned in `subdifferentialAt` and
  `subdifferentialGraphPairing` (Text 35.6.4 and Corollary 37.5.1), so this file normalizes the
  relation owner surface without introducing a second codomain owner.
-/

/-- Corollary 37.5.2 sign-flip graph owner on the intrinsic pairing layer:
pull `subdifferentialGraphPairing K` back along the first-dual-coordinate sign map. -/
abbrev subdifferentialGraphPairingSignFlip
    (K : U → V → WithTopBot 𝕜) : SetRel (U × V) (YU × YV) :=
  (Prod.map id (fun q : YU × YV ↦ (-q.1, q.2))) ⁻¹'
    gphd[YU, YV](K)

scoped[Rockafellar] notation "gphdsf[" YU ", " YV "](" K ")" =>
  Bifunction.subdifferentialGraphPairingSignFlip (YU := YU) (YV := YV) K

/-- Pointwise membership in the Corollary 37.5.2 sign-flipped graph view. -/
@[simp] theorem mem_subdifferentialGraphPairing_signFlip
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V} {uStar : YU} {vStar : YV} :
    (u, v) ~[gphdsf[YU, YV](K)] (uStar, vStar) ↔
      (u, v) ~[gphd[YU, YV](K)] (-uStar, vStar) := by
  simp

end

section

variable {𝕜 : Type w} [Add 𝕜] [LE 𝕜]
variable {U : Type u} {V : Type v}
variable [Sub U] [Sub V]
variable [HasPairing U U 𝕜] [HasPairing V V 𝕜]
variable [Neg U]

/-- Pointwise membership in the self-pairing sign-flipped saddle-subdifferential graph. -/
@[simp] theorem mem_subdifferentialGraph_signFlip
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V} {uStar : U} {vStar : V} :
    (u, v) ~[gphdsf[U, V](K)] (uStar, vStar) ↔
      (u, v) ~[gphd[U, V](K)] (-uStar, vStar) := by
  simpa using
    (mem_subdifferentialGraphPairing_signFlip
      (K := K) (u := u) (v := v) (uStar := uStar) (vStar := vStar)
      (YU := U) (YV := V))

end

section

variable {𝕜 : Type w} [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {U : Type u} {V : Type v}
variable [AddCommMonoid U] [SMul 𝕜 U] [Sub U]
variable [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
variable {YU : Type*} {YV : Type*}
variable [HasPairing U YU 𝕜] [HasPairing V YV 𝕜]
variable [Neg YU] [Sub YU] [Sub YV]

/-- Corollary 37.5.2, monotonicity clause: for a concave-convex saddle-function,
the sign-flipped saddle-subdifferential graph relation is monotone on the intrinsic pairing layer
`(U × V) ↔ (YU × YV)`. -/
theorem monotone_subdifferentialGraphPairing_signFlip
    {K : U → V → WithTopBot 𝕜}
    (hK_shape : SaddleFunction.IsConcaveConvex 𝕜 K) :
    Mon[𝕜](gphdsf[YU, YV](K)) := by
  let _ := hK_shape
  sorry

end

section

variable {𝕜 : Type w} [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {U : Type u} {V : Type v}
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
variable [HasPairing U U 𝕜] [HasPairing V V 𝕜]

/-!
For maximal monotonicity, this file follows the self-pairing owner used upstream by the Minty-map
homeomorphism theorem in Corollary 37.5.1 (`gphd[U, V](K) : SetRel (U × V) (U × V)`). This
clause therefore stays on the same scalar-parametric self-pairing abstraction layer as
Corollary 37.5.1, rather than specializing to Euclidean finite-dimensional models.
-/

/-- Corollary 37.5.2, maximal clause: for a closed proper concave-convex saddle-function,
the sign-flipped saddle-subdifferential graph relation is maximal monotone on the self-pairing
pairing owner layer. -/
theorem maximal_monotone_subdifferentialGraph_signFlip
    {K : U → V → WithTopBot 𝕜}
    (hK_shape : SaddleFunction.IsConcaveConvex 𝕜 K)
    (hK_closed : SaddleFunction.IsClosed K)
    (hK_proper : SaddleFunction.IsProper K) :
    Maximal (·.Monotone 𝕜) (gphdsf[U, V](K)) := by
  let _ := hK_shape
  let _ := hK_closed
  let _ := hK_proper
  sorry

end

end Bifunction
