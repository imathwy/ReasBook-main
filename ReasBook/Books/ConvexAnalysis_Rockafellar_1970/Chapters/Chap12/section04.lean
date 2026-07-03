import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_12_4 (from Chap03) -/
noncomputable section

open scoped Rockafellar

section

variable {ι : Type*} {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]

local notation "E" => ι → 𝕜
local notation "Quadrant" => orthant[𝕜](E)
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)
variable [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 12.4 says that orthant Fenchel conjugation preserves the class of
  nondecreasing lower semicontinuous convex functions on the non-negative orthant whose origin
  value is finite in the chapter sense `⊥ < g 0 ∧ g 0 < ⊤`, and that this orthant-side
  conjugation is involutive on that class.
- `core/canonical`: the orthant owner is the inherited `convexConjugate` on
  `Quadrant`, together with `g.IsMonotoneClosedConvexOnQuadrant`; the ambient owner
  reused here is `Function.IsClosedProperConvex`, and the proof uses the primitive Chapter 12
  owner lemmas `Function.isConvex_convexConjugate`,
  `Function.IsConvex.convexConjugate_isProper_iff`,
  `lowerSemicontinuous_convexConjugate`,
  `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull`, and
  `lowerSemicontinuousHull_eq_self`.
- `bridge/view`: `orthantAbsExtension` and
  `convexConjugate_orthantAbsExtension_eq_convexConjugate_comp_coordinatewiseAbsQuadrant` from
  Text 12.3.6 identify orthant monotone conjugation with ordinary Fenchel conjugation on the
  ambient absolute-value extension, so this file does not introduce a second conjugacy owner.

Domain-style sampling used here:
- the chapter owner `convexConjugate` from Definitions 12.2 and 12.4;
- the chapter owner predicate `Function.IsMonotoneClosedConvexOnQuadrant` from Text 12.3.6;
- the ambient owner predicate `Function.IsClosedProperConvex` and its owner lemmas
  `Function.isConvex_convexConjugate`,
  `Function.IsConvex.convexConjugate_isProper_iff`,
  `lowerSemicontinuous_convexConjugate`,
  `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull`, and
  `lowerSemicontinuousHull_eq_self` from Theorem 12.2 and Text 7.0.4;
- the bridge theorems `orthantAbsExtension_isClosedProperConvex_iff` and
  `convexConjugate_orthantAbsExtension_eq_convexConjugate_comp_coordinatewiseAbsQuadrant` from
  Text 12.3.6;
- the inherited orthant conjugate notation `g⋆` and `g⋆⋆`.

Primitive data vs derived API:
- the primitive input is a function `g : Quadrant → WithTopBot 𝕜`;
  `g.IsMonotoneClosedConvexOnQuadrant` from Text 12.3.6, built from lower semicontinuity,
  convexity, finiteness at `0`, and orthant monotonicity;
- the derived API is preservation under `g⋆` and the involution identity
  `g⋆⋆ = g`.

Layer target: `source-facing`; the item stays about the orthant-side conjugate itself rather than
being folded into a different owner abstraction on all of `𝕜^ι`, but its proof route is organized
through the canonical ambient closed-proper-convex owner.
-/

/- The ambient Chapter 12 owner `Function.IsClosedProperConvex` is handled through the primitive
conjugacy lemmas from Theorem 12.2. The orthant theorem below reuses that owner through
`orthantAbsExtension` and then returns to the orthant owner surface. -/

-- Proof sketch: apply `orthantAbsExtension_isClosedProperConvex_iff` to `g` to move to
-- the ambient absolute-value extension `orthantAbsExtension g`. Then use
-- `convexConjugate_orthantAbsExtension_eq_convexConjugate_comp_coordinatewiseAbsQuadrant` to
-- identify its Fenchel conjugate with `orthantAbsExtension (g⋆)`, and invoke the
-- ambient Chapter 12 primitive lemmas for conjugate convexity/properness/closedness.
-- Translating back through the same orthant-extension characterization yields the claimed
-- orthant-side stability.
namespace Function.IsMonotoneClosedConvexOnQuadrant

section Conjugate

variable [HasPairingSwap E E 𝕜]

/-- Theorem 12.4 (1): the orthant Fenchel conjugate `g⋆` of a nondecreasing lower semicontinuous
convex function on the non-negative orthant that is finite at the origin is again a function of
the same kind. -/
theorem convexConjugate
    {g : Quadrant → WithTopBot 𝕜}
    (hg : g.IsMonotoneClosedConvexOnQuadrant) :
    (g⋆).IsMonotoneClosedConvexOnQuadrant := by
  let gStar : Quadrant → WithTopBot 𝕜 := g⋆
  have hclosed : IsClosedProperConvex[𝕜] (orthantAbsExtension g) :=
    (orthantAbsExtension_isClosedProperConvex_iff g).2 hg
  have hstar :
      (orthantAbsExtension g)⋆ = orthantAbsExtension gStar := by
    simpa [gStar, orthantAbsExtension] using
      convexConjugate_orthantAbsExtension_eq_convexConjugate_comp_coordinatewiseAbsQuadrant g
  have hclosed_conj : IsClosedProperConvex[𝕜] (orthantAbsExtension gStar) := by
    rw [← hstar]
    refine ⟨?_, ?_, ?_⟩
    · simpa using
        (Function.isConvex_convexConjugate (𝕜 := 𝕜) (f := orthantAbsExtension g))
    · exact (hclosed.convex.convexConjugate_isProper_iff).2 hclosed.proper
    · simpa using
        (lowerSemicontinuous_convexConjugate (𝕜 := 𝕜) (f := orthantAbsExtension g))
  have hgStar : gStar.IsMonotoneClosedConvexOnQuadrant :=
    (orthantAbsExtension_isClosedProperConvex_iff gStar).1 hclosed_conj
  simpa [gStar] using hgStar

end Conjugate

-- Proof sketch: rewrite the double orthant conjugate through
-- `convexConjugate_orthantAbsExtension_eq_convexConjugate_comp_coordinatewiseAbsQuadrant` as
-- the Fenchel biconjugate of `orthantAbsExtension g`. By
-- `orthantAbsExtension_isClosedProperConvex_iff`, the hypothesis on `g` gives a closed proper
-- convex ambient extension, so the ambient primitive biconjugacy theorem
-- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull` applies; then
-- `lowerSemicontinuousHull_eq_self` uses closedness.
-- Restricting the resulting ambient equality back to the orthant recovers
-- `g⋆⋆ = g`.
section Biconjugate

variable [OrderTopology 𝕜]

/-- Theorem 12.4 (2): taking the orthant conjugate twice recovers the original orthant function. -/
theorem biconjugate_eq
    {g : Quadrant → WithTopBot 𝕜}
    (hg : g.IsMonotoneClosedConvexOnQuadrant) :
    g⋆⋆ = g := by
  let gStar : Quadrant → WithTopBot 𝕜 := g⋆
  let gStarStar : Quadrant → WithTopBot 𝕜 := gStar⋆
  have hclosed : IsClosedProperConvex[𝕜] (orthantAbsExtension g) :=
    (orthantAbsExtension_isClosedProperConvex_iff g).2 hg
  have hstar :
      (orthantAbsExtension g)⋆ = orthantAbsExtension gStar := by
    simpa [gStar, orthantAbsExtension] using
      convexConjugate_orthantAbsExtension_eq_convexConjugate_comp_coordinatewiseAbsQuadrant g
  have hstarstar :
      (orthantAbsExtension gStar)⋆ = orthantAbsExtension gStarStar := by
    simpa [gStar, gStarStar, orthantAbsExtension] using
      convexConjugate_orthantAbsExtension_eq_convexConjugate_comp_coordinatewiseAbsQuadrant
        gStar
  have hbiconj :
      ((orthantAbsExtension g)⋆⋆ : E → WithTopBot 𝕜) = cl(orthantAbsExtension g) :=
    hclosed.convex.biconjugate_eq_lowerSemicontinuousHull
  have hcl : cl(orthantAbsExtension g) = orthantAbsExtension g :=
    lowerSemicontinuousHull_eq_self hclosed.closed
  have hext : orthantAbsExtension gStarStar = orthantAbsExtension g := by
    calc
      orthantAbsExtension gStarStar = (orthantAbsExtension gStar)⋆ := hstarstar.symm
      _ = ((orthantAbsExtension g)⋆)⋆ := by
        rw [hstar]
      _ = ((orthantAbsExtension g)⋆⋆ : E → WithTopBot 𝕜) := rfl
      _ = cl(orthantAbsExtension g) := hbiconj
      _ = orthantAbsExtension g := hcl
  have hstarstar_eq : gStarStar = g := by
    ext x
    have hxabs : coordinatewiseAbsQuadrant x.1 = x := by
      ext i
      simp [coordinatewiseAbsQuadrant_apply, abs_of_nonneg (x.2 i)]
    simpa [orthantAbsExtension, hxabs] using congrFun hext x.1
  simpa [gStar, gStarStar] using hstarstar_eq

end Biconjugate

end Function.IsMonotoneClosedConvexOnQuadrant

end
