import Mathlib.Order.SaddlePoint
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_7
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_6_3

noncomputable section

universe u v w

open Set
open scoped Rockafellar

namespace Bifunction

section Pairing

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 36.5.2 characterizes saddle-points of a saddle-function by the
  vanishing of the two partial subdifferentials, equivalently by the vanishing of the product
  saddle subdifferential.
- `core/canonical`: the chapter's source-ordered owner is `Bifunction.IsSaddlePoint L u x`; the
  product subdifferential owner is `Bifunction.subdifferentialAt L u x`.
- `bridge/view`: the source's separate conditions `0 ∈ ∂₁L(u, x)` and `0 ∈ ∂₂L(u, x)` are the
  coordinate form of product-membership in the chapter saddle subdifferential owner.

Domain-style sampling used here:
- `Bifunction.IsSaddlePoint` and `Bifunction.isSaddlePoint_iff_source_order` from
  `Chap06.Definition_6_28_7`;
- `Bifunction.subdifferential1At` from `Chap07.Text_35_5_1`;
- `Bifunction.subdifferential2At` from `Chap07.Text_35_5_2`;
- `Bifunction.subdifferentialAt` and `Bifunction.mem_subdifferentialAt` from `Chap07.Text_35_6_3`.

Primitive data vs derived API:
- primitive owner data: the bifunction `L`, the candidate point `(u, x)`, the source-ordered
  saddle-point owner, and the chapter owner `Bifunction.subdifferentialAt L u x`;
- derived API: the coordinate split into the two partial zero-subgradient conditions, recovered
  canonically from `mem_subdifferentialAt`.

Layer target: source-facing owner first (`Bifunction.IsSaddlePoint`), with Euclidean
Fréchet-Riesz statements provided only as downstream bridge specializations.

Ambient-assumption minimization:
- the source hypothesis "`L` is concave-convex" is redundant for this characterization: the
  inequalities defining a saddle-point are equivalent to zero belonging to the corresponding
  partial subdifferentials purely by the definitions of `subdifferential1At` and
  `subdifferential2At`.
- the canonical statement below uses the pairing owner directly
  (`d(L ; u, x | U, X)`), so it does not require inner-product-space hypotheses.
- the pairing-level source statements here live directly over a generic scalar/codomain layer
  `𝕜` / `WithTopBot 𝕜`; only the separate strong-dual bridge section below adds the normed-field
  hypotheses needed to talk about `StrongDual 𝕜 _`.
-/

/-- Source-facing companion to Proposition 36.5.2: a pair `(u, x)` is a saddle-point of `L` on
the whole product space exactly when both pairing-valued partial zero-subgradient conditions
hold. -/
theorem isSaddlePoint_iff_zero_mem_subdifferential1At_and_zero_mem_subdifferential2At
    {𝕜 : Type w} [AddZeroClass 𝕜] [Preorder 𝕜]
    {U : Type u} {X : Type v} {UStar : Type*} {XStar : Type*}
    [Sub U] [Sub X]
    [Zero UStar] [Zero XStar]
    [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]
    [HasPairingZeroRight U UStar 𝕜] [HasPairingZeroRight X XStar 𝕜]
    {L : U → X → WithTopBot 𝕜} {u : U} {x : X} :
    IsSaddlePoint L u x ↔
      0 ∈ ∂₁[UStar]L(u, x) ∧
        0 ∈ ∂₂[XStar]L(u, x) := by
  rw [Bifunction.isSaddlePoint_iff_source_order]
  rw [mem_subdifferential1At_pairing, mem_subdifferential2At_pairing]
  constructor
  · rintro ⟨hleft, hright⟩
    refine ⟨?_, ?_⟩
    · intro u'
      simpa [pairing_zero_right] using hleft u'
    · intro x'
      simpa [pairing_zero_right] using hright x'
  · rintro ⟨hsub1, hsub2⟩
    refine ⟨?_, ?_⟩
    · intro u'
      simpa [pairing_zero_right] using hsub1 u'
    · intro x'
      simpa [pairing_zero_right] using hsub2 x'

/-- Pairing-level product-owner form of Proposition 36.5.2: `(u, x)` is a saddle-point of `L`
exactly when the zero pair belongs to the product subdifferential `d(L ; u, x | U, X)`. -/
theorem isSaddlePoint_iff_zero_mem_subdifferentialAt
    {𝕜 : Type w} [AddZeroClass 𝕜] [Preorder 𝕜]
    {U : Type u} {X : Type v} {UStar : Type*} {XStar : Type*}
    [Sub U] [Sub X]
    [Zero UStar] [Zero XStar]
    [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]
    [HasPairingZeroRight U UStar 𝕜] [HasPairingZeroRight X XStar 𝕜]
    {L : U → X → WithTopBot 𝕜} {u : U} {x : X} :
    IsSaddlePoint L u x ↔ 0 ∈ d(L ; u, x | UStar, XStar) := by
  rw [mem_subdifferentialAt]
  exact
    (isSaddlePoint_iff_zero_mem_subdifferential1At_and_zero_mem_subdifferential2At
      (UStar := UStar) (XStar := XStar) (L := L) (u := u) (x := x))

end Pairing

section Dual

variable {U : Type u} {X : Type v}
variable {𝕜 : Type w} [NormedField 𝕜] [Preorder 𝕜]
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Strong-dual bridge form of Proposition 36.5.2 in split-coordinate form. -/
theorem isSaddlePoint_iff_zero_mem_subdifferential1AtDual_and_zero_mem_subdifferential2AtDual
    {L : U → X → WithTopBot 𝕜} {u : U} {x : X} :
    IsSaddlePoint L u x ↔
      0 ∈ ∂₁ L(u, x) ∧
        0 ∈ ∂₂ L(u, x) := by
  exact
    (isSaddlePoint_iff_zero_mem_subdifferential1At_and_zero_mem_subdifferential2At
      (UStar := StrongDual 𝕜 U) (XStar := StrongDual 𝕜 X)
      (L := L) (u := u) (x := x))

/-- Strong-dual bridge form of Proposition 36.5.2 on the canonical saddle subdifferential owner
`∂ₛ L(u, x)`. -/
theorem isSaddlePoint_iff_zero_mem_subdifferentialAtDual
    {L : U → X → WithTopBot 𝕜} {u : U} {x : X} :
    IsSaddlePoint L u x ↔ 0 ∈ ∂ₛ L(u, x) := by
  rw [mem_subdifferentialAtDual]
  change IsSaddlePoint L u x ↔
      0 ∈ ∂₁ L(u, x) ∧
        0 ∈ ∂₂ L(u, x)
  exact isSaddlePoint_iff_zero_mem_subdifferential1AtDual_and_zero_mem_subdifferential2AtDual

end Dual

end Bifunction
