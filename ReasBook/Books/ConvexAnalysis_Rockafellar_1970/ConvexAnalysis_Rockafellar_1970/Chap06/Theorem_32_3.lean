import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_1_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_4_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_4

open scoped Rockafellar

universe u

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 32.3 reduces maximization on `C` to the textbook slice
  `C ∩ Lᗮ`, where `L = span (lin C)`.
- `core/canonical`: lineality `lin[𝕜](C)`, submodule span, pairing annihilator `ᗮₚ`,
  `Set.extremePoints`, `sSup`, and `IsMaxOn`.
- `bridge/view`: this file exposes the pairing-level annihilator owner
  `Set.linealAnnihilator`; the textbook slice is then written directly as
  `C ∩ linAnn[𝕜](C)` in the theorem surfaces.

Primitive data vs derived API:
- primitive owner data: `C` and `lin[𝕜](C)`;
- derived API: `linAnn[𝕜](C) = ((span 𝕜 (lin[𝕜](C)))ᗮₚ : Set Y)` and the
  source-facing slice `C ∩ linAnn[𝕜](C)`.

Layer target: `source-facing`, on the scalar/pairing-generic owner layer.
-/

namespace Set

open scoped Rockafellar
open Submodule

section PairingAnnihilator

/-- Pairing-level annihilator of the lineality subspace `span 𝕜 (lin[𝕜](C))`. -/
abbrev linealAnnihilator (𝕜 : Type*) [CommSemiring 𝕜] [LE 𝕜]
    {E : Type u} [AddCommGroup E] [Module 𝕜 E]
    {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]
    (C : Set E) : Set Y :=
  (((span 𝕜 (lin[𝕜](C)))ᗮₚ : Submodule 𝕜 Y) : Set Y)

scoped[Rockafellar] notation "linAnn[" 𝕜 "](" C ")" =>
  Set.linealAnnihilator (𝕜 := 𝕜) C

end PairingAnnihilator

end Set

section SupremumClause

variable {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [HasLinearPairing E E 𝕜]
variable {α : Type*} [AddCommMonoid α] [ConditionallyCompleteLinearOrder α]
  [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]

-- Proof sketch: remove the lineality directions of `C` by passing to the textbook slice
-- `C ∩ Lᗮₚ`, where `L = Submodule.span 𝕜 (lin[𝕜](C))`. On that slice there are no affine-line
-- directions coming from `lin[𝕜](C)`, so the Chapter 18 representation by extreme
-- points/extreme directions can be combined with half-line boundedness of `f` to eliminate the
-- direction part and reduce the supremum to extreme points.
/-- Theorem 32.3 (1): under convexity/domain and half-line boundedness hypotheses on a closed
convex set `C`, the supremum of `f` on `C` agrees with the supremum on the extreme points of
`C ∩ linAnn[𝕜](C)`. -/
theorem sSup_image_eq_sSup_image_extremePoints_linealAnnihilatorSlice
    {f : E → WithBotTop α} {C : Set E} (hf : f.IsConvex 𝕜)
    (hC_closed : IsClosed C)
    (hC_convex : Convex 𝕜 C) (hC_dom : C ⊆ dom(f))
    (hhalfLine_bddAbove :
      ∀ ⦃x : E⦄ ⦃r : Module.Ray 𝕜 E⦄,
        affineHalfLine x r ⊆ C → BddAbove (f '' affineHalfLine x r)) :
    sSup (f '' C) = sSup (f '' (Set.extremePoints 𝕜 (C ∩ linAnn[𝕜](C)))) := sorry

end SupremumClause

section AttainmentClause

variable {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [HasLinearPairing E E 𝕜]
variable {α : Type*} [AddCommMonoid α] [LinearOrder α]
  [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]

-- Proof sketch: once the supremum side is reduced to extreme points of the slice `C ∩ Lᗮₚ`,
-- combine that reduction with the attainment bridge from Theorem 32.2 to transfer a maximizer on
-- `C` to a maximizer on those extreme points.
/-- Theorem 32.3 (2): if `f` attains a maximum on `C`, then under the same geometric hypotheses
it attains that maximum at an extreme point of
`C ∩ linAnn[𝕜](C)`.
This clause is kept in a separate section so it does not inherit unnecessary
`ConditionallyCompleteLinearOrder` assumptions from the supremum clause. -/
theorem exists_mem_isMaxOn_extremePoints_linealAnnihilatorSlice_of_exists_mem_isMaxOn
    {f : E → WithBotTop α} {C : Set E} (hf : f.IsConvex 𝕜)
    (hC_closed : IsClosed C)
    (hC_convex : Convex 𝕜 C) (hC_dom : C ⊆ dom(f))
    (hhalfLine_bddAbove :
      ∀ ⦃x : E⦄ ⦃r : Module.Ray 𝕜 E⦄,
        affineHalfLine x r ⊆ C → BddAbove (f '' affineHalfLine x r))
    (hmax : ∃ x ∈ C, IsMaxOn f C x) :
    ∃ y ∈ Set.extremePoints 𝕜 (C ∩ linAnn[𝕜](C)),
      IsMaxOn f C y := sorry

end AttainmentClause
