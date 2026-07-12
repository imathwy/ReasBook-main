import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open scoped Rockafellar

variable {X : Type u} {Y : Type v} {L : Type w}
variable [CompleteSemilatticeSup L] [Sub L] [HasPairing X Y L]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.2.1 states that if `f₁ ≤ f₂` pointwise, then the conjugates satisfy
  the reverse pointwise inequality `f₂⋆ ≤ f₁⋆`.
- `core/canonical`: the owner abstraction is the order-reversing conjugation operator
  `convexConjugate : (X → L) → Y → L`.
- `bridge/view`: the scoped postfix notation `f⋆` and the textbook two-function implication
  `f₁ ≤ f₂ → f₂⋆ ≤ f₁⋆` are direct specializations of that owner-level `Antitone` statement.

Domain-style sampling used here:
- `convexConjugate` and its scoped notation `f⋆`;
- the owner formula `convexConjugate_eq_iSup_pairing_sub`;
- `Antitone` for order-reversing owner maps;
- codomain-side subtraction antitonicity in the primitive form
  `∀ a : L, Antitone (fun b : L ↦ a - b)`, together with complete-sup order on `L`-valued
  functions.

Primitive data vs derived API:
- primitive owner data: the pairing-valued conjugation operator `convexConjugate`;
- derived API: the two-function order-reversal statement obtained by applying owner antitonicity
  once.

Layer target: `core/canonical`; Text 12.2.1 is completed by the owner theorem itself, and the
source-facing two-function inequality is recovered by applying it to a pointwise comparison.
-/

-- Proof sketch: the hypothesis `f₁ x ≤ f₂ x` implies
-- `⟪x, y⟫ₚ - f₂ x ≤ ⟪x, y⟫ₚ - f₁ x` for every `x`, and taking the supremum over `x`
-- preserves that pointwise order. This is exactly the antitonicity of Fenchel conjugation.
/-- Core owner form of Text 12.2.1: Fenchel conjugation is order reversing whenever subtraction is
antitone in its right argument. -/
theorem convexConjugate_antitone_of_subRightAntitone
    (hsub : ∀ a : L, Antitone (fun b : L ↦ a - b)) :
    Antitone (convexConjugate : (X → L) → Y → L) := by
  intro f₁ f₂ h y
  rw [convexConjugate_eq_iSup_pairing_sub, convexConjugate_eq_iSup_pairing_sub]
  change sSup (Set.range (fun x : X ↦ ⟪x, y⟫ₚ - f₂ x)) ≤
      sSup (Set.range (fun x : X ↦ ⟪x, y⟫ₚ - f₁ x))
  refine sSup_le ?_
  intro z hz
  rcases hz with ⟨x, rfl⟩
  exact (hsub (⟪x, y⟫ₚ)) (h x) |>.trans
    (le_sSup ⟨x, rfl⟩)

section WithBotTop

variable {α : Type w}
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α]
variable [HasPairing X Y α]

/-- Text 12.2.1: on the chapter-canonical codomain `WithBotTop α`, Fenchel conjugation is order
reversing: if `f₁ ≤ f₂`, then `f₂⋆ ≤ f₁⋆`. -/
theorem convexConjugate_antitone :
    Antitone (convexConjugate : (X → WithBotTop α) → Y → WithBotTop α) := by
  refine convexConjugate_antitone_of_subRightAntitone (X := X) (Y := Y)
      (L := WithBotTop α) ?_
  intro a b c hbc
  exact WithBotTop.sub_le_sub le_rfl hbc

/-- Text 12.2.1, source-facing two-function form on `WithBotTop α`: `f₁ ≤ f₂` implies
`f₂⋆ ≤ f₁⋆`. -/
theorem convexConjugate_le_convexConjugate_of_le
    {f₁ f₂ : X → WithBotTop α} (h : f₁ ≤ f₂) :
    f₂⋆ ≤ (f₁⋆ : Y → WithBotTop α) :=
  convexConjugate_antitone h

end WithBotTop

end
