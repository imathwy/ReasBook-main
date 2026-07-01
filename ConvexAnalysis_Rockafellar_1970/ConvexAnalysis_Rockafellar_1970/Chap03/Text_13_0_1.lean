import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Text 13.0.1 introduces the support function `δ*(· | C)` by its supremum formula.
- `core/canonical`: the project owner abstraction is the function `supportFunction` attached
  directly to a subset `C`.
- `bridge/view`: the textbook formula is the existing specification theorem `supportFunction_def`.
- Primitive data vs derived API: the support function itself is the core notion; the displayed
  supremum identity is its defining specification. The source's convexity hypothesis is redundant
  for the bare definition, since the same formula makes sense for any subset.

Domain-style sampling used here:
- the existing project owner `supportFunction`;
- its specification theorem `supportFunction_def`;
- the function-valued bridge `supportFunction_eq_iSup`;
- and the pointwise bridge companion `supportFunction_eq_iSup_apply`.
-/

/-!
Canonicalization checklist for this item:

- Codomain layer: keep the declaration at arbitrary `L` with only `[SupSet L]`; no `EReal`,
  `WithBotTop α`, or concrete linear order is required for the defining supremum identity.
- Scalar/ambient structure: no scalar field or module data is part of the primitive statement.
- Model owner: keep the pairing-level owner `[HasPairing X Y L]`; no inner-product/strong-dual
  specialization belongs in the source item.
- Topology: no closure/interior/relative-topology owner is present in Text 13.0.1, so no ambient
  topological assumptions should appear here.
- Theorem surface: use textbook support-function notation `δᵛ` as the primary public statement,
  with `supportFunction` remaining the canonical underlying owner; use `δᵛ[L](x | C)` when the
  codomain must be fixed explicitly.
-/

/- Text 13.0.1: the support function `δ*(· | C)` is the canonical project function
`supportFunction`, defined on any set `C` by taking the supremum of the pairings `⟪x, x⋆⟫` over
`x ∈ C`. -/
recall supportFunction {X : Type u} {Y : Type v} {L : Type w}
    [SupSet L] [HasPairing X Y L] (C : Set Y) : X → L

/- The textbook supremum formula for the support function is the existing project specification
theorem `supportFunction_def`. -/
recall supportFunction_def {X : Type u} {Y : Type v} {L : Type w}
    [SupSet L] [HasPairing X Y L] (C : Set Y) (x : X) :
    δᵛ(x | C) = (⨆ y : C, (⟪x, (y : Y)⟫ₚ : L))

/- Function-valued bridge form used for rewriting under function operators. -/
recall supportFunction_eq_iSup {X : Type u} {Y : Type v} {L : Type w}
    [SupSet L] [HasPairing X Y L] (C : Set Y) :
    (δᵛ(· | C) : X → L) = (⨆ y : C, (⟪·, (y : Y)⟫ₚ : X → L))

/- Pointwise companion of `supportFunction_eq_iSup` for direct pointwise rewrites. -/
recall supportFunction_eq_iSup_apply {X : Type u} {Y : Type v} {L : Type w}
    [SupSet L] [HasPairing X Y L] (C : Set Y) (x : X) :
    δᵛ(x | C) = (⨆ y : C, (⟪x, (y : Y)⟫ₚ : L))

/- Set-image bridge form of Text 13.0.1 at the primitive `SupSet` owner layer. -/
recall supportFunction_eq_sSup_image {X : Type u} {Y : Type v} {L : Type w}
    [SupSet L] [HasPairing X Y L] (C : Set Y) (x : X) :
    δᵛ(x | C) = sSup ((fun y : Y ↦ (⟪x, y⟫ₚ : L)) '' C)
