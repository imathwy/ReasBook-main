import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
import Mathlib.Order.SetNotation

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section ConvexConjugate

variable {X : Type u} {Y : Type v} {L : Type w}
variable [SupSet L] [Sub L] [HasPairing X Y L]

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Defn 12.2 introduces the Fenchel conjugate `f*` by the supremum formula.
- `core/canonical`: the primitive owner is the conjugation operator itself, built only from the
  pairing values and the ambient codomain operations actually used by the formula.
- `bridge/view`: the scoped postfix notations `f⋆` and `f⋆⋆`, together
  with the immediate pointwise supremum theorem, are thin views of that owner.

Primitive data vs derived API:
- primitive input: a function `f : X → L`;
- primitive owner: `convexConjugate f : Y → L`;
- primitive ambient data: a pairing `X → Y → L`, subtraction on `L`, and set-supremum on `L`;
- derived API in this file: the direct pointwise `⨆` restatement, the dual-pairing biconjugate
  restatement for `(f⋆)⋆`, and the self-pairing biconjugate surface `f⋆⋆`.

Layer target: `source-facing`. The source writes the conjugate in a concrete real Euclidean
setting, but the owner itself only needs a pairing-valued codomain with `⨆` and subtraction, so
the public definition is kept at that more primitive level.
-/

/-- Defn 12.2: the Fenchel conjugate of a function with values in an ambient pairing codomain. -/
def convexConjugate (f : X → L) : Y → L :=
  fun y ↦ ⨆ x : X, ⟪x, y⟫ₚ - f x

scoped[Rockafellar] postfix:max "⋆" => convexConjugate

section DualBiconjugate

/-- Evaluating the dual Fenchel biconjugate `(f⋆)⋆` at `x` gives the pointwise supremum formula.
-/
theorem convexConjugate_convexConjugate_eq_iSup_pairing_sub
    [HasPairing Y X L] (f : X → L) (x : X) :
    ((f⋆ : Y → L)⋆ : X → L) x = ⨆ y : Y, ⟪y, x⟫ₚ - f⋆ y :=
  rfl

end DualBiconjugate

section Biconjugate

variable {E : Type u}
variable [HasPairing E E L]

/-- The self-pairing Fenchel biconjugate is the dual biconjugate with `X = Y`. -/
def convexBiconjugate (f : E → L) : E → L :=
  ((f⋆ : E → L)⋆ : E → L)

scoped[Rockafellar] postfix:max "⋆⋆" => convexBiconjugate

/-- Evaluating the self-pairing Fenchel biconjugate at `x` gives the pointwise supremum formula. -/
theorem convexBiconjugate_eq_iSup_pairing_sub (f : E → L) (x : E) :
    f⋆⋆ x = ⨆ y : E, ⟪y, x⟫ₚ - f⋆ y :=
  rfl

end Biconjugate

/-- Evaluating the Fenchel conjugate at `y` gives the supremum of the affine defects
`pairing x y - f x`. -/
theorem convexConjugate_eq_iSup_pairing_sub (f : X → L) (y : Y) :
    f⋆ y = ⨆ x : X, ⟪x, y⟫ₚ - f x :=
  rfl

/-- If the opposite-orientation pairing is swap-compatible with the forward pairing, reading the
Fenchel conjugate on the opposite side reverses the displayed pairing order. -/
theorem convexConjugate_eq_iSup_pairing_sub_swap (f : Y → L) (x : X)
    [HasPairing Y X L] [HasPairingSwap X Y L] :
    f⋆ x = ⨆ y : Y, ⟪x, y⟫ₚ - f y := by
  rw [convexConjugate_eq_iSup_pairing_sub (f := f) (y := x)]
  refine iSup_congr ?_
  intro y
  rw [(HasPairingSwap.pairing_swap x y).symm]

section WithTopBot

variable {α : Type w}
variable [AddCommGroup α] [ConditionallyCompleteLattice α] [IsOrderedAddMonoid α]
variable [HasPairing X Y α]

private theorem convexConjugate_eq_neg_iInf_sub_pairing_withTopBot (f : X → WithTopBot α)
    (y : Y) :
    f⋆ y = - ⨅ x : X, f x - ⟪x, y⟫ₚ := by
  let g : X → WithTopBot α := fun x ↦ ((⟪x, y⟫ₚ : α) : WithTopBot α) - f x
  have hneg_iSup :
      -(⨆ x : X, g x) = ⨅ x : X, -g x := by
    change
        (WithBotTop.negOrderIso : WithBotTop α ≃o OrderDual (WithBotTop α)) (⨆ x : X, g x) =
          ⨆ x : X,
            (WithBotTop.negOrderIso : WithBotTop α ≃o OrderDual (WithBotTop α)) (g x)
    exact
      (OrderIso.map_iSup
        (WithBotTop.negOrderIso : WithBotTop α ≃o OrderDual (WithBotTop α)) g)
  have hneg :
      -(f⋆ y) = ⨅ x : X, -g x := by
    rw [convexConjugate_eq_iSup_pairing_sub]
    simpa [g] using hneg_iSup
  have hpoint :
      (fun x : X ↦ -(((⟪x, y⟫ₚ : α) : WithTopBot α) - f x)) =
        fun x : X ↦ f x - (((⟪x, y⟫ₚ : α) : WithTopBot α)) := by
    funext x
    let a : WithTopBot α := (⟪x, y⟫ₚ : α)
    have htop : a ≠ (⊤ : WithTopBot α) := WithBotTop.coe_ne_top (⟪x, y⟫ₚ)
    have hbot : a ≠ (⊥ : WithTopBot α) := WithBotTop.coe_ne_bot (⟪x, y⟫ₚ)
    have h : -(a - f x) = -a + f x := WithBotTop.neg_sub (Or.inl hbot) (Or.inl htop)
    simpa [a, sub_eq_add_neg, add_comm] using h
  calc
    f⋆ y = -(-(f⋆ y)) := by simp
    _ = - (⨅ x : X, -(((⟪x, y⟫ₚ : α) : WithTopBot α) - f x)) := by rw [hneg]
    _ = - ⨅ x : X, f x - (((⟪x, y⟫ₚ : α) : WithTopBot α)) := by rw [hpoint]
    _ = - ⨅ x : X, f x - ⟪x, y⟫ₚ := rfl

/-- On the chapter-facing codomain `WithTopBot α`, the Fenchel conjugate can equivalently be
written as the negative of an infimum. -/
theorem convexConjugate_eq_neg_iInf_sub_pairing (f : X → WithTopBot α) (y : Y) :
    f⋆ y = - ⨅ x : X, f x - ⟪x, y⟫ₚ := by
  simpa using convexConjugate_eq_neg_iInf_sub_pairing_withTopBot (f := f) (y := y)

end WithTopBot

section OrderedAddCompleteCodomain

variable {M : Type w}
variable [CompleteLattice M] [AddCommGroup M] [IsOrderedAddMonoid M]
variable [HasPairing X Y M]

/-- Ordered-additive complete-lattice codomain form of the Fenchel negative-infimum identity. -/
theorem convexConjugate_eq_neg_iInf_sub_pairing_of_orderedAddComplete
    (f : X → M) (y : Y) :
    f⋆ y = - ⨅ x : X, f x - ⟪x, y⟫ₚ := by
  have hneg_iSup :
      -(⨆ x : X, (⟪x, y⟫ₚ : M) - f x) = ⨅ x : X, -((⟪x, y⟫ₚ : M) - f x) := by
    change
      (OrderIso.neg (α := M)) (⨆ x : X, (⟪x, y⟫ₚ : M) - f x) =
        ⨆ x : X, (OrderIso.neg (α := M)) ((⟪x, y⟫ₚ : M) - f x)
    exact (OrderIso.neg (α := M)).map_iSup (fun x : X ↦ (⟪x, y⟫ₚ : M) - f x)
  have hpoint :
      (fun x : X ↦ -((⟪x, y⟫ₚ : M) - f x)) =
        fun x : X ↦ f x - (⟪x, y⟫ₚ : M) := by
    funext x
    exact _root_.neg_sub (⟪x, y⟫ₚ : M) (f x)
  rw [convexConjugate_eq_iSup_pairing_sub]
  calc
    (⨆ x : X, (⟪x, y⟫ₚ : M) - f x) = -(- (⨆ x : X, (⟪x, y⟫ₚ : M) - f x)) := by simp
    _ = - (⨅ x : X, -((⟪x, y⟫ₚ : M) - f x)) := by rw [hneg_iSup]
    _ = - ⨅ x : X, f x - (⟪x, y⟫ₚ : M) := by rw [hpoint]

end OrderedAddCompleteCodomain

end ConvexConjugate
