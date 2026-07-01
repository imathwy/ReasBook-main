import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_4

noncomputable section

open scoped Rockafellar

universe u v w

section

variable {X : Type u} {Y : Type v} {α : Type w}
variable [AddCommGroup α] [ConditionallyCompleteLattice α] [LinearOrder α]
variable [IsOrderedAddMonoid α]
variable [HasPairing X Y α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.1 is the weak-duality inequality comparing the primal difference
  `x ↦ f x - g x` with the dual difference `y ↦ g∗ y - f⋆ y`.
- `core/canonical`: the primitive owners are already the Chapter 12 conjugate `convexConjugate`
  and the Chapter 6 order-dual bridge owner `concaveConjugate`.
- `bridge/view`: the source inequality is assembled from the owner formulas
  `convexConjugate_eq_iSup_pairing_sub` and `concaveConjugate_eq_iInf_pairing_sub`.

Domain-style sampling used here:
- `convexConjugate_eq_iSup_pairing_sub`;
- `concaveConjugate_eq_iInf_pairing_sub`;
- `convexConjugate_le_of_isFenchelPair` from `Chap03.Text_12_2_2`, checked as the nearby owner
  theorem for generalized Fenchel inequalities.

Primitive data vs derived API:
- primitive inputs: the pairing data and functions `f g : X → WithTopBot α`;
- owner abstractions reused here: `f⋆` and `g∗`;
- derived API kept here: the pointwise weak-duality comparison and its `iInf`/`iSup` corollary.

Layer target: `core/canonical`. The file keeps the source-facing weak-duality statements, but it
does not expose the single-point `iInf`/`iSup` bounds as a second public API layer because those
are direct one-line consequences of the conjugate owners themselves.
-/

/-- Pointwise weak duality in canonical owner form: each dual gap value is bounded above by each
primal gap value. -/
-- Proof sketch: combine the owner formulas
-- `concaveConjugate_eq_iInf_pairing_sub` and `convexConjugate_eq_iSup_pairing_sub`. The chosen
-- primal point `x` bounds `g∗ y` from above and `f⋆ y` from below, and subtraction monotonicity
-- removes the pairing term.
theorem concaveConjugate_sub_convexConjugate_le_sub
    (f g : X → WithTopBot α)
    (x : X) (y : Y) :
    g∗ y - f⋆ y ≤ f x - g x := by
  let p : α := ⟪x, y⟫ₚ
  have hg : g∗ y ≤ ((p : WithTopBot α) - g x) := by
    rw [concaveConjugate_eq_iInf_pairing_sub]
    exact iInf_le (fun x' : X ↦ (((⟪x', y⟫ₚ : α) : WithTopBot α) - g x')) x
  have hf : ((p : WithTopBot α) - f x) ≤ f⋆ y := by
    rw [convexConjugate_eq_iSup_pairing_sub]
    exact le_iSup (fun x' : X ↦ (((⟪x', y⟫ₚ : α) : WithTopBot α) - f x')) x
  have hcancel :
      (((p : WithTopBot α) - g x) - ((p : WithTopBot α) - f x)) = f x - g x := by
    have hneg : -((p : WithTopBot α) - f x) = f x - (p : WithTopBot α) := by
      rw [WithBotTop.sub_eq_add_neg]
      calc
        -((p : WithTopBot α) + -f x) = -(-f x + (p : WithTopBot α)) := by
          simp [add_comm]
        _ = -(-f x) + -(p : WithTopBot α) := by
          exact WithBotTop.neg_add
            (Or.inr (WithBotTop.coe_ne_top p))
            (Or.inr (WithBotTop.coe_ne_bot p))
        _ = f x - (p : WithTopBot α) := by
          simp
    calc
      (((p : WithTopBot α) - g x) - ((p : WithTopBot α) - f x))
          = ((p : WithTopBot α) - g x) + (f x - (p : WithTopBot α)) := by
              rw [WithBotTop.sub_eq_add_neg, hneg]
      _ = (p : WithTopBot α) + (f x - g x) - (p : WithTopBot α) := by
              simp [add_assoc, add_left_comm, add_comm]
      _ = f x - g x := by
            show (p : WithTopBot α) + (f x - g x) - (p : WithTopBot α) = f x - g x
            exact WithBotTop.add_sub_cancel_left
  calc
    g∗ y - f⋆ y ≤ (((p : WithTopBot α) - g x) - ((p : WithTopBot α) - f x)) :=
      WithBotTop.sub_le_sub hg hf
    _ = f x - g x := hcancel

/-- Lemma 31.0.1 in canonical formula surface: the supremum of the dual gap is bounded above by
the infimum of the primal gap. -/
-- Proof sketch: apply the pointwise weak-duality inequality
-- `g∗ y - f⋆ y ≤ f x - g x` for arbitrary `x` and `y`, then take the supremum over `y` on the
-- left and the infimum over `x` on the right.
theorem iSup_concaveConjugate_sub_convexConjugate_le_iInf_sub
    (f g : X → WithTopBot α) :
    (⨆ y : Y, g∗ y - f⋆ y) ≤ ⨅ x : X, f x - g x := by
  refine iSup_le ?_
  intro y
  refine le_iInf ?_
  intro x
  exact concaveConjugate_sub_convexConjugate_le_sub f g x y

end
