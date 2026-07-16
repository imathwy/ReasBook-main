import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section

open scoped Rockafellar

variable {α : Type v} [AddCommGroup α]
variable {X : Type u} {Y : Type w} [HasPairing X Y α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item rewrites the support half-space level set
  `{x | h x ≤ β + ⟪x, b⋆⟫ₚ}` as a nonpositive sublevel set and computes the conjugate of the
  corresponding affine perturbation of `h`.
- `core/canonical`: the owner abstractions are the project declaration `convexConjugate` for
  Fenchel conjugation and the chapter affine-change theorem
  `convexConjugate_affineChange`.
- `bridge/view`: the textbook function `x ↦ h x - ⟪x, b⋆⟫ₚ - β` is kept as a direct source-facing
  affine perturbation of `h`. Its conjugate formula is proved directly on the pairing layer,
  while the chapter affine-change theorem remains the stronger linear-equiv companion.

Domain-style sampling used here:
- `convexConjugate` and the chapter notation `f⋆` from `Defn_12_2`;
- `convexConjugate_eq_iSup_pairing_sub` from `Defn_12_2`;
- `convexConjugate_affineChange` from `Theorem_12_3`, as the linear-equivalence affine-change
  companion.

Primitive data vs derived API:
- primitive data: the function `h : X → WithBotTop α`, the dual vector `bStar : Y`, and the scalar
  `β : α`;
- derived API: the level-set equality and the conjugate translation formula.

Layer target: `source-facing`; the item is formalized directly as the displayed set identity and
conjugate formula, without introducing a parallel local wrapper.

Redundant-source-assumption elimination: although the textbook states the result for proper convex
`h`, both displayed formulas are purely algebraic consequences of the Fenchel definition, so the
Lean statements below do not keep those redundant hypotheses.
-/

-- Proof sketch: membership in the left-hand set is exactly the
-- inequality `h x - ⟪x, b⋆⟫ₚ - β ≤ 0` after moving the finite affine term to the left.
/-- Text 13.4.3 (1): the set `{x | h x ≤ β + ⟪x, b⋆⟫ₚ}` is the nonpositive sublevel set of
`x ↦ h x - ⟪x, b⋆⟫ₚ - β`. -/
theorem levelSet_pairing_le_eq_preimage_sub_nonpos
    [LinearOrder α] [IsOrderedAddMonoid α]
    (h : X → WithBotTop α) (bStar : Y) (β : α) :
    {x : X | h x ≤ β + ⟪x, bStar⟫ₚ} =
      (fun x ↦ h x - ⟪x, bStar⟫ₚ - β) ⁻¹' Set.Iic (0 : WithBotTop α) := by
  ext x
  change h x ≤ β + ⟪x, bStar⟫ₚ ↔ h x - ⟪x, bStar⟫ₚ - β ≤ 0
  constructor
  · intro hx
    let pairx : WithBotTop α := ⟪x, bStar⟫ₚ
    have hx_pair : h x ≤ (β : WithBotTop α) + pairx := by
      simpa [pairx] using hx
    have hx' : h x - pairx ≤ β := by
      exact (WithBotTop.sub_le_iff_le_add
        (a := h x) (b := pairx) (c := (β : WithBotTop α))
        (.inr (WithBotTop.coe_ne_top β)) (.inr (WithBotTop.coe_ne_bot β))).2 hx_pair
    exact WithBotTop.sub_nonpos.mpr hx'
  · intro hx
    let pairx : WithBotTop α := ⟪x, bStar⟫ₚ
    have hx' : h x - pairx ≤ β := by
      simpa [pairx] using (WithBotTop.sub_nonpos.mp hx)
    have hx_pair : h x ≤ (β : WithBotTop α) + pairx := by
      exact (WithBotTop.sub_le_iff_le_add
        (a := h x) (b := pairx) (c := (β : WithBotTop α))
        (.inr (WithBotTop.coe_ne_top β)) (.inr (WithBotTop.coe_ne_bot β))).1 hx'
    simpa [pairx] using hx_pair

-- Proof sketch: unfold both conjugates by `convexConjugate_eq_iSup_pairing_sub`, move the finite
-- scalar `β` outside the supremum through the order isomorphism `t ↦ t + β`, and simplify the
-- pointwise affine term using `⟪x, x⋆ + b⋆⟫ₚ = ⟪x, x⋆⟫ₚ + ⟪x, b⋆⟫ₚ`.
/-- Text 13.4.3 (2): the conjugate of `x ↦ h x - ⟪x, b⋆⟫ₚ - β` is
`x⋆ ↦ h*(x⋆ + b⋆) + β`. -/
theorem convexConjugate_sub_pairing_const
    [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α]
    [Add Y]
    [HasPairingAddRight X Y α]
    (h : X → WithBotTop α) (bStar : Y) (β : α) :
    (fun x ↦ h x - ⟪x, bStar⟫ₚ - β)⋆ =
      fun xStar ↦ h⋆ (xStar + bStar) + β := by
  let addRightβ : WithBotTop α ≃o WithBotTop α :=
    { toFun := fun t ↦ t + β
      invFun := fun t ↦ t - β
      left_inv := fun _ ↦ WithBotTop.add_sub_cancel_right
      right_inv := fun _ ↦ WithBotTop.sub_add_cancel
      map_rel_iff' := fun {a b} ↦ (WithBotTop.addLECancellable_coe β).add_le_add_iff_right }
  funext xStar
  calc
    (fun x ↦ h x - ⟪x, bStar⟫ₚ - β)⋆ xStar
      = ⨆ x : X, (⟪x, xStar⟫ₚ - (h x - ⟪x, bStar⟫ₚ - β)) := by
          rw [convexConjugate_eq_iSup_pairing_sub]
    _ = ⨆ x : X, ((⟪x, xStar + bStar⟫ₚ - h x) + β) := by
          apply iSup_congr
          intro x
          have hpair_ne_bot : (⟪x, bStar⟫ₚ : WithBotTop α) ≠ ⊥ := by
            change (((⟪x, bStar⟫ₚ : α) : WithBotTop α) ≠ ⊥)
            exact WithBotTop.coe_ne_bot _
          have hpair_ne_top : (⟪x, bStar⟫ₚ : WithBotTop α) ≠ ⊤ := by
            change (((⟪x, bStar⟫ₚ : α) : WithBotTop α) ≠ ⊤)
            exact WithBotTop.coe_ne_top _
          have hneg_pair :
              -(h x - (⟪x, bStar⟫ₚ : WithBotTop α)) = -h x + ⟪x, bStar⟫ₚ := by
            exact
              (WithBotTop.neg_sub
                (x := h x) (y := (⟪x, bStar⟫ₚ : WithBotTop α))
                (.inr hpair_ne_bot) (.inr hpair_ne_top))
          have hneg_pair' :
              -(h x + -⟪x, bStar⟫ₚ) = -h x + ⟪x, bStar⟫ₚ := by
            simpa [WithBotTop.sub_eq_add_neg] using hneg_pair
          have hpair :
              (⟪x, xStar + bStar⟫ₚ : WithBotTop α) =
                (⟪x, xStar⟫ₚ : WithBotTop α) + (⟪x, bStar⟫ₚ : WithBotTop α) := by
            exact congrArg (fun t : α ↦ (t : WithBotTop α))
              (HasPairingAddRight.pairing_add_right (X := X) (Y := Y) (𝕜 := α) x xStar bStar)
          calc
            ⟪x, xStar⟫ₚ - (h x - ⟪x, bStar⟫ₚ - β)
                = ⟪x, xStar⟫ₚ + (-(h x - ⟪x, bStar⟫ₚ) + β) := by
                    rw [WithBotTop.sub_eq_add_neg]
                    rw [WithBotTop.neg_sub (.inr (WithBotTop.coe_ne_bot β))
                      (.inr (WithBotTop.coe_ne_top β))]
            _ = ⟪x, xStar⟫ₚ + (-h x + ⟪x, bStar⟫ₚ) + β := by
                    rw [show (-(h x - ⟪x, bStar⟫ₚ) : WithBotTop α) = -(h x + -⟪x, bStar⟫ₚ) by
                      simp [WithBotTop.sub_eq_add_neg]]
                    rw [hneg_pair']
                    simp [add_assoc, add_left_comm, add_comm]
            _ = ⟪x, xStar + bStar⟫ₚ + (-h x) + β := by
                    rw [hpair]
                    simp [add_assoc, add_left_comm, add_comm]
            _ = (⟪x, xStar + bStar⟫ₚ - h x) + β := by
                    rfl
    _ = addRightβ (⨆ x : X, (⟪x, xStar + bStar⟫ₚ - h x)) := by
          change (⨆ x : X, addRightβ (⟪x, xStar + bStar⟫ₚ - h x)) =
            addRightβ (⨆ x : X, (⟪x, xStar + bStar⟫ₚ - h x))
          symm
          exact addRightβ.map_iSup _
    _ = addRightβ (h⋆ (xStar + bStar)) := by
          rw [convexConjugate_eq_iSup_pairing_sub]
    _ = h⋆ (xStar + bStar) + β := by
          rfl

end
