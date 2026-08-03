import Mathlib
import BauschkeLean.Chap20.Definition_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Definition 20.51 directly defines the Fitzpatrick function `F_A` as the
  supremum over graph points of `A`.
- `core/canonical`: the owner abstractions reused here are the chapter's `SetValuedOperator.graph`
  on the source side and the ambient `EReal` supremum function space on the codomain side.
- `bridge/view`: the infimum reformulation below is a companion identity for the same owner, not a
  replacement owner. -/

/-- Definition 20.51: the Fitzpatrick function attached to a set-valued operator `A`; for
monotone `A`, this is the textbook Fitzpatrick function. It is the extended-real-valued function
on `H × H` obtained by taking the supremum of `⟪y, u⟫ + ⟪x, v⟫ - ⟪y, v⟫` over graph points
`(y, v) ∈ gra A`. The Lean surface notation for the textbook symbol `F_A` is `F[A]`. -/
noncomputable def fitzpatrickFunction (A : SetValuedOperator H H) : H × H → EReal :=
  fun (x, u) ↦
    ⨆ p : gra A, ((⟪p.1.1, u⟫_ℝ + ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ : ℝ) : EReal)

/- Lean cannot parse an arbitrary term as a literal subscript, so we use the bracketed surface
`F[A]` as the direct notation for the textbook Fitzpatrick function `F_A`. -/
scoped notation:max "F[" A:max "]" => fitzpatrickFunction A

open scoped SetValuedOperator

/-- Helper for Definition 20.51: the Fitzpatrick supremand can be rewritten as the base pairing
minus the gap pairing `⟪x - y, u - v⟫`. -/
private theorem innerPairingSubGap (x u y v : H) :
    ⟪y, u⟫_ℝ + ⟪x, v⟫_ℝ - ⟪y, v⟫_ℝ = ⟪x, u⟫_ℝ - ⟪x - y, u - v⟫_ℝ := by
  -- Expand the gap pairing so the scalar identity reduces to a ring normalization.
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  ring_nf

/-- Helper for Definition 20.51: each graph-point supremand is the coercion of the real gap
normal form from `innerPairingSubGap`. -/
private theorem fitzpatrickSupremandEqCoeSubGap
    (A : SetValuedOperator H H) (x u : H) (p : gra A) :
    ((⟪p.1.1, u⟫_ℝ + ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ : ℝ) : EReal) =
      (((⟪x, u⟫_ℝ - ⟪x - p.1.1, u - p.1.2⟫_ℝ : ℝ) : ℝ) : EReal) := by
  -- Convert the scalar identity from `innerPairingSubGap` directly into `EReal`.
  exact congrArg (fun t : ℝ => (t : EReal))
    (innerPairingSubGap x u p.1.1 p.1.2)

/-- Helper for Definition 20.51: translation by a finite real constant is an order isomorphism on
`EReal`. -/
private noncomputable def erealAddRightOrderIso (c : ℝ) : EReal ≃o EReal where
  toEquiv :=
    { toFun := fun z => z + c
      invFun := fun z => z - c
      left_inv := by
        intro z
        -- Cancel the translated finite real constant on the right.
        simpa using (EReal.add_sub_cancel_right (a := z) (b := c))
      right_inv := by
        intro z
        -- Undo right translation by adding the same finite real constant back.
        simpa [add_comm] using (EReal.sub_add_cancel (a := z) (b := c)) }
  map_rel_iff' := by
    intro a b
    -- Right translation by a finite real preserves order because it is cancellable.
    simpa [add_comm] using (EReal.addLECancellable_coe c).add_le_add_iff_right

/-- Helper for Definition 20.51: an indexed supremum of finite left subtractions is finite left
subtraction of the indexed infimum. -/
private theorem iSupSubEqSubIInfOfRealFamily {ι : Sort*} (c : ℝ) (g : ι → ℝ) :
    (⨆ i, ((c - g i : ℝ) : EReal)) = (c : EReal) - ⨅ i, ((g i : ℝ) : EReal) := by
  -- Route correction: transport first through negation, then through right translation by `c`.
  calc
    (⨆ i, ((c - g i : ℝ) : EReal))
        = ⨆ i, (-( ((g i : ℝ) : EReal)) + c) := by
            simp [sub_eq_add_neg, add_comm]
    _ = erealAddRightOrderIso c (⨆ i, -(((g i : ℝ) : EReal))) := by
          -- Pull the common finite translation outside the indexed supremum.
          simpa [erealAddRightOrderIso] using
            ((erealAddRightOrderIso c).map_iSup fun i => -(((g i : ℝ) : EReal))).symm
    _ = erealAddRightOrderIso c (- ⨅ i, (((g i : ℝ) : EReal))) := by
          -- Negation is the order-reversing bridge from `iInf` to `iSup`.
          congr 1
          have h :=
            congrArg OrderDual.ofDual
              (EReal.negOrderIso.map_iInf fun i => (((g i : ℝ) : EReal)))
          exact h.symm
    _ = (c : EReal) - ⨅ i, ((g i : ℝ) : EReal) := by
          -- Rewrite the translated negated infimum back into subtraction.
          simp [erealAddRightOrderIso, sub_eq_add_neg, add_comm]

-- Proof sketch: for each graph point `(y, v)`, expand
-- `⟪y, u⟫ + ⟪x, v⟫ - ⟪y, v⟫ = ⟪x, u⟫ - ⟪x - y, u - v⟫`; then the first display is the
-- supremum of `⟪x, u⟫ - ...` over `gra A`, which is `⟪x, u⟫` minus the infimum term.
/-- Evaluating `F[A]` at `(x, u)` gives the pairing `⟪x, u⟫` minus the infimum
of `⟪x - y, u - v⟫` over `gra A`. -/
theorem fitzpatrickFunction_apply_eq_inner_sub_iInf (A : SetValuedOperator H H) (x u : H) :
    F[A] (x, u) =
      (⟪x, u⟫_ℝ : EReal) -
        ⨅ p : gra A, ((⟪x - p.1.1, u - p.1.2⟫_ℝ : ℝ) : EReal) := by
  -- Rewrite the graph-point supremand to the scalar gap normal form from the textbook identity.
  rw [fitzpatrickFunction]
  simp_rw [fitzpatrickSupremandEqCoeSubGap]
  -- Transport the resulting `iSup` of finite left subtractions to `inner - iInf`.
  simpa using
    iSupSubEqSubIInfOfRealFamily (c := ⟪x, u⟫_ℝ)
      (g := fun p : gra A ↦ ⟪x - p.1.1, u - p.1.2⟫_ℝ)

end SetValuedOperator
