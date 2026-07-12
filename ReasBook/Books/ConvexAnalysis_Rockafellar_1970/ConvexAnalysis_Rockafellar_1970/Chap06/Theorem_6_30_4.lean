import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_16_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_4

noncomputable section

open scoped Rockafellar

universe u v w

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.4 compares the Chapter 6 concave conjugate of `g` with the
  Chapter 12 Fenchel conjugate of the negated function `-g`.
- `core/canonical`: the owner declarations are already `concaveConjugate` and `convexConjugate`
  (notation `(·)⋆`) on the pairing-based `WithBotTop α` layer.
- `bridge/view`: this file contributes only the sign-duality comparison theorem between those two
  existing owners; it does not introduce a new conjugation wrapper.

Domain-style sampling:
- `concaveConjugate` and `concaveConjugate_eq_iInf_pairing_sub` from
  `Chap06.Definition_6_30_4`;
- `convexConjugate`, notation `(·)⋆`, and
  `convexConjugate_eq_neg_iInf_sub_pairing` from `Chap03.Defn_12_2`.

Primitive data vs derived API:
- primitive owners already upstream: `concaveConjugate` and `convexConjugate`;
- derived API here: the sign-twisted bridge
  `g* = (fun y ↦ - ((-g)⋆ (-y)))`, with a pointwise corollary.

Layer target: `bridge/view`. The properness and concavity hypotheses from the textbook are
redundant for this algebraic identity, so the theorem is stated at the weaker canonical
pairing-and-order layer actually used by the formula.
-/

section

variable {X : Type u} {Y : Type v} {α : Type w}
variable [AddCommGroup α] [ConditionallyCompleteLattice α] [IsOrderedAddMonoid α]
variable [Neg Y] [HasPairing X Y α] [HasPairingNegRight X Y α]

-- Proof sketch: rewrite `concaveConjugate g y` by its defining `iInf` formula and rewrite
-- `-((-g)⋆ (-y))` using `convexConjugate_eq_neg_iInf_sub_pairing`. The owner
-- `HasPairingNegRight` converts the pairing term at `-y`, and the remaining pointwise integrands
-- agree by commutativity of addition in `WithBotTop α`.
/-- Theorem 6.30.4: the concave conjugate of `g` at `y` is the negative of the Fenchel conjugate
of the negated function `-g` evaluated at `-y`, stated at the function-owner layer. -/
theorem concaveConjugate_eq_neg_convexConjugate_neg
    (g : X → WithBotTop α) :
    g∗ = fun y ↦ -((-g)⋆ (-y)) := by
  ext y
  rw [concaveConjugate_eq_iInf_pairing_sub, convexConjugate_eq_neg_iInf_sub_pairing]
  simp only [neg_neg]
  refine iInf_congr fun x ↦ ?_
  have hpair :
      (((⟪x, -y⟫ₚ : α) : WithBotTop α)) = -(((⟪x, y⟫ₚ : α) : WithBotTop α)) := by
    exact
      congrArg ((↑) : α → WithBotTop α)
        (HasPairingNegRight.pairing_neg_right (x := x) (y := y))
  change (((⟪x, y⟫ₚ : α) : WithBotTop α) + -g x) =
    (-g x + -(((⟪x, -y⟫ₚ : α) : WithBotTop α)))
  rw [hpair]
  simp [add_comm]

/-- Pointwise companion of Theorem 6.30.4. -/
theorem concaveConjugate_eq_neg_convexConjugate_neg_apply
    (g : X → WithBotTop α)
    (y : Y) :
    g∗ y = -((-g)⋆ (-y)) := by
  simpa using congrFun (concaveConjugate_eq_neg_convexConjugate_neg g) y

end

section

variable {X : Type u} {Y : Type v} {α : Type w}
variable [Field α] [ConditionallyCompleteLinearOrder α] [IsStrictOrderedRing α]
variable [MulAction α X]
variable [Neg Y] [HasPairing X Y α] [HasPairingNegRight X Y α]

/-- Positive-scalar companion of Theorem 6.30.4: when `λ > 0`, the concave conjugate of `g λ`
is the pointwise left scalar multiple `λ g*`. -/
theorem concaveConjugate_rightScalarMul_eq_left_smul_of_pos
    (g : X → WithBotTop α) {lam : α} (hlam : (0 : α) < lam) :
    ((⟨lam, hlam.le⟩ : Set.Ici (0 : α)) •ʳ g)∗ =
      (lam : WithBotTop α) • g∗ := by
  let lamNN : Set.Ici (0 : α) := ⟨lam, hlam.le⟩
  have hneg_rightScalarMul :
      ((lamNN •ʳ (-g) : X → WithBotTop α)) =
        -((lamNN •ʳ g) : X → WithBotTop α) := by
    ext x
    have hleft :
        (lamNN •ʳ (-g)) x =
          ((lam : WithBotTop α) * (-g (lam⁻¹ • x))) := by
      simpa using
        (rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos (f := -g) (a := lam) hlam x)
    have hright :
        (lamNN •ʳ g) x =
          ((lam : WithBotTop α) * (g (lam⁻¹ • x))) := by
      simpa using
        (rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos (f := g) (a := lam) hlam x)
    calc
      (lamNN •ʳ (-g)) x = ((lam : WithBotTop α) * (-g (lam⁻¹ • x))) := hleft
      _ = -((lam : WithBotTop α) * (g (lam⁻¹ • x))) := by
            simp [WithBotTop.mul_neg]
      _ = -((lamNN •ʳ g) x) := by rw [hright]
  have hconv :
      (((lamNN •ʳ (-g))⋆ : Y → WithBotTop α)) =
        ((lam : WithBotTop α) • (((-g)⋆ : Y → WithBotTop α))) := by
    simpa using
      (convexConjugate_rightScalarMul_eq_left_smul_of_pos (f := -g) (lam := lam) hlam)
  ext y
  have hbase :
      (((lamNN •ʳ g)∗ : Y → WithBotTop α) y) =
        -(((-(lamNN •ʳ g : X → WithBotTop α))⋆ :
          Y → WithBotTop α) (-y)) := by
    simpa using
      (concaveConjugate_eq_neg_convexConjugate_neg_apply
        (g := ((lamNN •ʳ g) : X → WithBotTop α)) (y := y))
  calc
    (((lamNN •ʳ g)∗) : Y → WithBotTop α) y
        = -(((-(lamNN •ʳ g : X → WithBotTop α))⋆ :
          Y → WithBotTop α) (-y)) := hbase
    _ = -(((lamNN •ʳ (-g))⋆ : Y → WithBotTop α) (-y)) := by
          rw [← hneg_rightScalarMul]
    _ = -(((lam : WithBotTop α) • (((-g)⋆ : Y → WithBotTop α))) (-y)) := by
          rw [hconv]
    _ = ((lam : WithBotTop α) • (g∗ : Y → WithBotTop α)) y := by
          rw [Pi.smul_apply, Pi.smul_apply,
            concaveConjugate_eq_neg_convexConjugate_neg_apply (g := g) (y := y)]
          simp [WithBotTop.mul_neg]

end
