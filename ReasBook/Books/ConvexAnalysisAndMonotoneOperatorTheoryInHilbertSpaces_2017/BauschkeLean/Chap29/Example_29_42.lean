import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Proposition_12_30
import BauschkeLean.Chap29.Definition_29_40

open scoped Gradient InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A witness that `h` attains its minimum value `0` on the ambient space. -/
structure AttainsMinZero (h : H → Set.Ioi (⊥ : EReal)) where
  point : H
  isMinOn : IsMinOn h.asEReal Set.univ point
  eq_zero : (h point : EReal) = 0

variable (h : H → Set.Ioi (⊥ : EReal))

/-- An `AttainsMinZero` witness certifies that the ambient space is nonempty. -/
instance attainsMinZero_nonempty (hmin : AttainsMinZero h) : Nonempty H :=
  ⟨hmin.point⟩

/-- `AttainsMinZero h` recovers the source-style attained minimum-zero hypothesis. -/
theorem AttainsMinZero.exists_isMinOn_eq_zero
    (hmin : AttainsMinZero h) :
    ∃ x, IsMinOn h.asEReal Set.univ x ∧ (h x : EReal) = 0 := sorry

-- Semantic recall: this item uses the Chapter 12 Moreau-envelope and proximal-operator owners,
-- and its source-facing projector is written directly by the Chapter 29 differentiable formula.

/-- The unit Moreau regularization `g = h □ ((1 / 2) ‖·‖²)` attached to `h`. -/
def unitMoreauRegularization
    (h : H → Set.Ioi (⊥ : EReal)) : H → EReal :=
  {}^[(1 : PosReal)] h

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Evaluating `unitMoreauRegularization` at `x` just returns the unit Moreau envelope of `h`
at `x`. -/
@[simp] theorem unitMoreauRegularization_apply
    (h : H → Set.Ioi (⊥ : EReal)) (x : H) :
    unitMoreauRegularization h x = ({}^[(1 : PosReal)] h) x :=
  rfl

/-- The source real-valued power regularization `f = g^γ` from Example 29.42. -/
def moreauPowerRegularization
    (h : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) : H → ℝ :=
  fun x ↦
    (unitMoreauRegularization h x).toReal ^ (γ : ℝ)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Evaluating `moreauPowerRegularization` at `x` raises the unit Moreau regularization of `h` to
the positive exponent `γ`. -/
@[simp] theorem moreauPowerRegularization_apply
    (h : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) (x : H) :
    moreauPowerRegularization h γ x =
      (unitMoreauRegularization h x).toReal ^ (γ : ℝ) :=
  rfl

variable (γ : PosReal)

/-- The real-valued unit Moreau envelope associated with `h`, viewed through the canonical
Chapter 12 `toReal` bridge. -/
theorem gradient_unitMoreauRegularization_toReal_eq_residual
    (hh : h ∈ Γ₀(H)) :
    ∇ (fun y : H ↦ (unitMoreauRegularization h y).toReal) =
      fun x ↦ x - Prox[h, hh] x := by
  sorry

/-- The gradient field inserted into the Example 29.42 Chapter 29 projector owner. -/
noncomputable def moreauPowerRegularizationGradient
    : H → H :=
  fun x ↦
    (((γ : ℝ) * moreauPowerRegularization h γ x ^ ((γ : ℝ) - 1)) •
      (∇ (fun y : H ↦ (unitMoreauRegularization h y).toReal) x))

/-- Evaluating `moreauPowerRegularizationGradient` at `x` returns the Moreau-power residual field
used in Example 29.42. -/
@[simp] theorem moreauPowerRegularizationGradient_apply
    (x : H) :
    moreauPowerRegularizationGradient h γ x =
      (((γ : ℝ) * moreauPowerRegularization h γ x ^ ((γ : ℝ) - 1)) •
        (∇ (fun y : H ↦ (unitMoreauRegularization h y).toReal) x)) :=
  rfl

/-- Example 29.42: the source-facing operator is the Chapter 29 differentiable subgradient
projector attached to `(moreauPowerRegularization h γ, 0)` and the Moreau-power gradient field. -/
noncomputable def moreauPowerSubgradientProjector
    : H → H :=
  fun x ↦
    if 0 < moreauPowerRegularization h γ x then
      x +
        (((0 : ℝ) - moreauPowerRegularization h γ x) /
            ‖moreauPowerRegularizationGradient h γ x‖ ^ 2) •
          moreauPowerRegularizationGradient h γ x
    else
      x

/-- Under the attained minimum-zero hypothesis from Example 29.42, `Argmin h` is exactly the
nonpositive level set of `moreauPowerRegularization h γ`. -/
theorem argmin_eq_lowerLevelSet_moreauPowerRegularization
    (hh : h ∈ Γ₀(H))
    (hmin : AttainsMinZero h) :
    Argmin h.asEReal =
      lowerLevelSet (moreauPowerRegularization h γ).toEReal.asEReal 0 := sorry

/-- On the zero lower-level-set branch, the Example 29.42 operator fixes `x`. -/
theorem moreauPowerSubgradientProjector_apply_of_mem_lowerLevelSet
    {x : H}
    (hx : x ∈ lowerLevelSet (moreauPowerRegularization h γ).toEReal.asEReal 0) :
    moreauPowerSubgradientProjector h γ x = x := by
  have hfx : moreauPowerRegularization h γ x ≤ 0 := by
    simpa [Function.toEReal_apply] using
      (mem_lowerLevelSet_iff (moreauPowerRegularization h γ).toEReal.asEReal 0 x).1 hx
  rw [moreauPowerSubgradientProjector, if_neg (not_lt.mpr hfx)]

/-- On the positive branch of `(29.73)`, the Example 29.42 piecewise proximal residual map is the
displayed explicit formula. -/
theorem moreauPowerSubgradientProjector_apply_of_pos
    (hh : h ∈ Γ₀(H))
    {x : H} (hx : (0 : EReal) < (h x : EReal)) :
    moreauPowerSubgradientProjector h γ x =
      x -
        (((unitMoreauRegularization h x).toReal / (γ : ℝ) /
            ‖x - Prox[h, hh] x‖ ^ 2) • (x - Prox[h, hh] x)) := sorry

/-- On the minimizing branch of `(29.73)`, the Example 29.42 piecewise proximal residual map
fixes `x`. -/
theorem moreauPowerSubgradientProjector_apply_of_eq_zero
    (hh : h ∈ Γ₀(H))
    (hmin : AttainsMinZero h)
    {x : H} (hx : (h x : EReal) = 0) :
    moreauPowerSubgradientProjector h γ x = x := sorry

/-- Under the attained minimum-zero hypothesis from Example 29.42, the fixed-point
set of `moreauPowerSubgradientProjector` is the zero lower level set of
`moreauPowerRegularization h γ`. -/
theorem moreauPowerSubgradientProjector_fixedPoints_eq_lowerLevelSet
    (hh : h ∈ Γ₀(H))
    (hmin : AttainsMinZero h) :
    Function.fixedPoints (moreauPowerSubgradientProjector h γ) =
      lowerLevelSet (moreauPowerRegularization h γ).toEReal.asEReal 0 := sorry

end

end ERealFunction
