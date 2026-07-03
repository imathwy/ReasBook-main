import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_8_0_1 (from Chap08) -/
namespace ERealFunction

/-- Multiplying a `]-∞,+∞]`-value by a positive real again yields a `]-∞,+∞]`-value. -/
-- Proof sketch: use `EReal.mul_ne_bot` for the product `(ξ : EReal) * x`, combining that real
-- coercions are neither `⊥` nor `⊤`, that `x` is not `⊥` by membership in `Set.Ioi ⊥`, and that a
-- positive real is nonnegative.
theorem adjoint_mul_mem_Ioi_bot (ξ : ℝ) (hξ : 0 < ξ) (x : Set.Ioi (⊥ : EReal)) :
    (⊥ : EReal) < (ξ : EReal) * (x : EReal) := by
  -- Turn the membership goal into the statement that the product is not `⊥`.
  rw [bot_lt_iff_ne_bot]
  -- Apply the characterization of when a product in `EReal` avoids the value `⊥`.
  exact (EReal.mul_ne_bot _ _).2
    ⟨Or.inl (EReal.coe_ne_bot ξ), Or.inr x.property.ne', Or.inl (EReal.coe_ne_top ξ),
      Or.inl (EReal.coe_nonneg.2 hξ.le)⟩

/-- The value `+∞` belongs to `]-∞,+∞]`. -/
-- Proof sketch: rewrite membership in `Set.Ioi (⊥ : EReal)` as the inequality `⊥ < ⊤`.
theorem top_mem_Ioi_bot : (⊤ : EReal) ∈ Set.Ioi (⊥ : EReal) := by
  -- Membership in `Set.Ioi (⊥ : EReal)` is exactly the strict inequality `⊥ < ⊤`.
  simp

/-- Text 8.0.1: the adjoint of `φ : ℝ → ]-∞,+∞]` is the function `φ*` defined by
`φ*(ξ) = ξ φ(1 / ξ)` for `ξ > 0` and `φ*(ξ) = +∞` otherwise. -/
noncomputable def adjoint (φ : ℝ → Set.Ioi (⊥ : EReal)) : ℝ → Set.Ioi (⊥ : EReal) :=
  fun ξ ↦
    if hξ : 0 < ξ then
      ⟨(ξ : EReal) * (φ (1 / ξ) : EReal), adjoint_mul_mem_Ioi_bot ξ hξ (φ (1 / ξ))⟩
    else
      ⟨(⊤ : EReal), top_mem_Ioi_bot⟩

/-- The positive branch of the adjoint definition evaluates to `ξ φ(1 / ξ)`. -/
-- Proof sketch: unfold `adjoint` and simplify the defining `if` using the hypothesis `0 < ξ`.
@[simp] theorem adjoint_apply_of_pos (φ : ℝ → Set.Ioi (⊥ : EReal)) {ξ : ℝ} (hξ : 0 < ξ) :
    (adjoint φ ξ : EReal) = (ξ : EReal) * (φ (1 / ξ) : EReal) := by
  -- Select the positive branch in the defining case split of `adjoint`.
  simp [adjoint, hξ]

/-- The nonpositive branch of the adjoint definition evaluates to `+∞`. -/
-- Proof sketch: unfold `adjoint` and simplify the defining `if` using `¬ 0 < ξ`, obtained from
-- the assumption `ξ ≤ 0`.
@[simp] theorem adjoint_apply_of_nonpos (φ : ℝ → Set.Ioi (⊥ : EReal)) {ξ : ℝ} (hξ : ξ ≤ 0) :
    (adjoint φ ξ : EReal) = ⊤ := by
  -- Select the nonpositive branch in the defining case split of `adjoint`.
  simp [adjoint, not_lt.mpr hξ]

end ERealFunction

/-! ### Text_8_0_2 (from Chap08) -/
universe u

open scoped Pointwise

section

variable {H : Type u} [SMul ℝ H]

/-- Text 8.0.2: the Minkowski gauge of a subset `C` is the `]-∞,+∞]`-valued function sending
`x` to the infimum of the positive real numbers `ξ` such that `x ∈ ξ C`. -/
noncomputable def minkowskiGauge (C : Set H) : H → EReal :=
  fun x ↦ sInf (Real.toEReal '' {ξ : ℝ | 0 < ξ ∧ x ∈ ξ • C})

notation "m[" C "]" => minkowskiGauge C

/-- The textbook Minkowski gauge is the infimum of the positive real scalings that contain the
point. -/
-- Proof sketch: unfold `minkowskiGauge`; the statement is exactly its defining equation.
theorem minkowskiGauge_eq_sInf (C : Set H) (x : H) :
    m[C] x = sInf (Real.toEReal '' {ξ : ℝ | 0 < ξ ∧ x ∈ ξ • C}) := by
  -- The notation `m[C]` is just `minkowskiGauge C`.
  -- Unfolding the definition yields exactly the claimed infimum formula.
  rfl

end

/-! ### Text_8_0_3 (from Chap08) -/
open Set

/-- Text 8.0.3: the Huber function with threshold `ρ ∈ ℝ_{++}` is quadratic on `|x| ≤ ρ` and
affine in `|x|` on `ρ < |x|`. -/
noncomputable def huberFunction (ρ : Ioi (0 : ℝ)) : ℝ → ℝ :=
  {x : ℝ | (ρ : ℝ) < |x|}.piecewise
    (fun x ↦ (ρ : ℝ) * |x| - (ρ : ℝ) ^ 2 / 2)
    (fun x ↦ |x| ^ 2 / 2)

/-- On the region `ρ < |x|`, the Huber function agrees with its affine branch. -/
-- Proof sketch: unfold `huberFunction` and simplify the defining `Set.piecewise` expression using
-- the hypothesis `(ρ : ℝ) < |x|`.
theorem huberFunction_eq_of_lt (ρ : Ioi (0 : ℝ)) {x : ℝ} (hx : (ρ : ℝ) < |x|) :
    huberFunction ρ x = (ρ : ℝ) * |x| - (ρ : ℝ) ^ 2 / 2 := by
  -- The hypothesis places `x` in the threshold set controlling the piecewise definition.
  simpa [huberFunction] using
    Set.piecewise_eq_of_mem
      (s := {y : ℝ | (ρ : ℝ) < |y|})
      (f := fun y ↦ (ρ : ℝ) * |y| - (ρ : ℝ) ^ 2 / 2)
      (g := fun y ↦ y ^ 2 / 2)
      hx

/-- On the region `|x| ≤ ρ`, the Huber function agrees with its quadratic branch. -/
-- Proof sketch: unfold `huberFunction` and simplify the defining `Set.piecewise` expression using
-- `not_lt.mpr hx` to select the quadratic case.
theorem huberFunction_eq_of_le (ρ : Ioi (0 : ℝ)) {x : ℝ} (hx : |x| ≤ (ρ : ℝ)) :
    huberFunction ρ x = |x| ^ 2 / 2 := by
  -- The complementary inequality shows that `x` is outside the threshold set.
  have hx_not_mem : x ∉ {y : ℝ | (ρ : ℝ) < |y|} := not_lt.mpr hx
  -- With the non-membership established, the piecewise definition reduces to the quadratic branch.
  simpa [huberFunction] using
    Set.piecewise_eq_of_notMem
      (s := {y : ℝ | (ρ : ℝ) < |y|})
      (f := fun y ↦ (ρ : ℝ) * |y| - (ρ : ℝ) ^ 2 / 2)
      (g := fun y ↦ y ^ 2 / 2)
      hx_not_mem
