import BauschkeLean.Chap12.ProximityOperator

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

noncomputable section

-- Source/core/bridge triage:
-- - `source-facing`: Example 24.42 owns the scalar penalty `ξ ↦ ω |ξ| - log (1 + ω |ξ|)` and
--   its displayed proximal formula on `ℝ`.
-- - `core/canonical`: the surrounding repository surface is the scalar `Γ₀(ℝ)` owner together
--   with `Prox[φ, hφ]`.
-- - `bridge/view`: this file keeps the textbook owner and adds only the coercion/parity
--   companions that downstream scalar Chapter 24 lemmas typically consume.

/-- The `]-∞,+∞]`-valued scalar penalty `ξ ↦ ω |ξ| - log (1 + ω |ξ|)`. -/
def linearLogAbsPenalty (ω : PosReal) : ℝ → Set.Ioi (⊥ : EReal) :=
  (fun ξ : ℝ ↦ (ω : ℝ) * |ξ| - Real.log (1 + (ω : ℝ) * |ξ|)).toEReal

/-- Coercing `linearLogAbsPenalty ω` back to `EReal` recovers the real-valued formula
`ξ ↦ ω |ξ| - log (1 + ω |ξ|)`. -/
@[simp] theorem linearLogAbsPenalty_apply (ω : PosReal) (ξ : ℝ) :
    (linearLogAbsPenalty ω ξ : EReal) =
      ((ω : ℝ) * |ξ| - Real.log (1 + (ω : ℝ) * |ξ|) : ℝ) := by
  simp [linearLogAbsPenalty, Function.toEReal_apply]

/-- The scalar penalty `linearLogAbsPenalty ω` is even. -/
theorem linearLogAbsPenalty_even (ω : PosReal) :
    Function.Even (linearLogAbsPenalty ω) := by
  intro ξ
  apply Subtype.ext
  simp [linearLogAbsPenalty_apply, abs_neg]

/-- The scalar penalty `ξ ↦ ω |ξ| - log (1 + ω |ξ|)` belongs to `Γ₀(ℝ)`. -/
theorem linearLogAbsPenalty_mem_gammaZero (ω : PosReal) :
    linearLogAbsPenalty ω ∈ Γ₀(ℝ) := sorry

/-- Example 24.42: for `ω ∈ ℝ_{++}` and
`φ(ξ) = ω |ξ| - log (1 + ω |ξ|)`, the proximity operator of `φ` is the displayed
signed quadratic-root formula `(24.79)`. -/
theorem prox_linearLogAbsPenalty_eq_sign_mul_quadratic_root (ω : PosReal) :
    Prox[linearLogAbsPenalty ω, linearLogAbsPenalty_mem_gammaZero ω] =
      fun ξ : ℝ ↦
        Real.sign ξ *
          (((ω : ℝ) * |ξ| - (ω : ℝ) ^ (2 : ℕ) - 1 +
                Real.sqrt
                  (|((ω : ℝ) * |ξ| - (ω : ℝ) ^ (2 : ℕ) - 1)| ^ (2 : ℕ) +
                    4 * (ω : ℝ) * |ξ|)) /
            (2 * (ω : ℝ))) := sorry

end

end ERealFunction
