import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {n : ℕ} {p : ℝ}

local notation "E" => WithLp (ENNReal.ofReal p) (Fin n → ℝ)

local macro "halfSquaredLpNormSmoothProp[" hp:term "]" : term =>
  `(by
      letI : Fact (1 ≤ ENNReal.ofReal p) :=
        ⟨(ENNReal.one_le_ofReal).2 (by linarith [$hp])⟩
      exact
        is_l_smooth_on
          (fun z : E ↦ ‖z‖ ^ (2 : ℕ) / 2)
          Set.univ
          (Real.toNNReal (p - 1)))

local macro "halfSquaredLpNormUpperModelProp[" hp:term "]" : term =>
  `(by
      letI : Fact (1 ≤ ENNReal.ofReal p) :=
        ⟨(ENNReal.one_le_ofReal).2 (by linarith [$hp])⟩
      exact
        ∀ x y : E,
          (fun z : E ↦ ‖z‖ ^ (2 : ℕ) / 2) y ≤
            (fun z : E ↦ ‖z‖ ^ (2 : ℕ) / 2) x +
              fderiv ℝ (fun z : E ↦ ‖z‖ ^ (2 : ℕ) / 2) x (y - x) +
                ((p - 1) / 2) * ‖x - y‖ ^ (2 : ℕ))

/- Proposition 5.5 is `source-facing`: the textbook object is the half-squared `ℓ_p` norm on
`ℝ^n`. Domain sampling identifies the ambient owner object as the canonical `WithLp` model and
the chapter owner property as `is_l_smooth_on`; the quadratic upper model is a companion
`bridge/view` consequence of that owner-level smoothness statement. Since the function itself is
just the canonical map `x ↦ ‖x‖² / 2` on that owner space, no separate wrapper definition is
needed. -/

-- Proof sketch: prove first that `x ↦ ‖x‖² / 2` on `E` is differentiable for `p ≥ 2`, compute
-- its Fréchet derivative in the canonical `WithLp` normed-space model, and then bound the
-- derivative difference by `p - 1` using the coordinate estimates from the textbook proof
-- together with Hölder/Cauchy-Schwarz.
/-- Proposition 5.5: for `p ≥ 2`, the half-squared `ℓ_p` norm on `ℝ^n`, viewed on the canonical
`WithLp` model, is globally `(p - 1)`-smooth with respect to the `ℓ_p` norm. This is the
owner-level Chapter 5 formulation of the textbook statement. -/
theorem half_squared_lp_norm_is_l_smooth (hp : 2 ≤ p) :
    halfSquaredLpNormSmoothProp[hp] := by
  sorry

-- Proof sketch: combine the owner-level smoothness theorem with the standard second-order upper
-- model estimate for an `L`-smooth function, here specialized to the canonical Fréchet derivative
-- on the `WithLp` model.
/-- Proposition 5.5 companion: the half-squared `ℓ_p` norm satisfies the textbook quadratic upper
model with constant `p - 1`. -/
theorem half_squared_lp_norm_upper_model (hp : 2 ≤ p) :
    halfSquaredLpNormUpperModelProp[hp] := by
  sorry

end
