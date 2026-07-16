import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01.Example_1_9
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_47.Example_7_4_torus

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Torus

noncomputable section

section

variable {n : ℕ} (v : Fin n → ℝ)

/-- Example 7.24: the coordinatewise exponential map `εⁿ : ℝⁿ → 𝕋ⁿ` intertwines translation by
`t • v` on `ℝⁿ` with multiplication by `εⁿ (t • v)` on `𝕋ⁿ`. -/
theorem torus_epsilon_add_char_equivariant (t : ℝ) (x : Fin n → ℝ) :
    ε^{n} (x + t • v) = ε^{n} (t • v) * ε^{n} x := by
  simpa [add_comm] using (ε^{n}).map_add_eq_mul (t • v) x

end
