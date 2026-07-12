import Mathlib.Analysis.Calculus.LineDeriv.Basic

section

universe u

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

/- Definition 3.14-extra-2: for a smooth real-valued function on `V`, Lee's operator `D_v|_a`
is the real line-derivative operator `lineDeriv ℝ`, specialized to functions `V → ℝ`. -/
#check (lineDeriv ℝ : (V → ℝ) → V → V → ℝ)

end
