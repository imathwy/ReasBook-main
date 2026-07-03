import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.20: on `ℝ^n`, modeled as `Fin n → ℝ`, the canonical norm is the `l_infty`-norm,
given by the supremum, equivalently the maximum, of the coordinate absolute values; this is the
specialization of the standard finite-product sup-norm formula `Pi.norm_def`. -/
section

variable {n : ℕ}

#check (Pi.norm_def : ∀ x : Fin n → ℝ, ‖x‖ = ↑(Finset.univ.sup fun i ↦ ‖x i‖₊))

end
