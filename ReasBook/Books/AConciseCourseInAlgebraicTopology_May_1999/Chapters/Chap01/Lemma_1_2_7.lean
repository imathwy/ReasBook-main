import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Path.Homotopic.Quotient

variable {X : Type u} [TopologicalSpace X] {x y : X}

/- Lemma 1.2.7 (1): constant paths are right units up to endpoint-fixed homotopy, so for a path
`f : Path x y`, the class of `f.trans (Path.refl y)` equals the class of `f`. -/
#check (trans_refl : (γ : Path.Homotopic.Quotient x y) → γ.trans (refl y) = γ)

/- Lemma 1.2.7 (2): constant paths are left units up to endpoint-fixed homotopy, so for a path
`f : Path x y`, the class of `(Path.refl x).trans f` equals the class of `f`. -/
#check (refl_trans : (γ : Path.Homotopic.Quotient x y) → (refl x).trans γ = γ)
