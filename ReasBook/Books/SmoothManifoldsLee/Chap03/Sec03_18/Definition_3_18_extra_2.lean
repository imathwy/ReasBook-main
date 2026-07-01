import SmoothManifoldsLee.Chap03.Sec03_18.Definition_3_18_extra_1
import Mathlib.RingTheory.Derivation.Basic

-- Declarations for this item will be appended below by the statement pipeline.

-- This file uses the smooth-germ stalk API from
-- `Definition_3_18_extra_1`.

noncomputable section

open scoped ContDiff Manifold

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]

/-- Evaluation at `p` gives the stalk `C_p^∞(M)` its natural algebra structure on `ℝ`. -/
instance smooth_function_germs_at_evalAlgebra (p : M) :
    Algebra C^∞_[p](I) ℝ :=
  (smoothSheafCommRing.eval I 𝓘(ℝ) M ℝ p).toAlgebra

/-- Definition 3.18-extra-2: the textbook vector space `𝒟_p M` of derivations of `C_p^∞(M)` is
the type of `ℝ`-derivations from the germ ring at `p` to `ℝ`, where `ℝ` is viewed as a
`C_p^∞(M)`-algebra by evaluation at `p`. The model-with-corners parameter is explicit because it
is not recoverable from `p` alone. -/
abbrev smooth_germ_derivation_at (I : ModelWithCorners ℝ E H) (p : M) :=
  Derivation ℝ C^∞_[p](I) ℝ

/-- A smooth germ derivation satisfies the Leibniz rule on the smooth germ ring. -/
theorem smooth_germ_derivation_at_map_mul (I : ModelWithCorners ℝ E H) (p : M)
    (v : smooth_germ_derivation_at I p) (f g : C^∞_[p](I)) :
    v (f * g) = f • v g + g • v f := sorry
