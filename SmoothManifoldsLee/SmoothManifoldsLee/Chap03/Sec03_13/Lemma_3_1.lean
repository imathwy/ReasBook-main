import Mathlib.Analysis.InnerProductSpace.PiL2
import SmoothManifoldsLee.Chap03.Sec03_13.Definition_3_13_extra_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ContDiff Manifold

variable {n : ℕ}

local notation "R^n" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓘(ℝ, R^n)
local notation "SmoothRn" => C^∞⟮I, R^n; ℝ⟯

-- Proof sketch: `PointDerivation` is a `Derivation`, so constants lie in the image of
-- `algebraMap ℝ SmoothRn` and are annihilated by `Derivation.map_algebraMap`.
/-- Lemma 3.1 (1): (a) point derivations at `a` annihilate constant smooth real-valued functions
on `ℝ^n`. -/
theorem point_derivation_apply_const
    (a : R^n) (w : PointDerivation I a) (c : ℝ) :
    w (ContMDiffMap.const c) = 0 := by
  change w ((algebraMap ℝ SmoothRn) c) = 0
  exact w.map_algebraMap c

-- Proof sketch: specialize the chapter bridge theorem `point_derivation_leibniz`; the factors
-- `f a` and `g a` then vanish by hypothesis.
/-- Lemma 3.1 (2): (b) if smooth functions `f` and `g` both vanish at `a`, then any point
derivation at `a` annihilates their product. -/
theorem point_derivation_mul_eq_zero_of_vanish_at
    (a : R^n) (w : PointDerivation I a) (f g : SmoothRn)
    (hf : f a = 0) (hg : g a = 0) :
    w (f * g) = 0 := by
  rw [point_derivation_leibniz]
  simp [hf, hg]
