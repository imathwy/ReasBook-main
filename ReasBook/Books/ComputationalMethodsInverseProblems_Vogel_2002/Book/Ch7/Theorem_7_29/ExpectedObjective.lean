module

public import Book.Ch7.Definition_7_2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

public section

universe u

noncomputable section

namespace TikhonovGcv

/-- The concrete `n`-indexed expected GCV objective for a discrete Tikhonov
reconstruction family `R n α`, evaluated at the noisy data
`(K n).toEuclideanLin (fTrue n) + η n ω`. -/
@[expose] def expectedObjective
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (K : ∀ n : ℕ, Matrix (Fin n.succ) (Fin n.succ) ℝ)
    (R : ∀ n : ℕ, ℝ → Matrix (Fin n.succ) (Fin n.succ) ℝ)
    (fTrue : ∀ n : ℕ, EuclideanSpace ℝ (Fin n.succ))
    (η : ∀ n : ℕ, Ω → EuclideanSpace ℝ (Fin n.succ)) :
    ℕ → ℝ → ℝ :=
  fun n α ↦
    ∫ ω, gcv (fun β ↦ influenceMatrix (K n) (R n β))
      ((K n).toEuclideanLin (fTrue n) + η n ω) α ∂μ

/-- The defining formula for `TikhonovGcv.expectedObjective`. -/
@[simp] theorem expectedObjective_apply
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (K : ∀ n : ℕ, Matrix (Fin n.succ) (Fin n.succ) ℝ)
    (R : ∀ n : ℕ, ℝ → Matrix (Fin n.succ) (Fin n.succ) ℝ)
    (fTrue : ∀ n : ℕ, EuclideanSpace ℝ (Fin n.succ))
    (η : ∀ n : ℕ, Ω → EuclideanSpace ℝ (Fin n.succ))
    (n : ℕ) (α : ℝ) :
    expectedObjective μ K R fTrue η n α =
      ∫ ω, gcv (fun β ↦ influenceMatrix (K n) (R n β))
        ((K n).toEuclideanLin (fTrue n) + η n ω) α ∂μ := by
  -- This is the defining equation of `expectedObjective`.
  rfl

end TikhonovGcv
