import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap24.Corollary_24_29

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: realize `X` by the normalized-Gamma construction of the Dirichlet law, then
-- permute the independent Gamma coordinates. The product Gamma law is invariant under coordinate
-- permutations, so pushing forward by the same normalization yields the Dirichlet law with the
-- permuted parameter vector.
/-- Exercise 24.3.2 (1): permuting the coordinates of a Dirichlet-distributed vector permutes the
parameter vector in the same way. -/
theorem hasLaw_dirichlet_permute
    {n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Fin n → ℝ}
    {θ : Fin n → ℝ} (hθ : ∀ i, 0 < θ i) (σ : Equiv.Perm (Fin n))
    (hX : HasLaw X (dirichletMeasure θ) μ) :
    HasLaw (fun ω i ↦ X ω (σ i)) (dirichletMeasure fun i ↦ θ (σ i)) μ := sorry

-- Proof sketch: write `X` as normalized independent Gamma coordinates with shapes `θ i`. Group
-- the last two Gamma variables into their sum, use Gamma-additivity to identify the new last
-- shape as `θ_{n+1} + θ_{n+2}`, and normalize again to obtain the Dirichlet law of the merged
-- vector.
/-- Exercise 24.3.2 (2): combining the last two coordinates of a Dirichlet-distributed
`(n + 2)`-tuple produces a Dirichlet-distributed `(n + 1)`-tuple whose last parameter is the sum
of the last two parameters. -/
theorem hasLaw_dirichlet_merge_last
    {n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Fin (n + 2) → ℝ}
    {θ : Fin (n + 2) → ℝ} (hθ : ∀ i, 0 < θ i)
    (hX : HasLaw X (dirichletMeasure θ) μ) :
    HasLaw
      (fun ω ↦
        Fin.snoc
          (Fin.init (Fin.init (X ω)))
          ((Fin.init (X ω)) (Fin.last n) + X ω (Fin.last (n + 1))))
      (dirichletMeasure <|
        Fin.snoc
          (Fin.init (Fin.init θ))
          ((Fin.init θ) (Fin.last n) + θ (Fin.last (n + 1)))) μ := sorry

end ProbabilityTheory
