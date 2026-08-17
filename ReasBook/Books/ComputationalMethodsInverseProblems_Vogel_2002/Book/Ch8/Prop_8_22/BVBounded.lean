module

public import Book.Ch8.Definition_8_9

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}

/-- A subset of the Chapter 8 `L¹(Ω)` carrier is BV-bounded if the source BV quantity
`‖f‖_{L¹(Ω)} + TV(f)` is uniformly bounded on that set. This keeps the source hypothesis on
the existing owners `MeasureTheory.Lp ℝ 1 (domainMeasure Ω)` and `totalVariation` without
introducing a guessed bundled `BV(Ω)` type. -/
def IsBVBounded
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (S : Set (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))) : Prop :=
  ∃ C : ℝ, ∀ ⦃f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)⦄, f ∈ S →
    ((‖f‖ : ℝ) : EReal) + totalVariation f ≤ (C : EReal)

/-- The defining BV-bound inequality for a BV-bounded set. -/
theorem IsBVBounded.norm_add_totalVariation_le
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {S : Set (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))}
    (hS : IsBVBounded S) :
    ∃ C : ℝ, ∀ ⦃f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)⦄, f ∈ S →
      ((‖f‖ : ℝ) : EReal) + totalVariation f ≤ (C : EReal) :=
  hS

/-- A subset of a BV-bounded set is BV-bounded. -/
theorem IsBVBounded.mono
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {S T : Set (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))}
    (hT : IsBVBounded T)
    (hST : S ⊆ T) :
    IsBVBounded S := by
  rcases hT with ⟨C, hC⟩
  exact ⟨C, fun {_f} hfS ↦ hC (hST hfS)⟩

end VariationalRegularization
