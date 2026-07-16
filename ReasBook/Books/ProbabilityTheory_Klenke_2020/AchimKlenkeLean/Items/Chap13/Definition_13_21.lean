import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap01.Definition_1_59

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

section

/-- For a defective distribution function, the textbook endpoint value `sup (range F)` is the
total mass of the associated Lebesgue--Stieltjes measure. -/
theorem sSup_range_eq_measure_univ_toReal (F : StieltjesFunction ℝ)
    [hF : IsDefectiveDistributionFunction F] :
    sSup (range F) = (F.measure univ).toReal := by
  have h_atTop : Tendsto F atTop (𝓝 (sSup (range F))) := by
    simpa [sSup_range] using
      (tendsto_atTop_ciSup F.mono
        ⟨1, fun y hy ↦ by
          rcases hy with ⟨x, rfl⟩
          exact hF.le_one x⟩)
  have h_nonneg : 0 ≤ sSup (range F) := by
    refine le_trans (hF.nonneg 0) ?_
    exact le_csSup
      ⟨1, fun y hy ↦ by
        rcases hy with ⟨x, rfl⟩
        exact hF.le_one x⟩
      (mem_range_self 0)
  rw [F.measure_univ hF.tendsto_atBot_zero h_atTop]
  simp [h_nonneg]

/-- Definition 13.21: a sequence of defective distribution functions converges weakly to `F` when
`Fₙ x → F x` at every continuity point `x` of `F`, and the endpoint values satisfy the
sub-probability endpoint condition `F(∞) ≥ limsup Fₙ(∞)`. Using
`sSup_range_eq_measure_univ_toReal`, this endpoint value is the total mass of the associated
Lebesgue--Stieltjes measure. For honest distribution functions, the endpoint condition is
automatic because every endpoint value is `1`. -/
def distribution_function_weakly_converges_to
    (Fs : ℕ → StieltjesFunction ℝ) (F : StieltjesFunction ℝ) : Prop :=
  IsDefectiveDistributionFunction F ∧
    (∀ n, IsDefectiveDistributionFunction (Fs n)) ∧
    (∀ ⦃x : ℝ⦄, ContinuousAt F x → Tendsto (fun n ↦ Fs n x) atTop (𝓝 (F x))) ∧
      (F.measure univ).toReal ≥ limsup (fun n ↦ ((Fs n).measure univ).toReal) atTop

/-- The source-facing weak convergence predicate for defective distribution functions is
exactly the textbook criterion: pointwise convergence at every continuity point of the limit
function together with the endpoint limsup inequality. -/
theorem distribution_function_weakly_converges_to_iff
    (Fs : ℕ → StieltjesFunction ℝ) (F : StieltjesFunction ℝ) :
    distribution_function_weakly_converges_to Fs F ↔
      IsDefectiveDistributionFunction F ∧
        (∀ n, IsDefectiveDistributionFunction (Fs n)) ∧
        (∀ ⦃x : ℝ⦄, ContinuousAt F x → Tendsto (fun n ↦ Fs n x) atTop (𝓝 (F x))) ∧
          (F.measure univ).toReal ≥ limsup (fun n ↦ ((Fs n).measure univ).toReal) atTop :=
  Iff.rfl

-- Proof sketch: use monotonicity of defective distribution functions to compare `F(∞)` and
-- `Fₙ(∞)` with values at large continuity points of `F`; then pass to the limit in `n` and let
-- the continuity points tend to `+∞`.
/-- The continuity-point convergence part of weak convergence forces the endpoint value of the
limit distribution function to be bounded above by the limit inferior of the endpoint values of
the approximating sequence. -/
theorem distribution_function_at_top_value_le_liminf_of_continuity_convergence
    (Fs : ℕ → StieltjesFunction ℝ) (F : StieltjesFunction ℝ)
    (hF : IsDefectiveDistributionFunction F)
    (hFs : ∀ n, IsDefectiveDistributionFunction (Fs n))
    (hcont : ∀ ⦃x : ℝ⦄, ContinuousAt F x → Tendsto (fun n ↦ Fs n x) atTop (𝓝 (F x))) :
    (F.measure Set.univ).toReal ≤ liminf (fun n ↦ ((Fs n).measure Set.univ).toReal) atTop := sorry

-- Proof sketch: combine the endpoint limsup inequality from
-- `distribution_function_weakly_converges_to_iff` with
-- `distribution_function_at_top_value_le_liminf_of_continuity_convergence`; then `liminf` and
-- `limsup` squeeze the endpoint values to the same limit.
/-- Under weak convergence of defective distribution functions, the endpoint values `Fₙ(∞)`
converge to `F(∞)`. -/
theorem tendsto_distribution_function_at_top_value_of_weak_convergence
    (Fs : ℕ → StieltjesFunction ℝ) (F : StieltjesFunction ℝ)
    (h : distribution_function_weakly_converges_to Fs F) :
    Tendsto (fun n ↦ ((Fs n).measure univ).toReal) atTop
      (𝓝 ((F.measure univ).toReal)) := sorry

end
