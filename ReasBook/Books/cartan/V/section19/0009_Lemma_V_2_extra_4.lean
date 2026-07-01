import Mathlib

namespace PeriodPair

/-- Lemma V.2-extra-4: the series of `1 / ‖ω‖^3` over the nonzero points of the period lattice
`L.lattice` is convergent. -/
theorem summable_inv_norm_cubed (L : PeriodPair) :
    Summable (fun ω : {z : L.lattice // z ≠ 0} ↦ (1 : ℝ) / ‖(ω : L.lattice)‖ ^ (3 : ℕ)) := by
  refine ((ZLattice.summable_norm_rpow L.lattice (-3 : ℝ) (by
      norm_num [L.finrank_lattice])).subtype {z : L.lattice | z ≠ 0}).congr ?_
  intro ω
  change ‖(ω : L.lattice)‖ ^ (-3 : ℝ) = (1 : ℝ) / ‖(ω : L.lattice)‖ ^ (3 : ℕ)
  rw [show (-3 : ℝ) = -(3 : ℝ) by norm_num, Real.rpow_neg]
  · simp [one_div]
  · positivity

end PeriodPair
