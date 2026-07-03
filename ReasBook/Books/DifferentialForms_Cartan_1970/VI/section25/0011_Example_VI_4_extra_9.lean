import Mathlib
import cartan.III.section11.PeriodLattice
import cartan.III.section11.«0012_Corollary_III_5_extra_8»

-- Declarations for this item will be appended below by the statement pipeline.

open Function

-- Semantic recall note: the core owner for lattice-periodicity in this chapter is
-- `HasPeriodLattice`, and the source-facing constancy theorem is already available as
-- `differentiable_eq_const_of_has_period_lattice`.

/-- A holomorphic function on `ℂ` that is periodic with respect to every point of the lattice
spanned by a period pair takes the same value at any two points. -/
theorem differentiable_apply_eq_apply_of_lattice_periodic
    (L : PeriodPair) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hperiodic : HasPeriodLattice L f) (z w : ℂ) :
    f z = f w := by
  obtain ⟨c, hc⟩ := differentiable_eq_const_of_has_period_lattice L hf hperiodic
  rw [hc z, hc w]

/-- Example VI.4-extra-9. Any holomorphic function on `ℂ` whose periods contain every point of the
lattice spanned by a period pair is constant; equivalently, any entire doubly periodic function is
constant. -/
theorem exists_eq_const_of_differentiable_doubly_periodic
    (L : PeriodPair) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hperiodic : HasPeriodLattice L f) :
    ∃ c : ℂ, f = const ℂ c := by
  obtain ⟨c, hc⟩ := differentiable_eq_const_of_has_period_lattice L hf hperiodic
  exact ⟨c, funext hc⟩
