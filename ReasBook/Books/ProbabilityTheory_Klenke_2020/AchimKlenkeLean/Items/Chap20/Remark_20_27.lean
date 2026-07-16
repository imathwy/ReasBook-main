import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap20.Definition_20_24
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap20.Example_20_9
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap20.Example_20_28
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap20.Example_20_36

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: if the correlation sequence itself converges to `P A * P B` for every measurable
-- `A` and `B`, then the system is strongly mixing in the sense recalled in Definition 20.24.
-- Combining this with Theorem 20.23 yields ergodicity.
/-- Remark 20.27: the mixing correlation limit condition implies ergodicity. -/
theorem ergodic_of_isStronglyMixing
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω} (hτ : MeasurePreserving τ P P)
    (hstrong : IsStronglyMixing τ P) :
    Ergodic τ P := sorry

-- Proof sketch: Example 20.9 gives ergodicity for irrational rotations on `AddCircle 1`. Such a
-- rotation is not strongly mixing, since the correlations of nontrivial Fourier characters do not
-- tend to the product of their integrals. Reuse the canonical translation map on `UnitAddCircle`;
-- the passage from `volume` to `AddCircle.haarAddCircle` is only the
-- canonical normalization bridge on `AddCircle 1`.
/-- An irrational rotation on the circle is ergodic but not mixing. -/
theorem irrational_mod_one_rotation_ergodic_not_mixing {r : ℝ} (hr : Irrational r) :
    Ergodic ((· + (r : UnitAddCircle))) AddCircle.haarAddCircle ∧
      ¬ IsStronglyMixing ((· + (r : UnitAddCircle))) AddCircle.haarAddCircle := by
  constructor
  · simpa [AddCircle.volume_eq_smul_haarAddCircle] using
      ((mod_one_rotation_ergodic_iff_irrational r).2 hr)
  · simpa [AddCircle.volume_eq_smul_haarAddCircle] using
      irrational_addCircle_rotation_not_stronglyMixing r hr
