import ProbabilityTheory_Klenke_2020.Items.Chap20.Example_20_9
import ProbabilityTheory_Klenke_2020.Items.Chap20.Example_20_36
import ProbabilityTheory_Klenke_2020.Items.Chap20.Remark_20_25

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/- Exercise 20.5.1 (1): strongly mixing implies weak mixing. This is exactly the already
formalized theorem `isWeaklyMixing_of_isStronglyMixing`. -/
recall isWeaklyMixing_of_isStronglyMixing

-- Proof sketch: apply weak mixing to an invariant measurable set `A` with `B = A`. The Cesàro
-- averages then have constant value `|P A - (P A)^2|`, so the weak-mixing limit forces
-- `P A = 0` or `P A = 1`, which is the defining criterion for ergodicity.
/-- Exercise 20.5.1 (2): every weakly mixing probability-preserving dynamical system is ergodic. -/
theorem ergodic_of_isWeaklyMixing
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hτ : MeasurePreserving τ P P) (hweak : IsWeaklyMixing τ P) :
    Ergodic τ P := sorry

-- Proof sketch: combine `mod_one_rotation_ergodic_iff_irrational` with `irrational_pi`,
-- then transport the result from `volume` to `AddCircle.haarAddCircle`. The measure-preserving
-- part is already contained in `Ergodic`. Nontrivial Fourier characters on the additive circle
-- give eigenfunctions for the rotation, so the system is not weakly mixing.
/-- Exercise 20.5.1 (3-5): rotation by `π` on `AddCircle 1` with Haar probability measure is an
ergodic but not weakly mixing dynamical system. -/
theorem rotation_by_pi_ergodic_not_weaklyMixing :
    Ergodic ((· + (Real.pi : UnitAddCircle))) AddCircle.haarAddCircle ∧
      ¬ IsWeaklyMixing ((· + (Real.pi : UnitAddCircle))) AddCircle.haarAddCircle := by
  constructor
  · simpa [AddCircle.volume_eq_smul_haarAddCircle] using
      ((mod_one_rotation_ergodic_iff_irrational Real.pi).2 irrational_pi)
  · sorry
