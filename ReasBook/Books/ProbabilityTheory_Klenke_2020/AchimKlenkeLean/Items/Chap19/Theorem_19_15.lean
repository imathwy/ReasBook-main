import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap08.Example_8_27
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap19.Definition_19_1
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap19.Definition_19_11
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap19.Definition_19_13

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

variable {E : Type u}

/-- The electrical current induced by a potential `u` on the conductance network `C`, given by
Ohm's law `I(x,y) = C(x,y) (u(x) - u(y))`. -/
def electricalCurrent (C : E → E → ℝ≥0∞) (u : E → ℝ) : E → E → ℝ :=
  fun x y ↦ (C x y).toReal * (u x - u y)

-- Proof sketch: unfold `electricalCurrent`; evaluating the induced current at `(x,y)` gives the
-- Ohm-law expression `(C x y).toReal * (u x - u y)`.
/-- Evaluating the current induced by `u` gives the Ohm-law formula at the ordered edge
`(x,y)`. -/
@[simp]
theorem electricalCurrent_apply (C : E → E → ℝ≥0∞) (u : E → ℝ) (x y : E) :
    electricalCurrent C u x y = (C x y).toReal * (u x - u y) := rfl

section

variable [Fintype E]

/-- An electrical potential on `(E,C)` outside `A` is a potential whose Ohm-law current is a flow
on `E \ A`. -/
def IsElectricalPotential (C : E → E → ℝ≥0∞) (A : Set E) (u : E → ℝ) : Prop :=
  IsFlowOutside A (electricalCurrent C u)

-- Proof sketch: unfold `IsElectricalPotential`; the definition says exactly that the Ohm-law
-- current associated with `u` is a flow outside `A`.
/-- A function is an electrical potential exactly when its induced current is a flow on `E \ A`. -/
theorem isElectricalPotential_iff (C : E → E → ℝ≥0∞) (A : Set E) (u : E → ℝ) :
    IsElectricalPotential C A u ↔ IsFlowOutside A (electricalCurrent C u) := Iff.rfl

end

section MeasurableBridge

variable [MeasurableSpace E] [DiscreteMeasurableSpace E]

section

variable [Fintype E]

-- Proof sketch: combine Ohm's law with Kirchhoff's rule for the induced current. After dividing
-- the identity `∑ y, C(x,y) * (u x - u y) = 0` by the total conductance `conductance C x`, the
-- remaining equality is exactly the one-step averaging equation for the random walk with weights
-- `C`.
/-- Theorem 19.15: an electrical potential on the finite conductance network `(E,C)` is harmonic
outside `A` for the random walk with transition matrix `p(x,y) = C(x,y) / conductance C x`. -/
theorem electricalPotential_isHarmonicOn_compl
    {p C : E → E → ℝ≥0∞} [IsRandomWalkWithWeights p C]
    {A : Set E} {u : E → ℝ} (hu : IsElectricalPotential C A u) :
    IsHarmonicOutside (discreteMatrixKernel p) A u := sorry

-- Proof sketch: apply `electricalPotential_isHarmonicOn_compl` to both potentials and then invoke
-- the finite-state uniqueness principle for harmonic functions on `Aᶜ`. Since the electrical
-- network is finite, the complement `Aᶜ` is automatically finite, and irreducibility forces two
-- harmonic functions with the same boundary values to coincide.
/-- If the conductance network is irreducible, an electrical potential is uniquely determined by
its boundary values on `A`. -/
theorem electricalPotential_eq_of_eqOn_boundary_of_irreducible
    {p C : E → E → ℝ≥0∞} [IsRandomWalkWithWeights p C]
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)]
    {A : Set E} (hA_nonempty : A.Nonempty) {u v : E → ℝ}
    (hu : IsElectricalPotential C A u) (hv : IsElectricalPotential C A v)
    (h_eq : Set.EqOn u v A) :
    u = v := sorry

end

end MeasurableBridge

end ProbabilityTheory
