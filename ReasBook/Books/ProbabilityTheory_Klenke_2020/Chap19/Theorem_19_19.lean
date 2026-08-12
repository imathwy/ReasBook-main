import ProbabilityTheory_Klenke_2020.Chap19.Definition_19_17
import ProbabilityTheory_Klenke_2020.Chap19.Theorem_19_15

open scoped BigOperators ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

/- Domain-style sampling for Theorem 19.19:
- `source-facing`: the finite-boundary effective conductance `C_eff(A0 ↔ A1)`.
- `core/canonical`: `electricalCurrent`, `IsElectricalPotential`, `netFlowOnSet`, and the
  Chapter 19 quadratic-energy pattern already used for electrical flows.
- `bridge/view`: Definition 19.17 identifies `C_eff(A0 ↔ A1)` with the boundary current of a
  unit-voltage electrical potential, so the current-based formula belongs as companion API rather
  than as the owner statement. -/

attribute [local instance] Classical.propDecidable

variable {E : Type u} [Fintype E]
variable {p p' C C' : E → E → ℝ≥0∞}
variable [IsRandomWalkWithWeights p C] [IsRandomWalkWithWeights p' C']
variable {A0 A1 : Set E} {u u' : E → ℝ}

/-- The Dirichlet energy of a potential `u` on the conductance network `C`. -/
def dirichletEnergy (C : E → E → ℝ≥0∞) (u : E → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x : E, ∑ y : E, (C x y).toReal * (u x - u y) ^ (2 : ℕ)

/-- The finite-boundary effective conductance between `A0` and `A1`, defined intrinsically as the
infimum of the Dirichlet energies of unit-boundary potentials. -/
def effectiveConductance (C : E → E → ℝ≥0∞) (A0 A1 : Set E) : ℝ :=
  sInf <|
    dirichletEnergy C ''
      {u : E → ℝ | Set.EqOn u (fun _ : E ↦ 0) A0 ∧ Set.EqOn u (fun _ : E ↦ 1) A1}

-- Proof sketch: Definition 19.17 identifies the effective conductance with the boundary current
-- of the electrical current induced by any unit-voltage electrical potential between `A0` and
-- `A1`; this realizes the infimum in `effectiveConductance`.
/-- For a unit-voltage electrical potential between disjoint nonempty boundary sets, the owner
`effectiveConductance C A0 A1` is the boundary current through `A1`. -/
theorem effectiveConductance_eq_netFlowOnSet_electricalCurrent
    (hA0 : A0.Nonempty) (hA1 : A1.Nonempty) (hdisj : Disjoint A0 A1)
    (hu : IsElectricalPotential C (A0 ∪ A1) u)
    (hu0 : Set.EqOn u (fun _ : E ↦ 0) A0)
    (hu1 : Set.EqOn u (fun _ : E ↦ 1) A1) :
    effectiveConductance C A0 A1 =
      netFlowOnSet (electricalCurrent C u) A1 := sorry

-- Proof sketch: the Dirichlet-energy infimum defining `effectiveConductance` is monotone in the
-- conductance family because every admissible unit-boundary potential has smaller energy for `C'`
-- than for `C` when `C' ≤ C` pointwise. The nonempty and disjoint boundary hypotheses are the
-- textbook assumptions for the finite-boundary conductance problem.
/-- Theorem 19.19: Rayleigh's monotonicity principle. If `C' x y ≤ C x y` for all `x, y`, then the
effective conductance `C_eff(A0 ↔ A1)` of the network with conductances `C` is at least the
effective conductance for `C'`. -/
theorem rayleigh_monotonicity_principle
    (hA0 : A0.Nonempty) (hA1 : A1.Nonempty) (hdisj : Disjoint A0 A1)
    (hCC' : ∀ x y : E, C' x y ≤ C x y) :
    effectiveConductance C A0 A1 ≥ effectiveConductance C' A0 A1 := sorry

-- Proof sketch: rewrite both effective conductances via
-- `effectiveConductance_eq_netFlowOnSet_electricalCurrent`, then apply the owner-level Rayleigh
-- monotonicity theorem.
/-- For unit-voltage electrical potentials on the two conductance networks, Rayleigh monotonicity
rewrites as the corresponding boundary-current inequality. -/
theorem rayleigh_monotonicity_principle_netFlowOnSet
    (hA0 : A0.Nonempty) (hA1 : A1.Nonempty) (hdisj : Disjoint A0 A1)
    (hCC' : ∀ x y : E, C' x y ≤ C x y)
    (hu : IsElectricalPotential C (A0 ∪ A1) u)
    (hu0 : Set.EqOn u (fun _ : E ↦ 0) A0)
    (hu1 : Set.EqOn u (fun _ : E ↦ 1) A1)
    (hu' : IsElectricalPotential C' (A0 ∪ A1) u')
    (hu'0 : Set.EqOn u' (fun _ : E ↦ 0) A0)
    (hu'1 : Set.EqOn u' (fun _ : E ↦ 1) A1) :
    netFlowOnSet (electricalCurrent C u) A1 ≥
      netFlowOnSet (electricalCurrent C' u') A1 := sorry

end ProbabilityTheory
