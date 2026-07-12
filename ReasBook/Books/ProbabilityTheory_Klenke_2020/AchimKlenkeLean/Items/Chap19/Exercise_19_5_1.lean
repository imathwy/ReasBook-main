import ProbabilityTheory_Klenke_2020.Items.Chap19.Theorem_19_19
import Mathlib

open scoped BigOperators ENNReal

noncomputable section

namespace ProbabilityTheory

/- Domain-style sampling for Exercise 19.5.1:
- `source-facing`: the star-triangle transformation for a three-legged star with branch
  conductances `c`.
- `core/canonical`: finite conductance families together with the Chapter 19 owner declaration
  `dirichletEnergy`.
- `bridge/view`: the star and triangle boundary energies below are source-facing views obtained by
  evaluating `dirichletEnergy` on the corresponding conductance families. -/

/-- The total conductance of the three star edges. -/
def starTriangleTotalConductance (c : Fin 3 → NNReal) : NNReal :=
  ∑ i : Fin 3, c i

/-- The conductance-weighted center value used in the star-triangle transformation. When
`0 < starTriangleTotalConductance c`, this is the unique harmonic potential at the center; when
the total conductance vanishes, the defining weighted sum is `0`, so this value is `0`. -/
def starTriangleCenterPotential (c : Fin 3 → NNReal) (v : Fin 3 → ℝ) : ℝ :=
  (∑ i : Fin 3, (c i : ℝ) * v i) / starTriangleTotalConductance c

/-- The conductance family on the boundary triangle equivalent to the star with branch
conductances `c`. -/
def starTriangleEquivalentConductance (c : Fin 3 → NNReal) : Fin 3 → Fin 3 → ℝ≥0∞ :=
  fun i j ↦
    if i = j then 0
    else ((c i * c j / starTriangleTotalConductance c : NNReal) : ℝ≥0∞)

-- Proof sketch: unfold `starTriangleEquivalentConductance`; when `i ≠ j` the off-diagonal branch
-- of the `if` reduces to the quotient formula `c i * c j / ∑ k, c k`.
/-- Off the diagonal, the triangle edge conductance is `c i * c j / (∑ k, c k)`. -/
theorem starTriangleEquivalentConductance_apply_of_ne
    (c : Fin 3 → NNReal) {i j : Fin 3} (hij : i ≠ j) :
    starTriangleEquivalentConductance c i j =
      c i * c j / starTriangleTotalConductance c := sorry

private inductive StarTriangleVertex
  | center
  | boundary (i : Fin 3)
  deriving DecidableEq, Fintype

private def starConductance (c : Fin 3 → NNReal) : StarTriangleVertex → StarTriangleVertex → ℝ≥0∞
  | .center, .boundary i => c i
  | .boundary i, .center => c i
  | _, _ => 0

private def starPotential (u : ℝ) (v : Fin 3 → ℝ) : StarTriangleVertex → ℝ
  | .center => u
  | .boundary i => v i

/-- The Dirichlet energy of the star network with center potential `u` and boundary potential
`v`. -/
def starNetworkBoundaryEnergy (c : Fin 3 → NNReal) (u : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  dirichletEnergy (starConductance c) (starPotential u v)

/-- The Dirichlet energy of the triangle obtained from the star by the star-triangle
transformation. -/
def triangleNetworkBoundaryEnergy (c : Fin 3 → NNReal) (v : Fin 3 → ℝ) : ℝ :=
  dirichletEnergy (starTriangleEquivalentConductance c) v

-- Proof sketch: if `starTriangleTotalConductance c = 0`, then every branch conductance vanishes,
-- so both Dirichlet energies are `0`. Otherwise substitute the weighted center value
-- `starTriangleCenterPotential c v = (∑ i, c i * v i) / (∑ i, c i)` into the star energy,
-- expand the square, and simplify the resulting quadratic form. The coefficients match the
-- triangle energy defined by the equivalent conductance family
-- `starTriangleEquivalentConductance c`.
/-- Exercise 19.5.1: the star-triangle transformation is valid. For three boundary vertices with
star branch conductances `c`, eliminating the center vertex by the conductance-weighted center
value `starTriangleCenterPotential c v` produces the same boundary Dirichlet energy as the
triangle with edge conductances `c i * c j / (∑ k, c k)`. For positive total conductance this
center value is the harmonic one, while in the degenerate zero-conductance case both energies
vanish. -/
theorem star_triangle_transformation
    (c : Fin 3 → NNReal) (v : Fin 3 → ℝ) :
    starNetworkBoundaryEnergy c (starTriangleCenterPotential c v) v =
      triangleNetworkBoundaryEnergy c v := sorry

end ProbabilityTheory
