import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_19_5_1 (from Items/Chap19) -/
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

/-! ### Exercise_19_5_2 (from Items/Chap19) -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory.DiscreteMarkovChain

/-
`source-facing`: the two-hexagon honeycomb graph together with the distinguished vertices
`one`, `zero`, and `start = x`.
`core/canonical`: the Chapter 19 graph-walk owner `IsSimpleRandomWalk`, the discrete-kernel owner
`discreteMatrixKernel`, and the first-hit owner `F_A`.
`bridge/view`: the concrete transition matrix `honeycombTransitionMatrix`, obtained from the unit
conductances of the honeycomb graph.
-/

/-- The ten vertices of the two-hexagon honeycomb graph from Exercise 19.5.2, with distinguished
vertices `one`, `zero`, and `start = x`. -/
inductive HoneycombVertex
  | one
  | leftUpper
  | sharedUpper
  | start
  | lowerMiddle
  | leftLower
  | rightUpperLeft
  | rightUpperRight
  | zero
  | rightLower
  deriving DecidableEq, Fintype

open HoneycombVertex

/-- The finite honeycomb state space carries the discrete measurable structure. -/
instance : MeasurableSpace HoneycombVertex := ⊤

/-- The measurable structure on the honeycomb state space is discrete. -/
instance : DiscreteMeasurableSpace HoneycombVertex := by
  infer_instance

/-- The undirected edges of the two-hexagon honeycomb graph, listed once each. -/
private def honeycombEdges : Finset (HoneycombVertex × HoneycombVertex) :=
  { (one, leftUpper),
    (one, leftLower),
    (leftUpper, sharedUpper),
    (sharedUpper, start),
    (sharedUpper, rightUpperLeft),
    (start, lowerMiddle),
    (start, rightLower),
    (lowerMiddle, leftLower),
    (rightUpperLeft, rightUpperRight),
    (rightUpperRight, zero),
    (zero, rightLower) }

/-- The adjacency relation of the two-hexagon honeycomb graph. -/
private def honeycombAdj (x y : HoneycombVertex) : Prop :=
  (x, y) ∈ honeycombEdges ∨ (y, x) ∈ honeycombEdges

private theorem honeycombAdj_symm : Symmetric honeycombAdj := by
  intro x y hxy
  simpa [honeycombAdj, or_comm] using hxy

private theorem honeycombAdj_irrefl : Std.Irrefl honeycombAdj := by
  exact ⟨fun x ↦ by
    cases x <;> simp [honeycombAdj, honeycombEdges]⟩

/-- The two-hexagon honeycomb graph from Exercise 19.5.2. -/
def honeycombGraph : SimpleGraph HoneycombVertex where
  Adj := honeycombAdj
  symm := honeycombAdj_symm
  loopless := honeycombAdj_irrefl

/-- The unit conductance family of the honeycomb graph. -/
def honeycombConductance : HoneycombVertex → HoneycombVertex → ℝ≥0∞ :=
  simpleGraphWeights honeycombGraph

/-- The simple random-walk transition matrix on the honeycomb graph. -/
def honeycombTransitionMatrix : HoneycombVertex → HoneycombVertex → ℝ≥0∞ :=
  conductanceTransitionMatrix honeycombConductance

-- Proof sketch: each honeycomb vertex has degree `2` or `3`, so the normalized unit-conductance
-- walk on `honeycombGraph` is exactly the simple random walk on that graph.
/-- The honeycomb transition matrix is the Chapter 19 simple-random-walk owner on
`honeycombGraph`. -/
theorem honeycombTransitionMatrix_isSimpleRandomWalk :
    IsSimpleRandomWalk honeycombTransitionMatrix honeycombGraph := sorry

/-- The honeycomb transition matrix is stochastic. -/
theorem honeycombTransitionMatrix_isStochastic :
    IsStochasticMatrix honeycombTransitionMatrix :=
  IsRandomWalkWithWeights.isStochasticMatrix honeycombTransitionMatrix_isSimpleRandomWalk

/-- The discrete kernel associated with `honeycombTransitionMatrix` is Markov. -/
instance : IsMarkovKernel (discreteMatrixKernel honeycombTransitionMatrix) :=
  discreteMatrixKernel_isMarkovKernel _ honeycombTransitionMatrix_isStochastic

section

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : HoneycombVertex → ProbabilityMeasure Ω}
variable {X : ℕ → Ω → HoneycombVertex}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ discreteMatrixKernel honeycombTransitionMatrix ^ n) P X]

-- Proof sketch: either reduce the electrical network by star-triangle moves and apply the
-- effective-resistance formula for the corresponding Dirichlet problem, or kill the chain at
-- `{one, zero}` and compute the Green matrix entry for the matrix inverse `(I - p̄)⁻¹`. Both
-- methods yield the same value `8 / 17`.
/-- Exercise 19.5.2: for the simple random walk on the two-hexagon honeycomb graph, started at the
distinguished vertex `x`, the probability of visiting `1` before `0` is `8 / 17`; this is the
value the exercise asks to recover both by network reduction and by matrix inversion. -/
theorem honeycomb_start_hittingProbability_one_before_zero :
    F_A P X ({zero} : Set HoneycombVertex) start one = (8 : ℝ) / 17 := sorry

end

end ProbabilityTheory.DiscreteMarkovChain

/-! ### Exercise_19_5_3 (from Items/Chap19) -/
open MeasureTheory ProbabilityTheory SimpleGraph
open scoped ENNReal

noncomputable section

universe u v

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

/-
Domain-style sampling for Exercise 19.5.3:
- `source-facing`: the simple ladder graph of Fig. 19.15 together with the marked vertices `a`
  and `z`.
- `core/canonical`: `SimpleGraph.pathGraph`, `SimpleGraph.boxProd`, `SimpleGraph.pathGraph_adj`,
  and `SimpleGraph.boxProd_adj`.
- `bridge/view`: any explicit coordinate adjacency description on `Fin 7 × Fin 2`, derived from
  the box-product owner when needed.
Primitive data: the ladder graph and the distinguished vertices `a`, `z`, reused from
`Exercise_19_5_LadderGraphs`.
Derived API: the conductance and hitting-probability statements below.
-/

-- Proof sketch: use the left-right reflection symmetry about the middle rung to reduce the
-- network to one half of the ladder, solve the resulting reduced network by series-parallel
-- reduction, and evaluate the induced effective conductance.
/-- Exercise 19.5.3 (1): item (i). For the simple ladder graph of Fig. 19.15, the effective
conductance between the middle vertices `a` and `z` is `√3`. -/
theorem simpleLadder_effectiveConductance_between_a_z_eq_sqrt_three
    :
    effectiveConductance (simpleGraphWeights simpleLadderGraph)
      ({simpleLadderA} : Set SimpleLadderVertex) ({simpleLadderZ} : Set SimpleLadderVertex) =
        Real.sqrt 3 := sorry

-- Proof sketch: apply the owner-level formula
-- `effectiveConductance_eq_netFlowOnSet_electricalCurrent` to the simple ladder boundary value
-- problem and then use
-- `simpleLadder_effectiveConductance_between_a_z_eq_sqrt_three`.
/-- For any unit-boundary electrical potential on the simple ladder graph with `u(a) = 1` and
`u(z) = 0`, the emitted boundary current through the sink `{z}` is `-√3` because `netFlowOnSet`
uses the emitted-current convention. This is the boundary-current companion to the owner-level
conductance statement above. -/
theorem simpleLadder_netFlowOnSet_electricalCurrent_at_z_eq_neg_sqrt_three
    {u : SimpleLadderVertex → ℝ}
    (hu : IsElectricalPotential (simpleGraphWeights simpleLadderGraph) simpleLadderBoundary u)
    (ha : u simpleLadderA = 1)
    (hz : u simpleLadderZ = 0) :
    netFlowOnSet (electricalCurrent (simpleGraphWeights simpleLadderGraph) u)
      ({simpleLadderZ} : Set SimpleLadderVertex) = -Real.sqrt 3 := sorry

-- Proof sketch: identify `P_a[τ_z < τ_a]` with
-- `escapeToSetProbability P X simpleLadderA {simpleLadderZ}`. Then use the effective
-- conductance computation from
-- `simpleLadder_effectiveConductance_between_a_z_eq_sqrt_three` together with the network identity
-- `P_a[τ_z < τ_a] = conductance(a)⁻¹ C_eff(a ↔ z)` and the fact that the Chapter 19 owner
-- `IsSimpleRandomWalk p simpleLadderGraph` makes `a` a degree-`3` simple-graph state.
/-- Exercise 19.5.3 (2): item (ii). For a random walk started at the middle top vertex `a` of the
simple ladder graph, the probability of hitting `z` before the first strictly positive return to
`a` is `1 / √3`. -/
theorem simpleLadder_hit_z_before_return_to_a_eq_inv_sqrt_three
    {Ω : Type v} [MeasurableSpace Ω]
    {p : SimpleLadderVertex → SimpleLadderVertex → ℝ≥0∞}
    {P : SimpleLadderVertex → ProbabilityMeasure Ω}
    {X : ℕ → Ω → SimpleLadderVertex}
    [IsSimpleRandomWalk p simpleLadderGraph]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    escapeToSetProbability P X simpleLadderA ({simpleLadderZ} : Set SimpleLadderVertex) =
      ENNReal.ofReal (1 / Real.sqrt 3) := sorry

end ProbabilityTheory

/-! ### Exercise_19_5_4 (from Items/Chap19) -/
open MeasureTheory ProbabilityTheory SimpleGraph
open scoped ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

/- Domain-style sampling for Exercise 19.5.4:
- `source-facing`: the crossed ladder graph of Fig. 19.16 with the distinguished vertices `a` and
  `z`.
- Inspected owner declarations:
  `SimpleLadderVertex`,
  `simpleLadderA`,
  `simpleLadderZ`,
  `effectiveConductance`,
  `escapeToSetProbability`.
- Best owner abstraction: the concrete Fig. 19.16 graph on the shared ladder carrier from
  `Exercise_19_5_LadderGraphs`, with the source quantities expressed through the Chapter 19 owners
  `effectiveConductance` and `escapeToSetProbability`.
- Primitive data: the graph of Fig. 19.16 itself. The carrier and marked vertices are reused from
  `Exercise_19_5_LadderGraphs` rather than duplicated.
  Derived API: the effective conductance between `a` and `z` and the hit-before-return probability
  for simple random walk on that graph.
- Source/core/bridge triage: this file is `source-facing`; it models the concrete graph from the
  figure, while the conductance and hitting-probability expressions are the existing canonical
  Chapter 19 bridge/view owners. -/

-- Proof sketch: by reflection symmetry across the horizontal midline and across the middle
-- column, every non-boundary column has potential `1 / 2` on both vertices in the unit boundary
-- value problem with `u(a) = 1` and `u(z) = 0`. The emitted current from `a` is therefore
-- `1 + 4 * (1 / 2) = 3`.
/-- Exercise 19.5.4 (1): for the crossed ladder graph of Fig. 19.16, the effective conductance
between `a` and `z` is `3`. -/
theorem crossedLadder_effectiveConductance_between_a_z_eq_three :
    effectiveConductance (simpleGraphWeights crossedLadderGraph)
      ({simpleLadderA} : Set SimpleLadderVertex) ({simpleLadderZ} : Set SimpleLadderVertex) = 3 :=
  sorry

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {p : SimpleLadderVertex → SimpleLadderVertex → ℝ≥0∞}
variable {P : SimpleLadderVertex → ProbabilityMeasure Ω}
variable {X : ℕ → Ω → SimpleLadderVertex}
variable [IsSimpleRandomWalk p crossedLadderGraph]
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

-- Proof sketch: the marked vertex `a` has degree `5` in the crossed ladder graph. Combine the
-- conductance value from `crossedLadder_effectiveConductance_between_a_z_eq_three` with the
-- Chapter 19 identity `P_a[τ_z < τ_a] = conductance(a)⁻¹ C_eff(a ↔ z)`.
/-- Exercise 19.5.4 (2): for the simple random walk on the crossed ladder graph of Fig. 19.16,
started at `a`, the probability of hitting `z` before the first strictly positive return to `a`
is `3 / 5`. -/
theorem crossedLadder_hit_z_before_return_to_a_eq_three_fifths :
    escapeToSetProbability P X simpleLadderA ({simpleLadderZ} : Set SimpleLadderVertex) =
      (3 / 5 : ℝ≥0∞) := sorry

end

end ProbabilityTheory

/-! ### Definition_19_5 (from Items/Chap19) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E]

/-- Definition 19.5: a function `f` solves the Dirichlet problem on `E \ A` with respect to
`p - I` and boundary value `g` on `A` if `f` is harmonic outside `A` for `p` and agrees with `g`
on `A`. -/
def SolvesDirichletProblem (p : Kernel E E) (A : Set E) (g f : E → ℝ) : Prop :=
  IsHarmonicOutside p A f ∧ Set.EqOn f g A

-- Proof sketch: unfold `SolvesDirichletProblem`; the two conjuncts are exactly harmonicity on
-- `E \ A` and equality with the prescribed boundary values on `A`.
/-- Solving the Dirichlet problem means being harmonic off the boundary set and matching the
boundary datum on that boundary. -/
theorem solvesDirichletProblem_iff (p : Kernel E E) (A : Set E) (g f : E → ℝ) :
    SolvesDirichletProblem p A g f ↔ IsHarmonicOutside p A f ∧ Set.EqOn f g A :=
  Iff.rfl

end ProbabilityTheory

/-! ### Exercise_19_5_5 (from Items/Chap19) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

/- Domain-style sampling for Exercise 19.5.5:
- Primary domain: discrete-time Markov chains on finite graphs, viewed through electrical-network
  hitting probabilities.
- Inspected owner declarations:
  `HypercubeState`,
  `hypercubeFlipAt`,
  `simpleGraphWeights` / `IsSimpleRandomWalk`,
  `escapeToSetProbability`,
  `simpleLadder_hit_z_before_return_to_a_eq_inv_sqrt_three`.
- Best owner abstraction: the simple random walk on the Chapter 18 hypercube state space
  `HypercubeState 4`, with the source quantity `P_a[τ_z < τ_a]` expressed through the Chapter 19
  owner `escapeToSetProbability`.
- Primitive data: the Fig. 19.17 hypercube graph on `HypercubeState 4` and its distinguished
  vertices `a` and `z`.
  Derived API: the value of `escapeToSetProbability` for that walk.
- Source/core/bridge triage: the main item is `source-facing`; the graph and vertices model the
  concrete figure, while `escapeToSetProbability` is the existing `bridge/view` used to encode
  `P_a[τ_z < τ_a]` canonically. -/

/-- The adjacency relation of the hypercube in Fig. 19.17: two vertices are adjacent when one is
obtained from the other by flipping exactly one coordinate. -/
private def fig19_17Adj (x y : HypercubeState 4) : Prop :=
  ∃ i : Fin 4, y = hypercubeFlipAt x i

-- Proof sketch: flipping the same coordinate twice returns to the original vertex, so
-- `y = hypercubeFlipAt x i` implies `x = hypercubeFlipAt y i`.
/-- The Fig. 19.17 hypercube adjacency relation is symmetric. -/
private theorem fig19_17Adj_symm : Symmetric fig19_17Adj := sorry

-- Proof sketch: `hypercubeFlipAt x i` differs from `x` at the coordinate `i`, so no vertex is
-- adjacent to itself.
/-- The Fig. 19.17 hypercube adjacency relation is irreflexive. -/
private theorem fig19_17Adj_irrefl : Std.Irrefl fig19_17Adj := sorry

/-- The graph of Fig. 19.17, modeled as the 4-dimensional hypercube. -/
def fig19_17HypercubeGraph : SimpleGraph (HypercubeState 4) where
  Adj := fig19_17Adj
  symm := fig19_17Adj_symm
  loopless := fig19_17Adj_irrefl

/-- The distinguished starting vertex `a` in Fig. 19.17. -/
def fig19_17A : HypercubeState 4 := fun _ ↦ false

/-- The distinguished target vertex `z` in Fig. 19.17, opposite to `a` in the hypercube. -/
def fig19_17Z : HypercubeState 4 := fun _ ↦ true

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {p : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
variable {P : HypercubeState 4 → ProbabilityMeasure Ω}
variable {X : ℕ → Ω → HypercubeState 4}
variable [IsSimpleRandomWalk p fig19_17HypercubeGraph]
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

-- Proof sketch: collapse the hypercube by Hamming distance from `a`; the resulting birth-death
-- chain on the four distance layers has boundary values `0` at `a` and `1` at `z`. Solving the
-- layer equations gives `P_a[τ_z < τ_a] = 3 / 8`.
/-- Exercise 19.5.5: for the simple random walk on the hypercube of Fig. 19.17, started at `a`,
the probability of hitting the opposite vertex `z` before the first strictly positive return to
`a` is `3 / 8`. -/
theorem fig19_17_hit_z_before_return_to_a_eq_three_eighths :
    escapeToSetProbability P X fig19_17A {fig19_17Z} =
      (3 / 8 : ℝ≥0∞) := sorry

end

end ProbabilityTheory

/-! ### Exercise_19_5_LadderGraphs (from Items/Chap19) -/
open SimpleGraph

noncomputable section

namespace ProbabilityTheory

/-- The vertex set shared by the ladder graphs in Figs. 19.15 and 19.16, realized as seven
columns and two rows. -/
abbrev SimpleLadderVertex := Fin 7 × Fin 2

/-- The simple ladder graph of Fig. 19.15, realized as the box product of the seven-vertex path
with the two-vertex path. -/
def simpleLadderGraph : SimpleGraph SimpleLadderVertex :=
  pathGraph 7 □ pathGraph 2

/-- The crossed ladder graph of Fig. 19.16 on the same vertex set. Adjacent columns are completely
joined, and each column still contains its vertical rung. -/
def crossedLadderGraph : SimpleGraph SimpleLadderVertex where
  Adj x y := (pathGraph 7).Adj x.1 y.1 ∨ x.1 = y.1 ∧ (pathGraph 2).Adj x.2 y.2
  symm x y := by
    simp [or_comm, eq_comm, adj_comm]
  loopless := ⟨fun x ↦ by simp⟩

/-- The distinguished top-middle vertex `a` in Figs. 19.15 and 19.16. -/
abbrev simpleLadderA : SimpleLadderVertex := (⟨3, by decide⟩, ⟨1, by decide⟩)

/-- The distinguished bottom-middle vertex `z` in Figs. 19.15 and 19.16. -/
abbrev simpleLadderZ : SimpleLadderVertex := (⟨3, by decide⟩, ⟨0, by decide⟩)

/-- The boundary pair `{a, z}` shared by the ladder exercises. -/
def simpleLadderBoundary : Set SimpleLadderVertex := {simpleLadderA, simpleLadderZ}

end ProbabilityTheory
