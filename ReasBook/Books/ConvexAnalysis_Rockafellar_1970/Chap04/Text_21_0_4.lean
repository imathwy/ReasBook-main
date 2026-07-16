import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_21_0_1

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage:

- `source-facing`: Text 21.0.4 says that a system of linear equations can be rewritten as a pair
  of weak linear inequalities by replacing each equation `⟪x, bᵢ⟫ = βᵢ` with the two inequalities
  `⟪x, bᵢ⟫ ≤ βᵢ` and `⟪x, -bᵢ⟫ ≤ -βᵢ`.
- `core/canonical`: the upstream owner abstractions are
  `LinearConstraintRelation.feasibleSet` specialized to relation `.eq` for the equation system and
  `linearInequalitySolutionSet` for the resulting pure weak system, with the doubled weak-parameter
  owner `linear_equation_pair_inequalities`.
- `bridge/view`: this item is exactly the equation-only specialization of the mixed bridge already
  provided upstream in `Text_19_0_2`.

Domain-style sampling used here:
- `LinearConstraintRelation.feasibleSet` (relation `.eq`);
- `linear_equation_pair_inequalities`;
- `linearInequalitySolutionSet`;
- `feasibleSet_eq_eq_pair_of_linear_inequality_solution_set` from `Text_19_0_2`.

Primitive data vs derived API:
- primitive data: the indexed normals `bᵢ` and right-hand sides `βᵢ`;
- derived API: the equality-system feasible set and its canonical realization as a weak
  inequality-system feasible set on a doubled index.

Layer target: `bridge/view`, with Chapter 19's equation-to-weak bridge repackaged at the Chapter
21 owner layer `convexInequalitySolutionSet` (all-weak relation on the doubled index).
-/

universe u

section

variable {𝕜 : Type*} {Y : Type*} {I : Type u}

open scoped Rockafellar

variable [CommRing 𝕜] [PartialOrder 𝕜]
variable [AddCommGroup Y] [Module 𝕜 Y]
variable [IsOrderedRing 𝕜]

local notation "weakRelation" => (fun _ : I ⊕ I ↦ ConvexInequalityRelation.le)
local notation "equationPairNormals" => (fun b : I → Y ↦ Sum.elim b (fun j ↦ -b j))
local notation "equationPairBounds" => (fun β : I → 𝕜 ↦ Sum.elim β (fun j ↦ -β j))

/- Text 21.0.4 in Chapter 21 owner form: a system of linear equations is equivalent to the all-weak
convex-inequality system on the doubled index obtained by replacing each equation
`⟪x, bᵢ⟫ = βᵢ` with `⟪x, bᵢ⟫ ≤ βᵢ` and `⟪x, -bᵢ⟫ ≤ -βᵢ`. -/
theorem feasibleSet_eq_eq_pair_of_weak_convexInequalitySolutionSet
    {X : Type*} [AddCommMonoid X] [Module 𝕜 X] [HasLinearPairing X Y 𝕜]
    (b : I → Y) (β : I → 𝕜) :
    (LinearConstraintRelation.feasibleSet (X := X)
      (fun _ ↦ (.eq : LinearConstraintRelation)) b β : Set X) =
      convexInequalitySolutionSet
        weakRelation
        (fun i x ↦ ⟪x, equationPairNormals b i⟫ₚ)
        (equationPairBounds β) := by
  calc
    (LinearConstraintRelation.feasibleSet (X := X)
      (fun _ ↦ (.eq : LinearConstraintRelation)) b β : Set X) =
        solutionSet[linear_equation_pair_inequalities b β] :=
      feasibleSet_eq_eq_pair_of_linear_inequality_solution_set b β
    _ =
        LinearConstraintRelation.leFeasible
          (equationPairNormals b)
          (equationPairBounds β) := by
      simpa [linear_equation_pair_inequalities] using
        (linearInequalitySolutionSet_range_eq_leFeasible
          (a := equationPairNormals b)
          (α := equationPairBounds β))
    _ =
        convexInequalitySolutionSet
          weakRelation
          (fun i x ↦ ⟪x, equationPairNormals b i⟫ₚ)
          (equationPairBounds β) := by
      ext x
      simp [convexInequalitySolutionSet]

end
