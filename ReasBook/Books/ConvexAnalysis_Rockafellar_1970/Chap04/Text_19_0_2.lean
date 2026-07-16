import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Definition_17_2_4
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {𝕜 : Type*} {Y : Type*}
variable {I : Type u} {J : Type v}

open scoped Rockafellar
open LinearConstraintRelation

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 19.0.2 says that the feasible set of any finite mixed system of linear
  equations and weak linear inequalities is polyhedral convex, presented here directly at the
  abstract pairing-based module layer.
- `core/canonical`: the owner abstractions already present upstream are
  `LinearConstraintRelation.feasibleSet` for the mixed system,
  `linearInequalitySolutionSet` for the pure weak subsystem, and `Set.IsPolyhedral` for the
  polyhedral conclusion.
- `bridge/view`: the textbook split into one family of equations and one family of weak
  inequalities is encoded by the mixed owner on the sum index `I ⊕ J`, while the doubled pure
  weak system is routed through the chapter owner `linearInequalitySolutionSet`.
- Domain-style sampling used here: the mixed owner `LinearConstraintRelation.feasibleSet` and its
  membership theorem `LinearConstraintRelation.mem_feasibleSet`; `linearInequalitySolutionSet`
  and `mem_linearInequalitySolutionSet_range_iff`; and the finite-index polyhedral owner bridge
  `Set.isPolyhedral_setOf_forall_linear_le` from `Text_19_0_1`.
- Primitive data vs derived API: the primitive inputs are the ambient primal carrier `X` together
  with the finite families `a, α` and `b, β`; the owner-side mixed feasible set and its
  polyhedrality are derived API, while the doubled-index pure-inequality realization is a
  canonical `bridge/view` into `linearInequalitySolutionSet`.
- Layer target: the main theorem is refined to the `core/canonical` owner
  `LinearConstraintRelation.feasibleSet` on the mixed side and to `linearInequalitySolutionSet` on
  the pure weak side, with equation systems also expressed on
  `LinearConstraintRelation.feasibleSet` specialized to `.eq`.
--/

/-- Membership in the equation-only specialization of `feasibleSet` is exactly the pointwise
family of equations. -/
@[simp] theorem mem_feasibleSet_eq
    {X : Type*} [LE 𝕜] [LT 𝕜] [HasPairing X Y 𝕜]
    (b : I → Y) (β : I → 𝕜) :
    (feasibleSet (fun _ ↦ (.eq : LinearConstraintRelation)) b β : Set X) =
      {x : X | ∀ i, ⟪x, b i⟫ₚ = β i} := by
  ext x
  simp [mem_feasibleSet]

/-- Doubled weak-system parameters obtained by replacing each equation
`⟪x, b i⟫ = β i` with `⟪x, b i⟫ ≤ β i` and `⟪x, -b i⟫ ≤ -β i`. -/
def linear_equation_pair_inequalities
    [Neg Y] [Neg 𝕜]
    (b : I → Y) (β : I → 𝕜) : Set (Y × 𝕜) :=
  Set.range fun i : I ⊕ I ↦
    (Sum.elim b (fun j ↦ -(b j)) i, Sum.elim β (fun j ↦ -(β j)) i)

/-- Doubled weak-system parameters for a mixed system: each equality in `(a, α)` is replaced by
its pair of weak inequalities, while each weak inequality in `(b, β)` is kept unchanged. -/
def mixed_linear_constraint_pair_inequalities
    [Neg Y] [Neg 𝕜]
    (a : I → Y) (α : I → 𝕜) (b : J → Y) (β : J → 𝕜) : Set (Y × 𝕜) :=
  Set.range fun i : (I ⊕ I) ⊕ J ↦
    (Sum.elim (Sum.elim a fun j ↦ -(a j)) b i,
      Sum.elim (Sum.elim α fun j ↦ -(α j)) β i)

section EquationToWeakBridge

variable [AddGroup 𝕜] [PartialOrder 𝕜] [AddLeftMono 𝕜] [AddRightMono 𝕜]

/-- Equation-only specialization of the mixed bridge: each equality
`⟪x, b i⟫ = β i` may be replaced by the pair of weak inequalities
`⟪x, b i⟫ ≤ β i` and `⟪x, -b i⟫ ≤ -β i`. -/
theorem feasibleSet_eq_eq_pair_of_linear_inequality_solution_set
    {X : Type*} [Neg Y] [HasPairing X Y 𝕜] [HasPairingNegRight X Y 𝕜]
    (b : I → Y) (β : I → 𝕜) :
    (feasibleSet (fun _ ↦ (.eq : LinearConstraintRelation)) b β : Set X) =
      solutionSet[linear_equation_pair_inequalities b β] := by
  ext x
  rw [mem_feasibleSet, linear_equation_pair_inequalities,
    mem_linearInequalitySolutionSet_range_iff]
  simp [forall_and, HasPairingNegRight.pairing_neg_right, le_antisymm_iff, neg_le_neg_iff]

/-- The owner mixed feasible set is exactly the pure weak-inequality system obtained by doubling
the equality indices and negating the second copy. -/
theorem mixed_linear_constraint_solution_set_eq_linear_inequality_solution_set
    {X : Type*} [Neg Y] [HasPairing X Y 𝕜] [HasPairingNegRight X Y 𝕜]
    (a : I → Y) (α : I → 𝕜) (b : J → Y) (β : J → 𝕜) :
    (feasibleSet
      (Sum.elim (fun _ ↦ .eq) fun _ ↦ .le)
      (Sum.elim a b) (Sum.elim α β) : Set X) =
      solutionSet[mixed_linear_constraint_pair_inequalities a α b β] := by
  ext x
  rw [mem_feasibleSet, mixed_linear_constraint_pair_inequalities,
    mem_linearInequalitySolutionSet_range_iff]
  simp [forall_and, HasPairingNegRight.pairing_neg_right, le_antisymm_iff, neg_le_neg_iff]

end EquationToWeakBridge

section Polyhedrality

variable [AddGroup 𝕜] [PartialOrder 𝕜] [AddLeftMono 𝕜] [AddRightMono 𝕜]

/-- Text 19.0.2: the common solution set of finitely many linear equations and finitely many weak
linear inequalities is a polyhedral convex set, stated at an arbitrary paired primal/dual
owner layer. -/
theorem mixed_linear_system_solution_set_isPolyhedralConvexSet
    {X : Type*} [Neg Y] [HasPairing X Y 𝕜] [HasPairingNegRight X Y 𝕜]
    [Finite I] [Finite J]
    (a : I → Y) (α : I → 𝕜) (b : J → Y) (β : J → 𝕜)
    : ((feasibleSet
          (Sum.elim (fun _ ↦ .eq) fun _ ↦ .le)
          (Sum.elim a b) (Sum.elim α β) : Set X)).IsPolyhedral 𝕜 Y := by
  have hpoly :
      Set.IsPolyhedral (𝕜 := 𝕜) (Y := Y)
        (solutionSet[mixed_linear_constraint_pair_inequalities a α b β] : Set X) := by
    let a' : (I ⊕ I) ⊕ J → Y := Sum.elim (Sum.elim a fun j ↦ -(a j)) b
    let α' : (I ⊕ I) ⊕ J → 𝕜 := Sum.elim (Sum.elim α fun j ↦ -(α j)) β
    change (solutionSet[Set.range fun i : (I ⊕ I) ⊕ J ↦ (a' i, α' i)] : Set X).IsPolyhedral 𝕜 Y
    rw [linearInequalitySolutionSet_range_eq_leFeasible,
      LinearConstraintRelation.leFeasible_eq_feasibleSet_le]
    rw [LinearConstraintRelation.feasibleSet_eq_setOf]
    simpa [LinearConstraintRelation.le_holds_iff] using
      (Set.isPolyhedral_setOf_forall_pairing_le (I := (I ⊕ I) ⊕ J) a' α')
  simpa [mixed_linear_constraint_solution_set_eq_linear_inequality_solution_set
    (a := a) (α := α) (b := b) (β := β)] using hpoly

/-- Equation-only owner companion: a finite family of linear equations cuts out a polyhedral
convex set. -/
theorem feasibleSet_eq_isPolyhedralConvexSet
    {X : Type*} [Neg Y] [HasPairing X Y 𝕜] [HasPairingNegRight X Y 𝕜]
    [Finite I] (b : I → Y) (β : I → 𝕜) :
    (feasibleSet (fun _ ↦ (.eq : LinearConstraintRelation)) b β :
      Set X).IsPolyhedral 𝕜 Y := by
  have hpoly :
      (solutionSet[linear_equation_pair_inequalities b β] : Set X).IsPolyhedral 𝕜 Y := by
    let a' : I ⊕ I → Y := Sum.elim b fun j ↦ -(b j)
    let α' : I ⊕ I → 𝕜 := Sum.elim β fun j ↦ -(β j)
    change (solutionSet[Set.range fun i : I ⊕ I ↦ (a' i, α' i)] : Set X).IsPolyhedral 𝕜 Y
    rw [linearInequalitySolutionSet_range_eq_leFeasible,
      LinearConstraintRelation.leFeasible_eq_feasibleSet_le]
    rw [LinearConstraintRelation.feasibleSet_eq_setOf]
    simpa [LinearConstraintRelation.le_holds_iff] using
      (Set.isPolyhedral_setOf_forall_pairing_le (Y := Y) (I := I ⊕ I) a' α')
  simpa [feasibleSet_eq_eq_pair_of_linear_inequality_solution_set (b := b) (β := β)] using hpoly

end Polyhedrality

end
