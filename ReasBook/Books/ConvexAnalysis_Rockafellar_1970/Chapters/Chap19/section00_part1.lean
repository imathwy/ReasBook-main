import Mathlib
import Mathlib.Algebra.Order.Ring.Defs

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_19_0_1 (from Chap04) -/
universe u v w

open scoped Rockafellar

section OwnerLayer

variable {𝕜 : Type v} {E : Type u}
variable [Preorder 𝕜]

namespace Set

/-- Owner-primary finite bridge: a set is polyhedral iff it is cut out by a finite family of weak
pairing inequalities, encoded by a finite subset of `(Y × 𝕜)` and the canonical chapter owner
`solutionSet[·]`. -/
theorem isPolyhedral_iff_exists_pairing_le {Y : Type w} [HasPairing E Y 𝕜]
    {s : Set E} :
    s.IsPolyhedral 𝕜 Y ↔
      ∃ S : Finset (Y × 𝕜), s = solutionSet[(S : Set (Y × 𝕜))] := by
  constructor
  · rintro ⟨S, rfl⟩
    refine ⟨S, ?_⟩
    ext x
    simp [linearInequalitySolutionSet_eq_iInter_closedHalfSpaceLE]
  · rintro ⟨S, rfl⟩
    refine ⟨S, ?_⟩
    ext x
    simp [linearInequalitySolutionSet_eq_iInter_closedHalfSpaceLE]

/-- Set-builder companion of `Set.isPolyhedral_iff_exists_pairing_le`. -/
theorem isPolyhedral_iff_exists_pairing_le_setOf {Y : Type w} [HasPairing E Y 𝕜]
    {s : Set E} :
    s.IsPolyhedral 𝕜 Y ↔
      ∃ S : Finset (Y × 𝕜), s = {x : E | ∀ y ∈ S, ⟪x, y.1⟫ₚ ≤ y.2} := by
  constructor
  · intro hs
    rcases (isPolyhedral_iff_exists_pairing_le (Y := Y) (s := s)).1 hs with ⟨S, hsS⟩
    refine ⟨S, ?_⟩
    rw [hsS]
    ext x
    simp
  · rintro ⟨S, hsS⟩
    refine (isPolyhedral_iff_exists_pairing_le (Y := Y) (s := s)).2 ?_
    refine ⟨S, ?_⟩
    rw [hsS]
    ext x
    simp

/-- Finite-index owner corollary: any finite weak pairing system defines a polyhedral set. -/
theorem isPolyhedral_setOf_forall_pairing_le {Y : Type w} [HasPairing E Y 𝕜]
    {I : Type*} [Finite I] (b : I → Y) (β : I → 𝕜) :
    ({x : E | ∀ i, ⟪x, b i⟫ₚ ≤ β i}).IsPolyhedral 𝕜 Y := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  refine (isPolyhedral_iff_exists_pairing_le_setOf
    (Y := Y) (s := ({x : E | ∀ i, ⟪x, b i⟫ₚ ≤ β i} : Set E))).2 ?_
  refine ⟨Finset.univ.image (fun i : I ↦ (b i, β i)), ?_⟩
  ext x
  constructor
  · intro hx
    change ∀ y ∈ Finset.univ.image (fun i : I ↦ (b i, β i)), ⟪x, y.1⟫ₚ ≤ y.2
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, -, rfl⟩
    exact hx i
  · intro hx
    change ∀ i : I, ⟪x, b i⟫ₚ ≤ β i
    intro i
    exact hx (b i, β i) (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)

section LinearSpecialization

variable [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]

/-- Linear-functional owner-primary finite bridge:
`Y := E →ₗ[𝕜] 𝕜` in `Set.isPolyhedral_iff_exists_pairing_le_setOf`. -/
theorem isPolyhedral_iff_exists_linear_le {s : Set E} :
    s.IsPolyhedral 𝕜 (E →ₗ[𝕜] 𝕜) ↔
      ∃ S : Finset ((E →ₗ[𝕜] 𝕜) × 𝕜),
        s = {x : E | ∀ y ∈ S, y.1 x ≤ y.2} := by
  simpa using
    (isPolyhedral_iff_exists_pairing_le_setOf
      (Y := E →ₗ[𝕜] 𝕜) (s := s))

/-- Finite-index linear-functional specialization of
`Set.isPolyhedral_setOf_forall_pairing_le` (`Y := E →ₗ[𝕜] 𝕜`). -/
theorem isPolyhedral_setOf_forall_linear_le {I : Type*} [Finite I] (ℓ : I → E →ₗ[𝕜] 𝕜)
    (β : I → 𝕜) :
    ({x : E | ∀ i, ℓ i x ≤ β i}).IsPolyhedral 𝕜 (E →ₗ[𝕜] 𝕜) := by
  simpa using
    (isPolyhedral_setOf_forall_pairing_le (Y := E →ₗ[𝕜] 𝕜) (I := I) ℓ β)

end LinearSpecialization

end Set

end OwnerLayer

/-! ### Text_19_0_2 (from Chap04) -/
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

/-! ### Text_19_0_3 (from Chap04) -/
universe u v

section

open scoped Rockafellar

variable {𝕜 : Type u} {E : Type v} {Y : Type (max u v)}

/-!
Source/core/bridge triage:

- `source-facing`: Text 19.0.3 characterizes which polyhedral convex subsets are cones, namely
  those admitting a finite defining family of closed half-spaces through the origin. In this
  project the source-facing cone owner `Set.IsCone 𝕜` does not itself force the origin to belong
  to the set, so the translated statement must keep the origin condition explicit.
- `core/canonical`: the owner abstractions already present in the project are
  `Set.IsPolyhedral` for polyhedral convex sets, `Set.IsConvexCone 𝕜` for the convex-conic
  structure, `Set.IsCone 𝕜` for the positive-ray closure component, the chapter weak-system owner
  `linearInequalitySolutionSet`, and the half-space owner `closedHalfSpaceLE`.
- `bridge/view`: the textbook finite family of homogeneous closed half-spaces
  `closedHalfSpaceLE y 0` is exactly the finite homogeneous weak-system owner surface obtained
  from a finite family `S : Finset (Y × 𝕜)` with `y.2 = 0` for each `y ∈ S`.
- Primitive data vs derived API: the primitive source-facing data are the finite family of
  pairing normals defining the homogeneous inequalities; the chapter owner
  `linearInequalitySolutionSet` is the canonical set attached to that data, while the explicit
  finite-half-space intersection is a thin companion view.
- Domain-style sampling used here: `Set.IsPolyhedral`, `linearInequalitySolutionSet`,
  `mem_linearInequalitySolutionSet_iff`, `closedHalfSpaceLE`, and
  `mem_closedHalfSpaceLE_iff`.
- Layer target: `core/canonical` for the main weak-system presentation, with the explicit
  half-space statement kept as a thin `bridge/view` companion.
-/

section ConeCharacterization

section PrimitiveDirections

variable [CommSemiring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]
  [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]

/-- Primitive owner-level direction: if a set is presented by finitely many homogeneous weak
linear inequalities, then it is a cone (in the chapter sense) and contains the origin. This does
not require any polyhedrality assumption, since the finite homogeneous weak-system owner already
contains the needed primitive data. -/
theorem Set.isCone_zero_mem_of_exists_finset_homogeneous_linearInequalitySolutionSet
    {C : Set E}
    (hC :
      ∃ S : Finset (Y × 𝕜),
        (∀ y ∈ S, y.2 = (0 : 𝕜)) ∧
          C = solutionSet[(S : Set (Y × 𝕜))]) :
    Set.IsCone 𝕜 C ∧ (0 : E) ∈ C := by
  rcases hC with ⟨S, hS_hom, hS⟩
  refine ⟨?_, ?_⟩
  · intro c hc x hx
    rw [hS, mem_linearInequalitySolutionSet_iff] at hx ⊢
    intro y hyS
    have hyx : (⟪x, y.1⟫ₚ : 𝕜) ≤ y.2 := hx y hyS
    have hy0 : y.2 = (0 : 𝕜) := hS_hom y hyS
    have hc0 : (0 : 𝕜) ≤ c := (show (0 : 𝕜) < c from hc).le
    have hyx0 : (⟪x, y.1⟫ₚ : 𝕜) ≤ 0 := by simpa [hy0] using hyx
    have hy_mul : c * (⟪x, y.1⟫ₚ : 𝕜) ≤ c * 0 :=
      mul_le_mul_of_nonneg_left (a := c) hyx0 hc0
    have hcy0 : (⟪c • x, y.1⟫ₚ : 𝕜) ≤ 0 := by
      calc
        (⟪c • x, y.1⟫ₚ : 𝕜) = c * ⟪x, y.1⟫ₚ := by simp
        _ ≤ c * 0 := hy_mul
        _ = 0 := by simp
    simpa [hy0] using hcy0
  · rw [hS, mem_linearInequalitySolutionSet_iff]
    intro y hyS
    simp [hS_hom y hyS]

/-- Primitive owner-level half-space bridge direction: if a set is a finite intersection of
homogeneous closed half-spaces, then it is a cone and contains the origin. -/
theorem Set.isCone_zero_mem_of_exists_finset_homogeneous_closedHalfSpaceLE
    {C : Set E}
    (hC : ∃ S : Finset Y, C = ⋂ y ∈ S, closedHalfSpaceLE y (0 : 𝕜)) :
    Set.IsCone 𝕜 C ∧ (0 : E) ∈ C := by
  classical
  rcases hC with ⟨S, hS⟩
  have hHom :
      ∃ T : Finset (Y × 𝕜),
        (∀ y ∈ T, y.2 = (0 : 𝕜)) ∧
          C = solutionSet[(T : Set (Y × 𝕜))] := by
    refine ⟨S.image fun y : Y ↦ (y, (0 : 𝕜)), ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
      simp
    · rw [hS]
      ext x
      simp [mem_closedHalfSpaceLE_iff]
  exact Set.isCone_zero_mem_of_exists_finset_homogeneous_linearInequalitySolutionSet hHom

/-- Primitive owner-level canonical form: a finite homogeneous weak-system presentation already
gives a convex cone (in the chapter owner `Set.IsConvexCone 𝕜`) together with origin membership.
-/
theorem Set.isConvexCone_zero_mem_of_exists_finset_homogeneous_linearInequalitySolutionSet
    {C : Set E}
    (hC :
      ∃ S : Finset (Y × 𝕜),
        (∀ y ∈ S, y.2 = (0 : 𝕜)) ∧
          C = solutionSet[(S : Set (Y × 𝕜))]) :
    Set.IsConvexCone 𝕜 C ∧ (0 : E) ∈ C := by
  rcases hC with ⟨S, hS_hom, hS⟩
  have hConeZero :
      Set.IsCone 𝕜 C ∧ (0 : E) ∈ C :=
    Set.isCone_zero_mem_of_exists_finset_homogeneous_linearInequalitySolutionSet
      (C := C) ⟨S, hS_hom, hS⟩
  have hPoly : C.IsPolyhedral 𝕜 Y := by
    refine ⟨S, ?_⟩
    simpa [hS] using
      (linearInequalitySolutionSet_eq_iInter_closedHalfSpaceLE
        (E := E) (Y := Y) (R := 𝕜) (SStar := (S : Set (Y × 𝕜))))
  exact ⟨⟨hConeZero.1, hPoly.convex⟩, hConeZero.2⟩

/-- Primitive owner-level canonical half-space bridge: a finite homogeneous closed-half-space
presentation already gives a convex cone and origin membership. -/
theorem Set.isConvexCone_zero_mem_of_exists_finset_homogeneous_closedHalfSpaceLE
    {C : Set E}
    (hC : ∃ S : Finset Y, C = ⋂ y ∈ S, closedHalfSpaceLE y (0 : 𝕜)) :
    Set.IsConvexCone 𝕜 C ∧ (0 : E) ∈ C := by
  classical
  rcases hC with ⟨S, hS⟩
  have hHom :
      ∃ T : Finset (Y × 𝕜),
        (∀ y ∈ T, y.2 = (0 : 𝕜)) ∧
          C = solutionSet[(T : Set (Y × 𝕜))] := by
    refine ⟨S.image fun y : Y ↦ (y, (0 : 𝕜)), ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
      simp
    · rw [hS]
      ext x
      simp [mem_closedHalfSpaceLE_iff]
  exact Set.isConvexCone_zero_mem_of_exists_finset_homogeneous_linearInequalitySolutionSet hHom

end PrimitiveDirections

section PolyhedralCharacterization

variable [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]
  [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]

/-- Text 19.0.3, in canonical ambient form: a polyhedral convex set `C` is a cone with vertex at
the origin if and only if it is the solution set of a finite homogeneous weak linear system,
expressed through the chapter owner `linearInequalitySolutionSet`. The explicit hypothesis
`0 ∈ C` is the source-faithful translation of “with vertex at the origin”, since this project's
`Set.IsCone 𝕜` records only positive-scalar closure. -/
-- Proof sketch: start from a finite owner-half-space presentation of `C` coming from
-- `Set.IsPolyhedral`. If `C` is a cone and contains the origin, each defining level can be
-- replaced by `0`, yielding a finite homogeneous family encoded by
-- `solutionSet[S]` together with the owner-level homogeneity condition
-- `∀ y ∈ S, y.2 = 0`.
-- Conversely,
-- each such owner half-space is homogeneous and contains `0`, and finite intersections preserve
-- both properties.
theorem Set.IsPolyhedral.isCone_zero_mem_iff_exists_finset_homogeneous_linearInequalitySolutionSet
    {C : Set E} (hC : C.IsPolyhedral 𝕜 Y) :
    Set.IsCone 𝕜 C ∧ (0 : E) ∈ C ↔
      ∃ S : Finset (Y × 𝕜),
        (∀ y ∈ S, y.2 = (0 : 𝕜)) ∧
          C = solutionSet[(S : Set (Y × 𝕜))] := by
  classical
  constructor
  · rintro ⟨hCone, h0⟩
    rcases hC with ⟨S, hS⟩
    let T : Finset (Y × 𝕜) := S.image fun p : Y × 𝕜 ↦ (p.1, (0 : 𝕜))
    refine ⟨T, ?_, ?_⟩
    · intro y hyT
      rcases Finset.mem_image.mp hyT with ⟨p, hpS, rfl⟩
      simp
    ext x
    constructor
    · intro hx
      rw [mem_linearInequalitySolutionSet_iff]
      intro y hyT
      rcases Finset.mem_image.mp hyT with ⟨p, hpS, rfl⟩
      have hbdd : BddAbove ((fun z : E ↦ (⟪z, p.1⟫ₚ : 𝕜)) '' C) := by
        refine ⟨p.2, ?_⟩
        rintro _ ⟨z, hzC, rfl⟩
        have hzS : ∀ q ∈ S, ⟪z, q.1⟫ₚ ≤ q.2 := by
          simpa [hS, mem_closedHalfSpaceLE_iff] using hzC
        exact hzS p hpS
      have hy_nonpos : (⟪x, p.1⟫ₚ : 𝕜) ≤ 0 :=
        Set.IsCone.pairing_nonpos_of_bddAbove hCone hbdd x hx
      simpa using hy_nonpos
    · intro hx
      rw [hS]
      have h0S : ∀ p ∈ S, ⟪(0 : E), p.1⟫ₚ ≤ p.2 := by
        simpa [hS, mem_closedHalfSpaceLE_iff] using h0
      rw [mem_linearInequalitySolutionSet_iff] at hx
      have hxS : ∀ p ∈ S, ⟪x, p.1⟫ₚ ≤ p.2 := by
        intro p hp
        have hpT : (p.1, (0 : 𝕜)) ∈ T :=
          Finset.mem_image.mpr ⟨p, hp, by simp⟩
        have hpx : ⟪x, p.1⟫ₚ ≤ (0 : 𝕜) := by
          simpa using hx (p.1, (0 : 𝕜)) hpT
        have hp0 : (0 : 𝕜) ≤ p.2 := by
          simpa using h0S p hp
        exact le_trans hpx hp0
      simpa [mem_closedHalfSpaceLE_iff] using hxS
  · intro hHom
    exact Set.isCone_zero_mem_of_exists_finset_homogeneous_linearInequalitySolutionSet hHom

/-- Canonical convex-cone owner form of Text 19.0.3: for a polyhedral set, the source-facing
"cone with vertex at the origin" condition is equivalent to `Set.IsConvexCone 𝕜 C` together with
`0 ∈ C`, and this holds exactly when `C` is given by finitely many homogeneous weak inequalities.
-/
theorem Set.IsPolyhedral.isConvexCone_zero_mem_iff_exists_finset_homogeneous_linearInequalitySolutionSet
    {C : Set E} (hC : C.IsPolyhedral 𝕜 Y) :
    Set.IsConvexCone 𝕜 C ∧ (0 : E) ∈ C ↔
      ∃ S : Finset (Y × 𝕜),
        (∀ y ∈ S, y.2 = (0 : 𝕜)) ∧
          C = solutionSet[(S : Set (Y × 𝕜))] := by
  constructor
  · rintro ⟨hConvCone, h0⟩
    exact
      (Set.IsPolyhedral.isCone_zero_mem_iff_exists_finset_homogeneous_linearInequalitySolutionSet
        hC).mp ⟨hConvCone.isCone, h0⟩
  · intro hHom
    exact
      Set.isConvexCone_zero_mem_of_exists_finset_homogeneous_linearInequalitySolutionSet
        hHom

/-- Companion source-facing form: a polyhedral convex set is a cone with vertex at the origin if
and only if it is the intersection of finitely many homogeneous closed half-spaces
`closedHalfSpaceLE y 0`. -/
theorem Set.IsPolyhedral.isCone_zero_mem_iff_exists_finset_homogeneous_closedHalfSpaceLE
    {C : Set E} (hC : C.IsPolyhedral 𝕜 Y) :
    Set.IsCone 𝕜 C ∧ (0 : E) ∈ C ↔
      ∃ S : Finset Y, C = ⋂ y ∈ S, closedHalfSpaceLE y (0 : 𝕜) := by
  classical
  constructor
  · intro hConeZero
    rcases
        (Set.IsPolyhedral.isCone_zero_mem_iff_exists_finset_homogeneous_linearInequalitySolutionSet
          hC).mp hConeZero with ⟨S, hS_hom, hS⟩
    let T : Finset Y := S.image Prod.fst
    refine ⟨T, ?_⟩
    ext x
    constructor
    · intro hx
      rw [mem_iInter]
      intro y
      rw [mem_iInter]
      intro hyT
      rw [mem_closedHalfSpaceLE_iff]
      have hxS : x ∈ solutionSet[(S : Set (Y × 𝕜))] := by simpa [hS] using hx
      rw [mem_linearInequalitySolutionSet_iff] at hxS
      rcases Finset.mem_image.mp hyT with ⟨p, hpS, hp_eq⟩
      have hxp : (⟪x, p.1⟫ₚ : 𝕜) ≤ p.2 := hxS p hpS
      simpa [hS_hom p hpS, hp_eq] using hxp
    · intro hx
      rw [hS, mem_linearInequalitySolutionSet_iff]
      have hxT : ∀ y ∈ T, (⟪x, y⟫ₚ : 𝕜) ≤ 0 := by
        simpa [mem_closedHalfSpaceLE_iff]
          using hx
      intro p hpS
      have hpT : p.1 ∈ T := Finset.mem_image.mpr ⟨p, hpS, rfl⟩
      have hxp : (⟪x, p.1⟫ₚ : 𝕜) ≤ 0 := hxT p.1 hpT
      simpa [hS_hom p hpS] using hxp
  · rintro ⟨S, hS⟩
    exact Set.isCone_zero_mem_of_exists_finset_homogeneous_closedHalfSpaceLE ⟨S, hS⟩

/-- Canonical convex-cone owner companion: for a polyhedral set, the condition
`Set.IsConvexCone 𝕜 C ∧ 0 ∈ C` is equivalent to a finite homogeneous closed-half-space
presentation. -/
theorem Set.IsPolyhedral.isConvexCone_zero_mem_iff_exists_finset_homogeneous_closedHalfSpaceLE
    {C : Set E} (hC : C.IsPolyhedral 𝕜 Y) :
    Set.IsConvexCone 𝕜 C ∧ (0 : E) ∈ C ↔
      ∃ S : Finset Y, C = ⋂ y ∈ S, closedHalfSpaceLE y (0 : 𝕜) := by
  constructor
  · rintro ⟨hConvCone, h0⟩
    exact
      (Set.IsPolyhedral.isCone_zero_mem_iff_exists_finset_homogeneous_closedHalfSpaceLE
        hC).mp ⟨hConvCone.isCone, h0⟩
  · intro hHom
    exact Set.isConvexCone_zero_mem_of_exists_finset_homogeneous_closedHalfSpaceLE hHom

end PolyhedralCharacterization

end ConeCharacterization

end

/-! ### Text_19_0_4 (from Chap04) -/
universe uR uE

section

variable {R : Type uR} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable {E : Type uE} [AddCommMonoid E] [Module R E]

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Text 19.0.4 introduces finitely generated convex sets as mixed convex hulls of
  finitely many points and finitely many directions.
- `core/canonical`: the owner abstractions are the chapter declaration `mixedConvexHull` and the
  finiteness predicate `Set.Finite` on the generating point set and the direction-ray set.
- `bridge/view`: concrete finite-family encodings such as `Finset` or indexed vectors are derived
  presentations of this owner-level notion.

Domain-style sampling used here:
- the chapter owner `mixedConvexHull`;
- the chapter bridge owner `rayOfDirections`, written with the notation `ray`;
- the chapter convexity theorem `convex_mixedConvexHull`;
- `Set.Finite` as the canonical owner for finite generating families.

Primitive data vs derived API:
- primitive source-facing data: the finite generating point set and finite generating direction-ray
  set;
- derived API: convexity of every finitely generated set and concrete finite-family presentations.
- ambient refinement: the owner predicate only uses the chapter owners `mixedConvexHull`,
  `rayOfDirections`, and `Set.Finite`, so it lives naturally over the same scalar-generic ambient
  assumptions rather than being frozen to `ℝ`.
-/

namespace Set

variable (R)

/-- Text 19.0.4: a subset of an `R`-module is finitely generated when it is the mixed convex hull
of finitely many generating points and finitely many generating directions. -/
def IsFinitelyGeneratedConvex (C : Set E) : Prop :=
  ∃ points : Set E, ∃ directions : Set (Module.Ray R E),
    points.Finite ∧ directions.Finite ∧ C = mconv[R](points | ray directions)

end Set

namespace Set.IsFinitelyGeneratedConvex

/-- Constructor at the primitive owner layer: a mixed convex hull generated by finite point and
finite direction-ray sets is finitely generated convex. -/
theorem mk {points : Set E} {directions : Set (Module.Ray R E)}
    (hpoints : points.Finite) (hdirections : directions.Finite) :
    (mconv[R](points | ray directions)).IsFinitelyGeneratedConvex R :=
  ⟨points, directions, hpoints, hdirections, rfl⟩

/-- Canonical constructor for the finite-point specialization: the convex hull of a finite point
set is finitely generated convex. -/
theorem mk_convexHull {points : Set E} (hpoints : points.Finite) :
    (conv[R] points).IsFinitelyGeneratedConvex R := by
  have hfg :
      (mconv[R](points | ray (∅ : Set (Module.Ray R E)))).IsFinitelyGeneratedConvex R :=
    mk (R := R) hpoints Set.finite_empty
  have hmixed :
      mconv[R](points | ray (∅ : Set (Module.Ray R E))) = conv[R] points := by
    refine mixedConvexHull_eq_convexHull_of_directions_subset_zero (R := R) ?_
    simp [ray_empty]
  exact hmixed.symm ▸ hfg

/-- Intrinsic finite-index constructor: finite point and direction-ray indexed families generate a
finitely generated convex set via their mixed convex hull. -/
theorem mk_finite {ιp : Type*} [Finite ιp] (points : ιp → E)
    {ιd : Type*} [Finite ιd] (directions : ιd → Module.Ray R E) :
    (mconv[R](Set.range points | ray (Set.range directions))).IsFinitelyGeneratedConvex R := by
  classical
  letI : Fintype ιp := Fintype.ofFinite ιp
  letI : Fintype ιd := Fintype.ofFinite ιd
  exact mk (R := R) (points := Set.range points) (directions := Set.range directions)
    (Set.finite_range points) (Set.finite_range directions)

set_option linter.unusedFintypeInType false in
/-- Operational finite-index constructor: `Fintype`-indexed point and direction-ray families
generate a finitely generated convex set via their mixed convex hull. -/
theorem mk_fintype {ιp : Type*} [Fintype ιp] (points : ιp → E)
    {ιd : Type*} [Fintype ιd] (directions : ιd → Module.Ray R E) :
    (mconv[R](Set.range points | ray (Set.range directions))).IsFinitelyGeneratedConvex R := by
  exact mk_finite (R := R) points directions

/-- Operational constructor: finite point and direction-ray families (`Finset`) generate a
finitely generated convex set via their mixed convex hull. -/
theorem mk_finset (points : Finset E) (directions : Finset (Module.Ray R E)) :
    (mconv[R]((points : Set E) |
      ray (directions : Set (Module.Ray R E)))).IsFinitelyGeneratedConvex R :=
  ⟨(points : Set E), (directions : Set (Module.Ray R E)),
    points.finite_toSet, directions.finite_toSet, rfl⟩

/-- Intrinsic finite-index bridge: finite generation is equivalent to a mixed-hull presentation by
honestly finite indexed point and direction-ray families. -/
theorem iff_exists_finite {C : Set E} :
    C.IsFinitelyGeneratedConvex R ↔
      ∃ (ιp : Type uE) (_ : Finite ιp) (points : ιp → E)
        (ιd : Type uE) (_ : Finite ιd) (directions : ιd → Module.Ray R E),
        C = mconv[R](Set.range points | ray (Set.range directions)) := by
  constructor
  · rintro ⟨points, directions, hpoints, hdirections, rfl⟩
    classical
    letI : Fintype ↥points := hpoints.fintype
    letI : Fintype ↥directions := hdirections.fintype
    refine ⟨↥points, Finite.of_fintype ↥points, Subtype.val,
      ↥directions, Finite.of_fintype ↥directions, Subtype.val, ?_⟩
    simp
  · rintro ⟨ιp, hιp, points, ιd, hιd, directions, rfl⟩
    classical
    letI : Finite ιp := hιp
    letI : Finite ιd := hιd
    letI : Fintype ιp := Fintype.ofFinite ιp
    letI : Fintype ιd := Fintype.ofFinite ιd
    exact ⟨Set.range points, Set.range directions,
      Set.finite_range points, Set.finite_range directions, rfl⟩

/-- Intrinsic finite-index bridge, forward direction. -/
theorem exists_finite {C : Set E} (hC : C.IsFinitelyGeneratedConvex R) :
    ∃ (ιp : Type uE) (_ : Finite ιp) (points : ιp → E)
      (ιd : Type uE) (_ : Finite ιd) (directions : ιd → Module.Ray R E),
      C = mconv[R](Set.range points | ray (Set.range directions)) :=
  (iff_exists_finite (R := R)).mp hC

/-- Intrinsic finite-index bridge, converse direction. -/
theorem of_exists_finite {C : Set E}
    (hC :
      ∃ (ιp : Type uE) (_ : Finite ιp) (points : ιp → E)
        (ιd : Type uE) (_ : Finite ιd) (directions : ιd → Module.Ray R E),
        C = mconv[R](Set.range points | ray (Set.range directions))) :
    C.IsFinitelyGeneratedConvex R :=
  (iff_exists_finite (R := R)).mpr hC

/-- Intrinsic finite-index bridge: finite generation is equivalent to a mixed-hull presentation by
`Fintype`-indexed point and direction-ray families. -/
theorem iff_exists_fintype {C : Set E} :
    C.IsFinitelyGeneratedConvex R ↔
      ∃ (ιp : Type uE) (_ : Fintype ιp) (points : ιp → E)
        (ιd : Type uE) (_ : Fintype ιd) (directions : ιd → Module.Ray R E),
        C = mconv[R](Set.range points | ray (Set.range directions)) := by
  constructor
  · intro hC
    rcases (iff_exists_finite (R := R) (C := C)).mp hC with
      ⟨ιp, hιp, points, ιd, hιd, directions, hEq⟩
    classical
    letI : Finite ιp := hιp
    letI : Finite ιd := hιd
    letI : Fintype ιp := Fintype.ofFinite ιp
    letI : Fintype ιd := Fintype.ofFinite ιd
    exact ⟨ιp, inferInstance, points, ιd, inferInstance, directions, hEq⟩
  · rintro ⟨ιp, _, points, ιd, _, directions, hEq⟩
    exact (iff_exists_finite (R := R) (C := C)).mpr
      ⟨ιp, inferInstance, points, ιd, inferInstance, directions, hEq⟩

/-- Intrinsic finite-index bridge, forward direction. -/
theorem exists_fintype {C : Set E} (hC : C.IsFinitelyGeneratedConvex R) :
    ∃ (ιp : Type uE) (_ : Fintype ιp) (points : ιp → E)
      (ιd : Type uE) (_ : Fintype ιd) (directions : ιd → Module.Ray R E),
      C = mconv[R](Set.range points | ray (Set.range directions)) :=
  (iff_exists_fintype (R := R)).mp hC

/-- Intrinsic finite-index bridge, converse direction. -/
theorem of_exists_fintype {C : Set E}
    (hC :
      ∃ (ιp : Type uE) (_ : Fintype ιp) (points : ιp → E)
        (ιd : Type uE) (_ : Fintype ιd) (directions : ιd → Module.Ray R E),
        C = mconv[R](Set.range points | ray (Set.range directions))) :
    C.IsFinitelyGeneratedConvex R :=
  (iff_exists_fintype (R := R)).mpr hC

/-- Finite-generation owner predicate in `Set` form is equivalent to a finite-family (`Finset`)
presentation of points and direction rays. -/
theorem iff_exists_finset {C : Set E} :
    C.IsFinitelyGeneratedConvex R ↔
      ∃ points : Finset E, ∃ directions : Finset (Module.Ray R E),
        C = mconv[R]((points : Set E) | ray (directions : Set (Module.Ray R E))) := by
  classical
  constructor
  · rintro ⟨points, directions, hpoints, hdirections, rfl⟩
    exact ⟨hpoints.toFinset, hdirections.toFinset, by
      simp [hpoints.coe_toFinset, hdirections.coe_toFinset]⟩
  · rintro ⟨points, directions, hC⟩
    exact ⟨(points : Set E), (directions : Set (Module.Ray R E)),
      points.finite_toSet, directions.finite_toSet, hC⟩

/-- Operational finite-family bridge, forward direction. -/
theorem exists_finset {C : Set E} (hC : C.IsFinitelyGeneratedConvex R) :
    ∃ points : Finset E, ∃ directions : Finset (Module.Ray R E),
      C = mconv[R]((points : Set E) | ray (directions : Set (Module.Ray R E))) :=
  (iff_exists_finset (R := R)).mp hC

/-- Operational finite-family bridge, converse direction. -/
theorem of_exists_finset {C : Set E}
    (hC :
      ∃ points : Finset E, ∃ directions : Finset (Module.Ray R E),
        C = mconv[R]((points : Set E) | ray (directions : Set (Module.Ray R E)))) :
    C.IsFinitelyGeneratedConvex R :=
  (iff_exists_finset (R := R)).mpr hC

-- Proof sketch: write `C` as `mconv[R](points | ray directions)`; the chapter owner
-- theorem `convex_mixedConvexHull` gives convexity of that mixed hull, and the defining equality
-- transfers it to `C`.
/-- Every finitely generated set is convex. -/
theorem convex {C : Set E} (hC : C.IsFinitelyGeneratedConvex R) :
    Convex R C := by
  rcases hC with ⟨points, directions, _, _, rfl⟩
  exact convex_mixedConvexHull R points (ray directions)

end Set.IsFinitelyGeneratedConvex

namespace Set.IsPolytope

/-- Every polytope is a finitely generated convex set. -/
theorem isFinitelyGeneratedConvex {C : Set E} (hC : C.IsPolytope R) :
    C.IsFinitelyGeneratedConvex R := by
  rcases hC with ⟨points, hpoints_finite, rfl⟩
  exact Set.IsFinitelyGeneratedConvex.mk_convexHull hpoints_finite

end Set.IsPolytope

end

/-! ### Text_19_0_5 (from Chap04) -/
open scoped BigOperators Rockafellar

section

universe u v

variable {R : Type v} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-!
Source/core/bridge triage:

- `source-facing`: Text 19.0.5 says that a finite family generates a convex cone exactly when the
  cone is the set of all nonnegative finite linear combinations of those generators.
- `core/canonical`: the raw owner is `PointedCone.hull R`; the source-facing owner notation is
  `cone[R]`.
- `bridge/view`: the textbook finite-sum display is the pointwise membership description of
  `(cone[R] s : Set E)` over a finite generator subtype `s`, with `Finset` as an operational
  specialization.

Domain-style sampling used here:
- `PointedCone.hull`;
- `PointedCone.mem_hull_set`;
- the coercion from `PointedCone R E` to its carrier set;
- `Finsupp` as the primitive finite-combination owner layer.

Primitive data vs derived API:
- primitive owner data: the generator owner set `s : Set E` and ambient finitely supported
  coefficients `weights : E →₀ R` with `weights.support ⊆ s`;
- derived API: subtype-indexed coefficient views, finite nonnegative-sum membership/set-equality
  formulas, and the `Finset` specialization.

Ambient minimization:
- the theorem uses only the ordered-semiring/module structure already required by
  `PointedCone.mem_hull_set`, so the file stays at that owner layer instead of hard-coding
  `EuclideanSpace ℝ (Fin n)`.

Layer target: `bridge/view`.
-/

namespace PointedCone

/-- Primitive bridge form: membership in a generated cone, stated on ambient finitely supported
coefficients with support constrained to the generator set. -/
theorem mem_cone_set_iff_exists_nonneg_finsupp
    (s : Set E) (x : E) :
    (x ∈ cone[R] s) ↔
      ∃ weights : E →₀ R,
        ↑weights.support ⊆ s ∧
        (∀ a, 0 ≤ weights a) ∧
        weights.sum (fun a r ↦ r • a) = x := by
  simpa using (PointedCone.mem_hull_set (R := R) (s := s) (x := x))

/-- Primitive set-owner form: a generated cone is exactly the set of all nonnegative finitely
supported linear combinations whose support is contained in the generator set. -/
theorem cone_set_eq_setOf_exists_nonneg_finsupp
    (s : Set E) :
    (cone[R] s : Set E) =
      {x : E | ∃ weights : E →₀ R,
          ↑weights.support ⊆ s ∧
          (∀ a, 0 ≤ weights a) ∧
          weights.sum (fun a r ↦ r • a) = x} := by
  ext x
  simpa [Set.mem_setOf_eq] using
    (mem_cone_set_iff_exists_nonneg_finsupp (R := R) (s := s) (x := x))

/-- Intrinsic generator-subtype bridge, derived from
`mem_cone_set_iff_exists_nonneg_finsupp`. -/
theorem mem_cone_set_iff_exists_nonneg_finsupp_subtype
    (s : Set E) (x : E) :
    (x ∈ cone[R] s) ↔
      ∃ weights : s →₀ R,
        (∀ a, 0 ≤ weights a) ∧
        weights.sum (fun a r ↦ r • (a : E)) = x := by
  classical
  constructor
  · intro hx
    rcases (mem_cone_set_iff_exists_nonneg_finsupp (R := R) (s := s) (x := x)).1 hx with
      ⟨weights, hsupport, hnonneg, hsum⟩
    refine ⟨weights.subtypeDomain (· ∈ s), ?_, ?_⟩
    · intro a
      exact hnonneg a
    · exact
        (Finsupp.sum_subtypeDomain_index
          (p := (· ∈ s))
          (v := weights)
          (h := fun a r ↦ r • a)
          hsupport).trans hsum
  · rintro ⟨weights, hnonneg, hsum⟩
    refine (mem_cone_set_iff_exists_nonneg_finsupp (R := R) (s := s) (x := x)).2 ?_
    refine ⟨weights.extendDomain, ?_, ?_, ?_⟩
    · exact Finsupp.support_extendDomain_subset (f := weights)
    · intro a
      by_cases ha : a ∈ s
      · simpa [Finsupp.extendDomain, ha] using hnonneg ⟨a, ha⟩
      · simp [Finsupp.extendDomain, ha]
    · calc
        weights.extendDomain.sum (fun a r ↦ r • a) =
            weights.sum (fun a r ↦ r • (a : E)) := by
          simpa [Finsupp.extendDomain_eq_embDomain_subtype] using
            (Finsupp.sum_embDomain
              (f := Function.Embedding.subtype (· ∈ s))
              (v := weights)
              (g := fun a r ↦ r • a))
        _ = x := hsum

/-- Primitive set-owner form using intrinsic generator subtypes. -/
theorem cone_set_eq_setOf_exists_nonneg_finsupp_subtype
    (s : Set E) :
    (cone[R] s : Set E) =
      {x : E | ∃ weights : s →₀ R,
          (∀ a, 0 ≤ weights a) ∧
          weights.sum (fun a r ↦ r • (a : E)) = x} := by
  ext x
  simpa [Set.mem_setOf_eq] using
    (mem_cone_set_iff_exists_nonneg_finsupp_subtype (R := R) (s := s) (x := x))

/-- Finset specialization of `mem_cone_set_iff_exists_nonneg_finsupp`. -/
theorem mem_cone_finset_iff_exists_nonneg_finsupp
    (generators : Finset E) (x : E) :
    (x ∈ cone[R] (generators : Set E)) ↔
      ∃ weights : generators →₀ R,
        (∀ a, 0 ≤ weights a) ∧
        weights.sum (fun a r ↦ r • (a : E)) = x := by
  simpa using
    (mem_cone_set_iff_exists_nonneg_finsupp_subtype
      (R := R)
      (s := (generators : Set E))
      (x := x))

/-- Intrinsic finite-index bridge: membership in a generated cone is equivalent to an ordinary
finite nonnegative sum over the generator subtype. -/
theorem mem_cone_set_iff_exists_nonneg_sum
    (s : Set E) [Fintype s] (x : E) :
    (x ∈ cone[R] s) ↔
      ∃ weights : s → R,
        (∀ a, 0 ≤ weights a) ∧
        (∑ a, weights a • (a : E)) = x := by
  classical
  constructor
  · intro hx
    rcases (mem_cone_set_iff_exists_nonneg_finsupp_subtype (R := R) (s := s) (x := x)).1 hx with
      ⟨weights, hnonneg, hsum⟩
    refine ⟨Finsupp.equivFunOnFinite weights, ?_, ?_⟩
    · intro a
      simpa [Finsupp.equivFunOnFinite_apply] using hnonneg a
    · calc
        (∑ a, (Finsupp.equivFunOnFinite weights) a • (a : E)) =
            weights.sum (fun a r ↦ r • (a : E)) := by
          symm
          simpa [Finsupp.equivFunOnFinite_apply] using
            (Finsupp.sum_fintype
              weights
              (fun a r ↦ r • (a : E))
              (fun a ↦ zero_smul R (a : E)))
        _ = x := hsum
  · rintro ⟨weights, hnonneg, hsum⟩
    let coeffs : s →₀ R := Finsupp.equivFunOnFinite.symm weights
    refine (mem_cone_set_iff_exists_nonneg_finsupp_subtype (R := R) (s := s) (x := x)).2 ?_
    refine ⟨coeffs, ?_, ?_⟩
    · intro a
      simpa [coeffs] using hnonneg a
    · calc
        coeffs.sum (fun a r ↦ r • (a : E)) =
            (∑ a, (Finsupp.equivFunOnFinite coeffs) a • (a : E)) := by
          simpa [Finsupp.equivFunOnFinite_apply] using
            (Finsupp.sum_fintype
              coeffs
              (fun a r ↦ r • (a : E))
              (fun a ↦ zero_smul R (a : E)))
        _ = ∑ a, weights a • (a : E) := by
          simp [coeffs]
        _ = x := hsum

/-- A point lies in the cone generated by a finite family exactly when it is a nonnegative finite
linear combination of those generators. -/
theorem mem_cone_finset_iff_exists_nonneg_sum
    (generators : Finset E) (x : E) :
    (x ∈ cone[R] (generators : Set E)) ↔
      ∃ weights : generators → R,
        (∀ a, 0 ≤ weights a) ∧
        (∑ a, weights a • (a : E)) = x := by
  simpa using
    (mem_cone_set_iff_exists_nonneg_sum
      (R := R)
      (s := (generators : Set E))
      x)

/-- Set-owner form of Text 19.0.5: when the generator subtype is finite, the generated cone is
exactly the set of all nonnegative finite linear combinations of those generators. -/
theorem cone_set_eq_setOf_exists_nonneg_sum
    (s : Set E) [Fintype s] :
    (cone[R] s : Set E) =
      {x : E | ∃ weights : s → R,
          (∀ a, 0 ≤ weights a) ∧
          (∑ a, weights a • (a : E)) = x} := by
  ext x
  simpa [Set.mem_setOf_eq] using
    (mem_cone_set_iff_exists_nonneg_sum (R := R) (s := s) x)

/-- Text 19.0.5: the cone generated by a finite family is exactly the set of all nonnegative
finite linear combinations of those generators. -/
theorem cone_finset_eq_setOf_exists_nonneg_sum
    (generators : Finset E) :
    (cone[R] (generators : Set E) : Set E) =
      {x : E | ∃ weights : generators → R,
          (∀ a, 0 ≤ weights a) ∧
          (∑ a, weights a • (a : E)) = x} := by
  simpa using
    (cone_set_eq_setOf_exists_nonneg_sum
      (R := R)
      (s := (generators : Set E)))

end PointedCone

end

/-! ### Text_19_0_6 (from Chap04) -/
section

open Bornology Set
open scoped Rockafellar

variable {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [Bornology E] [AddCommMonoid E] [Module 𝕜 E]

/-!
Source/core/bridge triage:
- `source-facing`: Text 19.0.6 singles out the unbounded finitely generated case and interprets
  the finite direction generators as vertices at infinity.
- `core/canonical`: the chapter owner remains `Set.IsFinitelyGeneratedConvex`, built from
  `mixedConvexHull`, `ray`, and `Set.Finite`.
- `bridge/view`: the right refinement is a thin theorem saying that an unbounded finitely
  generated convex set admits a mixed-hull presentation by finitely many points together with a
  nonempty finite family of direction rays.

Domain-style sampling used here:
- `Set.IsFinitelyGeneratedConvex`;
- `mixedConvexHull`;
- `mem_ray_iff`;
- `mixedConvexHull_eq_convexHull_of_directions_subset_zero`;
- `Set.Finite.isCompact_convexHull`.

Primitive data vs derived API:
- primitive owner data: finite generating points and finite generating direction rays carried by
  `Set.IsFinitelyGeneratedConvex`;
- primitive ambient bridge input: boundedness of the specific point-generator convex hull;
- derived bridge data here: when the set is unbounded, the direction family cannot be empty, since
  the empty-direction case collapses to a bounded finite convex hull.

Layer target: `bridge/view`.

Ambient refinement:
- core owner theorem below is stated on the weakest bornological module layer plus the primitive
  bridge assumption that the relevant point convex hull is bounded, and a thin derived wrapper then
  recovers the finite-family boundedness bridge input;
- the source-facing topological specialization is then recovered as a thin bridge theorem using
  `Set.Finite.isCompact_convexHull` and `IsCompact.isBounded`.
-/

namespace Set.IsFinitelyGeneratedConvex

/-- Primitive mixed-hull layer: if the point-generator convex hull is bounded, then an unbounded
mixed convex hull must have a nonempty direction-ray family. -/
theorem directions_nonempty_of_not_isBounded_mixedConvexHull_of_isBounded_convexHull
    {points : Set E} {directions : Set (Module.Ray 𝕜 E)}
    (hbounded_convexHull_points : IsBounded (conv[𝕜] points))
    (hunbounded : ¬ IsBounded (mconv[𝕜](points | ray directions))) :
    directions.Nonempty := by
  by_contra hdirections_empty
  have hray_zero : ray directions ⊆ ({0} : Set E) := by
    intro y hy
    rcases (mem_ray_iff directions y).1 hy with rfl | ⟨_, hy_direction⟩
    · simp
    · exact (hdirections_empty ⟨_, hy_direction⟩).elim
  have hbounded_mixed : IsBounded (mconv[𝕜](points | ray directions)) := by
    rw [mixedConvexHull_eq_convexHull_of_directions_subset_zero 𝕜 hray_zero]
    exact hbounded_convexHull_points
  exact hunbounded hbounded_mixed

/-- Derived finite-generator bridge: if all finite point-generator convex hulls are bounded, then
an unbounded finite-point mixed convex hull must have a nonempty direction-ray family. -/
theorem directions_nonempty_of_not_isBounded_mixedConvexHull_of_bounded_convexHull_finite
    {points : Set E} {directions : Set (Module.Ray 𝕜 E)}
    (hpoints_finite : points.Finite)
    (hbounded_convexHull_finite : ∀ {s : Set E}, s.Finite → IsBounded (conv[𝕜] s))
    (hunbounded : ¬ IsBounded (mconv[𝕜](points | ray directions))) :
    directions.Nonempty :=
  directions_nonempty_of_not_isBounded_mixedConvexHull_of_isBounded_convexHull
    (hbounded_convexHull_finite hpoints_finite) hunbounded

/-- Text 19.0.6, core owner form: assuming finite convex hulls are bounded, an unbounded finitely
generated convex set admits a finite mixed presentation by points together with a nonempty finite
family of direction rays (the source's vertices at infinity). -/
theorem exists_points_directions_of_not_isBounded_of_bounded_convexHull_finite {C : Set E}
    (hC : C.IsFinitelyGeneratedConvex 𝕜)
    (hbounded_convexHull_finite : ∀ {s : Set E}, s.Finite → IsBounded (conv[𝕜] s))
    (hC_unbounded : ¬ IsBounded C) :
    ∃ points : Set E, ∃ directions : Set (Module.Ray 𝕜 E),
      points.Finite ∧ directions.Finite ∧ directions.Nonempty ∧
        C = mconv[𝕜](points | ray directions) := by
  rcases hC with ⟨points, directions, hpoints_finite, hdirections_finite, hC_eq⟩
  refine ⟨points, directions, hpoints_finite, hdirections_finite, ?_, hC_eq⟩
  refine directions_nonempty_of_not_isBounded_mixedConvexHull_of_bounded_convexHull_finite
    hpoints_finite hbounded_convexHull_finite ?_
  simpa [hC_eq] using hC_unbounded

end Set.IsFinitelyGeneratedConvex

end

section

open Bornology Set
open scoped Rockafellar

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderClosedTopology 𝕜] [CompactIccSpace 𝕜] [ContinuousAdd 𝕜]
variable {E : Type*} [TopologicalSpace E] [Bornology E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

namespace Set.IsFinitelyGeneratedConvex

/-- Topological-boundedness bridge form of Text 19.0.6: if compact sets are bounded in the ambient
bornology, then an unbounded finite-point mixed convex hull has a nonempty direction family. -/
theorem directions_nonempty_of_not_isBounded_mixedConvexHull_of_isCompact_isBounded
    {points : Set E} {directions : Set (Module.Ray 𝕜 E)}
    (hpoints_finite : points.Finite)
    (hcompact_isBounded : ∀ {s : Set E}, IsCompact s → IsBounded s)
    (hunbounded : ¬ IsBounded (mconv[𝕜](points | ray directions))) :
    directions.Nonempty := by
  refine directions_nonempty_of_not_isBounded_mixedConvexHull_of_isBounded_convexHull ?_ hunbounded
  exact hcompact_isBounded (hpoints_finite.isCompact_convexHull 𝕜)

/-- Topological-boundedness bridge form of Text 19.0.6: if compact sets are bounded in the ambient
bornology, an unbounded finitely generated convex set admits a finite mixed presentation by points
together with a nonempty finite family of direction rays. -/
theorem exists_points_directions_of_not_isBounded_of_isCompact_isBounded {C : Set E}
    (hC : C.IsFinitelyGeneratedConvex 𝕜)
    (hcompact_isBounded : ∀ {s : Set E}, IsCompact s → IsBounded s)
    (hC_unbounded : ¬ IsBounded C) :
    ∃ points : Set E, ∃ directions : Set (Module.Ray 𝕜 E),
      points.Finite ∧ directions.Finite ∧ directions.Nonempty ∧
        C = mconv[𝕜](points | ray directions) := by
  exact
    exists_points_directions_of_not_isBounded_of_bounded_convexHull_finite
      hC (fun hs ↦ hcompact_isBounded (hs.isCompact_convexHull 𝕜)) hC_unbounded

end Set.IsFinitelyGeneratedConvex

end

section

open Bornology Set
open scoped Rockafellar

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderClosedTopology 𝕜] [CompactIccSpace 𝕜] [ContinuousAdd 𝕜]
variable {E : Type*} [PseudoMetricSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

namespace Set.IsFinitelyGeneratedConvex

/-- Source-facing bridge form of Text 19.0.6: in the standard metric-topological ambient where
finite convex hulls are compact (hence bounded), an unbounded finite-point mixed convex hull has a
nonempty direction family. -/
theorem directions_nonempty_of_not_isBounded_mixedConvexHull
    {points : Set E} {directions : Set (Module.Ray 𝕜 E)}
    (hpoints_finite : points.Finite)
    (hunbounded : ¬ IsBounded (mconv[𝕜](points | ray directions))) :
    directions.Nonempty :=
  directions_nonempty_of_not_isBounded_mixedConvexHull_of_isCompact_isBounded
    hpoints_finite (fun hs ↦ hs.isBounded) hunbounded

/-- Text 19.0.6, source-facing bridge form: in the standard metric-topological ambient, an
unbounded finitely generated convex set admits a finite mixed presentation by points together with
a nonempty finite family of direction rays, interpreted as vertices at infinity. -/
theorem exists_points_directions_of_not_isBounded {C : Set E}
    (hC : C.IsFinitelyGeneratedConvex 𝕜) (hC_unbounded : ¬ IsBounded C) :
    ∃ points : Set E, ∃ directions : Set (Module.Ray 𝕜 E),
      points.Finite ∧ directions.Finite ∧ directions.Nonempty ∧
        C = mconv[𝕜](points | ray directions) :=
  exists_points_directions_of_not_isBounded_of_isCompact_isBounded
    hC (fun hs ↦ hs.isBounded) hC_unbounded

end Set.IsFinitelyGeneratedConvex

end

/-! ### Text_19_0_7 (from Chap04) -/
section

variable {𝕜 : Type*} [Semifield 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [PosMulReflectLT 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: Text 19.0.7 says that every face of a polyhedral convex set is again
  polyhedral.
- `core/canonical`: the owner abstractions already present in the chapter are
  `Set.IsFinitelyGeneratedConvex` for the primitive mixed point-direction presentation,
  `Set.IsPolyhedral` for its finite-dimensional bridge, and `Set.IsFace` for faces.
- `bridge/view`: the source polyhedral statement is recovered from the core owner theorem
  `Set.IsFace.isFinitelyGeneratedConvex` by the existing Chapter 19 bridge
  `Set.IsFinitelyGeneratedConvex.isPolyhedral`.

Domain-style sampling used here:
- `Set.IsPolyhedral`, together with `Set.IsPolyhedral.convex` and
  `Set.IsPolyhedral.isFinitelyGeneratedConvex`;
- `Set.IsFace`;
- `Set.IsFace.eq_mixedConvexHull_inter_recessionCone_of_eq_mixedConvexHull`;
- `Set.IsFinitelyGeneratedConvex`.

Primitive data vs derived API:
- primitive input: the ambient set `C`, the face candidate `F`, the face hypothesis, and the
  finitely generated mixed point-direction presentation of `C`;
- derived bridge API: the polyhedrality conclusion itself.

Layer target:
- `core/canonical` for the owner theorem `Set.IsFace.isFinitelyGeneratedConvex`;
- `source-facing` for the polyhedral statement, expressed as a thin bridge.

Ambient refinement:
- the core face-of-finite-generation theorem only uses `Set.IsFace`,
  `Set.IsFace.eq_mixedConvexHull_inter_recessionCone_of_eq_mixedConvexHull`, the ray owner `ray`,
  and the recession-cone
  owner `0⁺[𝕜]`, so it lives on the weaker ordered-semifield module layer;
- the source polyhedral bridge then uses
  `Set.IsPolyhedral.isFinitelyGeneratedConvex` and
  `Set.IsFinitelyGeneratedConvex.isPolyhedral`,
  which already live on arbitrary finite-dimensional topological modules over `𝕜`,
  so any concrete Euclidean coordinate model is presentation only and should not remain in the
  public statement.
-/

namespace Set.IsFace

private theorem sameRay_exists_pos_right {x y : E} (h : SameRay 𝕜 x y)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ r : 𝕜, 0 < r ∧ x = r • y := by
  rcases h.exists_pos hx hy with ⟨r₁, r₂, hr₁, hr₂, hxy⟩
  refine ⟨r₁⁻¹ * r₂, mul_pos (inv_pos.mpr hr₁) hr₂, ?_⟩
  calc
    x = r₁⁻¹ • (r₁ • x) := by rw [inv_smul_smul₀ hr₁.ne']
    _ = r₁⁻¹ • (r₂ • y) := by rw [hxy]
    _ = (r₁⁻¹ * r₂) • y := by rw [mul_smul]

/-- A face of a finitely generated convex set is finitely generated. -/
-- Proof sketch: use Theorem 19.1 to rewrite `C` as a finitely generated mixed convex hull with
-- a witness `C.IsFinitelyGeneratedConvex`, then unpack its defining finite point and direction
-- data.
-- `Set.IsFace.eq_mixedConvexHull_inter_recessionCone_of_eq_mixedConvexHull` identifies `F` with
-- the mixed convex hull generated by the point generators lying in `F` and the direction vectors
-- that lie in the recession cone of `F`. Filter the finite direction-ray family by the canonical
-- ray predicate `r.someVector ∈ 0⁺[𝕜] F`, which is equivalent because recession cones are closed
-- under positive scaling.
theorem isFinitelyGeneratedConvex {C F : Set E} (hF : F.IsFace 𝕜 C)
    (hC : C.IsFinitelyGeneratedConvex 𝕜) : F.IsFinitelyGeneratedConvex 𝕜 := by
  rcases hC with
    ⟨points, directions, hpoints_finite, hdirections_finite, hC_eq⟩
  have hF_eq :
      F = mixedConvexHull 𝕜 (points ∩ F) (ray directions ∩ 0⁺[𝕜] F) := by
    exact hF.eq_mixedConvexHull_inter_recessionCone_of_eq_mixedConvexHull hC_eq
  let faceDirections : Set (Module.Ray 𝕜 E) :=
    {r | r ∈ directions ∧ r.someVector ∈ 0⁺[𝕜] F}
  have hfaceDirections_finite : faceDirections.Finite :=
    hdirections_finite.subset fun _ hr ↦ hr.1
  have hray_eq : ray faceDirections = ray directions ∩ 0⁺[𝕜] F := by
    ext v
    constructor
    · intro hv
      rcases (mem_ray_iff faceDirections v).1 hv with rfl | ⟨hv0, hvr⟩
      · exact
          ⟨(mem_ray_iff directions 0).2 (Or.inl rfl), zero_mem_recessionCone F⟩
      · rcases hvr with ⟨hdir, hrvF⟩
        refine ⟨(mem_ray_iff directions v).2 (Or.inr ⟨hv0, hdir⟩), ?_⟩
        have hsameRay : SameRay 𝕜 v (rayOfNeZero 𝕜 v hv0).someVector := by
          exact
            (ray_eq_iff hv0 (rayOfNeZero 𝕜 v hv0).someVector_ne_zero).1 <|
              (rayOfNeZero 𝕜 v hv0).someVector_ray.symm
        rcases sameRay_exists_pos_right hsameRay hv0 (rayOfNeZero 𝕜 v hv0).someVector_ne_zero with
          ⟨t, ht, htv⟩
        rw [htv]
        exact (recessionCone_isCone F).smul_mem ht hrvF
    · rintro ⟨hvdir, hvF⟩
      rcases (mem_ray_iff directions v).1 hvdir with rfl | ⟨hv0, hvr⟩
      · exact (mem_ray_iff faceDirections 0).2 (Or.inl rfl)
      · have hsameRay : SameRay 𝕜 (rayOfNeZero 𝕜 v hv0).someVector v := by
          exact
            (ray_eq_iff (rayOfNeZero 𝕜 v hv0).someVector_ne_zero hv0).1 <|
              (rayOfNeZero 𝕜 v hv0).someVector_ray
        rcases sameRay_exists_pos_right hsameRay (rayOfNeZero 𝕜 v hv0).someVector_ne_zero hv0 with
          ⟨t, ht, htv⟩
        exact
          (mem_ray_iff faceDirections v).2 <|
            Or.inr ⟨hv0, ⟨hvr, by rw [htv]; exact (recessionCone_isCone F).smul_mem ht hvF⟩⟩
  have hF_fg : F.IsFinitelyGeneratedConvex 𝕜 := by
    refine ⟨points ∩ F, faceDirections, ?_, hfaceDirections_finite, ?_⟩
    · exact hpoints_finite.subset (inter_subset_left : points ∩ F ⊆ points)
    · calc
        F = mixedConvexHull 𝕜 (points ∩ F) (ray directions ∩ 0⁺[𝕜] F) := hF_eq
        _ = mixedConvexHull 𝕜 (points ∩ F) (ray faceDirections) := by rw [← hray_eq]
  exact hF_fg

end Set.IsFace

end

section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]

open scoped Rockafellar

namespace Set.IsFace

/-- Core bridge at the finite-generation owner layer: in the Chapter 19 ambient assumptions,
every face of a finitely generated convex set is polyhedral. -/
theorem isPolyhedral_of_isFinitelyGeneratedConvex {C F : Set E} (hF : F.IsFace 𝕜 C)
    (hC : C.IsFinitelyGeneratedConvex 𝕜) : F.IsPolyhedral 𝕜 :=
  (hF.isFinitelyGeneratedConvex hC).isPolyhedral

/-- Text 19.0.7 on the canonical owner surface: every face of a polyhedral convex set is
polyhedral. -/
theorem isPolyhedral {C F : Set E} (hF : F.IsFace 𝕜 C)
    (hC : C.IsPolyhedral 𝕜) : F.IsPolyhedral 𝕜 :=
  hF.isPolyhedral_of_isFinitelyGeneratedConvex hC.isFinitelyGeneratedConvex

/-- Text 19.0.7, source-facing bridge form in face-family notation: if `F ∈ 𝓕[𝕜](C)` and `C` is
polyhedral, then `F` is polyhedral. -/
theorem isPolyhedral_of_mem_faces {C F : Set E} (hF : F ∈ 𝓕[𝕜](C))
    (hC : C.IsPolyhedral 𝕜) : F.IsPolyhedral 𝕜 :=
  (mem_faces_iff.mp hF).isPolyhedral hC

end Set.IsFace

end

/-! ### Text_19_0_8 (from Chap04) -/
noncomputable section

section

open scoped Rockafellar

section CoreOwner

namespace Function

variable {𝕜 : Type*} [Semiring 𝕜] [Preorder 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
variable {α : Type*} [AddCommMonoid α] [Module 𝕜 α] [Preorder α]

/-- Text 19.0.8 owner predicate at the primitive codomain/scalar layer:
polyhedrality of the intrinsic epigraph `epi f` for `f : E → WithTopBot α`. -/
abbrev HasPolyhedralEpigraph (f : E → WithTopBot α) : Prop :=
  (epi f).IsPolyhedral 𝕜

namespace HasPolyhedralEpigraph

/-- Owner-side theorem: `HasPolyhedralEpigraph` is exactly polyhedrality of `epi f`. -/
theorem isPolyhedral {f : E → WithTopBot α} (hf : f.HasPolyhedralEpigraph) :
    (epi f).IsPolyhedral 𝕜 :=
  hf

end HasPolyhedralEpigraph

end Function

end CoreOwner

section ConvexityLayer

variable {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜]
variable [IsOrderedAddMonoid 𝕜] [PosSMulMono 𝕜 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
variable {α : Type*} [AddCommMonoid α] [Module 𝕜 α] [PartialOrder α]

namespace Function.HasPolyhedralEpigraph

/-- A function with polyhedral epigraph is convex. -/
theorem isConvex {f : E → WithTopBot α} (hf : f.HasPolyhedralEpigraph) :
    f.IsConvex 𝕜 := by
  exact hf.isPolyhedral.convex

end Function.HasPolyhedralEpigraph

end ConvexityLayer

section IndicatorLayer

variable {𝕜 : Type*} [Ring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]

namespace Set

/-- Set-owner bridge: the product with the nonnegative vertical ray is polyhedral
iff the base set is polyhedral. -/
private theorem isPolyhedral_prod_Ici_zero_iff (C : Set E) :
    (C ×ˢ Set.Ici (0 : 𝕜)).IsPolyhedral 𝕜 ↔ C.IsPolyhedral 𝕜 := by
  constructor
  · intro hprod
    classical
    rcases hprod with ⟨S, hS⟩
    let inlMap : E →ₗ[𝕜] E × 𝕜 := LinearMap.inl 𝕜 E 𝕜
    let projectedParams : Finset ((E →ₗ[𝕜] 𝕜) × 𝕜) :=
      S.image fun y ↦ (y.1.comp inlMap, y.2)
    refine ⟨projectedParams, ?_⟩
    ext x
    constructor
    · intro hx
      have hxS : ∀ y ∈ S, (x, (0 : 𝕜)) ∈ closedHalfSpaceLE y.1 y.2 := by
        have hxProd : (x, (0 : 𝕜)) ∈ C ×ˢ Set.Ici (0 : 𝕜) := by
          exact ⟨hx, by simp⟩
        rw [hS] at hxProd
        simpa [Set.mem_iInter] using hxProd
      simpa [Set.mem_iInter, inlMap, LinearMap.inl_apply, LinearMap.comp_apply] using
        (show ∀ z ∈ projectedParams, x ∈ closedHalfSpaceLE z.1 z.2 from by
          intro z hz
          rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
          simpa [inlMap, LinearMap.inl_apply, LinearMap.comp_apply] using hxS y hy)
    · intro hx
      have hxProjected : ∀ z ∈ projectedParams, x ∈ closedHalfSpaceLE z.1 z.2 := by
        simpa [Set.mem_iInter] using hx
      have hxProd : (x, (0 : 𝕜)) ∈ C ×ˢ Set.Ici (0 : 𝕜) := by
        rw [hS]
        simpa [Set.mem_iInter, inlMap, LinearMap.inl_apply, LinearMap.comp_apply] using
          (show ∀ y ∈ S, (x, (0 : 𝕜)) ∈ closedHalfSpaceLE y.1 y.2 from by
            intro y hy
            have hyProjected : (y.1.comp inlMap, y.2) ∈ projectedParams :=
              Finset.mem_image.mpr ⟨y, hy, rfl⟩
            simpa [inlMap, LinearMap.inl_apply, LinearMap.comp_apply] using
              (hxProjected _ hyProjected))
      exact hxProd.1
  · intro hC
    classical
    rcases hC with ⟨S, hS⟩
    let fstMap : E × 𝕜 →ₗ[𝕜] E := LinearMap.fst 𝕜 E 𝕜
    let sndMap : E × 𝕜 →ₗ[𝕜] 𝕜 := LinearMap.snd 𝕜 E 𝕜
    let liftedParams : Finset ((E × 𝕜 →ₗ[𝕜] 𝕜) × 𝕜) :=
      S.image fun y ↦ (y.1.comp fstMap, y.2)
    let rayParam : (E × 𝕜 →ₗ[𝕜] 𝕜) × 𝕜 := (-sndMap, 0)
    refine ⟨insert rayParam liftedParams, ?_⟩
    ext p
    rw [hS]
    constructor
    · rintro ⟨hpC, hpμ⟩
      have hpS : ∀ y ∈ S, p.1 ∈ closedHalfSpaceLE y.1 y.2 := by
        simpa [Set.mem_iInter] using hpC
      simpa [Set.mem_iInter, fstMap, sndMap, rayParam, liftedParams,
        LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.comp_apply] using
        (show ∀ z ∈ insert rayParam liftedParams, p ∈ closedHalfSpaceLE z.1 z.2 from by
          intro z hz
          rcases Finset.mem_insert.mp hz with hzRay | hzLift
          · subst hzRay
            have hp2 : (0 : 𝕜) ≤ p.2 := hpμ
            have hneg : -p.2 ≤ (0 : 𝕜) := neg_nonpos.mpr hp2
            change (-LinearMap.snd 𝕜 E 𝕜 p) ≤ (0 : 𝕜)
            simpa [LinearMap.snd_apply] using hneg
          · rcases Finset.mem_image.mp hzLift with ⟨y, hy, rfl⟩
            simpa [fstMap, LinearMap.fst_apply, LinearMap.comp_apply] using hpS y hy)
    · intro hp
      have hpAll : ∀ z ∈ insert rayParam liftedParams, p ∈ closedHalfSpaceLE z.1 z.2 := by
        simpa [Set.mem_iInter] using hp
      have hpμ : p.2 ∈ Set.Ici (0 : 𝕜) := by
        have hray : p ∈ closedHalfSpaceLE rayParam.1 rayParam.2 :=
          hpAll rayParam (Finset.mem_insert_self rayParam liftedParams)
        have hneg : -p.2 ≤ (0 : 𝕜) := by
          change (-LinearMap.snd 𝕜 E 𝕜 p) ≤ (0 : 𝕜) at hray
          simpa [LinearMap.snd_apply] using hray
        exact neg_nonpos.mp hneg
      have hpC : p.1 ∈ ⋂ y ∈ S, closedHalfSpaceLE y.1 y.2 := by
        simpa [Set.mem_iInter] using
          (show ∀ y ∈ S, p.1 ∈ closedHalfSpaceLE y.1 y.2 from by
            intro y hy
            have hyLift : (y.1.comp fstMap, y.2) ∈ liftedParams :=
              Finset.mem_image.mpr ⟨y, hy, rfl⟩
            have hpy : p ∈ closedHalfSpaceLE (y.1.comp fstMap) y.2 :=
              hpAll _ (Finset.mem_insert.mpr <| Or.inr hyLift)
            simpa [fstMap, LinearMap.fst_apply, LinearMap.comp_apply] using hpy)
      exact ⟨hpC, hpμ⟩

end Set

namespace Function.HasPolyhedralEpigraph

/-- Canonical owner bridge for indicators: `δ[𝕜](· | C)` has polyhedral epigraph exactly
when `C` is polyhedral. -/
theorem indicator_iff_isPolyhedral (C : Set E) :
    (δ[𝕜](· | C)).HasPolyhedralEpigraph ↔ C.IsPolyhedral 𝕜 := by
  rw [Function.HasPolyhedralEpigraph, epi_indicator_eq_prod]
  exact Set.isPolyhedral_prod_Ici_zero_iff C

end Function.HasPolyhedralEpigraph

namespace Set

/-- Set-owner bridge for indicators: `C` is polyhedral iff the indicator of `C` has polyhedral
epigraph. -/
theorem isPolyhedral_iff_hasPolyhedralEpigraph_indicator (C : Set E) :
    C.IsPolyhedral 𝕜 ↔ (δ[𝕜](· | C)).HasPolyhedralEpigraph := by
  simpa using
    (Function.HasPolyhedralEpigraph.indicator_iff_isPolyhedral (C := C)).symm

end Set

namespace Set.IsPolyhedral

/-- Owner projection from a polyhedral base set to the indicator epigraph owner. -/
theorem hasPolyhedralEpigraph_indicator {C : Set E} (hC : C.IsPolyhedral 𝕜) :
    (δ[𝕜](· | C)).HasPolyhedralEpigraph :=
  (Set.isPolyhedral_iff_hasPolyhedralEpigraph_indicator C).1 hC

end Set.IsPolyhedral

namespace Function.HasPolyhedralEpigraph

/-- Owner projection from indicator-epigraph polyhedrality back to base-set polyhedrality. -/
theorem isPolyhedral_indicator {C : Set E}
    (hδ : (δ[𝕜](· | C)).HasPolyhedralEpigraph) :
    C.IsPolyhedral 𝕜 :=
  (Set.isPolyhedral_iff_hasPolyhedralEpigraph_indicator C).2 hδ

end Function.HasPolyhedralEpigraph

end IndicatorLayer

end
