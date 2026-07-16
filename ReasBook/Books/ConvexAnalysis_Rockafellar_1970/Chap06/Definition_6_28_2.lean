import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

noncomputable section

section

variable {𝕜 : Type v} {E : Type u} {β : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]

namespace OrdinaryConvexProgram

variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E β r s ι κ)

/-- Canonical split index type for the inequality and equality blocks of `P`. -/
abbrev ConstraintIndex (_ : OrdinaryConvexProgram 𝕜 E β r s ι κ) : Type := ι ⊕ κ

/-- Ambient constraint family attached to `P`, built from the canonical zero-extension of each
source inequality/equality branch. -/
def constraint (P : OrdinaryConvexProgram 𝕜 E β r s ι κ) : P.ConstraintIndex → E → β :=
  Sum.elim P.inequalityAmbient P.equalityAmbient

@[simp] theorem constraint_inl (i : ι) :
    P.constraint (Sum.inl i) = P.inequalityAmbient i := by
  rfl

@[simp] theorem constraint_inr (j : κ) :
    P.constraint (Sum.inr j) = P.equalityAmbient j := by
  rfl

/-- The canonical equality-index subset inside `P.ConstraintIndex`: exactly the right branch of
the split index type. -/
abbrev equalityIndices (P : OrdinaryConvexProgram 𝕜 E β r s ι κ) : Set P.ConstraintIndex :=
  Set.range Sum.inr

@[simp] theorem inl_not_mem_equalityIndices (i : ι) :
    Sum.inl i ∉ P.equalityIndices := by
  simp [OrdinaryConvexProgram.equalityIndices]

@[simp] theorem inr_mem_equalityIndices (j : κ) :
    Sum.inr j ∈ P.equalityIndices := by
  simp [OrdinaryConvexProgram.equalityIndices]

/-- Mixed relation map attached to `P`: equality on the right block and weak inequality on the
left block, expressed through the Chapter 1 canonical owner `LinearConstraintRelation.eqOn`. -/
abbrev relation
    (P : OrdinaryConvexProgram 𝕜 E β r s ι κ) : P.ConstraintIndex → LinearConstraintRelation :=
  LinearConstraintRelation.eqOn P.equalityIndices

@[simp] theorem relation_inl (i : ι) :
    P.relation (Sum.inl i) = .le := by
  simp [OrdinaryConvexProgram.relation, LinearConstraintRelation.eqOn]

@[simp] theorem relation_inr (j : κ) :
    P.relation (Sum.inr j) = .eq := by
  simp [OrdinaryConvexProgram.relation, LinearConstraintRelation.eqOn]

/-- Definition 6.28.2: the feasible solution set of an ordinary convex program is the ambient
constraint set together with the nonpositive inequality constraints and zero equality constraints.
The source index owners are `ι` and `κ` (defaulting to textbook `Fin r` and `Fin s`), and the
constraint family is routed through the Chapter 1 homogeneous mixed-feasible-set owner via the
canonical evaluation pairing on ambient functions. -/
def feasibleSet : Set E :=
  P.constraintSet ∩
    LinearConstraintRelation.homogeneousFeasibleSet β
      P.relation
      P.constraint

-- Proof sketch: unfold `feasibleSet`; membership in the intersection gives the ambient
-- constraint witness `hxC : x ∈ P.constraintSet` plus the mixed homogeneous relation family.
-- Then rewrite each ambient value through the constrained representative `⟨x, hxC⟩`.
/-- Intrinsic owner-level view of feasibility: a point is feasible iff it has a witness
`hxC : x ∈ P.constraintSet` such that every inequality value at `⟨x, hxC⟩` is nonpositive and
every equality value at `⟨x, hxC⟩` is zero. -/
theorem mem_feasibleSet (x : E) :
    x ∈ P.feasibleSet ↔
      ∃ hxC : x ∈ P.constraintSet,
        (∀ i, P.inequality i ⟨x, hxC⟩ ≤ 0) ∧
        (∀ j, P.equality j ⟨x, hxC⟩ = 0) := by
  constructor
  · intro hx
    have hxAmbient :
        x ∈ P.constraintSet ∧
          (∀ i, P.inequalityAmbient i x ≤ 0) ∧
          (∀ j, P.equalityAmbient j x = 0) := by
      simpa [OrdinaryConvexProgram.feasibleSet, OrdinaryConvexProgram.constraint] using hx
    refine ⟨hxAmbient.1, ?_, ?_⟩
    · intro i
      have hix : P.inequalityAmbient i x ≤ 0 := hxAmbient.2.1 i
      have hix_eq : P.inequalityAmbient i x = P.inequality i ⟨x, hxAmbient.1⟩ := by
        simpa using (P.inequalityAmbient_apply i ⟨x, hxAmbient.1⟩)
      exact hix_eq ▸ hix
    · intro j
      have hjx : P.equalityAmbient j x = 0 := hxAmbient.2.2 j
      have hjx_eq : P.equalityAmbient j x = P.equality j ⟨x, hxAmbient.1⟩ := by
        simpa using (P.equalityAmbient_apply j ⟨x, hxAmbient.1⟩)
      exact hjx_eq ▸ hjx
  · rintro ⟨hxC, hxI, hxE⟩
    have hxAmbient :
        x ∈ P.constraintSet ∧
          (∀ i, P.inequalityAmbient i x ≤ 0) ∧
          (∀ j, P.equalityAmbient j x = 0) := by
      refine ⟨hxC, ?_, ?_⟩
      · intro i
        have hix : P.inequalityAmbient i x = P.inequality i ⟨x, hxC⟩ := by
          simpa using (P.inequalityAmbient_apply i ⟨x, hxC⟩)
        exact hix ▸ hxI i
      · intro j
        have hjx : P.equalityAmbient j x = P.equality j ⟨x, hxC⟩ := by
          simpa using (P.equalityAmbient_apply j ⟨x, hxC⟩)
        exact hjx ▸ hxE j
    simpa [OrdinaryConvexProgram.feasibleSet, OrdinaryConvexProgram.constraint] using hxAmbient

-- Proof sketch: this is the ambient bridge form obtained by unfolding `feasibleSet`.
/-- Ambient bridge view of feasibility through the canonical ambient owners
`P.inequalityAmbient` and `P.equalityAmbient`. -/
@[simp] theorem mem_feasibleSet_ambient (x : E) :
    x ∈ P.feasibleSet ↔
      x ∈ P.constraintSet ∧
        (∀ i, P.inequalityAmbient i x ≤ 0) ∧
        (∀ j, P.equalityAmbient j x = 0) := by
  simp [OrdinaryConvexProgram.feasibleSet, OrdinaryConvexProgram.constraint]

/-- Every feasible point of an ordinary convex program belongs to its ambient constraint set. -/
theorem feasible_mem_constraintSet (x : P.feasibleSet) :
    x.1 ∈ P.constraintSet :=
  by
    rcases (P.mem_feasibleSet x.1).1 x.2 with ⟨hxC, -, -⟩
    exact hxC

section Convexity

variable [Module 𝕜 β] [IsOrderedAddMonoid β] [PosSMulMono 𝕜 β]

-- Proof sketch: `P.constraintSet` is convex by `P.constraintSet_convex`. For each inequality
-- index `i`, the sublevel set `{x ∈ P.constraintSet | P.inequalityAmbient i x ≤ 0}` is
-- convex by `ConvexOn.convex_le` applied to `P.inequality_convexOn i`. For each equality index
-- `j`, the zero set is the intersection of a convex sublevel set and a convex superlevel set,
-- using the convex and concave consequences of `P.equality_affOn j`. Intersecting these convex
-- sets yields `P.feasibleSet`.
/-- The feasible solution set of an ordinary convex program is convex. -/
theorem feasibleSet_convex :
    Convex 𝕜 P.feasibleSet := sorry

end Convexity

end OrdinaryConvexProgram

end
