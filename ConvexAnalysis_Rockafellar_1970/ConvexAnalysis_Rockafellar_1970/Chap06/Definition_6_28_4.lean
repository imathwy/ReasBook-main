import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

noncomputable section

attribute [local instance] Classical.propDecidable

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

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.28.4 introduces, for a fixed ordinary convex program `P`, the
  perturbed problem obtained by replacing the zero right-hand sides of the inequality and equality
  constraints by prescribed perturbation levels.
- `core/canonical`: in the project, a constrained minimization problem is most naturally encoded
  as the finite objective extended by `+∞` off its feasible set, via
  `Function.toWithTopBotOn`.
- `bridge/view`: because `OrdinaryConvexProgram` already represents the textbook indices
  `1, …, r` and `r + 1, …, m` by the canonical owner `P.ConstraintIndex`, the perturbation vector
  is represented intrinsically as one map `u : P.ConstraintIndex → β`.

Domain-style sampling used here:
- `OrdinaryConvexProgram` and `extendZero` from `Definition_6_28_1`;
- `OrdinaryConvexProgram.relation`, `OrdinaryConvexProgram.constraint`,
  and `LinearConstraintRelation.feasibleSet`;
- `Function.toWithTopBotOn` from `Remark_4_4_5`.

Primitive data vs derived API:
- primitive source data: the base program `P` and one perturbation vector
  `u : P.ConstraintIndex → β`;
- supporting source-facing data: the perturbed feasible set cut out by that perturbation vector;
- main owner: the perturbed problem as the canonical `WithTopBot β`-valued extension of the
  objective to the perturbed feasible set, with the mixed relation and constraint family reused
  from `Definition_6_28_2`.

Layer target: `source-facing` with a canonical extended-value owner. This item defines a genuine
perturbed problem attached to `P`, so it should stay public; the feasible-set description is a
supporting bridge, not a separate wrapper owner.
-/

/-- The feasible set of the perturbed problem attached to `P` with perturbation vector
`u : P.ConstraintIndex → β`. -/
def perturbedFeasibleSet (u : P.ConstraintIndex → β) : Set E :=
  P.constraintSet ∩
    LinearConstraintRelation.feasibleSet
      P.relation
      P.constraint
      u

/-- Definition 6.28.4: the perturbed problem `(P_u)` attached to an ordinary convex program `P`.
The textbook perturbation vector `u = (v₁, …, v_m)` is represented canonically as one map on the
disjoint index owner `P.ConstraintIndex`, where `u (Sum.inl i)` are inequality bounds and
`u (Sum.inr j)` are equality targets. The problem is encoded as the objective extended by `+∞`
off the perturbed feasible set. -/
def perturbedProblem (u : P.ConstraintIndex → β) : E → WithTopBot β :=
  Function.toWithTopBotOn (extendZero P.objective) (P.perturbedFeasibleSet u)

-- Proof sketch: unfold `perturbedFeasibleSet`; membership in the intersections is exactly the
-- ambient constraint together with the mixed relation family attached to `P`.
/-- Intrinsic owner-level membership characterization: `x` belongs to the perturbed feasible set
iff it belongs to the source constraint set and satisfies each mixed linear relation prescribed by
`P.relation` at level `u`. -/
@[simp] theorem mem_perturbedFeasibleSet
    {u : P.ConstraintIndex → β} {x : E} :
    x ∈ P.perturbedFeasibleSet u ↔
      x ∈ P.constraintSet ∧
        (∀ i, (P.relation i).holds (P.constraint i x) (u i)) := by
  constructor
  · rintro ⟨hxC, hx⟩
    refine ⟨hxC, ?_⟩
    exact (LinearConstraintRelation.mem_feasibleSet
      P.relation P.constraint u x).1 hx
  · rintro ⟨hxC, hx⟩
    refine ⟨hxC, ?_⟩
    exact (LinearConstraintRelation.mem_feasibleSet
      P.relation P.constraint u x).2 hx

-- Proof sketch: specialize `mem_perturbedFeasibleSet` to the left (`ι`) and right (`κ`)
-- blocks of `P.ConstraintIndex`, then unfold the intrinsic `Sum.elim` owners
-- `P.relation` and `P.constraint`.
/-- Source-facing split view of `mem_perturbedFeasibleSet`: membership means belonging to the
original constraint set, satisfying each perturbed inequality bound, and satisfying each perturbed
equality target. -/
theorem mem_perturbedFeasibleSet_split
    {u : P.ConstraintIndex → β} {x : E} :
    x ∈ P.perturbedFeasibleSet u ↔
      ∃ hxC : x ∈ P.constraintSet,
        (∀ i, P.inequality i ⟨x, hxC⟩ ≤ u (Sum.inl i)) ∧
        (∀ j, P.equality j ⟨x, hxC⟩ = u (Sum.inr j)) := by
  constructor
  · intro hx
    rcases (P.mem_perturbedFeasibleSet).1 hx with ⟨hxC, hrel⟩
    refine ⟨hxC, ?_, ?_⟩
    · intro i
      have hi : extendZero (P.inequality i) x ≤ u (Sum.inl i) := by
        simpa [OrdinaryConvexProgram.relation, OrdinaryConvexProgram.constraint] using
          hrel (Sum.inl i)
      have hix : extendZero (P.inequality i) x = P.inequality i ⟨x, hxC⟩ := by
        simpa using (extendZero_apply (P.inequality i) ⟨x, hxC⟩)
      exact hix ▸ hi
    · intro j
      have hj : extendZero (P.equality j) x = u (Sum.inr j) := by
        simpa [OrdinaryConvexProgram.relation, OrdinaryConvexProgram.constraint] using
          hrel (Sum.inr j)
      have hjx : extendZero (P.equality j) x = P.equality j ⟨x, hxC⟩ := by
        simpa using (extendZero_apply (P.equality j) ⟨x, hxC⟩)
      exact hjx ▸ hj
  · rintro ⟨hxC, hI, hE⟩
    refine (P.mem_perturbedFeasibleSet).2 ?_
    refine ⟨hxC, ?_⟩
    intro i
    cases i with
    | inl j =>
        have hix : extendZero (P.inequality j) x = P.inequality j ⟨x, hxC⟩ := by
          simpa using (extendZero_apply (P.inequality j) ⟨x, hxC⟩)
        have hi : extendZero (P.inequality j) x ≤ u (Sum.inl j) := by
          simpa [hix] using hI j
        simpa [OrdinaryConvexProgram.relation, OrdinaryConvexProgram.constraint] using hi
    | inr j =>
        have hjx : extendZero (P.equality j) x = P.equality j ⟨x, hxC⟩ := by
          simpa using (extendZero_apply (P.equality j) ⟨x, hxC⟩)
        have hj : extendZero (P.equality j) x = u (Sum.inr j) := by
          simpa [hjx] using hE j
        simpa [OrdinaryConvexProgram.relation, OrdinaryConvexProgram.constraint] using hj

-- Proof sketch: unfold `perturbedProblem` and rewrite `Function.toWithTopBotOn` as its
-- canonical two-branch piecewise definition on `P.perturbedFeasibleSet u`.
/-- The perturbed problem takes the original objective value on the perturbed feasible set and the
value `+∞` outside it. -/
@[simp] theorem perturbedProblem_apply
    (u : P.ConstraintIndex → β) (x : E) :
    P.perturbedProblem u x =
      if x ∈ P.perturbedFeasibleSet u
      then ((extendZero P.objective x : β) : WithTopBot β)
      else ⊤ := by
  by_cases hx : x ∈ P.perturbedFeasibleSet u
  · simp [perturbedProblem, hx]
  · simp [perturbedProblem, hx]

end OrdinaryConvexProgram

namespace OrdinaryConvexProgram

section PureInequality

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {δ : Type w} [AddCommMonoid δ] [PartialOrder δ] [SMul 𝕜 δ]
variable {m : ℕ} {ι : Type}
variable [Fintype ι] [Fact (Fintype.card ι = m)]
variable (P : OrdinaryConvexProgram 𝕜 E (WithTopBot δ) m 0 ι)

/-- Bridge owner for `s = 0`: insert a perturbation vector `u : ι → δ` into the canonical
perturbation owner `P.ConstraintIndex → WithTopBot δ` by using `u` on the inequality block and
the unique function on the empty equality block. -/
abbrev pureInequalityPerturbation (u : ι → δ) : P.ConstraintIndex → WithTopBot δ :=
  Sum.elim (fun i ↦ (u i : WithTopBot δ)) Fin.elim0

/-- Bridge/view: in the pure-inequality case, the perturbed problem may be read as a bifunction on
the source perturbation space `δ^m`, represented intrinsically as `ι → δ`, by inserting the
perturbation vector into the inequality block and using the unique empty equality block. Since the
objective branch is already `WithTopBot δ`-valued, this bridge keeps that codomain and uses the
canonical two-branch
`Set.piecewise` owner rather than adding another `WithTopBot` layer. -/
abbrev pureInequalityPerturbedProblem
    : (ι → δ) → E → WithTopBot δ :=
  fun u ↦
    (P.perturbedFeasibleSet (P.pureInequalityPerturbation u)).piecewise
      (extendZero P.objective)
      ⊤

@[simp] theorem pureInequalityPerturbedProblem_apply (u : ι → δ) (x : E) :
    P.pureInequalityPerturbedProblem u x =
      if x ∈ P.perturbedFeasibleSet (P.pureInequalityPerturbation u) then
        extendZero P.objective x
      else
        ⊤ := by
  by_cases hx : x ∈ P.perturbedFeasibleSet (P.pureInequalityPerturbation u)
  · simp [pureInequalityPerturbedProblem, hx]
  · simp [pureInequalityPerturbedProblem, hx]

end PureInequality

end OrdinaryConvexProgram

end
