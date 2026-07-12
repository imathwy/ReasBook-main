import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_21_0_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {E : Type*}

open ConvexInequalityRelation

/-!
Source/core/bridge triage:

- `source-facing`: Text 21.0.2 rewrites the solution set of a system of convex inequalities given
  by weak indices `I₁` and strict indices `I₂` as the intersection of the displayed weak and
  strict level sets.
- `core/canonical`: the owner abstraction is the direct feasible-set owner
  `convexInequalitySolutionSet relation f μ` from `Text 21.0.1`, together with the single-
  constraint owner `ConvexInequalityRelation.solutionSet`.
- `bridge/view`: this item identifies that owner solution set, specialized to the sum-indexed
  relation family `Sum.elim (fun _ ↦ .le) (fun _ ↦ .lt)`, with the textbook family-wise
  intersection of the corresponding weak and strict owner constraint sets.

Domain-style sampling used here:
- `convexInequalitySolutionSet` from `Text_21_0_1`;
- `ConvexInequalityRelation.solutionSet` from `Text_21_0_1`;
- `Function.IsConvex.convex_le` and `Function.IsConvex.convex_lt` from `Chap01.Theorem_4_6`;
- the earlier intersection-style solution-set owner `linearInequalitySolutionSet` from
  `Definition_17_2_4`.

Primitive data vs derived API:
- primitive data: the weak family `fLe`, `μLe` and the strict family `fLt`, `μLt`;
- derived API: the canonical mixed feasible set on `I₁ ⊕ I₂` and the equality between that owner
  set and the split intersection of the single-constraint owner sets.

Layer target: `bridge/view`.
-/

section MixedSystem

variable {I1 : Type u} {I2 : Type v} {β : Type w} [LE β] [LT β]
variable (relation1 : I1 → ConvexInequalityRelation) (f1 : I1 → E → β) (μ1 : I1 → β)
variable (relation2 : I2 → ConvexInequalityRelation) (f2 : I2 → E → β) (μ2 : I2 → β)

/-- Owner-level split lemma: a mixed feasible-set owner indexed by `I₁ ⊕ I₂` factors as the
intersection of the two subsystem owners for the two relation/function/bound families. -/
theorem convexInequalitySolutionSet_sum_elim_eq_inter :
    convexInequalitySolutionSet (Sum.elim relation1 relation2)
      (Sum.elim f1 f2) (Sum.elim μ1 μ2) =
      convexInequalitySolutionSet relation1 f1 μ1 ∩
        convexInequalitySolutionSet relation2 f2 μ2 := by
  ext x
  simp [convexInequalitySolutionSet]

variable (fLe : I1 → E → β) (μLe : I1 → β)
variable (fLt : I2 → E → β) (μLt : I2 → β)

local notation "weakRelation" => (fun _ : I1 ↦ ConvexInequalityRelation.le)
local notation "strictRelation" => (fun _ : I2 ↦ ConvexInequalityRelation.lt)
local notation "mixedRelation" => Sum.elim weakRelation strictRelation

-- Proof sketch: unfold `convexInequalitySolutionSet` for the sum-indexed relation family and split
-- the intersection with `Set.iInter_sum`. Each branch is exactly the intersection of the
-- corresponding owner single-constraint solution sets.
/-- Text 21.0.2: the feasible set of a mixed system of convex inequalities is the intersection of
the displayed weak and strict single-constraint feasible sets. -/
theorem convexInequalitySolutionSet_sum_eq_inter_solutionSets :
    convexInequalitySolutionSet mixedRelation (Sum.elim fLe fLt) (Sum.elim μLe μLt) =
      (⋂ i, (.le : ConvexInequalityRelation).solutionSet (fLe i) (μLe i)) ∩
        ⋂ i, (.lt : ConvexInequalityRelation).solutionSet (fLt i) (μLt i) := by
  simpa [convexInequalitySolutionSet] using
    convexInequalitySolutionSet_sum_elim_eq_inter
      (relation1 := weakRelation) (f1 := fLe) (μ1 := μLe)
      (relation2 := strictRelation) (f2 := fLt) (μ2 := μLt)

/-- Companion owner-level factorization of Text 21.0.2: the mixed feasible-set owner on `I₁ ⊕ I₂`
splits as the intersection of the weak and strict subsystem owners. -/
theorem convexInequalitySolutionSet_sum_eq_inter :
    convexInequalitySolutionSet mixedRelation (Sum.elim fLe fLt) (Sum.elim μLe μLt) =
      convexInequalitySolutionSet weakRelation fLe μLe ∩
        convexInequalitySolutionSet strictRelation fLt μLt := by
  simpa using
    convexInequalitySolutionSet_sum_elim_eq_inter
      (relation1 := weakRelation) (f1 := fLe) (μ1 := μLe)
      (relation2 := strictRelation) (f2 := fLt) (μ2 := μLt)

end MixedSystem

end
