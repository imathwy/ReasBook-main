import Mathlib
import StacksProject_2024.stacks_project.Chap05.Definition_5_11_4
import StacksProject_2024.stacks_project.Chap05.Definition_5_20_1
import StacksProject_2024.stacks_project.Chap05.Lemma_5_8_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Lemma 5.20.2:
- project owner for dimension functions: `IsDimensionFunction` in `Definition_5_20_1`
- derived graded-order owner: `IsDimensionFunction.gradeOrder` on `Specialization X`
- project owner for catenarity and relative codimension: `CatenarySpace` and `codimBetween` in
  `Definition_5_11_4`
- project soberification bridge: `toIrreducibleCloseds` in `Lemma_5_8_16`
- mathlib specialization owner: `Specializes.closure_subset`

Layer triage:
- `source-facing`: Lemma 5.20.2, pairing catenarity with the codimension formula for closures of
  specialized points
- `core/canonical`: `IsDimensionFunction`, its induced `gradeOrder`, `CatenarySpace`, and
  sobriety encoded by
  `[QuasiSober X]` together with the derived instance `hδ.t0Space`
- `bridge/view`: the order comparison on `IrreducibleCloseds X` induced by a specialization

Primitive data already belongs to the upstream owners, so this file keeps the combined textbook
statement primary and derives the individual consequences from it.
-/

namespace IsDimensionFunction

section

variable [QuasiSober X] {δ : X → ℤ}

-- Proof sketch: use quasi-sobriety together with the derived instance `hδ.t0Space` to identify
-- irreducible closed subsets with closures of their generic points. The dimension-function axioms
-- then compute the common length of maximal chains by telescoping along immediate specializations.
/-- Lemma 5.20.2: if `X` is sober and `δ` is a dimension function on `X`, then `X` is catenary.
Moreover, for any specialization `x ⤳ y`, the difference `δ x - δ y` equals the codimension of
`closure {y}` inside `closure {x}`. Quasi-sobriety is an ambient hypothesis, and `T₀` is derived
canonically from the dimension function. -/
theorem catenarySpace_and_sub_eq_codimBetween_pointClosure
    (hδ : IsDimensionFunction δ)
    :
    CatenarySpace X ∧
      ∀ (x y : X) (hxy : x ⤳ y),
        δ x - δ y =
          (ENat.toNat
            (codimBetween (toIrreducibleCloseds y) (toIrreducibleCloseds x)
              hxy.toIrreducibleCloseds_le) : ℤ) := sorry

/-- A quasi-sober topological space with a dimension function is catenary; the ambient `T₀`
structure is derived canonically from the dimension function. -/
theorem catenarySpace (hδ : IsDimensionFunction δ) :
    CatenarySpace X :=
  hδ.catenarySpace_and_sub_eq_codimBetween_pointClosure.1

-- Proof sketch: this is the codimension component of Lemma 5.20.2, applied to the irreducible
-- closed interval `[closure {y}, closure {x}]`.
/-- On a sober space, a dimension function computes the codimension between point closures along a
specialization. Here quasi-sobriety is ambient, and `T₀` is supplied canonically by the
dimension function. -/
theorem sub_eq_codimBetween_pointClosure (hδ : IsDimensionFunction δ)
    (x y : X) (hxy : x ⤳ y) :
    δ x - δ y =
      (ENat.toNat
        (codimBetween (toIrreducibleCloseds y) (toIrreducibleCloseds x)
          hxy.toIrreducibleCloseds_le) : ℤ) :=
  hδ.catenarySpace_and_sub_eq_codimBetween_pointClosure.2 x y hxy

end

end IsDimensionFunction
