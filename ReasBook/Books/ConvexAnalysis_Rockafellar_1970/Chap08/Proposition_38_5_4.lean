import ConvexAnalysis_Rockafellar_1970.Chap07.Lemma33_0_9
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_5_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

universe u v w

namespace Function

section IndicatorOfPoint

variable {X : Type u} {Y : Type v} {α : Type w}
variable [AddGroup α] [ConditionallyCompleteLattice α] [HasPairing X Y α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.5.4 evaluates the Chapter 38 inner product of the convex
  indicator of the point `a` and the concave indicator of the point `b`.
- `core/canonical`: the owner already introduced upstream is `Function.innerProduct`; the point
  indicators are already owned by the Chapter 1 notation `δ[α](· | C)`.
- `bridge/view`: the self-inner-product reading from the source is a specialization of the
  canonical pairing statement, so this file should reuse the Chapter 33 singleton-pairing bridge
  theorems instead of rebuilding conjugate/support calculations locally.

Primary mathematical domain:
- Fenchel-style function pairings on the primitive pairing layer.

Domain-style sampling used here:
- `Function.innerProduct` from `Definition_38_5_2`;
- `convexConjugate_eq_iSup_pairing_sub` from `Chap03.Defn_12_2`;
- `Function.concaveConjugate_negIndicator_singleton` from `Chap07.Lemma33_0_9`;
- `Function.convexPairing_indicator_singleton` from `Chap07.Lemma33_0_9`.

Primitive data vs derived API:
- primitive data: a left point `a : X`, a right point `b : Y`, and the ambient pairing;
- derived API: the Chapter 38 inner-product value of the corresponding singleton indicators.

Layer target: `source-facing`, stated directly on the Chapter 38 function owner at the canonical
pairing level.
-/

local instance indicatorSingletonHasPairing : HasPairing Y X α :=
  HasPairing.swap

-- Proof sketch: rewrite the Chapter 38 owner `innerProduct` as the outer supremum formula and
-- collapse the concave singleton indicator there by the Chapter 33 singleton-pairing theorem.
-- The remaining supremum is exactly the convex pairing of the singleton indicator at `a`, which
-- the companion Chapter 33 theorem evaluates to the ambient pairing value `⟪a, b⟫ₚ`.
/-- Proposition 38.5.4: the Chapter 38 inner product of the convex indicator of the point `a`
and the concave indicator of the point `b` is the ambient pairing value `⟪a, b⟫ₚ`. In the source
self-pairing case, this specializes to the ordinary inner product. -/
theorem innerProduct_indicator_singleton_eq_pairing
    (a : X) (b : Y) :
    innerProduct (δ[α](· | ({a} : Set X))) (fun y ↦ -(δ[α](y | ({b} : Set Y)))) =
      (⟪a, b⟫ₚ : WithBotTop α) := by
  calc
    innerProduct (δ[α](· | ({a} : Set X))) (fun y ↦ -(δ[α](y | ({b} : Set Y)))) =
        ⟪(δ[α](· | ({a} : Set X))), b⟫ᶠ := by
          rw [innerProduct_eq_iSup_concaveConjugate_sub, convexConjugate_eq_iSup_pairing_sub]
          refine iSup_congr fun x ↦ ?_
          exact
            congrArg (fun t : WithBotTop α ↦ t - δ[α](x | ({a} : Set X)))
              (concaveConjugate_negIndicator_singleton b x)
    _ = (⟪a, b⟫ₚ : WithBotTop α) := by
          exact convexPairing_indicator_singleton a b

end IndicatorOfPoint

end Function
