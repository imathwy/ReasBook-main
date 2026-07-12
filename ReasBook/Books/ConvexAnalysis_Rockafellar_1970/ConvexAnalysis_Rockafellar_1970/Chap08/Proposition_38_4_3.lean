import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_9
import ConvexAnalysis_Rockafellar_1970.Chap08.Theorem_38_5

noncomputable section

universe u v w r

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.4.3 identifies the Chapter 38 product of two singleton-graph
  indicator bifunctions with the singleton-graph indicator of the composite map.
- `core/canonical`: the owner abstractions already present upstream are `Bifunction.comp` for the
  Chapter 38 product, `Bifunction.graphIndicator` for singleton-graph indicators, and
  `Function.comp` for composition of maps.
- `bridge/view`: this item is therefore a direct equality between existing owners, while the
  indexed-infimum formula is kept only as a companion derived from `comp_apply_eq_iInf`.

Primary mathematical domain:
- composition of singleton-indicator bifunctions attached to maps.

Domain-style sampling used here:
- `Bifunction.graphIndicator` from `Chap06.Definition_6_29_9`;
- `Bifunction.comp` and `Bifunction.comp_apply_eq_iInf` from `Chap08.Theorem_38_5`;
- `Function.comp` from core Lean.

Primitive data vs derived API:
- primitive source data: maps `A : U → X` and `B : X → Y`;
- primitive source-facing owner expression: `comp (graphIndicator 𝕜 B) (graphIndicator 𝕜 A)`;
- derived API: the owner equality with `graphIndicator 𝕜 (B ∘ A)` and its explicit pointwise
  `iInf` formula, from which the textbook linear-map case follows by specialization.

Layer target: `bridge/view`.
-/

section

variable {𝕜 : Type r} {U : Type u} {X : Type v} {Y : Type w}
variable [AddMonoid 𝕜] [ConditionallyCompleteLattice 𝕜]

-- Proof sketch: evaluate the Chapter 38 owner `comp` with `comp_apply_eq_iInf`. If
-- `y = B (A u)`, the summand at `x = A u` is `0`, and every other summand is `⊤`; if
-- `y ≠ B (A u)`, then every summand is already `⊤`. This is exactly the singleton-indicator
-- bifunction of `B ∘ A`.
/-- Proposition 38.4.3, owner form: the Chapter 38 product of the singleton-indicator
bifunctions of maps `A` and `B` is the singleton-indicator bifunction of the composite
`B ∘ A`. The textbook linear-map statement is its direct specialization. -/
theorem comp_graphIndicator_eq_graphIndicator_comp
    (A : U → X) (B : X → Y) :
    comp (graphIndicator 𝕜 B) (graphIndicator 𝕜 A) =
      graphIndicator 𝕜 (B ∘ A) := by
  classical
  funext u y
  rw [comp_apply_eq_iInf]
  by_cases hy : y = B (A u)
  · have hle :
        (⨅ x : X, graphIndicator 𝕜 A u x + graphIndicator 𝕜 B x y) ≤
          (0 : WithBotTop 𝕜) := by
      simpa [graphIndicator_cases, hy] using
        (iInf_le (fun x : X ↦ graphIndicator 𝕜 A u x + graphIndicator 𝕜 B x y) (A u))
    have hge :
        (0 : WithBotTop 𝕜) ≤
          ⨅ x : X, graphIndicator 𝕜 A u x + graphIndicator 𝕜 B x y := by
      refine le_iInf fun x ↦ ?_
      by_cases hx : x = A u
      · subst hx
        simp [graphIndicator_cases, hy]
      · have hbranch : (if B (A u) = B x then (0 : WithBotTop 𝕜) else ⊤) ≠ ⊥ := by
          by_cases hBx : B (A u) = B x <;> simp [hBx]
        simp [graphIndicator_cases, hx, hy, hbranch] at *
    simpa [graphIndicator_cases, hy] using le_antisymm hle hge
  · have htop :
        (⊤ : WithBotTop 𝕜) ≤
          ⨅ x : X, graphIndicator 𝕜 A u x + graphIndicator 𝕜 B x y := by
      refine le_iInf fun x ↦ ?_
      by_cases hx : x = A u
      · subst hx
        simp [graphIndicator_cases, hy]
      · have hbranch : (if y = B x then (0 : WithBotTop 𝕜) else ⊤) ≠ ⊥ := by
          by_cases hBx : y = B x <;> simp [hBx]
        simp [graphIndicator_cases, hx, hbranch] at *
    simpa [graphIndicator_cases, hy] using le_antisymm le_top htop

/-- Pointwise owner form of Proposition 38.4.3. -/
@[simp] theorem comp_graphIndicator_apply
    (A : U → X) (B : X → Y) (u : U) (y : Y) :
    comp (graphIndicator 𝕜 B) (graphIndicator 𝕜 A) u y =
      graphIndicator 𝕜 (B ∘ A) u y := by
  simpa using congrFun (congrFun (comp_graphIndicator_eq_graphIndicator_comp A B) u) y

/-- Pointwise `iInf` companion form of Proposition 38.4.3, obtained by expanding the Chapter 38
owner `comp`. -/
theorem iInf_add_graphIndicator_eq_graphIndicator_comp
    (A : U → X) (B : X → Y) (u : U) (y : Y) :
    (⨅ x : X, graphIndicator 𝕜 A u x + graphIndicator 𝕜 B x y) =
      graphIndicator 𝕜 (B ∘ A) u y := by
  simpa [comp_apply_eq_iInf] using comp_graphIndicator_apply A B u y

end

end Bifunction
