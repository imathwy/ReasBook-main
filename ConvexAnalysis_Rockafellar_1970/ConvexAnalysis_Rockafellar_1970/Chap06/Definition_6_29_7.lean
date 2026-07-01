import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 6.29.7 names the graph domain of a bifunction `F`.
- `core/canonical`: Definition 6.29.2 already fixes the graph function as `uncurry F`,
  and Definition 4.4 already fixes effective domains through the owner `effectiveDomain`, written
  `dom(·)`.
- `bridge/view`: the source pointwise reading "the pairs `(u, x)` where `F u x < ⊤`" is not a
  second owner; it is exactly `mem_effectiveDomain` specialized to `uncurry F`.

Domain-style sampling used here:
- `Function.uncurry` (used as `uncurry`) from `Definition_6_29_2`;
- `effectiveDomain` and the notation `dom(·)` from `Definition_4_4`;
- `mem_effectiveDomain` from `Definition_4_4`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → β` into a codomain with `⊤` and `<`;
- canonical owner surface: `dom(uncurry F)`;
- derived API: downstream files should use `mem_effectiveDomain` directly on
  `uncurry F`, rather than a parallel local wrapper theorem.

Layer target: `core/canonical recall/use`.
-/

section

open Function

variable {U : Type u} {X : Type v} {β : Type w}
variable [Top β] [LT β]
variable (F : U → X → β)

/- Definition 6.29.7: the graph domain of a bifunction `F` is the effective domain of its graph
function from Definition 6.29.2, namely the canonical owner set `dom(uncurry F)`. -/
#check (dom(uncurry F) : Set (U × X))

/- Pointwise bridge (without introducing a duplicate owner): membership in the graph domain is
exactly the strict-top test for the uncurried graph function. -/
#check (show ∀ p : U × X, p ∈ dom(uncurry F) ↔ F p.1 p.2 < ⊤ from
  fun p => by
    calc
      p ∈ dom(uncurry F) ↔ uncurry F p < ⊤ :=
        (_root_.mem_effectiveDomain (f := uncurry F) (x := p))
      _ ↔ F p.1 p.2 < ⊤ := by
        simp [uncurry])

end
