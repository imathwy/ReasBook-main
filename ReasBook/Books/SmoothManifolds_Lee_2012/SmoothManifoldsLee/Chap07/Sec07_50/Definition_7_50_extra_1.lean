import Mathlib
import Mathlib.Tactic.Recall

-- `lean_leansearch` was unavailable in this environment; the canonical names below were verified
-- directly against mathlib's group action and smooth action APIs.

/-!
Definition 7.50-extra-1

Canonical mathlib owners for the textbook terminology in this section:

* left actions of a group `G` on `M`: `MulAction G M`
* right actions are modeled as left actions of the opposite group
* continuous actions / `G`-spaces: `ContinuousSMul G M`
* smooth actions of Lie groups on manifolds: `ContMDiffSMul I I' n G M`
* orbits: `MulAction.orbit G p`
* isotropy groups / stabilizers: `MulAction.stabilizer G p`
* transitive actions: `MulAction.IsPretransitive G M`
* free actions: `IsCancelSMul G M`
-/

#check MulAction
#check ContinuousSMul
#check ContMDiffSMul
#check MulAction.orbit
#check MulAction.stabilizer
#check MulAction.IsPretransitive

universe u v

/- Definition 7.50-extra-1: a group action is free exactly when the canonical mathlib owner
`IsCancelSMul G M` holds. -/
recall IsCancelSMul (G : Type u) (P : Type v) [SMul G P] : Prop

/- A group action is free exactly when every stabilizer subgroup is trivial. -/
recall isCancelSMul_iff_stabilizer_eq_bot {G : Type u} {α : Type v} [Group G] [MulAction G α] :
    IsCancelSMul G α ↔ ∀ a : α, MulAction.stabilizer G a = ⊥
