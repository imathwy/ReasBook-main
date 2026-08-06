import Mathlib.Tactic.Recall
import Mathlib.Topology.Homotopy.Basic

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable (f f' : C(X, Y)) (A : Set X)

-- Semantic recall via `lean_leansearch`: mathlib's canonical owners for homotopies fixed on a
-- subset and for the corresponding relative-homotopy relation are
-- `ContinuousMap.HomotopyRel` and `ContinuousMap.HomotopicRel`.

namespace ContinuousMap

scoped notation:50 f " HRel[" A "] " g =>
  ContinuousMap.HomotopyRel f g A

scoped notation:50 f " ≃ₕ[" A "] " g =>
  ContinuousMap.HomotopicRel f g A

end ContinuousMap

open scoped ContinuousMap

/- Definition 9.6.4: for continuous maps `f, f' : C(X, Y)` underlying maps of pairs
`(X, A) → (Y, B)` and agreeing on `A`, a homotopy relative to `A` is a homotopy fixed on `A`.
Mathlib formalizes this canonical owner as `f HRel[A] f'`; the corresponding proposition,
written in the source as `f ≃ f' rel A`, is `f ≃ₕ[A] f'`. -/
recall ContinuousMap.HomotopyRel (f f' : C(X, Y)) (A : Set X) : Type _

/- The relative-homotopy relation itself is the proposition `f ≃ₕ[A] f'`. -/
recall ContinuousMap.HomotopicRel (f f' : C(X, Y)) (A : Set X) : Prop

namespace ContinuousMap

variable {f f' : C(X, Y)} {A : Set X}

/-- The proposition-level relative-homotopy relation is exactly the nonempty witness type. -/
theorem homotopicRel_iff_nonempty_homotopyRel :
    (f ≃ₕ[A] f') ↔ Nonempty (f HRel[A] f') :=
  Iff.rfl

/-- A relative homotopy witness forces the endpoint maps to agree on the fixed subset. -/
theorem HomotopyRel.eqOn (H : f HRel[A] f') : Set.EqOn f f' A := by
  intro x hx
  exact H.fst_eq_snd hx

/-- Relative-homotopic maps agree on the fixed subset. -/
theorem homotopicRel_eqOn (h : f ≃ₕ[A] f') : Set.EqOn f f' A := by
  intro x hx
  exact h.fst_eq_snd hx

end ContinuousMap
