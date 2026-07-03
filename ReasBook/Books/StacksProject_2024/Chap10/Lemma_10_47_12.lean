import Mathlib
import StacksProject_2024.Chap10.Definition_10_47_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CommRingCat IntermediateField

namespace Algebra

universe u

section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

-- Proof sketch: for the forward implication, if `α` is separable over `k`, then the simple
-- extension `k⟮α⟯ / k` is a finite separable subextension of `K`; geometric irreducibility forces
-- this subextension to be trivial, so `α` lies in `k`. For the converse, the hypothesis says the
-- algebraic closure of `k` inside `K` is purely inseparable over `k`; combine Lemma `10.47.8`
-- with the geometric irreducibility of purely inseparable extensions and then apply transitivity
-- from Lemma `10.47.9`.
/-- Lemma 10.47.12: a field extension `K / k` is geometrically irreducible exactly when its
relative separable closure in `K` is trivial. -/
theorem isGeometricallyIrreducibleOver_iff_separableClosure_eq_bot :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k K))) ↔
      separableClosure k K = ⊥ := sorry

/-- Lemma 10.47.12, source form: a field extension `K / k` is geometrically irreducible exactly
when every separable element of `K` already lies in the base field `k`. -/
theorem isGeometricallyIrreducibleOver_iff_forall_separable_mem_bot :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k K))) ↔
      ∀ α : K, IsSeparable k α → α ∈ (⊥ : IntermediateField k K) := by
  refine isGeometricallyIrreducibleOver_iff_separableClosure_eq_bot.trans ?_
  constructor
  · intro h α hα
    simpa [h] using (mem_separableClosure_iff.2 hα : α ∈ separableClosure k K)
  · intro h
    exact bot_unique fun α hα ↦ h α (mem_separableClosure_iff.1 hα)

end

end Algebra
