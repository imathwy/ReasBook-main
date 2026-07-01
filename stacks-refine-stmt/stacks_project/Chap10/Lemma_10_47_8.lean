import Mathlib
import stacks_project.Chap09.Definition_9_26_9
import stacks_project.Chap10.Lemma_10_47_12

open AlgebraicGeometry CommRingCat

namespace Algebra

universe u

section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

-- If `k` is algebraically closed in `K`, then no nontrivial separable subextension of `K / k`
-- remains: the relative separable closure is `k` itself.
private theorem separableClosure_eq_bot_of_algebraicClosure_eq_bot
    (hclosed : algebraicClosure k K = ⊥) :
    separableClosure k K = ⊥ := by
  apply bot_unique
  intro x hx
  obtain ⟨y, rfl⟩ :=
    (algebraicClosure_eq_bot_iff k K).mp hclosed x <|
      (mem_separableClosure_iff.mp hx).isIntegral.isAlgebraic
  exact IntermediateField.mem_bot.mpr ⟨y, rfl⟩

-- Proof sketch: use the canonical field-extension criterion from Lemma `10.47.12`, which says
-- geometric irreducibility is equivalent to the relative separable closure being trivial. The
-- auxiliary lemma above shows exactly this triviality from the hypothesis that `k` is
-- algebraically closed in `K`.
/-- Lemma 10.47.8: if `k` is algebraically closed in the field extension `K`, then `K` is
geometrically irreducible over `k`. -/
@[stacks 037P]
theorem isGeometricallyIrreducibleOver_of_algebraicClosure_eq_bot
    (hclosed : algebraicClosure k K = ⊥) :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k K))) := by
  rw [isGeometricallyIrreducibleOver_iff_separableClosure_eq_bot]
  exact separableClosure_eq_bot_of_algebraicClosure_eq_bot hclosed

end

end Algebra
