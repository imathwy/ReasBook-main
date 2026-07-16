import StacksProject_2024.stacks_project.Chap10.Definition_10_157_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: the source statement is directly stalkwise, and the canonical Serre owners for
-- `(R_0)` and `(S_1)` already live at the ring level in Chapter 10. This file therefore keeps the
-- source-facing stalkwise formulation instead of introducing a Chapter-28 to Chapter-30 back-edge
-- merely to reuse a later scheme-level specialization of `(S_k)`.

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- Lemma 28.12.4: a locally Noetherian scheme `X` is reduced if and only if every stalk
`X.presheaf.stalk x` satisfies Serre's conditions `(S_1)` and `(R_0)`. -/
@[stacks 0343]
theorem isReduced_iff_stalkwise_serreConditionS_one_and_serreConditionR_zero :
    IsReduced X ↔
      (∀ x : X, SerreConditionS (X.presheaf.stalk x) 1) ∧
        ∀ x : X, SerreConditionR (X.presheaf.stalk x) 0 := sorry

/-- Companion form of Lemma 28.12.4 in the canonical `(R_0) ∧ (S_1)` order used by the
ring-level Serre criterion. -/
theorem isReduced_iff_stalkwise_serreConditionR_zero_and_serreConditionS_one :
    IsReduced X ↔
      (∀ x : X, SerreConditionR (X.presheaf.stalk x) 0) ∧
        ∀ x : X, SerreConditionS (X.presheaf.stalk x) 1 := by
  constructor
  · intro h
    rcases (isReduced_iff_stalkwise_serreConditionS_one_and_serreConditionR_zero X).mp h with
      ⟨hS, hR⟩
    exact ⟨hR, hS⟩
  · rintro ⟨hR, hS⟩
    exact (isReduced_iff_stalkwise_serreConditionS_one_and_serreConditionR_zero X).mpr ⟨hS, hR⟩

end AlgebraicGeometry.Scheme
