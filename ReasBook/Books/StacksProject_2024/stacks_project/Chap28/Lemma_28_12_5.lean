import StacksProject_2024.Chap28.Definition_28_7_1
import StacksProject_2024.Chap28.Definition_28_12_1
import StacksProject_2024.Chap10.Lemma_10_157_4_Serre_s_criterion_for_normality
import StacksProject_2024.Chap30.Definition_30_11_1_Scheme

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: the source states Lemma 28.12.5 stalkwise. Chapter 28 already owns the
-- scheme-level `(R₁)` predicate via `satisfiesSerreConditionR`, while the canonical `(S₂)` owner
-- still lives at the ring level in this part of the development. The main theorem therefore keeps
-- the chapter-local scheme owner for `(R₁)` and a stalkwise ring-level `(S₂)` clause, with a
-- fully stalkwise ring-level companion theorem below.

variable (X : Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X]

/-- Lemma 28.12.5: a locally Noetherian scheme `X` is normal if and only if it satisfies the
scheme-level condition `(R_1)` and every stalk `X.presheaf.stalk x` satisfies `(S_2)`. This is
the source stalkwise criterion, with the Chapter 28 owner `satisfiesSerreConditionR X 1`
absorbing the `(R_1)` half. -/
@[stacks 0345]
theorem isNormal_iff_satisfiesSerreConditionR_one_and_stalkwise_serreConditionS_two :
    X.isNormal ↔
      satisfiesSerreConditionR X 1 ∧ ∀ x : X, (X.presheaf.stalk x) ⊧ (S₂) := by
  rw [isNormal_iff, satisfiesSerreConditionR_iff_stalkwise_serreConditionR]
  constructor
  · intro hX
    refine ⟨?_, ?_⟩
    · intro x
      exact (isNormalRing_iff_serreConditionR_one_and_serreConditionS_two.1 (hX x)).1
    · intro x
      exact (isNormalRing_iff_serreConditionR_one_and_serreConditionS_two.1 (hX x)).2
  · rintro ⟨hR, hS⟩ x
    exact isNormalRing_iff_serreConditionR_one_and_serreConditionS_two.2 ⟨hR x, hS x⟩

/-- Stalkwise ring-level form of Lemma 28.12.5 in the canonical `(R_1) ∧ (S_2)` order. -/
theorem isNormal_iff_stalkwise_serreConditionR_one_and_serreConditionS_two :
    X.isNormal ↔
      ∀ x : X, (X.presheaf.stalk x) ⊧ (R₁) ∧ (X.presheaf.stalk x) ⊧ (S₂) := by
  rw [isNormal_iff_satisfiesSerreConditionR_one_and_stalkwise_serreConditionS_two X,
    satisfiesSerreConditionR_iff_stalkwise_serreConditionR]
  constructor
  · rintro ⟨hR, hS⟩ x
    exact ⟨hR x, hS x⟩
  · intro h
    exact ⟨fun x ↦ (h x).1, fun x ↦ (h x).2⟩

/-- A locally Noetherian normal scheme satisfies Serre's condition `(S_2)`. This is the canonical
scheme-level bridge from the Chapter 28 normality owner to the Chapter 30 scheme owner
`satisfiesSerreConditionS X 2`. -/
theorem satisfiesSerreConditionS_two_of_isNormal
    (hnormal : X.isNormal) :
    satisfiesSerreConditionS X 2 := by
  sorry

end AlgebraicGeometry.Scheme
