import Mathlib.AlgebraicGeometry.Morphisms.Integral
import StacksProject_2024.Chap05.Lemma_5_19_9

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` and mathlib identify
-- `AlgebraicGeometry.IsIntegralHom` and `AlgebraicGeometry.Surjective` as the canonical
-- scheme-morphism owners for the source hypotheses.
--
-- Source-faithfulness note: although this generated file is named `Lemma_29_44_9.lean`, the
-- Stacks statements below are the dimension-theoretic Lemma `29.45.9`, tag `0ECG`.

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-
Layer triage:
- `source-facing`: `topologicalKrullDim_le_of_isIntegralHom`, the dimension inequality for an
  integral morphism.
- `bridge/view`: `topologicalKrullDim_eq_of_surjective_isIntegralHom`, combining the
  source-facing inequality with Chapter 5's canonical surjective specializing-map comparison.
-/

/-- Lemma 29.45.9 (1): an integral morphism of schemes does not increase Krull dimension. -/
@[stacks 0ECG]
theorem topologicalKrullDim_le_of_isIntegralHom [IsIntegralHom f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y := sorry

/-- Lemma 29.45.9 (2): a surjective integral morphism of schemes preserves Krull dimension. -/
@[stacks 0ECG]
theorem topologicalKrullDim_eq_of_surjective_isIntegralHom [IsIntegralHom f] [Surjective f] :
    topologicalKrullDim X = topologicalKrullDim Y := by
  apply le_antisymm
  · exact topologicalKrullDim_le_of_isIntegralHom f
  · exact topologicalKrullDim_le_of_surjective_specializing_or_generalizing
      f.surjective (.inl f.isClosedMap.specializingMap)

end

end AlgebraicGeometry
