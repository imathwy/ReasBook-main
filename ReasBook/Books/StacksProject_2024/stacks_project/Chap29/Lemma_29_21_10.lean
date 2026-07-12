import StacksProject_2024.Chap29.Definition_29_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

-- Semantic recall / owner check:
-- - `Definition_29_21_1.lean` records the source phrase “of finite presentation” by the chapter
--   owner `Scheme.Hom.FinitePresentation`;
-- - mathlib already provides the canonical bridges from quasi-compact and quasi-separated
--   morphisms to the corresponding topological properties of the source scheme;
-- - the source file's paired base assumptions can therefore be refined to the minimal canonical
--   hypotheses needed for each consequence while keeping the Stacks-facing statements directly on
--   `Scheme.Hom.FinitePresentation`.

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Lemma 29.21.10: if `X` is of finite presentation over a quasi-compact and quasi-separated
base `S`, then `X` is quasi-compact and quasi-separated. -/
@[stacks 01TY]
theorem compactSpace_and_quasiSeparatedSpace_of_finitePresentation [CompactSpace S]
    [QuasiSeparatedSpace S] [FinitePresentation f] :
    CompactSpace X ∧ QuasiSeparatedSpace X := by
  constructor
  · let _ : QuasiCompact f := inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace f
  · let _ : QuasiCompact f := inferInstance
    exact quasiSeparatedSpace_of_quasiSeparated f

/-- If `X` is of finite presentation over a quasi-compact base `S`, then `X` is quasi-compact. -/
theorem compactSpace_of_finitePresentation [CompactSpace S] [FinitePresentation f] :
    CompactSpace X := by
  let _ : QuasiCompact f := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace f

/-- If `X` is of finite presentation over a quasi-separated base `S`, then `X` is
quasi-separated. -/
theorem quasiSeparatedSpace_of_finitePresentation [QuasiSeparatedSpace S]
    [FinitePresentation f] :
    QuasiSeparatedSpace X := by
  let _ : QuasiCompact f := inferInstance
  exact quasiSeparatedSpace_of_quasiSeparated f

end AlgebraicGeometry.Scheme.Hom
