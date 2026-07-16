import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall note: local mathlib/source checks confirm that a morphism of finite
-- presentation is represented in this repository by `Scheme.Hom.FinitePresentation`, whose
-- canonical consequences include `LocallyOfFinitePresentation` and `QuasiCompact`; closed
-- immersions are also quasi-compact. This remark is source-facing, while the quasi-compactness
-- implication below is the bridge to the canonical owner.

/-- A factorization through a closed immersion and a morphism of finite presentation is
quasi-compact. -/
theorem quasiCompact_of_closedImmersion_finitePresentation_factorization
    {X X' S : Scheme.{u}} {f : X ⟶ S} (i : X ⟶ X') (g : X' ⟶ S)
    [IsClosedImmersion i] [Scheme.Hom.FinitePresentation g] (hfactor : i ≫ g = f) :
    QuasiCompact f := by
  simpa [hfactor] using (inferInstance : QuasiCompact (i ≫ g))

/-- A factorization through a closed immersion and a morphism of finite presentation forces
quasi-compactness. -/
theorem quasiCompact_of_exists_closedImmersion_finitePresentation_factorization
    {X S : Scheme.{u}} {f : X ⟶ S}
    (h :
      ∃ (X' : Scheme.{u}) (i : X ⟶ X') (g : X' ⟶ S),
        IsClosedImmersion i ∧ Scheme.Hom.FinitePresentation g ∧ i ≫ g = f) :
    QuasiCompact f := by
  rcases h with ⟨X', i, g, hi, hg, hfactor⟩
  letI : IsClosedImmersion i := hi
  letI : Scheme.Hom.FinitePresentation g := hg
  exact quasiCompact_of_closedImmersion_finitePresentation_factorization i g hfactor

/-- Remark 32.9.2: if `f : X ⟶ S` is not quasi-compact, then one cannot factor `f` through a
closed immersion `X ⟶ X'` with `X' ⟶ S` of finite presentation. -/
theorem no_closedImmersion_factorization_into_finitePresentation_of_not_quasiCompact
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : ¬ QuasiCompact f) :
    ¬ ∃ (X' : Scheme.{u}) (i : X ⟶ X') (g : X' ⟶ S),
      IsClosedImmersion i ∧ Scheme.Hom.FinitePresentation g ∧ i ≫ g = f := by
  intro h
  exact hf (quasiCompact_of_exists_closedImmersion_finitePresentation_factorization h)

end AlgebraicGeometry
