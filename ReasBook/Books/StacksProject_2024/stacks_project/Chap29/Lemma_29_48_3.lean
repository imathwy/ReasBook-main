import StacksProject_2024.Chap29.Lemma_29_48_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

section

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}

-- Semantic recall: `Lemma_29_48_2.lean` already records finite locally free morphisms through the
-- Chapter 29 source-facing owner `IsFiniteLocallyFree` and its canonical bridge to the explicit
-- conjunction `IsFinite ∧ Flat ∧ LocallyOfFinitePresentation`; the composition-stable components
-- are the existing owners `isFinite_comp`, `Flat.comp`, and `locallyOfFinitePresentation_comp`.

/-- Lemma 29.48.3: a composition of finite locally free morphisms is finite locally free. Here
“finite locally free” is recorded by the Chapter 29 owner `IsFiniteLocallyFree`. -/
theorem finiteLocallyFree_comp
    (hf : IsFiniteLocallyFree f) (hg : IsFiniteLocallyFree g) :
    IsFiniteLocallyFree (f ≫ g) := by
  letI : IsFiniteLocallyFree f := hf
  letI : IsFiniteLocallyFree g := hg
  exact isFiniteLocallyFree_of_isFinite_and_flat_and_locallyOfFinitePresentation
    (by infer_instance) (Flat.comp f g) (locallyOfFinitePresentation_comp f g)

/-- A composition of finite locally free morphisms is finite locally free. -/
instance instIsFiniteLocallyFreeComp
    [IsFiniteLocallyFree f] [IsFiniteLocallyFree g] :
    IsFiniteLocallyFree (f ≫ g) :=
  finiteLocallyFree_comp inferInstance inferInstance

end

end AlgebraicGeometry
