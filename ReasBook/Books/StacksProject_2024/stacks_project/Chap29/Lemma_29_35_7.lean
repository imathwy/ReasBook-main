import StacksProject_2024.stacks_project.Chap29.Lemma_29_35_9

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the canonical open-immersion consequences
  `AlgebraicGeometry.FormallyUnramified`,
  `AlgebraicGeometry.locallyOfFiniteType_of_isOpenImmersion`, and
  `AlgebraicGeometry.locallyOfFinitePresentation_of_isOpenImmersion`;
- the local Chapter 29 owner `GUnramified` is introduced in `Lemma_29_35_9.lean`, so this item is
  recorded as the source-facing bridge from open immersions to that owner.
-/

instance instUnramifiedOfIsOpenImmersion [IsOpenImmersion f] :
    Unramified f where
  toFormallyUnramified := inferInstanceAs (FormallyUnramified f)
  toLocallyOfFiniteType := inferInstanceAs (LocallyOfFiniteType f)

/-- An open immersion is unramified. -/
theorem unramified_of_isOpenImmersion [IsOpenImmersion f] :
    Unramified f :=
  inferInstance

instance instGUnramifiedOfIsOpenImmersion [IsOpenImmersion f] :
    GUnramified f where
  toFormallyUnramified := inferInstanceAs (FormallyUnramified f)
  toLocallyOfFinitePresentation := inferInstanceAs (LocallyOfFinitePresentation f)

/-- Lemma 29.35.7: any open immersion is G-unramified. -/
@[stacks 02GB]
theorem gUnramified_of_isOpenImmersion [IsOpenImmersion f] :
    GUnramified f :=
  inferInstance

end AlgebraicGeometry
