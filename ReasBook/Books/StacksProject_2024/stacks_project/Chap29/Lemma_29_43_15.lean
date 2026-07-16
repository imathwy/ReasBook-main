import StacksProject_2024.stacks_project.Chap29.Definition_29_43_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry

section

variable {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}

namespace Projective

/-- Companion API: a closed immersion followed by a projective morphism is projective. -/
theorem comp_of_isClosedImmersion
    (hf : IsClosedImmersion f) [Projective g] :
    Projective (f ≫ g) := by
  sorry

/-- Companion API: if `g ∘ f` is projective and `g` is separated, then `f` is projective. -/
theorem of_comp_of_isSeparated
    [IsSeparated g] [Projective (f ≫ g)] :
    Projective f := by
  sorry

end Projective

/- Semantic recall / source-core-bridge check:
Chapter 29 already owns the source-facing scheme-morphism predicate `Projective` in
`Definition_29_43_1`. The relevant core descent pattern is the generic separated-postcomposition
mechanism for morphism properties, but this file should expose the source lemma directly on the
existing projective owner rather than leaving only that generic recall. The Stacks tag evidence is
consistent: item tag `0C4Q` matches the source URL ending in `/tag/0C4Q`. -/

/-- Lemma 29.43.15: if `g ∘ f` is projective and `g` is separated, then `f` is projective. -/
@[stacks 0C4Q]
theorem projective_of_comp_of_isSeparated [IsSeparated g] (hfg : Projective (f ≫ g)) :
    Projective f := by
  letI : Projective (f ≫ g) := hfg
  exact Projective.of_comp_of_isSeparated

end

end AlgebraicGeometry
