import Mathlib.AlgebraicGeometry.Morphisms.Constructors
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.Topology.Homeomorph.Defs

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the existing scheme-level owners
-- `AlgebraicGeometry.UniversallyInjective` and `AlgebraicGeometry.UniversallyClosed`, but no
-- dedicated owner for universal homeomorphisms in the current library snapshot. The source item is
-- therefore formalized directly as the universal `IsHomeomorph` condition on pullback projections.

section

/-- The scheme morphism property of being a homeomorphism on underlying topological spaces. -/
abbrev topologicallyIsHomeomorph : MorphismProperty Scheme.{u} :=
  topologically fun f ↦ IsHomeomorph f

/-- The homeomorphism-on-spaces morphism property is stable under composition. -/
instance topologicallyIsHomeomorph_isStableUnderComposition :
    topologicallyIsHomeomorph.IsStableUnderComposition :=
  topologically_isStableUnderComposition _ (fun _ _ hf hg ↦ hg.comp hf)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Definition 29.45.1: a morphism of schemes is a universal homeomorphism if every base change
projection is a homeomorphism on the underlying topological spaces. -/
@[stacks 04DD, mk_iff]
class UniversalHomeomorphism (f : X ⟶ Y) : Prop where
  universally_isHomeomorph : universally topologicallyIsHomeomorph f

/-- Every pullback projection of a universal homeomorphism is a homeomorphism on underlying
topological spaces. -/
@[stacks 04DD]
theorem UniversalHomeomorphism.pullbackSnd_isHomeomorph
    [UniversalHomeomorphism f] {T : Scheme.{u}} (g : T ⟶ Y) :
    IsHomeomorph (pullback.snd f g) :=
  UniversalHomeomorphism.universally_isHomeomorph _ _ _ (IsPullback.of_hasPullback f g).flip

/-- A universal homeomorphism is a homeomorphism on the underlying topological spaces. -/
@[stacks 04DD]
theorem Scheme.Hom.isHomeomorph (f : X ⟶ Y) [UniversalHomeomorphism f] :
    IsHomeomorph f :=
  UniversalHomeomorphism.universally_isHomeomorph _ _ _ IsPullback.of_id_snd

end

end AlgebraicGeometry
