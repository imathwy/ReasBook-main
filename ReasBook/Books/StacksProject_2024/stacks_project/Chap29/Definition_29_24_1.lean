import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.Topology.Maps.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the existing scheme-level owners
-- `AlgebraicGeometry.UniversallyOpen` and `AlgebraicGeometry.UniversallyClosed`, but no
-- dedicated owner for submersive morphisms in the current library snapshot. The source item is
-- therefore formalized directly as the quotient-map condition on the underlying topological
-- spaces, together with its universal base-change version.

universe u

section

/-- The scheme morphism property of being a quotient map on underlying topological spaces. -/
abbrev submersiveProperty : MorphismProperty Scheme.{u} :=
  fun _ _ f ↦ Topology.IsQuotientMap f

/-- Submersiveness is stable under composition. -/
instance submersiveProperty_isStableUnderComposition :
    submersiveProperty.IsStableUnderComposition :=
  ⟨fun f g hf hg ↦ by
    simpa only [Scheme.Hom.comp_base, TopCat.coe_comp] using hg.comp hf⟩

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Definition 29.24.1 (1): a morphism of schemes is submersive if the induced continuous map on
underlying topological spaces is submersive, equivalently a quotient map. -/
class Submersive (f : X ⟶ Y) : Prop where
  isQuotientMap : submersiveProperty f

/-- Unfold `Submersive` as the quotient-map condition on the underlying topological spaces. -/
theorem submersive_iff_base_isQuotientMap :
    Submersive f ↔ Topology.IsQuotientMap f :=
  ⟨fun h ↦ h.isQuotientMap, fun h ↦ ⟨h⟩⟩

attribute [simp] submersive_iff_base_isQuotientMap

/-- A submersive morphism of schemes is a quotient map on the underlying topological spaces. -/
theorem Scheme.Hom.isQuotientMap (f : X ⟶ Y) [Submersive f] :
    Topology.IsQuotientMap f :=
  Submersive.isQuotientMap

/-- Definition 29.24.1 (2): a morphism of schemes is universally submersive if every base change
projection is submersive. -/
class UniversallySubmersive (f : X ⟶ Y) : Prop where
  universally : submersiveProperty.universally f

/-- Unfold `UniversallySubmersive` as the universal quotient-map condition on pullbacks. -/
theorem universallySubmersive_iff_universally :
    UniversallySubmersive f ↔ submersiveProperty.universally f :=
  ⟨fun h ↦ h.universally, fun h ↦ ⟨h⟩⟩

attribute [simp] universallySubmersive_iff_universally

end

end AlgebraicGeometry
