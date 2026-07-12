import Mathlib

open CategoryTheory Limits Opposite CategoryOfElements
open CategoryTheory.OverPresheafAux

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (ℱ : Sheaf J (Type v))

noncomputable section LocalizationProjection

/-- The projection from the category of elements of a sheaf to the base site. -/
abbrev localizationProjection (ℱ : Sheaf J (Type v)) : ℱ.obj.Elementsᵒᵖ ⥤ C :=
  (π ℱ.obj).leftOp

local notation "j" => localizationProjection ℱ

/-- The projection from the category of elements of a sheaf is locally cover-dense for the base
topology. -/
private instance localizationProjection_locallyCoverDense :
    Functor.LocallyCoverDense (localizationProjection ℱ) J := by
  sorry

/-- The projection from the category of elements of a sheaf is locally full for the base
topology. -/
private instance localizationProjection_isLocallyFull :
    Functor.IsLocallyFull (localizationProjection ℱ) J := by
  sorry

/-- The projection from the category of elements of a sheaf is locally faithful for the base
topology. -/
private instance localizationProjection_isLocallyFaithful :
    Functor.IsLocallyFaithful (localizationProjection ℱ) J := by
  sorry

/-- The Grothendieck topology on the category of elements induced from the base site. -/
abbrev localizationTopology (ℱ : Sheaf J (Type v)) : GrothendieckTopology ℱ.obj.Elementsᵒᵖ :=
  Functor.inducedTopology (localizationProjection ℱ) J

local notation "Jₑ" => localizationTopology ℱ

-- Proof sketch: compatible families on the induced topology are exactly the ones obtained by
-- restricting along the projection; continuity then follows from the canonical induced-topology
-- cover-preserving theorem.
private theorem sheafCategoryOfElementsProjection_compatiblePreserving :
    CompatiblePreserving J j := by
  sorry

/-- The localization projection is continuous for the induced topology on the category of
elements. -/
instance localizationProjection_isContinuous :
    Functor.IsContinuous (localizationProjection ℱ) (localizationTopology ℱ) J :=
  Functor.isContinuous_of_coverPreserving
    (sheafCategoryOfElementsProjection_compatiblePreserving ℱ)
    (Functor.inducedTopology_coverPreserving j J)

/-- The localization projection is cocontinuous for the induced topology on the category of
elements. -/
instance localizationProjection_isCocontinuous :
    Functor.IsCocontinuous (localizationProjection ℱ) (localizationTopology ℱ) J :=
  inferInstance

end LocalizationProjection

end CategoryTheory
