import StacksProject_2024.stacks_project.Chap06.Definition_6_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite TopologicalSpace

noncomputable section

universe u v

variable {X : Type u} [TopologicalSpace X]
variable {B : Set (Opens X)}

/-- The full subcategory of basis opens containing the point `x`. -/
abbrev BasisOpenNhds (B : Set (Opens X)) (x : X) :=
  ObjectProperty.FullSubcategory fun U : BasisOpen B ↦ x ∈ U.1

/-- The inclusion of basis neighborhoods of `x` into the category of all basis opens. -/
abbrev basisOpenNhdsInclusion (B : Set (Opens X)) (x : X) :
    BasisOpenNhds B x ⥤ BasisOpen B :=
  ObjectProperty.ι fun U : BasisOpen B ↦ x ∈ U.1

/-- The diagram of sections of a basis presheaf over basis opens containing `x`. -/
abbrev basisPresheafStalkDiagram (F : Presheaf.{max u v} (BasisOpen B)) (x : X) :
    (BasisOpenNhds B x)ᵒᵖ ⥤ Type (max u v) :=
  (basisOpenNhdsInclusion B x).op ⋙ F

/-- Stalks as filtered colimits over basis neighbourhoods: the stalk of a basis presheaf at `x` is
the colimit of its values on basis opens in `B` containing `x`. -/
abbrev basisPresheafStalk (F : Presheaf.{max u v} (BasisOpen B)) (x : X) : Type (max u v) :=
  colimit (basisPresheafStalkDiagram F x)

-- Proof sketch: `basisPresheafStalk` is defined to be this colimit, so the statement is
-- definitional after unfolding the abbreviation.
/-- The basis-presheaf stalk is, by definition, the colimit over basis neighborhoods of `x`. -/
theorem basisPresheafStalk_eq_colimit (F : Presheaf.{max u v} (BasisOpen B)) (x : X) :
    basisPresheafStalk F x = colimit (basisPresheafStalkDiagram F x) := sorry
