import Mathlib
import StacksProject_2024.stacks_project.Chap34.Definition_34_9_10
import StacksProject_2024.stacks_project.Chap34.Definition_34_9_13

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/- Semantic recall for this item:
`lean_leansearch` surfaced the canonical sheaf owners `Scheme.zariskiTopology` and
`CategoryTheory.Presheaf.IsSheaf`. Local Chapter 34 precedent already fixes the fixed-family owner
at `satisfiesSheafPropertyForFamily`, and standard fpqc coverings are represented by
`StandardFpqcCover`. The affine faithfully flat singleton test is therefore the `PUnit`-indexed
singleton family attached to a flat surjective morphism between affine schemes. -/

/-- A contravariant set-valued functor on schemes satisfies the sheaf property for Zariski
coverings when it is a sheaf for the canonical big Zariski topology on schemes. -/
abbrev satisfiesZariskiSheafProperty (F : Schemeᵒᵖ ⥤ Type v) : Prop :=
  Presheaf.IsSheaf Scheme.zariskiTopology F

/-- A contravariant set-valued functor on schemes satisfies the sheaf property for standard fpqc
coverings when it satisfies the fixed-family sheaf condition for every standard fpqc covering of
an affine scheme. -/
abbrev satisfiesStandardFpqcSheafProperty (F : Schemeᵒᵖ ⥤ Type v) : Prop :=
  ∀ {T : Scheme.{u}} (hT : IsAffine T) (𝒰 : StandardFpqcCover T),
    satisfiesSheafPropertyForFamily F 𝒰.U 𝒰.map

/-- A contravariant set-valued functor on schemes satisfies the affine faithfully-flat singleton
sheaf condition when it satisfies the fixed-family sheaf condition for every singleton family
`{V ⟶ U}` with `U` and `V` affine and `V ⟶ U` flat and surjective. -/
abbrev satisfiesAffineFaithfullyFlatSingletonSheafProperty
    (F : Schemeᵒᵖ ⥤ Type v) : Prop :=
  ∀ {U V : Scheme.{u}} (f : V ⟶ U) [IsAffine U] [IsAffine V] [Flat f] [Surjective f],
    satisfiesSheafPropertyForFamily F (fun _ : Unit ↦ V) (fun _ ↦ f)

/-- Lemma 34.9.14 (1): a contravariant set-valued functor on schemes satisfies the sheaf property
for the fpqc topology if and only if it satisfies the sheaf property for Zariski coverings and for
every standard fpqc covering of an affine scheme. -/
theorem satisfiesFpqcSheafProperty_iff_zariski_and_standardFpqc
    (F : Schemeᵒᵖ ⥤ Type v) :
    satisfiesFpqcSheafProperty F ↔
      satisfiesZariskiSheafProperty F ∧
        satisfiesStandardFpqcSheafProperty F := sorry

/-- Lemma 34.9.14 (2): assuming the Zariski sheaf condition, the sheaf property for every
standard fpqc covering is equivalent to the sheaf property for each singleton family `{V ⟶ U}`
with `U` and `V` affine and `V ⟶ U` flat and surjective. -/
theorem satisfiesStandardFpqcSheafProperty_iff_affineFaithfullyFlatSingleton
    (F : Schemeᵒᵖ ⥤ Type v)
    (hzar : satisfiesZariskiSheafProperty F) :
    satisfiesStandardFpqcSheafProperty F ↔
      satisfiesAffineFaithfullyFlatSingletonSheafProperty F := sorry

end AlgebraicGeometry
