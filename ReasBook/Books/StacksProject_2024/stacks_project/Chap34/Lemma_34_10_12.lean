import Mathlib
import StacksProject_2024.stacks_project.Chap34.Definition_34_10_11
import StacksProject_2024.stacks_project.Chap34.Lemma_34_10_4
import StacksProject_2024.stacks_project.Chap34.Definition_34_10_1
import StacksProject_2024.stacks_project.Chap34.Lemma_34_9_14

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

namespace AffineFamilyOver

/-- The singleton affine family over `U` attached to a single morphism `f : V ⟶ U` with affine
source. -/
def singleton {U V : Scheme.{u}} (f : V ⟶ U) (hV : IsAffine V) : AffineFamilyOver U where
  n := 1
  U := fun _ ↦ V
  map := fun _ ↦ f
  isAffine := fun _ ↦ hV

@[simp] theorem singleton_map {U V : Scheme.{u}} (f : V ⟶ U) (hV : IsAffine V) (j : Fin 1) :
    (singleton f hV).map j = f :=
  rfl

end AffineFamilyOver

/- Semantic recall for this item:
`lean_leansearch` surfaced the canonical sheaf owners `Scheme.zariskiTopology` and
`CategoryTheory.Presheaf.IsSheaf`. Local Chapter 34 precedent already packages the Zariski clause
as `satisfiesZariskiSheafProperty`, the full `V`-topology clause as `satisfiesVSheafProperty`,
and standard `V` coverings as `AffineFamilyOver` with `IsStandardVCover`; the source is therefore
best split into the same two iff-statements as the fpqc analogue in `Lemma_34_9_14`. -/

/-- The fixed-family sheaf condition for a finite affine family over a scheme. -/
abbrev satisfiesSheafPropertyForAffineFamily
    (F : Schemeᵒᵖ ⥤ Type v) {T : Scheme.{u}} (𝒰 : AffineFamilyOver T) : Prop :=
  satisfiesSheafPropertyForFamily F 𝒰.U 𝒰.map

/-- A contravariant set-valued functor on schemes satisfies the sheaf property for standard `V`
coverings when it satisfies the fixed-family sheaf condition for every standard `V` covering of an
affine scheme. -/
abbrev satisfiesStandardVSheafProperty (F : Schemeᵒᵖ ⥤ Type v) : Prop :=
  ∀ {T : Scheme.{u}} (_ : IsAffine T) (𝒰 : AffineFamilyOver T),
    AffineFamilyOver.IsStandardVCover 𝒰 → satisfiesSheafPropertyForAffineFamily F 𝒰

/-- A contravariant set-valued functor on schemes satisfies the singleton standard `V` sheaf
condition when it satisfies the fixed-family sheaf condition for every standard `V` covering of
the form `{V ⟶ U}` with `U` and `V` affine. -/
abbrev satisfiesStandardVSingletonSheafProperty (F : Schemeᵒᵖ ⥤ Type v) : Prop :=
  ∀ {U V : Scheme.{u}} (_ : IsAffine U) (hV : IsAffine V) (f : V ⟶ U),
    AffineFamilyOver.IsStandardVCover (AffineFamilyOver.singleton f hV) →
      satisfiesSheafPropertyForAffineFamily F (AffineFamilyOver.singleton f hV)

/-- Lemma 34.10.12 (1): a contravariant set-valued functor on schemes satisfies the sheaf
property for the `V` topology if and only if it satisfies the sheaf property for Zariski coverings
and for every standard `V` covering of an affine scheme. -/
@[stacks 0ETM]
theorem satisfiesVSheafProperty_iff_zariski_and_standardV
    (F : Schemeᵒᵖ ⥤ Type v) :
    satisfiesVSheafProperty F ↔
      satisfiesZariskiSheafProperty F ∧ satisfiesStandardVSheafProperty F := sorry

/-- Lemma 34.10.12 (2): assuming the Zariski sheaf condition, the sheaf property for every
standard `V` covering of an affine scheme is equivalent to the sheaf property for each standard
`V` covering of the form `{V ⟶ U}` consisting of a single arrow. -/
@[stacks 0ETM]
theorem satisfiesStandardVSheafProperty_iff_singleton
    (F : Schemeᵒᵖ ⥤ Type v)
    (hzar : satisfiesZariskiSheafProperty F) :
    satisfiesStandardVSheafProperty F ↔
      satisfiesStandardVSingletonSheafProperty F := sorry

end AlgebraicGeometry
