import Mathlib.Topology.Category.TopCat.Basic

universe u

namespace TopCat

/-- The canonical morphism `TopCat.of A ⟶ TopCat.of X` induced by the subtype inclusion
`A ↪ X`. -/
abbrev subtypeInclusion {X : Type u} [TopologicalSpace X] (A : Set X) :
    TopCat.of A ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem subtypeInclusion_apply {X : Type u} [TopologicalSpace X] (A : Set X) (x : A) :
    (subtypeInclusion A).hom x = x :=
  rfl

end TopCat
