import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Category.Preorder
import stacks_project.Chap04.Definition_4_2_15

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

section

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I]
variable {M N : I ⥤ ModuleCat R}

/- Definition 10.8.6: a homomorphism of systems of `R`-modules over the same preordered set `I`
is exactly a natural transformation `M ⟶ N`, i.e. the specialization of Categories,
Definition 4.2.15 to the functor category from the preorder `I` to `ModuleCat R`. Its primitive
data are the component morphisms `Φ.app i : M.obj i ⟶ N.obj i`; compatibility with transition maps
is derived from naturality. -/
#check (M ⟶ N)

/-- Companion bridge: the components of a morphism of module systems commute with the transition
maps. This is the naturality square of `Φ` specialized to the unique morphism `homOfLE h : i ⟶ j`
in the preorder category `I`. -/
-- Proof sketch: unfold `CommSq` and apply the naturality identity of the natural transformation
-- `Φ` at the preorder morphism `homOfLE h`.
theorem module_system_hom_naturality
    (Φ : M ⟶ N) {i j : I} (h : i ≤ j) :
    CommSq (M.map (homOfLE h)) (Φ.app i) (Φ.app j) (N.map (homOfLE h)) := sorry

end

end CategoryTheory
