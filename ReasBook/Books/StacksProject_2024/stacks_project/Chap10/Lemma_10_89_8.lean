import StacksProject_2024.stacks_project.Chap10.Definition_10_88_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

namespace CategoryTheory.ShortComplex

section

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}

-- Proof sketch: for any family `(Q a)`, tensor the exact sequence `S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` with
-- `∀ a, Q a` and compare it to the product of the exact sequences obtained by tensoring with each
-- `Q a`. Proposition `10.89.2` makes the left vertical map surjective because `S.X₁` is finite,
-- and Proposition `10.89.5` makes the middle vertical map injective because `S.X₂` is
-- Mittag-Leffler. A diagram chase gives injectivity on the right vertical map, and Proposition
-- `10.89.5` then shows that `S.X₃` is Mittag-Leffler.
/-- Lemma 10.89.8: if `S : ShortComplex (ModuleCat R)` is exact, `S.g` is surjective, `S.X₁` is
finite, and `S.X₂` is Mittag-Leffler, then `S.X₃` is Mittag-Leffler. -/
theorem mittagLeffler_X₃_of_exact_of_finite_of_mittagLeffler
    (hS : S.Exact) (hSurj : Function.Surjective S.g) [Module.Finite R S.X₁]
    [Module.MittagLeffler R S.X₂] :
    Module.MittagLeffler R S.X₃ := sorry

end

end CategoryTheory.ShortComplex
