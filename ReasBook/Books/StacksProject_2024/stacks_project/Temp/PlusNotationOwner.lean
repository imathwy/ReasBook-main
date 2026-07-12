import Mathlib.CategoryTheory.Sites.Plus
open CategoryTheory Opposite
universe v u
namespace CategoryTheory.GrothendieckTopology
section
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
set_option quotPrecheck false in
scoped notation:max P "⁺" => GrothendieckTopology.plusObj J P
end
end CategoryTheory.GrothendieckTopology
