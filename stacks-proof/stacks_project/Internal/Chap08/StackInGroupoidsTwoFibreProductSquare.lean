import stacks_project.Chap04.Lemma_4_35_7
import stacks_project.Chap08.Definition_8_5_5

universe u v

namespace CategoryTheory
namespace StackInGroupoidsOver

open StackInGroupoidsOver.Hom

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y S : StackInGroupoidsOver J}

/-- Restrict an ambient fibred-in-groupoids square to the full sub-`2`-category of stacks in
groupoids, once its vertex is known to be a stack on the site. -/
@[irreducible] noncomputable def ofFibredInGroupoidsSquare
    {F : X ⟶ S} {G : Y ⟶ S}
    (P : BicategoricalTwoCommutativeSquare F.toHom G.toHom)
    (hstack : IsStackOnSite J P.obj.p) :
    BicategoricalTwoCommutativeSquare F G :=
  let T : StackInGroupoidsOver J := ⟨P.obj, hstack⟩
  let p : T ⟶ X := StackInGroupoidsOver.ofAmbientHom P.p
  let q : T ⟶ Y := StackInGroupoidsOver.ofAmbientHom P.q
  { obj := T
    p := p
    q := q
    ψ := StackInGroupoidsOver.Hom.ofAmbientHomIso P.ψ }

@[irreducible] noncomputable def mkTwoFibreProductSquare
    (F : X ⟶ S) (G : Y ⟶ S)
    (hstack :
      IsStackOnSite J
        (FibredCategoryOver.twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p) :
    BicategoricalTwoCommutativeSquare F G :=
  let P := FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom
  ofFibredInGroupoidsSquare P (by
    change IsStackOnSite J
      (FibredCategoryOver.twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p
    exact hstack)

end StackInGroupoidsOver
end CategoryTheory
