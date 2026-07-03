import StacksProject_2024.Chap04.Definition_4_35_6
import StacksProject_2024.Chap04.Lemma_4_33_10

universe u v

namespace CategoryTheory
namespace FibredInGroupoidsOver

open FibredInGroupoidsMor

variable {C : Type u} [Category.{v} C]
variable {X Y S : FibredInGroupoidsOver C}

noncomputable def mkTwoFibreProductSquare
    (F : X ⟶ S) (G : Y ⟶ S)
    (hP : IsFibredInGroupoids (FibredCategoryOver.twoFibreProduct F.toHom G.toHom).p) :
    BicategoricalTwoCommutativeSquare F G :=
  let P := FibredCategoryOver.twoFibreProductSquare F.toHom G.toHom
  { obj := ⟨FibredCategoryOver.twoFibreProduct F.toHom G.toHom, hP⟩
    p := ofAmbientHom P.p
    q := ofAmbientHom P.q
    ψ := by
      exact ofFibredCategoryMorIso P.ψ }

end FibredInGroupoidsOver
end CategoryTheory
