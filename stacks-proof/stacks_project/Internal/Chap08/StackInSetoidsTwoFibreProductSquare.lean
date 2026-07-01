import stacks_project.Internal.Chap08.StackInGroupoidsTwoFibreProductSquare
import stacks_project.Chap08.Definition_8_6_5

universe u v

namespace CategoryTheory
namespace StackInSetoidsOver

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y S : StackInSetoidsOver J}

set_option maxHeartbeats 1000000 in
/-- Restrict an ambient stack-in-groupoids square to the full sub-`2`-category of stacks in
setoids, once its vertex is known to be fibred in setoids. -/
@[irreducible] noncomputable def ofStackInGroupoidsSquare
    {F : X ⟶ S} {G : Y ⟶ S}
    (P : BicategoricalTwoCommutativeSquare F.obj.obj G.obj.obj)
    (hsetoid : IsFibredInSetoids P.obj.p) :
    BicategoricalTwoCommutativeSquare F G :=
  let T : StackInSetoidsOver J := ⟨P.obj, hsetoid⟩
  let p : T ⟶ X := StackInSetoidsOver.ofAmbientHom P.p
  let q : T ⟶ Y := StackInSetoidsOver.ofAmbientHom P.q
  { obj := T
    p := p
    q := q
    ψ := StackInSetoidsOver.ofAmbientHomIso P.ψ }

end StackInSetoidsOver
end CategoryTheory
