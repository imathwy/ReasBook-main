import StacksProject_2024.stacks_project.Chap04.Definition_4_39_3
import StacksProject_2024.stacks_project.Chap04.Lemma_4_35_7

universe u v

namespace CategoryTheory

open CategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y S : FibredInSetoidsOver C}

private noncomputable abbrev explicitTwoFibreProductOver
    (F : X ⟶ S) (G : Y ⟶ S) :=
  explicitTwoFibreProduct
    (FibredInSetoidsOver.toBasedFunctor F)
    (FibredInSetoidsOver.toBasedFunctor G)

/-- If `F : X ⟶ S` and `G : Y ⟶ S` are morphisms of categories fibred in setoids over `C`, then
the explicit `2`-fibre-product projection is again fibred in setoids. -/
theorem explicitTwoFibreProductProjection_isFibredInSetoids
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsFibredInSetoids (explicitTwoFibreProductOver F G).p := by
  sorry

instance (F : X ⟶ S) (G : Y ⟶ S) :
    IsFibredInSetoids (explicitTwoFibreProductOver F G).p :=
  explicitTwoFibreProductProjection_isFibredInSetoids F G

namespace FibredInSetoidsOver

private noncomputable abbrev ambientTwoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    FibredInGroupoidsOver C :=
  FibredInGroupoidsOver.twoFibreProduct F.toHom G.toHom

private theorem ambientTwoFibreProduct_isFibredInSetoids
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsFibredInSetoids (ambientTwoFibreProduct F G).p := by
  change IsFibredInSetoids (explicitTwoFibreProductOver F G).p
  exact explicitTwoFibreProductProjection_isFibredInSetoids F G

/-- The canonical fibred `2`-fibre product of morphisms of categories fibred in setoids over
`C`, obtained by rebundling the chapter-level owner `FibredInGroupoidsOver.twoFibreProduct`
inside `FibredInSetoidsOver C`. -/
noncomputable abbrev twoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    FibredInSetoidsOver C :=
  ⟨ambientTwoFibreProduct F G, ambientTwoFibreProduct_isFibredInSetoids F G⟩

end FibredInSetoidsOver

end CategoryTheory
