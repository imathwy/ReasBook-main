import StacksProject_2024.Chap08.Lemma_8_11_5.FiberIso
import StacksProject_2024.Chap08.Lemma_8_11_5.StackPullback

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackInGroupoidsOver.Hom

/-- Helper for Lemma 8.11.5: a comparison map between two final stack `2`-fibre product squares
is an equivalence on the apex over the base. -/
theorem apexMap_isEquivalenceOverBase_of_final_squares
    {A B S : StackInGroupoidsOver J}
    {F : A ⟶ S} {G : B ⟶ S}
    (P Q : BicategoricalTwoCommutativeSquare F G)
    (hP : Bicategory.IsFinal P)
    (hQ : Bicategory.IsFinal Q)
    (u : Q ⟶ P) :
    u.hom.IsEquivalenceOverBase := by
  letI : Bicategory.IsFinal P := hP
  letI : Bicategory.IsFinal Q := hQ
  let v : P ⟶ Q := ⊤_ (P ⟶ Q)
  let ηsq : (𝟙 Q : Q ⟶ Q) ≅ u ≫ v := by
    exact asIso ((Bicategory.IsFinal.homIsTerminal (x := Q) (y := Q) (f := u ≫ v)).from (𝟙 Q))
  let εsq : v ≫ u ≅ (𝟙 P : P ⟶ P) := by
    exact asIso ((Bicategory.IsFinal.homIsTerminal (x := P) (y := P) (f := 𝟙 P)).from (v ≫ u))
  let η : ((𝟙 Q.obj : Q.obj ⟶ Q.obj) ≅ u.hom ≫ v.hom) := asIso ηsq.hom.hom
  let ε : (v.hom ≫ u.hom ≅ (𝟙 P.obj : P.obj ⟶ P.obj)) := asIso εsq.hom.hom
  -- The terminal comparison isomorphisms provide the based quasi-inverse data for the apex map.
  change BasedFunctor.IsEquivalenceOverBase u.hom.toBasedFunctor
  refine BasedFunctor.IsEquivalenceOverBase.mkPrime v.hom.toBasedFunctor ?_ ?_
  · change (𝟙 Q.obj.toBasedCategory) ≅
      BasedFunctor.comp u.hom.toBasedFunctor v.hom.toBasedFunctor
    simpa [BasedFunctor.comp] using basedFunctorIsoOfStackHomIso (J := J) η
  · change BasedFunctor.comp v.hom.toBasedFunctor u.hom.toBasedFunctor ≅
      (𝟙 P.obj.toBasedCategory)
    simpa [BasedFunctor.comp] using basedFunctorIsoOfStackHomIso (J := J) ε


end StackInGroupoidsOver.Hom

end

end CategoryTheory
