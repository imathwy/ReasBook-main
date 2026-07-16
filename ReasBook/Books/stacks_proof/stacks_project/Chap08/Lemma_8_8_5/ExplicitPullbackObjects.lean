import stacks_proof.stacks_project.Chap08.Lemma_8_8_5.InertiaCartesian

universe u v

namespace CategoryTheory

open CategoryOver

variable {C : Type u} [Category.{v} C]

/-- Helper for Chap08 Lemma 8 8 5: explicit two-fibre-product objects are determined by the
base, the two underlying endpoint objects, and the underlying comparison arrow. -/
theorem explicitTwoFibreProductObject_ext_underlying
    {X Y S : BasedCategory C} {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    {P Q : ExplicitTwoFibreProductObject F G}
    (hU : P.U = Q.U) (hfst : P.obj.fst.1 = Q.obj.fst.1)
    (hsnd : P.obj.snd.1 = Q.obj.snd.1)
    (hcomp : P.comparison ≍ Q.comparison) :
    P = Q := by
  cases P with
  | mk U obj =>
  cases Q with
  | mk U' obj' =>
  cases hU
  cases obj with
  | mk fst snd iso =>
  cases obj' with
  | mk fst' snd' iso' =>
  dsimp at hfst hsnd hcomp
  cases fst with
  | mk fst hf =>
  cases fst' with
  | mk fst' hf' =>
  cases snd with
  | mk snd hs =>
  cases snd' with
  | mk snd' hs' =>
  dsimp at hfst hsnd hcomp
  cases hfst
  cases hsnd
  dsimp [ExplicitTwoFibreProductObject.comparison] at hcomp
  have hhom : iso.hom = iso'.hom := by
    apply Subtype.ext
    exact HEq.eq hcomp
  have hiso : iso = iso' := by
    ext
    exact congrArg Subtype.val hhom
  cases hiso
  rfl

/-- Helper for Chap08 Lemma 8 8 5: after transporting the source and target objects, a morphism
in an explicit two-fibre product is determined by its two endpoint components. -/
theorem explicitTwoFibreProductHom_transport_eq_of_components
    {X Y S : BasedCategory C} {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    {P Q P' Q' : ExplicitTwoFibreProductObject F G}
    (hP : P = P') (hQ : Q = Q')
    (φ : P ⟶ Q) (ψ : P' ⟶ Q')
    (ha : φ.a = (eqToHom hP ≫ ψ ≫ eqToHom hQ.symm).a)
    (hb : φ.b = (eqToHom hP ≫ ψ ≫ eqToHom hQ.symm).b) :
    φ = eqToHom hP ≫ ψ ≫ eqToHom hQ.symm := by
  -- Reduce the transported morphism equality to the two component equalities supplied by the
  -- caller; the base arrow is forced by the explicit pullback lift conditions.
  apply ExplicitTwoFibreProductHom.ext
  · exact ha
  · exact hb

end CategoryTheory
