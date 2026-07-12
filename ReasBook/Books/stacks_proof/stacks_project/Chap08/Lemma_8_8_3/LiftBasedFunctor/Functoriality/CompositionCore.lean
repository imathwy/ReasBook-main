import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.FunctorialityCore
import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.Arrows.CompositionFactor
import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.CompositionCocycle

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Core composition formula for the descended arrow before the final chosen cartesian arrow is
appended. -/
theorem stackificationLiftBasedFunctorMapCore_comp
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {T T' T'' : S'.S} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    let y₂ : S'.p.Fiber (S'.p.obj T'') :=
      Functor.Fiber.mk (p := S'.p) (a := T'') rfl
    let f := S'.p.map φ
    let g := S'.p.map ψ
    let gf := S'.p.map (φ ≫ ψ)
    let hgf : f ≫ g = gf := by
      dsimp only [f, g, gf]
      simpa using (S'.p.map_comp φ ψ).symm
    let κX := mapCompAppIso X.p g f gf
      (FibredCategoryMor.comp_toLoc_eq g f gf hgf)
      (stackificationLiftObjectGlued X G hG F y₂)
    stackificationLiftBasedFunctorMapCore X G hG F (φ ≫ ψ) =
      stackificationLiftBasedFunctorMapCore X G hG F φ ≫
        ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
          (stackificationLiftBasedFunctorMapCore X G hG F ψ) ≫
        κX.inv := by
  intro y₂ f g gf hgf κX
  let κS := mapCompAppIso S'.p g f gf
    (FibredCategoryMor.comp_toLoc_eq g f gf hgf) y₂
  dsimp [stackificationLiftBasedFunctorMapCore]
  rw [stackificationLiftArrowVerticalFactor_comp]
  let vφ := stackificationLiftArrowVerticalFactor (S' := S') φ
  let vψ := stackificationLiftArrowVerticalFactor (S' := S') ψ
  let MfS := ((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor
  change stackificationLiftVerticalMap X G hG F (vφ ≫ MfS.map vψ ≫ κS.inv) ≫
      (stackificationLiftArrowPullbackObjectComparison X G hG F (φ ≫ ψ)).hom =
    (stackificationLiftVerticalMap X G hG F vφ ≫
        (stackificationLiftArrowPullbackObjectComparison X G hG F φ).hom) ≫
      ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
          (stackificationLiftVerticalMap X G hG F vψ ≫
            (stackificationLiftArrowPullbackObjectComparison X G hG F ψ).hom) ≫
        κX.inv
  rw [show vφ ≫ MfS.map vψ ≫ κS.inv = vφ ≫ (MfS.map vψ ≫ κS.inv) by rfl]
  rw [stackificationLiftVerticalMap_comp X G hG F vφ (MfS.map vψ ≫ κS.inv)]
  erw [stackificationLiftVerticalMap_comp X G hG F (MfS.map vψ) κS.inv]
  simp only [Functor.map_comp, Category.assoc]
  rw [stackificationLiftObjectPullbackComparison_verticalMap]
  have hcocycle :=
    stackificationLiftObjectPullbackComparison_comp_inv X G hG F f g gf hgf y₂
  dsimp only [stackificationLiftArrowPullbackObjectComparison,
    stackificationLiftArrowPullbackTarget] at hcocycle ⊢
  let A := stackificationLiftVerticalMap X G hG F vφ
  let B := (stackificationLiftObjectPullbackComparison X G hG F f
    (Functor.Fiber.mk (p := S'.p) (a := T') rfl)).hom
  let Cmap := ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
    (stackificationLiftVerticalMap X G hG F vψ)
  let D := (stackificationLiftObjectPullbackComparison X G hG F f
    (g ^*[canonicalPullbackChoice S'.p] y₂)).inv
  let E := stackificationLiftVerticalMap X G hG F κS.inv
  let H := (stackificationLiftObjectPullbackComparison X G hG F gf y₂).hom
  let K := ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
    (stackificationLiftObjectPullbackComparison X G hG F g y₂).hom
  let L := κX.inv
  change A ≫ (((B ≫ Cmap ≫ D) ≫ E) ≫ H) =
    A ≫ B ≫ ((Cmap ≫ K) ≫ L)
  have hDEH : D ≫ E ≫ H = K ≫ L := by
    simpa only [D, E, H, K, L] using hcocycle
  calc
    A ≫ (((B ≫ Cmap ≫ D) ≫ E) ≫ H) =
        A ≫ B ≫ Cmap ≫ (D ≫ E ≫ H) := by
          simp only [Category.assoc]
    _ = A ≫ B ≫ Cmap ≫ (K ≫ L) := by
          exact congrArg (fun t => A ≫ B ≫ Cmap ≫ t) hDEH
    _ = A ≫ B ≫ ((Cmap ≫ K) ≫ L) := by
          simp only [Category.assoc]

end

end CategoryTheory
