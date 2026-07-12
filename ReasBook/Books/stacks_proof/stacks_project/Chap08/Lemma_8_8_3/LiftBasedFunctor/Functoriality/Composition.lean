import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.Functoriality.CompositionCore

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: the descended arrow formula respects composition of total
arrows. -/
theorem stackificationLiftBasedFunctorMap_comp
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {T T' T'' : S'.S} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    stackificationLiftBasedFunctorMap X G hG F (φ ≫ ψ) =
      stackificationLiftBasedFunctorMap X G hG F φ ≫
        stackificationLiftBasedFunctorMap X G hG F ψ := by
  let y₁ : S'.p.Fiber (S'.p.obj T') :=
    Functor.Fiber.mk (p := S'.p) (a := T') rfl
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
  have hcore := stackificationLiftBasedFunctorMapCore_comp X G hG F φ ψ
  dsimp only at hcore
  rw [stackificationLiftBasedFunctorMap_eq_core_comp_cart]
  rw [stackificationLiftBasedFunctorMap_eq_core_comp_cart X G hG F φ]
  rw [stackificationLiftBasedFunctorMap_eq_core_comp_cart X G hG F ψ]
  rw [hcore]
  let coreφ := stackificationLiftBasedFunctorMapCore X G hG F φ
  let coreψ := stackificationLiftBasedFunctorMapCore X G hG F ψ
  let z₁ := stackificationLiftObjectGlued X G hG F y₁
  let z₂ := stackificationLiftObjectGlued X G hG F y₂
  let Mx := ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor
  let cartFz₁ := (canonicalPullbackChoice X.p).map f z₁
  let cartGz₂ := (canonicalPullbackChoice X.p).map g z₂
  let cartFGz₂ := (canonicalPullbackChoice X.p).map f
    (g ^*[canonicalPullbackChoice X.p] z₂)
  let cartGFz₂ := (canonicalPullbackChoice X.p).map gf z₂
  have hκ :
      κX.inv.1 ≫ cartGFz₂ = cartFGz₂ ≫ cartGz₂ := by
    dsimp [κX, cartGFz₂, cartFGz₂, cartGz₂, z₂]
    simpa [f, g, gf, y₂, hgf] using
      mapCompAppIso_inv_comp_pullbackMap X.p g f gf hgf
        (stackificationLiftObjectGlued X G hG F y₂)
  have hmap :
      (Mx.map coreψ).1 ≫ cartFGz₂ = cartFz₁ ≫ coreψ.1 := by
    dsimp [Mx, coreψ, cartFGz₂, cartFz₁, z₁, z₂]
    simpa [canonicalFiberPseudofunctor, PullbackChoice.fiberPseudofunctor, f, g, y₁, y₂] using
      (canonicalPullbackChoice X.p).pullbackFunctor_map_fac f
        (stackificationLiftBasedFunctorMapCore X G hG F ψ)
  change (coreφ.1 ≫ (Mx.map coreψ).1 ≫ κX.inv.1) ≫ cartGFz₂ =
    (coreφ.1 ≫ cartFz₁) ≫ coreψ.1 ≫ cartGz₂
  calc
    (coreφ.1 ≫ (Mx.map coreψ).1 ≫ κX.inv.1) ≫ cartGFz₂ =
        coreφ.1 ≫ (Mx.map coreψ).1 ≫ (κX.inv.1 ≫ cartGFz₂) := by
          simp only [Category.assoc]
    _ = coreφ.1 ≫ (Mx.map coreψ).1 ≫ (cartFGz₂ ≫ cartGz₂) := by
          exact congrArg (fun t => coreφ.1 ≫ (Mx.map coreψ).1 ≫ t) hκ
    _ = coreφ.1 ≫ ((Mx.map coreψ).1 ≫ cartFGz₂) ≫ cartGz₂ := by
          simp only [Category.assoc]
    _ = coreφ.1 ≫ (cartFz₁ ≫ coreψ.1) ≫ cartGz₂ := by
          exact congrArg (fun t => coreφ.1 ≫ t ≫ cartGz₂) hmap
    _ = (coreφ.1 ≫ cartFz₁) ≫ coreψ.1 ≫ cartGz₂ := by
          simp only [Category.assoc]

end

end CategoryTheory
