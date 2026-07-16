import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Arrows.VerticalFactorUniqueness
import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Functoriality.IdentityPullback

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: the vertical factor of a composite total arrow is the
composite of the first vertical factor, the pullback of the second vertical factor, and the
inverse pullback-composition comparison. -/
theorem stackificationLiftArrowVerticalFactor_comp
    {T T' T'' : S'.S} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    stackificationLiftArrowVerticalFactor (S' := S') (φ ≫ ψ) =
      stackificationLiftArrowVerticalFactor (S' := S') φ ≫
        ((canonicalFiberPseudofunctor S'.p).map (S'.p.map φ).op.toLoc).toFunctor.map
          (stackificationLiftArrowVerticalFactor (S' := S') ψ) ≫
        (mapCompAppIso S'.p (S'.p.map ψ) (S'.p.map φ) (S'.p.map (φ ≫ ψ))
          (FibredCategoryMor.comp_toLoc_eq (S'.p.map ψ) (S'.p.map φ)
            (S'.p.map (φ ≫ ψ)) (by
              simpa using (S'.p.map_comp φ ψ).symm))
          (Functor.Fiber.mk (p := S'.p) (a := T'') rfl : S'.p.Fiber (S'.p.obj T''))).inv := by
  let y₂ : S'.p.Fiber (S'.p.obj T'') :=
    Functor.Fiber.mk (p := S'.p) (a := T'') rfl
  let f := S'.p.map φ
  let g := S'.p.map ψ
  let gf := S'.p.map (φ ≫ ψ)
  let hgf : f ≫ g = gf := by
    dsimp only [f, g, gf]
    simpa using (S'.p.map_comp φ ψ).symm
  let κ := mapCompAppIso S'.p g f gf
    (FibredCategoryMor.comp_toLoc_eq g f gf hgf) y₂
  let vφ := stackificationLiftArrowVerticalFactor (S' := S') φ
  let vψ := stackificationLiftArrowVerticalFactor (S' := S') ψ
  let M := ((canonicalFiberPseudofunctor S'.p).map f.op.toLoc).toFunctor
  let candidate :=
    vφ ≫ M.map vψ ≫ κ.inv
  change stackificationLiftArrowVerticalFactor (S' := S') (φ ≫ ψ) = candidate
  apply stackificationLiftArrowVerticalFactor_eq_of_fac (S' := S') (φ ≫ ψ) candidate
  dsimp only [candidate]
  change (vφ.1 ≫ (M.map vψ).1 ≫ κ.inv.1) ≫
      (canonicalPullbackChoice S'.p).map gf y₂ =
    φ ≫ ψ
  have hκ :
      κ.inv.1 ≫ (canonicalPullbackChoice S'.p).map gf y₂ =
        (canonicalPullbackChoice S'.p).map f
            (g ^*[canonicalPullbackChoice S'.p] y₂) ≫
          (canonicalPullbackChoice S'.p).map g y₂ := by
    simpa [κ, f, g, gf, hgf, y₂] using
      mapCompAppIso_inv_comp_pullbackMap S'.p g f gf hgf y₂
  have hmap :
      (M.map vψ).1 ≫
        (canonicalPullbackChoice S'.p).map f
          (g ^*[canonicalPullbackChoice S'.p] y₂) =
      (canonicalPullbackChoice S'.p).map f
          (Functor.Fiber.mk (p := S'.p) (a := T') rfl : S'.p.Fiber (S'.p.obj T')) ≫
        vψ.1 := by
    dsimp only [M, f, g, y₂, vψ]
    simpa [canonicalFiberPseudofunctor, PullbackChoice.fiberPseudofunctor] using
      (canonicalPullbackChoice S'.p).pullbackFunctor_map_fac (S'.p.map φ)
        (stackificationLiftArrowVerticalFactor (S' := S') ψ)
  have hvφ :
      vφ.1 ≫
        (canonicalPullbackChoice S'.p).map f
          (Functor.Fiber.mk (p := S'.p) (a := T') rfl : S'.p.Fiber (S'.p.obj T')) =
      φ := by
    dsimp only [vφ, f]
    simpa using stackificationLiftArrowVerticalFactor_fac (S' := S') φ
  have hvψ :
      vψ.1 ≫ (canonicalPullbackChoice S'.p).map g y₂ = ψ := by
    dsimp only [vψ, g, y₂]
    simpa using stackificationLiftArrowVerticalFactor_fac (S' := S') ψ
  have hstepκ :
      vφ.1 ≫ (M.map vψ).1 ≫ κ.inv.1 ≫
          (canonicalPullbackChoice S'.p).map gf y₂ =
        vφ.1 ≫ (M.map vψ).1 ≫
          ((canonicalPullbackChoice S'.p).map f
              (g ^*[canonicalPullbackChoice S'.p] y₂) ≫
            (canonicalPullbackChoice S'.p).map g y₂) := by
    simpa only [Category.assoc] using
      congrArg (fun t => vφ.1 ≫ (M.map vψ).1 ≫ t) hκ
  have hstepmap :
      vφ.1 ≫
          ((M.map vψ).1 ≫
            (canonicalPullbackChoice S'.p).map f
              (g ^*[canonicalPullbackChoice S'.p] y₂)) ≫
            (canonicalPullbackChoice S'.p).map g y₂ =
        vφ.1 ≫
          ((canonicalPullbackChoice S'.p).map f
              (Functor.Fiber.mk (p := S'.p) (a := T') rfl : S'.p.Fiber (S'.p.obj T')) ≫
            vψ.1) ≫
          (canonicalPullbackChoice S'.p).map g y₂ := by
    exact congrArg (fun t => vφ.1 ≫ t ≫ (canonicalPullbackChoice S'.p).map g y₂) hmap
  calc
    (vφ.1 ≫ (M.map vψ).1 ≫ κ.inv.1) ≫
        (canonicalPullbackChoice S'.p).map gf y₂ =
      vφ.1 ≫ (M.map vψ).1 ≫
        ((canonicalPullbackChoice S'.p).map f
            (g ^*[canonicalPullbackChoice S'.p] y₂) ≫
          (canonicalPullbackChoice S'.p).map g y₂) := by
        simpa only [Category.assoc] using hstepκ
    _ = vφ.1 ≫
        ((canonicalPullbackChoice S'.p).map f
            (Functor.Fiber.mk (p := S'.p) (a := T') rfl : S'.p.Fiber (S'.p.obj T')) ≫
          vψ.1) ≫
        (canonicalPullbackChoice S'.p).map g y₂ := by
        simpa only [Category.assoc] using hstepmap
    _ = (vφ.1 ≫
        (canonicalPullbackChoice S'.p).map f
          (Functor.Fiber.mk (p := S'.p) (a := T') rfl : S'.p.Fiber (S'.p.obj T'))) ≫
        (vψ.1 ≫ (canonicalPullbackChoice S'.p).map g y₂) := by
        simp only [Category.assoc]
    _ = φ ≫ ψ := by
        rw [hvφ, hvψ]
        rfl

end

end CategoryTheory
