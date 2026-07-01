import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open scoped TensorProduct

noncomputable section

universe u v w

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The commutative stalk ring at a point of a site, computed by the point fiber functor. -/
abbrev sourcePointRing (𝒪 : Sheaf J CommRingCat.{w}) (p : GrothendieckTopology.Point.{w} J) :
    CommRingCat.{w} :=
  p.sheafFiber.obj 𝒪

end

section

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (f : D ⥤ C) [Functor.IsContinuous f K J]
variable [((f.sheafPushforwardContinuous CommRingCat K J).IsRightAdjoint)]
variable (𝒪 : Sheaf J CommRingCat.{u}) (𝒪' : Sheaf K CommRingCat.{u})
variable (fSharp : (f.sheafPullback CommRingCat.{u} K J).obj 𝒪' ⟶ 𝒪)
variable (p : GrothendieckTopology.Point.{u} J)
variable (q : GrothendieckTopology.Point.{u} K)

/-- The underlying additive group of the stalk of a sheaf of modules at a site point. -/
abbrev sourcePointModuleCarrier
    (𝒪 : Sheaf J CommRingCat.{u}) (p : GrothendieckTopology.Point.{u} J)
    (M : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) : Type u :=
  ((p.presheafFiber : (Cᵒᵖ ⥤ Ab.{u}) ⥤ Ab.{u})).obj M.val.presheaf

/-- The adjoint-form structure-sheaf map `𝒪' ⟶ f_* 𝒪` corresponding to
`fSharp : f^{-1}𝒪' ⟶ 𝒪`. -/
abbrev adjointStructureMap
    (f : D ⥤ C) [Functor.IsContinuous f K J]
    [((f.sheafPushforwardContinuous CommRingCat K J).IsRightAdjoint)]
    (𝒪 : Sheaf J CommRingCat.{u}) (𝒪' : Sheaf K CommRingCat.{u})
    (fSharp : (f.sheafPullback CommRingCat.{u} K J).obj 𝒪' ⟶ 𝒪) :
    𝒪' ⟶ (f.sheafPushforwardContinuous CommRingCat.{u} K J).obj 𝒪 :=
  ((Adjunction.ofIsRightAdjoint
      (f.sheafPushforwardContinuous CommRingCat.{u} K J)).homEquiv _ _) fSharp

/-- The underlying `RingCat`-valued structure map used by `SheafOfModules.pullback`. -/
abbrev ringedSheafMap
    (f : D ⥤ C) [Functor.IsContinuous f K J]
    [((f.sheafPushforwardContinuous CommRingCat K J).IsRightAdjoint)]
    (𝒪 : Sheaf J CommRingCat.{u}) (𝒪' : Sheaf K CommRingCat.{u})
    (fSharp : (f.sheafPullback CommRingCat.{u} K J).obj 𝒪' ⟶ 𝒪) :
    (sheafCompose K (forget₂ CommRingCat RingCat)).obj 𝒪' ⟶
      (f.sheafPushforwardContinuous RingCat.{u} K J).obj
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪) :=
  (sheafCompose K (forget₂ CommRingCat RingCat)).map
    (adjointStructureMap f 𝒪 𝒪' fSharp)

/-- The ring homomorphism on stalks induced by `fSharp : f^{-1}𝒪' ⟶ 𝒪` and a comparison
between the `q`-fiber and the `p`-fiber of `f^{-1}` on commutative-ring sheaves. -/
abbrev pointStructureRingHom
    (f : D ⥤ C) [Functor.IsContinuous f K J]
    [((f.sheafPushforwardContinuous CommRingCat K J).IsRightAdjoint)]
    (𝒪 : Sheaf J CommRingCat.{u}) (𝒪' : Sheaf K CommRingCat.{u})
    (p : GrothendieckTopology.Point.{u} J)
    (q : GrothendieckTopology.Point.{u} K)
    (hRing : f.sheafPullback CommRingCat.{u} K J ⋙ p.sheafFiber ≅ q.sheafFiber)
    (fSharp : (f.sheafPullback CommRingCat.{u} K J).obj 𝒪' ⟶ 𝒪) :
    sourcePointRing 𝒪' q ⟶ sourcePointRing 𝒪 p :=
  (hRing.inv.app 𝒪') ≫ (p.sheafFiber).map fSharp

-- Proof sketch: rewrite the module pullback as the extension-of-scalars functor attached to the
-- adjoint form of `fSharp`, identify the stalk of `f^{-1}\mathcal F` at `p` with the `q`-stalk of
-- `\mathcal F` via `hRing` and the corresponding fiber comparison on abelian sheaves, and then use
-- that point fibers commute with tensor products.
/-- Lemma 18.36.4: for a site-presented morphism of ringed topoi with inverse-image
structure-sheaf map `fSharp : f^{-1}\mathcal O' ⟶ \mathcal O`, if `hRing` identifies the
`q`-fiber of commutative-ring sheaves with the `p`-fiber after inverse image, then the stalk of
the pullback module at `p` is the scalar extension of the stalk of `\mathcal F` at `q` along the
induced stalk map `\mathcal O'_q \to \mathcal O_p`. -/
theorem pullback_stalk_linearEquiv_tensor
    (hRing : f.sheafPullback CommRingCat.{u} K J ⋙ p.sheafFiber ≅ q.sheafFiber) :
    let _ : Algebra (sourcePointRing 𝒪' q) (sourcePointRing 𝒪 p) :=
      (pointStructureRingHom f 𝒪 𝒪' p q hRing fSharp).hom.toAlgebra
    ∀ (ℱ : SheafOfModules ((sheafCompose K (forget₂ CommRingCat RingCat)).obj 𝒪')),
      [Module (sourcePointRing 𝒪' q) (sourcePointModuleCarrier 𝒪' q ℱ)] →
      [Module (sourcePointRing 𝒪 p)
        (sourcePointModuleCarrier 𝒪 p
          ((SheafOfModules.pullback (ringedSheafMap f 𝒪 𝒪' fSharp)).obj ℱ))] →
      [Module (sourcePointRing 𝒪 p)
        (sourcePointModuleCarrier 𝒪' q ℱ ⊗[(sourcePointRing 𝒪' q)] (sourcePointRing 𝒪 p))] →
      Nonempty
        (sourcePointModuleCarrier 𝒪 p
            ((SheafOfModules.pullback (ringedSheafMap f 𝒪 𝒪' fSharp)).obj ℱ) ≃ₗ[
              sourcePointRing 𝒪 p]
          (sourcePointModuleCarrier 𝒪' q ℱ ⊗[(sourcePointRing 𝒪' q)]
            (sourcePointRing 𝒪 p))) := sorry

end

end CategoryTheory
