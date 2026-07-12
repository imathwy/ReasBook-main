import Mathlib
import StacksProject_2024.Chap18.Lemma_18_36_3

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

/-- Helper for Chap18 Lemma 18 36 4: forget commutativity in the structure sheaf before applying
the module-valued point-stalk functor. -/
abbrev sourceRingSheaf (𝒪 : Sheaf J CommRingCat.{u}) :
    Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪

/-- The underlying additive group of the stalk of a sheaf of modules at a site point. -/
abbrev sourcePointModuleCarrier
    (𝒪 : Sheaf J CommRingCat.{u}) (p : GrothendieckTopology.Point.{u} J)
    (M : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) : Type u :=
  ((p.presheafFiber : (Cᵒᵖ ⥤ Ab.{u}) ⥤ Ab.{u})).obj M.val.presheaf

/-- Helper for Chap18 Lemma 18 36 4: package the raw point-fiber carrier as a `ModuleCat`
object over the corresponding stalk ring. -/
abbrev sourcePointModule
    (𝒪 : Sheaf J CommRingCat.{u}) (p : GrothendieckTopology.Point.{u} J)
    (M : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))
    [Module (sourcePointRing 𝒪 p) (sourcePointModuleCarrier 𝒪 p M)] :
    ModuleCat (sourcePointRing 𝒪 p) :=
  ModuleCat.of (sourcePointRing 𝒪 p) (sourcePointModuleCarrier 𝒪 p M)

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

/-- Helper for Chap18 Lemma 18 36 4: the stalk map used in the theorem is literally the composite
of the comparison on source stalks with the stalk map of `fSharp`. -/
@[simp] lemma pointStructureRingHom_hom
    (f : D ⥤ C) [Functor.IsContinuous f K J]
    [((f.sheafPushforwardContinuous CommRingCat K J).IsRightAdjoint)]
    (𝒪 : Sheaf J CommRingCat.{u}) (𝒪' : Sheaf K CommRingCat.{u})
    (p : GrothendieckTopology.Point.{u} J)
    (q : GrothendieckTopology.Point.{u} K)
    (hRing : f.sheafPullback CommRingCat.{u} K J ⋙ p.sheafFiber ≅ q.sheafFiber)
    (fSharp : (f.sheafPullback CommRingCat.{u} K J).obj 𝒪' ⟶ 𝒪) :
    (pointStructureRingHom f 𝒪 𝒪' p q hRing fSharp).hom =
      ((hRing.inv.app 𝒪') ≫ (p.sheafFiber).map fSharp).hom :=
  rfl

/-- Helper for Chap18 Lemma 18 36 4: the raw stalk carrier is the underlying module of the
canonical module-valued stalk functor. -/
noncomputable def sourcePointModuleCarrierIsoSheafModuleStalk
    (𝒪 : Sheaf J CommRingCat.{u}) (p : GrothendieckTopology.Point.{u} J)
    (M : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))
    [Module (sourcePointRing 𝒪 p) (sourcePointModuleCarrier 𝒪 p M)] :
    sourcePointModule 𝒪 p M ≅
      (p.sheafModuleStalkFunctor (sourceRingSheaf 𝒪)).obj M := by
  -- The source-facing carrier was defined from the same point-fiber colimit as the owner stalk.
  exact (LinearEquiv.refl _ _).toModuleIso

/-- Helper for Chap18 Lemma 18 36 4: `extendScalars` is the usual tensor-product model, and the
result can be presented in the theorem's tensor order by a single tensor swap. -/
noncomputable def extendScalarsTensorLinearEquiv
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (M : ModuleCat R) :
    ((ModuleCat.extendScalars φ).obj M) ≃ₗ[S] (M ⊗[R] S) := by
  let _ : Algebra R S := φ.toAlgebra
  -- `extendScalars φ` is `S ⊗[R] M`; define the swap map and its inverse as `S`-linear lifts.
  let forward :
      ((ModuleCat.extendScalars φ).obj M) →ₗ[S] (M ⊗[R] S) :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun s ↦
          { toFun := fun m ↦ m ⊗ₜ[R] s
            map_add' := fun m₁ m₂ ↦ by simp
            map_smul' := fun r m ↦ by simp [TensorProduct.tmul_smul] }
        map_add' := fun s₁ s₂ ↦ by
          ext m
          simp
        map_smul' := fun s₁ s₂ ↦ by
          ext m
          simp [smul_tmul'] }
  let backward :
      (M ⊗[R] S) →ₗ[S] ((ModuleCat.extendScalars φ).obj M) :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun m ↦
          { toFun := fun s ↦ s ⊗ₜ[R, φ] m
            map_add' := fun s₁ s₂ ↦ by simp
            map_smul' := fun r s ↦ by simp [TensorProduct.smul_tmul'] }
        map_add' := fun m₁ m₂ ↦ by
          ext s
          simp
        map_smul' := fun s m ↦ by
          ext t
          simp [TensorProduct.tmul_smul, mul_comm] }
  refine LinearEquiv.ofLinear forward backward ?_ ?_
  · -- The two lifts are inverse on pure tensors, hence everywhere by tensor extensionality.
    ext s m
    simp [forward, backward]
  · -- The same generator check proves the other composite is the identity.
    ext m s
    simp [forward, backward]

/-- Helper for Chap18 Lemma 18 36 4: owner-level comparison between the stalk of the sheaf pullback
and the stalk of the underlying presheaf pullback. -/
noncomputable def pullbackStalkToPresheafPullbackIso
    (ℱ : SheafOfModules ((sheafCompose K (forget₂ CommRingCat RingCat)).obj 𝒪')) :
    (p.sheafModuleStalkFunctor (sourceRingSheaf 𝒪)).obj
        ((SheafOfModules.pullback (ringedSheafMap f 𝒪 𝒪' fSharp)).obj ℱ) ≅
      (p.presheafModuleStalkFunctor (sourceRingSheaf 𝒪)).obj
        ((PresheafOfModules.pullback (ringedSheafMap f 𝒪 𝒪' fSharp)).obj ℱ.val) := by
  -- First replace the actual sheaf pullback with the sheafified presheaf pullback.
  refine
    (p.sheafModuleStalkFunctor (sourceRingSheaf 𝒪)).mapIso
      ((SheafOfModules.pullbackIso (ringedSheafMap f 𝒪 𝒪' fSharp)).app ℱ) ≪≫ ?_
  -- Then remove the sheafification at the stalk using the canonical comparison from Lemma `18.36.3`.
  exact
    ((p.presheafModuleStalkSheafificationIso (sourceRingSheaf 𝒪)).symm.app
      ((PresheafOfModules.pullback (ringedSheafMap f 𝒪 𝒪' fSharp)).obj ℱ.val))

/-- Helper for Chap18 Lemma 18 36 4: the presheaf-level stalk comparison is the actual base-change
step, after the sheafification transport has been separated out. -/
noncomputable def presheafPullbackStalkIsoExtendScalars
    (hRing : f.sheafPullback CommRingCat.{u} K J ⋙ p.sheafFiber ≅ q.sheafFiber)
    (ℱ : SheafOfModules ((sheafCompose K (forget₂ CommRingCat RingCat)).obj 𝒪')) :
    (p.presheafModuleStalkFunctor (sourceRingSheaf 𝒪)).obj
        ((PresheafOfModules.pullback (ringedSheafMap f 𝒪 𝒪' fSharp)).obj ℱ.val) ≅
      (ModuleCat.extendScalars (pointStructureRingHom f 𝒪 𝒪' p q hRing fSharp).hom).obj
        ((q.sheafModuleStalkFunctor (sourceRingSheaf 𝒪')).obj ℱ) := by
  -- Route correction: after isolating the sheafification transport, the only remaining task is the
  -- presheaf-stalk base-change comparison controlled by `hRing`.
  --
  -- TODO: construct this by either
  -- 1. porting the Chapter 6 `stalkBaseChangeComparison` argument from neighborhood stalks to the
  --    site-point colimit owner `GrothendieckTopology.Point.presheafModuleStalkFunctor`, or
  -- 2. replacing `hRing` by a genuine point-comap identification so that the owner-level
  --    comparison from `Mathlib.CategoryTheory.Sites.Point.Comap` can be applied directly,
  -- and then rewrite the resulting ring map with `pointStructureRingHom_hom`.
  sorry

/-- Helper for Chap18 Lemma 18 36 4: owner-level comparison between the stalk of the sheaf pullback
and extension of scalars of the source stalk. -/
noncomputable def pullbackStalkIsoExtendScalars
    (hRing : f.sheafPullback CommRingCat.{u} K J ⋙ p.sheafFiber ≅ q.sheafFiber)
    (ℱ : SheafOfModules ((sheafCompose K (forget₂ CommRingCat RingCat)).obj 𝒪')) :
    (p.sheafModuleStalkFunctor (sourceRingSheaf 𝒪)).obj
        ((SheafOfModules.pullback (ringedSheafMap f 𝒪 𝒪' fSharp)).obj ℱ) ≅
      (ModuleCat.extendScalars (pointStructureRingHom f 𝒪 𝒪' p q hRing fSharp).hom).obj
        ((q.sheafModuleStalkFunctor (sourceRingSheaf 𝒪')).obj ℱ) := by
  -- Route correction: factor the old monolithic transport into the sheafification-side stalk
  -- comparison and the presheaf-level base-change comparison, then compose them.
  exact
    pullbackStalkToPresheafPullbackIso
      (f := f) (𝒪 := 𝒪) (𝒪' := 𝒪') (fSharp := fSharp) (p := p) (q := q) ℱ ≪≫
    presheafPullbackStalkIsoExtendScalars
      (f := f) (𝒪 := 𝒪) (𝒪' := 𝒪') (fSharp := fSharp) (p := p) (q := q) hRing ℱ

-- Proof sketch: rewrite the module pullback as the extension-of-scalars functor attached to the
-- adjoint form of `fSharp`, identify the stalk of `f^{-1}\mathcal F` at `p` with the `q`-stalk of
-- `\mathcal F` via `hRing` and the corresponding fiber comparison on abelian sheaves, and then use
-- that point fibers commute with tensor products.
/-- Lemma 18.36.4: for a site-presented morphism of ringed topoi with inverse-image
structure-sheaf map `fSharp : f^{-1}\mathcal O' ⟶ \mathcal O`, if `hRing` identifies the
`q`-fiber of commutative-ring sheaves with the `p`-fiber after inverse image, then the stalk of
the pullback module at `p` is the scalar extension of the stalk of `\mathcal F` at `q` along the
induced stalk map `\mathcal O'_q \to \mathcal O_p`. -/
@[stacks 05V5]
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
            (sourcePointRing 𝒪 p))) := by
  intro ℱ _ _ _
  -- Move from the raw source-facing stalk carrier to the canonical module-valued stalk object.
  let eSource :=
    sourcePointModuleCarrierIsoSheafModuleStalk 𝒪 p
      ((SheafOfModules.pullback (ringedSheafMap f 𝒪 𝒪' fSharp)).obj ℱ)
  -- Apply the owner-level pullback/base-change comparison.
  let ePullback := pullbackStalkIsoExtendScalars
    (f := f) (𝒪 := 𝒪) (𝒪' := 𝒪') (fSharp := fSharp) (p := p) (q := q) hRing ℱ
  -- Replace `extendScalars` by the theorem's tensor-product presentation.
  let eTensor :=
    (extendScalarsTensorLinearEquiv
      ((pointStructureRingHom f 𝒪 𝒪' p q hRing fSharp).hom)
      ((q.sheafModuleStalkFunctor (sourceRingSheaf 𝒪')).obj ℱ)).toModuleIso
  -- The remaining transports are definitional wrappers around the same stalk carriers.
  refine ⟨?_⟩
  simpa [sourcePointModule, sourcePointModuleCarrier] using
    (eSource ≪≫ ePullback ≪≫ eTensor).toLinearEquiv

end

end CategoryTheory
