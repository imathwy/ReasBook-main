import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_32_8

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced the ring-level tensor-product theorem
-- `KaehlerDifferential.tensorKaehlerEquiv`. Local Chapter 29 precedent uses the scheme-level
-- owners `Ω[f.toShHom]` and the comparison maps characterized by Lemma 29.32.8, so this item is
-- stated as the induced biproduct map for the two canonical projection comparisons.

/-- Helper for Lemma 29.32.11: the comparison map from the first projection sends universal
relative differentials on `X` to their pullbacks on `X ×_S Y`. -/
private def productLeftRelativeDifferentialsMapSpec
    (f : X ⟶ S) (g : Y ⟶ S)
    (τX : (RingedSpace.Hom.pullback (pullback.fst f g).toShHom).obj Ω[f.toShHom] ⟶
      Ω[(pullback.snd f g ≫ g).toShHom]) : Prop :=
  ∀ {U : (Opens X)ᵒᵖ} (t : X.presheaf.obj U),
    let U' := (Opens.map (pullback.fst f g).base).op.obj U
    let φp := (pullback.fst f g).toRingCatSheafHom
    let pSharpU := φp.hom.app U
    ((((SheafOfModules.pullbackPushforwardAdjunction
          φp).homEquiv _ _)
        τX).val.app U)
      (((d[f.toShHom]).app U).d t) =
      ((d[(pullback.snd f g ≫ g).toShHom]).app U').d (pSharpU t)

/-- Helper for Lemma 29.32.11: the comparison map from the second projection sends universal
relative differentials on `Y` to their pullbacks on `X ×_S Y`. -/
private def productRightRelativeDifferentialsMapSpec
    (f : X ⟶ S) (g : Y ⟶ S)
    (τY : (RingedSpace.Hom.pullback (pullback.snd f g).toShHom).obj Ω[g.toShHom] ⟶
      Ω[(pullback.snd f g ≫ g).toShHom]) : Prop :=
  ∀ {V : (Opens Y)ᵒᵖ} (t : Y.presheaf.obj V),
    let V' := (Opens.map (pullback.snd f g).base).op.obj V
    let φq := (pullback.snd f g).toRingCatSheafHom
    let qSharpV := φq.hom.app V
    ((((SheafOfModules.pullbackPushforwardAdjunction
          φq).homEquiv _ _)
        τY).val.app V)
      (((d[g.toShHom]).app V).d t) =
      ((d[(pullback.snd f g ≫ g).toShHom]).app V').d (qSharpV t)

/-- Lemma 29.32.11: for morphisms of schemes `f : X ⟶ S` and `g : Y ⟶ S`, with
projections `p : X ×_S Y ⟶ X` and `q : X ×_S Y ⟶ Y`, the two comparison maps supplied by
Lemma 29.32.8 induce an isomorphism
`p^* Ω_{X/S} ⊕ q^* Ω_{Y/S} ⟶ Ω_{X ×_S Y/S}`. The target morphism
`X ×_S Y ⟶ S` is represented by `q ≫ g`, equivalently by `p ≫ f`. -/
@[stacks 01V1]
theorem isIso_biprodDesc_schemePullbackDifferentialsProduct
    (f : X ⟶ S) (g : Y ⟶ S)
    (τX : (RingedSpace.Hom.pullback (pullback.fst f g).toShHom).obj Ω[f.toShHom] ⟶
      Ω[(pullback.snd f g ≫ g).toShHom])
    (τY : (RingedSpace.Hom.pullback (pullback.snd f g).toShHom).obj Ω[g.toShHom] ⟶
      Ω[(pullback.snd f g ≫ g).toShHom])
    (_hτX : productLeftRelativeDifferentialsMapSpec f g τX)
    (_hτY : productRightRelativeDifferentialsMapSpec f g τY) :
    IsIso
      (biprod.desc τX τY :
        ((RingedSpace.Hom.pullback (pullback.fst f g).toShHom).obj Ω[f.toShHom] ⊞
          (RingedSpace.Hom.pullback (pullback.snd f g).toShHom).obj Ω[g.toShHom]) ⟶
          Ω[(pullback.snd f g ≫ g).toShHom]) := sorry

end AlgebraicGeometry
