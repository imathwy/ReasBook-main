import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomCartesianPointwiseComposition

universe u v uX vX

namespace CategoryTheory

open Bicategory
open FibredCategoryMor
open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace FibredCategoryMor
namespace LocallyDefinedHomTotal
namespace SameCoverLocalFactorization

set_option linter.unnecessarySimpa false in
set_option linter.unusedSimpArgs false in
set_option backward.isDefEq.respectTransparency false in
/-- For an arbitrary local factor representative `beta`, composing with the ordinary
representative of `phi` and then postcomposing with the canonical cartesian target arrow is the
same as postcomposing the local component of `beta` with the cartesian arrow to `x` and then with
`phi`.

This is the cancellation-facing version of the composite calculation used for the pointwise
factor. -/
theorem composeOver_ordinary_family_postcomp
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    ⦃x y z : X.S⦄ (phi : x ⟶ y)
    (g : X.p.obj z ⟶ X.p.obj x)
    (beta : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (LocallyDefinedHomRepresentativeOver.compositionCover (J := J) beta
      (ordinaryHomToRepresentativeOver (J := J) X phi)).Arrow) :
    let Fp := canonicalFiberPseudofunctor X.p
    let hc := canonicalPullbackChoice X.p
    let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
    let yF : X.p.Fiber (X.p.obj y) := Functor.Fiber.mk (p := X.p) (a := y) rfl
    let gxF : X.p.Fiber (X.p.obj z) := (Fp.map g.op.toLoc).toFunctor.obj xF
    let gyF : X.p.Fiber (X.p.obj z) := (Fp.map (g ≫ X.p.map phi).op.toLoc).toFunctor.obj yF
    let i : I.Y.left ⟶ X.p.obj z := I.Y.hom
    let betaLocal := (beta.family
      (LocallyDefinedHomRepresentativeOver.compositionCoverToLeft (J := J) beta
        (ordinaryHomToRepresentativeOver (J := J) X phi) I)).down
    let compLocal := ((LocallyDefinedHomRepresentativeOver.composeOver (J := J) beta
      (ordinaryHomToRepresentativeOver (J := J) X phi)).family I).down
    compLocal.1 ≫ hc.map i gyF ≫ hc.map (g ≫ X.p.map phi) yF =
      betaLocal.1 ≫ hc.map i gxF ≫ hc.map g xF ≫ phi := by
  intro Fp hc xF yF gxF gyF i betaLocal compLocal
  let ord := ordinaryHomToRepresentativeOver (J := J) X phi
  let phiyF : X.p.Fiber (X.p.obj x) := (Fp.map (X.p.map phi).op.toLoc).toFunctor.obj yF
  let M := (LocallyDefinedHomRepresentativeOver.compositionMiddleIso (J := J) beta ord I).hom
  let N := (LocallyDefinedHomRepresentativeOver.compositionRightLocal (J := J) beta ord I).down
  let T := LocallyDefinedHomRepresentativeOver.compositionTargetHom (J := J) beta ord I
  have hM : M.1 ≫ hc.map (i ≫ g) xF = hc.map i gxF ≫ hc.map g xF := by
    have hraw := LocallyDefinedHomRepresentativeOver.compositionMiddleIso_hom_fac
      (J := J) beta ord I
    dsimp only at hraw
    simpa [M, ord, Fp, hc, xF, i, gxF] using hraw
  have hT : T.1 ≫ hc.map i gyF ≫ hc.map (g ≫ X.p.map phi) yF =
      hc.map (i ≫ g) phiyF ≫ hc.map (X.p.map phi) yF := by
    have hraw := LocallyDefinedHomRepresentativeOver.compositionTargetHom_fac
      (J := J) beta ord I
    dsimp only at hraw
    simpa [T, ord, Fp, hc, yF, gyF, phiyF, i, Category.assoc] using hraw
  have hN : N.1 ≫ hc.map (i ≫ g) phiyF ≫ hc.map (X.p.map phi) yF =
      hc.map (i ≫ g) xF ≫ phi := by
    have hraw := ordinaryHomToRepresentativeOver_family_cartesian_fac
      (J := J) X phi
      (LocallyDefinedHomRepresentativeOver.compositionCoverToRight (J := J) beta ord I)
    dsimp only at hraw
    simpa [N, ord, Fp, hc, xF, yF, phiyF, i,
      LocallyDefinedHomRepresentative.compositionCoverToRight_hom, Category.assoc] using hraw
  have hNT : N.1 ≫ T.1 ≫ hc.map i gyF ≫ hc.map (g ≫ X.p.map phi) yF =
      hc.map (i ≫ g) xF ≫ phi := by
    calc
      N.1 ≫ T.1 ≫ hc.map i gyF ≫ hc.map (g ≫ X.p.map phi) yF
          = N.1 ≫ (T.1 ≫ hc.map i gyF ≫ hc.map (g ≫ X.p.map phi) yF) := by
            simp [Category.assoc]
      _ = N.1 ≫ (hc.map (i ≫ g) phiyF ≫ hc.map (X.p.map phi) yF) := by
            rw [hT]
      _ = N.1 ≫ hc.map (i ≫ g) phiyF ≫ hc.map (X.p.map phi) yF := by
            simp [Category.assoc]
      _ = hc.map (i ≫ g) xF ≫ phi := hN
  have htail : M.1 ≫ N.1 ≫ T.1 ≫ hc.map i gyF ≫ hc.map (g ≫ X.p.map phi) yF =
      hc.map i gxF ≫ hc.map g xF ≫ phi := by
    calc
      M.1 ≫ N.1 ≫ T.1 ≫ hc.map i gyF ≫ hc.map (g ≫ X.p.map phi) yF
          = M.1 ≫
              (N.1 ≫ T.1 ≫ hc.map i gyF ≫ hc.map (g ≫ X.p.map phi) yF) := by
            simp [Category.assoc]
      _ = M.1 ≫ (hc.map (i ≫ g) xF ≫ phi) := by
            rw [hNT]
      _ = (M.1 ≫ hc.map (i ≫ g) xF) ≫ phi := by
            simp [Category.assoc]
      _ = (hc.map i gxF ≫ hc.map g xF) ≫ phi := by
            rw [hM]
      _ = hc.map i gxF ≫ hc.map g xF ≫ phi := by
            simp [Category.assoc]
  change (betaLocal.1 ≫ M.1 ≫ N.1 ≫ T.1) ≫
      hc.map i gyF ≫ hc.map (g ≫ X.p.map phi) yF =
    betaLocal.1 ≫ hc.map i gxF ≫ hc.map g xF ≫ phi
  calc
    (betaLocal.1 ≫ M.1 ≫ N.1 ≫ T.1) ≫
        hc.map i gyF ≫ hc.map (g ≫ X.p.map phi) yF
        = betaLocal.1 ≫
            (M.1 ≫ N.1 ≫ T.1 ≫ hc.map i gyF ≫
              hc.map (g ≫ X.p.map phi) yF) := by
          simp [Category.assoc]
    _ = betaLocal.1 ≫ (hc.map i gxF ≫ hc.map g xF ≫ phi) := by
          rw [htail]
    _ = betaLocal.1 ≫ hc.map i gxF ≫ hc.map g xF ≫ phi := by
          simp [Category.assoc]

set_option linter.unnecessarySimpa false in
set_option linter.unusedSimpArgs false in
set_option backward.isDefEq.respectTransparency false in
/-- Postcomposition with an ordinary strongly cartesian arrow is faithful on raw locally-defined
representatives, up to the common-refinement equivalence. -/
theorem composeOver_ordinary_cartesian_cancel
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    ⦃x y z : X.S⦄ (phi : x ⟶ y)
    (hphi : X.p.IsStronglyCartesian (X.p.map phi) phi)
    (g : X.p.obj z ⟶ X.p.obj x)
    (beta beta' : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (hcomp :
      LocallyDefinedHomRepresentativeOver.Equivalent (J := J)
        (LocallyDefinedHomRepresentativeOver.composeOver (J := J) beta'
          (ordinaryHomToRepresentativeOver (J := J) X phi))
        (LocallyDefinedHomRepresentativeOver.composeOver (J := J) beta
          (ordinaryHomToRepresentativeOver (J := J) X phi))) :
    LocallyDefinedHomRepresentativeOver.Equivalent (J := J) beta' beta := by
  let ord := ordinaryHomToRepresentativeOver (J := J) X phi
  let compβ' := LocallyDefinedHomRepresentativeOver.composeOver (J := J) beta' ord
  let compβ := LocallyDefinedHomRepresentativeOver.composeOver (J := J) beta ord
  rcases hcomp with ⟨W, hcompβ', hcompβ, hW⟩
  let hβ' : W ⟶ beta'.cover := homOfLE (by
    intro Y k hk
    exact (LocallyDefinedHomRepresentativeOver.compositionCoverToLeft (J := J) beta' ord
      ⟨Y, k, (leOfHom hcompβ') _ hk⟩).hf)
  let hβ : W ⟶ beta.cover := homOfLE (by
    intro Y k hk
    exact (LocallyDefinedHomRepresentativeOver.compositionCoverToLeft (J := J) beta ord
      ⟨Y, k, (leOfHom hcompβ) _ hk⟩).hf)
  refine ⟨W, hβ', hβ, ?_⟩
  apply Meq.ext
  intro I
  let Iβ' : (LocallyDefinedHomRepresentativeOver.compositionCover (J := J) beta' ord).Arrow :=
    ⟨I.Y, I.f, (leOfHom hcompβ') _ I.hf⟩
  let Iβ : (LocallyDefinedHomRepresentativeOver.compositionCover (J := J) beta ord).Arrow :=
    ⟨I.Y, I.f, (leOfHom hcompβ) _ I.hf⟩
  let b' := (beta'.family
    (LocallyDefinedHomRepresentativeOver.compositionCoverToLeft (J := J) beta' ord Iβ')).down
  let b := (beta.family
    (LocallyDefinedHomRepresentativeOver.compositionCoverToLeft (J := J) beta ord Iβ)).down
  let c' := (compβ'.family Iβ').down
  let c := (compβ.family Iβ).down
  have hfamily := congrArg (fun m : Meq (locallyDefinedHomSaturatedPresheaf X
      (g ≫ X.p.map phi)) W => m I) hW
  have hcEq : c'.1 = c.1 := by
    have hdown := congrArg (fun t => (ULift.down t).1) hfamily
    simpa [compβ', compβ, c', c, Iβ', Iβ] using hdown
  apply ULift.ext
  change b' = b
  apply Functor.Fiber.hom_ext
  let Fp := canonicalFiberPseudofunctor X.p
  let hc := canonicalPullbackChoice X.p
  let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
  let yF : X.p.Fiber (X.p.obj y) := Functor.Fiber.mk (p := X.p) (a := y) rfl
  let gxF : X.p.Fiber (X.p.obj z) := (Fp.map g.op.toLoc).toFunctor.obj xF
  let gyF : X.p.Fiber (X.p.obj z) := (Fp.map (g ≫ X.p.map phi).op.toLoc).toFunctor.obj yF
  let i : I.Y.left ⟶ X.p.obj z := I.Y.hom
  let cartX : ((Fp.map i.op.toLoc).toFunctor.obj gxF).1 ⟶ x :=
    hc.map i gxF ≫ hc.map g xF
  let cartPhi : ((Fp.map i.op.toLoc).toFunctor.obj gxF).1 ⟶ y :=
    cartX ≫ phi
  let cartAll : ((Fp.map i.op.toLoc).toFunctor.obj gyF).1 ⟶ y :=
    hc.map i gyF ≫ hc.map (g ≫ X.p.map phi) yF
  have hcartI : X.p.IsStronglyCartesian i (hc.map i gxF) := by
    simpa [i, gxF, Fp, hc] using hc.isStronglyCartesian i gxF
  have hcartG : X.p.IsStronglyCartesian g (hc.map g xF) := by
    simpa [gxF, Fp, hc] using hc.isStronglyCartesian g xF
  have hcartX : X.p.IsStronglyCartesian (i ≫ g) cartX := by
    letI : X.p.IsStronglyCartesian i (hc.map i gxF) := hcartI
    letI : X.p.IsStronglyCartesian g (hc.map g xF) := hcartG
    simpa [cartX] using
      (inferInstance : X.p.IsStronglyCartesian (i ≫ g)
        ((hc.map i gxF) ≫ hc.map g xF))
  have hcartPhi : X.p.IsStronglyCartesian ((i ≫ g) ≫ X.p.map phi) cartPhi := by
    letI : X.p.IsStronglyCartesian (i ≫ g) cartX := hcartX
    letI : X.p.IsStronglyCartesian (X.p.map phi) phi := hphi
    simpa [cartPhi] using
      (inferInstance : X.p.IsStronglyCartesian ((i ≫ g) ≫ X.p.map phi) (cartX ≫ phi))
  have hpost' : c'.1 ≫ cartAll = b'.1 ≫ cartPhi := by
    have hraw := composeOver_ordinary_family_postcomp (J := J) phi g beta' Iβ'
    dsimp only at hraw
    simpa [ord, compβ', c', b', Fp, hc, xF, yF, gxF, gyF, i, cartX, cartPhi, cartAll,
      Category.assoc] using hraw
  have hpost : c.1 ≫ cartAll = b.1 ≫ cartPhi := by
    have hraw := composeOver_ordinary_family_postcomp (J := J) phi g beta Iβ
    dsimp only at hraw
    simpa [ord, compβ, c, b, Fp, hc, xF, yF, gxF, gyF, i, cartX, cartPhi, cartAll,
      Category.assoc] using hraw
  have hpostEq : b'.1 ≫ cartPhi = b.1 ≫ cartPhi := by
    calc
      b'.1 ≫ cartPhi = c'.1 ≫ cartAll := hpost'.symm
      _ = c.1 ≫ cartAll := by rw [hcEq]
      _ = b.1 ≫ cartPhi := hpost
  change b'.1 = b.1
  refine @Functor.IsStronglyCartesian.ext C X.S _ _ X.p _ _ _ _
    ((i ≫ g) ≫ X.p.map phi) cartPhi hcartPhi
    _ _ (𝟙 I.Y.left) b'.1 b.1 ?_ ?_ ?_
  · exact b'.2
  · exact b.2
  · simpa [cartPhi, Category.assoc] using hpostEq

set_option backward.isDefEq.respectTransparency false in
/-- The raw same-cover uniqueness statement for source stage 2.6. -/
theorem pointwiseLocalFactor_sameCoverUniqueness
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    ⦃x y z : X.S⦄ (phi : x ⟶ y)
    (hphi : X.p.IsStronglyCartesian (X.p.map phi) phi)
    (g : X.p.obj z ⟶ X.p.obj x)
    (alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi))
    (beta beta' : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (hbeta :
      LocallyDefinedHomRepresentativeOver.Equivalent (J := J)
        (LocallyDefinedHomRepresentativeOver.composeOver (J := J) beta
          (ordinaryHomToRepresentativeOver (J := J) X phi))
        alpha)
    (hbeta' :
      LocallyDefinedHomRepresentativeOver.Equivalent (J := J)
        (LocallyDefinedHomRepresentativeOver.composeOver (J := J) beta'
          (ordinaryHomToRepresentativeOver (J := J) X phi))
        alpha) :
    LocallyDefinedHomRepresentativeOver.Equivalent (J := J) beta' beta := by
  have hcomp :
      LocallyDefinedHomRepresentativeOver.Equivalent (J := J)
        (LocallyDefinedHomRepresentativeOver.composeOver (J := J) beta'
          (ordinaryHomToRepresentativeOver (J := J) X phi))
        (LocallyDefinedHomRepresentativeOver.composeOver (J := J) beta
          (ordinaryHomToRepresentativeOver (J := J) X phi)) :=
    LocallyDefinedHomRepresentativeOver.equivalent_trans (J := J) hbeta'
      (LocallyDefinedHomRepresentativeOver.equivalent_symm (J := J) hbeta)
  exact composeOver_ordinary_cartesian_cancel (J := J) phi hphi g beta beta' hcomp

end SameCoverLocalFactorization
end LocallyDefinedHomTotal
end FibredCategoryMor

end CategoryTheory
