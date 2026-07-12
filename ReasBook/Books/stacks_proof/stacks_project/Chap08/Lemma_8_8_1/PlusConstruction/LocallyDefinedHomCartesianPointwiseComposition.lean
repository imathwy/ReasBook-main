import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomCartesianPointwise

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

set_option backward.isDefEq.respectTransparency false in
/-- Restricting the trivial-cover representative of an ordinary arrow and then composing with the
chosen cartesian target map recovers the ordinary arrow after the source restriction. -/
theorem ordinaryHomToRepresentativeOver_family_cartesian_fac
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y : X.S} (a : x ⟶ y)
    (I : (ordinaryHomToRepresentativeOver (J := J) X a).cover.Arrow) :
    let Fp := canonicalFiberPseudofunctor X.p
    let hc := canonicalPullbackChoice X.p
    let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
    let yF : X.p.Fiber (X.p.obj y) := Functor.Fiber.mk (p := X.p) (a := y) rfl
    let ayF : X.p.Fiber (X.p.obj x) := (Fp.map (X.p.map a).op.toLoc).toFunctor.obj yF
    ((ordinaryHomToRepresentativeOver (J := J) X a).family I).down.1 ≫
        hc.map I.Y.hom ayF ≫ hc.map (X.p.map a) yF =
      hc.map I.Y.hom xF ≫ a := by
  intro Fp hc xF yF ayF
  let ordPull := ordinaryHomToPullbackFiberHom X a
  have hdown := ordinaryHomToRepresentativeOver_family_apply_down (J := J) X a I
  have hmap :
      (((Fp.map I.Y.hom.op.toLoc).toFunctor.map ordPull).1) ≫
          hc.map I.Y.hom ayF =
        hc.map I.Y.hom xF ≫ ordPull.1 := by
    simpa [Fp, hc, xF, yF, ayF, ordPull] using
      (canonical_pullbackFunctor_map_fac (p := X.p) I.Y.hom ordPull)
  calc
    ((ordinaryHomToRepresentativeOver (J := J) X a).family I).down.1 ≫
        hc.map I.Y.hom ayF ≫ hc.map (X.p.map a) yF
        = (((Fp.map I.Y.hom.op.toLoc).toFunctor.map ordPull).1) ≫
            hc.map I.Y.hom ayF ≫ hc.map (X.p.map a) yF := by
          rw [hdown]
    _ = (hc.map I.Y.hom xF ≫ ordPull.1) ≫ hc.map (X.p.map a) yF := by
          simpa [Category.assoc] using
            congrArg (fun t => t ≫ hc.map (X.p.map a) yF) hmap
    _ = hc.map I.Y.hom xF ≫ (ordPull.1 ≫ hc.map (X.p.map a) yF) := by
          simp [Category.assoc]
    _ = hc.map I.Y.hom xF ≫ a := by
          rw [ordinaryHomToPullbackFiberHom_fac X a]

namespace LocallyDefinedHomRepresentativeOver

set_option backward.isDefEq.respectTransparency false in
/-- The middle comparison in the local composite is the inverse canonical pullback-composition
map, hence it factors through the one-step pullback arrow. -/
theorem compositionMiddleIso_hom_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (compositionCover (J := J) α β).Arrow) :
    let Fp := canonicalFiberPseudofunctor X.p
    let hc := canonicalPullbackChoice X.p
    let yF : X.p.Fiber (X.p.obj y) := Functor.Fiber.mk (p := X.p) (a := y) rfl
    ((compositionMiddleIso (J := J) α β I).hom).1 ≫
        hc.map (I.Y.hom ≫ f) yF =
      hc.map I.Y.hom ((Fp.map f.op.toLoc).toFunctor.obj yF) ≫ hc.map f yF := by
  intro Fp hc yF
  simpa [Fp, hc, yF, compositionMiddleIso, Category.assoc] using
    (canonicalFiberPseudofunctor_mapComp'_inv_app_fac
      (p := X.p) f I.Y.hom (I.Y.hom ≫ f) (by rfl) yF)

set_option backward.isDefEq.respectTransparency false in
/-- The target comparison in the local composite factors through the canonical cartesian target
for the composite base arrow. -/
theorem compositionTargetHom_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (compositionCover (J := J) α β).Arrow) :
    let Fp := canonicalFiberPseudofunctor X.p
    let hc := canonicalPullbackChoice X.p
    let zF : X.p.Fiber (X.p.obj z) := Functor.Fiber.mk (p := X.p) (a := z) rfl
    let gzF : X.p.Fiber (X.p.obj y) := (Fp.map g.op.toLoc).toFunctor.obj zF
    let fgzF : X.p.Fiber (X.p.obj x) := (Fp.map (f ≫ g).op.toLoc).toFunctor.obj zF
    (compositionTargetHom (J := J) α β I).1 ≫
        hc.map I.Y.hom fgzF ≫ hc.map (f ≫ g) zF =
      hc.map (I.Y.hom ≫ f) gzF ≫ hc.map g zF := by
  intro Fp hc zF gzF fgzF
  let A := (Fp.mapComp' f.op.toLoc I.Y.hom.op.toLoc ((I.Y.hom ≫ f).op.toLoc)
    (by rfl)).hom.toNatTrans.app gzF
  let B := (Fp.map I.Y.hom.op.toLoc).toFunctor.map
      ((Fp.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app zF)
  have hB :
      B.1 ≫ hc.map I.Y.hom fgzF =
        hc.map I.Y.hom ((Fp.map f.op.toLoc).toFunctor.obj gzF) ≫
          ((Fp.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app zF).1 := by
    simpa [B, Fp, hc, zF, gzF, fgzF] using
      (canonical_pullbackFunctor_map_fac (p := X.p) I.Y.hom
        ((Fp.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app zF))
  have hInv :
      ((Fp.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app zF).1 ≫
          hc.map (f ≫ g) zF =
        hc.map f gzF ≫ hc.map g zF := by
    rw [← Pseudofunctor.mapComp'_eq_mapComp Fp g.op.toLoc f.op.toLoc]
    simpa [Fp, hc, zF, gzF, Category.assoc] using
      (canonicalFiberPseudofunctor_mapComp'_inv_app_fac
        (p := X.p) g f (f ≫ g) (by rfl) zF)
  have hA :
      A.1 ≫ hc.map I.Y.hom ((Fp.map f.op.toLoc).toFunctor.obj gzF) ≫
          hc.map f gzF =
        hc.map (I.Y.hom ≫ f) gzF := by
    simpa [A, Fp, hc, zF, gzF, Category.assoc] using
      (canonicalFiberPseudofunctor_mapComp'_hom_app_fac
        (p := X.p) f I.Y.hom (I.Y.hom ≫ f) (by rfl) gzF)
  change (A.1 ≫ B.1) ≫ hc.map I.Y.hom fgzF ≫ hc.map (f ≫ g) zF =
    hc.map (I.Y.hom ≫ f) gzF ≫ hc.map g zF
  calc
    (A.1 ≫ B.1) ≫ hc.map I.Y.hom fgzF ≫ hc.map (f ≫ g) zF
        = A.1 ≫ (B.1 ≫ hc.map I.Y.hom fgzF) ≫ hc.map (f ≫ g) zF := by
          simp [Category.assoc]
    _ = A.1 ≫ (hc.map I.Y.hom ((Fp.map f.op.toLoc).toFunctor.obj gzF) ≫
          ((Fp.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app zF).1) ≫
          hc.map (f ≫ g) zF := by
          rw [hB]
    _ = A.1 ≫ hc.map I.Y.hom ((Fp.map f.op.toLoc).toFunctor.obj gzF) ≫
          (((Fp.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app zF).1 ≫
            hc.map (f ≫ g) zF) := by
          simp [Category.assoc]
    _ = A.1 ≫ hc.map I.Y.hom ((Fp.map f.op.toLoc).toFunctor.obj gzF) ≫
          (hc.map f gzF ≫ hc.map g zF) := by
          rw [hInv]
    _ = (A.1 ≫ hc.map I.Y.hom ((Fp.map f.op.toLoc).toFunctor.obj gzF) ≫
          hc.map f gzF) ≫ hc.map g zF := by
          simp [Category.assoc]
    _ = hc.map (I.Y.hom ≫ f) gzF ≫ hc.map g zF := by
          rw [hA]

end LocallyDefinedHomRepresentativeOver

namespace LocallyDefinedHomTotal
namespace SameCoverLocalFactorization

set_option linter.unnecessarySimpa false in
set_option linter.unusedSimpArgs false in
set_option backward.isDefEq.respectTransparency false in
/-- On the composition cover of the constructed same-cover factor and the ordinary
representative of `phi`, the local composite is exactly the original local representative of
`alpha`. -/
theorem pointwiseLocalFactor_comp_family_apply
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    ⦃x y z : X.S⦄ (phi : x ⟶ y)
    (hphi : X.p.IsStronglyCartesian (X.p.map phi) phi)
    (g : X.p.obj z ⟶ X.p.obj x)
    (alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi))
    (hcompatible :
      ∀ R : alpha.cover.Relation,
        (locallyDefinedHomSaturatedPresheaf X g).map R.r.g₁.op
            (pointwiseLocalFactor (J := J) phi hphi g alpha (alpha.cover.shape.fst R)) =
          (locallyDefinedHomSaturatedPresheaf X g).map R.r.g₂.op
            (pointwiseLocalFactor (J := J) phi hphi g alpha (alpha.cover.shape.snd R)))
    (I : (LocallyDefinedHomRepresentativeOver.compositionCover (J := J)
      ({ cover := alpha.cover
         family := ⟨fun I => pointwiseLocalFactor (J := J) phi hphi g alpha I,
           hcompatible⟩ } :
        LocallyDefinedHomRepresentativeOver (J := J) X g)
      (ordinaryHomToRepresentativeOver (J := J) X phi)).Arrow) :
    (LocallyDefinedHomRepresentativeOver.composeOver (J := J)
      ({ cover := alpha.cover
         family := ⟨fun I => pointwiseLocalFactor (J := J) phi hphi g alpha I,
           hcompatible⟩ } :
        LocallyDefinedHomRepresentativeOver (J := J) X g)
      (ordinaryHomToRepresentativeOver (J := J) X phi)).family I =
      alpha.family (LocallyDefinedHomRepresentativeOver.compositionCoverToLeft (J := J)
        ({ cover := alpha.cover
           family := ⟨fun I => pointwiseLocalFactor (J := J) phi hphi g alpha I,
             hcompatible⟩ } :
          LocallyDefinedHomRepresentativeOver (J := J) X g)
        (ordinaryHomToRepresentativeOver (J := J) X phi) I) := by
  let betaRep : LocallyDefinedHomRepresentativeOver (J := J) X g :=
    { cover := alpha.cover
      family := ⟨fun I => pointwiseLocalFactor (J := J) phi hphi g alpha I, hcompatible⟩ }
  let ord := ordinaryHomToRepresentativeOver (J := J) X phi
  let leftI := LocallyDefinedHomRepresentativeOver.compositionCoverToLeft (J := J) betaRep ord I
  let rightI := LocallyDefinedHomRepresentativeOver.compositionCoverToRight (J := J) betaRep ord I
  rw [LocallyDefinedHomRepresentativeOver.composeOver_family_apply]
  apply ULift.ext
  change (LocallyDefinedHomRepresentativeOver.compositionLocal (J := J) betaRep ord I).down =
    (alpha.family leftI).down
  apply Functor.Fiber.hom_ext
  let Fp := canonicalFiberPseudofunctor X.p
  let hc := canonicalPullbackChoice X.p
  let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
  let yF : X.p.Fiber (X.p.obj y) := Functor.Fiber.mk (p := X.p) (a := y) rfl
  let gxF : X.p.Fiber (X.p.obj z) := (Fp.map g.op.toLoc).toFunctor.obj xF
  let gyF : X.p.Fiber (X.p.obj z) := (Fp.map (g ≫ X.p.map phi).op.toLoc).toFunctor.obj yF
  let phiyF : X.p.Fiber (X.p.obj x) := (Fp.map (X.p.map phi).op.toLoc).toFunctor.obj yF
  let i : I.Y.left ⟶ X.p.obj z := I.Y.hom
  let L := (LocallyDefinedHomRepresentativeOver.compositionLeftLocal (J := J) betaRep ord I).down
  let M := (LocallyDefinedHomRepresentativeOver.compositionMiddleIso (J := J) betaRep ord I).hom
  let N := (LocallyDefinedHomRepresentativeOver.compositionRightLocal (J := J) betaRep ord I).down
  let T := LocallyDefinedHomRepresentativeOver.compositionTargetHom (J := J) betaRep ord I
  let alphaLocal := (alpha.family leftI).down
  let cartAll : ((Fp.map i.op.toLoc).toFunctor.obj gyF).1 ⟶ y :=
    hc.map i gyF ≫ hc.map (g ≫ X.p.map phi) yF
  have hcartI : X.p.IsStronglyCartesian i (hc.map i gyF) := by
    simpa [i, gyF, Fp, hc] using hc.isStronglyCartesian i gyF
  have hcartRest : X.p.IsStronglyCartesian (g ≫ X.p.map phi)
      (hc.map (g ≫ X.p.map phi) yF) := by
    simpa [gyF, Fp, hc] using hc.isStronglyCartesian (g ≫ X.p.map phi) yF
  have hcartAll : X.p.IsStronglyCartesian (i ≫ (g ≫ X.p.map phi)) cartAll := by
    letI : X.p.IsStronglyCartesian i (hc.map i gyF) := hcartI
    letI : X.p.IsStronglyCartesian (g ≫ X.p.map phi)
      (hc.map (g ≫ X.p.map phi) yF) := hcartRest
    simpa [cartAll] using
      (inferInstance : X.p.IsStronglyCartesian (i ≫ (g ≫ X.p.map phi))
        ((hc.map i gyF) ≫ hc.map (g ≫ X.p.map phi) yF))
  have hM : M.1 ≫ hc.map (i ≫ g) xF = hc.map i gxF ≫ hc.map g xF := by
    have hraw := LocallyDefinedHomRepresentativeOver.compositionMiddleIso_hom_fac
      (J := J) betaRep ord I
    dsimp only at hraw
    simpa [M, betaRep, ord, Fp, hc, xF, i, gxF] using hraw
  have hT : T.1 ≫ hc.map i gyF ≫ hc.map (g ≫ X.p.map phi) yF =
      hc.map (i ≫ g) phiyF ≫ hc.map (X.p.map phi) yF := by
    have hraw := LocallyDefinedHomRepresentativeOver.compositionTargetHom_fac
      (J := J) betaRep ord I
    dsimp only at hraw
    simpa [T, betaRep, ord, Fp, hc, yF, gyF, phiyF, i, Category.assoc] using hraw
  have hN : N.1 ≫ hc.map (i ≫ g) phiyF ≫ hc.map (X.p.map phi) yF =
      hc.map (i ≫ g) xF ≫ phi := by
    have hraw := ordinaryHomToRepresentativeOver_family_cartesian_fac
      (J := J) X phi rightI
    dsimp only at hraw
    simpa [N, rightI, betaRep, ord, Fp, hc, xF, yF, phiyF, i,
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
  have hcomp : (LocallyDefinedHomRepresentativeOver.compositionLocal (J := J) betaRep ord I).down.1 ≫
      cartAll = L.1 ≫ hc.map i gxF ≫ hc.map g xF ≫ phi := by
    change (L.1 ≫ M.1 ≫ N.1 ≫ T.1) ≫ cartAll =
      L.1 ≫ hc.map i gxF ≫ hc.map g xF ≫ phi
    calc
      (L.1 ≫ M.1 ≫ N.1 ≫ T.1) ≫ cartAll
          = L.1 ≫
              (M.1 ≫ N.1 ≫ T.1 ≫ hc.map i gyF ≫ hc.map (g ≫ X.p.map phi) yF) := by
            simp [cartAll, Category.assoc]
      _ = L.1 ≫ (hc.map i gxF ≫ hc.map g xF ≫ phi) := by
            rw [htail]
      _ = L.1 ≫ hc.map i gxF ≫ hc.map g xF ≫ phi := by
            simp [Category.assoc]
  have hpoint := pointwiseLocalFactor_fac_cartesian (J := J) phi hphi g alpha leftI
  dsimp only at hpoint
  have hpost : (LocallyDefinedHomRepresentativeOver.compositionLocal (J := J) betaRep ord I).down.1 ≫
      cartAll = alphaLocal.1 ≫ cartAll := by
    calc
      (LocallyDefinedHomRepresentativeOver.compositionLocal (J := J) betaRep ord I).down.1 ≫
          cartAll
          = L.1 ≫ hc.map i gxF ≫ hc.map g xF ≫ phi := hcomp
      _ = alphaLocal.1 ≫ cartAll := by
          simpa [L, alphaLocal, leftI, betaRep, Fp, hc, xF, yF, gxF, gyF, i, cartAll,
            Category.assoc] using hpoint
  change (LocallyDefinedHomRepresentativeOver.compositionLocal (J := J) betaRep ord I).down.1 =
    alphaLocal.1
  refine @Functor.IsStronglyCartesian.ext C X.S _ _ X.p _ _ _ _
    (i ≫ (g ≫ X.p.map phi)) cartAll hcartAll
    _ _ (𝟙 I.Y.left)
    (LocallyDefinedHomRepresentativeOver.compositionLocal (J := J) betaRep ord I).down.1
    alphaLocal.1 ?_ ?_ ?_
  · exact (LocallyDefinedHomRepresentativeOver.compositionLocal (J := J) betaRep ord I).down.2
  · exact alphaLocal.2
  · simpa [Category.assoc] using hpost

set_option backward.isDefEq.respectTransparency false in
/-- The pointwise factor family, composed with the ordinary representative of `phi`, represents
the original locally-defined morphism on a common refinement. -/
theorem pointwiseLocalFactor_comp_equivalent_of_compatible
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    ⦃x y z : X.S⦄ (phi : x ⟶ y)
    (hphi : X.p.IsStronglyCartesian (X.p.map phi) phi)
    (g : X.p.obj z ⟶ X.p.obj x)
    (alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi))
    (hcompatible :
      ∀ R : alpha.cover.Relation,
        (locallyDefinedHomSaturatedPresheaf X g).map R.r.g₁.op
            (pointwiseLocalFactor (J := J) phi hphi g alpha (alpha.cover.shape.fst R)) =
          (locallyDefinedHomSaturatedPresheaf X g).map R.r.g₂.op
            (pointwiseLocalFactor (J := J) phi hphi g alpha (alpha.cover.shape.snd R))) :
    LocallyDefinedHomRepresentativeOver.Equivalent (J := J)
      (LocallyDefinedHomRepresentativeOver.composeOver (J := J)
        ({ cover := alpha.cover
           family := ⟨fun I => pointwiseLocalFactor (J := J) phi hphi g alpha I,
             hcompatible⟩ } :
          LocallyDefinedHomRepresentativeOver (J := J) X g)
        (ordinaryHomToRepresentativeOver (J := J) X phi))
      alpha := by
  let betaRep : LocallyDefinedHomRepresentativeOver (J := J) X g :=
    { cover := alpha.cover
      family := ⟨fun I => pointwiseLocalFactor (J := J) phi hphi g alpha I, hcompatible⟩ }
  let ord := ordinaryHomToRepresentativeOver (J := J) X phi
  let comp := LocallyDefinedHomRepresentativeOver.composeOver (J := J) betaRep ord
  let hcompToAlpha : comp.cover ⟶ alpha.cover := homOfLE (by
    intro Y k hk
    exact (LocallyDefinedHomRepresentativeOver.compositionCoverToLeft (J := J) betaRep ord
      ⟨Y, k, hk⟩).hf)
  refine ⟨comp.cover, 𝟙 comp.cover, hcompToAlpha, ?_⟩
  apply Meq.ext
  intro I
  change comp.family I =
    alpha.family ⟨I.Y, I.f, (leOfHom hcompToAlpha) _ I.hf⟩
  simpa [comp, hcompToAlpha, betaRep, ord] using
    pointwiseLocalFactor_comp_family_apply (J := J) phi hphi g alpha hcompatible I

set_option backward.isDefEq.respectTransparency false in
/-- The constructed pointwise factor family has the required composite representative. -/
theorem pointwiseLocalFactor_comp_equivalent
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    ⦃x y z : X.S⦄ (phi : x ⟶ y)
    (hphi : X.p.IsStronglyCartesian (X.p.map phi) phi)
    (g : X.p.obj z ⟶ X.p.obj x)
    (alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi)) :
    LocallyDefinedHomRepresentativeOver.Equivalent (J := J)
      (LocallyDefinedHomRepresentativeOver.composeOver (J := J)
        ({ cover := alpha.cover
           family := ⟨fun I => pointwiseLocalFactor (J := J) phi hphi g alpha I,
             pointwiseLocalFactor_compatible (J := J) phi hphi g alpha⟩ } :
          LocallyDefinedHomRepresentativeOver (J := J) X g)
        (ordinaryHomToRepresentativeOver (J := J) X phi))
      alpha :=
  pointwiseLocalFactor_comp_equivalent_of_compatible (J := J)
    phi hphi g alpha (pointwiseLocalFactor_compatible (J := J) phi hphi g alpha)

end SameCoverLocalFactorization
end LocallyDefinedHomTotal
end FibredCategoryMor

end CategoryTheory
