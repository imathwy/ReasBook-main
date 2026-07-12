import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomCartesianRaw

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

set_option backward.isDefEq.respectTransparency false in
/-- Source stage 2.6, pointwise local construction.

For one member `I` of the cover of a representative `alpha`, this constructs the local factor
`beta_i` from the Stacks proof.  The construction is exactly the source argument, written on the
canonical-fiber-pseudofunctor surface:

1. view the local component of `alpha` as a total-category arrow into `y`;
2. factor it through the strongly cartesian arrow `phi`;
3. factor the result through the chosen cartesian pullback of `x`;
4. convert `(i >> g)^* x` to `i^*(g^* x)` by the canonical pullback-composition isomorphism.

The remaining stage-2.6 work is to prove that these pointwise factors satisfy the matching
condition and the raw uniqueness statement. -/
noncomputable def pointwiseLocalFactor
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    ⦃x y z : X.S⦄ (phi : x ⟶ y)
    (hphi : X.p.IsStronglyCartesian (X.p.map phi) phi)
    (g : X.p.obj z ⟶ X.p.obj x)
    (alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi))
    (I : alpha.cover.Arrow) :
    (locallyDefinedHomSaturatedPresheaf X g).obj (op I.Y) := by
  let Fp := canonicalFiberPseudofunctor X.p
  let hc := canonicalPullbackChoice X.p
  let zF : X.p.Fiber (X.p.obj z) := Functor.Fiber.mk (p := X.p) (a := z) rfl
  let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
  let yF : X.p.Fiber (X.p.obj y) := Functor.Fiber.mk (p := X.p) (a := y) rfl
  let i : I.Y.left ⟶ X.p.obj z := I.Y.hom
  let a := (alpha.family I).down
  let yPull : X.p.Fiber (X.p.obj z) :=
    (Fp.map (g ≫ X.p.map phi).op.toLoc).toFunctor.obj yF
  let yPullI : X.p.Fiber I.Y.left :=
    (Fp.map i.op.toLoc).toFunctor.obj yPull
  let zPullI : X.p.Fiber I.Y.left :=
    (Fp.map i.op.toLoc).toFunctor.obj zF
  let psiY : zPullI.1 ⟶ y :=
    a.1 ≫ hc.map i yPull ≫ hc.map (g ≫ X.p.map phi) yF
  have hpsiY : X.p.IsHomLift ((i ≫ g) ≫ X.p.map phi) psiY := by
    have hcomp1 : X.p.IsHomLift (𝟙 I.Y.left ≫ i) (a.1 ≫ hc.map i yPull) := by
      exact
        @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ (𝟙 I.Y.left) i
          a.1 (hc.map i yPull) a.2 ((hc.isStronglyCartesian i yPull).toIsHomLift)
    have hcomp2 :
        X.p.IsHomLift ((𝟙 I.Y.left ≫ i) ≫ (g ≫ X.p.map phi))
          ((a.1 ≫ hc.map i yPull) ≫ hc.map (g ≫ X.p.map phi) yF) := by
      exact
        @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ (𝟙 I.Y.left ≫ i)
          (g ≫ X.p.map phi) (a.1 ≫ hc.map i yPull)
          (hc.map (g ≫ X.p.map phi) yF) hcomp1
          ((hc.isStronglyCartesian (g ≫ X.p.map phi) yF).toIsHomLift)
    simpa [psiY, i, Category.assoc] using hcomp2
  letI : X.p.IsStronglyCartesian (X.p.map phi) phi := hphi
  letI : X.p.IsHomLift ((i ≫ g) ≫ X.p.map phi) psiY := hpsiY
  let hbasePhi : ((i ≫ g) ≫ X.p.map phi) = (i ≫ g) ≫ X.p.map phi := rfl
  let delta : zPullI.1 ⟶ x :=
    IsStronglyCartesian.map X.p (X.p.map phi) phi (g := i ≫ g)
      (f' := (i ≫ g) ≫ X.p.map phi) hbasePhi psiY
  have hdelta : X.p.IsHomLift (i ≫ g) delta := by
    simpa [delta] using
      (IsStronglyCartesian.map_isHomLift X.p (X.p.map phi) phi
        (g := i ≫ g) (f' := (i ≫ g) ≫ X.p.map phi) hbasePhi psiY)
  let xPullIG : X.p.Fiber I.Y.left := (i ≫ g) ^*[hc] xF
  let cartX : xPullIG.1 ⟶ x := hc.map (i ≫ g) xF
  have hcartX : X.p.IsStronglyCartesian (i ≫ g) cartX :=
    hc.isStronglyCartesian (i ≫ g) xF
  letI : X.p.IsStronglyCartesian (i ≫ g) cartX := hcartX
  letI : X.p.IsHomLift (i ≫ g) delta := hdelta
  let hbaseX : i ≫ g = 𝟙 I.Y.left ≫ (i ≫ g) := by simp
  let betaDirect : zPullI.1 ⟶ xPullIG.1 :=
    IsStronglyCartesian.map X.p (i ≫ g) cartX (g := 𝟙 I.Y.left)
      (f' := i ≫ g) hbaseX delta
  have hbetaDirect : X.p.IsHomLift (𝟙 I.Y.left) betaDirect := by
    simpa [betaDirect] using
      (IsStronglyCartesian.map_isHomLift X.p (i ≫ g) cartX
        (g := 𝟙 I.Y.left) (f' := i ≫ g) hbaseX delta)
  let compIso := hc.pullbackCompComponentIso g i xF
  let beta : zPullI.1 ⟶ (i ^*[hc] (g ^*[hc] xF)).1 :=
    betaDirect ≫ compIso.hom.1
  have hbeta : X.p.IsHomLift (𝟙 I.Y.left) beta := by
    have hcomp : X.p.IsHomLift (𝟙 I.Y.left ≫ 𝟙 I.Y.left)
        (betaDirect ≫ compIso.hom.1) := by
      exact
        @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ (𝟙 I.Y.left) (𝟙 I.Y.left)
          betaDirect compIso.hom.1 hbetaDirect compIso.hom.2
    simpa [beta] using hcomp
  exact ULift.up ⟨beta, hbeta⟩

set_option linter.unnecessarySimpa false in
set_option backward.isDefEq.respectTransparency false in
/-- The defining factorization property of `pointwiseLocalFactor`.

After converting the target `i^*(g^*x)` back to `(i >> g)^*x`, the constructed local factor
composes with the chosen cartesian pullback of `x` and then with `phi` to recover the original
local component of `alpha`. -/
theorem pointwiseLocalFactor_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    ⦃x y z : X.S⦄ (phi : x ⟶ y)
    (hphi : X.p.IsStronglyCartesian (X.p.map phi) phi)
    (g : X.p.obj z ⟶ X.p.obj x)
    (alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi))
    (I : alpha.cover.Arrow) :
    let Fp := canonicalFiberPseudofunctor X.p
    let hc := canonicalPullbackChoice X.p
    let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
    let yF : X.p.Fiber (X.p.obj y) := Functor.Fiber.mk (p := X.p) (a := y) rfl
    let i : I.Y.left ⟶ X.p.obj z := I.Y.hom
    let yPull : X.p.Fiber (X.p.obj z) :=
      (Fp.map (g ≫ X.p.map phi).op.toLoc).toFunctor.obj yF
    (((pointwiseLocalFactor (J := J) phi hphi g alpha I).down).1 ≫
        (hc.pullbackCompComponentIso g i xF).inv.1 ≫
        hc.map (i ≫ g) xF) ≫ phi =
      ((alpha.family I).down).1 ≫ hc.map i yPull ≫ hc.map (g ≫ X.p.map phi) yF := by
  dsimp only
  let Fp := canonicalFiberPseudofunctor X.p
  let hc := canonicalPullbackChoice X.p
  let zF : X.p.Fiber (X.p.obj z) := Functor.Fiber.mk (p := X.p) (a := z) rfl
  let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
  let yF : X.p.Fiber (X.p.obj y) := Functor.Fiber.mk (p := X.p) (a := y) rfl
  let i : I.Y.left ⟶ X.p.obj z := I.Y.hom
  let a := (alpha.family I).down
  let yPull : X.p.Fiber (X.p.obj z) :=
    (Fp.map (g ≫ X.p.map phi).op.toLoc).toFunctor.obj yF
  let yPullI : X.p.Fiber I.Y.left :=
    (Fp.map i.op.toLoc).toFunctor.obj yPull
  let zPullI : X.p.Fiber I.Y.left :=
    (Fp.map i.op.toLoc).toFunctor.obj zF
  let psiY : zPullI.1 ⟶ y :=
    a.1 ≫ hc.map i yPull ≫ hc.map (g ≫ X.p.map phi) yF
  have hpsiY : X.p.IsHomLift ((i ≫ g) ≫ X.p.map phi) psiY := by
    have hcomp1 : X.p.IsHomLift (𝟙 I.Y.left ≫ i) (a.1 ≫ hc.map i yPull) := by
      exact
        @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ (𝟙 I.Y.left) i
          a.1 (hc.map i yPull) a.2 ((hc.isStronglyCartesian i yPull).toIsHomLift)
    have hcomp2 :
        X.p.IsHomLift ((𝟙 I.Y.left ≫ i) ≫ (g ≫ X.p.map phi))
          ((a.1 ≫ hc.map i yPull) ≫ hc.map (g ≫ X.p.map phi) yF) := by
      exact
        @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ (𝟙 I.Y.left ≫ i)
          (g ≫ X.p.map phi) (a.1 ≫ hc.map i yPull)
          (hc.map (g ≫ X.p.map phi) yF) hcomp1
          ((hc.isStronglyCartesian (g ≫ X.p.map phi) yF).toIsHomLift)
    simpa [psiY, i, Category.assoc] using hcomp2
  letI : X.p.IsStronglyCartesian (X.p.map phi) phi := hphi
  letI : X.p.IsHomLift ((i ≫ g) ≫ X.p.map phi) psiY := hpsiY
  let hbasePhi : ((i ≫ g) ≫ X.p.map phi) = (i ≫ g) ≫ X.p.map phi := rfl
  let delta : zPullI.1 ⟶ x :=
    IsStronglyCartesian.map X.p (X.p.map phi) phi (g := i ≫ g)
      (f' := (i ≫ g) ≫ X.p.map phi) hbasePhi psiY
  have hdelta_fac : delta ≫ phi = psiY := by
    simpa [delta] using
      (IsStronglyCartesian.fac X.p (X.p.map phi) phi
        (f' := (i ≫ g) ≫ X.p.map phi) hbasePhi psiY)
  have hdelta : X.p.IsHomLift (i ≫ g) delta := by
    simpa [delta] using
      (IsStronglyCartesian.map_isHomLift X.p (X.p.map phi) phi
        (g := i ≫ g) (f' := (i ≫ g) ≫ X.p.map phi) hbasePhi psiY)
  let xPullIG : X.p.Fiber I.Y.left := (i ≫ g) ^*[hc] xF
  let cartX : xPullIG.1 ⟶ x := hc.map (i ≫ g) xF
  have hcartX : X.p.IsStronglyCartesian (i ≫ g) cartX :=
    hc.isStronglyCartesian (i ≫ g) xF
  letI : X.p.IsStronglyCartesian (i ≫ g) cartX := hcartX
  letI : X.p.IsHomLift (i ≫ g) delta := hdelta
  let hbaseX : i ≫ g = 𝟙 I.Y.left ≫ (i ≫ g) := by simp
  let betaDirect : zPullI.1 ⟶ xPullIG.1 :=
    IsStronglyCartesian.map X.p (i ≫ g) cartX (g := 𝟙 I.Y.left)
      (f' := i ≫ g) hbaseX delta
  have hbetaDirect_fac : betaDirect ≫ cartX = delta := by
    simpa [betaDirect] using
      (IsStronglyCartesian.fac X.p (i ≫ g) cartX
        (g := 𝟙 I.Y.left) (f' := i ≫ g) hbaseX delta)
  let compIso := hc.pullbackCompComponentIso g i xF
  have hIso : compIso.hom.1 ≫ compIso.inv.1 = 𝟙 xPullIG.1 := by
    change (compIso.hom ≫ compIso.inv).1 = (𝟙 xPullIG : xPullIG ⟶ xPullIG).1
    rw [compIso.hom_inv_id]
  change (((betaDirect ≫ compIso.hom.1) ≫ compIso.inv.1 ≫ cartX) ≫ phi = psiY)
  calc
    (((betaDirect ≫ compIso.hom.1) ≫ compIso.inv.1 ≫ cartX) ≫ phi)
        = ((betaDirect ≫ (compIso.hom.1 ≫ compIso.inv.1)) ≫ cartX) ≫ phi := by
          simp [Category.assoc]
    _ = (betaDirect ≫ cartX) ≫ phi := by
          rw [hIso]
          simp
    _ = delta ≫ phi := by rw [hbetaDirect_fac]
    _ = psiY := hdelta_fac

set_option backward.isDefEq.respectTransparency false in
/-- A cartesian-target form of `pointwiseLocalFactor_fac`.

This removes the intermediate `(i >> g)^*x` by the inverse composition-comparison
factorization, so the constructed factor is compared directly after composing with
`i^*(g^*x) -> g^*x -> x -> y`. -/
theorem pointwiseLocalFactor_fac_cartesian
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    ⦃x y z : X.S⦄ (phi : x ⟶ y)
    (hphi : X.p.IsStronglyCartesian (X.p.map phi) phi)
    (g : X.p.obj z ⟶ X.p.obj x)
    (alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi))
    (I : alpha.cover.Arrow) :
    let Fp := canonicalFiberPseudofunctor X.p
    let hc := canonicalPullbackChoice X.p
    let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
    let yF : X.p.Fiber (X.p.obj y) := Functor.Fiber.mk (p := X.p) (a := y) rfl
    let i : I.Y.left ⟶ X.p.obj z := I.Y.hom
    let gxF : X.p.Fiber (X.p.obj z) := (Fp.map g.op.toLoc).toFunctor.obj xF
    let gyF : X.p.Fiber (X.p.obj z) :=
      (Fp.map (g ≫ X.p.map phi).op.toLoc).toFunctor.obj yF
    (((pointwiseLocalFactor (J := J) phi hphi g alpha I).down).1 ≫
        hc.map i gxF ≫ hc.map g xF) ≫ phi =
      ((alpha.family I).down).1 ≫ hc.map i gyF ≫ hc.map (g ≫ X.p.map phi) yF := by
  intro Fp hc xF yF i gxF gyF
  have h := pointwiseLocalFactor_fac (J := J) phi hphi g alpha I
  dsimp only at h
  have hinv := (canonicalPullbackChoice X.p).pullbackCompComponentIso_inv_fac g i xF
  calc
    (((pointwiseLocalFactor (J := J) phi hphi g alpha I).down).1 ≫
        hc.map i gxF ≫ hc.map g xF) ≫ phi
        = ((((pointwiseLocalFactor (J := J) phi hphi g alpha I).down).1 ≫
            (hc.pullbackCompComponentIso g i xF).inv.1 ≫
            hc.map (i ≫ g) xF) ≫ phi) := by
          have hstep := congrArg
            (fun k => ((pointwiseLocalFactor (J := J) phi hphi g alpha I).down).1 ≫
              k ≫ phi) hinv.symm
          simpa [gxF, Fp, hc, Category.assoc] using hstep
    _ = ((alpha.family I).down).1 ≫ hc.map i gyF ≫ hc.map (g ≫ X.p.map phi) yF := h

set_option linter.unnecessarySimpa false in
set_option backward.isDefEq.respectTransparency false in
/-- The cartesian-target factorization property remains true after restricting to a further
overlap.

This is the exact overlap form used in the source proof: restrict the constructed `beta_i` and
the original `alpha_i` to a common refinement, then compare after composing with the common
cartesian target arrow. -/
theorem pointwiseLocalFactor_fac_cartesian_pullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    ⦃x y z : X.S⦄ (phi : x ⟶ y)
    (hphi : X.p.IsStronglyCartesian (X.p.map phi) phi)
    (g : X.p.obj z ⟶ X.p.obj x)
    (alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi))
    (I : alpha.cover.Arrow)
    {T : C} (q : T ⟶ I.Y.left) (qi : T ⟶ X.p.obj z)
    (hqi : q ≫ I.Y.hom = qi) :
    let Fp := canonicalFiberPseudofunctor X.p
    let hc := canonicalPullbackChoice X.p
    let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
    let yF : X.p.Fiber (X.p.obj y) := Functor.Fiber.mk (p := X.p) (a := y) rfl
    let gxF : X.p.Fiber (X.p.obj z) := (Fp.map g.op.toLoc).toFunctor.obj xF
    let gyF : X.p.Fiber (X.p.obj z) :=
      (Fp.map (g ≫ X.p.map phi).op.toLoc).toFunctor.obj yF
    let betaQ := Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := Fp) (pointwiseLocalFactor (J := J) phi hphi g alpha I).down
      q qi qi hqi hqi
    let alphaQ := Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := Fp) (alpha.family I).down q qi qi hqi hqi
    betaQ.1 ≫ hc.map qi gxF ≫ hc.map g xF ≫ phi =
      alphaQ.1 ≫ hc.map qi gyF ≫ hc.map (g ≫ X.p.map phi) yF := by
  intro Fp hc xF yF gxF gyF betaQ alphaQ
  let zF : X.p.Fiber (X.p.obj z) := Functor.Fiber.mk (p := X.p) (a := z) rfl
  let i : I.Y.left ⟶ X.p.obj z := I.Y.hom
  let beta := (pointwiseLocalFactor (J := J) phi hphi g alpha I).down
  let a := (alpha.family I).down
  let A := ((Fp.mapComp' i.op.toLoc q.op.toLoc qi.op.toLoc
    (comp_toLoc_eq i q qi hqi)).hom.toNatTrans.app zF)
  have hbetaPost := canonicalFiberPseudofunctor_pullHom_postcompose_cartesian
    (p := X.p) i i q qi qi hqi hqi (M₁ := zF) (M₂ := gxF) beta
  have halphaPost := canonicalFiberPseudofunctor_pullHom_postcompose_cartesian
    (p := X.p) i i q qi qi hqi hqi (M₁ := zF) (M₂ := gyF) a
  have hfac := pointwiseLocalFactor_fac_cartesian (J := J) phi hphi g alpha I
  dsimp only at hfac
  have hfacFront :
      A.1 ≫ hc.map q ((Fp.map i.op.toLoc).toFunctor.obj zF) ≫
          beta.1 ≫ hc.map i gxF ≫ hc.map g xF ≫ phi =
        A.1 ≫ hc.map q ((Fp.map i.op.toLoc).toFunctor.obj zF) ≫
          a.1 ≫ hc.map i gyF ≫ hc.map (g ≫ X.p.map phi) yF := by
    simpa [A, beta, a, Fp, hc, xF, yF, gxF, gyF, i, Category.assoc] using
      congrArg
        (fun t => A.1 ≫ hc.map q ((Fp.map i.op.toLoc).toFunctor.obj zF) ≫ t)
        hfac
  calc
    betaQ.1 ≫ hc.map qi gxF ≫ hc.map g xF ≫ phi
        = A.1 ≫ hc.map q ((Fp.map i.op.toLoc).toFunctor.obj zF) ≫
            beta.1 ≫ hc.map i gxF ≫ hc.map g xF ≫ phi := by
          simpa [A, betaQ, beta, Fp, hc, gxF, zF, i, Category.assoc] using
            congrArg (fun t => t ≫ hc.map g xF ≫ phi) hbetaPost
    _ = A.1 ≫ hc.map q ((Fp.map i.op.toLoc).toFunctor.obj zF) ≫
          a.1 ≫ hc.map i gyF ≫ hc.map (g ≫ X.p.map phi) yF := hfacFront
    _ = alphaQ.1 ≫ hc.map qi gyF ≫ hc.map (g ≫ X.p.map phi) yF := by
          simpa [A, alphaQ, a, Fp, hc, gyF, zF, i, Category.assoc] using
            (congrArg (fun t => t ≫ hc.map (g ≫ X.p.map phi) yF) halphaPost).symm

set_option linter.unnecessarySimpa false in
set_option backward.isDefEq.respectTransparency false in
/-- Overlap compatibility for the pointwise factors reduces to the source proof's final
restricted-composite equality.

The cartesian uniqueness part is now discharged here: on an overlap, it is enough to show that
the two restricted factors become equal after composing with the canonical cartesian arrow to
`x` and then with `phi`.  The remaining proof is the source calculation using
`alpha.family.condition` and the pullback-composition coherence of the canonical cleavage. -/
theorem pointwiseLocalFactor_compatible_of_cartesian_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    ⦃x y z : X.S⦄ (phi : x ⟶ y)
    (hphi : X.p.IsStronglyCartesian (X.p.map phi) phi)
    (g : X.p.obj z ⟶ X.p.obj x)
    (alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi))
    (hfac : ∀ R : alpha.cover.Relation,
      let Fp := canonicalFiberPseudofunctor X.p
      let hc := canonicalPullbackChoice X.p
      let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
      let gxF : X.p.Fiber (X.p.obj z) := (Fp.map g.op.toLoc).toFunctor.obj xF
      let targetR : X.p.Fiber R.r.Z.left :=
        (Fp.map R.r.Z.hom.op.toLoc).toFunctor.obj gxF
      let cartR : targetR.1 ⟶ gxF.1 := hc.map R.r.Z.hom gxF
      let cartG : gxF.1 ⟶ x := hc.map g xF
      let cartAll : targetR.1 ⟶ y := cartR ≫ cartG ≫ phi
      let beta₁ := Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := Fp) (pointwiseLocalFactor (J := J) phi hphi g alpha R.fst).down
        R.r.g₁.left R.r.Z.hom R.r.Z.hom (by simpa using R.r.g₁.w)
        (by simpa using R.r.g₁.w)
      let beta₂ := Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := Fp) (pointwiseLocalFactor (J := J) phi hphi g alpha R.snd).down
        R.r.g₂.left R.r.Z.hom R.r.Z.hom (by simpa using R.r.g₂.w)
        (by simpa using R.r.g₂.w)
      beta₁.1 ≫ cartAll = beta₂.1 ≫ cartAll) :
      ∀ R : alpha.cover.Relation,
        (locallyDefinedHomSaturatedPresheaf X g).map R.r.g₁.op
            (pointwiseLocalFactor (J := J) phi hphi g alpha (alpha.cover.shape.fst R)) =
          (locallyDefinedHomSaturatedPresheaf X g).map R.r.g₂.op
            (pointwiseLocalFactor (J := J) phi hphi g alpha (alpha.cover.shape.snd R)) := by
  intro R
  apply ULift.ext
  dsimp [locallyDefinedHomSaturatedPresheaf, locallyDefinedHomPresheaf]
  let Fp := canonicalFiberPseudofunctor X.p
  let hc := canonicalPullbackChoice X.p
  let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
  let gxF : X.p.Fiber (X.p.obj z) := (Fp.map g.op.toLoc).toFunctor.obj xF
  let targetR : X.p.Fiber R.r.Z.left :=
    (Fp.map R.r.Z.hom.op.toLoc).toFunctor.obj gxF
  let cartR : targetR.1 ⟶ gxF.1 := hc.map R.r.Z.hom gxF
  let cartG : gxF.1 ⟶ x := hc.map g xF
  let cartAll : targetR.1 ⟶ y := cartR ≫ cartG ≫ phi
  have hcartR : X.p.IsStronglyCartesian R.r.Z.hom cartR := by
    simpa [cartR, targetR, gxF, Fp, hc] using hc.isStronglyCartesian R.r.Z.hom gxF
  have hcartG : X.p.IsStronglyCartesian g cartG := by
    simpa [cartG, gxF, Fp, hc] using hc.isStronglyCartesian g xF
  have hcartRG : X.p.IsStronglyCartesian (R.r.Z.hom ≫ g) (cartR ≫ cartG) := by
    letI : X.p.IsStronglyCartesian R.r.Z.hom cartR := hcartR
    letI : X.p.IsStronglyCartesian g cartG := hcartG
    infer_instance
  have hcartAll : X.p.IsStronglyCartesian ((R.r.Z.hom ≫ g) ≫ X.p.map phi) cartAll := by
    letI : X.p.IsStronglyCartesian (R.r.Z.hom ≫ g) (cartR ≫ cartG) := hcartRG
    letI : X.p.IsStronglyCartesian (X.p.map phi) phi := hphi
    simpa [cartAll] using
      (inferInstance : X.p.IsStronglyCartesian ((R.r.Z.hom ≫ g) ≫ X.p.map phi)
        ((cartR ≫ cartG) ≫ phi))
  apply Functor.Fiber.hom_ext
  let beta₁ := Pseudofunctor.LocallyDiscreteOpToCat.pullHom
    (F := Fp) (pointwiseLocalFactor (J := J) phi hphi g alpha R.fst).down
    R.r.g₁.left R.r.Z.hom R.r.Z.hom (by simpa using R.r.g₁.w)
      (by simpa using R.r.g₁.w)
  let beta₂ := Pseudofunctor.LocallyDiscreteOpToCat.pullHom
    (F := Fp) (pointwiseLocalFactor (J := J) phi hphi g alpha R.snd).down
    R.r.g₂.left R.r.Z.hom R.r.Z.hom (by simpa using R.r.g₂.w)
      (by simpa using R.r.g₂.w)
  change beta₁.1 = beta₂.1
  refine @Functor.IsStronglyCartesian.ext C X.S _ _ X.p _ _ _ _
    (((R.r.Z.hom ≫ g) ≫ X.p.map phi)) cartAll hcartAll
    _ _ (𝟙 R.r.Z.left) beta₁.1 beta₂.1 ?_ ?_ ?_
  · exact beta₁.2
  · exact beta₂.2
  · exact hfac R

set_option linter.unnecessarySimpa false in
set_option backward.isDefEq.respectTransparency false in
/-- The pointwise local factors satisfy the matching condition on overlaps.

This is the source overlap argument for stage 2.6: after composing both restricted factors with
the common cartesian arrow to `y`, the factorization lemma reduces the equality to the matching
condition already present in `alpha`. -/
theorem pointwiseLocalFactor_compatible
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    ⦃x y z : X.S⦄ (phi : x ⟶ y)
    (hphi : X.p.IsStronglyCartesian (X.p.map phi) phi)
    (g : X.p.obj z ⟶ X.p.obj x)
    (alpha : LocallyDefinedHomRepresentativeOver (J := J) X (g ≫ X.p.map phi)) :
      ∀ R : alpha.cover.Relation,
        (locallyDefinedHomSaturatedPresheaf X g).map R.r.g₁.op
            (pointwiseLocalFactor (J := J) phi hphi g alpha (alpha.cover.shape.fst R)) =
          (locallyDefinedHomSaturatedPresheaf X g).map R.r.g₂.op
            (pointwiseLocalFactor (J := J) phi hphi g alpha (alpha.cover.shape.snd R)) := by
  refine pointwiseLocalFactor_compatible_of_cartesian_fac (J := J) phi hphi g alpha ?_
  intro R
  dsimp only
  let Fp := canonicalFiberPseudofunctor X.p
  let hc := canonicalPullbackChoice X.p
  let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
  let yF : X.p.Fiber (X.p.obj y) := Functor.Fiber.mk (p := X.p) (a := y) rfl
  let gxF : X.p.Fiber (X.p.obj z) := (Fp.map g.op.toLoc).toFunctor.obj xF
  let gyF : X.p.Fiber (X.p.obj z) :=
    (Fp.map (g ≫ X.p.map phi).op.toLoc).toFunctor.obj yF
  let beta₁ := Pseudofunctor.LocallyDiscreteOpToCat.pullHom
    (F := Fp) (pointwiseLocalFactor (J := J) phi hphi g alpha R.fst).down
    R.r.g₁.left R.r.Z.hom R.r.Z.hom (by simpa using R.r.g₁.w)
      (by simpa using R.r.g₁.w)
  let beta₂ := Pseudofunctor.LocallyDiscreteOpToCat.pullHom
    (F := Fp) (pointwiseLocalFactor (J := J) phi hphi g alpha R.snd).down
    R.r.g₂.left R.r.Z.hom R.r.Z.hom (by simpa using R.r.g₂.w)
      (by simpa using R.r.g₂.w)
  let alpha₁ := Pseudofunctor.LocallyDiscreteOpToCat.pullHom
    (F := Fp) (alpha.family R.fst).down
    R.r.g₁.left R.r.Z.hom R.r.Z.hom (by simpa using R.r.g₁.w)
      (by simpa using R.r.g₁.w)
  let alpha₂ := Pseudofunctor.LocallyDiscreteOpToCat.pullHom
    (F := Fp) (alpha.family R.snd).down
    R.r.g₂.left R.r.Z.hom R.r.Z.hom (by simpa using R.r.g₂.w)
      (by simpa using R.r.g₂.w)
  have hβ₁ := pointwiseLocalFactor_fac_cartesian_pullHom
    (J := J) phi hphi g alpha R.fst R.r.g₁.left R.r.Z.hom (by simpa using R.r.g₁.w)
  have hβ₂ := pointwiseLocalFactor_fac_cartesian_pullHom
    (J := J) phi hphi g alpha R.snd R.r.g₂.left R.r.Z.hom (by simpa using R.r.g₂.w)
  dsimp only at hβ₁ hβ₂
  have hαhom := congrArg (fun t => (ULift.down t).1) (alpha.family.condition R)
  dsimp [locallyDefinedHomSaturatedPresheaf, locallyDefinedHomPresheaf, CategoryTheory.uliftFunctor]
    at hαhom
  have hα : alpha₁.1 = alpha₂.1 := by
    simpa [alpha₁, alpha₂, Fp] using hαhom
  calc
    beta₁.1 ≫ (hc.map R.r.Z.hom gxF ≫ hc.map g xF ≫ phi)
        = alpha₁.1 ≫ hc.map R.r.Z.hom gyF ≫ hc.map (g ≫ X.p.map phi) yF := by
          simpa [beta₁, alpha₁, Fp, hc, xF, yF, gxF, gyF, Category.assoc] using hβ₁
    _ = alpha₂.1 ≫ hc.map R.r.Z.hom gyF ≫ hc.map (g ≫ X.p.map phi) yF := by
          rw [hα]
    _ = beta₂.1 ≫ (hc.map R.r.Z.hom gxF ≫ hc.map g xF ≫ phi) := by
          simpa [beta₂, alpha₂, Fp, hc, xF, yF, gxF, gyF, Category.assoc] using hβ₂.symm

end SameCoverLocalFactorization

end LocallyDefinedHomTotal
end FibredCategoryMor

end CategoryTheory
