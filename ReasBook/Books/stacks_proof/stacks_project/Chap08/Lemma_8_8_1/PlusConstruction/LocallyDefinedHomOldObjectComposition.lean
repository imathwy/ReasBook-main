import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomOldObjectComparison

universe u v uX vX w wA

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

private theorem ulift_heq_of_down_heq
    {A B : Type wA} {x : ULift.{w, wA} A} {y : ULift.{w, wA} B}
    (h : HEq x.down y.down) : HEq x y := by
  cases x
  cases y
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The vertical factor of the ordinary composite is the composite of the two ordinary vertical
factors, followed by the canonical pullback-composition comparison and the explicit transport
induced by `X.p.map_comp`.

This is the global, owner-sensitive form of the source proof's sentence that the trivial-cover
representative of `g ∘ f` is obtained by composing the two trivial-cover representatives. -/
theorem ordinaryHomToPullbackFiberHom_comp_afterTransport
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y z : X.S}
    (f : x ⟶ y) (g : y ⟶ z) :
    let Fp := canonicalFiberPseudofunctor X.p
    let zF : X.p.Fiber (X.p.obj z) := Functor.Fiber.mk (p := X.p) (a := z) rfl
    let hbase : X.p.map (f ≫ g) = X.p.map f ≫ X.p.map g := X.p.map_comp f g
    let targetTransport :
        ((Fp.map (X.p.map (f ≫ g)).op.toLoc).toFunctor.obj zF) ⟶
          ((Fp.map (X.p.map f ≫ X.p.map g).op.toLoc).toFunctor.obj zF) :=
      (eqToHom (congrArg (fun k => (canonicalPullbackChoice X.p).pullbackFunctor k)
        hbase)).app zF
    ordinaryHomToPullbackFiberHom X (f ≫ g) ≫ targetTransport =
      ordinaryHomToPullbackFiberHom X f ≫
        (Fp.map (X.p.map f).op.toLoc).toFunctor.map
          (ordinaryHomToPullbackFiberHom X g) ≫
        (Fp.mapComp (X.p.map g).op.toLoc (X.p.map f).op.toLoc).inv.toNatTrans.app zF := by
  intro Fp zF hbase targetTransport
  apply Functor.Fiber.hom_ext
  let hc := canonicalPullbackChoice X.p
  let lhs := ordinaryHomToPullbackFiberHom X (f ≫ g) ≫ targetTransport
  let rhs := ordinaryHomToPullbackFiberHom X f ≫
        (Fp.map (X.p.map f).op.toLoc).toFunctor.map
          (ordinaryHomToPullbackFiberHom X g) ≫
        (Fp.mapComp (X.p.map g).op.toLoc (X.p.map f).op.toLoc).inv.toNatTrans.app zF
  change lhs.1 = rhs.1
  refine @Functor.IsStronglyCartesian.ext C X.S _ _ X.p _ _ _ _
    (X.p.map f ≫ X.p.map g) (hc.map (X.p.map f ≫ X.p.map g) zF)
    (hc.isStronglyCartesian (X.p.map f ≫ X.p.map g) zF)
    _ _ (𝟙 (X.p.obj x)) lhs.1 rhs.1 ?_ ?_ ?_
  · exact lhs.2
  · exact rhs.2
  · have htransport :
        targetTransport.1 ≫ hc.map (X.p.map f ≫ X.p.map g) zF =
          hc.map (X.p.map (f ≫ g)) zF := by
      dsimp [targetTransport, hbase, hc, Fp, zF]
      have haux {k : X.p.obj x ⟶ X.p.obj z}
          (e : X.p.map (f ≫ g) = k) :
          (Functor.Fiber.fiberInclusion.map
              ((eqToHom (congrArg
                (fun k => (canonicalPullbackChoice X.p).pullbackFunctor k) e)).app zF)) ≫
            (canonicalPullbackChoice X.p).map k zF =
          (canonicalPullbackChoice X.p).map (X.p.map (f ≫ g)) zF := by
        cases e
        simp
      exact haux (X.p.map_comp f g)
    have hleft :
        lhs.1 ≫ hc.map (X.p.map f ≫ X.p.map g) zF = f ≫ g := by
      dsimp [lhs]
      change (Functor.Fiber.fiberInclusion.map
          (ordinaryHomToPullbackFiberHom X (f ≫ g) ≫ targetTransport)) ≫
          hc.map (X.p.map f ≫ X.p.map g) zF = f ≫ g
      rw [Functor.map_comp]
      change ((ordinaryHomToPullbackFiberHom X (f ≫ g)).1 ≫ targetTransport.1) ≫
          hc.map (X.p.map f ≫ X.p.map g) zF = f ≫ g
      rw [Category.assoc]
      rw [htransport]
      exact ordinaryHomToPullbackFiberHom_fac X (f ≫ g)
    have hcompInv :
        ((Fp.mapComp (X.p.map g).op.toLoc (X.p.map f).op.toLoc).inv.toNatTrans.app zF).1 ≫
          hc.map (X.p.map f ≫ X.p.map g) zF =
        hc.map (X.p.map f)
            (((canonicalFiberPseudofunctor X.p).map (X.p.map g).op.toLoc).toFunctor.obj zF) ≫
          hc.map (X.p.map g) zF := by
      simpa [Fp, hc, canonicalFiberPseudofunctor, PullbackChoice.fiberPseudofunctor] using
        (hc.pullbackCompComponentIso_inv_fac (X.p.map g) (X.p.map f) zF)
    have hmapg :
        (((Fp.map (X.p.map f).op.toLoc).toFunctor.map
          (ordinaryHomToPullbackFiberHom X g)).1) ≫
            hc.map (X.p.map f)
              (((canonicalFiberPseudofunctor X.p).map (X.p.map g).op.toLoc).toFunctor.obj zF) =
          hc.map (X.p.map f) (Functor.Fiber.mk (p := X.p) (a := y) rfl) ≫
            (ordinaryHomToPullbackFiberHom X g).1 := by
      simpa [Fp, hc, canonicalFiberPseudofunctor, PullbackChoice.fiberPseudofunctor, zF] using
        (hc.pullbackFunctor_map_fac (X.p.map f) (ordinaryHomToPullbackFiberHom X g))
    have hright :
        rhs.1 ≫ hc.map (X.p.map f ≫ X.p.map g) zF = f ≫ g := by
      dsimp [rhs]
      change ((ordinaryHomToPullbackFiberHom X f).1 ≫
          (((Fp.map (X.p.map f).op.toLoc).toFunctor.map
            (ordinaryHomToPullbackFiberHom X g)).1) ≫
          ((Fp.mapComp (X.p.map g).op.toLoc (X.p.map f).op.toLoc).inv.toNatTrans.app zF).1) ≫
        hc.map (X.p.map f ≫ X.p.map g) zF = f ≫ g
      calc
        ((ordinaryHomToPullbackFiberHom X f).1 ≫
            (((Fp.map (X.p.map f).op.toLoc).toFunctor.map
              (ordinaryHomToPullbackFiberHom X g)).1) ≫
            ((Fp.mapComp (X.p.map g).op.toLoc
              (X.p.map f).op.toLoc).inv.toNatTrans.app zF).1) ≫
          hc.map (X.p.map f ≫ X.p.map g) zF
            =
          (ordinaryHomToPullbackFiberHom X f).1 ≫
            (((Fp.map (X.p.map f).op.toLoc).toFunctor.map
              (ordinaryHomToPullbackFiberHom X g)).1) ≫
            (((Fp.mapComp (X.p.map g).op.toLoc
                (X.p.map f).op.toLoc).inv.toNatTrans.app zF).1 ≫
              hc.map (X.p.map f ≫ X.p.map g) zF) := by
              simp [Category.assoc]
        _ =
          (ordinaryHomToPullbackFiberHom X f).1 ≫
            (((Fp.map (X.p.map f).op.toLoc).toFunctor.map
              (ordinaryHomToPullbackFiberHom X g)).1) ≫
            (hc.map (X.p.map f)
                (((canonicalFiberPseudofunctor X.p).map
                  (X.p.map g).op.toLoc).toFunctor.obj zF) ≫
              hc.map (X.p.map g) zF) := by
              rw [hcompInv]
        _ =
          (ordinaryHomToPullbackFiberHom X f).1 ≫
            ((((Fp.map (X.p.map f).op.toLoc).toFunctor.map
              (ordinaryHomToPullbackFiberHom X g)).1) ≫
              hc.map (X.p.map f)
                (((canonicalFiberPseudofunctor X.p).map
                  (X.p.map g).op.toLoc).toFunctor.obj zF)) ≫
            hc.map (X.p.map g) zF := by
              simp [Category.assoc]
        _ =
          (ordinaryHomToPullbackFiberHom X f).1 ≫
            (hc.map (X.p.map f) (Functor.Fiber.mk (p := X.p) (a := y) rfl) ≫
              (ordinaryHomToPullbackFiberHom X g).1) ≫
            hc.map (X.p.map g) zF := by
              rw [hmapg]
        _ =
          ((ordinaryHomToPullbackFiberHom X f).1 ≫
            hc.map (X.p.map f) (Functor.Fiber.mk (p := X.p) (a := y) rfl)) ≫
            (ordinaryHomToPullbackFiberHom X g).1 ≫
            hc.map (X.p.map g) zF := by
              simp [Category.assoc]
        _ = f ≫ g := by
          rw [ordinaryHomToPullbackFiberHom_fac X f]
          rw [ordinaryHomToPullbackFiberHom_fac X g]
    exact hleft.trans hright.symm

set_option backward.isDefEq.respectTransparency false in
/-- Restricting the trivial-cover representative of an ordinary morphism to an identity-slice
member is just the canonical fiber-pseudofunctor restriction of its vertical factor. -/
theorem ordinaryHomToRepresentativeOver_family_apply_down
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y : X.S} (a : x ⟶ y)
    (I : (ordinaryHomToRepresentativeOver (J := J) X a).cover.Arrow) :
    let Fp := canonicalFiberPseudofunctor X.p
    ((ordinaryHomToRepresentativeOver (J := J) X a).family I).down =
      (Fp.map I.Y.hom.op.toLoc).toFunctor.map (ordinaryHomToPullbackFiberHom X a) := by
  intro Fp
  let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
  let yF : X.p.Fiber (X.p.obj y) := Functor.Fiber.mk (p := X.p) (a := y) rfl
  let e := (Fp.map I.Y.hom.op.toLoc).toFunctor.map (ordinaryHomToPullbackFiberHom X a)
  have hf : I.f = (Over.homMk I.Y.hom : I.Y ⟶ Over.mk (𝟙 (X.p.obj x))) := by
    ext
    simpa using I.f.w
  rw [ordinaryHomToRepresentativeOver_family_apply (J := J) X a I]
  change
    ((locallyDefinedHomSaturatedPresheaf X (X.p.map a)).map I.f.op
      (ULift.up
        (((canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv)
          (ordinaryHomToPullbackFiberHom X a)))).down =
      e
  rw [hf]
  simpa [locallyDefinedHomSaturatedPresheaf, locallyDefinedHomPresheaf, Fp, xF, yF, e] using
    (presheafHom_map_identitySlice_hom_overMk (p := X.p) I.Y.hom
      xF ((Fp.map (X.p.map a).op.toLoc).toFunctor.obj yF)
      (ordinaryHomToPullbackFiberHom X a))

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSimpArgs false in
/-- On the composition cover of two trivial-cover ordinary representatives, the local composite
is the restriction of the global composite of the two ordinary vertical factors. -/
theorem ordinaryCompositionLocal_down_eq_mapGlobal
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y z : X.S} (f : x ⟶ y) (g : y ⟶ z)
    (I : (LocallyDefinedHomRepresentativeOver.compositionCover (J := J)
      (ordinaryHomToRepresentativeOver (J := J) X f)
      (ordinaryHomToRepresentativeOver (J := J) X g)).Arrow) :
    let Fp := canonicalFiberPseudofunctor X.p
    let zF : X.p.Fiber (X.p.obj z) := Functor.Fiber.mk (p := X.p) (a := z) rfl
    let global :=
      ordinaryHomToPullbackFiberHom X f ≫
        (Fp.map (X.p.map f).op.toLoc).toFunctor.map
          (ordinaryHomToPullbackFiberHom X g) ≫
        (Fp.mapComp (X.p.map g).op.toLoc (X.p.map f).op.toLoc).inv.toNatTrans.app zF
    ((LocallyDefinedHomRepresentativeOver.compositionLocal (J := J)
      (ordinaryHomToRepresentativeOver (J := J) X f)
      (ordinaryHomToRepresentativeOver (J := J) X g) I).down) =
      (Fp.map I.Y.hom.op.toLoc).toFunctor.map global := by
  intro Fp zF global
  let α := ordinaryHomToRepresentativeOver (J := J) X f
  let β := ordinaryHomToRepresentativeOver (J := J) X g
  let yF : X.p.Fiber (X.p.obj y) := Functor.Fiber.mk (p := X.p) (a := y) rfl
  let gfZ := (Fp.map (X.p.map g).op.toLoc).toFunctor.obj zF
  let L := (Fp.map I.Y.hom.op.toLoc).toFunctor.map (ordinaryHomToPullbackFiberHom X f)
  let M := (Fp.mapComp' (X.p.map f).op.toLoc I.Y.hom.op.toLoc
    ((I.Y.hom ≫ X.p.map f).op.toLoc) (by rfl)).inv.toNatTrans.app yF
  let N := (Fp.map (I.Y.hom ≫ X.p.map f).op.toLoc).toFunctor.map
    (ordinaryHomToPullbackFiberHom X g)
  let T := (Fp.mapComp' (X.p.map f).op.toLoc I.Y.hom.op.toLoc
      ((I.Y.hom ≫ X.p.map f).op.toLoc) (by rfl)).hom.toNatTrans.app gfZ ≫
    (Fp.map I.Y.hom.op.toLoc).toFunctor.map
      ((Fp.mapComp (X.p.map g).op.toLoc (X.p.map f).op.toLoc).inv.toNatTrans.app zF)
  have hL :
      ((LocallyDefinedHomRepresentativeOver.compositionLeftLocal (J := J) α β I).down) = L := by
    simpa [α, β, L, Fp] using
      ordinaryHomToRepresentativeOver_family_apply_down (J := J) X f
        (LocallyDefinedHomRepresentativeOver.compositionCoverToLeft (J := J) α β I)
  have hN :
      ((LocallyDefinedHomRepresentativeOver.compositionRightLocal (J := J) α β I).down) = N := by
    have hraw :=
      ordinaryHomToRepresentativeOver_family_apply_down (J := J) X g
        (LocallyDefinedHomRepresentativeOver.compositionCoverToRight (J := J) α β I)
    simpa [α, β, N, Fp, LocallyDefinedHomRepresentative.compositionCoverToRight_hom] using hraw
  have hlocal :
      ((LocallyDefinedHomRepresentativeOver.compositionLocal (J := J) α β I).down) =
        L ≫ M ≫ N ≫ T := by
    dsimp [LocallyDefinedHomRepresentativeOver.compositionLocal,
      LocallyDefinedHomRepresentativeOver.compositionMiddleIso,
      LocallyDefinedHomRepresentativeOver.compositionTargetHom]
    rw [hL, hN]
    simp [α, β, L, M, N, T, Fp, yF, zF, gfZ]
  rw [hlocal]
  dsimp [global]
  simp [L, M, N, T, Fp, yF, zF, gfZ, Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Fixed-base comparison: after transporting along `X.p.map_comp`, the trivial-cover ordinary
representative of `f ≫ g` is equivalent to the source composite of the two trivial-cover ordinary
representatives. -/
theorem ordinaryHomToRepresentativeOver_comp_equivalent
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y z : X.S} (f : x ⟶ y) (g : y ⟶ z) :
    let hbase : X.p.map (f ≫ g) = X.p.map f ≫ X.p.map g := X.p.map_comp f g
    LocallyDefinedHomRepresentativeOver.Equivalent (J := J)
      (LocallyDefinedHomRepresentativeOver.castBase (J := J) hbase
        (ordinaryHomToRepresentativeOver (J := J) X (f ≫ g)))
      (LocallyDefinedHomRepresentativeOver.composeOver (J := J)
        (ordinaryHomToRepresentativeOver (J := J) X f)
        (ordinaryHomToRepresentativeOver (J := J) X g)) := by
  intro hbase
  let α := ordinaryHomToRepresentativeOver (J := J) X f
  let β := ordinaryHomToRepresentativeOver (J := J) X g
  let ord := ordinaryHomToRepresentativeOver (J := J) X (f ≫ g)
  let comp := LocallyDefinedHomRepresentativeOver.composeOver (J := J) α β
  apply (LocallyDefinedHomRepresentativeOver.toPlusSection_eq_iff_equivalent (J := J)
    (LocallyDefinedHomRepresentativeOver.castBase (J := J) hbase ord) comp).1
  rw [LocallyDefinedHomRepresentativeOver.castBase_toPlusSection_eq_mk_castBaseFamily]
  change GrothendieckTopology.Plus.mk
      (LocallyDefinedHomRepresentativeOver.castBaseFamily (J := J) hbase ord) =
    GrothendieckTopology.Plus.mk comp.family
  rw [GrothendieckTopology.Plus.eq_mk_iff_exists]
  let hOrd : comp.cover ⟶ ord.cover := homOfLE (by
    intro Y k hk
    trivial)
  refine ⟨comp.cover, hOrd, 𝟙 comp.cover, ?_⟩
  apply Meq.ext
  intro I
  apply eq_of_heq
  let IOrd : ord.cover.Arrow := ⟨I.Y, I.f, (leOfHom hOrd) _ I.hf⟩
  have hcast := LocallyDefinedHomRepresentativeOver.castBaseFamily_apply_heq (J := J)
    hbase ord IOrd
  refine HEq.trans hcast ?_
  let Fp := canonicalFiberPseudofunctor X.p
  let zF : X.p.Fiber (X.p.obj z) := Functor.Fiber.mk (p := X.p) (a := z) rfl
  let e := (Fp.map I.Y.hom.op.toLoc).toFunctor.map (ordinaryHomToPullbackFiberHom X (f ≫ g))
  let targetTransport :
      ((Fp.map (X.p.map (f ≫ g)).op.toLoc).toFunctor.obj zF) ⟶
        ((Fp.map (X.p.map f ≫ X.p.map g).op.toLoc).toFunctor.obj zF) :=
    (eqToHom (congrArg (fun k => (canonicalPullbackChoice X.p).pullbackFunctor k)
      hbase)).app zF
  let global :=
      ordinaryHomToPullbackFiberHom X f ≫
        (Fp.map (X.p.map f).op.toLoc).toFunctor.map
          (ordinaryHomToPullbackFiberHom X g) ≫
        (Fp.mapComp (X.p.map g).op.toLoc (X.p.map f).op.toLoc).inv.toNatTrans.app zF
  have hord :
      (ord.family IOrd).down = e := by
    simpa [ord, Fp, e] using
      ordinaryHomToRepresentativeOver_family_apply_down (J := J) X (f ≫ g) IOrd
  have hglobal :
      ordinaryHomToPullbackFiberHom X (f ≫ g) ≫ targetTransport = global := by
    simpa [Fp, zF, hbase, targetTransport, global] using
      ordinaryHomToPullbackFiberHom_comp_afterTransport X f g
  have hlocal :
      (LocallyDefinedHomRepresentativeOver.compositionLocal (J := J) α β I).down =
        (Fp.map I.Y.hom.op.toLoc).toFunctor.map global := by
    simpa [α, β, Fp, zF, global] using
      ordinaryCompositionLocal_down_eq_mapGlobal (J := J) X f g I
  have hmapGlobal :
      (Fp.map I.Y.hom.op.toLoc).toFunctor.map global =
        e ≫ (Fp.map I.Y.hom.op.toLoc).toFunctor.map targetTransport := by
    rw [← hglobal]
    simp [e, Functor.map_comp]
  have htail :
      HEq (e ≫ (Fp.map I.Y.hom.op.toLoc).toFunctor.map targetTransport) e := by
    simpa [Fp, zF, hbase, targetTransport, e] using
      canonicalFiberPseudofunctor_map_eqToHom_transport_tail_heq
        (p := X.p) hbase I.Y.hom zF (e := e)
  have hcompFamily :=
    LocallyDefinedHomRepresentativeOver.composeOver_family_apply (J := J) α β I
  have hcompDownToOrd :
      HEq ((LocallyDefinedHomRepresentativeOver.compositionLocal (J := J) α β I).down)
        (ord.family IOrd).down := by
    exact HEq.trans (heq_of_eq hlocal)
      (HEq.trans (heq_of_eq hmapGlobal)
        (HEq.trans htail (heq_of_eq hord.symm)))
  have hOrdToCompLocal :
      HEq (ord.family IOrd)
        (LocallyDefinedHomRepresentativeOver.compositionLocal (J := J) α β I) :=
    ulift_heq_of_down_heq hcompDownToOrd.symm
  have hCompLocalToFamily :
      HEq (LocallyDefinedHomRepresentativeOver.compositionLocal (J := J) α β I)
        (comp.family I) := by
    exact heq_of_eq hcompFamily.symm
  exact HEq.trans hOrdToCompLocal hCompLocalToFamily

/-- Raw-representative form of ordinary functoriality for composition. -/
theorem ordinaryHomToRepresentative_comp_equivalent
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y z : X.S} (f : x ⟶ y) (g : y ⟶ z) :
    LocallyDefinedHomRepresentative.Equivalent (J := J)
      (ordinaryHomToRepresentative (J := J) X (f ≫ g))
      (LocallyDefinedHomRepresentative.compose (J := J)
        (ordinaryHomToRepresentative (J := J) X f)
        (ordinaryHomToRepresentative (J := J) X g)) := by
  apply (LocallyDefinedHomRepresentative.equivalent_iff_exists_base_eq (J := J)
    (ordinaryHomToRepresentative (J := J) X (f ≫ g))
    (LocallyDefinedHomRepresentative.compose (J := J)
      (ordinaryHomToRepresentative (J := J) X f)
      (ordinaryHomToRepresentative (J := J) X g))).2
  refine ⟨X.p.map_comp f g, ?_⟩
  exact ordinaryHomToRepresentativeOver_comp_equivalent (J := J) X f g

/-- Ordinary arrows are compatible with the source locally-defined composition. -/
theorem ordinaryHomToLocallyDefinedHom_comp
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y z : X.S} (f : x ⟶ y) (g : y ⟶ z) :
    ordinaryHomToLocallyDefinedHom (J := J) X (f ≫ g) =
      LocallyDefinedHom.comp (J := J)
        (ordinaryHomToLocallyDefinedHom (J := J) X f)
        (ordinaryHomToLocallyDefinedHom (J := J) X g) := by
  calc
    ordinaryHomToLocallyDefinedHom (J := J) X (f ≫ g) =
        (ordinaryHomToRepresentative (J := J) X (f ≫ g)).toLocallyDefinedHom := rfl
    _ =
        (LocallyDefinedHomRepresentative.compose (J := J)
          (ordinaryHomToRepresentative (J := J) X f)
          (ordinaryHomToRepresentative (J := J) X g)).toLocallyDefinedHom :=
      ordinaryHomToRepresentative_comp_equivalent (J := J) X f g
    _ =
        LocallyDefinedHom.comp (J := J)
          (ordinaryHomToLocallyDefinedHom (J := J) X f)
          (ordinaryHomToLocallyDefinedHom (J := J) X g) := by
      rw [ordinaryHomToLocallyDefinedHom, ordinaryHomToLocallyDefinedHom]
      symm
      exact LocallyDefinedHom.comp_toLocallyDefinedHom (J := J)
        (ordinaryHomToRepresentative (J := J) X f)
        (ordinaryHomToRepresentative (J := J) X g)

namespace LocallyDefinedHomTotal

/-- The old-object comparison frontier with both owner-sensitive identity and composition
bridges discharged. -/
noncomputable def oldObjectComparisonFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C) :
    OldObjectComparisonFrontier (J := J) X :=
  oldObjectComparisonFrontierOfCompositionBridge (J := J) X
    (fun {x y z} f g =>
      ordinaryHomToLocallyDefinedHom_comp (J := J) X (x := x) (y := y) (z := z) f g)

/-- The old total category maps to the source stage 2 category after discharging the ordinary
identity and composition bridges. -/
noncomputable def oldObjectToSourceFunctor
    (X : FibredCategoryOver.{u, v, uX, vX} C) :
    letI := sourceCategory (J := J) X
    X.S ⥤ LocallyDefinedHomTotal (J := J) X :=
  oldObjectToSourceFunctorOfFrontier (J := J) X
    (oldObjectComparisonFrontier (J := J) X)

@[simp]
theorem oldObjectToSourceFunctor_obj_apply
    (X : FibredCategoryOver.{u, v, uX, vX} C) (x : X.S) :
    letI := sourceCategory (J := J) X
    (oldObjectToSourceFunctor (J := J) X).obj x = ofObj (J := J) X x := by
  letI := sourceCategory (J := J) X
  rfl

@[simp]
theorem oldObjectToSourceFunctor_map_apply
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y : X.S} (f : x ⟶ y) :
    letI := sourceCategory (J := J) X
    (oldObjectToSourceFunctor (J := J) X).map f =
      ordinaryHomToLocallyDefinedHom (J := J) X f := by
  letI := sourceCategory (J := J) X
  rfl

/-- Based-functor form of the old-object comparison into the source stage 2 projection. -/
noncomputable def oldObjectToSourceBasedFunctor
    (X : FibredCategoryOver.{u, v, uX, vX} C) :
    X.toBasedCategory ⥤ᵇ sourceBasedCategory (J := J) X :=
  oldObjectToSourceBasedFunctorOfFrontier (J := J) X
    (oldObjectComparisonFrontier (J := J) X)

end LocallyDefinedHomTotal

end FibredCategoryMor

end CategoryTheory
