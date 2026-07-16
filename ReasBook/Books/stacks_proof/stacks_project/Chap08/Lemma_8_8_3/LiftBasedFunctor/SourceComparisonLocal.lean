import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Vertical

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: on literal source-image objects, the glued vertical map is
natural with respect to the canonical comparison from the descended glued object to the original
source value. -/
theorem stackificationLiftVerticalMap_sourceImage_naturality
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {x x' : S.p.Fiber U} (φ : x ⟶ x') :
    stackificationLiftVerticalMap X G hG F
        ((FibredCategoryMor.fiberFunctor G U).map φ) ≫
      (stackificationLiftObjectSourceImageGluedIso X G hG F x').hom =
    (stackificationLiftObjectSourceImageGluedIso X G hG F x).hom ≫
      (FibredCategoryMor.fiberFunctor F U).map φ := by
  let y := (FibredCategoryMor.fiberFunctor G U).obj x
  let y' := (FibredCategoryMor.fiberFunctor G U).obj x'
  let d := (FibredCategoryMor.fiberFunctor G U).map φ
  let e := stackificationLiftObjectSourceImageGluedIso X G hG F x
  let e' := stackificationLiftObjectSourceImageGluedIso X G hG F x'
  apply stack_cover_hom_ext (J := J) X
    (stackificationLiftVerticalCommonCover (J := J) G hG y y')
  intro I
  let Iy := stackificationLiftVerticalCommonCover_left (J := J) G hG y y' I
  let Iy' := stackificationLiftVerticalCommonCover_right (J := J) G hG y y' I
  let M := ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor
  have hVert : M.map (stackificationLiftVerticalMap X G hG F d) =
      stackificationLiftVerticalLocalMap X G hG F d I := by
    simpa [M, d] using stackificationLiftVerticalMap_local X G hG F d I
  have he : M.map e.hom =
      (stackificationLiftObjectGluedLocalIso X G hG F y Iy).hom ≫
        (stackificationLiftObjectSourceImageLocalIso X G hG F x Iy).inv := by
    simpa [M, e, y, Iy] using
      stackificationLiftObjectSourceImageGluedIso_local_hom X G hG F x Iy
  have he' : M.map e'.hom =
      (stackificationLiftObjectGluedLocalIso X G hG F y' Iy').hom ≫
        (stackificationLiftObjectSourceImageLocalIso X G hG F x' Iy').inv := by
    simpa [M, e', y', Iy'] using
      stackificationLiftObjectSourceImageGluedIso_local_hom X G hG F x' Iy'
  change M.map ((stackificationLiftVerticalMap X G hG F d) ≫ e'.hom) =
    M.map (e.hom ≫ (FibredCategoryMor.fiberFunctor F U).map φ)
  rw [M.map_comp, M.map_comp]
  rw [hVert, he, he']
  let L := stackificationLiftObjectGluedLocalIso X G hG F y Iy
  let L' := stackificationLiftObjectGluedLocalIso X G hG F y' Iy'
  let sx := stackificationLiftObjectSourceImageLocalIso X G hG F x Iy
  let sx' := stackificationLiftObjectSourceImageLocalIso X G hG F x' Iy'
  let xI := (stackificationLiftObjectModel (J := J) G hG y Iy).1
  let xI' := (stackificationLiftObjectModel (J := J) G hG y' Iy').1
  let cy := (stackificationLiftObjectModel (J := J) G hG y Iy).2
  let cy' := (stackificationLiftObjectModel (J := J) G hG y' Iy').2
  let MG := ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor
  let α : ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ⟶
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI') :=
    cy.hom ≫ MG.map d ≫ cy'.inv
  let mid := stackificationLiftHomExtensionFiberMap X G hG F xI xI' α
  have hVL : stackificationLiftVerticalLocalMap X G hG F d I =
      L.hom ≫ mid ≫ L'.inv := by
    rfl
  rw [hVL]
  change (L.hom ≫ mid ≫ L'.inv) ≫ (L'.hom ≫ sx'.inv) =
    (L.hom ≫ sx.inv) ≫ M.map ((FibredCategoryMor.fiberFunctor F U).map φ)
  have hcore :
      mid ≫ sx'.inv =
        sx.inv ≫ M.map ((FibredCategoryMor.fiberFunctor F U).map φ) := by
    let MS := ((canonicalFiberPseudofunctor S.p).map I.f.op.toLoc).toFunctor
    let φI : (I.f ^*[canonicalPullbackChoice S.p] x) ⟶
        (I.f ^*[canonicalPullbackChoice S.p] x') := MS.map φ
    let cGx := FibredCategoryMor.pullbackComparison G I.f x
    let cGx' := FibredCategoryMor.pullbackComparison G I.f x'
    let cFx := FibredCategoryMor.pullbackComparison F I.f x
    let cFx' := FibredCategoryMor.pullbackComparison F I.f x'
    let β : ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ⟶
        ((FibredCategoryMor.fiberFunctor G I.Y).obj
          (I.f ^*[canonicalPullbackChoice S.p] x)) :=
      cy.hom ≫ cGx.hom
    let β' : ((FibredCategoryMor.fiberFunctor G I.Y).obj xI') ⟶
        ((FibredCategoryMor.fiberFunctor G I.Y).obj
          (I.f ^*[canonicalPullbackChoice S.p] x')) :=
      cy'.hom ≫ cGx'.hom
    have hFmap :
        M.map ((FibredCategoryMor.fiberFunctor F U).map φ) =
          cFx.hom ≫
            (FibredCategoryMor.fiberFunctor F I.Y).map φI ≫
            cFx'.inv := by
      have h :=
        FibredCategoryMor.pullbackComparison_naturality_over_vertical F I.f φ
      exact ((Iso.eq_comp_inv cFx').2 h).trans
        (Category.assoc cFx.hom ((FibredCategoryMor.fiberFunctor F I.Y).map φI) cFx'.inv)
    have hGmap :
        MG.map d ≫ cGx'.hom =
          cGx.hom ≫ (FibredCategoryMor.fiberFunctor G I.Y).map φI := by
      dsimp only [MG, MS, d, φI, cGx, cGx']
      exact FibredCategoryMor.pullbackComparison_naturality_over_vertical G I.f φ
    have hαβ :
        α ≫ β' =
          β ≫ (FibredCategoryMor.fiberFunctor G I.Y).map φI := by
      dsimp only [α, β, β']
      calc
        (cy.hom ≫ MG.map d ≫ cy'.inv) ≫ cy'.hom ≫ cGx'.hom =
            cy.hom ≫ MG.map d ≫ (cy'.inv ≫ cy'.hom) ≫ cGx'.hom := by
              simp only [Category.assoc]
        _ = cy.hom ≫ MG.map d ≫ cGx'.hom := by
              calc
                cy.hom ≫ MG.map d ≫ (cy'.inv ≫ cy'.hom) ≫ cGx'.hom =
                    cy.hom ≫ MG.map d ≫ (𝟙 _) ≫ cGx'.hom := by
                    exact congrArg
                      (fun t => cy.hom ≫ MG.map d ≫ t ≫ cGx'.hom)
                      cy'.inv_hom_id
                _ = cy.hom ≫ MG.map d ≫ cGx'.hom := by
                    simp only [Category.id_comp]
        _ = cy.hom ≫ (MG.map d ≫ cGx'.hom) := by
              rfl
        _ = cy.hom ≫ (cGx.hom ≫
              (FibredCategoryMor.fiberFunctor G I.Y).map φI) := by
              exact congrArg (fun t => cy.hom ≫ t) hGmap
        _ = (cy.hom ≫ cGx.hom) ≫
              (FibredCategoryMor.fiberFunctor G I.Y).map φI := by
              simp only [Category.assoc]
    have hmid :
        mid ≫ stackificationLiftHomExtensionFiberMap X G hG F
            xI' (I.f ^*[canonicalPullbackChoice S.p] x') β' =
          stackificationLiftHomExtensionFiberMap X G hG F
            xI (I.f ^*[canonicalPullbackChoice S.p] x) β ≫
            (FibredCategoryMor.fiberFunctor F I.Y).map φI := by
      let Hβ' := stackificationLiftHomExtensionFiberMap X G hG F
        xI' (I.f ^*[canonicalPullbackChoice S.p] x') β'
      let Hαβ := stackificationLiftHomExtensionFiberMap X G hG F
        xI (I.f ^*[canonicalPullbackChoice S.p] x') (α ≫ β')
      let HβG := stackificationLiftHomExtensionFiberMap X G hG F
        xI (I.f ^*[canonicalPullbackChoice S.p] x')
          (β ≫ (FibredCategoryMor.fiberFunctor G I.Y).map φI)
      let Hβ := stackificationLiftHomExtensionFiberMap X G hG F
        xI (I.f ^*[canonicalPullbackChoice S.p] x) β
      let HGφ := stackificationLiftHomExtensionFiberMap X G hG F
        (I.f ^*[canonicalPullbackChoice S.p] x)
        (I.f ^*[canonicalPullbackChoice S.p] x')
        ((FibredCategoryMor.fiberFunctor G I.Y).map φI)
      have h1 : mid ≫ Hβ' = Hαβ := by
        dsimp only [mid, Hβ', Hαβ]
        exact (stackificationLiftHomExtensionFiberMap_comp X G hG F α β').symm
      have h2 : Hαβ = HβG := by
        dsimp only [Hαβ, HβG]
        exact congrArg
          (fun t => stackificationLiftHomExtensionFiberMap X G hG F
            xI (I.f ^*[canonicalPullbackChoice S.p] x') t)
          hαβ
      have h3 : HβG = Hβ ≫ HGφ := by
        dsimp only [HβG, Hβ, HGφ]
        exact stackificationLiftHomExtensionFiberMap_comp X G hG F β
          ((FibredCategoryMor.fiberFunctor G I.Y).map φI)
      have h4 : HGφ = (FibredCategoryMor.fiberFunctor F I.Y).map φI := by
        dsimp only [HGφ]
        exact stackificationLiftHomExtensionFiberMap_on_image X G hG F φI
      exact h1.trans (h2.trans (h3.trans
        (congrArg (fun t => Hβ ≫ t) h4)))
    dsimp only [sx, sx', stackificationLiftObjectSourceImageLocalIso]
    change
      mid ≫
          stackificationLiftHomExtensionFiberMap X G hG F
            xI' (I.f ^*[canonicalPullbackChoice S.p] x') β' ≫ cFx'.inv =
        (stackificationLiftHomExtensionFiberMap X G hG F
            xI (I.f ^*[canonicalPullbackChoice S.p] x) β ≫ cFx.inv) ≫
          M.map ((FibredCategoryMor.fiberFunctor F U).map φ)
    rw [hFmap]
    calc
      mid ≫
          stackificationLiftHomExtensionFiberMap X G hG F
            xI' (I.f ^*[canonicalPullbackChoice S.p] x') β' ≫ cFx'.inv =
        (stackificationLiftHomExtensionFiberMap X G hG F
            xI (I.f ^*[canonicalPullbackChoice S.p] x) β ≫
          (FibredCategoryMor.fiberFunctor F I.Y).map φI) ≫ cFx'.inv := by
          calc
            mid ≫
                stackificationLiftHomExtensionFiberMap X G hG F
                  xI' (I.f ^*[canonicalPullbackChoice S.p] x') β' ≫ cFx'.inv =
              (mid ≫
                stackificationLiftHomExtensionFiberMap X G hG F
                  xI' (I.f ^*[canonicalPullbackChoice S.p] x') β') ≫ cFx'.inv := by
                simp only [Category.assoc]
            _ = (stackificationLiftHomExtensionFiberMap X G hG F
                xI (I.f ^*[canonicalPullbackChoice S.p] x) β ≫
              (FibredCategoryMor.fiberFunctor F I.Y).map φI) ≫ cFx'.inv := by
                exact congrArg (fun t => t ≫ cFx'.inv) hmid
      _ =
        (stackificationLiftHomExtensionFiberMap X G hG F
            xI (I.f ^*[canonicalPullbackChoice S.p] x) β ≫ cFx.inv) ≫
          (cFx.hom ≫ (FibredCategoryMor.fiberFunctor F I.Y).map φI ≫ cFx'.inv) := by
          calc
            (stackificationLiftHomExtensionFiberMap X G hG F
                xI (I.f ^*[canonicalPullbackChoice S.p] x) β ≫
              (FibredCategoryMor.fiberFunctor F I.Y).map φI) ≫ cFx'.inv =
              stackificationLiftHomExtensionFiberMap X G hG F
                xI (I.f ^*[canonicalPullbackChoice S.p] x) β ≫
                (FibredCategoryMor.fiberFunctor F I.Y).map φI ≫ cFx'.inv := by
                simp only [Category.assoc]
            _ =
              stackificationLiftHomExtensionFiberMap X G hG F
                xI (I.f ^*[canonicalPullbackChoice S.p] x) β ≫
                (cFx.inv ≫ cFx.hom) ≫
                (FibredCategoryMor.fiberFunctor F I.Y).map φI ≫ cFx'.inv := by
                calc
                  stackificationLiftHomExtensionFiberMap X G hG F
                      xI (I.f ^*[canonicalPullbackChoice S.p] x) β ≫
                    (FibredCategoryMor.fiberFunctor F I.Y).map φI ≫ cFx'.inv =
                    stackificationLiftHomExtensionFiberMap X G hG F
                      xI (I.f ^*[canonicalPullbackChoice S.p] x) β ≫
                    (𝟙 _) ≫
                    (FibredCategoryMor.fiberFunctor F I.Y).map φI ≫ cFx'.inv := by
                    simp only [Category.id_comp]
                  _ =
                    stackificationLiftHomExtensionFiberMap X G hG F
                      xI (I.f ^*[canonicalPullbackChoice S.p] x) β ≫
                    (cFx.inv ≫ cFx.hom) ≫
                    (FibredCategoryMor.fiberFunctor F I.Y).map φI ≫ cFx'.inv := by
                    exact congrArg
                      (fun t =>
                        stackificationLiftHomExtensionFiberMap X G hG F
                          xI (I.f ^*[canonicalPullbackChoice S.p] x) β ≫
                        t ≫ (FibredCategoryMor.fiberFunctor F I.Y).map φI ≫ cFx'.inv)
                      cFx.inv_hom_id.symm
            _ =
              (stackificationLiftHomExtensionFiberMap X G hG F
                  xI (I.f ^*[canonicalPullbackChoice S.p] x) β ≫ cFx.inv) ≫
                (cFx.hom ≫ (FibredCategoryMor.fiberFunctor F I.Y).map φI ≫
                  cFx'.inv) := by
                simp only [Category.assoc]
  calc
    (L.hom ≫ mid ≫ L'.inv) ≫ (L'.hom ≫ sx'.inv) =
        L.hom ≫ (mid ≫ sx'.inv) := by
          calc
            (L.hom ≫ mid ≫ L'.inv) ≫ (L'.hom ≫ sx'.inv) =
                L.hom ≫ mid ≫ (L'.inv ≫ L'.hom) ≫ sx'.inv := by
                simp only [Category.assoc]
            _ = L.hom ≫ mid ≫ sx'.inv := by
                calc
                  L.hom ≫ mid ≫ (L'.inv ≫ L'.hom) ≫ sx'.inv =
                      L.hom ≫ mid ≫ (𝟙 _) ≫ sx'.inv := by
                      exact congrArg (fun t => L.hom ≫ mid ≫ t ≫ sx'.inv)
                        L'.inv_hom_id
                  _ = L.hom ≫ mid ≫ sx'.inv := by
                      simp only [Category.id_comp]
            _ = L.hom ≫ (mid ≫ sx'.inv) := by
                rfl
    _ = L.hom ≫ (sx.inv ≫ M.map ((FibredCategoryMor.fiberFunctor F U).map φ)) := by
          exact congrArg (fun t => L.hom ≫ t) hcore
    _ = (L.hom ≫ sx.inv) ≫ M.map ((FibredCategoryMor.fiberFunctor F U).map φ) := by
          simp only [Category.assoc]

end

end CategoryTheory
