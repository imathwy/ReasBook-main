import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.SourceComparisonPullback
import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Cartesian
import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Arrows.VerticalFactorUniqueness

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- The source comparison is natural on arrows coming from the stackification source. -/
theorem stackificationLiftBasedFunctor_sourceIso_naturality
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {T T' : S.S} (φ : T ⟶ T') :
    stackificationLiftBasedFunctorMap X G hG F (G.toHom.map φ) ≫
      (stackificationLiftBasedFunctorObj_sourceIso X G hG F T').hom =
    (stackificationLiftBasedFunctorObj_sourceIso X G hG F T).hom ≫
      F.toHom.map φ := by
  let U : C := S'.p.obj (G.toHom.obj T')
  let V : C := S'.p.obj (G.toHom.obj T)
  have hxbase : S.p.obj T = V := by
    dsimp only [V]
    symm
    simpa only [FibredCategoryMor.toFunctor] using
      congrArg (fun H : S.S ⥤ C => H.obj T) (FibredCategoryMor.comm G)
  have hx'base : S.p.obj T' = U := by
    dsimp only [U]
    symm
    simpa only [FibredCategoryMor.toFunctor] using
      congrArg (fun H : S.S ⥤ C => H.obj T') (FibredCategoryMor.comm G)
  let x : S.p.Fiber V := Functor.Fiber.mk (p := S.p) (a := T) hxbase
  let x' : S.p.Fiber U := Functor.Fiber.mk (p := S.p) (a := T') hx'base
  let ySource : S'.p.Fiber V :=
    Functor.Fiber.mk (p := S'.p) (a := G.toHom.obj T) rfl
  let yImage : S'.p.Fiber V := (FibredCategoryMor.fiberFunctor G V).obj x
  have hy : ySource = yImage := by
    apply Functor.Fiber.fiberInclusion_obj_inj
    rfl
  let ySource' : S'.p.Fiber U :=
    Functor.Fiber.mk (p := S'.p) (a := G.toHom.obj T') rfl
  let yImage' : S'.p.Fiber U := (FibredCategoryMor.fiberFunctor G U).obj x'
  have hy' : ySource' = yImage' := by
    apply Functor.Fiber.fiberInclusion_obj_inj
    rfl
  let sx := stackificationLiftObjectSourceImageGluedIso X G hG F x
  let sx' := stackificationLiftObjectSourceImageGluedIso X G hG F x'
  let eTotal :=
    (Functor.Fiber.fiberInclusion : X.p.Fiber V ⥤ X.S).mapIso sx
  have hSourceEq :
      stackificationLiftBasedFunctorObj X G hG F (G.toHom.obj T) =
        (Functor.Fiber.fiberInclusion : X.p.Fiber V ⥤ X.S).obj
          (stackificationLiftObjectGlued X G hG F yImage) := by
    dsimp only [stackificationLiftBasedFunctorObj, ySource]
    exact congrArg
      (fun y : S'.p.Fiber V =>
        (stackificationLiftObjectGlued X G hG F y).1)
      hy
  let eSource :
      stackificationLiftBasedFunctorObj X G hG F (G.toHom.obj T) ≅
        (Functor.Fiber.fiberInclusion : X.p.Fiber V ⥤ X.S).obj
          (stackificationLiftObjectGlued X G hG F yImage) :=
    eqToIso hSourceEq
  have hTargetEq :
      (Functor.Fiber.fiberInclusion : X.p.Fiber V ⥤ X.S).obj
          ((FibredCategoryMor.fiberFunctor F V).obj x) =
        F.toHom.obj T :=
    rfl
  let eTarget :
      (Functor.Fiber.fiberInclusion : X.p.Fiber V ⥤ X.S).obj
          ((FibredCategoryMor.fiberFunctor F V).obj x) ≅
        F.toHom.obj T :=
    eqToIso hTargetEq
  have hshape :
      (stackificationLiftBasedFunctorObj_sourceIso X G hG F T).hom =
        (eSource ≪≫ eTotal ≪≫ eTarget).hom := by
    rfl
  let eTotal' :=
    (Functor.Fiber.fiberInclusion : X.p.Fiber U ⥤ X.S).mapIso sx'
  have hSourceEq' :
      stackificationLiftBasedFunctorObj X G hG F (G.toHom.obj T') =
        (Functor.Fiber.fiberInclusion : X.p.Fiber U ⥤ X.S).obj
          (stackificationLiftObjectGlued X G hG F yImage') := by
    dsimp only [stackificationLiftBasedFunctorObj, ySource']
    exact congrArg
      (fun y : S'.p.Fiber U =>
        (stackificationLiftObjectGlued X G hG F y).1)
      hy'
  let eSource' :
      stackificationLiftBasedFunctorObj X G hG F (G.toHom.obj T') ≅
        (Functor.Fiber.fiberInclusion : X.p.Fiber U ⥤ X.S).obj
          (stackificationLiftObjectGlued X G hG F yImage') :=
    eqToIso hSourceEq'
  have hTargetEq' :
      (Functor.Fiber.fiberInclusion : X.p.Fiber U ⥤ X.S).obj
          ((FibredCategoryMor.fiberFunctor F U).obj x') =
        F.toHom.obj T' :=
    rfl
  let eTarget' :
      (Functor.Fiber.fiberInclusion : X.p.Fiber U ⥤ X.S).obj
          ((FibredCategoryMor.fiberFunctor F U).obj x') ≅
        F.toHom.obj T' :=
    eqToIso hTargetEq'
  have hshape' :
      (stackificationLiftBasedFunctorObj_sourceIso X G hG F T').hom =
        (eSource' ≪≫ eTotal' ≪≫ eTarget').hom := by
    rfl
  let f : V ⟶ U := S'.p.map (G.toHom.map φ)
  have hφLift : S.p.IsHomLift f φ := by
    refine IsHomLift.of_fac S.p f φ hxbase hx'base ?_
    dsimp only [f, U, V]
    have hcomm := Functor.congr_hom (FibredCategoryMor.comm G) φ
    simpa only [FibredCategoryMor.toFunctor] using hcomm
  let cartS := (canonicalPullbackChoice S.p).map f x'
  have hcartS : S.p.IsStronglyCartesian f cartS :=
    (canonicalPullbackChoice S.p).isStronglyCartesian f x'
  haveI : S.p.IsStronglyCartesian f cartS := hcartS
  let φTo : T ⟶ x'.1 := φ
  have hφToLift : S.p.IsHomLift f φTo := by
    simpa [φTo] using hφLift
  haveI : S.p.IsHomLift f φTo := hφToLift
  have hf_id : f = 𝟙 V ≫ f := by simp
  let vhom : T ⟶ (f ^*[canonicalPullbackChoice S.p] x').1 :=
    Functor.IsStronglyCartesian.map (p := S.p) (f := f) (φ := cartS)
      (g := 𝟙 V) (f' := f) hf_id φTo
  have hvhom : S.p.IsHomLift (𝟙 V) vhom := by
    dsimp only [vhom]
    exact Functor.IsStronglyCartesian.map_isHomLift (p := S.p) (f := f) (φ := cartS)
      (g := 𝟙 V) (f' := f) hf_id φTo
  let v : x ⟶ f ^*[canonicalPullbackChoice S.p] x' := ⟨vhom, hvhom⟩
  have hv_fac : v.1 ≫ cartS = φ := by
    have hfacTo : vhom ≫ cartS = φTo := by
      dsimp only [vhom, cartS]
      exact Functor.IsStronglyCartesian.fac (p := S.p) (f := f)
        (φ := (canonicalPullbackChoice S.p).map f x') (g := 𝟙 V) (f' := f) hf_id φTo
    simpa [v, φTo] using hfacTo
  cases hy
  cases hy'
  let cG := FibredCategoryMor.pullbackComparison G f x'
  let vG : yImage ⟶ stackificationLiftArrowPullbackTarget (S' := S') (G.toHom.map φ) :=
    (FibredCategoryMor.fiberFunctor G V).map v ≫ cG.inv
  have hvG_fac :
      vG.1 ≫
        (canonicalPullbackChoice S'.p).map (S'.p.map (G.toHom.map φ))
          (Functor.Fiber.mk (p := S'.p) (a := G.toHom.obj T') rfl :
            S'.p.Fiber (S'.p.obj (G.toHom.obj T'))) =
        G.toHom.map φ := by
    dsimp only [vG, stackificationLiftArrowPullbackTarget, f, cG]
    have hpost :
        (FibredCategoryMor.pullbackComparison G f x').inv.1 ≫
          (canonicalPullbackChoice S'.p).map f ((FibredCategoryMor.fiberFunctor G U).obj x') =
        G.toHom.map ((canonicalPullbackChoice S.p).map f x') :=
      FibredCategoryMor.pullbackComparison_inv_postcompose_owner G f x'
    have hvmap :
        ((FibredCategoryMor.fiberFunctor G V).map v).1 = G.toHom.map v.1 := by
      rfl
    have hfirst :
        (((FibredCategoryMor.fiberFunctor G V).map v).1 ≫
              (FibredCategoryMor.pullbackComparison G f x').inv.1) ≫
            (canonicalPullbackChoice S'.p).map f ((FibredCategoryMor.fiberFunctor G U).obj x') =
          ((FibredCategoryMor.fiberFunctor G V).map v).1 ≫
            G.toHom.map ((canonicalPullbackChoice S.p).map f x') := by
      calc
        (((FibredCategoryMor.fiberFunctor G V).map v).1 ≫
              (FibredCategoryMor.pullbackComparison G f x').inv.1) ≫
            (canonicalPullbackChoice S'.p).map f ((FibredCategoryMor.fiberFunctor G U).obj x') =
            ((FibredCategoryMor.fiberFunctor G V).map v).1 ≫
              ((FibredCategoryMor.pullbackComparison G f x').inv.1 ≫
                (canonicalPullbackChoice S'.p).map f ((FibredCategoryMor.fiberFunctor G U).obj x')) := by
              rw [Category.assoc]
        _ = ((FibredCategoryMor.fiberFunctor G V).map v).1 ≫
              G.toHom.map ((canonicalPullbackChoice S.p).map f x') := by
              exact congrArg (fun m => ((FibredCategoryMor.fiberFunctor G V).map v).1 ≫ m) hpost
    have hsecond :
        ((FibredCategoryMor.fiberFunctor G V).map v).1 ≫
            G.toHom.map ((canonicalPullbackChoice S.p).map f x') =
          G.toHom.map φ := by
      rw [hvmap]
      have hcomp := G.toHom.map_comp v.1 ((canonicalPullbackChoice S.p).map f x')
      exact hcomp.symm.trans (congrArg (fun m => G.toHom.map m) hv_fac)
    exact hfirst.trans hsecond
  have hfactor_eq :
      stackificationLiftArrowVerticalFactor (S' := S') (G.toHom.map φ) = vG := by
    exact stackificationLiftArrowVerticalFactor_eq_of_fac
      (S' := S') (G.toHom.map φ) vG hvG_fac
  let cF := FibredCategoryMor.pullbackComparison F f x'
  let P := stackificationLiftObjectPullbackComparison X G hG F f
    ((FibredCategoryMor.fiberFunctor G U).obj x')
  let M := ((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor
  let cartGlued :=
    (canonicalPullbackChoice X.p).map f
      (stackificationLiftObjectGlued X G hG F ((FibredCategoryMor.fiberFunctor G U).obj x'))
  let cartF :=
    (canonicalPullbackChoice X.p).map f ((FibredCategoryMor.fiberFunctor F U).obj x')
  have hcore :=
    stackificationLiftObjectSourceImage_arrowCore_naturality X G hG F f x' v
  have hcart_sx :
      cartGlued ≫ sx'.hom.1 = (M.map sx'.hom).1 ≫ cartF := by
    exact (FibredCategoryMor.canonical_pullbackFunctor_map_fac (p := X.p) (f := f)
      (φ := sx'.hom)).symm
  have hright_cart :
      ((sx.hom ≫ (FibredCategoryMor.fiberFunctor F V).map v ≫ cF.inv).1) ≫ cartF =
        sx.hom.1 ≫ F.toHom.map φ := by
    have hFpost :
        cF.inv.1 ≫ cartF =
          F.toHom.map ((canonicalPullbackChoice S.p).map f x') :=
      FibredCategoryMor.pullbackComparison_inv_postcompose_owner F f x'
    have hFv :
        ((FibredCategoryMor.fiberFunctor F V).map v).1 = F.toHom.map v.1 := by
      rfl
    have h0 :
        ((sx.hom ≫ (FibredCategoryMor.fiberFunctor F V).map v ≫ cF.inv).1) ≫ cartF =
          sx.hom.1 ≫ ((FibredCategoryMor.fiberFunctor F V).map v).1 ≫
            (cF.inv.1 ≫ cartF) := by
      let a := (FibredCategoryMor.fiberFunctor F V).map v
      change ((sx.hom ≫ (a ≫ cF.inv)).1) ≫ cartF =
        sx.hom.1 ≫ a.1 ≫ (cF.inv.1 ≫ cartF)
      have hproj₁ :
          (sx.hom ≫ (a ≫ cF.inv)).1 = sx.hom.1 ≫ (a ≫ cF.inv).1 := by
        rfl
      have hproj₀ : (a ≫ cF.inv).1 = a.1 ≫ cF.inv.1 := by
        rfl
      calc
        ((sx.hom ≫ (a ≫ cF.inv)).1) ≫ cartF =
            (sx.hom.1 ≫ (a ≫ cF.inv).1) ≫ cartF := by
              rw [hproj₁]
        _ = (sx.hom.1 ≫ (a.1 ≫ cF.inv.1)) ≫ cartF := by
              rw [hproj₀]
        _ = sx.hom.1 ≫ a.1 ≫ (cF.inv.1 ≫ cartF) := by
              simp only [Category.assoc]
    have h1 :
        sx.hom.1 ≫ ((FibredCategoryMor.fiberFunctor F V).map v).1 ≫
            (cF.inv.1 ≫ cartF) =
          sx.hom.1 ≫ ((FibredCategoryMor.fiberFunctor F V).map v).1 ≫
            F.toHom.map ((canonicalPullbackChoice S.p).map f x') := by
      exact congrArg
        (fun m => sx.hom.1 ≫ ((FibredCategoryMor.fiberFunctor F V).map v).1 ≫ m)
        hFpost
    have hcompF :
        F.toHom.map v.1 ≫
            F.toHom.map ((canonicalPullbackChoice S.p).map f x') =
          F.toHom.map φ := by
      exact (F.toHom.map_comp v.1 ((canonicalPullbackChoice S.p).map f x')).symm.trans
        (congrArg (fun m => F.toHom.map m) hv_fac)
    have h2 :
        sx.hom.1 ≫ ((FibredCategoryMor.fiberFunctor F V).map v).1 ≫
            F.toHom.map ((canonicalPullbackChoice S.p).map f x') =
        sx.hom.1 ≫ F.toHom.map φ := by
      rw [hFv]
      exact congrArg (fun m => sx.hom.1 ≫ m) hcompF
    exact h0.trans (h1.trans h2)
  have hshape_reduced :
      (stackificationLiftBasedFunctorObj_sourceIso X G hG F T).hom = sx.hom.1 := by
    rw [hshape]
    dsimp only [Iso.trans_hom, Functor.mapIso_hom]
    cases hSourceEq
    cases hTargetEq
    dsimp only [eSource, eTarget]
    change (𝟙 _ : _ ⟶ _) ≫ eTotal.hom ≫ (𝟙 _ : _ ⟶ _) = sx.hom.1
    simp only [Category.id_comp, Category.comp_id]
    rfl
  have hshape'_reduced :
      (stackificationLiftBasedFunctorObj_sourceIso X G hG F T').hom = sx'.hom.1 := by
    rw [hshape']
    dsimp only [Iso.trans_hom, Functor.mapIso_hom]
    cases hSourceEq'
    cases hTargetEq'
    dsimp only [eSource', eTarget']
    change (𝟙 _ : _ ⟶ _) ≫ eTotal'.hom ≫ (𝟙 _ : _ ⟶ _) = sx'.hom.1
    simp only [Category.id_comp, Category.comp_id]
    rfl
  rw [hshape_reduced, hshape'_reduced]
  dsimp only [stackificationLiftBasedFunctorMap]
  rw [hfactor_eq]
  calc
    ((stackificationLiftVerticalMap X G hG F vG).1 ≫ P.hom.1 ≫ cartGlued) ≫ sx'.hom.1 =
        ((stackificationLiftVerticalMap X G hG F vG ≫ P.hom ≫ M.map sx'.hom).1) ≫
          cartF := by
        let A := stackificationLiftVerticalMap X G hG F vG
        have hcomp :
            (A ≫ P.hom ≫ M.map sx'.hom).1 =
              A.1 ≫ (P.hom.1 ≫ (M.map sx'.hom).1) := by
          rfl
        calc
          (A.1 ≫ P.hom.1 ≫ cartGlued) ≫ sx'.hom.1 =
              A.1 ≫ P.hom.1 ≫ (cartGlued ≫ sx'.hom.1) := by
                simp only [Category.assoc]
          _ = A.1 ≫ P.hom.1 ≫ ((M.map sx'.hom).1 ≫ cartF) := by
                exact congrArg (fun m => A.1 ≫ P.hom.1 ≫ m) hcart_sx
          _ = ((A ≫ P.hom ≫ M.map sx'.hom).1) ≫ cartF := by
                rw [hcomp]
                simp only [Category.assoc]
    _ = ((sx.hom ≫ (FibredCategoryMor.fiberFunctor F V).map v ≫ cF.inv).1) ≫
          cartF := by
        exact congrArg (fun m => m.1 ≫ cartF) hcore
    _ = sx.hom.1 ≫ F.toHom.map φ := hright_cart

end

end CategoryTheory
