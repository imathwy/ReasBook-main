import Mathlib
import stacks_proof.stacks_project.Chap08.Lemma_8_11_5.FiberIso

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open FibredCategoryOver

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ Zₛ : StackInGroupoidsOver J}

/-- Helper for Lemma 8.11.6: two local object-image isomorphisms compose after passing through
the pullback-comparison and chosen composite-pullback isomorphisms. -/
private noncomputable def compLocalEssentialImageIso
    (F : Xₛ ⟶ Yₛ) (G : Yₛ ⟶ Zₛ)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (z : Zₛ.p.Fiber U) (y : Yₛ.p.Fiber V) (x : Xₛ.p.Fiber W)
    (ηF : (F.fiberFunctor W).obj x ≅ g ^*[canonicalPullbackChoice Yₛ.p] y)
    (ηG : (G.fiberFunctor V).obj y ≅ f ^*[canonicalPullbackChoice Zₛ.p] z) :
    ((F ≫ G).fiberFunctor W).obj x ≅
      (g ≫ f) ^*[canonicalPullbackChoice Zₛ.p] z :=
  Iso.trans
    (Iso.trans
      (Functor.mapIso (G.fiberFunctor W) ηF)
      (FibredCategoryMor.pullbackComparison G.toFibredCategoryMor g y).symm)
    (Iso.trans
      (((canonicalPullbackChoice Zₛ.p).pullbackFunctor g).mapIso ηG)
      ((canonicalPullbackChoice Zₛ.p).pullbackCompComponentIso f g z).symm)

/-- Helper for Lemma 8.11.6: local essential-surjectivity on objects is stable under composition
of morphisms of stacks in groupoids. -/
private theorem locallyEssentiallySurjectiveOnObjects_comp
    (F : Xₛ ⟶ Yₛ) (G : Yₛ ⟶ Zₛ)
    (hF : StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects F)
    (hG : StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects G) :
    StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects (F ≫ G) := by
  classical
  intro U z
  -- Lift `z` locally through `G`, then lift the chosen local `Y`-object through `F`.
  obtain ⟨S, hS⟩ := hG U z
  choose y hy using hS
  let T : ∀ I : S.Arrow, J.Cover I.Y := fun I => Classical.choose (hF I.Y (y I))
  have hT : ∀ I : S.Arrow, ∀ K : (T I).Arrow,
      ∃ x : Xₛ.p.Fiber K.Y,
        Nonempty (((F.fiberFunctor K.Y).obj x) ≅ K.f ^*[canonicalPullbackChoice Yₛ.p] (y I)) := by
    intro I
    exact Classical.choose_spec (hF I.Y (y I))
  refine ⟨S.bind T, ?_⟩
  intro A
  -- An arrow of the bound cover is a second-stage arrow followed by a first-stage arrow.
  let I : S.Arrow := A.fromMiddle
  let K : (T I).Arrow := A.toMiddle
  obtain ⟨x, hx⟩ := hT I K
  refine ⟨x, ?_⟩
  obtain ⟨ηF⟩ := hx
  obtain ⟨ηG⟩ := hy I
  -- The adapter iso has target pullback along `K.f ≫ I.f`; `middle_spec` identifies this with
  -- the actual bound-cover arrow.
  rw [← A.middle_spec]
  refine ⟨?_⟩
  simpa [I, K, BasedFunctor.comp] using
    compLocalEssentialImageIso (J := J) F G I.f K.f z (y I) x ηF ηG

/-- Helper for Lemma 8.11.6: the hom side of the chosen pullback-composition isomorphism is
natural in the object of the source fiber. -/
private theorem pullbackCompComponentIso_hom_naturality
    {S : Type*} [Category S] {p : S ⥤ C} (hc : PullbackChoice p)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {X Y : p.Fiber U} (θ : X ⟶ Y) :
    (hc.pullbackFunctor (g ≫ f)).map θ ≫
        (hc.pullbackCompComponentIso f g Y).hom =
      (hc.pullbackCompComponentIso f g X).hom ≫
        (hc.pullbackFunctor g).map ((hc.pullbackFunctor f).map θ) := by
  -- This is the naturality square of the pullback-composition comparison, repackaged so later
  -- square pasting can rewrite the composite pullback into an iterated pullback.
  simpa [PullbackChoice.pullbackCompIso] using (hc.pullbackCompIso f g).hom.naturality θ

/-- Helper for Lemma 8.11.6: pullback comparisons for a stack morphism are compatible with
composing two base arrows. -/
private theorem pullbackComparison_baseComp_hom
    (F : Xₛ ⟶ Yₛ)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (x : Xₛ.p.Fiber U) :
    (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor (g ≫ f) x).hom ≫
        (F.fiberFunctor W).map ((canonicalPullbackChoice Xₛ.p).pullbackCompComponentIso f g x).hom =
      ((canonicalPullbackChoice Yₛ.p).pullbackCompComponentIso f g
        ((F.fiberFunctor U).obj x)).hom ≫
        ((canonicalPullbackChoice Yₛ.p).pullbackFunctor g).map
          (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom ≫
        (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor g
          (f ^*[canonicalPullbackChoice Xₛ.p] x)).hom := by
  let hcX := canonicalPullbackChoice Xₛ.p
  let hcY := canonicalPullbackChoice Yₛ.p
  let efg := FibredCategoryMor.pullbackComparison F.toFibredCategoryMor (g ≫ f) x
  let ef := FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x
  let eg := FibredCategoryMor.pullbackComparison F.toFibredCategoryMor g (f ^*[hcX] x)
  let cX := hcX.pullbackCompComponentIso f g x
  let cY := hcY.pullbackCompComponentIso f g ((F.fiberFunctor U).obj x)
  apply Functor.Fiber.hom_ext
  let θ := F.toFibredCategoryMor.toHom.map (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x)
  have hθ : Yₛ.p.IsStronglyCartesian (g ≫ f) θ := by
    have hcartX :
        Xₛ.p.IsStronglyCartesian (g ≫ f)
          (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x) := by
      letI : Xₛ.p.IsStronglyCartesian g (hcX.map g (f ^*[hcX] x)) :=
        hcX.isStronglyCartesian g (f ^*[hcX] x)
      letI : Xₛ.p.IsStronglyCartesian f (hcX.map f x) :=
        hcX.isStronglyCartesian f x
      infer_instance
    exact
      FibredCategoryMor.map_stronglyCartesian_of_lift F.toFibredCategoryMor
        (g ≫ f) (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x) hcartX
  have hleft : Yₛ.p.IsHomLift (𝟙 W)
      ((efg.hom ≫ (F.fiberFunctor W).map cX.hom).1) := by
    exact (efg.hom ≫ (F.fiberFunctor W).map cX.hom).2
  have hright : Yₛ.p.IsHomLift (𝟙 W)
      ((cY.hom ≫ (hcY.pullbackFunctor g).map ef.hom ≫ eg.hom).1) := by
    exact (cY.hom ≫ (hcY.pullbackFunctor g).map ef.hom ≫ eg.hom).2
  have hpost :
      ((efg.hom ≫ (F.fiberFunctor W).map cX.hom).1) ≫ θ =
        ((cY.hom ≫ (hcY.pullbackFunctor g).map ef.hom ≫ eg.hom).1) ≫ θ := by
    -- After postcomposing with the strongly-cartesian composite pullback arrow, both sides reduce
    -- to the same chosen pullback map by the defining comparison identities.
    change
      ((efg.hom.1 ≫ ((F.fiberFunctor W).map cX.hom).1) ≫ θ =
        (cY.hom.1 ≫ ((hcY.pullbackFunctor g).map ef.hom).1 ≫ eg.hom.1) ≫ θ)
    change
      ((efg.hom.1 ≫ F.toFibredCategoryMor.toHom.map cX.hom.1) ≫
          F.toFibredCategoryMor.toHom.map (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x) =
        (cY.hom.1 ≫ ((hcY.pullbackFunctor g).map ef.hom).1 ≫ eg.hom.1) ≫
          F.toFibredCategoryMor.toHom.map (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x))
    have hcXfac :
        cX.hom.1 ≫ hcX.map g (f ^*[hcX] x) ≫ hcX.map f x =
          hcX.map (g ≫ f) x := by
      simpa only [cX] using hcX.pullbackCompComponentIso_fac f g x
    have hmapX :
        F.toFibredCategoryMor.toHom.map cX.hom.1 ≫
            F.toFibredCategoryMor.toHom.map
              (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x) =
          F.toFibredCategoryMor.toHom.map (hcX.map (g ≫ f) x) := by
      rw [← Functor.map_comp]
      exact congrArg F.toFibredCategoryMor.toHom.map hcXfac
    have hefg :
        efg.hom.1 ≫ F.toFibredCategoryMor.toHom.map (hcX.map (g ≫ f) x) =
          hcY.map (g ≫ f) ((F.fiberFunctor U).obj x) := by
      simpa only [efg] using
        FibredCategoryMor.pullbackComparison_hom_postcompose
          F.toFibredCategoryMor (g ≫ f) x
    have hef :
        ef.hom.1 ≫ F.toFibredCategoryMor.toHom.map (hcX.map f x) =
          hcY.map f ((F.fiberFunctor U).obj x) := by
      simpa only [ef] using
        FibredCategoryMor.pullbackComparison_hom_postcompose F.toFibredCategoryMor f x
    have heg :
        eg.hom.1 ≫ F.toFibredCategoryMor.toHom.map (hcX.map g (f ^*[hcX] x)) =
          hcY.map g ((F.fiberFunctor V).obj (f ^*[hcX] x)) := by
      simpa only [eg] using
        FibredCategoryMor.pullbackComparison_hom_postcompose
          F.toFibredCategoryMor g (f ^*[hcX] x)
    have hmapY :
        ((hcY.pullbackFunctor g).map ef.hom).1 ≫
            hcY.map g ((F.fiberFunctor V).obj (f ^*[hcX] x)) =
          hcY.map g (f ^*[hcY] ((F.fiberFunctor U).obj x)) ≫ ef.hom.1 := by
      simpa only using hcY.pullbackFunctor_map_fac g ef.hom
    have hcYfac :
        cY.hom.1 ≫ hcY.map g (f ^*[hcY] ((F.fiberFunctor U).obj x)) ≫
          hcY.map f ((F.fiberFunctor U).obj x) =
          hcY.map (g ≫ f) ((F.fiberFunctor U).obj x) := by
      simpa only [cY] using
        hcY.pullbackCompComponentIso_fac f g ((F.fiberFunctor U).obj x)
    have hrightPost :
        (cY.hom.1 ≫ ((hcY.pullbackFunctor g).map ef.hom).1 ≫ eg.hom.1) ≫
            F.toFibredCategoryMor.toHom.map (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x) =
          cY.hom.1 ≫ hcY.map g (f ^*[hcY] ((F.fiberFunctor U).obj x)) ≫
            hcY.map f ((F.fiberFunctor U).obj x) := by
      calc
        (cY.hom.1 ≫ ((hcY.pullbackFunctor g).map ef.hom).1 ≫ eg.hom.1) ≫
            F.toFibredCategoryMor.toHom.map (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x) =
          cY.hom.1 ≫ ((hcY.pullbackFunctor g).map ef.hom).1 ≫
            (eg.hom.1 ≫ F.toFibredCategoryMor.toHom.map (hcX.map g (f ^*[hcX] x))) ≫
            F.toFibredCategoryMor.toHom.map (hcX.map f x) := by
            simp only [Functor.map_comp, Category.assoc]
            rfl
        _ = cY.hom.1 ≫ ((hcY.pullbackFunctor g).map ef.hom).1 ≫
            hcY.map g ((F.fiberFunctor V).obj (f ^*[hcX] x)) ≫
            F.toFibredCategoryMor.toHom.map (hcX.map f x) := by
            exact
              congrArg
                (fun m ↦ cY.hom.1 ≫ ((hcY.pullbackFunctor g).map ef.hom).1 ≫
                  m ≫ F.toFibredCategoryMor.toHom.map (hcX.map f x))
                heg
        _ = cY.hom.1 ≫
            (((hcY.pullbackFunctor g).map ef.hom).1 ≫
              hcY.map g ((F.fiberFunctor V).obj (f ^*[hcX] x))) ≫
            F.toFibredCategoryMor.toHom.map (hcX.map f x) := by
            simp only [Category.assoc]
        _ = cY.hom.1 ≫
            (hcY.map g (f ^*[hcY] ((F.fiberFunctor U).obj x)) ≫ ef.hom.1) ≫
            F.toFibredCategoryMor.toHom.map (hcX.map f x) := by
            exact
              congrArg
                (fun m ↦ cY.hom.1 ≫ m ≫
                  F.toFibredCategoryMor.toHom.map (hcX.map f x))
                hmapY
        _ = cY.hom.1 ≫ hcY.map g (f ^*[hcY] ((F.fiberFunctor U).obj x)) ≫
            (ef.hom.1 ≫ F.toFibredCategoryMor.toHom.map (hcX.map f x)) := by
            simp only [Category.assoc]
        _ = cY.hom.1 ≫ hcY.map g (f ^*[hcY] ((F.fiberFunctor U).obj x)) ≫
            hcY.map f ((F.fiberFunctor U).obj x) := by
            exact
              congrArg
                (fun m ↦ cY.hom.1 ≫
                  hcY.map g (f ^*[hcY] ((F.fiberFunctor U).obj x)) ≫ m)
                hef
    have hleftPost :
        (efg.hom.1 ≫ F.toFibredCategoryMor.toHom.map cX.hom.1) ≫
            F.toFibredCategoryMor.toHom.map (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x) =
          cY.hom.1 ≫ hcY.map g (f ^*[hcY] ((F.fiberFunctor U).obj x)) ≫
            hcY.map f ((F.fiberFunctor U).obj x) := by
      calc
        (efg.hom.1 ≫ F.toFibredCategoryMor.toHom.map cX.hom.1) ≫
            F.toFibredCategoryMor.toHom.map (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x)
            = efg.hom.1 ≫
                (F.toFibredCategoryMor.toHom.map cX.hom.1 ≫
                  F.toFibredCategoryMor.toHom.map
                    (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x)) := by
              rw [Category.assoc]
        _ = efg.hom.1 ≫ F.toFibredCategoryMor.toHom.map (hcX.map (g ≫ f) x) := by
              exact congrArg (fun m ↦ efg.hom.1 ≫ m) hmapX
        _ = hcY.map (g ≫ f) ((F.fiberFunctor U).obj x) := hefg
        _ = cY.hom.1 ≫ hcY.map g (f ^*[hcY] ((F.fiberFunctor U).obj x)) ≫
            hcY.map f ((F.fiberFunctor U).obj x) := hcYfac.symm
    exact hleftPost.trans hrightPost.symm
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ Yₛ.p _ _ _ _
      (g ≫ f) θ hθ _ _ (𝟙 W)
      ((efg.hom ≫ (F.fiberFunctor W).map cX.hom).1)
      ((cY.hom ≫ (hcY.pullbackFunctor g).map ef.hom ≫ eg.hom).1)
      hleft hright hpost

/-- Helper for Lemma 8.11.6: the base-composition compatibility also rewrites after moving the
source pullback-composition comparison to the right as an inverse. -/
private theorem pullbackComparison_baseComp_inv_hom_assoc
    (F : Xₛ ⟶ Yₛ)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (x : Xₛ.p.Fiber U) :
    ((canonicalPullbackChoice Yₛ.p).pullbackFunctor g).map
          (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).hom ≫
        (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor g
          (f ^*[canonicalPullbackChoice Xₛ.p] x)).hom ≫
        (F.fiberFunctor W).map ((canonicalPullbackChoice Xₛ.p).pullbackCompComponentIso f g x).inv =
      ((canonicalPullbackChoice Yₛ.p).pullbackCompComponentIso f g
        ((F.fiberFunctor U).obj x)).inv ≫
        (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor (g ≫ f) x).hom := by
  let hcX := canonicalPullbackChoice Xₛ.p
  let hcY := canonicalPullbackChoice Yₛ.p
  let efg := FibredCategoryMor.pullbackComparison F.toFibredCategoryMor (g ≫ f) x
  let ef := FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x
  let eg := FibredCategoryMor.pullbackComparison F.toFibredCategoryMor g (f ^*[hcX] x)
  let cX := hcX.pullbackCompComponentIso f g x
  let cY := hcY.pullbackCompComponentIso f g ((F.fiberFunctor U).obj x)
  have h := pullbackComparison_baseComp_hom (J := J) F f g x
  -- Multiply the hom-form comparison by the inverse comparison isomorphisms on the two sides.
  calc
    (hcY.pullbackFunctor g).map ef.hom ≫ eg.hom ≫ (F.fiberFunctor W).map cX.inv =
        (cY.inv ≫ cY.hom) ≫ ((hcY.pullbackFunctor g).map ef.hom ≫ eg.hom) ≫
          (F.fiberFunctor W).map cX.inv := by
          rw [Iso.inv_hom_id]
          simp only [Category.id_comp, Category.assoc]
          rfl
    _ = cY.inv ≫ (efg.hom ≫ (F.fiberFunctor W).map cX.hom) ≫
          (F.fiberFunctor W).map cX.inv := by
          simpa only [cY, cX, efg, ef, eg, hcX, hcY, Category.assoc] using
            congrArg (fun k ↦ cY.inv ≫ k ≫ (F.fiberFunctor W).map cX.inv) h.symm
    _ = cY.inv ≫ efg.hom ≫
          ((F.fiberFunctor W).map cX.hom ≫ (F.fiberFunctor W).map cX.inv) := by
          simp only [Category.assoc]
    _ = cY.inv ≫ efg.hom ≫ 𝟙 _ := by
          rw [← Functor.map_comp]
          simp only [Iso.hom_inv_id, Functor.map_id]
    _ = cY.inv ≫ efg.hom := by
          simp only [Category.comp_id]

/-- Helper for Lemma 8.11.6: a local lift through `G` and then through `F` gives the required
commuting square for the composite morphism over a composite base arrow. -/
private theorem compLocalLiftSquare
    (F : Xₛ ⟶ Yₛ) (G : Yₛ ⟶ Zₛ)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {x x' : Xₛ.p.Fiber U}
    (b : (G.fiberFunctor U).obj ((F.fiberFunctor U).obj x) ⟶
      (G.fiberFunctor U).obj ((F.fiberFunctor U).obj x'))
    (aG : f ^*[canonicalPullbackChoice Yₛ.p] ((F.fiberFunctor U).obj x) ⟶
      f ^*[canonicalPullbackChoice Yₛ.p] ((F.fiberFunctor U).obj x'))
    (hGsq : CommSq
      (((canonicalPullbackChoice Zₛ.p).pullbackFunctor f).map b)
      (FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f
        ((F.fiberFunctor U).obj x)).hom
      (FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f
        ((F.fiberFunctor U).obj x')).hom
      ((G.fiberFunctor V).map aG))
    (aF : g ^*[canonicalPullbackChoice Xₛ.p] (f ^*[canonicalPullbackChoice Xₛ.p] x) ⟶
      g ^*[canonicalPullbackChoice Xₛ.p] (f ^*[canonicalPullbackChoice Xₛ.p] x'))
    (hFsq : CommSq
      (((canonicalPullbackChoice Yₛ.p).pullbackFunctor g).map
        ((FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x).inv ≫
          aG ≫
          (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x').hom))
      (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor g
        (f ^*[canonicalPullbackChoice Xₛ.p] x)).hom
      (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor g
        (f ^*[canonicalPullbackChoice Xₛ.p] x')).hom
      ((F.fiberFunctor W).map aF)) :
    CommSq
      (((canonicalPullbackChoice Zₛ.p).pullbackFunctor (g ≫ f)).map b)
      (FibredCategoryMor.pullbackComparison (F ≫ G).toFibredCategoryMor (g ≫ f) x).hom
      (FibredCategoryMor.pullbackComparison (F ≫ G).toFibredCategoryMor (g ≫ f) x').hom
      (((F ≫ G).fiberFunctor W).map
        (((canonicalPullbackChoice Xₛ.p).pullbackCompComponentIso f g x).hom ≫
          aF ≫
          ((canonicalPullbackChoice Xₛ.p).pullbackCompComponentIso f g x').inv)) := by
  refine ⟨?_⟩
  -- Cancel the right composite-pullback comparison and reduce both sides to the same
  -- base-composition normal form.
  rw [← cancel_mono (((F ≫ G).fiberFunctor W).map
    ((canonicalPullbackChoice Xₛ.p).pullbackCompComponentIso f g x').hom)]
  simp only [Functor.map_comp]
  slice_lhs 2 3 =>
    erw [pullbackComparison_baseComp_hom (J := J) (F := F ≫ G) f g x']
  slice_rhs 1 2 =>
    erw [pullbackComparison_baseComp_hom (J := J) (F := F ≫ G) f g x]
  simp only [Category.assoc]
  let hcX := canonicalPullbackChoice Xₛ.p
  let hcY := canonicalPullbackChoice Yₛ.p
  let hcZ := canonicalPullbackChoice Zₛ.p
  let cX' := hcX.pullbackCompComponentIso f g x'
  let cZ := hcZ.pullbackCompComponentIso f g (((F ≫ G).fiberFunctor U).obj x)
  let cZ' := hcZ.pullbackCompComponentIso f g (((F ≫ G).fiberFunctor U).obj x')
  let eFf := FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x
  let eFf' := FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f x'
  let eFg := FibredCategoryMor.pullbackComparison F.toFibredCategoryMor g (f ^*[hcX] x)
  let eFg' := FibredCategoryMor.pullbackComparison F.toFibredCategoryMor g (f ^*[hcX] x')
  let eGf := FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f ((F.fiberFunctor U).obj x)
  let eGf' := FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f ((F.fiberFunctor U).obj x')
  let eGg :=
    FibredCategoryMor.pullbackComparison G.toFibredCategoryMor g
      ((F.fiberFunctor V).obj (f ^*[hcX] x))
  let eGg' :=
    FibredCategoryMor.pullbackComparison G.toFibredCategoryMor g
      ((F.fiberFunctor V).obj (f ^*[hcX] x'))
  let γ := eFf.inv ≫ aG ≫ eFf'.hom
  -- Expand the comparison for `F ≫ G` into the comparison for `G`, followed by the
  -- image of the comparison for `F`.
  erw [← StackInGroupoidsOver.Hom.pullbackComparison_comp_hom (J := J) F G f x,
    ← StackInGroupoidsOver.Hom.pullbackComparison_comp_hom (J := J) F G f x',
    ← StackInGroupoidsOver.Hom.pullbackComparison_comp_hom (J := J) F G g (f ^*[hcX] x),
    ← StackInGroupoidsOver.Hom.pullbackComparison_comp_hom (J := J) F G g (f ^*[hcX] x')]
  have hZcomp :
      (hcZ.pullbackFunctor (g ≫ f)).map b ≫ cZ'.hom =
        cZ.hom ≫ (hcZ.pullbackFunctor g).map ((hcZ.pullbackFunctor f).map b) := by
    simpa only [hcZ, cZ, cZ', BasedFunctor.comp] using
      pullbackCompComponentIso_hom_naturality
        (hc := canonicalPullbackChoice Zₛ.p) f g b
  have hGsq_w :
      (hcZ.pullbackFunctor f).map b ≫ eGf'.hom =
        eGf.hom ≫ (G.fiberFunctor V).map aG := by
    simpa only [hcZ, eGf, eGf'] using hGsq.w
  have hprefix : eFf.hom ≫ γ = aG ≫ eFf'.hom := by
    -- The morphism lifted through `F` is the `G`-lift conjugated by the first
    -- pullback-comparison isomorphism.
    change eFf.hom ≫ (eFf.inv ≫ aG ≫ eFf'.hom) = aG ≫ eFf'.hom
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hGpaste :
      (hcZ.pullbackFunctor g).map ((hcZ.pullbackFunctor f).map b) ≫
          (hcZ.pullbackFunctor g).map
            (eGf'.hom ≫ (G.fiberFunctor V).map eFf'.hom) =
        (hcZ.pullbackFunctor g).map
            (eGf.hom ≫ (G.fiberFunctor V).map eFf.hom) ≫
          (hcZ.pullbackFunctor g).map ((G.fiberFunctor V).map γ) := by
    have hprefixG :
        (G.fiberFunctor V).map aG ≫ (G.fiberFunctor V).map eFf'.hom =
          (G.fiberFunctor V).map eFf.hom ≫ (G.fiberFunctor V).map γ := by
      rw [← Functor.map_comp, ← Functor.map_comp, hprefix]
    have hinner :
        (hcZ.pullbackFunctor f).map b ≫
            (eGf'.hom ≫ (G.fiberFunctor V).map eFf'.hom) =
          (eGf.hom ≫ (G.fiberFunctor V).map eFf.hom) ≫
            (G.fiberFunctor V).map γ := by
      calc
        (hcZ.pullbackFunctor f).map b ≫
            (eGf'.hom ≫ (G.fiberFunctor V).map eFf'.hom) =
          ((hcZ.pullbackFunctor f).map b ≫ eGf'.hom) ≫
            (G.fiberFunctor V).map eFf'.hom := by
            simp only [Category.assoc]
        _ = (eGf.hom ≫ (G.fiberFunctor V).map aG) ≫
            (G.fiberFunctor V).map eFf'.hom := by
            exact congrArg (fun k ↦ k ≫ (G.fiberFunctor V).map eFf'.hom) hGsq_w
        _ = eGf.hom ≫
            ((G.fiberFunctor V).map aG ≫ (G.fiberFunctor V).map eFf'.hom) := by
            simp only [Category.assoc]
        _ = eGf.hom ≫
            ((G.fiberFunctor V).map eFf.hom ≫ (G.fiberFunctor V).map γ) := by
            exact congrArg (fun k ↦ eGf.hom ≫ k) hprefixG
        _ = (eGf.hom ≫ (G.fiberFunctor V).map eFf.hom) ≫
            (G.fiberFunctor V).map γ := by
            simp only [Category.assoc]
    calc
      (hcZ.pullbackFunctor g).map ((hcZ.pullbackFunctor f).map b) ≫
          (hcZ.pullbackFunctor g).map
            (eGf'.hom ≫ (G.fiberFunctor V).map eFf'.hom) =
        (hcZ.pullbackFunctor g).map
          ((hcZ.pullbackFunctor f).map b ≫
            (eGf'.hom ≫ (G.fiberFunctor V).map eFf'.hom)) := by
          simp only [Functor.map_comp]
      _ = (hcZ.pullbackFunctor g).map
          ((eGf.hom ≫ (G.fiberFunctor V).map eFf.hom) ≫
            (G.fiberFunctor V).map γ) := by
          exact congrArg (hcZ.pullbackFunctor g).map hinner
      _ = (hcZ.pullbackFunctor g).map
            (eGf.hom ≫ (G.fiberFunctor V).map eFf.hom) ≫
          (hcZ.pullbackFunctor g).map ((G.fiberFunctor V).map γ) := by
          simp only [Functor.map_comp, Category.assoc]
  have hGnat :
      (hcZ.pullbackFunctor g).map ((G.fiberFunctor V).map γ) ≫ eGg'.hom =
        eGg.hom ≫ (G.fiberFunctor W).map ((hcY.pullbackFunctor g).map γ) := by
    simpa only [hcY, hcZ, eGg, eGg', γ] using
      stack_morphism_pullbackComparison_naturality_over_vertical
        G.toFibredCategoryMor g γ
  have hFsq_w :
      (hcY.pullbackFunctor g).map γ ≫ eFg'.hom =
        eFg.hom ≫ (F.fiberFunctor W).map aF := by
    simpa only [hcY, eFf, eFf', eFg, eFg', γ] using hFsq.w
  have hFpaste :
      (G.fiberFunctor W).map ((hcY.pullbackFunctor g).map γ) ≫
          (G.fiberFunctor W).map eFg'.hom =
        (G.fiberFunctor W).map eFg.hom ≫
          ((F ≫ G).fiberFunctor W).map aF := by
    have hmapComp :
        (G.fiberFunctor W).map ((F.fiberFunctor W).map aF) =
          ((F ≫ G).fiberFunctor W).map aF := by
      rfl
    have hFpaste_raw :
        (G.fiberFunctor W).map ((hcY.pullbackFunctor g).map γ) ≫
            (G.fiberFunctor W).map eFg'.hom =
          (G.fiberFunctor W).map eFg.hom ≫
            (G.fiberFunctor W).map ((F.fiberFunctor W).map aF) := by
      exact
        ((G.fiberFunctor W).map_comp ((hcY.pullbackFunctor g).map γ) eFg'.hom).symm.trans
          ((congrArg (G.fiberFunctor W).map hFsq_w).trans
            ((G.fiberFunctor W).map_comp eFg.hom ((F.fiberFunctor W).map aF)))
    exact hFpaste_raw.trans
      (congrArg (fun k ↦ (G.fiberFunctor W).map eFg.hom ≫ k) hmapComp)
  have htail :
      ((F ≫ G).fiberFunctor W).map aF =
        ((F ≫ G).fiberFunctor W).map aF ≫
          ((F ≫ G).fiberFunctor W).map cX'.inv ≫
            ((F ≫ G).fiberFunctor W).map cX'.hom := by
    calc
      ((F ≫ G).fiberFunctor W).map aF =
          ((F ≫ G).fiberFunctor W).map aF ≫ 𝟙 _ := by
          rw [Category.comp_id]
      _ = ((F ≫ G).fiberFunctor W).map aF ≫
          ((F ≫ G).fiberFunctor W).map (cX'.inv ≫ cX'.hom) := by
          simp only [Iso.inv_hom_id, Functor.map_id]
      _ = ((F ≫ G).fiberFunctor W).map aF ≫
          (((F ≫ G).fiberFunctor W).map cX'.inv ≫
            ((F ≫ G).fiberFunctor W).map cX'.hom) := by
          rw [Functor.map_comp]
      _ = ((F ≫ G).fiberFunctor W).map aF ≫
          ((F ≫ G).fiberFunctor W).map cX'.inv ≫
            ((F ≫ G).fiberFunctor W).map cX'.hom := by
          rfl
  have hFprefix :
      cZ.hom ≫
          (hcZ.pullbackFunctor g).map
            (eGf.hom ≫ (G.fiberFunctor V).map eFf.hom) ≫
          (eGg.hom ≫ (G.fiberFunctor W).map ((hcY.pullbackFunctor g).map γ)) ≫
          (G.fiberFunctor W).map eFg'.hom =
        (cZ.hom ≫
            (hcZ.pullbackFunctor g).map
              (eGf.hom ≫ (G.fiberFunctor V).map eFf.hom) ≫
            eGg.hom ≫ (G.fiberFunctor W).map eFg.hom) ≫
          ((F ≫ G).fiberFunctor W).map aF := by
    simpa only [Category.assoc] using
      (congrArg
        (fun k ↦ cZ.hom ≫
          (hcZ.pullbackFunctor g).map
            (eGf.hom ≫ (G.fiberFunctor V).map eFf.hom) ≫
          eGg.hom ≫ k)
        hFpaste)
  have hGFprefix :
      cZ.hom ≫
          ((hcZ.pullbackFunctor g).map
              (eGf.hom ≫ (G.fiberFunctor V).map eFf.hom) ≫
            (hcZ.pullbackFunctor g).map ((G.fiberFunctor V).map γ)) ≫
          eGg'.hom ≫
          (G.fiberFunctor W).map eFg'.hom =
        (cZ.hom ≫
            (hcZ.pullbackFunctor g).map
              (eGf.hom ≫ (G.fiberFunctor V).map eFf.hom) ≫
            eGg.hom ≫ (G.fiberFunctor W).map eFg.hom) ≫
          ((F ≫ G).fiberFunctor W).map aF := by
    simpa only [Category.assoc] using
      (congrArg
          (fun k ↦ cZ.hom ≫
            (hcZ.pullbackFunctor g).map
              (eGf.hom ≫ (G.fiberFunctor V).map eFf.hom) ≫
            k ≫ (G.fiberFunctor W).map eFg'.hom)
          hGnat).trans hFprefix
  have hcalc :
      ((hcZ.pullbackFunctor (g ≫ f)).map b ≫ cZ'.hom) ≫
          (hcZ.pullbackFunctor g).map
            (eGf'.hom ≫ (G.fiberFunctor V).map eFf'.hom) ≫
            eGg'.hom ≫ (G.fiberFunctor W).map eFg'.hom =
        (cZ.hom ≫
            (hcZ.pullbackFunctor g).map
              (eGf.hom ≫ (G.fiberFunctor V).map eFf.hom) ≫
              eGg.hom ≫ (G.fiberFunctor W).map eFg.hom) ≫
          ((F ≫ G).fiberFunctor W).map aF ≫
            ((F ≫ G).fiberFunctor W).map cX'.inv ≫
              ((F ≫ G).fiberFunctor W).map cX'.hom := by
    have hpre :
        ((hcZ.pullbackFunctor (g ≫ f)).map b ≫ cZ'.hom) ≫
            (hcZ.pullbackFunctor g).map
              (eGf'.hom ≫ (G.fiberFunctor V).map eFf'.hom) ≫
              eGg'.hom ≫ (G.fiberFunctor W).map eFg'.hom =
          cZ.hom ≫
            ((hcZ.pullbackFunctor g).map
                (eGf.hom ≫ (G.fiberFunctor V).map eFf.hom) ≫
              (hcZ.pullbackFunctor g).map ((G.fiberFunctor V).map γ)) ≫
              eGg'.hom ≫ (G.fiberFunctor W).map eFg'.hom := by
      calc
        ((hcZ.pullbackFunctor (g ≫ f)).map b ≫ cZ'.hom) ≫
            (hcZ.pullbackFunctor g).map
              (eGf'.hom ≫ (G.fiberFunctor V).map eFf'.hom) ≫
              eGg'.hom ≫ (G.fiberFunctor W).map eFg'.hom =
          (cZ.hom ≫ (hcZ.pullbackFunctor g).map ((hcZ.pullbackFunctor f).map b)) ≫
            (hcZ.pullbackFunctor g).map
              (eGf'.hom ≫ (G.fiberFunctor V).map eFf'.hom) ≫
              eGg'.hom ≫ (G.fiberFunctor W).map eFg'.hom := by
            exact
              congrArg
                (fun k ↦ k ≫
                  (hcZ.pullbackFunctor g).map
                    (eGf'.hom ≫ (G.fiberFunctor V).map eFf'.hom) ≫
                  eGg'.hom ≫ (G.fiberFunctor W).map eFg'.hom)
                hZcomp
        _ = cZ.hom ≫
            ((hcZ.pullbackFunctor g).map ((hcZ.pullbackFunctor f).map b) ≫
              (hcZ.pullbackFunctor g).map
                (eGf'.hom ≫ (G.fiberFunctor V).map eFf'.hom)) ≫
              eGg'.hom ≫ (G.fiberFunctor W).map eFg'.hom := by
            simp only [Category.assoc]
        _ = cZ.hom ≫
            ((hcZ.pullbackFunctor g).map
                (eGf.hom ≫ (G.fiberFunctor V).map eFf.hom) ≫
              (hcZ.pullbackFunctor g).map ((G.fiberFunctor V).map γ)) ≫
              eGg'.hom ≫ (G.fiberFunctor W).map eFg'.hom := by
            exact
              congrArg
                (fun k ↦ cZ.hom ≫ k ≫
                  eGg'.hom ≫ (G.fiberFunctor W).map eFg'.hom)
                hGpaste
    have htailPrefix :
        (cZ.hom ≫
            (hcZ.pullbackFunctor g).map
              (eGf.hom ≫ (G.fiberFunctor V).map eFf.hom) ≫
            eGg.hom ≫ (G.fiberFunctor W).map eFg.hom) ≫
          ((F ≫ G).fiberFunctor W).map aF =
        (cZ.hom ≫
            (hcZ.pullbackFunctor g).map
              (eGf.hom ≫ (G.fiberFunctor V).map eFf.hom) ≫
            eGg.hom ≫ (G.fiberFunctor W).map eFg.hom) ≫
          ((F ≫ G).fiberFunctor W).map aF ≫
            ((F ≫ G).fiberFunctor W).map cX'.inv ≫
              ((F ≫ G).fiberFunctor W).map cX'.hom := by
      exact
        congrArg
          (fun k ↦ (cZ.hom ≫
            (hcZ.pullbackFunctor g).map
              (eGf.hom ≫ (G.fiberFunctor V).map eFf.hom) ≫
            eGg.hom ≫ (G.fiberFunctor W).map eFg.hom) ≫ k)
          htail
    exact hpre.trans (hGFprefix.trans htailPrefix)
  calc
    (hcZ.pullbackFunctor (g ≫ f)).map b ≫ cZ'.hom ≫
        (hcZ.pullbackFunctor g).map
          (eGf'.hom ≫ (G.fiberFunctor V).map eFf'.hom) ≫
          eGg'.hom ≫ (G.fiberFunctor W).map eFg'.hom =
      ((hcZ.pullbackFunctor (g ≫ f)).map b ≫ cZ'.hom) ≫
        (hcZ.pullbackFunctor g).map
          (eGf'.hom ≫ (G.fiberFunctor V).map eFf'.hom) ≫
          eGg'.hom ≫ (G.fiberFunctor W).map eFg'.hom := by
        rw [Category.assoc]
    _ = (cZ.hom ≫
          (hcZ.pullbackFunctor g).map
            (eGf.hom ≫ (G.fiberFunctor V).map eFf.hom) ≫
            eGg.hom ≫ (G.fiberFunctor W).map eFg.hom) ≫
        ((F ≫ G).fiberFunctor W).map aF ≫
          ((F ≫ G).fiberFunctor W).map cX'.inv ≫
            ((F ≫ G).fiberFunctor W).map cX'.hom := hcalc

/-- Helper for Lemma 8.11.6: the two-stage cover refinement used for local morphism lifting under
composition of stack morphisms. -/
private theorem locallyLiftsFiberMorphisms_comp
    (F : Xₛ ⟶ Yₛ) (G : Yₛ ⟶ Zₛ)
    (hF : StackInGroupoidsOver.Hom.LocallyLiftsFiberMorphisms F)
    (hG : StackInGroupoidsOver.Hom.LocallyLiftsFiberMorphisms G) :
    StackInGroupoidsOver.Hom.LocallyLiftsFiberMorphisms (F ≫ G) := by
  classical
  intro U x x' b
  let hcX := canonicalPullbackChoice Xₛ.p
  let hcY := canonicalPullbackChoice Yₛ.p
  let hcZ := canonicalPullbackChoice Zₛ.p
  let bG : (G.fiberFunctor U).obj ((F.fiberFunctor U).obj x) ⟶
      (G.fiberFunctor U).obj ((F.fiberFunctor U).obj x') := by
    simpa [BasedFunctor.comp] using b
  -- First lift the given composite-image morphism locally through `G`.
  obtain ⟨S, hS⟩ := hG ((F.fiberFunctor U).obj x) ((F.fiberFunctor U).obj x') bG
  let aG : ∀ I : S.Arrow,
      I.f ^*[hcY] ((F.fiberFunctor U).obj x) ⟶
        I.f ^*[hcY] ((F.fiberFunctor U).obj x') := fun I => Classical.choose (hS I)
  have hGsq : ∀ I : S.Arrow,
      CommSq
        ((hcZ.pullbackFunctor I.f).map bG)
        (FibredCategoryMor.pullbackComparison G.toFibredCategoryMor I.f ((F.fiberFunctor U).obj x)).hom
        (FibredCategoryMor.pullbackComparison G.toFibredCategoryMor I.f ((F.fiberFunctor U).obj x')).hom
        ((G.fiberFunctor I.Y).map (aG I)) := by
    intro I
    exact Classical.choose_spec (hS I)
  -- Convert the local `G`-lift into a morphism between `F`-images by the pullback comparison for
  -- `F`, then lift that morphism locally through `F`.
  let bF : ∀ I : S.Arrow,
      (F.fiberFunctor I.Y).obj (I.f ^*[hcX] x) ⟶
        (F.fiberFunctor I.Y).obj (I.f ^*[hcX] x') := fun I =>
    (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor I.f x).inv ≫
      aG I ≫
      (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor I.f x').hom
  let T : ∀ I : S.Arrow, J.Cover I.Y := fun I =>
    Classical.choose (hF (I.f ^*[hcX] x) (I.f ^*[hcX] x') (bF I))
  have hT : ∀ I : S.Arrow, ∀ K : (T I).Arrow,
      ∃ a : K.f ^*[hcX] (I.f ^*[hcX] x) ⟶ K.f ^*[hcX] (I.f ^*[hcX] x'),
        CommSq
          ((hcY.pullbackFunctor K.f).map (bF I))
          (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor K.f (I.f ^*[hcX] x)).hom
          (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor K.f (I.f ^*[hcX] x')).hom
          ((F.fiberFunctor K.Y).map a) := by
    intro I
    exact Classical.choose_spec (hF (I.f ^*[hcX] x) (I.f ^*[hcX] x') (bF I))
  refine ⟨S.bind T, ?_⟩
  intro A
  -- The final lift is the `F`-lift transported from the iterated pullback to the pullback along
  -- the composite bound-cover arrow.
  let I : S.Arrow := A.fromMiddle
  let K : (T I).Arrow := A.toMiddle
  obtain ⟨aF, hFsq⟩ := hT I K
  -- Work over the displayed composite leg of the bound-cover arrow before choosing the lift, so
  -- the square proof has no dependent transport left over.
  rw [← A.middle_spec]
  refine ⟨?_, ?_⟩
  · -- Transport the second-stage `F`-lift from the iterated pullback to the bound cover arrow.
    simpa [I, K] using
      ((hcX.pullbackCompComponentIso I.f K.f x).hom ≫ aF ≫
        (hcX.pullbackCompComponentIso I.f K.f x').inv)
  · -- The fixed-arrow pasting helper proves the square before the final bound-cover rewrite.
    simpa only [I, K, hcX, hcY, hcZ, bG, BasedFunctor.comp,
      GrothendieckTopology.Cover.Arrow.toMiddle] using
      compLocalLiftSquare (J := J) F G I.f K.f (b := bG) (aG := aG I)
        (hGsq := hGsq I) (aF := aF) (hFsq := hFsq)

-- Proof sketch: by Lemma `8.11.3`, a gerbe morphism is exactly a morphism that is locally
-- essentially surjective on objects and locally lifts fiber morphisms. These local conditions are
-- stable under composition after refining covers, so they apply to `F ≫ G`.
/-- Lemma 8.11.6: if `F : Xₛ ⟶ Yₛ` and `G : Yₛ ⟶ Zₛ` are gerbes over their targets, then the
composite `F ≫ G : Xₛ ⟶ Zₛ` is again a gerbe over `Zₛ`. -/
@[stacks 06R3]
theorem isGerbeOver_comp
    (F : Xₛ ⟶ Yₛ) (G : Yₛ ⟶ Zₛ)
    (hF : StackInGroupoidsOver.Hom.IsGerbeOver F)
    (hG : StackInGroupoidsOver.Hom.IsGerbeOver G) :
    StackInGroupoidsOver.Hom.IsGerbeOver (F ≫ G) := by
  -- Reduce gerbe-over stability to stability of the two local conditions.
  rw [StackInGroupoidsOver.Hom.isGerbeOver_iff_locallyEssentiallySurjectiveOnObjects_and_locallyLiftsFiberMorphisms]
  exact
    ⟨locallyEssentiallySurjectiveOnObjects_comp F G
        hF.locallyEssentiallySurjectiveOnObjects hG.locallyEssentiallySurjectiveOnObjects,
      locallyLiftsFiberMorphisms_comp F G
        hF.locallyLiftsFiberMorphisms hG.locallyLiftsFiberMorphisms⟩

end CategoryTheory
