import Mathlib
import StacksProject_2024.Chap04.Definition_4_31_2
import StacksProject_2024.Chap04.Definition_4_35_6
import StacksProject_2024.Chap04.Lemma_4_35_9
import StacksProject_2024.Chap08.Definition_8_11_4
import StacksProject_2024.Chap08.Lemma_8_11_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open FibredCategoryOver
universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

variable {X Y Y' X' : StackInGroupoidsOver J}
variable (F : X ⟶ Y)
variable (G : Y' ⟶ Y)
variable (F' : X' ⟶ Y')
variable (G' : X' ⟶ X)
variable (α : F' ≫ G ≅ G' ≫ F)

/-- Helper for Lemma 8.11.7: the canonical fiber pseudofunctor uses the same morphism map as
the pullback functor of the canonical pullback choice. -/
private theorem canonicalPullbackFunctor_map_eq_fiberPseudofunctor_map_forGerbeDescent
    {S : Type*} [Category S] {p : S ⥤ C} [p.IsFibered]
    {U V : C} (f : V ⟶ U) {x y : p.Fiber U} (φ : x ⟶ y) :
    ((canonicalPullbackChoice p).pullbackFunctor f).map φ =
      ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map φ := by
  rfl

/-- Helper for Lemma 8.11.7: reassociate a composite with the last three factors grouped. -/
private theorem comp_assoc_four_forGerbeDescent
    {D : Type*} [Category D] {A B E₁ E₂ E₃ : D}
    (f : A ⟶ B) (g : B ⟶ E₁) (h : E₁ ⟶ E₂) (i : E₂ ⟶ E₃) :
    f ≫ ((g ≫ h) ≫ i) = (f ≫ g) ≫ h ≫ i := by
  simp only [Category.assoc]

/-- Helper for Lemma 8.11.7: reassociate a fivefold composite with a grouped tail. -/
private theorem comp_assoc_five_forGerbeDescent
    {D : Type*} [Category D] {A B E₁ E₂ E₃ E₄ : D}
    (f : A ⟶ B) (g : B ⟶ E₁) (h : E₁ ⟶ E₂) (i : E₂ ⟶ E₃)
    (j : E₃ ⟶ E₄) :
    f ≫ ((g ≫ h ≫ i) ≫ j) = (f ≫ g) ≫ h ≫ i ≫ j := by
  simp only [Category.assoc]

/-- Helper for Lemma 8.11.7: reassociate after appending one morphism to a fourfold
composite. -/
private theorem comp_assoc_append_forGerbeDescent
    {D : Type*} [Category D] {A B E₁ E₂ E₃ E₄ : D}
    (f : A ⟶ B) (g : B ⟶ E₁) (h : E₁ ⟶ E₂) (i : E₂ ⟶ E₃)
    (j : E₃ ⟶ E₄) :
    ((f ≫ g) ≫ (h ≫ i)) ≫ j = (f ≫ g) ≫ h ≫ i ≫ j := by
  simp only [Category.assoc]

/-- Helper for Lemma 8.11.7: local essential-image isomorphisms compose across two
stack morphisms after replacing the iterated pullback by the pullback along the composite base
arrow. -/
private noncomputable def compLocalEssentialImageIsoForGerbeDescent
    {A B S : StackInGroupoidsOver J}
    (H : A ⟶ B) (K : B ⟶ S)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (z : S.p.Fiber U) (y : B.p.Fiber V) (x : A.p.Fiber W)
    (ηH : (H.fiberFunctor W).obj x ≅ g ^*[canonicalPullbackChoice B.p] y)
    (ηK : (K.fiberFunctor V).obj y ≅ f ^*[canonicalPullbackChoice S.p] z) :
    ((H ≫ K).fiberFunctor W).obj x ≅
      (g ≫ f) ^*[canonicalPullbackChoice S.p] z :=
  Iso.trans
    (Iso.trans
      (Functor.mapIso (K.fiberFunctor W) ηH)
      (FibredCategoryMor.pullbackComparison K.toFibredCategoryMor g y).symm)
    (Iso.trans
      (((canonicalPullbackChoice S.p).pullbackFunctor g).mapIso ηK)
      ((canonicalPullbackChoice S.p).pullbackCompComponentIso f g z).symm)

/-- Helper for Lemma 8.11.7: local essential surjectivity on objects is stable under
composition of stack morphisms. -/
private theorem locallyEssentiallySurjectiveOnObjects_comp_forGerbeDescent
    {A B S : StackInGroupoidsOver J}
    (H : A ⟶ B) (K : B ⟶ S)
    (hH : StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects H)
    (hK : StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects K) :
    StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects (H ≫ K) := by
  classical
  intro U z
  -- First lift the target object through `K`; then lift the chosen local object through `H`.
  obtain ⟨S₀, hS₀⟩ := hK U z
  choose y hy using hS₀
  let T : ∀ I : S₀.Arrow, J.Cover I.Y := fun I => Classical.choose (hH I.Y (y I))
  have hT : ∀ I : S₀.Arrow, ∀ K₀ : (T I).Arrow,
      ∃ x : A.p.Fiber K₀.Y,
        Nonempty (((H.fiberFunctor K₀.Y).obj x) ≅
          K₀.f ^*[canonicalPullbackChoice B.p] (y I)) := by
    intro I
    exact Classical.choose_spec (hH I.Y (y I))
  refine ⟨S₀.bind T, ?_⟩
  intro R
  -- An arrow in the bound cover is a second-stage arrow followed by a first-stage arrow.
  let I : S₀.Arrow := R.fromMiddle
  let K₀ : (T I).Arrow := R.toMiddle
  obtain ⟨x, hx⟩ := hT I K₀
  obtain ⟨ηH⟩ := hx
  obtain ⟨ηK⟩ := hy I
  refine ⟨x, ?_⟩
  -- The composed local image isomorphism has target pullback along `K₀.f ≫ I.f`, which is the
  -- displayed arrow of the bound cover.
  rw [← R.middle_spec]
  refine ⟨?_⟩
  simpa [I, K₀, BasedFunctor.comp] using
    compLocalEssentialImageIsoForGerbeDescent (J := J) H K I.f K₀.f z (y I) x ηH ηK

/-- Helper for Lemma 8.11.7: the gerbe structure on the left leg of an arbitrary final square
transports to the left projection of the canonical stack two-fibre product square. -/
private theorem canonicalLeftProjection_isGerbeOver_of_twoCartesian
    (hcart :
      Bicategory.IsFinal
        ({ obj := X'
           p := F'
           q := G'
           ψ := α } :
          BicategoricalTwoCommutativeSquare G F))
    (hF' : StackInGroupoidsOver.Hom.IsGerbeOver F') :
    StackInGroupoidsOver.Hom.IsGerbeOver
      (StackInGroupoidsOver.Hom.stackTwoFibreProductSquare (J := J) G F).p := by
  let P : BicategoricalTwoCommutativeSquare G F :=
    { obj := X'
      p := F'
      q := G'
      ψ := α }
  let Q : BicategoricalTwoCommutativeSquare G F :=
    StackInGroupoidsOver.Hom.stackTwoFibreProductSquare (J := J) G F
  have hQ : Bicategory.IsFinal Q := by
    exact StackInGroupoidsOver.Hom.stackTwoFibreProductSquare_isTwoFibreProduct (J := J) G F
  letI : Bicategory.IsFinal P := hcart
  letI : Bicategory.IsFinal Q := hQ
  let u : P ⟶ Q := ⊤_ (P ⟶ Q)
  have hu : u.hom.IsEquivalenceOverBase :=
    StackInGroupoidsOver.Hom.apexMap_isEquivalenceOverBase_of_final_squares
      (J := J) Q P hQ hcart u
  -- Transport along the source equivalence from the arbitrary final square to the canonical one.
  exact
    StackInGroupoidsOver.Hom.isGerbeOver_of_source_equivalence_comp_hom
      (J := J) u.hom Q.p P.p hu u.left hF'

/-- Helper for Lemma 8.11.7: if the canonical pullback left projection is locally essentially
surjective and the base-change leg is locally essentially surjective, then the right leg is
locally essentially surjective. -/
private theorem leftProjectionGerbe_locallyEssentiallySurjectiveOnObjects_rightLeg
    (hG : StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects G)
    (hp :
      StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects
        (StackInGroupoidsOver.Hom.stackTwoFibreProductSquare (J := J) G F).p) :
    StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects F := by
  let Q : BicategoricalTwoCommutativeSquare G F :=
    StackInGroupoidsOver.Hom.stackTwoFibreProductSquare (J := J) G F
  have hcomp :
      StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects (Q.p ≫ G) :=
    locallyEssentiallySurjectiveOnObjects_comp_forGerbeDescent (J := J) Q.p G hp hG
  -- The canonical square identifies `Q.q ≫ F` with `Q.p ≫ G`, so local essential
  -- surjectivity descends from the composite to `F`.
  exact
    StackInGroupoidsOver.Hom.locallyEssentiallySurjectiveOnObjects_of_comp_hom
      (J := J) Q.q F (Q.p ≫ G) Q.ψ.inv hcomp

/-- Helper for Lemma 8.11.7: equality transport cancels with the inverse transport coming from
another proof of the same object equality. -/
private theorem eqToHom_comp_symm_of_eq_proof_forGerbeDescent
    {D : Type*} [Category D] {X Y : D} (h h' : X = Y) :
    eqToHom h ≫ eqToHom h'.symm = 𝟙 X := by
  -- Remove one equality proof; proof irrelevance for equality transports reduces the other one.
  cases h
  simp

/-- Helper for Lemma 8.11.7: equality of functors transports mapped arrows by the object-level
`eqToHom` comparisons. -/
private theorem functorMap_eqToHom_comp_of_functor_eq_forGerbeDescent
    {D E : Type*} [Category D] [Category E]
    {L R : D ⥤ E} (h : L = R) {X Y : D} (f : X ⟶ Y) :
    L.map f ≫ eqToHom (congrArg (fun H : D ⥤ E => H.obj Y) h) =
      eqToHom (congrArg (fun H : D ⥤ E => H.obj X) h) ≫ R.map f := by
  -- After identifying the functors, the object transports are identities.
  cases h
  simp

/-- Helper for Lemma 8.11.7: solve a commutative square for its lower arrow when the
left vertical arrow is an isomorphism. -/
private theorem commSq_right_eq_inv_comp_forGerbeDescent
    {D : Type*} [Category D] {A B C E : D}
    {top : A ⟶ B} {left : A ⟶ C} {right : B ⟶ E} {bottom : C ⟶ E}
    [IsIso left] (h : CommSq top left right bottom) :
    bottom = inv left ≫ top ≫ right := by
  -- Move the left vertical isomorphism across the square equality.
  calc
    bottom = 𝟙 C ≫ bottom := by
      simp only [Category.id_comp]
    _ = (inv left ≫ left) ≫ bottom := by
      rw [IsIso.inv_hom_id]
    _ = inv left ≫ (left ≫ bottom) := by
      simp only [Category.assoc]
    _ = inv left ≫ (top ≫ right) := by
      exact congrArg (fun m ↦ inv left ≫ m) h.w.symm
    _ = inv left ≫ top ≫ right := by
      rfl

/-- Helper for Lemma 8.11.7: adjacent inverse isomorphisms cancel around a middle arrow. -/
private theorem hom_inv_comp_iso_cancel_forGerbeDescent
    {D : Type*} [Category D] {A X Y Z W B : D}
    (a : A ⟶ X) (i : X ⟶ Y) [IsIso i]
    (m : X ⟶ Z) (e : Z ≅ W) (d : Z ⟶ B) :
    (a ≫ i) ≫ (inv i ≫ m ≫ e.hom) ≫ (e.inv ≫ d) = a ≫ m ≫ d := by
  -- Reassociate so that both inverse pairs are adjacent, then cancel them.
  calc
    (a ≫ i) ≫ (inv i ≫ m ≫ e.hom) ≫ (e.inv ≫ d) =
        a ≫ (i ≫ inv i) ≫ m ≫ (e.hom ≫ e.inv) ≫ d := by
      simp only [Category.assoc]
    _ = a ≫ 𝟙 _ ≫ m ≫ 𝟙 _ ≫ d := by
      rw [IsIso.hom_inv_id, e.hom_inv_id]
    _ = a ≫ m ≫ d := by
      simp only [Category.id_comp]

/-- Helper for Lemma 8.11.7: the hom side of the chosen pullback-composition isomorphism is
natural in the fiber object. -/
private theorem pullbackCompComponentIso_hom_naturality_forGerbeDescent
    {S : Type*} [Category S] {p : S ⥤ C} (hc : PullbackChoice p)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {X Y : p.Fiber U} (θ : X ⟶ Y) :
    (hc.pullbackFunctor (g ≫ f)).map θ ≫
        (hc.pullbackCompComponentIso f g Y).hom =
      (hc.pullbackCompComponentIso f g X).hom ≫
        (hc.pullbackFunctor g).map ((hc.pullbackFunctor f).map θ) := by
  -- Repackage naturality of the composite-pullback comparison in the rewrite orientation needed
  -- for projecting the local lift through the right leg.
  simpa [PullbackChoice.pullbackCompIso] using (hc.pullbackCompIso f g).hom.naturality θ

/-- Helper for Lemma 8.11.7: pullback comparisons for a stack morphism are compatible with
composition of base arrows. -/
private theorem pullbackComparison_baseComp_hom_forGerbeDescent
    (H : X ⟶ Y)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (x : X.p.Fiber U) :
    (FibredCategoryMor.pullbackComparison H.toFibredCategoryMor (g ≫ f) x).hom ≫
        (H.fiberFunctor W).map ((canonicalPullbackChoice X.p).pullbackCompComponentIso f g x).hom =
      ((canonicalPullbackChoice Y.p).pullbackCompComponentIso f g
        ((H.fiberFunctor U).obj x)).hom ≫
        ((canonicalPullbackChoice Y.p).pullbackFunctor g).map
          (FibredCategoryMor.pullbackComparison H.toFibredCategoryMor f x).hom ≫
        (FibredCategoryMor.pullbackComparison H.toFibredCategoryMor g
          (f ^*[canonicalPullbackChoice X.p] x)).hom := by
  let hcX := canonicalPullbackChoice X.p
  let hcY := canonicalPullbackChoice Y.p
  let efg := FibredCategoryMor.pullbackComparison H.toFibredCategoryMor (g ≫ f) x
  let ef := FibredCategoryMor.pullbackComparison H.toFibredCategoryMor f x
  let eg := FibredCategoryMor.pullbackComparison H.toFibredCategoryMor g (f ^*[hcX] x)
  let cX := hcX.pullbackCompComponentIso f g x
  let cY := hcY.pullbackCompComponentIso f g ((H.fiberFunctor U).obj x)
  apply Functor.Fiber.hom_ext
  let θ := H.toFibredCategoryMor.toHom.map (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x)
  have hθ : Y.p.IsStronglyCartesian (g ≫ f) θ := by
    have hcartX :
        X.p.IsStronglyCartesian (g ≫ f)
          (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x) := by
      letI : X.p.IsStronglyCartesian g (hcX.map g (f ^*[hcX] x)) :=
        hcX.isStronglyCartesian g (f ^*[hcX] x)
      letI : X.p.IsStronglyCartesian f (hcX.map f x) :=
        hcX.isStronglyCartesian f x
      infer_instance
    exact
      FibredCategoryMor.map_stronglyCartesian_of_lift H.toFibredCategoryMor
        (g ≫ f) (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x) hcartX
  have hleft : Y.p.IsHomLift (𝟙 W)
      ((efg.hom ≫ (H.fiberFunctor W).map cX.hom).1) := by
    exact (efg.hom ≫ (H.fiberFunctor W).map cX.hom).2
  have hright : Y.p.IsHomLift (𝟙 W)
      ((cY.hom ≫ (hcY.pullbackFunctor g).map ef.hom ≫ eg.hom).1) := by
    exact (cY.hom ≫ (hcY.pullbackFunctor g).map ef.hom ≫ eg.hom).2
  have hpost :
      ((efg.hom ≫ (H.fiberFunctor W).map cX.hom).1) ≫ θ =
        ((cY.hom ≫ (hcY.pullbackFunctor g).map ef.hom ≫ eg.hom).1) ≫ θ := by
    -- Postcompose with the strongly-cartesian composite pullback arrow; both sides reduce to
    -- the same chosen pullback map by the defining comparison identities.
    change
      ((efg.hom.1 ≫ ((H.fiberFunctor W).map cX.hom).1) ≫ θ =
        (cY.hom.1 ≫ ((hcY.pullbackFunctor g).map ef.hom).1 ≫ eg.hom.1) ≫ θ)
    change
      ((efg.hom.1 ≫ H.toFibredCategoryMor.toHom.map cX.hom.1) ≫
          H.toFibredCategoryMor.toHom.map (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x) =
        (cY.hom.1 ≫ ((hcY.pullbackFunctor g).map ef.hom).1 ≫ eg.hom.1) ≫
          H.toFibredCategoryMor.toHom.map (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x))
    have hcXfac :
        cX.hom.1 ≫ hcX.map g (f ^*[hcX] x) ≫ hcX.map f x =
          hcX.map (g ≫ f) x := by
      simpa only [cX] using hcX.pullbackCompComponentIso_fac f g x
    have hmapX :
        H.toFibredCategoryMor.toHom.map cX.hom.1 ≫
            H.toFibredCategoryMor.toHom.map
              (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x) =
          H.toFibredCategoryMor.toHom.map (hcX.map (g ≫ f) x) := by
      rw [← Functor.map_comp]
      exact congrArg H.toFibredCategoryMor.toHom.map hcXfac
    have hefg :
        efg.hom.1 ≫ H.toFibredCategoryMor.toHom.map (hcX.map (g ≫ f) x) =
          hcY.map (g ≫ f) ((H.fiberFunctor U).obj x) := by
      simpa only [efg] using
        FibredCategoryMor.pullbackComparison_hom_postcompose
          H.toFibredCategoryMor (g ≫ f) x
    have hef :
        ef.hom.1 ≫ H.toFibredCategoryMor.toHom.map (hcX.map f x) =
          hcY.map f ((H.fiberFunctor U).obj x) := by
      simpa only [ef] using
        FibredCategoryMor.pullbackComparison_hom_postcompose H.toFibredCategoryMor f x
    have heg :
        eg.hom.1 ≫ H.toFibredCategoryMor.toHom.map (hcX.map g (f ^*[hcX] x)) =
          hcY.map g ((H.fiberFunctor V).obj (f ^*[hcX] x)) := by
      simpa only [eg] using
        FibredCategoryMor.pullbackComparison_hom_postcompose
          H.toFibredCategoryMor g (f ^*[hcX] x)
    have hmapY :
        ((hcY.pullbackFunctor g).map ef.hom).1 ≫
            hcY.map g ((H.fiberFunctor V).obj (f ^*[hcX] x)) =
          hcY.map g (f ^*[hcY] ((H.fiberFunctor U).obj x)) ≫ ef.hom.1 := by
      simpa only using hcY.pullbackFunctor_map_fac g ef.hom
    have hcYfac :
        cY.hom.1 ≫ hcY.map g (f ^*[hcY] ((H.fiberFunctor U).obj x)) ≫
          hcY.map f ((H.fiberFunctor U).obj x) =
          hcY.map (g ≫ f) ((H.fiberFunctor U).obj x) := by
      simpa only [cY] using
        hcY.pullbackCompComponentIso_fac f g ((H.fiberFunctor U).obj x)
    have hrightPost :
        (cY.hom.1 ≫ ((hcY.pullbackFunctor g).map ef.hom).1 ≫ eg.hom.1) ≫
            H.toFibredCategoryMor.toHom.map (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x) =
          cY.hom.1 ≫ hcY.map g (f ^*[hcY] ((H.fiberFunctor U).obj x)) ≫
            hcY.map f ((H.fiberFunctor U).obj x) := by
      calc
        (cY.hom.1 ≫ ((hcY.pullbackFunctor g).map ef.hom).1 ≫ eg.hom.1) ≫
            H.toFibredCategoryMor.toHom.map (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x) =
          cY.hom.1 ≫ ((hcY.pullbackFunctor g).map ef.hom).1 ≫
            (eg.hom.1 ≫ H.toFibredCategoryMor.toHom.map (hcX.map g (f ^*[hcX] x))) ≫
            H.toFibredCategoryMor.toHom.map (hcX.map f x) := by
            simp only [Functor.map_comp, Category.assoc]
            rfl
        _ = cY.hom.1 ≫ ((hcY.pullbackFunctor g).map ef.hom).1 ≫
            hcY.map g ((H.fiberFunctor V).obj (f ^*[hcX] x)) ≫
            H.toFibredCategoryMor.toHom.map (hcX.map f x) := by
            exact
              congrArg
                (fun m ↦ cY.hom.1 ≫ ((hcY.pullbackFunctor g).map ef.hom).1 ≫
                  m ≫ H.toFibredCategoryMor.toHom.map (hcX.map f x))
                heg
        _ = cY.hom.1 ≫
            (((hcY.pullbackFunctor g).map ef.hom).1 ≫
              hcY.map g ((H.fiberFunctor V).obj (f ^*[hcX] x))) ≫
            H.toFibredCategoryMor.toHom.map (hcX.map f x) := by
            simp only [Category.assoc]
        _ = cY.hom.1 ≫
            (hcY.map g (f ^*[hcY] ((H.fiberFunctor U).obj x)) ≫ ef.hom.1) ≫
            H.toFibredCategoryMor.toHom.map (hcX.map f x) := by
            exact
              congrArg
                (fun m ↦ cY.hom.1 ≫ m ≫
                  H.toFibredCategoryMor.toHom.map (hcX.map f x))
                hmapY
        _ = cY.hom.1 ≫ hcY.map g (f ^*[hcY] ((H.fiberFunctor U).obj x)) ≫
            (ef.hom.1 ≫ H.toFibredCategoryMor.toHom.map (hcX.map f x)) := by
            simp only [Category.assoc]
        _ = cY.hom.1 ≫ hcY.map g (f ^*[hcY] ((H.fiberFunctor U).obj x)) ≫
            hcY.map f ((H.fiberFunctor U).obj x) := by
            exact
              congrArg
                (fun m ↦ cY.hom.1 ≫
                  hcY.map g (f ^*[hcY] ((H.fiberFunctor U).obj x)) ≫ m)
                hef
    have hleftPost :
        (efg.hom.1 ≫ H.toFibredCategoryMor.toHom.map cX.hom.1) ≫
            H.toFibredCategoryMor.toHom.map (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x) =
          cY.hom.1 ≫ hcY.map g (f ^*[hcY] ((H.fiberFunctor U).obj x)) ≫
            hcY.map f ((H.fiberFunctor U).obj x) := by
      calc
        (efg.hom.1 ≫ H.toFibredCategoryMor.toHom.map cX.hom.1) ≫
            H.toFibredCategoryMor.toHom.map (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x)
            = efg.hom.1 ≫
                (H.toFibredCategoryMor.toHom.map cX.hom.1 ≫
                  H.toFibredCategoryMor.toHom.map
                    (hcX.map g (f ^*[hcX] x) ≫ hcX.map f x)) := by
              rw [Category.assoc]
        _ = efg.hom.1 ≫ H.toFibredCategoryMor.toHom.map (hcX.map (g ≫ f) x) := by
              exact congrArg (fun m ↦ efg.hom.1 ≫ m) hmapX
        _ = hcY.map (g ≫ f) ((H.fiberFunctor U).obj x) := hefg
        _ = cY.hom.1 ≫ hcY.map g (f ^*[hcY] ((H.fiberFunctor U).obj x)) ≫
            hcY.map f ((H.fiberFunctor U).obj x) := hcYfac.symm
    exact hleftPost.trans hrightPost.symm
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ Y.p _ _ _ _
      (g ≫ f) θ hθ _ _ (𝟙 W)
      ((efg.hom ≫ (H.fiberFunctor W).map cX.hom).1)
      ((cY.hom ≫ (hcY.pullbackFunctor g).map ef.hom ≫ eg.hom).1)
      hleft hright hpost

/-- Helper for Lemma 8.11.7: an iterated-pullback lifting square transports to the pullback
along the composite base arrow. -/
private theorem compositePullbackSquareOfIterated_forGerbeDescent
    (H : X ⟶ Y)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {x x' : X.p.Fiber U}
    (b : (H.fiberFunctor U).obj x ⟶ (H.fiberFunctor U).obj x')
    (aIter : g ^*[canonicalPullbackChoice X.p] (f ^*[canonicalPullbackChoice X.p] x) ⟶
      g ^*[canonicalPullbackChoice X.p] (f ^*[canonicalPullbackChoice X.p] x'))
    (hIter :
      ((canonicalPullbackChoice Y.p).pullbackFunctor g).map
            (((canonicalPullbackChoice Y.p).pullbackFunctor f).map b) ≫
          ((canonicalPullbackChoice Y.p).pullbackFunctor g).map
            (FibredCategoryMor.pullbackComparison H.toFibredCategoryMor f x').hom ≫
          (FibredCategoryMor.pullbackComparison H.toFibredCategoryMor g
            (f ^*[canonicalPullbackChoice X.p] x')).hom =
        ((canonicalPullbackChoice Y.p).pullbackFunctor g).map
            (FibredCategoryMor.pullbackComparison H.toFibredCategoryMor f x).hom ≫
          (FibredCategoryMor.pullbackComparison H.toFibredCategoryMor g
            (f ^*[canonicalPullbackChoice X.p] x)).hom ≫
          (H.fiberFunctor W).map aIter) :
    CommSq
      (((canonicalPullbackChoice Y.p).pullbackFunctor (g ≫ f)).map b)
      (FibredCategoryMor.pullbackComparison H.toFibredCategoryMor (g ≫ f) x).hom
      (FibredCategoryMor.pullbackComparison H.toFibredCategoryMor (g ≫ f) x').hom
      ((H.fiberFunctor W).map
        (((canonicalPullbackChoice X.p).pullbackCompComponentIso f g x).hom ≫
          aIter ≫
          ((canonicalPullbackChoice X.p).pullbackCompComponentIso f g x').inv)) := by
  let hcX := canonicalPullbackChoice X.p
  let hcY := canonicalPullbackChoice Y.p
  let cX := hcX.pullbackCompComponentIso f g x
  let cX' := hcX.pullbackCompComponentIso f g x'
  let cY := hcY.pullbackCompComponentIso f g ((H.fiberFunctor U).obj x)
  let cY' := hcY.pullbackCompComponentIso f g ((H.fiberFunctor U).obj x')
  let efg := FibredCategoryMor.pullbackComparison H.toFibredCategoryMor (g ≫ f) x
  let efg' := FibredCategoryMor.pullbackComparison H.toFibredCategoryMor (g ≫ f) x'
  let ef := FibredCategoryMor.pullbackComparison H.toFibredCategoryMor f x
  let ef' := FibredCategoryMor.pullbackComparison H.toFibredCategoryMor f x'
  let eg := FibredCategoryMor.pullbackComparison H.toFibredCategoryMor g (f ^*[hcX] x)
  let eg' := FibredCategoryMor.pullbackComparison H.toFibredCategoryMor g (f ^*[hcX] x')
  refine ⟨?_⟩
  -- First normalize the target pullback of `b` to the iterated-pullback normal form.
  have hnat :
      (hcY.pullbackFunctor (g ≫ f)).map b ≫ cY'.hom =
        cY.hom ≫ (hcY.pullbackFunctor g).map ((hcY.pullbackFunctor f).map b) := by
    simpa only [hcY, cY, cY'] using
      pullbackCompComponentIso_hom_naturality_forGerbeDescent
        (hc := canonicalPullbackChoice Y.p) f g b
  have hbase :
      efg.hom ≫ (H.fiberFunctor W).map cX.hom =
        cY.hom ≫ (hcY.pullbackFunctor g).map ef.hom ≫ eg.hom := by
    simpa only [hcX, hcY, cX, cY, efg, ef, eg] using
      pullbackComparison_baseComp_hom_forGerbeDescent (J := J) H f g x
  have hbase' :
      efg'.hom ≫ (H.fiberFunctor W).map cX'.hom =
        cY'.hom ≫ (hcY.pullbackFunctor g).map ef'.hom ≫ eg'.hom := by
    simpa only [hcX, hcY, cX', cY', efg', ef', eg'] using
      pullbackComparison_baseComp_hom_forGerbeDescent (J := J) H f g x'
  -- Then paste the iterated square and cancel the comparison isomorphism on the right.
  calc
    (hcY.pullbackFunctor (g ≫ f)).map b ≫ efg'.hom =
        (hcY.pullbackFunctor (g ≫ f)).map b ≫ efg'.hom ≫
          (H.fiberFunctor W).map cX'.hom ≫ (H.fiberFunctor W).map cX'.inv := by
          rw [← Category.assoc, ← Functor.map_comp]
          simp only [Iso.hom_inv_id, Functor.map_id, Category.comp_id]
    _ = (hcY.pullbackFunctor (g ≫ f)).map b ≫
          (cY'.hom ≫ (hcY.pullbackFunctor g).map ef'.hom ≫ eg'.hom) ≫
          (H.fiberFunctor W).map cX'.inv := by
          calc
            (hcY.pullbackFunctor (g ≫ f)).map b ≫ efg'.hom ≫
                (H.fiberFunctor W).map cX'.hom ≫ (H.fiberFunctor W).map cX'.inv =
              ((hcY.pullbackFunctor (g ≫ f)).map b ≫
                (efg'.hom ≫ (H.fiberFunctor W).map cX'.hom)) ≫
                  (H.fiberFunctor W).map cX'.inv := by
                simp only [Category.assoc]
            _ = ((hcY.pullbackFunctor (g ≫ f)).map b ≫
                (cY'.hom ≫ (hcY.pullbackFunctor g).map ef'.hom ≫ eg'.hom)) ≫
                  (H.fiberFunctor W).map cX'.inv := by
                exact congrArg
                  (fun k ↦ ((hcY.pullbackFunctor (g ≫ f)).map b ≫ k) ≫
                    (H.fiberFunctor W).map cX'.inv) hbase'
            _ = (hcY.pullbackFunctor (g ≫ f)).map b ≫
                  (cY'.hom ≫ (hcY.pullbackFunctor g).map ef'.hom ≫ eg'.hom) ≫
                  (H.fiberFunctor W).map cX'.inv := by
                simp only [Category.assoc]
    _ = ((hcY.pullbackFunctor (g ≫ f)).map b ≫ cY'.hom) ≫
          (hcY.pullbackFunctor g).map ef'.hom ≫ eg'.hom ≫
          (H.fiberFunctor W).map cX'.inv := by
          simp only [Category.assoc]
    _ = (cY.hom ≫ (hcY.pullbackFunctor g).map ((hcY.pullbackFunctor f).map b)) ≫
          (hcY.pullbackFunctor g).map ef'.hom ≫ eg'.hom ≫
          (H.fiberFunctor W).map cX'.inv := by
          exact congrArg
            (fun k ↦ k ≫ (hcY.pullbackFunctor g).map ef'.hom ≫ eg'.hom ≫
              (H.fiberFunctor W).map cX'.inv) hnat
    _ = cY.hom ≫
          ((hcY.pullbackFunctor g).map ((hcY.pullbackFunctor f).map b) ≫
            (hcY.pullbackFunctor g).map ef'.hom ≫ eg'.hom) ≫
          (H.fiberFunctor W).map cX'.inv := by
          simp only [Category.assoc]
    _ = cY.hom ≫ ((hcY.pullbackFunctor g).map ef.hom ≫ eg.hom ≫
          (H.fiberFunctor W).map aIter) ≫ (H.fiberFunctor W).map cX'.inv := by
          exact congrArg (fun k ↦ cY.hom ≫ k ≫ (H.fiberFunctor W).map cX'.inv) hIter
    _ = (cY.hom ≫ (hcY.pullbackFunctor g).map ef.hom ≫ eg.hom) ≫
          (H.fiberFunctor W).map aIter ≫ (H.fiberFunctor W).map cX'.inv := by
          simp only [Category.assoc]
    _ = (efg.hom ≫ (H.fiberFunctor W).map cX.hom) ≫
          (H.fiberFunctor W).map aIter ≫ (H.fiberFunctor W).map cX'.inv := by
          exact congrArg
            (fun k ↦ k ≫ (H.fiberFunctor W).map aIter ≫ (H.fiberFunctor W).map cX'.inv)
            hbase.symm
    _ = efg.hom ≫ (H.fiberFunctor W).map (cX.hom ≫ aIter ≫ cX'.inv) := by
          simp only [Functor.map_comp, Category.assoc]

/-- Helper for Lemma 8.11.7: if the canonical pullback left projection locally lifts fiber
morphisms and the base-change leg is locally essentially surjective, then the right leg locally
lifts fiber morphisms. -/
private theorem leftProjectionGerbe_locallyLiftsFiberMorphisms_rightLeg
    (hG : StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects G)
    (hp :
      StackInGroupoidsOver.Hom.LocallyLiftsFiberMorphisms
        (StackInGroupoidsOver.Hom.stackTwoFibreProductSquare (J := J) G F).p) :
    StackInGroupoidsOver.Hom.LocallyLiftsFiberMorphisms F := by
  classical
  intro U x x' b
  let hcX := canonicalPullbackChoice X.p
  let hcY := canonicalPullbackChoice Y.p
  -- First localize the source image of `x` along `G`.
  obtain ⟨S, hS⟩ := hG U ((F.fiberFunctor U).obj x)
  choose y hy using hS
  let T : ∀ I : S.Arrow, J.Cover I.Y := fun I =>
    let Q : BicategoricalTwoCommutativeSquare G F :=
      StackInGroupoidsOver.Hom.stackTwoFibreProductSquare (J := J) G F
    let P : Q.obj.p.Fiber I.Y :=
      let Pcat : Limits.CategoricalPullback (G.fiberFunctor I.Y) (F.fiberFunctor I.Y) :=
        { fst := y I
          snd := I.f ^*[hcX] x
          iso := Classical.choice (hy I) ≪≫
            FibredCategoryMor.pullbackComparison F.toFibredCategoryMor I.f x }
      ⟨{ U := I.Y, obj := Pcat }, rfl⟩
    letI : IsIso b := IsFibredInGroupoids.hom_isIso (p := Y.p) (U := U) b
    let P' : Q.obj.p.Fiber I.Y :=
      let Pcat : Limits.CategoricalPullback (G.fiberFunctor I.Y) (F.fiberFunctor I.Y) :=
        { fst := y I
          snd := I.f ^*[hcX] x'
          iso := Classical.choice (hy I) ≪≫
            (hcY.pullbackFunctor I.f).mapIso (asIso b) ≪≫
            FibredCategoryMor.pullbackComparison F.toFibredCategoryMor I.f x' }
      ⟨{ U := I.Y, obj := Pcat }, rfl⟩
    Classical.choose (hp P P' (𝟙 _))
  have hT : ∀ I : S.Arrow, ∀ K : (T I).Arrow,
      ∃ a : (K.f ≫ I.f) ^*[hcX] x ⟶ (K.f ≫ I.f) ^*[hcX] x',
        CommSq
          ((hcY.pullbackFunctor (K.f ≫ I.f)).map b)
          (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor (K.f ≫ I.f) x).hom
          (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor (K.f ≫ I.f) x').hom
          ((F.fiberFunctor K.Y).map a) := by
    intro I K
    let Q : BicategoricalTwoCommutativeSquare G F :=
      StackInGroupoidsOver.Hom.stackTwoFibreProductSquare (J := J) G F
    let P : Q.obj.p.Fiber I.Y :=
      let Pcat : Limits.CategoricalPullback (G.fiberFunctor I.Y) (F.fiberFunctor I.Y) :=
        { fst := y I
          snd := I.f ^*[hcX] x
          iso := Classical.choice (hy I) ≪≫
            FibredCategoryMor.pullbackComparison F.toFibredCategoryMor I.f x }
      ⟨{ U := I.Y, obj := Pcat }, rfl⟩
    letI : IsIso b := IsFibredInGroupoids.hom_isIso (p := Y.p) (U := U) b
    let P' : Q.obj.p.Fiber I.Y :=
      let Pcat : Limits.CategoricalPullback (G.fiberFunctor I.Y) (F.fiberFunctor I.Y) :=
        { fst := y I
          snd := I.f ^*[hcX] x'
          iso := Classical.choice (hy I) ≪≫
            (hcY.pullbackFunctor I.f).mapIso (asIso b) ≪≫
            FibredCategoryMor.pullbackComparison F.toFibredCategoryMor I.f x' }
      ⟨{ U := I.Y, obj := Pcat }, rfl⟩
    obtain ⟨δ, hδ⟩ := Classical.choose_spec (hp P P' (𝟙 _)) K
    let eW := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      G.toBasedFunctor F.toBasedFunctor K.Y
    let ix := StackInGroupoidsOver.Hom.fibreOfPullback_pullbackObjIso (J := J) G F K.f P
    let ix' := StackInGroupoidsOver.Hom.fibreOfPullback_pullbackObjIso (J := J) G F K.f P'
    let δstd :=
      ix.hom ≫ eW.functor.map δ ≫ ix'.inv
    let aIter : K.f ^*[hcX] (I.f ^*[hcX] x) ⟶ K.f ^*[hcX] (I.f ^*[hcX] x') :=
      δstd.snd
    let a : (K.f ≫ I.f) ^*[hcX] x ⟶ (K.f ≫ I.f) ^*[hcX] x' :=
      (hcX.pullbackCompComponentIso I.f K.f x).hom ≫ aIter ≫
        (hcX.pullbackCompComponentIso I.f K.f x').inv
    refine ⟨a, ?_⟩
    -- Project the local `Q.p`-lift through the right leg and then transport the iterated
    -- pullback lift to the composite cover arrow.
    refine
      compositePullbackSquareOfIterated_forGerbeDescent
        (J := J) F I.f K.f (b := b) (aIter := aIter) ?_
    let cQ := FibredCategoryMor.pullbackComparison Q.p.toFibredCategoryMor K.f P
    let cQ' := FibredCategoryMor.pullbackComparison Q.p.toFibredCategoryMor K.f P'
    have hδp :
        (Q.p.fiberFunctor K.Y).map δ =
          inv cQ.hom ≫
            ((canonicalPullbackChoice Y'.p).pullbackFunctor K.f).map
              (𝟙 ((Q.p.fiberFunctor I.Y).obj P)) ≫
            cQ'.hom := by
      -- Read the `Q.p`-lifting square as an explicit formula for the projected lift.
      simpa only [cQ, cQ', Category.assoc] using
        (commSq_right_eq_inv_comp_forGerbeDescent hδ)
    let eI := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      G.toBasedFunctor F.toBasedFunctor I.Y
    let hπ₁I :=
      StackInGroupoidsOver.Hom.fibreOfPullback_equiv_pullbackOfFibres_functor_comp_stackTwoFibreProductLeftProjection
        (J := J) G F I.Y
    let hπ₁W :=
      StackInGroupoidsOver.Hom.fibreOfPullback_equiv_pullbackOfFibres_functor_comp_stackTwoFibreProductLeftProjection
        (J := J) G F K.Y
    let leftI : (eI.functor.obj P).fst = (Q.p.fiberFunctor I.Y).obj P :=
      congrArg (fun H : Q.obj.p.Fiber I.Y ⥤ Y'.p.Fiber I.Y => H.obj P) hπ₁I
    let leftI' : (eI.functor.obj P').fst = (Q.p.fiberFunctor I.Y).obj P' :=
      congrArg (fun H : Q.obj.p.Fiber I.Y ⥤ Y'.p.Fiber I.Y => H.obj P') hπ₁I
    let leftW :
        (eW.functor.obj (K.f ^*[canonicalPullbackChoice Q.obj.p] P)).fst =
          (Q.p.fiberFunctor K.Y).obj
            (K.f ^*[canonicalPullbackChoice Q.obj.p] P) :=
      congrArg
        (fun H : Q.obj.p.Fiber K.Y ⥤ Y'.p.Fiber K.Y =>
          H.obj (K.f ^*[canonicalPullbackChoice Q.obj.p] P)) hπ₁W
    let leftW' :
        (eW.functor.obj (K.f ^*[canonicalPullbackChoice Q.obj.p] P')).fst =
          (Q.p.fiberFunctor K.Y).obj
            (K.f ^*[canonicalPullbackChoice Q.obj.p] P') :=
      congrArg
        (fun H : Q.obj.p.Fiber K.Y ⥤ Y'.p.Fiber K.Y =>
          H.obj (K.f ^*[canonicalPullbackChoice Q.obj.p] P')) hπ₁W
    have htransport :
        (eW.functor.map δ).fst ≫ eqToHom leftW' =
          eqToHom leftW ≫ (Q.p.fiberFunctor K.Y).map δ := by
      -- Move the first projection through the equality of the equivalence projection functor
      -- with the canonical left projection `Q.p`.
      simpa only [leftW, leftW', Functor.comp_map, Limits.CategoricalPullback.comp_fst] using
        (functorMap_eqToHom_comp_of_functor_eq_forGerbeDescent hπ₁W δ)
    have hpmap :
        (eW.functor.map δ).fst =
          eqToHom leftW ≫ (Q.p.fiberFunctor K.Y).map δ ≫ eqToHom leftW'.symm := by
      -- Solve the transport equation for the raw first component of `eW.functor.map δ`.
      calc
        (eW.functor.map δ).fst = (eW.functor.map δ).fst ≫ 𝟙 _ := by
          simp only [Category.comp_id]
        _ = (eW.functor.map δ).fst ≫
              (eqToHom leftW' ≫ eqToHom leftW'.symm) := by
          simp only [eqToHom_trans, eqToHom_refl]
        _ = ((eW.functor.map δ).fst ≫ eqToHom leftW') ≫ eqToHom leftW'.symm := by
          simp only [Category.assoc]
        _ = (eqToHom leftW ≫ (Q.p.fiberFunctor K.Y).map δ) ≫
              eqToHom leftW'.symm := by
          exact congrArg (fun k => k ≫ eqToHom leftW'.symm) htransport
        _ = eqToHom leftW ≫ (Q.p.fiberFunctor K.Y).map δ ≫
              eqToHom leftW'.symm := by
          simp only [Category.assoc]
    let rI :
        ((canonicalPullbackChoice Y'.p).pullbackFunctor K.f).obj (eI.functor.obj P).fst =
          ((canonicalPullbackChoice Y'.p).pullbackFunctor K.f).obj
            ((Q.p.fiberFunctor I.Y).obj P) :=
      congrArg (fun z => ((canonicalPullbackChoice Y'.p).pullbackFunctor K.f).obj z) leftI
    let rI' :
        ((canonicalPullbackChoice Y'.p).pullbackFunctor K.f).obj (eI.functor.obj P').fst =
          ((canonicalPullbackChoice Y'.p).pullbackFunctor K.f).obj
            ((Q.p.fiberFunctor I.Y).obj P') :=
      congrArg (fun z => ((canonicalPullbackChoice Y'.p).pullbackFunctor K.f).obj z) leftI'
    have hleft :
        (StackInGroupoidsOver.Hom.fibreOfPullback_pullbackObjIsoLeft
            (J := J) G F K.f P).hom ≫ eqToHom leftW =
          eqToHom rI ≫ cQ.hom := by
      -- Expand the first-component comparison of `ix` and cancel the target equality transport.
      simpa only [StackInGroupoidsOver.Hom.fibreOfPullback_pullbackObjIsoLeft,
        Q, cQ, rI, leftI, leftW, hπ₁I, hπ₁W] using
        (isoTrans_hom_comp_eqToHom rI leftW cQ)
    have hright :
        eqToHom leftW'.symm ≫
            (StackInGroupoidsOver.Hom.fibreOfPullback_pullbackObjIsoLeft
              (J := J) G F K.f P').inv =
          cQ'.inv ≫ eqToHom rI'.symm := by
      -- The same comparison for `ix'`, now in inverse orientation.
      simpa only [StackInGroupoidsOver.Hom.fibreOfPullback_pullbackObjIsoLeft,
        Q, cQ', rI', leftI', leftW', hπ₁I, hπ₁W] using
        (eqToHom_symm_comp_isoTrans_inv rI' leftW' cQ')
    have hδfst : δstd.fst = 𝟙 _ := by
      -- Combine the projected lift formula with the two comparison isomorphisms. Since the
      -- chosen morphism for `Q.p` is the identity on the common first component `y I`, all
      -- transports reduce to the identity.
      let m := ((canonicalPullbackChoice Y'.p).pullbackFunctor K.f).map
        (𝟙 ((Q.p.fiberFunctor I.Y).obj P))
      have hsubst :
          (eqToHom rI ≫ cQ.hom) ≫ (Q.p.fiberFunctor K.Y).map δ ≫
              cQ'.inv ≫ eqToHom rI'.symm =
            (eqToHom rI ≫ cQ.hom) ≫ (inv cQ.hom ≫ m ≫ cQ'.hom) ≫
              cQ'.inv ≫ eqToHom rI'.symm := by
        simpa only [Category.assoc] using
          congrArg
            (fun k => (eqToHom rI ≫ cQ.hom) ≫ k ≫
              cQ'.inv ≫ eqToHom rI'.symm)
            hδp
      have hcancel :
          (eqToHom rI ≫ cQ.hom) ≫ (inv cQ.hom ≫ m ≫ cQ'.hom) ≫
              cQ'.inv ≫ eqToHom rI'.symm =
            eqToHom rI ≫ m ≫ eqToHom rI'.symm := by
        simpa only [Category.assoc] using
          hom_inv_comp_iso_cancel_forGerbeDescent
            (eqToHom rI) cQ.hom m cQ' (eqToHom rI'.symm)
      have hid : eqToHom rI ≫ m ≫ eqToHom rI'.symm = 𝟙 _ := by
        simpa only [m, P, P', Q,
          StackInGroupoidsOver.Hom.stackTwoFibreProductSquare,
          StackInGroupoidsOver.Hom.stackTwoFibreProduct,
          StackInGroupoidsOver.ofAmbientHom, StackInGroupoidsOver.Hom.ofAmbientHomIso,
          FibredInGroupoidsOver.twoFibreProductSquare,
          FibredInGroupoidsOver.twoFibreProductLeftProjection,
          FibredInGroupoidsOver.twoFibreProduct, Functor.map_id, Category.id_comp,
          eqToHom_trans] using
          (eqToHom_comp_symm_of_eq_proof_forGerbeDescent rI rI')
      have hleftApplied :
          ((StackInGroupoidsOver.Hom.fibreOfPullback_pullbackObjIsoLeft
                (J := J) G F K.f P).hom ≫ eqToHom leftW) ≫
              (Q.p.fiberFunctor K.Y).map δ ≫
              (eqToHom leftW'.symm ≫
                (StackInGroupoidsOver.Hom.fibreOfPullback_pullbackObjIsoLeft
                  (J := J) G F K.f P').inv) =
            (eqToHom rI ≫ cQ.hom) ≫ (Q.p.fiberFunctor K.Y).map δ ≫
              (eqToHom leftW'.symm ≫
                (StackInGroupoidsOver.Hom.fibreOfPullback_pullbackObjIsoLeft
                  (J := J) G F K.f P').inv) := by
        -- Apply the normalized source comparison to the whole right-composed expression.
        exact
          congrArg
            (fun k => k ≫ (Q.p.fiberFunctor K.Y).map δ ≫
              (eqToHom leftW'.symm ≫
                (StackInGroupoidsOver.Hom.fibreOfPullback_pullbackObjIsoLeft
                  (J := J) G F K.f P').inv))
            hleft
      have hrightApplied :
          (eqToHom rI ≫ cQ.hom) ≫ (Q.p.fiberFunctor K.Y).map δ ≫
              (eqToHom leftW'.symm ≫
                (StackInGroupoidsOver.Hom.fibreOfPullback_pullbackObjIsoLeft
                  (J := J) G F K.f P').inv) =
            (eqToHom rI ≫ cQ.hom) ≫ (Q.p.fiberFunctor K.Y).map δ ≫
              cQ'.inv ≫ eqToHom rI'.symm := by
        -- Apply the normalized target comparison and flatten the resulting composition.
        simpa only [Category.assoc] using
          congrArg
            (fun k => (eqToHom rI ≫ cQ.hom) ≫
              (Q.p.fiberFunctor K.Y).map δ ≫ k)
            hright
      have hraw : δstd.fst = eqToHom rI ≫ m ≫ eqToHom rI'.symm := by
        calc
          δstd.fst =
            (StackInGroupoidsOver.Hom.fibreOfPullback_pullbackObjIsoLeft
              (J := J) G F K.f P).hom ≫ (eW.functor.map δ).fst ≫
              (StackInGroupoidsOver.Hom.fibreOfPullback_pullbackObjIsoLeft
                (J := J) G F K.f P').inv := by
            simp only [δstd, ix, ix',
              StackInGroupoidsOver.Hom.fibreOfPullback_pullbackObjIso,
              Limits.CategoricalPullback.comp_fst,
              Limits.CategoricalPullback.mkIso_hom_fst,
              Limits.CategoricalPullback.mkIso_inv_fst]
          _ = ((StackInGroupoidsOver.Hom.fibreOfPullback_pullbackObjIsoLeft
                (J := J) G F K.f P).hom ≫ eqToHom leftW) ≫
              (Q.p.fiberFunctor K.Y).map δ ≫
              (eqToHom leftW'.symm ≫
                (StackInGroupoidsOver.Hom.fibreOfPullback_pullbackObjIsoLeft
                  (J := J) G F K.f P').inv) := by
            rw [hpmap]
            simp only [Category.assoc]
          _ = (eqToHom rI ≫ cQ.hom) ≫ (Q.p.fiberFunctor K.Y).map δ ≫
              cQ'.inv ≫ eqToHom rI'.symm := hleftApplied.trans hrightApplied
          _ = (eqToHom rI ≫ cQ.hom) ≫ (inv cQ.hom ≫ m ≫ cQ'.hom) ≫
              cQ'.inv ≫ eqToHom rI'.symm := by
            simpa only [Category.assoc] using hsubst
          _ = eqToHom rI ≫ m ≫ eqToHom rI'.symm := by
            simpa only [Category.assoc] using hcancel
      exact hraw.trans hid
    let γ := Classical.choice (hy I)
    let cG := FibredCategoryMor.pullbackComparison G.toFibredCategoryMor K.f (y I)
    have hPobj :
        (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
            G.toBasedFunctor F.toBasedFunctor I.Y).functor.obj P =
          ({ fst := y I
             snd := I.f ^*[hcX] x
             iso := γ ≪≫
               FibredCategoryMor.pullbackComparison F.toFibredCategoryMor I.f x } :
            Limits.CategoricalPullback (G.fiberFunctor I.Y) (F.fiberFunctor I.Y)) := by
      rfl
    have hP'obj :
        (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
            G.toBasedFunctor F.toBasedFunctor I.Y).functor.obj P' =
          ({ fst := y I
             snd := I.f ^*[hcX] x'
             iso := γ ≪≫ (hcY.pullbackFunctor I.f).mapIso (asIso b) ≪≫
               FibredCategoryMor.pullbackComparison F.toFibredCategoryMor I.f x' } :
            Limits.CategoricalPullback (G.fiberFunctor I.Y) (F.fiberFunctor I.Y)) := by
      rfl
    let sourceIso :=
      (StackInGroupoidsOver.Hom.pullbackOfFiberProductObj G F K.f P.1.obj).iso.hom
    let targetIso :=
      (StackInGroupoidsOver.Hom.pullbackOfFiberProductObj G F K.f P'.1.obj).iso.hom
    let gPrefix :=
      cG.inv ≫ ((canonicalPullbackChoice Y.p).pullbackFunctor K.f).map γ.hom
    let leftIter :=
      ((canonicalPullbackChoice Y.p).pullbackFunctor K.f).map
          (((canonicalPullbackChoice Y.p).pullbackFunctor I.f).map b) ≫
        ((canonicalPullbackChoice Y.p).pullbackFunctor K.f).map
          (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor I.f x').hom ≫
        (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor K.f
          (I.f ^*[canonicalPullbackChoice X.p] x')).hom
    let rightIter :=
      ((canonicalPullbackChoice Y.p).pullbackFunctor K.f).map
          (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor I.f x).hom ≫
        (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor K.f
          (I.f ^*[canonicalPullbackChoice X.p] x)).hom ≫
        (F.fiberFunctor K.Y).map aIter
    have hsourceIso : sourceIso = gPrefix ≫
        ((canonicalPullbackChoice Y.p).pullbackFunctor K.f).map
          (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor I.f x).hom ≫
        (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor K.f
          (I.f ^*[canonicalPullbackChoice X.p] x)).hom := by
      simp only [sourceIso, gPrefix, γ, cG, P,
        StackInGroupoidsOver.Hom.pullbackOfFiberProductObj,
        Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
        ← canonicalPullbackFunctor_map_eq_fiberPseudofunctor_map_forGerbeDescent,
        Functor.map_comp]
      simpa only [hcX, cG, γ] using
        comp_assoc_four_forGerbeDescent
          cG.inv
          (((canonicalPullbackChoice Y.p).pullbackFunctor K.f).map γ.hom)
          (((canonicalPullbackChoice Y.p).pullbackFunctor K.f).map
            (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor I.f x).hom)
          ((FibredCategoryMor.pullbackComparison F.toFibredCategoryMor K.f
            (I.f ^*[hcX] x)).hom)
    have htargetIso : targetIso = gPrefix ≫ leftIter := by
      simp only [targetIso, gPrefix, leftIter, γ, cG, P',
        StackInGroupoidsOver.Hom.pullbackOfFiberProductObj,
        Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
        ← canonicalPullbackFunctor_map_eq_fiberPseudofunctor_map_forGerbeDescent,
        Functor.map_comp]
      simpa only [hcX, hcY, asIso_hom, cG, γ] using
        comp_assoc_five_forGerbeDescent
          cG.inv
          (((canonicalPullbackChoice Y.p).pullbackFunctor K.f).map γ.hom)
          (((canonicalPullbackChoice Y.p).pullbackFunctor K.f).map
            (((canonicalPullbackChoice Y.p).pullbackFunctor I.f).map b))
          (((canonicalPullbackChoice Y.p).pullbackFunctor K.f).map
            (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor I.f x').hom)
          ((FibredCategoryMor.pullbackComparison F.toFibredCategoryMor K.f
            (I.f ^*[hcX] x')).hom)
    have htarget :
        (G.fiberFunctor K.Y).map δstd.fst ≫ targetIso = gPrefix ≫ leftIter := by
      rw [hδfst]
      erw [Functor.map_id]
      erw [Category.id_comp]
      exact htargetIso
    have hsource :
        sourceIso ≫ (F.fiberFunctor K.Y).map δstd.snd = gPrefix ≫ rightIter := by
      rw [hsourceIso]
      simp only [rightIter, aIter]
      simpa only [gPrefix, hcX] using
        comp_assoc_append_forGerbeDescent
          cG.inv
          (((canonicalPullbackChoice Y.p).pullbackFunctor K.f).map γ.hom)
          (((canonicalPullbackChoice Y.p).pullbackFunctor K.f).map
            (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor I.f x).hom)
          ((FibredCategoryMor.pullbackComparison F.toFibredCategoryMor K.f
            (I.f ^*[hcX] x)).hom)
          ((F.fiberFunctor K.Y).map δstd.snd)
    -- The compatibility square of `δstd` has the same invertible `G`-prefix on both sides.
    -- Cancel that prefix, and the remaining equality is exactly the iterated right-leg square.
    exact (cancel_epi gPrefix).1 <| by
      exact htarget.symm.trans (δstd.w.trans hsource)
  refine ⟨S.bind T, ?_⟩
  intro A
  -- The bound cover arrow is the composite of the second-stage arrow with the first-stage arrow.
  let I : S.Arrow := A.fromMiddle
  let K : (T I).Arrow := A.toMiddle
  obtain ⟨a, ha⟩ := hT I K
  rw [← A.middle_spec]
  exact ⟨a, ha⟩

/-
Domain-style sampling for Lemma 8.11.7:
- primary domain: gerbes over morphisms of stacks in groupoids and their behavior under
  bicategorical `2`-cartesian squares;
- inspected owner-level declarations:
  `IsGerbeOver`,
  `StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects`,
  `BicategoricalTwoCommutativeSquare`,
  `Bicategory.IsFinal`;
- best owner abstraction: the source-facing theorem should be stated directly in terms of stack
  morphisms and the chapter's square owner `BicategoricalTwoCommutativeSquare G F`; the
  based-functor coercions are only bridge/view data and should not appear in the public statement;
- primitive data: the four stack morphisms, the comparison `2`-isomorphism `α`, the
  `2`-cartesian hypothesis on the resulting square, the local essential-image hypothesis on `G`,
  and the gerbe hypothesis on `F'`;
- derived API: descent of the gerbe-over property to `F`.

Source/core/bridge triage:
- `source-facing`: the gerbe descent statement of Lemma `8.11.7`;
- `core/canonical`: `IsGerbeOver`, `LocallyEssentiallySurjectiveOnObjects`,
  `BicategoricalTwoCommutativeSquare G F`, and `Bicategory.IsFinal`;
- `bridge/view`: the coercions from stack morphisms to based functors, which are not part of the
  refined theorem surface. -/

-- Proof sketch: the `2`-cartesian square identifies `X'` with the pullback `Y' ×_Y X`. Prove
-- conditions `(2)(a)` and `(2)(b)` of Lemma `8.11.3` for `F : X ⟶ Y`: first lift target objects
-- locally along `G`, then use that `F'` is a gerbe over `Y'`; for morphisms, pull the source
-- object back to `Y'`, form the corresponding objects of `X'`, and apply the local lifting
-- condition supplied by the gerbe structure on `F'`.
/-- Lemma 8.11.7: let
`X' --G'--> X`,
`X' --F'--> Y'`,
`Y' --G--> Y`,
and `X --F--> Y`
be a `2`-cartesian square of stacks in groupoids over a site `(C, J)`. If every object of every
fiber of `Y` is locally in the essential image of `G`, and if `X'` is a gerbe over `Y'`, then
`X` is a gerbe over `Y`. -/
@[stacks 06P4]
theorem isGerbeOver_of_twoCartesian_of_locallyEssentiallySurjective
    (hcart :
      Bicategory.IsFinal
        ({ obj := X'
           p := F'
           q := G'
           ψ := α } :
          BicategoricalTwoCommutativeSquare G F))
    (hG : StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects G)
    (hF' : StackInGroupoidsOver.Hom.IsGerbeOver F') :
    StackInGroupoidsOver.Hom.IsGerbeOver F := by
  let Q : BicategoricalTwoCommutativeSquare G F :=
    StackInGroupoidsOver.Hom.stackTwoFibreProductSquare (J := J) G F
  have hQp : StackInGroupoidsOver.Hom.IsGerbeOver Q.p :=
    canonicalLeftProjection_isGerbeOver_of_twoCartesian
      (J := J) (F := F) (G := G) (F' := F') (G' := G') (α := α) hcart hF'
  -- Reduce the target gerbe statement to the two local conditions from Lemma 8.11.3.
  rw [StackInGroupoidsOver.Hom.isGerbeOver_iff_locallyEssentiallySurjectiveOnObjects_and_locallyLiftsFiberMorphisms]
  refine ⟨?_, ?_⟩
  · exact
      leftProjectionGerbe_locallyEssentiallySurjectiveOnObjects_rightLeg
        (J := J) (F := F) (G := G) hG hQp.locallyEssentiallySurjectiveOnObjects
  · exact
      leftProjectionGerbe_locallyLiftsFiberMorphisms_rightLeg
        (J := J) (F := F) (G := G) hG hQp.locallyLiftsFiberMorphisms

end

end CategoryTheory
