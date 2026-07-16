import Mathlib
import stacks_proof.stacks_project.Chap04.Lemma_4_44_2
import stacks_proof.stacks_project.Chap04.Lemma_4_33_10
import stacks_proof.stacks_project.Chap08.Lemma_8_4_6.Index
import stacks_proof.stacks_project.Chap08.Lemma_8_4_6
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.Index
import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.Prelude
import stacks_proof.stacks_project.Chap07.Lemma_7_42_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open Bicategory
open FibredCategoryOver
open Opposite
open scoped Bicategory

universe uE vE t w

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [UnivLE.{max u v, v}]

variable {X Y Z : FibredCategoryOver C}
variable {X' Y' Z' : StackOver J}

namespace WideSubcategory

private abbrev toFibredCategoryMor {T S : StackOver J} (f : T ⟶ S) :=
  InducedCategory.Hom.toFibredCategoryMor f

end WideSubcategory

/- Domain-style sampling for Lemma 8.8.4:
- primary domain: stacks over a site together with bicategorical `2`-fibre products of fibred
  categories.
- inspected owner-level declarations:
  `FibredCategoryOver.twoFibreProduct`,
  `FibredCategoryOver.twoFibreProductSquare`,
  `FibredCategoryOver.twoFibreProduct_isTwoFibreProduct`,
  `BicategoricalTwoCommutativeSquare.postcompose`,
  `BicategoricalTwoCommutativeSquare.postcomposeRight`.
- best owner abstraction: the canonical comparison map should be derived from the owner square
  `FibredCategoryOver.twoFibreProductSquare` and the terminality of the pullback square for the
  lifted morphisms `f'` and `g'`; the old objectwise fiber construction is only bridge/view data.
- primitive data: the source pullback owner `twoFibreProduct f g`, the stackification maps
  `i`, `j`, `k`, and the ambient comparison `2`-isomorphisms `α`, `β`.
- derived API: the induced square over `f'` and `g'`, the terminal comparison morphism into the
  target pullback owner, and the resulting source-facing stackification theorem.

Source/core/bridge triage:
- `source-facing`: `twoFibreProduct_of_stackifications_isStackification`.
- `core/canonical`: `FibredCategoryOver.twoFibreProductSquare` together with
  `FibredCategoryOver.twoFibreProduct_isTwoFibreProduct`,
  `BicategoricalTwoCommutativeSquare.postcompose`,
  `BicategoricalTwoCommutativeSquare.postcomposeRight`.
- `bridge/view`: the induced square below and the terminal morphism
  `twoFibreProductOfStackificationsHom`. -/

/-- Helper for Chap08 Lemma 8 8 4: the source `2`-fibre-product square transported to the
chosen lifted morphisms `fF` and `gF`. -/
private noncomputable def twoFibreProductOfStackificationsSquare
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (fF : FibredCategoryMor X'.toFibredCategoryOver Y'.toFibredCategoryOver)
    (gF : FibredCategoryMor Z'.toFibredCategoryOver Y'.toFibredCategoryOver)
    (α : i ≫ fF ≅ f ≫ j)
    (β : k ≫ gF ≅ g ≫ j) :
    BicategoricalTwoCommutativeSquare fF gF :=
  -- Transport the source pullback square first across the right comparison `β`, then across the
  -- left comparison `α`, to obtain a square over the lifted morphisms.
  (((twoFibreProductSquare f g).postcompose β.symm).symm.postcomposeRight α.symm).symm

/-- Helper for Chap08 Lemma 8 8 4: the transported comparison square has the original explicit
two-fibre product as its apex. -/
private theorem twoFibreProductOfStackificationsSquare_obj
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (fF : FibredCategoryMor X'.toFibredCategoryOver Y'.toFibredCategoryOver)
    (gF : FibredCategoryMor Z'.toFibredCategoryOver Y'.toFibredCategoryOver)
    (α : i ≫ fF ≅ f ≫ j)
    (β : k ≫ gF ≅ g ≫ j) :
    (twoFibreProductOfStackificationsSquare f g i j k fF gF α β).obj =
      twoFibreProduct f g := by
  -- The postcomposition operations transport only the cospan labels, so the apex is unchanged.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the left edge of the transported comparison square is the
source left projection followed by the stackification map `i`. -/
private theorem twoFibreProductOfStackificationsSquare_p
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (fF : FibredCategoryMor X'.toFibredCategoryOver Y'.toFibredCategoryOver)
    (gF : FibredCategoryMor Z'.toFibredCategoryOver Y'.toFibredCategoryOver)
    (α : i ≫ fF ≅ f ≫ j)
    (β : k ≫ gF ≅ g ≫ j) :
    (twoFibreProductOfStackificationsSquare f g i j k fF gF α β).p =
      twoFibreProductLeftProjection f g ≫ i := by
  -- The final symmetry returns the transported right-edge data to the left projection slot.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the right edge of the transported comparison square is the
source right projection followed by the stackification map `k`. -/
private theorem twoFibreProductOfStackificationsSquare_q
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (fF : FibredCategoryMor X'.toFibredCategoryOver Y'.toFibredCategoryOver)
    (gF : FibredCategoryMor Z'.toFibredCategoryOver Y'.toFibredCategoryOver)
    (α : i ≫ fF ≅ f ≫ j)
    (β : k ≫ gF ≅ g ≫ j) :
    (twoFibreProductOfStackificationsSquare f g i j k fF gF α β).q =
      twoFibreProductRightProjection f g ≫ k := by
  -- The right endpoint is transported through `β`, while the left transport by `α` leaves it
  -- in the right projection slot after the last symmetry.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the target `2`-fibre product of stack morphisms carries the
stack structure as soon as the owner theorem for stack pullbacks is available from a compiling
dependency. -/
private theorem targetTwoFibreProduct_isStackOnSite_from_owner
    (hOwner : ∀ {A B S : StackOver J} (F : A ⟶ S) (G : B ⟶ S),
      IsStackOnSite J
        (twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p)
    (F : X' ⟶ Y') (G : Z' ⟶ Y') :
    IsStackOnSite J
      (twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p := by
  -- Specialize the owner-level pullback-stack theorem to the two stack morphisms used in this
  -- comparison target.
  exact hOwner F G

/-- Helper for Chap08 Lemma 8 8 4: the componentwise fixed-cover descent comparison for a
stack-level two-fibre product is an equivalence. -/
private theorem stackTwoFibreProduct_descentComponentMap_isEquivalence
    (F : X' ⟶ Y') (G : Z' ⟶ Y') {U : C} (T : J.Cover U) :
    (two_fibre_product_map
        (cover_descent_data_functor_of_stack_morphism_toDescentData_iso
          (J := J) (InducedCategory.Hom.toFibredCategoryMor G) T)
        ((cover_descent_data_functor_of_stack_morphism_toDescentData_iso
          (J := J) (InducedCategory.Hom.toFibredCategoryMor F) T).symm)).IsEquivalence := by
  -- This is the componentwise descent equivalence supplied by the imported Lemma 8.4.6 support
  -- module, before whiskering by the explicit fiber-pullback equivalence.
  exact cover_descent_two_fibre_product_map_isEquivalence_bridge_explicit (J := J) F G T

/-- Helper for Chap08 Lemma 8 8 4: the already exported fixed-cover pullback model for a
stack-level two-fibre product is an equivalence. -/
private theorem stackTwoFibreProduct_pullbackModelDescent_isEquivalence
    (F : X' ⟶ Y') (G : Z' ⟶ Y') {U : C} (T : J.Cover U) :
    (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (InducedCategory.Hom.toBasedFunctor F) (InducedCategory.Hom.toBasedFunctor G) U).functor) ⋙
      two_fibre_product_map
        (cover_descent_data_functor_of_stack_morphism_toDescentData_iso
          (J := J) (InducedCategory.Hom.toFibredCategoryMor G) T)
        ((cover_descent_data_functor_of_stack_morphism_toDescentData_iso
          (J := J) (InducedCategory.Hom.toFibredCategoryMor F) T).symm)).IsEquivalence := by
  -- Freeze the target-specific form of the public pullback-model theorem; the remaining
  -- fixed-cover blocker is only the bridge from this model to the canonical descent functor.
  exact cover_descent_pullback_model_isEquivalence_bridge_explicit (J := J) F G T

/-- Helper for Chap08 Lemma 8 8 4: a stack structure on the target `2`-fibre product supplies
the fixed-cover canonical descent equivalence needed by the coverwise stack criterion. -/
private theorem stackTwoFibreProduct_coverwiseDescent_of_isStackOnSite
    (F : X' ⟶ Y') (G : Z' ⟶ Y')
    (hStack : IsStackOnSite J
      (twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p)
    {U : C} (T : J.Cover U) :
    ((canonicalFiberPseudofunctor
        (twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p).toDescentData
          (fun I : T.Arrow ↦ I.f)).IsEquivalence := by
  -- Turn the explicit stack proof into the fibration instance required by the coverwise
  -- characterization, then project out the fixed-cover equivalence.
  letI : (twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p.IsFibered :=
    hStack.toIsFibered
  exact
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J
      (twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p).1
      hStack U T

/-- Helper for Chap08 Lemma 8 8 4: an owner-level theorem that stack pullbacks of stacks are
stacks immediately gives the fixed-cover descent equivalence for the chosen target pullback. -/
private theorem stackTwoFibreProduct_coverwiseDescent_from_owner
    (hOwner : ∀ {A B S : StackOver J} (F : A ⟶ S) (G : B ⟶ S),
      IsStackOnSite J
        (twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p)
    (F : X' ⟶ Y') (G : Z' ⟶ Y') {U : C} (T : J.Cover U) :
    ((canonicalFiberPseudofunctor
        (twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p).toDescentData
          (fun I : T.Arrow ↦ I.f)).IsEquivalence := by
  -- Specialize the owner theorem to this pullback target, then use the coverwise adapter above.
  exact
    stackTwoFibreProduct_coverwiseDescent_of_isStackOnSite
      (J := J) F G (targetTwoFibreProduct_isStackOnSite_from_owner hOwner F G) T

/-- Helper for Chap08 Lemma 8 8 4: the missing fixed-cover descent equivalence for stack-level
two-fibre products, isolated from the non-compiling owner module. -/
private theorem stackTwoFibreProduct_coverwiseDescent_isEquivalence
    (F : X' ⟶ Y') (G : Z' ⟶ Y')
    [(twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p.IsFibered]
    {U : C} (T : J.Cover U) :
    ((canonicalFiberPseudofunctor
        (twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p).toDescentData
          (fun I : T.Arrow ↦ I.f)).IsEquivalence := by
  -- The aggregate Lemma 8.4.6 owner theorem is now usable in this Lake state; apply it and then
  -- project the fixed-cover descent equivalence through the coverwise stack criterion.
  exact
    stackTwoFibreProduct_coverwiseDescent_of_isStackOnSite
      (J := J) F G (stackTwoFibreProduct_isStack (J := J) F G) T

/-- Helper for Chap08 Lemma 8 8 4: coverwise descent equivalences give the stack structure on
the target `2`-fibre product of two stack morphisms. -/
private theorem stackTwoFibreProduct_isStack_from_coverwiseDescent
    (F : X' ⟶ Y') (G : Z' ⟶ Y') :
    IsStackOnSite J
      (twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p := by
  -- Supply the explicit two-fibre-product fibration instance and apply the coverwise stack
  -- criterion; the only remaining content is the fixed-cover equivalence above.
  letI : (twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p.IsFibered :=
    stack_two_fibre_product_projection_isFibered F G
  exact
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J
      (twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p).2
      (fun _ T ↦
        stackTwoFibreProduct_coverwiseDescent_isEquivalence (J := J) F G T)

/-- Helper for Chap08 Lemma 8 8 4: the target `2`-fibre product of stack morphisms carries the
stack structure supplied by Lemma 8.4.6. -/
private instance targetTwoFibreProduct_isStackOnSite
    (F : X' ⟶ Y') (G : Z' ⟶ Y') :
    IsStackOnSite J
      (twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p := by
  -- Route correction: the aggregate Lemma 8.4.6 module currently fails before exporting its owner
  -- theorem, so use the dependency-closed coverwise adapter and expose the precise missing
  -- fixed-cover equivalence as the remaining prerequisite.
  exact stackTwoFibreProduct_isStack_from_coverwiseDescent F G

/-- Helper for Chap08 Lemma 8 8 4: two local essential-image isomorphisms compose after
replacing the iterated chosen pullback by the chosen pullback along the composite base arrow. -/
private noncomputable def compLocalEssentialImageIso
    {A B D : FibredCategoryOver C}
    (F : A ⟶ B) (G : B ⟶ D)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (z : D.p.Fiber U) (y : B.p.Fiber V) (x : A.p.Fiber W)
    (ηF : (FibredCategoryMor.fiberFunctor F W).obj x ≅
      g ^*[canonicalPullbackChoice B.p] y)
    (ηG : (FibredCategoryMor.fiberFunctor G V).obj y ≅
      f ^*[canonicalPullbackChoice D.p] z) :
    (FibredCategoryMor.fiberFunctor (F ≫ G) W).obj x ≅
      (g ≫ f) ^*[canonicalPullbackChoice D.p] z :=
  Iso.trans
    (Iso.trans
      (Functor.mapIso (FibredCategoryMor.fiberFunctor G W) ηF)
      (FibredCategoryMor.pullbackComparison G g y).symm)
    (Iso.trans
      (((canonicalPullbackChoice D.p).pullbackFunctor g).mapIso ηG)
      ((canonicalPullbackChoice D.p).pullbackCompComponentIso f g z).symm)

/-- Helper for Chap08 Lemma 8 8 4: local essential surjectivity on objects is stable under
composition of fibred-category morphisms. -/
private theorem locallyEssentiallySurjectiveOnObjects_comp
    {A B D : FibredCategoryOver C}
    (F : A ⟶ B) (G : B ⟶ D)
    (hF : FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J F)
    (hG : FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J G) :
    FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J (F ≫ G) := by
  classical
  intro U z
  -- First lift the target object locally through `G`, then lift each chosen local model through
  -- `F` on the bound refinement.
  obtain ⟨S, hS⟩ := hG U z
  choose y hy using hS
  let T : ∀ I : S.Arrow, J.Cover I.Y := fun I => Classical.choose (hF I.Y (y I))
  have hT : ∀ I : S.Arrow, ∀ R : (T I).Arrow,
      ∃ x : A.p.Fiber R.Y,
        Nonempty (((FibredCategoryMor.fiberFunctor F R.Y).obj x) ≅
          R.f ^*[canonicalPullbackChoice B.p] (y I)) := by
    intro I
    exact Classical.choose_spec (hF I.Y (y I))
  refine ⟨S.bind T, ?_⟩
  intro R
  -- The arrow of the bound cover is a second-stage arrow followed by a first-stage arrow, so the
  -- two local image isomorphisms compose after rewriting by `middle_spec`.
  let I : S.Arrow := R.fromMiddle
  let K : (T I).Arrow := R.toMiddle
  obtain ⟨x, hx⟩ := hT I K
  obtain ⟨ηF⟩ := hx
  obtain ⟨ηG⟩ := hy I
  refine ⟨x, ?_⟩
  rw [← R.middle_spec]
  refine ⟨?_⟩
  simpa [I, K, BasedFunctor.comp] using
    compLocalEssentialImageIso F G I.f K.f z (y I) x ηF ηG

/-- Helper for Chap08 Lemma 8 8 4: the Hom-presheaf `W` condition is stable under composition of
fibred-category morphisms. -/
private theorem morphismPresheafMap_W_comp
    {A B D : FibredCategoryOver C}
    (F : A ⟶ B) (G : B ⟶ D)
    (hF : ∀ (U : C) (x y : A.p.Fiber U),
      (J.over U).W (FibredCategoryMor.fibredMorphismPresheafMap F x y))
    (hG : ∀ (U : C) (x y : B.p.Fiber U),
      (J.over U).W (FibredCategoryMor.fibredMorphismPresheafMap G x y)) :
    ∀ (U : C) (x y : A.p.Fiber U),
      (J.over U).W (FibredCategoryMor.fibredMorphismPresheafMap (F ≫ G) x y) := by
  intro U x y
  -- Rewrite the composite Hom-presheaf map to a categorical composite and use closure of `W`.
  rw [fibredMorphismPresheafMap_comp F G x y]
  exact (J.over U).W.comp_mem _ _ (hF U x y)
    (hG U ((FibredCategoryMor.fiberFunctor F U).obj x)
      ((FibredCategoryMor.fiberFunctor F U).obj y))

/-- Helper for Chap08 Lemma 8 8 4: fieldwise stackification data for a first morphism composes
with a stackification morphism on the target. -/
private theorem isStackification_comp_of_stackificationData
    {A B : FibredCategoryOver C} {D : StackOver J}
    (F : A ⟶ B) (G : B ⟶ D)
    (hFW : ∀ (U : C) (x y : A.p.Fiber U),
      (J.over U).W (FibredCategoryMor.fibredMorphismPresheafMap F x y))
    (hFess : FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J F)
    (hG : FibredCategoryMor.IsStackification G) :
    FibredCategoryMor.IsStackification (F ≫ G) := by
  constructor
  · -- Compose the two Hom-presheaf local equivalence conditions.
    exact morphismPresheafMap_W_comp F G hFW hG.morphismPresheafMap_W
  · -- Compose the two local essential-image conditions using cover binding.
    exact locallyEssentiallySurjectiveOnObjects_comp F G hFess
      hG.locallyEssentiallySurjectiveOnObjects

/-- Helper for Chap08 Lemma 8 8 4: the composite of two stackification morphisms is again a
stackification. -/
private theorem isStackification_comp
    {A : FibredCategoryOver C} {B D : StackOver J}
    (F : A ⟶ B) (G : B.toFibredCategoryOver ⟶ D)
    (hF : FibredCategoryMor.IsStackification F)
    (hG : FibredCategoryMor.IsStackification G) :
    FibredCategoryMor.IsStackification (F ≫ G) := by
  -- Package the two fields of the first stackification and feed them to the already proved
  -- fieldwise composition lemma.
  exact isStackification_comp_of_stackificationData F G
    hF.morphismPresheafMap_W hF.locallyEssentiallySurjectiveOnObjects hG

/-- Helper for Chap08 Lemma 8 8 4: an equivalence over the base induces local weak
equivalences on all Hom presheaves. -/
private theorem morphismPresheafMap_W_of_isEquivalenceOverBase
    {A : FibredCategoryOver C} {D : StackOver J}
    (H : A ⟶ D)
    (hH : FibredCategoryMor.IsEquivalenceOverBase H) :
    ∀ (U : C) (x y : A.p.Fiber U),
      (J.over U).W (FibredCategoryMor.fibredMorphismPresheafMap H x y) := by
  intro U x y
  -- Convert the fiberwise equivalence into an isomorphism of Hom presheaves, then use the slice
  -- topology's closure under isomorphisms.
  have hIso : IsIso (FibredCategoryMor.fibredMorphismPresheafMap H x y) :=
    fibredMorphismPresheafMap_isIso_of_isEquivalenceOverBase H hH x y
  let τ := FibredCategoryMor.fibredMorphismPresheafMap H x y
  let _ : IsIso τ := hIso
  exact (J.over U).W.of_isIso τ

/-- Helper for Chap08 Lemma 8 8 4: an equivalence over the base is locally essentially
surjective on objects. -/
private theorem locallyEssentiallySurjectiveOnObjects_of_isEquivalenceOverBase
    {A : FibredCategoryOver C} {D : StackOver J}
    (H : A ⟶ D)
    (hH : FibredCategoryMor.IsEquivalenceOverBase H) :
    FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J H := by
  intro U y
  -- The top cover is enough: every fiber functor of an equivalence over the base is essentially
  -- surjective, so it locally represents the pulled-back target object.
  refine ⟨⊤, ?_⟩
  intro I
  let Φ := FibredCategoryMor.fiberFunctor H I.Y
  have hFiberEquiv : Φ.IsEquivalence :=
    BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase
      (FibredCategoryMor.toBasedFunctor H) hH I.Y
  let _ : Φ.IsEquivalence := hFiberEquiv
  let _ : Φ.EssSurj := by infer_instance
  obtain ⟨x, ⟨η⟩⟩ := Functor.EssSurj.mem_essImage
    (F := Φ) (I.f ^*[canonicalPullbackChoice D.p] y)
  exact ⟨x, ⟨η⟩⟩

/-- Helper for Chap08 Lemma 8 8 4: an equivalence over the base between stacks is a
stackification morphism. -/
private theorem isStackification_of_isEquivalenceOverBase
    {D E : StackOver J}
    (H : D.toFibredCategoryOver ⟶ E)
    (hH : FibredCategoryMor.IsEquivalenceOverBase H) :
    FibredCategoryMor.IsStackification H := by
  constructor
  · -- Reuse the extracted Hom-presheaf field for equivalences over the base.
    exact morphismPresheafMap_W_of_isEquivalenceOverBase H hH
  · -- Reuse the extracted local essential-surjectivity field for equivalences over the base.
    exact locallyEssentiallySurjectiveOnObjects_of_isEquivalenceOverBase H hH

/-- Helper for Chap08 Lemma 8 8 4: postcomposing a stackification with a target equivalence over
the base preserves the stackification condition. -/
private theorem isStackification_comp_right_of_isEquivalenceOverBase
    {A : FibredCategoryOver C} {D E : StackOver J}
    (F : A ⟶ D)
    (H : D.toFibredCategoryOver ⟶ E)
    (hF : FibredCategoryMor.IsStackification F)
    (hH : FibredCategoryMor.IsEquivalenceOverBase H) :
    FibredCategoryMor.IsStackification (F ≫ H) := by
  -- Package the target equivalence as a stackification and use the composition lemma already
  -- established for stackification data.
  exact isStackification_comp F H hF
    (isStackification_of_isEquivalenceOverBase H hH)

/-- Helper for Chap08 Lemma 8 8 4: the Hom-presheaf `W` field of a stackification transports
across an owner isomorphism of fibred-category morphisms with the same stack target. -/
private theorem morphismPresheafMap_W_of_ownerIso
    {A : FibredCategoryOver C} {D : StackOver J}
    {F G : A ⟶ D}
    (α : F ≅ G)
    (hF : ∀ (U : C) (x y : A.p.Fiber U),
      (J.over U).W (FibredCategoryMor.fibredMorphismPresheafMap F x y)) :
    ∀ (U : C) (x y : A.p.Fiber U),
      (J.over U).W (FibredCategoryMor.fibredMorphismPresheafMap G x y) := by
  intro U x y
  -- The owner isomorphism conjugates the target Hom presheaf by fiberwise isomorphisms, so the
  -- `W` condition is unchanged after postcomposition with that presheaf isomorphism.
  let τ :=
    (fiberHomPresheafIso (Y := D.toFibredCategoryOver)
      (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) U x)
      (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) U y)).hom
  have hfac :
      FibredCategoryMor.fibredMorphismPresheafMap G x y =
        FibredCategoryMor.fibredMorphismPresheafMap F x y ≫ τ := by
    ext W δ
    exact fibredMorphismPresheafMap_natural_of_ownerIso_app α x y W δ
  have hIso : MorphismProperty.isomorphisms _ τ := by
    infer_instance
  rw [hfac]
  exact
      (((GrothendieckTopology.W (J := J.over U) (A := Type _)).postcomp_iff
      (W' := MorphismProperty.isomorphisms _)
      (FibredCategoryMor.fibredMorphismPresheafMap F x y)
      τ hIso).2 (hF U x y))

/-- Helper for Chap08 Lemma 8 8 4: precomposing a Hom-presheaf `W` condition with an
equivalence over the base preserves the condition. -/
private theorem morphismPresheafMap_W_comp_left_of_isEquivalenceOverBase
    {A B : FibredCategoryOver C} {D : StackOver J}
    (E : A ⟶ B)
    (hE : FibredCategoryMor.IsEquivalenceOverBase E)
    (G : B ⟶ D)
    (hG : ∀ (U : C) (x y : B.p.Fiber U),
      (J.over U).W (FibredCategoryMor.fibredMorphismPresheafMap G x y)) :
    ∀ (U : C) (x y : A.p.Fiber U),
      (J.over U).W (FibredCategoryMor.fibredMorphismPresheafMap (E ≫ G) x y) := by
  intro U x y
  -- Factor the composite Hom-presheaf map into the source-equivalence part followed by the
  -- target stackification part.
  rw [fibredMorphismPresheafMap_comp E G x y]
  have hIso : IsIso (FibredCategoryMor.fibredMorphismPresheafMap E x y) :=
    fibredMorphismPresheafMap_isIso_of_isEquivalenceOverBase E hE x y
  let τ := FibredCategoryMor.fibredMorphismPresheafMap E x y
  let _ : IsIso τ := hIso
  -- The first factor is an isomorphism in the slice-local class, and the second factor is the
  -- given `W` condition for `G`.
  exact
    (J.over U).W.comp_mem _ _
      ((J.over U).W.of_isIso τ)
      (hG U
        ((FibredCategoryMor.fiberFunctor E U).obj x)
        ((FibredCategoryMor.fiberFunctor E U).obj y))

/-- Helper for Chap08 Lemma 8 8 4: local essential surjectivity transports across an owner
isomorphism of fibred-category morphisms with the same target. -/
private theorem locallyEssentiallySurjectiveOnObjects_of_ownerIso
    {A : FibredCategoryOver C} {D : StackOver J}
    {F G : A ⟶ D}
    (α : F ≅ G)
    (hF : FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J F) :
    FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J G := by
  intro U y
  -- Reuse the local models for `F`; on each cover arrow, the fiberwise component of `α`
  -- converts the `G`-image of the same source object to the corresponding `F`-image.
  obtain ⟨S, hS⟩ := hF U y
  refine ⟨S, ?_⟩
  intro I
  obtain ⟨x, ⟨ηF⟩⟩ := hS I
  let ηα :=
    basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) I.Y x
  exact ⟨x, ⟨ηα.symm ≪≫ ηF⟩⟩

/-- Helper for Chap08 Lemma 8 8 4: being a stackification is invariant under owner isomorphism
of the comparison morphism. -/
private theorem isStackification_of_ownerIso
    {A : FibredCategoryOver C} {D : StackOver J}
    {F G : A ⟶ D}
    (α : F ≅ G)
    (hF : FibredCategoryMor.IsStackification F) :
    FibredCategoryMor.IsStackification G := by
  constructor
  · -- Transport the Hom-presheaf field through the fiberwise conjugation induced by `α`.
    exact morphismPresheafMap_W_of_ownerIso α hF.morphismPresheafMap_W
  · -- Transport the local object-image field through the same fiberwise isomorphism.
    exact locallyEssentiallySurjectiveOnObjects_of_ownerIso α
      hF.locallyEssentiallySurjectiveOnObjects

/-- Helper for Chap08 Lemma 8 8 4: precomposing a stackification with a source equivalence
over the base preserves the stackification condition. -/
private theorem isStackification_comp_left_of_isEquivalenceOverBase
    {A B : FibredCategoryOver C} {D : StackOver J}
    (E : A ⟶ B)
    (hE : FibredCategoryMor.IsEquivalenceOverBase E)
    (G : B ⟶ D)
    (hG : FibredCategoryMor.IsStackification G) :
    FibredCategoryMor.IsStackification (E ≫ G) := by
  constructor
  · -- Reuse the extracted Hom-presheaf transport lemma for precomposition by a source
    -- equivalence.
    exact morphismPresheafMap_W_comp_left_of_isEquivalenceOverBase
      E hE G hG.morphismPresheafMap_W
  · -- Local essential surjectivity is invariant under precomposition by a source equivalence.
    exact
      locallyEssentiallySurjectiveOnObjects_comp_left_of_isEquivalenceOverBase
        E hE G hG.locallyEssentiallySurjectiveOnObjects

/-- Helper for Chap08 Lemma 8 8 4: if postcomposition with a target equivalence over the base
is a stackification, then the original morphism is already a stackification. -/
private theorem isStackification_of_comp_right_isEquivalenceOverBase
    {A : FibredCategoryOver C} {D E : StackOver J}
    (F : A ⟶ D)
    (H : D.toFibredCategoryOver ⟶ E)
    (hH : FibredCategoryMor.IsEquivalenceOverBase H)
    (hFH : FibredCategoryMor.IsStackification (F ≫ H)) :
    FibredCategoryMor.IsStackification F := by
  constructor
  · intro U x y
    -- Reflect the Hom-presheaf `W` condition through the isomorphism induced by the target
    -- equivalence on the already-composed comparison map.
    have hcomp := hFH.morphismPresheafMap_W U x y
    rw [fibredMorphismPresheafMap_comp F H x y] at hcomp
    have hIso : IsIso (FibredCategoryMor.fibredMorphismPresheafMap H
        ((FibredCategoryMor.fiberFunctor F U).obj x)
        ((FibredCategoryMor.fiberFunctor F U).obj y)) :=
      fibredMorphismPresheafMap_isIso_of_isEquivalenceOverBase H hH
        ((FibredCategoryMor.fiberFunctor F U).obj x)
        ((FibredCategoryMor.fiberFunctor F U).obj y)
    let τ := FibredCategoryMor.fibredMorphismPresheafMap H
      ((FibredCategoryMor.fiberFunctor F U).obj x)
      ((FibredCategoryMor.fiberFunctor F U).obj y)
    let _ : IsIso τ := hIso
    have hIsoProp : MorphismProperty.isomorphisms _ τ := by
      infer_instance
    have hcomp' :
        (J.over U).W (FibredCategoryMor.fibredMorphismPresheafMap F x y ≫ τ) := by
      exact hcomp
    exact
      (((GrothendieckTopology.W (J := J.over U) (A := Type _)).postcomp_iff
        (W' := MorphismProperty.isomorphisms _)
        (FibredCategoryMor.fibredMorphismPresheafMap F x y)
        τ hIsoProp).1 hcomp')
  · intro U y
    -- Lift the target object through the composite and use full faithfulness of the fiber
    -- equivalence to reflect the resulting local isomorphism back before applying `H`.
    obtain ⟨S, hS⟩ := hFH.locallyEssentiallySurjectiveOnObjects U
      ((FibredCategoryMor.fiberFunctor H U).obj y)
    refine ⟨S, ?_⟩
    intro I
    obtain ⟨x, ⟨ηFH⟩⟩ := hS I
    have hFiberEquiv : (FibredCategoryMor.fiberFunctor H I.Y).IsEquivalence :=
      BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase
        (FibredCategoryMor.toBasedFunctor H) hH I.Y
    let Φ := FibredCategoryMor.fiberFunctor H I.Y
    let _ : Φ.IsEquivalence := hFiberEquiv
    have hFF : Φ.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful Φ
    let ηTarget :
        Φ.obj ((FibredCategoryMor.fiberFunctor F I.Y).obj x) ≅
      Φ.obj (I.f ^*[canonicalPullbackChoice D.p] y) := by
      change (FibredCategoryMor.fiberFunctor (F ≫ H) I.Y).obj x ≅
          Φ.obj (I.f ^*[canonicalPullbackChoice D.p] y)
      exact ηFH ≪≫ (FibredCategoryMor.pullbackComparison H I.f y)
    exact ⟨x, ⟨hFF.preimageIso ηTarget⟩⟩

/-- Helper for Chap08 Lemma 8 8 4: a Type-valued presheaf morphism is in `W` if its
`ULift`-whiskering is in `W`. This avoids committing the small Hom-presheaf value universe to a
locally-bijective `W` instance. -/
private theorem W_of_whiskerRight_ulift
    {E : Type uE} [Category.{vE} E] (L : GrothendieckTopology E)
    {P Q : Eᵒᵖ ⥤ Type t} (η : P ⟶ Q)
    [L.HasSheafCompose
      (CategoryTheory.uliftFunctor.{max uE vE, t} :
        Type t ⥤ Type (max t (max uE vE)))]
    (h : L.W
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max uE vE, t} :
          Type t ⥤ Type (max t (max uE vE))))) :
    L.W η := by
  let U : Type t ⥤ Type (max t (max uE vE)) :=
    CategoryTheory.uliftFunctor.{max uE vE, t}
  let WR :=
    (Functor.whiskeringRight Eᵒᵖ (Type t) (Type (max t (max uE vE)))).obj U
  have hWR : WR.FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful U).whiskeringRight Eᵒᵖ
  intro Z hZ
  have hZU : Presheaf.IsSheaf L (Z ⋙ U) :=
    GrothendieckTopology.HasSheafCompose.isSheaf (J := L) (F := U) Z hZ
  have hbij := h (Z ⋙ U) hZU
  constructor
  · intro g₁ g₂ hg
    have hlarge : WR.map g₁ = WR.map g₂ := by
      apply hbij.1
      simpa only [WR, Functor.whiskeringRight_obj_map] using
        congrArg (fun θ => WR.map θ) hg
    exact hWR.map_injective hlarge
  · intro k
    obtain ⟨gU, hgU⟩ := hbij.2 (WR.map k)
    let g : Q ⟶ Z := WR.preimage gU
    refine ⟨g, ?_⟩
    apply hWR.map_injective
    have hmap : WR.map (η ≫ g) = WR.map η ≫ gU := by
      rw [WR.map_comp, WR.map_preimage]
      rfl
    exact hmap.trans (by
      simpa only [WR, Functor.whiskeringRight_obj_map] using hgU)

/-- Helper for Chap08 Lemma 8 8 4: under a local-bijectivity bridge, a `W` morphism of
Type-valued presheaves is locally injective. -/
private theorem W_to_type_isLocallyInjective
    {E : Type uE} [Category.{vE} E] (L : GrothendieckTopology E)
    {P Q : Eᵒᵖ ⥤ Type t} (η : P ⟶ Q)
    [L.WEqualsLocallyBijective (Type t)]
    (hη : L.W η) :
    Presheaf.IsLocallyInjective L η := by
  exact hη.isLocallyInjective

/-- Helper for Chap08 Lemma 8 8 4: a `W` morphism into a sheaf-valued Type presheaf is locally
surjective without using a universe-specific `WEqualsLocallyBijective` instance. -/
private theorem W_to_sheaf_isLocallySurjective
    {E : Type uE} [Category.{vE} E] (L : GrothendieckTopology E)
    {P Q : Eᵒᵖ ⥤ Type t} (η : P ⟶ Q)
    [HasWeakSheafify L (Type t)]
    (hη : L.W η) (hQ : Presheaf.IsSheaf L Q) :
    Presheaf.IsLocallySurjective L η := by
  classical
  rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']
  let Rsub : Subfunctor Q := (Subfunctor.range η).sheafify L
  let R : Eᵒᵖ ⥤ Type t := Rsub.toFunctor
  let i : R ⟶ Q := Rsub.ι
  have hQ' : Presieve.IsSheaf L Q := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact hQ
  have hRpresieve : Presieve.IsSheaf L R := by
    exact Subfunctor.sheafify_isSheaf (J := L) (G := Subfunctor.range η) hQ'
  have hR : Presheaf.IsSheaf L R := by
    rw [isSheaf_iff_isSheaf_of_type]
    exact hRpresieve
  have hfac : Subfunctor.toRangeSheafify L η ≫ i = η := by
    ext U x
    rfl
  have hbij := hη R hR
  obtain ⟨r, hr⟩ := hbij.2 (Subfunctor.toRangeSheafify L η)
  have hri : r ≫ i = 𝟙 Q := by
    apply (hη Q hQ).1
    calc
      η ≫ (r ≫ i) = (η ≫ r) ≫ i := by simp only [Category.assoc]
      _ = Subfunctor.toRangeSheafify L η ≫ i := by
        rw [show η ≫ r = Subfunctor.toRangeSheafify L η from hr]
      _ = η := hfac
      _ = η ≫ 𝟙 Q := by simp only [Category.comp_id]
  have hir : i ≫ r = 𝟙 R := by
    apply (cancel_mono i).1
    simp only [Category.assoc, hri, Category.comp_id, Category.id_comp]
  haveI : IsIso i := ⟨⟨r, hir, hri⟩⟩
  exact (Subfunctor.eq_top_iff_isIso (G := Rsub)).2 inferInstance

/-- Helper for Chap08 Lemma 8 8 4: the small Type-valued locally-bijective bridge on an over
site, obtained from the ambient universe bound. -/
private theorem over_WEqualsLocallyBijective_small (U : C) :
    (J.over U).WEqualsLocallyBijective (Type v) := by
  let _ :
      ∀ P' : (Over U)ᵒᵖ ⥤ Type v,
        Presheaf.IsLocallyInjective (J.over U) (toSheafify (J.over U) P') := by
    intro P'
    exact
      CategoryTheory.Functor.small_type_toSheafify_isLocallyInjective_of_univLE
        (L := J.over U) P'
  let _ :
      ∀ P' : (Over U)ᵒᵖ ⥤ Type v,
        Presheaf.IsLocallySurjective (J.over U) (toSheafify (J.over U) P') := by
    intro P'
    exact
      CategoryTheory.Functor.toSheafify_isLocallySurjective_type_of_hasWeakSheafify
        (L := J.over U) P'
  exact GrothendieckTopology.WEqualsLocallyBijective.mk'
    (J := J.over U) (A := Type v)

/-- Helper for Chap08 Lemma 8 8 4: morphisms in the total category of an explicit two-fibre
product are determined by their left and right component morphisms. -/
private theorem twoFibreProductHom_ext_components
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    {P Q : (twoFibreProduct f g).S}
    (φ ψ : P ⟶ Q)
    (ha : φ.a = ψ.a) (hb : φ.b = ψ.b) :
    φ = ψ := by
  -- The owner extensionality lemma for explicit pullback morphisms cancels the proof fields and
  -- the common base arrow once the two component maps agree.
  apply CategoryOver.ExplicitTwoFibreProductHom.ext
  · exact ha
  · exact hb

/-- Helper for Chap08 Lemma 8 8 4: morphisms in a fiber of an explicit two-fibre product are
determined by their left and right component morphisms. -/
private theorem twoFibreProductFiberHom_ext_components
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    {U : C} {P Q : (twoFibreProduct f g).p.Fiber U}
    (φ ψ : P ⟶ Q)
    (ha : φ.1.a = ψ.1.a) (hb : φ.1.b = ψ.1.b) :
    φ = ψ := by
  -- Forget the outer fiber packaging, then apply the total-category componentwise
  -- extensionality lemma.
  apply Functor.Fiber.hom_ext
  exact twoFibreProductHom_ext_components f g φ.1 ψ.1 ha hb

/-- Helper for Chap08 Lemma 8 8 4: equality transports do not depend on the chosen equality
proof. -/
private theorem eqToHom_eq_of_proofs_local
    {D : Type uE} [Category.{vE} D] {A B : D} (h h' : A = B) :
    eqToHom h = eqToHom h' := by
  cases h
  cases h'
  rfl

/-- Helper for Chap08 Lemma 8 8 4: composing two equality transports gives any transport with
the same endpoints. -/
private theorem eqToHom_comp_eqToHom_eqToHom_local
    {D : Type uE} [Category.{vE} D] {A B C : D}
    (hAB : A = B) (hBC : B = C) (hAC : A = C) :
    eqToHom hAB ≫ eqToHom hBC = eqToHom hAC := by
  cases hAB
  cases hBC
  cases hAC
  simp only [eqToHom_refl, Category.id_comp]

/-- Helper for Chap08 Lemma 8 8 4: a morphism in the left projected fibre lies over the
transported identity between the underlying total two-fibre-product bases. -/
private theorem twoFibreProduct_leftFiberHom_isHomLift
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    {U : C} (P Q : (twoFibreProduct f g).p.Fiber U)
    (a : ((FibredCategoryMor.fiberFunctor (twoFibreProductLeftProjection f g) U).obj P) ⟶
      ((FibredCategoryMor.fiberFunctor (twoFibreProductLeftProjection f g) U).obj Q)) :
    X.p.IsHomLift (eqToHom P.2 ≫ (𝟙 U) ≫ eqToHom Q.2.symm) a.1 := by
  letI : X.p.IsHomLift (𝟙 U) a.1 := a.2
  refine IsHomLift.of_fac' X.p
    (eqToHom P.2 ≫ (𝟙 U) ≫ eqToHom Q.2.symm) a.1
    P.1.obj.fst.2 Q.1.obj.fst.2 ?_
  rw [IsHomLift.fac' X.p (𝟙 U) a.1]
  have hdom :
      eqToHom (IsHomLift.domain_eq X.p (𝟙 U) a.1) =
        eqToHom (P.1.obj.fst.2.trans P.2) :=
    eqToHom_eq_of_proofs_local _ _
  have hcod :
      eqToHom (IsHomLift.codomain_eq X.p (𝟙 U) a.1).symm =
        eqToHom (Q.1.obj.fst.2.trans Q.2).symm :=
    eqToHom_eq_of_proofs_local _ _
  rw [hdom, hcod]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  exact eqToHom_comp_eqToHom_eqToHom_local (D := C) _ _ _

/-- Helper for Chap08 Lemma 8 8 4: a morphism in the right projected fibre lies over the
transported identity between the underlying total two-fibre-product bases. -/
private theorem twoFibreProduct_rightFiberHom_isHomLift
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    {U : C} (P Q : (twoFibreProduct f g).p.Fiber U)
    (b : ((FibredCategoryMor.fiberFunctor (twoFibreProductRightProjection f g) U).obj P) ⟶
      ((FibredCategoryMor.fiberFunctor (twoFibreProductRightProjection f g) U).obj Q)) :
    Z.p.IsHomLift (eqToHom P.2 ≫ (𝟙 U) ≫ eqToHom Q.2.symm) b.1 := by
  letI : Z.p.IsHomLift (𝟙 U) b.1 := b.2
  refine IsHomLift.of_fac' Z.p
    (eqToHom P.2 ≫ (𝟙 U) ≫ eqToHom Q.2.symm) b.1
    P.1.obj.snd.2 Q.1.obj.snd.2 ?_
  rw [IsHomLift.fac' Z.p (𝟙 U) b.1]
  have hdom :
      eqToHom (IsHomLift.domain_eq Z.p (𝟙 U) b.1) =
        eqToHom (P.1.obj.snd.2.trans P.2) :=
    eqToHom_eq_of_proofs_local _ _
  have hcod :
      eqToHom (IsHomLift.codomain_eq Z.p (𝟙 U) b.1).symm =
        eqToHom (Q.1.obj.snd.2.trans Q.2).symm :=
    eqToHom_eq_of_proofs_local _ _
  rw [hdom, hcod]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  exact eqToHom_comp_eqToHom_eqToHom_local (D := C) _ _ _

/-- Helper for Chap08 Lemma 8 8 4: the left component of a total composite in an explicit
two-fibre product is the composite of the left components. -/
private theorem twoFibreProductHom_comp_a
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    {P Q R : (twoFibreProduct f g).S}
    (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    (φ ≫ ψ).a = φ.a ≫ ψ.a := by
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the right component of a total composite in an explicit
two-fibre product is the composite of the right components. -/
private theorem twoFibreProductHom_comp_b
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    {P Q R : (twoFibreProduct f g).S}
    (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    (φ ≫ ψ).b = φ.b ≫ ψ.b := by
  rfl

/-- Helper for Chap08 Lemma 8 8 4: forgetting a composite in a fibre gives the composite of
the forgotten morphisms. -/
private theorem fiberHom_comp_underlying
    {D : Type uE} [Category.{vE} D] (p : D ⥤ C)
    {U : C} {P Q R : p.Fiber U}
    (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    (φ ≫ ψ).1 = φ.1 ≫ ψ.1 := by
  rfl

/-- Helper for Chap08 Lemma 8 8 4: an equality of fibre morphisms gives equality of the
underlying total-category morphisms. -/
private theorem fiberHom_eq_underlying
    {D : Type uE} [Category.{vE} D] (p : D ⥤ C)
    {U : C} {P Q : p.Fiber U} {φ ψ : P ⟶ Q} (h : φ = ψ) :
    φ.1 = ψ.1 := by
  cases h
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the underlying total-category map of a mapped fibre
morphism is the map under the total functor. -/
private theorem fibredMorphism_fiberFunctor_map_underlying
    {A B : FibredCategoryOver C} (H : FibredCategoryMor A B)
    {U : C} {P Q : A.p.Fiber U} (φ : P ⟶ Q) :
    ((FibredCategoryMor.fiberFunctor H U).map φ).1 =
      (FibredCategoryMor.toFunctor H).map φ.1 := by
  rfl

/-- Helper for Chap08 Lemma 8 8 4: functorial images of an isomorphism-conjugated morphism
cancel back to the middle morphism. -/
private theorem functor_map_iso_conjugate_cancel
    {A : Type uE} [Category.{vE} A] {B : Type t} [Category B] (F : A ⥤ B)
    {X₁ X₂ Y₁ Y₂ : A} (eX : X₁ ≅ X₂) (eY : Y₁ ≅ Y₂) (φ : X₁ ⟶ Y₁) :
    F.map eX.hom ≫ F.map (eX.inv ≫ φ ≫ eY.hom) ≫ F.map eY.inv =
      F.map φ := by
  calc
    F.map eX.hom ≫ F.map (eX.inv ≫ φ ≫ eY.hom) ≫ F.map eY.inv =
        F.map (eX.hom ≫ eX.inv ≫ φ ≫ eY.hom) ≫ F.map eY.inv := by
      simp only [Functor.map_comp, Category.assoc]
    _ = F.map (φ ≫ eY.hom) ≫ F.map eY.inv := by
      congr 1
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = F.map ((φ ≫ eY.hom) ≫ eY.inv) := by
      simp only [Functor.map_comp]
    _ = F.map φ := by
      congr 1
      simp only [Category.assoc, eY.hom_inv_id, Category.comp_id]

/-- Helper for Chap08 Lemma 8 8 4: cancel a morphism equality surrounded by isomorphism
comparison shells. -/
private theorem iso_shell_cancel
    {A : Type uE} [Category.{vE} A] {X₁ X₂ Y₁ Y₂ : A}
    (eX : X₁ ≅ X₂) (eY : Y₁ ≅ Y₂) {f g : X₂ ⟶ Y₂}
    (h : (eX.hom ≫ f) ≫ eY.inv = (eX.hom ≫ g) ≫ eY.inv) :
    f = g := by
  have h' := congrArg (fun m => eX.inv ≫ m ≫ eY.hom) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.id_comp, Category.comp_id] using h'

/-- Helper for Chap08 Lemma 8 8 4: the left component of a composite in a fibre of an
explicit two-fibre product is the composite of the left components. -/
private theorem twoFibreProductFiberHom_comp_a
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    {U : C} {P Q R : (twoFibreProduct f g).p.Fiber U}
    (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    (φ ≫ ψ).1.a = φ.1.a ≫ ψ.1.a := by
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the right component of a composite in a fibre of an
explicit two-fibre product is the composite of the right components. -/
private theorem twoFibreProductFiberHom_comp_b
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    {U : C} {P Q R : (twoFibreProduct f g).p.Fiber U}
    (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    (φ ≫ ψ).1.b = φ.1.b ≫ ψ.1.b := by
  rfl

/-- Helper for Chap08 Lemma 8 8 4: applying a fibred-category morphism to a reindexed
vertical morphism is the target reindexing of the mapped morphism, conjugated by the
pullback-comparison isomorphisms. -/
private theorem fibredMorphism_map_reindexed_hom
    {A B : FibredCategoryOver C} (H : FibredCategoryMor A B)
    [A.p.IsFibered] [B.p.IsFibered]
    {U V : C} (f : V ⟶ U) {P Q : A.p.Fiber U} (φ : P ⟶ Q) :
    (FibredCategoryMor.fiberFunctor H V).map
        (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ) =
      (FibredCategoryMor.pullbackComparison H f P).inv ≫
        (((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
          ((FibredCategoryMor.fiberFunctor H U).map φ)) ≫
        (FibredCategoryMor.pullbackComparison H f Q).hom := by
  let eP := FibredCategoryMor.pullbackComparison H f P
  let eQ := FibredCategoryMor.pullbackComparison H f Q
  let θ :=
    (FibredCategoryMor.fiberFunctor H V).map
      (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)
  let eta :=
    (((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
      ((FibredCategoryMor.fiberFunctor H U).map φ))
  have hnat : θ ≫ eQ.inv = eP.inv ≫ eta := by
    simpa only [θ, eta, eP, eQ] using
      FibredCategoryMor.pullbackComparison_inv_naturality_over_vertical H f φ
  have hpost : (θ ≫ eQ.inv) ≫ eQ.hom = (eP.inv ≫ eta) ≫ eQ.hom :=
    congrArg (fun k => k ≫ eQ.hom) hnat
  have hleft : (θ ≫ eQ.inv) ≫ eQ.hom = θ := by
    calc
      (θ ≫ eQ.inv) ≫ eQ.hom = θ ≫ (eQ.inv ≫ eQ.hom) := by
        exact Category.assoc θ eQ.inv eQ.hom
      _ = θ ≫ 𝟙 _ := by
        exact congrArg (fun k => θ ≫ k) eQ.inv_hom_id
      _ = θ := by
        rw [Category.comp_id]
  have hresult : θ = eP.inv ≫ eta ≫ eQ.hom :=
    hleft.symm.trans (hpost.trans (Category.assoc eP.inv eta eQ.hom))
  simpa only [θ, eta, eP, eQ] using hresult

/-- Helper for Chap08 Lemma 8 8 4: the left projection of a fibre morphism in an explicit
two-fibre product is its stored left component. -/
private theorem twoFibreProduct_leftProjection_map_underlying
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    {U : C} {P Q : (twoFibreProduct f g).p.Fiber U} (φ : P ⟶ Q) :
    ((FibredCategoryMor.fiberFunctor (twoFibreProductLeftProjection f g) U).map φ).1 =
      φ.1.a := by
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the right projection of a fibre morphism in an explicit
two-fibre product is its stored right component. -/
private theorem twoFibreProduct_rightProjection_map_underlying
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    {U : C} {P Q : (twoFibreProduct f g).p.Fiber U} (φ : P ⟶ Q) :
    ((FibredCategoryMor.fiberFunctor (twoFibreProductRightProjection f g) U).map φ).1 =
      φ.1.b := by
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the right projection of a fibre object in an explicit
two-fibre product is its stored right object. -/
private theorem twoFibreProduct_rightProjection_obj_underlying
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    {U : C} (P : (twoFibreProduct f g).p.Fiber U) :
    ((FibredCategoryMor.fiberFunctor (twoFibreProductRightProjection f g) U).obj P).1 =
      P.1.obj.snd.1 := by
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the left component of a reindexed explicit
two-fibre-product morphism is the reindexed left projection, conjugated by the left
pullback-comparison isomorphisms. -/
private theorem twoFibreProduct_reindex_left_component
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    [(twoFibreProduct f g).p.IsFibered]
    {U V : C} (h : V ⟶ U)
    {P Q : (twoFibreProduct f g).p.Fiber U} (φ : P ⟶ Q) :
    ((((canonicalFiberPseudofunctor (twoFibreProduct f g).p).map
          h.op.toLoc).toFunctor.map φ).1).a =
      ((FibredCategoryMor.pullbackComparison
          (twoFibreProductLeftProjection f g) h P).inv ≫
        (((canonicalFiberPseudofunctor X.p).map h.op.toLoc).toFunctor.map
          ((FibredCategoryMor.fiberFunctor
            (twoFibreProductLeftProjection f g) U).map φ)) ≫
        (FibredCategoryMor.pullbackComparison
          (twoFibreProductLeftProjection f g) h Q).hom).1 := by
  have hmap :=
    fibredMorphism_map_reindexed_hom
      (H := twoFibreProductLeftProjection f g) h φ
  simpa only [twoFibreProduct_leftProjection_map_underlying] using
    congrArg (fun ψ => ψ.1) hmap

/-- Helper for Chap08 Lemma 8 8 4: the right component of a reindexed explicit
two-fibre-product morphism is the reindexed right projection, conjugated by the right
pullback-comparison isomorphisms. -/
private theorem twoFibreProduct_reindex_right_component
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    [(twoFibreProduct f g).p.IsFibered]
    {U V : C} (h : V ⟶ U)
    {P Q : (twoFibreProduct f g).p.Fiber U} (φ : P ⟶ Q) :
    ((((canonicalFiberPseudofunctor (twoFibreProduct f g).p).map
          h.op.toLoc).toFunctor.map φ).1).b =
      ((FibredCategoryMor.pullbackComparison
          (twoFibreProductRightProjection f g) h P).inv ≫
        (((canonicalFiberPseudofunctor Z.p).map h.op.toLoc).toFunctor.map
          ((FibredCategoryMor.fiberFunctor
            (twoFibreProductRightProjection f g) U).map φ)) ≫
        (FibredCategoryMor.pullbackComparison
          (twoFibreProductRightProjection f g) h Q).hom).1 := by
  have hmap :=
    fibredMorphism_map_reindexed_hom
      (H := twoFibreProductRightProjection f g) h φ
  simpa only [twoFibreProduct_rightProjection_map_underlying] using
    congrArg (fun ψ => ψ.1) hmap

/-- Helper for Chap08 Lemma 8 8 4: the left component of a morphism in a fixed fibre of an
explicit two-fibre product lies over the identity of that fibre's base object. -/
private theorem twoFibreProduct_fiber_left_over_id
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    {U : C} {P Q : (twoFibreProduct f g).p.Fiber U}
    (φ : P ⟶ Q) :
    X.p.IsHomLift (𝟙 U) φ.1.a := by
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  letI : (twoFibreProduct f g).p.IsHomLift (𝟙 UP) φ.1 := φ.2
                  have hbase : φ.1.base = 𝟙 UP := by
                    simpa [FibredCategoryOver.twoFibreProduct] using
                      (IsHomLift.fac' ((twoFibreProduct f g).p) (𝟙 UP) φ.1)
                  simpa [hbase, FibredCategoryOver.twoFibreProduct] using φ.1.a_over

/-- Helper for Chap08 Lemma 8 8 4: the right component of a morphism in a fixed fibre of an
explicit two-fibre product lies over the identity of that fibre's base object. -/
private theorem twoFibreProduct_fiber_right_over_id
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    {U : C} {P Q : (twoFibreProduct f g).p.Fiber U}
    (φ : P ⟶ Q) :
    Z.p.IsHomLift (𝟙 U) φ.1.b := by
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  letI : (twoFibreProduct f g).p.IsHomLift (𝟙 UP) φ.1 := φ.2
                  have hbase : φ.1.base = 𝟙 UP := by
                    simpa [FibredCategoryOver.twoFibreProduct] using
                      (IsHomLift.fac' ((twoFibreProduct f g).p) (𝟙 UP) φ.1)
                  simpa [hbase, FibredCategoryOver.twoFibreProduct] using φ.1.b_over

/-- Helper for Chap08 Lemma 8 8 4: the stored comparison morphism of an object in a fixed
fibre of an explicit two-fibre product lies over the identity of that fibre's base object. -/
private theorem twoFibreProduct_fiber_comparison_over_id
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    {U : C} (P : (twoFibreProduct f g).p.Fiber U) :
    Y.p.IsHomLift (𝟙 U) P.1.comparison := by
  cases P with
  | mk P hP =>
      cases hP
      simpa [FibredCategoryOver.twoFibreProduct] using
        CategoryOver.ExplicitTwoFibreProductObject.comparison_over
          (FibredCategoryMor.toBasedFunctor f) (FibredCategoryMor.toBasedFunctor g) P

/-- Helper for Chap08 Lemma 8 8 4: the inverse of the stored comparison of an object in a fixed
fibre of an explicit two-fibre product lies over the identity of that fibre's base object. -/
private theorem twoFibreProduct_fiber_comparison_inv_over_id
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    {U : C} (P : (twoFibreProduct f g).p.Fiber U) :
    Y.p.IsHomLift (𝟙 U) P.1.obj.iso.inv.1 := by
  cases P with
  | mk P hP =>
      cases hP
      simpa [FibredCategoryOver.twoFibreProduct] using P.obj.iso.inv.2

/-- Helper for Chap08 Lemma 8 8 4: the stored comparison of a fibre object in an explicit
two-fibre product, packaged as an isomorphism in the target fibre. -/
private noncomputable def twoFibreProduct_fiber_comparisonIso
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    {U : C} (P : (twoFibreProduct f g).p.Fiber U) :
    ((FibredCategoryMor.fiberFunctor f U).obj
      ⟨P.1.obj.fst.1, by
        rw [P.1.obj.fst.2]
        simpa using P.2⟩) ≅
      ((FibredCategoryMor.fiberFunctor g U).obj
        ⟨P.1.obj.snd.1, by
          rw [P.1.obj.snd.2]
          simpa using P.2⟩) :=
  { hom := ⟨P.1.comparison, twoFibreProduct_fiber_comparison_over_id f g P⟩
    inv := ⟨P.1.obj.iso.inv.1, twoFibreProduct_fiber_comparison_inv_over_id f g P⟩
    hom_inv_id := by
      apply Functor.Fiber.hom_ext
      exact congrArg (fun φ => φ.1) P.1.obj.iso.hom_inv_id
    inv_hom_id := by
      apply Functor.Fiber.hom_ext
      exact congrArg (fun φ => φ.1) P.1.obj.iso.inv_hom_id }

/-- Helper for Chap08 Lemma 8 8 4: an isomorphism in a fibre of an explicit two-fibre product
conjugates the stored comparison morphism. -/
private theorem twoFibreProduct_comparison_conjugate_of_iso
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    {U : C} {P Q : (twoFibreProduct f g).p.Fiber U} (e : P ≅ Q) :
    (FibredCategoryMor.toFunctor f).map e.hom.1.a ≫ Q.1.comparison ≫
      (FibredCategoryMor.toFunctor g).map e.inv.1.b =
    P.1.comparison := by
  have hb : e.hom.1.b ≫ e.inv.1.b = 𝟙 _ := by
    exact congrArg (fun φ => φ.1.b) e.hom_inv_id
  calc
    (FibredCategoryMor.toFunctor f).map e.hom.1.a ≫ Q.1.comparison ≫
        (FibredCategoryMor.toFunctor g).map e.inv.1.b =
      (P.1.comparison ≫ (FibredCategoryMor.toFunctor g).map e.hom.1.b) ≫
        (FibredCategoryMor.toFunctor g).map e.inv.1.b := by
        simpa only [Category.assoc] using
          congrArg (fun k => k ≫ (FibredCategoryMor.toFunctor g).map e.inv.1.b)
            e.hom.1.comm.w
    _ =
      P.1.comparison ≫
        (FibredCategoryMor.toFunctor g).map (e.hom.1.b ≫ e.inv.1.b) := by
        simp only [Functor.map_comp, Category.assoc]
    _ = P.1.comparison := by
        rw [hb]
        simp only [Functor.map_id, Category.comp_id]

/-- Helper for Chap08 Lemma 8 8 4: restricting the stored comparison of an explicit
two-fibre-product object is the comparison of the restricted object, conjugated by the two
projection pullback-comparisons. -/
private theorem twoFibreProduct_comparison_reindex_boundary
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    [(twoFibreProduct f g).p.IsFibered]
    {U V : C} (q : V ⟶ U) (P : (twoFibreProduct f g).p.Fiber U) :
    let HL := twoFibreProductLeftProjection f g ≫ f
    let HR := twoFibreProductRightProjection f g ≫ g
    let qP := q ^*[canonicalPullbackChoice (twoFibreProduct f g).p] P
    let compP : (FibredCategoryMor.fiberFunctor HL U).obj P ⟶
        (FibredCategoryMor.fiberFunctor HR U).obj P :=
      ⟨P.1.comparison, twoFibreProduct_fiber_comparison_over_id f g P⟩
    let compqP : (FibredCategoryMor.fiberFunctor HL V).obj qP ⟶
        (FibredCategoryMor.fiberFunctor HR V).obj qP :=
      ⟨qP.1.comparison, twoFibreProduct_fiber_comparison_over_id f g qP⟩
    ((canonicalFiberPseudofunctor Y.p).map q.op.toLoc).toFunctor.map compP =
      (FibredCategoryMor.pullbackComparison HL q P).hom ≫
        compqP ≫
          (FibredCategoryMor.pullbackComparison HR q P).inv := by
  -- Compare both fiber morphisms after postcomposition with the right projected cartesian tail;
  -- the two postcomposites are the defining commutative square of the pulled explicit product.
  dsimp only
  let HL := twoFibreProductLeftProjection f g ≫ f
  let HR := twoFibreProductRightProjection f g ≫ g
  let qP := q ^*[canonicalPullbackChoice (twoFibreProduct f g).p] P
  let compP : (FibredCategoryMor.fiberFunctor HL U).obj P ⟶
      (FibredCategoryMor.fiberFunctor HR U).obj P :=
    ⟨P.1.comparison, twoFibreProduct_fiber_comparison_over_id f g P⟩
  let compqP : (FibredCategoryMor.fiberFunctor HL V).obj qP ⟶
      (FibredCategoryMor.fiberFunctor HR V).obj qP :=
    ⟨qP.1.comparison, twoFibreProduct_fiber_comparison_over_id f g qP⟩
  let α := ((canonicalFiberPseudofunctor Y.p).map q.op.toLoc).toFunctor.map compP
  let eR := FibredCategoryMor.pullbackComparison HR q P
  let eL := FibredCategoryMor.pullbackComparison HL q P
  let eta := (canonicalPullbackChoice (twoFibreProduct f g).p).map q P
  let tailR := HR.toHom.map eta
  have htail : Y.p.IsStronglyCartesian q tailR := by
    dsimp only [tailR, HR, eta]
    exact
      FibredCategoryMor.map_stronglyCartesian_of_lift
        (twoFibreProductRightProjection f g ≫ g) q _
        ((canonicalPullbackChoice (twoFibreProduct f g).p).isStronglyCartesian q P)
  have hleftLift :
      Y.p.IsHomLift (𝟙 V) (Functor.Fiber.fiberInclusion.map α ≫ eR.hom.1) := by
    exact (α ≫ eR.hom).2
  have hrightLift :
      Y.p.IsHomLift (𝟙 V) (eL.hom.1 ≫ Functor.Fiber.fiberInclusion.map compqP) := by
    exact (eL.hom ≫ compqP).2
  have hR :
      eR.hom.1 ≫ HR.toHom.map eta =
        (canonicalPullbackChoice Y.p).map q
          ((FibredCategoryMor.fiberFunctor HR U).obj P) := by
    simpa only [eR, eta, HR] using
      FibredCategoryMor.pullbackComparison_hom_postcompose HR q P
  have hL :
      eL.hom.1 ≫ HL.toHom.map eta =
        (canonicalPullbackChoice Y.p).map q
          ((FibredCategoryMor.fiberFunctor HL U).obj P) := by
    simpa only [eL, eta, HL] using
      FibredCategoryMor.pullbackComparison_hom_postcompose HL q P
  have hα :
      Functor.Fiber.fiberInclusion.map α ≫ (canonicalPullbackChoice Y.p).map q
          ((FibredCategoryMor.fiberFunctor HR U).obj P) =
        (canonicalPullbackChoice Y.p).map q
            ((FibredCategoryMor.fiberFunctor HL U).obj P) ≫
          Functor.Fiber.fiberInclusion.map compP := by
    simpa only [α, compP, HL, HR] using
      FibredCategoryMor.canonical_pullbackFunctor_map_fac
        (p := Y.p) (f := q) (φ := compP)
  have hη :
      HL.toHom.map eta ≫ Functor.Fiber.fiberInclusion.map compP =
        Functor.Fiber.fiberInclusion.map compqP ≫ HR.toHom.map eta := by
    simpa only [HL, HR, eta, compP, compqP] using eta.comm.w
  have hleft :
      (Functor.Fiber.fiberInclusion.map α ≫ eR.hom.1) ≫ HR.toHom.map eta =
        (canonicalPullbackChoice Y.p).map q
            ((FibredCategoryMor.fiberFunctor HL U).obj P) ≫
          Functor.Fiber.fiberInclusion.map compP := by
    exact
      (Category.assoc (Functor.Fiber.fiberInclusion.map α) eR.hom.1
        (HR.toHom.map eta)).trans
        ((congrArg (fun k ↦ Functor.Fiber.fiberInclusion.map α ≫ k) hR).trans hα)
  have hright :
      (eL.hom.1 ≫ Functor.Fiber.fiberInclusion.map compqP) ≫ HR.toHom.map eta =
        (canonicalPullbackChoice Y.p).map q
            ((FibredCategoryMor.fiberFunctor HL U).obj P) ≫
          Functor.Fiber.fiberInclusion.map compP := by
    exact
      (Category.assoc eL.hom.1 (Functor.Fiber.fiberInclusion.map compqP)
        (HR.toHom.map eta)).trans
        ((congrArg (fun k ↦ eL.hom.1 ≫ k) hη.symm).trans
          ((Category.assoc eL.hom.1 (HL.toHom.map eta)
            (Functor.Fiber.fiberInclusion.map compP)).symm.trans
            (congrArg (fun k ↦ k ≫ Functor.Fiber.fiberInclusion.map compP) hL)))
  have hboundary : α ≫ eR.hom = eL.hom ≫ compqP := by
    apply Functor.Fiber.hom_ext
    refine @Functor.IsStronglyCartesian.ext _ _ _ _ Y.p _ _ _ _
      q tailR htail _ _ (𝟙 V)
      (Functor.Fiber.fiberInclusion.map α ≫ eR.hom.1)
      (eL.hom.1 ≫ Functor.Fiber.fiberInclusion.map compqP)
      hleftLift hrightLift ?_
    rw [show tailR = HR.toHom.map eta by rfl]
    exact hleft.trans hright.symm
  change α = eL.hom ≫ compqP ≫ eR.inv
  exact ((Iso.eq_comp_inv eR).2 hboundary).trans (Category.assoc eL.hom compqP eR.inv)

/-- Helper for Chap08 Lemma 8 8 4: the app of a fibred morphism Hom-presheaf map is the
pullback-comparison conjugation shell. -/
private theorem fibredMorphismPresheafMap_app_pullbackComparison
    {A B : FibredCategoryOver C} (F : A ⟶ B)
    {U : C} (x y : A.p.Fiber U) (W : Over U)
    (δ : ((canonicalFiberPseudofunctor A.p).presheafHom x y).obj (Opposite.op W)) :
    (FibredCategoryMor.fibredMorphismPresheafMap F x y).app (Opposite.op W) δ =
      (FibredCategoryMor.pullbackComparison F W.hom x).hom ≫
        (FibredCategoryMor.fiberFunctor F W.left).map δ ≫
        (FibredCategoryMor.pullbackComparison F W.hom y).inv := by
  -- Unfold the public Hom-presheaf map once; the slice app is exactly the comparison-conjugated
  -- fiber morphism used in the source proof.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: two Hom-presheaf sections into an explicit two-fibre product
are equal once their left and right projection images are equal. -/
private theorem twoFibreProduct_presheafHom_ext
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    [(twoFibreProduct f g).p.IsFibered]
    {U : C} (P Q : (twoFibreProduct f g).p.Fiber U)
    (W : (Over U)ᵒᵖ)
    {φ ψ : ((canonicalFiberPseudofunctor
      (twoFibreProduct f g).p).presheafHom P Q).obj W}
    (hleft :
      (FibredCategoryMor.fibredMorphismPresheafMap
        (twoFibreProductLeftProjection f g) P Q).app W φ =
      (FibredCategoryMor.fibredMorphismPresheafMap
        (twoFibreProductLeftProjection f g) P Q).app W ψ)
    (hright :
      (FibredCategoryMor.fibredMorphismPresheafMap
        (twoFibreProductRightProjection f g) P Q).app W φ =
      (FibredCategoryMor.fibredMorphismPresheafMap
        (twoFibreProductRightProjection f g) P Q).app W ψ) :
    φ = ψ := by
  induction W using Opposite.rec
  rename_i W
  let L := twoFibreProductLeftProjection f g
  let R := twoFibreProductRightProjection f g
  let eLP := FibredCategoryMor.pullbackComparison L W.hom P
  let eLQ := FibredCategoryMor.pullbackComparison L W.hom Q
  let eRP := FibredCategoryMor.pullbackComparison R W.hom P
  let eRQ := FibredCategoryMor.pullbackComparison R W.hom Q
  have hleftMap :
      (FibredCategoryMor.fiberFunctor L W.left).map φ =
        (FibredCategoryMor.fiberFunctor L W.left).map ψ := by
    have hleftShell :
        ((eLP.hom ≫ (FibredCategoryMor.fiberFunctor L W.left).map φ) ≫ eLQ.inv) =
          ((eLP.hom ≫ (FibredCategoryMor.fiberFunctor L W.left).map ψ) ≫ eLQ.inv) := by
      simpa only [L, eLP, eLQ, Category.assoc] using
        (fibredMorphismPresheafMap_app_pullbackComparison L P Q W φ).symm.trans
          (hleft.trans (fibredMorphismPresheafMap_app_pullbackComparison L P Q W ψ))
    apply (cancel_epi eLP.hom).1
    apply (cancel_mono eLQ.inv).1
    simpa only [L, eLP, eLQ] using hleftShell
  have hrightMap :
      (FibredCategoryMor.fiberFunctor R W.left).map φ =
        (FibredCategoryMor.fiberFunctor R W.left).map ψ := by
    have hrightShell :
        ((eRP.hom ≫ (FibredCategoryMor.fiberFunctor R W.left).map φ) ≫ eRQ.inv) =
          ((eRP.hom ≫ (FibredCategoryMor.fiberFunctor R W.left).map ψ) ≫ eRQ.inv) := by
      simpa only [R, eRP, eRQ, Category.assoc] using
        (fibredMorphismPresheafMap_app_pullbackComparison R P Q W φ).symm.trans
          (hright.trans (fibredMorphismPresheafMap_app_pullbackComparison R P Q W ψ))
    apply (cancel_epi eRP.hom).1
    apply (cancel_mono eRQ.inv).1
    simpa only [R, eRP, eRQ] using hrightShell
  apply twoFibreProductFiberHom_ext_components f g
  · simpa only [L, twoFibreProduct_leftProjection_map_underlying] using
      congrArg (fun eta => eta.1) hleftMap
  · simpa only [R, twoFibreProduct_rightProjection_map_underlying] using
      congrArg (fun eta => eta.1) hrightMap

/-- Helper for Chap08 Lemma 8 8 4: package the component of a pseudofunctorial composition
comparison as an isomorphism between the direct and iterated chosen pullbacks. -/
private noncomputable def canonicalFiberPseudofunctor_mapCompAppIso
    {T : Type uE} [Category.{vE} T] (p : T ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc) (x : p.Fiber D) :
    (gf ^*[canonicalPullbackChoice p] x) ≅
      (g ^*[canonicalPullbackChoice p] (f ^*[canonicalPullbackChoice p] x)) where
  hom :=
    ((canonicalFiberPseudofunctor p).mapComp'
      f.op.toLoc g.op.toLoc gf.op.toLoc hgf).hom.toNatTrans.app x
  inv :=
    ((canonicalFiberPseudofunctor p).mapComp'
      f.op.toLoc g.op.toLoc gf.op.toLoc hgf).inv.toNatTrans.app x
  hom_inv_id :=
    Cat.Hom.hom_inv_id_toNatTrans_app
      ((canonicalFiberPseudofunctor p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc hgf) x
  inv_hom_id :=
    Cat.Hom.inv_hom_id_toNatTrans_app
      ((canonicalFiberPseudofunctor p).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc hgf) x

/-- Helper for Chap08 Lemma 8 8 4: restricting a comparison-conjugated image morphism along
one more base arrow is the comparison-conjugated image of the restricted source morphism. -/
private theorem stack_morphism_pullHom_conjugate_normalized
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered]
    {D V W : C} (x y : A.p.Fiber D)
    (a : V ⟶ D) (k : W ⟶ V) (b : W ⟶ D) (hk : k ≫ a = b)
    (δ :
      ((canonicalFiberPseudofunctor A.p).map a.op.toLoc).toFunctor.obj x ⟶
        ((canonicalFiberPseudofunctor A.p).map a.op.toLoc).toFunctor.obj y) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor B.p)
        ((FibredCategoryMor.pullbackComparison H a x).hom ≫
          (FibredCategoryMor.fiberFunctor H V).map δ ≫
          (FibredCategoryMor.pullbackComparison H a y).inv)
        k b b hk hk =
      (FibredCategoryMor.pullbackComparison H b x).hom ≫
        (FibredCategoryMor.fiberFunctor H W).map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := canonicalFiberPseudofunctor A.p) δ k b b hk hk) ≫
        (FibredCategoryMor.pullbackComparison H b y).inv := by
  let FBk := ((canonicalFiberPseudofunctor B.p).map k.op.toLoc).toFunctor
  let FAk := ((canonicalFiberPseudofunctor A.p).map k.op.toLoc).toFunctor
  let d := δ
  let e₁ := FibredCategoryMor.pullbackComparison H a x
  let e₂ := FibredCategoryMor.pullbackComparison H a y
  let eb₁ := FibredCategoryMor.pullbackComparison H b x
  let eb₂ := FibredCategoryMor.pullbackComparison H b y
  let ck₁ := FibredCategoryMor.pullbackComparison H k
    (((canonicalFiberPseudofunctor A.p).map a.op.toLoc).toFunctor.obj x)
  let ck₂ := FibredCategoryMor.pullbackComparison H k
    (((canonicalFiberPseudofunctor A.p).map a.op.toLoc).toFunctor.obj y)
  let leftTarget :=
    (((canonicalFiberPseudofunctor B.p).mapComp'
        a.op.toLoc k.op.toLoc b.op.toLoc
        (comp_toLoc_eq a k b hk)).hom.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor H D).obj x))
  let rightTarget :=
    (((canonicalFiberPseudofunctor B.p).mapComp'
        a.op.toLoc k.op.toLoc b.op.toLoc
        (comp_toLoc_eq a k b hk)).inv.toNatTrans.app
      ((FibredCategoryMor.fiberFunctor H D).obj y))
  let leftSource :=
    (((canonicalFiberPseudofunctor A.p).mapComp'
        a.op.toLoc k.op.toLoc b.op.toLoc
        (comp_toLoc_eq a k b hk)).hom.toNatTrans.app x)
  let rightSource :=
    (((canonicalFiberPseudofunctor A.p).mapComp'
        a.op.toLoc k.op.toLoc b.op.toLoc
        (comp_toLoc_eq a k b hk)).inv.toNatTrans.app y)
  have hunfolded :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor B.p)
          (e₁.hom ≫ (FibredCategoryMor.fiberFunctor H V).map d ≫ e₂.inv)
          k b b hk hk =
        leftTarget ≫ FBk.map (e₁.hom ≫ (FibredCategoryMor.fiberFunctor H V).map d ≫ e₂.inv) ≫
          rightTarget := by
    rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    rfl
  have hmap :
      FBk.map (e₁.hom ≫ (FibredCategoryMor.fiberFunctor H V).map d ≫ e₂.inv) =
        FBk.map e₁.hom ≫ FBk.map ((FibredCategoryMor.fiberFunctor H V).map d) ≫
          FBk.map e₂.inv := by
    simpa only [FBk, d, e₁, e₂] using
      functor_map_threefold_comp FBk e₁.hom ((FibredCategoryMor.fiberFunctor H V).map d) e₂.inv
  have hleft :
      leftTarget ≫ FBk.map e₁.hom =
        eb₁.hom ≫ (FibredCategoryMor.fiberFunctor H W).map leftSource ≫ ck₁.inv := by
    simpa only [FBk, e₁, eb₁, ck₁, leftTarget, leftSource] using
      stack_morphism_pullbackComparison_pullHom_left_boundary H a k b hk x
  have hmid :
      ck₁.inv ≫ FBk.map ((FibredCategoryMor.fiberFunctor H V).map d) =
        (FibredCategoryMor.fiberFunctor H W).map (FAk.map d) ≫ ck₂.inv := by
    simpa only [FBk, FAk, d, ck₁, ck₂] using
      (stack_morphism_pullbackComparison_inv_naturality_over_vertical (H := H) (f := k)
        (φ := d)).symm
  have hright :
      ck₂.inv ≫ FBk.map e₂.inv ≫ rightTarget =
        (FibredCategoryMor.fiberFunctor H W).map rightSource ≫ eb₂.inv := by
    simpa only [FBk, e₂, eb₂, ck₂, rightTarget, rightSource] using
      stack_morphism_pullbackComparison_pullHom_right_boundary H a k b hk y
  have hfold :
      (FibredCategoryMor.fiberFunctor H W).map leftSource ≫
          (FibredCategoryMor.fiberFunctor H W).map (FAk.map d) ≫
          (FibredCategoryMor.fiberFunctor H W).map rightSource =
        (FibredCategoryMor.fiberFunctor H W).map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := canonicalFiberPseudofunctor A.p) d k b b hk hk) := by
    change
      (FibredCategoryMor.fiberFunctor H W).map leftSource ≫
          (FibredCategoryMor.fiberFunctor H W).map (FAk.map d) ≫
          (FibredCategoryMor.fiberFunctor H W).map rightSource =
        (FibredCategoryMor.fiberFunctor H W).map
          (leftSource ≫ FAk.map d ≫ rightSource)
    rw [functor_map_threefold_comp]
  have hright' :
      eb₁.hom ≫ (FibredCategoryMor.fiberFunctor H W).map leftSource ≫
          (FibredCategoryMor.fiberFunctor H W).map (FAk.map d) ≫
        (ck₂.inv ≫ FBk.map e₂.inv ≫ rightTarget) =
      eb₁.hom ≫ (FibredCategoryMor.fiberFunctor H W).map leftSource ≫
          (FibredCategoryMor.fiberFunctor H W).map (FAk.map d) ≫
        ((FibredCategoryMor.fiberFunctor H W).map rightSource ≫ eb₂.inv) := by
    simpa only [Category.assoc] using
      congrArg
        (fun t ↦ eb₁.hom ≫ (FibredCategoryMor.fiberFunctor H W).map leftSource ≫
          (FibredCategoryMor.fiberFunctor H W).map (FAk.map d) ≫ t)
        hright
  have hmap' :
      leftTarget ≫ FBk.map (e₁.hom ≫ (FibredCategoryMor.fiberFunctor H V).map d ≫ e₂.inv) ≫
          rightTarget =
        leftTarget ≫ FBk.map e₁.hom ≫ FBk.map ((FibredCategoryMor.fiberFunctor H V).map d) ≫
          FBk.map e₂.inv ≫ rightTarget := by
    calc
      leftTarget ≫ FBk.map (e₁.hom ≫ (FibredCategoryMor.fiberFunctor H V).map d ≫ e₂.inv) ≫
          rightTarget =
        leftTarget ≫
          (FBk.map e₁.hom ≫ FBk.map ((FibredCategoryMor.fiberFunctor H V).map d) ≫
            FBk.map e₂.inv) ≫
          rightTarget := by
            exact congrArg (fun t ↦ leftTarget ≫ t ≫ rightTarget) hmap
      _ =
        leftTarget ≫ FBk.map e₁.hom ≫ FBk.map ((FibredCategoryMor.fiberFunctor H V).map d) ≫
          FBk.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
  have hleft' :
      leftTarget ≫ FBk.map e₁.hom ≫ FBk.map ((FibredCategoryMor.fiberFunctor H V).map d) ≫
          FBk.map e₂.inv ≫ rightTarget =
        eb₁.hom ≫ (FibredCategoryMor.fiberFunctor H W).map leftSource ≫ ck₁.inv ≫
          FBk.map ((FibredCategoryMor.fiberFunctor H V).map d) ≫ FBk.map e₂.inv ≫ rightTarget := by
    calc
      leftTarget ≫ FBk.map e₁.hom ≫ FBk.map ((FibredCategoryMor.fiberFunctor H V).map d) ≫
          FBk.map e₂.inv ≫ rightTarget =
        (leftTarget ≫ FBk.map e₁.hom) ≫ FBk.map ((FibredCategoryMor.fiberFunctor H V).map d) ≫
          FBk.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
      _ =
        (eb₁.hom ≫ (FibredCategoryMor.fiberFunctor H W).map leftSource ≫ ck₁.inv) ≫
          FBk.map ((FibredCategoryMor.fiberFunctor H V).map d) ≫ FBk.map e₂.inv ≫
          rightTarget := by
            exact congrArg
              (fun t ↦ t ≫ FBk.map ((FibredCategoryMor.fiberFunctor H V).map d) ≫
                FBk.map e₂.inv ≫ rightTarget)
              hleft
      _ =
        eb₁.hom ≫ (FibredCategoryMor.fiberFunctor H W).map leftSource ≫ ck₁.inv ≫
          FBk.map ((FibredCategoryMor.fiberFunctor H V).map d) ≫ FBk.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
  have hmid' :
      eb₁.hom ≫ (FibredCategoryMor.fiberFunctor H W).map leftSource ≫ ck₁.inv ≫
          FBk.map ((FibredCategoryMor.fiberFunctor H V).map d) ≫ FBk.map e₂.inv ≫ rightTarget =
        eb₁.hom ≫ (FibredCategoryMor.fiberFunctor H W).map leftSource ≫
          (FibredCategoryMor.fiberFunctor H W).map (FAk.map d) ≫
          ck₂.inv ≫ FBk.map e₂.inv ≫ rightTarget := by
    calc
      eb₁.hom ≫ (FibredCategoryMor.fiberFunctor H W).map leftSource ≫ ck₁.inv ≫
          FBk.map ((FibredCategoryMor.fiberFunctor H V).map d) ≫ FBk.map e₂.inv ≫ rightTarget =
        eb₁.hom ≫ (FibredCategoryMor.fiberFunctor H W).map leftSource ≫
          (ck₁.inv ≫ FBk.map ((FibredCategoryMor.fiberFunctor H V).map d)) ≫
          FBk.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
      _ =
        eb₁.hom ≫ (FibredCategoryMor.fiberFunctor H W).map leftSource ≫
          ((FibredCategoryMor.fiberFunctor H W).map (FAk.map d) ≫ ck₂.inv) ≫
          FBk.map e₂.inv ≫ rightTarget := by
            exact congrArg
              (fun t ↦ eb₁.hom ≫ (FibredCategoryMor.fiberFunctor H W).map leftSource ≫ t ≫
                FBk.map e₂.inv ≫ rightTarget)
              hmid
      _ =
        eb₁.hom ≫ (FibredCategoryMor.fiberFunctor H W).map leftSource ≫
          (FibredCategoryMor.fiberFunctor H W).map (FAk.map d) ≫
          ck₂.inv ≫ FBk.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
  have hsource_flat :
      eb₁.hom ≫ (FibredCategoryMor.fiberFunctor H W).map leftSource ≫
          (FibredCategoryMor.fiberFunctor H W).map (FAk.map d) ≫
          (FibredCategoryMor.fiberFunctor H W).map rightSource ≫ eb₂.inv =
        eb₁.hom ≫
          (FibredCategoryMor.fiberFunctor H W).map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              (F := canonicalFiberPseudofunctor A.p) d k b b hk hk) ≫
          eb₂.inv := by
    calc
      eb₁.hom ≫ (FibredCategoryMor.fiberFunctor H W).map leftSource ≫
          (FibredCategoryMor.fiberFunctor H W).map (FAk.map d) ≫
          (FibredCategoryMor.fiberFunctor H W).map rightSource ≫ eb₂.inv =
        eb₁.hom ≫
          ((FibredCategoryMor.fiberFunctor H W).map leftSource ≫
            (FibredCategoryMor.fiberFunctor H W).map (FAk.map d) ≫
            (FibredCategoryMor.fiberFunctor H W).map rightSource) ≫
          eb₂.inv := by
            simp only [Category.assoc]
      _ =
        eb₁.hom ≫
          (FibredCategoryMor.fiberFunctor H W).map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              (F := canonicalFiberPseudofunctor A.p) d k b b hk hk) ≫
          eb₂.inv := by
            exact congrArg (fun t ↦ eb₁.hom ≫ t ≫ eb₂.inv) hfold
  have hprefix :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor B.p)
          (e₁.hom ≫ (FibredCategoryMor.fiberFunctor H V).map d ≫ e₂.inv)
          k b b hk hk =
        eb₁.hom ≫ (FibredCategoryMor.fiberFunctor H W).map leftSource ≫
          (FibredCategoryMor.fiberFunctor H W).map (FAk.map d) ≫
          ck₂.inv ≫ FBk.map e₂.inv ≫ rightTarget := by
    exact hunfolded.trans (hmap'.trans (hleft'.trans hmid'))
  exact
    hprefix.trans
      (hright'.trans
        (hsource_flat.trans rfl))

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 4: restricting an identity-slice Hom section along `f` is the
pseudofunctorial pullback of the corresponding fiber morphism. -/
private theorem identitySlicePresheafHom_map_hom_clean
    {T : Type uE} [Category.{vE} T] (p : T ⥤ C) [p.IsFibered]
    {W Z : C} (g : Z ⟶ W)
    (M N : p.Fiber W)
    (φ : M ⟶ N) :
    ((canonicalFiberPseudofunctor p).presheafHom M N).map
        (Over.homMk g (by change g ≫ 𝟙 W = g; rw [Category.comp_id]) :
          Over.mk g ⟶ Over.mk (𝟙 W)).op
        ((canonicalFiberPseudofunctor p).presheafHomObjHomEquiv φ) =
      ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ := by
  rw [Pseudofunctor.presheafHom_map]
  dsimp only []
  rw [Pseudofunctor.presheafHomObjHomEquiv_apply]
  dsimp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  have hmid :
      ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op W))).hom.toNatTrans.app M ≫
          φ ≫
          ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op W))).inv.toNatTrans.app N =
        ((canonicalFiberPseudofunctor p).map (Over.mk (𝟙 W)).hom.op.toLoc).toFunctor.map φ := by
    rw [← (canonicalFiberPseudofunctor p).mapId'_eq_mapId (LocallyDiscrete.mk (op W)),
      ← Category.assoc,
      ← (canonicalFiberPseudofunctor p).mapId'_hom_naturality
        (𝟙 (LocallyDiscrete.mk (op W))) rfl φ,
      Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]
    rfl
  rw [hmid]
  rw [(canonicalFiberPseudofunctor p).mapComp'_naturality_2]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 4: the same identity-slice restriction in the raw
`Over.mk (f ≫ 𝟙 _)` normal form produced by equalizer sieves. -/
private theorem identitySlicePresheafHom_map_hom_raw
    {T : Type uE} [Category.{vE} T] (p : T ⥤ C) [p.IsFibered]
    {W Z : C} (g : Z ⟶ W)
    (M N : p.Fiber W)
    (φ : M ⟶ N) :
    ((canonicalFiberPseudofunctor p).presheafHom M N).map
        (Over.homMk g : Over.mk (g ≫ 𝟙 W) ⟶ Over.mk (𝟙 W)).op
        ((canonicalFiberPseudofunctor p).presheafHomObjHomEquiv φ) =
      ((canonicalFiberPseudofunctor p).map (g ≫ 𝟙 W).op.toLoc).toFunctor.map φ := by
  rw [Pseudofunctor.presheafHom_map]
  dsimp only []
  rw [Pseudofunctor.presheafHomObjHomEquiv_apply]
  dsimp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  have hmid :
      ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op W))).hom.toNatTrans.app M ≫
          φ ≫
          ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op W))).inv.toNatTrans.app N =
        ((canonicalFiberPseudofunctor p).map (Over.mk (𝟙 W)).hom.op.toLoc).toFunctor.map φ := by
    rw [← (canonicalFiberPseudofunctor p).mapId'_eq_mapId (LocallyDiscrete.mk (op W)),
      ← Category.assoc,
      ← (canonicalFiberPseudofunctor p).mapId'_hom_naturality
        (𝟙 (LocallyDiscrete.mk (op W))) rfl φ,
      Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]
    rfl
  rw [hmid]
  rw [(canonicalFiberPseudofunctor p).mapComp'_naturality_2]
  rfl

/-- Helper for Chap08 Lemma 8 8 4: a pullback-comparison conjugate is unchanged when the base
arrow is replaced by an equal arrow, up to the evident `eqToHom` casts. -/
private theorem pullbackComparison_conjugate_eqToHom_cast
    {S₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (G : S₀ ⟶ Y₁)
    {U V : C} {b b' : V ⟶ U} (hbb : b = b')
    (x y : S₀.p.Fiber U)
    (φ : ((FibredCategoryMor.fiberFunctor G U).obj x) ⟶
        ((FibredCategoryMor.fiberFunctor G U).obj y))
    (h₁ : ((FibredCategoryMor.fiberFunctor G V).obj
        (b' ^*[canonicalPullbackChoice S₀.p] x)) =
        ((FibredCategoryMor.fiberFunctor G V).obj
          (b ^*[canonicalPullbackChoice S₀.p] x)))
    (h₂ : ((FibredCategoryMor.fiberFunctor G V).obj
        (b ^*[canonicalPullbackChoice S₀.p] y)) =
        ((FibredCategoryMor.fiberFunctor G V).obj
          (b' ^*[canonicalPullbackChoice S₀.p] y))) :
    eqToHom h₁ ≫
        (FibredCategoryMor.pullbackComparison G b x).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map b.op.toLoc).toFunctor.map φ ≫
          (FibredCategoryMor.pullbackComparison G b y).hom ≫
        eqToHom h₂ =
      (FibredCategoryMor.pullbackComparison G b' x).inv ≫
        ((canonicalFiberPseudofunctor Y₁.p).map b'.op.toLoc).toFunctor.map φ ≫
        (FibredCategoryMor.pullbackComparison G b' y).hom := by
  subst hbb
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Helper for Chap08 Lemma 8 8 4: push an identity-slice cover down to a cover of the base
object. -/
private noncomputable def baseCoverOfIdentitySliceCover
    {U : C} (T : (J.over U).Cover (Over.mk (𝟙 U))) :
    J.Cover U :=
  ⟨Sieve.overEquiv (Over.mk (𝟙 U)) T.1, by
    have hT : T.1 ∈ (J.over U) (Over.mk (𝟙 U)) := T.2
    rwa [J.mem_over_iff] at hT⟩

/-- Helper for Chap08 Lemma 8 8 4: membership in the pushed-down base cover is membership of
the corresponding identity-slice arrow upstairs. -/
private theorem baseCoverOfIdentitySliceCover_arrow_mem
    {U : C} (T : (J.over U).Cover (Over.mk (𝟙 U)))
    (I : (baseCoverOfIdentitySliceCover (J := J) T).Arrow) :
    T.1 (Over.homMk I.f : Over.mk (I.f ≫ 𝟙 U) ⟶ Over.mk (𝟙 U)) := by
  exact (Sieve.overEquiv_iff (Y := Over.mk (𝟙 U)) T.1 I.f).1 I.hf

/-- Helper for Chap08 Lemma 8 8 4: push a cover of an arbitrary slice object down to a cover
of that object's source. -/
private noncomputable def baseCoverOfSliceCover
    {U : C} (T : Over U) (S : (J.over U).Cover T) :
    J.Cover T.left :=
  ⟨Sieve.overEquiv T S.1, by
    have hS : S.1 ∈ (J.over U) T := S.2
    rwa [J.mem_over_iff] at hS⟩

/-- Helper for Chap08 Lemma 8 8 4: membership in the pushed-down base cover is membership of
the corresponding slice arrow upstairs. -/
private theorem baseCoverOfSliceCover_arrow_mem
    {U : C} (T : Over U) (S : (J.over U).Cover T)
    (I : (baseCoverOfSliceCover (J := J) T S).Arrow) :
    S.1 (Over.homMk I.f : Over.mk (I.f ≫ T.hom) ⟶ T) := by
  exact (Sieve.overEquiv_iff (Y := T) S.1 I.f).1 I.hf

/-- Helper for Chap08 Lemma 8 8 4: the base cover associated to the identity-slice Hom-image
cover of a stackification. -/
private noncomputable abbrev stackificationHomImageBaseCover
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (j : FibredCategoryMor Y₀ Y₁)
    (hj : FibredCategoryMor.IsStackification j)
    {U : C} (x y : Y₀.p.Fiber U)
    [(J.over U).WEqualsLocallyBijective (Type v)]
    (β :
      ((canonicalFiberPseudofunctor Y₁.p).presheafHom
        ((FibredCategoryMor.fiberFunctor j U).obj x)
        ((FibredCategoryMor.fiberFunctor j U).obj y)).obj
          (Opposite.op (Over.mk (𝟙 U)))) :
    J.Cover U :=
  baseCoverOfIdentitySliceCover (J := J)
    (stackification_hom_image_cover (J := J) j hj (x := x) (y := y) β)

/-- Helper for Chap08 Lemma 8 8 4: over the base image cover, a target fiber morphism has a
source-side lift with the standard pullback-comparison formula. -/
private theorem stackificationHomImageBaseCover_lift_hom
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (j : FibredCategoryMor Y₀ Y₁)
    (hj : FibredCategoryMor.IsStackification j)
    {U : C} (x y : Y₀.p.Fiber U)
    [(J.over U).WEqualsLocallyBijective (Type v)]
    (d : ((FibredCategoryMor.fiberFunctor j U).obj x) ⟶
      ((FibredCategoryMor.fiberFunctor j U).obj y))
    (I : (stackificationHomImageBaseCover (J := J) j hj x y
      ((canonicalFiberPseudofunctor Y₁.p).presheafHomObjHomEquiv d)).Arrow) :
    ∃ γ : (I.f ^*[canonicalPullbackChoice Y₀.p] x) ⟶
        (I.f ^*[canonicalPullbackChoice Y₀.p] y),
      (FibredCategoryMor.fiberFunctor j I.Y).map γ =
        (FibredCategoryMor.pullbackComparison j I.f x).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map I.f.op.toLoc).toFunctor.map d ≫
          (FibredCategoryMor.pullbackComparison j I.f y).hom := by
  let β :
      ((canonicalFiberPseudofunctor Y₁.p).presheafHom
        ((FibredCategoryMor.fiberFunctor j U).obj x)
        ((FibredCategoryMor.fiberFunctor j U).obj y)).obj
          (Opposite.op (Over.mk (𝟙 U))) :=
    (canonicalFiberPseudofunctor Y₁.p).presheafHomObjHomEquiv d
  let Tslice : (J.over U).Cover (Over.mk (𝟙 U)) :=
    stackification_hom_image_cover (J := J) j hj (x := x) (y := y) β
  let Islice : Tslice.Arrow :=
    ⟨Over.mk (I.f ≫ 𝟙 U), Over.homMk I.f,
      baseCoverOfIdentitySliceCover_arrow_mem (J := J) Tslice I⟩
  obtain ⟨γRaw, hγRaw⟩ :=
    stackification_coverwise_hom_lift (J := J) j hj (x := x) (y := y) β Islice
  have hfeq : I.f ≫ 𝟙 U = I.f := Category.comp_id _
  have hxcast :
      (I.f ^*[canonicalPullbackChoice Y₀.p] x) =
        ((I.f ≫ 𝟙 U) ^*[canonicalPullbackChoice Y₀.p] x) := by
    rw [hfeq]
  have hycast :
      ((I.f ≫ 𝟙 U) ^*[canonicalPullbackChoice Y₀.p] y) =
        (I.f ^*[canonicalPullbackChoice Y₀.p] y) := by
    rw [hfeq]
  refine ⟨(eqToHom hxcast) ≫ γRaw ≫ (eqToHom hycast), ?_⟩
  · have hγRawApp :
        (FibredCategoryMor.pullbackComparison j (I.f ≫ 𝟙 U) x).hom ≫
            (FibredCategoryMor.fiberFunctor j I.Y).map γRaw ≫
            (FibredCategoryMor.pullbackComparison j (I.f ≫ 𝟙 U) y).inv =
          (((canonicalFiberPseudofunctor Y₁.p).presheafHom
              ((FibredCategoryMor.fiberFunctor j U).obj x)
              ((FibredCategoryMor.fiberFunctor j U).obj y)).map Islice.f.op) β := by
      rw [← hγRaw]
      rfl
    rw [identitySlicePresheafHom_map_hom_raw] at hγRawApp
    have hγRawMap :
        (FibredCategoryMor.fiberFunctor j I.Y).map γRaw =
          (FibredCategoryMor.pullbackComparison j (I.f ≫ 𝟙 U) x).inv ≫
            ((canonicalFiberPseudofunctor Y₁.p).map (I.f ≫ 𝟙 U).op.toLoc).toFunctor.map d ≫
            (FibredCategoryMor.pullbackComparison j (I.f ≫ 𝟙 U) y).hom := by
      have h1 :=
        (Iso.eq_inv_comp (FibredCategoryMor.pullbackComparison j (I.f ≫ 𝟙 U) x)).2
          hγRawApp
      have h2 :=
        (Iso.comp_inv_eq (FibredCategoryMor.pullbackComparison j (I.f ≫ 𝟙 U) y)).1 h1
      rw [Category.assoc] at h2
      exact h2
    rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
    erw [hγRawMap]
    let e₁ := eqToHom (congrArg (FibredCategoryMor.fiberFunctor j I.Y).obj hxcast)
    let a := (FibredCategoryMor.pullbackComparison j (I.f ≫ 𝟙 U) x).inv
    let b := ((canonicalFiberPseudofunctor Y₁.p).map
      (I.f ≫ 𝟙 U).op.toLoc).toFunctor.map d
    let c := (FibredCategoryMor.pullbackComparison j (I.f ≫ 𝟙 U) y).hom
    let e₂ := eqToHom (congrArg (FibredCategoryMor.fiberFunctor j I.Y).obj hycast)
    have hcast : e₁ ≫ a ≫ b ≫ c ≫ e₂ =
        (FibredCategoryMor.pullbackComparison j I.f x).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map I.f.op.toLoc).toFunctor.map d ≫
          (FibredCategoryMor.pullbackComparison j I.f y).hom := by
      simpa only [e₁, a, b, c, e₂, Functor.map_comp, Category.assoc] using
        pullbackComparison_conjugate_eqToHom_cast (J := J) j hfeq x y d
          (congrArg (FibredCategoryMor.fiberFunctor j I.Y).obj hxcast)
          (congrArg (FibredCategoryMor.fiberFunctor j I.Y).obj hycast)
    change e₁ ≫ ((a ≫ b ≫ c) ≫ e₂) =
        (FibredCategoryMor.pullbackComparison j I.f x).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map I.f.op.toLoc).toFunctor.map d ≫
          (FibredCategoryMor.pullbackComparison j I.f y).hom
    calc
      e₁ ≫ ((a ≫ b ≫ c) ≫ e₂) = e₁ ≫ a ≫ b ≫ c ≫ e₂ := by
        simp only [Category.assoc]
      _ = _ := hcast

/-- Helper for Chap08 Lemma 8 8 4: the base cover on which two source-side homs with the same
`j`-image become equal. -/
private noncomputable def stackificationHomEqualizerBaseCover
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (j : FibredCategoryMor Y₀ Y₁)
    (hj : FibredCategoryMor.IsStackification j)
    {U : C} {x y : Y₀.p.Fiber U}
    (α β : x ⟶ y)
    (hαβ : (FibredCategoryMor.fiberFunctor j U).map α =
      (FibredCategoryMor.fiberFunctor j U).map β) :
    J.Cover U :=
  let θ := FibredCategoryMor.fibredMorphismPresheafMap j x y
  let βα :
      ((canonicalFiberPseudofunctor Y₀.p).presheafHom x y).obj
        (Opposite.op (Over.mk (𝟙 U))) :=
    (canonicalFiberPseudofunctor Y₀.p).presheafHomObjHomEquiv α
  let ββ :
      ((canonicalFiberPseudofunctor Y₀.p).presheafHom x y).obj
        (Opposite.op (Over.mk (𝟙 U))) :=
    (canonicalFiberPseudofunctor Y₀.p).presheafHomObjHomEquiv β
  let T : (J.over U).Cover (Over.mk (𝟙 U)) :=
    ⟨Presheaf.equalizerSieve
        (F := (canonicalFiberPseudofunctor Y₀.p).presheafHom x y) βα ββ,
      by
        haveI : (J.over U).WEqualsLocallyBijective (Type v) :=
          over_WEqualsLocallyBijective_small (J := J) U
        haveI : Presheaf.IsLocallyInjective (J.over U) θ :=
          (hj.morphismPresheafMap_W U x y : (J.over U).W θ).isLocallyInjective
        have hβ :
            θ.app (Opposite.op (Over.mk (𝟙 U))) βα =
              θ.app (Opposite.op (Over.mk (𝟙 U))) ββ := by
          rw [fibredMorphismPresheafMap_app_id_local j x y α]
          rw [fibredMorphismPresheafMap_app_id_local j x y β]
          exact congrArg
            (canonicalFiberPseudofunctor Y₁.p).presheafHomObjHomEquiv hαβ
        simpa using
          Presheaf.equalizerSieve_mem (J.over U) θ βα ββ hβ⟩
  baseCoverOfIdentitySliceCover (J := J) T

/-- Helper for Chap08 Lemma 8 8 4: membership in the Hom-equalizer base cover gives equality of
the reindexed source morphisms. -/
private theorem stackificationHomEqualizerBaseCover_eq
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (j : FibredCategoryMor Y₀ Y₁)
    (hj : FibredCategoryMor.IsStackification j)
    {U : C} {x y : Y₀.p.Fiber U}
    (α β : x ⟶ y)
    (hαβ : (FibredCategoryMor.fiberFunctor j U).map α =
      (FibredCategoryMor.fiberFunctor j U).map β)
    (I : (stackificationHomEqualizerBaseCover (J := J) j hj α β hαβ).Arrow) :
    ((canonicalFiberPseudofunctor Y₀.p).map (I.f ≫ 𝟙 U).op.toLoc).toFunctor.map α =
      ((canonicalFiberPseudofunctor Y₀.p).map (I.f ≫ 𝟙 U).op.toLoc).toFunctor.map β := by
  let θ := FibredCategoryMor.fibredMorphismPresheafMap j x y
  let βα :
      ((canonicalFiberPseudofunctor Y₀.p).presheafHom x y).obj
        (Opposite.op (Over.mk (𝟙 U))) :=
    (canonicalFiberPseudofunctor Y₀.p).presheafHomObjHomEquiv α
  let ββ :
      ((canonicalFiberPseudofunctor Y₀.p).presheafHom x y).obj
        (Opposite.op (Over.mk (𝟙 U))) :=
    (canonicalFiberPseudofunctor Y₀.p).presheafHomObjHomEquiv β
  let T : (J.over U).Cover (Over.mk (𝟙 U)) :=
    ⟨Presheaf.equalizerSieve
        (F := (canonicalFiberPseudofunctor Y₀.p).presheafHom x y) βα ββ,
      by
        haveI : (J.over U).WEqualsLocallyBijective (Type v) :=
          over_WEqualsLocallyBijective_small (J := J) U
        haveI : Presheaf.IsLocallyInjective (J.over U) θ :=
          (hj.morphismPresheafMap_W U x y : (J.over U).W θ).isLocallyInjective
        have hβ :
            θ.app (Opposite.op (Over.mk (𝟙 U))) βα =
              θ.app (Opposite.op (Over.mk (𝟙 U))) ββ := by
          rw [fibredMorphismPresheafMap_app_id_local j x y α]
          rw [fibredMorphismPresheafMap_app_id_local j x y β]
          exact congrArg
            (canonicalFiberPseudofunctor Y₁.p).presheafHomObjHomEquiv hαβ
        simpa using
          Presheaf.equalizerSieve_mem (J.over U) θ βα ββ hβ⟩
  have hI : T.1 (Over.homMk I.f : Over.mk (I.f ≫ 𝟙 U) ⟶ Over.mk (𝟙 U)) := by
    simpa [stackificationHomEqualizerBaseCover, T, θ, βα, ββ] using
      baseCoverOfIdentitySliceCover_arrow_mem (J := J) T I
  dsimp [T, Presheaf.equalizerSieve, βα, ββ] at hI
  exact
    (identitySlicePresheafHom_map_hom_raw (p := Y₀.p) (g := I.f)
      (M := x) (N := y) (φ := α)).symm.trans
      (hI.trans
        (identitySlicePresheafHom_map_hom_raw (p := Y₀.p) (g := I.f)
          (M := x) (N := y) (φ := β)))

/-- Helper for Chap08 Lemma 8 8 4: if local lifts of an isomorphism and its inverse have the
standard stackification image, then the composite lift maps to the identity. -/
private theorem stackification_lifted_hom_inv_image_id
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (j : FibredCategoryMor Y₀ Y₁)
    {U V : C} (q : V ⟶ U) (x y : Y₀.p.Fiber U)
    (d : ((FibredCategoryMor.fiberFunctor j U).obj x) ≅
      ((FibredCategoryMor.fiberFunctor j U).obj y))
    (γ : (q ^*[canonicalPullbackChoice Y₀.p] x) ⟶
        (q ^*[canonicalPullbackChoice Y₀.p] y))
    (δ : (q ^*[canonicalPullbackChoice Y₀.p] y) ⟶
        (q ^*[canonicalPullbackChoice Y₀.p] x))
    (hγ : (FibredCategoryMor.fiberFunctor j V).map γ =
        (FibredCategoryMor.pullbackComparison j q x).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map q.op.toLoc).toFunctor.map d.hom ≫
          (FibredCategoryMor.pullbackComparison j q y).hom)
    (hδ : (FibredCategoryMor.fiberFunctor j V).map δ =
        (FibredCategoryMor.pullbackComparison j q y).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map q.op.toLoc).toFunctor.map d.inv ≫
          (FibredCategoryMor.pullbackComparison j q x).hom) :
    (FibredCategoryMor.fiberFunctor j V).map (γ ≫ δ) =
      𝟙 ((FibredCategoryMor.fiberFunctor j V).obj
        (q ^*[canonicalPullbackChoice Y₀.p] x)) := by
  let eX := FibredCategoryMor.pullbackComparison j q x
  let eY := FibredCategoryMor.pullbackComparison j q y
  let M := ((canonicalFiberPseudofunctor Y₁.p).map q.op.toLoc).toFunctor
  rw [Functor.map_comp, hγ, hδ]
  change (eX.inv ≫ M.map d.hom ≫ eY.hom) ≫ eY.inv ≫ M.map d.inv ≫ eX.hom = 𝟙 _
  calc
    (eX.inv ≫ M.map d.hom ≫ eY.hom) ≫ eY.inv ≫ M.map d.inv ≫ eX.hom =
        eX.inv ≫ M.map d.hom ≫ (eY.hom ≫ eY.inv) ≫ M.map d.inv ≫ eX.hom := by
          simp only [Category.assoc]
    _ = eX.inv ≫ M.map d.hom ≫ 𝟙 _ ≫ M.map d.inv ≫ eX.hom := by
          exact congrArg
            (fun t => eX.inv ≫ M.map d.hom ≫ t ≫ M.map d.inv ≫ eX.hom)
            eY.hom_inv_id
    _ = eX.inv ≫ M.map d.hom ≫ M.map d.inv ≫ eX.hom := by
          simp only [Category.assoc, Category.id_comp, Category.comp_id]
    _ = eX.inv ≫ (M.map d.hom ≫ M.map d.inv) ≫ eX.hom := by
          rw [Category.assoc]
    _ = eX.inv ≫ M.map (d.hom ≫ d.inv) ≫ eX.hom := by
          exact congrArg (fun t => eX.inv ≫ t ≫ eX.hom)
            (Functor.map_comp M d.hom d.inv).symm
    _ = eX.inv ≫ M.map (𝟙 _) ≫ eX.hom := by
          exact congrArg (fun t => eX.inv ≫ M.map t ≫ eX.hom) d.hom_inv_id
    _ = eX.inv ≫ 𝟙 _ ≫ eX.hom := by
          exact congrArg (fun t => eX.inv ≫ t ≫ eX.hom) (Functor.map_id M _)
    _ = eX.inv ≫ eX.hom := by
          exact congrArg (fun t => eX.inv ≫ t) (Category.id_comp eX.hom)
    _ = 𝟙 _ := eX.inv_hom_id

/-- Helper for Chap08 Lemma 8 8 4: if local lifts of an isomorphism and its inverse have the
standard stackification image, then the reverse composite lift maps to the identity. -/
private theorem stackification_lifted_inv_hom_image_id
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (j : FibredCategoryMor Y₀ Y₁)
    {U V : C} (q : V ⟶ U) (x y : Y₀.p.Fiber U)
    (d : ((FibredCategoryMor.fiberFunctor j U).obj x) ≅
      ((FibredCategoryMor.fiberFunctor j U).obj y))
    (γ : (q ^*[canonicalPullbackChoice Y₀.p] x) ⟶
        (q ^*[canonicalPullbackChoice Y₀.p] y))
    (δ : (q ^*[canonicalPullbackChoice Y₀.p] y) ⟶
        (q ^*[canonicalPullbackChoice Y₀.p] x))
    (hγ : (FibredCategoryMor.fiberFunctor j V).map γ =
        (FibredCategoryMor.pullbackComparison j q x).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map q.op.toLoc).toFunctor.map d.hom ≫
          (FibredCategoryMor.pullbackComparison j q y).hom)
    (hδ : (FibredCategoryMor.fiberFunctor j V).map δ =
        (FibredCategoryMor.pullbackComparison j q y).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map q.op.toLoc).toFunctor.map d.inv ≫
          (FibredCategoryMor.pullbackComparison j q x).hom) :
    (FibredCategoryMor.fiberFunctor j V).map (δ ≫ γ) =
      𝟙 ((FibredCategoryMor.fiberFunctor j V).obj
        (q ^*[canonicalPullbackChoice Y₀.p] y)) := by
  let eX := FibredCategoryMor.pullbackComparison j q x
  let eY := FibredCategoryMor.pullbackComparison j q y
  let M := ((canonicalFiberPseudofunctor Y₁.p).map q.op.toLoc).toFunctor
  rw [Functor.map_comp, hδ, hγ]
  change (eY.inv ≫ M.map d.inv ≫ eX.hom) ≫ eX.inv ≫ M.map d.hom ≫ eY.hom = 𝟙 _
  calc
    (eY.inv ≫ M.map d.inv ≫ eX.hom) ≫ eX.inv ≫ M.map d.hom ≫ eY.hom =
        eY.inv ≫ M.map d.inv ≫ (eX.hom ≫ eX.inv) ≫ M.map d.hom ≫ eY.hom := by
          simp only [Category.assoc]
    _ = eY.inv ≫ M.map d.inv ≫ 𝟙 _ ≫ M.map d.hom ≫ eY.hom := by
          exact congrArg
            (fun t => eY.inv ≫ M.map d.inv ≫ t ≫ M.map d.hom ≫ eY.hom)
            eX.hom_inv_id
    _ = eY.inv ≫ M.map d.inv ≫ M.map d.hom ≫ eY.hom := by
          simp only [Category.assoc, Category.id_comp, Category.comp_id]
    _ = eY.inv ≫ (M.map d.inv ≫ M.map d.hom) ≫ eY.hom := by
          rw [Category.assoc]
    _ = eY.inv ≫ M.map (d.inv ≫ d.hom) ≫ eY.hom := by
          exact congrArg (fun t => eY.inv ≫ t ≫ eY.hom)
            (Functor.map_comp M d.inv d.hom).symm
    _ = eY.inv ≫ M.map (𝟙 _) ≫ eY.hom := by
          exact congrArg (fun t => eY.inv ≫ M.map t ≫ eY.hom) d.inv_hom_id
    _ = eY.inv ≫ 𝟙 _ ≫ eY.hom := by
          exact congrArg (fun t => eY.inv ≫ t ≫ eY.hom) (Functor.map_id M _)
    _ = eY.inv ≫ eY.hom := by
          exact congrArg (fun t => eY.inv ≫ t) (Category.id_comp eY.hom)
    _ = 𝟙 _ := eY.inv_hom_id

/-- Helper for Chap08 Lemma 8 8 4: a local source-side lift of a target Hom remains in the
standard stackification image form after one more restriction, once the iterated chosen pullback
is compared with the direct chosen pullback along the composite base map. -/
private theorem stackification_lifted_hom_reindex_direct_image
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (j : FibredCategoryMor Y₀ Y₁)
    {U V W : C} (q : V ⟶ U) (r : W ⟶ V) (b : W ⟶ U) (hb : r ≫ q = b)
    (x y : Y₀.p.Fiber U)
    (φ : ((FibredCategoryMor.fiberFunctor j U).obj x) ⟶
      ((FibredCategoryMor.fiberFunctor j U).obj y))
    (γ : (q ^*[canonicalPullbackChoice Y₀.p] x) ⟶
        (q ^*[canonicalPullbackChoice Y₀.p] y))
    (hγ : (FibredCategoryMor.fiberFunctor j V).map γ =
        (FibredCategoryMor.pullbackComparison j q x).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map q.op.toLoc).toFunctor.map φ ≫
          (FibredCategoryMor.pullbackComparison j q y).hom) :
    let κx := canonicalFiberPseudofunctor_mapCompAppIso Y₀.p q r b
      (comp_toLoc_eq q r b hb) x
    let κy := canonicalFiberPseudofunctor_mapCompAppIso Y₀.p q r b
      (comp_toLoc_eq q r b hb) y
    (FibredCategoryMor.fiberFunctor j W).map
        (κx.hom ≫
          ((canonicalFiberPseudofunctor Y₀.p).map r.op.toLoc).toFunctor.map γ ≫
          κy.inv) =
      (FibredCategoryMor.pullbackComparison j b x).inv ≫
        ((canonicalFiberPseudofunctor Y₁.p).map b.op.toLoc).toFunctor.map φ ≫
        (FibredCategoryMor.pullbackComparison j b y).hom := by
  dsimp only
  let κx := canonicalFiberPseudofunctor_mapCompAppIso Y₀.p q r b
    (comp_toLoc_eq q r b hb) x
  let κy := canonicalFiberPseudofunctor_mapCompAppIso Y₀.p q r b
    (comp_toLoc_eq q r b hb) y
  let A :=
    (canonicalFiberPseudofunctor Y₁.p).mapComp' q.op.toLoc r.op.toLoc b.op.toLoc
      (comp_toLoc_eq q r b hb)
  let Mq := ((canonicalFiberPseudofunctor Y₁.p).map q.op.toLoc).toFunctor
  let Mr := ((canonicalFiberPseudofunctor Y₁.p).map r.op.toLoc).toFunctor
  let Mb := ((canonicalFiberPseudofunctor Y₁.p).map b.op.toLoc).toFunctor
  let jqx := (FibredCategoryMor.pullbackComparison j q x)
  let jqy := (FibredCategoryMor.pullbackComparison j q y)
  let jrx := (FibredCategoryMor.pullbackComparison j r
    (q ^*[canonicalPullbackChoice Y₀.p] x))
  let jry := (FibredCategoryMor.pullbackComparison j r
    (q ^*[canonicalPullbackChoice Y₀.p] y))
  let jbx := (FibredCategoryMor.pullbackComparison j b x)
  let jby := (FibredCategoryMor.pullbackComparison j b y)
  let ψ :=
    κx.hom ≫
      ((canonicalFiberPseudofunctor Y₀.p).map r.op.toLoc).toFunctor.map γ ≫
        κy.inv
  have hnat :
      A.hom.toNatTrans.app ((FibredCategoryMor.fiberFunctor j U).obj x) ≫
          Mr.map (Mq.map φ) ≫
          A.inv.toNatTrans.app ((FibredCategoryMor.fiberFunctor j U).obj y) =
        Mb.map φ := by
    exact (canonicalFiberPseudofunctor Y₁.p).mapComp'_naturality_2
      q.op.toLoc r.op.toLoc b.op.toLoc (comp_toLoc_eq q r b hb) φ
  let targetγ :=
    jqx.hom ≫ (FibredCategoryMor.fiberFunctor j V).map γ ≫ jqy.inv
  have htargetγ : targetγ = Mq.map φ := by
    dsimp only [targetγ]
    rw [hγ]
    calc
      jqx.hom ≫ (jqx.inv ≫ Mq.map φ ≫ jqy.hom) ≫ jqy.inv =
          (jqx.hom ≫ jqx.inv) ≫ Mq.map φ ≫ jqy.hom ≫ jqy.inv := by
        simp only [Category.assoc]
      _ = Mq.map φ := by
        rw [jqx.hom_inv_id]
        simpa only [Category.id_comp] using
          (Category.assoc (Mq.map φ) jqy.hom jqy.inv).symm.trans
            ((Iso.comp_inv_eq jqy).2 rfl)
  have hconj :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor Y₁.p)
          targetγ r b b hb hb =
        jbx.hom ≫ (FibredCategoryMor.fiberFunctor j W).map ψ ≫ jby.inv := by
    simpa only [targetγ, ψ, jqx, jqy, jbx, jby, κx, κy,
      canonicalFiberPseudofunctor_mapCompAppIso,
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom] using
      stack_morphism_pullHom_conjugate_normalized (H := j) x y q r b hb γ
  have hpull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor Y₁.p)
          targetγ r b b hb hb =
        Mb.map φ := by
    rw [htargetγ]
    simpa only [A, Mq, Mr, Mb,
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom] using hnat
  have hwrapped :
      jbx.hom ≫ (FibredCategoryMor.fiberFunctor j W).map ψ ≫ jby.inv =
        Mb.map φ :=
    hconj.symm.trans hpull
  change (FibredCategoryMor.fiberFunctor j W).map ψ =
    jbx.inv ≫ Mb.map φ ≫ jby.hom
  rw [← hwrapped]
  calc
    (FibredCategoryMor.fiberFunctor j W).map ψ =
        𝟙 _ ≫ (FibredCategoryMor.fiberFunctor j W).map ψ ≫ 𝟙 _ := by
      simp only [Category.id_comp, Category.comp_id]
    _ = (jbx.inv ≫ jbx.hom) ≫ (FibredCategoryMor.fiberFunctor j W).map ψ ≫
          (jby.inv ≫ jby.hom) := by
      rw [jbx.inv_hom_id, jby.inv_hom_id]
    _ = jbx.inv ≫
          (jbx.hom ≫ (FibredCategoryMor.fiberFunctor j W).map ψ ≫ jby.inv) ≫
          jby.hom := by
      simp only [Category.assoc]

/-- Helper for Chap08 Lemma 8 8 4: after one more restriction, the reindexed lifts of an
isomorphism and its inverse still compose to the identity if their unreindexed composite has
become locally equal to the identity. -/
private theorem stackification_lifted_hom_inv_reindex_eq_id
    {Y₀ : FibredCategoryOver C}
    {U V W : C} (q : V ⟶ U) (r : W ⟶ V) (b : W ⟶ U) (hb : r ≫ q = b)
    (x y : Y₀.p.Fiber U)
    (γ : (q ^*[canonicalPullbackChoice Y₀.p] x) ⟶
      (q ^*[canonicalPullbackChoice Y₀.p] y))
    (δ : (q ^*[canonicalPullbackChoice Y₀.p] y) ⟶
      (q ^*[canonicalPullbackChoice Y₀.p] x))
    (hEq :
      ((canonicalFiberPseudofunctor Y₀.p).map r.op.toLoc).toFunctor.map (γ ≫ δ) =
        ((canonicalFiberPseudofunctor Y₀.p).map r.op.toLoc).toFunctor.map
          (𝟙 (q ^*[canonicalPullbackChoice Y₀.p] x))) :
    let κx := canonicalFiberPseudofunctor_mapCompAppIso Y₀.p q r b
      (comp_toLoc_eq q r b hb) x
    let κy := canonicalFiberPseudofunctor_mapCompAppIso Y₀.p q r b
      (comp_toLoc_eq q r b hb) y
    let M := ((canonicalFiberPseudofunctor Y₀.p).map r.op.toLoc).toFunctor
    (κx.hom ≫ M.map γ ≫ κy.inv) ≫
        (κy.hom ≫ M.map δ ≫ κx.inv) =
      𝟙 (b ^*[canonicalPullbackChoice Y₀.p] x) := by
  dsimp only
  let κx := canonicalFiberPseudofunctor_mapCompAppIso Y₀.p q r b
    (comp_toLoc_eq q r b hb) x
  let κy := canonicalFiberPseudofunctor_mapCompAppIso Y₀.p q r b
    (comp_toLoc_eq q r b hb) y
  let M := ((canonicalFiberPseudofunctor Y₀.p).map r.op.toLoc).toFunctor
  calc
    (κx.hom ≫ M.map γ ≫ κy.inv) ≫ (κy.hom ≫ M.map δ ≫ κx.inv) =
        κx.hom ≫ M.map γ ≫ (κy.inv ≫ κy.hom) ≫ M.map δ ≫ κx.inv := by
      simp only [Category.assoc]
    _ = κx.hom ≫ M.map γ ≫ 𝟙 _ ≫ M.map δ ≫ κx.inv := by
      exact congrArg
        (fun t => κx.hom ≫ M.map γ ≫ t ≫ M.map δ ≫ κx.inv)
        κy.inv_hom_id
    _ = κx.hom ≫ M.map γ ≫ M.map δ ≫ κx.inv := by
      simp only [Category.id_comp]
    _ = κx.hom ≫ M.map (γ ≫ δ) ≫ κx.inv := by
      exact
        (congrArg (fun t => κx.hom ≫ t)
          (Category.assoc (M.map γ) (M.map δ) κx.inv).symm).trans
          (congrArg (fun t => κx.hom ≫ t ≫ κx.inv)
            (Functor.map_comp M γ δ).symm)
    _ = κx.hom ≫ M.map (𝟙 (q ^*[canonicalPullbackChoice Y₀.p] x)) ≫ κx.inv := by
      rw [hEq]
    _ = κx.hom ≫ 𝟙 _ ≫ κx.inv := by
      exact congrArg (fun t => κx.hom ≫ t ≫ κx.inv)
        (Functor.map_id M (q ^*[canonicalPullbackChoice Y₀.p] x))
    _ = κx.hom ≫ κx.inv := by
      simp only [Category.assoc, Category.id_comp]
    _ = 𝟙 (b ^*[canonicalPullbackChoice Y₀.p] x) := κx.hom_inv_id

/-- Helper for Chap08 Lemma 8 8 4: the reverse reindexed composite also becomes the identity
after the equalizer refinement. -/
private theorem stackification_lifted_inv_hom_reindex_eq_id
    {Y₀ : FibredCategoryOver C}
    {U V W : C} (q : V ⟶ U) (r : W ⟶ V) (b : W ⟶ U) (hb : r ≫ q = b)
    (x y : Y₀.p.Fiber U)
    (γ : (q ^*[canonicalPullbackChoice Y₀.p] x) ⟶
      (q ^*[canonicalPullbackChoice Y₀.p] y))
    (δ : (q ^*[canonicalPullbackChoice Y₀.p] y) ⟶
      (q ^*[canonicalPullbackChoice Y₀.p] x))
    (hEq :
      ((canonicalFiberPseudofunctor Y₀.p).map r.op.toLoc).toFunctor.map (δ ≫ γ) =
        ((canonicalFiberPseudofunctor Y₀.p).map r.op.toLoc).toFunctor.map
          (𝟙 (q ^*[canonicalPullbackChoice Y₀.p] y))) :
    let κx := canonicalFiberPseudofunctor_mapCompAppIso Y₀.p q r b
      (comp_toLoc_eq q r b hb) x
    let κy := canonicalFiberPseudofunctor_mapCompAppIso Y₀.p q r b
      (comp_toLoc_eq q r b hb) y
    let M := ((canonicalFiberPseudofunctor Y₀.p).map r.op.toLoc).toFunctor
    (κy.hom ≫ M.map δ ≫ κx.inv) ≫
        (κx.hom ≫ M.map γ ≫ κy.inv) =
      𝟙 (b ^*[canonicalPullbackChoice Y₀.p] y) := by
  dsimp only
  let κx := canonicalFiberPseudofunctor_mapCompAppIso Y₀.p q r b
    (comp_toLoc_eq q r b hb) x
  let κy := canonicalFiberPseudofunctor_mapCompAppIso Y₀.p q r b
    (comp_toLoc_eq q r b hb) y
  let M := ((canonicalFiberPseudofunctor Y₀.p).map r.op.toLoc).toFunctor
  calc
    (κy.hom ≫ M.map δ ≫ κx.inv) ≫ (κx.hom ≫ M.map γ ≫ κy.inv) =
        κy.hom ≫ M.map δ ≫ (κx.inv ≫ κx.hom) ≫ M.map γ ≫ κy.inv := by
      simp only [Category.assoc]
    _ = κy.hom ≫ M.map δ ≫ 𝟙 _ ≫ M.map γ ≫ κy.inv := by
      exact congrArg
        (fun t => κy.hom ≫ M.map δ ≫ t ≫ M.map γ ≫ κy.inv)
        κx.inv_hom_id
    _ = κy.hom ≫ M.map δ ≫ M.map γ ≫ κy.inv := by
      simp only [Category.id_comp]
    _ = κy.hom ≫ M.map (δ ≫ γ) ≫ κy.inv := by
      exact
        (congrArg (fun t => κy.hom ≫ t)
          (Category.assoc (M.map δ) (M.map γ) κy.inv).symm).trans
          (congrArg (fun t => κy.hom ≫ t ≫ κy.inv)
            (Functor.map_comp M δ γ).symm)
    _ = κy.hom ≫ M.map (𝟙 (q ^*[canonicalPullbackChoice Y₀.p] y)) ≫ κy.inv := by
      rw [hEq]
    _ = κy.hom ≫ 𝟙 _ ≫ κy.inv := by
      exact congrArg (fun t => κy.hom ≫ t ≫ κy.inv)
        (Functor.map_id M (q ^*[canonicalPullbackChoice Y₀.p] y))
    _ = κy.hom ≫ κy.inv := by
      simp only [Category.assoc, Category.id_comp]
    _ = 𝟙 (b ^*[canonicalPullbackChoice Y₀.p] y) := κy.hom_inv_id

/-- Helper for Chap08 Lemma 8 8 4: the equalizer cover forcing a lifted hom followed by a
lifted inverse to be the identity. -/
private noncomputable def stackificationLiftIsoHomInvEqualizerCover
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (j : FibredCategoryMor Y₀ Y₁)
    (hj : FibredCategoryMor.IsStackification j)
    {U V : C} (q : V ⟶ U) (x y : Y₀.p.Fiber U)
    (d : ((FibredCategoryMor.fiberFunctor j U).obj x) ≅
      ((FibredCategoryMor.fiberFunctor j U).obj y))
    (γ : (q ^*[canonicalPullbackChoice Y₀.p] x) ⟶
      (q ^*[canonicalPullbackChoice Y₀.p] y))
    (δ : (q ^*[canonicalPullbackChoice Y₀.p] y) ⟶
      (q ^*[canonicalPullbackChoice Y₀.p] x))
    (hγ : (FibredCategoryMor.fiberFunctor j V).map γ =
        (FibredCategoryMor.pullbackComparison j q x).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map q.op.toLoc).toFunctor.map d.hom ≫
          (FibredCategoryMor.pullbackComparison j q y).hom)
    (hδ : (FibredCategoryMor.fiberFunctor j V).map δ =
        (FibredCategoryMor.pullbackComparison j q y).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map q.op.toLoc).toFunctor.map d.inv ≫
          (FibredCategoryMor.pullbackComparison j q x).hom) :
    J.Cover V :=
  stackificationHomEqualizerBaseCover (J := J) j hj
    (γ ≫ δ)
    (𝟙 (q ^*[canonicalPullbackChoice Y₀.p] x))
    ((stackification_lifted_hom_inv_image_id (J := J) j q x y d γ δ hγ hδ).trans
      (Functor.map_id (FibredCategoryMor.fiberFunctor j V)
        (q ^*[canonicalPullbackChoice Y₀.p] x)).symm)

/-- Helper for Chap08 Lemma 8 8 4: membership in the hom-inverse equalizer cover gives equality
of the restricted composite with the restricted identity. -/
private theorem stackificationLiftIsoHomInvEqualizerCover_eq
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (j : FibredCategoryMor Y₀ Y₁)
    (hj : FibredCategoryMor.IsStackification j)
    {U V : C} (q : V ⟶ U) (x y : Y₀.p.Fiber U)
    (d : ((FibredCategoryMor.fiberFunctor j U).obj x) ≅
      ((FibredCategoryMor.fiberFunctor j U).obj y))
    (γ : (q ^*[canonicalPullbackChoice Y₀.p] x) ⟶
      (q ^*[canonicalPullbackChoice Y₀.p] y))
    (δ : (q ^*[canonicalPullbackChoice Y₀.p] y) ⟶
      (q ^*[canonicalPullbackChoice Y₀.p] x))
    (hγ : (FibredCategoryMor.fiberFunctor j V).map γ =
        (FibredCategoryMor.pullbackComparison j q x).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map q.op.toLoc).toFunctor.map d.hom ≫
          (FibredCategoryMor.pullbackComparison j q y).hom)
    (hδ : (FibredCategoryMor.fiberFunctor j V).map δ =
        (FibredCategoryMor.pullbackComparison j q y).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map q.op.toLoc).toFunctor.map d.inv ≫
          (FibredCategoryMor.pullbackComparison j q x).hom)
    (K : (stackificationLiftIsoHomInvEqualizerCover (J := J) j hj q x y d γ δ hγ hδ).Arrow) :
    ((canonicalFiberPseudofunctor Y₀.p).map K.f.op.toLoc).toFunctor.map (γ ≫ δ) =
      ((canonicalFiberPseudofunctor Y₀.p).map K.f.op.toLoc).toFunctor.map
        (𝟙 (q ^*[canonicalPullbackChoice Y₀.p] x)) := by
  have hraw := stackificationHomEqualizerBaseCover_eq (J := J) j hj
    (γ ≫ δ)
    (𝟙 (q ^*[canonicalPullbackChoice Y₀.p] x))
    ((stackification_lifted_hom_inv_image_id (J := J) j q x y d γ δ hγ hδ).trans
      (Functor.map_id (FibredCategoryMor.fiberFunctor j V)
        (q ^*[canonicalPullbackChoice Y₀.p] x)).symm)
    K
  have hid : (K.f ≫ 𝟙 V).op.toLoc = K.f.op.toLoc := by
    rw [Category.comp_id]
  rw [hid] at hraw
  exact hraw

/-- Helper for Chap08 Lemma 8 8 4: the equalizer cover forcing a lifted inverse followed by a
lifted hom to be the identity. -/
private noncomputable def stackificationLiftIsoInvHomEqualizerCover
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (j : FibredCategoryMor Y₀ Y₁)
    (hj : FibredCategoryMor.IsStackification j)
    {U V : C} (q : V ⟶ U) (x y : Y₀.p.Fiber U)
    (d : ((FibredCategoryMor.fiberFunctor j U).obj x) ≅
      ((FibredCategoryMor.fiberFunctor j U).obj y))
    (γ : (q ^*[canonicalPullbackChoice Y₀.p] x) ⟶
      (q ^*[canonicalPullbackChoice Y₀.p] y))
    (δ : (q ^*[canonicalPullbackChoice Y₀.p] y) ⟶
      (q ^*[canonicalPullbackChoice Y₀.p] x))
    (hγ : (FibredCategoryMor.fiberFunctor j V).map γ =
        (FibredCategoryMor.pullbackComparison j q x).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map q.op.toLoc).toFunctor.map d.hom ≫
          (FibredCategoryMor.pullbackComparison j q y).hom)
    (hδ : (FibredCategoryMor.fiberFunctor j V).map δ =
        (FibredCategoryMor.pullbackComparison j q y).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map q.op.toLoc).toFunctor.map d.inv ≫
          (FibredCategoryMor.pullbackComparison j q x).hom) :
    J.Cover V :=
  stackificationHomEqualizerBaseCover (J := J) j hj
    (δ ≫ γ)
    (𝟙 (q ^*[canonicalPullbackChoice Y₀.p] y))
    ((stackification_lifted_inv_hom_image_id (J := J) j q x y d γ δ hγ hδ).trans
      (Functor.map_id (FibredCategoryMor.fiberFunctor j V)
        (q ^*[canonicalPullbackChoice Y₀.p] y)).symm)

/-- Helper for Chap08 Lemma 8 8 4: membership in the inverse-hom equalizer cover gives equality
of the restricted reverse composite with the restricted identity. -/
private theorem stackificationLiftIsoInvHomEqualizerCover_eq
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (j : FibredCategoryMor Y₀ Y₁)
    (hj : FibredCategoryMor.IsStackification j)
    {U V : C} (q : V ⟶ U) (x y : Y₀.p.Fiber U)
    (d : ((FibredCategoryMor.fiberFunctor j U).obj x) ≅
      ((FibredCategoryMor.fiberFunctor j U).obj y))
    (γ : (q ^*[canonicalPullbackChoice Y₀.p] x) ⟶
      (q ^*[canonicalPullbackChoice Y₀.p] y))
    (δ : (q ^*[canonicalPullbackChoice Y₀.p] y) ⟶
      (q ^*[canonicalPullbackChoice Y₀.p] x))
    (hγ : (FibredCategoryMor.fiberFunctor j V).map γ =
        (FibredCategoryMor.pullbackComparison j q x).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map q.op.toLoc).toFunctor.map d.hom ≫
          (FibredCategoryMor.pullbackComparison j q y).hom)
    (hδ : (FibredCategoryMor.fiberFunctor j V).map δ =
        (FibredCategoryMor.pullbackComparison j q y).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map q.op.toLoc).toFunctor.map d.inv ≫
          (FibredCategoryMor.pullbackComparison j q x).hom)
    (K : (stackificationLiftIsoInvHomEqualizerCover (J := J) j hj q x y d γ δ hγ hδ).Arrow) :
    ((canonicalFiberPseudofunctor Y₀.p).map K.f.op.toLoc).toFunctor.map (δ ≫ γ) =
      ((canonicalFiberPseudofunctor Y₀.p).map K.f.op.toLoc).toFunctor.map
        (𝟙 (q ^*[canonicalPullbackChoice Y₀.p] y)) := by
  have hraw := stackificationHomEqualizerBaseCover_eq (J := J) j hj
    (δ ≫ γ)
    (𝟙 (q ^*[canonicalPullbackChoice Y₀.p] y))
    ((stackification_lifted_inv_hom_image_id (J := J) j q x y d γ δ hγ hδ).trans
      (Functor.map_id (FibredCategoryMor.fiberFunctor j V)
        (q ^*[canonicalPullbackChoice Y₀.p] y)).symm)
    K
  have hid : (K.f ≫ 𝟙 V).op.toLoc = K.f.op.toLoc := by
    rw [Category.comp_id]
  rw [hid] at hraw
  exact hraw

/-- Helper for Chap08 Lemma 8 8 4: refine local lifts of the two directions by equalizer covers
so that they become inverse isomorphisms after reindexing. -/
private theorem stackificationHomImageBaseCover_lift_iso_from_lifts
    {Y₀ : FibredCategoryOver.{u, v, max u v, v} C}
    {Y₁ : StackOver.{u, v, max u v, v} J}
    (j : FibredCategoryMor Y₀ Y₁)
    (hj : FibredCategoryMor.IsStackification j)
    {U : C} (x y : Y₀.p.Fiber U)
    (d : ((FibredCategoryMor.fiberFunctor j U).obj x) ≅
      ((FibredCategoryMor.fiberFunctor j U).obj y))
    (S₀ : J.Cover U)
    (γ₀ : ∀ I : S₀.Arrow,
      (I.f ^*[canonicalPullbackChoice Y₀.p] x) ⟶
        (I.f ^*[canonicalPullbackChoice Y₀.p] y))
    (δ₀ : ∀ I : S₀.Arrow,
      (I.f ^*[canonicalPullbackChoice Y₀.p] y) ⟶
        (I.f ^*[canonicalPullbackChoice Y₀.p] x))
    (hγ₀ : ∀ I : S₀.Arrow,
      (FibredCategoryMor.fiberFunctor j I.Y).map (γ₀ I) =
        (FibredCategoryMor.pullbackComparison j I.f x).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map I.f.op.toLoc).toFunctor.map d.hom ≫
          (FibredCategoryMor.pullbackComparison j I.f y).hom)
    (hδ₀ : ∀ I : S₀.Arrow,
      (FibredCategoryMor.fiberFunctor j I.Y).map (δ₀ I) =
        (FibredCategoryMor.pullbackComparison j I.f y).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map I.f.op.toLoc).toFunctor.map d.inv ≫
          (FibredCategoryMor.pullbackComparison j I.f x).hom) :
    ∃ S : J.Cover U, ∀ A : S.Arrow,
      ∃ γ : (A.f ^*[canonicalPullbackChoice Y₀.p] x) ≅
          (A.f ^*[canonicalPullbackChoice Y₀.p] y),
        (FibredCategoryMor.fiberFunctor j A.Y).map γ.hom =
            (FibredCategoryMor.pullbackComparison j A.f x).inv ≫
              ((canonicalFiberPseudofunctor Y₁.p).map A.f.op.toLoc).toFunctor.map d.hom ≫
              (FibredCategoryMor.pullbackComparison j A.f y).hom := by
  let T₁ : ∀ I : S₀.Arrow, J.Cover I.Y := fun I =>
    stackificationLiftIsoHomInvEqualizerCover (J := J) j hj I.f x y d
      (γ₀ I) (δ₀ I) (hγ₀ I) (hδ₀ I)
  let T₂ : ∀ I : S₀.Arrow, J.Cover I.Y := fun I =>
    stackificationLiftIsoInvHomEqualizerCover (J := J) j hj I.f x y d
      (γ₀ I) (δ₀ I) (hγ₀ I) (hδ₀ I)
  let T : ∀ I : S₀.Arrow, J.Cover I.Y := fun I => T₁ I ⊓ T₂ I
  refine ⟨S₀.bind T, ?_⟩
  intro A
  let I : S₀.Arrow := A.fromMiddle
  let K : (T I).Arrow := A.toMiddle
  let K₁ : (T₁ I).Arrow := ⟨K.Y, K.f, K.hf.left⟩
  let K₂ : (T₂ I).Arrow := ⟨K.Y, K.f, K.hf.right⟩
  let κx := canonicalFiberPseudofunctor_mapCompAppIso Y₀.p I.f K.f A.f
    (comp_toLoc_eq I.f K.f A.f A.middle_spec) x
  let κy := canonicalFiberPseudofunctor_mapCompAppIso Y₀.p I.f K.f A.f
    (comp_toLoc_eq I.f K.f A.f A.middle_spec) y
  let M := ((canonicalFiberPseudofunctor Y₀.p).map K.f.op.toLoc).toFunctor
  let γ :=
    κx.hom ≫ M.map (γ₀ I) ≫ κy.inv
  let δ :=
    κy.hom ≫ M.map (δ₀ I) ≫ κx.inv
  have hEq₁ :
      M.map ((γ₀ I) ≫ (δ₀ I)) =
        M.map (𝟙 (I.f ^*[canonicalPullbackChoice Y₀.p] x)) := by
    have hraw :=
      stackificationLiftIsoHomInvEqualizerCover_eq (J := J) j hj I.f x y d
        (γ₀ I) (δ₀ I) (hγ₀ I) (hδ₀ I) K₁
    have hid :
        (𝟙 (LocallyDiscrete.mk (Opposite.op I.Y)) ≫ K.f.op.toLoc) = K.f.op.toLoc := by
      exact Category.id_comp K.f.op.toLoc
    have hid' : (K.f ≫ 𝟙 I.Y).op.toLoc = K.f.op.toLoc := by
      rw [Category.comp_id]
    simpa [M, K₁, hid, hid'] using hraw
  have hEq₂ :
      M.map ((δ₀ I) ≫ (γ₀ I)) =
        M.map (𝟙 (I.f ^*[canonicalPullbackChoice Y₀.p] y)) := by
    have hraw :=
      stackificationLiftIsoInvHomEqualizerCover_eq (J := J) j hj I.f x y d
        (γ₀ I) (δ₀ I) (hγ₀ I) (hδ₀ I) K₂
    have hid :
        (𝟙 (LocallyDiscrete.mk (Opposite.op I.Y)) ≫ K.f.op.toLoc) = K.f.op.toLoc := by
      exact Category.id_comp K.f.op.toLoc
    have hid' : (K.f ≫ 𝟙 I.Y).op.toLoc = K.f.op.toLoc := by
      rw [Category.comp_id]
    simpa [M, K₂, hid, hid'] using hraw
  have hhom_inv : γ ≫ δ = 𝟙 (A.f ^*[canonicalPullbackChoice Y₀.p] x) := by
    simpa only [γ, δ, κx, κy, M] using
      stackification_lifted_hom_inv_reindex_eq_id
        (q := I.f) (r := K.f) (b := A.f) A.middle_spec
        x y (γ₀ I) (δ₀ I) hEq₁
  have hinv_hom : δ ≫ γ = 𝟙 (A.f ^*[canonicalPullbackChoice Y₀.p] y) := by
    simpa only [γ, δ, κx, κy, M] using
      stackification_lifted_inv_hom_reindex_eq_id
        (q := I.f) (r := K.f) (b := A.f) A.middle_spec
        x y (γ₀ I) (δ₀ I) hEq₂
  refine ⟨{ hom := γ, inv := δ, hom_inv_id := hhom_inv, inv_hom_id := hinv_hom }, ?_⟩
  have hγ :=
    stackification_lifted_hom_reindex_direct_image (J := J) j I.f K.f A.f
      A.middle_spec x y d.hom (γ₀ I) (hγ₀ I)
  simpa only [γ, κx, κy, M] using hγ

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 4: an isomorphism between two `j`-images lifts locally to a
source-side isomorphism with the standard stackification image formulas for both directions. -/
private theorem stackificationHomImageBaseCover_lift_iso
    {Y₀ : FibredCategoryOver.{u, v, max u v, v} C}
    {Y₁ : StackOver.{u, v, max u v, v} J}
    (j : FibredCategoryMor Y₀ Y₁)
    (hj : FibredCategoryMor.IsStackification j)
    {U : C} (x y : Y₀.p.Fiber U)
    [(J.over U).WEqualsLocallyBijective (Type v)]
    (d : ((FibredCategoryMor.fiberFunctor j U).obj x) ≅
      ((FibredCategoryMor.fiberFunctor j U).obj y)) :
    ∃ S : J.Cover U, ∀ I : S.Arrow,
      ∃ γ : (I.f ^*[canonicalPullbackChoice Y₀.p] x) ≅
          (I.f ^*[canonicalPullbackChoice Y₀.p] y),
        (FibredCategoryMor.fiberFunctor j I.Y).map γ.hom =
            (FibredCategoryMor.pullbackComparison j I.f x).inv ≫
              ((canonicalFiberPseudofunctor Y₁.p).map I.f.op.toLoc).toFunctor.map d.hom ≫
              (FibredCategoryMor.pullbackComparison j I.f y).hom := by
  classical
  let βh :
      ((canonicalFiberPseudofunctor Y₁.p).presheafHom
        ((FibredCategoryMor.fiberFunctor j U).obj x)
        ((FibredCategoryMor.fiberFunctor j U).obj y)).obj
          (Opposite.op (Over.mk (𝟙 U))) :=
    (canonicalFiberPseudofunctor Y₁.p).presheafHomObjHomEquiv d.hom
  let βi :
      ((canonicalFiberPseudofunctor Y₁.p).presheafHom
        ((FibredCategoryMor.fiberFunctor j U).obj y)
        ((FibredCategoryMor.fiberFunctor j U).obj x)).obj
          (Opposite.op (Over.mk (𝟙 U))) :=
    (canonicalFiberPseudofunctor Y₁.p).presheafHomObjHomEquiv d.inv
  let Sh : J.Cover U := stackificationHomImageBaseCover (J := J) j hj x y βh
  let Si : J.Cover U := stackificationHomImageBaseCover (J := J) j hj y x βi
  let S₀ : J.Cover U := Sh ⊓ Si
  let liftHom : ∀ I : S₀.Arrow,
      ∃ γ : (I.f ^*[canonicalPullbackChoice Y₀.p] x) ⟶
          (I.f ^*[canonicalPullbackChoice Y₀.p] y),
        (FibredCategoryMor.fiberFunctor j I.Y).map γ =
          (FibredCategoryMor.pullbackComparison j I.f x).inv ≫
            ((canonicalFiberPseudofunctor Y₁.p).map I.f.op.toLoc).toFunctor.map d.hom ≫
            (FibredCategoryMor.pullbackComparison j I.f y).hom := by
    intro I
    let Ih : Sh.Arrow := ⟨I.Y, I.f, I.hf.left⟩
    simpa only [S₀, Sh, Ih] using
      stackificationHomImageBaseCover_lift_hom (J := J) j hj x y d.hom Ih
  let liftInv : ∀ I : S₀.Arrow,
      ∃ δ : (I.f ^*[canonicalPullbackChoice Y₀.p] y) ⟶
          (I.f ^*[canonicalPullbackChoice Y₀.p] x),
        (FibredCategoryMor.fiberFunctor j I.Y).map δ =
          (FibredCategoryMor.pullbackComparison j I.f y).inv ≫
            ((canonicalFiberPseudofunctor Y₁.p).map I.f.op.toLoc).toFunctor.map d.inv ≫
            (FibredCategoryMor.pullbackComparison j I.f x).hom := by
    intro I
    let Ii : Si.Arrow := ⟨I.Y, I.f, I.hf.right⟩
    simpa only [S₀, Si, Ii] using
      stackificationHomImageBaseCover_lift_hom (J := J) j hj y x d.inv Ii
  let γ₀ : ∀ I : S₀.Arrow,
      (I.f ^*[canonicalPullbackChoice Y₀.p] x) ⟶
        (I.f ^*[canonicalPullbackChoice Y₀.p] y) := fun I =>
    Classical.choose (liftHom I)
  let δ₀ : ∀ I : S₀.Arrow,
      (I.f ^*[canonicalPullbackChoice Y₀.p] y) ⟶
        (I.f ^*[canonicalPullbackChoice Y₀.p] x) := fun I =>
    Classical.choose (liftInv I)
  have hγ₀ : ∀ I : S₀.Arrow,
      (FibredCategoryMor.fiberFunctor j I.Y).map (γ₀ I) =
        (FibredCategoryMor.pullbackComparison j I.f x).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map I.f.op.toLoc).toFunctor.map d.hom ≫
          (FibredCategoryMor.pullbackComparison j I.f y).hom := fun I =>
    Classical.choose_spec (liftHom I)
  have hδ₀ : ∀ I : S₀.Arrow,
      (FibredCategoryMor.fiberFunctor j I.Y).map (δ₀ I) =
        (FibredCategoryMor.pullbackComparison j I.f y).inv ≫
          ((canonicalFiberPseudofunctor Y₁.p).map I.f.op.toLoc).toFunctor.map d.inv ≫
          (FibredCategoryMor.pullbackComparison j I.f x).hom := fun I =>
    Classical.choose_spec (liftInv I)
  exact
    stackificationHomImageBaseCover_lift_iso_from_lifts (J := J) j hj x y d
      S₀ γ₀ δ₀ hγ₀ hδ₀

/-- Helper for Chap08 Lemma 8 8 4: the explicit middle-postcomposition functor sends an object
of the source two-fibre product to the object obtained by applying `j` to its comparison
isomorphism. -/
private noncomputable def twoFibreProductMiddlePostcomposeObj
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    (P : (twoFibreProduct f g).S) :
    (twoFibreProduct (f ≫ j) (g ≫ j)).S :=
  { U := P.U
    obj :=
      { fst := P.obj.fst
        snd := P.obj.snd
        iso := (FibredCategoryMor.fiberFunctor j P.U).mapIso P.obj.iso } }

/-- Helper for Chap08 Lemma 8 8 4: the explicit middle-postcomposition object keeps the left
component unchanged. -/
private theorem twoFibreProductMiddlePostcomposeObj_fst
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    (P : (twoFibreProduct f g).S) :
    (twoFibreProductMiddlePostcomposeObj f g j P).obj.fst = P.obj.fst := by
  -- The middle replacement changes only the stored comparison isomorphism.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the explicit middle-postcomposition object keeps the right
component unchanged. -/
private theorem twoFibreProductMiddlePostcomposeObj_snd
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    (P : (twoFibreProduct f g).S) :
    (twoFibreProductMiddlePostcomposeObj f g j P).obj.snd = P.obj.snd := by
  -- The right endpoint is also unchanged by middle postcomposition.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the comparison morphism of the explicit
middle-postcomposition object is the `j`-image of the original comparison morphism. -/
private theorem twoFibreProductMiddlePostcomposeObj_comparison
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    (P : (twoFibreProduct f g).S) :
    (twoFibreProductMiddlePostcomposeObj f g j P).comparison =
      (FibredCategoryMor.toFunctor j).map P.comparison := by
  -- The object was built by applying the fiber functor of `j` to the original fiberwise
  -- comparison isomorphism.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the explicit middle-postcomposition map satisfies the
two-fibre-product commutativity relation. -/
private theorem twoFibreProductMiddlePostcomposeMap_comm
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    {P Q : (twoFibreProduct f g).S} (φ : P ⟶ Q) :
    CommSq ((FibredCategoryMor.toFunctor (f ≫ j)).map φ.a)
      (twoFibreProductMiddlePostcomposeObj f g j P).comparison
      (twoFibreProductMiddlePostcomposeObj f g j Q).comparison
      ((FibredCategoryMor.toFunctor (g ≫ j)).map φ.b) := by
  refine ⟨?_⟩
  -- After unfolding the composite morphisms, this is just functoriality of `j` applied to the
  -- original two-fibre-product square carried by `φ`.
  change (FibredCategoryMor.toFunctor j).map ((FibredCategoryMor.toFunctor f).map φ.a) ≫
      (FibredCategoryMor.toFunctor j).map Q.comparison =
    (FibredCategoryMor.toFunctor j).map P.comparison ≫
      (FibredCategoryMor.toFunctor j).map ((FibredCategoryMor.toFunctor g).map φ.b)
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (FibredCategoryMor.toFunctor j).map φ.comm.w

/-- Helper for Chap08 Lemma 8 8 4: the explicit middle-postcomposition functor sends morphisms
by keeping their endpoint components and applying `j` only to the comparison square. -/
private noncomputable def twoFibreProductMiddlePostcomposeMap
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    {P Q : (twoFibreProduct f g).S} (φ : P ⟶ Q) :
    twoFibreProductMiddlePostcomposeObj f g j P ⟶
      twoFibreProductMiddlePostcomposeObj f g j Q :=
  { base := φ.base
    a := φ.a
    a_over := φ.a_over
    b := φ.b
    b_over := φ.b_over
    comm := twoFibreProductMiddlePostcomposeMap_comm f g j φ }

/-- Helper for Chap08 Lemma 8 8 4: the explicit middle-postcomposition map keeps the left
morphism component unchanged. -/
private theorem twoFibreProductMiddlePostcomposeMap_a
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    {P Q : (twoFibreProduct f g).S} (φ : P ⟶ Q) :
    (twoFibreProductMiddlePostcomposeMap f g j φ).a = φ.a := by
  -- The map was defined componentwise with identical endpoint arrows.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the explicit middle-postcomposition map keeps the right
morphism component unchanged. -/
private theorem twoFibreProductMiddlePostcomposeMap_b
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    {P Q : (twoFibreProduct f g).S} (φ : P ⟶ Q) :
    (twoFibreProductMiddlePostcomposeMap f g j φ).b = φ.b := by
  -- The right component is equally unchanged.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the explicit middle-postcomposition map preserves identity
morphisms. -/
private theorem twoFibreProductMiddlePostcomposeMap_id
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    (P : (twoFibreProduct f g).S) :
    twoFibreProductMiddlePostcomposeMap f g j (𝟙 P) =
      𝟙 (twoFibreProductMiddlePostcomposeObj f g j P) := by
  -- Identity preservation is checked on the two explicit endpoint components.
  apply CategoryOver.ExplicitTwoFibreProductHom.ext
  · rfl
  · rfl

/-- Helper for Chap08 Lemma 8 8 4: the explicit middle-postcomposition map preserves
composition of morphisms. -/
private theorem twoFibreProductMiddlePostcomposeMap_comp
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    {P Q R : (twoFibreProduct f g).S} (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    twoFibreProductMiddlePostcomposeMap f g j (φ ≫ ψ) =
      twoFibreProductMiddlePostcomposeMap f g j φ ≫
        twoFibreProductMiddlePostcomposeMap f g j ψ := by
  -- Composition preservation is also componentwise; proof fields are proof-irrelevant after
  -- the endpoint components are fixed.
  apply CategoryOver.ExplicitTwoFibreProductHom.ext
  · rfl
  · rfl

/-- Helper for Chap08 Lemma 8 8 4: the transparent ordinary functor underlying middle
postcomposition of explicit two-fibre products. -/
private noncomputable def twoFibreProductMiddlePostcomposeFunctor
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁) :
    (twoFibreProduct f g).S ⥤ (twoFibreProduct (f ≫ j) (g ≫ j)).S where
  obj := twoFibreProductMiddlePostcomposeObj f g j
  map := fun φ ↦ twoFibreProductMiddlePostcomposeMap f g j φ
  map_id := twoFibreProductMiddlePostcomposeMap_id f g j
  map_comp := fun φ ψ ↦ twoFibreProductMiddlePostcomposeMap_comp f g j φ ψ

/-- Helper for Chap08 Lemma 8 8 4: the transparent middle-postcomposition functor lies over the
identity on the base site. -/
private theorem twoFibreProductMiddlePostcomposeFunctor_base
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁) :
    twoFibreProductMiddlePostcomposeFunctor f g j ⋙
        (twoFibreProduct (f ≫ j) (g ≫ j)).p =
      (twoFibreProduct f g).p := by
  -- On objects and morphisms the functor preserves the stored base coordinate exactly.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the transparent based functor underlying middle
postcomposition of explicit two-fibre products. -/
private noncomputable def twoFibreProductMiddlePostcomposeBasedFunctor
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁) :
    (twoFibreProduct f g).toBasedCategory ⥤ᵇ
      (twoFibreProduct (f ≫ j) (g ≫ j)).toBasedCategory :=
  { toFunctor := twoFibreProductMiddlePostcomposeFunctor f g j
    w := twoFibreProductMiddlePostcomposeFunctor_base f g j }

/-- Helper for Chap08 Lemma 8 8 4: postcomposing both legs of a two-fibre-product square by
the same middle morphism gives the canonical middle-replacement square. -/
private noncomputable def twoFibreProductMiddlePostcomposeSquare
    {Y₀ Y₁ : FibredCategoryOver C}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁) :
    BicategoricalTwoCommutativeSquare (f ≫ j) (g ≫ j) :=
  -- Keep the middle-replacement square in the associator-normal form used by the explicit
  -- objectwise comparison, rather than routing through `.postcompose` and its unitor transport.
  { obj := twoFibreProduct f g
    p := twoFibreProductLeftProjection f g
    q := twoFibreProductRightProjection f g
    ψ :=
      (α_ (twoFibreProductLeftProjection f g) f j).symm ≪≫
        whiskerRightIso (twoFibreProductSquare f g).ψ j ≪≫
          (α_ (twoFibreProductRightProjection f g) g j) }

/-- Helper for Chap08 Lemma 8 8 4: the middle-replacement square has the original
two-fibre-product as apex. -/
private theorem twoFibreProductMiddlePostcomposeSquare_obj
    {Y₀ Y₁ : FibredCategoryOver C}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁) :
    (twoFibreProductMiddlePostcomposeSquare f g j).obj = twoFibreProduct f g := by
  -- Postcomposition changes only the cospan labels, not the apex object.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the middle-replacement square keeps the original left
projection. -/
private theorem twoFibreProductMiddlePostcomposeSquare_p
    {Y₀ Y₁ : FibredCategoryOver C}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁) :
    (twoFibreProductMiddlePostcomposeSquare f g j).p = twoFibreProductLeftProjection f g := by
  -- Only the common target is postcomposed by `j`; the left projection itself is unchanged.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the middle-replacement square keeps the original right
projection. -/
private theorem twoFibreProductMiddlePostcomposeSquare_q
    {Y₀ Y₁ : FibredCategoryOver C}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁) :
    (twoFibreProductMiddlePostcomposeSquare f g j).q = twoFibreProductRightProjection f g := by
  -- The right projection is similarly unchanged by postcomposing the comparison square.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the canonical middle-replacement morphism from the original
two-fibre product to the two-fibre product after postcomposition by the middle map. -/
private noncomputable def twoFibreProductMiddlePostcomposeHom
    {Y₀ Y₁ : FibredCategoryOver C}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁) :
    FibredCategoryMor (twoFibreProduct f g) (twoFibreProduct (f ≫ j) (g ≫ j)) :=
  -- Route correction: use the explicit terminal-lift morphism from Lemma 4.33.10, so the
  -- cartesian-preservation proof and projection cells are shared with the canonical owner API.
  let P := twoFibreProductMiddlePostcomposeSquare f g j
  (twoFibreProduct_terminalLift (f ≫ j) (g ≫ j) P).hom

/-- Helper for Chap08 Lemma 8 8 4: the public terminal-lift middle morphism keeps the left
object component. -/
private theorem twoFibreProductMiddlePostcomposeHom_obj_fst
    {Y₀ Y₁ : FibredCategoryOver C}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    (P : (twoFibreProduct f g).S) :
    ((FibredCategoryMor.toFunctor (twoFibreProductMiddlePostcomposeHom f g j)).obj P).obj.fst =
      P.obj.fst := by
  -- Compare only the cheap endpoint projection rather than the whole structured object.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the public terminal-lift middle morphism keeps the right
object component. -/
private theorem twoFibreProductMiddlePostcomposeHom_obj_snd
    {Y₀ Y₁ : FibredCategoryOver C}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    (P : (twoFibreProduct f g).S) :
    ((FibredCategoryMor.toFunctor (twoFibreProductMiddlePostcomposeHom f g j)).obj P).obj.snd =
      P.obj.snd := by
  -- The terminal-lift object stores the original right projection object.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the public terminal-lift middle morphism keeps the left
morphism component. -/
private theorem twoFibreProductMiddlePostcomposeHom_map_a
    {Y₀ Y₁ : FibredCategoryOver C}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    {P Q : (twoFibreProduct f g).S} (φ : P ⟶ Q) :
    ((FibredCategoryMor.toFunctor (twoFibreProductMiddlePostcomposeHom f g j)).map φ).a =
      φ.a := by
  -- On morphisms, the public terminal lift uses the source square's left leg.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the public terminal-lift middle morphism keeps the right
morphism component. -/
private theorem twoFibreProductMiddlePostcomposeHom_map_b
    {Y₀ Y₁ : FibredCategoryOver C}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    {P Q : (twoFibreProduct f g).S} (φ : P ⟶ Q) :
    ((FibredCategoryMor.toFunctor (twoFibreProductMiddlePostcomposeHom f g j)).map φ).b =
      φ.b := by
  -- The right leg is equally inherited from the source square.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: on fibres, the public terminal-lift middle morphism keeps
the left morphism component. -/
private theorem twoFibreProductMiddlePostcomposeHom_fiber_map_a
    {Y₀ Y₁ : FibredCategoryOver C}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    {U : C} {P Q : (twoFibreProduct f g).p.Fiber U} (φ : P ⟶ Q) :
    (((FibredCategoryMor.fiberFunctor
      (twoFibreProductMiddlePostcomposeHom f g j) U).map φ).1).a = φ.1.a := by
  rfl

/-- Helper for Chap08 Lemma 8 8 4: on fibres, the public terminal-lift middle morphism keeps
the right morphism component. -/
private theorem twoFibreProductMiddlePostcomposeHom_fiber_map_b
    {Y₀ Y₁ : FibredCategoryOver C}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    {U : C} {P Q : (twoFibreProduct f g).p.Fiber U} (φ : P ⟶ Q) :
    (((FibredCategoryMor.fiberFunctor
      (twoFibreProductMiddlePostcomposeHom f g j) U).map φ).1).b = φ.1.b := by
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the public terminal-lift middle morphism stores the
comparison component coming from the postcomposed square. -/
private theorem twoFibreProductMiddlePostcomposeHom_obj_comparison_owner
    {Y₀ Y₁ : FibredCategoryOver C}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    (P : (twoFibreProduct f g).S) :
    ((FibredCategoryMor.toFunctor (twoFibreProductMiddlePostcomposeHom f g j)).obj
        P).comparison =
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso
        (twoFibreProductMiddlePostcomposeSquare f g j).ψ).hom.app P := by
  -- Unfold only the public terminal-lift object; this is the stored comparison field.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the terminal-lift middle object stores the same comparison as
the transparent middle-postcomposition object. -/
private theorem twoFibreProductMiddlePostcomposeHom_obj_comparison
    {Y₀ Y₁ : FibredCategoryOver C}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    (P : (twoFibreProduct f g).S) :
    ((FibredCategoryMor.toFunctor (twoFibreProductMiddlePostcomposeHom f g j)).obj
        P).comparison =
      (FibredCategoryMor.toFunctor j).map P.comparison := by
  -- First expose the terminal lift's stored owner-square component; the direct square definition
  -- then reduces that component to the right-whiskered source comparison.
  rw [twoFibreProductMiddlePostcomposeHom_obj_comparison_owner]
  unfold twoFibreProductMiddlePostcomposeSquare
  have hAssoc :
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso
        ((α_ (twoFibreProductLeftProjection f g) f j).symm ≪≫
          whiskerRightIso (twoFibreProductSquare f g).ψ j ≪≫
            (α_ (twoFibreProductRightProjection f g) g j))).hom.app P =
        (FibredCategoryMor.basedFunctorIsoOfOwnerIso
          (whiskerRightIso (twoFibreProductSquare f g).ψ j)).hom.app P := by
    -- The two strict associators become identity `eqToHom` components after forgetting to based
    -- functors; cancel those components around the middle right-whiskered comparison.
    unfold FibredCategoryMor.basedFunctorIsoOfOwnerIso
    rw [Functor.mapIso_trans, Functor.mapIso_trans]
    rw [Bicategory.Strict.associator_eqToIso (twoFibreProductLeftProjection f g) f j]
    rw [Bicategory.Strict.associator_eqToIso (twoFibreProductRightProjection f g) g j]
    simp only [Functor.mapIso_symm, eqToIso_map, Iso.trans_hom]
    let m := ((fibredCategoryOverSubTwoCategory C).hom (twoFibreProduct f g) Y₁).inclusion.mapIso
      ((twoFibreProductSquare f g).ψ ▷ᵢ j)
    let sourceObj :=
      (((fibredCategoryOverSubTwoCategory C).hom (twoFibreProduct f g) Y₁).inclusion.obj
        (((twoFibreProductSquare f g).p ≫ f) ≫ j)).obj P
    let targetObj :=
      (((fibredCategoryOverSubTwoCategory C).hom (twoFibreProduct f g) Y₁).inclusion.obj
        (((twoFibreProductSquare f g).q ≫ g) ≫ j)).obj P
    change 𝟙 sourceObj ≫ (m.hom.toNatTrans.app P ≫ 𝟙 targetObj) =
      m.hom.toNatTrans.app P
    rw [Category.id_comp, Category.comp_id]
  -- The remaining middle component is definitionally the functor `j` applied to the source
  -- comparison stored in the original explicit two-fibre product.
  exact hAssoc.trans rfl

/-- Helper for Chap08 Lemma 8 8 4: the middle-postcomposition map carries a left projection
comparison back to the original left projection. -/
private noncomputable def twoFibreProductMiddlePostcomposeHom_leftProjection
    {Y₀ Y₁ : FibredCategoryOver C}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁) :
    twoFibreProductMiddlePostcomposeHom f g j ≫
        twoFibreProductLeftProjection (f ≫ j) (g ≫ j) ⟶
      twoFibreProductLeftProjection f g :=
  -- Reuse the left projection cell packaged with the public terminal lift.
  let P := twoFibreProductMiddlePostcomposeSquare f g j
  (twoFibreProduct_terminalLift (f ≫ j) (g ≫ j) P).left

/-- Helper for Chap08 Lemma 8 8 4: the middle-postcomposition map carries a right projection
comparison back to the original right projection. -/
private noncomputable def twoFibreProductMiddlePostcomposeHom_rightProjection
    {Y₀ Y₁ : FibredCategoryOver C}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁) :
    twoFibreProductMiddlePostcomposeHom f g j ≫
        twoFibreProductRightProjection (f ≫ j) (g ≫ j) ⟶
      twoFibreProductRightProjection f g :=
  -- Reuse the right projection cell packaged with the public terminal lift.
  let P := twoFibreProductMiddlePostcomposeSquare f g j
  (twoFibreProduct_terminalLift (f ≫ j) (g ≫ j) P).right

/-- Helper for Chap08 Lemma 8 8 4: on each fixed fibre, the middle-postcomposition map is
injective on Hom sets because it keeps both endpoint components unchanged. -/
private theorem twoFibreProductMiddlePostcomposeHom_fiberFunctor_map_injective
    {Y₀ Y₁ : FibredCategoryOver C}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    {U : C} (P Q : (twoFibreProduct f g).p.Fiber U) :
    Function.Injective
      ((FibredCategoryMor.fiberFunctor (twoFibreProductMiddlePostcomposeHom f g j) U).map :
        (P ⟶ Q) →
          ((FibredCategoryMor.fiberFunctor
            (twoFibreProductMiddlePostcomposeHom f g j) U).obj P ⟶
              (FibredCategoryMor.fiberFunctor
                (twoFibreProductMiddlePostcomposeHom f g j) U).obj Q)) := by
  intro φ ψ hφψ
  apply twoFibreProductFiberHom_ext_components f g φ ψ
  · have hleft := congrArg (fun eta => eta.1.a) hφψ
    simpa [FibredCategoryMor.fiberFunctor, twoFibreProductMiddlePostcomposeHom_map_a] using hleft
  · have hright := congrArg (fun eta => eta.1.b) hφψ
    simpa [FibredCategoryMor.fiberFunctor, twoFibreProductMiddlePostcomposeHom_map_b] using hright

/-- Helper for Chap08 Lemma 8 8 4: each app of the middle-postcomposition Hom-presheaf map is
injective. -/
private theorem twoFibreProductMiddlePostcomposeHom_presheafMap_app_injective
    {Y₀ Y₁ : FibredCategoryOver C}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    {U : C} (P Q : (twoFibreProduct f g).p.Fiber U)
    (W : (Over U)ᵒᵖ) :
    Function.Injective
      ((FibredCategoryMor.fibredMorphismPresheafMap
        (twoFibreProductMiddlePostcomposeHom f g j) P Q).app W) := by
  induction W using Opposite.rec
  rename_i W
  intro δ₁ δ₂ hδ
  let F := twoFibreProductMiddlePostcomposeHom f g j
  letI : (twoFibreProduct f g).p.IsFibered :=
    FibredCategoryOver.isFibred (twoFibreProduct f g)
  let eP := FibredCategoryMor.pullbackComparison F W.hom P
  let eQ := FibredCategoryMor.pullbackComparison F W.hom Q
  have hmap :
      (FibredCategoryMor.fiberFunctor F W.left).map δ₁ =
        (FibredCategoryMor.fiberFunctor F W.left).map δ₂ := by
    have hδ' :
        (eP.hom ≫ (FibredCategoryMor.fiberFunctor F W.left).map δ₁) ≫ eQ.inv =
          (eP.hom ≫ (FibredCategoryMor.fiberFunctor F W.left).map δ₂) ≫ eQ.inv := by
      have hδ₁ :
          (eP.hom ≫ (FibredCategoryMor.fiberFunctor F W.left).map δ₁) ≫ eQ.inv =
            (FibredCategoryMor.fibredMorphismPresheafMap F P Q).app (Opposite.op W) δ₁ := by
        simpa only [eP, eQ, Category.assoc] using
          (fibredMorphismPresheafMap_app_pullbackComparison F P Q W δ₁).symm
      have hδ₂ :
          (FibredCategoryMor.fibredMorphismPresheafMap F P Q).app (Opposite.op W) δ₂ =
            (eP.hom ≫ (FibredCategoryMor.fiberFunctor F W.left).map δ₂) ≫ eQ.inv := by
        simpa only [eP, eQ, Category.assoc] using
          fibredMorphismPresheafMap_app_pullbackComparison F P Q W δ₂
      exact hδ₁.trans (hδ.trans hδ₂)
    have hleft :
        eP.hom ≫ (FibredCategoryMor.fiberFunctor F W.left).map δ₁ =
          eP.hom ≫ (FibredCategoryMor.fiberFunctor F W.left).map δ₂ := by
      apply (cancel_mono eQ.inv).1
      exact hδ'
    exact (cancel_epi eP.hom).1 hleft
  exact
    twoFibreProductMiddlePostcomposeHom_fiberFunctor_map_injective
      f g j
      (W.hom ^*[canonicalPullbackChoice (twoFibreProduct f g).p] P)
      (W.hom ^*[canonicalPullbackChoice (twoFibreProduct f g).p] Q)
      hmap

/-- Helper for Chap08 Lemma 8 8 4: the endpoint-replacement square after the middle has already
been postcomposed by `j`, built directly rather than through the final comparison map. -/
private noncomputable def twoFibreProductEndpointReplacementDirectSquare
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j) :
    BicategoricalTwoCommutativeSquare f'.toFibredCategoryMor g'.toFibredCategoryMor :=
  -- Build the endpoint stage directly so the stored comparison is the source comparison
  -- conjugated by `α` and `β`, with no identity-middle unitor transport.
  let L := twoFibreProductLeftProjection (f ≫ j) (g ≫ j)
  let R := twoFibreProductRightProjection (f ≫ j) (g ≫ j)
  { obj := twoFibreProduct (f ≫ j) (g ≫ j)
    p := L ≫ i
    q := R ≫ k
    ψ :=
      (α_ L i f'.toFibredCategoryMor) ≪≫
        whiskerLeftIso L α ≪≫
          (twoFibreProductSquare (f ≫ j) (g ≫ j)).ψ ≪≫
            whiskerLeftIso R β.symm ≪≫
              (α_ R k g'.toFibredCategoryMor).symm }

/-- Helper for Chap08 Lemma 8 8 4: the direct endpoint-replacement square has the
middle-replaced two-fibre product as its apex. -/
private theorem twoFibreProductEndpointReplacementDirectSquare_obj
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j) :
    (twoFibreProductEndpointReplacementDirectSquare f g i j k f' g' α β).obj =
      twoFibreProduct (f ≫ j) (g ≫ j) := by
  -- This exposes the apex carried by the endpoint stage, separate from the original source
  -- pullback used by the full terminal comparison.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the left leg of the direct endpoint-replacement square is the
middle left projection followed by the endpoint stackification map. -/
private theorem twoFibreProductEndpointReplacementDirectSquare_p
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j) :
    (twoFibreProductEndpointReplacementDirectSquare f g i j k f' g' α β).p =
      twoFibreProductLeftProjection (f ≫ j) (g ≫ j) ≫ i := by
  -- Only the endpoint label is changed at this stage, so the left projection is postcomposed by
  -- `i`.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the right leg of the direct endpoint-replacement square is the
middle right projection followed by the endpoint stackification map. -/
private theorem twoFibreProductEndpointReplacementDirectSquare_q
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j) :
    (twoFibreProductEndpointReplacementDirectSquare f g i j k f' g' α β).q =
      twoFibreProductRightProjection (f ≫ j) (g ≫ j) ≫ k := by
  -- The right endpoint is treated symmetrically, with `k` replacing the endpoint.
  rfl

/-- Helper for Chap08 Lemma 8 8 5: forgetting an owner-level transitive isomorphism to based
functors preserves the componentwise composite normal form. -/
private theorem basedFunctorIsoOfOwnerIso_trans_hom_app
    {A B : FibredCategoryOver C} {F G H : A ⟶ B}
    (α : F ≅ G) (β : G ≅ H) (P : A.S) :
    (FibredCategoryMor.basedFunctorIsoOfOwnerIso (α ≪≫ β)).hom.app P =
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso α).hom.app P ≫
        (FibredCategoryMor.basedFunctorIsoOfOwnerIso β).hom.app P := by
  -- The owner inclusion is functorial, so transitive isomorphisms are evaluated componentwise.
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the component of a forgotten symmetric owner isomorphism is
the inverse component of the forgotten isomorphism. -/
private theorem basedFunctorIsoOfOwnerIso_symm_hom_app
    {A B : FibredCategoryOver C} {F G : A ⟶ B}
    (α : F ≅ G) (P : A.S) :
    (FibredCategoryMor.basedFunctorIsoOfOwnerIso α.symm).hom.app P =
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso α).inv.app P := by
  -- Symmetry of owner isomorphisms becomes inversion after forgetting to based functors.
  rfl

/-- Helper for Chap08 Lemma 8 8 5: strict associator components are identity morphisms after
forgetting owner morphisms to based functors. -/
private theorem basedFunctorIsoOfOwnerIso_associator_hom_app
    {A B D E : FibredCategoryOver C}
    (F : A ⟶ B) (G : B ⟶ D) (H : D ⟶ E) (P : A.S) :
    (FibredCategoryMor.basedFunctorIsoOfOwnerIso (α_ F G H)).hom.app P = 𝟙 _ := by
  -- The ambient bicategory of fibred categories is strict, so the associator is an equality
  -- isomorphism whose component is the identity.
  rw [Bicategory.Strict.associator_eqToIso F G H]
  rfl

/-- Helper for Chap08 Lemma 8 8 5: strict inverse associator components are also identities after
forgetting owner morphisms to based functors. -/
private theorem basedFunctorIsoOfOwnerIso_associator_symm_hom_app
    {A B D E : FibredCategoryOver C}
    (F : A ⟶ B) (G : B ⟶ D) (H : D ⟶ E) (P : A.S) :
    (FibredCategoryMor.basedFunctorIsoOfOwnerIso (α_ F G H).symm).hom.app P = 𝟙 _ := by
  -- This is the inverse component of the preceding strict associator equality.
  rw [Bicategory.Strict.associator_eqToIso F G H]
  rfl

/-- Helper for Chap08 Lemma 8 8 5: inverse strict associator components are identities after
forgetting owner morphisms to based functors. -/
private theorem basedFunctorIsoOfOwnerIso_associator_inv_app
    {A B D E : FibredCategoryOver C}
    (F : A ⟶ B) (G : B ⟶ D) (H : D ⟶ E) (P : A.S) :
    (FibredCategoryMor.basedFunctorIsoOfOwnerIso (α_ F G H)).inv.app P = 𝟙 _ := by
  -- The inverse of a strict associator is still an identity component.
  rw [Bicategory.Strict.associator_eqToIso F G H]
  rfl

/-- Helper for Chap08 Lemma 8 8 5: left-whiskering an owner isomorphism evaluates at the image of
the whiskering morphism. -/
private theorem basedFunctorIsoOfOwnerIso_whiskerLeft_hom_app
    {A B D : FibredCategoryOver C} (L : A ⟶ B) {F G : B ⟶ D}
    (α : F ≅ G) (P : A.S) :
    (FibredCategoryMor.basedFunctorIsoOfOwnerIso (whiskerLeftIso L α)).hom.app P =
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso α).hom.app
        ((FibredCategoryMor.toFunctor L).obj P) := by
  -- Whiskering only precomposes the natural isomorphism by the left morphism.
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the canonical pullback square stores exactly the explicit
two-fibre-product comparison morphism. -/
private theorem twoFibreProductSquare_comparison_hom_app
    {A B S : FibredCategoryOver C} (F : A ⟶ S) (G : B ⟶ S)
    (P : (twoFibreProduct F G).S) :
    (FibredCategoryMor.basedFunctorIsoOfOwnerIso (twoFibreProductSquare F G).ψ).hom.app P =
      P.comparison := by
  -- This is the comparison isomorphism used in the explicit pullback object.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the direct endpoint-replacement map from the middle-replaced
two-fibre product to the target two-fibre product. -/
private noncomputable def twoFibreProductEndpointReplacementDirectHom
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j) :
    FibredCategoryMor (twoFibreProduct (f ≫ j) (g ≫ j))
      (twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor) :=
  -- Route correction: use the public terminal lift directly rather than a fresh raw terminal
  -- object in the hom-category.
  let P := twoFibreProductEndpointReplacementDirectSquare f g i j k f' g' α β
  (twoFibreProduct_terminalLift f'.toFibredCategoryMor g'.toFibredCategoryMor P).hom

/-- Helper for Chap08 Lemma 8 8 5: the direct endpoint replacement stores the source
comparison conjugated by the endpoint owner isomorphisms. -/
private theorem twoFibreProductEndpointReplacementDirectHom_obj_comparison
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    (P : (twoFibreProduct (f ≫ j) (g ≫ j)).S) :
    ((FibredCategoryMor.toFunctor
      (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β)).obj P).comparison =
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso α).hom.app P.obj.fst.1 ≫
        P.comparison ≫
          (FibredCategoryMor.basedFunctorIsoOfOwnerIso β).inv.app P.obj.snd.1 := by
  -- Unfold only the endpoint terminal lift; its comparison field is the transported square
  -- component used to build the lifted endpoint object.
  change (FibredCategoryMor.basedFunctorIsoOfOwnerIso
      (twoFibreProductEndpointReplacementDirectSquare f g i j k f' g' α β).ψ).hom.app P =
    (FibredCategoryMor.basedFunctorIsoOfOwnerIso α).hom.app P.obj.fst.1 ≫
      P.comparison ≫
        (FibredCategoryMor.basedFunctorIsoOfOwnerIso β).inv.app P.obj.snd.1
  unfold twoFibreProductEndpointReplacementDirectSquare
  simp only [NatTrans.comp_app, basedFunctorIsoOfOwnerIso_trans_hom_app,
    basedFunctorIsoOfOwnerIso_associator_hom_app,
    basedFunctorIsoOfOwnerIso_associator_symm_hom_app,
    basedFunctorIsoOfOwnerIso_associator_inv_app,
    basedFunctorIsoOfOwnerIso_whiskerLeft_hom_app,
    basedFunctorIsoOfOwnerIso_symm_hom_app,
    twoFibreProductSquare_comparison_hom_app, Category.id_comp, Category.comp_id]
  have hψ :
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso
          (twoFibreProductSquare (f ≫ j) (g ≫ j)).ψ).hom.app P =
        P.comparison :=
    twoFibreProductSquare_comparison_hom_app (f ≫ j) (g ≫ j) P
  have hβ :
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso
          (twoFibreProductRightProjection (f ≫ j) (g ≫ j) ◁ᵢ β.symm)).hom.app P =
        (FibredCategoryMor.basedFunctorIsoOfOwnerIso β).inv.app P.obj.snd.1 := by
    -- The right whisker evaluates at the right endpoint of the explicit pullback object.
    simpa only [basedFunctorIsoOfOwnerIso_symm_hom_app] using
      basedFunctorIsoOfOwnerIso_whiskerLeft_hom_app
        (twoFibreProductRightProjection (f ≫ j) (g ≫ j)) β.symm P
  -- Finally remove the identity associator components and rewrite the middle comparison and the
  -- right endpoint whisker to their concrete forms.
  erw [Category.id_comp, Category.comp_id, hψ, hβ]
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the direct endpoint-replacement map sends the left endpoint
object through the left stackification morphism. -/
private theorem twoFibreProductEndpointReplacementDirectHom_obj_fst
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    (P : (twoFibreProduct (f ≫ j) (g ≫ j)).S) :
    ((FibredCategoryMor.toFunctor
      (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β)).obj P).obj.fst.1 =
      (FibredCategoryMor.toFunctor i).obj P.obj.fst.1 := by
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the direct endpoint-replacement map sends the right endpoint
object through the right stackification morphism. -/
private theorem twoFibreProductEndpointReplacementDirectHom_obj_snd
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    (P : (twoFibreProduct (f ≫ j) (g ≫ j)).S) :
    ((FibredCategoryMor.toFunctor
      (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β)).obj P).obj.snd.1 =
      (FibredCategoryMor.toFunctor k).obj P.obj.snd.1 := by
  rfl

/-- Helper for Chap08 Lemma 8 8 4: on morphisms, direct endpoint replacement maps the left
component through the left stackification morphism. -/
private theorem twoFibreProductEndpointReplacementDirectHom_map_a
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    {P Q : (twoFibreProduct (f ≫ j) (g ≫ j)).S}
    (φ : P ⟶ Q) :
    ((FibredCategoryMor.toFunctor
      (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β)).map φ).a =
      (FibredCategoryMor.toFunctor i).map φ.a := by
  rfl

/-- Helper for Chap08 Lemma 8 8 4: on morphisms, direct endpoint replacement maps the right
component through the right stackification morphism. -/
private theorem twoFibreProductEndpointReplacementDirectHom_map_b
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    {P Q : (twoFibreProduct (f ≫ j) (g ≫ j)).S}
    (φ : P ⟶ Q) :
    ((FibredCategoryMor.toFunctor
      (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β)).map φ).b =
      (FibredCategoryMor.toFunctor k).map φ.b := by
  rfl

/-- Helper for Chap08 Lemma 8 8 4: if two endpoint component maps lift the components of a
target morphism under the direct endpoint replacement, then they satisfy the source
two-fibre-product commutativity relation. -/
private theorem twoFibreProductEndpointReplacementDirectHom_preimage_comm
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    {U : C} {P Q : (twoFibreProduct (f ≫ j) (g ≫ j)).p.Fiber U}
    (τ : ((FibredCategoryMor.fiberFunctor
        (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) U).obj P) ⟶
      ((FibredCategoryMor.fiberFunctor
        (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) U).obj Q))
    (a : P.1.obj.fst.1 ⟶ Q.1.obj.fst.1)
    (b : P.1.obj.snd.1 ⟶ Q.1.obj.snd.1)
    (ha : (FibredCategoryMor.toFunctor i).map a = τ.1.a)
    (hb : (FibredCategoryMor.toFunctor k).map b = τ.1.b) :
    (FibredCategoryMor.toFunctor (f ≫ j)).map a ≫ Q.1.comparison =
      P.1.comparison ≫ (FibredCategoryMor.toFunctor (g ≫ j)).map b := by
  let E := twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β
  let αb := FibredCategoryMor.basedFunctorIsoOfOwnerIso α
  let βb := FibredCategoryMor.basedFunctorIsoOfOwnerIso β
  have hτ := τ.1.comm.w
  change
    (FibredCategoryMor.toFunctor f'.toFibredCategoryMor).map τ.1.a ≫
        ((FibredCategoryMor.toFunctor E).obj Q.1).comparison =
      ((FibredCategoryMor.toFunctor E).obj P.1).comparison ≫
        (FibredCategoryMor.toFunctor g'.toFibredCategoryMor).map τ.1.b at hτ
  rw [← ha, ← hb] at hτ
  rw [twoFibreProductEndpointReplacementDirectHom_obj_comparison,
    twoFibreProductEndpointReplacementDirectHom_obj_comparison] at hτ
  have hαnat :
      (FibredCategoryMor.toFunctor f'.toFibredCategoryMor).map
            ((FibredCategoryMor.toFunctor i).map a) ≫
          αb.hom.app Q.1.obj.fst.1 =
        αb.hom.app P.1.obj.fst.1 ≫
          (FibredCategoryMor.toFunctor (f ≫ j)).map a := by
    exact αb.hom.toNatTrans.naturality a
  have hβnat :
      (FibredCategoryMor.toFunctor g'.toFibredCategoryMor).map
            ((FibredCategoryMor.toFunctor k).map b) ≫
          βb.hom.app Q.1.obj.snd.1 =
        βb.hom.app P.1.obj.snd.1 ≫
          (FibredCategoryMor.toFunctor (g ≫ j)).map b := by
    exact βb.hom.toNatTrans.naturality b
  have hβinv :
      βb.inv.app P.1.obj.snd.1 ≫
          (FibredCategoryMor.toFunctor g'.toFibredCategoryMor).map
            ((FibredCategoryMor.toFunctor k).map b) =
        (FibredCategoryMor.toFunctor (g ≫ j)).map b ≫
          βb.inv.app Q.1.obj.snd.1 := by
    let βP := βb.hom.app P.1.obj.snd.1
    let βQ := βb.hom.app Q.1.obj.snd.1
    let βPi := βb.inv.app P.1.obj.snd.1
    let βQi := βb.inv.app Q.1.obj.snd.1
    let Gmap :=
      (FibredCategoryMor.toFunctor g'.toFibredCategoryMor).map
        ((FibredCategoryMor.toFunctor k).map b)
    let rhs := (FibredCategoryMor.toFunctor (g ≫ j)).map b
    have hβnat' : Gmap ≫ βQ = βP ≫ rhs := hβnat
    have hβQCancel : βQ ≫ βQi = 𝟙 _ := by
      change βb.hom.app Q.1.obj.snd.1 ≫ βb.inv.app Q.1.obj.snd.1 = 𝟙 _
      exact congrArg (fun eta => eta.app Q.1.obj.snd.1) βb.hom_inv_id
    have hβPCancel : βPi ≫ βP = 𝟙 _ := by
      change βb.inv.app P.1.obj.snd.1 ≫ βb.hom.app P.1.obj.snd.1 = 𝟙 _
      exact congrArg (fun eta => eta.app P.1.obj.snd.1) βb.inv_hom_id
    calc
      βPi ≫ Gmap = (βPi ≫ Gmap) ≫ 𝟙 _ := by
        rw [Category.comp_id]
      _ = (βPi ≫ Gmap) ≫ (βQ ≫ βQi) := by
        exact congrArg (fun t => (βPi ≫ Gmap) ≫ t) hβQCancel.symm
      _ = βPi ≫ (Gmap ≫ βQ) ≫ βQi := by
        simp only [Category.assoc]
      _ = βPi ≫ (βP ≫ rhs) ≫ βQi := by
        exact congrArg (fun t => βPi ≫ t ≫ βQi) hβnat'
      _ = (βPi ≫ βP) ≫ rhs ≫ βQi := by
        simp only [Category.assoc]
      _ = rhs ≫ βQi := by
        rw [hβPCancel]
        simp only [Category.id_comp]
  apply (cancel_epi (αb.hom.app P.1.obj.fst.1)).1
  apply (cancel_mono (βb.inv.app Q.1.obj.snd.1)).1
  simp only [Category.assoc]
  slice_lhs 1 2 => rw [← hαnat]
  have hassocLeft :
      (((FibredCategoryMor.toFunctor f'.toFibredCategoryMor).map
            ((FibredCategoryMor.toFunctor i).map a) ≫
          αb.hom.app Q.1.obj.fst.1) ≫ Q.1.comparison) ≫
          βb.inv.app Q.1.obj.snd.1 =
        (FibredCategoryMor.toFunctor f'.toFibredCategoryMor).map
            ((FibredCategoryMor.toFunctor i).map a) ≫
          αb.hom.app Q.1.obj.fst.1 ≫ Q.1.comparison ≫
            βb.inv.app Q.1.obj.snd.1 := by
    simp only [Category.assoc]
  have hright :
      (αb.hom.app P.1.obj.fst.1 ≫
        P.1.comparison ≫ βb.inv.app P.1.obj.snd.1) ≫
        (FibredCategoryMor.toFunctor g'.toFibredCategoryMor).map
          ((FibredCategoryMor.toFunctor k).map b) =
      αb.hom.app P.1.obj.fst.1 ≫ P.1.comparison ≫
        (FibredCategoryMor.toFunctor (g ≫ j)).map b ≫
          βb.inv.app Q.1.obj.snd.1 := by
    simp only [Category.assoc]
    slice_lhs 3 4 => rw [hβinv]
    rfl
  exact hassocLeft.trans (hτ.trans hright)

/-- Helper for Chap08 Lemma 8 8 4: the direct endpoint-replacement map carries a left projection
comparison to the middle left projection followed by `i`. -/
private noncomputable def twoFibreProductEndpointReplacementDirectHom_leftProjection
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j) :
    twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β ≫
        twoFibreProductLeftProjection f'.toFibredCategoryMor g'.toFibredCategoryMor ⟶
      twoFibreProductLeftProjection (f ≫ j) (g ≫ j) ≫ i :=
  -- Read the left endpoint comparison from the public terminal-lift package.
  let P := twoFibreProductEndpointReplacementDirectSquare f g i j k f' g' α β
  (twoFibreProduct_terminalLift f'.toFibredCategoryMor g'.toFibredCategoryMor P).left

/-- Helper for Chap08 Lemma 8 8 4: the direct endpoint-replacement map carries a right projection
comparison to the middle right projection followed by `k`. -/
private noncomputable def twoFibreProductEndpointReplacementDirectHom_rightProjection
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j) :
    twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β ≫
        twoFibreProductRightProjection f'.toFibredCategoryMor g'.toFibredCategoryMor ⟶
      twoFibreProductRightProjection (f ≫ j) (g ≫ j) ≫ k :=
  -- This is the symmetric projection comparison extracted from the same public terminal lift.
  let P := twoFibreProductEndpointReplacementDirectSquare f g i j k f' g' α β
  (twoFibreProduct_terminalLift f'.toFibredCategoryMor g'.toFibredCategoryMor P).right

/-- Helper for Chap08 Lemma 8 8 4: after projecting to the left endpoint, the Hom-presheaf map
of the direct endpoint replacement is the Hom-presheaf map of `i`. -/
private theorem twoFibreProductEndpointReplacementDirectHom_presheaf_left_app
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    [(twoFibreProduct (f ≫ j) (g ≫ j)).p.IsFibered]
    {U : C} (P Q : (twoFibreProduct (f ≫ j) (g ≫ j)).p.Fiber U)
    (W : (Over U)ᵒᵖ)
    (φ : ((canonicalFiberPseudofunctor
      (twoFibreProduct (f ≫ j) (g ≫ j)).p).presheafHom P Q).obj W) :
    (FibredCategoryMor.fibredMorphismPresheafMap i
        ((FibredCategoryMor.fiberFunctor
          (twoFibreProductLeftProjection (f ≫ j) (g ≫ j)) U).obj P)
        ((FibredCategoryMor.fiberFunctor
          (twoFibreProductLeftProjection (f ≫ j) (g ≫ j)) U).obj Q)).app W
      ((FibredCategoryMor.fibredMorphismPresheafMap
        (twoFibreProductLeftProjection (f ≫ j) (g ≫ j)) P Q).app W φ) =
    (FibredCategoryMor.fibredMorphismPresheafMap
        (twoFibreProductLeftProjection f'.toFibredCategoryMor g'.toFibredCategoryMor)
        ((FibredCategoryMor.fiberFunctor
          (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) U).obj P)
        ((FibredCategoryMor.fiberFunctor
          (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) U).obj Q)).app W
      ((FibredCategoryMor.fibredMorphismPresheafMap
        (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) P Q).app W φ) := by
  change
    ((FibredCategoryMor.fibredMorphismPresheafMap
          (twoFibreProductLeftProjection (f ≫ j) (g ≫ j)) P Q ≫
        FibredCategoryMor.fibredMorphismPresheafMap i
          ((FibredCategoryMor.fiberFunctor
            (twoFibreProductLeftProjection (f ≫ j) (g ≫ j)) U).obj P)
          ((FibredCategoryMor.fiberFunctor
            (twoFibreProductLeftProjection (f ≫ j) (g ≫ j)) U).obj Q)).app W φ) =
      ((FibredCategoryMor.fibredMorphismPresheafMap
          (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) P Q ≫
        FibredCategoryMor.fibredMorphismPresheafMap
          (twoFibreProductLeftProjection f'.toFibredCategoryMor g'.toFibredCategoryMor)
          ((FibredCategoryMor.fiberFunctor
            (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) U).obj P)
          ((FibredCategoryMor.fiberFunctor
            (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) U).obj Q)).app W φ)
  rw [← fibredMorphismPresheafMap_comp
    (twoFibreProductLeftProjection (f ≫ j) (g ≫ j)) i P Q]
  rw [← fibredMorphismPresheafMap_comp
    (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β)
    (twoFibreProductLeftProjection f'.toFibredCategoryMor g'.toFibredCategoryMor) P Q]
  rfl

/-- Helper for Chap08 Lemma 8 8 4: after projecting to the right endpoint, the Hom-presheaf map
of the direct endpoint replacement is the Hom-presheaf map of `k`. -/
private theorem twoFibreProductEndpointReplacementDirectHom_presheaf_right_app
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    [(twoFibreProduct (f ≫ j) (g ≫ j)).p.IsFibered]
    {U : C} (P Q : (twoFibreProduct (f ≫ j) (g ≫ j)).p.Fiber U)
    (W : (Over U)ᵒᵖ)
    (φ : ((canonicalFiberPseudofunctor
      (twoFibreProduct (f ≫ j) (g ≫ j)).p).presheafHom P Q).obj W) :
    (FibredCategoryMor.fibredMorphismPresheafMap k
        ((FibredCategoryMor.fiberFunctor
          (twoFibreProductRightProjection (f ≫ j) (g ≫ j)) U).obj P)
        ((FibredCategoryMor.fiberFunctor
          (twoFibreProductRightProjection (f ≫ j) (g ≫ j)) U).obj Q)).app W
      ((FibredCategoryMor.fibredMorphismPresheafMap
        (twoFibreProductRightProjection (f ≫ j) (g ≫ j)) P Q).app W φ) =
    (FibredCategoryMor.fibredMorphismPresheafMap
        (twoFibreProductRightProjection f'.toFibredCategoryMor g'.toFibredCategoryMor)
        ((FibredCategoryMor.fiberFunctor
          (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) U).obj P)
        ((FibredCategoryMor.fiberFunctor
          (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) U).obj Q)).app W
      ((FibredCategoryMor.fibredMorphismPresheafMap
        (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) P Q).app W φ) := by
  change
    ((FibredCategoryMor.fibredMorphismPresheafMap
          (twoFibreProductRightProjection (f ≫ j) (g ≫ j)) P Q ≫
        FibredCategoryMor.fibredMorphismPresheafMap k
          ((FibredCategoryMor.fiberFunctor
            (twoFibreProductRightProjection (f ≫ j) (g ≫ j)) U).obj P)
          ((FibredCategoryMor.fiberFunctor
            (twoFibreProductRightProjection (f ≫ j) (g ≫ j)) U).obj Q)).app W φ) =
      ((FibredCategoryMor.fibredMorphismPresheafMap
          (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) P Q ≫
        FibredCategoryMor.fibredMorphismPresheafMap
          (twoFibreProductRightProjection f'.toFibredCategoryMor g'.toFibredCategoryMor)
          ((FibredCategoryMor.fiberFunctor
            (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) U).obj P)
          ((FibredCategoryMor.fiberFunctor
            (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) U).obj Q)).app W φ)
  rw [← fibredMorphismPresheafMap_comp
    (twoFibreProductRightProjection (f ≫ j) (g ≫ j)) k P Q]
  rw [← fibredMorphismPresheafMap_comp
    (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β)
    (twoFibreProductRightProjection f'.toFibredCategoryMor g'.toFibredCategoryMor) P Q]
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the Hom-presheaf map of the direct endpoint replacement is
locally injective, because equality can be tested on the two endpoint projections and `i`, `k`
are locally injective on Hom presheaves. -/
private theorem twoFibreProductEndpointReplacementDirectHom_presheafMap_isLocallyInjective
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    (hi : FibredCategoryMor.IsStackification i)
    (hk : FibredCategoryMor.IsStackification k)
    {U : C} (P Q : (twoFibreProduct (f ≫ j) (g ≫ j)).p.Fiber U) :
    Presheaf.IsLocallyInjective (J.over U)
      (FibredCategoryMor.fibredMorphismPresheafMap
        (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) P Q) := by
  classical
  let E := twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β
  let L := twoFibreProductLeftProjection (f ≫ j) (g ≫ j)
  let R := twoFibreProductRightProjection (f ≫ j) (g ≫ j)
  let L' := twoFibreProductLeftProjection f'.toFibredCategoryMor g'.toFibredCategoryMor
  let R' := twoFibreProductRightProjection f'.toFibredCategoryMor g'.toFibredCategoryMor
  let eta := FibredCategoryMor.fibredMorphismPresheafMap E P Q
  let lMap := FibredCategoryMor.fibredMorphismPresheafMap L P Q
  let rMap := FibredCategoryMor.fibredMorphismPresheafMap R P Q
  let thetaI := FibredCategoryMor.fibredMorphismPresheafMap i
    ((FibredCategoryMor.fiberFunctor L U).obj P)
    ((FibredCategoryMor.fiberFunctor L U).obj Q)
  let thetaK := FibredCategoryMor.fibredMorphismPresheafMap k
    ((FibredCategoryMor.fiberFunctor R U).obj P)
    ((FibredCategoryMor.fiberFunctor R U).obj Q)
  letI : (twoFibreProduct (f ≫ j) (g ≫ j)).p.IsFibered :=
    FibredCategoryOver.isFibred (twoFibreProduct (f ≫ j) (g ≫ j))
  haveI : (J.over U).WEqualsLocallyBijective (Type v) :=
    over_WEqualsLocallyBijective_small (J := J) U
  haveI : Presheaf.IsLocallyInjective (J.over U) thetaI :=
    (hi.morphismPresheafMap_W U
      ((FibredCategoryMor.fiberFunctor L U).obj P)
      ((FibredCategoryMor.fiberFunctor L U).obj Q) : (J.over U).W thetaI).isLocallyInjective
  haveI : Presheaf.IsLocallyInjective (J.over U) thetaK :=
    (hk.morphismPresheafMap_W U
      ((FibredCategoryMor.fiberFunctor R U).obj P)
      ((FibredCategoryMor.fiberFunctor R U).obj Q) : (J.over U).W thetaK).isLocallyInjective
  constructor
  intro T φ ψ hφψ
  have hleftImage : thetaI.app T (lMap.app T φ) = thetaI.app T (lMap.app T ψ) := by
    have hleftφ :=
      twoFibreProductEndpointReplacementDirectHom_presheaf_left_app
        (J := J) f g i j k f' g' α β P Q T φ
    have hleftψ :=
      twoFibreProductEndpointReplacementDirectHom_presheaf_left_app
        (J := J) f g i j k f' g' α β P Q T ψ
    have hη : eta.app T φ = eta.app T ψ := by
      simpa only [eta] using hφψ
    have hmiddle :
        (FibredCategoryMor.fibredMorphismPresheafMap L'
          ((FibredCategoryMor.fiberFunctor E U).obj P)
          ((FibredCategoryMor.fiberFunctor E U).obj Q)).app T (eta.app T φ) =
        (FibredCategoryMor.fibredMorphismPresheafMap L'
          ((FibredCategoryMor.fiberFunctor E U).obj P)
          ((FibredCategoryMor.fiberFunctor E U).obj Q)).app T (eta.app T ψ) :=
      congrArg
        ((FibredCategoryMor.fibredMorphismPresheafMap L'
          ((FibredCategoryMor.fiberFunctor E U).obj P)
          ((FibredCategoryMor.fiberFunctor E U).obj Q)).app T)
        hη
    exact hleftφ.trans (hmiddle.trans hleftψ.symm)
  have hrightImage : thetaK.app T (rMap.app T φ) = thetaK.app T (rMap.app T ψ) := by
    have hrightφ :=
      twoFibreProductEndpointReplacementDirectHom_presheaf_right_app
        (J := J) f g i j k f' g' α β P Q T φ
    have hrightψ :=
      twoFibreProductEndpointReplacementDirectHom_presheaf_right_app
        (J := J) f g i j k f' g' α β P Q T ψ
    have hη : eta.app T φ = eta.app T ψ := by
      simpa only [eta] using hφψ
    have hmiddle :
        (FibredCategoryMor.fibredMorphismPresheafMap R'
          ((FibredCategoryMor.fiberFunctor E U).obj P)
          ((FibredCategoryMor.fiberFunctor E U).obj Q)).app T (eta.app T φ) =
        (FibredCategoryMor.fibredMorphismPresheafMap R'
          ((FibredCategoryMor.fiberFunctor E U).obj P)
          ((FibredCategoryMor.fiberFunctor E U).obj Q)).app T (eta.app T ψ) :=
      congrArg
        ((FibredCategoryMor.fibredMorphismPresheafMap R'
          ((FibredCategoryMor.fiberFunctor E U).obj P)
          ((FibredCategoryMor.fiberFunctor E U).obj Q)).app T)
        hη
    exact hrightφ.trans (hmiddle.trans hrightψ.symm)
  let Fleft :=
    (canonicalFiberPseudofunctor X.p).presheafHom
      ((FibredCategoryMor.fiberFunctor L U).obj P)
      ((FibredCategoryMor.fiberFunctor L U).obj Q)
  let Fright :=
    (canonicalFiberPseudofunctor Z.p).presheafHom
      ((FibredCategoryMor.fiberFunctor R U).obj P)
      ((FibredCategoryMor.fiberFunctor R U).obj Q)
  have hleftS :=
    Presheaf.equalizerSieve_mem (J.over U) thetaI (lMap.app T φ) (lMap.app T ψ) hleftImage
  have hrightS :=
    Presheaf.equalizerSieve_mem (J.over U) thetaK (rMap.app T φ) (rMap.app T ψ) hrightImage
  have hintersection :
      Presheaf.equalizerSieve (F := Fleft) (lMap.app T φ) (lMap.app T ψ) ⊓
          Presheaf.equalizerSieve (F := Fright) (rMap.app T φ) (rMap.app T ψ) ∈
        (J.over U) T.unop := by
    exact
      (J.over U).intersection_covering
        (R := Presheaf.equalizerSieve (F := Fleft) (lMap.app T φ) (lMap.app T ψ))
        (S := Presheaf.equalizerSieve (F := Fright) (rMap.app T φ) (rMap.app T ψ))
        hleftS hrightS
  refine (J.over U).superset_covering
    (S := Presheaf.equalizerSieve (F := Fleft) (lMap.app T φ) (lMap.app T ψ) ⊓
      Presheaf.equalizerSieve (F := Fright) (rMap.app T φ) (rMap.app T ψ)) ?_
    hintersection
  intro V hV hVmem
  change
    (((canonicalFiberPseudofunctor (twoFibreProduct (f ≫ j) (g ≫ j)).p).presheafHom
      P Q).map hV.op φ) =
      (((canonicalFiberPseudofunctor (twoFibreProduct (f ≫ j) (g ≫ j)).p).presheafHom
        P Q).map hV.op ψ)
  apply twoFibreProduct_presheafHom_ext (f ≫ j) (g ≫ j) P Q (Opposite.op V)
  · calc
      lMap.app (Opposite.op V)
          (((canonicalFiberPseudofunctor (twoFibreProduct (f ≫ j) (g ≫ j)).p).presheafHom
            P Q).map hV.op φ) =
        (((canonicalFiberPseudofunctor X.p).presheafHom
          ((FibredCategoryMor.fiberFunctor L U).obj P)
          ((FibredCategoryMor.fiberFunctor L U).obj Q)).map hV.op) (lMap.app T φ) := by
          exact NatTrans.naturality_apply lMap hV.op φ
      _ =
        (((canonicalFiberPseudofunctor X.p).presheafHom
          ((FibredCategoryMor.fiberFunctor L U).obj P)
          ((FibredCategoryMor.fiberFunctor L U).obj Q)).map hV.op) (lMap.app T ψ) := by
          simpa only [Fleft, Presheaf.equalizerSieve] using hVmem.1
      _ =
        lMap.app (Opposite.op V)
          (((canonicalFiberPseudofunctor (twoFibreProduct (f ≫ j) (g ≫ j)).p).presheafHom
            P Q).map hV.op ψ) := by
          exact (NatTrans.naturality_apply lMap hV.op ψ).symm
  · calc
      rMap.app (Opposite.op V)
          (((canonicalFiberPseudofunctor (twoFibreProduct (f ≫ j) (g ≫ j)).p).presheafHom
            P Q).map hV.op φ) =
        (((canonicalFiberPseudofunctor Z.p).presheafHom
          ((FibredCategoryMor.fiberFunctor R U).obj P)
          ((FibredCategoryMor.fiberFunctor R U).obj Q)).map hV.op) (rMap.app T φ) := by
          exact NatTrans.naturality_apply rMap hV.op φ
      _ =
        (((canonicalFiberPseudofunctor Z.p).presheafHom
          ((FibredCategoryMor.fiberFunctor R U).obj P)
          ((FibredCategoryMor.fiberFunctor R U).obj Q)).map hV.op) (rMap.app T ψ) := by
          simpa only [Fright, Presheaf.equalizerSieve] using hVmem.2
      _ =
        rMap.app (Opposite.op V)
          (((canonicalFiberPseudofunctor (twoFibreProduct (f ≫ j) (g ≫ j)).p).presheafHom
            P Q).map hV.op ψ) := by
          exact (NatTrans.naturality_apply rMap hV.op ψ).symm

/-- Helper for Chap08 Lemma 8 8 4: a local lift through the left endpoint stackification gives
the left component of the direct endpoint-replacement preimage. -/
private theorem twoFibreProductEndpointReplacementDirectHom_local_left_component
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    {U : C} (P Q : (twoFibreProduct (f ≫ j) (g ≫ j)).p.Fiber U)
    (V : Over U)
    (sV :
      ((canonicalFiberPseudofunctor
        (twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor).p).presheafHom
          ((FibredCategoryMor.fiberFunctor
            (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) U).obj P)
          ((FibredCategoryMor.fiberFunctor
            (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) U).obj Q)).obj
        (Opposite.op V))
    (aSec :
      ((canonicalFiberPseudofunctor X.p).presheafHom
        ((FibredCategoryMor.fiberFunctor
          (twoFibreProductLeftProjection (f ≫ j) (g ≫ j)) U).obj P)
        ((FibredCategoryMor.fiberFunctor
          (twoFibreProductLeftProjection (f ≫ j) (g ≫ j)) U).obj Q)).obj
        (Opposite.op V))
    (haSec :
      (FibredCategoryMor.fibredMorphismPresheafMap i
        ((FibredCategoryMor.fiberFunctor
          (twoFibreProductLeftProjection (f ≫ j) (g ≫ j)) U).obj P)
        ((FibredCategoryMor.fiberFunctor
          (twoFibreProductLeftProjection (f ≫ j) (g ≫ j)) U).obj Q)).app
          (Opposite.op V) aSec =
        (FibredCategoryMor.fibredMorphismPresheafMap
          (twoFibreProductLeftProjection f'.toFibredCategoryMor g'.toFibredCategoryMor)
          ((FibredCategoryMor.fiberFunctor
            (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) U).obj P)
          ((FibredCategoryMor.fiberFunctor
            (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) U).obj Q)).app
            (Opposite.op V) sV) :
    (FibredCategoryMor.toFunctor i).map
        (((FibredCategoryMor.pullbackComparison
          (twoFibreProductLeftProjection (f ≫ j) (g ≫ j)) V.hom P).inv ≫
          aSec ≫
          (FibredCategoryMor.pullbackComparison
            (twoFibreProductLeftProjection (f ≫ j) (g ≫ j)) V.hom Q).hom).1) =
      (((FibredCategoryMor.pullbackComparison
          (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) V.hom P).inv ≫
          sV ≫
          (FibredCategoryMor.pullbackComparison
            (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) V.hom Q).hom).1).a := by
  classical
  let E := twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β
  let L := twoFibreProductLeftProjection (f ≫ j) (g ≫ j)
  let L' := twoFibreProductLeftProjection f'.toFibredCategoryMor g'.toFibredCategoryMor
  let eP := FibredCategoryMor.pullbackComparison E V.hom P
  let eQ := FibredCategoryMor.pullbackComparison E V.hom Q
  let tau := eP.inv ≫ sV ≫ eQ.hom
  let eLP := FibredCategoryMor.pullbackComparison L V.hom P
  let eLQ := FibredCategoryMor.pullbackComparison L V.hom Q
  let aFiber := eLP.inv ≫ aSec ≫ eLQ.hom
  change (FibredCategoryMor.toFunctor i).map aFiber.1 = tau.1.a
  let lhs := (FibredCategoryMor.fiberFunctor i V.left).map aFiber
  let rhs := (FibredCategoryMor.fiberFunctor L' V.left).map tau
  have haFiber : lhs = rhs := by
    let Fi := FibredCategoryMor.fiberFunctor i V.left
    let eiP := FibredCategoryMor.pullbackComparison i V.hom
      ((FibredCategoryMor.fiberFunctor L U).obj P)
    let eiQ := FibredCategoryMor.pullbackComparison i V.hom
      ((FibredCategoryMor.fiberFunctor L U).obj Q)
    let eCompP := FibredCategoryMor.pullbackComparison (L ≫ i) V.hom P
    let eCompQ := FibredCategoryMor.pullbackComparison (L ≫ i) V.hom Q
    let leftMap := FibredCategoryMor.fibredMorphismPresheafMap L'
      ((FibredCategoryMor.fiberFunctor E U).obj P)
      ((FibredCategoryMor.fiberFunctor E U).obj Q)
    have hleftShell :
        (eCompP.hom ≫ Fi.map aFiber) ≫ eCompQ.inv =
          (FibredCategoryMor.fibredMorphismPresheafMap i
            ((FibredCategoryMor.fiberFunctor L U).obj P)
            ((FibredCategoryMor.fiberFunctor L U).obj Q)).app (Opposite.op V) aSec := by
      have hcancel :=
        functor_map_iso_conjugate_cancel Fi eLP eLQ aSec
      have hraw :
          eiP.hom ≫ (Fi.map eLP.hom ≫ Fi.map aFiber ≫ Fi.map eLQ.inv) ≫
              eiQ.inv =
            eiP.hom ≫ Fi.map aSec ≫ eiQ.inv := by
        simpa only [aFiber] using
          congrArg (fun m => eiP.hom ≫ m ≫ eiQ.inv) hcancel
      have hconj :
          ((eiP.hom ≫ Fi.map eLP.hom) ≫ Fi.map aFiber) ≫
              Fi.map eLQ.inv ≫ eiQ.inv =
            eiP.hom ≫ Fi.map aSec ≫ eiQ.inv := by
        simpa only [Category.assoc] using hraw
      simpa only [Fi, eiP, eiQ, eCompP, eCompQ, eLP, eLQ,
        aFiber, L, E,
        fibredMorphismPresheafMap_app_pullbackComparison,
        FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
        twoFibreProduct_leftProjection_map_underlying,
        fiberHom_comp_underlying,
        pullbackComparison_comp_hom, pullbackComparison_comp_inv] using hconj
    have hrightShell :
        (eCompP.hom ≫ (FibredCategoryMor.fiberFunctor L' V.left).map tau) ≫
            eCompQ.inv =
          leftMap.app (Opposite.op V) sV := by
      let FL' := FibredCategoryMor.fiberFunctor L' V.left
      let eL'P := FibredCategoryMor.pullbackComparison L' V.hom
        ((FibredCategoryMor.fiberFunctor E U).obj P)
      let eL'Q := FibredCategoryMor.pullbackComparison L' V.hom
        ((FibredCategoryMor.fiberFunctor E U).obj Q)
      have hcancel :=
        functor_map_iso_conjugate_cancel FL' eP eQ sV
      have hCompHomP :
          eL'P.hom ≫ FL'.map eP.hom = eiP.hom ≫ Fi.map eLP.hom := by
        simpa only [Fi, FL', eL'P, eP, eiP, eLP, E, L, L',
          FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
          twoFibreProductEndpointReplacementDirectHom_obj_fst,
          twoFibreProductEndpointReplacementDirectHom_map_a,
          twoFibreProduct_leftProjection_map_underlying,
          pullbackComparison_comp_hom] using
          ((pullbackComparison_comp_hom E L' V.hom P).symm.trans
            (pullbackComparison_comp_hom L i V.hom P))
      have hCompInvQ :
          FL'.map eQ.inv ≫ eL'Q.inv = Fi.map eLQ.inv ≫ eiQ.inv := by
        simpa only [Fi, FL', eL'Q, eQ, eiQ, eLQ, E, L, L',
          FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
          twoFibreProductEndpointReplacementDirectHom_obj_fst,
          twoFibreProductEndpointReplacementDirectHom_map_a,
          twoFibreProduct_leftProjection_map_underlying,
          pullbackComparison_comp_inv] using
          ((pullbackComparison_comp_inv E L' V.hom Q).symm.trans
            (pullbackComparison_comp_inv L i V.hom Q))
      have hraw :
          eL'P.hom ≫ (FL'.map eP.hom ≫ FL'.map tau ≫ FL'.map eQ.inv) ≫
              eL'Q.inv =
            eL'P.hom ≫ FL'.map sV ≫ eL'Q.inv := by
        simpa only [tau] using
          congrArg (fun m => eL'P.hom ≫ m ≫ eL'Q.inv) hcancel
      have hconj :
          ((eL'P.hom ≫ FL'.map eP.hom) ≫ FL'.map tau) ≫
              FL'.map eQ.inv ≫ eL'Q.inv =
            eL'P.hom ≫ FL'.map sV ≫ eL'Q.inv := by
        simpa only [Category.assoc] using hraw
      rw [show eCompP.hom = eiP.hom ≫ Fi.map eLP.hom by
        simpa only [Fi, eiP, eLP, eCompP, L,
          FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor] using
          pullbackComparison_comp_hom L i V.hom P]
      rw [show eCompQ.inv = Fi.map eLQ.inv ≫ eiQ.inv by
        simpa only [Fi, eiQ, eLQ, eCompQ, L,
          FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor] using
          pullbackComparison_comp_inv L i V.hom Q]
      rw [← hCompHomP, ← hCompInvQ]
      simpa only [FL', eL'P, eL'Q, eP, eQ, leftMap, tau, L', E,
        fibredMorphismPresheafMap_app_pullbackComparison,
        FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor] using hconj
    have hshell :
        (eCompP.hom ≫ lhs) ≫ eCompQ.inv =
          (eCompP.hom ≫ rhs) ≫ eCompQ.inv := by
      exact hleftShell.trans (haSec.trans hrightShell.symm)
    exact iso_shell_cancel eCompP eCompQ hshell
  change lhs.1 = rhs.1
  exact congrArg Subtype.val haFiber

/-- Helper for Chap08 Lemma 8 8 4: a local lift through the right endpoint stackification gives
the right component of the direct endpoint-replacement preimage. -/
private theorem twoFibreProductEndpointReplacementDirectHom_local_right_component
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    {U : C} (P Q : (twoFibreProduct (f ≫ j) (g ≫ j)).p.Fiber U)
    (V : Over U)
    (sV :
      ((canonicalFiberPseudofunctor
        (twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor).p).presheafHom
          ((FibredCategoryMor.fiberFunctor
            (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) U).obj P)
          ((FibredCategoryMor.fiberFunctor
            (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) U).obj Q)).obj
        (Opposite.op V))
    (bSec :
      ((canonicalFiberPseudofunctor Z.p).presheafHom
        ((FibredCategoryMor.fiberFunctor
          (twoFibreProductRightProjection (f ≫ j) (g ≫ j)) U).obj P)
        ((FibredCategoryMor.fiberFunctor
          (twoFibreProductRightProjection (f ≫ j) (g ≫ j)) U).obj Q)).obj
        (Opposite.op V))
    (hbSec :
      (FibredCategoryMor.fibredMorphismPresheafMap k
        ((FibredCategoryMor.fiberFunctor
          (twoFibreProductRightProjection (f ≫ j) (g ≫ j)) U).obj P)
        ((FibredCategoryMor.fiberFunctor
          (twoFibreProductRightProjection (f ≫ j) (g ≫ j)) U).obj Q)).app
          (Opposite.op V) bSec =
        (FibredCategoryMor.fibredMorphismPresheafMap
          (twoFibreProductRightProjection f'.toFibredCategoryMor g'.toFibredCategoryMor)
          ((FibredCategoryMor.fiberFunctor
            (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) U).obj P)
          ((FibredCategoryMor.fiberFunctor
            (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) U).obj Q)).app
            (Opposite.op V) sV) :
    (FibredCategoryMor.toFunctor k).map
        (((FibredCategoryMor.pullbackComparison
          (twoFibreProductRightProjection (f ≫ j) (g ≫ j)) V.hom P).inv ≫
          bSec ≫
          (FibredCategoryMor.pullbackComparison
            (twoFibreProductRightProjection (f ≫ j) (g ≫ j)) V.hom Q).hom).1) =
      (((FibredCategoryMor.pullbackComparison
          (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) V.hom P).inv ≫
          sV ≫
          (FibredCategoryMor.pullbackComparison
            (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) V.hom Q).hom).1).b := by
  classical
  let E := twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β
  let R := twoFibreProductRightProjection (f ≫ j) (g ≫ j)
  let R' := twoFibreProductRightProjection f'.toFibredCategoryMor g'.toFibredCategoryMor
  let eP := FibredCategoryMor.pullbackComparison E V.hom P
  let eQ := FibredCategoryMor.pullbackComparison E V.hom Q
  let tau := eP.inv ≫ sV ≫ eQ.hom
  let eRP := FibredCategoryMor.pullbackComparison R V.hom P
  let eRQ := FibredCategoryMor.pullbackComparison R V.hom Q
  let bFiber := eRP.inv ≫ bSec ≫ eRQ.hom
  change (FibredCategoryMor.toFunctor k).map bFiber.1 = tau.1.b
  let lhs := (FibredCategoryMor.fiberFunctor k V.left).map bFiber
  let rhs := (FibredCategoryMor.fiberFunctor R' V.left).map tau
  have hbFiber : lhs = rhs := by
    let Fk := FibredCategoryMor.fiberFunctor k V.left
    let ekP := FibredCategoryMor.pullbackComparison k V.hom
      ((FibredCategoryMor.fiberFunctor R U).obj P)
    let ekQ := FibredCategoryMor.pullbackComparison k V.hom
      ((FibredCategoryMor.fiberFunctor R U).obj Q)
    let eCompP := FibredCategoryMor.pullbackComparison (R ≫ k) V.hom P
    let eCompQ := FibredCategoryMor.pullbackComparison (R ≫ k) V.hom Q
    let rightMap := FibredCategoryMor.fibredMorphismPresheafMap R'
      ((FibredCategoryMor.fiberFunctor E U).obj P)
      ((FibredCategoryMor.fiberFunctor E U).obj Q)
    have hleftShell :
        (eCompP.hom ≫ Fk.map bFiber) ≫ eCompQ.inv =
          (FibredCategoryMor.fibredMorphismPresheafMap k
            ((FibredCategoryMor.fiberFunctor R U).obj P)
            ((FibredCategoryMor.fiberFunctor R U).obj Q)).app (Opposite.op V) bSec := by
      have hcancel :=
        functor_map_iso_conjugate_cancel Fk eRP eRQ bSec
      have hraw :
          ekP.hom ≫ (Fk.map eRP.hom ≫ Fk.map bFiber ≫ Fk.map eRQ.inv) ≫
              ekQ.inv =
            ekP.hom ≫ Fk.map bSec ≫ ekQ.inv := by
        simpa only [bFiber] using
          congrArg (fun m => ekP.hom ≫ m ≫ ekQ.inv) hcancel
      have hconj :
          ((ekP.hom ≫ Fk.map eRP.hom) ≫ Fk.map bFiber) ≫
              Fk.map eRQ.inv ≫ ekQ.inv =
            ekP.hom ≫ Fk.map bSec ≫ ekQ.inv := by
        simpa only [Category.assoc] using hraw
      simpa only [Fk, ekP, ekQ, eCompP, eCompQ, eRP, eRQ,
        bFiber, R, E,
        fibredMorphismPresheafMap_app_pullbackComparison,
        FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
        twoFibreProduct_rightProjection_map_underlying,
        fiberHom_comp_underlying,
        pullbackComparison_comp_hom, pullbackComparison_comp_inv] using hconj
    have hrightShell :
        (eCompP.hom ≫ (FibredCategoryMor.fiberFunctor R' V.left).map tau) ≫
            eCompQ.inv =
          rightMap.app (Opposite.op V) sV := by
      let FR' := FibredCategoryMor.fiberFunctor R' V.left
      let eR'P := FibredCategoryMor.pullbackComparison R' V.hom
        ((FibredCategoryMor.fiberFunctor E U).obj P)
      let eR'Q := FibredCategoryMor.pullbackComparison R' V.hom
        ((FibredCategoryMor.fiberFunctor E U).obj Q)
      have hcancel :=
        functor_map_iso_conjugate_cancel FR' eP eQ sV
      have hCompHomP :
          eR'P.hom ≫ FR'.map eP.hom = ekP.hom ≫ Fk.map eRP.hom := by
        simpa only [Fk, FR', eR'P, eP, ekP, eRP, E, R, R',
          FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
          twoFibreProductEndpointReplacementDirectHom_obj_snd,
          twoFibreProductEndpointReplacementDirectHom_map_b,
          twoFibreProduct_rightProjection_map_underlying,
          pullbackComparison_comp_hom] using
          ((pullbackComparison_comp_hom E R' V.hom P).symm.trans
            (pullbackComparison_comp_hom R k V.hom P))
      have hCompInvQ :
          FR'.map eQ.inv ≫ eR'Q.inv = Fk.map eRQ.inv ≫ ekQ.inv := by
        simpa only [Fk, FR', eR'Q, eQ, ekQ, eRQ, E, R, R',
          FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
          twoFibreProductEndpointReplacementDirectHom_obj_snd,
          twoFibreProductEndpointReplacementDirectHom_map_b,
          twoFibreProduct_rightProjection_map_underlying,
          pullbackComparison_comp_inv] using
          ((pullbackComparison_comp_inv E R' V.hom Q).symm.trans
            (pullbackComparison_comp_inv R k V.hom Q))
      have hraw :
          eR'P.hom ≫ (FR'.map eP.hom ≫ FR'.map tau ≫ FR'.map eQ.inv) ≫
              eR'Q.inv =
            eR'P.hom ≫ FR'.map sV ≫ eR'Q.inv := by
        simpa only [tau] using
          congrArg (fun m => eR'P.hom ≫ m ≫ eR'Q.inv) hcancel
      have hconj :
          ((eR'P.hom ≫ FR'.map eP.hom) ≫ FR'.map tau) ≫
              FR'.map eQ.inv ≫ eR'Q.inv =
            eR'P.hom ≫ FR'.map sV ≫ eR'Q.inv := by
        simpa only [Category.assoc] using hraw
      rw [show eCompP.hom = ekP.hom ≫ Fk.map eRP.hom by
        simpa only [Fk, ekP, eRP, eCompP, R,
          FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor] using
          pullbackComparison_comp_hom R k V.hom P]
      rw [show eCompQ.inv = Fk.map eRQ.inv ≫ ekQ.inv by
        simpa only [Fk, ekQ, eRQ, eCompQ, R,
          FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor] using
          pullbackComparison_comp_inv R k V.hom Q]
      rw [← hCompHomP, ← hCompInvQ]
      simpa only [FR', eR'P, eR'Q, eP, eQ, rightMap, tau, R', E,
        fibredMorphismPresheafMap_app_pullbackComparison,
        FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor] using hconj
    have hshell :
        (eCompP.hom ≫ lhs) ≫ eCompQ.inv =
          (eCompP.hom ≫ rhs) ≫ eCompQ.inv := by
      exact hleftShell.trans (hbSec.trans hrightShell.symm)
    exact iso_shell_cancel eCompP eCompQ hshell
  change lhs.1 = rhs.1
  exact congrArg Subtype.val hbFiber

/-- Helper for Chap08 Lemma 8 8 4: the Hom-presheaf map of the direct endpoint replacement is
locally surjective, by locally lifting the two endpoint components through `i` and `k` and then
reassembling the two-fibre-product morphism. -/
private theorem twoFibreProductEndpointReplacementDirectHom_presheafMap_isLocallySurjective
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    (hi : FibredCategoryMor.IsStackification i)
    (hk : FibredCategoryMor.IsStackification k)
    {U : C} (P Q : (twoFibreProduct (f ≫ j) (g ≫ j)).p.Fiber U) :
    Presheaf.IsLocallySurjective (J.over U)
      (FibredCategoryMor.fibredMorphismPresheafMap
        (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) P Q) := by
  classical
  let E := twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β
  let L := twoFibreProductLeftProjection (f ≫ j) (g ≫ j)
  let R := twoFibreProductRightProjection (f ≫ j) (g ≫ j)
  let L' := twoFibreProductLeftProjection f'.toFibredCategoryMor g'.toFibredCategoryMor
  let R' := twoFibreProductRightProjection f'.toFibredCategoryMor g'.toFibredCategoryMor
  let eta := FibredCategoryMor.fibredMorphismPresheafMap E P Q
  let lMap := FibredCategoryMor.fibredMorphismPresheafMap L P Q
  let rMap := FibredCategoryMor.fibredMorphismPresheafMap R P Q
  let thetaI := FibredCategoryMor.fibredMorphismPresheafMap i
    ((FibredCategoryMor.fiberFunctor L U).obj P)
    ((FibredCategoryMor.fiberFunctor L U).obj Q)
  let thetaK := FibredCategoryMor.fibredMorphismPresheafMap k
    ((FibredCategoryMor.fiberFunctor R U).obj P)
    ((FibredCategoryMor.fiberFunctor R U).obj Q)
  letI : (twoFibreProduct (f ≫ j) (g ≫ j)).p.IsFibered :=
    FibredCategoryOver.isFibred (twoFibreProduct (f ≫ j) (g ≫ j))
  letI : (twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor).p.IsFibered :=
    FibredCategoryOver.isFibred (twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor)
  haveI : (J.over U).WEqualsLocallyBijective (Type v) :=
    over_WEqualsLocallyBijective_small (J := J) U
  have hthetaI_surj : Presheaf.IsLocallySurjective (J.over U) thetaI :=
    (hi.morphismPresheafMap_W U
      ((FibredCategoryMor.fiberFunctor L U).obj P)
      ((FibredCategoryMor.fiberFunctor L U).obj Q) : (J.over U).W thetaI).isLocallySurjective
  have hthetaK_surj : Presheaf.IsLocallySurjective (J.over U) thetaK :=
    (hk.morphismPresheafMap_W U
      ((FibredCategoryMor.fiberFunctor R U).obj P)
      ((FibredCategoryMor.fiberFunctor R U).obj Q) : (J.over U).W thetaK).isLocallySurjective
  refine ⟨fun {T} s => ?_⟩
  let targetHom :=
    (canonicalFiberPseudofunctor
      (twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor).p).presheafHom
        ((FibredCategoryMor.fiberFunctor E U).obj P)
        ((FibredCategoryMor.fiberFunctor E U).obj Q)
  let leftTarget :=
    (FibredCategoryMor.fibredMorphismPresheafMap L'
      ((FibredCategoryMor.fiberFunctor E U).obj P)
      ((FibredCategoryMor.fiberFunctor E U).obj Q)).app (Opposite.op T) s
  let rightTarget :=
    (FibredCategoryMor.fibredMorphismPresheafMap R'
      ((FibredCategoryMor.fiberFunctor E U).obj P)
      ((FibredCategoryMor.fiberFunctor E U).obj Q)).app (Opposite.op T) s
  have hleftS :
      Presheaf.imageSieve thetaI leftTarget ∈ (J.over U) T := by
    exact hthetaI_surj.imageSieve_mem leftTarget
  have hrightS :
      Presheaf.imageSieve thetaK rightTarget ∈ (J.over U) T := by
    exact hthetaK_surj.imageSieve_mem rightTarget
  have hintersection :
      Presheaf.imageSieve thetaI leftTarget ⊓
          Presheaf.imageSieve thetaK rightTarget ∈
        (J.over U) T := by
    exact (J.over U).intersection_covering hleftS hrightS
  refine (J.over U).superset_covering
    (S := Presheaf.imageSieve thetaI leftTarget ⊓
      Presheaf.imageSieve thetaK rightTarget) ?_ hintersection
  intro V hV hVmem
  let sourceHom :=
    (canonicalFiberPseudofunctor (twoFibreProduct (f ≫ j) (g ≫ j)).p).presheafHom P Q
  let sV := targetHom.map hV.op s
  let PV := V.hom ^*[canonicalPullbackChoice (twoFibreProduct (f ≫ j) (g ≫ j)).p] P
  let QV := V.hom ^*[canonicalPullbackChoice (twoFibreProduct (f ≫ j) (g ≫ j)).p] Q
  let eP := FibredCategoryMor.pullbackComparison E V.hom P
  let eQ := FibredCategoryMor.pullbackComparison E V.hom Q
  let tau := eP.inv ≫ sV ≫ eQ.hom
  let aSec := Presheaf.localPreimage thetaI leftTarget hV hVmem.1
  let bSec := Presheaf.localPreimage thetaK rightTarget hV hVmem.2
  have haSec :
      thetaI.app (Opposite.op V) aSec =
        (FibredCategoryMor.fibredMorphismPresheafMap L'
          ((FibredCategoryMor.fiberFunctor E U).obj P)
          ((FibredCategoryMor.fiberFunctor E U).obj Q)).app (Opposite.op V) sV := by
    have hpre := Presheaf.app_localPreimage thetaI leftTarget hV hVmem.1
    have hnat :=
      (NatTrans.naturality_apply
        (FibredCategoryMor.fibredMorphismPresheafMap L'
          ((FibredCategoryMor.fiberFunctor E U).obj P)
          ((FibredCategoryMor.fiberFunctor E U).obj Q)) hV.op s).symm
    exact hpre.trans hnat
  have hbSec :
      thetaK.app (Opposite.op V) bSec =
        (FibredCategoryMor.fibredMorphismPresheafMap R'
          ((FibredCategoryMor.fiberFunctor E U).obj P)
          ((FibredCategoryMor.fiberFunctor E U).obj Q)).app (Opposite.op V) sV := by
    have hpre := Presheaf.app_localPreimage thetaK rightTarget hV hVmem.2
    have hnat :=
      (NatTrans.naturality_apply
        (FibredCategoryMor.fibredMorphismPresheafMap R'
          ((FibredCategoryMor.fiberFunctor E U).obj P)
          ((FibredCategoryMor.fiberFunctor E U).obj Q)) hV.op s).symm
    exact hpre.trans hnat
  let eLP := FibredCategoryMor.pullbackComparison L V.hom P
  let eLQ := FibredCategoryMor.pullbackComparison L V.hom Q
  let eRP := FibredCategoryMor.pullbackComparison R V.hom P
  let eRQ := FibredCategoryMor.pullbackComparison R V.hom Q
  let aFiber := eLP.inv ≫ aSec ≫ eLQ.hom
  let bFiber := eRP.inv ≫ bSec ≫ eRQ.hom
  have ha :
      (FibredCategoryMor.toFunctor i).map aFiber.1 = tau.1.a := by
    exact
      twoFibreProductEndpointReplacementDirectHom_local_left_component
        (J := J) f g i j k f' g' α β P Q V sV aSec haSec
  have hb :
      (FibredCategoryMor.toFunctor k).map bFiber.1 = tau.1.b := by
    exact
      twoFibreProductEndpointReplacementDirectHom_local_right_component
        (J := J) f g i j k f' g' α β P Q V sV bSec hbSec
  let sigmaRaw : PV.1 ⟶ QV.1 :=
    { base := eqToHom PV.2 ≫ (𝟙 V.left) ≫ eqToHom QV.2.symm
      a := aFiber.1
      a_over := by
        exact twoFibreProduct_leftFiberHom_isHomLift (f ≫ j) (g ≫ j) PV QV aFiber
      b := bFiber.1
      b_over := by
        exact twoFibreProduct_rightFiberHom_isHomLift (f ≫ j) (g ≫ j) PV QV bFiber
      comm := by
        refine ⟨?_⟩
        exact
          twoFibreProductEndpointReplacementDirectHom_preimage_comm
            (J := J) f g i j k f' g' α β tau aFiber.1 bFiber.1 ha hb }
  have hsigmaRaw_over :
      (twoFibreProduct (f ≫ j) (g ≫ j)).p.IsHomLift (𝟙 V.left) sigmaRaw := by
    refine IsHomLift.of_fac' (twoFibreProduct (f ≫ j) (g ≫ j)).p
      (𝟙 V.left) sigmaRaw PV.2 QV.2 ?_
    change sigmaRaw.base = eqToHom PV.2 ≫ (𝟙 V.left) ≫ eqToHom QV.2.symm
    rfl
  let sigma : PV ⟶ QV := ⟨sigmaRaw, hsigmaRaw_over⟩
  refine ⟨sigma, ?_⟩
  change eta.app (Opposite.op V) sigma = targetHom.map hV.op s
  rw [fibredMorphismPresheafMap_app_pullbackComparison E P Q V sigma]
  change eP.hom ≫ (FibredCategoryMor.fiberFunctor E V.left).map sigma ≫ eQ.inv = sV
  have hEtau : (FibredCategoryMor.fiberFunctor E V.left).map sigma = tau := by
    apply twoFibreProductFiberHom_ext_components f'.toFibredCategoryMor g'.toFibredCategoryMor
    · change
        ((FibredCategoryMor.toFunctor E).map sigma.1).a = tau.1.a
      rw [twoFibreProductEndpointReplacementDirectHom_map_a
        (J := J) f g i j k f' g' α β sigma.1]
      change (FibredCategoryMor.toFunctor i).map aFiber.1 = tau.1.a
      exact ha
    · change
        ((FibredCategoryMor.toFunctor E).map sigma.1).b = tau.1.b
      rw [twoFibreProductEndpointReplacementDirectHom_map_b
        (J := J) f g i j k f' g' α β sigma.1]
      change (FibredCategoryMor.toFunctor k).map bFiber.1 = tau.1.b
      exact hb
  rw [hEtau]
  change eP.hom ≫ (eP.inv ≫ sV ≫ eQ.hom) ≫ eQ.inv = sV
  calc
    eP.hom ≫ (eP.inv ≫ sV ≫ eQ.hom) ≫ eQ.inv
        = (eP.hom ≫ eP.inv) ≫ sV ≫ (eQ.hom ≫ eQ.inv) := by
          simp only [Category.assoc]
    _ = sV := by
          rw [eP.hom_inv_id]
          simp only [Category.id_comp]
          have hright : (sV ≫ eQ.hom) ≫ eQ.inv = sV :=
            (eQ.comp_inv_eq).2 rfl
          simpa only [Category.assoc] using hright

/-- Helper for Chap08 Lemma 8 8 4: the staged comparison first replaces the middle by `j` and
then replaces the two endpoints by `i` and `k`. -/
private noncomputable def twoFibreProductStagedComparisonHom
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j) :
    FibredCategoryMor (twoFibreProduct f g)
      (twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor) :=
  -- This is the nonrecursive staged map identified by the source proof: middle replacement,
  -- followed by direct endpoint replacement.
  twoFibreProductMiddlePostcomposeHom f g j ≫
    twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β

/-- The canonical morphism of fibred categories from the explicit `2`-fibre product of `f` and
`g` to the explicit `2`-fibre product of the chosen lifted morphisms `f'` and `g'`. -/
noncomputable def twoFibreProductOfStackificationsHom
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j) :
    FibredCategoryMor
      (twoFibreProduct f g)
      (twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor) :=
  -- Route correction: use the source proof's staged comparison by definition, avoiding the
  -- terminal-lift normal form whose projection transports caused the previous blocker.
  twoFibreProductStagedComparisonHom f g i j k f' g' α β

/-- Helper for Chap08 Lemma 8 8 4: the public comparison map unfolds to the staged comparison
that first replaces the middle and then replaces the endpoints. -/
private theorem twoFibreProductOfStackificationsHom_eq_stagedComparison
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j) :
    twoFibreProductOfStackificationsHom f g i j k f' g' α β =
      twoFibreProductStagedComparisonHom f g i j k f' g' α β := by
  -- The definition-order pivot made this equality definitional; naming it prevents later
  -- proofs from reopening the old terminal-lift normal form.
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the canonical comparison sends the left endpoint object by
the left stackification morphism. -/
theorem twoFibreProductOfStackificationsHom_obj_fst
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    (P : (twoFibreProduct f g).S) :
    ((FibredCategoryMor.toFunctor
      (twoFibreProductOfStackificationsHom f g i j k f' g' α β)).obj P).obj.fst.1 =
      (FibredCategoryMor.toFunctor i).obj P.obj.fst.1 := by
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the canonical comparison sends the right endpoint object by
the right stackification morphism. -/
theorem twoFibreProductOfStackificationsHom_obj_snd
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    (P : (twoFibreProduct f g).S) :
    ((FibredCategoryMor.toFunctor
      (twoFibreProductOfStackificationsHom f g i j k f' g' α β)).obj P).obj.snd.1 =
      (FibredCategoryMor.toFunctor k).obj P.obj.snd.1 := by
  rfl

/-- Helper for Chap08 Lemma 8 8 4: on morphisms, the canonical comparison sends the left
component by the left stackification morphism. -/
theorem twoFibreProductOfStackificationsHom_map_a
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    {P Q : (twoFibreProduct f g).S} (φ : P ⟶ Q) :
    ((FibredCategoryMor.toFunctor
      (twoFibreProductOfStackificationsHom f g i j k f' g' α β)).map φ).a =
      (FibredCategoryMor.toFunctor i).map φ.a := by
  rfl

/-- Helper for Chap08 Lemma 8 8 4: on morphisms, the canonical comparison sends the right
component by the right stackification morphism. -/
theorem twoFibreProductOfStackificationsHom_map_b
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    {P Q : (twoFibreProduct f g).S} (φ : P ⟶ Q) :
    ((FibredCategoryMor.toFunctor
      (twoFibreProductOfStackificationsHom f g i j k f' g' α β)).map φ).b =
      (FibredCategoryMor.toFunctor k).map φ.b := by
  rfl

/-- Helper for Chap08 Lemma 8 8 5: the canonical comparison stores the endpoint comparison
isomorphisms around the middle image of the source comparison. -/
theorem twoFibreProductOfStackificationsHom_obj_comparison
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    (P : (twoFibreProduct f g).S) :
    ((FibredCategoryMor.toFunctor
      (twoFibreProductOfStackificationsHom f g i j k f' g' α β)).obj P).comparison =
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso α).hom.app P.obj.fst.1 ≫
        (FibredCategoryMor.toFunctor j).map P.comparison ≫
          (FibredCategoryMor.basedFunctorIsoOfOwnerIso β).inv.app P.obj.snd.1 := by
  -- First expose the staged comparison; its object comparison is the middle image conjugated by
  -- the two endpoint comparison isomorphisms.
  unfold twoFibreProductOfStackificationsHom
  unfold twoFibreProductStagedComparisonHom
  let Pm := (FibredCategoryMor.toFunctor (twoFibreProductMiddlePostcomposeHom f g j)).obj P
  change ((FibredCategoryMor.toFunctor
      (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β)).obj Pm).comparison =
    (FibredCategoryMor.basedFunctorIsoOfOwnerIso α).hom.app P.obj.fst.1 ≫
      (FibredCategoryMor.toFunctor j).map P.comparison ≫
        (FibredCategoryMor.basedFunctorIsoOfOwnerIso β).inv.app P.obj.snd.1
  rw [twoFibreProductEndpointReplacementDirectHom_obj_comparison]
  rw [twoFibreProductMiddlePostcomposeHom_obj_comparison]
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the staged comparison has the expected left projection
comparison to the source left projection followed by `i`. -/
private noncomputable def twoFibreProductStagedComparisonHom_leftProjection
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j) :
    twoFibreProductStagedComparisonHom f g i j k f' g' α β ≫
        twoFibreProductLeftProjection f'.toFibredCategoryMor g'.toFibredCategoryMor ⟶
      twoFibreProductLeftProjection f g ≫ i :=
  -- Compose the endpoint left projection cell with the middle left projection cell, inserting the
  -- associators explicitly so later square morphisms do not depend on definitional reduction.
  let M := twoFibreProductMiddlePostcomposeHom f g j
  let E := twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β
  let Lmid := twoFibreProductLeftProjection (f ≫ j) (g ≫ j)
  let Ltarget := twoFibreProductLeftProjection f'.toFibredCategoryMor g'.toFibredCategoryMor
  (α_ M E Ltarget).hom ≫
    M ◁ (twoFibreProductEndpointReplacementDirectHom_leftProjection f g i j k f' g' α β) ≫
      (α_ M Lmid i).inv ≫
        (twoFibreProductMiddlePostcomposeHom_leftProjection f g j ▷ i)

/-- Helper for Chap08 Lemma 8 8 4: the staged comparison has the expected right projection
comparison to the source right projection followed by `k`. -/
private noncomputable def twoFibreProductStagedComparisonHom_rightProjection
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j) :
    twoFibreProductStagedComparisonHom f g i j k f' g' α β ≫
        twoFibreProductRightProjection f'.toFibredCategoryMor g'.toFibredCategoryMor ⟶
      twoFibreProductRightProjection f g ≫ k :=
  -- This is the right-leg analogue of the staged projection composite.
  let M := twoFibreProductMiddlePostcomposeHom f g j
  let E := twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β
  let Rmid := twoFibreProductRightProjection (f ≫ j) (g ≫ j)
  let Rtarget := twoFibreProductRightProjection f'.toFibredCategoryMor g'.toFibredCategoryMor
  (α_ M E Rtarget).hom ≫
    M ◁ (twoFibreProductEndpointReplacementDirectHom_rightProjection f g i j k f' g' α β) ≫
      (α_ M Rmid k).inv ≫
        (twoFibreProductMiddlePostcomposeHom_rightProjection f g j ▷ k)

/-- Helper for Chap08 Lemma 8 8 4: after the middle has been replaced, the remaining endpoint
comparison is the canonical stackification comparison using the identity middle map. -/
private noncomputable def twoFibreProductEndpointReplacementHom
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j) :
    FibredCategoryMor (twoFibreProduct (f ≫ j) (g ≫ j))
      (twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor) :=
  -- Route correction: use the direct endpoint terminal construction instead of recursively
  -- specializing the final comparison map with the identity middle stackification.
  twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β

/-- Helper for Chap08 Lemma 8 8 4: the older endpoint helper is definitionally the direct
nonrecursive endpoint-replacement map. -/
private theorem twoFibreProductEndpointReplacementHom_eq_direct
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j) :
    twoFibreProductEndpointReplacementHom f g i j k f' g' α β =
      twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β := by
  -- Both names now expand to the same terminal morphism from the direct endpoint square.
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Helper for Chap08 Lemma 8 8 4: the middle-postcomposition map has locally invertible
Hom-presheaf maps because its only nontrivial component is induced by the middle stackification
map. -/
private theorem twoFibreProductMiddlePostcomposeHom_morphismPresheafMap_W
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    (hj : FibredCategoryMor.IsStackification j) :
    ∀ (U : C) (P Q : (twoFibreProduct f g).p.Fiber U),
      (J.over U).W (FibredCategoryMor.fibredMorphismPresheafMap
        (twoFibreProductMiddlePostcomposeHom f g j) P Q) := by
  intro U P Q
  let eta :=
    FibredCategoryMor.fibredMorphismPresheafMap
      (twoFibreProductMiddlePostcomposeHom f g j) P Q
  haveI : Presheaf.IsLocallyInjective (J.over U) eta := by
    apply Presheaf.isLocallyInjective_of_injective
    intro W
    exact twoFibreProductMiddlePostcomposeHom_presheafMap_app_injective f g j P Q W
  haveI : Presheaf.IsLocallySurjective (J.over U) eta := by
    refine ⟨fun {T} s => ?_⟩
    let F := twoFibreProductMiddlePostcomposeHom f g j
    letI : (twoFibreProduct f g).p.IsFibered :=
      FibredCategoryOver.isFibred (twoFibreProduct f g)
    letI : (twoFibreProduct (f ≫ j) (g ≫ j)).p.IsFibered :=
      FibredCategoryOver.isFibred (twoFibreProduct (f ≫ j) (g ≫ j))
    let PT := T.hom ^*[canonicalPullbackChoice (twoFibreProduct f g).p] P
    let QT := T.hom ^*[canonicalPullbackChoice (twoFibreProduct f g).p] Q
    let eP := FibredCategoryMor.pullbackComparison F T.hom P
    let eQ := FibredCategoryMor.pullbackComparison F T.hom Q
    let τ := eP.inv ≫ s ≫ eQ.hom
    have hτa_over : X.p.IsHomLift (𝟙 T.left) τ.1.a := by
      exact twoFibreProduct_fiber_left_over_id (f ≫ j) (g ≫ j) τ
    have hτb_over : Z.p.IsHomLift (𝟙 T.left) τ.1.b := by
      exact twoFibreProduct_fiber_right_over_id (f ≫ j) (g ≫ j) τ
    let PTfst : X.p.Fiber T.left :=
      ⟨PT.1.obj.fst.1, by
        rw [PT.1.obj.fst.2]
        simpa using PT.2⟩
    let QTfst : X.p.Fiber T.left :=
      ⟨QT.1.obj.fst.1, by
        rw [QT.1.obj.fst.2]
        simpa using QT.2⟩
    let PTsnd : Z.p.Fiber T.left :=
      ⟨PT.1.obj.snd.1, by
        rw [PT.1.obj.snd.2]
        simpa using PT.2⟩
    let QTsnd : Z.p.Fiber T.left :=
      ⟨QT.1.obj.snd.1, by
        rw [QT.1.obj.snd.2]
        simpa using QT.2⟩
    let aτ : PTfst ⟶ QTfst := ⟨τ.1.a, hτa_over⟩
    let bτ : PTsnd ⟶ QTsnd := ⟨τ.1.b, hτb_over⟩
    have hQTcomparison : Y₀.p.IsHomLift (𝟙 T.left) QT.1.comparison := by
      change Y₀.p.IsHomLift (𝟙 ((𝟭 C).obj T.left)) QT.1.comparison
      exact twoFibreProduct_fiber_comparison_over_id f g QT
    have hPTcomparison : Y₀.p.IsHomLift (𝟙 T.left) PT.1.comparison := by
      change Y₀.p.IsHomLift (𝟙 ((𝟭 C).obj T.left)) PT.1.comparison
      exact twoFibreProduct_fiber_comparison_over_id f g PT
    let lhs :
        ((FibredCategoryMor.fiberFunctor f T.left).obj PTfst) ⟶
          ((FibredCategoryMor.fiberFunctor g T.left).obj QTsnd) :=
      (FibredCategoryMor.fiberFunctor f T.left).map aτ ≫
        ⟨QT.1.comparison, hQTcomparison⟩
    let rhs :
        ((FibredCategoryMor.fiberFunctor f T.left).obj PTfst) ⟶
          ((FibredCategoryMor.fiberFunctor g T.left).obj QTsnd) :=
      ⟨PT.1.comparison, hPTcomparison⟩ ≫
        (FibredCategoryMor.fiberFunctor g T.left).map bτ
    have himage :
        (FibredCategoryMor.fiberFunctor j T.left).map lhs =
          (FibredCategoryMor.fiberFunctor j T.left).map rhs := by
      apply Functor.Fiber.hom_ext
      have hcomm := τ.1.comm.w
      change (FibredCategoryMor.toFunctor j).map
            (((FibredCategoryMor.toFunctor f).map τ.1.a ≫ QT.1.comparison)) =
        (FibredCategoryMor.toFunctor j).map
          (PT.1.comparison ≫ (FibredCategoryMor.toFunctor g).map τ.1.b)
      rw [Functor.map_comp, Functor.map_comp]
      change (FibredCategoryMor.toFunctor j).map
            ((FibredCategoryMor.toFunctor f).map τ.1.a) ≫
          (FibredCategoryMor.toFunctor j).map QT.1.comparison =
        (FibredCategoryMor.toFunctor j).map PT.1.comparison ≫
          (FibredCategoryMor.toFunctor j).map
            ((FibredCategoryMor.toFunctor g).map τ.1.b)
      change (FibredCategoryMor.toFunctor (f ≫ j)).map τ.1.a ≫
          (FibredCategoryMor.toFunctor j).map QT.1.comparison =
        (FibredCategoryMor.toFunctor j).map PT.1.comparison ≫
          (FibredCategoryMor.toFunctor (g ≫ j)).map τ.1.b
      have hQTcomp :
          (FibredCategoryMor.toFunctor j).map QT.1.comparison =
            ((FibredCategoryMor.toFunctor (twoFibreProductMiddlePostcomposeHom f g j)).obj
              QT.1).comparison :=
        (twoFibreProductMiddlePostcomposeHom_obj_comparison f g j QT.1).symm
      have hPTcomp :
          (FibredCategoryMor.toFunctor j).map PT.1.comparison =
            ((FibredCategoryMor.toFunctor (twoFibreProductMiddlePostcomposeHom f g j)).obj
              PT.1).comparison :=
        (twoFibreProductMiddlePostcomposeHom_obj_comparison f g j PT.1).symm
      erw [hQTcomp, hPTcomp]
      exact hcomm
    let y₁ := (FibredCategoryMor.fiberFunctor f T.left).obj PTfst
    let y₂ := (FibredCategoryMor.fiberFunctor g T.left).obj QTsnd
    let θ := FibredCategoryMor.fibredMorphismPresheafMap j y₁ y₂
    haveI : (J.over T.left).WEqualsLocallyBijective (Type v) := by
      let _ :
          ∀ P' : (Over T.left)ᵒᵖ ⥤ Type v,
            Presheaf.IsLocallyInjective (J.over T.left) (toSheafify (J.over T.left) P') := by
        intro P'
        exact
          CategoryTheory.Functor.small_type_toSheafify_isLocallyInjective_of_univLE
            (L := J.over T.left) P'
      let _ :
          ∀ P' : (Over T.left)ᵒᵖ ⥤ Type v,
            Presheaf.IsLocallySurjective (J.over T.left) (toSheafify (J.over T.left) P') := by
        intro P'
        exact
          CategoryTheory.Functor.toSheafify_isLocallySurjective_type_of_hasWeakSheafify
            (L := J.over T.left) P'
      exact GrothendieckTopology.WEqualsLocallyBijective.mk'
        (J := J.over T.left) (A := Type v)
    haveI : Presheaf.IsLocallyInjective (J.over T.left) θ :=
      (hj.morphismPresheafMap_W T.left y₁ y₂ : (J.over T.left).W θ).isLocallyInjective
    let βlhs :
        ((canonicalFiberPseudofunctor Y₀.p).presheafHom y₁ y₂).obj
          (Opposite.op (Over.mk (𝟙 T.left))) :=
      (canonicalFiberPseudofunctor Y₀.p).presheafHomObjHomEquiv
        (show y₁ ⟶ y₂ from lhs)
    let βrhs :
        ((canonicalFiberPseudofunctor Y₀.p).presheafHom y₁ y₂).obj
          (Opposite.op (Over.mk (𝟙 T.left))) :=
      (canonicalFiberPseudofunctor Y₀.p).presheafHomObjHomEquiv
        (show y₁ ⟶ y₂ from rhs)
    have hβ :
        θ.app (Opposite.op (Over.mk (𝟙 T.left))) βlhs =
          θ.app (Opposite.op (Over.mk (𝟙 T.left))) βrhs := by
      rw [fibredMorphismPresheafMap_app_id_local j y₁ y₂ lhs]
      rw [fibredMorphismPresheafMap_app_id_local j y₁ y₂ rhs]
      exact congrArg
        (canonicalFiberPseudofunctor Y₁.p).presheafHomObjHomEquiv himage
    have hEq :
        Presheaf.equalizerSieve
            (F := (canonicalFiberPseudofunctor Y₀.p).presheafHom y₁ y₂)
            βlhs βrhs ∈
          (J.over T.left) (Over.mk (𝟙 T.left)) :=
      by
        simpa using
          Presheaf.equalizerSieve_mem (J.over T.left) θ βlhs βrhs hβ
    rw [J.mem_over_iff]
    refine J.superset_covering
      (S := (Sieve.overEquiv (Over.mk (𝟙 T.left)))
        (Presheaf.equalizerSieve
          (F := (canonicalFiberPseudofunctor Y₀.p).presheafHom y₁ y₂)
          βlhs βrhs)) ?_ ?_
    · intro V h hh
      rw [Sieve.overEquiv_iff] at hh ⊢
      let TV : Over U := Over.mk (h ≫ T.hom)
      let hraw : V ⟶ T.left := h ≫ 𝟙 T.left
      have hTV : hraw ≫ T.hom = TV.hom := by
        simp [hraw, TV]
      let hTVloc := comp_toLoc_eq T.hom hraw TV.hom hTV
      let ι : TV ⟶ T := Over.homMk hraw hTV
      let sV :
          ((canonicalFiberPseudofunctor (twoFibreProduct (f ≫ j) (g ≫ j)).p).presheafHom
            ((FibredCategoryMor.fiberFunctor F U).obj P)
            ((FibredCategoryMor.fiberFunctor F U).obj Q)).obj (Opposite.op TV) :=
        ((canonicalFiberPseudofunctor (twoFibreProduct (f ≫ j) (g ≫ j)).p).presheafHom
          ((FibredCategoryMor.fiberFunctor F U).obj P)
          ((FibredCategoryMor.fiberFunctor F U).obj Q)).map ι.op s
      let PV := TV.hom ^*[canonicalPullbackChoice (twoFibreProduct f g).p] P
      let QV := TV.hom ^*[canonicalPullbackChoice (twoFibreProduct f g).p] Q
      let ePV := FibredCategoryMor.pullbackComparison F TV.hom P
      let eQV := FibredCategoryMor.pullbackComparison F TV.hom Q
      let τV := ePV.inv ≫ sV ≫ eQV.hom
      have hcommV :
          (FibredCategoryMor.toFunctor f).map τV.1.a ≫ QV.1.comparison =
            PV.1.comparison ≫ (FibredCategoryMor.toFunctor g).map τV.1.b := by
        have hhh := hh
        dsimp [Presheaf.equalizerSieve, βlhs, βrhs] at hhh
        have hhh' :
            ((canonicalFiberPseudofunctor Y₀.p).map
               (h ≫ 𝟙 T.left).op.toLoc).toFunctor.map lhs =
              ((canonicalFiberPseudofunctor Y₀.p).map
               (h ≫ 𝟙 T.left).op.toLoc).toFunctor.map rhs := by
          exact
            (identitySlicePresheafHom_map_hom_raw (p := Y₀.p) (g := h)
               (M := y₁) (N := y₂) (φ := lhs)).symm.trans
              (hhh.trans
                (identitySlicePresheafHom_map_hom_raw (p := Y₀.p) (g := h)
                  (M := y₁) (N := y₂) (φ := rhs)))
        let eVf := FibredCategoryMor.pullbackComparison f hraw PTfst
        let eVg := FibredCategoryMor.pullbackComparison g hraw QTsnd
        let κP :=
          canonicalFiberPseudofunctor_mapCompAppIso
            (twoFibreProduct f g).p T.hom hraw TV.hom
            hTVloc P
        let κQ :=
          canonicalFiberPseudofunctor_mapCompAppIso
            (twoFibreProduct f g).p T.hom hraw TV.hom
            hTVloc Q
        let lamP := FibredCategoryMor.pullbackComparison
          (twoFibreProductLeftProjection f g) hraw PT
        let lamQ := FibredCategoryMor.pullbackComparison
          (twoFibreProductRightProjection f g) hraw QT
        let muP :=
          lamP ≪≫
            (FibredCategoryMor.fiberFunctor (twoFibreProductLeftProjection f g) V).mapIso κP.symm
        let muQ :=
          lamQ ≪≫
            (FibredCategoryMor.fiberFunctor (twoFibreProductRightProjection f g) V).mapIso κQ.symm
        let eVfTotal := eVf ≪≫ (FibredCategoryMor.fiberFunctor f V).mapIso muP
        let eVgTotal := eVg ≪≫ (FibredCategoryMor.fiberFunctor g V).mapIso muQ
        let eFPT := FibredCategoryMor.pullbackComparison F hraw PT
        let eFQT := FibredCategoryMor.pullbackComparison F hraw QT
        let eFPTotal := eFPT ≪≫ (FibredCategoryMor.fiberFunctor F V).mapIso κP.symm
        let eFQTotal := eFQT ≪≫ (FibredCategoryMor.fiberFunctor F V).mapIso κQ.symm
        have hτV_transport :
              eFPTotal.hom ≫ τV =
                ((canonicalFiberPseudofunctor (twoFibreProduct (f ≫ j) (g ≫ j)).p).map
                    hraw.op.toLoc).toFunctor.map τ ≫ eFQTotal.hom := by
            let B := twoFibreProduct (f ≫ j) (g ≫ j)
            let M := ((canonicalFiberPseudofunctor
              (twoFibreProduct (f ≫ j) (g ≫ j)).p).map hraw.op.toLoc).toFunctor
            let AP :=
              ((canonicalFiberPseudofunctor
                (twoFibreProduct (f ≫ j) (g ≫ j)).p).mapComp'
                T.hom.op.toLoc hraw.op.toLoc
                TV.hom.op.toLoc hTVloc).hom.toNatTrans.app
                  ((FibredCategoryMor.fiberFunctor F U).obj P)
            let APi :=
              ((canonicalFiberPseudofunctor
                (twoFibreProduct (f ≫ j) (g ≫ j)).p).mapComp'
                T.hom.op.toLoc hraw.op.toLoc
                TV.hom.op.toLoc hTVloc).inv.toNatTrans.app
                  ((FibredCategoryMor.fiberFunctor F U).obj P)
            let AQ :=
              ((canonicalFiberPseudofunctor
                (twoFibreProduct (f ≫ j) (g ≫ j)).p).mapComp'
                T.hom.op.toLoc hraw.op.toLoc
                TV.hom.op.toLoc hTVloc).hom.toNatTrans.app
                  ((FibredCategoryMor.fiberFunctor F U).obj Q)
            let AQi :=
              ((canonicalFiberPseudofunctor
                (twoFibreProduct (f ≫ j) (g ≫ j)).p).mapComp'
                T.hom.op.toLoc hraw.op.toLoc
                TV.hom.op.toLoc hTVloc).inv.toNatTrans.app
                  ((FibredCategoryMor.fiberFunctor F U).obj Q)
            have hleftCocycle :
                (FibredCategoryMor.pullbackComparison F hraw PT).inv ≫
                    M.map (FibredCategoryMor.pullbackComparison F T.hom P).inv ≫ APi =
                  (FibredCategoryMor.fiberFunctor F V).map κP.symm.hom ≫
                    (FibredCategoryMor.pullbackComparison F TV.hom P).inv := by
              simpa only [B, M, APi, PT, eP, ePV, κP, hTVloc,
                FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor] using
                pullbackComparison_mapComp_inv_cocycle F T.hom hraw TV.hom hTV P
            have hleft :
                (FibredCategoryMor.pullbackComparison F hraw PT).hom ≫
                    (FibredCategoryMor.fiberFunctor F V).map κP.symm.hom ≫
                      (FibredCategoryMor.pullbackComparison F TV.hom P).inv ≫ AP =
                  M.map (FibredCategoryMor.pullbackComparison F T.hom P).inv := by
              calc
                (FibredCategoryMor.pullbackComparison F hraw PT).hom ≫
                    (FibredCategoryMor.fiberFunctor F V).map κP.symm.hom ≫
                      (FibredCategoryMor.pullbackComparison F TV.hom P).inv ≫ AP =
                  (FibredCategoryMor.pullbackComparison F hraw PT).hom ≫
                    ((FibredCategoryMor.fiberFunctor F V).map κP.symm.hom ≫
                      (FibredCategoryMor.pullbackComparison F TV.hom P).inv) ≫ AP := by
                    simp only [Category.assoc]
                _ =
                  (FibredCategoryMor.pullbackComparison F hraw PT).hom ≫
                    ((FibredCategoryMor.pullbackComparison F hraw PT).inv ≫
                      M.map (FibredCategoryMor.pullbackComparison F T.hom P).inv ≫ APi) ≫ AP := by
                    rw [← hleftCocycle]
                  _ = M.map (FibredCategoryMor.pullbackComparison F T.hom P).inv := by
                      have hAP : APi ≫ AP = 𝟙 _ := by
                        exact
                          Cat.Hom.inv_hom_id_toNatTrans_app
                            ((canonicalFiberPseudofunctor
                              (twoFibreProduct (f ≫ j) (g ≫ j)).p).mapComp'
                              T.hom.op.toLoc hraw.op.toLoc TV.hom.op.toLoc hTVloc)
                            ((FibredCategoryMor.fiberFunctor F U).obj P)
                      simp only [Category.assoc]
                      rw [Iso.hom_inv_id_assoc]
                      slice_lhs 2 3 => rw [hAP]
                      exact Category.comp_id
                        (M.map (FibredCategoryMor.pullbackComparison F T.hom P).inv)
            have hrightCocycle :
                AQ ≫ M.map (FibredCategoryMor.pullbackComparison F T.hom Q).hom ≫
                    (FibredCategoryMor.pullbackComparison F hraw QT).hom =
                  (FibredCategoryMor.pullbackComparison F TV.hom Q).hom ≫
                    (FibredCategoryMor.fiberFunctor F V).map κQ.hom := by
              simpa only [B, M, AQ, QT, eQ, eQV, κQ, hTVloc,
                FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor] using
                pullbackComparison_mapComp_hom_cocycle F T.hom hraw TV.hom hTV Q
            have hright :
                AQi ≫ (FibredCategoryMor.pullbackComparison F TV.hom Q).hom =
                  M.map (FibredCategoryMor.pullbackComparison F T.hom Q).hom ≫
                    (FibredCategoryMor.pullbackComparison F hraw QT).hom ≫
                      (FibredCategoryMor.fiberFunctor F V).map κQ.symm.hom := by
              calc
                AQi ≫ (FibredCategoryMor.pullbackComparison F TV.hom Q).hom =
                    AQi ≫ ((FibredCategoryMor.pullbackComparison F TV.hom Q).hom ≫
                      (FibredCategoryMor.fiberFunctor F V).map κQ.hom) ≫
                        (FibredCategoryMor.fiberFunctor F V).map κQ.symm.hom := by
                      simp only [Category.assoc]
                      rw [← Functor.map_comp]
                      simp only [Iso.symm_hom, Iso.hom_inv_id, Functor.map_id, Category.comp_id]
                _ =
                  AQi ≫ (AQ ≫ M.map (FibredCategoryMor.pullbackComparison F T.hom Q).hom ≫
                    (FibredCategoryMor.pullbackComparison F hraw QT).hom) ≫
                      (FibredCategoryMor.fiberFunctor F V).map κQ.symm.hom := by
                    rw [hrightCocycle]
                _ =
                  M.map (FibredCategoryMor.pullbackComparison F T.hom Q).hom ≫
                    (FibredCategoryMor.pullbackComparison F hraw QT).hom ≫
                      (FibredCategoryMor.fiberFunctor F V).map κQ.symm.hom := by
                    have hAQ : AQi ≫ AQ = 𝟙 _ := by
                        exact
                          Cat.Hom.inv_hom_id_toNatTrans_app
                            ((canonicalFiberPseudofunctor
                              (twoFibreProduct (f ≫ j) (g ≫ j)).p).mapComp'
                              T.hom.op.toLoc hraw.op.toLoc TV.hom.op.toLoc hTVloc)
                            ((FibredCategoryMor.fiberFunctor F U).obj Q)
                    simp only [Category.assoc]
                    slice_lhs 1 2 => rw [hAQ]
                    simpa only [Category.id_comp, Category.assoc]
            have hsV :
                sV = AP ≫ M.map s ≫ AQi := by
              have hsVraw :
                  Pseudofunctor.LocallyDiscreteOpToCat.pullHom
                      (F := canonicalFiberPseudofunctor B.p) s hraw TV.hom TV.hom hTV hTV =
                    AP ≫ M.map s ≫ AQi := by
                rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
              simpa only [B, sV, ι, Pseudofunctor.presheafHom_map] using hsVraw
            simp only [eFPTotal, eFQTotal, eFPT, eFQT, τV, τ, eP, eQ, ePV, eQV,
              FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
              Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
            rw [hsV]
            simp only [Category.assoc]
            slice_lhs 1 4 => rw [hleft]
            simp only [Category.assoc]
            slice_lhs 3 4 => rw [hright]
        have hτV_eq :
            τV =
              eFPTotal.inv ≫
                ((canonicalFiberPseudofunctor (twoFibreProduct (f ≫ j) (g ≫ j)).p).map
                    hraw.op.toLoc).toFunctor.map τ ≫ eFQTotal.hom := by
          calc
            τV = 𝟙 _ ≫ τV := by
              simp only [Category.id_comp]
            _ = (eFPTotal.inv ≫ eFPTotal.hom) ≫ τV := by
              rw [Iso.inv_hom_id]
            _ = eFPTotal.inv ≫ (eFPTotal.hom ≫ τV) := by
              simp only [Category.assoc]
            _ =
              eFPTotal.inv ≫
                (((canonicalFiberPseudofunctor (twoFibreProduct (f ≫ j) (g ≫ j)).p).map
                    hraw.op.toLoc).toFunctor.map τ ≫ eFQTotal.hom) := by
              rw [hτV_transport]
            _ =
              eFPTotal.inv ≫
                ((canonicalFiberPseudofunctor (twoFibreProduct (f ≫ j) (g ≫ j)).p).map
                    hraw.op.toLoc).toFunctor.map τ ≫ eFQTotal.hom := by
              simp only [Category.assoc]
        let PVfstV : X.p.Fiber V :=
          (FibredCategoryMor.fiberFunctor (twoFibreProductLeftProjection f g) V).obj PV
        let QVsndV : Z.p.Fiber V :=
          (FibredCategoryMor.fiberFunctor (twoFibreProductRightProjection f g) V).obj QV
        have hPVleft :
            (FibredCategoryMor.fiberFunctor (twoFibreProductLeftProjection f g) V).obj PV =
              PVfstV := by
          rfl
        have hQVright :
            (FibredCategoryMor.fiberFunctor (twoFibreProductRightProjection f g) V).obj QV =
              QVsndV := by
          rfl
        let eVfCancel := eVfTotal
        let eVgCancel := eVgTotal
        let eVfQ := FibredCategoryMor.pullbackComparison f hraw QTfst
        let lamQLeft := FibredCategoryMor.pullbackComparison
          (twoFibreProductLeftProjection f g) hraw QT
        let muQLeft :=
          lamQLeft ≪≫
            (FibredCategoryMor.fiberFunctor (twoFibreProductLeftProjection f g) V).mapIso
              κQ.symm
        let eVfQTotal := eVfQ ≪≫ (FibredCategoryMor.fiberFunctor f V).mapIso muQLeft
        let eVgP := FibredCategoryMor.pullbackComparison g hraw PTsnd
        let lamPRight := FibredCategoryMor.pullbackComparison
          (twoFibreProductRightProjection f g) hraw PT
        let muPRight :=
          lamPRight ≪≫
            (FibredCategoryMor.fiberFunctor (twoFibreProductRightProjection f g) V).mapIso
              κP.symm
        let eVgPTotal := eVgP ≪≫ (FibredCategoryMor.fiberFunctor g V).mapIso muPRight
        have hcompPT :=
          twoFibreProduct_comparison_reindex_boundary f g hraw PT
        have hcompQT :=
          twoFibreProduct_comparison_reindex_boundary f g hraw QT
        have hleftEndpoint :
            muP.hom.1 ≫ τV.1.a =
              (((canonicalFiberPseudofunctor X.p).map hraw.op.toLoc).toFunctor.map aτ).1 ≫
                muQLeft.hom.1 := by
          have hdirect :
              τV.1.a =
                muP.inv.1 ≫
                  (((canonicalFiberPseudofunctor X.p).map hraw.op.toLoc).toFunctor.map aτ).1 ≫
                    muQLeft.hom.1 := by
            let Lm := twoFibreProductLeftProjection (f ≫ j) (g ≫ j)
            have hτLeft :=
              twoFibreProduct_reindex_left_component (f ≫ j) (g ≫ j) hraw τ
            have hLmτ :
                (FibredCategoryMor.fiberFunctor Lm T.left).map τ = aτ := by
              apply Functor.Fiber.hom_ext
              change ((FibredCategoryMor.fiberFunctor Lm T.left).map τ).1 = aτ.1
              simpa only [Lm, aτ] using
                twoFibreProduct_leftProjection_map_underlying (f ≫ j) (g ≫ j) τ
            have hcompLeftInv :
                (FibredCategoryMor.pullbackComparison F hraw PT).inv.1.a ≫
                    (FibredCategoryMor.pullbackComparison Lm hraw
                      ((FibredCategoryMor.fiberFunctor F T.left).obj PT)).inv.1 =
                  (FibredCategoryMor.pullbackComparison
                    (twoFibreProductLeftProjection f g) hraw PT).inv.1 := by
              have h :=
                congrArg (fun φ => φ.1)
                  (pullbackComparison_comp_inv F Lm hraw PT)
              simpa only [Lm, F,
                FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
                twoFibreProductMiddlePostcomposeHom_obj_fst,
                twoFibreProductMiddlePostcomposeHom_map_a,
                twoFibreProduct_leftProjection_map_underlying,
                fiberHom_comp_underlying, Category.assoc] using h.symm
            have hcompLeftHom :
                (FibredCategoryMor.pullbackComparison Lm hraw
                    ((FibredCategoryMor.fiberFunctor F T.left).obj QT)).hom.1 ≫
                  (FibredCategoryMor.pullbackComparison F hraw QT).hom.1.a =
                (FibredCategoryMor.pullbackComparison
                  (twoFibreProductLeftProjection f g) hraw QT).hom.1 := by
              have h :=
                congrArg (fun φ => φ.1)
                  (pullbackComparison_comp_hom F Lm hraw QT)
              simpa only [Lm, F,
                FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
                twoFibreProductMiddlePostcomposeHom_obj_fst,
                twoFibreProductMiddlePostcomposeHom_map_a,
                twoFibreProduct_leftProjection_map_underlying,
                fiberHom_comp_underlying, Category.assoc] using h.symm
            let Mτ :=
              ((canonicalFiberPseudofunctor
                (twoFibreProduct (f ≫ j) (g ≫ j)).p).map hraw.op.toLoc).toFunctor.map τ
            let kP := (FibredCategoryMor.fiberFunctor F V).map κP.hom
            let kQ := (FibredCategoryMor.fiberFunctor F V).map κQ.inv
            have hcomponent :
                (kP.1 ≫ (FibredCategoryMor.pullbackComparison F hraw PT).inv.1 ≫
                    Mτ.1 ≫ (FibredCategoryMor.pullbackComparison F hraw QT).hom.1 ≫
                    kQ.1).a =
                  κP.hom.1.a ≫
                    (FibredCategoryMor.pullbackComparison
                      (twoFibreProductLeftProjection f g) hraw PT).inv.1 ≫
                      (((canonicalFiberPseudofunctor X.p).map hraw.op.toLoc).toFunctor.map
                        aτ).1 ≫
                        (FibredCategoryMor.pullbackComparison
                          (twoFibreProductLeftProjection f g) hraw QT).hom.1 ≫
                          κQ.inv.1.a := by
              calc
                (kP.1 ≫ (FibredCategoryMor.pullbackComparison F hraw PT).inv.1 ≫
                    Mτ.1 ≫ (FibredCategoryMor.pullbackComparison F hraw QT).hom.1 ≫
                    kQ.1).a =
                  kP.1.a ≫ (FibredCategoryMor.pullbackComparison F hraw PT).inv.1.a ≫
                    Mτ.1.a ≫ (FibredCategoryMor.pullbackComparison F hraw QT).hom.1.a ≫
                      kQ.1.a := by
                    simp only [twoFibreProductHom_comp_a, Category.assoc]
                _ =
                  κP.hom.1.a ≫
                    (FibredCategoryMor.pullbackComparison F hraw PT).inv.1.a ≫
                      Mτ.1.a ≫
                        (FibredCategoryMor.pullbackComparison F hraw QT).hom.1.a ≫
                          κQ.inv.1.a := by
                    simp only [kP, kQ, F, FibredCategoryMor.fiberFunctor,
                      BasedFunctor.fiberFunctor,
                      twoFibreProductMiddlePostcomposeHom_fiber_map_a]
                _ =
                  κP.hom.1.a ≫
                    (FibredCategoryMor.pullbackComparison F hraw PT).inv.1.a ≫
                      ((FibredCategoryMor.pullbackComparison Lm hraw
                          ((FibredCategoryMor.fiberFunctor F T.left).obj PT)).inv ≫
                        (((canonicalFiberPseudofunctor X.p).map hraw.op.toLoc).toFunctor.map
                          aτ) ≫
                        (FibredCategoryMor.pullbackComparison Lm hraw
                          ((FibredCategoryMor.fiberFunctor F T.left).obj QT)).hom).1 ≫
                        (FibredCategoryMor.pullbackComparison F hraw QT).hom.1.a ≫
                          κQ.inv.1.a := by
                    rw [hτLeft, hLmτ]
                _ =
                  κP.hom.1.a ≫
                    ((FibredCategoryMor.pullbackComparison F hraw PT).inv.1.a ≫
                      (FibredCategoryMor.pullbackComparison Lm hraw
                        ((FibredCategoryMor.fiberFunctor F T.left).obj PT)).inv.1) ≫
                      (((canonicalFiberPseudofunctor X.p).map hraw.op.toLoc).toFunctor.map
                        aτ).1 ≫
                        ((FibredCategoryMor.pullbackComparison Lm hraw
                          ((FibredCategoryMor.fiberFunctor F T.left).obj QT)).hom.1 ≫
                          (FibredCategoryMor.pullbackComparison F hraw QT).hom.1.a) ≫
                          κQ.inv.1.a := by
                    simp only [fiberHom_comp_underlying, Category.assoc]
                _ =
                  κP.hom.1.a ≫
                    (FibredCategoryMor.pullbackComparison
                      (twoFibreProductLeftProjection f g) hraw PT).inv.1 ≫
                      (((canonicalFiberPseudofunctor X.p).map hraw.op.toLoc).toFunctor.map
                        aτ).1 ≫
                        (FibredCategoryMor.pullbackComparison
                          (twoFibreProductLeftProjection f g) hraw QT).hom.1 ≫
                          κQ.inv.1.a := by
                    rw [hcompLeftInv, hcompLeftHom]
            have hτV_component :
                τV.1.a =
                  (kP.1 ≫ (FibredCategoryMor.pullbackComparison F hraw PT).inv.1 ≫
                    Mτ.1 ≫ (FibredCategoryMor.pullbackComparison F hraw QT).hom.1 ≫
                    kQ.1).a := by
              have htransport :=
                congrArg (fun φ => φ.1.a) hτV_eq
              simpa only [eFPTotal, eFQTotal, eFPT, eFQT, Mτ, kP, kQ,
                FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
                Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
                Category.assoc] using htransport
            simpa only [muP, muQLeft, lamP, lamQLeft, κP, κQ,
              FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
              Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
              Functor.mapIso_inv, Functor.mapIso_hom,
              twoFibreProduct_leftProjection_map_underlying,
              fiberHom_comp_underlying, Category.assoc] using hτV_component.trans hcomponent
          calc
            muP.hom.1 ≫ τV.1.a =
                muP.hom.1 ≫
                  (muP.inv.1 ≫
                    (((canonicalFiberPseudofunctor X.p).map hraw.op.toLoc).toFunctor.map aτ).1 ≫
                      muQLeft.hom.1) := by
              rw [hdirect]
            _ =
                (muP.hom.1 ≫ muP.inv.1) ≫
                  (((canonicalFiberPseudofunctor X.p).map hraw.op.toLoc).toFunctor.map aτ).1 ≫
                    muQLeft.hom.1 := by
              simp only [Category.assoc]
            _ =
                (((canonicalFiberPseudofunctor X.p).map hraw.op.toLoc).toFunctor.map aτ).1 ≫
                  muQLeft.hom.1 := by
              rw [show muP.hom.1 ≫ muP.inv.1 = 𝟙 _ from
                congrArg (fun φ => φ.1) muP.hom_inv_id]
              simp only [Category.id_comp]
        have hleftNaturality :
            (((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map
                ((FibredCategoryMor.fiberFunctor f T.left).map aτ)).1 ≫ eVfQ.hom.1 =
              eVf.hom.1 ≫ (FibredCategoryMor.toFunctor f).map
                ((((canonicalFiberPseudofunctor X.p).map hraw.op.toLoc).toFunctor.map aτ).1) := by
          simpa only [FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor] using
            congrArg (fun φ => φ.1)
              (stack_morphism_pullbackComparison_naturality_over_vertical f hraw aτ)
        have hleftPart :
            eVfCancel.hom.1 ≫ (FibredCategoryMor.toFunctor f).map τV.1.a =
              (((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map
                ((FibredCategoryMor.fiberFunctor f T.left).map aτ)).1 ≫
                  eVfQTotal.hom.1 := by
          calc
            eVfCancel.hom.1 ≫ (FibredCategoryMor.toFunctor f).map τV.1.a =
                (eVf.hom.1 ≫ (FibredCategoryMor.toFunctor f).map muP.hom.1) ≫
                  (FibredCategoryMor.toFunctor f).map τV.1.a := by
              simp only [eVfCancel, eVfTotal, Iso.trans_hom, Functor.mapIso_hom,
                FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
                fibredMorphism_fiberFunctor_map_underlying, fiberHom_comp_underlying]
            _ =
                eVf.hom.1 ≫
                  (FibredCategoryMor.toFunctor f).map (muP.hom.1 ≫ τV.1.a) := by
              simp only [Functor.map_comp, Category.assoc]
            _ =
                eVf.hom.1 ≫
                  (FibredCategoryMor.toFunctor f).map
                    ((((canonicalFiberPseudofunctor X.p).map hraw.op.toLoc).toFunctor.map aτ).1 ≫
                      muQLeft.hom.1) := by
              rw [hleftEndpoint]
            _ =
                eVf.hom.1 ≫
                  (FibredCategoryMor.toFunctor f).map
                    ((((canonicalFiberPseudofunctor X.p).map hraw.op.toLoc).toFunctor.map aτ).1) ≫
                    (FibredCategoryMor.toFunctor f).map muQLeft.hom.1 := by
              simp only [Functor.map_comp, Category.assoc]
            _ =
                ((((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map
                    ((FibredCategoryMor.fiberFunctor f T.left).map aτ)).1 ≫
                  eVfQ.hom.1) ≫
                    (FibredCategoryMor.toFunctor f).map muQLeft.hom.1 := by
              simpa only [Category.assoc] using
                congrArg (fun k => k ≫ (FibredCategoryMor.toFunctor f).map muQLeft.hom.1)
                  hleftNaturality.symm
            _ =
                (((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map
                    ((FibredCategoryMor.fiberFunctor f T.left).map aτ)).1 ≫
                  eVfQTotal.hom.1 := by
              simp only [eVfQTotal, Iso.trans_hom, Functor.mapIso_hom,
                FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
                fibredMorphism_fiberFunctor_map_underlying, fiberHom_comp_underlying,
                Category.assoc]
        have hrightEndpoint :
            τV.1.b ≫ muQ.inv.1 =
              muPRight.inv.1 ≫
                (((canonicalFiberPseudofunctor Z.p).map hraw.op.toLoc).toFunctor.map bτ).1 := by
          let Rm := twoFibreProductRightProjection (f ≫ j) (g ≫ j)
          have hτRight :=
            twoFibreProduct_reindex_right_component (f ≫ j) (g ≫ j) hraw τ
          have hRmτ :
              (FibredCategoryMor.fiberFunctor Rm T.left).map τ = bτ := by
            apply Functor.Fiber.hom_ext
            change ((FibredCategoryMor.fiberFunctor Rm T.left).map τ).1 = bτ.1
            simpa only [Rm, bτ] using
              twoFibreProduct_rightProjection_map_underlying (f ≫ j) (g ≫ j) τ
          have hcompRightInv :
              (FibredCategoryMor.pullbackComparison F hraw PT).inv.1.b ≫
                  (FibredCategoryMor.pullbackComparison Rm hraw
                    ((FibredCategoryMor.fiberFunctor F T.left).obj PT)).inv.1 =
                (FibredCategoryMor.pullbackComparison
                  (twoFibreProductRightProjection f g) hraw PT).inv.1 := by
            have h :=
              congrArg (fun φ => φ.1)
                (pullbackComparison_comp_inv F Rm hraw PT)
            simpa only [Rm, F,
              FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
              twoFibreProductMiddlePostcomposeHom_obj_snd,
              twoFibreProductMiddlePostcomposeHom_map_b,
              twoFibreProduct_rightProjection_map_underlying,
              fiberHom_comp_underlying, Category.assoc] using h.symm
          have hcompRightHom :
              (FibredCategoryMor.pullbackComparison Rm hraw
                  ((FibredCategoryMor.fiberFunctor F T.left).obj QT)).hom.1 ≫
                (FibredCategoryMor.pullbackComparison F hraw QT).hom.1.b =
              (FibredCategoryMor.pullbackComparison
                (twoFibreProductRightProjection f g) hraw QT).hom.1 := by
            have h :=
              congrArg (fun φ => φ.1)
                (pullbackComparison_comp_hom F Rm hraw QT)
            simpa only [Rm, F,
              FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
              twoFibreProductMiddlePostcomposeHom_obj_snd,
              twoFibreProductMiddlePostcomposeHom_map_b,
              twoFibreProduct_rightProjection_map_underlying,
              fiberHom_comp_underlying, Category.assoc] using h.symm
          let Mτ :=
            ((canonicalFiberPseudofunctor
              (twoFibreProduct (f ≫ j) (g ≫ j)).p).map hraw.op.toLoc).toFunctor.map τ
          let kP := (FibredCategoryMor.fiberFunctor F V).map κP.hom
          let kQ := (FibredCategoryMor.fiberFunctor F V).map κQ.inv
          have hκQCancel : κQ.inv.1.b ≫ κQ.hom.1.b = 𝟙 _ := by
            exact congrArg (fun φ => φ.1.b) κQ.inv_hom_id
          have hlamQCancel :
              (FibredCategoryMor.pullbackComparison
                  (twoFibreProductRightProjection f g) hraw QT).hom.1 ≫
                (FibredCategoryMor.pullbackComparison
                  (twoFibreProductRightProjection f g) hraw QT).inv.1 = 𝟙 _ := by
            exact congrArg (fun φ => φ.1)
              (FibredCategoryMor.pullbackComparison
                (twoFibreProductRightProjection f g) hraw QT).hom_inv_id
          let RQT := FibredCategoryMor.pullbackComparison
            (twoFibreProductRightProjection f g) hraw QT
          have hκQCancelR :
              κQ.inv.1.b ≫ κQ.hom.1.b =
                𝟙 ((FibredCategoryMor.fiberFunctor
                  (twoFibreProductRightProjection f g) V).obj
                    (hraw ^*[canonicalPullbackChoice (twoFibreProduct f g).p] QT)).1 := by
            simpa only [twoFibreProduct_rightProjection_obj_underlying] using hκQCancel
          have hκQCancel_tail :
              (κQ.inv.1.b ≫ κQ.hom.1.b) ≫ RQT.inv.1 = RQT.inv.1 := by
            calc
              (κQ.inv.1.b ≫ κQ.hom.1.b) ≫ RQT.inv.1 =
                  𝟙 _ ≫ RQT.inv.1 := by
                rw [hκQCancelR]
              _ = RQT.inv.1 := by
                simp only [Category.id_comp]
          have hlamQCancel_tail :
              (((canonicalFiberPseudofunctor Z.p).map hraw.op.toLoc).toFunctor.map
                    bτ).1 ≫ (RQT.hom.1 ≫ RQT.inv.1) =
                (((canonicalFiberPseudofunctor Z.p).map hraw.op.toLoc).toFunctor.map
                    bτ).1 := by
            calc
              (((canonicalFiberPseudofunctor Z.p).map hraw.op.toLoc).toFunctor.map
                    bτ).1 ≫ (RQT.hom.1 ≫ RQT.inv.1) =
                  (((canonicalFiberPseudofunctor Z.p).map hraw.op.toLoc).toFunctor.map
                    bτ).1 ≫ 𝟙 _ := by
                simpa only [RQT] using
                  congrArg
                    (fun k =>
                      (((canonicalFiberPseudofunctor Z.p).map hraw.op.toLoc).toFunctor.map
                        bτ).1 ≫ k)
                    hlamQCancel
              _ =
                  (((canonicalFiberPseudofunctor Z.p).map hraw.op.toLoc).toFunctor.map
                    bτ).1 := by
                simp only [Category.comp_id]
          have hcomponent :
              (kP.1 ≫ (FibredCategoryMor.pullbackComparison F hraw PT).inv.1 ≫
                  Mτ.1 ≫ (FibredCategoryMor.pullbackComparison F hraw QT).hom.1 ≫
                  kQ.1).b ≫
                (κQ.hom.1.b ≫
                  (FibredCategoryMor.pullbackComparison
                    (twoFibreProductRightProjection f g) hraw QT).inv.1) =
              (κP.hom.1.b ≫
                (FibredCategoryMor.pullbackComparison
                  (twoFibreProductRightProjection f g) hraw PT).inv.1) ≫
                (((canonicalFiberPseudofunctor Z.p).map hraw.op.toLoc).toFunctor.map
                  bτ).1 := by
            calc
              (kP.1 ≫ (FibredCategoryMor.pullbackComparison F hraw PT).inv.1 ≫
                  Mτ.1 ≫ (FibredCategoryMor.pullbackComparison F hraw QT).hom.1 ≫
                  kQ.1).b ≫
                (κQ.hom.1.b ≫
                  (FibredCategoryMor.pullbackComparison
                    (twoFibreProductRightProjection f g) hraw QT).inv.1) =
                κP.hom.1.b ≫
                  (FibredCategoryMor.pullbackComparison F hraw PT).inv.1.b ≫
                    Mτ.1.b ≫
                      (FibredCategoryMor.pullbackComparison F hraw QT).hom.1.b ≫
                        κQ.inv.1.b ≫ κQ.hom.1.b ≫
                          (FibredCategoryMor.pullbackComparison
                            (twoFibreProductRightProjection f g) hraw QT).inv.1 := by
                  simp only [kP, kQ, F,
                    FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
                    twoFibreProductHom_comp_b,
                    twoFibreProductMiddlePostcomposeHom_fiber_map_b,
                    Category.assoc]
              _ =
                κP.hom.1.b ≫
                  (FibredCategoryMor.pullbackComparison F hraw PT).inv.1.b ≫
                    Mτ.1.b ≫
                      (FibredCategoryMor.pullbackComparison F hraw QT).hom.1.b ≫
                        (FibredCategoryMor.pullbackComparison
                          (twoFibreProductRightProjection f g) hraw QT).inv.1 := by
                  calc
                    κP.hom.1.b ≫
                        (FibredCategoryMor.pullbackComparison F hraw PT).inv.1.b ≫
                          Mτ.1.b ≫
                            (FibredCategoryMor.pullbackComparison F hraw QT).hom.1.b ≫
                              κQ.inv.1.b ≫ κQ.hom.1.b ≫
                                (FibredCategoryMor.pullbackComparison
                                  (twoFibreProductRightProjection f g) hraw QT).inv.1 =
                      κP.hom.1.b ≫
                        (FibredCategoryMor.pullbackComparison F hraw PT).inv.1.b ≫
                          Mτ.1.b ≫
                            (FibredCategoryMor.pullbackComparison F hraw QT).hom.1.b ≫
                              (κQ.inv.1.b ≫ κQ.hom.1.b) ≫
                                (FibredCategoryMor.pullbackComparison
                                  (twoFibreProductRightProjection f g) hraw QT).inv.1 := by
                        simp only [Category.assoc]
                    _ =
                      κP.hom.1.b ≫
                        (FibredCategoryMor.pullbackComparison F hraw PT).inv.1.b ≫
                          Mτ.1.b ≫
                            (FibredCategoryMor.pullbackComparison F hraw QT).hom.1.b ≫
                              RQT.inv.1 := by
                        rw [hκQCancel_tail]
                    _ =
                      κP.hom.1.b ≫
                        (FibredCategoryMor.pullbackComparison F hraw PT).inv.1.b ≫
                          Mτ.1.b ≫
                            (FibredCategoryMor.pullbackComparison F hraw QT).hom.1.b ≫
                              (FibredCategoryMor.pullbackComparison
                                (twoFibreProductRightProjection f g) hraw QT).inv.1 := by
                        rfl
              _ =
                κP.hom.1.b ≫
                  (FibredCategoryMor.pullbackComparison F hraw PT).inv.1.b ≫
                    ((FibredCategoryMor.pullbackComparison Rm hraw
                        ((FibredCategoryMor.fiberFunctor F T.left).obj PT)).inv ≫
                      (((canonicalFiberPseudofunctor Z.p).map hraw.op.toLoc).toFunctor.map
                        bτ) ≫
                      (FibredCategoryMor.pullbackComparison Rm hraw
                        ((FibredCategoryMor.fiberFunctor F T.left).obj QT)).hom).1 ≫
                      (FibredCategoryMor.pullbackComparison F hraw QT).hom.1.b ≫
                        (FibredCategoryMor.pullbackComparison
                          (twoFibreProductRightProjection f g) hraw QT).inv.1 := by
                  rw [hτRight, hRmτ]
              _ =
                κP.hom.1.b ≫
                  ((FibredCategoryMor.pullbackComparison F hraw PT).inv.1.b ≫
                    (FibredCategoryMor.pullbackComparison Rm hraw
                      ((FibredCategoryMor.fiberFunctor F T.left).obj PT)).inv.1) ≫
                    (((canonicalFiberPseudofunctor Z.p).map hraw.op.toLoc).toFunctor.map
                      bτ).1 ≫
                      ((FibredCategoryMor.pullbackComparison Rm hraw
                        ((FibredCategoryMor.fiberFunctor F T.left).obj QT)).hom.1 ≫
                        (FibredCategoryMor.pullbackComparison F hraw QT).hom.1.b) ≫
                        (FibredCategoryMor.pullbackComparison
                          (twoFibreProductRightProjection f g) hraw QT).inv.1 := by
                  simp only [fiberHom_comp_underlying, Category.assoc]
              _ =
                κP.hom.1.b ≫
                  (FibredCategoryMor.pullbackComparison
                    (twoFibreProductRightProjection f g) hraw PT).inv.1 ≫
                    (((canonicalFiberPseudofunctor Z.p).map hraw.op.toLoc).toFunctor.map
                      bτ).1 ≫
                      (FibredCategoryMor.pullbackComparison
                        (twoFibreProductRightProjection f g) hraw QT).hom.1 ≫
                        (FibredCategoryMor.pullbackComparison
                          (twoFibreProductRightProjection f g) hraw QT).inv.1 := by
                  rw [hcompRightInv, hcompRightHom]
              _ =
                κP.hom.1.b ≫
                  (FibredCategoryMor.pullbackComparison
                    (twoFibreProductRightProjection f g) hraw PT).inv.1 ≫
                    (((canonicalFiberPseudofunctor Z.p).map hraw.op.toLoc).toFunctor.map
                        bτ).1 := by
                    calc
                      κP.hom.1.b ≫
                          (FibredCategoryMor.pullbackComparison
                            (twoFibreProductRightProjection f g) hraw PT).inv.1 ≫
                            (((canonicalFiberPseudofunctor Z.p).map hraw.op.toLoc).toFunctor.map
                              bτ).1 ≫
                              (FibredCategoryMor.pullbackComparison
                                (twoFibreProductRightProjection f g) hraw QT).hom.1 ≫
                                (FibredCategoryMor.pullbackComparison
                                  (twoFibreProductRightProjection f g) hraw QT).inv.1 =
                        κP.hom.1.b ≫
                          (FibredCategoryMor.pullbackComparison
                            (twoFibreProductRightProjection f g) hraw PT).inv.1 ≫
                            (((canonicalFiberPseudofunctor Z.p).map hraw.op.toLoc).toFunctor.map
                              bτ).1 ≫
                              ((FibredCategoryMor.pullbackComparison
                                (twoFibreProductRightProjection f g) hraw QT).hom.1 ≫
                                (FibredCategoryMor.pullbackComparison
                                  (twoFibreProductRightProjection f g) hraw QT).inv.1) := by
                          simp only [Category.assoc]
                      _ =
                        κP.hom.1.b ≫
                          (FibredCategoryMor.pullbackComparison
                            (twoFibreProductRightProjection f g) hraw PT).inv.1 ≫
                            (((canonicalFiberPseudofunctor Z.p).map hraw.op.toLoc).toFunctor.map
                              bτ).1 := by
                          rw [hlamQCancel_tail]
                      _ =
                        κP.hom.1.b ≫
                          (FibredCategoryMor.pullbackComparison
                            (twoFibreProductRightProjection f g) hraw PT).inv.1 ≫
                            (((canonicalFiberPseudofunctor Z.p).map hraw.op.toLoc).toFunctor.map
                              bτ).1 := by
                          rfl
              _ =
                (κP.hom.1.b ≫
                  (FibredCategoryMor.pullbackComparison
                    (twoFibreProductRightProjection f g) hraw PT).inv.1) ≫
                  (((canonicalFiberPseudofunctor Z.p).map hraw.op.toLoc).toFunctor.map
                    bτ).1 := by
                  simp only [Category.assoc]
          have hτV_component :
              τV.1.b =
                (kP.1 ≫ (FibredCategoryMor.pullbackComparison F hraw PT).inv.1 ≫
                  Mτ.1 ≫ (FibredCategoryMor.pullbackComparison F hraw QT).hom.1 ≫
                  kQ.1).b := by
            have htransport :=
              congrArg (fun φ => φ.1.b) hτV_eq
            simpa only [eFPTotal, eFQTotal, eFPT, eFQT, Mτ, kP, kQ,
              FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
              Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
              Category.assoc] using htransport
          calc
            τV.1.b ≫ muQ.inv.1 =
                (kP.1 ≫ (FibredCategoryMor.pullbackComparison F hraw PT).inv.1 ≫
                  Mτ.1 ≫ (FibredCategoryMor.pullbackComparison F hraw QT).hom.1 ≫
                  kQ.1).b ≫ muQ.inv.1 := by
              rw [hτV_component]
            _ =
              muPRight.inv.1 ≫
                (((canonicalFiberPseudofunctor Z.p).map hraw.op.toLoc).toFunctor.map bτ).1 := by
              simpa only [muQ, muPRight, lamQ, lamPRight, κP, κQ,
                FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
                Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
                twoFibreProduct_rightProjection_map_underlying,
                fiberHom_comp_underlying, Category.assoc] using hcomponent
        have hrightNaturality :
            (FibredCategoryMor.toFunctor g).map
                ((((canonicalFiberPseudofunctor Z.p).map hraw.op.toLoc).toFunctor.map bτ).1) ≫
              eVg.inv.1 =
            eVgP.inv.1 ≫
              (((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map
                ((FibredCategoryMor.fiberFunctor g T.left).map bτ)).1 := by
          simpa only [eVg, eVgP, FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
            fibredMorphism_fiberFunctor_map_underlying, fiberHom_comp_underlying] using
            congrArg (fun φ => φ.1)
              (stack_morphism_pullbackComparison_inv_naturality_over_vertical g hraw bτ)
        have hrightPart :
            (FibredCategoryMor.toFunctor g).map τV.1.b ≫ eVgCancel.inv.1 =
              eVgPTotal.inv.1 ≫
                (((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map
                  ((FibredCategoryMor.fiberFunctor g T.left).map bτ)).1 := by
          calc
            (FibredCategoryMor.toFunctor g).map τV.1.b ≫ eVgCancel.inv.1 =
                (FibredCategoryMor.toFunctor g).map τV.1.b ≫
                  ((FibredCategoryMor.toFunctor g).map muQ.inv.1 ≫ eVg.inv.1) := by
              simp only [eVgCancel, eVgTotal, Iso.trans_inv, Functor.mapIso_inv,
                FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
                fibredMorphism_fiberFunctor_map_underlying,
                fiberHom_comp_underlying, Category.assoc]
            _ =
                (FibredCategoryMor.toFunctor g).map (τV.1.b ≫ muQ.inv.1) ≫ eVg.inv.1 := by
              simp only [Functor.map_comp, Category.assoc]
            _ =
                (FibredCategoryMor.toFunctor g).map
                    (muPRight.inv.1 ≫
                      (((canonicalFiberPseudofunctor Z.p).map hraw.op.toLoc).toFunctor.map
                        bτ).1) ≫ eVg.inv.1 := by
              rw [hrightEndpoint]
            _ =
                (FibredCategoryMor.toFunctor g).map muPRight.inv.1 ≫
                  (FibredCategoryMor.toFunctor g).map
                    ((((canonicalFiberPseudofunctor Z.p).map hraw.op.toLoc).toFunctor.map
                      bτ).1) ≫ eVg.inv.1 := by
              simp only [Functor.map_comp, Category.assoc]
            _ =
                (FibredCategoryMor.toFunctor g).map muPRight.inv.1 ≫
                  (eVgP.inv.1 ≫
                    (((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map
                      ((FibredCategoryMor.fiberFunctor g T.left).map bτ)).1) := by
              rw [hrightNaturality]
            _ =
                ((FibredCategoryMor.toFunctor g).map muPRight.inv.1 ≫ eVgP.inv.1) ≫
                  (((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map
                    ((FibredCategoryMor.fiberFunctor g T.left).map bτ)).1 := by
              simp only [Category.assoc]
            _ =
                eVgPTotal.inv.1 ≫
                  (((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map
                    ((FibredCategoryMor.fiberFunctor g T.left).map bτ)).1 := by
              simp only [eVgPTotal, Iso.trans_inv, Functor.mapIso_inv,
                FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
                fibredMorphism_fiberFunctor_map_underlying,
                fiberHom_comp_underlying, Category.assoc]
        have hcompQT_total :
            (((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map
              (⟨QT.1.comparison, hQTcomparison⟩)).1 =
              (eVfQTotal.hom.1 ≫ QV.1.comparison) ≫ eVgTotal.inv.1 := by
          have hκQcomparison :
              (FibredCategoryMor.toFunctor f).map κQ.symm.hom.1.a ≫
                  QV.1.comparison ≫
                    (FibredCategoryMor.toFunctor g).map κQ.symm.inv.1.b =
                (hraw ^*[canonicalPullbackChoice (twoFibreProduct f g).p] QT).1.comparison := by
            simpa only [QV, κQ, Iso.symm_hom, Iso.symm_inv] using
              twoFibreProduct_comparison_conjugate_of_iso f g κQ.symm
          simpa only [eVfQTotal, eVgTotal, muQLeft, muQ, lamQLeft, lamQ, κQ,
            eVfQ, eVg, QV, TV, FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
            ← hκQcomparison, fibredMorphism_fiberFunctor_map_underlying,
            twoFibreProduct_leftProjection_map_underlying,
            twoFibreProduct_rightProjection_map_underlying, fiberHom_comp_underlying,
            pullbackComparison_comp_hom, pullbackComparison_comp_inv,
            Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
            Functor.map_comp, Category.assoc] using congrArg (fun φ => φ.1) hcompQT
        have hcompPT_total :
            (((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map
              (⟨PT.1.comparison, hPTcomparison⟩)).1 =
              (eVfTotal.hom.1 ≫ PV.1.comparison) ≫ eVgPTotal.inv.1 := by
          have hκPcomparison :
              (FibredCategoryMor.toFunctor f).map κP.symm.hom.1.a ≫
                  PV.1.comparison ≫
                    (FibredCategoryMor.toFunctor g).map κP.symm.inv.1.b =
                (hraw ^*[canonicalPullbackChoice (twoFibreProduct f g).p] PT).1.comparison := by
            simpa only [PV, κP, Iso.symm_hom, Iso.symm_inv] using
              twoFibreProduct_comparison_conjugate_of_iso f g κP.symm
          simpa only [eVfTotal, eVgPTotal, muP, muPRight, lamP, lamPRight, κP,
            eVf, eVgP, PV, TV, FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
            ← hκPcomparison, fibredMorphism_fiberFunctor_map_underlying,
            twoFibreProduct_leftProjection_map_underlying,
            twoFibreProduct_rightProjection_map_underlying, fiberHom_comp_underlying,
            pullbackComparison_comp_hom, pullbackComparison_comp_inv,
            Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
            Functor.map_comp, Category.assoc] using congrArg (fun φ => φ.1) hcompPT
        haveI : IsIso eVfCancel.hom.1 := by
          refine ⟨⟨eVfCancel.inv.1, ?_, ?_⟩⟩
          · exact congrArg (fun φ => φ.1) eVfCancel.hom_inv_id
          · exact congrArg (fun φ => φ.1) eVfCancel.inv_hom_id
        haveI : IsIso eVgCancel.inv.1 := by
          refine ⟨⟨eVgCancel.hom.1, ?_, ?_⟩⟩
          · exact congrArg (fun φ => φ.1) eVgCancel.inv_hom_id
          · exact congrArg (fun φ => φ.1) eVgCancel.hom_inv_id
        apply (cancel_epi eVfCancel.hom.1).1
        apply (cancel_mono eVgCancel.inv.1).1
        calc
          (eVfCancel.hom.1 ≫
              (FibredCategoryMor.toFunctor f).map τV.1.a ≫ QV.1.comparison) ≫
                eVgCancel.inv.1 =
            (((canonicalFiberPseudofunctor Y₀.p).map
               hraw.op.toLoc).toFunctor.map lhs).1 := by
              calc
                (eVfCancel.hom.1 ≫
                    (FibredCategoryMor.toFunctor f).map τV.1.a ≫ QV.1.comparison) ≫
                      eVgCancel.inv.1 =
                    (eVfCancel.hom.1 ≫
                      (FibredCategoryMor.toFunctor f).map τV.1.a) ≫
                        QV.1.comparison ≫ eVgCancel.inv.1 := by
                  simp only [Category.assoc]
                _ =
                    (((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map
                        ((FibredCategoryMor.fiberFunctor f T.left).map aτ)).1 ≫
                      eVfQTotal.hom.1 ≫ QV.1.comparison ≫ eVgCancel.inv.1 := by
                  simpa only [Category.assoc] using
                    congrArg (fun k => k ≫ QV.1.comparison ≫ eVgCancel.inv.1) hleftPart
                _ =
                    (((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map
                        ((FibredCategoryMor.fiberFunctor f T.left).map aτ)).1 ≫
                      ((eVfQTotal.hom.1 ≫ QV.1.comparison) ≫ eVgTotal.inv.1) := by
                  simp only [eVgCancel, Category.assoc]
                _ =
                    (((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map
                        ((FibredCategoryMor.fiberFunctor f T.left).map aτ)).1 ≫
                      (((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map
                          (⟨QT.1.comparison, hQTcomparison⟩)).1 := by
                  rw [← hcompQT_total]
                _ =
                    (((canonicalFiberPseudofunctor Y₀.p).map
                       hraw.op.toLoc).toFunctor.map lhs).1 := by
                  simpa only [lhs, fiberHom_comp_underlying] using
                      (congrArg (fun φ => φ.1)
                        (((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map_comp
                          ((FibredCategoryMor.fiberFunctor f T.left).map aτ)
                          (show
                            (FibredCategoryMor.fiberFunctor f T.left).obj QTfst ⟶
                              (FibredCategoryMor.fiberFunctor g T.left).obj QTsnd from
                            ⟨QT.1.comparison, hQTcomparison⟩))).symm
          _ =
            (((canonicalFiberPseudofunctor Y₀.p).map
               hraw.op.toLoc).toFunctor.map rhs).1 := by
              exact congrArg (fun φ => φ.1) hhh'
          _ =
            (eVfCancel.hom.1 ≫ PV.1.comparison ≫
              (FibredCategoryMor.toFunctor g).map τV.1.b) ≫ eVgCancel.inv.1 := by
              calc
                (((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map
                    rhs).1 =
                      (((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map
                          (⟨PT.1.comparison, hPTcomparison⟩)).1 ≫
                    (((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map
                          ((FibredCategoryMor.fiberFunctor g T.left).map bτ)).1 := by
                    simpa only [rhs, fiberHom_comp_underlying] using
                        congrArg (fun φ => φ.1)
                          (((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map_comp
                            (show
                              (FibredCategoryMor.fiberFunctor f T.left).obj PTfst ⟶
                                (FibredCategoryMor.fiberFunctor g T.left).obj PTsnd from
                              ⟨PT.1.comparison, hPTcomparison⟩)
                            ((FibredCategoryMor.fiberFunctor g T.left).map bτ))
                _ =
                    ((eVfTotal.hom.1 ≫ PV.1.comparison) ≫ eVgPTotal.inv.1) ≫
                      (((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map
                        ((FibredCategoryMor.fiberFunctor g T.left).map bτ)).1 := by
                  rw [hcompPT_total]
                _ =
                    (eVfCancel.hom.1 ≫ PV.1.comparison) ≫
                      (eVgPTotal.inv.1 ≫
                        (((canonicalFiberPseudofunctor Y₀.p).map hraw.op.toLoc).toFunctor.map
                          ((FibredCategoryMor.fiberFunctor g T.left).map bτ)).1) := by
                  simp only [eVfCancel, Category.assoc]
                _ =
                    (eVfCancel.hom.1 ≫ PV.1.comparison) ≫
                      ((FibredCategoryMor.toFunctor g).map τV.1.b ≫ eVgCancel.inv.1) := by
                  rw [← hrightPart]
                _ =
                    (eVfCancel.hom.1 ≫ PV.1.comparison ≫
                      (FibredCategoryMor.toFunctor g).map τV.1.b) ≫ eVgCancel.inv.1 := by
                  simp only [Category.assoc]
      let σVraw : PV.1 ⟶ QV.1 :=
        { base := τV.1.base
          a := τV.1.a
          a_over := τV.1.a_over
          b := τV.1.b
          b_over := τV.1.b_over
          comm := ⟨hcommV⟩ }
      have hσV_over :
          (twoFibreProduct f g).p.IsHomLift (𝟙 ((𝟭 C).obj TV.left)) σVraw := by
        have hτV_lift :
            (twoFibreProduct (f ≫ j) (g ≫ j)).p.IsHomLift
              (𝟙 ((𝟭 C).obj TV.left)) τV.1 :=
          τV.2
        letI :
            (twoFibreProduct (f ≫ j) (g ≫ j)).p.IsHomLift
              (𝟙 ((𝟭 C).obj TV.left)) τV.1 :=
          hτV_lift
        have hbase :
            τV.1.base =
              eqToHom PV.2 ≫ (𝟙 ((𝟭 C).obj TV.left)) ≫ eqToHom QV.2.symm := by
          simpa only [FibredCategoryOver.twoFibreProduct] using
            (IsHomLift.fac' ((twoFibreProduct (f ≫ j) (g ≫ j)).p)
              (𝟙 ((𝟭 C).obj TV.left)) τV.1)
        refine IsHomLift.of_fac' (twoFibreProduct f g).p
          (𝟙 ((𝟭 C).obj TV.left)) σVraw PV.2 QV.2 ?_
        simpa only [FibredCategoryOver.twoFibreProduct, σVraw] using hbase
      let σV : PV ⟶ QV := ⟨σVraw, hσV_over⟩
      refine ⟨σV, ?_⟩
      have hsV_cover :
          (((canonicalFiberPseudofunctor (twoFibreProduct (f ≫ j) (g ≫ j)).p).presheafHom
              ((FibredCategoryMor.fiberFunctor F U).obj P)
              ((FibredCategoryMor.fiberFunctor F U).obj Q)).map
            (Over.homMk h (by simp [TV]) : TV ⟶ T).op) s = sV := by
        let PH :=
          ((canonicalFiberPseudofunctor (twoFibreProduct (f ≫ j) (g ≫ j)).p).presheafHom
            ((FibredCategoryMor.fiberFunctor F U).obj P)
            ((FibredCategoryMor.fiberFunctor F U).obj Q))
        have hι : (Over.homMk h (by simp [TV]) : TV ⟶ T) = ι := by
          ext
          simp [ι, hraw]
        change PH.map (Over.homMk h (by simp [TV]) : TV ⟶ T).op s = PH.map ι.op s
        exact congrArg (fun e : TV ⟶ T => PH.map e.op s) hι
      dsimp only [eta]
      change (FibredCategoryMor.fibredMorphismPresheafMap F P Q).app (Opposite.op TV) σV = _
      rw [fibredMorphismPresheafMap_app_pullbackComparison F P Q TV σV]
      change ePV.hom ≫ (FibredCategoryMor.fiberFunctor F TV.left).map σV ≫ eQV.inv =
        (((canonicalFiberPseudofunctor (twoFibreProduct (f ≫ j) (g ≫ j)).p).presheafHom
            ((FibredCategoryMor.fiberFunctor F U).obj P)
            ((FibredCategoryMor.fiberFunctor F U).obj Q)).map
          (Over.homMk h (by simp [TV]) : TV ⟶ T).op) s
      rw [hsV_cover]
      change ePV.hom ≫ (FibredCategoryMor.fiberFunctor F TV.left).map σV ≫ eQV.inv = sV
      have hFσ : (FibredCategoryMor.fiberFunctor F TV.left).map σV = τV := by
        apply twoFibreProductFiberHom_ext_components (f ≫ j) (g ≫ j)
        · rfl
        · rfl
      rw [hFσ]
      change ePV.hom ≫ (ePV.inv ≫ sV ≫ eQV.hom) ≫ eQV.inv = sV
      have hleft :
          ePV.hom ≫ (ePV.inv ≫ sV ≫ eQV.hom) = sV ≫ eQV.hom := by
        simpa only [Category.assoc] using
          (Iso.hom_inv_id_assoc ePV (sV ≫ eQV.hom))
      have hright : (sV ≫ eQV.hom) ≫ eQV.inv = sV :=
        (eQV.comp_inv_eq).2 rfl
      have hleft' :
          ePV.hom ≫ (ePV.inv ≫ sV ≫ eQV.hom) ≫ eQV.inv =
            (sV ≫ eQV.hom) ≫ eQV.inv := by
        calc
          ePV.hom ≫ (ePV.inv ≫ sV ≫ eQV.hom) ≫ eQV.inv =
              (ePV.hom ≫ ePV.inv ≫ sV ≫ eQV.hom) ≫ eQV.inv := by
            simp only [Category.assoc]
          _ = (sV ≫ eQV.hom) ≫ eQV.inv := by
            rw [hleft]
      exact hleft'.trans hright
    · rw [← J.mem_over_iff]
      exact hEq
  let Ulf :=
    (CategoryTheory.uliftFunctor.{max u v, v} : Type v ⥤ Type (max v (max u v)))
  haveI : Presheaf.IsLocallyInjective (J.over U) (Functor.whiskerRight eta Ulf) :=
    CategoryTheory.Functor.isLocallyInjective_whisker_ulift (L := J.over U) (η := eta)
  haveI : Presheaf.IsLocallySurjective (J.over U) (Functor.whiskerRight eta Ulf) :=
    CategoryTheory.Functor.isLocallySurjective_whisker_ulift (L := J.over U) (η := eta)
  have hLargeW : (J.over U).W (Functor.whiskerRight eta Ulf) := by
    let _ : (J.over U).WEqualsLocallyBijective (Type (max v (max u v))) :=
      CategoryTheory.Functor.large_type_WEqualsLocallyBijective (L := J.over U)
    exact GrothendieckTopology.W_of_isLocallyBijective
      (J := J.over U) (f := Functor.whiskerRight eta Ulf)
  exact W_of_whiskerRight_ulift (J.over U) eta hLargeW

/-- Helper for Chap08 Lemma 8 8 4: an equality transport followed by its inverse is the
identity. -/
private theorem eqToHom_symm_comp_eqToHom_local
    {D : Type uE} [Category.{vE} D] {A B : D} (h : A = B) :
    eqToHom h.symm ≫ eqToHom h = 𝟙 B := by
  cases h
  simp

private theorem eqToHom_eq_local
    {D : Type uE} [Category.{vE} D] {A B : D} (h h' : A = B) :
    eqToHom h = eqToHom h' := by
  cases h
  cases h'
  rfl

/-- Helper for Chap08 Lemma 8 8 4: the stored comparison of a target middle object, viewed as an
isomorphism between the two endpoint images under `j`. -/
private noncomputable def twoFibreProductMiddlePostcomposeHom_targetComparisonIso
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    {U : C} (P : (twoFibreProduct (f ≫ j) (g ≫ j)).p.Fiber U) :
    ((FibredCategoryMor.fiberFunctor j U).obj
      ((FibredCategoryMor.fiberFunctor f U).obj
        ⟨P.1.obj.fst.1, by
          rw [P.1.obj.fst.2]
          simpa using P.2⟩)) ≅
      ((FibredCategoryMor.fiberFunctor j U).obj
        ((FibredCategoryMor.fiberFunctor g U).obj
          ⟨P.1.obj.snd.1, by
            rw [P.1.obj.snd.2]
            simpa using P.2⟩)) :=
  { hom := ⟨P.1.comparison, twoFibreProduct_fiber_comparison_over_id (f ≫ j) (g ≫ j) P⟩
    inv := ⟨P.1.obj.iso.inv.1,
      twoFibreProduct_fiber_comparison_inv_over_id (f ≫ j) (g ≫ j) P⟩
    hom_inv_id := by
      apply Functor.Fiber.hom_ext
      exact congrArg (fun φ => φ.1) P.1.obj.iso.hom_inv_id
    inv_hom_id := by
      apply Functor.Fiber.hom_ext
      exact congrArg (fun φ => φ.1) P.1.obj.iso.inv_hom_id }

/-- Helper for Chap08 Lemma 8 8 4: once a target middle comparison is represented by a
source-side isomorphism over the same fibre, the middle-postcomposition map represents that
target object. -/
private noncomputable def twoFibreProductMiddlePostcomposeHom_localObjectIsoOfComparisonIso
    {Y₀ : FibredCategoryOver C} {Y₁ : StackOver J}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    {U : C} (P : (twoFibreProduct (f ≫ j) (g ≫ j)).p.Fiber U)
    (γ :
      ((FibredCategoryMor.fiberFunctor f U).obj
        ⟨P.1.obj.fst.1, by
          rw [P.1.obj.fst.2]
          simpa using P.2⟩) ≅
        ((FibredCategoryMor.fiberFunctor g U).obj
          ⟨P.1.obj.snd.1, by
            rw [P.1.obj.snd.2]
            simpa using P.2⟩))
    (hγ :
      (FibredCategoryMor.fiberFunctor j U).map γ.hom =
        ⟨P.1.comparison, twoFibreProduct_fiber_comparison_over_id (f ≫ j) (g ≫ j) P⟩) :
    ∃ Q : (twoFibreProduct f g).p.Fiber U,
      Nonempty
        (((FibredCategoryMor.fiberFunctor (twoFibreProductMiddlePostcomposeHom f g j) U).obj Q) ≅
          P) := by
  let x : X.p.Fiber U :=
    ⟨P.1.obj.fst.1, by
      rw [P.1.obj.fst.2]
      simpa using P.2⟩
  let z : Z.p.Fiber U :=
    ⟨P.1.obj.snd.1, by
      rw [P.1.obj.snd.2]
      simpa using P.2⟩
  let Qraw : (twoFibreProduct f g).S :=
    { U := U
      obj :=
        { fst := x
          snd := z
          iso := γ } }
  let Q : (twoFibreProduct f g).p.Fiber U := ⟨Qraw, rfl⟩
  have hcomparison :
      ((FibredCategoryMor.toFunctor (twoFibreProductMiddlePostcomposeHom f g j)).obj
          Qraw).comparison =
        P.1.comparison := by
    rw [twoFibreProductMiddlePostcomposeHom_obj_comparison]
    exact congrArg (fun φ => φ.1) hγ
  let homRaw :
      ((FibredCategoryMor.toFunctor (twoFibreProductMiddlePostcomposeHom f g j)).obj Qraw) ⟶
        P.1 :=
    { base := eqToHom P.2.symm
      a := 𝟙 P.1.obj.fst.1
      a_over := by
        refine IsHomLift.of_fac' X.p (eqToHom P.2.symm) (𝟙 P.1.obj.fst.1)
          x.2 P.1.obj.fst.2 ?_
        simp [x]
      b := 𝟙 P.1.obj.snd.1
      b_over := by
        refine IsHomLift.of_fac' Z.p (eqToHom P.2.symm) (𝟙 P.1.obj.snd.1)
          z.2 P.1.obj.snd.2 ?_
        simp [z]
      comm := by
        refine ⟨?_⟩
        have hleftmap :
            (FibredCategoryMor.toBasedFunctor (f ≫ j)).map (𝟙 P.1.obj.fst.1) =
              𝟙 ((FibredCategoryMor.toBasedFunctor (f ≫ j)).obj P.1.obj.fst.1) := by
          change (FibredCategoryMor.toBasedFunctor (f ≫ j)).toFunctor.map
              (𝟙 P.1.obj.fst.1) =
            𝟙 ((FibredCategoryMor.toBasedFunctor (f ≫ j)).obj P.1.obj.fst.1)
          exact Functor.map_id (FibredCategoryMor.toBasedFunctor (f ≫ j)).toFunctor
            P.1.obj.fst.1
        have hrightmap :
            (FibredCategoryMor.toBasedFunctor (g ≫ j)).map (𝟙 P.1.obj.snd.1) =
              𝟙 ((FibredCategoryMor.toBasedFunctor (g ≫ j)).obj P.1.obj.snd.1) := by
          change (FibredCategoryMor.toBasedFunctor (g ≫ j)).toFunctor.map
              (𝟙 P.1.obj.snd.1) =
            𝟙 ((FibredCategoryMor.toBasedFunctor (g ≫ j)).obj P.1.obj.snd.1)
          exact Functor.map_id (FibredCategoryMor.toBasedFunctor (g ≫ j)).toFunctor
            P.1.obj.snd.1
        let source :=
          ((FibredCategoryMor.toFunctor (twoFibreProductMiddlePostcomposeHom f g j)).obj
            Qraw).comparison
        have hleftHead :
            (FibredCategoryMor.toBasedFunctor (f ≫ j)).map (𝟙 P.1.obj.fst.1) ≫
                P.1.comparison =
              P.1.comparison := by
          calc
            (FibredCategoryMor.toBasedFunctor (f ≫ j)).map (𝟙 P.1.obj.fst.1) ≫
                P.1.comparison =
              𝟙 _ ≫ P.1.comparison := congrArg (fun a => a ≫ P.1.comparison) hleftmap
            _ = P.1.comparison := Category.id_comp P.1.comparison
        have hrightTail :
            source =
              source ≫ (FibredCategoryMor.toBasedFunctor (g ≫ j)).map (𝟙 P.1.obj.snd.1) := by
          have h₁ : source = source ≫ 𝟙 _ := (Category.comp_id source).symm
          have h₂ :
              source ≫ 𝟙 _ =
                source ≫ (FibredCategoryMor.toBasedFunctor (g ≫ j)).map (𝟙 P.1.obj.snd.1) :=
            (congrArg (fun b => source ≫ b) hrightmap).symm
          exact h₁.trans h₂
        exact hleftHead.trans (hcomparison.symm.trans hrightTail) }
  let invRaw :
      P.1 ⟶
        ((FibredCategoryMor.toFunctor (twoFibreProductMiddlePostcomposeHom f g j)).obj Qraw) :=
    { base := eqToHom P.2
      a := 𝟙 P.1.obj.fst.1
      a_over := by
        refine IsHomLift.of_fac' X.p (eqToHom P.2) (𝟙 P.1.obj.fst.1)
          P.1.obj.fst.2 x.2 ?_
        simp [x]
      b := 𝟙 P.1.obj.snd.1
      b_over := by
        refine IsHomLift.of_fac' Z.p (eqToHom P.2) (𝟙 P.1.obj.snd.1)
          P.1.obj.snd.2 z.2 ?_
        simp [z]
      comm := by
        refine ⟨?_⟩
        have hleftmap :
            (FibredCategoryMor.toBasedFunctor (f ≫ j)).map (𝟙 P.1.obj.fst.1) =
              𝟙 ((FibredCategoryMor.toBasedFunctor (f ≫ j)).obj P.1.obj.fst.1) := by
          change (FibredCategoryMor.toBasedFunctor (f ≫ j)).toFunctor.map
              (𝟙 P.1.obj.fst.1) =
            𝟙 ((FibredCategoryMor.toBasedFunctor (f ≫ j)).obj P.1.obj.fst.1)
          exact Functor.map_id (FibredCategoryMor.toBasedFunctor (f ≫ j)).toFunctor
            P.1.obj.fst.1
        have hrightmap :
            (FibredCategoryMor.toBasedFunctor (g ≫ j)).map (𝟙 P.1.obj.snd.1) =
              𝟙 ((FibredCategoryMor.toBasedFunctor (g ≫ j)).obj P.1.obj.snd.1) := by
          change (FibredCategoryMor.toBasedFunctor (g ≫ j)).toFunctor.map
              (𝟙 P.1.obj.snd.1) =
            𝟙 ((FibredCategoryMor.toBasedFunctor (g ≫ j)).obj P.1.obj.snd.1)
          exact Functor.map_id (FibredCategoryMor.toBasedFunctor (g ≫ j)).toFunctor
            P.1.obj.snd.1
        let source :=
          ((FibredCategoryMor.toFunctor (twoFibreProductMiddlePostcomposeHom f g j)).obj
            Qraw).comparison
        have hleftHead :
            (FibredCategoryMor.toBasedFunctor (f ≫ j)).map (𝟙 P.1.obj.fst.1) ≫
                source =
              source := by
          calc
            (FibredCategoryMor.toBasedFunctor (f ≫ j)).map (𝟙 P.1.obj.fst.1) ≫
                source =
              𝟙 _ ≫ source := congrArg (fun a => a ≫ source) hleftmap
            _ = source := Category.id_comp source
        have hrightTail :
            P.1.comparison =
              P.1.comparison ≫
                (FibredCategoryMor.toBasedFunctor (g ≫ j)).map (𝟙 P.1.obj.snd.1) := by
          simpa [hrightmap] using (Category.comp_id P.1.comparison).symm
        exact hleftHead.trans (hcomparison.trans hrightTail) }
  have hhom_over :
      (twoFibreProduct (f ≫ j) (g ≫ j)).p.IsHomLift (𝟙 U) homRaw := by
    refine IsHomLift.of_fac (twoFibreProduct (f ≫ j) (g ≫ j)).p
      (𝟙 U) homRaw rfl P.2 ?_
    change 𝟙 U = eqToHom rfl.symm ≫ homRaw.base ≫ eqToHom P.2
    simp [homRaw]
    exact (eq_of_heq (eqToHom_heq_id_dom U U _)).symm
  have hinv_over :
      (twoFibreProduct (f ≫ j) (g ≫ j)).p.IsHomLift (𝟙 U) invRaw := by
    refine IsHomLift.of_fac' (twoFibreProduct (f ≫ j) (g ≫ j)).p
      (𝟙 U) invRaw P.2 rfl ?_
    change invRaw.base = eqToHom P.2 ≫ 𝟙 U ≫ eqToHom rfl.symm
    simp [invRaw]
    apply eqToHom_eq_local
  let hom : ((FibredCategoryMor.fiberFunctor
      (twoFibreProductMiddlePostcomposeHom f g j) U).obj Q) ⟶ P := ⟨homRaw, hhom_over⟩
  let inv : P ⟶
      ((FibredCategoryMor.fiberFunctor (twoFibreProductMiddlePostcomposeHom f g j) U).obj Q) :=
    ⟨invRaw, hinv_over⟩
  refine ⟨Q, ⟨?_⟩⟩
  exact
    { hom := hom
      inv := inv
      hom_inv_id := by
        apply twoFibreProductFiberHom_ext_components (f ≫ j) (g ≫ j)
        · change homRaw.a ≫ invRaw.a = 𝟙 P.1.obj.fst.1
          exact Category.id_comp _
        · change homRaw.b ≫ invRaw.b = 𝟙 P.1.obj.snd.1
          exact Category.id_comp _
      inv_hom_id := by
        apply twoFibreProductFiberHom_ext_components (f ≫ j) (g ≫ j)
        · change invRaw.a ≫ homRaw.a = 𝟙 P.1.obj.fst.1
          exact Category.id_comp _
        · change invRaw.b ≫ homRaw.b = 𝟙 P.1.obj.snd.1
          exact Category.id_comp _ }

/-- Helper for Chap08 Lemma 8 8 4: the middle-postcomposition map is locally essentially
surjective on objects by locally lifting only the compatibility object through the middle
stackification map. -/
private theorem twoFibreProductMiddlePostcomposeHom_locallyEssentiallySurjectiveOnObjects
    {Y₀ : FibredCategoryOver.{u, v, max u v, v} C}
    {Y₁ : StackOver.{u, v, max u v, v} J}
    (f : FibredCategoryMor X Y₀) (g : FibredCategoryMor Z Y₀)
    (j : FibredCategoryMor Y₀ Y₁)
    (hj : FibredCategoryMor.IsStackification j) :
    FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J
      (twoFibreProductMiddlePostcomposeHom f g j) := by
  classical
  intro U P
  let x : Y₀.p.Fiber U :=
    (FibredCategoryMor.fiberFunctor f U).obj
      ⟨P.1.obj.fst.1, by
        rw [P.1.obj.fst.2]
        simpa using P.2⟩
  let y : Y₀.p.Fiber U :=
    (FibredCategoryMor.fiberFunctor g U).obj
      ⟨P.1.obj.snd.1, by
        rw [P.1.obj.snd.2]
        simpa using P.2⟩
  let d := twoFibreProductMiddlePostcomposeHom_targetComparisonIso f g j P
  haveI : (J.over U).WEqualsLocallyBijective (Type v) :=
    over_WEqualsLocallyBijective_small (J := J) U
  obtain ⟨S, hS⟩ := stackificationHomImageBaseCover_lift_iso (J := J) j hj x y d
  refine ⟨S, ?_⟩
  intro I
  letI : (twoFibreProduct (f ≫ j) (g ≫ j)).p.IsFibered :=
    FibredCategoryOver.isFibred (twoFibreProduct (f ≫ j) (g ≫ j))
  let PI : (twoFibreProduct (f ≫ j) (g ≫ j)).p.Fiber I.Y :=
    I.f ^*[canonicalPullbackChoice (twoFibreProduct (f ≫ j) (g ≫ j)).p] P
  obtain ⟨γ, hγ⟩ := hS I
  let HL := twoFibreProductLeftProjection (f ≫ j) (g ≫ j) ≫ f
  let HR := twoFibreProductRightProjection (f ≫ j) (g ≫ j) ≫ g
  let eL := FibredCategoryMor.pullbackComparison HL I.f P
  let eR := FibredCategoryMor.pullbackComparison HR I.f P
  let γ' :
      ((FibredCategoryMor.fiberFunctor f I.Y).obj
        ⟨PI.1.obj.fst.1, by
          rw [PI.1.obj.fst.2]
          simpa using PI.2⟩) ≅
        ((FibredCategoryMor.fiberFunctor g I.Y).obj
          ⟨PI.1.obj.snd.1, by
            rw [PI.1.obj.snd.2]
            simpa using PI.2⟩) :=
    eL.symm ≪≫ γ ≪≫ eR
  have hγ' :
      (FibredCategoryMor.fiberFunctor j I.Y).map γ'.hom =
        ⟨PI.1.comparison, twoFibreProduct_fiber_comparison_over_id (f ≫ j) (g ≫ j) PI⟩ := by
    let JI := FibredCategoryMor.fiberFunctor j I.Y
    let M := ((canonicalFiberPseudofunctor Y₁.p).map I.f.op.toLoc).toFunctor
    let pcx := FibredCategoryMor.pullbackComparison j I.f x
    let pcy := FibredCategoryMor.pullbackComparison j I.f y
    let L := twoFibreProductLeftProjection (f ≫ j) (g ≫ j)
    let R := twoFibreProductRightProjection (f ≫ j) (g ≫ j)
    let HLj := L ≫ (f ≫ j)
    let HRj := R ≫ (g ≫ j)
    let pcHLj := FibredCategoryMor.pullbackComparison HLj I.f P
    let pcHRj := FibredCategoryMor.pullbackComparison HRj I.f P
    have hboundary :=
      twoFibreProduct_comparison_reindex_boundary (f ≫ j) (g ≫ j) I.f P
    have hleftComp : JI.map eL.inv ≫ pcx.inv = pcHLj.inv := by
      simpa only [JI, pcx, pcHLj, HLj, L, HL, x, eL, FibredCategoryMor.fiberFunctor,
        BasedFunctor.fiberFunctor, Category.assoc] using
        (pullbackComparison_comp_inv HL j I.f P).symm
    have hrightComp : pcy.hom ≫ JI.map eR.hom = pcHRj.hom := by
      simpa only [JI, pcy, pcHRj, HRj, R, HR, y, eR, FibredCategoryMor.fiberFunctor,
        BasedFunctor.fiberFunctor, Category.assoc] using
        (pullbackComparison_comp_hom HR j I.f P).symm
    have hmid :
        JI.map eL.inv ≫ JI.map γ.hom ≫ JI.map eR.hom =
          JI.map eL.inv ≫ (pcx.inv ≫ M.map d.hom ≫ pcy.hom) ≫ JI.map eR.hom := by
      simpa only [JI, pcx, pcy, M] using
        congrArg (fun m => JI.map eL.inv ≫ m ≫ JI.map eR.hom) hγ
    have hcombine :
        (JI.map eL.inv ≫ pcx.inv) ≫ M.map d.hom ≫
            (pcy.hom ≫ JI.map eR.hom) =
          pcHLj.inv ≫ M.map d.hom ≫ pcHRj.hom := by
      rw [hleftComp]
      simpa only [Category.assoc] using
        congrArg (fun φ => pcHLj.inv ≫ M.map d.hom ≫ φ) hrightComp
    have hstart :
        (FibredCategoryMor.fiberFunctor j I.Y).map γ'.hom =
          JI.map eL.inv ≫ JI.map γ.hom ≫ JI.map eR.hom := by
      simp only [γ', JI, Iso.trans_hom, Iso.symm_hom, Functor.map_comp]
      rfl
    have htoBoundary :
        JI.map eL.inv ≫ JI.map γ.hom ≫ JI.map eR.hom =
          pcHLj.inv ≫ M.map d.hom ≫ pcHRj.hom := by
      calc
        JI.map eL.inv ≫ JI.map γ.hom ≫ JI.map eR.hom =
            JI.map eL.inv ≫ (pcx.inv ≫ M.map d.hom ≫ pcy.hom) ≫
              JI.map eR.hom := hmid
        _ = (JI.map eL.inv ≫ pcx.inv) ≫ M.map d.hom ≫
              (pcy.hom ≫ JI.map eR.hom) := by
          simp only [Category.assoc]
        _ = pcHLj.inv ≫ M.map d.hom ≫ pcHRj.hom := hcombine
    have htarget :
        pcHLj.inv ≫ M.map d.hom ≫ pcHRj.hom =
          ⟨PI.1.comparison,
            twoFibreProduct_fiber_comparison_over_id (f ≫ j) (g ≫ j) PI⟩ := by
      have hboundary' :
          M.map d.hom =
            pcHLj.hom ≫
              ⟨PI.1.comparison,
                twoFibreProduct_fiber_comparison_over_id (f ≫ j) (g ≫ j) PI⟩ ≫
                pcHRj.inv := by
        simpa only [M, d, twoFibreProductMiddlePostcomposeHom_targetComparisonIso,
          pcHLj, pcHRj, HLj, HRj, L, R, PI] using hboundary
      calc
        pcHLj.inv ≫ M.map d.hom ≫ pcHRj.hom =
            pcHLj.inv ≫
              (pcHLj.hom ≫
                ⟨PI.1.comparison,
                  twoFibreProduct_fiber_comparison_over_id (f ≫ j) (g ≫ j) PI⟩ ≫
                pcHRj.inv) ≫ pcHRj.hom := by
          simpa only [Category.assoc] using
            congrArg (fun φ => pcHLj.inv ≫ φ ≫ pcHRj.hom) hboundary'
        _ = ⟨PI.1.comparison,
              twoFibreProduct_fiber_comparison_over_id (f ≫ j) (g ≫ j) PI⟩ := by
          simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.id_comp,
            Category.comp_id]
    exact hstart.trans (htoBoundary.trans htarget)
  exact twoFibreProductMiddlePostcomposeHom_localObjectIsoOfComparisonIso f g j PI γ' hγ'

/-- Helper for Chap08 Lemma 8 8 4: if the two endpoint objects of a target
two-fibre-product object are represented by source endpoint objects, then the direct endpoint
replacement map represents the target object over the same fibre. -/
private theorem twoFibreProductEndpointReplacementDirectHom_localObjectLift
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    {U : C}
    (T : (twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor).p.Fiber U)
    (x : X.p.Fiber U) (z : Z.p.Fiber U)
    (ex : (FibredCategoryMor.fiberFunctor i U).obj x ≅
      (FibredCategoryMor.fiberFunctor
        (twoFibreProductLeftProjection f'.toFibredCategoryMor g'.toFibredCategoryMor) U).obj T)
    (ez : (FibredCategoryMor.fiberFunctor k U).obj z ≅
      (FibredCategoryMor.fiberFunctor
        (twoFibreProductRightProjection f'.toFibredCategoryMor g'.toFibredCategoryMor) U).obj T) :
    ∃ Q : (twoFibreProduct (f ≫ j) (g ≫ j)).p.Fiber U,
      Nonempty
        (((FibredCategoryMor.fiberFunctor
          (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) U).obj Q) ≅ T) := by
  rcases T with ⟨Traw, hTraw⟩
  subst U
  let U : C := (twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor).p.obj Traw
  let T : (twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor).p.Fiber
      U :=
    ⟨Traw, rfl⟩
  let E := twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β
  let αx := basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) U x
  let βz := basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso β) U z
  let tComp := twoFibreProduct_fiber_comparisonIso f'.toFibredCategoryMor g'.toFibredCategoryMor T
  let comp :
      ((FibredCategoryMor.fiberFunctor (f ≫ j) U).obj x) ≅
        ((FibredCategoryMor.fiberFunctor (g ≫ j) U).obj z) :=
    αx.symm ≪≫
      (FibredCategoryMor.fiberFunctor f'.toFibredCategoryMor U).mapIso ex ≪≫
        tComp ≪≫
          (FibredCategoryMor.fiberFunctor g'.toFibredCategoryMor U).mapIso ez.symm ≪≫
            βz
  let Qraw : (twoFibreProduct (f ≫ j) (g ≫ j)).S :=
    { U := U
      obj :=
        { fst := x
          snd := z
          iso := comp } }
  let Q : (twoFibreProduct (f ≫ j) (g ≫ j)).p.Fiber U := ⟨Qraw, rfl⟩
  refine ⟨Q, ⟨?_⟩⟩
  let EQraw := (FibredCategoryMor.toFunctor E).obj Qraw
  have hcomparison :
      EQraw.comparison =
        (FibredCategoryMor.toFunctor f'.toFibredCategoryMor).map ex.hom.1 ≫
          T.1.comparison ≫
            (FibredCategoryMor.toFunctor g'.toFibredCategoryMor).map ez.inv.1 := by
    have hα_cancel :
        (FibredCategoryMor.basedFunctorIsoOfOwnerIso α).hom.app x.1 ≫
            (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) U x).inv.1 =
          𝟙 _ := by
      exact congrArg (fun φ => φ.1)
        (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) U x).hom_inv_id
    have hβ_cancel :
        (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso β) U z).hom.1 ≫
            (FibredCategoryMor.basedFunctorIsoOfOwnerIso β).inv.app z.1 =
          𝟙 _ := by
      exact congrArg (fun φ => φ.1)
        (basedFiberFunctorIso (FibredCategoryMor.basedFunctorIsoOfOwnerIso β) U z).hom_inv_id
    dsimp only [EQraw, E]
    rw [twoFibreProductEndpointReplacementDirectHom_obj_comparison]
    simp only [Qraw, CategoryOver.ExplicitTwoFibreProductObject.comparison,
      comp, αx, βz, tComp, twoFibreProduct_fiber_comparisonIso,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      fiberHom_comp_underlying, fibredMorphism_fiberFunctor_map_underlying]
    simp only [FibredCategoryMor.toFunctor]
    let A :=
      (FibredCategoryMor.toBasedFunctor f'.toFibredCategoryMor).map ex.hom.1
    let B :=
      CategoryOver.ExplicitTwoFibreProductObject.comparison
        (FibredCategoryMor.toBasedFunctor f'.toFibredCategoryMor)
        (FibredCategoryMor.toBasedFunctor g'.toFibredCategoryMor) T.1
    let Cg :=
      (FibredCategoryMor.toBasedFunctor g'.toFibredCategoryMor).map ez.inv.1
    let αh := (FibredCategoryMor.basedFunctorIsoOfOwnerIso α).hom.app x.1
    let αi := (basedFiberFunctorIso
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso α) U x).inv.1
    let βh := (basedFiberFunctorIso
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso β) U z).hom.1
    let βi := (FibredCategoryMor.basedFunctorIsoOfOwnerIso β).inv.app z.1
    have hα_cancel' : αh ≫ αi = 𝟙 _ := hα_cancel
    have hβ_cancel' : βh ≫ βi = 𝟙 _ := hβ_cancel
    have hβ_cancel'' :
        βh ≫ βi =
          𝟙 ((FibredCategoryMor.toBasedFunctor g'.toFibredCategoryMor).obj
            ((FibredCategoryMor.fiberFunctor k U).obj z).1) := by
      simpa only [βh, βi, FibredCategoryMor.fiberFunctor,
        BasedFunctor.fiberFunctor, BasedFunctor.comp] using hβ_cancel'
    have hright :
        A ≫ B ≫ Cg ≫ βh ≫ βi = A ≫ B ≫ Cg := by
      calc
        A ≫ B ≫ Cg ≫ βh ≫ βi =
            (A ≫ B ≫ Cg) ≫ (βh ≫ βi) := by
          simp only [Category.assoc]
        _ = (A ≫ B ≫ Cg) ≫
            𝟙 ((FibredCategoryMor.toBasedFunctor g'.toFibredCategoryMor).obj
              ((FibredCategoryMor.fiberFunctor k U).obj z).1) := by
          simpa only [Category.assoc] using
            congrArg (fun t => (A ≫ B ≫ Cg) ≫ t) hβ_cancel''
        _ = A ≫ B ≫ Cg := by
          exact Category.comp_id (A ≫ B ≫ Cg)
    have hleft :
        (αh ≫ αi) ≫ A ≫ B ≫ Cg ≫ βh ≫ βi =
          A ≫ B ≫ Cg ≫ βh ≫ βi := by
      rw [hα_cancel']
      simpa only [FibredCategoryMor.fiberFunctor, BasedFunctor.fiberFunctor,
        BasedFunctor.comp] using
        (Category.id_comp (A ≫ B ≫ Cg ≫ βh ≫ βi))
    have hαtail :
        αh ≫ αi ≫ A ≫ B ≫ Cg ≫ βh ≫ βi =
          A ≫ B ≫ Cg ≫ βh ≫ βi := by
      simpa only [Category.assoc] using hleft
    change αh ≫ (αi ≫ A ≫ B ≫ Cg ≫ βh) ≫ βi = A ≫ B ≫ Cg
    calc
      αh ≫ (αi ≫ A ≫ B ≫ Cg ≫ βh) ≫ βi =
          αh ≫ αi ≫ A ≫ B ≫ Cg ≫ βh ≫ βi := by
        simp only [Category.assoc]
      _ = A ≫ B ≫ Cg := hαtail.trans hright
  let homRaw : EQraw ⟶ T.1 :=
    { base := 𝟙 U
      a := ex.hom.1
      a_over := ex.hom.2
      b := ez.hom.1
      b_over := ez.hom.2
      comm := by
        refine ⟨?_⟩
        have hright_cancel :
            (FibredCategoryMor.toBasedFunctor g'.toFibredCategoryMor).map ez.inv.1 ≫
                (FibredCategoryMor.toBasedFunctor g'.toFibredCategoryMor).map ez.hom.1 =
              𝟙 _ := by
          rw [← Functor.map_comp]
          have h : ez.inv.1 ≫ ez.hom.1 = 𝟙 _ :=
            congrArg (fun φ => φ.1) ez.inv_hom_id
          rw [h]
          simp only [Functor.map_id]
        rw [hcomparison]
        simp only [FibredCategoryMor.toFunctor]
        calc
          (FibredCategoryMor.toBasedFunctor f'.toFibredCategoryMor).map ex.hom.1 ≫
              T.1.comparison =
            ((FibredCategoryMor.toBasedFunctor f'.toFibredCategoryMor).map ex.hom.1 ≫
                T.1.comparison) ≫ 𝟙 _ := by
            rw [Category.comp_id]
          _ =
            ((FibredCategoryMor.toBasedFunctor f'.toFibredCategoryMor).map ex.hom.1 ≫
                T.1.comparison) ≫
              ((FibredCategoryMor.toBasedFunctor g'.toFibredCategoryMor).map ez.inv.1 ≫
                (FibredCategoryMor.toBasedFunctor g'.toFibredCategoryMor).map ez.hom.1) := by
            simpa only [Category.assoc] using congrArg
              (fun t =>
                ((FibredCategoryMor.toBasedFunctor f'.toFibredCategoryMor).map ex.hom.1 ≫
                    T.1.comparison) ≫ t)
              hright_cancel.symm
          _ =
            ((FibredCategoryMor.toBasedFunctor f'.toFibredCategoryMor).map ex.hom.1 ≫
                T.1.comparison ≫
                  (FibredCategoryMor.toBasedFunctor g'.toFibredCategoryMor).map ez.inv.1) ≫
                (FibredCategoryMor.toBasedFunctor g'.toFibredCategoryMor).map ez.hom.1 := by
            simp only [Category.assoc] }
  let invRaw : T.1 ⟶ EQraw :=
    { base := 𝟙 U
      a := ex.inv.1
      a_over := ex.inv.2
      b := ez.inv.1
      b_over := ez.inv.2
      comm := by
        refine ⟨?_⟩
        have hleft_cancel :
            (FibredCategoryMor.toBasedFunctor f'.toFibredCategoryMor).map ex.inv.1 ≫
                (FibredCategoryMor.toBasedFunctor f'.toFibredCategoryMor).map ex.hom.1 =
              𝟙 _ := by
          rw [← Functor.map_comp]
          have h : ex.inv.1 ≫ ex.hom.1 = 𝟙 _ :=
            congrArg (fun φ => φ.1) ex.inv_hom_id
          rw [h]
          simp only [Functor.map_id]
        rw [hcomparison]
        simp only [FibredCategoryMor.toFunctor]
        calc
          (FibredCategoryMor.toBasedFunctor f'.toFibredCategoryMor).map ex.inv.1 ≫
              ((FibredCategoryMor.toBasedFunctor f'.toFibredCategoryMor).map ex.hom.1 ≫
                T.1.comparison ≫
                  (FibredCategoryMor.toBasedFunctor g'.toFibredCategoryMor).map ez.inv.1) =
            ((FibredCategoryMor.toBasedFunctor f'.toFibredCategoryMor).map ex.inv.1 ≫
                (FibredCategoryMor.toBasedFunctor f'.toFibredCategoryMor).map ex.hom.1) ≫
                  T.1.comparison ≫
                    (FibredCategoryMor.toBasedFunctor g'.toFibredCategoryMor).map ez.inv.1 := by
            simp only [Category.assoc]
          _ =
              T.1.comparison ≫
                (FibredCategoryMor.toBasedFunctor g'.toFibredCategoryMor).map ez.inv.1 := by
            rw [hleft_cancel]
            rw [Category.id_comp]
            rfl }
  have hhom_over :
      (twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor).p.IsHomLift
        (𝟙 U) homRaw := by
    refine IsHomLift.of_fac (twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor).p
      (𝟙 U) homRaw rfl rfl ?_
    change 𝟙 U = eqToHom rfl.symm ≫ (𝟙 U) ≫ eqToHom rfl
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  have hinv_over :
      (twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor).p.IsHomLift
        (𝟙 U) invRaw := by
    refine IsHomLift.of_fac' (twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor).p
      (𝟙 U) invRaw rfl rfl ?_
    change 𝟙 U = eqToHom rfl ≫ (𝟙 U) ≫ eqToHom rfl.symm
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  let hom : ((FibredCategoryMor.fiberFunctor E U).obj Q) ⟶ T := ⟨homRaw, hhom_over⟩
  let inv : T ⟶ ((FibredCategoryMor.fiberFunctor E U).obj Q) := ⟨invRaw, hinv_over⟩
  exact
    { hom := hom
      inv := inv
      hom_inv_id := by
        apply twoFibreProductFiberHom_ext_components
          f'.toFibredCategoryMor g'.toFibredCategoryMor
        · change homRaw.a ≫ invRaw.a = 𝟙 EQraw.obj.fst.1
          exact congrArg (fun φ => φ.1) ex.hom_inv_id
        · change homRaw.b ≫ invRaw.b = 𝟙 EQraw.obj.snd.1
          exact congrArg (fun φ => φ.1) ez.hom_inv_id
      inv_hom_id := by
        apply twoFibreProductFiberHom_ext_components
          f'.toFibredCategoryMor g'.toFibredCategoryMor
        · change invRaw.a ≫ homRaw.a = 𝟙 T.1.obj.fst.1
          exact congrArg (fun φ => φ.1) ex.inv_hom_id
        · change invRaw.b ≫ homRaw.b = 𝟙 T.1.obj.snd.1
          exact congrArg (fun φ => φ.1) ez.inv_hom_id }

/-- Helper for Chap08 Lemma 8 8 4: after the middle has been replaced, endpoint replacement is
locally essentially surjective on objects by independently lifting the two endpoint objects
through `i` and `k`. -/
private theorem twoFibreProductEndpointReplacementDirectHom_locallyEssentiallySurjectiveOnObjects
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    (hi : FibredCategoryMor.IsStackification i)
    (hk : FibredCategoryMor.IsStackification k) :
    FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J
      (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) := by
  classical
  intro U T
  let L' := twoFibreProductLeftProjection f'.toFibredCategoryMor g'.toFibredCategoryMor
  let R' := twoFibreProductRightProjection f'.toFibredCategoryMor g'.toFibredCategoryMor
  obtain ⟨Sx, hSx⟩ :=
    hi.locallyEssentiallySurjectiveOnObjects U
      ((FibredCategoryMor.fiberFunctor L' U).obj T)
  obtain ⟨Sz, hSz⟩ :=
    hk.locallyEssentiallySurjectiveOnObjects U
      ((FibredCategoryMor.fiberFunctor R' U).obj T)
  refine ⟨Sx ⊓ Sz, ?_⟩
  intro I
  let Ix : Sx.Arrow := ⟨I.Y, I.f, I.hf.left⟩
  let Iz : Sz.Arrow := ⟨I.Y, I.f, I.hf.right⟩
  obtain ⟨x, ⟨ex⟩⟩ := hSx Ix
  obtain ⟨z, ⟨ez⟩⟩ := hSz Iz
  let TI : (twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor).p.Fiber I.Y :=
    I.f ^*[canonicalPullbackChoice
      (twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor).p] T
  let eL := FibredCategoryMor.pullbackComparison L' I.f T
  let eR := FibredCategoryMor.pullbackComparison R' I.f T
  let exT : (FibredCategoryMor.fiberFunctor i I.Y).obj x ≅
      (FibredCategoryMor.fiberFunctor L' I.Y).obj TI :=
    ex ≪≫ eL
  let ezT : (FibredCategoryMor.fiberFunctor k I.Y).obj z ≅
      (FibredCategoryMor.fiberFunctor R' I.Y).obj TI :=
    ez ≪≫ eR
  exact
      twoFibreProductEndpointReplacementDirectHom_localObjectLift
        (J := J) f g i j k f' g' α β TI x z exT ezT

/-- Helper for Chap08 Lemma 8 8 4: the direct endpoint replacement Hom-presheaf maps are in `W`,
because the componentwise local lifting arguments give local injectivity and surjectivity. -/
private theorem twoFibreProductEndpointReplacementDirectHom_morphismPresheafMap_W
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    (hi : FibredCategoryMor.IsStackification i)
    (hk : FibredCategoryMor.IsStackification k) :
    ∀ (U : C) (P Q : (twoFibreProduct (f ≫ j) (g ≫ j)).p.Fiber U),
      (J.over U).W (FibredCategoryMor.fibredMorphismPresheafMap
        (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) P Q) := by
  intro U P Q
  let eta :=
    FibredCategoryMor.fibredMorphismPresheafMap
      (twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) P Q
  haveI : Presheaf.IsLocallyInjective (J.over U) eta :=
    twoFibreProductEndpointReplacementDirectHom_presheafMap_isLocallyInjective
      (J := J) f g i j k f' g' α β hi hk P Q
  haveI : Presheaf.IsLocallySurjective (J.over U) eta :=
    twoFibreProductEndpointReplacementDirectHom_presheafMap_isLocallySurjective
      (J := J) f g i j k f' g' α β hi hk P Q
  let Ulf :=
    (CategoryTheory.uliftFunctor.{max u v, v} : Type v ⥤ Type (max v (max u v)))
  haveI : Presheaf.IsLocallyInjective (J.over U) (Functor.whiskerRight eta Ulf) :=
    CategoryTheory.Functor.isLocallyInjective_whisker_ulift (L := J.over U) (η := eta)
  haveI : Presheaf.IsLocallySurjective (J.over U) (Functor.whiskerRight eta Ulf) :=
    CategoryTheory.Functor.isLocallySurjective_whisker_ulift (L := J.over U) (η := eta)
  have hLargeW : (J.over U).W (Functor.whiskerRight eta Ulf) := by
    let _ : (J.over U).WEqualsLocallyBijective (Type (max v (max u v))) :=
      CategoryTheory.Functor.large_type_WEqualsLocallyBijective (L := J.over U)
    exact GrothendieckTopology.W_of_isLocallyBijective
      (J := J.over U) (f := Functor.whiskerRight eta Ulf)
  exact W_of_whiskerRight_ulift (J.over U) eta hLargeW

/-- Helper for Chap08 Lemma 8 8 4: after the middle has been replaced, the direct endpoint
replacement map is a stackification. -/
private theorem twoFibreProductEndpointReplacementDirectHom_isStackification
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    (hi : FibredCategoryMor.IsStackification i)
    (hj : FibredCategoryMor.IsStackification j)
    (hk : FibredCategoryMor.IsStackification k) :
    let target : StackOver J :=
      ⟨twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor, inferInstance⟩
    FibredCategoryMor.IsStackification
      (show FibredCategoryMor
          (twoFibreProduct (f ≫ j) (g ≫ j))
          target
        from twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β) := by
  constructor
  · intro U P Q
    exact
      twoFibreProductEndpointReplacementDirectHom_morphismPresheafMap_W
        (J := J) f g i j k f' g' α β hi hk U P Q
  · exact
      twoFibreProductEndpointReplacementDirectHom_locallyEssentiallySurjectiveOnObjects
        (J := J) f g i j k f' g' α β hi hk

/-- Helper for Chap08 Lemma 8 8 4: the staged two-fibre-product comparison is a
stackification. -/
private theorem twoFibreProductStagedComparisonHom_isStackification
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    (hi : FibredCategoryMor.IsStackification i)
    (hj : FibredCategoryMor.IsStackification j)
    (hk : FibredCategoryMor.IsStackification k) :
    let target : StackOver J :=
      ⟨twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor, inferInstance⟩
    FibredCategoryMor.IsStackification
      (show FibredCategoryMor
          (twoFibreProduct f g)
          target
        from twoFibreProductStagedComparisonHom f g i j k f' g' α β) := by
  -- The source proof factors the comparison into middle replacement followed by endpoint
  -- replacement; record the target stack object once so the endpoint stage has the right codomain.
  let target : StackOver J :=
    ⟨twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor, inferInstance⟩
  let endpoint : FibredCategoryMor (twoFibreProduct (f ≫ j) (g ≫ j)) target :=
    twoFibreProductEndpointReplacementDirectHom f g i j k f' g' α β
  have hMiddleW : ∀ (U : C) (P Q : (twoFibreProduct f g).p.Fiber U),
      (J.over U).W (FibredCategoryMor.fibredMorphismPresheafMap
        (twoFibreProductMiddlePostcomposeHom f g j) P Q) := by
    -- Use the isolated middle Hom-field helper so the composition skeleton does not duplicate
    -- the pullback-normal-form proof.
    exact twoFibreProductMiddlePostcomposeHom_morphismPresheafMap_W f g j hj
  have hMiddleEss : FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J
      (twoFibreProductMiddlePostcomposeHom f g j) := by
    -- The object-field proof is likewise isolated at the middle replacement API boundary.
    exact twoFibreProductMiddlePostcomposeHom_locallyEssentiallySurjectiveOnObjects f g j hj
  have hEndpoint : FibredCategoryMor.IsStackification endpoint := by
    -- Close the endpoint stage through the named endpoint stackification helper.
    exact
      twoFibreProductEndpointReplacementDirectHom_isStackification
        (J := J) f g i j k f' g' α β hi hj hk
  -- Once the two staged pieces are available, the existing composition lemma gives the desired
  -- stackification of the staged comparison.
  exact isStackification_comp_of_stackificationData
    (twoFibreProductMiddlePostcomposeHom f g j)
    endpoint
    hMiddleW hMiddleEss hEndpoint

/-- Helper for Chap08 Lemma 8 8 4: the canonical two-fibre-product comparison is a
stackification; this is the single remaining staged-comparison assertion from which the two
source-facing fields are projected. -/
private theorem twoFibreProductComparison_isStackification_bridge
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    (hi : FibredCategoryMor.IsStackification i)
    (hj : FibredCategoryMor.IsStackification j)
    (hk : FibredCategoryMor.IsStackification k) :
    let target : StackOver J :=
      ⟨twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor, inferInstance⟩
    FibredCategoryMor.IsStackification
      (show FibredCategoryMor
          (twoFibreProduct f g)
          target
        from twoFibreProductOfStackificationsHom f g i j k f' g' α β) := by
  -- Route correction: the public comparison now unfolds to the staged middle-then-endpoint
  -- comparison, so the bridge is just the staged stackification theorem.
  exact twoFibreProductStagedComparisonHom_isStackification f g i j k f' g' α β hi hj hk

/-- Helper for Chap08 Lemma 8 8 4: the Hom-presheaf map of the canonical comparison is locally
an equivalence on each slice. -/
private theorem twoFibreProductComparison_homPresheafMap_W_componentwise
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    (hi : FibredCategoryMor.IsStackification i)
    (hj : FibredCategoryMor.IsStackification j)
    (hk : FibredCategoryMor.IsStackification k) :
    ∀ (U : C) (P Q : (twoFibreProduct f g).p.Fiber U),
      (J.over U).W
        (FibredCategoryMor.fibredMorphismPresheafMap
          (twoFibreProductOfStackificationsHom f g i j k f' g' α β) P Q) := by
  intro U P Q
  -- Project the Hom-presheaf field from the isolated stackification bridge, so this declaration
  -- no longer carries its own transport-heavy proof search.
  exact
    (twoFibreProductComparison_isStackification_bridge
      (J := J) f g i j k f' g' α β hi hj hk).morphismPresheafMap_W U P Q

/-- Helper for Chap08 Lemma 8 8 4: the canonical comparison is locally essentially surjective on
objects. -/
private theorem twoFibreProductComparison_localObjectLifts_componentwise
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    (hi : FibredCategoryMor.IsStackification i)
    (hj : FibredCategoryMor.IsStackification j)
    (hk : FibredCategoryMor.IsStackification k) :
    FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J
      (twoFibreProductOfStackificationsHom f g i j k f' g' α β) := by
  -- Project the local object-lifting field from the same bridge; the remaining open work is now
  -- one stackification proof rather than two separately duplicated componentwise arguments.
  exact
    (twoFibreProductComparison_isStackification_bridge
      (J := J) f g i j k f' g' α β hi hj hk).locallyEssentiallySurjectiveOnObjects

/-- Helper for Chap08 Lemma 8 8 4: the canonical two-fibre-product comparison is the remaining
core stackification assertion, from which the two source-facing fields are projected below. -/
private theorem twoFibreProductComparison_isStackification_core
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    (hi : FibredCategoryMor.IsStackification i)
    (hj : FibredCategoryMor.IsStackification j)
    (hk : FibredCategoryMor.IsStackification k) :
    let target : StackOver J :=
      ⟨twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor, inferInstance⟩
    FibredCategoryMor.IsStackification
      (show FibredCategoryMor
          (twoFibreProduct f g)
          target
        from twoFibreProductOfStackificationsHom f g i j k f' g' α β) := by
  -- Reuse the isolated bridge so all downstream declarations agree on the same proof frontier.
  exact
    twoFibreProductComparison_isStackification_bridge
      (J := J) f g i j k f' g' α β hi hj hk

/-- Helper for Chap08 Lemma 8 8 4: the canonical two-fibre-product comparison map satisfies the
Hom-presheaf `W` field of a stackification. -/
private theorem twoFibreProductComparison_morphismPresheafMap_W
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    (hi : FibredCategoryMor.IsStackification i)
    (hj : FibredCategoryMor.IsStackification j)
    (hk : FibredCategoryMor.IsStackification k) :
    ∀ (U : C) (P Q : (twoFibreProduct f g).p.Fiber U),
      (J.over U).W
      (FibredCategoryMor.fibredMorphismPresheafMap
        (twoFibreProductOfStackificationsHom f g i j k f' g' α β) P Q) := by
  intro U P Q
  -- Reuse the direct componentwise Hom-presheaf field rather than projecting recursively from the
  -- core stackification theorem.
  exact
    twoFibreProductComparison_homPresheafMap_W_componentwise
      (J := J) f g i j k f' g' α β hi hj hk U P Q

/-- Helper for Chap08 Lemma 8 8 4: the canonical two-fibre-product comparison map is locally
essentially surjective on objects. -/
private theorem twoFibreProductComparison_locallyEssentiallySurjectiveOnObjects
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    (hi : FibredCategoryMor.IsStackification i)
    (hj : FibredCategoryMor.IsStackification j)
    (hk : FibredCategoryMor.IsStackification k) :
    FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J
      (twoFibreProductOfStackificationsHom f g i j k f' g' α β) := by
  -- Reuse the direct componentwise object-lifting field rather than projecting recursively from
  -- the core stackification theorem.
  exact
    twoFibreProductComparison_localObjectLifts_componentwise
      (J := J) f g i j k f' g' α β hi hj hk

-- Proof sketch: apply Lemma `8.4.6` to the chosen lifted morphisms `f' : X' ⟶ Y'` and
-- `g' : Z' ⟶ Y'` to put a stack structure on their explicit `2`-fibre product. The comparison
-- `2`-isomorphisms `α` and `β` already live on the ambient fibred-category morphisms
-- `f'.toFibredCategoryMor` and `g'.toFibredCategoryMor`, so they directly define the square
-- `twoFibreProductOfStackificationsSquare f g i j k f'.toFibredCategoryMor
-- g'.toFibredCategoryMor α β`. The canonical comparison map is
-- then the induced terminal morphism to the owner pullback square
-- `FibredCategoryOver.twoFibreProductSquare f'.toFibredCategoryMor g'.toFibredCategoryMor`.
/-- Lemma 8.8.4: if `i : X ⟶ X'`, `j : Y ⟶ Y'`, and `k : Z ⟶ Z'` are stackifications of fibred
categories over the site `(C, J)`, and if `f' : X' ⟶ Y'` and `g' : Z' ⟶ Y'` are chosen lifts of
`f : X ⟶ Y` and `g : Z ⟶ Y` together with comparison `2`-isomorphisms to the original
composites, then the induced canonical morphism from the explicit `2`-fibre product of `f` and
`g` to the explicit `2`-fibre product of `f'` and `g'` is a stackification. -/
@[stacks 04Y1]
theorem twoFibreProduct_of_stackifications_isStackification
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    (hi : FibredCategoryMor.IsStackification i)
    (hj : FibredCategoryMor.IsStackification j)
    (hk : FibredCategoryMor.IsStackification k) :
    let target : StackOver J :=
      ⟨twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor, inferInstance⟩
    FibredCategoryMor.IsStackification
      (show FibredCategoryMor
          (twoFibreProduct f g)
          target
        from twoFibreProductOfStackificationsHom f g i j k f' g' α β) := by
  -- The stackification predicate has exactly the two source-facing fields from Lemma 8.8.1.
  -- Splitting here fixes the proof frontier at the Hom-presheaf and object-lifting statements
  -- for the canonical comparison map of `2`-fibre products.
  constructor
  · intro U P Q
    -- The remaining Hom-presheaf field is isolated in the closing helper above.
    exact
      twoFibreProductComparison_morphismPresheafMap_W
        (J := J) f g i j k f' g' α β hi hj hk U P Q
  · -- The object-lifting field is isolated in the second closing helper above.
    exact
      twoFibreProductComparison_locallyEssentiallySurjectiveOnObjects
        (J := J) f g i j k f' g' α β hi hj hk

end

end CategoryTheory
