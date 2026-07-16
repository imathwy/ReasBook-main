import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.Criteria
import stacks_proof.stacks_project.Chap04.Lemma_4_35_9
import stacks_proof.stacks_project.Chap04.Definition_4_36_2
import stacks_proof.stacks_project.Chap08.Lemma_8_2_3
import stacks_proof.stacks_project.Chap08.Definition_8_4_1
import stacks_proof.stacks_project.Chap08.Definition_8_4_5
import stacks_proof.stacks_project.Chap08.Lemma_8_4_4
import stacks_proof.stacks_project.Chap07.Lemma_7_10_17

universe u v

namespace CategoryTheory

open Bicategory
open BasedFunctor
open FibredCategoryMor
open InducedCategory.Hom
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section

/-- Helper for Lemma 8.8.1: in a stack target, a vertical morphism is determined by its pullbacks
to the arrows of any fixed covering family. -/
theorem stack_cover_hom_ext
    (Z : StackOver J)
    {U : C} (S : J.Cover U)
    {x y : Z.p.Fiber U}
    {f g : x ⟶ y}
    (hfg :
      ∀ I : S.Arrow,
        (((canonicalFiberPseudofunctor Z.p).map I.f.op.toLoc).toFunctor.map f) =
          (((canonicalFiberPseudofunctor Z.p).map I.f.op.toLoc).toFunctor.map g)) :
    f = g := by
  let Fp := canonicalFiberPseudofunctor Z.p
  let Φ := Fp.toDescentData (fun I : S.Arrow ↦ I.f)
  letI : Φ.IsEquivalence :=
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
      (J := J) (p := Z.p)).1 inferInstance U S
  letI : Φ.Faithful := by infer_instance
  -- The fixed-cover descent functor of a stack is faithful, so equality can be checked after
  -- passing to descent data and then componentwise on the chosen cover.
  apply Φ.map_injective
  apply Pseudofunctor.DescentData.hom_ext
  intro I
  exact hfg I

/-- Helper for Lemma 8.8.1: in a stack target, a compatible morphism of fixed-cover descent data
comes from a unique global fiber morphism. -/
theorem stack_cover_hom_glue
    (Z : StackOver J)
    {U : C} (S : J.Cover U)
    {x y : Z.p.Fiber U}
    (δ :
      (((canonicalFiberPseudofunctor Z.p).toDescentData (fun I : S.Arrow ↦ I.f)).obj x) ⟶
        (((canonicalFiberPseudofunctor Z.p).toDescentData (fun I : S.Arrow ↦ I.f)).obj y)) :
    ∃! f : x ⟶ y,
      (((canonicalFiberPseudofunctor Z.p).toDescentData (fun I : S.Arrow ↦ I.f)).map f) = δ := by
  let Fp := canonicalFiberPseudofunctor Z.p
  let Φ := Fp.toDescentData (fun I : S.Arrow ↦ I.f)
  letI : Φ.IsEquivalence :=
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
      (J := J) (p := Z.p)).1 inferInstance U S
  let hFF : Φ.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful Φ
  let f : x ⟶ y := hFF.preimage δ
  have hf : Φ.map f = δ := hFF.map_preimage δ
  refine ⟨f, ?_, ?_⟩
  · -- Use the preimage chosen by full faithfulness of the fixed-cover descent functor.
    simpa [Φ, f] using hf
  · intro g hg
    -- Compare the two candidate morphisms on the chosen cover, then descend equality globally.
    apply stack_cover_hom_ext (J := J) Z S
    intro I
    have hI :
        (Φ.map g).hom I = (Φ.map f).hom I := by
      calc
        (Φ.map g).hom I = δ.hom I := by
          exact congrArg (fun η ↦ η.hom I) hg
        _ = (Φ.map f).hom I := by
          exact (congrArg (fun η ↦ η.hom I) hf).symm
    simpa [Φ] using hI

/-- Helper for Lemma 8.8.1 (object descent): in a stack target, every fixed-cover descent-data
object comes from a global fiber object. This is the essential-surjectivity half of the
fixed-cover descent equivalence, the object-level companion of `stack_cover_hom_glue`. -/
theorem stack_cover_obj_glue
    (Z : StackOver J)
    {U : C} (S : J.Cover U)
    (ξ : (canonicalFiberPseudofunctor Z.p).DescentData (fun I : S.Arrow ↦ I.f)) :
    ∃ z : Z.p.Fiber U,
      Nonempty
        (((canonicalFiberPseudofunctor Z.p).toDescentData (fun I : S.Arrow ↦ I.f)).obj z ≅ ξ) := by
  let Fp := canonicalFiberPseudofunctor Z.p
  let Φ := Fp.toDescentData (fun I : S.Arrow ↦ I.f)
  letI : Φ.IsEquivalence :=
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
      (J := J) (p := Z.p)).1 inferInstance U S
  letI : Φ.EssSurj := by infer_instance
  -- The fixed-cover descent functor of a stack is an equivalence, hence essentially surjective; the
  -- chosen preimage of `ξ` is the desired global fiber object.
  exact ⟨Φ.objPreimage ξ, ⟨Φ.objObjPreimageIso ξ⟩⟩

/-- Helper for Lemma 8.8.1: the local essential-image condition for a stackification provides a
single common cover on which two target-fiber objects are both represented by source-fiber
objects. This is the first source-faithful reduction step before comparing Hom presheaves on
arbitrary target objects. -/
theorem stackification_common_local_models
    {X : FibredCategoryOver C} {Y : StackOver J}
    (G : X ⟶ Y)
    (hG : FibredCategoryMor.IsStackification G)
    {U : C} (x y : Y.p.Fiber U) :
    ∃ S : J.Cover U,
      ∀ I : S.Arrow,
        ∃ xI yI : X.p.Fiber I.Y,
          Nonempty
            (((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
              I.f ^*[canonicalPullbackChoice Y.p] x) ∧
          Nonempty
            (((FibredCategoryMor.fiberFunctor G I.Y).obj yI) ≅
              I.f ^*[canonicalPullbackChoice Y.p] y) := by
  -- Choose local source models for `x` and `y` separately, then intersect the two covers so both
  -- models are simultaneously available on each arrow of the refined cover.
  rcases hG.locallyEssentiallySurjectiveOnObjects U x with ⟨Sx, hSx⟩
  rcases hG.locallyEssentiallySurjectiveOnObjects U y with ⟨Sy, hSy⟩
  refine ⟨Sx ⊓ Sy, ?_⟩
  intro I
  let Ix : Sx.Arrow := ⟨I.Y, I.f, I.hf.1⟩
  let Iy : Sy.Arrow := ⟨I.Y, I.f, I.hf.2⟩
  rcases hSx Ix with ⟨xI, hxI⟩
  rcases hSy Iy with ⟨yI, hyI⟩
  -- On the intersection cover, each arrow is literally an arrow of both original covers.
  refine ⟨xI, yI, ?_, ?_⟩
  · simpa [Ix] using hxI
  · simpa [Iy] using hyI

/-- Helper for Lemma 8.8.1: for a slice object `T : Over U`, the pullback of a fixed cover
`S : J.Cover U` along `T.hom` can be viewed as an explicit semi-representable family on the slice
site `(C/U, J.over U)`. This is the source-faithful owner needed before applying the Chapter 7
`W`-criterion objectwise on the slice site. -/
noncomputable abbrev comparison_stackification_slice_pullback_cover_family
    {U : C} (S : J.Cover U) (T : Over U) :
    SemiRepresentableFamily.Over T :=
  SemiRepresentableFamily.Over.ofArrows
    (fun I : (S.pullback T.hom).Arrow ↦ Over.mk (I.f ≫ T.hom))
    (fun I ↦ Over.homMk I.f)

/-- Helper for Lemma 8.8.1: the left object of one member of the explicit slice pullback-cover
family is definitionally the corresponding pullback-cover object over `U`. This keeps the later
componentwise `W`-calculation on the source-faithful family from unfolding `ofArrows` by hand. -/
theorem comparison_stackification_slice_pullback_cover_family_obj_left
    {U : C} (S : J.Cover U) (T : Over U) (i : (S.pullback T.hom).Arrow) :
    ((comparison_stackification_slice_pullback_cover_family (J := J) S T).obj i).left =
      Over.mk (i.f ≫ T.hom) := by
  -- The family was defined by `SemiRepresentableFamily.Over.ofArrows` on exactly these objects.
  rfl

/-- Helper for Lemma 8.8.1: the structure morphism of one member of the explicit slice
pullback-cover family is definitionally the arrow `Over.homMk i.f : Over.mk (i.f ≫ T.hom) ⟶ T`.
This isolates the family-level transport before the remaining componentwise bijectivity step. -/
theorem comparison_stackification_slice_pullback_cover_family_obj_hom
    {U : C} (S : J.Cover U) (T : Over U) (i : (S.pullback T.hom).Arrow) :
    ((comparison_stackification_slice_pullback_cover_family (J := J) S T).obj i).hom =
      Over.homMk i.f := by
  -- The explicit family uses `Over.homMk i.f` as its defining arrow into `T`.
  rfl

end

end CategoryTheory
