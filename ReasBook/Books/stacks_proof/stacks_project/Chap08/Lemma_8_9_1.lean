import Mathlib
import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Lemma_8_8_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X : FibredInGroupoidsOver.{v, u, max u v, max u v} C}
variable {Y : StackInGroupoidsOver.{u, v, max u v, max u v} J}

/- Domain-style sampling for Lemma 8.9.1:
- primary domain: stackification of categories fibred in groupoids, specialized from the Chapter 8
  stackification theory for fibred categories;
- inspected owner-level declarations:
  `FibredCategoryMor.IsStackification`,
  `exists_stackification`,
  `stackification_unique_up_to_unique_twoIso`,
  `StackInGroupoidsOver.Hom.IsEquivalenceOverBase`;
- best owner abstraction: the stackification predicate should stay on the ambient owner
  `FibredCategoryMor.IsStackification` after passing from a morphism of fibred-in-groupoids to the
  canonical bridge `toStackFibredCategoryMor`; comparison morphisms between stackifications should
  reuse the owner hom type `Y₁ ⟶ Y₂`;
- primitive data: a target `Y : StackInGroupoidsOver J`, a morphism `G : FibredInGroupoidsMor X Y`,
  and the ambient stackification predicate on `G.toStackFibredCategoryMor`;
- derived API: the comparison equivalence-over-base predicate on owner homs in
  `StackInGroupoidsOver J` and the compatible comparison `2`-isomorphism inherited from the
  ambient stackification uniqueness theorem.

Source/core/bridge triage:
- `source-facing`: the existence and uniqueness statements for stackifications in groupoids;
- `core/canonical`: `FibredCategoryMor.IsStackification`, `exists_stackification`,
  `stackification_unique_up_to_unique_twoIso`, and
  `StackInGroupoidsOver.Hom.IsEquivalenceOverBase`;
- `bridge/view`: the canonical bridge `FibredInGroupoidsMor.toStackFibredCategoryMor` from the
  groupoid-specialized morphism to the ambient owner predicate. -/

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

variable (X : FibredInGroupoidsOver.{v, u, max u v, max u v} C)

/-- Helper for Chap08 Lemma 8 9 1: a morphism of descent data is an isomorphism when all of
its components are isomorphisms. -/
private theorem descentDataHom_isIso_of_components
    {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat} {U : C} {ι : Type*} {V : ι → C} {f : ∀ i, V i ⟶ U}
    {D₁ D₂ : F.DescentData f} (φ : D₁ ⟶ D₂)
    (hφ : ∀ i, IsIso (Pseudofunctor.DescentData.Hom.hom φ i)) :
    IsIso φ := by
  -- Build the inverse componentwise and use the descent-data compatibility already present in φ.
  let e : ∀ i, D₁.obj i ≅ D₂.obj i :=
    fun i ↦ asIso (Pseudofunctor.DescentData.Hom.hom φ i)
  -- The constructed descent-data isomorphism has hom part exactly `φ`.
  refine (Pseudofunctor.DescentData.isoMk e ?_).isIso_hom
  intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
  simpa [e] using φ.comm q f₁ f₂ hf₁ hf₂

/-- Helper for Chap08 Lemma 8 9 1: in a stack, a fiber morphism is an isomorphism if it becomes
an isomorphism after pullback along every arrow of one cover. -/
private theorem stackFiberHom_isIso_of_coverwise_isIso
    (Z : StackOver J)
    {U : C} {x y : Z.p.Fiber U} (f : x ⟶ y)
    (S : J.Cover U)
    (hS :
      ∀ I : S.Arrow,
        IsIso (((canonicalFiberPseudofunctor Z.p).map I.f.op.toLoc).toFunctor.map f)) :
    IsIso f := by
  -- The fixed-cover descent functor for a stack is an equivalence, hence reflects isomorphisms.
  let Fp := canonicalFiberPseudofunctor Z.p
  let Φ := Fp.toDescentData (fun I : S.Arrow ↦ I.f)
  letI : Φ.IsEquivalence :=
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
      (J := J) (p := Z.p)).1 inferInstance U S
  have hΦf : IsIso (Φ.map f) := by
    -- Componentwise, `Φ.map f` is exactly the family of the pulled-back morphisms.
    refine descentDataHom_isIso_of_components (Φ.map f) ?_
    intro I
    simpa [Φ, Fp] using hS I
  -- Reflect the descent-data isomorphism back to the original fiber morphism.
  let hΦff : Φ.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful Φ
  exact hΦff.isIso_of_isIso_map f

/-- Helper for Chap08 Lemma 8 9 1: the base sieve underlying an identity-slice cover is covering. -/
private theorem baseCoverOfIdSliceCover_condition
    {W : C} (S : (J.over W).Cover (Over.mk (𝟙 W))) :
    Sieve.overEquiv (Over.mk (𝟙 W)) S.1 ∈ J W := by
  -- Unpack the definition of the topology on the slice over `W`.
  have h : S.1 ∈ (J.over W) (Over.mk (𝟙 W)) := S.2
  rw [J.mem_over_iff] at h
  exact h

/-- Helper for Chap08 Lemma 8 9 1: a slice cover of the identity object induces a base cover. -/
private noncomputable def baseCoverOfIdSliceCover
    {W : C} (S : (J.over W).Cover (Over.mk (𝟙 W))) :
    J.Cover W :=
  ⟨Sieve.overEquiv (Over.mk (𝟙 W)) S.1, baseCoverOfIdSliceCover_condition (J := J) S⟩

/-- Helper for Chap08 Lemma 8 9 1: an arrow in the induced base cover is the corresponding
identity-slice arrow in the original slice cover. -/
private theorem baseCoverOfIdSliceCover_arrow_mem
    {W : C} (S : (J.over W).Cover (Over.mk (𝟙 W)))
    (I : (baseCoverOfIdSliceCover (J := J) S).Arrow) :
    S.1 (Over.homMk I.f : Over.mk (I.f ≫ 𝟙 W) ⟶ Over.mk (𝟙 W)) :=
  (Sieve.overEquiv_iff (Y := Over.mk (𝟙 W)) S.1 I.f).1 I.hf

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 9 1: restriction of an identity-slice Hom section is the canonical
pullback of the corresponding fiber morphism. -/
private theorem presheafHom_idSlice_map_eq_pullback_map
    {S : Type*} [Category S] (p : S ⥤ C) [p.IsFibered]
    {W Z : C} (g : Z ⟶ W)
    (M N : p.Fiber W)
    (φ : M ⟶ N) :
    ((canonicalFiberPseudofunctor p).presheafHom M N).map
        (Over.homMk g : Over.mk (g ≫ 𝟙 W) ⟶ Over.mk (𝟙 W)).op
        ((canonicalFiberPseudofunctor p).presheafHomObjHomEquiv φ) =
      ((canonicalFiberPseudofunctor p).map (g ≫ 𝟙 W).op.toLoc).toFunctor.map φ := by
  -- Expand the Hom presheaf restriction to its pseudofunctorial pullback shell.
  rw [Pseudofunctor.presheafHom_map]
  dsimp only []
  rw [Pseudofunctor.presheafHomObjHomEquiv_apply]
  dsimp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  have hmid :
      ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op W))).hom.toNatTrans.app M ≫
          φ ≫
          ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op W))).inv.toNatTrans.app N =
        ((canonicalFiberPseudofunctor p).map (Over.mk (𝟙 W)).hom.op.toLoc).toFunctor.map φ := by
    -- The identity-slice leg contributes only the usual `mapId` naturality square.
    rw [← (canonicalFiberPseudofunctor p).mapId'_eq_mapId (LocallyDiscrete.mk (op W)),
      ← Category.assoc,
      ← (canonicalFiberPseudofunctor p).mapId'_hom_naturality
        (𝟙 (LocallyDiscrete.mk (op W))) rfl φ,
      Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]
    rfl
  rw [hmid]
  -- The remaining outer shell is the pseudofunctor composition naturality square.
  rw [(canonicalFiberPseudofunctor p).mapComp'_naturality_2]
  rfl

/-- Helper for Chap08 Lemma 8 9 1: any target fiber morphism between objects in the image of a
stackification from a fibred-in-groupoids source is an isomorphism. -/
private theorem stackification_imageFiberHom_isIso
    {X : FibredInGroupoidsOver.{v, u, max u v, max u v} C}
    {Y : StackOver.{u, v, max u v, max u v} J}
    (G : (X : FibredCategoryOver C) ⟶ Y)
    (hG : FibredCategoryMor.IsStackification G)
    {U : C} {x y : X.p.Fiber U}
    (d : (FibredCategoryMor.fiberFunctor G U).obj x ⟶
      (FibredCategoryMor.fiberFunctor G U).obj y) :
    IsIso d := by
  -- Turn `d` into a section of the target Hom presheaf and take its local image cover.
  let β : ((canonicalFiberPseudofunctor Y.p).presheafHom
      ((FibredCategoryMor.fiberFunctor G U).obj x)
      ((FibredCategoryMor.fiberFunctor G U).obj y)).obj (op (Over.mk (𝟙 U))) :=
    (canonicalFiberPseudofunctor Y.p).presheafHomObjHomEquiv d
  let Sslice : (J.over U).Cover (Over.mk (𝟙 U)) :=
    stackification_hom_image_cover (J := J) G hG (x := x) (y := y) β
  let Sbase : J.Cover U := baseCoverOfIdSliceCover (J := J) Sslice
  apply stackFiberHom_isIso_of_coverwise_isIso (J := J) Y d Sbase
  intro I
  let Islice : Sslice.Arrow :=
    ⟨Over.mk (I.f ≫ 𝟙 U), Over.homMk I.f,
      baseCoverOfIdSliceCover_arrow_mem (J := J) Sslice I⟩
  obtain ⟨γRaw, hγRaw⟩ :=
    stackification_coverwise_hom_lift (J := J) G hG (x := x) (y := y) β Islice
  -- Read the local preimage equality as a conjugation formula for the pulled-back morphism.
  have hγRawApp :
      (FibredCategoryMor.pullbackComparison G (Islice.Y.hom) x).hom ≫
          (FibredCategoryMor.fiberFunctor G Islice.Y.left).map γRaw ≫
          (FibredCategoryMor.pullbackComparison G (Islice.Y.hom) y).inv =
        (((canonicalFiberPseudofunctor Y.p).presheafHom
            ((FibredCategoryMor.fiberFunctor G U).obj x)
            ((FibredCategoryMor.fiberFunctor G U).obj y)).map Islice.f.op) β := by
    rw [← hγRaw]
    rfl
  dsimp only [β] at hγRawApp
  rw [presheafHom_idSlice_map_eq_pullback_map] at hγRawApp
  have hγRawMap :
      (FibredCategoryMor.fiberFunctor G I.Y).map γRaw =
        (FibredCategoryMor.pullbackComparison G (Islice.Y.hom) x).inv ≫
          ((canonicalFiberPseudofunctor Y.p).map (I.f ≫ 𝟙 U).op.toLoc).toFunctor.map d ≫
          (FibredCategoryMor.pullbackComparison G (Islice.Y.hom) y).hom := by
    have h1 :=
      (Iso.eq_inv_comp (FibredCategoryMor.pullbackComparison G (Islice.Y.hom) x)).2
        hγRawApp
    have h2 :=
      (Iso.comp_inv_eq (FibredCategoryMor.pullbackComparison G (Islice.Y.hom) y)).1 h1
    rw [Category.assoc] at h2
    exact h2
  have hconjIso :
      IsIso ((FibredCategoryMor.pullbackComparison G (Islice.Y.hom) x).inv ≫
          ((canonicalFiberPseudofunctor Y.p).map (I.f ≫ 𝟙 U).op.toLoc).toFunctor.map d ≫
          (FibredCategoryMor.pullbackComparison G (Islice.Y.hom) y).hom) := by
    -- The source fiber is a groupoid, so the local source lift and its image are isomorphisms.
    have hγRawIso : IsIso γRaw :=
      IsFibredInGroupoids.hom_isIso (p := X.p) Islice.Y.left γRaw
    letI : IsIso γRaw := hγRawIso
    rw [← hγRawMap]
    exact Functor.map_isIso (FibredCategoryMor.fiberFunctor G I.Y) γRaw
  let ex := FibredCategoryMor.pullbackComparison G (Islice.Y.hom) x
  let ey := FibredCategoryMor.pullbackComparison G (Islice.Y.hom) y
  have hmapCompIso :
      IsIso (((canonicalFiberPseudofunctor Y.p).map (I.f ≫ 𝟙 U).op.toLoc).toFunctor.map d) := by
    -- Cancel the two pullback-comparison isomorphisms around the local source-image lift.
    have hright :
        IsIso (((canonicalFiberPseudofunctor Y.p).map (I.f ≫ 𝟙 U).op.toLoc).toFunctor.map d ≫
          ey.hom) := by
      exact (isIso_comp_left_iff ex.inv
        (((canonicalFiberPseudofunctor Y.p).map (I.f ≫ 𝟙 U).op.toLoc).toFunctor.map d ≫
          ey.hom)).1 hconjIso
    exact (isIso_comp_right_iff
      (((canonicalFiberPseudofunctor Y.p).map (I.f ≫ 𝟙 U).op.toLoc).toFunctor.map d)
      ey.hom).1 hright
  -- Remove the harmless identity in the base arrow of the slice object.
  have hfeq : I.f ≫ 𝟙 U = I.f := Category.comp_id _
  rw [hfeq] at hmapCompIso
  exact hmapCompIso

/-- Helper for Chap08 Lemma 8 9 1: the target of a stackification of a category fibred in
groupoids is again fibred in groupoids. -/
private theorem stackificationTarget_isFibredInGroupoids
    {X : FibredInGroupoidsOver.{v, u, max u v, max u v} C}
    {Y : StackOver.{u, v, max u v, max u v} J}
    (G : (X : FibredCategoryOver C) ⟶ Y)
    (hG : FibredCategoryMor.IsStackification G) :
    IsFibredInGroupoids Y.p := by
  -- It is enough to show every standard fiber of the already-fibred stack projection is a groupoid.
  apply isFibredInGroupoids_of_isFibered_and_fiber_groupoid Y.p inferInstance
  intro U
  refine { all_isIso := ?_ }
  intro x y f
  obtain ⟨S, hS⟩ := stackification_common_local_models (J := J) G hG x y
  apply stackFiberHom_isIso_of_coverwise_isIso (J := J) Y f S
  intro I
  rcases hS I with ⟨xI, yI, ⟨exI⟩, ⟨eyI⟩⟩
  let Mf := ((canonicalFiberPseudofunctor Y.p).map I.f.op.toLoc).toFunctor
  let dI : (FibredCategoryMor.fiberFunctor G I.Y).obj xI ⟶
      (FibredCategoryMor.fiberFunctor G I.Y).obj yI :=
    exI.hom ≫ Mf.map f ≫ eyI.inv
  have hdI : IsIso dI := stackification_imageFiberHom_isIso (J := J) G hG dI
  -- The pullback of `f` is conjugate to the image morphism `dI`, hence is an isomorphism.
  have hwrapped : IsIso (exI.inv ≫ dI ≫ eyI.hom) := by
    infer_instance
  simpa [dI, Mf, Category.assoc] using hwrapped

/-
Chap08 Lemma 8 9 1: the two public declarations below record existence of stackification by
stacks in groupoids and uniqueness up to equivalence over the base.
-/
-- recall exists_stackInGroupoids_stackification / stackInGroupoids_stackification_unique_up_to_unique_twoIso

/-
/-- Validator bridge for Chap08 Lemma 8 9 1: records the two public declarations that together
form the planned main result for this item. -/
theorem exists_stackInGroupoids_stackification / stackInGroupoids_stackification_unique_up_to_unique_twoIso
-/

-- Proof sketch: apply the generic stackification result of Lemma `8.8.1` to the underlying
-- fibred category of `X`, then use Lemma `8.5.2` to see that the resulting stack is again fibred
-- in groupoids. Since both source and target are now bundled in the groupoid-specific APIs, the
-- stackification morphism is canonically a `FibredInGroupoidsMor`.
/-- First part of Chap08 Lemma 8 9 1: a category fibred in groupoids over a site admits a stackification by a
stack in groupoids, with the induced morphism presheaf maps identifying the target with the
sheafification of the source and with local essential surjectivity on objects in each fiber. -/
@[stacks 02ZP]
theorem exists_stackInGroupoids_stackification :
    ∃ Y : StackInGroupoidsOver J,
      ∃ G : FibredInGroupoidsMor X Y,
        FibredCategoryMor.IsStackification G.toStackFibredCategoryMor := by
  -- Start from the ambient stackification theorem for fibred categories.
  obtain ⟨Y, G, hG⟩ :=
    exists_stackification (J := J)
      (X := (X : FibredCategoryOver.{u, v, max u v, max u v} C))
  -- The target-fiber groupoid bridge globalizes local source-image invertibility through the stack
  -- Hom descent functor.
  have hYgroupoid : IsFibredInGroupoids Y.p := by
    exact stackificationTarget_isFibredInGroupoids (J := J) G hG
  letI : IsFibredInGroupoids Y.p := hYgroupoid
  have hYstack : IsStackOnSite J (FibredInGroupoidsOver.ofFunctor Y.p).p := by
    simpa [FibredInGroupoidsOver.p, FibredInGroupoidsOver.ofFunctor,
      FibredCategoryOver.p, FibredCategoryOver.ofFunctor] using
      (inferInstance : IsStackOnSite J Y.p)
  let Yg : StackInGroupoidsOver J := ⟨FibredInGroupoidsOver.ofFunctor Y.p, hYstack⟩
  let Gg : FibredInGroupoidsMor X Yg := FibredInGroupoidsMor.ofAmbientHom G
  -- Repackage the ambient target and morphism in the stack-in-groupoids owners.
  refine ⟨Yg, Gg, ?_⟩
  simpa [Yg, Gg, FibredInGroupoidsMor.toStackFibredCategoryMor,
    FibredInGroupoidsOver.ofFunctor, FibredInGroupoidsMor.ofAmbientHom] using hG

-- Proof sketch: forget the two stackifications in groupoids to stackifications in the sense of
-- Lemma `8.8.1`, apply `stackification_unique_up_to_unique_twoIso` there, and lift the ambient
-- comparison back to the owner hom between stacks in groupoids.
/-- Second part of Chap08 Lemma 8 9 1: a stackification of a category fibred in groupoids by a stack in groupoids is
determined up to equivalence over the base together with compatible comparison `2`-isomorphism.
The raw type of compatible comparison isomorphisms for one fixed comparison morphism is not a
subsingleton in general; the unique-`2`-isomorphism clause is the comparison-pair uniqueness
recorded by the ambient stack theorem. -/
@[stacks 02ZP]
theorem stackInGroupoids_stackification_unique_up_to_unique_twoIso
    {Y₁ Y₂ : StackInGroupoidsOver J}
    (G₁ : FibredInGroupoidsMor X Y₁)
    (G₂ : FibredInGroupoidsMor X Y₂)
    (hG₁ : FibredCategoryMor.IsStackification G₁.toStackFibredCategoryMor)
    (hG₂ : FibredCategoryMor.IsStackification G₂.toStackFibredCategoryMor) :
    ∃ H : Y₁ ⟶ Y₂,
      StackInGroupoidsOver.Hom.IsEquivalenceOverBase H ∧
        let GH : FibredInGroupoidsMor X Y₂ :=
          G₁ ≫ StackInGroupoidsOver.Hom.toFibredInGroupoidsMor H
        Nonempty (GH ≅ G₂) := by
  -- Apply ambient uniqueness after forgetting the stack-in-groupoids owners.
  obtain ⟨Hc, hHc, α, _huniq⟩ :=
    stackification_unique_up_to_unique_twoIso
      (X : FibredCategoryOver C)
      G₁.toStackFibredCategoryMor G₂.toStackFibredCategoryMor hG₁ hG₂
  let H : Y₁ ⟶ Y₂ :=
    StackInGroupoidsOver.ofFibredCategoryHom (InducedCategory.Hom.toFibredCategoryMor Hc)
  refine ⟨H, ?_, ?_⟩
  · -- The equivalence-over-base predicate is unchanged by the full-subcategory rewrapping.
    simpa [H, StackInGroupoidsOver.Hom.IsEquivalenceOverBase,
      StackInGroupoidsOver.Hom.toBasedFunctor, StackInGroupoidsOver.Hom.toFibredInGroupoidsMor,
      StackInGroupoidsOver.ofFibredCategoryHom, FibredInGroupoidsMor.toBasedFunctor,
      FibredInGroupoidsMor.toFibredCategoryMor, InducedCategory.Hom.IsEquivalenceOverBase,
      InducedCategory.Hom.toBasedFunctor] using hHc
  · -- Lift the ambient compatible `2`-isomorphism back to the owner hom-category.
    dsimp only
    refine ⟨FibredInGroupoidsMor.ofFibredCategoryMorIso ?_⟩
    simpa [H, FibredInGroupoidsMor.toStackFibredCategoryMor,
      StackInGroupoidsOver.ofFibredCategoryHom, StackInGroupoidsOver.Hom.toFibredInGroupoidsMor,
      FibredInGroupoidsMor.toFibredCategoryMor] using α

end

end CategoryTheory
