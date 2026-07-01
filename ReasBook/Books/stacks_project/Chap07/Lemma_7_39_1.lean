import Mathlib
import stacks_project.Chap04.Lemma_4_19_2
import stacks_project.Chap07.«7_32_1_1»
import stacks_project.Chap07.Definition_7_8_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open GrothendieckTopology.Point
open CategoryTheory.SemiRepresentableFamily.Over

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

attribute [local instance] initiallySmall_of_essentiallySmall

/- Domain-style sampling for Lemma 7.39.1:
- primary domain: fibers of cofiltered inverse systems and the induced raw stalk functors on
  sheaves, together with explicit finite covering families on a fixed target;
- sampled owner API:
  `GrothendieckTopology.Point.ofIsCofiltered.fiber`,
  `GrothendieckTopology.Point.ofIsCofiltered.fiberMk`,
  `GrothendieckTopology.Point.ofIsCofiltered.refinementFiber`,
  `Functor.presheafFiber`,
  `GrothendieckTopology.Point.presheafFiber`,
  `GrothendieckTopology.Point.Hom.presheafFiber`,
  `SemiRepresentableFamily.Over`,
  `SemiRepresentableFamily.Over.toSieve`;
- source/core/bridge triage:
  `source-facing`: a directed inverse system `S : ιᵒᵖ ⥤ C`, its associated set-valued functor
  `u`, a fixed-target finite covering family `𝒰 : SemiRepresentableFamily.Over W`, and a
  refinement datum `S ≅ (j.toOrderHom.toFunctor).op ⋙ T`;
  `core/canonical`: `GrothendieckTopology.Point.ofIsCofiltered.fiber`, with raw stalk layer
  `sheafToPresheaf J (Type _) ⋙ (ofIsCofiltered.fiber S).presheafFiber`;
  `bridge/view`: `SemiRepresentableFamily.Over.toSieve` for finite covering families, together
  with the refinement-induced natural transformation `ofIsCofiltered.refinementFiber` between
  these canonical inverse-system fibers and its objectwise/raw-stalk projections.

Primitive data are only the inverse systems and the refinement datum. The covering-surjectivity
data needed to upgrade an inverse system to a site point are absent, so the source-facing theorem
must stay at the inverse-system fiber layer rather than be promoted to `Point.ofIsCofiltered`.
The sheaf-fiber layer is derived API of `Functor.presheafFiber`, and Chapter 7 already packages
explicit fixed-target families by `SemiRepresentableFamily.Over`, so this file should reuse those
owners instead of parallel local inverse-system-fiber or covering-family encodings.
-/
namespace GrothendieckTopology.Point.ofIsCofiltered

variable {ι : Type w} [Preorder ι]

private noncomputable abbrev refinementFiberDiagram (S : ιᵒᵖ ⥤ C) (W : C) :
    ιᵒᵖᵒᵖ ⥤ Type (max u v w) :=
  S.op ⋙ shrinkYoneda.{max u v w}.obj W

variable {ι' : Type w} [Preorder ι'] {S : ιᵒᵖ ⥤ C}
  (j : ι ↪o ι') (T : ι'ᵒᵖ ⥤ C) (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T)

private noncomputable abbrev refinementIndexFunctor :
    ιᵒᵖᵒᵖ ⥤ ι'ᵒᵖᵒᵖ :=
  show ιᵒᵖᵒᵖ ⥤ ι'ᵒᵖᵒᵖ from (j.toOrderHom.toFunctor).op.op

private noncomputable abbrev refinementDiagramHom :
    S.op ⟶ refinementIndexFunctor j ⋙ T.op :=
  show S.op ⟶ refinementIndexFunctor j ⋙ T.op from
    NatTrans.op e.inv ≫ (Functor.opComp (j.toOrderHom.toFunctor).op T).hom

private noncomputable def refinementFiberDiagramMap (W : C) :
    refinementFiberDiagram S W ⟶ refinementIndexFunctor j ⋙ refinementFiberDiagram T W :=
  Functor.whiskerRight (refinementDiagramHom j T e) (shrinkYoneda.{max u v w}.obj W)

/-- Helper for Lemma 7.39.1: the objectwise map on inverse-system fibers induced by a
refinement datum. -/
private noncomputable def refinementFiberApp (W : C) :
    (fiber.{max u v w} S).obj W ⟶ (fiber.{max u v w} T).obj W :=
  colim.map (refinementFiberDiagramMap j T e W) ≫
    colimit.pre (refinementFiberDiagram T W) (refinementIndexFunctor j)

/-- Helper for Lemma 7.39.1: the refinement map sends a canonical fiber generator to the
corresponding refined generator. -/
private theorem refinementFiberApp_fiberMk {U : ιᵒᵖ} {W : C} (f : S.obj U ⟶ W) :
    refinementFiberApp j T e W (fiberMk.{max u v w} f) =
      (show (fiber.{max u v w} T).obj W from fiberMk.{max u v w} (e.inv.app U ≫ f)) := by
  -- First transport the generator through the colimit map induced by the refinement datum.
  rw [refinementFiberApp, show fiberMk.{max u v w} f =
    colimit.ι (S.op ⋙ shrinkYoneda.{max u v w}.obj W) (op U)
      ((shrinkYonedaObjObjEquiv.{max u v w}).symm f) by rfl]
  change colimit.pre (refinementFiberDiagram T W) (refinementIndexFunctor j)
      (colimMap (refinementFiberDiagramMap j T e W)
        (colimit.ι (S.op ⋙ shrinkYoneda.{max u v w}.obj W) (op U)
          ((shrinkYonedaObjObjEquiv.{max u v w}).symm f))) =
    (show (fiber.{max u v w} T).obj W from fiberMk.{max u v w} (e.inv.app U ≫ f))
  have hmap :
      colimMap (refinementFiberDiagramMap j T e W)
        (colimit.ι (S.op ⋙ shrinkYoneda.{max u v w}.obj W) (op U)
          ((shrinkYonedaObjObjEquiv.{max u v w}).symm f)) =
        colimit.ι ((refinementIndexFunctor j) ⋙ refinementFiberDiagram T W) (op U)
          ((refinementFiberDiagramMap j T e W).app (op U)
            ((shrinkYonedaObjObjEquiv.{max u v w}).symm f)) := by
    simpa using congrFun (ι_colimMap (refinementFiberDiagramMap j T e W) (op U))
      ((shrinkYonedaObjObjEquiv.{max u v w}).symm f)
  rw [hmap]
  -- The objectwise component is exactly postcomposition with `e.inv.app U`.
  refine (congrFun (colimit.ι_pre (refinementFiberDiagram T W) (refinementIndexFunctor j) (op U))
      ((refinementFiberDiagramMap j T e W).app (op U)
        ((shrinkYonedaObjObjEquiv.{max u v w}).symm f))).trans ?_
  simpa [fiberMk, refinementFiberDiagramMap, refinementDiagramHom, refinementFiberDiagram] using
    congrArg
      (colimit.ι (refinementFiberDiagram T W) ((refinementIndexFunctor j).obj (op U)))
      (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{max u v w} ((e.inv.app U).op) f)

/-- The natural transformation on inverse-system fiber functors induced by a refinement datum
`S ≅ (j.toOrderHom.toFunctor).op ⋙ T`. -/
noncomputable def refinementFiber :
    fiber.{max u v w} S ⟶ fiber.{max u v w} T where
  app := refinementFiberApp j T e
  naturality := by
    intro X Y f
    -- The refinement map is determined on the canonical fiber generators `fiberMk g`.
    ext x
    rcases fiberMk_jointly_surjective x with ⟨U, g, rfl⟩
    simp [refinementFiberApp_fiberMk]

@[simp]
theorem refinementFiber_app_fiberMk {U : ιᵒᵖ} {W : C} (f : S.obj U ⟶ W) :
    (refinementFiber j T e).app W (fiberMk f) =
      (show (fiber.{max u v w} T).obj W from fiberMk (e.inv.app U ≫ f)) := by
  -- Evaluate the colimit morphism defining `refinementFiber` on the generator `fiberMk f`.
  simpa [refinementFiber] using refinementFiberApp_fiberMk (j := j) (T := T) (e := e) f

end GrothendieckTopology.Point.ofIsCofiltered

section

variable {J : GrothendieckTopology C}

open GrothendieckTopology.Point.ofIsCofiltered
open CategoryTheory.SemiRepresentableFamily.Over

variable (J)

/-- Helper for Lemma 7.39.1: pulling back a fixed-target covering family along a stage map again
gives a covering family in the site. -/
private theorem pullback_covering_family_mem
    [HasPullbacks C] {U W : C} (𝒰 : SemiRepresentableFamily.Over W)
    (h𝒰 : 𝒰.toSieve ∈ J W) (f : U ⟶ W) :
    Sieve.ofArrows (fun k : 𝒰.index ↦ pullback (𝒰.obj k).hom f)
        (fun k : 𝒰.index ↦
          (show pullback (𝒰.obj k).hom f ⟶ U from pullback.snd (𝒰.obj k).hom f)) ∈ J U := by
  -- Identify the branch family with the sieve-theoretic pullback of the original covering family.
  rw [Sieve.ofArrows_eq_pullback_of_isPullback
    (f := fun k : 𝒰.index ↦ (𝒰.obj k).hom)
    (g := f)
    (P := fun k : 𝒰.index ↦ pullback (𝒰.obj k).hom f)
    (p₁ := fun k : 𝒰.index ↦
      (show pullback (𝒰.obj k).hom f ⟶ U from pullback.snd (𝒰.obj k).hom f))
    (p₂ := fun k : 𝒰.index ↦
      (show pullback (𝒰.obj k).hom f ⟶ (𝒰.obj k).left from pullback.fst (𝒰.obj k).hom f))]
  · simpa [SemiRepresentableFamily.Over.toSieve, SemiRepresentableFamily.Over.toPresieve] using
      J.pullback_stable f h𝒰
  · intro k
    -- Each branch square is the canonical pullback square.
    simpa using (IsPullback.of_isLimit (pullbackIsPullback (𝒰.obj k).hom f)).flip

/-- Helper for Lemma 7.39.1: separatedness on the pulled-back covering family makes the stagewise
restriction map into the branch family injective. -/
private theorem stage_pullback_cover_restriction_injective
    [HasPullbacks C] {U W : C} (𝒰 : SemiRepresentableFamily.Over W)
    (h𝒰 : 𝒰.toSieve ∈ J W) (ℱ : Sheaf J (Type (max u v w))) (f : U ⟶ W) :
    Function.Injective
      (fun t : ℱ.obj.obj (op U) ↦
        fun k : 𝒰.index ↦
          ℱ.obj.map
            (show (pullback (𝒰.obj k).hom f ⟶ U) from pullback.snd (𝒰.obj k).hom f).op t) := by
  intro s t hst
  -- Use the source proof's local separatedness step on the pullback cover itself.
  have hconst :
      (fun _ : PUnit ↦ s) = (fun _ : PUnit ↦ t) := by
    apply ℱ.property.hom_ext_ofArrows
      (f := fun k : 𝒰.index ↦
        (show pullback (𝒰.obj k).hom f ⟶ U from pullback.snd (𝒰.obj k).hom f))
      (hf := pullback_covering_family_mem (J := J) 𝒰 h𝒰 f)
    intro k
    funext _
    exact congrFun hst k
  exact congrFun hconst PUnit.unit

/-- Helper for Lemma 7.39.1: two distinct points of a finite product already differ on one
coordinate. -/
private theorem exists_ne_coordinate_of_ne_fun
    {α : Type*} [Finite α] {β : α → Sort*} {x y : ∀ a, β a}
    (hxy : x ≠ y) :
    ∃ a : α, x a ≠ y a := by
  classical
  -- If every coordinate agreed, function extensionality would force equality.
  by_contra h
  apply hxy
  funext a
  by_contra hne
  exact h ⟨a, hne⟩

/-- Helper for Lemma 7.39.1: an injective map into a finite product sends distinct points to
tuples differing on some coordinate. -/
private theorem exists_ne_coordinate_of_injective_map
    {α : Type*} [Finite α] {X : Sort*} {β : α → Sort*}
    (g : X → ∀ a, β a) {x y : X} (hxy : x ≠ y) (hg : Function.Injective g) :
    ∃ a : α, g x a ≠ g y a := by
  -- After applying the injective map, the two product-valued images are still distinct.
  apply exists_ne_coordinate_of_ne_fun
  intro hEq
  apply hxy
  exact hg hEq

/-- Helper for Lemma 7.39.1: once the inverse-system index is nonempty, two elements of the raw
presheaf fiber over `fiber S` admit a common presentation over one object of the category of
elements of `fiber S`. -/
private theorem inverse_system_presheafFiber_jointly_surjective₂
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (S : ιᵒᵖ ⥤ C)
    {F : Cᵒᵖ ⥤ Type (max u v w)}
    (x y : (fiber.{max u v w} S).presheafFiber.obj F) :
    ∃ (X : C) (u : (fiber.{max u v w} S).obj X) (z z' : F.obj (op X)),
      (fiber.{max u v w} S).toPresheafFiber X u F z = x ∧
      (fiber.{max u v w} S).toPresheafFiber X u F z' = y := by
  let _ : Nonempty (ιᵒᵖ) := Opposite.instNonempty
  let _ : IsCofiltered (ιᵒᵖ) := by
    infer_instance
  -- The raw presheaf fiber is a filtered colimit over the category of elements of `fiber S`.
  obtain ⟨⟨X, u⟩, z, z', rfl, rfl⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂
      (colimit.isColimit
        ((CategoryTheory.CategoryOfElements.π (fiber.{max u v w} S)).op ⋙ F))
      x y
  exact ⟨X, u, z, z', rfl, rfl⟩

/-- Helper for Lemma 7.39.1: a natural transformation of filtered diagrams in `Type` whose
components are injective induces an injective map on colimits. -/
private theorem colimit_map_injective_of_app_injective
    {I : Type w} [SmallCategory I] [IsFiltered I]
    {F G : I ⥤ Type (max u v w)} (η : F ⟶ G)
    (hη : ∀ i, Function.Injective (η.app i)) :
    Function.Injective (colim.map η) := by
  intro x y hxy
  obtain ⟨i, x', y', rfl, rfl⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂ (colimit.isColimit F) x y
  have hxy' :
      colimit.ι G i (η.app i x') = colimit.ι G i (η.app i y') := by
    simpa using hxy
  obtain ⟨j, f, hf⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (F := G) (colimit.isColimit G)
      (η.app i x') (η.app i y')).1 hxy'
  have hf' : η.app j (F.map f x') = η.app j (F.map f y') := by
    have hnatx : η.app j (F.map f x') = G.map f (η.app i x') := by
      simpa using congrFun (η.naturality f) x'
    have hnaty : η.app j (F.map f y') = G.map f (η.app i y') := by
      simpa using congrFun (η.naturality f) y'
    exact hnatx.trans (hf.trans hnaty.symm)
  apply Types.colimit_sound' f f
  exact hη j hf'

/-- Helper for Lemma 7.39.1: for a directed inverse system, the raw presheaf fiber is the colimit
of the stagewise section diagram over the index category itself. -/
private noncomputable def inverse_system_presheafFiberCocone
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (S : ιᵒᵖ ⥤ C) (F : Cᵒᵖ ⥤ Type (max u v w)) :
    Cocone (S.op ⋙ F) where
  pt := (fiber.{max u v w} S).presheafFiber.obj F
  ι :=
    { app := fun i ↦
        (fiber.{max u v w} S).toPresheafFiber (S.obj (unop i))
          (fiberMk.{max u v w} (𝟙 (S.obj (unop i)))) F
      naturality := by
        intro i j f
        have hmap :
            (fiber.{max u v w} S).map (S.map f.unop)
                (fiberMk.{max u v w} (𝟙 (S.obj (unop j)))) =
              fiberMk.{max u v w} (𝟙 (S.obj (unop i))) := by
          simp
        simpa [Functor.comp_map, hmap] using
          (fiber.{max u v w} S).toPresheafFiber_w
            (F := F) (S.map f.unop)
            (fiberMk.{max u v w} (𝟙 (S.obj (unop j)))) }

/-- Helper for Lemma 7.39.1: the cocone indexed by the original directed preorder computes the raw
presheaf fiber of the associated inverse-system fiber functor. -/
private noncomputable def inverse_system_presheafFiber_isColimit
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (S : ιᵒᵖ ⥤ C) (F : Cᵒᵖ ⥤ Type (max u v w)) :
    IsColimit (inverse_system_presheafFiberCocone (S := S) F) := by
  let _ : Nonempty (ιᵒᵖ) := Opposite.instNonempty
  let _ : IsCofiltered (ιᵒᵖ) := by
    infer_instance
  simpa [inverse_system_presheafFiberCocone, Functor.presheafFiber, Functor.toPresheafFiber] using
    (Functor.Final.isColimitWhiskerEquiv
      (GrothendieckTopology.Point.ofIsCofiltered.functor.{max u v w} (p := S)).op
      (colimit.cocone (((CategoryTheory.CategoryOfElements.π
        (fiber.{max u v w} S)).op) ⋙ F))).2
      (colimit.isColimit (((CategoryTheory.CategoryOfElements.π
        (fiber.{max u v w} S)).op) ⋙ F))

/-- Helper for Lemma 7.39.1: the cofinal tail of a directed preorder above `j₁`. -/
private def tail_inclusion {ι : Type w} [Preorder ι] (j₁ : ι) :
    Set.Ici j₁ ↪o ι where
  toFun := fun j ↦ j.1
  inj' := fun _ _ h ↦ Subtype.ext h
  map_rel_iff' := by
    intro a b
    rfl

/-- Helper for Lemma 7.39.1: the original inverse system restricted to the tail above `j₁`. -/
private noncomputable abbrev tail_system
    {ι : Type w} [Preorder ι] (S : ιᵒᵖ ⥤ C) (j₁ : ι) :
    (Set.Ici j₁)ᵒᵖ ⥤ C :=
  ((tail_inclusion j₁).toOrderHom.toFunctor).op ⋙ S

/-- Helper for Lemma 7.39.1: the object at a tail stage in the chosen pullback branch system. -/
private noncomputable abbrev branch_system_obj
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    (j : (Set.Ici j₁)ᵒᵖ) : C :=
  pullback (𝒰.obj k).hom (S.map (homOfLE (unop j).2).op ≫ f₁)

/-- Helper for Lemma 7.39.1: the stage map into `W` is compatible with restriction along the tail
ordering. -/
private theorem branch_system_stage_compat
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    {X Y : (Set.Ici j₁)ᵒᵖ} (g : X ⟶ Y) :
    (S.map (homOfLE (unop X).2).op ≫ f₁) ≫ 𝟙 W =
      S.map (homOfLE (leOfHom g.unop)).op ≫ (S.map (homOfLE (unop Y).2).op ≫ f₁) := by
  -- Rewrite the restriction to `X` as the composite of the restriction to `Y`
  -- with the transition map `g.unop` inside the tail preorder.
  have htail :
      (unop Y).2.trans (leOfHom g.unop) = (unop X).2 := by
    apply Subsingleton.elim
  rw [Category.comp_id]
  -- Normalize only the right-hand side to the single transition from `j₁` to `X`.
  conv_rhs =>
    rw [← Category.assoc, ← Functor.map_comp]
  have hop :=
    congrArg (fun h => S.map h ≫ f₁)
      (congrArg Quiver.Hom.op (homOfLE_comp (unop Y).2 (leOfHom g.unop)))
  simpa only [htail] using hop

/-- Helper for Lemma 7.39.1: the transition map in the chosen pullback branch system. -/
private noncomputable abbrev branch_system_map
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    {X Y : (Set.Ici j₁)ᵒᵖ} (g : X ⟶ Y) :
    branch_system_obj S j₁ f₁ 𝒰 k X ⟶ branch_system_obj S j₁ f₁ 𝒰 k Y :=
  pullback.map
    (𝒰.obj k).hom
    (S.map (homOfLE (unop X).2).op ≫ f₁)
    (𝒰.obj k).hom
    (S.map (homOfLE (unop Y).2).op ≫ f₁)
    (𝟙 _)
    (S.map (homOfLE (leOfHom g.unop)).op)
    (𝟙 _)
    (by simp)
    (branch_system_stage_compat (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k) g)

/-- Helper for Lemma 7.39.1: the ambient transition map of `S` attached to the tail identity
morphism is the identity on the corresponding stage. -/
private theorem tail_identity_map_on_stage
    {ι : Type w} [Preorder ι] (S : ιᵒᵖ ⥤ C) (j₁ : ι) (X : (Set.Ici j₁)ᵒᵖ) :
    S.map (homOfLE (leOfHom (𝟙 X).unop)).op =
      𝟙 (S.obj (op (((unop X : Set.Ici j₁) : ι)))) := by
  -- Normalize the identity morphism in the tail preorder to the ambient identity of `S`.
  simpa only [homOfLE_leOfHom, homOfLE_refl] using
    Functor.map_id S (op (((unop X : Set.Ici j₁) : ι)))

/-- Helper for Lemma 7.39.1: the branch transition at an identity morphism is the identity map. -/
private theorem branch_system_map_id
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    (X : (Set.Ici j₁)ᵒᵖ) :
    branch_system_map S j₁ f₁ 𝒰 k (𝟙 X) = 𝟙 _ := by
  -- Route correction: first normalize the ambient identity map of `S`, then the branch map is
  -- checked on the two pullback projections.
  apply pullback.hom_ext
  · -- The first projection of `pullback.map` is the chosen first leg of the lift.
    rw [branch_system_map]
    delta pullback.map
    rw [pullback.lift_fst]
    calc
      pullback.fst (𝒰.obj k).hom (S.map (homOfLE (unop X).2).op ≫ f₁) ≫
          𝟙 (𝒰.obj k).left =
        pullback.fst (𝒰.obj k).hom (S.map (homOfLE (unop X).2).op ≫ f₁) := by
          simp
      _ =
        𝟙 (branch_system_obj S j₁ f₁ 𝒰 k X) ≫
          pullback.fst (𝒰.obj k).hom (S.map (homOfLE (unop X).2).op ≫ f₁) := by
            simp
  · -- The second projection is the ambient tail identity map, which we now normalize explicitly.
    rw [branch_system_map]
    delta pullback.map
    rw [pullback.lift_snd]
    rw [tail_identity_map_on_stage (S := S) (j₁ := j₁) X]
    calc
      pullback.snd (𝒰.obj k).hom (S.map (homOfLE (unop X).2).op ≫ f₁) ≫
          𝟙 (S.obj (op (((unop X : Set.Ici j₁) : ι)))) =
        pullback.snd (𝒰.obj k).hom (S.map (homOfLE (unop X).2).op ≫ f₁) := by
          simp
      _ =
        𝟙 (branch_system_obj S j₁ f₁ 𝒰 k X) ≫
          pullback.snd (𝒰.obj k).hom (S.map (homOfLE (unop X).2).op ≫ f₁) := by
            simp

/-- Helper for Lemma 7.39.1: branch transitions compose as expected. -/
private theorem branch_system_map_comp
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    {X Y Z : (Set.Ici j₁)ᵒᵖ} (g₁ : X ⟶ Y) (g₂ : Y ⟶ Z) :
    branch_system_map S j₁ f₁ 𝒰 k g₁ ≫ branch_system_map S j₁ f₁ 𝒰 k g₂ =
      branch_system_map S j₁ f₁ 𝒰 k (g₁ ≫ g₂) := by
  -- The pullback transitions compose because the second coordinates are exactly the functorial
  -- restriction maps of `S` along the tail preorder.
  simpa [branch_system_map, Category.assoc, ← Functor.map_comp, ← op_comp,
      homOfLE_comp, homOfLE_leOfHom] using
    (pullback.map_comp
      (f := (𝒰.obj k).hom)
      (g := S.map (homOfLE (unop X).2).op ≫ f₁)
      (f' := (𝒰.obj k).hom)
      (g' := S.map (homOfLE (unop Y).2).op ≫ f₁)
      (f'' := (𝒰.obj k).hom)
      (g'' := S.map (homOfLE (unop Z).2).op ≫ f₁)
      (𝟙 _)
      (𝟙 _)
      (S.map (homOfLE (leOfHom g₁.unop)).op)
      (S.map (homOfLE (leOfHom g₂.unop)).op)
      (𝟙 W)
      (𝟙 W)
      (by simp)
      (branch_system_stage_compat (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k) g₁)
      (by simp)
      (branch_system_stage_compat (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k) g₂))

/-- Helper for Lemma 7.39.1: the pullback branch inverse system over the tail above `j₁`
associated with the cover member `k`. -/
private noncomputable def branch_system
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    (Set.Ici j₁)ᵒᵖ ⥤ C :=
  { obj := branch_system_obj S j₁ f₁ 𝒰 k
    map := fun g ↦ branch_system_map S j₁ f₁ 𝒰 k g
    map_id := branch_system_map_id (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)
    map_comp := fun f g ↦
      (branch_system_map_comp (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k) f g).symm }

/-- Helper for Lemma 7.39.1: the canonical colimit of the stagewise section diagram of an inverse
system identifies with the raw presheaf fiber of that system. -/
private noncomputable def inverse_system_presheafFiber_colimitIso
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (S : ιᵒᵖ ⥤ C) (F : Cᵒᵖ ⥤ Type (max u v w)) :
    colimit (S.op ⋙ F) ≅ (fiber.{max u v w} S).presheafFiber.obj F :=
  (colimit.isColimit (S.op ⋙ F)).coconePointUniqueUpToIso
    (inverse_system_presheafFiber_isColimit (S := S) F)

/-- Helper for Lemma 7.39.1: the refinement index obtained by adjoining the branch tail to the
original inverse-system index. -/
private structure glued_refinement_index {ι : Type w} [Preorder ι] (j₁ : ι) where
  val : Sum ι (Set.Ici j₁)

/-- Helper for Lemma 7.39.1: order on the glued refinement index, with right-summand branch stages
lying above exactly the original stages below their underlying tail index. -/
private instance glued_refinement_preorder
    {ι : Type w} [Preorder ι] (j₁ : ι) :
    Preorder (glued_refinement_index j₁) where
  le x y :=
    match x.val, y.val with
    | Sum.inl i, Sum.inl i' => i ≤ i'
    | Sum.inl i, Sum.inr j => i ≤ j.1
    | Sum.inr _, Sum.inl _ => False
    | Sum.inr j, Sum.inr j' => j ≤ j'
  le_refl x := by
    -- Each summand uses the ambient reflexive order, and there are no right-to-left relations.
    cases x with
    | mk x =>
        cases x <;> simp
  le_trans x y z hxy hyz := by
    -- Route correction: encode the source order on `J ⊔ J₀` directly, then transitivity is a
    -- finite case split over the two summands.
    cases x with
    | mk x =>
        cases y with
        | mk y =>
            cases z with
            | mk z =>
                cases x <;> cases y <;> cases z <;> simp at hxy hyz ⊢
                all_goals exact le_trans hxy hyz

/-- Helper for Lemma 7.39.1: the glued refinement index is directed, following the source proof's
order on `J ⊔ J₀`. -/
private instance glued_refinement_isDirected
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] (j₁ : ι) :
    IsDirected (glued_refinement_index j₁) (· ≤ ·) := by
  refine ⟨?_⟩
  intro x y
  -- Follow the source construction: choose a common upper bound in the ambient directed set and
  -- place it in the summand that stays above both inputs.
  cases x with
  | mk x =>
      cases y with
      | mk y =>
          cases x with
          | inl i =>
              cases y with
              | inl i' =>
                  obtain ⟨k, hik, hi'k⟩ := directed_of (· ≤ ·) i i'
                  exact ⟨⟨Sum.inl k⟩, by simpa using hik, by simpa using hi'k⟩
              | inr j =>
                  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j.1
                  exact ⟨⟨Sum.inr ⟨k, j.2.trans hjk⟩⟩, by simpa using hik, by simpa using hjk⟩
          | inr i =>
              cases y with
              | inl i' =>
                  obtain ⟨k, hik, hi'k⟩ := directed_of (· ≤ ·) i.1 i'
                  exact
                    ⟨⟨Sum.inr ⟨k, i.2.trans hik⟩⟩, by simpa using hik, by simpa using hi'k⟩
              | inr j =>
                  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i.1 j.1
                  exact
                    ⟨⟨Sum.inr ⟨k, i.2.trans hik⟩⟩, by simpa using hik, by simpa using hjk⟩

/-- Helper for Lemma 7.39.1: the order embedding of the original inverse-system index into the
glued refinement index. -/
private def glued_refinement_inclusion {ι : Type w} [Preorder ι] (j₁ : ι) :
    ι ↪o glued_refinement_index j₁ where
  toFun := fun i ↦ ⟨Sum.inl i⟩
  inj' := by
    intro i i' h
    exact Sum.inl.inj (congrArg glued_refinement_index.val h)
  map_rel_iff' := by
    intro i i'
    rfl

/-- Helper for Lemma 7.39.1: the order embedding of the chosen tail into the right summand of the
glued refinement index. -/
private def glued_refinement_tail_inclusion {ι : Type w} [Preorder ι] (j₁ : ι) :
    Set.Ici j₁ ↪o glued_refinement_index j₁ where
  toFun := fun i ↦ ⟨Sum.inr i⟩
  inj' := by
    intro i i' h
    exact Sum.inr.inj (congrArg glued_refinement_index.val h)
  map_rel_iff' := by
    intro i i'
    rfl

/-- Helper for Lemma 7.39.1: the second projection of a branch transition is the ambient
restriction map of the original inverse system. -/
private theorem branch_system_map_snd_assoc
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    {X Y : (Set.Ici j₁)ᵒᵖ} (g : X ⟶ Y) :
    branch_system_map S j₁ f₁ 𝒰 k g ≫
        pullback.snd (𝒰.obj k).hom (S.map (homOfLE (unop Y).2).op ≫ f₁) =
      pullback.snd (𝒰.obj k).hom (S.map (homOfLE (unop X).2).op ≫ f₁) ≫
        S.map (homOfLE (leOfHom g.unop)).op := by
  -- Unfold the pullback map only far enough to read off its second projection.
  rw [branch_system_map]
  delta pullback.map
  rw [pullback.lift_snd]

/-- Helper for Lemma 7.39.1: after a right-branch transition, the mixed map from the branch tail
to the left ambient system normalizes to the direct mixed map. -/
private theorem glued_refinement_mixed_map_comp
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    {i : ι} {j j' : Set.Ici j₁} (hij' : i ≤ j'.1) (hjj' : j' ≤ j) :
    branch_system_map S j₁ f₁ 𝒰 k (show op j ⟶ op j' from (homOfLE hjj').op) ≫
        pullback.snd (𝒰.obj k).hom (S.map (homOfLE j'.2).op ≫ f₁) ≫
          S.map (homOfLE hij').op =
      pullback.snd (𝒰.obj k).hom (S.map (homOfLE j.2).op ≫ f₁) ≫
        S.map (homOfLE (hij'.trans hjj')).op := by
  -- First normalize the branch transition on the pullback second projection.
  calc
    branch_system_map S j₁ f₁ 𝒰 k (show op j ⟶ op j' from (homOfLE hjj').op) ≫
        pullback.snd (𝒰.obj k).hom (S.map (homOfLE j'.2).op ≫ f₁) ≫
          S.map (homOfLE hij').op =
      (branch_system_map S j₁ f₁ 𝒰 k
          (show op j ⟶ op j' from (homOfLE hjj').op) ≫
        pullback.snd (𝒰.obj k).hom (S.map (homOfLE j'.2).op ≫ f₁)) ≫
          S.map (homOfLE hij').op := by
            rw [← Category.assoc]
    _ =
      (pullback.snd (𝒰.obj k).hom (S.map (homOfLE j.2).op ≫ f₁) ≫
          S.map (homOfLE hjj').op) ≫ S.map (homOfLE hij').op := by
            rw [branch_system_map_snd_assoc (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)
              (g := show op j ⟶ op j' from (homOfLE hjj').op)]
    _ =
      pullback.snd (𝒰.obj k).hom (S.map (homOfLE j.2).op ≫ f₁) ≫
          S.map (homOfLE hjj').op ≫ S.map (homOfLE hij').op := by
            rw [Category.assoc]
    -- Then collapse the two ambient restriction maps into the single direct restriction.
    _ =
      pullback.snd (𝒰.obj k).hom (S.map (homOfLE j.2).op ≫ f₁) ≫
        S.map (homOfLE (hij'.trans hjj')).op := by
          rw [← Functor.map_comp]
          have hjj'₀ : j'.1 ≤ j.1 := hjj'
          have hcomp :
              (show op j.1 ⟶ op j'.1 from (homOfLE hjj'₀).op) ≫
                  (show op j'.1 ⟶ op i from (homOfLE hij').op) =
                (show op j.1 ⟶ op i from (homOfLE (hij'.trans hjj'₀)).op) := by
            exact Subsingleton.elim _ _
          exact congrArg
            (fun m ↦
              pullback.snd (𝒰.obj k).hom (S.map (homOfLE j.2).op ≫ f₁) ≫ S.map m)
            hcomp

/-- Helper for Lemma 7.39.1: a mixed map from the right summand followed by a left-left ambient
transition is the direct mixed map to the smaller left stage. -/
private theorem glued_refinement_left_map_comp
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    {i i' : ι} {j : Set.Ici j₁} (hii' : i ≤ i') (hi'j : i' ≤ j.1) :
    pullback.snd (𝒰.obj k).hom (S.map (homOfLE j.2).op ≫ f₁) ≫
        S.map (homOfLE hi'j).op ≫ S.map (homOfLE hii').op =
      pullback.snd (𝒰.obj k).hom (S.map (homOfLE j.2).op ≫ f₁) ≫
        S.map (homOfLE (hii'.trans hi'j)).op := by
  -- This is just functoriality of the ambient system `S` on the left summand.
  simpa [Category.assoc, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- Helper for Lemma 7.39.1: the glued refinement system uses the original stage on the left
summand and the chosen branch stage on the right summand. -/
private noncomputable def glued_refinement_system_obj
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    (X : (glued_refinement_index j₁)ᵒᵖ) : C :=
  match (unop X).val with
  | Sum.inl i => S.obj (op i)
  | Sum.inr j => branch_system_obj S j₁ f₁ 𝒰 k (op j)

/-- Helper for Lemma 7.39.1: the glued refinement system uses the ambient restriction maps on the
left, the branch restriction maps on the right, and the mixed pullback-snd maps from right to
left. -/
private noncomputable def glued_refinement_system_map
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    {X Y : (glued_refinement_index j₁)ᵒᵖ} (g : X ⟶ Y) :
    glued_refinement_system_obj S j₁ f₁ 𝒰 k X ⟶
      glued_refinement_system_obj S j₁ f₁ 𝒰 k Y := by
  cases X using Opposite.rec
  rename_i x
  cases Y using Opposite.rec
  rename_i y
  cases x with
  | mk x =>
      cases y with
      | mk y =>
          cases x with
          | inl i =>
              cases y with
              | inl i' =>
                  exact S.map (show op i ⟶ op i' from (homOfLE (show i' ≤ i from leOfHom g.unop)).op)
              | inr _ =>
                  exact False.elim (show False from leOfHom g.unop)
          | inr j =>
              cases y with
              | inl i =>
                  exact
                    pullback.snd (𝒰.obj k).hom (S.map (homOfLE j.2).op ≫ f₁) ≫
                      S.map (show op j.1 ⟶ op i from
                        (homOfLE (show i ≤ j.1 from leOfHom g.unop)).op)
              | inr j' =>
                  exact
                    branch_system_map S j₁ f₁ 𝒰 k
                      (show op j ⟶ op j' from
                        (homOfLE (show j' ≤ j from leOfHom g.unop)).op)

/-- Helper for Lemma 7.39.1: the glued morphism on the identity map is the identity. -/
private theorem glued_refinement_system_map_id
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    (X : (glued_refinement_index j₁)ᵒᵖ) :
    glued_refinement_system_map S j₁ f₁ 𝒰 k (𝟙 X) =
      𝟙 (glued_refinement_system_obj S j₁ f₁ 𝒰 k X) := by
  -- The identity stays inside one summand, so the result is the ambient or branch identity map.
  cases X using Opposite.rec
  rename_i x
  cases x with
  | mk x =>
      cases x with
      | inl i =>
          simpa [glued_refinement_system_map, glued_refinement_system_obj,
            homOfLE_leOfHom, homOfLE_refl] using Functor.map_id S (op i)
      | inr j =>
          simpa [glued_refinement_system_map, glued_refinement_system_obj] using
            branch_system_map_id (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k) (op j)

/-- Helper for Lemma 7.39.1: the glued morphism map is functorial. -/
private theorem glued_refinement_system_map_comp
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    {X Y Z : (glued_refinement_index j₁)ᵒᵖ} (g : X ⟶ Y) (h : Y ⟶ Z) :
    glued_refinement_system_map S j₁ f₁ 𝒰 k g ≫
        glued_refinement_system_map S j₁ f₁ 𝒰 k h =
      glued_refinement_system_map S j₁ f₁ 𝒰 k (g ≫ h) := by
  -- Route correction: the source gluing has only one nontrivial composition, namely
  -- right-right followed by right-left; the remaining cases reduce to ambient or branch
  -- functoriality, or are impossible in the glued preorder.
  cases X using Opposite.rec
  rename_i x
  cases Y using Opposite.rec
  rename_i y
  cases Z using Opposite.rec
  rename_i z
  cases x with
  | mk x =>
      cases y with
      | mk y =>
          cases z with
          | mk z =>
              cases x with
              | inl i =>
                  cases y with
                  | inl i' =>
                      cases z with
                      | inl i'' =>
                          simpa [glued_refinement_system_map, ← op_comp, homOfLE_comp] using
                            (Functor.map_comp S
                              (show op i ⟶ op i' from
                                (homOfLE (show i' ≤ i from leOfHom g.unop)).op)
                              (show op i' ⟶ op i'' from
                                (homOfLE (show i'' ≤ i' from leOfHom h.unop)).op)).symm
                      | inr _ =>
                          exfalso
                          exact show False from leOfHom h.unop
                  | inr _ =>
                      exfalso
                      exact show False from leOfHom g.unop
              | inr j =>
                  cases y with
                  | inl i' =>
                      cases z with
                      | inl i =>
                          simpa [glued_refinement_system_map] using
                            glued_refinement_left_map_comp
                              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)
                              (i := i) (i' := i') (j := j)
                              (hii' := show i ≤ i' from leOfHom h.unop)
                              (hi'j := show i' ≤ j.1 from leOfHom g.unop)
                      | inr _ =>
                          exfalso
                          exact show False from leOfHom h.unop
                  | inr j' =>
                      cases z with
                      | inl i =>
                          simpa [glued_refinement_system_map] using
                            glued_refinement_mixed_map_comp
                              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)
                              (i := i) (j := j) (j' := j')
                              (hij' := show i ≤ j'.1 from leOfHom h.unop)
                              (hjj' := show j' ≤ j from leOfHom g.unop)
                      | inr j'' =>
                          simpa [glued_refinement_system_map] using
                            branch_system_map_comp (S := S) (j₁ := j₁) (f₁ := f₁)
                              (𝒰 := 𝒰) (k := k)
                              (show op j ⟶ op j' from
                                (homOfLE (show j' ≤ j from leOfHom g.unop)).op)
                              (show op j' ⟶ op j'' from
                                (homOfLE (show j'' ≤ j' from leOfHom h.unop)).op)

/-- Helper for Lemma 7.39.1: the glued refinement system contains the original system on the left
and the chosen pullback branch system on the right. -/
private noncomputable def glued_refinement_system
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    (glued_refinement_index j₁)ᵒᵖ ⥤ C :=
  { obj := glued_refinement_system_obj S j₁ f₁ 𝒰 k
    map := fun g ↦ glued_refinement_system_map S j₁ f₁ 𝒰 k g
    map_id := glued_refinement_system_map_id (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)
    map_comp := fun g h ↦
      (glued_refinement_system_map_comp
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k) g h).symm }

/-- Helper for Lemma 7.39.1: restricting the glued refinement system to the left summand recovers
the original inverse system. -/
private noncomputable def glued_refinement_iso
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    S ≅ ((glued_refinement_inclusion j₁).toOrderHom.toFunctor).op ⋙
      glued_refinement_system S j₁ f₁ 𝒰 k := by
  -- Restricting to the left summand does not change objects or transition maps of `S`.
  refine NatIso.ofComponents (fun _ ↦ Iso.refl _) ?_
  intro X Y g
  have hg :
      (show op (unop X) ⟶ op (unop Y) from
        (homOfLE (show unop Y ≤ unop X from leOfHom g.unop)).op) = g := by
    exact congrArg Quiver.Hom.op (homOfLE_leOfHom g.unop)
  simpa [glued_refinement_system, glued_refinement_system_obj, glued_refinement_system_map,
    glued_refinement_inclusion] using congrArg (fun f ↦ S.map f) hg

/-- Helper for Lemma 7.39.1: on each left stage, the inverse component of the glued refinement
identification is the identity. -/
private theorem glued_refinement_iso_inv_app_eq_id
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ j0 : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    (glued_refinement_iso S j₁ f₁ 𝒰 k).inv.app (op j0) = 𝟙 (S.obj (op j0)) := by
  -- The glued refinement agrees with `S` on the left summand objectwise.
  simp [glued_refinement_iso]

/-- Helper for Lemma 7.39.1: restricting the glued refinement system to the right summand recovers
the chosen pullback branch system. -/
private noncomputable def glued_refinement_right_restrict_iso
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    ((glued_refinement_tail_inclusion j₁).toOrderHom.toFunctor).op ⋙
        glued_refinement_system S j₁ f₁ 𝒰 k ≅
      branch_system S j₁ f₁ 𝒰 k := by
  -- The right summand was defined to be literally the branch system, so all components are
  -- identities and the only work is the right-right map normalization.
  refine NatIso.ofComponents (fun _ ↦ Iso.refl _) ?_
  intro X Y g
  simpa [glued_refinement_system, glued_refinement_system_obj, glued_refinement_system_map,
    branch_system, glued_refinement_tail_inclusion]

/-- Helper for Lemma 7.39.1: every stage of the glued refinement maps to some right-branch stage,
so the right summand is final for the raw-fiber colimit computation. -/
private theorem glued_refinement_tail_inclusion_final
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] (j₁ : ι) :
    Functor.Final ((glued_refinement_tail_inclusion j₁).toOrderHom.toFunctor) := by
  -- Follow the source order on `J ⊔ J₀`: a right stage maps to itself, and a left stage maps to
  -- some tail stage above both that stage and `j₁`.
  let _ : IsDirected (Set.Ici j₁) (· ≤ ·) := by
    refine ⟨?_⟩
    intro a b
    obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨k, a.2.trans hak⟩, by simpa using hak, by simpa using hbk⟩
  refine Functor.final_of_exists_of_isFiltered
    ((glued_refinement_tail_inclusion j₁).toOrderHom.toFunctor) ?_ ?_
  · intro d
    cases d with
    | mk x =>
        cases x with
        | inl i =>
            obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j₁
            refine ⟨⟨k, hjk⟩, ?_⟩
            exact ⟨show (⟨Sum.inl i⟩ : glued_refinement_index j₁) ⟶
                (glued_refinement_tail_inclusion j₁).toOrderHom.toFunctor.obj ⟨k, hjk⟩ from
                  homOfLE hik⟩
        | inr j =>
            refine ⟨j, ?_⟩
            exact ⟨𝟙 ((glued_refinement_tail_inclusion j₁).toOrderHom.toFunctor.obj j)⟩
  · intro d c s s'
    refine ⟨c, 𝟙 c, ?_⟩
    simpa using (Subsingleton.elim s s')
/-- Helper for Lemma 7.39.1: a common representative at stage `j₁` of the original inverse
system gives two actual tail germs whose images are `s` and `s'`. -/
private theorem common_tail_stage_sections
    {ι : Type w} [Preorder ι] (S' : ιᵒᵖ ⥤ C) (j₁ : ι)
    {Fobj : Cᵒᵖ ⥤ Type (max u v w)}
    {s s' : (fiber.{max u v w} S').presheafFiber.obj Fobj}
    {t₁ t₁' : Fobj.obj (op (S'.obj (op j₁)))}
    (hs₁ :
      (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
        (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁ = s)
    (hs₁' :
      (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
        (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁' = s')
    (hss' : s ≠ s') :
    ∃ ŝ ŝ' : (fiber.{max u v w} (tail_system S' j₁)).presheafFiber.obj Fobj,
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ = s ∧
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ' = s' ∧
      ŝ ≠ ŝ' := by
  let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
  let xTail : (fiber.{max u v w} (tail_system S' j₁)).obj (S'.obj (op j₁)) :=
    fiberMk.{max u v w} (U := op jTail) (X := S'.obj (op j₁)) (𝟙 (S'.obj (op j₁)))
  let ŝ : (fiber.{max u v w} (tail_system S' j₁)).presheafFiber.obj Fobj :=
    (fiber.{max u v w} (tail_system S' j₁)).toPresheafFiber (S'.obj (op j₁)) xTail Fobj t₁
  let ŝ' : (fiber.{max u v w} (tail_system S' j₁)).presheafFiber.obj Fobj :=
    (fiber.{max u v w} (tail_system S' j₁)).toPresheafFiber (S'.obj (op j₁)) xTail Fobj t₁'
  have hŝ :
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ = s := by
    -- Evaluate the tail-to-original refinement on the first canonical tail generator.
    have hrewrite :
        (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
          ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
            (S'.obj (op j₁)) xTail) Fobj t₁ =
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁ := by
      have hrewrite₀ :
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
              (S'.obj (op j₁)) xTail) Fobj t₁ =
            (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w}
                ((Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app
                  (op jTail) ≫ 𝟙 (S'.obj (op j₁)))) Fobj t₁ := by
        simpa only [jTail, xTail] using
          congrArg
            (fun x ↦
              (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁)) x Fobj t₁)
            (refinementFiber_app_fiberMk (j := tail_inclusion j₁) (T := S') (e := Iso.refl _)
              (U := op jTail) (W := S'.obj (op j₁)) (f := 𝟙 (S'.obj (op j₁))))
      have hrewrite₁ :
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w}
                ((Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app
                  (op jTail) ≫ 𝟙 (S'.obj (op j₁)))) Fobj t₁ =
            (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁ := by
        have hunit :
            (Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app (op jTail) ≫
              𝟙 (S'.obj (op j₁)) =
            𝟙 (S'.obj (op j₁)) := by
          simp [jTail]
        exact congrArg
          (fun g ↦
            (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w} g) Fobj t₁)
          hunit
      exact hrewrite₀.trans hrewrite₁
    calc
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ =
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
              (S'.obj (op j₁)) xTail) Fobj t₁ := by
              simpa [ŝ, xTail] using
                congrFun
                  (NatTrans.toPresheafFiber_presheafFiber_app
                    (η := refinementFiber (tail_inclusion j₁) S' (Iso.refl _))
                    (F := Fobj) (X := S'.obj (op j₁)) xTail)
                  t₁
      _ = (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁ := hrewrite
      _ = s := hs₁
  have hŝ' :
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ' = s' := by
    -- The same normalization identifies the second tail generator with `s'`.
    have hrewrite :
        (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
          ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
            (S'.obj (op j₁)) xTail) Fobj t₁' =
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁' := by
      have hrewrite₀ :
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
              (S'.obj (op j₁)) xTail) Fobj t₁' =
            (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w}
                ((Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app
                  (op jTail) ≫ 𝟙 (S'.obj (op j₁)))) Fobj t₁' := by
        simpa only [jTail, xTail] using
          congrArg
            (fun x ↦
              (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁)) x Fobj t₁')
            (refinementFiber_app_fiberMk (j := tail_inclusion j₁) (T := S') (e := Iso.refl _)
              (U := op jTail) (W := S'.obj (op j₁)) (f := 𝟙 (S'.obj (op j₁))))
      have hrewrite₁ :
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w}
                ((Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app
                  (op jTail) ≫ 𝟙 (S'.obj (op j₁)))) Fobj t₁' =
            (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁' := by
        have hunit :
            (Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app (op jTail) ≫
              𝟙 (S'.obj (op j₁)) =
            𝟙 (S'.obj (op j₁)) := by
          simp [jTail]
        exact congrArg
          (fun g ↦
            (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w} g) Fobj t₁')
          hunit
      exact hrewrite₀.trans hrewrite₁
    calc
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ' =
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
              (S'.obj (op j₁)) xTail) Fobj t₁' := by
              simpa [ŝ', xTail] using
                congrFun
                  (NatTrans.toPresheafFiber_presheafFiber_app
                    (η := refinementFiber (tail_inclusion j₁) S' (Iso.refl _))
                    (F := Fobj) (X := S'.obj (op j₁)) xTail)
                  t₁'
      _ = (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁' := hrewrite
      _ = s' := hs₁'
  have hne : ŝ ≠ ŝ' := by
    -- Distinct images in the original raw fiber force the two tail germs to be distinct.
    intro hEq
    apply hss'
    have hImage :
        ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ =
          ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ' := by
      simp [hEq]
    exact hŝ.symm.trans (hImage.trans hŝ')
  exact ⟨ŝ, ŝ', hŝ, hŝ', hne⟩

/-- Helper for Lemma 7.39.1: the explicit canonical tail-stage germs at `j₁` already map back to
`s` and `s'`, and they stay distinct. -/
private theorem canonical_tail_stage_sections
    {ι : Type w} [Preorder ι] (S' : ιᵒᵖ ⥤ C) (j₁ : ι)
    {Fobj : Cᵒᵖ ⥤ Type (max u v w)}
    {s s' : (fiber.{max u v w} S').presheafFiber.obj Fobj}
    {t₁ t₁' : Fobj.obj (op (S'.obj (op j₁)))}
    (hs₁ :
      (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
        (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁ = s)
    (hs₁' :
      (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
        (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁' = s')
    (hss' : s ≠ s') :
    let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
    let xTail : (fiber.{max u v w} (tail_system S' j₁)).obj (S'.obj (op j₁)) :=
      fiberMk.{max u v w} (U := op jTail) (X := S'.obj (op j₁)) (𝟙 (S'.obj (op j₁)))
    let ŝ : (fiber.{max u v w} (tail_system S' j₁)).presheafFiber.obj Fobj :=
      (fiber.{max u v w} (tail_system S' j₁)).toPresheafFiber (S'.obj (op j₁)) xTail Fobj t₁
    let ŝ' : (fiber.{max u v w} (tail_system S' j₁)).presheafFiber.obj Fobj :=
      (fiber.{max u v w} (tail_system S' j₁)).toPresheafFiber (S'.obj (op j₁)) xTail Fobj t₁'
    ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ = s ∧
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ' = s' ∧
      ŝ ≠ ŝ' := by
  let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
  let xTail : (fiber.{max u v w} (tail_system S' j₁)).obj (S'.obj (op j₁)) :=
    fiberMk.{max u v w} (U := op jTail) (X := S'.obj (op j₁)) (𝟙 (S'.obj (op j₁)))
  let ŝ : (fiber.{max u v w} (tail_system S' j₁)).presheafFiber.obj Fobj :=
    (fiber.{max u v w} (tail_system S' j₁)).toPresheafFiber (S'.obj (op j₁)) xTail Fobj t₁
  let ŝ' : (fiber.{max u v w} (tail_system S' j₁)).presheafFiber.obj Fobj :=
    (fiber.{max u v w} (tail_system S' j₁)).toPresheafFiber (S'.obj (op j₁)) xTail Fobj t₁'
  have hŝ :
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ = s := by
    -- Evaluate the tail-to-original refinement on the first canonical tail generator.
    have hrewrite :
        (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
          ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
            (S'.obj (op j₁)) xTail) Fobj t₁ =
        (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
          (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁ := by
      have hrewrite₀ :
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
              (S'.obj (op j₁)) xTail) Fobj t₁ =
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            (fiberMk.{max u v w}
              ((Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app
                (op jTail) ≫ 𝟙 (S'.obj (op j₁)))) Fobj t₁ := by
        simpa only [jTail, xTail] using
          congrArg
            (fun x ↦
              (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁)) x Fobj t₁)
            (refinementFiber_app_fiberMk (j := tail_inclusion j₁) (T := S') (e := Iso.refl _)
              (U := op jTail) (W := S'.obj (op j₁)) (f := 𝟙 (S'.obj (op j₁))))
      have hrewrite₁ :
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w}
                ((Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app
                  (op jTail) ≫ 𝟙 (S'.obj (op j₁)))) Fobj t₁ =
            (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁ := by
        have hunit :
            (Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app (op jTail) ≫
              𝟙 (S'.obj (op j₁)) =
            𝟙 (S'.obj (op j₁)) := by
          simp [jTail]
        exact congrArg
          (fun g ↦
            (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w} g) Fobj t₁)
          hunit
      exact hrewrite₀.trans hrewrite₁
    calc
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ =
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
              (S'.obj (op j₁)) xTail) Fobj t₁ := by
              simpa [ŝ, xTail] using
                congrFun
                  (NatTrans.toPresheafFiber_presheafFiber_app
                    (η := refinementFiber (tail_inclusion j₁) S' (Iso.refl _))
                    (F := Fobj) (X := S'.obj (op j₁)) xTail)
                  t₁
      _ = (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁ := hrewrite
      _ = s := hs₁
  have hŝ' :
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ' = s' := by
    -- The same normalization identifies the second tail generator with `s'`.
    have hrewrite :
        (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
          ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
            (S'.obj (op j₁)) xTail) Fobj t₁' =
        (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
          (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁' := by
      have hrewrite₀ :
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
              (S'.obj (op j₁)) xTail) Fobj t₁' =
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            (fiberMk.{max u v w}
              ((Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app
                (op jTail) ≫ 𝟙 (S'.obj (op j₁)))) Fobj t₁' := by
        simpa only [jTail, xTail] using
          congrArg
            (fun x ↦
              (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁)) x Fobj t₁')
            (refinementFiber_app_fiberMk (j := tail_inclusion j₁) (T := S') (e := Iso.refl _)
              (U := op jTail) (W := S'.obj (op j₁)) (f := 𝟙 (S'.obj (op j₁))))
      have hrewrite₁ :
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w}
                ((Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app
                  (op jTail) ≫ 𝟙 (S'.obj (op j₁)))) Fobj t₁' =
            (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁' := by
        have hunit :
            (Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S')).inv.app (op jTail) ≫
              𝟙 (S'.obj (op j₁)) =
            𝟙 (S'.obj (op j₁)) := by
          simp [jTail]
        exact congrArg
          (fun g ↦
            (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
              (fiberMk.{max u v w} g) Fobj t₁')
          hunit
      exact hrewrite₀.trans hrewrite₁
    calc
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ' =
          (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).app
              (S'.obj (op j₁)) xTail) Fobj t₁' := by
              simpa [ŝ', xTail] using
                congrFun
                  (NatTrans.toPresheafFiber_presheafFiber_app
                    (η := refinementFiber (tail_inclusion j₁) S' (Iso.refl _))
                    (F := Fobj) (X := S'.obj (op j₁)) xTail)
                  t₁'
      _ = (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
            (fiberMk.{max u v w} (𝟙 (S'.obj (op j₁)))) Fobj t₁' := hrewrite
      _ = s' := hs₁'
  have hne : ŝ ≠ ŝ' := by
    -- Distinct images in the original raw fiber force the two canonical tail germs to differ.
    intro hEq
    apply hss'
    have hImage :
        ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ =
          ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ' := by
      simp [hEq]
    exact hŝ.symm.trans (hImage.trans hŝ')
  exact ⟨hŝ, hŝ', hne⟩

/-- Helper for Lemma 7.39.1: the tail index above `j₁` remains directed. -/
private theorem tail_index_isDirected
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] (j₁ : ι) :
    IsDirected (Set.Ici j₁) (· ≤ ·) := by
  refine ⟨?_⟩
  intro a b
  -- Choose a common upper bound in the ambient directed preorder and keep it in the tail.
  obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a.1 b.1
  exact ⟨⟨k, a.2.trans hak⟩, by simpa using hak, by simpa using hbk⟩

/-- Helper for Lemma 7.39.1: on a fixed branch, the pullback second projections are natural with
respect to the tail transition maps. -/
private theorem branch_system_snd_naturality
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index)
    {X Y : (Set.Ici j₁)ᵒᵖ} (g : X ⟶ Y) :
    branch_system_map S j₁ f₁ 𝒰 k g ≫
        (show branch_system_obj S j₁ f₁ 𝒰 k Y ⟶ (tail_system S j₁).obj Y from
          pullback.snd (𝒰.obj k).hom (S.map (homOfLE (unop Y).2).op ≫ f₁)) =
      (show branch_system_obj S j₁ f₁ 𝒰 k X ⟶ (tail_system S j₁).obj X from
        pullback.snd (𝒰.obj k).hom (S.map (homOfLE (unop X).2).op ≫ f₁)) ≫
        (tail_system S j₁).map g := by
  -- The tail-system map is exactly the ambient transition map of `S` along the tail preorder.
  simpa [tail_system, Functor.comp_map] using
    branch_system_map_snd_assoc (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k) (g := g)

/-- Helper for Lemma 7.39.1: on a fixed branch, the pullback second projections define a natural
transformation from the branch system to the ambient tail system. -/
private noncomputable def branch_system_snd_hom
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    branch_system S j₁ f₁ 𝒰 k ⟶ tail_system S j₁ :=
  { app := fun j ↦ pullback.snd (𝒰.obj k).hom (S.map (homOfLE (unop j).2).op ≫ f₁)
    naturality := fun X Y g ↦
      branch_system_snd_naturality (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k) g }

/-- Helper for Lemma 7.39.1: the stagewise restriction from the tail system to a fixed pullback
branch gives a natural transformation on the corresponding section diagrams. -/
private noncomputable def tail_branch_diagram_hom
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (Fobj : Cᵒᵖ ⥤ Type (max u v w)) (k : 𝒰.index) :
    (tail_system S j₁).op ⋙ Fobj ⟶ (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj :=
  -- Route correction: define the branch restriction first on the inverse systems themselves and
  -- then pass to section diagrams by `NatTrans.op` and whiskering with `Fobj`.
  Functor.whiskerRight
    (NatTrans.op (branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k))
    Fobj

/-- Helper for Lemma 7.39.1: each cover branch induces the canonical map from the tail raw
presheaf fiber to the raw presheaf fiber of that branch system. -/
private noncomputable def tail_branch_presheafFiber_map
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (Fobj : Cᵒᵖ ⥤ Type (max u v w)) (k : 𝒰.index) :
    (fiber.{max u v w} (tail_system S j₁)).presheafFiber.obj Fobj ⟶
      (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).presheafFiber.obj Fobj :=
  let _ : Nonempty (Set.Ici j₁) := ⟨⟨j₁, le_rfl⟩⟩
  let _ : IsDirected (Set.Ici j₁) (· ≤ ·) := tail_index_isDirected (j₁ := j₁)
  (inverse_system_presheafFiber_colimitIso (tail_system S j₁) Fobj).inv ≫
    colim.map (tail_branch_diagram_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
      (Fobj := Fobj) k) ≫
    (inverse_system_presheafFiber_colimitIso (branch_system S j₁ f₁ 𝒰 k) Fobj).hom

/-- Helper for Lemma 7.39.1: at the base tail stage `j₁`, the branch map on raw presheaf fibers
normalizes to the canonical branch germ built from the pullback second projection. -/
private theorem tail_branch_presheafFiber_map_base_generator_eq
    [HasPullbacks C] {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (Fobj : Cᵒᵖ ⥤ Type (max u v w)) (k : 𝒰.index)
    (t : Fobj.obj (op (S.obj (op j₁)))) :
    let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
    let xTail : (fiber.{max u v w} (tail_system S j₁)).obj (S.obj (op j₁)) :=
      fiberMk.{max u v w} (U := op jTail) (X := S.obj (op j₁)) (𝟙 (S.obj (op j₁)))
    tail_branch_presheafFiber_map (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k
        ((fiber.{max u v w} (tail_system S j₁)).toPresheafFiber (S.obj (op j₁)) xTail Fobj t) =
      (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber (S.obj (op j₁))
        (fiberMk.{max u v w} (U := op jTail)
          ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
            (op jTail))) Fobj t := by
  let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
  let xTail : (fiber.{max u v w} (tail_system S j₁)).obj (S.obj (op j₁)) :=
    fiberMk.{max u v w} (U := op jTail) (X := S.obj (op j₁)) (𝟙 (S.obj (op j₁)))
  let _ : Nonempty (Set.Ici j₁) := ⟨jTail⟩
  let _ : IsDirected (Set.Ici j₁) (· ≤ ·) := tail_index_isDirected (j₁ := j₁)
  let tailIso := inverse_system_presheafFiber_colimitIso (tail_system S j₁) Fobj
  let branchIso := inverse_system_presheafFiber_colimitIso (branch_system S j₁ f₁ 𝒰 k) Fobj
  let tBranch : Fobj.obj (op ((branch_system S j₁ f₁ 𝒰 k).obj (op jTail))) :=
    Fobj.map
      (((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
        (op jTail))).op t
  let xBranch : (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).obj
      ((branch_system S j₁ f₁ 𝒰 k).obj (op jTail)) :=
    fiberMk.{max u v w} (U := op jTail) (X := (branch_system S j₁ f₁ 𝒰 k).obj (op jTail))
      (𝟙 ((branch_system S j₁ f₁ 𝒰 k).obj (op jTail)))
  have htailHom :
      tailIso.hom (colimit.ι ((tail_system S j₁).op ⋙ Fobj) (op (op jTail)) t) =
        (fiber.{max u v w} (tail_system S j₁)).toPresheafFiber (S.obj (op j₁)) xTail Fobj t := by
    -- The tail colimit generator at `jTail` is the canonical raw fiber generator.
    simpa [tailIso, inverse_system_presheafFiber_colimitIso,
      inverse_system_presheafFiberCocone, jTail, xTail] using
      congrFun
        (colimit.comp_coconePointUniqueUpToIso_hom
          (hc := inverse_system_presheafFiber_isColimit (S := tail_system S j₁) Fobj)
          (op (op jTail)))
        t
  have htailInv :
      tailIso.inv
          ((fiber.{max u v w} (tail_system S j₁)).toPresheafFiber (S.obj (op j₁))
            xTail Fobj t) =
        colimit.ι ((tail_system S j₁).op ⋙ Fobj) (op (op jTail)) t := by
    -- Apply the inverse of the colimit comparison after rewriting by `htailHom`.
    rw [← htailHom]
    simp
  have hmap :
      colim.map (tail_branch_diagram_hom
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k)
          (colimit.ι ((tail_system S j₁).op ⋙ Fobj) (op (op jTail)) t) =
        colimit.ι ((branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj) (op (op jTail))
          (((tail_branch_diagram_hom
            (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k).app
              (op (op jTail))) t) := by
    -- Mapping a colimit generator along the branch diagram hom stays at the same stage.
    simpa using
      congrFun
        (ι_colimMap
          (tail_branch_diagram_hom
            (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k)
          (op (op jTail)))
        t
  have happ :
      ((tail_branch_diagram_hom
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k).app
          (op (op jTail))) t =
        tBranch := by
    -- At the base tail stage the branch restriction is exactly the pullback second projection.
    simp [tBranch, tail_branch_diagram_hom]
  have hbranchHom :
      branchIso.hom
          (colimit.ι ((branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj) (op (op jTail)) tBranch) =
        (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber
          ((branch_system S j₁ f₁ 𝒰 k).obj (op jTail)) xBranch Fobj tBranch := by
    -- The branch colimit generator at `jTail` is the identity germ on the pullback object.
    simpa [branchIso, inverse_system_presheafFiber_colimitIso,
      inverse_system_presheafFiberCocone, jTail, xBranch, tBranch] using
      congrFun
        (colimit.comp_coconePointUniqueUpToIso_hom
          (hc := inverse_system_presheafFiber_isColimit
            (S := branch_system S j₁ f₁ 𝒰 k) Fobj)
          (op (op jTail)))
        tBranch
  have hbranchRewrite :
      (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber
          ((branch_system S j₁ f₁ 𝒰 k).obj (op jTail)) xBranch Fobj tBranch =
        (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber (S.obj (op j₁))
          (fiberMk.{max u v w} (U := op jTail)
            ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
              (op jTail))) Fobj t := by
    -- Move the identity germ on the pullback object along `pullback.snd`.
    have hrewrite₀ :
        (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber
            ((branch_system S j₁ f₁ 𝒰 k).obj (op jTail)) xBranch Fobj tBranch =
          (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber
            (S.obj (op ((tail_inclusion j₁) jTail)))
            ((fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).map
              ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
                (op jTail))
              xBranch) Fobj t := by
      simpa [tBranch] using
        congrFun
          ((fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber_w
            (F := Fobj)
            ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
              (op jTail))
            xBranch)
          t
    have hrewrite₁ :
        ((fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).map
          ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
            (op jTail))
          xBranch) =
          fiberMk.{max u v w} (U := op jTail)
            ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
              (op jTail)) := by
      simpa [xBranch]
    rw [hrewrite₁] at hrewrite₀
    simpa [jTail] using hrewrite₀
  -- Evaluate the composite definition of `tail_branch_presheafFiber_map` on the base generator
  -- and then normalize the resulting branch germ.
  calc
    tail_branch_presheafFiber_map (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k
        ((fiber.{max u v w} (tail_system S j₁)).toPresheafFiber (S.obj (op j₁))
          xTail Fobj t) =
      branchIso.hom
        (colim.map (tail_branch_diagram_hom
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k)
          (tailIso.inv
            ((fiber.{max u v w} (tail_system S j₁)).toPresheafFiber (S.obj (op j₁))
              xTail Fobj t))) := by
          rfl
    _ =
      branchIso.hom
        (colim.map (tail_branch_diagram_hom
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k)
          (colimit.ι ((tail_system S j₁).op ⋙ Fobj) (op (op jTail)) t)) := by
            rw [htailInv]
    _ =
      branchIso.hom
        (colimit.ι ((branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj) (op (op jTail))
          (((tail_branch_diagram_hom
            (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k).app
              (op (op jTail))) t)) := by
            rw [hmap]
    _ =
      branchIso.hom
        (colimit.ι ((branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj) (op (op jTail))
          tBranch) := by
            rw [happ]
    _ =
      (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber
        ((branch_system S j₁ f₁ 𝒰 k).obj (op jTail)) xBranch Fobj tBranch := hbranchHom
    _ =
      (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber (S.obj (op j₁))
        (fiberMk.{max u v w} (U := op jTail)
          ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
            (op jTail))) Fobj t :=
          hbranchRewrite

/-- Helper for Lemma 7.39.1: the source proof's finite-product map from the tail raw presheaf
fiber to the tuple of all branch raw presheaf fibers. -/
private noncomputable def tail_branch_product_map
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (Fobj : Cᵒᵖ ⥤ Type (max u v w)) :
    (fiber.{max u v w} (tail_system S j₁)).presheafFiber.obj Fobj →
      ∀ k : 𝒰.index, (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).presheafFiber.obj Fobj :=
  fun x k ↦ tail_branch_presheafFiber_map (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k x

/-- Helper for Lemma 7.39.1: the branch restriction maps assemble into the source proof's
stagewise map from the tail section diagram to the product of the branch section diagrams. -/
private noncomputable def tail_branch_product_diagram_hom
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (Fobj : Cᵒᵖ ⥤ Type (max u v w)) :
    (tail_system S j₁).op ⋙ Fobj ⟶
      ∏ᶜ fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj :=
  -- Route correction: the product lives in the functor category over the fixed tail index,
  -- matching the source proof's single filtered colimit of the stagewise product diagram.
  Pi.lift fun k =>
    tail_branch_diagram_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k

/-- Helper for Lemma 7.39.1: after passing to colimits and then to the finite product of branch
colimits, projecting to coordinate `k` recovers the colimit map of the `k`-th branch diagram. -/
private theorem tail_branch_product_functor_projection
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    [Finite 𝒰.index] (Fobj : Cᵒᵖ ⥤ Type (max u v w)) [Fintype 𝒰.index]
    [PreservesLimit
      (Discrete.functor (fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj))
      (colim : (((Set.Ici j₁)ᵒᵖᵒᵖ ⥤ Type (max u v w)) ⥤ Type (max u v w)))]
    (k : 𝒰.index) :
    colim.map (tail_branch_product_diagram_hom
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj)) ≫
      (PreservesProduct.iso
        (colim : (((Set.Ici j₁)ᵒᵖᵒᵖ ⥤ Type (max u v w)) ⥤ Type (max u v w)))
        (fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj)).hom ≫
      Pi.π (fun k : 𝒰.index =>
        colimit ((branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj)) k =
    colim.map (tail_branch_diagram_hom
      (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k) := by
  -- Project the finite-product comparison to coordinate `k` and then collapse the lifted
  -- branch tuple back to the `k`-th branch restriction map.
  let hπ :
      (PreservesProduct.iso
        (colim : (((Set.Ici j₁)ᵒᵖᵒᵖ ⥤ Type (max u v w)) ⥤ Type (max u v w)))
        (fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj)).hom ≫
        Pi.π (fun k : 𝒰.index =>
          colimit ((branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj)) k =
      colim.map
        (Pi.π (fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj) k) := by
    simpa [PreservesProduct.iso_hom] using
      (piComparison_comp_π
        (G := (colim : (((Set.Ici j₁)ᵒᵖᵒᵖ ⥤ Type (max u v w)) ⥤ Type (max u v w))))
        (f := fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj)
        k)
  calc
    colim.map (tail_branch_product_diagram_hom
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj)) ≫
        (PreservesProduct.iso
          (colim : (((Set.Ici j₁)ᵒᵖᵒᵖ ⥤ Type (max u v w)) ⥤ Type (max u v w)))
          (fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj)).hom ≫
        Pi.π (fun k : 𝒰.index =>
          colimit ((branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj)) k
        =
      colim.map (tail_branch_product_diagram_hom
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj)) ≫
        colim.map
          (Pi.π (fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj) k) := by
            simpa [Category.assoc] using
              congrArg
                (fun m ↦
                  colim.map (tail_branch_product_diagram_hom
                    (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj)) ≫ m)
                hπ
    _ =
      colim.map
        (tail_branch_product_diagram_hom
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) ≫
          Pi.π (fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj) k) := by
            rw [← Functor.map_comp]
    _ =
      colim.map (tail_branch_diagram_hom
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k) := by
            congr 1
            simpa [tail_branch_product_diagram_hom] using
              (Pi.lift_π
                (p := fun k : 𝒰.index =>
                  tail_branch_diagram_hom
                    (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k)
                k)

/-- Helper for Lemma 7.39.1: at a fixed tail stage, projecting the product-valued branch map to
coordinate `k` gives the explicit restriction map along the pullback second projection. -/
private theorem tail_branch_product_projection_app_eq_stage_restriction
    [HasPullbacks C] {ι : Type w} [Preorder ι] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (Fobj : Cᵒᵖ ⥤ Type (max u v w)) (j : (Set.Ici j₁)ᵒᵖᵒᵖ) (k : 𝒰.index) :
    ((Pi.π (fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj) k).app j) ∘
        ((tail_branch_product_diagram_hom
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj)).app j) =
      fun t ↦
        Fobj.map
          (pullback.snd (𝒰.obj k).hom
            (S.map (homOfLE (unop (unop j)).2).op ≫ f₁)).op t := by
  -- First project the lifted tuple to the chosen branch coordinate.
  ext t
  have hπ :
      ((Pi.π (fun k : 𝒰.index => (branch_system S j₁ f₁ 𝒰 k).op ⋙ Fobj) k).app j)
          (((tail_branch_product_diagram_hom
            (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj)).app j) t) =
        ((tail_branch_diagram_hom
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k).app j) t := by
    simpa [CategoryTheory.types_comp_apply, tail_branch_product_diagram_hom] using
      congrFun
        (congrArg (fun η ↦ η.app j)
          (Pi.lift_π
            (p := fun k : 𝒰.index =>
              tail_branch_diagram_hom
                (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k)
            k))
        t
  -- Then unfold the remaining branch coordinate to the literal pullback restriction.
  simpa [tail_branch_diagram_hom, branch_system_snd_hom] using hπ

/-- Helper for Lemma 7.39.1: at each tail stage, the branch-product restriction map is injective
because the pulled-back finite cover is separating for sheaf sections. -/
private theorem tail_branch_stage_product_injective
    [HasPullbacks C] {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (h𝒰 : 𝒰.toSieve ∈ J W) (ℱ : Sheaf J (Type (max u v w)))
    (j : (Set.Ici j₁)ᵒᵖᵒᵖ) :
    Function.Injective
      ((tail_branch_product_diagram_hom
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
          (Fobj := (sheafToPresheaf J (Type (max u v w))).obj ℱ)).app j) := by
  -- Project each coordinate to the explicit pullback restriction map at the chosen tail stage and
  -- invoke the sheaf separatedness statement for that pulled-back finite cover.
  intro s t hst
  apply stage_pullback_cover_restriction_injective (J := J) (𝒰 := 𝒰) h𝒰 ℱ
    (S.map (homOfLE (unop (unop j)).2).op ≫ f₁)
  funext k
  let πk :
      ((∏ᶜ fun k : 𝒰.index =>
          (branch_system S j₁ f₁ 𝒰 k).op ⋙
            (sheafToPresheaf J (Type (max u v w))).obj ℱ).obj j) →
        (((branch_system S j₁ f₁ 𝒰 k).op ⋙
          (sheafToPresheaf J (Type (max u v w))).obj ℱ).obj j) :=
    ((Pi.π (fun k : 𝒰.index =>
      (branch_system S j₁ f₁ 𝒰 k).op ⋙
        (sheafToPresheaf J (Type (max u v w))).obj ℱ) k).app j)
  have hk :
      πk
          ((tail_branch_product_diagram_hom
            (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
            (Fobj := (sheafToPresheaf J (Type (max u v w))).obj ℱ)).app j s) =
        πk
          ((tail_branch_product_diagram_hom
            (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
            (Fobj := (sheafToPresheaf J (Type (max u v w))).obj ℱ)).app j t) := by
    exact congrArg πk hst
  have hsProj :
      πk
          ((tail_branch_product_diagram_hom
            (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
            (Fobj := (sheafToPresheaf J (Type (max u v w))).obj ℱ)).app j s) =
        ℱ.obj.map
          (pullback.snd (𝒰.obj k).hom
            (S.map (homOfLE (unop (unop j)).2).op ≫ f₁)).op s := by
    simpa [CategoryTheory.types_comp_apply] using
      congrFun
        (tail_branch_product_projection_app_eq_stage_restriction
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
          (Fobj := (sheafToPresheaf J (Type (max u v w))).obj ℱ) (j := j) (k := k))
        s
  have htProj :
      πk
          ((tail_branch_product_diagram_hom
            (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
            (Fobj := (sheafToPresheaf J (Type (max u v w))).obj ℱ)).app j t) =
        ℱ.obj.map
          (pullback.snd (𝒰.obj k).hom
            (S.map (homOfLE (unop (unop j)).2).op ≫ f₁)).op t := by
    simpa [CategoryTheory.types_comp_apply] using
      congrFun
        (tail_branch_product_projection_app_eq_stage_restriction
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
          (Fobj := (sheafToPresheaf J (Type (max u v w))).obj ℱ) (j := j) (k := k))
        t
  exact hsProj.symm.trans (hk.trans htProj)

/-- Helper for Lemma 7.39.1: equality in one branch raw presheaf fiber can be canceled back to
the corresponding equality on the branch colimit before the raw-fiber comparison isomorphism. -/
private theorem tail_branch_raw_eq_implies_branch_colimit_eq
    [HasPullbacks C] {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    [Nonempty (Set.Ici j₁)] [IsDirected (Set.Ici j₁) (· ≤ ·)]
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (Fobj : Cᵒᵖ ⥤ Type (max u v w)) (k : 𝒰.index)
    {x y : (fiber.{max u v w} (tail_system S j₁)).presheafFiber.obj Fobj}
    (hxy :
      tail_branch_presheafFiber_map (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k x =
        tail_branch_presheafFiber_map (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k y) :
    colim.map
        (tail_branch_diagram_hom
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k)
        ((inverse_system_presheafFiber_colimitIso (tail_system S j₁) Fobj).inv x) =
    colim.map
        (tail_branch_diagram_hom
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) k)
        ((inverse_system_presheafFiber_colimitIso (tail_system S j₁) Fobj).inv y) := by
  let tailIso := inverse_system_presheafFiber_colimitIso (tail_system S j₁) Fobj
  let branchIso := inverse_system_presheafFiber_colimitIso (branch_system S j₁ f₁ 𝒰 k) Fobj
  have hxy' : branchIso.inv
      (tail_branch_presheafFiber_map
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k x) =
    branchIso.inv
      (tail_branch_presheafFiber_map
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k y) := by
    exact congrArg branchIso.inv hxy
  -- Cancel the branch colimit comparison isomorphism on the chosen coordinate.
  simpa [tail_branch_presheafFiber_map, tailIso, branchIso] using hxy'

/-- Helper for Lemma 7.39.1: the source-proof map from the tail raw presheaf fiber to the product
of the branch raw presheaf fibers is injective for sheaf sections. -/
private theorem tail_branch_product_map_injective
    [HasPullbacks C] {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    [Finite 𝒰.index] (h𝒰 : 𝒰.toSieve ∈ J W) (ℱ : Sheaf J (Type (max u v w))) :
    Function.Injective
      (tail_branch_product_map (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
        ((sheafToPresheaf J (Type (max u v w))).obj ℱ)) := by
  -- Route correction: the remaining gap is no longer the coordinatewise branch cancellation. The
  -- helper `tail_branch_raw_eq_implies_branch_colimit_eq` now isolates that step, so the only
  -- missing source-proof ingredient is the finite-product comparison
  -- `colimit (j ↦ ∀ k, F(V_{j,k})) ≅ ∀ k, colimit (j ↦ F(V_{j,k}))` from Lemma 4.19.2, packaged in
  -- a universe-stable form that matches `tail_branch_product_map`.
  let _ : Nonempty (Set.Ici j₁) := ⟨⟨j₁, le_rfl⟩⟩
  let _ : IsDirected (Set.Ici j₁) (· ≤ ·) := tail_index_isDirected (j₁ := j₁)
  let Fobj : Cᵒᵖ ⥤ Type (max u v w) := (sheafToPresheaf J (Type (max u v w))).obj ℱ
  let tailIso := inverse_system_presheafFiber_colimitIso (tail_system S j₁) Fobj
  letI : Fintype 𝒰.index := Fintype.ofFinite 𝒰.index
  let e : Fin (Fintype.card 𝒰.index) ≃ 𝒰.index := (Fintype.equivFin 𝒰.index).symm
  let family :
      Fin (Fintype.card 𝒰.index) → (Set.Ici j₁)ᵒᵖᵒᵖ ⥤ Type (max u v w) :=
    fun n => (branch_system S j₁ f₁ 𝒰 (e n)).op ⋙ Fobj
  let θ :
      (tail_system S j₁).op ⋙ Fobj ⟶ ∏ᶜ family :=
    Pi.lift fun n =>
      tail_branch_diagram_hom
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n)
  let productIso := PreservesProduct.iso
    (colim : (((Set.Ici j₁)ᵒᵖᵒᵖ ⥤ Type (max u v w)) ⥤ Type (max u v w)))
    family
  let tupleIso :
      colimit (∏ᶜ family) ≅
        ∀ n : Fin (Fintype.card 𝒰.index), colimit (family n) :=
    productIso ≪≫ Types.productIso (fun n => colimit (family n))
  have htupleIso_injective : Function.Injective tupleIso.hom :=
    (ConcreteCategory.bijective_of_isIso tupleIso.hom).1
  have hθ_app_injective :
      ∀ j : (Set.Ici j₁)ᵒᵖᵒᵖ, Function.Injective (θ.app j) := by
    intro j s t hst
    -- Reindex the tuple equality back along `e : Fin n ≃ 𝒰.index`, then invoke separatedness
    -- for the pulled-back cover at the tail stage `j`.
    apply stage_pullback_cover_restriction_injective (J := J) (𝒰 := 𝒰) h𝒰 ℱ
      (S.map (homOfLE (unop (unop j)).2).op ≫ f₁)
    funext k
    let n : Fin (Fintype.card 𝒰.index) := e.symm k
    let πn :
        ((∏ᶜ family).obj j) → ((family n).obj j) :=
      (Pi.π family n).app j
    have hkEq : e n = k := by
      simp [n]
    have hπeq :
        ((tail_branch_diagram_hom
            (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n)).app j) s =
          ((tail_branch_diagram_hom
            (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n)).app j) t := by
      have hn :
          πn ((θ.app j) s) = πn ((θ.app j) t) := by
        exact congrArg πn hst
      have hsπ :
          πn ((θ.app j) s) =
            ((tail_branch_diagram_hom
              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n)).app j) s := by
        simpa [πn, θ, CategoryTheory.types_comp_apply] using
          congrFun
            (congrArg (fun η ↦ η.app j)
              (Pi.lift_π
                (p := fun n =>
                  tail_branch_diagram_hom
                    (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n))
                n))
            s
      have htπ :
          πn ((θ.app j) t) =
            ((tail_branch_diagram_hom
              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n)).app j) t := by
        simpa [πn, θ, CategoryTheory.types_comp_apply] using
          congrFun
            (congrArg (fun η ↦ η.app j)
              (Pi.lift_π
                (p := fun n =>
                  tail_branch_diagram_hom
                    (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n))
                n))
            t
      exact hsπ.symm.trans (hn.trans htπ)
    rw [hkEq] at hπeq
    simpa [Fobj, tail_branch_diagram_hom, branch_system_snd_hom] using hπeq
  have htailMap_injective : Function.Injective (colim.map θ) := by
    -- This is exactly the source-proof stagewise injectivity step on the pulled-back finite cover.
    letI : Mono θ :=
      (NatTrans.mono_iff_mono_app θ).2 fun j ↦ (mono_iff_injective _).2 (hθ_app_injective j)
    exact (mono_iff_injective _).1 (colim.map_mono θ)
  intro x y hxy
  have hcoord :
      ∀ n : Fin (Fintype.card 𝒰.index),
        colim.map
            (tail_branch_diagram_hom
              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n))
            (tailIso.inv x) =
          colim.map
            (tail_branch_diagram_hom
              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n))
            (tailIso.inv y) := by
    intro n
    -- Each product coordinate is the chosen branch raw-fiber map.
    exact
      tail_branch_raw_eq_implies_branch_colimit_eq
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (k := e n)
        (hxy := congrFun hxy (e n))
  have hproduct_hom :
      tupleIso.hom (colim.map θ (tailIso.inv x)) =
        tupleIso.hom (colim.map θ (tailIso.inv y)) := by
    -- Compare the product images coordinatewise after the finite-product comparison isomorphism.
    funext n
    have hxproj :
        (tupleIso.hom (colim.map θ (tailIso.inv x))) n =
          colim.map
            (tail_branch_diagram_hom
              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n))
            (tailIso.inv x) := by
      have hπ :
          tupleIso.hom ≫ (fun f ↦ f n) =
            colim.map (Pi.π family n) := by
        have hπ0 :
            tupleIso.hom ≫ (fun f ↦ f n) =
              productIso.hom ≫ Pi.π (fun n => colimit (family n)) n := by
          simp [tupleIso, Category.assoc, Types.productIso_hom_comp_eval]
        exact hπ0.trans <| by
          simpa [PreservesProduct.iso_hom] using
            (piComparison_comp_π
              (G := (colim :
                (((Set.Ici j₁)ᵒᵖᵒᵖ ⥤ Type (max u v w)) ⥤ Type (max u v w))))
              (f := family) n)
      have hπx := congrFun hπ (colim.map θ (tailIso.inv x))
      have hmapcomp :
          colim.map (Pi.π family n) (colim.map θ (tailIso.inv x)) =
            colim.map (θ ≫ Pi.π family n) (tailIso.inv x) := by
        have hcomp :
            colim.map θ ≫ colim.map (Pi.π family n) =
              colim.map (θ ≫ Pi.π family n) := by
          rw [← Functor.map_comp]
        simpa [CategoryTheory.types_comp_apply] using congrFun hcomp (tailIso.inv x)
      have hθπ :
          θ ≫ Pi.π family n =
            tail_branch_diagram_hom
              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n) := by
        simpa [θ] using
          (Pi.lift_π
            (p := fun n =>
              tail_branch_diagram_hom
                (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n))
            n)
      calc
        (tupleIso.hom (colim.map θ (tailIso.inv x))) n =
          colim.map (Pi.π family n) (colim.map θ (tailIso.inv x)) := by
            simpa [CategoryTheory.types_comp_apply] using hπx
        _ = colim.map (θ ≫ Pi.π family n) (tailIso.inv x) := hmapcomp
        _ = colim.map
              (tail_branch_diagram_hom
                (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n))
              (tailIso.inv x) := by rw [hθπ]
    have hyproj :
        (tupleIso.hom (colim.map θ (tailIso.inv y))) n =
          colim.map
            (tail_branch_diagram_hom
              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n))
            (tailIso.inv y) := by
      have hπ :
          tupleIso.hom ≫ (fun f ↦ f n) =
            colim.map (Pi.π family n) := by
        have hπ0 :
            tupleIso.hom ≫ (fun f ↦ f n) =
              productIso.hom ≫ Pi.π (fun n => colimit (family n)) n := by
          simp [tupleIso, Category.assoc, Types.productIso_hom_comp_eval]
        exact hπ0.trans <| by
          simpa [PreservesProduct.iso_hom] using
            (piComparison_comp_π
              (G := (colim :
                (((Set.Ici j₁)ᵒᵖᵒᵖ ⥤ Type (max u v w)) ⥤ Type (max u v w))))
              (f := family) n)
      have hπy := congrFun hπ (colim.map θ (tailIso.inv y))
      have hmapcomp :
          colim.map (Pi.π family n) (colim.map θ (tailIso.inv y)) =
            colim.map (θ ≫ Pi.π family n) (tailIso.inv y) := by
        have hcomp :
            colim.map θ ≫ colim.map (Pi.π family n) =
              colim.map (θ ≫ Pi.π family n) := by
          rw [← Functor.map_comp]
        simpa [CategoryTheory.types_comp_apply] using congrFun hcomp (tailIso.inv y)
      have hθπ :
          θ ≫ Pi.π family n =
            tail_branch_diagram_hom
              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n) := by
        simpa [θ] using
          (Pi.lift_π
            (p := fun n =>
              tail_branch_diagram_hom
                (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n))
            n)
      calc
        (tupleIso.hom (colim.map θ (tailIso.inv y))) n =
          colim.map (Pi.π family n) (colim.map θ (tailIso.inv y)) := by
            simpa [CategoryTheory.types_comp_apply] using hπy
        _ = colim.map (θ ≫ Pi.π family n) (tailIso.inv y) := hmapcomp
        _ = colim.map
              (tail_branch_diagram_hom
                (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (e n))
              (tailIso.inv y) := by rw [hθπ]
    exact hxproj.trans ((hcoord n).trans hyproj.symm)
  have hproduct : colim.map θ (tailIso.inv x) = colim.map θ (tailIso.inv y) := by
    -- Cancel the product comparison isomorphism to return to the colimit of the tuple diagram.
    exact htupleIso_injective hproduct_hom
  have htail : tailIso.inv x = tailIso.inv y := htailMap_injective hproduct
  -- Finally cancel the tail raw-fiber comparison isomorphism.
  simpa using congrArg tailIso.hom htail

/-- Helper for Lemma 7.39.1: once the source-proof product map is injective, two distinct tail
germs differ on at least one branch coordinate. -/
private theorem exists_branch_raw_ne_of_tail_ne
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    [Finite 𝒰.index]
    (Fobj : Cᵒᵖ ⥤ Type (max u v w))
    {x y : (fiber.{max u v w} (tail_system S j₁)).presheafFiber.obj Fobj}
    (hxy : x ≠ y)
    (hinj : Function.Injective (tail_branch_product_map
      (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj)) :
    ∃ k : 𝒰.index,
      tail_branch_presheafFiber_map (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k x ≠
        tail_branch_presheafFiber_map (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k y := by
  -- Apply the general finite-product separation lemma to the source-proof product map.
  simpa [tail_branch_product_map] using
    exists_ne_coordinate_of_injective_map
      (g := tail_branch_product_map (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj)
      hxy hinj

/-- Helper for Lemma 7.39.1: the right base stage of the glued refinement is the chosen pullback
object. -/
private theorem glued_refinement_right_base_obj
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    (glued_refinement_system S j₁ f₁ 𝒰 k).obj
        (op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁)) =
      pullback (𝒰.obj k).hom f₁ := by
  -- The right summand of the glued system is definitionally the branch pullback system.
  simp [glued_refinement_system, glued_refinement_system_obj, branch_system_obj]

/-- Helper for Lemma 7.39.1: the left stage `j0` of the glued refinement is the original stage
`S.obj (op j0)`. -/
private theorem glued_refinement_left_stage_obj
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C) (j₁ j0 : ι)
    {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    (glued_refinement_system S j₁ f₁ 𝒰 k).obj
        (op (⟨Sum.inl j0⟩ : glued_refinement_index j₁)) =
      S.obj (op j0) := by
  -- The left summand of the glued system is definitionally the original inverse system.
  simp [glued_refinement_system, glued_refinement_system_obj]

/-- Helper for Lemma 7.39.1: every left stage `j0 ≤ j₁` lies below the glued right base stage. -/
private theorem glued_refinement_left_stage_le_right_base
    {ι : Type w} [Preorder ι] {j0 j₁ : ι} (hj₀ : j0 ≤ j₁) :
    (⟨Sum.inl j0⟩ : glued_refinement_index j₁) ≤ ⟨Sum.inr ⟨j₁, le_rfl⟩⟩ := by
  -- This is exactly the mixed left-to-right clause in the glued refinement preorder.
  simpa using hj₀

/-- Helper for Lemma 7.39.1: the canonical morphism from the glued right base stage to the left
stage `j0`. -/
private def glued_refinement_right_base_to_left_hom
    {ι : Type w} [Preorder ι] {j0 j₁ : ι} (hj₀ : j0 ≤ j₁) :
    op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁) ⟶
      op (⟨Sum.inl j0⟩ : glued_refinement_index j₁) :=
  (homOfLE (glued_refinement_left_stage_le_right_base (j0 := j0) (j₁ := j₁) hj₀)).op

/-- Helper for Lemma 7.39.1: the mixed morphism from the glued right base stage to the left stage
`j0` remembers exactly the source inequality `hj₀`. -/
private theorem glued_refinement_right_base_to_left_hom_le
    {ι : Type w} [Preorder ι] {j0 j₁ : ι} (hj₀ : j0 ≤ j₁) :
    leOfHom (glued_refinement_right_base_to_left_hom (j0 := j0) (j₁ := j₁) hj₀).unop = hj₀ := by
  -- The mixed glued morphism is literally the opposite of `homOfLE hj₀`.
  apply Subsingleton.elim

/-- Helper for Lemma 7.39.1: after identifying the glued right base with the chosen pullback
object, the pullback point still lands over the original stage morphism to `W`. -/
private theorem glued_refinement_right_base_fst_comp_cover
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C)
    {j0 j₁ : ι} (hj₀ : j0 ≤ j₁) {W : C} (f₀ : S.obj (op j0) ⟶ W)
    (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    let rightBase : (glued_refinement_index j₁)ᵒᵖ :=
      op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁)
    let hRightObj :
        (glued_refinement_system S j₁ (S.map (homOfLE hj₀).op ≫ f₀) 𝒰 k).obj rightBase =
          pullback (𝒰.obj k).hom (S.map (homOfLE hj₀).op ≫ f₀) :=
      by
        simpa [rightBase] using
          (glued_refinement_right_base_obj
            (S := S) (j₁ := j₁) (f₁ := S.map (homOfLE hj₀).op ≫ f₀) (𝒰 := 𝒰) (k := k))
    eqToHom hRightObj ≫ pullback.fst (𝒰.obj k).hom (S.map (homOfLE hj₀).op ≫ f₀) ≫
        (𝒰.obj k).hom =
      eqToHom hRightObj ≫ pullback.snd (𝒰.obj k).hom (S.map (homOfLE hj₀).op ≫ f₀) ≫
        (S.map (homOfLE hj₀).op ≫ f₀) := by
  dsimp
  let rightBase : (glued_refinement_index j₁)ᵒᵖ :=
    op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁)
  have hRightObj :
      (glued_refinement_system S j₁ (S.map (homOfLE hj₀).op ≫ f₀) 𝒰 k).obj rightBase =
        pullback (𝒰.obj k).hom (S.map (homOfLE hj₀).op ≫ f₀) := by
    simpa [rightBase] using
      (glued_refinement_right_base_obj
        (S := S) (j₁ := j₁) (f₁ := S.map (homOfLE hj₀).op ≫ f₀) (𝒰 := 𝒰) (k := k))
  -- This is the pullback compatibility relation, transported across the right-base object
  -- identification used in the glued refinement.
  simpa [rightBase, Category.assoc] using
    congrArg
      (fun m ↦ eqToHom hRightObj ≫ m)
      (show
        pullback.fst (𝒰.obj k).hom (S.map (homOfLE hj₀).op ≫ f₀) ≫ (𝒰.obj k).hom =
          pullback.snd (𝒰.obj k).hom (S.map (homOfLE hj₀).op ≫ f₀) ≫
            (S.map (homOfLE hj₀).op ≫ f₀) from
          pullback.condition)

/-- Helper for Lemma 7.39.1: at the definitional glued right-base pullback object, the cover map
already factors through the original stage map to `W`. -/
private theorem glued_refinement_right_base_cover_factorization
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C)
    {j0 j₁ : ι} (hj₀ : j0 ≤ j₁) {W : C} (f₀ : S.obj (op j0) ⟶ W)
    (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    let f₁ : S.obj (op j₁) ⟶ W := S.map (homOfLE hj₀).op ≫ f₀
    let rightBase : (glued_refinement_index j₁)ᵒᵖ :=
      op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁)
    let T := glued_refinement_system S j₁ f₁ 𝒰 k
    let rightBaseHom : T.obj rightBase ⟶ (𝒰.obj k).left :=
      pullback.fst (𝒰.obj k).hom (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁)
    rightBaseHom ≫ (𝒰.obj k).hom =
      T.map (glued_refinement_right_base_to_left_hom (j0 := j0) (j₁ := j₁) hj₀) ≫ f₀ := by
  let f₁ : S.obj (op j₁) ⟶ W := S.map (homOfLE hj₀).op ≫ f₀
  let rightBase : (glued_refinement_index j₁)ᵒᵖ :=
    op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁)
  let T := glued_refinement_system S j₁ f₁ 𝒰 k
  let rightBaseHom : T.obj rightBase ⟶ (𝒰.obj k).left :=
    pullback.fst (𝒰.obj k).hom (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁)
  -- Route correction: use the definitional right-base pullback object, so the cover
  -- factorization is exactly the pullback condition plus the mixed-map formula.
  dsimp [rightBaseHom, T, f₁, rightBase]
  have hpullback :
      pullback.fst (𝒰.obj k).hom
          (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫
            (S.map (homOfLE hj₀).op ≫ f₀)) ≫
            (𝒰.obj k).hom =
        pullback.snd (𝒰.obj k).hom
          (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫
            (S.map (homOfLE hj₀).op ≫ f₀)) ≫
            S.map (homOfLE hj₀).op ≫ f₀ := by
    calc
      pullback.fst (𝒰.obj k).hom
          (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫
            (S.map (homOfLE hj₀).op ≫ f₀)) ≫
            (𝒰.obj k).hom =
        pullback.snd (𝒰.obj k).hom
          (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫
            (S.map (homOfLE hj₀).op ≫ f₀)) ≫
            (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫
              (S.map (homOfLE hj₀).op ≫ f₀)) := by
              simpa using
                (pullback.condition
                  (f := (𝒰.obj k).hom)
                  (g := S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫
                    (S.map (homOfLE hj₀).op ≫ f₀)))
      _ =
        pullback.snd (𝒰.obj k).hom
          (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫
            (S.map (homOfLE hj₀).op ≫ f₀)) ≫
            S.map (homOfLE hj₀).op ≫ f₀ := by
              simp [Category.assoc]
  have hmap :
      pullback.snd (𝒰.obj k).hom
          (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫
            (S.map (homOfLE hj₀).op ≫ f₀)) ≫
            S.map (homOfLE hj₀).op ≫ f₀ =
        T.map (glued_refinement_right_base_to_left_hom (j0 := j0) (j₁ := j₁) hj₀) ≫ f₀ := by
    change pullback.snd (𝒰.obj k).hom
        (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫
          (S.map (homOfLE hj₀).op ≫ f₀)) ≫
          S.map (homOfLE hj₀).op ≫ f₀ =
      (pullback.snd (𝒰.obj k).hom
        (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁) ≫
          S.map (show op j₁ ⟶ op j0 from (homOfLE hj₀).op)) ≫ f₀
    simpa [f₁, Category.assoc]
  exact hpullback.trans hmap

/-- Helper for Lemma 7.39.1: after identifying the left summand of the glued refinement with the
original stage `j0`, the morphism used in the refinement witness is literally `f₀`. -/
private theorem glued_refinement_left_stage_map_eq
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C)
    {j0 j₁ : ι} (hj₀ : j0 ≤ j₁) {W : C} (f₀ : S.obj (op j0) ⟶ W)
    (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    let f₁ : S.obj (op j₁) ⟶ W := S.map (homOfLE hj₀).op ≫ f₀
    let T := glued_refinement_system S j₁ f₁ 𝒰 k
    let j : ι ↪o glued_refinement_index j₁ := glued_refinement_inclusion j₁
    let e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T := glued_refinement_iso S j₁ f₁ 𝒰 k
    let leftStageMap : T.obj (op (j j0)) ⟶ W := e.inv.app (op j0) ≫ f₀
    leftStageMap = f₀ := by
  let f₁ : S.obj (op j₁) ⟶ W := S.map (homOfLE hj₀).op ≫ f₀
  let T := glued_refinement_system S j₁ f₁ 𝒰 k
  let j : ι ↪o glued_refinement_index j₁ := glued_refinement_inclusion j₁
  let e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T := glued_refinement_iso S j₁ f₁ 𝒰 k
  let leftStageMap : T.obj (op (j j0)) ⟶ W := e.inv.app (op j0) ≫ f₀
  -- On the left summand, the inverse component of the glued refinement is the identity.
  dsimp [leftStageMap]
  rw [glued_refinement_iso_inv_app_eq_id
    (S := S) (j₁ := j₁) (j0 := j0) (f₁ := f₁) (𝒰 := 𝒰) (k := k)]
  exact Category.id_comp f₀

/-- Helper for Lemma 7.39.1: once a branch `k` is chosen, the canonical pullback point on the
right summand of the glued refinement maps to the refined image of the original generator. -/
private theorem glued_refinement_right_base_generator_eq_refinement_image
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C)
    {j0 j₁ : ι} (hj₀ : j0 ≤ j₁) {W : C} (f₀ : S.obj (op j0) ⟶ W)
    (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    let f₁ : S.obj (op j₁) ⟶ W := S.map (homOfLE hj₀).op ≫ f₀
    let T := glued_refinement_system S j₁ f₁ 𝒰 k
    let j : ι ↪o glued_refinement_index j₁ := glued_refinement_inclusion j₁
    let e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T := glued_refinement_iso S j₁ f₁ 𝒰 k
    let rightBaseHom :
        T.obj (op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁)) ⟶ (𝒰.obj k).left :=
      pullback.fst (𝒰.obj k).hom
        (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁)
    ((fiber.{max u v w} T).map (𝒰.obj k).hom) (fiberMk.{max u v w} rightBaseHom) =
      (refinementFiber j T e).app W (show (fiber.{max u v w} S).obj W from
        fiberMk.{max u v w} f₀) := by
  let f₁ : S.obj (op j₁) ⟶ W := S.map (homOfLE hj₀).op ≫ f₀
  let T := glued_refinement_system S j₁ f₁ 𝒰 k
  let j : ι ↪o glued_refinement_index j₁ := glued_refinement_inclusion j₁
  let e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T := glued_refinement_iso S j₁ f₁ 𝒰 k
  let rightBaseToLeft :=
    glued_refinement_right_base_to_left_hom (j0 := j0) (j₁ := j₁) hj₀
  let leftStageMap : T.obj (op (j j0)) ⟶ W := e.inv.app (op j0) ≫ f₀
  let rightBaseHom :
      T.obj (op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁)) ⟶ (𝒰.obj k).left :=
    pullback.fst (𝒰.obj k).hom
      (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁)
  have hleftStageMap : leftStageMap = f₀ := by
    -- On the left summand, the refinement identification contributes only the identity.
    simpa [leftStageMap, f₁, T, j, e] using
      glued_refinement_left_stage_map_eq
        (S := S) (hj₀ := hj₀) (f₀ := f₀) (𝒰 := 𝒰) (k := k)
  have hmap :
      ((fiber.{max u v w} T).map (𝒰.obj k).hom) (fiberMk.{max u v w} rightBaseHom) =
        (show (fiber.{max u v w} T).obj W from
          fiberMk.{max u v w} (rightBaseHom ≫ (𝒰.obj k).hom)) := by
    -- Push the explicit right-base generator along the cover morphism.
    simpa [T, rightBaseHom] using
      (fiber_map_fiberMk.{max u v w}
        (p := T) (f := rightBaseHom) (g := (𝒰.obj k).hom) :
          ((fiber.{max u v w} T).map (𝒰.obj k).hom) (fiberMk.{max u v w} rightBaseHom) =
            fiberMk.{max u v w} (rightBaseHom ≫ (𝒰.obj k).hom))
  have hfactor :
      (show (fiber.{max u v w} T).obj W from
        fiberMk.{max u v w} (rightBaseHom ≫ (𝒰.obj k).hom)) =
      (show (fiber.{max u v w} T).obj W from
        fiberMk.{max u v w} (T.map rightBaseToLeft ≫ f₀)) := by
    -- Rewrite the pullback-point image using the cover factorization at the glued right base.
    exact congrArg
      (fun m ↦ (show (fiber.{max u v w} T).obj W from fiberMk.{max u v w} m))
      (by
        simpa [f₁, T, rightBaseHom, rightBaseToLeft] using
          glued_refinement_right_base_cover_factorization
            (S := S) (hj₀ := hj₀) (f₀ := f₀) (𝒰 := 𝒰) (k := k))
  have hrewrite :
      (show (fiber.{max u v w} T).obj W from
        fiberMk.{max u v w} (T.map rightBaseToLeft ≫ f₀)) =
      (show (fiber.{max u v w} T).obj W from
        fiberMk.{max u v w} (T.map rightBaseToLeft ≫ leftStageMap)) := by
    -- Replace the left-stage map by the explicit refinement-image morphism.
    exact congrArg
      (fun m ↦
        (show (fiber.{max u v w} T).obj W from
          fiberMk.{max u v w} (T.map rightBaseToLeft ≫ m)))
      hleftStageMap.symm
  have hcollapse :
      (show (fiber.{max u v w} T).obj W from
        fiberMk.{max u v w} (T.map rightBaseToLeft ≫ leftStageMap)) =
      (show (fiber.{max u v w} T).obj W from fiberMk.{max u v w} leftStageMap) := by
    -- Now the right-base presentation collapses to the left-stage generator.
    exact
      (fiberMk_map_comp.{max u v w} (p := T) (g := rightBaseToLeft) (f := leftStageMap) :
        fiberMk.{max u v w} (T.map rightBaseToLeft ≫ leftStageMap) =
          fiberMk.{max u v w} leftStageMap)
  have hrefine :
      (show (fiber.{max u v w} T).obj W from fiberMk.{max u v w} leftStageMap) =
        (refinementFiber j T e).app W (show (fiber.{max u v w} S).obj W from
          fiberMk.{max u v w} f₀) := by
    -- The left-stage generator is exactly the refinement image of the original one.
    symm
    simpa [leftStageMap] using
      (refinementFiber_app_fiberMk (j := j) (T := T) (e := e)
        (U := op j0) (W := W) (f := f₀))
  exact hmap.trans (hfactor.trans (hrewrite.trans (hcollapse.trans hrefine)))

/-- Helper for Lemma 7.39.1: once a branch `k` is chosen, the canonical pullback point on the
right summand of the glued refinement maps to the refined image of the original generator. -/
private theorem glued_refinement_generator_lifts_cover
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C)
    {j0 j₁ : ι} (hj₀ : j0 ≤ j₁) {W : C} (f₀ : S.obj (op j0) ⟶ W)
    (𝒰 : SemiRepresentableFamily.Over W) (k : 𝒰.index) :
    let f₁ : S.obj (op j₁) ⟶ W := S.map (homOfLE hj₀).op ≫ f₀
    let T := glued_refinement_system S j₁ f₁ 𝒰 k
    let j : ι ↪o glued_refinement_index j₁ := glued_refinement_inclusion j₁
    let e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T := glued_refinement_iso S j₁ f₁ 𝒰 k
    ∃ y : (fiber.{max u v w} T).obj (𝒰.obj k).left,
      ((fiber.{max u v w} T).map (𝒰.obj k).hom) y =
        (refinementFiber j T e).app W (show (fiber.{max u v w} S).obj W from
          fiberMk.{max u v w} f₀) := by
  let f₁ : S.obj (op j₁) ⟶ W := S.map (homOfLE hj₀).op ≫ f₀
  let T := glued_refinement_system S j₁ f₁ 𝒰 k
  let j : ι ↪o glued_refinement_index j₁ := glued_refinement_inclusion j₁
  let e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T := glued_refinement_iso S j₁ f₁ 𝒰 k
  let rightBaseHom :
      T.obj (op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁)) ⟶ (𝒰.obj k).left :=
    pullback.fst (𝒰.obj k).hom
      (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁)
  -- Use the explicit pullback generator on the right base stage as the witness lifting `f₀`.
  refine ⟨fiberMk.{max u v w} rightBaseHom, ?_⟩
  simpa [f₁, T, j, e, rightBaseHom] using
    glued_refinement_right_base_generator_eq_refinement_image
      (S := S) (hj₀ := hj₀) (f₀ := f₀) (𝒰 := 𝒰) (k := k)

/-- Helper for Lemma 7.39.1: the raw presheaf fiber of the chosen branch agrees with the raw
presheaf fiber of the glued refinement by finality of the right summand. -/
private noncomputable def glued_right_branch_presheafFiber_iso
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [HasPullbacks C] (S : ιᵒᵖ ⥤ C)
    (j₁ : ι) {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (k : 𝒰.index) (Fobj : Cᵒᵖ ⥤ Type (max u v w)) :
    (fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).presheafFiber.obj Fobj ≅
      (fiber.{max u v w} (glued_refinement_system S j₁ f₁ 𝒰 k)).presheafFiber.obj Fobj := by
  let i : (Set.Ici j₁)ᵒᵖ ⥤ (glued_refinement_index j₁)ᵒᵖ :=
    ((glued_refinement_tail_inclusion j₁).toOrderHom.toFunctor).op
  let B := branch_system S j₁ f₁ 𝒰 k
  let T := glued_refinement_system S j₁ f₁ 𝒰 k
  let hSections : B.op ⋙ Fobj ≅ i.op ⋙ T.op ⋙ Fobj :=
    -- First identify the right restriction of the glued system with the explicit branch system,
    -- then rewrite the section diagram into the whiskered form expected by finality.
    (Functor.isoWhiskerRight
        (NatIso.op (glued_refinement_right_restrict_iso
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)).symm)
        Fobj) ≪≫
      (Functor.isoWhiskerRight (Functor.opComp i T) Fobj) ≪≫
      (Functor.associator i.op T.op Fobj)
  let _ : Functor.Final ((glued_refinement_tail_inclusion j₁).toOrderHom.toFunctor) :=
    glued_refinement_tail_inclusion_final (j₁ := j₁)
  let _ : Functor.Final i.op := by infer_instance
  let _ : Nonempty (Set.Ici j₁) := ⟨⟨j₁, le_rfl⟩⟩
  let _ : IsDirected (Set.Ici j₁) (· ≤ ·) := tail_index_isDirected (j₁ := j₁)
  let _ : Nonempty (glued_refinement_index j₁) := ⟨⟨Sum.inl j₁⟩⟩
  -- Compute both raw fibers by colimits of stagewise sections and insert the finality comparison
  -- for the right summand of the glued refinement.
  exact
    (inverse_system_presheafFiber_colimitIso B Fobj).symm ≪≫
      (HasColimit.isoOfNatIso hSections) ≪≫
      (Functor.Final.colimitIso i.op (T.op ⋙ Fobj)) ≪≫
      (inverse_system_presheafFiber_colimitIso T Fobj)

/-- Helper for Lemma 7.39.1: on the canonical tail-stage generator, the branch-to-glued raw-fiber
comparison agrees with first returning to the original system and then refining to the glued
system. -/
private theorem glued_right_branch_presheafFiber_iso_hom_branch_base_germ_eq
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [HasPullbacks C] (S : ιᵒᵖ ⥤ C)
    (j₁ : ι) {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (k : 𝒰.index) (Fobj : Cᵒᵖ ⥤ Type (max u v w))
    (t : Fobj.obj (op (S.obj (op j₁)))) :
    let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
    (glued_right_branch_presheafFiber_iso
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom
        ((fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber (S.obj (op j₁))
          (fiberMk.{max u v w} (U := op jTail)
            ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
              (op jTail))) Fobj t) =
      (fiber.{max u v w} (glued_refinement_system S j₁ f₁ 𝒰 k)).toPresheafFiber (S.obj (op j₁))
        (fiberMk.{max u v w}
          (U := op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁))
          (pullback.snd (𝒰.obj k).hom
            (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁))) Fobj t := by
  let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
  -- Route correction: isolate the remaining blocker to the finality/colimit evaluation on the
  -- single canonical branch generator at `jTail`.
  -- TODO: unfold `glued_right_branch_presheafFiber_iso` to the chain
  -- `inverse_system_presheafFiber_colimitIso.symm ≫ HasColimit.isoOfNatIso ≫
  --  Functor.Final.colimitIso ≫ inverse_system_presheafFiber_colimitIso`, then evaluate the
  -- `jTail` colimit generator with `colimit.comp_coconePointUniqueUpToIso_hom`,
  -- `HasColimit.isoOfNatIso_ι_hom`, and `Functor.Final.ι_colimitIso_hom`.
  sorry

/-- Helper for Lemma 7.39.1: the explicit glued right-base raw germ is already the refinement
image of the canonical tail-stage germ. -/
private theorem glued_right_base_presheafFiber_germ_eq_refinement_image
    {ι : Type w} [Preorder ι] [HasPullbacks C] (S : ιᵒᵖ ⥤ C)
    (j₁ : ι) {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (k : 𝒰.index) (Fobj : Cᵒᵖ ⥤ Type (max u v w))
    (t : Fobj.obj (op (S.obj (op j₁)))) :
    let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
    let xTail : (fiber.{max u v w} (tail_system S j₁)).obj (S.obj (op j₁)) :=
      fiberMk.{max u v w} (U := op jTail) (X := S.obj (op j₁)) (𝟙 (S.obj (op j₁)))
    let ŝt : (fiber.{max u v w} (tail_system S j₁)).presheafFiber.obj Fobj :=
      (fiber.{max u v w} (tail_system S j₁)).toPresheafFiber (S.obj (op j₁)) xTail Fobj t
    (fiber.{max u v w} (glued_refinement_system S j₁ f₁ 𝒰 k)).toPresheafFiber (S.obj (op j₁))
        (fiberMk.{max u v w}
          (U := op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁))
          (pullback.snd (𝒰.obj k).hom
            (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁))) Fobj t =
      ((refinementFiber (glued_refinement_inclusion j₁)
        (glued_refinement_system S j₁ f₁ 𝒰 k)
        (glued_refinement_iso S j₁ f₁ 𝒰 k)).presheafFiber).app Fobj
        (((refinementFiber (tail_inclusion j₁) S (Iso.refl _)).presheafFiber).app Fobj ŝt) := by
  let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
  let xTail : (fiber.{max u v w} (tail_system S j₁)).obj (S.obj (op j₁)) :=
    fiberMk.{max u v w} (U := op jTail) (X := S.obj (op j₁)) (𝟙 (S.obj (op j₁)))
  let ŝt : (fiber.{max u v w} (tail_system S j₁)).presheafFiber.obj Fobj :=
    (fiber.{max u v w} (tail_system S j₁)).toPresheafFiber (S.obj (op j₁)) xTail Fobj t
  let T := glued_refinement_system S j₁ f₁ 𝒰 k
  let ηTail := refinementFiber (tail_inclusion j₁) S (Iso.refl _)
  let ηG := refinementFiber (glued_refinement_inclusion j₁) T (glued_refinement_iso S j₁ f₁ 𝒰 k)
  let rightBaseToLeft :=
    glued_refinement_right_base_to_left_hom (j0 := j₁) (j₁ := j₁) (show j₁ ≤ j₁ from le_rfl)
  let rightBaseHom :
      T.obj (op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁)) ⟶ (𝒰.obj k).left :=
    pullback.fst (𝒰.obj k).hom
      (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁)
  have htail :
      ηTail.presheafFiber.app Fobj ŝt =
        (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
          (fiberMk.{max u v w} (𝟙 (S.obj (op j₁)))) Fobj t := by
    -- First identify the tail refinement image of the canonical tail germ with the identity germ.
    have hrewrite :
        (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
          (ηTail.app (S.obj (op j₁)) xTail) Fobj t =
        (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
          (fiberMk.{max u v w} (𝟙 (S.obj (op j₁)))) Fobj t := by
      have hrewrite₀ :
          (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
            (ηTail.app (S.obj (op j₁)) xTail) Fobj t =
          (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
            (fiberMk.{max u v w}
              ((Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S)).inv.app
                (op jTail) ≫ 𝟙 (S.obj (op j₁)))) Fobj t := by
        simpa only [ηTail, jTail, xTail] using
          congrArg
            (fun x ↦
              (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁)) x Fobj t)
            (refinementFiber_app_fiberMk (j := tail_inclusion j₁) (T := S) (e := Iso.refl _)
              (U := op jTail) (W := S.obj (op j₁)) (f := 𝟙 (S.obj (op j₁))))
      have hrewrite₁ :
          (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
              (fiberMk.{max u v w}
                ((Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S)).inv.app
                  (op jTail) ≫ 𝟙 (S.obj (op j₁)))) Fobj t =
            (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
              (fiberMk.{max u v w} (𝟙 (S.obj (op j₁)))) Fobj t := by
        have hunit :
            (Iso.refl ((tail_inclusion j₁).toOrderHom.toFunctor.op ⋙ S)).inv.app (op jTail) ≫
              𝟙 (S.obj (op j₁)) =
            𝟙 (S.obj (op j₁)) := by
          simp [jTail]
        exact congrArg
          (fun g ↦
            (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
              (fiberMk.{max u v w} g) Fobj t)
          hunit
      exact hrewrite₀.trans hrewrite₁
    calc
      ηTail.presheafFiber.app Fobj ŝt =
          (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
            (ηTail.app (S.obj (op j₁)) xTail) Fobj t := by
              simpa [ηTail, ŝt, xTail] using
                congrFun
                  (NatTrans.toPresheafFiber_presheafFiber_app
                    (η := ηTail) (F := Fobj) (X := S.obj (op j₁)) xTail)
                  t
      _ = (fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
            (fiberMk.{max u v w} (𝟙 (S.obj (op j₁)))) Fobj t := hrewrite
  have hrightBaseToLeft :
      T.map rightBaseToLeft =
        pullback.snd (𝒰.obj k).hom
          (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁) := by
    -- The mixed right-to-left map at the base tail stage is exactly the pullback second projection.
    change pullback.snd (𝒰.obj k).hom
        (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁) ≫
          S.map (show op j₁ ⟶ op j₁ from (homOfLE (show j₁ ≤ j₁ from le_rfl)).op) =
      pullback.snd (𝒰.obj k).hom
        (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁)
    simpa using
      Category.comp_id
        (pullback.snd (𝒰.obj k).hom
          (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁))
  have hleftGenerator :
      ηG.app (S.obj (op j₁))
          (show (fiber.{max u v w} S).obj (S.obj (op j₁)) from
            fiberMk.{max u v w} (𝟙 (S.obj (op j₁)))) =
        (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
          fiberMk.{max u v w}
            (U := op (⟨Sum.inl j₁⟩ : glued_refinement_index j₁))
            (𝟙 (S.obj (op j₁)))) := by
    -- On the left summand, the refinement map is exactly the identity stage inclusion.
    change (refinementFiber (glued_refinement_inclusion j₁) T
        (glued_refinement_iso S j₁ f₁ 𝒰 k)).app (S.obj (op j₁))
          (show (fiber.{max u v w} S).obj (S.obj (op j₁)) from
            fiberMk.{max u v w} (𝟙 (S.obj (op j₁)))) =
        (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
          fiberMk.{max u v w}
            (U := op (⟨Sum.inl j₁⟩ : glued_refinement_index j₁))
            (𝟙 (S.obj (op j₁))))
    have hraw :
        (refinementFiber (glued_refinement_inclusion j₁) T
            (glued_refinement_iso S j₁ f₁ 𝒰 k)).app (S.obj (op j₁))
            (show (fiber.{max u v w} S).obj (S.obj (op j₁)) from
              fiberMk.{max u v w} (𝟙 (S.obj (op j₁)))) =
          (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
            fiberMk.{max u v w}
              (U := op ((glued_refinement_inclusion j₁) j₁))
              ((glued_refinement_iso S j₁ f₁ 𝒰 k).inv.app (op j₁) ≫
                𝟙 (S.obj (op j₁)))) := by
      simpa using
        (refinementFiber_app_fiberMk
          (j := glued_refinement_inclusion j₁) (T := T)
          (e := glued_refinement_iso S j₁ f₁ 𝒰 k)
          (U := op j₁) (W := S.obj (op j₁)) (f := 𝟙 (S.obj (op j₁))))
    have hunit :
        (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
          fiberMk.{max u v w}
            (U := op ((glued_refinement_inclusion j₁) j₁))
            ((glued_refinement_iso S j₁ f₁ 𝒰 k).inv.app (op j₁) ≫
              𝟙 (S.obj (op j₁)))) =
        (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
          fiberMk.{max u v w}
            (U := op (⟨Sum.inl j₁⟩ : glued_refinement_index j₁))
            (𝟙 (S.obj (op j₁)))) := by
      refine congrArg
        (fun m ↦ (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
          fiberMk.{max u v w}
            (U := op (⟨Sum.inl j₁⟩ : glued_refinement_index j₁)) m)) ?_
      simpa using
        glued_refinement_iso_inv_app_eq_id
          (S := S) (j₁ := j₁) (j0 := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)
    exact hraw.trans hunit
  have hrightBase :
      (fiber.{max u v w} T).toPresheafFiber (S.obj (op j₁))
          (fiberMk.{max u v w}
            (U := op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁))
            (pullback.snd (𝒰.obj k).hom
              (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁))) Fobj t =
        (fiber.{max u v w} T).toPresheafFiber (S.obj (op j₁))
          (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
            ηG.app (S.obj (op j₁))
              (show (fiber.{max u v w} S).obj (S.obj (op j₁)) from
                fiberMk.{max u v w} (𝟙 (S.obj (op j₁))))) Fobj t := by
    -- Rewrite the explicit right-base germ by the specialized fiber equality.
    have hcollapse :
        (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
          fiberMk.{max u v w}
            (T.map rightBaseToLeft ≫ 𝟙 (S.obj (op j₁)))) =
        (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
          fiberMk.{max u v w}
            (U := op (⟨Sum.inl j₁⟩ : glued_refinement_index j₁))
            (𝟙 (S.obj (op j₁)))) := by
      simpa using
        (fiberMk_map_comp.{max u v w}
          (p := T) (g := rightBaseToLeft) (f := 𝟙 (S.obj (op j₁))) :
            fiberMk.{max u v w} (T.map rightBaseToLeft ≫ 𝟙 (S.obj (op j₁))) =
              fiberMk.{max u v w} (𝟙 (S.obj (op j₁))))
    have hexplicit :
        (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
          fiberMk.{max u v w}
            (U := op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁))
            (pullback.snd (𝒰.obj k).hom
              (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁))) =
        (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
          fiberMk.{max u v w}
            (T.map rightBaseToLeft ≫ 𝟙 (S.obj (op j₁)))) := by
      refine congrArg
        (fun m ↦ (show (fiber.{max u v w} T).obj (S.obj (op j₁)) from
          fiberMk.{max u v w} m)) ?_
      have hmorph :
          pullback.snd (𝒰.obj k).hom
              (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁) =
            T.map rightBaseToLeft ≫ 𝟙 (S.obj (op j₁)) := by
        rw [hrightBaseToLeft.symm]
        exact (Category.comp_id (T.map rightBaseToLeft)).symm
      exact hmorph
    exact
      congrArg
          (fun x ↦ (fiber.{max u v w} T).toPresheafFiber (S.obj (op j₁)) x Fobj t)
          hexplicit |>.trans <|
        (congrArg
          (fun x ↦ (fiber.{max u v w} T).toPresheafFiber (S.obj (op j₁)) x Fobj t)
          hcollapse).trans <|
        congrArg
          (fun x ↦ (fiber.{max u v w} T).toPresheafFiber (S.obj (op j₁)) x Fobj t)
          hleftGenerator.symm
  -- Now consume the two refinement maps by first normalizing the tail germ and then applying
  -- `toPresheafFiber_presheafFiber_app` for the glued refinement.
  calc
    (fiber.{max u v w} T).toPresheafFiber (S.obj (op j₁))
        (fiberMk.{max u v w}
          (U := op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁))
          (pullback.snd (𝒰.obj k).hom
            (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁))) Fobj t =
      (fiber.{max u v w} T).toPresheafFiber (S.obj (op j₁))
        (ηG.app (S.obj (op j₁))
          (show (fiber.{max u v w} S).obj (S.obj (op j₁)) from
            fiberMk.{max u v w} (𝟙 (S.obj (op j₁))))) Fobj t := hrightBase
    _ =
      ηG.presheafFiber.app Fobj
        ((fiber.{max u v w} S).toPresheafFiber (S.obj (op j₁))
          (fiberMk.{max u v w} (𝟙 (S.obj (op j₁)))) Fobj t) := by
            symm
            simpa [ηG] using
              congrFun
                (NatTrans.toPresheafFiber_presheafFiber_app
                  (η := ηG) (F := Fobj) (X := S.obj (op j₁))
                  (fiberMk.{max u v w} (𝟙 (S.obj (op j₁)))))
                t
    _ = ηG.presheafFiber.app Fobj (ηTail.presheafFiber.app Fobj ŝt) := by
          rw [htail]
    _ =
      ((refinementFiber (glued_refinement_inclusion j₁)
        (glued_refinement_system S j₁ f₁ 𝒰 k)
        (glued_refinement_iso S j₁ f₁ 𝒰 k)).presheafFiber).app Fobj
        (((refinementFiber (tail_inclusion j₁) S (Iso.refl _)).presheafFiber).app Fobj ŝt) := by
          rfl

/-- Helper for Lemma 7.39.1: on the canonical tail-stage generator, the branch-to-glued raw-fiber
comparison agrees with first returning to the original system and then refining to the glued
system. -/
private theorem glued_right_branch_presheafFiber_iso_hom_base_generator_eq
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [HasPullbacks C] (S : ιᵒᵖ ⥤ C)
    (j₁ : ι) {W : C} (f₁ : S.obj (op j₁) ⟶ W) (𝒰 : SemiRepresentableFamily.Over W)
    (k : 𝒰.index) (Fobj : Cᵒᵖ ⥤ Type (max u v w))
    (t : Fobj.obj (op (S.obj (op j₁)))) :
    let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
    let xTail : (fiber.{max u v w} (tail_system S j₁)).obj (S.obj (op j₁)) :=
      fiberMk.{max u v w} (U := op jTail) (X := S.obj (op j₁)) (𝟙 (S.obj (op j₁)))
    let ŝt : (fiber.{max u v w} (tail_system S j₁)).presheafFiber.obj Fobj :=
      (fiber.{max u v w} (tail_system S j₁)).toPresheafFiber (S.obj (op j₁)) xTail Fobj t
    (glued_right_branch_presheafFiber_iso
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom
        (tail_branch_presheafFiber_map
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k ŝt) =
      ((refinementFiber (glued_refinement_inclusion j₁)
        (glued_refinement_system S j₁ f₁ 𝒰 k)
        (glued_refinement_iso S j₁ f₁ 𝒰 k)).presheafFiber).app Fobj
        (((refinementFiber (tail_inclusion j₁) S (Iso.refl _)).presheafFiber).app Fobj ŝt) := by
  let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
  let xTail : (fiber.{max u v w} (tail_system S j₁)).obj (S.obj (op j₁)) :=
    fiberMk.{max u v w} (U := op jTail) (X := S.obj (op j₁)) (𝟙 (S.obj (op j₁)))
  let ŝt : (fiber.{max u v w} (tail_system S j₁)).presheafFiber.obj Fobj :=
    (fiber.{max u v w} (tail_system S j₁)).toPresheafFiber (S.obj (op j₁)) xTail Fobj t
  -- First normalize the tail-to-branch map on the canonical base generator.
  calc
    (glued_right_branch_presheafFiber_iso
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom
        (tail_branch_presheafFiber_map
          (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k ŝt) =
      (glued_right_branch_presheafFiber_iso
        (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom
        ((fiber.{max u v w} (branch_system S j₁ f₁ 𝒰 k)).toPresheafFiber (S.obj (op j₁))
          (fiberMk.{max u v w} (U := op jTail)
            ((branch_system_snd_hom (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k).app
              (op jTail))) Fobj t) := by
            exact congrArg
              ((glued_right_branch_presheafFiber_iso
                (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom)
              (by
                simpa [jTail, xTail, ŝt] using
                  tail_branch_presheafFiber_map_base_generator_eq
                    (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (Fobj := Fobj) (k := k) t)
    _ =
      (fiber.{max u v w} (glued_refinement_system S j₁ f₁ 𝒰 k)).toPresheafFiber (S.obj (op j₁))
        (fiberMk.{max u v w}
          (U := op (⟨Sum.inr ⟨j₁, le_rfl⟩⟩ : glued_refinement_index j₁))
          (pullback.snd (𝒰.obj k).hom
            (S.map (homOfLE (show j₁ ≤ j₁ from le_rfl)).op ≫ f₁))) Fobj t := by
              simpa [jTail] using
                glued_right_branch_presheafFiber_iso_hom_branch_base_germ_eq
                  (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)
                  (Fobj := Fobj) (t := t)
    _ =
      ((refinementFiber (glued_refinement_inclusion j₁)
        (glued_refinement_system S j₁ f₁ 𝒰 k)
        (glued_refinement_iso S j₁ f₁ 𝒰 k)).presheafFiber).app Fobj
        (((refinementFiber (tail_inclusion j₁) S (Iso.refl _)).presheafFiber).app Fobj ŝt) := by
          simpa [jTail, xTail, ŝt] using
            glued_right_base_presheafFiber_germ_eq_refinement_image
              (S := S) (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)
              (Fobj := Fobj) (t := t)

-- Proof sketch: represent `f` by a map from one stage of the original inverse system to `W`,
-- pull back the finite covering family `𝒰` to that stage, and use the sheaf condition together with
-- filtered-colimit commutation with finite products to find one cover member on which the images
-- of `s` and `s'` are still distinct. Adjoining those pullback stages yields a further directed
-- inverse system refining the original one, and the induced canonical maps on the associated
-- fibers still separate `s` and `s'` while making `f` come from one of the `u(𝒰ᵢ)`.
/-- Lemma 7.39.1: for a directed inverse system on a site whose category has pullbacks, two distinct elements of the canonical
raw sheaf fiber
`(sheafToPresheaf J (Type _) ⋙ (GrothendieckTopology.Point.ofIsCofiltered.fiber S').presheafFiber).obj ℱ`
of a sheaf can be separated after passing to a refinement of the inverse system, and a chosen
element of the source-facing set-valued functor
`(GrothendieckTopology.Point.ofIsCofiltered.fiber S').obj W` can simultaneously be made to come
from one member of a given finite covering family `𝒰 : SemiRepresentableFamily.Over W`. The
refinement data is given directly by a larger directed inverse system together with an order
embedding and an identification of the old system with the restriction of the new one. -/
theorem exists_refined_inverse_system_separating_sections_and_lifting_cover
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [HasPullbacks C] (S' : ιᵒᵖ ⥤ C)
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (hss' : s ≠ s')
    {W : C} (𝒰 : SemiRepresentableFamily.Over W) [Finite 𝒰.index]
    (h𝒰 : 𝒰.toSieve ∈ J W)
    (f : (fiber.{max u v w} S').obj W) :
    ∃ (ι' : Type w) (_ : Preorder ι') (_ : IsDirected ι' (· ≤ ·))
      (T : ι'ᵒᵖ ⥤ C) (j : ι ↪o ι') (e : S' ≅ (j.toOrderHom.toFunctor).op ⋙ T),
      ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s' ∧
        ∃ i : 𝒰.index, ∃ y : (fiber.{max u v w} T).obj (𝒰.obj i).left,
          ((fiber.{max u v w} T).map (𝒰.obj i).hom) y =
            (refinementFiber j T e).app W f := by
  -- Represent the chosen fiber element by a single stage map, exactly as in the source proof.
  rcases fiberMk_jointly_surjective f with ⟨j0, f0, rfl⟩
  let _ : Nonempty ι := ⟨j0.unop⟩
  let Fobj : Cᵒᵖ ⥤ Type (max u v w) :=
    (sheafToPresheaf J (Type (max u v w))).obj ℱ
  -- Route correction: before passing to the tail above `j0`, put `s` and `s'` on one raw
  -- generator of `(fiber S').presheafFiber`.
  obtain ⟨X, x, t, t', hs, hs'⟩ :=
    inverse_system_presheafFiber_jointly_surjective₂ (S := S') (F := Fobj) s s'
  have htt' : t ≠ t' := by
    intro hEq
    have hFiberEq :
        (fiber.{max u v w} S').toPresheafFiber X x Fobj t =
          (fiber.{max u v w} S').toPresheafFiber X x Fobj t' := by
      simp [hEq]
    apply hss'
    exact hs.symm.trans (hFiberEq.trans hs')
  rcases fiberMk_jointly_surjective x with ⟨jx, gx, rfl⟩
  obtain ⟨j₁, hj₀, hjx⟩ := directed_of (· ≤ ·) j0.unop jx.unop
  let g₁ : S'.obj (op j₁) ⟶ X := S'.map (homOfLE hjx).op ≫ gx
  let f₁ : S'.obj (op j₁) ⟶ W := S'.map (homOfLE hj₀).op ≫ f0
  let t₁ : Fobj.obj (op (S'.obj (op j₁))) := Fobj.map g₁.op t
  let t₁' : Fobj.obj (op (S'.obj (op j₁))) := Fobj.map g₁.op t'
  have hs₁ :
      (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
        (fiberMk (𝟙 (S'.obj (op j₁)))) Fobj t₁ = s := by
    -- Restrict the original common representative along the map from stage `j₁` to stage `jx`.
    calc
      (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
          (fiberMk (𝟙 (S'.obj (op j₁)))) Fobj t₁ =
        (fiber.{max u v w} S').toPresheafFiber X
          ((fiber.{max u v w} S').map g₁ (fiberMk (𝟙 (S'.obj (op j₁))))) Fobj t := by
            simpa [t₁] using
              congrFun
                ((fiber.{max u v w} S').toPresheafFiber_w (F := Fobj)
                  g₁ (fiberMk (𝟙 (S'.obj (op j₁))))) t
      _ = (fiber.{max u v w} S').toPresheafFiber X (fiberMk g₁) Fobj t := by
            simp
      _ = (fiber.{max u v w} S').toPresheafFiber X (fiberMk gx) Fobj t := by
            simp [g₁]
      _ = s := hs
  have hs₁' :
      (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
        (fiberMk (𝟙 (S'.obj (op j₁)))) Fobj t₁' = s' := by
    -- The same restriction step transports the second representative to the common tail stage.
    calc
      (fiber.{max u v w} S').toPresheafFiber (S'.obj (op j₁))
          (fiberMk (𝟙 (S'.obj (op j₁)))) Fobj t₁' =
        (fiber.{max u v w} S').toPresheafFiber X
          ((fiber.{max u v w} S').map g₁ (fiberMk (𝟙 (S'.obj (op j₁))))) Fobj t' := by
            simpa [t₁'] using
              congrFun
                ((fiber.{max u v w} S').toPresheafFiber_w (F := Fobj)
                  g₁ (fiberMk (𝟙 (S'.obj (op j₁))))) t'
      _ = (fiber.{max u v w} S').toPresheafFiber X (fiberMk g₁) Fobj t' := by
            simp
      _ = (fiber.{max u v w} S').toPresheafFiber X (fiberMk gx) Fobj t' := by
            simp [g₁]
      _ = s' := hs'
  let jTail : Set.Ici j₁ := ⟨j₁, le_rfl⟩
  let xTail : (fiber.{max u v w} (tail_system S' j₁)).obj (S'.obj (op j₁)) :=
    fiberMk.{max u v w} (U := op jTail) (X := S'.obj (op j₁)) (𝟙 (S'.obj (op j₁)))
  let ŝ : (fiber.{max u v w} (tail_system S' j₁)).presheafFiber.obj Fobj :=
    (fiber.{max u v w} (tail_system S' j₁)).toPresheafFiber (S'.obj (op j₁)) xTail Fobj t₁
  let ŝ' : (fiber.{max u v w} (tail_system S' j₁)).presheafFiber.obj Fobj :=
    (fiber.{max u v w} (tail_system S' j₁)).toPresheafFiber (S'.obj (op j₁)) xTail Fobj t₁'
  have htailSections :
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ = s ∧
        ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ' = s' ∧
        ŝ ≠ ŝ' := by
    -- Use the canonical tail-stage generators instead of abstract witnesses, so the final
    -- branch-to-glued comparison applies on the nose.
    simpa [jTail, xTail, ŝ, ŝ'] using
      canonical_tail_stage_sections (S' := S') (j₁ := j₁) (Fobj := Fobj)
        (s := s) (s' := s') (t₁ := t₁) (t₁' := t₁') hs₁ hs₁' hss'
  have hsTail :
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ = s :=
    htailSections.1
  have hsTail' :
      ((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app Fobj ŝ' = s' :=
    htailSections.2.1
  have hTailNe : ŝ ≠ ŝ' := htailSections.2.2
  have hbranchRaw :
      ∃ k : 𝒰.index,
        tail_branch_presheafFiber_map (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
            Fobj k ŝ ≠
          tail_branch_presheafFiber_map (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰)
            Fobj k ŝ' := by
    -- Route correction: choose the branch only after mapping the distinct tail germs into the
    -- finite product of branch raw fibers, matching the textbook proof.
    have hproductInj :
        Function.Injective
          (tail_branch_product_map
            (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj) := by
      -- Factor through the colimit/product comparison and use stagewise separatedness on the
      -- pulled-back cover, exactly as in the source proof.
      simpa [Fobj] using
        tail_branch_product_map_injective
          (J := J) (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) h𝒰 ℱ
    exact
      exists_branch_raw_ne_of_tail_ne
        (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj hTailNe hproductInj
  rcases hbranchRaw with ⟨k, hk⟩
  refine ⟨glued_refinement_index j₁, glued_refinement_preorder j₁,
      glued_refinement_isDirected j₁, glued_refinement_system S' j₁ f₁ 𝒰 k,
      glued_refinement_inclusion j₁, glued_refinement_iso S' j₁ f₁ 𝒰 k, ?_, ?_⟩
  · -- Apply the right-branch finality comparison on the explicit canonical tail generators and
    -- cancel it by injectivity to transport the chosen branch inequality into the glued refinement.
    intro hEq
    have hIsoEq :
        (glued_right_branch_presheafFiber_iso
          (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom
            (tail_branch_presheafFiber_map
              (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k ŝ) =
          (glued_right_branch_presheafFiber_iso
            (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom
            (tail_branch_presheafFiber_map
              (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k ŝ') := by
      calc
        (glued_right_branch_presheafFiber_iso
            (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom
            (tail_branch_presheafFiber_map
              (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k ŝ) =
          ((refinementFiber (glued_refinement_inclusion j₁)
              (glued_refinement_system S' j₁ f₁ 𝒰 k)
              (glued_refinement_iso S' j₁ f₁ 𝒰 k)).presheafFiber).app Fobj
            (((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app
              Fobj ŝ) := by
                simpa [jTail, xTail, ŝ] using
                  glued_right_branch_presheafFiber_iso_hom_base_generator_eq
                    (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)
                    (Fobj := Fobj) (t := t₁)
        _ =
          ((refinementFiber (glued_refinement_inclusion j₁)
              (glued_refinement_system S' j₁ f₁ 𝒰 k)
              (glued_refinement_iso S' j₁ f₁ 𝒰 k)).presheafFiber).app Fobj s := by
                rw [hsTail]
        _ =
          ((refinementFiber (glued_refinement_inclusion j₁)
              (glued_refinement_system S' j₁ f₁ 𝒰 k)
              (glued_refinement_iso S' j₁ f₁ 𝒰 k)).presheafFiber).app Fobj s' := hEq
        _ =
          ((refinementFiber (glued_refinement_inclusion j₁)
              (glued_refinement_system S' j₁ f₁ 𝒰 k)
              (glued_refinement_iso S' j₁ f₁ 𝒰 k)).presheafFiber).app Fobj
            (((refinementFiber (tail_inclusion j₁) S' (Iso.refl _)).presheafFiber).app
              Fobj ŝ') := by
                rw [hsTail']
        _ =
          (glued_right_branch_presheafFiber_iso
            (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom
            (tail_branch_presheafFiber_map
              (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) Fobj k ŝ') := by
                symm
                simpa [jTail, xTail, ŝ'] using
                  glued_right_branch_presheafFiber_iso_hom_base_generator_eq
                    (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) (k := k)
                    (Fobj := Fobj) (t := t₁')
    have hIsoInj :
        Function.Injective
          (glued_right_branch_presheafFiber_iso
            (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom :=
      (ConcreteCategory.bijective_of_isIso
        ((glued_right_branch_presheafFiber_iso
          (S := S') (j₁ := j₁) (f₁ := f₁) (𝒰 := 𝒰) k Fobj).hom)).1
    exact hk (hIsoInj hIsoEq)
  · -- The lift half of the source proof is now realized directly at the right base branch stage.
    refine ⟨k, ?_⟩
    simpa [f₁] using
      glued_refinement_generator_lifts_cover
        (S := S') (hj₀ := hj₀) (f₀ := f0) (𝒰 := 𝒰) (k := k)

end

end CategoryTheory
