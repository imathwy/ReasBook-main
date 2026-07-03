import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_26_4 (from Chap07) -/
open CategoryTheory

universe u v w

namespace CategoryTheory
namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {U : C}

/- Domain-style sampling for Lemma 7.26.4:
- primary domain: effective descent for sheaves on slice sites, encoded by the pseudofunctor
  `J.pseudofunctorOver (Type (max u v))`;
- sampled owner API:
  `GrothendieckTopology.pseudofunctorOver`,
  `Pseudofunctor.IsStackFor`,
  `Pseudofunctor.isStackFor_ofArrows_iff`,
  `Pseudofunctor.IsStackFor.essSurj`,
  `Functor.EssSurj`,
  `GrothendieckTopology.Cover`;
- source-facing layer: the essential-surjectivity statement for descent data on a fixed cover
  `𝒰 : J.Cover U`;
- core/canonical owner: the fixed-cover stack condition
  `(J.pseudofunctorOver (Type (max u v))).IsStackFor (Presieve.ofArrows _ (fun I : 𝒰.Arrow ↦ I.f))`;
- bridge/view: the descent-data functor attached to the family of cover arrows
  `fun I : 𝒰.Arrow ↦ I.f`.

Primitive data are the site topology `J`, the object `U`, and the cover `𝒰 : J.Cover U`. The
fixed-cover stack condition is the canonical owner abstraction; the essential-surjectivity
statement for the descent-data functor is derived API of that owner. This file keeps the
source-facing `EssSurj` theorem and packages the same content once at the owner level so later
files can reuse it directly instead of rebuilding the stack proof.
-/

-- Proof sketch: view the family of slice-site sheaf categories as the pseudofunctor
-- `J.pseudofunctorOver (Type (max u v))`. Combine the prestack theorem from Lemma `7.26.1`
-- with essential surjectivity for the fixed cover to obtain the owner-level stack condition,
-- then recover the textbook `EssSurj` statement from that owner theorem.
/-- Helper for Lemma 7.26.4: giving, for each descent datum on the fixed cover `𝒰`, an object in
the essential image of the descent-data functor is exactly the data needed to prove essential
surjectivity. -/
private theorem localized_cover_descent_essSurj_of_glued_objects
    (𝒰 : J.Cover U)
    (lift :
      ∀ D : (J.pseudofunctorOver (Type w)).DescentData (fun I : 𝒰.Arrow ↦ I.f),
        (((J.pseudofunctorOver (Type w)).toDescentData
          (fun I : 𝒰.Arrow ↦ I.f)).essImage D)) :
    ((J.pseudofunctorOver (Type w)).toDescentData
      (fun I : 𝒰.Arrow ↦ I.f)).EssSurj := by
  -- `Functor.EssSurj.mk` packages the objectwise essential-image witnesses.
  exact Functor.EssSurj.mk lift

/-- Helper for Lemma 7.26.4: the owner-level stack statement for the fixed cover `𝒰` immediately
implies the source-facing essential-surjectivity statement for the associated descent-data
functor. -/
private theorem localized_cover_descent_essSurj_of_isStackFor
    (𝒰 : J.Cover U)
    (h :
      (J.pseudofunctorOver (Type w)).IsStackFor
        (Presieve.ofArrows _ (fun I : 𝒰.Arrow ↦ I.f))) :
    ((J.pseudofunctorOver (Type w)).toDescentData
      (fun I : 𝒰.Arrow ↦ I.f)).EssSurj := by
  -- Convert the owner-level stack statement into an equivalence of categories.
  letI :
      ((J.pseudofunctorOver (Type w)).toDescentData
        (fun I : 𝒰.Arrow ↦ I.f)).IsEquivalence :=
    (((J.pseudofunctorOver (Type w)).isStackFor_ofArrows_iff
      (fun I : 𝒰.Arrow ↦ I.f))).1 h
  -- Essential surjectivity is then an instance field of the resulting equivalence.
  infer_instance

/-- Helper for Lemma 7.26.4: the fixed-cover descent category attached to `𝒰`. -/
private abbrev localized_cover_descent_category
    (𝒰 : J.Cover U) :=
  (J.pseudofunctorOver (Type w)).DescentData (fun I : 𝒰.Arrow ↦ I.f)

/-- Helper for Lemma 7.26.4: on the pullback cover of `V ⟶ U`, each arrow has the same domain as
its base arrow, so the pullback comparison square is witnessed by the identity on that domain. -/
private theorem localized_cover_descent_pullbackDatum_w
    (𝒰 : J.Cover U) (V : Over U) (K : (𝒰.pullback V.hom).Arrow) :
    (𝟙 K.Y) ≫ K.base.f = K.f ≫ V.hom := by
  -- The base arrow of `K` is defined by composing `K.f` with `V.hom`.
  simp [GrothendieckTopology.Cover.Arrow.base]

/-- Helper for Lemma 7.26.4: pull a fixed-cover descent datum back along an object `V` of the
slice `C / U`, so later objectwise formulas can talk directly about the pulled-back cover
`𝒰.pullback V.hom`. -/
private def localized_cover_descent_pullbackDatum
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (V : Over U) :
    (J.pseudofunctorOver (Type w)).DescentData
      (fun K : (𝒰.pullback V.hom).Arrow ↦ K.f) :=
  (Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
    (f := fun I : 𝒰.Arrow ↦ I.f)
    (p := V.hom)
    (f' := fun K : (𝒰.pullback V.hom).Arrow ↦ K.f)
    (α := fun K ↦ K.base)
    (p' := fun _ ↦ 𝟙 _)
    (w := localized_cover_descent_pullbackDatum_w (J := J) (U := U) 𝒰 V)).obj D

/-- Helper for Lemma 7.26.4: pulling back the descent datum of an actual sheaf is canonically the
same as taking descent data after pulling the sheaf back to the smaller slice. -/
private def localized_cover_descent_pullbackDatum_of_toDescentData_iso
    (𝒰 : J.Cover U)
    (M : Sheaf (J.over U) (Type w))
    (V : Over U) :
    localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰
      (((J.pseudofunctorOver (Type w)).toDescentData
        (fun I : 𝒰.Arrow ↦ I.f)).obj M) V ≅
      (((J.pseudofunctorOver (Type w)).toDescentData
        (fun K : (𝒰.pullback V.hom).Arrow ↦ K.f)).obj
          ((J.overMapPullback (Type w) V.hom).obj M)) :=
  (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
    (J.pseudofunctorOver (Type w))
    (f := fun I : 𝒰.Arrow ↦ I.f)
    (p := V.hom)
    (f' := fun K : (𝒰.pullback V.hom).Arrow ↦ K.f)
    (α := fun K ↦ K.base)
    (p' := fun _ ↦ 𝟙 _)
    (w := localized_cover_descent_pullbackDatum_w (J := J) (U := U) 𝒰 V)).app M

/-- Helper for Lemma 7.26.4: over the pullback cover above a chosen cover member `I`, one may
reindex the pulled-back datum from the varying base arrows `K.base` to the fixed component `I`
using the descent isomorphisms already stored in `D`. -/
private def localized_cover_descent_componentPullbackDatum
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :
    (J.pseudofunctorOver (Type w)).DescentData
      (fun K : (𝒰.pullback I.f).Arrow ↦ K.f) :=
  (Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
    (f := fun JI : 𝒰.Arrow ↦ JI.f)
    (p := I.f)
    (f' := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
    (α := fun _ ↦ I)
    (p' := fun K ↦ K.f)
    (w := fun K ↦ by simp)).obj D

/-- Helper for Lemma 7.26.4: pulling back the terminal object of `Over K.Y` along `K.f` gives the
object `Over.mk K.f` in `Over I.Y`. This is the section-level normalization used when passing
between global sections of a pulled-back sheaf and sections over the overlap object itself. -/
private theorem localized_cover_descent_overMap_terminal_obj
    {X Y : C}
    (f : X ⟶ Y) :
    (Over.map f).obj (Over.mk (𝟙 X)) = Over.mk f := by
  change Over.mk ((𝟙 X) ≫ f) = Over.mk f
  simp

/-- Helper for Lemma 7.26.4: for the constant-index pullback datum over a chosen cover member `I`,
the `K`-component is literally the pullback of the fixed sheaf `D.obj I` along `K.f`, so its
global sections are exactly sections of `D.obj I` over `Over.mk K.f`. -/
private theorem localized_cover_descent_componentPullbackDatum_section_eq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (K : (𝒰.pullback I.f).Arrow) :
    (((localized_cover_descent_componentPullbackDatum (J := J) (U := U) 𝒰 D I).obj K).1.obj
      (Opposite.op (Over.mk (𝟙 K.Y)))) =
      ((D.obj I).1.obj (Opposite.op (Over.mk K.f))) := by
  -- The pullback datum at `K` is defined using `J.overMapPullback` along `K.f`.
  simp [localized_cover_descent_componentPullbackDatum,
    localized_cover_descent_overMap_terminal_obj]

/-- Helper for Lemma 7.26.4: the same section identification holds for the ordinary
`toDescentData` construction on the fixed sheaf `D.obj I`. This is the target-side normal form
used when comparing pulled-back descent data to the textbook compatible-family description. -/
private theorem localized_cover_descent_toDescentData_section_eq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (K : (𝒰.pullback I.f).Arrow) :
    (((((J.pseudofunctorOver (Type w)).toDescentData
        (fun L : (𝒰.pullback I.f).Arrow ↦ L.f)).obj (D.obj I)).obj K).1.obj
      (Opposite.op (Over.mk (𝟙 K.Y)))) =
      ((D.obj I).1.obj (Opposite.op (Over.mk K.f))) := by
  -- Unfolding `toDescentData` shows that its `K`-component is the same pullback sheaf.
  simp [Pseudofunctor.toDescentData, localized_cover_descent_overMap_terminal_obj]

/-- Helper for Lemma 7.26.4: the pulled-back datum can first be reindexed to the constant
component `I` before comparing it with the ordinary descent datum of `D.obj I`. -/
private def localized_cover_descent_pullbackDatum_reindex_iso
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :
    localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D (Over.mk I.f) ≅
      localized_cover_descent_componentPullbackDatum (J := J) (U := U) 𝒰 D I :=
  (Pseudofunctor.DescentData.pullFunctorIso (J.pseudofunctorOver (Type w))
    (f := fun JI : 𝒰.Arrow ↦ JI.f)
    (p := I.f)
    (f' := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
    (α := fun K ↦ K.base)
    (p' := fun _ ↦ 𝟙 _)
    (w := localized_cover_descent_pullbackDatum_w (J := J) (U := U) 𝒰 (Over.mk I.f))
    (β := fun _ ↦ I)
    (p'' := fun K ↦ K.f)
    (w' := fun K ↦ by simp)).app D

/-- Helper for Lemma 7.26.4: once the pullback datum over `I` has been reindexed so that every
component comes from the fixed sheaf `D.obj I`, its transition maps are exactly the canonical
transition maps of the ordinary descent datum of `D.obj I`. -/
private noncomputable def localized_cover_descent_componentPullbackDatum_toDescentData_obj
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :
    localized_cover_descent_componentPullbackDatum (J := J) (U := U) 𝒰 D I ≅
      (((J.pseudofunctorOver (Type w)).toDescentData
        (fun K : (𝒰.pullback I.f).Arrow ↦ K.f)).obj (D.obj I)) := by
  -- The object components already agree definitionally after reindexing to the fixed index `I`.
  refine Pseudofunctor.DescentData.isoMk (fun K ↦ Iso.refl _) ?_
  intro Y q K₁ K₂ f₁ f₂ hf₁ hf₂
  -- Route correction: specialize the pullback transition map to the common composite `q ≫ I.f`;
  -- the middle descent morphism of `D` then becomes the identity on the `I`-component.
  -- `pullFunctorObjHom_eq` rewrites the pullback transition map into a `D.hom` term at index `I`,
  -- and `hom_self` then collapses that middle map to the identity.
  simpa [localized_cover_descent_componentPullbackDatum, Pseudofunctor.toDescentData,
    D.hom_self, hf₁, hf₂, Category.assoc] using
    (Pseudofunctor.DescentData.pullFunctorObjHom_eq
      (F := J.pseudofunctorOver (Type w))
      (f := fun JI : 𝒰.Arrow ↦ JI.f)
      (p := I.f)
      (f' := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
      (α := fun _ ↦ I)
      (p' := fun K ↦ K.f)
      (w := fun K ↦ by simp)
      (D := D)
      (q := q)
      (f₁ := f₁)
      (f₂ := f₂)
      (q' := q ≫ I.f)
      (f₁' := q)
      (f₂' := q)).symm

/-- Helper for Lemma 7.26.4: after restricting a descent datum to the pullback cover over a fixed
cover member `I`, the resulting datum is canonically identified with the ordinary descent datum of
the component sheaf `D.obj I` on that pullback cover. -/
private noncomputable def localized_cover_descent_pullbackDatum_toDescentData_obj
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :
    localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D (Over.mk I.f) ≅
      (((J.pseudofunctorOver (Type w)).toDescentData
        (fun K : (𝒰.pullback I.f).Arrow ↦ K.f)).obj (D.obj I)) := by
  -- First reindex the pulled-back datum so every component is expressed over the fixed sheaf
  -- `D.obj I`; this separates the real remaining issue from the bookkeeping transport.
  refine localized_cover_descent_pullbackDatum_reindex_iso (J := J) (U := U) 𝒰 D I ≪≫
    localized_cover_descent_componentPullbackDatum_toDescentData_obj
      (J := J) (U := U) 𝒰 D I

/-- Helper for Lemma 7.26.4: on each pullback-cover member `K`, the comparison isomorphism from
the pulled-back datum over `I` to the ordinary descent datum of `D.obj I` has a concrete
componentwise sheaf isomorphism. -/
private noncomputable def localized_cover_descent_pullbackDatum_component_iso
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (K : (𝒰.pullback I.f).Arrow) :
    (localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D (Over.mk I.f)).obj K ≅
      ((((J.pseudofunctorOver (Type w)).toDescentData
          (fun L : (𝒰.pullback I.f).Arrow ↦ L.f)).obj (D.obj I)).obj K) where
  hom :=
    (localized_cover_descent_pullbackDatum_toDescentData_obj
      (J := J) (U := U) 𝒰 D I).hom.hom K
  inv :=
    (localized_cover_descent_pullbackDatum_toDescentData_obj
      (J := J) (U := U) 𝒰 D I).inv.hom K
  hom_inv_id := by
    have hK :
        (localized_cover_descent_pullbackDatum_toDescentData_obj
          (J := J) (U := U) 𝒰 D I).hom.hom K ≫
          (localized_cover_descent_pullbackDatum_toDescentData_obj
            (J := J) (U := U) 𝒰 D I).inv.hom K =
            𝟙 ((localized_cover_descent_pullbackDatum
              (J := J) (U := U) 𝒰 D (Over.mk I.f)).obj K) := by
      exact congrArg
        (fun f ↦ f.hom K)
        ((localized_cover_descent_pullbackDatum_toDescentData_obj
          (J := J) (U := U) 𝒰 D I).hom_inv_id)
    exact hK
  inv_hom_id := by
    have hK :
        (localized_cover_descent_pullbackDatum_toDescentData_obj
          (J := J) (U := U) 𝒰 D I).inv.hom K ≫
          (localized_cover_descent_pullbackDatum_toDescentData_obj
            (J := J) (U := U) 𝒰 D I).hom.hom K =
            𝟙 (((((J.pseudofunctorOver (Type w)).toDescentData
              (fun L : (𝒰.pullback I.f).Arrow ↦ L.f)).obj (D.obj I)).obj K)) := by
      exact congrArg
        (fun f ↦ f.hom K)
        ((localized_cover_descent_pullbackDatum_toDescentData_obj
          (J := J) (U := U) 𝒰 D I).inv_hom_id)
    exact hK

/-- Helper for Lemma 7.26.4: evaluating the `K`-component comparison isomorphism at the terminal
object of `Over K.Y` identifies sections of the pulled-back datum with sections of the fixed
component sheaf `D.obj I` over the overlap object `Over.mk K.f`. -/
private noncomputable def localized_cover_descent_pullbackDatum_section_equiv_component
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (K : (𝒰.pullback I.f).Arrow) :
    (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D (Over.mk I.f)).obj K).1.obj
      (Opposite.op (Over.mk (𝟙 K.Y)))) ≃
      ((D.obj I).1.obj (Opposite.op (Over.mk K.f))) where
  toFun x :=
    cast
      (localized_cover_descent_toDescentData_section_eq (J := J) (U := U) 𝒰 D I K)
      ((localized_cover_descent_pullbackDatum_component_iso
        (J := J) (U := U) 𝒰 D I K).hom.hom.app
          (Opposite.op (Over.mk (𝟙 K.Y))) x)
  invFun y :=
    ((localized_cover_descent_pullbackDatum_component_iso
      (J := J) (U := U) 𝒰 D I K).inv.hom.app
        (Opposite.op (Over.mk (𝟙 K.Y)))
        (cast
          (localized_cover_descent_toDescentData_section_eq
            (J := J) (U := U) 𝒰 D I K).symm y))
  left_inv x := by
    -- Undo the target-side cast and apply the inverse relation of the component comparison.
    let e :=
      ((sheafToPresheaf (J.over K.Y) (Type w)).mapIso
        (localized_cover_descent_pullbackDatum_component_iso
          (J := J) (U := U) 𝒰 D I K)).app
        (Opposite.op (Over.mk (𝟙 K.Y)))
    simpa [e] using CategoryTheory.hom_inv_id_apply e x
  right_inv y := by
    -- The same inverse relation shows that a component section is recovered unchanged.
    let h :=
      localized_cover_descent_toDescentData_section_eq (J := J) (U := U) 𝒰 D I K
    let e :=
      ((sheafToPresheaf (J.over K.Y) (Type w)).mapIso
        (localized_cover_descent_pullbackDatum_component_iso
          (J := J) (U := U) 𝒰 D I K)).app
        (Opposite.op (Over.mk (𝟙 K.Y)))
    simpa [e, h] using congrArg (cast h)
      (CategoryTheory.inv_hom_id_apply e (cast h.symm y))

/-- Helper for Lemma 7.26.4: a morphism `g : V ⟶ W` in `Over U` sends an arrow of the pullback
cover above `V` to the corresponding arrow of the pullback cover above `W` by postcomposing with
`g.left`. This is the indexing map needed for the glued-compatible-family restriction maps. -/
private def localized_cover_descent_pullback_arrow_map
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (K : (𝒰.pullback V.hom).Arrow) :
    (𝒰.pullback W.hom).Arrow :=
  ⟨K.Y, K.f ≫ g.left, by
    -- Rewrite the composite to `U` using the defining equality of morphisms in `Over U`.
    have hg : K.f ≫ g.left ≫ W.hom = K.f ≫ V.hom := by
      simpa [Category.assoc] using congrArg (fun h ↦ K.f ≫ h) (Over.w g)
    simpa [GrothendieckTopology.Cover.coe_pullback] using hg ▸ K.hf⟩

/-- Helper for Lemma 7.26.4: the arrow of `𝒰` underlying an indexed pullback arrow does not
change when that pullback arrow is transported along a morphism in `Over U`. -/
private theorem localized_cover_descent_pullback_arrow_map_base
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (K : (𝒰.pullback V.hom).Arrow) :
    (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K).base = K.base := by
  -- Compare the two underlying arrows in the original cover after expanding `base`.
  ext
  · rfl
  · simpa [localized_cover_descent_pullback_arrow_map, GrothendieckTopology.Cover.Arrow.base,
      Category.assoc] using congrArg (fun h ↦ K.f ≫ h) (Over.w g)

/-- Helper for Lemma 7.26.4: a relation in the pullback cover above `V` is also a relation
between the transported arrows in the pullback cover above `W`. This packages the overlap
reindexing needed for the glued-compatible-family restriction maps. -/
private def localized_cover_descent_pullback_relation_map
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation) :
    (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g R.fst).Relation
      (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g R.snd) :=
  { R.r with
    w := by
      -- The overlap equation is preserved after postcomposing both sides with `g.left`.
      simpa [localized_cover_descent_pullback_arrow_map, Category.assoc] using
        congrArg (fun f ↦ f ≫ g.left) R.r.w }

/-- Helper for Lemma 7.26.4: after pulling a component of `localized_cover_descent_pullbackDatum`
back along `g : Z ⟶ K.Y`, evaluating at the terminal object of `Over Z` is the same as evaluating
the original component on `Over.mk g`. This is the terminal-section normalization used in the
glued compatible-family overlap equations. -/
private theorem localized_cover_descent_pullbackDatum_section_eq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (V : Over U)
    (K : (𝒰.pullback V.hom).Arrow)
    {Z : C}
    (g : Z ⟶ K.Y) :
    (((J.overMapPullback (Type w) g).obj
        ((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D V).obj K)).1.obj
      (Opposite.op (Over.mk (𝟙 Z)))) =
      (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D V).obj K).1.obj
        (Opposite.op (Over.mk g))) := by
  -- Unfold the pullback-datum component and normalize the pulled-back terminal object.
  simp [localized_cover_descent_pullbackDatum,
    localized_cover_descent_overMap_terminal_obj]

/-- Helper for Lemma 7.26.4: once a glue functor together with unit and counit isomorphisms is
constructed, the fixed-cover descent functor is packaged as an equivalence of categories. -/
private def localized_cover_descent_equivalence
    (𝒰 : J.Cover U)
    (glue : localized_cover_descent_category (J := J) (U := U) 𝒰 ⥤
      Sheaf (J.over U) (Type w))
    (unitIso :
      𝟭 (Sheaf (J.over U) (Type w)) ≅
        ((J.pseudofunctorOver (Type w)).toDescentData
          (fun I : 𝒰.Arrow ↦ I.f)) ⋙ glue)
    (counitIso :
      glue ⋙ ((J.pseudofunctorOver (Type w)).toDescentData
        (fun I : 𝒰.Arrow ↦ I.f)) ≅
        𝟭 (localized_cover_descent_category (J := J) (U := U) 𝒰)) :
    Sheaf (J.over U) (Type w) ≌
      localized_cover_descent_category (J := J) (U := U) 𝒰 :=
  Equivalence.mk
    ((J.pseudofunctorOver (Type w)).toDescentData (fun I : 𝒰.Arrow ↦ I.f))
    glue
    unitIso
    counitIso

/-- Helper for Lemma 7.26.4: an explicit glue quasi-inverse to `toDescentData` is enough to prove
the owner-level fixed-cover stack statement. -/
private theorem localized_cover_descent_isStackFor_of_equivalenceData
    (𝒰 : J.Cover U)
    (glue : localized_cover_descent_category (J := J) (U := U) 𝒰 ⥤
      Sheaf (J.over U) (Type w))
    (unitIso :
      𝟭 (Sheaf (J.over U) (Type w)) ≅
        ((J.pseudofunctorOver (Type w)).toDescentData
          (fun I : 𝒰.Arrow ↦ I.f)) ⋙ glue)
    (counitIso :
      glue ⋙ ((J.pseudofunctorOver (Type w)).toDescentData
        (fun I : 𝒰.Arrow ↦ I.f)) ≅
        𝟭 (localized_cover_descent_category (J := J) (U := U) 𝒰)) :
    (J.pseudofunctorOver (Type w)).IsStackFor
      (Presieve.ofArrows _ (fun I : 𝒰.Arrow ↦ I.f)) := by
  -- Rewrite the owner theorem to the explicit descent-data functor statement.
  rw [Pseudofunctor.isStackFor_ofArrows_iff]
  -- The quasi-inverse data now closes the goal by the standard equivalence package.
  exact (localized_cover_descent_equivalence (J := J) (U := U) 𝒰
    glue unitIso counitIso).isEquivalence_functor

-- Route correction: the local `localized_pseudofunctorOver_*` transport block duplicated the
-- prestack work from Lemma `7.26.1` and was the source of the compile errors in this file. The
-- fixed-cover full-faithfulness proof below now uses the direct terminal-cover sheaf condition.
-- The surviving comparison lemmas remain available because the fixed-cover proof still needs the
-- stable NatIso between the ordinary slice-site Hom sheaf and `pseudofunctorOver.presheafHom`.

/-- Helper for Lemma 7.26.4: transporting a sheaf on the iterated slice
`((Over U) / T)` across the canonical equivalence with `Over T.left` identifies the iterated
pullback of a slice sheaf with the ordinary pullback along `T.hom`. -/
private noncomputable def localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
    (T : Over U)
    (M : Sheaf (J.over U) (Type w)) :
    (T.iteratedSliceEquiv.sheafCongr (((J.over U)).over T) (J.over T.left) (Type w)).functor.obj
      ((((J.over U)).overPullback (Type w) T).obj M) ≅
      ((J.overMapPullback (Type w) T.hom).obj M) := by
  -- Compare the two localized sheaves at the presheaf level using
  -- `iteratedSliceBackward ⋙ forget = Over.map T.hom`.
  refine (fullyFaithfulSheafToPresheaf (J.over T.left) (Type w)).preimageIso ?_
  simpa [GrothendieckTopology.overPullback, GrothendieckTopology.overMapPullback,
    Equivalence.sheafCongr, Equivalence.sheafCongr.functor] using
    (Functor.isoWhiskerRight
      (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T)))
      M.obj)

/-- Helper for Lemma 7.26.4: after forgetting to presheaves, the forward map of the iterated-slice
pullback comparison is exactly the whiskered identity transport coming from
`Over.iteratedSliceBackward_forget`. -/
private theorem localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback_hom_map
    (T : Over U)
    (M : Sheaf (J.over U) (Type w)) :
    (sheafToPresheaf (J.over T.left) (Type w)).map
      (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
        (J := J) (U := U) T M).hom =
      (Functor.isoWhiskerRight
        (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T)))
        M.obj).hom := by
  -- This is the defining property of the `preimageIso` used above.
  simp [localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback]

/-- Helper for Lemma 7.26.4: after forgetting to presheaves, the inverse map of the iterated-slice
pullback comparison is the inverse whiskered identity transport coming from
`Over.iteratedSliceBackward_forget`. -/
private theorem localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback_inv_map
    (T : Over U)
    (M : Sheaf (J.over U) (Type w)) :
    (sheafToPresheaf (J.over T.left) (Type w)).map
      (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
        (J := J) (U := U) T M).inv =
      (Functor.isoWhiskerRight
        (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T)))
        M.obj).inv := by
  -- The inverse statement is the same `preimageIso` computation for the inverse component.
  simp [localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback]

/-- Helper for Lemma 7.26.4: after transporting from the iterated slice to `Over T.left`,
morphisms between the two iterated pullbacks are the same as morphisms between their transported
images. -/
private noncomputable def localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
    (T : Over U)
    (M N : Sheaf (J.over U) (Type w)) :
    ((((J.over U)).overPullback (Type w) T).obj M ⟶
      (((J.over U)).overPullback (Type w) T).obj N) ≃
      ((T.iteratedSliceEquiv.sheafCongr (((J.over U)).over T) (J.over T.left) (Type w)).functor.obj
          ((((J.over U)).overPullback (Type w) T).obj M) ⟶
        (T.iteratedSliceEquiv.sheafCongr (((J.over U)).over T) (J.over T.left) (Type w)).functor.obj
          ((((J.over U)).overPullback (Type w) T).obj N)) :=
  (Functor.FullyFaithful.ofFullyFaithful
    ((T.iteratedSliceEquiv.sheafCongr (((J.over U)).over T) (J.over T.left) (Type w)).functor)).homEquiv

/-- Helper for Lemma 7.26.4: the ordinary Hom sheaf on `J.over U` evaluated at `T` matches the
owner-level presheaf of morphisms for `J.pseudofunctorOver` at the same object `T`. -/
private noncomputable def localized_pseudofunctorOver_presheafHom_obj_equiv
    (T : Over U)
    (M N : Sheaf (J.over U) (Type w)) :
    ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T)) ≃
      (((J.pseudofunctorOver (Type w)).presheafHom M N).obj (Opposite.op T)) := by
  -- First identify the ordinary Hom-sheaf value with morphisms on the iterated slice,
  -- then transport those morphisms to the `overMapPullback` owner used by `presheafHom`.
  exact
    (localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv (J := J) (U := U) T M N).trans
      (Iso.homCongr
        (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T M)
        (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T N))

/-- Helper for Lemma 7.26.4: evaluating the objectwise comparison at `T` already lands in the
owner-side source coordinates used by `overMapCompPresheafHomIso` at the terminal object of
`Over T.left`. This packages the source-side coordinate change needed in the naturality step. -/
private noncomputable abbrev localized_pseudofunctorOver_presheafHom_obj_equiv_owner_source
    (T : Over U)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T))) :
    (((Over.map T.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
      (Opposite.op (Over.mk (𝟙 T.left)))) :=
  Eq.mp
    (by
      simp [localized_cover_descent_overMap_terminal_obj]
      rfl)
    (localized_pseudofunctorOver_presheafHom_obj_equiv
      (J := J) (U := U) T M N x)

/-- Helper for Lemma 7.26.4: the objectwise comparison between the ordinary Hom sheaf and the
owner-side Hom presheaf is a bijection on every slice object `T`. -/
private theorem localized_pseudofunctorOver_presheafHom_obj_equiv_bijective
    (T : Over U)
    (M N : Sheaf (J.over U) (Type w)) :
    Function.Bijective
      (localized_pseudofunctorOver_presheafHom_obj_equiv (J := J) (U := U) T M N) := by
  -- This is just the bijectivity of the explicit equivalence recorded above.
  exact (localized_pseudofunctorOver_presheafHom_obj_equiv
    (J := J) (U := U) T M N).bijective

/-- Helper for Lemma 7.26.4: on the ordinary slice-site Hom sheaf, restriction along
`g : T₁ ⟶ T₂` is definitionally the localized pullback functor on sheaves over `J.over U`. -/
private theorem localized_pseudofunctorOver_sheafHom_map_eq
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    ((CategoryTheory.sheafHom (J := J.over U) M N).1).map g.op x =
      ((J.over U).overMapPullback (Type w) g).map x := by
  -- `sheafHom` is implemented via `sheafHom'`, whose restriction maps are exactly these
  -- localized pullback functors.
  rfl

/-- Helper for Lemma 7.26.4: after expanding the source-side comparison at `T₁`, the left side
of the Hom-presheaf naturality equation is the iterated-slice transport of the localized pullback
map on `x`. -/
private theorem localized_pseudofunctorOver_presheafHom_obj_equiv_source_map
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    localized_pseudofunctorOver_presheafHom_obj_equiv (J := J) (U := U) T₁ M N
      (((CategoryTheory.sheafHom (J := J.over U) M N).1).map g.op x) =
      ((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
        (J := J) (U := U) T₁ M N).trans
        ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₁ M).homCongr
          (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
            (J := J) (U := U) T₁ N)))
        (((J.over U).overMapPullback (Type w) g).map x) := by
  -- Route correction: normalize the source-side restriction map before comparing it with the
  -- owner-side `pullHom`; this removes the outer `sheafHom` wrapper from the blocker.
  rw [localized_pseudofunctorOver_sheafHom_map_eq (J := J) (U := U) g M N x]
  rfl

/-- Helper for Lemma 7.26.4: on the owner-side Hom presheaf, restriction along `g : T₁ ⟶ T₂`
is already the explicit `pullHom` map along `g.left`. This isolates the target-side
normalization needed in the remaining transport comparison. -/
private theorem localized_pseudofunctorOver_presheafHom_target_map
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (y : (((J.pseudofunctorOver (Type w)).presheafHom M N).obj (Opposite.op T₂))) :
    (((J.pseudofunctorOver (Type w)).presheafHom M N).map g.op y) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom y g.left T₁.hom T₁.hom
        (by simpa using Over.w g) (by simpa using Over.w g) := by
  -- This is the defining formula for the restriction map of `Pseudofunctor.presheafHom`.
  rfl

/-- Helper for Lemma 7.26.4: after both sides of the Hom-presheaf naturality statement are
written in owner coordinates, the remaining equality is the bare transport comparison between the
iterated-slice pullback map and the owner-side `pullHom` formula. -/
private theorem localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv_underlying_left_normal_form
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    (sheafToPresheaf (J.over T₁.left) (Type w)).map
      (((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
        (J := J) (U := U) T₁ M N).trans
        ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₁ M).homCongr
          (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
            (J := J) (U := U) T₁ N)))
        (((J.over U).overMapPullback (Type w) g).map x)) =
      (Functor.isoWhiskerRight
        (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
        M.obj).inv ≫
        T₁.iteratedSliceBackward.op.whiskerLeft ((Over.map g).op.whiskerLeft x.hom) ≫
          (Functor.isoWhiskerRight
            (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
            N.obj).hom := by
  -- Normalize the objectwise equivalence and the outer comparison isomorphisms before touching
  -- the owner-side `pullHom`; this isolates the left-hand transport as a plain presheaf map.
  simp only [Equiv.trans_apply, Iso.homCongr_apply]
  rw [Functor.map_comp, Functor.map_comp,
    localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback_inv_map,
    localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback_hom_map]
  -- The remaining middle map is just the sheaf-congruence functor applied to the localized
  -- pullback morphism, so forgetting to presheaves reveals the expected whiskered natural map.
  simp only [localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv,
    Equivalence.sheafCongr, Equivalence.sheafCongr.functor,
    Functor.sheafPushforwardContinuous]
  rfl

/-- Helper for Lemma 7.26.4: after both sides of the Hom-presheaf naturality statement are
written in owner coordinates, the remaining equality is the bare transport comparison between the
iterated-slice pullback map and the owner-side `pullHom` formula. -/
private theorem localized_pseudofunctorOver_mapComp'_witness
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂) :
    T₂.hom.op.toLoc ≫ g.left.op.toLoc = T₁.hom.op.toLoc := by
  -- This is exactly `Over.w g`, translated into the `LocallyDiscrete Cᵒᵖ` coordinates used by
  -- `pseudofunctorOver.mapComp'`.
  simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
    congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op (Over.w g))

/-- Helper for Lemma 7.26.4: the owner-side `mapComp'` for the pair
`(T₂.hom, g.left)` literally splits into the equality transport from
`g.left ≫ T₂.hom = T₁.hom` followed by the strict `mapComp`. This is the stable normal form
used to isolate the two outer factors of `pullHom`. -/
private theorem localized_pseudofunctorOver_mapComp'_eq_map₂Iso_comp_mapComp
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂) :
    (J.pseudofunctorOver (Type w)).mapComp'
      T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
      (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g) =
      (J.pseudofunctorOver (Type w)).map₂Iso
        (eqToIso (by
          simpa using (localized_pseudofunctorOver_mapComp'_witness
            (T₁ := T₁) (T₂ := T₂) g).symm)) ≪≫
      (J.pseudofunctorOver (Type w)).mapComp T₂.hom.op.toLoc g.left.op.toLoc := by
  -- This is exactly the defining expansion of the flexible comparison `mapComp'`.
  simp [Pseudofunctor.mapComp']

/-- Helper for Lemma 7.26.4: after forgetting to presheaves, the source outer factor in the
owner-side `pullHom` formula is exactly the source-side component of
`J.overMapPullbackComp (Type w) g.left T₂.hom`. This records the stable owner-coordinate cast
used before comparing the middle restriction map. -/
private theorem localized_pseudofunctorOver_mapComp'_hom_owner_source_cast_type
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M : Sheaf (J.over U) (Type w)) :
    (((J.overMapPullback (Type w) (g.left ≫ T₂.hom)).obj M).obj ⟶
      ((J.overMapPullback (Type w) T₂.hom ⋙ J.overMapPullback (Type w) g.left).obj M).obj) =
      ((((J.pseudofunctorOver (Type w)).map T₁.hom.op.toLoc).toFunctor.obj M).obj ⟶
        ((((J.pseudofunctorOver (Type w)).map T₂.hom.op.toLoc ≫
          (J.pseudofunctorOver (Type w)).map g.left.op.toLoc).toFunctor.obj M).obj)) := by
  -- Unfold the owner coordinates and use `Over.w g : g.left ≫ T₂.hom = T₁.hom`.
  simpa [GrothendieckTopology.pseudofunctorOver] using
    congrArg
      (fun f =>
        ((J.overMapPullback (Type w) f).obj M).obj ⟶
          ((J.overMapPullback (Type w) T₂.hom ⋙ J.overMapPullback (Type w) g.left).obj M).obj)
      (Over.w g)

/-- Helper for Lemma 7.26.4: the target-side component of `J.overMapPullbackComp` lives on
`g.left ≫ T₂.hom`, and this theorem records the exact owner-coordinate type equality needed to
view it over `T₁.hom`. -/
private theorem localized_pseudofunctorOver_mapComp'_inv_owner_target_cast_type
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (N : Sheaf (J.over U) (Type w)) :
    (((J.overMapPullback (Type w) T₂.hom ⋙ J.overMapPullback (Type w) g.left).obj N).obj ⟶
      ((J.overMapPullback (Type w) (g.left ≫ T₂.hom)).obj N).obj) =
      (((((J.pseudofunctorOver (Type w)).map T₂.hom.op.toLoc ≫
          (J.pseudofunctorOver (Type w)).map g.left.op.toLoc).toFunctor.obj N).obj) ⟶
        (((J.pseudofunctorOver (Type w)).map T₁.hom.op.toLoc).toFunctor.obj N).obj) := by
  -- The same owner-coordinate cast uses the target equality `g.left ≫ T₂.hom = T₁.hom`.
  simpa [GrothendieckTopology.pseudofunctorOver] using
    congrArg
      (fun f =>
        ((J.overMapPullback (Type w) T₂.hom ⋙ J.overMapPullback (Type w) g.left).obj N).obj ⟶
          ((J.overMapPullback (Type w) f).obj N).obj)
      (Over.w g)

/-- Helper for Lemma 7.26.4: after forgetting the owner-side `pullHom` to presheaves, the map is
the explicit three-factor composite of the two `mapComp'` outer transports and the localized
pullback of the middle morphism. This removes hidden unfolding from the remaining transport
comparison. -/
private theorem localized_pseudofunctorOver_pullHom_underlying_normal_form
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    (sheafToPresheaf (J.over T₁.left) (Type w)).map
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (localized_pseudofunctorOver_presheafHom_obj_equiv
          (J := J) (U := U) T₂ M N x)
        g.left T₁.hom T₁.hom
        (by simpa using Over.w g) (by simpa using Over.w g)) =
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.pseudofunctorOver (Type w)).mapComp'
          T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
          (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).hom.toNatTrans.app
            M) ≫
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.overMapPullback (Type w) g.left).map
          (localized_pseudofunctorOver_presheafHom_obj_equiv
            (J := J) (U := U) T₂ M N x))) ≫
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.pseudofunctorOver (Type w)).mapComp'
          T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
          (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).inv.toNatTrans.app
            N) := by
  -- Forget `pullHom` before any owner-coordinate transport rewrites; only the two outer
  -- `mapComp'` factors and the pulled-back middle morphism remain.
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  rfl

/-! ### HEq strip toolkit for the iterated-slice transport core
These helpers collapse cast-like component applications (`eqToHom`, 2-cell `eqToHom`
components, `pseudofunctorOver.mapComp` components) to their arguments up to `HEq`,
with syntactic patterns matching the goal spellings so no defeq-unfolding is needed. -/

private theorem eqToHom_apply_heq {A B : Type w} (h : A = B) (a : A) :
    HEq ((eqToHom h) a) a := by subst h; rfl

private theorem dep_app_heq {ι : Type*} {P Q : ι → Type w} (f : ∀ i, P i → Q i)
    {i j : ι} (h : i = j) {a : P i} {b : P j} (hab : HEq a b) :
    HEq (f i a) (f j b) := by subst h; rw [eq_of_heq hab]

private theorem map_op_eqToHom_apply_heq {D : Type*} [Category D] (F : Dᵒᵖ ⥤ Type w)
    {A B : D} (φ : A ⟶ B) (h : A = B) (hφ : φ = eqToHom h) (m : F.obj (Opposite.op B)) :
    HEq (F.map φ.op m) m := by
  subst hφ; cases h; exact heq_of_eq (by simp)

private theorem over_eqToHom_left {T : Type*} [Category T] {B : T} {A A' : Over B}
    (h : A = A') : (eqToHom h).left = eqToHom (congrArg Comma.left h) := by
  subst h; rfl

private theorem sheaf2cell_eqToHom_component_apply_heq
    {𝒞 : Cat} {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    {F G : 𝒞 ⟶ Cat.of (Sheaf K (Type w))} (h : F = G) (Mo : 𝒞) (X : Dᵒᵖ)
    (m : ((F.toFunctor.obj Mo)).obj.obj X) :
    HEq ((((eqToHom h).toNatTrans.app Mo).hom.app X) m) m := by
  subst h; rfl


private theorem pf_mapComp_inv_component_apply_heq
    {a b c : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) (g' : b ⟶ c)
    (No : Sheaf (J.over (Opposite.unop a.as)) (Type w)) (X : (Over (Opposite.unop c.as))ᵒᵖ)
    (m : No.obj.obj (Opposite.op
      ((Over.map f.as.unop).obj ((Over.map g'.as.unop).obj (Opposite.unop X))))) :
    HEq (((((J.pseudofunctorOver (Type w)).mapComp f g').inv.toNatTrans.app No).hom.app X) m) m := by
  rw [GrothendieckTopology.pseudofunctorOver_mapComp_inv_toNatTrans_app_hom_app]
  have hl : ((Over.mapComp g'.as.unop f.as.unop).hom.app (Opposite.unop X)).left
      = 𝟙 (Opposite.unop X).left := by simp [Over.mapComp]
  have hAB : ((Over.map (g'.as.unop ≫ f.as.unop)).obj (Opposite.unop X))
      = (Over.map f.as.unop).obj ((Over.map g'.as.unop).obj (Opposite.unop X)) :=
    (congrArg Over.mk (Category.assoc (Opposite.unop X).hom g'.as.unop f.as.unop)).symm
  exact map_op_eqToHom_apply_heq No.obj _ hAB
    (Over.OverMorphism.ext
      (hl.trans (((over_eqToHom_left hAB).trans
        (eqToHom_refl (Opposite.unop X).left _)).symm))) m

private theorem pf_mapComp_hom_component_apply_heq
    {a b c : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) (g' : b ⟶ c)
    (Mo : Sheaf (J.over (Opposite.unop a.as)) (Type w)) (X : (Over (Opposite.unop c.as))ᵒᵖ)
    (m : Mo.obj.obj (Opposite.op
      ((Over.map (g'.as.unop ≫ f.as.unop)).obj (Opposite.unop X)))) :
    HEq (((((J.pseudofunctorOver (Type w)).mapComp f g').hom.toNatTrans.app Mo).hom.app X) m) m := by
  rw [GrothendieckTopology.pseudofunctorOver_mapComp_hom_toNatTrans_app_hom_app]
  have hl : ((Over.mapComp g'.as.unop f.as.unop).inv.app (Opposite.unop X)).left
      = 𝟙 (Opposite.unop X).left := by simp [Over.mapComp]
  have hBA : ((Over.map f.as.unop).obj ((Over.map g'.as.unop).obj (Opposite.unop X)))
      = (Over.map (g'.as.unop ≫ f.as.unop)).obj (Opposite.unop X) :=
    congrArg Over.mk (Category.assoc (Opposite.unop X).hom g'.as.unop f.as.unop)
  exact map_op_eqToHom_apply_heq Mo.obj _ hBA
    (Over.OverMorphism.ext
      (hl.trans (((over_eqToHom_left hBA).trans
        (eqToHom_refl (Opposite.unop X).left _)).symm))) m


private theorem over_mk_hext {𝒞 : Type*} [Category 𝒞] {B : 𝒞} {Y₁ Y₂ : 𝒞}
    (hY : Y₁ = Y₂) (f₁ : Y₁ ⟶ B) (f₂ : Y₂ ⟶ B) (hf : HEq f₁ f₂) :
    Over.mk f₁ = Over.mk f₂ := by subst hY; rw [eq_of_heq hf]

private theorem hom_heq_of_left_eq {T : Type*} [Category T] {B : T} {U₁ U₂ V : Over B}
    (hU : U₁ = U₂) (k₁ : U₁ ⟶ V) (k₂ : U₂ ⟶ V) (hk : HEq k₁.left k₂.left) :
    HEq k₁ k₂ := by
  subst hU; exact heq_of_eq (Over.OverMorphism.ext (eq_of_heq hk))

set_option maxHeartbeats 4000000 in
/-- Helper for Lemma 7.26.4: the iterated-slice whisker form of the transported section
equals the three-factor owner transport composite. This is the mathematical core of the
naturality square, proved elementwise by an `HEq` chain through `x.hom` at the two
canonically equal slice objects. -/
private theorem localized_pseudofunctorOver_whisker_transport_core
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    (Functor.isoWhiskerRight
      (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
      M.obj).inv ≫
      T₁.iteratedSliceBackward.op.whiskerLeft ((Over.map g).op.whiskerLeft x.hom) ≫
        (Functor.isoWhiskerRight
          (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
          N.obj).hom =
    (sheafToPresheaf (J.over T₁.left) (Type w)).map
      (((J.pseudofunctorOver (Type w)).mapComp'
        T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
        (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).hom.toNatTrans.app
          M) ≫
    (sheafToPresheaf (J.over T₁.left) (Type w)).map
      (((J.overMapPullback (Type w) g.left).map
        (localized_pseudofunctorOver_presheafHom_obj_equiv
          (J := J) (U := U) T₂ M N x))) ≫
    (sheafToPresheaf (J.over T₁.left) (Type w)).map
      (((J.pseudofunctorOver (Type w)).mapComp'
        T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
        (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).inv.toNatTrans.app
          N) := by
  -- hmid: 619-mirror at T₂ with the chain spelled out syntactically (so trans_apply fires)
  have hmid : (sheafToPresheaf (J.over T₂.left) (Type w)).map
      (((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
        (J := J) (U := U) T₂ M N).trans
        ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₂ M).homCongr
          (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
            (J := J) (U := U) T₂ N)))
        x) =
      (Functor.isoWhiskerRight
        (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₂)))
        M.obj).inv ≫
        T₂.iteratedSliceBackward.op.whiskerLeft x.hom ≫
          (Functor.isoWhiskerRight
            (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₂)))
            N.obj).hom := by
    simp only [Equiv.trans_apply, Iso.homCongr_apply]
    rw [Functor.map_comp, Functor.map_comp,
      localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback_inv_map,
      localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback_hom_map]
    simp only [localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv,
      Equivalence.sheafCongr, Equivalence.sheafCongr.functor,
      Functor.sheafPushforwardContinuous]
    rfl
  -- defeq bridge: F2 = whiskeringLeft-image of the chain's presheaf shadow
  have hF2 : (sheafToPresheaf (J.over T₁.left) (Type w)).map
      ((J.overMapPullback (Type w) g.left).map
        (localized_pseudofunctorOver_presheafHom_obj_equiv (J := J) (U := U) T₂ M N x)) =
      ((Functor.whiskeringLeft (Over T₁.left)ᵒᵖ (Over T₂.left)ᵒᵖ (Type w)).obj
        (Over.map g.left).op).map
        ((sheafToPresheaf (J.over T₂.left) (Type w)).map
          (((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
            (J := J) (U := U) T₂ M N).trans
            ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
              (J := J) (U := U) T₂ M).homCongr
              (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
                (J := J) (U := U) T₂ N)))
            x)) := rfl
  have h2 := hF2.trans (congrArg
    (((Functor.whiskeringLeft (Over T₁.left)ᵒᵖ (Over T₂.left)ᵒᵖ (Type w)).obj
      (Over.map g.left).op).map) hmid)
  refine Eq.trans ?core (congrArg (fun k ↦
    (sheafToPresheaf (J.over T₁.left) (Type w)).map
      (((J.pseudofunctorOver (Type w)).mapComp'
        T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
        (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).hom.toNatTrans.app
          M) ≫ k ≫
    (sheafToPresheaf (J.over T₁.left) (Type w)).map
      (((J.pseudofunctorOver (Type w)).mapComp'
        T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
        (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).inv.toNatTrans.app
          N)) h2).symm
  -- core: pure whisker/eqToHom identity, all factors concrete
  ext X a
  simp [Pseudofunctor.mapComp',
    GrothendieckTopology.pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_map₂,
    eqToHom_map, eqToHom_app]
  apply eq_of_heq
  refine HEq.trans (b := x.hom.app
      (Opposite.op (Over.mk (Over.homMk
        (U := Over.mk (((Opposite.unop X).hom ≫ g.left) ≫ T₂.hom))
        ((Opposite.unop X).hom ≫ g.left) rfl)))
      (eqToHom (congrArg M.obj.obj (Functor.congr_obj
          (Eq.symm (congrArg Functor.op (Over.iteratedSliceBackward_forget T₂)))
          (Opposite.op ((Over.map g.left).obj (Opposite.unop X)))))
        ((((J.pseudofunctorOver (Type w)).mapComp
            T₂.hom.op.toLoc g.left.op.toLoc).hom.toNatTrans.app M).hom.app X
          (((eqToHom (congrArg (fun k => (J.pseudofunctorOver (Type w)).map k)
                ((localized_pseudofunctorOver_mapComp'_witness
                  (T₁ := T₁) (T₂ := T₂) g).symm))).toNatTrans.app M).hom.app X a)))) ?hl ?hr
  case hl =>
    refine HEq.trans (eqToHom_apply_heq _ _) ?_
    refine dep_app_heq x.hom.app ?ho ?ha
    case ho =>
      exact congrArg Opposite.op (over_mk_hext
        (congrArg Over.mk ((congrArg (fun k => (Opposite.unop X).hom ≫ k) (Over.w g)).symm.trans
          (Category.assoc _ _ _).symm)) _ _
        (hom_heq_of_left_eq
          (congrArg Over.mk ((congrArg (fun k => (Opposite.unop X).hom ≫ k) (Over.w g)).symm.trans
            (Category.assoc _ _ _).symm)) _ _ (by simp)))
    case ha =>
      refine HEq.trans (eqToHom_apply_heq _ _) (HEq.symm ?_)
      refine HEq.trans (eqToHom_apply_heq _ _) ?_
      refine HEq.trans (pf_mapComp_hom_component_apply_heq T₂.hom.op.toLoc g.left.op.toLoc M X _) ?_
      exact sheaf2cell_eqToHom_component_apply_heq _ _ _ _
  case hr =>
    exact ((sheaf2cell_eqToHom_component_apply_heq _ _ _ _).trans
      ((pf_mapComp_inv_component_apply_heq T₂.hom.op.toLoc g.left.op.toLoc N X _).trans
        (eqToHom_apply_heq _ _))).symm

/-- Helper for Lemma 7.26.4: after both sides of the Hom-presheaf naturality statement are
written in owner coordinates, the remaining equality is the bare transport comparison between the
iterated-slice pullback map and the owner-side `pullHom` formula. -/
private theorem localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv_underlying_left_normal_form_app
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left) :
    ((sheafToPresheaf (J.over T₁.left) (Type w)).map
      (((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
        (J := J) (U := U) T₁ M N).trans
        ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₁ M).homCongr
          (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
            (J := J) (U := U) T₁ N)))
        (((J.over U).overMapPullback (Type w) g).map x))).app (Opposite.op X) =
      (((Functor.isoWhiskerRight
        (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
        M.obj).inv ≫
          T₁.iteratedSliceBackward.op.whiskerLeft ((Over.map g).op.whiskerLeft x.hom) ≫
            (Functor.isoWhiskerRight
              (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
              N.obj).hom).app (Opposite.op X)) := by
  -- Specialize the already-proved natural-transformation normal form at the chosen slice object.
  exact congrArg (fun α ↦ α.app (Opposite.op X))
    (localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv_underlying_left_normal_form
      (J := J) (U := U) g M N x)

/-- Helper for Lemma 7.26.4: the forgotten owner-side `pullHom` normal form can be specialized to
one slice object `X`, yielding the three-factor owner composite used later in the transport
comparison. -/
private theorem localized_pseudofunctorOver_pullHom_underlying_normal_form_app
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left) :
    ((sheafToPresheaf (J.over T₁.left) (Type w)).map
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (localized_pseudofunctorOver_presheafHom_obj_equiv
          (J := J) (U := U) T₂ M N x)
        g.left T₁.hom T₁.hom
        (by simpa using Over.w g) (by simpa using Over.w g))).app (Opposite.op X) =
      (((sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.pseudofunctorOver (Type w)).mapComp'
          T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
          (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).hom.toNatTrans.app
            M) ≫
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.overMapPullback (Type w) g.left).map
          (localized_pseudofunctorOver_presheafHom_obj_equiv
            (J := J) (U := U) T₂ M N x))) ≫
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.pseudofunctorOver (Type w)).mapComp'
          T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
          (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).inv.toNatTrans.app
            N)).app (Opposite.op X)) := by
  -- Specialize the forgotten `pullHom` normal form at the chosen slice object.
  exact congrArg (fun α ↦ α.app (Opposite.op X))
    (localized_pseudofunctorOver_pullHom_underlying_normal_form
      (J := J) (U := U) g M N x)

/-- Helper for Lemma 7.26.4: after both sides of the Hom-presheaf naturality statement are
written in owner coordinates, the remaining equality is the bare transport comparison between the
iterated-slice pullback map and the owner-side `pullHom` formula. -/
private noncomputable abbrev localized_pseudofunctorOver_transport_source_app
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left) :=
  ((sheafToPresheaf (J.over T₁.left) (Type w)).map
    (((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
      (J := J) (U := U) T₁ M N).trans
      ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
        (J := J) (U := U) T₁ M).homCongr
        (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₁ N)))
      (((J.over U).overMapPullback (Type w) g).map x))).app (Opposite.op X)

/-- Helper for Lemma 7.26.4: this is the reduced owner-side `pullHom` component appearing after
the normal-form rewrites for the remaining prestack transport comparison. -/
private noncomputable abbrev localized_pseudofunctorOver_transport_target_app
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left) :=
  ((sheafToPresheaf (J.over T₁.left) (Type w)).map
    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (localized_pseudofunctorOver_presheafHom_obj_equiv
        (J := J) (U := U) T₂ M N x)
      g.left T₁.hom T₁.hom
      (by simpa using Over.w g) (by simpa using Over.w g))).app (Opposite.op X)

/-- Helper for Lemma 7.26.4: rewriting the two outer `mapComp'` factors in the owner-side
`pullHom` formula by the strict `mapComp` comparison isolates the canonical three-factor owner
transport used in the remaining componentwise blocker. -/
private noncomputable abbrev localized_pseudofunctorOver_owner_transport_hom
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :=
  let hmap :
      (J.pseudofunctorOver (Type w)).map T₁.hom.op.toLoc =
        (J.pseudofunctorOver (Type w)).map (T₂.hom.op.toLoc ≫ g.left.op.toLoc) := by
    simpa using congrArg ((J.pseudofunctorOver (Type w)).map)
      (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g).symm
  (((eqToIso hmap ≪≫
      (J.pseudofunctorOver (Type w)).mapComp T₂.hom.op.toLoc g.left.op.toLoc).hom.toNatTrans.app
        M) ≫
    (J.overMapPullback (Type w) g.left).map
      (localized_pseudofunctorOver_presheafHom_obj_equiv
        (J := J) (U := U) T₂ M N x) ≫
    ((eqToIso hmap ≪≫
      (J.pseudofunctorOver (Type w)).mapComp T₂.hom.op.toLoc g.left.op.toLoc).inv.toNatTrans.app
        N))

/-- Helper for Lemma 7.26.4: evaluating the canonical owner-side three-factor transport at a
chosen slice object `X` recovers the section-level map used in the reduced target comparison. -/
private noncomputable abbrev localized_pseudofunctorOver_owner_transport_app
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left) :=
  ((sheafToPresheaf (J.over T₁.left) (Type w)).map
    (localized_pseudofunctorOver_owner_transport_hom
      (J := J) (U := U) g M N x)).app (Opposite.op X)

/-- Helper for Lemma 7.26.4: rewriting the two outer `mapComp'` factors in the owner-side
`pullHom` formula by the strict `mapComp` comparison isolates the canonical three-factor owner
transport used in the remaining componentwise blocker. -/
private theorem localized_pseudofunctorOver_transport_target_app_eq_owner_transport
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left) :
    localized_pseudofunctorOver_transport_target_app (J := J) (U := U) g M N x X =
      localized_pseudofunctorOver_owner_transport_app (J := J) (U := U) g M N x X := by
  -- Replace both flexible `mapComp'` transports by the strict `mapComp` normal form once, so
  -- the remaining blocker can target a single canonical owner-side composite.
  simpa [localized_pseudofunctorOver_transport_target_app,
    localized_pseudofunctorOver_owner_transport_app,
    localized_pseudofunctorOver_mapComp'_eq_map₂Iso_comp_mapComp] using
    localized_pseudofunctorOver_pullHom_underlying_normal_form_app
      (J := J) (U := U) g M N x X

/-- Helper for Lemma 7.26.4: after expressing the source-side comparison in owner coordinates,
the iterated-slice transport is already the same canonical owner transport used on the target
side. This isolates the source half of the remaining transport/coercion normalization. -/
private theorem localized_pseudofunctorOver_overMapCompPresheafHomIso_hom_naturality_over_homMk
    (T : Over U)
    (M N : Sheaf (J.over U) (Type w))
    (y : (((Over.map T.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
      (Opposite.op (Over.mk (𝟙 T.left)))))
    (X : Over T.left) :
    ((Pseudofunctor.overMapCompPresheafHomIso
      (F := J.pseudofunctorOver (Type w)) (M := M) (N := N) T.hom).hom.app
        (Opposite.op X))
      ((((Over.map T.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).map
        (Opposite.op (show X ⟶ Over.mk (𝟙 T.left) from Over.homMk X.hom (by simp))) y)) =
      (((J.pseudofunctorOver (Type w)).presheafHom
        (((J.pseudofunctorOver (Type w)).map T.hom.op.toLoc).toFunctor.obj M)
        (((J.pseudofunctorOver (Type w)).map T.hom.op.toLoc).toFunctor.obj N)).map
        (Opposite.op (show X ⟶ Over.mk (𝟙 T.left) from Over.homMk X.hom (by simp)))
        (((Pseudofunctor.overMapCompPresheafHomIso
          (F := J.pseudofunctorOver (Type w)) (M := M) (N := N) T.hom).hom.app
            (Opposite.op (Over.mk (𝟙 T.left)))) y)) := by
  -- This is exactly the naturality square of `overMapCompPresheafHomIso`, specialized to the
  -- terminal-arrow morphism `Over.homMk X.hom : X ⟶ Over.mk (𝟙 T.left)`.
  simpa using congrFun
    ((Pseudofunctor.overMapCompPresheafHomIso
      (F := J.pseudofunctorOver (Type w)) (M := M) (N := N) T.hom).hom.naturality
        (Opposite.op (show X ⟶ Over.mk (𝟙 T.left) from Over.homMk X.hom (by simp)))) y

/-- Helper for Lemma 7.26.4: to prove the remaining source-versus-target component comparison at
`X`, it suffices to compare the two explicit normal forms already isolated earlier in the file.
This packages the reduction from the abbreviated transport maps to the raw component equality. -/
private theorem localized_pseudofunctorOver_transport_app_eq_of_underlying_normal_forms
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left)
    (h :
      (((Functor.isoWhiskerRight
        (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
        M.obj).inv ≫
          T₁.iteratedSliceBackward.op.whiskerLeft ((Over.map g).op.whiskerLeft x.hom) ≫
            (Functor.isoWhiskerRight
              (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
              N.obj).hom).app (Opposite.op X)) =
        (((sheafToPresheaf (J.over T₁.left) (Type w)).map
          (((J.pseudofunctorOver (Type w)).mapComp'
            T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
            (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).hom.toNatTrans.app
              M) ≫
        (sheafToPresheaf (J.over T₁.left) (Type w)).map
          (((J.overMapPullback (Type w) g.left).map
            (localized_pseudofunctorOver_presheafHom_obj_equiv
              (J := J) (U := U) T₂ M N x))) ≫
        (sheafToPresheaf (J.over T₁.left) (Type w)).map
          (((J.pseudofunctorOver (Type w)).mapComp'
            T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
            (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).inv.toNatTrans.app
              N)).app (Opposite.op X))) :
    localized_pseudofunctorOver_transport_source_app (J := J) (U := U) g M N x X =
      localized_pseudofunctorOver_transport_target_app (J := J) (U := U) g M N x X := by
  -- Rewrite both abbreviations to the earlier explicit normal forms and splice in the supplied
  -- component equality between those normal forms.
  simpa [localized_pseudofunctorOver_transport_source_app,
    localized_pseudofunctorOver_transport_target_app] using
    ((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv_underlying_left_normal_form_app
      (J := J) (U := U) g M N x X).symm.trans
      (h.trans
        (localized_pseudofunctorOver_pullHom_underlying_normal_form_app
          (J := J) (U := U) g M N x X).symm))

/-- Helper for Lemma 7.26.4: after expressing the source-side comparison in owner coordinates,
the iterated-slice transport is already the same canonical owner transport used on the target
side. This isolates the source half of the remaining transport/coercion normalization. -/
private noncomputable abbrev localized_pseudofunctorOver_source_terminal_transport_hom
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    ((J.overMapPullback (Type w) T₁.hom).obj M) ⟶ ((J.overMapPullback (Type w) T₁.hom).obj N) :=
  (Pseudofunctor.presheafHomObjHomEquiv (F := J.pseudofunctorOver (Type w)) (S := T₁.left)).symm
    (((Pseudofunctor.overMapCompPresheafHomIso
      (F := J.pseudofunctorOver (Type w)) (M := M) (N := N) T₁.hom).hom.app
        (Opposite.op (Over.mk (𝟙 T₁.left))))
      (localized_pseudofunctorOver_presheafHom_obj_equiv_owner_source
        (J := J) (U := U) T₁ M N (((CategoryTheory.sheafHom (J := J.over U) M N).1).map g.op x)))

/-- Helper for Lemma 7.26.4: the owner-side `pullHom` comparison already agrees, as a sheaf
morphism, with the canonical three-factor owner transport. This packages the target-side
normalization once, so the remaining transport blocker is purely on the source side. -/
private theorem localized_pseudofunctorOver_pullHom_eq_owner_transport_hom
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (localized_pseudofunctorOver_presheafHom_obj_equiv
        (J := J) (U := U) T₂ M N x)
      g.left T₁.hom T₁.hom
      (by simpa using Over.w g) (by simpa using Over.w g) =
      localized_pseudofunctorOver_owner_transport_hom
        (J := J) (U := U) g M N x := by
  -- Compare the two sheaf morphisms after forgetting to presheaves and evaluating componentwise;
  -- the objectwise equality is exactly `transport_target_app_eq_owner_transport`.
  apply (sheafToPresheaf (J.over T₁.left) (Type w)).map_injective
  ext X a
  exact congrFun
    (localized_pseudofunctorOver_transport_target_app_eq_owner_transport
      (J := J) (U := U) g M N x X.unop) a

/-- Helper for Lemma 7.26.4: the terminal-source cast used to regard a section over
`(Over.map T.hom).obj (Over.mk (𝟙 T.left))` as a section over `Over.mk T.hom` preserves
equalities. This isolates the cast layer that blocks the remaining terminal-component proof. -/
private theorem localized_pseudofunctorOver_terminal_source_cast_congr
    {T : Over U}
    (M N : Sheaf (J.over U) (Type w))
    (e :
      (((J.pseudofunctorOver (Type w)).presheafHom M N).obj (Opposite.op T)) =
        (((Over.map T.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
          (Opposite.op (Over.mk (𝟙 T.left)))))
    {x y :
      (((J.pseudofunctorOver (Type w)).presheafHom M N).obj (Opposite.op T))}
    (h : x = y) :
    cast e x = cast e y := by
  -- The owner-source terminal cast is functorial in the transported section.
  cases h
  rfl

/-- Helper for Lemma 7.26.4: once the terminal source object is fixed, applying the terminal
component of `overMapCompPresheafHomIso` and then the base-point equivalence preserves equality
of source sections. -/
private theorem localized_pseudofunctorOver_terminal_component_congr
    {T : Over U}
    (M N : Sheaf (J.over U) (Type w))
    {x y :
      (((Over.map T.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
        (Opposite.op (Over.mk (𝟙 T.left))))}
    (h : x = y) :
    (Pseudofunctor.presheafHomObjHomEquiv (F := J.pseudofunctorOver (Type w))
        (S := T.left)).symm
      (((Pseudofunctor.overMapCompPresheafHomIso
        (F := J.pseudofunctorOver (Type w)) (M := M) (N := N) T.hom).hom.app
          (Opposite.op (Over.mk (𝟙 T.left)))) x) =
      (Pseudofunctor.presheafHomObjHomEquiv (F := J.pseudofunctorOver (Type w))
        (S := T.left)).symm
      (((Pseudofunctor.overMapCompPresheafHomIso
        (F := J.pseudofunctorOver (Type w)) (M := M) (N := N) T.hom).hom.app
          (Opposite.op (Over.mk (𝟙 T.left)))) y) := by
  -- The remaining terminal comparison is honest function application after the cast has been
  -- normalized, so equality propagates directly.
  cases h
  rfl

/-- Helper for Lemma 7.26.4: the terminal source fiber of the restricted Hom presheaf over
`T.hom` is literally the morphism type between the two pulled-back sheaves along `T.hom`. This
packages the source-fiber cast in a transport-stable form before the raw terminal-component
computation. -/
private theorem localized_pseudofunctorOver_terminal_source_fiber_eq_mapObjHom
    {T : Over U}
    (M N : Sheaf (J.over U) (Type w)) :
    (((Over.map T.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
      (Opposite.op (Over.mk (𝟙 T.left)))) =
      ((((J.pseudofunctorOver (Type w)).map T.hom.op.toLoc).toFunctor.obj M) ⟶
        (((J.pseudofunctorOver (Type w)).map T.hom.op.toLoc).toFunctor.obj N)) := by
  -- Expose `T`; then both sides are exactly the same pulled-back Hom type by definition of
  -- `Pseudofunctor.presheafHom` and the terminal object of the slice over `T.left`.
  cases T
  simp [Pseudofunctor.presheafHom]
  rfl

/-- Helper for Lemma 7.26.4: the source section over `T : Over U` and the terminal-source
section over `Over.mk (𝟙 T.left)` for the restricted Hom presheaf have the same underlying type.
This isolates the exact cast that appears in the remaining terminal-component normalization. -/
private theorem localized_pseudofunctorOver_terminal_source_type_eq
    {T : Over U}
    (M N : Sheaf (J.over U) (Type w)) :
    (((J.pseudofunctorOver (Type w)).presheafHom M N).obj (Opposite.op T)) =
      (((Over.map T.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
        (Opposite.op (Over.mk (𝟙 T.left)))) := by
  -- Route correction: identify both source fibers with the same pulled-back Hom type, rather
  -- than reopening the restricted functor every time the terminal-source cast appears.
  trans ((((J.pseudofunctorOver (Type w)).map T.hom.op.toLoc).toFunctor.obj M) ⟶
      (((J.pseudofunctorOver (Type w)).map T.hom.op.toLoc).toFunctor.obj N))
  · -- The direct source fiber is the defining value of `presheafHom` at `T`.
    cases T
    simp [Pseudofunctor.presheafHom]
  · -- The restricted terminal-source fiber is the same pulled-back Hom type by the new stable
    -- terminal-fiber identification.
    exact
      (localized_pseudofunctorOver_terminal_source_fiber_eq_mapObjHom
        (J := J) (U := U) (T := T) M N).symm

/-- Helper for Lemma 7.26.4: the terminal-source type equality can also be used in the reverse
direction when the raw terminal-component computation is converted back to the original source
fiber. -/
private theorem localized_pseudofunctorOver_terminal_source_type_eq_symm
    {T : Over U}
    (M N : Sheaf (J.over U) (Type w)) :
    (((Over.map T.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
      (Opposite.op (Over.mk (𝟙 T.left)))) =
      (((J.pseudofunctorOver (Type w)).presheafHom M N).obj (Opposite.op T)) := by
  -- Reuse the forward identification and reverse it once, so later proofs avoid ad hoc casts.
  simpa using
    (localized_pseudofunctorOver_terminal_source_type_eq
      (J := J) (U := U) (T := T) M N).symm

/-- Helper for Lemma 7.26.4: casting a terminal restricted source section along the stable
terminal-fiber identification does not change the underlying morphism after exposing `T`; the
result is heterogeneously equal to the original section. This records the transport layer needed
before comparing the terminal component itself. -/
private theorem localized_pseudofunctorOver_terminal_source_fiber_cast_heq
    {T : Over U}
    (M N : Sheaf (J.over U) (Type w))
    (z :
      (((Over.map T.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
        (Opposite.op (Over.mk (𝟙 T.left))))) :
    HEq
      (cast
      (localized_pseudofunctorOver_terminal_source_fiber_eq_mapObjHom
        (J := J) (U := U) (T := T) M N)
      z)
      z := by
  -- After exposing `T`, the cast is the identity on the literal pulled-back Hom type.
  cases T
  simp [Pseudofunctor.presheafHom]

/-- The 2-cell `eqToHom` between parallel `Cat`-morphisms evaluates objectwise to the canonical
transport. -/
private theorem cat_hom₂_eqToHom_app.{v₁, u₁} {A B : Cat.{v₁, u₁}} {f g : A ⟶ B}
    (h : f = g) (X : A) :
    (eqToHom h).toNatTrans.app X = eqToHom (congrArg (fun k ↦ k.toFunctor.obj X) h) := by
  cases h
  rfl

/-- Casting a morphism along Hom-type equalities induced by object equalities is conjugation by
the canonical transports. -/
private theorem cast_hom_eq_conj {𝒜 : Type*} [Category 𝒜] {A B A' B' : 𝒜}
    (hA : A = A') (hB : B = B')
    (h : (A ⟶ B) = (A' ⟶ B')) (f : A ⟶ B) :
    cast h f = eqToHom hA.symm ≫ f ≫ eqToHom hB := by
  cases hA
  cases hB
  exact ((Category.id_comp _).trans (Category.comp_id f)).symm

/-- The canonical conjugation chain by identity-collapse cells and transports equals the
type-level cast; all bicategorical content enters through the hypotheses. -/
private theorem conj_chain_eq_cast {𝒜 : Type*} [Category 𝒜]
    {Pm P0 Pq Qq Qm Q0 : 𝒜}
    (sInv : Pm ⟶ P0) (tHom : Q0 ⟶ Qm)
    (Aapp : P0 ⟶ Pq) (Bapp : Qq ⟶ Q0) (z : Pq ⟶ Qq)
    (a1 : P0 ⟶ Pm) (a2 : Pm ⟶ Pm) (a3 : Pm ⟶ Pq)
    (b2 : Qq ⟶ Qm) (b3 : Qm ⟶ Qm) (b4 : Qm ⟶ Q0)
    (hPa : Pm = Pq) (hQb : Qq = Qm)
    (hA : Aapp = (a1 ≫ a2 ≫ a3) ≫ 𝟙 Pq)
    (hB : Bapp = 𝟙 Qq ≫ b2 ≫ b3 ≫ b4)
    (ha2 : a2 = 𝟙 Pm) (hb3 : b3 = 𝟙 Qm)
    (ha3 : a3 = eqToHom hPa) (hb2 : b2 = eqToHom hQb)
    (hsa : sInv ≫ a1 = 𝟙 Pm) (hbt : b4 ≫ tHom = 𝟙 Qm)
    (hcast : (Pq ⟶ Qq) = (Pm ⟶ Qm)) :
    sInv ≫ ((Aapp ≫ z) ≫ Bapp) ≫ tHom = cast hcast z := by
  subst hA hB ha2 hb3 ha3 hb2
  rw [cast_hom_eq_conj hPa.symm hQb hcast z]
  subst hPa
  subst hQb
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp, Category.assoc]
  calc
    sInv ≫ a1 ≫ z ≫ b4 ≫ tHom
        = (sInv ≫ a1) ≫ z ≫ b4 ≫ tHom := (Category.assoc _ _ _).symm
    _ = 𝟙 _ ≫ z ≫ b4 ≫ tHom := congrArg (fun k ↦ k ≫ z ≫ b4 ≫ tHom) hsa
    _ = z ≫ b4 ≫ tHom := Category.id_comp _
    _ = z ≫ 𝟙 _ := congrArg (fun k ↦ z ≫ k) hbt
    _ = z := Category.comp_id z

/-- Helper for Lemma 7.26.4: after moving to the literal terminal-source fiber of
`(Over.map T.hom).op ⋙ presheafHom`, the terminal component of `overMapCompPresheafHomIso`
computes to the reverse type cast back to the original source fiber. -/
private theorem localized_pseudofunctorOver_terminal_component_apply_cast_eq_raw
    {T : Over U}
    (M N : Sheaf (J.over U) (Type w))
    (z :
      (((Over.map T.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
        (Opposite.op (Over.mk (𝟙 T.left))))) :
    (Pseudofunctor.presheafHomObjHomEquiv (F := (J.pseudofunctorOver (Type w)))
        (S := T.left)).symm
      (((Pseudofunctor.overMapCompPresheafHomIso
        (F := (J.pseudofunctorOver (Type w))) (M := M) (N := N) T.hom).hom.app
          (Opposite.op (Over.mk (𝟙 T.left)))) z) =
      cast
        (localized_pseudofunctorOver_terminal_source_type_eq_symm
          (J := J) (U := U) (T := T) M N)
        z := by
  obtain ⟨Tl, Tr, Th⟩ := T
  simp [Pseudofunctor.overMapCompPresheafHomIso, Pseudofunctor.presheafHomObjHomEquiv,
    Pseudofunctor.presheafHom, Pseudofunctor.mapComp', Pseudofunctor.mapComp_id_right,
    Iso.homCongr, Iso.homFromEquiv, Iso.homToEquiv, Cat.Hom.toNatIso, eqToHom_map,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.Hom₂.comp_app, Cat.Hom₂.id_app, eqToHom_app]
  have h₁ : ((J.pseudofunctorOver (Type w)).map Th.op.toLoc) =
      ((J.pseudofunctorOver (Type w)).map (Th.op.toLoc ≫ 𝟙 (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ))) :=
    congrArg (fun k ↦ (J.pseudofunctorOver (Type w)).map k) (Category.comp_id Th.op.toLoc).symm
  have h₂ : ((J.pseudofunctorOver (Type w)).map (Th.op.toLoc ≫ 𝟙 (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ))) =
      ((J.pseudofunctorOver (Type w)).map Th.op.toLoc) := h₁.symm
  exact conj_chain_eq_cast
    (sInv := ((J.pseudofunctorOver (Type w)).mapId (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ)).inv.toNatTrans.app
      (((J.pseudofunctorOver (Type w)).map Th.op.toLoc).toFunctor.obj M))
    (tHom := ((J.pseudofunctorOver (Type w)).mapId (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ)).hom.toNatTrans.app
      (((J.pseudofunctorOver (Type w)).map Th.op.toLoc).toFunctor.obj N))
    (Aapp := ((Bicategory.whiskerLeft ((J.pseudofunctorOver (Type w)).map Th.op.toLoc)
          ((J.pseudofunctorOver (Type w)).mapId (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ)).hom ≫
        (Bicategory.rightUnitor ((J.pseudofunctorOver (Type w)).map Th.op.toLoc)).hom ≫
          eqToHom h₁) ≫
        𝟙 ((J.pseudofunctorOver (Type w)).map (Th.op.toLoc ≫ 𝟙 (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ)))).toNatTrans.app M)
    (Bapp := ((𝟙 ((J.pseudofunctorOver (Type w)).map (Th.op.toLoc ≫ 𝟙 (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ))) ≫
        eqToHom h₂ ≫
          (Bicategory.rightUnitor ((J.pseudofunctorOver (Type w)).map Th.op.toLoc)).inv ≫
            Bicategory.whiskerLeft ((J.pseudofunctorOver (Type w)).map Th.op.toLoc)
              ((J.pseudofunctorOver (Type w)).mapId (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ)).inv).toNatTrans.app N))
    (z := z)
    (a1 := ((J.pseudofunctorOver (Type w)).mapId (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ)).hom.toNatTrans.app
      (((J.pseudofunctorOver (Type w)).map Th.op.toLoc).toFunctor.obj M))
    (a2 := (Bicategory.rightUnitor ((J.pseudofunctorOver (Type w)).map Th.op.toLoc)).hom.toNatTrans.app M)
    (a3 := (eqToHom h₁).toNatTrans.app M)
    (b2 := (eqToHom h₂).toNatTrans.app N)
    (b3 := (Bicategory.rightUnitor ((J.pseudofunctorOver (Type w)).map Th.op.toLoc)).inv.toNatTrans.app N)
    (b4 := ((J.pseudofunctorOver (Type w)).mapId (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ)).inv.toNatTrans.app
      (((J.pseudofunctorOver (Type w)).map Th.op.toLoc).toFunctor.obj N))
    (hPa := congrArg (fun k ↦ k.toFunctor.obj M) h₁)
    (hQb := congrArg (fun k ↦ k.toFunctor.obj N) h₂)
    (hA := rfl) (hB := rfl)
    (ha2 := rfl) (hb3 := rfl)
    (ha3 := cat_hom₂_eqToHom_app h₁ M) (hb2 := cat_hom₂_eqToHom_app h₂ N)
    (hsa := congrArg
      (fun α ↦ α.toNatTrans.app (((J.pseudofunctorOver (Type w)).map Th.op.toLoc).toFunctor.obj M))
      (((J.pseudofunctorOver (Type w)).mapId (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ)).inv_hom_id))
    (hbt := congrArg
      (fun α ↦ α.toNatTrans.app (((J.pseudofunctorOver (Type w)).map Th.op.toLoc).toFunctor.obj N))
      (((J.pseudofunctorOver (Type w)).mapId (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ)).inv_hom_id))
    (hcast := localized_pseudofunctorOver_terminal_source_type_eq_symm
      (J := J) (U := U) (T := ⟨Tl, Tr, Th⟩) M N)

/-- Helper for Lemma 7.26.4: eliminating the owner-source cast at the terminal object reduces
the terminal component of `overMapCompPresheafHomIso` to the original section. -/
private theorem localized_pseudofunctorOver_terminal_component_apply_cast_eq
    {T : Over U}
    (M N : Sheaf (J.over U) (Type w))
    (z : (((J.pseudofunctorOver (Type w)).presheafHom M N).obj (Opposite.op T))) :
    (Pseudofunctor.presheafHomObjHomEquiv (F := J.pseudofunctorOver (Type w))
        (S := T.left)).symm
      (((Pseudofunctor.overMapCompPresheafHomIso
        (F := J.pseudofunctorOver (Type w)) (M := M) (N := N) T.hom).hom.app
          (Opposite.op (Over.mk (𝟙 T.left))))
        (Eq.mp
          (localized_pseudofunctorOver_terminal_source_type_eq
            (J := J) (U := U) (T := T) M N)
          z)) =
      z := by
  -- First compute the terminal component in the literal terminal-source fiber, so the only
  -- remaining cast is the inverse type cast back to the original source section.
  have hraw :=
    localized_pseudofunctorOver_terminal_component_apply_cast_eq_raw
      (J := J) (U := U) (T := T) (M := M) (N := N)
      (Eq.mp
        (localized_pseudofunctorOver_terminal_source_type_eq
          (J := J) (U := U) (T := T) M N)
        z)
  -- The forward and reverse terminal-source casts cancel definitionally after exposing `T`.
  have hcancel :
      cast
          (localized_pseudofunctorOver_terminal_source_type_eq_symm
            (J := J) (U := U) (T := T) M N)
          (Eq.mp
            (localized_pseudofunctorOver_terminal_source_type_eq
              (J := J) (U := U) (T := T) M N)
            z) =
        z := by
    cases T
    simp [Pseudofunctor.presheafHom]
  -- This leaves the original theorem as a short corollary of the raw terminal computation.
  exact hraw.trans hcancel

/-- Helper for Lemma 7.26.4: after rewriting the source-side terminal section into owner
coordinates, the terminal component of `overMapCompPresheafHomIso` is exactly the explicit
owner-side `pullHom` morphism before the final `mapComp'`-to-`mapComp` normalization. -/
private theorem localized_pseudofunctorOver_source_terminal_component_eq_iterated_transport
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    (Pseudofunctor.presheafHomObjHomEquiv (F := J.pseudofunctorOver (Type w)) (S := T₁.left)).symm
      (((Pseudofunctor.overMapCompPresheafHomIso
        (F := J.pseudofunctorOver (Type w)) (M := M) (N := N) T₁.hom).hom.app
          (Opposite.op (Over.mk (𝟙 T₁.left))))
        (Eq.mp
          (by
            simp [localized_cover_descent_overMap_terminal_obj]
            rfl)
          (((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
            (J := J) (U := U) T₁ M N).trans
            ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
              (J := J) (U := U) T₁ M).homCongr
              (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
                (J := J) (U := U) T₁ N)))
            (((J.over U).overMapPullback (Type w) g).map x)))) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (localized_pseudofunctorOver_presheafHom_obj_equiv
          (J := J) (U := U) T₂ M N x)
        g.left T₁.hom T₁.hom
        (by simpa using Over.w g) (by simpa using Over.w g) := by
  -- Collapse the terminal round-trip via the proven cast computation; the remaining content is
  -- the sheaf-level comparison between the iterated-slice transport and the owner `pullHom`.
  refine (localized_pseudofunctorOver_terminal_component_apply_cast_eq
    (J := J) (U := U) (T := T₁) (M := M) (N := N)
    (((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
        (J := J) (U := U) T₁ M N).trans
        ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₁ M).homCongr
          (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
            (J := J) (U := U) T₁ N)))
        (((J.over U).overMapPullback (Type w) g).map x))).trans ?_
  apply (sheafToPresheaf (J.over T₁.left) (Type w)).map_injective
  have hcore :
      (Functor.isoWhiskerRight
        (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
        M.obj).inv ≫
        T₁.iteratedSliceBackward.op.whiskerLeft ((Over.map g).op.whiskerLeft x.hom) ≫
          (Functor.isoWhiskerRight
            (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
            N.obj).hom =
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.pseudofunctorOver (Type w)).mapComp'
          T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
          (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).hom.toNatTrans.app
            M) ≫
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.overMapPullback (Type w) g.left).map
          (localized_pseudofunctorOver_presheafHom_obj_equiv
            (J := J) (U := U) T₂ M N x))) ≫
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.pseudofunctorOver (Type w)).mapComp'
          T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
          (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).inv.toNatTrans.app
            N) :=
    localized_pseudofunctorOver_whisker_transport_core (J := J) (U := U) g M N x
  exact (localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv_underlying_left_normal_form
      (J := J) (U := U) g M N x).trans
    (hcore.trans
      (localized_pseudofunctorOver_pullHom_underlying_normal_form
        (J := J) (U := U) g M N x).symm)

/-- Helper for Lemma 7.26.4: after expressing the source-side comparison in owner coordinates,
the terminal owner-source section of `overMapCompPresheafHomIso` is exactly the canonical
three-factor owner transport sheaf morphism. -/
private theorem localized_pseudofunctorOver_overMapCompPresheafHomIso_terminal_component_eq_owner_transport
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    localized_pseudofunctorOver_source_terminal_transport_hom
      (J := J) (U := U) g M N x =
      localized_pseudofunctorOver_owner_transport_hom
        (J := J) (U := U) g M N x := by
  let y' :
      (((Over.map T₁.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
        (Opposite.op (Over.mk (𝟙 T₁.left)))) :=
    Eq.mp
      (by
        simp [localized_cover_descent_overMap_terminal_obj]
        rfl)
      (((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
        (J := J) (U := U) T₁ M N).trans
        ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₁ M).homCongr
          (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
            (J := J) (U := U) T₁ N)))
        (((J.over U).overMapPullback (Type w) g).map x))
  have hy :
      localized_pseudofunctorOver_presheafHom_obj_equiv_owner_source
          (J := J) (U := U) T₁ M N
          (((CategoryTheory.sheafHom (J := J.over U) M N).1).map g.op x) =
        y' := by
    -- Rewrite the terminal source coordinate using the already-normalized source map.
    exact congrArg
      (fun t =>
        Eq.mp
          (by
            simp [localized_cover_descent_overMap_terminal_obj]
            rfl)
          t)
      (localized_pseudofunctorOver_presheafHom_obj_equiv_source_map
        (J := J) (U := U) g M N x)
  rw [localized_pseudofunctorOver_source_terminal_transport_hom, hy]
  -- Route correction: isolate the source-side terminal cast mismatch first, then reuse the
  -- already-proved target-side normalization from `pullHom` to owner transport.
  exact
    (localized_pseudofunctorOver_source_terminal_component_eq_iterated_transport
      (J := J) (U := U) g M N x).trans
      (localized_pseudofunctorOver_pullHom_eq_owner_transport_hom
        (J := J) (U := U) g M N x)

/-- Helper for Lemma 7.26.4: the reduced source-side transport is obtained by restricting the
terminal owner-source morphism along `Over.homMk X.hom` and then evaluating at `X`. -/
private theorem localized_pseudofunctorOver_transport_source_app_eq_terminal_restrict
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left) :
    localized_pseudofunctorOver_transport_source_app (J := J) (U := U) g M N x X =
      ((sheafToPresheaf (J.over T₁.left) (Type w)).map
        (localized_pseudofunctorOver_source_terminal_transport_hom
          (J := J) (U := U) g M N x)).app (Opposite.op X) := by
  let y :
      (((Over.map T₁.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
        (Opposite.op (Over.mk (𝟙 T₁.left)))) :=
    localized_pseudofunctorOver_presheafHom_obj_equiv_owner_source
      (J := J) (U := U) T₁ M N
      (((CategoryTheory.sheafHom (J := J.over U) M N).1).map g.op x)
  let y' :
      (((Over.map T₁.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
        (Opposite.op (Over.mk (𝟙 T₁.left)))) :=
    Eq.mp
      (by
        simp [localized_cover_descent_overMap_terminal_obj]
        rfl)
      (((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
        (J := J) (U := U) T₁ M N).trans
        ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₁ M).homCongr
          (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
            (J := J) (U := U) T₁ N)))
        (((J.over U).overMapPullback (Type w) g).map x))
  have hy :
      y = y' := by
    -- The terminal source section is the owner-coordinate form of the normalized source map.
    exact congrArg
      (fun t =>
        Eq.mp
          (by
            simp [localized_cover_descent_overMap_terminal_obj]
            rfl)
          t)
      (localized_pseudofunctorOver_presheafHom_obj_equiv_source_map
        (J := J) (U := U) g M N x)
  -- The terminal round-trip of the normalized source section recovers the chain value itself,
  -- so the terminal transport morphism is literally the iterated-slice comparison value.
  have h1165 :=
    localized_pseudofunctorOver_terminal_component_apply_cast_eq
      (J := J) (U := U) (T := T₁) (M := M) (N := N)
      (((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
        (J := J) (U := U) T₁ M N).trans
        ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₁ M).homCongr
          (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
            (J := J) (U := U) T₁ N)))
        (((J.over U).overMapPullback (Type w) g).map x))
  have hhom :
      localized_pseudofunctorOver_source_terminal_transport_hom
        (J := J) (U := U) g M N x =
      ((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
        (J := J) (U := U) T₁ M N).trans
        ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₁ M).homCongr
          (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
            (J := J) (U := U) T₁ N)))
        (((J.over U).overMapPullback (Type w) g).map x) :=
    (congrArg
      (fun t ↦
        (Pseudofunctor.presheafHomObjHomEquiv (F := J.pseudofunctorOver (Type w))
            (S := T₁.left)).symm
          (((Pseudofunctor.overMapCompPresheafHomIso
            (F := J.pseudofunctorOver (Type w)) (M := M) (N := N) T₁.hom).hom.app
              (Opposite.op (Over.mk (𝟙 T₁.left)))) t))
      hy).trans h1165
  exact congrArg
    (fun s ↦ ((sheafToPresheaf (J.over T₁.left) (Type w)).map s).app (Opposite.op X))
    hhom.symm

/-- Helper for Lemma 7.26.4: after expressing the source-side comparison in owner coordinates,
the iterated-slice transport is already the same canonical owner transport used on the target
side. This isolates the source half of the remaining transport/coercion normalization. -/
private theorem localized_pseudofunctorOver_transport_source_app_eq_owner_transport
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left) :
    localized_pseudofunctorOver_transport_source_app (J := J) (U := U) g M N x X =
      localized_pseudofunctorOver_owner_transport_app (J := J) (U := U) g M N x X := by
  -- Route correction: the main theorem is now reduced to two explicit helper lemmas: first,
  -- rewrite the source-side map as restriction of the terminal owner-source morphism; second,
  -- identify that terminal morphism with the canonical owner transport and evaluate at `X`.
  have hsource :=
    localized_pseudofunctorOver_transport_source_app_eq_terminal_restrict
      (J := J) (U := U) g M N x X
  have hterminal :=
    localized_pseudofunctorOver_overMapCompPresheafHomIso_terminal_component_eq_owner_transport
      (J := J) (U := U) g M N x
  have happ :
      ((sheafToPresheaf (J.over T₁.left) (Type w)).map
        (localized_pseudofunctorOver_source_terminal_transport_hom
          (J := J) (U := U) g M N x)).app (Opposite.op X) =
        localized_pseudofunctorOver_owner_transport_app (J := J) (U := U) g M N x X := by
    -- Evaluate the terminal-component identification at `X`; the right-hand side is the
    -- definition of `localized_pseudofunctorOver_owner_transport_app`.
    simpa [localized_pseudofunctorOver_owner_transport_app] using
      congrArg
        (fun φ =>
          ((sheafToPresheaf (J.over T₁.left) (Type w)).map φ).app (Opposite.op X))
        hterminal
  exact hsource.trans happ

/-- Helper for Lemma 7.26.4: the remaining prestack transport theorem is equivalent to the
reduced presheaf-level comparison obtained by rewriting both sides with the established normal
forms. -/
private theorem localized_pseudofunctorOver_pullHom_three_factor_eq_iteratedSlice_transport_app_iff
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left) :
    (((Functor.isoWhiskerRight
        (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
        M.obj).inv ≫
          T₁.iteratedSliceBackward.op.whiskerLeft ((Over.map g).op.whiskerLeft x.hom) ≫
            (Functor.isoWhiskerRight
              (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
              N.obj).hom).app (Opposite.op X)) =
        (((sheafToPresheaf (J.over T₁.left) (Type w)).map
          (((J.pseudofunctorOver (Type w)).mapComp'
            T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
            (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).hom.toNatTrans.app
              M) ≫
        (sheafToPresheaf (J.over T₁.left) (Type w)).map
          (((J.overMapPullback (Type w) g.left).map
            (localized_pseudofunctorOver_presheafHom_obj_equiv
              (J := J) (U := U) T₂ M N x))) ≫
        (sheafToPresheaf (J.over T₁.left) (Type w)).map
          (((J.pseudofunctorOver (Type w)).mapComp'
            T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
            (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).inv.toNatTrans.app
              N)).app (Opposite.op X)) ↔
      localized_pseudofunctorOver_transport_source_app (J := J) (U := U) g M N x X =
        localized_pseudofunctorOver_transport_target_app (J := J) (U := U) g M N x X := by
  constructor
  · intro h
    simpa [localized_pseudofunctorOver_transport_source_app,
      localized_pseudofunctorOver_transport_target_app] using
      ((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv_underlying_left_normal_form_app
        (J := J) (U := U) g M N x X).symm.trans
        (h.trans
          (localized_pseudofunctorOver_pullHom_underlying_normal_form_app
            (J := J) (U := U) g M N x X).symm))
  · intro h
    simpa [localized_pseudofunctorOver_transport_source_app,
      localized_pseudofunctorOver_transport_target_app] using
      ((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv_underlying_left_normal_form_app
        (J := J) (U := U) g M N x X).trans
        (h.trans
          (localized_pseudofunctorOver_pullHom_underlying_normal_form_app
            (J := J) (U := U) g M N x X)))

/-- Helper for Lemma 7.26.4: after both sides of the Hom-presheaf naturality statement are
written in owner coordinates, the remaining equality is the bare transport comparison between the
iterated-slice pullback map and the owner-side `pullHom` formula. -/
private theorem localized_pseudofunctorOver_pullHom_three_factor_eq_iteratedSlice_transport_app
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left) :
    (((Functor.isoWhiskerRight
      (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
      M.obj).inv ≫
        T₁.iteratedSliceBackward.op.whiskerLeft ((Over.map g).op.whiskerLeft x.hom) ≫
          (Functor.isoWhiskerRight
            (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
            N.obj).hom).app (Opposite.op X)) =
      (((sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.pseudofunctorOver (Type w)).mapComp'
          T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
          (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).hom.toNatTrans.app
            M) ≫
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.overMapPullback (Type w) g.left).map
          (localized_pseudofunctorOver_presheafHom_obj_equiv
            (J := J) (U := U) T₂ M N x))) ≫
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.pseudofunctorOver (Type w)).mapComp'
          T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
          (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).inv.toNatTrans.app
            N)).app (Opposite.op X)) := by
  -- Route correction: keep the transport blocker at a single slice object `X`, so the remaining
  -- work is a flat equality of component maps instead of a full natural-transformation identity.
  let hmap :
      (J.pseudofunctorOver (Type w)).map T₁.hom.op.toLoc =
        (J.pseudofunctorOver (Type w)).map (T₂.hom.op.toLoc ≫ g.left.op.toLoc) := by
    -- Transport the base equality `g.left ≫ T₂.hom = T₁.hom` through the owner pseudofunctor.
    simpa using congrArg ((J.pseudofunctorOver (Type w)).map)
      (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g).symm
  let owner_transport :
      ((Over.map T₁.hom).op ⋙ M.obj).obj (Opposite.op X) ⟶
        ((Over.map T₁.hom).op ⋙ N.obj).obj (Opposite.op X) :=
    ((sheafToPresheaf (J.over T₁.left) (Type w)).map
      ((eqToIso hmap ≪≫
          (J.pseudofunctorOver (Type w)).mapComp T₂.hom.op.toLoc g.left.op.toLoc).hom.toNatTrans.app
            M ≫
        (J.overMapPullback (Type w) g.left).map
          (localized_pseudofunctorOver_presheafHom_obj_equiv
            (J := J) (U := U) T₂ M N x) ≫
        (eqToIso hmap ≪≫
          (J.pseudofunctorOver (Type w)).mapComp T₂.hom.op.toLoc g.left.op.toLoc).inv.toNatTrans.app
            N)).app (Opposite.op X)
  -- Route correction: the surviving blocker is no longer the normal-form rewrites themselves,
  -- but the reduced presheaf-level equality produced by the iff lemma just above.
  have hreduce :
      localized_pseudofunctorOver_transport_source_app (J := J) (U := U) g M N x X =
        localized_pseudofunctorOver_transport_target_app (J := J) (U := U) g M N x X := by
    have htarget :
        localized_pseudofunctorOver_transport_target_app (J := J) (U := U) g M N x X =
          owner_transport := by
      -- Normalize the target once so the remaining blocker is only the source-side comparison
      -- with the canonical owner transport.
      simpa [owner_transport, hmap, localized_pseudofunctorOver_owner_transport_app] using
        localized_pseudofunctorOver_transport_target_app_eq_owner_transport
          (J := J) (U := U) g M N x X
    have hsource :
        localized_pseudofunctorOver_transport_source_app (J := J) (U := U) g M N x X =
          owner_transport := by
      -- The source side now matches the same canonical owner transport after the identical
      -- `mapComp'`-to-`mapComp` normalization.
      simpa [owner_transport, hmap, localized_pseudofunctorOver_owner_transport_app] using
        localized_pseudofunctorOver_transport_source_app_eq_owner_transport
          (J := J) (U := U) g M N x X
    exact hsource.trans (by simpa using htarget.symm)
  exact
    (localized_pseudofunctorOver_pullHom_three_factor_eq_iteratedSlice_transport_app_iff
      (J := J) (U := U) g M N x X).2 hreduce

/-- Helper for Lemma 7.26.4: after both sides of the Hom-presheaf naturality statement are
written in owner coordinates, the remaining equality is the bare transport comparison between the
iterated-slice pullback map and the owner-side `pullHom` formula. -/
private theorem localized_pseudofunctorOver_pullHom_three_factor_eq_iteratedSlice_transport
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    (Functor.isoWhiskerRight
      (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
      M.obj).inv ≫
        T₁.iteratedSliceBackward.op.whiskerLeft ((Over.map g).op.whiskerLeft x.hom) ≫
          (Functor.isoWhiskerRight
            (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
            N.obj).hom =
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.pseudofunctorOver (Type w)).mapComp'
          T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
          (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).hom.toNatTrans.app
            M) ≫
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.overMapPullback (Type w) g.left).map
          (localized_pseudofunctorOver_presheafHom_obj_equiv
            (J := J) (U := U) T₂ M N x))) ≫
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.pseudofunctorOver (Type w)).mapComp'
          T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
          (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).inv.toNatTrans.app
            N) := by
  -- The full forgotten equality is now reduced to the objectwise comparison proved once above.
  ext X a
  exact congrFun
    (localized_pseudofunctorOver_pullHom_three_factor_eq_iteratedSlice_transport_app
      (J := J) (U := U) g M N x X.unop) a

/-- Helper for Lemma 7.26.4: after both sides of the Hom-presheaf naturality statement are
written in owner coordinates, the remaining equality is the bare transport comparison between the
iterated-slice pullback map and the owner-side `pullHom` formula. -/
private theorem localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv_underlying_naturality
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    (sheafToPresheaf (J.over T₁.left) (Type w)).map
      (((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
        (J := J) (U := U) T₁ M N).trans
        ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₁ M).homCongr
          (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
            (J := J) (U := U) T₁ N)))
        (((J.over U).overMapPullback (Type w) g).map x)) =
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (localized_pseudofunctorOver_presheafHom_obj_equiv
            (J := J) (U := U) T₂ M N x)
          g.left T₁.hom T₁.hom
          (by simpa using Over.w g) (by simpa using Over.w g)) := by
  -- Route correction: the remaining blocker lives entirely after forgetting to presheaves, so
  -- isolate that forgotten equality before reusing full faithfulness of `sheafToPresheaf`.
  rw [localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv_underlying_left_normal_form
    (J := J) (U := U) g M N x]
  rw [localized_pseudofunctorOver_pullHom_underlying_normal_form
    (J := J) (U := U) g M N x]
  -- The remaining equality is now the isolated forgotten-presheaf transport normalization.
  simpa using
    localized_pseudofunctorOver_pullHom_three_factor_eq_iteratedSlice_transport
      (J := J) (U := U) g M N x

/-- Helper for Lemma 7.26.4: after both sides of the Hom-presheaf naturality statement are
written in owner coordinates, the remaining equality is the bare transport comparison between the
iterated-slice pullback map and the owner-side `pullHom` formula. -/
private theorem localized_pseudofunctorOver_presheafHom_obj_equiv_naturality_transport
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    ((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
      (J := J) (U := U) T₁ M N).trans
      ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
        (J := J) (U := U) T₁ M).homCongr
        (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₁ N)))
      (((J.over U).overMapPullback (Type w) g).map x) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (localized_pseudofunctorOver_presheafHom_obj_equiv
          (J := J) (U := U) T₂ M N x)
        g.left T₁.hom T₁.hom
        (by simpa using Over.w g) (by simpa using Over.w g) := by
  -- Forget to presheaves so the comparison becomes an equality of explicit composites.
  apply (sheafToPresheaf (J.over T₁.left) (Type w)).map_injective
  -- The remaining transport normalization is exactly the isolated presheaf-level comparison.
  simpa using
    localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv_underlying_naturality
      (J := J) (U := U) g M N x

/-- Helper for Lemma 7.26.4: the objectwise comparison between the ordinary slice-site Hom sheaf
and the owner-side Hom presheaf commutes with restriction maps in `Over U`. -/
private theorem localized_pseudofunctorOver_presheafHom_obj_equiv_naturality
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    localized_pseudofunctorOver_presheafHom_obj_equiv (J := J) (U := U) T₁ M N
      (((CategoryTheory.sheafHom (J := J.over U) M N).1).map g.op x) =
      (((J.pseudofunctorOver (Type w)).presheafHom M N).map g.op
        (localized_pseudofunctorOver_presheafHom_obj_equiv
          (J := J) (U := U) T₂ M N x)) := by
  -- Normalize both sides to their concrete restriction maps before comparing the transports.
  rw [localized_pseudofunctorOver_presheafHom_obj_equiv_source_map (J := J) (U := U) g M N x,
    localized_pseudofunctorOver_presheafHom_target_map (J := J) (U := U) g M N]
  -- The remaining step is the isolated transport normalization recorded above.
  simpa using localized_pseudofunctorOver_presheafHom_obj_equiv_naturality_transport
    (J := J) (U := U) g M N x

/-- Helper for Lemma 7.26.4: at the terminal object of `Over U`, the ordinary Hom sheaf on
`J.over U` identifies with global morphisms `M ⟶ N`. -/
private noncomputable def localized_pseudofunctorOver_presheafHom_base_equiv
    (M N : Sheaf (J.over U) (Type w)) :
    ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op (Over.mk (𝟙 U)))) ≃
      (M ⟶ N) := by
  -- Combine the owner comparison at `Over.mk (𝟙 U)` with the standard base-point equivalence
  -- for `Pseudofunctor.presheafHom`.
  exact
    (localized_pseudofunctorOver_presheafHom_obj_equiv
      (J := J) (U := U) (Over.mk (𝟙 U)) M N).trans
      (Pseudofunctor.presheafHomObjHomEquiv (F := J.pseudofunctorOver (Type w))).symm

/-- Helper for Lemma 7.26.4: transporting a global morphism `ψ : M ⟶ N` to the terminal object
of the ordinary Hom sheaf and then back through the objectwise owner comparison recovers the
canonical base section of `Pseudofunctor.presheafHom`. -/
private theorem localized_pseudofunctorOver_presheafHom_base_equiv_apply
    {M N : Sheaf (J.over U) (Type w)}
    (ψ : M ⟶ N) :
    localized_pseudofunctorOver_presheafHom_obj_equiv (J := J) (U := U)
      (Over.mk (𝟙 U)) M N
      ((localized_pseudofunctorOver_presheafHom_base_equiv
        (J := J) (U := U) M N).symm ψ) =
      (Pseudofunctor.presheafHomObjHomEquiv
        (F := J.pseudofunctorOver (Type w)) ψ) := by
  -- Unfold the composite base equivalence and cancel the objectwise comparison with its inverse.
  change
    localized_pseudofunctorOver_presheafHom_obj_equiv (J := J) (U := U)
      (Over.mk (𝟙 U)) M N
      ((localized_pseudofunctorOver_presheafHom_obj_equiv (J := J) (U := U)
        (Over.mk (𝟙 U)) M N).symm
        (((Pseudofunctor.presheafHomObjHomEquiv
          (F := J.pseudofunctorOver (Type w))).symm).symm ψ)) =
      (((Pseudofunctor.presheafHomObjHomEquiv
        (F := J.pseudofunctorOver (Type w))).symm).symm ψ)
  exact
    (localized_pseudofunctorOver_presheafHom_obj_equiv (J := J) (U := U)
      (Over.mk (𝟙 U)) M N).apply_symm_apply
      ((((Pseudofunctor.presheafHomObjHomEquiv
        (F := J.pseudofunctorOver (Type w))).symm).symm ψ))

/-- Helper for Lemma 7.26.4: the ordinary slice-site Hom sheaf and the owner-side Hom presheaf
are identified by the objectwise iterated-slice comparison, promoted to a presheaf isomorphism. -/
private noncomputable def localized_pseudofunctorOver_presheafHom_iso
    (M N : Sheaf (J.over U) (Type w)) :
    (CategoryTheory.sheafHom (J := J.over U) M N).1 ≅
      ((J.pseudofunctorOver (Type w)).presheafHom M N) :=
  NatIso.ofComponents
    (fun T ↦
      Equiv.toIso
        (localized_pseudofunctorOver_presheafHom_obj_equiv
          (J := J) (U := U) T.unop M N))
    (by
      -- Route correction: prove the Hom-presheaf comparison once as a NatIso, so the fixed-cover
      -- prestack argument only transports the sheaf condition across that stable bridge.
      intro T₁ T₂ g
      ext x
      simpa using localized_pseudofunctorOver_presheafHom_obj_equiv_naturality
        (J := J) (U := U) g.unop M N x)

/-- Helper for Lemma 7.26.4: the cover arrows in `Over U` generate the same covering sieve at the
terminal object `U/U` as the original cover `𝒰`. -/
private theorem localized_cover_descent_cover_arrows_sieve_over_terminal
    (𝒰 : J.Cover U) :
    Sieve.overEquiv (Over.mk (𝟙 U))
      (Sieve.ofArrows (fun I : 𝒰.Arrow ↦ Over.mk I.f)
        (fun I ↦ show Over.mk I.f ⟶ Over.mk (𝟙 U) from Over.homMk I.f)) =
      (𝒰 : Sieve U) := by
  -- Unpack membership in the generated slice-site sieve into a factorization through one
  -- of the chosen cover arrows, then forget the slice structure back to `C`.
  ext Z g
  rw [Sieve.overEquiv_iff, Sieve.mem_ofArrows_iff]
  constructor
  · rintro ⟨I, h, _⟩
    have hw : h.left ≫ I.f = g := by
      simpa using Over.w h
    exact hw ▸ (𝒰 : Sieve U).downward_closed I.hf h.left
  · intro hg
    let a : Over.mk (g ≫ (Over.mk (𝟙 U)).hom) ⟶ Over.mk g := Over.homMk (𝟙 Z) (by simp)
    refine ⟨⟨Z, g, hg⟩, a, ?_⟩
    ext
    simp [a]

/-- Helper for Lemma 7.26.4: the chosen cover `𝒰` induces an honest cover of the terminal object
`U/U` inside the localized site `J.over U`. -/
private def localized_cover_descent_terminal_cover
    (𝒰 : J.Cover U) :
    (J.over U).Cover (Over.mk (𝟙 U)) :=
  ⟨Sieve.ofArrows (fun I : 𝒰.Arrow ↦ Over.mk I.f)
      (fun I ↦ show Over.mk I.f ⟶ Over.mk (𝟙 U) from Over.homMk I.f), by
    -- The generated slice-site sieve is exactly the original covering sieve on `U`.
    rw [J.mem_over_iff,
      localized_cover_descent_cover_arrows_sieve_over_terminal (J := J) (U := U) 𝒰]
    exact 𝒰.condition⟩

/-- Helper for Lemma 7.26.4: compatibility of sections for a family of base arrows
`f : Xᵢ ⟶ U` is equivalent to compatibility for the induced family of arrows
`Over.mk (f i) ⟶ Over.mk (𝟙 U)` in the localized site. This lets the source-compatible-family
formula talk directly to the existing slice-site sheaf API. -/
private theorem localized_cover_descent_compatible_over_terminal_iff
    (P : Cᵒᵖ ⥤ Type w) {ι : Type*} {X : ι → C} (f : ∀ i, X i ⟶ U)
    (x : ∀ i, P.obj (Opposite.op (X i))) :
    Presieve.Arrows.Compatible P f x ↔
      Presieve.Arrows.Compatible ((Over.forget U).op ⋙ P)
        (fun i ↦ (show Over.mk (f i) ⟶ Over.mk (𝟙 U) from Over.homMk (f i))) x := by
  constructor
  · intro hx i j Z gi gj h
    -- Forgetting the slice equality reduces the compatibility check to the base category.
    exact hx i j Z.left gi.left gj.left (by simpa using (Over.forget U).congr_map h)
  · intro hx i j Z gi gj h
    -- Repackage the common composite `gi ≫ f i = gj ≫ f j` as an object of `Over U`.
    let Z' : Over U := Over.mk (gi ≫ f i)
    exact hx i j Z' (Over.homMk gi) (Over.homMk gj (by simpa [Z'] using h.symm)) (by
      ext
      simp [Z', h])

/-- Helper for Lemma 7.26.4: the sheaf condition for a presheaf on a family of base arrows
`f : Xᵢ ⟶ U` is equivalent to the sheaf condition for its restriction to the induced family
`Over.mk (f i) ⟶ Over.mk (𝟙 U)` in the localized site. This is the formal bridge from source-side
compatible families to the terminal-cover language used later in the proof. -/
private theorem localized_cover_descent_isSheafFor_over_terminal_ofArrows_iff
    (P : Cᵒᵖ ⥤ Type w) {ι : Type*} (X : ι → C) (f : ∀ i, X i ⟶ U) :
    Presieve.IsSheafFor P (Presieve.ofArrows X f) ↔
      Presieve.IsSheafFor ((Over.forget U).op ⋙ P)
        (Presieve.ofArrows (fun i ↦ Over.mk (f i))
          (fun i ↦ (show Over.mk (f i) ⟶ Over.mk (𝟙 U) from Over.homMk (f i)))) := by
  rw [Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible,
    Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro x y hxy
      -- Equality of compatible families is detected pointwise on the original indices.
      apply h.1
      ext i
      exact congrFun (congrArg Subtype.val hxy) i
    · intro x
      -- Translate terminal-cover compatibility back to the base-arrow formulation, then solve
      -- the glued section using the original sheaf-condition bijection.
      obtain ⟨y, hy⟩ := h.2 ⟨x.1,
        (localized_cover_descent_compatible_over_terminal_iff
          (P := P) (f := f) x.1).2 x.2⟩
      refine ⟨y, ?_⟩
      apply Subtype.ext
      ext i
      exact congrFun (congrArg Subtype.val hy) i
  · intro h
    refine ⟨?_, ?_⟩
    · intro x y hxy
      -- The reverse direction uses the same pointwise detection after passing to the slice site.
      apply h.1
      ext i
      exact congrFun (congrArg Subtype.val hxy) i
    · intro x
      -- Translate base compatibility into the terminal-cover version, glue there, and unwrap.
      obtain ⟨y, hy⟩ := h.2 ⟨x.1,
        (localized_cover_descent_compatible_over_terminal_iff
          (P := P) (f := f) x.1).1 x.2⟩
      refine ⟨y, ?_⟩
      apply Subtype.ext
      ext i
      exact congrFun (congrArg Subtype.val hy) i

/-- Helper for Lemma 7.26.4: an arrow in the induced terminal cover of `U/U` comes from the
underlying arrow of the original cover `𝒰` after forgetting the slice-site packaging. -/
private def localized_cover_descent_terminal_cover_arrow_base
    (𝒰 : J.Cover U)
    (I : (localized_cover_descent_terminal_cover (J := J) (U := U) 𝒰).Arrow) :
    𝒰.Arrow := by
  refine ⟨I.Y.left, I.f.left, ?_⟩
  -- Unpack the slice-site arrow as a factorization through one original cover member, then forget
  -- the slice structure to recover membership in the original covering sieve on `U`.
  have hf :
      (Sieve.ofArrows (fun I : 𝒰.Arrow ↦ Over.mk I.f)
        (fun I ↦ show Over.mk I.f ⟶ Over.mk (𝟙 U) from Over.homMk I.f)) I.f := I.hf
  rw [Sieve.mem_ofArrows_iff] at hf
  rcases hf with ⟨J, a, ha⟩
  have hleft : I.f.left = a.left ≫ J.f := by
    have hfy : I.f.left = I.Y.hom := by
      simpa using Over.w I.f
    have hw : a.left ≫ J.f = I.Y.hom := by
      simpa [ha] using Over.w a
    exact hfy.trans hw.symm
  simpa [hleft] using (𝒰 : Sieve U).downward_closed J.hf a.left

/-- Helper for Lemma 7.26.4: after passing to the slice site `J.over I.Y`, the pullback cover
`𝒰.pullback I.f` induces the terminal cover of `I.Y / I.Y`. This is the cover whose one-hypercover
controls compatible local sections of `D.obj I`. -/
private def localized_cover_descent_component_terminal_cover
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow) :
    ((J.over I.Y).Cover (Over.mk (𝟙 I.Y))) :=
  localized_cover_descent_terminal_cover (J := J) (U := I.Y) (𝒰.pullback I.f)

/-- Helper for Lemma 7.26.4: compatible families of sections of the component sheaf `D.obj I`
along the terminal cover induced by `𝒰.pullback I.f` are equivalent to actual sections of
`D.obj I` over `I.Y / I.Y`. This is the slice-site multiequalizer bridge needed for the component
comparison step of the glued-object construction. -/
private noncomputable def localized_cover_descent_component_sections_equiv
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :
    ((((localized_cover_descent_component_terminal_cover
        (J := J) (U := U) 𝒰 I).oneHypercover).multicospanIndex ((D.obj I).1)).sections) ≃
      ((D.obj I).1.obj (Opposite.op (Over.mk (𝟙 I.Y)))) :=
  CategoryTheory.Limits.Multifork.IsLimit.sectionsEquiv
    (((localized_cover_descent_component_terminal_cover
      (J := J) (U := U) 𝒰 I).oneHypercover).isLimitMultifork (D.obj I))

/-- Helper for Lemma 7.26.4: evaluating the section reconstructed from a compatible family along
the induced terminal cover recovers the chosen local `K`-component. -/
private theorem localized_cover_descent_component_sections_equiv_apply_val
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (s :
      (((localized_cover_descent_component_terminal_cover
        (J := J) (U := U) 𝒰 I).oneHypercover).multicospanIndex ((D.obj I).1)).sections)
    (K : (localized_cover_descent_component_terminal_cover
      (J := J) (U := U) 𝒰 I).Arrow) :
    (((localized_cover_descent_component_terminal_cover
      (J := J) (U := U) 𝒰 I).oneHypercover).multifork ((D.obj I).1)).ι K
      (localized_cover_descent_component_sections_equiv
        (J := J) (U := U) 𝒰 D I s) = s.val K := by
  -- The one-hypercover limit identifies the reconstructed global section by its components.
  simpa using CategoryTheory.Limits.Multifork.IsLimit.sectionsEquiv_apply_val
    (((localized_cover_descent_component_terminal_cover
      (J := J) (U := U) 𝒰 I).oneHypercover).isLimitMultifork (D.obj I)) s K

/-- Helper for Lemma 7.26.4: the inverse direction of the component-sections equivalence is
computed by the canonical multifork legs of the terminal cover induced by `𝒰.pullback I.f`. -/
private theorem localized_cover_descent_component_sections_equiv_symm_apply_val
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (t : (D.obj I).1.obj (Opposite.op (Over.mk (𝟙 I.Y))))
    (K : (localized_cover_descent_component_terminal_cover
      (J := J) (U := U) 𝒰 I).Arrow) :
    ((localized_cover_descent_component_sections_equiv
      (J := J) (U := U) 𝒰 D I).symm t).val K =
      (((localized_cover_descent_component_terminal_cover
        (J := J) (U := U) 𝒰 I).oneHypercover).multifork ((D.obj I).1)).ι K t := by
  -- The inverse section is the multifork section cut out by the universal limit property.
  simpa using CategoryTheory.Limits.Multifork.IsLimit.sectionsEquiv_symm_apply_val
    (((localized_cover_descent_component_terminal_cover
      (J := J) (U := U) 𝒰 I).oneHypercover).isLimitMultifork (D.obj I)) t K

/-- Helper for Lemma 7.26.4: evaluating the pullback of a sheaf along `f : X ⟶ Y` at the
terminal object of `Over X` recovers the original sheaf evaluated at `Over.mk f`. -/
private theorem localized_cover_descent_overMap_terminal_section_eq
    {X Y : C}
    (f : X ⟶ Y)
    (M : Sheaf (J.over Y) (Type w)) :
    (((J.overMapPullback (Type w) f).obj M).1.obj
      (Opposite.op (Over.mk (𝟙 X)))) =
      (M.1.obj (Opposite.op (Over.mk f))) := by
  -- Unfold the localized pullback and rewrite the pulled-back terminal object to `Over.mk f`.
  simp [localized_cover_descent_overMap_terminal_obj]

/-- Helper for Lemma 7.26.4: after pulling the component sheaf `D.obj I` back to `J.over T.left`,
compatible local sections on the pulled-back cover over `T` are equivalent to a section at `T`.
This is the arbitrary-`T` version of the component gluing step from the source proof. -/
private abbrev localized_cover_descent_glue_component_source_over
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :=
  { s :
      ∀ K : ((𝒰.pullback I.f).pullback T.hom).Arrow,
        ((((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1).obj
          (Opposite.op (Over.mk K.f))) //
      Presieve.Arrows.Compatible
        (((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1)
        (fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦
          (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f))
        s }

/-- Helper for Lemma 7.26.4: after restricting the future glued presheaf to a fixed cover member
`I`, its source-compatible-family value at `T : Over I.Y` should be compared against this
standard subtype of compatible sections of the pulled-back component sheaf. -/
private noncomputable def localized_cover_descent_component_sections_equiv_over
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    localized_cover_descent_glue_component_source_over
      (J := J) (U := U) 𝒰 D I T ≃
      ((D.obj I).1.obj (Opposite.op T)) := by
  let P := (((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1)
  let π :=
    fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦
      (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f (by simp))
  have hsheaf :
      Presieve.IsSheafFor P
        (Presieve.ofArrows (fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ Over.mk K.f) π) := by
    -- The pulled-back component is a sheaf on `J.over T.left`, so it satisfies the sheaf
    -- condition for the induced terminal cover coming from the pulled-back base-site cover.
    rw [Presieve.isSheafFor_iff_generate]
    simpa [P, π, localized_cover_descent_terminal_cover] using
      (Presheaf.IsSheaf.isSheafFor
        (((J.overMapPullback (Type w) T.hom).obj (D.obj I)).2)
        ((localized_cover_descent_terminal_cover
          (J := J) (U := T.left) ((𝒰.pullback I.f).pullback T.hom)).1)
        ((localized_cover_descent_terminal_cover
          (J := J) (U := T.left) ((𝒰.pullback I.f).pullback T.hom)).condition))
  let hbij :=
    (Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible P π).mp hsheaf
  let hterminal :
      (P.obj (Opposite.op (Over.mk (𝟙 T.left)))) ≃
        ((D.obj I).1.obj (Opposite.op T)) :=
    (Equiv.cast
      (by
        simpa using
          localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := T.hom) (M := D.obj I)))
  -- First use the sheaf condition on the pulled-back component sheaf, then identify the
  -- resulting terminal section with a section of `(D.obj I).1` at `T`.
  exact (Equiv.ofBijective (Presieve.Arrows.toCompatible P π) hbij).symm.trans hterminal

/-- Helper for Lemma 7.26.4: this is the named Step 2 bridge from Agent C's plan. Once the
future glued presheaf is restricted to `I`, the remaining objectwise comparison is exactly the
compatible-family equivalence already proved for the pulled-back component sheaf. -/
private noncomputable def localized_cover_descent_glue_component_equiv_over
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    localized_cover_descent_glue_component_source_over
      (J := J) (U := U) 𝒰 D I T ≃
      ((D.obj I).1.obj (Opposite.op T)) := by
  -- This is exactly the arbitrary-`T` component gluing equivalence just established above.
  exact localized_cover_descent_component_sections_equiv_over (J := J) (U := U) 𝒰 D I T

/-- Helper for Lemma 7.26.4: specializing the arbitrary-`T` component comparison to the terminal
object of `Over I.Y` gives the exact terminal-section equivalence that will be used later when the
glued presheaf is compared with `D.obj I` on the basic cover member `I`. -/
private noncomputable def localized_cover_descent_glue_component_terminal_equiv
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :
    localized_cover_descent_glue_component_source_over
      (J := J) (U := U) 𝒰 D I (Over.mk (𝟙 I.Y)) ≃
      ((D.obj I).1.obj (Opposite.op (Over.mk (𝟙 I.Y)))) := by
  -- This is the same objectwise comparison as above, now frozen at the terminal slice object.
  simpa using
    localized_cover_descent_glue_component_equiv_over
      (J := J) (U := U) 𝒰 D I (Over.mk (𝟙 I.Y))

/-- Helper for Lemma 7.26.4: the terminal specialization of the component comparison is a genuine
equivalence, so applying it after its inverse recovers the original terminal section. -/
private theorem localized_cover_descent_glue_component_terminal_equiv_apply_symm
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (t : (D.obj I).1.obj (Opposite.op (Over.mk (𝟙 I.Y)))) :
    localized_cover_descent_glue_component_terminal_equiv
        (J := J) (U := U) 𝒰 D I
        ((localized_cover_descent_glue_component_terminal_equiv
          (J := J) (U := U) 𝒰 D I).symm t) =
      t := by
  -- The terminal comparison is an equivalence, so its inverse is a true inverse on sections.
  exact Equiv.apply_symm_apply
    (localized_cover_descent_glue_component_terminal_equiv
      (J := J) (U := U) 𝒰 D I)
    t

/-- Helper for Lemma 7.26.4: restricting the future glued presheaf along `I.f` and then
evaluating at `T : Over I.Y` amounts to looking at the pullback cover over the composite
`T.hom ≫ I.f`. This is the canonical cover-index identification needed in the objectwise
restriction comparison for the source-style glued presheaf. -/
private theorem localized_cover_descent_pullback_comp_eq_pullback_pullback
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    𝒰.pullback (T.hom ≫ I.f) = ((𝒰.pullback I.f).pullback T.hom) := by
  -- Both pullback covers are generated by the same composite map to `U`.
  ext Z g
  simp [GrothendieckTopology.Cover.coe_pullback, Category.assoc]

/-- Helper for Lemma 7.26.4: restricting the future glued presheaf along `I.f` and then
evaluating at `T : Over I.Y` amounts to looking at the pullback cover over the composite
`T.hom ≫ I.f`. This is the canonical cover-index identification needed in the objectwise
restriction comparison for the source-style glued presheaf. -/
private theorem localized_cover_descent_overMap_obj_hom
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    ((Over.map I.f).obj T).hom = T.hom ≫ I.f := by
  -- `Over.map` sends `T : Over I.Y` to the same object with structure map postcomposed by `I.f`.
  rfl

/-- Helper for Lemma 7.26.4: restricting the future glued presheaf along `I.f` and then
evaluating at `T : Over I.Y` amounts to looking at the pullback cover over the composite
`T.hom ≫ I.f`. This is the canonical cover-index identification needed in the objectwise
restriction comparison for the source-style glued presheaf. -/
private theorem localized_cover_descent_pullback_overMap_obj_eq_pullback_pullback
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    𝒰.pullback ((Over.map I.f).obj T).hom = ((𝒰.pullback I.f).pullback T.hom) := by
  -- Both pullback covers are defined by the same composite structure map `T.hom ≫ I.f`.
  change 𝒰.pullback (T.hom ≫ I.f) = ((𝒰.pullback I.f).pullback T.hom)
  exact localized_cover_descent_pullback_comp_eq_pullback_pullback (J := J) (U := U) 𝒰 I T

/-- Helper for Lemma 7.26.4: after restricting the original descent datum to a cover member `I`
and then pulling back further along `T : Over I.Y`, one obtains the ordinary descent datum of the
pulled-back component sheaf `((J.overMapPullback (Type w) T.hom).obj (D.obj I))` on the doubly
pulled-back cover. This is the arbitrary-`T` bridge used before packaging the final glued
presheaf restriction isomorphism. -/
private noncomputable def localized_cover_descent_pullbackDatum_toDescentData_over
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    (Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
      (f := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
      (p := T.hom)
      (f' := fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ K.f)
      (α := fun K ↦ K.base)
      (p' := fun _ ↦ 𝟙 _)
      (w := localized_cover_descent_pullbackDatum_w (J := J) (U := I.Y)
        (𝒰.pullback I.f) T)).obj
      (localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D (Over.mk I.f)) ≅
      (((J.pseudofunctorOver (Type w)).toDescentData
        (fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ K.f)).obj
        ((J.overMapPullback (Type w) T.hom).obj (D.obj I))) := by
  let w₂ :
      ∀ K : ((𝒰.pullback I.f).pullback T.hom).Arrow, (𝟙 K.Y) ≫ K.base.f = K.f ≫ T.hom :=
    localized_cover_descent_pullbackDatum_w (J := J) (U := I.Y) (𝒰.pullback I.f) T
  -- Route correction: first pull back the already-solved `I`-level comparison along `T.hom`.
  -- The remaining direct-vs-iterated pullback identification is kept separate from this
  -- structural bridge.
  refine ((Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
      (f := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
      (p := T.hom)
      (f' := fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ K.f)
      (α := fun K ↦ K.base)
      (p' := fun _ ↦ 𝟙 _)
      (w := w₂)).mapIso
      (localized_cover_descent_pullbackDatum_toDescentData_obj
        (J := J) (U := U) 𝒰 D I)) ≪≫ ?_
  exact
    (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
      (J.pseudofunctorOver (Type w))
      (f := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
      (p := T.hom)
      (f' := fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ K.f)
      (α := fun K ↦ K.base)
      (p' := fun _ ↦ 𝟙 _)
      (w := w₂)).app (D.obj I)

/-- Helper for Lemma 7.26.4: after transporting along the canonical identification of pullback
covers, the direct pullback datum over `((Over.map I.f).obj T)` is literally the same object as
the iterated pullback datum obtained by first restricting to `I` and then pulling back along
`T.hom`. This isolates the only dependent cast needed before the final objectwise restriction
comparison. -/
private theorem localized_cover_descent_pullbackDatum_over_direct_type
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    (J.pseudofunctorOver (Type w)).DescentData
        (fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ K.f) =
      (J.pseudofunctorOver (Type w)).DescentData
        (fun K : (𝒰.pullback ((Over.map I.f).obj T).hom).Arrow ↦ K.f) := by
  -- Rewriting the pullback cover along `((Over.map I.f).obj T).hom = T.hom ≫ I.f` aligns the two
  -- indexing families, so the ambient descent-data types coincide.
  rw [localized_cover_descent_pullback_overMap_obj_eq_pullback_pullback
    (J := J) (U := U) 𝒰 I T]
  rfl

/-- Helper for Lemma 7.26.4: after expressing the direct pullback along
`((Over.map I.f).obj T).hom = T.hom ≫ I.f` on the iterated pullback cover itself, the resulting
direct composite pullback datum is canonically isomorphic to the iterated pullback datum. This is
the cast-free source comparison behind the later direct-vs-iterated restriction bridge. -/
private noncomputable def localized_cover_descent_pullbackDatum_over_direct_source_iso
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    (Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
      (f := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
      (p := T.hom)
      (f' := fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ K.f)
      (α := fun K ↦ K.base)
      (p' := fun _ ↦ 𝟙 _)
      (w := localized_cover_descent_pullbackDatum_w (J := J) (U := I.Y)
        (𝒰.pullback I.f) T)).obj
      (localized_cover_descent_pullbackDatum
        (J := J) (U := U) 𝒰 D (Over.mk I.f)) ≅
      (Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
        (f := fun JI : 𝒰.Arrow ↦ JI.f)
        (p := ((Over.map I.f).obj T).hom)
        (f' := fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ K.f)
        (α := fun K ↦ K.base.base)
        (p' := fun _ ↦ 𝟙 _)
        (w := fun K ↦ by
          -- Normalize the direct composite witness to the underlying cover equation on `K`.
          change (𝟙 K.Y) ≫ K.base.base.f = K.f ≫ ((Over.map I.f).obj T).hom
          rw [show K.base.base.f = K.base.f ≫ I.f by
            simpa [GrothendieckTopology.Cover.Arrow.base] using
              localized_cover_descent_pullbackDatum_w
                (J := J) (U := U) 𝒰 (Over.mk I.f) K.base]
          rw [show K.base.f = K.f ≫ T.hom by
            simpa using
              localized_cover_descent_pullbackDatum_w
                (J := J) (U := I.Y) (𝒰.pullback I.f) T K]
          simp [Category.assoc])).obj D := by
  -- Compare the two-stage pullback (`I.f` then `T.hom`) with the one-stage pullback along the
  -- composite `((Over.map I.f).obj T).hom = T.hom ≫ I.f`; `pullFunctorCompIso` gives exactly the
  -- comparison between that one-step pullback and the two-step pullback.
  let e :=
    (Pseudofunctor.DescentData.pullFunctorCompIso
      (F := J.pseudofunctorOver (Type w))
      (f := fun JI : 𝒰.Arrow ↦ JI.f)
      (p := I.f)
      (f' := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
      (α := fun K ↦ K.base)
      (p' := fun _ ↦ 𝟙 _)
      (w := localized_cover_descent_pullbackDatum_w (J := J) (U := U) 𝒰 (Over.mk I.f))
      (q := T.hom)
      (f'' := fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ K.f)
      (β := fun K ↦ K.base)
      (q' := fun _ ↦ 𝟙 _)
      (w' := localized_cover_descent_pullbackDatum_w (J := J) (U := I.Y)
        (𝒰.pullback I.f) T)
      (r := ((Over.map I.f).obj T).hom)
      (r' := fun _ ↦ 𝟙 _)
      (hr := by rfl)
      (hr' := by intro K; simp))
  exact e.app D

/-- Helper for Lemma 7.26.4: an arrow in the iterated pullback cover over `I` and then `T`
already satisfies the direct composite compatibility for the single pullback along
`((Over.map I.f).obj T).hom = T.hom ≫ I.f`. This isolates the source-side cover equation needed
before packaging the direct-vs-iterated pullback comparison. -/
private theorem localized_cover_descent_pullback_over_direct_w
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow) :
    (𝟙 K.Y) ≫ K.base.base.f = K.f ≫ ((Over.map I.f).obj T).hom := by
  -- First rewrite the outer pullback condition over `I`, then substitute the inner pullback
  -- condition over `T`; the result is exactly the direct composite equation.
  rw [show K.base.base.f = K.base.f ≫ I.f by
    simpa [GrothendieckTopology.Cover.Arrow.base] using
      localized_cover_descent_pullbackDatum_w (J := J) (U := U) 𝒰 (Over.mk I.f) K.base]
  rw [show K.base.f = K.f ≫ T.hom by
    simpa using
      localized_cover_descent_pullbackDatum_w (J := J) (U := I.Y) (𝒰.pullback I.f) T K]
  simp [Category.assoc]

/-- Helper for Lemma 7.26.4: after first restricting the original descent datum to `I` and then
pulling back further along `T : Over I.Y`, the resulting source-side descent datum over the
iterated pullback cover is the concrete object whose terminal sections will later be reassembled
into the glued presheaf. -/
private abbrev localized_cover_descent_pullbackDatum_over_source
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :=
  (Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
    (f := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
    (p := T.hom)
    (f' := fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ K.f)
    (α := fun K ↦ K.base)
    (p' := fun _ ↦ 𝟙 _)
    (w := localized_cover_descent_pullbackDatum_w (J := J) (U := I.Y)
      (𝒰.pullback I.f) T)).obj
    (localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D (Over.mk I.f))

/-- Helper for Lemma 7.26.4: evaluating the ordinary descent datum of the pulled-back component
sheaf at the terminal object of `Over K.Y` reduces to evaluating that pulled-back component sheaf
at the overlap object `Over.mk K.f`. This is the arbitrary-`T` target-side section normal form.
-/
private theorem localized_cover_descent_toDescentData_over_section_eq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow) :
    (((((J.pseudofunctorOver (Type w)).toDescentData
        (fun L : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ L.f)).obj
        ((J.overMapPullback (Type w) T.hom).obj (D.obj I))).obj K).1.obj
      (Opposite.op (Over.mk (𝟙 K.Y)))) =
      ((((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1).obj
        (Opposite.op (Over.mk K.f))) := by
  -- The `K`-component of `toDescentData` is exactly the pullback of the component sheaf along
  -- `K.f`, so the terminal object of `Over K.Y` evaluates to the overlap object `Over.mk K.f`.
  simpa [Pseudofunctor.toDescentData] using
    (localized_cover_descent_overMap_terminal_section_eq
      (J := J) (f := K.f)
      (M := (J.overMapPullback (Type w) T.hom).obj (D.obj I)))

/-- Helper for Lemma 7.26.4: on each iterated pullback-cover member `K`, the arbitrary-`T`
comparison isomorphism from the source-side iterated pullback datum to the ordinary descent datum
of the pulled-back component sheaf has a concrete sheaf-level `K`-component. -/
private noncomputable def localized_cover_descent_pullbackDatum_over_component_iso
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow) :
    (localized_cover_descent_pullbackDatum_over_source
      (J := J) (U := U) 𝒰 D I T).obj K ≅
      (((((J.pseudofunctorOver (Type w)).toDescentData
          (fun L : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ L.f)).obj
          ((J.overMapPullback (Type w) T.hom).obj (D.obj I))).obj K)) where
  hom :=
    (localized_cover_descent_pullbackDatum_toDescentData_over
      (J := J) (U := U) 𝒰 D I T).hom.hom K
  inv :=
    (localized_cover_descent_pullbackDatum_toDescentData_over
      (J := J) (U := U) 𝒰 D I T).inv.hom K
  hom_inv_id := by
    have hK :
        (localized_cover_descent_pullbackDatum_toDescentData_over
          (J := J) (U := U) 𝒰 D I T).hom.hom K ≫
          (localized_cover_descent_pullbackDatum_toDescentData_over
            (J := J) (U := U) 𝒰 D I T).inv.hom K =
            𝟙 ((localized_cover_descent_pullbackDatum_over_source
              (J := J) (U := U) 𝒰 D I T).obj K) := by
      exact congrArg
        (fun f ↦ f.hom K)
        ((localized_cover_descent_pullbackDatum_toDescentData_over
          (J := J) (U := U) 𝒰 D I T).hom_inv_id)
    exact hK
  inv_hom_id := by
    have hK :
        (localized_cover_descent_pullbackDatum_toDescentData_over
          (J := J) (U := U) 𝒰 D I T).inv.hom K ≫
          (localized_cover_descent_pullbackDatum_toDescentData_over
            (J := J) (U := U) 𝒰 D I T).hom.hom K =
            𝟙 (((((J.pseudofunctorOver (Type w)).toDescentData
              (fun L : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ L.f)).obj
              ((J.overMapPullback (Type w) T.hom).obj (D.obj I))).obj K)) := by
      exact congrArg
        (fun f ↦ f.hom K)
        ((localized_cover_descent_pullbackDatum_toDescentData_over
          (J := J) (U := U) 𝒰 D I T).inv_hom_id)
    exact hK

/-- Helper for Lemma 7.26.4: evaluating the arbitrary-`T` source-side comparison at the terminal
object of `Over K.Y` identifies sections of the iterated pullback datum with sections of the
pulled-back component sheaf over the overlap object `Over.mk K.f`. -/
private noncomputable def localized_cover_descent_pullbackDatum_over_section_equiv_component
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow) :
    (((localized_cover_descent_pullbackDatum_over_source
      (J := J) (U := U) 𝒰 D I T).obj K).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y)))) ≃
      ((((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1).obj
        (Opposite.op (Over.mk K.f))) where
  toFun x :=
    cast
      (localized_cover_descent_toDescentData_over_section_eq
        (J := J) (U := U) 𝒰 D I T K)
      ((localized_cover_descent_pullbackDatum_over_component_iso
        (J := J) (U := U) 𝒰 D I T K).hom.hom.app
          (Opposite.op (Over.mk (𝟙 K.Y))) x)
  invFun y :=
    ((localized_cover_descent_pullbackDatum_over_component_iso
      (J := J) (U := U) 𝒰 D I T K).inv.hom.app
        (Opposite.op (Over.mk (𝟙 K.Y)))
        (cast
          (localized_cover_descent_toDescentData_over_section_eq
            (J := J) (U := U) 𝒰 D I T K).symm y))
  left_inv x := by
    -- Undo the target-side section cast and then apply the inverse relation of the `K`-component
    -- comparison isomorphism.
    let e :=
      ((sheafToPresheaf (J.over K.Y) (Type w)).mapIso
        (localized_cover_descent_pullbackDatum_over_component_iso
          (J := J) (U := U) 𝒰 D I T K)).app
        (Opposite.op (Over.mk (𝟙 K.Y)))
    simpa [e] using CategoryTheory.hom_inv_id_apply e x
  right_inv y := by
    -- The same inverse relation shows that a section of the pulled-back component sheaf is
    -- recovered unchanged from the source-side iterated pullback datum.
    let h :=
      localized_cover_descent_toDescentData_over_section_eq
        (J := J) (U := U) 𝒰 D I T K
    let e :=
      ((sheafToPresheaf (J.over K.Y) (Type w)).mapIso
        (localized_cover_descent_pullbackDatum_over_component_iso
          (J := J) (U := U) 𝒰 D I T K)).app
        (Opposite.op (Over.mk (𝟙 K.Y)))
    simpa [e, h] using congrArg (cast h)
      (CategoryTheory.inv_hom_id_apply e (cast h.symm y))

/-- Helper for Lemma 7.26.4: after normalizing the direct pullback along
`((Over.map I.f).obj T).hom` to the iterated pullback cover, this is the direct source-side
descent datum whose terminal sections encode the textbook compatible families over
`((Over.map I.f).obj T)`. -/
private abbrev localized_cover_descent_pullbackDatum_over_direct_source
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :=
  (Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
    (f := fun JI : 𝒰.Arrow ↦ JI.f)
    (p := ((Over.map I.f).obj T).hom)
    (f' := fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ K.f)
    (α := fun K ↦ K.base.base)
    (p' := fun _ ↦ 𝟙 _)
    (w := localized_cover_descent_pullback_over_direct_w (J := J) (U := U) 𝒰 I T)).obj D

/-- Helper for Lemma 7.26.4: on each iterated pullback-cover member `K`, the direct source-side
datum over `((Over.map I.f).obj T)` is canonically identified with the iterated source-side datum.
This isolates the source-faithful direct-to-iterated comparison before compatible families are
packaged as a single subtype. -/
private noncomputable def localized_cover_descent_pullbackDatum_over_direct_component_iso
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow) :
    (localized_cover_descent_pullbackDatum_over_direct_source
      (J := J) (U := U) 𝒰 D I T).obj K ≅
      (localized_cover_descent_pullbackDatum_over_source
        (J := J) (U := U) 𝒰 D I T).obj K where
  hom :=
    (localized_cover_descent_pullbackDatum_over_direct_source_iso
      (J := J) (U := U) 𝒰 D I T).inv.hom K
  inv :=
    (localized_cover_descent_pullbackDatum_over_direct_source_iso
      (J := J) (U := U) 𝒰 D I T).hom.hom K
  hom_inv_id := by
    have hK :
        (localized_cover_descent_pullbackDatum_over_direct_source_iso
          (J := J) (U := U) 𝒰 D I T).inv.hom K ≫
          (localized_cover_descent_pullbackDatum_over_direct_source_iso
            (J := J) (U := U) 𝒰 D I T).hom.hom K =
            𝟙 ((localized_cover_descent_pullbackDatum_over_direct_source
              (J := J) (U := U) 𝒰 D I T).obj K) := by
      exact congrArg
        (fun f ↦ f.hom K)
        ((localized_cover_descent_pullbackDatum_over_direct_source_iso
          (J := J) (U := U) 𝒰 D I T).inv_hom_id)
    exact hK
  inv_hom_id := by
    have hK :
        (localized_cover_descent_pullbackDatum_over_direct_source_iso
          (J := J) (U := U) 𝒰 D I T).hom.hom K ≫
          (localized_cover_descent_pullbackDatum_over_direct_source_iso
            (J := J) (U := U) 𝒰 D I T).inv.hom K =
            𝟙 ((localized_cover_descent_pullbackDatum_over_source
              (J := J) (U := U) 𝒰 D I T).obj K) := by
      exact congrArg
        (fun f ↦ f.hom K)
        ((localized_cover_descent_pullbackDatum_over_direct_source_iso
          (J := J) (U := U) 𝒰 D I T).hom_inv_id)
    exact hK

/-- Helper for Lemma 7.26.4: evaluating the direct source-side pullback datum at the terminal
object of `Over K.Y` and then transporting across the direct-to-iterated comparison recovers the
same component section of the pulled-back sheaf `((J.overMapPullback _ T.hom).obj (D.obj I))` as
the iterated source route. -/
private noncomputable def localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow) :
    (((localized_cover_descent_pullbackDatum_over_direct_source
      (J := J) (U := U) 𝒰 D I T).obj K).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y)))) ≃
      ((((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1).obj
        (Opposite.op (Over.mk K.f))) := by
  -- Route correction: compare the direct pullback along `((Over.map I.f).obj T).hom` with the
  -- already-stabilized iterated pullback source, then reuse the existing section-level bridge to
  -- the pulled-back component sheaf.
  refine (((sheafToPresheaf (J.over K.Y) (Type w)).mapIso
      (localized_cover_descent_pullbackDatum_over_direct_component_iso
        (J := J) (U := U) 𝒰 D I T K)).app
        (Opposite.op (Over.mk (𝟙 K.Y)))).toEquiv.trans ?_
  exact localized_cover_descent_pullbackDatum_over_section_equiv_component
    (J := J) (U := U) 𝒰 D I T K

/-- Helper for Lemma 7.26.4: these are the direct source-side terminal sections on the normalized
direct pullback cover above `((Over.map I.f).obj T)`. They are the explicit textbook families
before one switches to the iterated pullback owner. -/
private abbrev localized_cover_descent_glue_direct_family_over
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :=
  ∀ K : ((𝒰.pullback I.f).pullback T.hom).Arrow,
    (((localized_cover_descent_pullbackDatum_over_direct_source
      (J := J) (U := U) 𝒰 D I T).obj K).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y))))

/-- Helper for Lemma 7.26.4: the compatibility condition on the direct source-side family is
measured after transporting each terminal section to the pulled-back component sheaf. This keeps
the overlap equation on the stable sheaf `((J.overMapPullback _ T.hom).obj (D.obj I)).1`. -/
private def localized_cover_descent_glue_direct_compatible
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (s : localized_cover_descent_glue_direct_family_over (J := J) (U := U) 𝒰 D I T) : Prop :=
  Presieve.Arrows.Compatible
    (((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1)
    (fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦
      (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f))
    (fun K ↦
      localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I T K (s K))

/-- Helper for Lemma 7.26.4: this is the missing direct source-compatible-family subtype from the
source proof. After normalizing the cover `𝒰.pullback ((Over.map I.f).obj T).hom` to the iterated
pullback cover, it records exactly the direct compatible families of terminal sections. -/
private abbrev localized_cover_descent_glue_direct_source_over
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :=
  { s : localized_cover_descent_glue_direct_family_over (J := J) (U := U) 𝒰 D I T //
      localized_cover_descent_glue_direct_compatible
        (J := J) (U := U) 𝒰 D I T s }

/-- Helper for Lemma 7.26.4: transporting each direct source-side component section through the
direct-to-iterated comparison upgrades pointwise to an equivalence of direct families with the
standard component-side family. This is the family-level core of the missing restriction
comparison. -/
private noncomputable def localized_cover_descent_glue_direct_family_equiv
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    localized_cover_descent_glue_direct_family_over (J := J) (U := U) 𝒰 D I T ≃
      (∀ K : ((𝒰.pullback I.f).pullback T.hom).Arrow,
        ((((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1).obj
          (Opposite.op (Over.mk K.f)))) where
  toFun s K :=
    localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
      (J := J) (U := U) 𝒰 D I T K (s K)
  invFun t K :=
    (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
      (J := J) (U := U) 𝒰 D I T K).symm (t K)
  left_inv s := by
    -- Each direct source component is inverted by the corresponding section-level equivalence.
    funext K
    exact
      (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I T K).left_inv (s K)
  right_inv t := by
    -- The same pointwise inverse shows that the transported direct family is unchanged.
    funext K
    exact
      (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I T K).right_inv (t K)

/-- Helper for Lemma 7.26.4: after normalizing the direct pullback cover over
`((Over.map I.f).obj T)`, the direct source-compatible-family subtype is exactly the already
constructed iterated/source-compatible-family subtype. This is the objectwise bridge Agent C
requested before the glued presheaf is packaged into a natural isomorphism. -/
private noncomputable def localized_cover_descent_glue_restrict_obj_equiv_over
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    localized_cover_descent_glue_direct_source_over
      (J := J) (U := U) 𝒰 D I T ≃
      localized_cover_descent_glue_component_source_over
        (J := J) (U := U) 𝒰 D I T where
  toFun s :=
    ⟨localized_cover_descent_glue_direct_family_equiv
      (J := J) (U := U) 𝒰 D I T s.1, s.2⟩
  invFun t :=
    ⟨(localized_cover_descent_glue_direct_family_equiv
      (J := J) (U := U) 𝒰 D I T).symm t.1, by
        -- The direct compatibility predicate is defined by transporting to the component side, so
        -- the inverse family inherits compatibility from `t` verbatim.
        have ht :
            localized_cover_descent_glue_direct_family_equiv
                (J := J) (U := U) 𝒰 D I T
                ((localized_cover_descent_glue_direct_family_equiv
                  (J := J) (U := U) 𝒰 D I T).symm t.1) = t.1 :=
          (localized_cover_descent_glue_direct_family_equiv
            (J := J) (U := U) 𝒰 D I T).right_inv t.1
        exact (congrArg (Presieve.Arrows.Compatible _ _) ht).mpr t.2⟩
  left_inv s := by
    -- The subtype equality reduces to the pointwise inverse for the direct-family equivalence.
    apply Subtype.ext
    funext K
    exact congrFun
      ((localized_cover_descent_glue_direct_family_equiv
        (J := J) (U := U) 𝒰 D I T).left_inv s.1) K
  right_inv t := by
    -- The transported direct compatible family on the component side is recovered verbatim.
    apply Subtype.ext
    funext K
    exact congrFun
      ((localized_cover_descent_glue_direct_family_equiv
        (J := J) (U := U) 𝒰 D I T).right_inv t.1) K

/-- Helper for Lemma 7.26.4: these are the source-side terminal sections on the iterated pullback
cover over `I` and then `T`. They are the arbitrary-`T` precursor to the future glued presheaf
value restricted to `I`. -/
private abbrev localized_cover_descent_pullback_over_family
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :=
  ∀ K : ((𝒰.pullback I.f).pullback T.hom).Arrow,
    (((localized_cover_descent_pullbackDatum_over_source
      (J := J) (U := U) 𝒰 D I T).obj K).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y))))

/-- Helper for Lemma 7.26.4: the source-compatible-family condition on terminal sections of the
iterated pullback datum over `I` and `T` is defined by transporting each section to the ordinary
pulled-back component sheaf. This keeps the remaining arbitrary-`T` compatibility check at the
stable sheaf level from Agent C's plan. -/
private def localized_cover_descent_pullback_over_compatible
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (s : localized_cover_descent_pullback_over_family (J := J) (U := U) 𝒰 D I T) : Prop :=
  Presieve.Arrows.Compatible
    (((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1)
    (fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦
      (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f))
    (fun K ↦
      localized_cover_descent_pullbackDatum_over_section_equiv_component
        (J := J) (U := U) 𝒰 D I T K (s K))

/-- Helper for Lemma 7.26.4: the pointwise arbitrary-`T` section comparison upgrades to an
equivalence of the underlying families on the iterated pullback cover over `I` and then `T`. -/
private noncomputable def localized_cover_descent_pullback_over_family_equiv
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    localized_cover_descent_pullback_over_family (J := J) (U := U) 𝒰 D I T ≃
      (∀ K : ((𝒰.pullback I.f).pullback T.hom).Arrow,
        ((((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1).obj
          (Opposite.op (Over.mk K.f)))) where
  toFun s K :=
    localized_cover_descent_pullbackDatum_over_section_equiv_component
      (J := J) (U := U) 𝒰 D I T K (s K)
  invFun t K :=
    (localized_cover_descent_pullbackDatum_over_section_equiv_component
      (J := J) (U := U) 𝒰 D I T K).symm (t K)
  left_inv s := by
    -- Each arbitrary-`T` component is inverted by the corresponding section-level equivalence.
    funext K
    exact
      (localized_cover_descent_pullbackDatum_over_section_equiv_component
        (J := J) (U := U) 𝒰 D I T K).left_inv (s K)
  right_inv t := by
    -- The same pointwise inverse shows that the transported arbitrary-`T` family is unchanged.
    funext K
    exact
      (localized_cover_descent_pullbackDatum_over_section_equiv_component
        (J := J) (U := U) 𝒰 D I T K).right_inv (t K)

/-- Helper for Lemma 7.26.4: after rewriting each arbitrary-`T` component section by the
iterated-pullback comparison, the source-side subtype of compatible families is exactly the
standard subtype of compatible sections of the pulled-back component sheaf. This is the stable
arbitrary-`T` bridge that remains after the earlier transport block. -/
private noncomputable def localized_cover_descent_pullback_over_compatible_equiv
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    { s : localized_cover_descent_pullback_over_family (J := J) (U := U) 𝒰 D I T //
        localized_cover_descent_pullback_over_compatible
          (J := J) (U := U) 𝒰 D I T s } ≃
      localized_cover_descent_glue_component_source_over
        (J := J) (U := U) 𝒰 D I T where
  toFun s :=
    ⟨localized_cover_descent_pullback_over_family_equiv
      (J := J) (U := U) 𝒰 D I T s.1, s.2⟩
  invFun t :=
    ⟨(localized_cover_descent_pullback_over_family_equiv
      (J := J) (U := U) 𝒰 D I T).symm t.1, by
        -- The source-side compatibility predicate is defined by transporting to the component
        -- side, so the inverse family inherits compatibility from `t` verbatim.
        have ht :
            localized_cover_descent_pullback_over_family_equiv
                (J := J) (U := U) 𝒰 D I T
                ((localized_cover_descent_pullback_over_family_equiv
                  (J := J) (U := U) 𝒰 D I T).symm t.1) = t.1 :=
          (localized_cover_descent_pullback_over_family_equiv
            (J := J) (U := U) 𝒰 D I T).right_inv t.1
        exact (congrArg (Presieve.Arrows.Compatible _ _) ht).mpr t.2⟩
  left_inv s := by
    -- The subtype equality reduces to the pointwise inverse for the arbitrary-`T` family
    -- equivalence.
    apply Subtype.ext
    funext K
    exact congrFun
      ((localized_cover_descent_pullback_over_family_equiv
        (J := J) (U := U) 𝒰 D I T).left_inv s.1) K
  right_inv t := by
    -- The transported arbitrary-`T` compatible family on the component side is recovered
    -- verbatim.
    apply Subtype.ext
    funext K
    exact congrFun
      ((localized_cover_descent_pullback_over_family_equiv
        (J := J) (U := U) 𝒰 D I T).right_inv t.1) K

/-- Helper for Lemma 7.26.4: this is the source-proof family
`V/U ↦ ∏ₖ Fₖ(K ×ᵤ V)` before imposing the overlap equations. Each component is a section of the
pulled-back descent datum over the terminal object of the localized slice above `K.Y`. -/
private abbrev localized_cover_descent_glue_family
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (V : Over U) :=
  ∀ K : (𝒰.pullback V.hom).Arrow,
    (((localized_cover_descent_pullbackDatum
      (J := J) (U := U) 𝒰 D V).obj K).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y))))

/-- Helper for Lemma 7.26.4: this is the textbook overlap condition for a family of local sections
over the pullback cover of `V/U`. We first restrict both sections to the overlap object `R.r.Z`,
then compare them using the descent transition map of the pulled-back datum. -/
private def localized_cover_descent_glue_compatible
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (V : Over U)
    (s : localized_cover_descent_glue_family (J := J) (U := U) 𝒰 D V) : Prop :=
  let P := localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D V
  ∀ R : (𝒰.pullback V.hom).Relation,
    (P.hom (R.r.g₁ ≫ R.fst.f) R.r.g₁ R.r.g₂ rfl R.r.w.symm).hom.app
        (Opposite.op (Over.mk (𝟙 R.r.Z)))
        (cast
          (localized_cover_descent_pullbackDatum_section_eq
            (J := J) (U := U) 𝒰 D V R.fst R.r.g₁).symm
          (((P.obj R.fst).1.map (Over.homMk R.r.g₁).op) (s R.fst))) =
      cast
        (localized_cover_descent_pullbackDatum_section_eq
          (J := J) (U := U) 𝒰 D V R.snd R.r.g₂).symm
        (((P.obj R.snd).1.map (Over.homMk R.r.g₂).op) (s R.snd))

/-- Helper for Lemma 7.26.4: this packages the source-proof compatible family on the pullback
cover of `V/U`. The remaining presheaf step is to show that reindexing along `g : V ⟶ W`
preserves this predicate. -/
private abbrev localized_cover_descent_glue_value
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (V : Over U) :=
  { s : localized_cover_descent_glue_family (J := J) (U := U) 𝒰 D V //
      localized_cover_descent_glue_compatible
        (J := J) (U := U) 𝒰 D V s }

/-- Helper for Lemma 7.26.4: when `V = Uᵢ/U`, the underlying family in
`localized_cover_descent_glue_value` is literally the terminal-section family used by the fixed
component comparison over `I`. This identifies the main controlled source object without yet
repackaging its compatibility predicate. -/
private theorem localized_cover_descent_glue_family_over_arrow
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :
    localized_cover_descent_glue_family (J := J) (U := U) 𝒰 D (Over.mk I.f) =
      (∀ K : (𝒰.pullback I.f).Arrow,
        (((localized_cover_descent_pullbackDatum
          (J := J) (U := U) 𝒰 D (Over.mk I.f)).obj K).1.obj
            (Opposite.op (Over.mk (𝟙 K.Y))))) := rfl

/-- Helper for Lemma 7.26.4: the textbook family of terminal sections for the pullback datum over
`I` is identified pointwise with the family of sections of the fixed component sheaf `D.obj I`
over the overlap objects `Over.mk K.f`. -/
private abbrev localized_cover_descent_pullback_terminal_family
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :=
  ∀ K : (𝒰.pullback I.f).Arrow,
    (((localized_cover_descent_pullbackDatum
      (J := J) (U := U) 𝒰 D (Over.mk I.f)).obj K).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y))))

/-- Helper for Lemma 7.26.4: this is the fixed-component family on the pullback cover over `I`
that the textbook compatible-family formula should recover after reindexing. -/
private abbrev localized_cover_descent_component_terminal_family
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :=
  ∀ K : (𝒰.pullback I.f).Arrow,
    ((D.obj I).1.obj (Opposite.op (Over.mk K.f)))

/-- Helper for Lemma 7.26.4: the pullback-cover arrows over a chosen member `I` are the induced
arrows into the terminal object `I.Y / I.Y` of the localized site. -/
private abbrev localized_cover_descent_component_terminal_arrow
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (K : (𝒰.pullback I.f).Arrow) :
    Over.mk K.f ⟶ Over.mk (𝟙 I.Y) :=
  Over.homMk K.f

/-- Helper for Lemma 7.26.4: the source-compatible-family condition on terminal sections of the
pullback datum over `I` is just the ordinary compatibility condition after translating each
component section to the fixed sheaf `D.obj I`. -/
private def localized_cover_descent_pullback_terminal_compatible
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (s : localized_cover_descent_pullback_terminal_family (J := J) (U := U) 𝒰 D I) : Prop :=
  Presieve.Arrows.Compatible ((D.obj I).1)
    (fun K : (𝒰.pullback I.f).Arrow ↦
      localized_cover_descent_component_terminal_arrow (J := J) (U := U) 𝒰 I K)
    (fun K ↦
      localized_cover_descent_pullbackDatum_section_equiv_component
        (J := J) (U := U) 𝒰 D I K (s K))

/-- Helper for Lemma 7.26.4: the pointwise section comparison over a chosen cover member `I`
upgrades to an equivalence of the underlying families indexed by `𝒰.pullback I.f`. -/
private noncomputable def localized_cover_descent_pullback_component_family_equiv
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :
    localized_cover_descent_pullback_terminal_family (J := J) (U := U) 𝒰 D I ≃
      localized_cover_descent_component_terminal_family (J := J) (U := U) 𝒰 D I where
  toFun s K :=
    localized_cover_descent_pullbackDatum_section_equiv_component
      (J := J) (U := U) 𝒰 D I K (s K)
  invFun t K :=
    (localized_cover_descent_pullbackDatum_section_equiv_component
      (J := J) (U := U) 𝒰 D I K).symm (t K)
  left_inv s := by
    -- Each component is inverted by the corresponding section-level equivalence.
    funext K
    exact
      (localized_cover_descent_pullbackDatum_section_equiv_component
        (J := J) (U := U) 𝒰 D I K).left_inv (s K)
  right_inv t := by
    -- The same pointwise inverse shows that the transported component family is unchanged.
    funext K
    exact
      (localized_cover_descent_pullbackDatum_section_equiv_component
        (J := J) (U := U) 𝒰 D I K).right_inv (t K)

/-- Helper for Lemma 7.26.4: after rewriting each component section by the pullback-datum
comparison, compatible families on the source side and on the fixed component side are the same
subtype. This isolates the terminal-object comparison already proved in the file. -/
private noncomputable def localized_cover_descent_pullback_terminal_compatible_equiv
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :
    { s : localized_cover_descent_pullback_terminal_family (J := J) (U := U) 𝒰 D I //
        localized_cover_descent_pullback_terminal_compatible
          (J := J) (U := U) 𝒰 D I s } ≃
      { t : localized_cover_descent_component_terminal_family (J := J) (U := U) 𝒰 D I //
          Presieve.Arrows.Compatible ((D.obj I).1)
            (fun K : (𝒰.pullback I.f).Arrow ↦
              localized_cover_descent_component_terminal_arrow (J := J) (U := U) 𝒰 I K)
            t } where
  toFun s :=
    ⟨localized_cover_descent_pullback_component_family_equiv
      (J := J) (U := U) 𝒰 D I s.1, s.2⟩
  invFun t :=
    ⟨(localized_cover_descent_pullback_component_family_equiv
      (J := J) (U := U) 𝒰 D I).symm t.1, by
        -- The left-hand compatibility predicate is defined by transporting to the component side.
        have ht :
            localized_cover_descent_pullback_component_family_equiv
                (J := J) (U := U) 𝒰 D I
                ((localized_cover_descent_pullback_component_family_equiv
                  (J := J) (U := U) 𝒰 D I).symm t.1) = t.1 :=
          (localized_cover_descent_pullback_component_family_equiv
            (J := J) (U := U) 𝒰 D I).right_inv t.1
        simpa [localized_cover_descent_pullback_terminal_compatible,
          localized_cover_descent_pullback_component_family_equiv, ht] using t.2⟩
  left_inv s := by
    -- The subtype equality reduces to the pointwise inverse for the family equivalence.
    apply Subtype.ext
    funext K
    exact congrFun
      ((localized_cover_descent_pullback_component_family_equiv
        (J := J) (U := U) 𝒰 D I).left_inv s.1) K
  right_inv t := by
    -- The transported compatible family on the fixed component side is recovered verbatim.
    apply Subtype.ext
    funext K
    exact congrFun
      ((localized_cover_descent_pullback_component_family_equiv
        (J := J) (U := U) 𝒰 D I).right_inv t.1) K

/-- Helper for Lemma 7.26.4: on a source-compatible family over the pullback cover above `I`,
the forward subtype equivalence simply applies the pointwise section comparison on each component.
This is the explicit component formula needed when the future glued presheaf is restricted to `I`.
-/
private theorem localized_cover_descent_pullback_terminal_compatible_equiv_apply_val
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (s :
      { s : localized_cover_descent_pullback_terminal_family (J := J) (U := U) 𝒰 D I //
          localized_cover_descent_pullback_terminal_compatible
            (J := J) (U := U) 𝒰 D I s })
    (K : (𝒰.pullback I.f).Arrow) :
    ((localized_cover_descent_pullback_terminal_compatible_equiv
      (J := J) (U := U) 𝒰 D I s).1 K) =
      localized_cover_descent_pullbackDatum_section_equiv_component
        (J := J) (U := U) 𝒰 D I K (s.1 K) := by
  -- The forward subtype equivalence is defined by the pointwise family equivalence.
  rfl

/-- Helper for Lemma 7.26.4: on a compatible family of sections of the fixed component sheaf
`D.obj I`, the inverse subtype equivalence simply applies the inverse pointwise section
comparison on each overlap component. This is the explicit reconstruction formula for the source
family that the future glued presheaf will use.
-/
private theorem localized_cover_descent_pullback_terminal_compatible_equiv_symm_val
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (t :
      { t : localized_cover_descent_component_terminal_family (J := J) (U := U) 𝒰 D I //
          Presieve.Arrows.Compatible ((D.obj I).1)
            (fun K : (𝒰.pullback I.f).Arrow ↦
              localized_cover_descent_component_terminal_arrow (J := J) (U := U) 𝒰 I K)
            t })
    (K : (𝒰.pullback I.f).Arrow) :
    (((localized_cover_descent_pullback_terminal_compatible_equiv
      (J := J) (U := U) 𝒰 D I).symm t).1 K) =
      (localized_cover_descent_pullbackDatum_section_equiv_component
        (J := J) (U := U) 𝒰 D I K).symm (t.1 K) := by
  -- The inverse subtype equivalence is defined by the inverse pointwise family equivalence.
  rfl

/-- Helper for Lemma 7.26.4: the ordinary Hom sheaf on `J.over U` is a sheaf for the induced
terminal cover coming from `𝒰`. This isolates the slice-site input needed by the fixed-cover
fully-faithfulness route. -/
private theorem localized_cover_descent_sheafHom_isSheafFor_terminal_cover
    (𝒰 : J.Cover U)
    (M N : Sheaf (J.over U) (Type w)) :
    Presieve.IsSheafFor
      ((CategoryTheory.sheafHom (J := J.over U) M N).1)
      ((localized_cover_descent_terminal_cover (J := J) (U := U) 𝒰 : (J.over U).Cover
        (Over.mk (𝟙 U))).1.arrows) := by
  -- The ordinary internal Hom on the slice site is already a sheaf, so it satisfies the sheaf
  -- condition for every covering sieve in `J.over U`, in particular for the induced terminal cover.
  exact Presheaf.IsSheaf.isSheafFor
    ((CategoryTheory.sheafHom (J := J.over U) M N).2)
    (localized_cover_descent_terminal_cover (J := J) (U := U) 𝒰).1
    (localized_cover_descent_terminal_cover (J := J) (U := U) 𝒰).condition

/- Helper for Lemma 7.26.4: restricting a global section of the ordinary slice-site Hom sheaf
along a terminal-cover arrow matches the corresponding component of the owner-side descent datum
map after transporting through the canonical objectwise Hom equivalences. -/
/-
private theorem localized_cover_descent_terminal_component_restrict_eq
    (𝒰 : J.Cover U)
    {M N : Sheaf (J.over U) (Type w)}
    (ψ : M ⟶ N)
    (I : (localized_cover_descent_terminal_cover (J := J) (U := U) 𝒰).Arrow) :
    localized_pseudofunctorOver_presheafHom_obj_equiv (J := J) (U := U) I.Y M N
      (((CategoryTheory.sheafHom (J := J.over U) M N).1).map I.f.op
        ((localized_pseudofunctorOver_presheafHom_base_equiv
          (J := J) (U := U) M N).symm ψ)) =
      (((J.pseudofunctorOver (Type w)).presheafHom M N).map I.f.op
        (localized_pseudofunctorOver_presheafHom_obj_equiv (J := J) (U := U)
          (Over.mk (𝟙 U)) M N
          ((localized_pseudofunctorOver_presheafHom_base_equiv
            (J := J) (U := U) M N).symm ψ))) := by
  -- The fixed-cover restriction identity is the terminal-object specialization of the presheaf
  -- comparison naturality, after normalizing the base section on the owner side.
  simpa [localized_pseudofunctorOver_presheafHom_base_equiv_apply
    (J := J) (U := U) (ψ := ψ)] using
    congrFun
      ((localized_pseudofunctorOver_presheafHom_iso
        (J := J) (U := U) M N).hom.naturality I.f.op)
      ((localized_pseudofunctorOver_presheafHom_base_equiv
        (J := J) (U := U) M N).symm ψ)
-/
 
-- Before comparing with the owner-side `pullHom`, first expose the ordinary `sheafHom`
-- restriction map in its concrete localized-pullback form.
/-- Helper for Lemma 7.26.4: descent for morphisms on the fixed cover `𝒰` is already covered by
the slice-site Hom-sheaf theorem from Lemma `7.26.1`, so the associated descent-data functor is
fully faithful without using any object-level gluing. -/
private noncomputable def localized_cover_descent_fullyFaithful
    (𝒰 : J.Cover U) :
    ((J.pseudofunctorOver (Type w)).toDescentData
      (fun I : 𝒰.Arrow ↦ I.f)).FullyFaithful := by
  -- The owner-side Hom presheaf is definitionally the ordinary slice-site Hom sheaf, so the
  -- generic morphism-descent criterion only needs the terminal-cover sheaf condition.
  exact ((Functor.FullyFaithful.nonempty_iff_map_bijective
    (F := (J.pseudofunctorOver (Type w)).toDescentData
      (fun I : 𝒰.Arrow ↦ I.f))).2 (fun M N ↦ by
        -- The generic descent criterion reduces bijectivity to the sheaf condition for the
        -- owner-side Hom presheaf on the induced terminal cover of `U/U`. Transport the sheaf
        -- condition across the Hom-presheaf comparison before invoking the slice-site result.
        rw [Pseudofunctor.bijective_toDescentData_map_iff]
        let R :
            Presieve (Over.mk (𝟙 U)) :=
          Presieve.ofArrows (fun I : 𝒰.Arrow ↦ Over.mk I.f)
            (fun I ↦ show Over.mk I.f ⟶ Over.mk (𝟙 U) from Over.homMk I.f)
        have hsheaf_generate :
            Presieve.IsSheafFor
              ((CategoryTheory.sheafHom (J := J.over U) M N).1)
              (Sieve.generate R).arrows := by
          simpa [R, localized_cover_descent_terminal_cover, Sieve.ofArrows] using
            localized_cover_descent_sheafHom_isSheafFor_terminal_cover
              (J := J) (U := U) 𝒰 M N
        have hsheaf :
            Presieve.IsSheafFor
              ((CategoryTheory.sheafHom (J := J.over U) M N).1) R :=
          (Presieve.isSheafFor_iff_generate R).2 hsheaf_generate
        exact
          (Presieve.isSheafFor_iff_of_iso
            (localized_pseudofunctorOver_presheafHom_iso
              (J := J) (U := U) M N)).1
            hsheaf)).some

/-- Helper for Lemma 7.26.4: morphism descent on the fixed cover `𝒰` is already settled by the
fully faithful descent-data functor, so the remaining work in this file is purely object-level
gluing. -/
private theorem localized_cover_descent_isPrestackFor
    (𝒰 : J.Cover U) :
    (J.pseudofunctorOver (Type w)).IsPrestackFor
      (Presieve.ofArrows _ (fun I : 𝒰.Arrow ↦ I.f)) := by
  -- Package the fully faithful descent-data functor as the owner-side prestack statement.
  rw [Pseudofunctor.isPrestackFor_ofArrows_iff]
  exact ⟨localized_cover_descent_fullyFaithful (J := J) (U := U) 𝒰⟩

/-- Helper for Lemma 7.26.4: once the future glued presheaf is restricted to a fixed cover member
`I`, its objectwise comparison with the given component sheaf is exactly the composite of the
direct-source normalization and the already-proved component gluing equivalence. -/
private noncomputable def localized_cover_descent_glue_component_obj_equiv_over
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    localized_cover_descent_glue_direct_source_over
      (J := J) (U := U) 𝒰 D I T ≃
      ((D.obj I).1.obj (Opposite.op T)) :=
  -- First rewrite the restricted glued value into the stable component-side subtype, then glue
  -- that compatible family inside the sheaf `D.obj I`.
  (localized_cover_descent_glue_restrict_obj_equiv_over
    (J := J) (U := U) 𝒰 D I T).trans
    (localized_cover_descent_glue_component_equiv_over
      (J := J) (U := U) 𝒰 D I T)

/-- Helper for Lemma 7.26.4: applying the new objectwise comparison after the direct-source
normalization is definitionally the same composite that will later become the component of the
restriction `NatIso`. -/
private theorem localized_cover_descent_glue_component_obj_equiv_over_apply
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (s :
      localized_cover_descent_glue_direct_source_over
        (J := J) (U := U) 𝒰 D I T) :
    localized_cover_descent_glue_component_obj_equiv_over
        (J := J) (U := U) 𝒰 D I T s =
      localized_cover_descent_glue_component_equiv_over
        (J := J) (U := U) 𝒰 D I T
        (localized_cover_descent_glue_restrict_obj_equiv_over
          (J := J) (U := U) 𝒰 D I T s) := by
  -- The objectwise comparison is defined as this composite equivalence.
  rfl

/-- Helper for Lemma 7.26.4: the objectwise comparison over `T` is a genuine equivalence, so
transporting a section of `D.obj I` back to the direct-source compatible family and then forward
again recovers the original section. -/
private theorem localized_cover_descent_glue_component_obj_equiv_over_apply_symm
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (t : (D.obj I).1.obj (Opposite.op T)) :
    localized_cover_descent_glue_component_obj_equiv_over
        (J := J) (U := U) 𝒰 D I T
        ((localized_cover_descent_glue_component_obj_equiv_over
          (J := J) (U := U) 𝒰 D I T).symm t) =
      t := by
  -- This is the right-inverse identity for the explicit composite equivalence above.
  exact Equiv.apply_symm_apply
    (localized_cover_descent_glue_component_obj_equiv_over
      (J := J) (U := U) 𝒰 D I T)
    t

/-- Helper for Lemma 7.26.4: after moving a section of `D.obj I` back through the objectwise
comparison, applying the direct-source normalization alone recovers exactly the inverse of the
component-side gluing equivalence. This isolates the normalization half of the future naturality
square. -/
private theorem localized_cover_descent_glue_component_obj_equiv_over_symm_restrict
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (t : (D.obj I).1.obj (Opposite.op T)) :
    localized_cover_descent_glue_restrict_obj_equiv_over
        (J := J) (U := U) 𝒰 D I T
        ((localized_cover_descent_glue_component_obj_equiv_over
          (J := J) (U := U) 𝒰 D I T).symm t) =
      (localized_cover_descent_glue_component_equiv_over
        (J := J) (U := U) 𝒰 D I T).symm t := by
  -- Compare both candidates after applying the component-side gluing equivalence; this avoids
  -- reopening the transport-heavy definition of the composite objectwise equivalence.
  apply
    (localized_cover_descent_glue_component_equiv_over
      (J := J) (U := U) 𝒰 D I T).injective
  calc
    localized_cover_descent_glue_component_equiv_over
        (J := J) (U := U) 𝒰 D I T
        (localized_cover_descent_glue_restrict_obj_equiv_over
          (J := J) (U := U) 𝒰 D I T
          ((localized_cover_descent_glue_component_obj_equiv_over
            (J := J) (U := U) 𝒰 D I T).symm t)) =
      localized_cover_descent_glue_component_obj_equiv_over
        (J := J) (U := U) 𝒰 D I T
        ((localized_cover_descent_glue_component_obj_equiv_over
          (J := J) (U := U) 𝒰 D I T).symm t) := by
        rfl
    _ = t := localized_cover_descent_glue_component_obj_equiv_over_apply_symm
      (J := J) (U := U) 𝒰 D I T t
    _ =
      localized_cover_descent_glue_component_equiv_over
        (J := J) (U := U) 𝒰 D I T
        ((localized_cover_descent_glue_component_equiv_over
          (J := J) (U := U) 𝒰 D I T).symm t) := by
        symm
        exact Equiv.apply_symm_apply
          (localized_cover_descent_glue_component_equiv_over
            (J := J) (U := U) 𝒰 D I T)
          t

/-- Helper for Lemma 7.26.4: the source-facing gluing step is exactly the existence of a sheaf on
`J.over U` whose fixed-cover descent datum is isomorphic to the given datum `D`. -/
private theorem localized_cover_descent_glued_exists
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰) :
    ∃ M : Sheaf (J.over U) (Type w),
      Nonempty (((J.pseudofunctorOver (Type w)).toDescentData
        (fun I : 𝒰.Arrow ↦ I.f)).obj M ≅ D) := by
  -- Route correction: the attempted owner-level shortcut via `Pseudofunctor.isStackFor'` does not
  -- apply here because there is no available instance
  -- `(J.pseudofunctorOver (Type w)).IsStack J`. The remaining source-faithful work is therefore
  -- exactly Agent C's Step 1--5 construction: define the global compatible-family presheaf, prove
  -- the restriction-object normalization over `I`, package the natural transformation to `D.obj I`,
  -- and only then sheafify and assemble the descent-data isomorphism.
  -- TODO: the objectwise restricted comparison is now frozen as
  -- `localized_cover_descent_glue_component_obj_equiv_over`. The remaining blocker is to prove
  -- its naturality in `T`, promote it to the missing `localized_cover_descent_glue_component_natIso`,
  -- and then compose that NatIso with `sheafifyComposeIso` and `isoSheafify`.
  sorry

/-- Helper for Lemma 7.26.4: for a fixed descent datum `D` on `𝒰`, the owner-level stack theorem
directly places `D` in the essential image of the descent-data functor once the glued sheaf has
been constructed. -/
private theorem localized_cover_descent_glued_witness
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰) :
    (((J.pseudofunctorOver (Type w)).toDescentData
      (fun I : 𝒰.Arrow ↦ I.f)).essImage D) := by
  -- Route correction: the remaining object-side task is now isolated to a single essential-image
  -- witness for `D`, so later packaging lemmas do not have to keep reproving the existential
  -- wrapper around the glued sheaf and its descent-data isomorphism.
  rcases localized_cover_descent_glued_exists (J := J) (U := U) 𝒰 D with ⟨M, hM⟩
  exact ⟨M, hM⟩

/-- Helper for Lemma 7.26.4: for a fixed descent datum `D` on `𝒰`, unpacking the essential-image
package produces a sheaf together with the comparison isomorphism needed in the source-facing
existential statement. -/
private theorem localized_cover_descent_essImage_iff_exists_iso
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰) :
    (((J.pseudofunctorOver (Type w)).toDescentData
      (fun I : 𝒰.Arrow ↦ I.f)).essImage D) ↔
      ∃ M : Sheaf (J.over U) (Type w),
        Nonempty (((J.pseudofunctorOver (Type w)).toDescentData
          (fun I : 𝒰.Arrow ↦ I.f)).obj M ≅ D) := by
  -- An essential-image witness is exactly a source object together with an isomorphism to `D`.
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨M, hM⟩
  · rintro ⟨M, hM⟩
    exact ⟨M, hM⟩

/-- Helper for Lemma 7.26.4: for a fixed descent datum `D` on `𝒰`, unpacking the essential-image
package produces a sheaf together with the comparison isomorphism needed in the source-facing
existential statement. -/
private theorem localized_cover_descent_glued_object
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰) :
    ∃ M : Sheaf (J.over U) (Type w),
      Nonempty (((J.pseudofunctorOver (Type w)).toDescentData
        (fun I : 𝒰.Arrow ↦ I.f)).obj M ≅ D) := by
  -- The isolated source-facing gluing theorem is the existential statement needed later.
  exact localized_cover_descent_glued_exists (J := J) (U := U) 𝒰 D

/-- Helper for Lemma 7.26.4: once a glued sheaf `M` is accompanied by an isomorphism from its
fixed-cover descent datum to `D`, the corresponding essential-image witness is just the standard
`Functor.essImage` package. -/
private theorem localized_cover_descent_mem_essImage_of_iso
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (M : Sheaf (J.over U) (Type w))
    (e : ((J.pseudofunctorOver (Type w)).toDescentData
      (fun I : 𝒰.Arrow ↦ I.f)).obj M ≅ D) :
    (((J.pseudofunctorOver (Type w)).toDescentData
      (fun I : 𝒰.Arrow ↦ I.f)).essImage D) := by
  -- Package the glued sheaf and its comparison isomorphism into the essential-image witness.
  exact ⟨M, ⟨e⟩⟩

/-- Helper for Lemma 7.26.4: once the glued sheaf for `D` is available together with its
comparison isomorphism to `D`, the essential-image witness is just the standard packaging. -/
private theorem localized_cover_descent_mem_essImage
    (𝒰 : J.Cover U)
    (D : (J.pseudofunctorOver (Type w)).DescentData (fun I : 𝒰.Arrow ↦ I.f)) :
    (((J.pseudofunctorOver (Type w)).toDescentData
      (fun I : 𝒰.Arrow ↦ I.f)).essImage D) := by
  -- The isolated witness theorem records exactly the remaining gluing task for this file.
  exact localized_cover_descent_glued_witness (J := J) (U := U) 𝒰 D

/-- Helper for Lemma 7.26.4: the descent-data functor attached to a fixed cover `𝒰` of `U` is
essentially surjective. This isolates the glued-sheaf construction so the owner-level stack
statement and the public source-facing statement reuse the same witness. -/
private theorem localized_cover_descent_essSurj
    (𝒰 : J.Cover U) :
    ((J.pseudofunctorOver (Type w)).toDescentData
      (fun I : 𝒰.Arrow ↦ I.f)).EssSurj := by
  -- Package the objectwise essential-image witnesses obtained from the fixed-cover stack theorem.
  refine localized_cover_descent_essSurj_of_glued_objects (J := J) (U := U) 𝒰 ?_
  intro D
  exact localized_cover_descent_mem_essImage (J := J) (U := U) 𝒰 D

/-- Owner-level companion to Lemma 7.26.4: for a fixed cover `𝒰`, the localized sheaf
pseudofunctor satisfies effective descent for the presieve generated by the cover arrows. -/
theorem localizedSheafPseudofunctorOver_isStackFor_cover
    (𝒰 : J.Cover U) :
    (J.pseudofunctorOver (Type w)).IsStackFor
      (Presieve.ofArrows _ (fun I : 𝒰.Arrow ↦ I.f)) := by
  -- Route correction: the owner theorem now uses the standard `FullyFaithful + EssSurj`
  -- packaging, so the only unresolved mathematics is the direct essential-image witness.
  rw [Pseudofunctor.isStackFor_ofArrows_iff]
  let hFullyFaithful :
      ((J.pseudofunctorOver (Type w)).toDescentData
        (fun I : 𝒰.Arrow ↦ I.f)).FullyFaithful :=
    localized_cover_descent_fullyFaithful (J := J) (U := U) 𝒰
  let hEssSurj :
      ((J.pseudofunctorOver (Type w)).toDescentData
        (fun I : 𝒰.Arrow ↦ I.f)).EssSurj :=
    localized_cover_descent_essSurj (J := J) (U := U) 𝒰
  exact
    { faithful := hFullyFaithful.faithful
      full := hFullyFaithful.full
      essSurj := hEssSurj }

/-- Lemma 7.26.4: for a covering `𝒰` of `U`, the canonical descent-data functor from sheaves on
the localized site `C / U` to coverwise glueing data on `𝒰` is essentially surjective. -/
theorem localizedSheafToCoverDescentFunctor_essSurj (𝒰 : J.Cover U) :
    ((J.pseudofunctorOver (Type _)).toDescentData fun I : 𝒰.Arrow ↦ I.f).EssSurj := by
  -- Read the source-facing statement directly from the fixed-cover essential-surjectivity witness.
  simpa using localized_cover_descent_essSurj (J := J) (U := U) 𝒰

end

end GrothendieckTopology
end CategoryTheory
