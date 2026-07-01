import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u w

namespace CategoryTheory
namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/- Domain-style sampling for Lemma 7.26.6:
- primary domain: sheaf descent along the slice-site pseudofunctor `U ↦ Sh(C/U)`;
- sampled owner API:
  `GrothendieckTopology.pseudofunctorOver`,
  `GrothendieckTopology.overMapPullback`,
  `GrothendieckTopology.overMapPullbackId`,
  `Functor.sheafPushforwardContinuousComp'`;
- source-facing layer: `AbsoluteGlueing J`, the textbook datum of sheaves on all slice sites
  `C/U` with pullback comparison isomorphisms and cocycle compatibility;
- core/canonical owner: strong/cartesian sections of the slice-site sheaf pseudofunctor
  `J.pseudofunctorOver (Type w)`;
- bridge/view: the concrete transition maps `transition f`, which unpack that owner-level action
  entrywise.

Primitive data here are exactly the local sheaves `obj U` and the transition isomorphisms
`transition f`. The category structure on these data is derived API. There is an upstream owner
view via strong transformations into `J.pseudofunctorOver (Type w)`, but exposing that directly
would replace the textbook family-of-sheaves surface by terminal-category plumbing. This lemma
therefore keeps the source-facing object while reusing the owner pullback API and keeping the
derived category layer minimal.
-/

/-- An absolute glueing on a site consists of a sheaf on each localization `C/U`, together with
pullback isomorphisms along morphisms in `C` satisfying the usual identity and cocycle
compatibilities. -/
structure AbsoluteGlueing where
  /-- The local sheaf on the slice site `C/U`. -/
  obj (U : C) : Sheaf (J.over U) (Type w)
  /-- Pulling back the local sheaf on `C/U` along `f : V ⟶ U` identifies it with the local sheaf on
  `C/V`. -/
  transition {U V : C} (f : V ⟶ U) :
      (J.overMapPullback (Type w) f).obj (obj U) ≅ obj V
  /-- The transition attached to an identity morphism is the canonical identity pullback
  isomorphism. -/
  transition_id (U : C) :
      transition (𝟙 U) = (J.overMapPullbackId (Type w) U).app (obj U)
  /-- The transitions satisfy the expected cocycle condition for composable morphisms. -/
  transition_comp {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
      (J.overMapPullbackComp (Type w) g f).app (obj U) ≪≫ transition (g ≫ f) =
        (J.overMapPullback (Type w) g).mapIso (transition f) ≪≫ transition g

namespace AbsoluteGlueing

/-- A morphism of absolute glueings is a family of local morphisms compatible with the
transition isomorphisms. -/
@[ext] structure Hom (F G : AbsoluteGlueing J) where
  /-- The component on the localization at `U`. -/
  app (U : C) : F.obj U ⟶ G.obj U
  /-- Compatibility of the local components with pullback along morphisms. -/
  naturality {U V : C} (f : V ⟶ U) :
      CommSq ((J.overMapPullback (Type w) f).map (app U))
        (F.transition f).hom (G.transition f).hom (app V)

private theorem absoluteGlueing_id_naturality (F : AbsoluteGlueing J) :
    ∀ {U V : C} (f : V ⟶ U),
      CommSq ((J.overMapPullback (Type w) f).map (𝟙 (F.obj U)))
        (F.transition f).hom (F.transition f).hom (𝟙 (F.obj V)) := by
  intro U V f
  exact .mk (by simp)

private def absoluteGlueingId (F : AbsoluteGlueing J) :
    AbsoluteGlueing.Hom J F F where
  app U := 𝟙 (F.obj U)
  naturality := absoluteGlueing_id_naturality J F

private theorem absoluteGlueing_comp_naturality
    {F G H : AbsoluteGlueing J} (α : AbsoluteGlueing.Hom J F G)
    (β : AbsoluteGlueing.Hom J G H) :
    ∀ {U V : C} (f : V ⟶ U),
      CommSq ((J.overMapPullback (Type w) f).map (α.app U ≫ β.app U))
        (F.transition f).hom (H.transition f).hom (α.app V ≫ β.app V) := by
  intro U V f
  exact .mk <| by
    rw [Functor.map_comp, Category.assoc, (β.naturality f).w]
    rw [← Category.assoc, (α.naturality f).w]
    simp [Category.assoc]

private def absoluteGlueingComp
    {F G H : AbsoluteGlueing J} (α : AbsoluteGlueing.Hom J F G)
    (β : AbsoluteGlueing.Hom J G H) :
    AbsoluteGlueing.Hom J F H where
  app U := α.app U ≫ β.app U
  naturality := absoluteGlueing_comp_naturality J α β

private theorem absoluteGlueing_id_comp
    {F G : AbsoluteGlueing J} (α : AbsoluteGlueing.Hom J F G) :
    absoluteGlueingComp J (absoluteGlueingId J F) α = α := by
  ext U
  simp [absoluteGlueingComp, absoluteGlueingId]

private theorem absoluteGlueing_comp_id
    {F G : AbsoluteGlueing J} (α : AbsoluteGlueing.Hom J F G) :
    absoluteGlueingComp J α (absoluteGlueingId J G) = α := by
  ext U
  simp [absoluteGlueingComp, absoluteGlueingId]

private theorem absoluteGlueing_assoc
    {F G H K : AbsoluteGlueing J} (α : AbsoluteGlueing.Hom J F G)
    (β : AbsoluteGlueing.Hom J G H) (γ : AbsoluteGlueing.Hom J H K) :
    absoluteGlueingComp J (absoluteGlueingComp J α β) γ =
      absoluteGlueingComp J α (absoluteGlueingComp J β γ) := by
  ext U
  simp [absoluteGlueingComp, Category.assoc]

end AbsoluteGlueing

/-- The category of absolute glueings on the site `(C, J)`. -/
instance : Category (AbsoluteGlueing J) where
  Hom F G := AbsoluteGlueing.Hom J F G
  id := AbsoluteGlueing.absoluteGlueingId J
  comp α β := AbsoluteGlueing.absoluteGlueingComp J α β
  id_comp := AbsoluteGlueing.absoluteGlueing_id_comp J
  comp_id := AbsoluteGlueing.absoluteGlueing_comp_id J
  assoc := AbsoluteGlueing.absoluteGlueing_assoc J

/-- The functor sending a sheaf on `(C, J)` to its canonical absolute glueing. -/
noncomputable def sheafToAbsoluteGlueingFunctor :
    Sheaf J (Type w) ⥤ AbsoluteGlueing J where
  obj F :=
    { obj := fun U ↦ F.over U
      transition := fun {U V} f ↦
        (Functor.sheafPushforwardContinuousComp' (Over.mapForget f)
          (Type w) (J.over V) (J.over U) J).app F
      transition_id := by
        intro U
        -- Proof sketch: specialize the identity coherence of the canonical relocalization
        -- comparison.
        sorry
      transition_comp := by
        intro U V W f g
        -- Proof sketch: specialize the cocycle coherence of the canonical relocalization
        -- comparison.
        sorry }
  map {F G} η :=
    { app := fun U ↦ (J.overPullback (Type w) U).map η
      naturality := by
        intro U V f
        exact .mk <| by
          simpa using
            (Functor.sheafPushforwardContinuousComp' (Over.mapForget f)
              (Type w) (J.over V) (J.over U) J).hom.naturality η }
  map_id F := by
    apply AbsoluteGlueing.Hom.ext
    funext U
    rfl
  map_comp η θ := by
    apply AbsoluteGlueing.Hom.ext
    funext U
    rfl

-- Proof sketch: from an absolute glueing datum, form the presheaf `U ↦ ℱ_U(U)` with restriction
-- maps induced by the transition isomorphisms; the cocycle gives functoriality and the local
-- identifications `ℱ_U ≅ ℱ|_{C/U}` show the resulting presheaf is a sheaf. This construction is
-- quasi-inverse to `sheafToAbsoluteGlueingFunctor`.
/-- Lemma 7.26.6: the category `Sh(C)` is equivalent to the category of absolute glueings via the
functor sending a sheaf on `C` to its canonical absolute glueing. -/
instance sheafToAbsoluteGlueingFunctor_isEquivalence :
    Functor.IsEquivalence (sheafToAbsoluteGlueingFunctor J) := sorry

end GrothendieckTopology
end CategoryTheory
